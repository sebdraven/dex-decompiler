//! Method-wide reaching definitions grouped into def-use webs.
//!
//! A web is the set of definitions of one register that reach a common use: one source
//! variable. Naming and constant folding key on webs instead of bare register numbers.

use super::cfg::{BlockId, MethodCfg};
use super::read_write::instruction_reads_writes;
use dex_bytecode::Instruction;
use std::collections::{BTreeSet, HashMap, HashSet};

/// Pseudo definition: the value a register holds on method entry (incoming argument).
pub(crate) const ENTRY_DEF: u32 = u32::MAX;

type RegDefs = HashMap<u32, BTreeSet<u32>>;
/// (register, defining instruction offset or `ENTRY_DEF`).
pub(crate) type DefKey = (u32, u32);

pub(crate) struct DefWebs {
    block_in: Vec<RegDefs>,
    block_offsets: Vec<Vec<u32>>,
    position: HashMap<u32, (BlockId, usize)>,
    rw: HashMap<u32, (Vec<u32>, Vec<u32>)>,
    parent: HashMap<DefKey, DefKey>,
    uses: HashMap<DefKey, usize>,
    use_sites: HashMap<DefKey, Vec<u32>>,
    const_defs: HashSet<u32>,
    exception_defs: HashSet<u32>,
    object_defs: HashSet<u32>,
    /// Catch handler entries a block belongs to; empty when it is reachable without a throw.
    handlers_of: Vec<BTreeSet<BlockId>>,
    /// Protected byte ranges `[start, end)`.
    tries: Vec<(u32, u32)>,
}

fn merge(into: &mut RegDefs, from: &RegDefs) {
    for (reg, defs) in from {
        into.entry(*reg).or_default().extend(defs.iter().copied());
    }
}

fn find(parent: &HashMap<DefKey, DefKey>, key: DefKey) -> DefKey {
    let mut cur = key;
    while let Some(&p) = parent.get(&cur) {
        if p == cur {
            break;
        }
        cur = p;
    }
    cur
}

fn union(parent: &mut HashMap<DefKey, DefKey>, a: DefKey, b: DefKey) {
    parent.entry(a).or_insert(a);
    parent.entry(b).or_insert(b);
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        parent.insert(ra, rb);
    }
}

/// (protected block, handler block, try start, try end): the handler is entered from any
/// instruction of the block inside `[start, end)`.
pub(crate) type ExcEdge = (BlockId, BlockId, u32, u32);

impl DefWebs {
    /// A handler receives the definitions live just before an instruction of the try
    /// range, never those made after its last protected instruction.
    pub(crate) fn build(
        cfg: &MethodCfg,
        instructions: &[Instruction],
        exceptional_edges: &[ExcEdge],
        entry_regs: &[u32],
    ) -> Self {
        let rw: HashMap<u32, (Vec<u32>, Vec<u32>)> = instructions
            .iter()
            .map(|ins| {
                (
                    ins.offset as u32,
                    instruction_reads_writes(ins.mnemonic(), ins.operands()),
                )
            })
            .collect();
        let n = cfg.blocks.len();
        let block_offsets: Vec<Vec<u32>> = cfg
            .blocks
            .iter()
            .map(|b| b.instruction_offsets.clone())
            .collect();
        let mut position = HashMap::new();
        for (bid, offs) in block_offsets.iter().enumerate() {
            for (i, &off) in offs.iter().enumerate() {
                position.insert(off, (bid, i));
            }
        }
        let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
        for (from, to) in cfg.successor_edges() {
            if from < n && to < n && !preds[to].contains(&from) {
                preds[to].push(from);
            }
        }
        let exc_edges: Vec<ExcEdge> = exceptional_edges
            .iter()
            .copied()
            .filter(|&(from, to, _, _)| from < n && to < n && from != to)
            .collect();
        let mut succs: Vec<Vec<BlockId>> = vec![Vec::new(); n];
        for (to, from_list) in preds.iter().enumerate() {
            for &from in from_list {
                succs[from].push(to);
            }
        }
        let mut normal = vec![false; n];
        let mut stack = vec![cfg.entry];
        while let Some(b) = stack.pop() {
            if b >= n || normal[b] {
                continue;
            }
            normal[b] = true;
            stack.extend(succs[b].iter().copied());
        }
        let mut handlers_of: Vec<BTreeSet<BlockId>> = vec![BTreeSet::new(); n];
        let handler_entries: BTreeSet<BlockId> =
            exc_edges.iter().map(|&(_, to, _, _)| to).collect();
        for &h in &handler_entries {
            let mut stack = vec![h];
            while let Some(b) = stack.pop() {
                if b >= n || normal[b] || !handlers_of[b].insert(h) {
                    continue;
                }
                stack.extend(succs[b].iter().copied());
            }
        }
        let mut const_defs = HashSet::new();
        let mut exception_defs = HashSet::new();
        let mut check_casts = HashSet::new();
        let mut object_defs = HashSet::new();
        for ins in instructions {
            let off = ins.offset as u32;
            if matches!(
                ins.mnemonic(),
                "const-string"
                    | "const-string/jumbo"
                    | "new-instance"
                    | "move-result-object"
                    | "iget-object"
                    | "sget-object"
                    | "check-cast"
            ) {
                object_defs.insert(off);
            }
            match ins.mnemonic() {
                "const" | "const/4" | "const/16" | "const-string" | "const-string/jumbo"
                | "const-class" => {
                    const_defs.insert(off);
                }
                m if m.starts_with("const-wide") => {
                    const_defs.insert(off);
                }
                "move-exception" => {
                    exception_defs.insert(off);
                }
                "check-cast" => {
                    check_casts.insert(off);
                }
                _ => {}
            }
        }
        let mut seed = RegDefs::new();
        for &reg in entry_regs {
            seed.entry(reg).or_default().insert(ENTRY_DEF);
        }

        let mut block_in: Vec<RegDefs> = vec![RegDefs::new(); n];
        let mut block_out: Vec<RegDefs> = vec![RegDefs::new(); n];
        let mut exc_out: Vec<RegDefs> = vec![RegDefs::new(); exc_edges.len()];
        let mut changed = true;
        while changed {
            changed = false;
            for bid in 0..n {
                let mut inn = if bid == cfg.entry {
                    seed.clone()
                } else {
                    RegDefs::new()
                };
                for &p in &preds[bid] {
                    merge(&mut inn, &block_out[p]);
                }
                for (e, &(_, to, _, _)) in exc_edges.iter().enumerate() {
                    if to == bid {
                        merge(&mut inn, &exc_out[e]);
                    }
                }
                let leaving: Vec<usize> = (0..exc_edges.len())
                    .filter(|&e| exc_edges[e].0 == bid)
                    .collect();
                let mut thrown: Vec<RegDefs> = vec![RegDefs::new(); leaving.len()];
                let mut out = inn.clone();
                for off in &block_offsets[bid] {
                    for (k, &e) in leaving.iter().enumerate() {
                        let (_, _, start, end) = exc_edges[e];
                        if start <= *off && *off < end {
                            merge(&mut thrown[k], &out);
                        }
                    }
                    if let Some((_, writes)) = rw.get(off) {
                        for &w in writes {
                            out.insert(w, BTreeSet::from([*off]));
                        }
                    }
                }
                for (k, &e) in leaving.iter().enumerate() {
                    if thrown[k] != exc_out[e] {
                        exc_out[e] = std::mem::take(&mut thrown[k]);
                        changed = true;
                    }
                }
                if inn != block_in[bid] || out != block_out[bid] {
                    block_in[bid] = inn;
                    block_out[bid] = out;
                    changed = true;
                }
            }
        }

        let mut parent: HashMap<DefKey, DefKey> = HashMap::new();
        let mut uses: HashMap<DefKey, usize> = HashMap::new();
        let mut use_sites: HashMap<DefKey, Vec<u32>> = HashMap::new();
        for bid in 0..n {
            let mut cur = block_in[bid].clone();
            for off in &block_offsets[bid] {
                let Some((reads, writes)) = rw.get(off) else {
                    continue;
                };
                for &reg in reads {
                    let Some(defs) = cur.get(&reg) else {
                        continue;
                    };
                    let mut first: Option<DefKey> = None;
                    for &def in defs {
                        let key = (reg, def);
                        *uses.entry(key).or_insert(0) += 1;
                        use_sites.entry(key).or_default().push(*off);
                        match first {
                            None => {
                                parent.entry(key).or_insert(key);
                                first = Some(key);
                            }
                            Some(f) => union(&mut parent, f, key),
                        }
                    }
                    // check-cast rewrites the value it reads: still the same variable.
                    if let Some(f) = first.filter(|_| check_casts.contains(off)) {
                        union(&mut parent, f, (reg, *off));
                    }
                }
                for &w in writes {
                    cur.insert(w, BTreeSet::from([*off]));
                }
            }
        }
        let keys: Vec<DefKey> = parent.keys().copied().collect();
        for key in keys {
            let root = find(&parent, key);
            parent.insert(key, root);
        }

        Self {
            block_in,
            block_offsets,
            position,
            rw,
            parent,
            uses,
            use_sites,
            const_defs,
            exception_defs,
            object_defs,
            handlers_of,
            tries: Vec::new(),
        }
    }

    pub(crate) fn with_tries(mut self, tries: Vec<(u32, u32)>) -> Self {
        self.tries = tries;
        self
    }

    /// Definitions of `reg` live just before the instruction at `off`.
    pub(crate) fn reaching(&self, off: u32, reg: u32) -> BTreeSet<u32> {
        let Some(&(bid, idx)) = self.position.get(&off) else {
            return BTreeSet::new();
        };
        let mut defs = self.block_in[bid].get(&reg).cloned().unwrap_or_default();
        for prev in &self.block_offsets[bid][..idx] {
            if self.rw.get(prev).is_some_and(|(_, w)| w.contains(&reg)) {
                defs = BTreeSet::from([*prev]);
            }
        }
        defs
    }

    pub(crate) fn reads(&self, off: u32) -> &[u32] {
        self.rw.get(&off).map(|(r, _)| r.as_slice()).unwrap_or(&[])
    }

    /// Representative of the web holding definition `def` of `reg`.
    pub(crate) fn web(&self, reg: u32, def: u32) -> DefKey {
        find(&self.parent, (reg, def))
    }

    /// The value defined at `def` is the same source variable as the incoming one.
    pub(crate) fn shares_entry(&self, reg: u32, def: u32) -> bool {
        def == ENTRY_DEF
            || (self.parent.contains_key(&(reg, ENTRY_DEF))
                && self.web(reg, def) == self.web(reg, ENTRY_DEF))
    }

    /// Number of register reads reached by definition `def` of `reg`.
    pub(crate) fn use_count(&self, reg: u32, def: u32) -> usize {
        self.uses.get(&(reg, def)).copied().unwrap_or(0)
    }

    /// Offsets of the instructions that read definition `def` of `reg`.
    pub(crate) fn use_sites(&self, reg: u32, def: u32) -> &[u32] {
        self.use_sites
            .get(&(reg, def))
            .map(|s| s.as_slice())
            .unwrap_or(&[])
    }

    fn members(&self, web: DefKey) -> impl Iterator<Item = DefKey> + '_ {
        self.parent
            .iter()
            .filter(move |(_, root)| **root == web)
            .map(|(key, _)| *key)
    }

    /// Every definition of `web` is a `move-exception`: the variable of a catch clause.
    pub(crate) fn is_exception_web(&self, web: DefKey) -> bool {
        let mut members = self.members(web).peekable();
        members.peek().is_some() && members.all(|(_, def)| self.exception_defs.contains(&def))
    }

    /// One definition of `web` produces an object (string, new instance, object result,
    /// object field, cast).
    pub(crate) fn has_object_def(&self, web: DefKey) -> bool {
        self.members(web)
            .any(|(_, def)| self.object_defs.contains(&def))
    }

    /// The only definition of `web` is a constant, read once, inside the same try ranges
    /// and the same catch handlers as its definition.
    pub(crate) fn inlinable_const(&self, web: DefKey) -> bool {
        let mut members = self.members(web);
        let (Some((reg, def)), None) = (members.next(), members.next()) else {
            return false;
        };
        if !self.const_defs.contains(&def) || self.use_count(reg, def) != 1 {
            return false;
        }
        self.use_sites(reg, def)
            .first()
            .is_some_and(|&site| self.same_region(def, site))
    }

    fn same_region(&self, a: u32, b: u32) -> bool {
        let covering = |off: u32| -> Vec<bool> {
            self.tries
                .iter()
                .map(|&(start, end)| start <= off && off < end)
                .collect()
        };
        let handlers = |off: u32| {
            self.position
                .get(&off)
                .and_then(|&(bid, _)| self.handlers_of.get(bid))
        };
        covering(a) == covering(b)
            && matches!((handlers(a), handlers(b)), (Some(x), Some(y)) if x == y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn condition_no_branch(_: &Instruction) -> String {
        "true".into()
    }

    fn webs(bytecode: &[u8], entry_regs: &[u32]) -> DefWebs {
        let instructions = dex_bytecode::decode_all(bytecode, 0).expect("decode");
        let cfg = MethodCfg::build(&instructions, bytecode, 0, &condition_no_branch);
        DefWebs::build(&cfg, &instructions, &[], entry_regs)
    }

    /// `move-result` into the register of an earlier const is a new variable.
    #[test]
    fn move_result_starts_a_new_web() {
        let w = webs(
            &[
                0x12, 0x00, // 0: const/4 v0, 0
                0x6e, 0x10, 0x00, 0x00, 0x00, 0x00, // 2: invoke-virtual {v0}
                0x0a, 0x00, // 8: move-result v0
                0x6e, 0x10, 0x00, 0x00, 0x00, 0x00, // 10: invoke-virtual {v0}
                0x0e, 0x00, // 16: return-void
            ],
            &[],
        );
        assert_eq!(w.reaching(2, 0), BTreeSet::from([0]));
        assert_eq!(w.reaching(10, 0), BTreeSet::from([8]));
        assert_ne!(w.web(0, 0), w.web(0, 8));
        assert_eq!(w.use_count(0, 0), 1);
    }

    /// A parameter register reused for a constant is not the parameter any more.
    #[test]
    fn reused_parameter_register_leaves_the_entry_web() {
        let w = webs(
            &[
                0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 0: invoke-virtual {v1}
                0x12, 0x01, // 6: const/4 v1, 0
                0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 8: invoke-virtual {v1}
                0x0e, 0x00, // 14: return-void
            ],
            &[1],
        );
        assert_eq!(w.reaching(0, 1), BTreeSet::from([ENTRY_DEF]));
        assert_eq!(w.reaching(8, 1), BTreeSet::from([6]));
        assert!(!w.shares_entry(1, 6));
    }

    /// Two definitions merging at a join are one variable.
    #[test]
    fn definitions_meeting_at_a_join_share_a_web() {
        let w = webs(
            &[
                0x12, 0x00, // 0: const/4 v0, 0
                0x12, 0x11, // 2: const/4 v1, 1
                0x38, 0x00, 0x03, 0x00, // 4: if-eqz v0, +3 -> 10
                0x12, 0x21, // 8: const/4 v1, 2
                0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 10: invoke-virtual {v1}
                0x0e, 0x00, // 16: return-void
            ],
            &[],
        );
        assert_eq!(w.reaching(10, 1), BTreeSet::from([2, 8]));
        assert_eq!(w.web(1, 2), w.web(1, 8));
    }

    /// Webs of a method with one try range `[start, end)` and its handler at `handler`.
    fn webs_with_try(bytecode: &[u8], start: u32, end: u32, handler: u32) -> DefWebs {
        let instructions = dex_bytecode::decode_all(bytecode, 0).expect("decode");
        let mut cfg = MethodCfg::build(&instructions, bytecode, 0, &condition_no_branch);
        cfg.split_at_offsets(&[handler]);
        let edges: Vec<ExcEdge> = cfg
            .exceptional_edges_for_range(start, end, &[handler])
            .into_iter()
            .map(|(from, to)| (from, to, start, end))
            .collect();
        DefWebs::build(&cfg, &instructions, &edges, &[]).with_tries(vec![(start, end)])
    }

    /// T3 (001173 a()): three constants loaded in turn into v1, each read once. The try
    /// covers only the first; its handler reads v1. Only the first constant can reach the
    /// handler, so the three stay three webs.
    #[test]
    fn values_set_after_the_try_range_never_reach_its_handler() {
        let bytecode = [
            0x1a, 0x01, 0x00, 0x00, // 0: const-string v1, string@0
            0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 4: invoke-virtual {v1}
            0x1a, 0x01, 0x01, 0x00, // 10: const-string v1, string@1
            0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 14: invoke-virtual {v1}
            0x12, 0x01, // 20: const/4 v1, 0
            0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 22: invoke-virtual {v1}
            0x0e, 0x00, // 28: return-void
            0x0d, 0x00, // 30: move-exception v0
            0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 32: invoke-virtual {v1}
            0x0e, 0x00, // 38: return-void
        ];
        let w = webs_with_try(&bytecode, 0, 10, 30);
        assert_eq!(w.reaching(32, 1), BTreeSet::from([0]));
        let webs: BTreeSet<DefKey> = [0, 10, 20].iter().map(|&d| w.web(1, d)).collect();
        assert_eq!(webs.len(), 3);
    }

    /// S1 (000128 c()): a cast parameter is still the parameter: same web as the entry
    /// value, so `apply_def_web_names` keeps the parameter's name (`shares_entry`).
    #[test]
    fn check_cast_of_a_parameter_stays_in_the_entry_web() {
        let w = webs(
            &[
                0x1f, 0x01, 0x00, 0x00, // 0: check-cast v1, type@0
                0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 4: invoke-virtual {v1}
                0x0e, 0x00, // 10: return-void
            ],
            &[1],
        );
        assert_eq!(w.reaching(4, 1), BTreeSet::from([0]));
        assert_eq!(w.web(1, 0), w.web(1, ENTRY_DEF));
        assert!(w.shares_entry(1, 0));
    }

    /// S2: a constant read once inside the try range of its definition is inlinable; the
    /// same read with the definition outside the range is not.
    #[test]
    fn single_use_const_in_its_try_is_inlinable() {
        let bytecode = [
            0x12, 0x10, // 0: const/4 v0, 1
            0x6e, 0x10, 0x00, 0x00, 0x00, 0x00, // 2: invoke-virtual {v0}
            0x0e, 0x00, // 8: return-void
            0x0d, 0x01, // 10: move-exception v1
            0x0e, 0x00, // 12: return-void
        ];
        let w = webs_with_try(&bytecode, 0, 8, 10);
        assert!(w.inlinable_const(w.web(0, 0)));
        let w = webs_with_try(&bytecode, 2, 8, 10);
        assert!(!w.inlinable_const(w.web(0, 0)));
    }

    /// S2 (001155 t()): one value set in the try, another in the catch, read after the
    /// join: one web with two definitions, never inlinable.
    #[test]
    fn try_and_catch_definitions_joining_are_not_inlinable() {
        let bytecode = [
            0x12, 0x10, // 0: const/4 v0, 1
            0x28, 0x03, // 2: goto +3 -> 8
            0x0d, 0x01, // 4: move-exception v1
            0x12, 0x20, // 6: const/4 v0, 2
            0x6e, 0x10, 0x00, 0x00, 0x00, 0x00, // 8: invoke-virtual {v0}
            0x0e, 0x00, // 14: return-void
        ];
        let w = webs_with_try(&bytecode, 0, 2, 4);
        assert_eq!(w.reaching(8, 0), BTreeSet::from([0, 6]));
        assert_eq!(w.web(0, 0), w.web(0, 6));
        assert!(!w.inlinable_const(w.web(0, 0)));
    }

    /// S3: the register written by move-exception and read in the handler is a catch web.
    #[test]
    fn move_exception_web_is_the_catch_variable() {
        let bytecode = [
            0x0e, 0x00, // 0: return-void
            0x0d, 0x01, // 2: move-exception v1
            0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 4: invoke-virtual {v1}
            0x0e, 0x00, // 10: return-void
        ];
        let w = webs_with_try(&bytecode, 0, 2, 2);
        assert_eq!(w.reaching(4, 1), BTreeSet::from([2]));
        assert!(w.is_exception_web(w.web(1, 2)));
    }
}
