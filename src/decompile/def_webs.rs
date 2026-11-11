//! Method-wide reaching definitions grouped into def-use webs.
//!
//! A web is the set of definitions of one register that reach a common use: one source
//! variable. Naming and constant folding key on webs instead of bare register numbers.

use super::cfg::{BlockId, MethodCfg};
use super::read_write::instruction_reads_writes;
use dex_bytecode::Instruction;
use std::collections::{BTreeSet, HashMap};

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

impl DefWebs {
    /// `exceptional_edges` connect protected blocks to handlers: every definition made
    /// anywhere in the protected block may reach the handler.
    pub(crate) fn build(
        cfg: &MethodCfg,
        instructions: &[Instruction],
        exceptional_edges: &[(BlockId, BlockId)],
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
        let mut exc_preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
        for &(from, to) in exceptional_edges {
            if from < n && to < n && !exc_preds[to].contains(&from) {
                exc_preds[to].push(from);
            }
        }
        let mut seed = RegDefs::new();
        for &reg in entry_regs {
            seed.entry(reg).or_default().insert(ENTRY_DEF);
        }

        let mut block_in: Vec<RegDefs> = vec![RegDefs::new(); n];
        let mut block_out: Vec<RegDefs> = vec![RegDefs::new(); n];
        let mut block_all: Vec<RegDefs> = vec![RegDefs::new(); n];
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
                for &p in &exc_preds[bid] {
                    merge(&mut inn, &block_all[p]);
                }
                let mut out = inn.clone();
                let mut all = inn.clone();
                for off in &block_offsets[bid] {
                    if let Some((_, writes)) = rw.get(off) {
                        for &w in writes {
                            out.insert(w, BTreeSet::from([*off]));
                            all.entry(w).or_default().insert(*off);
                        }
                    }
                }
                if inn != block_in[bid] || out != block_out[bid] || all != block_all[bid] {
                    block_in[bid] = inn;
                    block_out[bid] = out;
                    block_all[bid] = all;
                    changed = true;
                }
            }
        }

        let mut parent: HashMap<DefKey, DefKey> = HashMap::new();
        let mut uses: HashMap<DefKey, usize> = HashMap::new();
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
                        match first {
                            None => {
                                parent.entry(key).or_insert(key);
                                first = Some(key);
                            }
                            Some(f) => union(&mut parent, f, key),
                        }
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
        }
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
}
