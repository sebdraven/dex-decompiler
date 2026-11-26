//! Whole-method structuring on the dominator tree, after N. Ramsey, "Beyond Relooper" (ICFP 2022, doi:10.1145/3547621).

use crate::decompile::cfg::{BlockEnd, BlockId, MethodCfg};
use crate::decompile::region::{region_is_empty, Region};
use crate::decompile::{negate_condition, DetHashMap, DetHashSet};

const UNDEF: usize = usize::MAX;
/// Deeper dominator trees go back to the legacy builder rather than risk the stack.
const MAX_DEPTH: usize = 1000;

/// Region tree in which every block reachable from `entry` appears exactly once,
/// or `None` when the flow is irreducible.
pub fn build(cfg: &MethodCfg, entry: BlockId) -> Option<Region> {
    let graph = Graph::new(cfg, entry)?;
    let mut builder = Builder {
        cfg,
        g: &graph,
        next_id: 0,
        depth: 0,
        failed: false,
    };
    let raw = builder.translate(entry, &mut Vec::new());
    if builder.failed {
        return None;
    }
    let region = finish(raw);
    each_reachable_block_once(&region, &graph).then_some(region)
}

fn successors(cfg: &MethodCfg, b: BlockId) -> Vec<BlockId> {
    match &cfg.blocks[b].end {
        BlockEnd::Exit => Vec::new(),
        BlockEnd::FallThrough => cfg.fall_through_block(b).into_iter().collect(),
        BlockEnd::Goto(t) => vec![*t],
        BlockEnd::Conditional {
            branch_target,
            fall_through,
            ..
        } => vec![*branch_target, *fall_through],
        BlockEnd::Switch {
            cases,
            default_block,
            ..
        } => cases
            .iter()
            .map(|(_, t)| *t)
            .chain(std::iter::once(*default_block))
            .collect(),
    }
}

struct Graph {
    /// Reverse-postorder number; `UNDEF` for blocks unreachable from the entry.
    rpo_num: Vec<usize>,
    /// Immediate dominator; the entry is its own.
    idom: Vec<BlockId>,
    /// Dominator-tree interval numbering, for constant-time dominance.
    pre: Vec<usize>,
    post: Vec<usize>,
    /// Dominator-tree children in reverse postorder.
    children: Vec<Vec<BlockId>>,
    /// Loop header → its natural loop (header included).
    loops: DetHashMap<BlockId, DetHashSet<BlockId>>,
    /// At least two predecessors through forward edges.
    merge: Vec<bool>,
    /// The outermost loop whose only exit is the block, when the loop dominates it.
    exit_owner: Vec<Option<BlockId>>,
    /// Loop header → its only exit.
    loop_exit: DetHashMap<BlockId, BlockId>,
    /// Block reached through lone `goto`s.
    through: Vec<BlockId>,
}

impl Graph {
    fn new(cfg: &MethodCfg, entry: BlockId) -> Option<Self> {
        let n = cfg.blocks.len();
        if entry >= n {
            return None;
        }
        let mut succs = Vec::with_capacity(n);
        for b in 0..n {
            let mut s = successors(cfg, b);
            if s.iter().any(|&t| t >= n) {
                return None;
            }
            let mut seen = DetHashSet::default();
            s.retain(|t| seen.insert(*t));
            succs.push(s);
        }

        let mut post_order = Vec::with_capacity(n);
        let mut visited = vec![false; n];
        visited[entry] = true;
        let mut stack = vec![(entry, 0usize)];
        while let Some(top) = stack.last_mut() {
            let (b, i) = *top;
            if let Some(&t) = succs[b].get(i) {
                top.1 += 1;
                if !visited[t] {
                    visited[t] = true;
                    stack.push((t, 0));
                }
            } else {
                post_order.push(b);
                stack.pop();
            }
        }
        let rpo: Vec<BlockId> = post_order.into_iter().rev().collect();
        let mut rpo_num = vec![UNDEF; n];
        for (i, &b) in rpo.iter().enumerate() {
            rpo_num[b] = i;
        }
        let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
        for &b in &rpo {
            for &t in &succs[b] {
                preds[t].push(b);
            }
        }

        // Cooper, Harvey, Kennedy: "A Simple, Fast Dominance Algorithm".
        let mut idom = vec![UNDEF; n];
        idom[entry] = entry;
        let mut changed = true;
        while changed {
            changed = false;
            for &b in rpo.iter().skip(1) {
                let mut new = UNDEF;
                for &p in &preds[b] {
                    if idom[p] == UNDEF {
                        continue;
                    }
                    new = if new == UNDEF {
                        p
                    } else {
                        intersect(&idom, &rpo_num, p, new)
                    };
                }
                if new != idom[b] {
                    idom[b] = new;
                    changed = true;
                }
            }
        }

        let mut children = vec![Vec::new(); n];
        for &b in rpo.iter().skip(1) {
            children[idom[b]].push(b);
        }
        let mut pre = vec![UNDEF; n];
        let mut post = vec![UNDEF; n];
        let mut clock = 0;
        pre[entry] = clock;
        clock += 1;
        let mut stack = vec![(entry, 0usize)];
        while let Some(top) = stack.last_mut() {
            let (b, i) = *top;
            if let Some(&c) = children[b].get(i) {
                top.1 += 1;
                pre[c] = clock;
                clock += 1;
                stack.push((c, 0));
            } else {
                post[b] = clock;
                clock += 1;
                stack.pop();
            }
        }
        let dominates = |a: BlockId, b: BlockId| pre[a] <= pre[b] && post[b] <= post[a];

        let mut back_sources: DetHashMap<BlockId, Vec<BlockId>> = DetHashMap::default();
        for &u in &rpo {
            for &v in &succs[u] {
                if dominates(v, u) {
                    back_sources.entry(v).or_default().push(u);
                } else if rpo_num[v] <= rpo_num[u] {
                    // A retreating edge whose target does not dominate its source:
                    // this cycle has no back edge.
                    return None;
                }
            }
        }
        let mut loops = DetHashMap::default();
        for (&h, sources) in &back_sources {
            let mut body = DetHashSet::default();
            body.insert(h);
            let mut stack = sources.clone();
            while let Some(b) = stack.pop() {
                if body.insert(b) {
                    stack.extend(preds[b].iter().copied());
                }
            }
            loops.insert(h, body);
        }
        let merge = (0..n)
            .map(|v| preds[v].iter().filter(|&&p| !dominates(v, p)).count() >= 2)
            .collect();
        // A loop leaving to a single block is followed by it, wherever in the loop the
        // test sits (dex_bytecode puts each branch in its own block, below the header).
        // A lone `goto` reached from one block only leads to its target.
        let lone_goto = |b: BlockId| {
            matches!(cfg.blocks[b].end, BlockEnd::Goto(_))
                && cfg.blocks[b].instruction_offsets.len() <= 1
                && preds[b].len() == 1
        };
        let through_gotos = |mut t: BlockId| {
            for _ in 0..n {
                match succs[t].as_slice() {
                    [s] if lone_goto(t) => t = *s,
                    _ => break,
                }
            }
            t
        };
        let mut exit_owner = vec![None; n];
        let mut loop_exit = DetHashMap::default();
        let mut outermost_first: Vec<(&BlockId, &DetHashSet<BlockId>)> = loops.iter().collect();
        outermost_first.sort_by_key(|(h, body)| (std::cmp::Reverse(body.len()), rpo_num[**h]));
        for (&h, body) in outermost_first {
            let mut exits = body
                .iter()
                .flat_map(|&b| succs[b].iter().copied())
                .filter(|t| !body.contains(t))
                .map(through_gotos);
            let Some(y) = exits.next() else {
                continue;
            };
            if exits.any(|t| t != y) || !body.contains(&idom[y]) || exit_owner[y].is_some() {
                continue;
            }
            exit_owner[y] = Some(h);
            loop_exit.insert(h, y);
        }
        let through = (0..n).map(through_gotos).collect();
        Some(Self {
            rpo_num,
            idom,
            pre,
            post,
            children,
            loops,
            merge,
            exit_owner,
            loop_exit,
            through,
        })
    }

    fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        self.pre[a] <= self.pre[b] && self.post[b] <= self.post[a]
    }
}

fn intersect(idom: &[BlockId], rpo_num: &[usize], mut a: BlockId, mut b: BlockId) -> BlockId {
    while a != b {
        while rpo_num[a] > rpo_num[b] {
            a = idom[a];
        }
        while rpo_num[b] > rpo_num[a] {
            b = idom[b];
        }
    }
    a
}

/// What encloses the code being translated, innermost last.
#[derive(Clone, Copy)]
enum Frame {
    /// Labeled block that ends just before `follow`.
    Block { follow: BlockId, id: usize },
    /// `while (true)`: `continue` goes to `header`, `break` to `follow`.
    Loop {
        header: BlockId,
        follow: Option<BlockId>,
        id: usize,
    },
    /// An unlabeled `break` inside binds here; it reaches `follow`.
    Switch { follow: Option<BlockId>, id: usize },
}

/// Labels are numbered `L0, L1…` once the tree is final.
fn tmp_label(id: usize) -> String {
    format!("#{id}")
}

fn seq(parts: Vec<Region>) -> Region {
    Region::Seq(parts)
}

fn labeled(id: usize, body: Region) -> Region {
    Region::Labeled {
        label: tmp_label(id),
        body: Box::new(body),
    }
}

fn ends_in_switch(cfg: &MethodCfg, b: BlockId) -> bool {
    matches!(cfg.blocks[b].end, BlockEnd::Switch { .. })
}

struct Builder<'a> {
    cfg: &'a MethodCfg,
    g: &'a Graph,
    next_id: usize,
    depth: usize,
    failed: bool,
}

impl Builder<'_> {
    fn fresh(&mut self) -> usize {
        self.next_id += 1;
        self.next_id - 1
    }

    fn fail(&mut self) -> Region {
        self.failed = true;
        seq(Vec::new())
    }

    /// The subtree of the dominator tree rooted at `x`.
    fn translate(&mut self, x: BlockId, ctx: &mut Vec<Frame>) -> Region {
        if self.failed || self.depth >= MAX_DEPTH {
            return self.fail();
        }
        self.depth += 1;
        let g = self.g;
        // A loop's dominated blocks outside the loop come after it, and so does its only
        // exit; for any other block, only the merge nodes it dominates do. A loop's exit
        // is left to that loop.
        let placed_here = |c: &BlockId| g.exit_owner[*c].is_none_or(|h| h == x);
        let (followers, inner): (Vec<BlockId>, Vec<BlockId>) = match g.loops.get(&x) {
            Some(body) => {
                let exit = g.loop_exit.get(&x).copied();
                // A lone `goto` to the exit stays where it is reached.
                let to_exit = |c: &BlockId| exit.is_some_and(|y| *c != y && g.through[*c] == y);
                let mut followers: Vec<BlockId> = g.children[x]
                    .iter()
                    .copied()
                    .filter(|c| !body.contains(c) && placed_here(c) && !to_exit(c))
                    .collect();
                if let Some(y) = exit {
                    if !followers.contains(&y) {
                        followers.push(y);
                    }
                }
                followers.sort_by_key(|&c| g.rpo_num[c]);
                (
                    followers,
                    g.children[x]
                        .iter()
                        .copied()
                        .filter(|c| body.contains(c) && g.merge[*c])
                        .collect(),
                )
            }
            None => (
                g.children[x]
                    .iter()
                    .copied()
                    .filter(|c| g.merge[*c] && placed_here(c))
                    .collect(),
                Vec::new(),
            ),
        };
        let r = self.with_followers(x, &followers, &inner, ctx);
        self.depth -= 1;
        r
    }

    /// `followers` in reverse postorder; the last one is placed outermost.
    fn with_followers(
        &mut self,
        x: BlockId,
        followers: &[BlockId],
        inner: &[BlockId],
        ctx: &mut Vec<Frame>,
    ) -> Region {
        let Some((&last, rest)) = followers.split_last() else {
            return self.core(x, None, inner, ctx);
        };
        if rest.is_empty() && (self.g.loops.contains_key(&x) || ends_in_switch(self.cfg, x)) {
            // The loop, or the switch, ends right before its only follower.
            let core = self.core(x, Some(last), inner, ctx);
            let after = self.translate(last, ctx);
            return seq(vec![core, after]);
        }
        let id = self.fresh();
        ctx.push(Frame::Block { follow: last, id });
        let body = self.with_followers(x, rest, inner, ctx);
        ctx.pop();
        let after = self.translate(last, ctx);
        seq(vec![labeled(id, body), after])
    }

    fn core(
        &mut self,
        x: BlockId,
        follow: Option<BlockId>,
        inner: &[BlockId],
        ctx: &mut Vec<Frame>,
    ) -> Region {
        if !self.g.loops.contains_key(&x) {
            return self.within(x, inner, follow, ctx);
        }
        let id = self.fresh();
        ctx.push(Frame::Loop {
            header: x,
            follow,
            id,
        });
        let body = self.within(x, inner, None, ctx);
        ctx.pop();
        labeled(
            id,
            Region::Loop {
                header: x,
                body: Box::new(body),
            },
        )
    }

    /// `x` itself, inside one labeled block per merge node of `inner`.
    fn within(
        &mut self,
        x: BlockId,
        inner: &[BlockId],
        switch_follow: Option<BlockId>,
        ctx: &mut Vec<Frame>,
    ) -> Region {
        if let Some((&last, rest)) = inner.split_last() {
            let id = self.fresh();
            ctx.push(Frame::Block { follow: last, id });
            let body = self.within(x, rest, switch_follow, ctx);
            ctx.pop();
            let after = self.translate(last, ctx);
            return seq(vec![labeled(id, body), after]);
        }
        let cfg = self.cfg;
        let block = Region::Block(x);
        match &cfg.blocks[x].end {
            BlockEnd::Exit => block,
            BlockEnd::FallThrough => match cfg.fall_through_block(x) {
                Some(t) => seq(vec![block, self.jump(x, t, ctx)]),
                None => block,
            },
            BlockEnd::Goto(t) => seq(vec![block, self.jump(x, *t, ctx)]),
            BlockEnd::Conditional {
                condition,
                branch_target,
                fall_through,
            } => {
                if branch_target == fall_through {
                    return seq(vec![block, self.jump(x, *branch_target, ctx)]);
                }
                let then_r = self.jump(x, *branch_target, ctx);
                let else_r = self.jump(x, *fall_through, ctx);
                seq(vec![block, make_if(condition, then_r, else_r)])
            }
            BlockEnd::Switch {
                condition,
                cases,
                default_block,
            } => {
                let id = self.fresh();
                ctx.push(Frame::Switch {
                    follow: switch_follow,
                    id,
                });
                let switch = self.switch(x, condition, cases, *default_block, ctx);
                ctx.pop();
                labeled(id, seq(vec![block, switch]))
            }
        }
    }

    /// Cases that share a target are adjacent; only the last label of a group has the body.
    fn switch(
        &mut self,
        x: BlockId,
        condition: &str,
        cases: &[(i32, BlockId)],
        default_block: BlockId,
        ctx: &mut Vec<Frame>,
    ) -> Region {
        let mut groups: Vec<(BlockId, Vec<i32>)> = Vec::new();
        for &(value, target) in cases {
            match groups.iter_mut().find(|(t, _)| *t == target) {
                Some((_, values)) => values.push(value),
                None => groups.push((target, vec![value])),
            }
        }
        let mut out = Vec::new();
        let mut default_case = None;
        for (target, values) in &groups {
            let Some((&owner, bare)) = values.split_last() else {
                continue;
            };
            let body = self.jump(x, *target, ctx);
            out.extend(bare.iter().map(|&v| (v, Box::new(seq(Vec::new())))));
            out.push((owner, Box::new(body)));
            if *target == default_block {
                default_case = Some(owner);
            }
        }
        let default = if default_case.is_some() {
            seq(Vec::new())
        } else {
            self.jump(x, default_block, ctx)
        };
        Region::Switch {
            condition: condition.to_string(),
            cases: out,
            default: Box::new(default),
            default_case,
        }
    }

    /// The edge `from → to`: `continue`, `break`, or the dominated subtree inline.
    fn jump(&mut self, from: BlockId, to: BlockId, ctx: &mut Vec<Frame>) -> Region {
        let g = self.g;
        if g.dominates(to, from) {
            let mut innermost = true;
            for frame in ctx.iter().rev() {
                if let Frame::Loop { header, id, .. } = *frame {
                    if header == to {
                        return Region::Continue {
                            label: (!innermost).then(|| tmp_label(id)),
                        };
                    }
                    innermost = false;
                }
            }
            return self.fail();
        }
        let mut innermost = true;
        for frame in ctx.iter().rev() {
            match *frame {
                Frame::Block { follow, id } if follow == to => {
                    return Region::Break {
                        label: Some(tmp_label(id)),
                    };
                }
                Frame::Loop {
                    follow: Some(f), id, ..
                }
                | Frame::Switch {
                    follow: Some(f),
                    id,
                } if f == to => {
                    return Region::Break {
                        label: (!innermost).then(|| tmp_label(id)),
                    };
                }
                Frame::Loop { .. } | Frame::Switch { .. } => innermost = false,
                Frame::Block { .. } => {}
            }
        }
        if g.merge[to] || g.idom[to] != from {
            return self.fail();
        }
        self.translate(to, ctx)
    }
}

/// A `break` or `continue` alone.
fn lone_jump(r: &Region) -> Option<&Region> {
    match r {
        Region::Break { .. } | Region::Continue { .. } => Some(r),
        Region::Seq(children) if children.len() == 1 => lone_jump(&children[0]),
        _ => None,
    }
}

/// A lone jump goes in the `then` arm, and `continue` before `break`.
fn make_if(condition: &str, then_r: Region, else_r: Region) -> Region {
    let swap = match (lone_jump(&then_r), lone_jump(&else_r)) {
        (None, Some(_)) => true,
        (Some(Region::Break { .. }), Some(Region::Continue { .. })) => true,
        _ => false,
    };
    if swap {
        Region::If {
            condition: negate_condition(condition),
            then_branch: Box::new(else_r),
            else_branch: Box::new(then_r),
        }
    } else {
        Region::If {
            condition: condition.to_string(),
            then_branch: Box::new(then_r),
            else_branch: Box::new(else_r),
        }
    }
}

fn finish(region: Region) -> Region {
    let mut region = flatten(region);
    strip_tail_breaks(&mut region);
    let mut refs = DetHashMap::default();
    count_refs(&region, &mut refs);
    let region = name_labels(region, &refs, &mut DetHashMap::default());
    flatten(region)
}

/// Splices nested sequences into their parent, dropping empty ones.
fn flatten(region: Region) -> Region {
    match region {
        Region::Seq(children) => {
            let mut out = Vec::with_capacity(children.len());
            for c in children {
                match flatten(c) {
                    Region::Seq(inner) => out.extend(inner),
                    other => out.push(other),
                }
            }
            Region::Seq(out)
        }
        Region::If {
            condition,
            then_branch,
            else_branch,
        } => Region::If {
            condition,
            then_branch: Box::new(flatten(*then_branch)),
            else_branch: Box::new(flatten(*else_branch)),
        },
        Region::Loop { header, body } => Region::Loop {
            header,
            body: Box::new(flatten(*body)),
        },
        Region::Labeled { label, body } => Region::Labeled {
            label,
            body: Box::new(flatten(*body)),
        },
        Region::Switch {
            condition,
            cases,
            default,
            default_case,
        } => Region::Switch {
            condition,
            cases: cases
                .into_iter()
                .map(|(v, r)| (v, Box::new(flatten(*r))))
                .collect(),
            default: Box::new(flatten(*default)),
            default_case,
        },
        other => other,
    }
}

/// Drops each `break label;` that ends its labeled block anyway.
fn strip_tail_breaks(region: &mut Region) {
    match region {
        Region::Seq(children) => children.iter_mut().for_each(strip_tail_breaks),
        Region::If {
            then_branch,
            else_branch,
            ..
        } => {
            strip_tail_breaks(then_branch);
            strip_tail_breaks(else_branch);
        }
        Region::Loop { body, .. } => strip_tail_breaks(body),
        Region::Switch { cases, default, .. } => {
            cases.iter_mut().for_each(|(_, r)| strip_tail_breaks(r));
            strip_tail_breaks(default);
        }
        Region::Labeled { label, body } => {
            strip_tail_breaks(body);
            remove_tail_break(body, label);
        }
        Region::Block(_) | Region::Break { .. } | Region::Continue { .. } => {}
    }
}

/// Falling off the end of a loop body or a switch case does not leave the block: stop there.
fn remove_tail_break(region: &mut Region, label: &str) {
    if matches!(region, Region::Break { label: Some(l) } if l.as_str() == label) {
        *region = seq(Vec::new());
        return;
    }
    match region {
        Region::Seq(children) => {
            for c in children.iter_mut().rev() {
                remove_tail_break(c, label);
                if !region_is_empty(c) {
                    break;
                }
            }
        }
        Region::If {
            then_branch,
            else_branch,
            ..
        } => {
            remove_tail_break(then_branch, label);
            remove_tail_break(else_branch, label);
        }
        Region::Labeled { body, .. } => remove_tail_break(body, label),
        _ => {}
    }
}

fn count_refs(region: &Region, refs: &mut DetHashMap<String, usize>) {
    match region {
        Region::Break { label: Some(l) } | Region::Continue { label: Some(l) } => {
            *refs.entry(l.clone()).or_default() += 1;
        }
        Region::Break { .. } | Region::Continue { .. } | Region::Block(_) => {}
        Region::Seq(children) => children.iter().for_each(|c| count_refs(c, refs)),
        Region::If {
            then_branch,
            else_branch,
            ..
        } => {
            count_refs(then_branch, refs);
            count_refs(else_branch, refs);
        }
        Region::Loop { body, .. } | Region::Labeled { body, .. } => count_refs(body, refs),
        Region::Switch { cases, default, .. } => {
            cases.iter().for_each(|(_, r)| count_refs(r, refs));
            count_refs(default, refs);
        }
    }
}

/// Unreferenced labels go; the others become `L0, L1…` in order of appearance.
fn name_labels(
    region: Region,
    refs: &DetHashMap<String, usize>,
    names: &mut DetHashMap<String, String>,
) -> Region {
    let rename = |label: Option<String>, names: &DetHashMap<String, String>| {
        label.map(|l| names.get(&l).cloned().unwrap_or(l))
    };
    match region {
        Region::Labeled { label, body } => {
            if refs.get(&label).copied().unwrap_or(0) == 0 {
                return name_labels(*body, refs, names);
            }
            let name = format!("L{}", names.len());
            names.insert(label, name.clone());
            Region::Labeled {
                label: name,
                body: Box::new(name_labels(*body, refs, names)),
            }
        }
        Region::Break { label } => Region::Break {
            label: rename(label, names),
        },
        Region::Continue { label } => Region::Continue {
            label: rename(label, names),
        },
        Region::Block(b) => Region::Block(b),
        Region::Seq(children) => Region::Seq(
            children
                .into_iter()
                .map(|c| name_labels(c, refs, names))
                .collect(),
        ),
        Region::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let then_branch = Box::new(name_labels(*then_branch, refs, names));
            let else_branch = Box::new(name_labels(*else_branch, refs, names));
            Region::If {
                condition,
                then_branch,
                else_branch,
            }
        }
        Region::Loop { header, body } => Region::Loop {
            header,
            body: Box::new(name_labels(*body, refs, names)),
        },
        Region::Switch {
            condition,
            cases,
            default,
            default_case,
        } => {
            let cases = cases
                .into_iter()
                .map(|(v, r)| (v, Box::new(name_labels(*r, refs, names))))
                .collect();
            let default = Box::new(name_labels(*default, refs, names));
            Region::Switch {
                condition,
                cases,
                default,
                default_case,
            }
        }
    }
}

fn count_blocks(region: &Region, count: &mut [usize]) -> bool {
    match region {
        Region::Block(b) => match count.get_mut(*b) {
            Some(c) => {
                *c += 1;
                true
            }
            None => false,
        },
        Region::Break { .. } | Region::Continue { .. } => true,
        Region::Seq(children) => children.iter().all(|c| count_blocks(c, count)),
        Region::If {
            then_branch,
            else_branch,
            ..
        } => count_blocks(then_branch, count) && count_blocks(else_branch, count),
        Region::Loop { body, .. } | Region::Labeled { body, .. } => count_blocks(body, count),
        Region::Switch { cases, default, .. } => {
            cases.iter().all(|(_, r)| count_blocks(r, count)) && count_blocks(default, count)
        }
    }
}

/// Every reachable block once, no other block.
fn each_reachable_block_once(region: &Region, g: &Graph) -> bool {
    let mut count = vec![0usize; g.rpo_num.len()];
    count_blocks(region, &mut count)
        && count
            .iter()
            .zip(&g.rpo_num)
            .all(|(&c, &num)| c == usize::from(num != UNDEF))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::cfg::CfgBlock;
    use crate::decompile::region::region_contains_block;
    use std::collections::{HashMap, HashSet};

    /// One two-byte block per end; `FallThrough` goes to the next block.
    fn cfg_of(ends: Vec<BlockEnd>) -> MethodCfg {
        let blocks: Vec<CfgBlock> = ends
            .into_iter()
            .enumerate()
            .map(|(i, end)| {
                let start = (i * 2) as u32;
                CfgBlock {
                    start_offset: start,
                    end_offset: start + 2,
                    end,
                    instruction_offsets: vec![start],
                }
            })
            .collect();
        let block_by_start: HashMap<u32, BlockId> = blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.start_offset, i))
            .collect();
        MethodCfg {
            blocks,
            block_by_start,
            loop_headers: HashSet::new(),
            entry: 0,
            folded_const_offsets: HashSet::new(),
        }
    }

    fn cond(c: &str, branch_target: BlockId, fall_through: BlockId) -> BlockEnd {
        BlockEnd::Conditional {
            condition: c.into(),
            branch_target,
            fall_through,
        }
    }

    /// Builds, checks that every reachable block appears exactly once.
    fn structured(cfg: &MethodCfg) -> Region {
        let r = build(cfg, cfg.entry).expect("reducible");
        let g = Graph::new(cfg, cfg.entry).expect("graph");
        assert!(each_reachable_block_once(&r, &g), "{r:#?}");
        r
    }

    fn nodes<'a>(r: &'a Region, out: &mut Vec<&'a Region>) {
        out.push(r);
        match r {
            Region::Seq(children) => children.iter().for_each(|c| nodes(c, out)),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => {
                nodes(then_branch, out);
                nodes(else_branch, out);
            }
            Region::Loop { body, .. } | Region::Labeled { body, .. } => nodes(body, out),
            Region::Switch { cases, default, .. } => {
                cases.iter().for_each(|(_, c)| nodes(c, out));
                nodes(default, out);
            }
            Region::Block(_) | Region::Break { .. } | Region::Continue { .. } => {}
        }
    }

    fn all(r: &Region) -> Vec<&Region> {
        let mut out = Vec::new();
        nodes(r, &mut out);
        out
    }

    fn labels(r: &Region) -> Vec<&str> {
        all(r)
            .into_iter()
            .filter_map(|n| match n {
                Region::Labeled { label, .. } => Some(label.as_str()),
                _ => None,
            })
            .collect()
    }

    fn breaks(r: &Region, label: Option<&str>) -> usize {
        all(r)
            .into_iter()
            .filter(|n| matches!(n, Region::Break { label: l } if l.as_deref() == label))
            .count()
    }

    fn continues(r: &Region, label: Option<&str>) -> usize {
        all(r)
            .into_iter()
            .filter(|n| matches!(n, Region::Continue { label: l } if l.as_deref() == label))
            .count()
    }

    fn top(r: &Region) -> &[Region] {
        match r {
            Region::Seq(children) => children,
            other => std::slice::from_ref(other),
        }
    }

    /// Index of the top-level loop with this header, and of block `after` following it.
    fn loop_then_block(r: &Region, header: BlockId, after: BlockId) -> (usize, usize) {
        let items = top(r);
        let at = items
            .iter()
            .position(|c| matches!(c, Region::Loop { header: h, .. } if *h == header))
            .unwrap_or_else(|| panic!("no top-level loop {header}: {r:#?}"));
        let next = items
            .iter()
            .position(|c| matches!(c, Region::Block(b) if *b == after))
            .unwrap_or_else(|| panic!("no top-level block {after}: {r:#?}"));
        (at, next)
    }

    #[test]
    fn diamond_is_if_else_then_merge_without_label() {
        // 0: if (a) goto 2; 1: goto 3; 2: (falls into 3); 3: return
        let cfg = cfg_of(vec![
            cond("a", 2, 1),
            BlockEnd::Goto(3),
            BlockEnd::FallThrough,
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        assert!(labels(&r).is_empty(), "{r:#?}");
        assert_eq!(breaks(&r, None) + continues(&r, None), 0, "{r:#?}");
        match top(&r) {
            [Region::Block(0), Region::If {
                then_branch,
                else_branch,
                ..
            }, Region::Block(3)] => {
                assert!(region_contains_block(then_branch, 2), "{r:#?}");
                assert!(region_contains_block(else_branch, 1), "{r:#?}");
            }
            other => panic!("expected Block(0), If, Block(3): {other:#?}"),
        }
    }

    #[test]
    fn simple_loop() {
        // 0 → 1: if (c) goto 3; 2: goto 1; 3: return
        let cfg = cfg_of(vec![
            BlockEnd::FallThrough,
            cond("c", 3, 2),
            BlockEnd::Goto(1),
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        let (at, next) = loop_then_block(&r, 1, 3);
        assert_eq!(next, at + 1, "{r:#?}");
        assert!(labels(&r).is_empty(), "{r:#?}");
        assert_eq!(breaks(&r, None), 1, "{r:#?}");
        assert_eq!(continues(&r, None), 1, "{r:#?}");
    }

    #[test]
    fn loop_with_break_in_the_middle() {
        // 1: if (c1) goto 4; 2: if (c2) goto 4; 3: goto 1; 4: return
        let cfg = cfg_of(vec![
            BlockEnd::FallThrough,
            cond("c1", 4, 2),
            cond("c2", 4, 3),
            BlockEnd::Goto(1),
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        let (at, next) = loop_then_block(&r, 1, 4);
        assert_eq!(next, at + 1, "{r:#?}");
        assert!(labels(&r).is_empty(), "{r:#?}");
        assert_eq!(breaks(&r, None), 2, "{r:#?}");
        assert_eq!(continues(&r, None), 1, "{r:#?}");
    }

    /// `breakInLoop`: the header only loads the bound, the tests sit in later blocks, and
    /// the second test leaves through a lone `goto`.
    #[test]
    fn exit_tested_below_the_header_follows_the_loop() {
        // 0 → 1 → 2: if (c1) goto 6; 3: if (c2) goto 5; 4: goto 6; 5: goto 1; 6: return
        let cfg = cfg_of(vec![
            BlockEnd::FallThrough,
            BlockEnd::FallThrough,
            cond("c1", 6, 3),
            cond("c2", 5, 4),
            BlockEnd::Goto(6),
            BlockEnd::Goto(1),
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        let (at, next) = loop_then_block(&r, 1, 6);
        assert_eq!(next, at + 1, "{r:#?}");
        assert!(labels(&r).is_empty(), "{r:#?}");
        assert_eq!(breaks(&r, None), 2, "{r:#?}");
        assert_eq!(continues(&r, None), 1, "{r:#?}");
    }

    /// `merge`: both tests of the first loop leave to the header of the next loop.
    #[test]
    fn loops_left_from_tests_below_their_headers_are_successive() {
        // 1: (header) 2: if (c1) goto 6; 3: 4: if (c2) goto 6; 5: goto 1;
        // 6: (header) 7: if (c3) goto 9; 8: goto 6; 9: return
        let cfg = cfg_of(vec![
            BlockEnd::FallThrough,
            BlockEnd::FallThrough,
            cond("c1", 6, 3),
            BlockEnd::FallThrough,
            cond("c2", 6, 5),
            BlockEnd::Goto(1),
            BlockEnd::FallThrough,
            cond("c3", 9, 8),
            BlockEnd::Goto(6),
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        let items = top(&r);
        let first = items
            .iter()
            .position(|c| matches!(c, Region::Loop { header: 1, .. }))
            .unwrap_or_else(|| panic!("no top-level loop 1: {r:#?}"));
        assert!(
            matches!(items.get(first + 1), Some(Region::Loop { header: 6, .. })),
            "{r:#?}"
        );
        assert!(matches!(items.get(first + 2), Some(Region::Block(9))), "{r:#?}");
        assert!(labels(&r).is_empty(), "{r:#?}");
        assert_eq!(breaks(&r, None), 3, "{r:#?}");
        assert_eq!(continues(&r, None), 2, "{r:#?}");
    }

    #[test]
    fn loop_with_continue() {
        // 1: if (c1) goto 4; 2: if (c2) goto 1; 3: goto 1; 4: return
        let cfg = cfg_of(vec![
            BlockEnd::FallThrough,
            cond("c1", 4, 2),
            cond("c2", 1, 3),
            BlockEnd::Goto(1),
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        let (at, next) = loop_then_block(&r, 1, 4);
        assert_eq!(next, at + 1, "{r:#?}");
        assert!(labels(&r).is_empty(), "{r:#?}");
        assert_eq!(breaks(&r, None), 1, "{r:#?}");
        assert_eq!(continues(&r, None), 2, "{r:#?}");
    }

    #[test]
    fn exit_of_outer_loop_from_inner_loop_is_labeled() {
        // outer 1: if (c1) goto 5; inner 2: if (c2) goto 4;
        // 3: if (c3) goto 5 (leaves both); 6: goto 2; 4: goto 1; 5: return
        let cfg = cfg_of(vec![
            BlockEnd::FallThrough,
            cond("c1", 5, 2),
            cond("c2", 4, 3),
            cond("c3", 5, 6),
            BlockEnd::Goto(1),
            BlockEnd::Exit,
            BlockEnd::Goto(2),
        ]);
        let r = structured(&cfg);
        assert_eq!(labels(&r), vec!["L0"], "{r:#?}");
        let outer = all(&r)
            .into_iter()
            .find(|n| matches!(n, Region::Labeled { .. }))
            .unwrap();
        assert!(
            matches!(outer, Region::Labeled { body, .. } if matches!(body.as_ref(), Region::Loop { header: 1, .. })),
            "label must sit on the outer loop: {r:#?}"
        );
        assert_eq!(breaks(&r, Some("L0")), 1, "{r:#?}");
        // Outer exit from its own header, inner exit to 4: both unlabeled.
        assert_eq!(breaks(&r, None), 2, "{r:#?}");
        assert_eq!(continues(&r, None), 2, "{r:#?}");
        assert!(
            matches!(top(&r).last(), Some(Region::Block(5))),
            "{r:#?}"
        );
    }

    #[test]
    fn forward_jump_to_a_merge_node_is_a_labeled_break() {
        // 0: if (a) goto 2; 1: if (b) goto 3; 2: (falls into 3); 3: return
        // 2 and 3 are both merge nodes: `b` skips 2, which `a` reaches directly.
        let cfg = cfg_of(vec![
            cond("a", 2, 1),
            cond("b", 3, 2),
            BlockEnd::FallThrough,
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        assert_eq!(labels(&r), vec!["L0"], "{r:#?}");
        assert_eq!(breaks(&r, Some("L0")), 1, "{r:#?}");
        match top(&r) {
            [Region::Labeled { label, body }, Region::Block(3)] => {
                assert_eq!(label, "L0");
                assert!(region_contains_block(body, 2), "{r:#?}");
            }
            other => panic!("expected L0: {{ … }} then Block(3): {other:#?}"),
        }
    }

    #[test]
    fn switch_cases_sharing_a_target() {
        // 0: switch (x) { 1, 2 → 1; 3 → 2; default → 3 }; 1, 2: goto 4; 3: (falls into 4); 4: return
        let cfg = cfg_of(vec![
            BlockEnd::Switch {
                condition: "x".into(),
                cases: vec![(1, 1), (2, 1), (3, 2)],
                default_block: 3,
            },
            BlockEnd::Goto(4),
            BlockEnd::Goto(4),
            BlockEnd::FallThrough,
            BlockEnd::Exit,
        ]);
        let r = structured(&cfg);
        assert!(labels(&r).is_empty(), "{r:#?}");
        match top(&r) {
            [Region::Block(0), Region::Switch {
                cases,
                default,
                default_case,
                ..
            }, Region::Block(4)] => {
                assert_eq!(cases.len(), 3, "{r:#?}");
                assert_eq!(cases[0].0, 1);
                assert!(region_is_empty(&cases[0].1), "case 1 shares case 2's body: {r:#?}");
                assert_eq!(cases[1].0, 2);
                assert!(region_contains_block(&cases[1].1, 1), "{r:#?}");
                assert_eq!(cases[2].0, 3);
                assert!(region_contains_block(&cases[2].1, 2), "{r:#?}");
                assert!(region_contains_block(default, 3), "{r:#?}");
                assert_eq!(*default_case, None);
            }
            other => panic!("expected Block(0), Switch, Block(4): {other:#?}"),
        }
        // Every arm leaves the switch with a plain `break;`.
        assert_eq!(breaks(&r, None), 3, "{r:#?}");
    }

    #[test]
    fn irreducible_flow_is_refused() {
        // 1 and 2 reach each other, and the entry reaches both directly.
        let cfg = cfg_of(vec![
            cond("c", 2, 1),
            cond("d", 2, 3),
            BlockEnd::Goto(1),
            BlockEnd::Exit,
        ]);
        assert!(build(&cfg, cfg.entry).is_none());
    }
}
