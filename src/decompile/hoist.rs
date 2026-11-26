//! Where each variable of a `structure::build` tree is declared: before the child of the
//! smallest region holding all its definitions and uses, when its first assignment does
//! not already come first at that level.

use super::cfg::{BlockId, MethodCfg};
use super::def_webs::{DefKey, DefWebs};
use super::region::Region;
use super::DetHashMap;

/// Address of a region of the tree → webs declared, uninitialized, right before it.
pub(crate) type HoistSites = DetHashMap<usize, Vec<DefKey>>;

pub(crate) fn region_addr(region: &Region) -> usize {
    region as *const Region as usize
}

struct Node<'r> {
    region: &'r Region,
    parent: Option<usize>,
    depth: usize,
}

/// Nodes in emission order.
struct Tree<'r> {
    nodes: Vec<Node<'r>>,
    block_node: DetHashMap<BlockId, usize>,
}

fn children(region: &Region) -> Vec<&Region> {
    match region {
        Region::Seq(c) => c.iter().collect(),
        Region::If {
            then_branch,
            else_branch,
            ..
        } => vec![then_branch.as_ref(), else_branch.as_ref()],
        Region::Loop { body, .. } | Region::Labeled { body, .. } => vec![body.as_ref()],
        Region::Switch { cases, default, .. } => cases
            .iter()
            .map(|(_, r)| r.as_ref())
            .chain(std::iter::once(default.as_ref()))
            .collect(),
        Region::Block(_) | Region::Break { .. } | Region::Continue { .. } => Vec::new(),
    }
}

impl<'r> Tree<'r> {
    fn new(root: &'r Region) -> Self {
        let mut tree = Tree {
            nodes: Vec::new(),
            block_node: DetHashMap::default(),
        };
        let mut stack = vec![(root, None, 0usize)];
        while let Some((region, parent, depth)) = stack.pop() {
            let id = tree.nodes.len();
            tree.nodes.push(Node {
                region,
                parent,
                depth,
            });
            if let Region::Block(b) = region {
                tree.block_node.insert(*b, id);
            }
            for c in children(region).into_iter().rev() {
                stack.push((c, Some(id), depth + 1));
            }
        }
        tree
    }

    fn lca(&self, mut a: usize, mut b: usize) -> usize {
        while self.nodes[a].depth > self.nodes[b].depth {
            a = self.nodes[a].parent.unwrap_or(a);
        }
        while self.nodes[b].depth > self.nodes[a].depth {
            b = self.nodes[b].parent.unwrap_or(b);
        }
        while a != b {
            match (self.nodes[a].parent, self.nodes[b].parent) {
                (Some(pa), Some(pb)) => (a, b) = (pa, pb),
                _ => break,
            }
        }
        a
    }

    /// Child of `ancestor` on the path to `node`.
    fn child_toward(&self, ancestor: usize, mut node: usize) -> usize {
        while let Some(p) = self.nodes[node].parent {
            if p == ancestor {
                break;
            }
            node = p;
        }
        node
    }
}

#[derive(Default)]
struct Occurrences {
    /// (block, offset) of each definition, then of each use.
    defs: Vec<(BlockId, u32)>,
    uses: Vec<(BlockId, u32)>,
    outside_tree: bool,
}

/// Declaration site of every web whose first assignment is not its first occurrence
/// at the level of the smallest region enclosing them all. Parameters and `this`
/// (webs holding the entry value) are left out.
pub(crate) fn hoist_sites(root: &Region, cfg: &MethodCfg, webs: &DefWebs) -> HoistSites {
    let tree = Tree::new(root);
    let mut block_of: DetHashMap<u32, BlockId> = DetHashMap::default();
    for (b, block) in cfg.blocks.iter().enumerate() {
        for &off in &block.instruction_offsets {
            block_of.insert(off, b);
        }
    }
    let mut occ: DetHashMap<DefKey, Occurrences> = DetHashMap::default();
    let mut order: Vec<DefKey> = Vec::new();
    for (b, block) in cfg.blocks.iter().enumerate() {
        if !tree.block_node.contains_key(&b) {
            continue;
        }
        for &off in &block.instruction_offsets {
            for &reg in webs.writes(off) {
                if webs.shares_entry(reg, off) {
                    continue;
                }
                let web = webs.web(reg, off);
                if webs.is_exception_web(web) {
                    continue;
                }
                let o = occ.entry(web).or_insert_with(|| {
                    order.push(web);
                    Occurrences::default()
                });
                o.defs.push((b, off));
                for &site in webs.use_sites(reg, off) {
                    match block_of.get(&site) {
                        Some(&sb) if tree.block_node.contains_key(&sb) => o.uses.push((sb, site)),
                        _ => o.outside_tree = true,
                    }
                }
            }
        }
    }

    let mut sites = HoistSites::default();
    for web in order {
        let o = &occ[&web];
        if o.outside_tree || o.uses.is_empty() {
            continue;
        }
        let node = |&(b, _): &(BlockId, u32)| tree.block_node[&b];
        let mut nodes = o.defs.iter().chain(&o.uses).map(node);
        let Some(first) = nodes.next() else {
            continue;
        };
        let lca = nodes.fold(first, |acc, n| tree.lca(acc, n));
        let mut anchor = match tree.nodes[lca].region {
            Region::Block(_) => continue,
            Region::Seq(_) => {
                let Some(child) = o
                    .defs
                    .iter()
                    .chain(&o.uses)
                    .map(|occurrence| tree.child_toward(lca, node(occurrence)))
                    .min()
                else {
                    continue;
                };
                if let Region::Block(b) = tree.nodes[child].region {
                    if declared_in_place(*b, o) {
                        continue;
                    }
                }
                child
            }
            _ => lca,
        };
        // A label belongs to its statement: declare before the label.
        while let Some(p) = tree.nodes[anchor].parent {
            if !matches!(tree.nodes[p].region, Region::Labeled { .. }) {
                break;
            }
            anchor = p;
        }
        sites
            .entry(region_addr(tree.nodes[anchor].region))
            .or_default()
            .push(web);
    }
    sites
}

/// Block `b` assigns the web before any read of it in `b`.
fn declared_in_place(b: BlockId, o: &Occurrences) -> bool {
    let Some(first_def) = o.defs.iter().filter(|(db, _)| *db == b).map(|(_, off)| *off).min()
    else {
        return false;
    };
    o.uses
        .iter()
        .filter(|(ub, _)| *ub == b)
        .all(|(_, off)| *off > first_def)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A bottom-tested loop: fetch into v0, repeat while zero, then show v0.
    /// Supply its tree explicitly so this scope test is independent of the structurer's
    /// choice to keep the exit tail inside the loop or place it after the loop.
    fn loop_fixture() -> (MethodCfg, DefWebs, Region) {
        let bytecode = [
            0x71, 0x00, 0x00, 0x00, 0x00, 0x00, // 0: touch()
            0x71, 0x00, 0x01, 0x00, 0x00, 0x00, // 6: fetch()
            0x0a, 0x00, // 12: move-result v0
            0x38, 0x00, 0xfc, 0xff, // 14: if-eqz v0 -> 6
            0x71, 0x10, 0x02, 0x00, 0x00, 0x00, // 18: showInt(v0)
            0x0e, 0x00, // 24: return-void
        ];
        let instructions = dex_bytecode::decode_all(&bytecode, 0).expect("decode");
        let cfg = MethodCfg::build(&instructions, &bytecode, 0, &|_| "v0 == 0".into());
        let webs = DefWebs::build(&cfg, &instructions, &[], &[]);
        let block_at = |off| {
            cfg.blocks
                .iter()
                .position(|b| b.instruction_offsets.contains(&off))
                .expect("block")
        };
        let header = block_at(6);
        let condition = block_at(14);
        let mut body = vec![Region::Block(header)];
        if condition != header {
            body.push(Region::Block(condition));
        }
        body.push(Region::If {
            condition: "v0 == 0".into(),
            then_branch: Box::new(Region::Continue { label: None }),
            else_branch: Box::new(Region::Break { label: None }),
        });
        let root = Region::Seq(vec![
            Region::Block(block_at(0)),
            Region::Loop {
                header,
                body: Box::new(Region::Seq(body)),
            },
            Region::Block(block_at(18)),
        ]);
        (cfg, webs, root)
    }

    #[test]
    fn variable_assigned_in_a_loop_and_read_after_is_declared_before_it() {
        let (cfg, webs, root) = loop_fixture();
        let Region::Seq(children) = &root else {
            panic!("sequence")
        };
        let sites = hoist_sites(&root, &cfg, &webs);
        assert_eq!(sites.len(), 1);
        assert_eq!(
            sites.get(&region_addr(&children[1])),
            Some(&vec![webs.web(0, 12)])
        );
    }

    #[test]
    fn loop_declaration_precedes_its_label() {
        let (cfg, webs, mut root) = loop_fixture();
        let Region::Seq(children) = &mut root else {
            panic!("sequence")
        };
        let loop_region = children.remove(1);
        children.insert(
            1,
            Region::Labeled {
                label: "L0".into(),
                body: Box::new(loop_region),
            },
        );
        let sites = hoist_sites(&root, &cfg, &webs);
        let Region::Seq(children) = &root else {
            panic!("sequence")
        };
        assert_eq!(sites.len(), 1);
        assert_eq!(
            sites.get(&region_addr(&children[1])),
            Some(&vec![webs.web(0, 12)])
        );
    }
}
