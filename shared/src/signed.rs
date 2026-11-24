//! A block's signed set: every signature its proof rests on, as the
//! leaves of one tree.
//!
//! Signatures are checked in proofs of their own
//! ([`crate::signature`]), each of up to [`SLOTS`] of them, which say
//! nothing of any block: they are made as the signatures arrive. What
//! such a proof is of is the root of the tree over its entries, a slot
//! with none being zeros. Proofs of proofs join four roots into one
//! ([`node_root`]), level after level, and the root of the last is the
//! set's.
//!
//! The tree is a set to whoever reads it. Where a transaction needs a
//! signature its proof shows the entry's path to the root
//! ([`Path`]); an entry nobody asks for is no harm, so a proof made for
//! transactions that have since gone into another's block still serves
//! for the rest. Every node is the hash of its two children in a domain
//! of its own, so the tree is one of pairs from an entry to the root,
//! however the proofs were grouped.

use crate::alg::{Alg, halves};
use crate::field::{F, as_bytes};
use crate::hash::{DOM_SIGNED_NODE, Digest, EMPTY, hash_domain};
use crate::sym::{Shared, Sym};

/// Entries a signature proof has room for, as a power of two.
pub const LOG_SLOTS: usize = 7;
pub const SLOTS: usize = 1 << LOG_SLOTS;
/// Roots a proof of proofs joins.
pub const FAN: usize = 4;
/// Levels of proofs of proofs over the signature proofs.
pub const NODE_LEVELS: usize = 7;
/// Pairs from an entry to the set's root.
pub const DEPTH: usize = LOG_SLOTS + 2 * NODE_LEVELS;

/// A node, from its two children.
pub fn pair(left: &Digest, right: &Digest) -> Digest {
    hash_domain(DOM_SIGNED_NODE, &[&left[..], right].concat())
}

/// The roots of the trees of nothing: `[h]` is the root of a tree of
/// `2^h` empty slots.
pub fn empty_roots() -> [Digest; DEPTH + 1] {
    let mut roots = [EMPTY; DEPTH + 1];
    for h in 0..DEPTH {
        roots[h + 1] = pair(&roots[h], &roots[h]);
    }
    roots
}

/// The root over `leaves`, a power of two of them.
fn root(leaves: &[Digest]) -> Digest {
    let mut level = leaves.to_vec();
    while level.len() > 1 {
        level = level.chunks_exact(2).map(|p| pair(&p[0], &p[1])).collect();
    }
    level[0]
}

/// The root of the tree over one signature proof's entries: the slots
/// after the last entry are empty.
pub fn segment_root(entries: &[Digest]) -> Digest {
    assert!(entries.len() <= SLOTS);
    let mut leaves = entries.to_vec();
    leaves.resize(SLOTS, EMPTY);
    root(&leaves)
}

/// The root of a node over four roots.
pub fn node_root(children: &[Digest; FAN]) -> Digest {
    root(children)
}

/// A path through the tree: the leaf's place and its siblings, the
/// lowest first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path {
    pub leaf: u64,
    pub siblings: Vec<Digest>,
}

impl Path {
    /// The root the path reaches from `entry`.
    pub fn root(&self, entry: &Digest) -> Digest {
        let mut node = *entry;
        for (level, sibling) in self.siblings.iter().enumerate() {
            node = if self.leaf >> level & 1 == 0 { pair(&node, sibling) } else { pair(sibling, &node) };
        }
        node
    }
}

/// The tree over `leaves` (a power of two of them), kept whole: for
/// whoever must show paths.
pub struct Tree {
    /// The root at 1, node `i`'s children at `2i` and `2i + 1`.
    nodes: Vec<Digest>,
}

impl Tree {
    pub fn new(leaves: &[Digest]) -> Tree {
        let n = leaves.len();
        assert!(n.is_power_of_two());
        let mut nodes = vec![EMPTY; 2 * n];
        nodes[n..].copy_from_slice(leaves);
        for i in (1..n).rev() {
            nodes[i] = pair(&nodes[2 * i], &nodes[2 * i + 1]);
        }
        Tree { nodes }
    }

    pub fn root(&self) -> Digest {
        self.nodes[1]
    }

    pub fn path(&self, leaf: usize) -> Path {
        let mut at = self.nodes.len() / 2 + leaf;
        let mut siblings = Vec::new();
        while at > 1 {
            siblings.push(self.nodes[at ^ 1]);
            at >>= 1;
        }
        Path { leaf: leaf as u64, siblings }
    }
}

/// A subtree as a circuit's arithmetic holds it: its root, or that it
/// is empty, which costs no row.
#[derive(Clone)]
enum Held {
    Empty,
    Root([Sym; 2]),
}

/// The root over `leaves` (given, then empty ones to `2^height`), by
/// the hash table's rows and the machine's: a row a pair that is not of
/// two empty trees.
fn root_into(cx: &Shared, leaves: &[[Sym; 2]], height: usize) -> [Sym; 2] {
    assert!(!leaves.is_empty() && leaves.len() <= 1 << height);
    let empty = empty_roots();
    let mut level: Vec<Held> = leaves.iter().cloned().map(Held::Root).collect();
    level.resize(1 << height, Held::Empty);
    for below in &empty[..height] {
        let of = |held: &Held| match held {
            Held::Root(root) => root.clone(),
            Held::Empty => halves(below).map(|x| cx.constant(x)),
        };
        let join = |p: &[Held]| {
            if matches!(p, [Held::Empty, Held::Empty]) {
                return Held::Empty;
            }
            let children: Vec<Sym> = p.iter().flat_map(&of).collect();
            let values: Vec<F> = children.iter().map(Sym::value).collect();
            let (data, out) = cx.with(|c| c.trace.digest(DOM_SIGNED_NODE, &values));
            for ((at, value), child) in data.iter().zip(&values).zip(&children) {
                assert!(cx.outside(*at, *value).is(child));
            }
            let digest = halves(&hash_domain(DOM_SIGNED_NODE, &as_bytes(&values)));
            Held::Root([cx.outside(out[0], digest[0]), cx.outside(out[1], digest[1])])
        };
        level = level.chunks_exact(2).map(join).collect();
    }
    match level.swap_remove(0) {
        Held::Root(root) => root,
        Held::Empty => unreachable!("a tree with a leaf"),
    }
}

/// [`segment_root`], by rows.
pub fn segment_root_into(cx: &Shared, entries: &[[Sym; 2]]) -> [Sym; 2] {
    root_into(cx, entries, LOG_SLOTS)
}

/// [`pair`] of two roots, by rows.
pub fn pair_into(cx: &Shared, children: &[[Sym; 2]; 2]) -> [Sym; 2] {
    root_into(cx, children, 1)
}

/// The root of the tree of `2^to` slots whose first `2^from` are the
/// tree of root `root` and whose others are empty.
pub fn lift(root: &Digest, from: usize, to: usize) -> Digest {
    let empty = empty_roots();
    (from..to).fold(*root, |node, level| pair(&node, &empty[level]))
}

/// [`lift`], by rows: a row a level.
pub fn lift_into(cx: &Shared, root: &[Sym; 2], from: usize, to: usize) -> [Sym; 2] {
    let empty = empty_roots();
    let mut node = root.clone();
    for below in &empty[from..to] {
        let children: Vec<Sym> = node.iter().cloned().chain(halves(below).map(|x| cx.constant(x))).collect();
        let values: Vec<F> = children.iter().map(Sym::value).collect();
        let (data, out) = cx.with(|c| c.trace.digest(DOM_SIGNED_NODE, &values));
        for ((at, value), child) in data.iter().zip(&values).zip(&children) {
            assert!(cx.outside(*at, *value).is(child));
        }
        let digest = halves(&hash_domain(DOM_SIGNED_NODE, &as_bytes(&values)));
        node = [cx.outside(out[0], digest[0]), cx.outside(out[1], digest[1])];
    }
    node
}

/// [`node_root`], by rows.
pub fn node_root_into(cx: &Shared, children: &[[Sym; 2]; FAN]) -> [Sym; 2] {
    root_into(cx, children, 2)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sym::tests::proven;

    fn digests(n: usize, seed: u8) -> Vec<Digest> {
        (0..n).map(|i| hash_domain(DOM_SIGNED_NODE, &[seed, i as u8])).collect()
    }

    #[test]
    fn a_path_reaches_the_root_and_no_other() {
        let entries = digests(5, 1);
        let mut leaves = entries.clone();
        leaves.resize(SLOTS, EMPTY);
        let tree = Tree::new(&leaves);
        assert_eq!(tree.root(), segment_root(&entries));
        for (i, entry) in entries.iter().enumerate() {
            let path = tree.path(i);
            assert_eq!((path.siblings.len(), path.root(entry)), (LOG_SLOTS, tree.root()));
            assert_ne!(path.root(&entries[(i + 1) % 5]), tree.root());
            assert_ne!(Path { leaf: path.leaf ^ 1, ..path.clone() }.root(entry), tree.root());
        }
        // A set of nothing, and four roots as one: the same pairs.
        assert_eq!(segment_root(&[]), empty_roots()[LOG_SLOTS]);
        let roots: [Digest; FAN] = std::array::from_fn(|i| segment_root(&digests(3, i as u8)));
        let all: Vec<Digest> = (0..FAN)
            .flat_map(|i| {
                let mut leaves = digests(3, i as u8);
                leaves.resize(SLOTS, EMPTY);
                leaves
            })
            .collect();
        assert_eq!(node_root(&roots), Tree::new(&all).root());
    }

    #[test]
    fn the_roots_are_made_by_rows() {
        let cx = Shared::new();
        let entries = digests(5, 2);
        let held: Vec<[Sym; 2]> = entries.iter().map(|d| halves(d).map(|x| cx.input(x))).collect();
        let before = cx.with(|c| c.trace.rows.len());
        let root = segment_root_into(&cx, &held);
        assert_eq!([root[0].value(), root[1].value()], halves(&segment_root(&entries)));
        // Five entries: four pairs with an entry in them at the bottom
        // (one of them with an empty slot), and so on up; not 127.
        assert_eq!(cx.with(|c| c.trace.rows.len()) - before, 3 + 2 + 1 + 4);
        let roots: [Digest; FAN] = std::array::from_fn(|i| segment_root(&digests(2, i as u8)));
        let node = node_root_into(&cx, &roots.map(|d| halves(&d).map(|x| cx.input(x))));
        assert_eq!([node[0].value(), node[1].value()], halves(&node_root(&roots)));
        cx.state(&[root, node].concat());
        assert!(proven(cx).0);
    }
}
