//! Part of a Merkle tree: the paths of some leaves, changed in memory.
//!
//! A block's proof shows the state changing a leaf at a time: this
//! output removed, that one added, each against the tree as the changes
//! before it left it. The store applies a block in one pass and keeps no
//! state in between, and has no need to; whoever proves a block does.
//!
//! So the prover takes from the state, as it is before the block, the
//! path of every leaf the block will touch ([`Partial::load`]), and
//! works on those alone: [`Partial::set`] changes a leaf and every node
//! above it, [`Partial::path`] is a leaf's path as the changes so far
//! have left it. The nodes of the paths loaded are all the tree there
//! is here, and all that those changes and those paths need.
//!
//! It is the prover's, not the node's: it holds forty-two nodes for
//! each leaf loaded.

use std::collections::HashMap;

use crate::hash::Digest;
use crate::ledger::state_node as compress;

/// Part of a tree of `H` levels: its root is the node of level `H`.
#[derive(Clone)]
pub struct Partial<const H: usize> {
    /// The nodes known, by level and index there.
    nodes: HashMap<(u8, u64), Digest>,
}

impl<const H: usize> Default for Partial<H> {
    fn default() -> Self {
        Partial { nodes: HashMap::new() }
    }
}

impl<const H: usize> Partial<H> {
    pub fn new() -> Partial<H> {
        Partial::default()
    }

    /// Takes in the leaf at `position` and its path, as the tree has
    /// them before any change: every path is loaded before the first
    /// [`Partial::set`]. Paths of one tree agree where they meet.
    pub fn load(&mut self, position: u64, leaf: &Digest, siblings: &[Digest; H]) {
        let mut node = *leaf;
        for (level, sibling) in siblings.iter().enumerate() {
            let index = position >> level;
            let known = *self.nodes.entry((level as u8, index)).or_insert(node);
            debug_assert_eq!(known, node, "paths of one tree agree");
            self.nodes.entry((level as u8, index ^ 1)).or_insert(*sibling);
            node = if index & 1 == 1 { compress(sibling, &node) } else { compress(&node, sibling) };
        }
        let known = *self.nodes.entry((H as u8, 0)).or_insert(node);
        debug_assert_eq!(known, node, "paths of one tree lead to one root");
    }

    /// The root, as the changes so far have left it. `None` before any
    /// path is loaded.
    pub fn root(&self) -> Option<Digest> {
        self.nodes.get(&(H as u8, 0)).copied()
    }

    /// The leaf at `position`, which must be one loaded.
    pub fn leaf(&self, position: u64) -> Digest {
        self.nodes[&(0, position)]
    }

    /// The path of the leaf at `position`, which must be one loaded.
    pub fn path(&self, position: u64) -> [Digest; H] {
        core::array::from_fn(|level| self.nodes[&(level as u8, (position >> level) ^ 1)])
    }

    /// Puts `leaf` at `position`, the tree's first empty one, whose path
    /// was loaded or which follows a leaf put so: every position from
    /// it on is empty, so what is to the right of its path is nothing.
    pub fn append(&mut self, position: u64, leaf: &Digest, empty: &[Digest]) {
        let mut node = *leaf;
        for (level, empty) in empty[..H].iter().enumerate() {
            let index = position >> level;
            self.nodes.insert((level as u8, index), node);
            let sibling = match index & 1 {
                1 => self.nodes[&(level as u8, index ^ 1)],
                _ => *self.nodes.entry((level as u8, index ^ 1)).or_insert(*empty),
            };
            node = if index & 1 == 1 { compress(&sibling, &node) } else { compress(&node, &sibling) };
        }
        self.nodes.insert((H as u8, 0), node);
    }

    /// The nodes to the left of `position`'s path, the lowest first: one
    /// at each level the position has a bit at. They must be known:
    /// the position's path was loaded, or it follows a leaf put by
    /// [`Partial::append`].
    pub fn frontier(&self, position: u64) -> Vec<Digest> {
        (0..H)
            .filter(|level| position >> level & 1 == 1)
            .map(|level| self.nodes[&(level as u8, (position >> level) ^ 1)])
            .collect()
    }

    /// Makes the leaf at `position`, which must be one loaded, `leaf`.
    pub fn set(&mut self, position: u64, leaf: &Digest) {
        let mut node = *leaf;
        for level in 0..H {
            let index = position >> level;
            self.nodes.insert((level as u8, index), node);
            let sibling = self.nodes[&(level as u8, index ^ 1)];
            node = if index & 1 == 1 { compress(&sibling, &node) } else { compress(&node, &sibling) };
        }
        self.nodes.insert((H as u8, 0), node);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::sparse::{EMPTY, root, root_of_path, root_with_path};
    use crate::test_util::Rng;

    /// Leaves changed one after another through their paths alone give
    /// the roots and the paths of the whole tree changed the same way.
    #[test]
    fn changes_through_paths_are_the_trees() {
        const H: usize = 12;
        let mut rng = Rng::new(0x9a47);
        let digest = |rng: &mut Rng| -> Digest { rng.digest() };
        // The tree: some leaves of 4096.
        let mut leaves: std::collections::BTreeMap<u64, Digest> =
            (0..300).map(|_| (rng.next_u64() % (1 << H), digest(&mut rng))).collect();
        let whole = |leaves: &std::collections::BTreeMap<u64, Digest>, at: u64| {
            let mut nodes: Vec<(u64, Digest)> = leaves.iter().map(|(p, d)| (*p, *d)).collect();
            let mut path = [EMPTY; H];
            let r = root_with_path(0, H, &mut nodes, Some((at, &mut path)));
            (r, path)
        };
        // Those to be touched: some there, some empty, two neighbours.
        let mut touched: Vec<u64> = leaves.keys().copied().step_by(9).collect();
        touched.extend((0..20).map(|_| rng.next_u64() % (1 << H)));
        touched.extend([leaves.keys().next().unwrap() ^ 1, 0, (1 << H) - 1]);
        let mut partial = Partial::<H>::new();
        assert_eq!(partial.root(), None);
        for p in &touched {
            let (_, path) = whole(&leaves, *p);
            partial.load(*p, &leaves.get(p).copied().unwrap_or(EMPTY), &path);
        }
        let before = root(0, H, &mut leaves.iter().map(|(p, d)| (*p, *d)).collect::<Vec<_>>());
        assert_eq!(partial.root(), Some(before));
        // Changed in an order of its own, some twice, some emptied.
        for round in 0..3 {
            for (i, p) in touched.iter().enumerate().rev() {
                let (_, path) = whole(&leaves, *p);
                assert_eq!(partial.path(*p), path, "the path of {p} before its change");
                assert_eq!(partial.leaf(*p), leaves.get(p).copied().unwrap_or(EMPTY));
                let new = if (i + round) % 4 == 0 { EMPTY } else { digest(&mut rng) };
                partial.set(*p, &new);
                match new == EMPTY {
                    true => leaves.remove(p),
                    false => leaves.insert(*p, new),
                };
                let (r, path) = whole(&leaves, *p);
                assert_eq!(partial.root(), Some(r));
                assert_eq!(root_of_path(*p, &new, &path), r);
            }
        }
        assert_ne!(partial.root(), Some(before));
    }
}
