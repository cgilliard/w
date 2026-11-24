//! The hashes of a sparse Merkle tree, computed from the nodes that are
//! not empty.
//!
//! The outputs' tree is binary: a node is the hash of its two children
//! ([`crate::ledger::state_node`]), an empty leaf is the zero digest,
//! and an empty subtree of each height has one hash, known beforehand
//! ([`empty`]). So the root of any subtree follows from its nonempty
//! nodes at some level below, however few they are and however far
//! apart: here it is computed from just those, level by level.
//!
//! Nothing is allocated: the nodes are combined in the caller's slice.

use crate::hash::Digest;
use crate::ledger::{OUTPUTS_HEIGHT, empty_roots, state_node};

/// The height of the outputs' tree.
pub const HEIGHT: usize = OUTPUTS_HEIGHT;

/// An empty leaf.
pub const EMPTY: Digest = crate::hash::EMPTY;

/// The hash of an empty subtree of `height` levels: `EMPTY` at height 0,
/// and the node over two of the height below at each above.
pub fn empty(height: usize) -> &'static Digest {
    &empty_roots()[height]
}

/// The root of the state with no output and no name: the outputs'
/// root with the names' ([`crate::registry::state_root`]).
pub fn empty_state() -> Digest {
    crate::registry::state_root(empty(HEIGHT), &crate::name::empty_root())
}

/// Digests of an output's path to the state's root: the siblings in the
/// outputs' tree, the lowest first, and then the names' root.
pub const STATE_HEIGHT: usize = HEIGHT + 1;

/// The state's root a path of an output leads to: from the leaf at
/// `position` up the outputs' tree, and that root with the names'.
pub fn root_of_state_path(position: u64, leaf: &Digest, path: &[Digest; STATE_HEIGHT]) -> Digest {
    let outputs = root_of_path(position, leaf, &path[..STATE_HEIGHT - 1]);
    crate::registry::state_root(&outputs, &path[STATE_HEIGHT - 1])
}

/// The root of a subtree, from its nonempty nodes at a level below.
///
/// `nodes` are `(index, hash)` at `level` (a leaf is level 0; the node of
/// index `i` at level `l` covers the positions `i << l` and up), ascending
/// and distinct, all under one node at level `top`; the result is that
/// node's hash. With no nodes it is the empty subtree's. The slice is
/// used as scratch.
pub fn root(level: usize, top: usize, nodes: &mut [(u64, Digest)]) -> Digest {
    root_with_path(level, top, nodes, None)
}

/// As [`root`], and also the path of the node of index `path.0` at
/// `level` (which need not be one of `nodes`): its sibling's hash at each
/// level from `level` up to `top - 1` is written to `path.1`, which has
/// `top - level` entries.
pub fn root_with_path(
    level: usize,
    top: usize,
    nodes: &mut [(u64, Digest)],
    mut path: Option<(u64, &mut [Digest])>,
) -> Digest {
    debug_assert!(level <= top && top <= HEIGHT);
    debug_assert!(nodes.windows(2).all(|w| w[0].0 < w[1].0), "nodes ascend");
    debug_assert!(nodes.iter().all(|n| n.0 >> (top - level) == nodes[0].0 >> (top - level)), "one subtree");
    if let Some((_, siblings)) = &path {
        debug_assert_eq!(siblings.len(), top - level);
    }
    let mut n = nodes.len();
    for l in level..top {
        if let Some((index, siblings)) = &mut path {
            let want = *index ^ 1;
            siblings[l - level] = match nodes[..n].binary_search_by_key(&want, |x| x.0) {
                Ok(i) => nodes[i].1,
                Err(_) => *empty(l),
            };
            *index >>= 1;
        }
        n = level_up(l, &mut nodes[..n]);
    }
    if n == 0 { *empty(top) } else { nodes[0].1 }
}

/// One level up: the nonempty nodes of level `l` (ascending) are
/// replaced, in place, by their parents at the level above, a node with
/// no sibling paired with the empty subtree's hash. Returns how many
/// parents there are.
pub fn level_up(l: usize, nodes: &mut [(u64, Digest)]) -> usize {
    let n = nodes.len();
    // The nodes of this level are read from `r` and their parents
    // written from `w`, never ahead of what is still to be read: a
    // parent takes at least one node.
    let (mut r, mut w) = (0, 0);
    while r < n {
        let (i, d) = nodes[r];
        let (left, right) = if i & 1 == 1 {
            (*empty(l), d)
        } else if r + 1 < n && nodes[r + 1].0 == i + 1 {
            r += 1;
            (d, nodes[r].1)
        } else {
            (d, *empty(l))
        };
        r += 1;
        nodes[w] = (i >> 1, state_node(&left, &right));
        w += 1;
    }
    w
}

/// The root a path leads to: the node of index `index` at the path's
/// first level, hashed with each sibling in turn.
pub fn root_of_path(mut index: u64, node: &Digest, siblings: &[Digest]) -> Digest {
    let mut d = *node;
    for s in siblings {
        d = if index & 1 == 1 { state_node(s, &d) } else { state_node(&d, s) };
        index >>= 1;
    }
    d
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    /// The definition: a node is the compression of its two halves, an
    /// absent leaf is `EMPTY`.
    fn naive(level: usize, top: usize, index: u64, nodes: &[(u64, Digest)]) -> Digest {
        // `index` is the node's at `top`; its nodes at `level` are those
        // whose index begins with it.
        let under: Vec<(u64, Digest)> = nodes.iter().copied().filter(|n| n.0 >> (top - level) == index).collect();
        // An empty subtree's hash, not from the table: by the definition,
        // to check the table.
        let empty_of = |height: usize| (0..height).fold(EMPTY, |d, _| state_node(&d, &d));
        if top == level {
            return under.first().map_or(empty_of(level), |n| n.1);
        }
        if under.is_empty() {
            return empty_of(top);
        }
        state_node(&naive(level, top - 1, 2 * index, &under), &naive(level, top - 1, 2 * index + 1, &under))
    }

    fn digest(rng: &mut Rng) -> Digest {
        rng.digest()
    }

    #[test]
    fn empty_subtrees() {
        assert_eq!(*empty(0), EMPTY);
        assert_eq!(*empty(1), state_node(&EMPTY, &EMPTY));
        assert_eq!(*empty(41), state_node(empty(40), empty(40)));
        for (level, top) in [(0, 0), (0, 7), (5, 41), (40, 41)] {
            assert_eq!(root(level, top, &mut []), *empty(top));
        }
        // A lone node at its own level is the root.
        let d = [9u8; 32];
        assert_eq!(root(3, 3, &mut [(77, d)]), d);
    }

    /// Any set of nodes, dense or sparse, at any level, under any top:
    /// the root is the definition's.
    #[test]
    fn roots_are_the_definitions() {
        let mut rng = Rng::new(0x5a45);
        for round in 0..if cfg!(debug_assertions) { 60 } else { 600 } {
            let height = 1 + rng.next_u64() as usize % 9;
            let level = rng.next_u64() as usize % 20;
            let top = level + height;
            let parent = rng.next_u64() % (1 << (41 - top.min(41)));
            let slots = 1u64 << height;
            // From empty to full, by rounds.
            let fill = match round % 6 {
                0 => 0,
                1 => 1,
                2 => slots,
                3 => slots.min(3),
                _ => 1 + rng.next_u64() % slots,
            };
            let mut picked: Vec<u64> = (0..slots).collect();
            for i in 0..fill as usize {
                let j = i + rng.next_u64() as usize % (slots as usize - i);
                picked.swap(i, j);
            }
            picked.truncate(fill as usize);
            picked.sort_unstable();
            let nodes: Vec<(u64, Digest)> = picked.iter().map(|s| (parent << height | s, digest(&mut rng))).collect();
            let want = naive(level, top, parent, &nodes);
            assert_eq!(root(level, top, &mut nodes.clone()), want, "round {round}: {fill} of {slots} at level {level}");

            // And every path leads to it: of a node present, and of one absent.
            for target in
                [nodes.first().map(|n| n.0), Some(parent << height | (rng.next_u64() % slots))].into_iter().flatten()
            {
                let mut siblings = vec![EMPTY; height];
                let got = root_with_path(level, top, &mut nodes.clone(), Some((target, &mut siblings)));
                assert_eq!(got, want);
                let at = nodes.iter().find(|n| n.0 == target).map_or(*empty(level), |n| n.1);
                assert_eq!(root_of_path(target, &at, &siblings), want, "round {round}: path of {target}");
                // Another node there does not.
                let other = digest(&mut rng);
                assert_ne!(root_of_path(target, &other, &siblings), want);
            }
        }
    }

    /// Few leaves under a tall tree: the whole of the outputs' half.
    #[test]
    fn a_tall_sparse_tree() {
        let mut rng = Rng::new(0x7a11);
        let positions = [0u64, 1, 2, 77, 1 << 20, (1 << 20) + 1, (1 << 40) - 1, 1 << 40, (1 << 41) - 1];
        let nodes: Vec<(u64, Digest)> = positions.iter().map(|p| (*p, digest(&mut rng))).collect();
        let want = naive(0, 41, 0, &nodes);
        assert_eq!(root(0, 41, &mut nodes.clone()), want);
        // Built in two steps, through the roots of the subtrees of 2^17
        // positions, it is the same.
        let mut parts: Vec<(u64, Digest)> = Vec::new();
        for chunk in nodes.chunk_by(|a, b| a.0 >> 17 == b.0 >> 17) {
            parts.push((chunk[0].0 >> 17, root(0, 17, &mut chunk.to_vec())));
        }
        assert_eq!(root(17, 41, &mut parts), want);
        // One leaf changed changes it; removed, it is as if never there.
        let mut changed = nodes.clone();
        changed[4].1[0] ^= 1;
        assert_ne!(root(0, 41, &mut changed), want);
        let mut fewer = nodes.clone();
        fewer.remove(3);
        assert_eq!(root(0, 41, &mut fewer.clone()), naive(0, 41, 0, &fewer));
    }
}
