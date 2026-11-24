//! Merkle trees over a codeword of field elements.
//!
//! A leaf is a run of consecutive elements, hashed as their bytes in the
//! domain of leaves; a node is its two children's digests hashed in the
//! domain of nodes ([`crate::hash`]). The number of leaves is a power of
//! two. Paths list siblings from the leaf's level upwards.
//!
//! A node is one compression. A leaf of `n` elements is `n / 4`, since a
//! block holds four elements.
//!
//! # Memory
//!
//! A tree ([`MerkleTree`]) is a prover's: every level, `2 n - 1` digests
//! for `n` leaves. A verifier holds no tree: an opening is checked from
//! the leaf and its path where they lie ([`verify`]).

use crate::field::{F, as_bytes};
use crate::hash::{DOM_LEAF, DOM_NODE, Digest, hash_domain, hash_domain_many};
use crate::parallel::par_chunks_mut;

pub struct MerkleTree {
    /// The leaves' hashes, then each level above, the root last.
    levels: Vec<Vec<Digest>>,
}

/// Digests a thread hashes before it looks for more work.
const RUN: usize = 1 << 10;

fn hash_level(domain: u32, input: &[u8], item_len: usize, n: usize) -> Vec<Digest> {
    let mut out = vec![[0u8; 32]; n];
    par_chunks_mut(&mut out, RUN, |i, o| {
        let at = i * RUN * item_len;
        hash_domain_many(domain, &input[at..at + o.len() * item_len], item_len, o);
    });
    out
}

impl MerkleTree {
    /// The tree of `data` in leaves of `leaf` elements.
    pub fn new(data: &[F], leaf: usize) -> MerkleTree {
        let n = data.len() / leaf;
        assert!(n.is_power_of_two() && n * leaf == data.len());
        MerkleTree::over(hash_level(DOM_LEAF, &as_bytes(data), leaf * F::BYTES, n))
    }

    /// The tree of `data` in leaves of `leaf` elements and one more
    /// from each of `more`: leaf `i` ends with their entries `i`.
    pub fn with_more(data: &[F], leaf: usize, more: &[&[F]]) -> MerkleTree {
        let n = data.len() / leaf;
        assert!(n.is_power_of_two() && n * leaf == data.len() && more.iter().all(|m| m.len() == n));
        let item = (leaf + more.len()) * F::BYTES;
        let mut hashes = vec![[0u8; 32]; n];
        par_chunks_mut(&mut hashes, RUN, |i, o| {
            let mut input = Vec::with_capacity(o.len() * item);
            for at in i * RUN..i * RUN + o.len() {
                input.extend_from_slice(&as_bytes(&data[at * leaf..(at + 1) * leaf]));
                for m in more {
                    input.extend_from_slice(&as_bytes(&m[at..at + 1]));
                }
            }
            hash_domain_many(DOM_LEAF, &input, item, o);
        });
        MerkleTree::over(hashes)
    }

    /// The tree over the leaves' hashes.
    fn over(leaves: Vec<Digest>) -> MerkleTree {
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let below = levels.last().unwrap();
            levels.push(hash_level(DOM_NODE, below.as_flattened(), 64, below.len() / 2));
        }
        MerkleTree { levels }
    }

    pub fn root(&self) -> Digest {
        self.levels.last().unwrap()[0]
    }

    /// Levels above the leaves: the length of a path.
    pub fn height(&self) -> usize {
        self.levels.len() - 1
    }

    /// The siblings from leaf `i` up.
    pub fn open(&self, mut i: usize) -> Vec<Digest> {
        let mut path = Vec::with_capacity(self.height());
        for level in &self.levels[..self.height()] {
            path.push(level[i ^ 1]);
            i >>= 1;
        }
        path
    }
}

/// Whether the leaf of elements `leaf`, at index `i`, is under `root` by
/// `path`.
pub fn verify(root: &Digest, leaf: &[F], mut i: usize, path: &[Digest]) -> bool {
    let mut d = hash_domain(DOM_LEAF, &as_bytes(leaf));
    let mut pair = [0u8; 64];
    for sibling in path {
        let (l, r) = if i & 1 == 0 { (&d, sibling) } else { (sibling, &d) };
        pair[..32].copy_from_slice(l);
        pair[32..].copy_from_slice(r);
        d = hash_domain(DOM_NODE, &pair);
        i >>= 1;
    }
    i == 0 && d == *root
}

/// One step up a tree for a batch of openings: `known` is the nodes of
/// a level that are known, in order of their indices, and `sibling` is
/// asked for the others' partners. Returns the level above the same way.
fn up(known: &[(usize, Digest)], mut sibling: impl FnMut(usize) -> Option<Digest>) -> Option<Vec<(usize, Digest)>> {
    let mut above = Vec::with_capacity(known.len());
    let mut at = 0;
    while at < known.len() {
        let (i, d) = known[at];
        let (l, r) = match known.get(at + 1) {
            // The node's partner is known too: no sibling is needed.
            Some((j, e)) if i & 1 == 0 && *j == i + 1 => {
                at += 1;
                (d, *e)
            }
            _ if i & 1 == 0 => (d, sibling(i + 1)?),
            _ => (sibling(i - 1)?, d),
        };
        let mut pair = [0u8; 64];
        pair[..32].copy_from_slice(&l);
        pair[32..].copy_from_slice(&r);
        above.push((i >> 1, hash_domain(DOM_NODE, &pair)));
        at += 1;
    }
    Some(above)
}

impl MerkleTree {
    /// The siblings the openings of the leaves `indices` (in order, each
    /// once) need between them: those no other opening gives, level by
    /// level from the leaves, in the order of the nodes they complete.
    pub fn open_batch(&self, indices: &[usize]) -> Vec<Digest> {
        let mut siblings = Vec::new();
        let mut known: Vec<(usize, Digest)> = indices.iter().map(|i| (*i, self.levels[0][*i])).collect();
        for level in &self.levels[..self.height()] {
            known = up(&known, |i| {
                siblings.push(level[i]);
                Some(level[i])
            })
            .expect("every sibling is in the tree");
        }
        siblings
    }
}

/// The hash of a leaf of elements.
pub fn leaf_hash(leaf: &[F]) -> Digest {
    hash_domain(DOM_LEAF, &as_bytes(leaf))
}

/// The root that the leaves of hashes `leaves`, at `indices` (in order,
/// each once) of a tree of `height`, come to with `siblings`: `None` if
/// the siblings are too few or too many. With it, the nodes computed.
pub fn batch_root(indices: &[usize], leaves: &[Digest], height: usize, siblings: &[Digest]) -> Option<(Digest, usize)> {
    if indices.is_empty() || indices.len() != leaves.len() || !indices.windows(2).all(|w| w[0] < w[1]) {
        return None;
    }
    if *indices.last().unwrap() >> height != 0 {
        return None;
    }
    let mut rest = siblings.iter();
    let mut known: Vec<(usize, Digest)> = indices.iter().copied().zip(leaves.iter().copied()).collect();
    let mut nodes = 0;
    for _ in 0..height {
        known = up(&known, |_| rest.next().copied())?;
        nodes += known.len();
    }
    (rest.next().is_none()).then_some((known[0].1, nodes))
}

/// Each leaf's own path, from a batch that verifies: for a prover that
/// must show each opening by itself, as a circuit does.
pub fn batch_paths(indices: &[usize], leaves: &[Digest], height: usize, siblings: &[Digest]) -> Vec<Vec<Digest>> {
    let mut rest = siblings.iter();
    let mut known: Vec<(usize, Digest)> = indices.iter().copied().zip(leaves.iter().copied()).collect();
    // Every node met at each level, known or given.
    let mut levels: Vec<Vec<(usize, Digest)>> = Vec::with_capacity(height);
    for _ in 0..height {
        let mut met = known.clone();
        known = up(&known, |i| {
            let d = *rest.next()?;
            met.push((i, d));
            Some(d)
        })
        .expect("the batch verifies");
        met.sort_unstable_by_key(|(i, _)| *i);
        levels.push(met);
    }
    indices
        .iter()
        .map(|i| {
            let find = |level: usize| {
                let want = (i >> level) ^ 1;
                let met = &levels[level];
                met[met.binary_search_by_key(&want, |(j, _)| *j).expect("the sibling was met")].1
            };
            (0..height).map(find).collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    #[test]
    fn openings_verify_and_others_do_not() {
        let mut rng = Rng(6);
        for (n, leaf) in [(1 << 12, 16), (64, 4), (32, 1), (16, 16)] {
            let data = rng.fs(n);
            let tree = MerkleTree::new(&data, leaf);
            assert_eq!(1 << tree.height(), n / leaf);
            for i in [0, 1, n / leaf - 1, n / leaf / 2].into_iter().filter(|i| *i < n / leaf) {
                let l = &data[i * leaf..(i + 1) * leaf];
                let path = tree.open(i);
                assert!(verify(&tree.root(), l, i, &path));
                assert!(!verify(&tree.root(), l, i ^ 1, &path) || n == leaf);
                let mut bad = l.to_vec();
                bad[0] += F::ONE;
                assert!(!verify(&tree.root(), &bad, i, &path));
            }
        }
    }

    #[test]
    fn a_leaf_is_not_a_node() {
        // Four elements are 64 bytes, as two digests are: the domains
        // keep a leaf from standing for a node.
        let mut rng = Rng(7);
        let data = rng.fs(8);
        let tree = MerkleTree::new(&data, 4);
        let leaves = [hash_domain(DOM_LEAF, &as_bytes(&data[..4])), hash_domain(DOM_LEAF, &as_bytes(&data[4..]))];
        assert_eq!(tree.root(), hash_domain(DOM_NODE, leaves.as_flattened()));
        assert_ne!(tree.root(), hash_domain(DOM_LEAF, leaves.as_flattened()));
    }

    #[test]
    fn a_batch_shares_its_siblings() {
        let mut rng = Rng(9);
        let data = rng.fs(64 * 4);
        let tree = MerkleTree::new(&data, 4);
        let hashes: Vec<Digest> = data.chunks(4).map(leaf_hash).collect();
        for (indices, siblings) in [
            (vec![0], 6),
            (vec![0, 1], 5),
            (vec![0, 63], 10),
            (vec![5, 6, 7, 40], 2 + 1 + 5 + 1),
            ((0..64).collect(), 0),
        ] {
            let leaves: Vec<Digest> = indices.iter().map(|i| hashes[*i]).collect();
            let batch = tree.open_batch(&indices);
            assert_eq!(batch.len(), siblings, "{indices:?}");
            assert_eq!(batch_root(&indices, &leaves, 6, &batch).map(|r| r.0), Some(tree.root()));
            // Each leaf's own path is the tree's.
            let paths = batch_paths(&indices, &leaves, 6, &batch);
            for (i, path) in indices.iter().zip(&paths) {
                assert_eq!(*path, tree.open(*i));
                assert!(verify(&tree.root(), &data[i * 4..(i + 1) * 4], *i, path));
            }
            // A leaf, a sibling or an index wrong; siblings missing or over.
            let mut bad = leaves.clone();
            bad[0][0] ^= 1;
            assert_ne!(batch_root(&indices, &bad, 6, &batch).map(|r| r.0), Some(tree.root()));
            if !batch.is_empty() {
                let mut bad = batch.clone();
                bad[0][0] ^= 1;
                assert_ne!(batch_root(&indices, &leaves, 6, &bad).map(|r| r.0), Some(tree.root()));
                assert_eq!(batch_root(&indices, &leaves, 6, &batch[1..]), None);
            }
            let over = [&batch[..], &[[0u8; 32]]].concat();
            assert_eq!(batch_root(&indices, &leaves, 6, &over), None);
            if indices.len() < 64 {
                let mut moved = indices.clone();
                *moved.last_mut().unwrap() ^= 1;
                moved.sort_unstable();
                moved.dedup();
                if moved.len() == indices.len() {
                    assert_ne!(batch_root(&moved, &leaves, 6, &batch).map(|r| r.0), Some(tree.root()));
                }
            }
        }
        // Indices out of order, twice, or past the tree.
        let h = |i: usize| hashes[i];
        assert_eq!(batch_root(&[3, 2], &[h(3), h(2)], 6, &[]), None);
        assert_eq!(batch_root(&[2, 2], &[h(2), h(2)], 6, &[]), None);
        assert_eq!(batch_root(&[64], &[h(0)], 6, &tree.open_batch(&[0])), None);
    }
}
