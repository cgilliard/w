//! The check of an XMSS signature, as rows of three tables proven
//! together: what a block's proof says of every signature in it.
//!
//! | | |
//! |---|---|
//! | [`crate::wots`] | the 67 chains: 1,005 rows |
//! | [`crate::recursion`] | the message digest, the leaf's three hashes, the path to the root, the entry: about 45 rows |
//! | [`crate::machine`] | that all of those are of one signature: about 500 rows |
//!
//! The hash table's rows send the elements they hash and the digests
//! they make; the chains' rows take the message digest from them and
//! send each chain's end, the public seed and the leaf's index. The
//! machine reads every one and finds them to agree: the ends hashed
//! into the leaf are the chains', every hash's head has the chains'
//! seed and leaf, the path is climbed by that leaf's index and the
//! index is within the tree.
//!
//! # The entry
//!
//! Nothing is asserted about whose signature it is. What the check
//! leaves is an **entry**: the hash of the root the path reached, the
//! seed, the height, the message and the leaf's index. "The key with
//! this root, seed and height signed this message with this leaf" is
//! then the entry being in the set of a block's entries, which whoever
//! spends looks up. A signature that is not the key's has an entry of
//! some other root, which is nobody's key.
//!
//! A check says nothing of any block: it is proven as soon as the
//! signature is known.

use crate::alg::{Alg, halves};
use crate::field::F;
use crate::hash::{DOM_SIGNED, DOM_XMSS_LEAF, DOM_XMSS_MSG, DOM_XMSS_TREE, Digest, hash_domain};
use crate::sym::{Shared, Sym};
use crate::wots::{Addresses, Chains};
use crate::xmss::{CHAINS, PK_PART, PublicKey, Signature, message_digest};

/// A hash's head as the two elements it is: the seed, and the leaf's
/// index with the height and the part above it.
fn head(pk: &PublicKey, leaf: u64, part: u32) -> [F; 2] {
    [F::from_bytes(&pk.pub_seed), F(leaf as u128 | (pk.height as u128) << 64 | (part as u128) << 96)]
}

/// The entry of the key's signature of `msg` with `leaf`.
pub fn entry(pk: &PublicKey, msg: &Digest, leaf: u64) -> Digest {
    let [r0, r1] = halves(&pk.root);
    let [m0, m1] = halves(msg);
    let elements = [r0, r1, F::from_bytes(&pk.pub_seed), F(pk.height as u128), m0, m1, F(leaf as u128)];
    hash_domain(DOM_SIGNED, &crate::field::as_bytes(&elements))
}

/// The check of `sig` as a signature of `msg` under a key of `pk`'s seed
/// and height, made rows of `cx` and of `chains`: the entry, as the
/// arithmetic holds it. It is [`entry`] of `pk` if the signature is
/// `pk`'s, and of another root if not. `None` for a signature that is
/// not of the key's height or names a leaf the tree has not.
pub fn check_into(cx: &Shared, chains: &mut Chains, pk: &PublicKey, msg: &Digest, sig: &Signature) -> Option<[Sym; 2]> {
    let height = pk.height();
    if sig.auth_path.len() != height || sig.index >> height != 0 {
        return None;
    }
    let leaf = sig.index;
    let read =
        |at: &[u32], values: &[F]| -> Vec<Sym> { at.iter().zip(values).map(|(at, x)| cx.outside(*at, *x)).collect() };
    let pair = |d: &Digest| halves(d);
    // A hash of elements by the hash table: what it took, and its digest.
    let hashed = |domain: u32, elements: &[F]| -> (Vec<Sym>, [Sym; 2]) {
        let (data, out) = cx.with(|c| c.trace.digest(domain, elements));
        let digest = hash_domain(domain, &crate::field::as_bytes(elements));
        let out = read(&out, &pair(&digest));
        (read(&data, elements), [out[0].clone(), out[1].clone()])
    };

    // The message digest, which the chains take off the bus themselves.
    let digest = message_digest(&pk.pub_seed, leaf, pk.height, &sig.randomizer, msg);
    let mut elements = head(pk, leaf, 0).to_vec();
    elements.extend(pair(&sig.randomizer).into_iter().chain(pair(msg)));
    let (taken, digest_at) = cx.with(|c| c.trace.digest(DOM_XMSS_MSG, &elements));
    let taken = read(&taken, &elements);

    // The chains, and what they send: the seed, the leaf, the ends.
    let at = cx.with(|c| Addresses {
        digest: digest_at,
        ends: (0..CHAINS).map(|_| [c.trace.reserve(), c.trace.reserve()]).collect(),
        key: [c.trace.reserve(), c.trace.reserve()],
    });
    let ends = chains.signature(&pk.pub_seed, leaf as u32, &digest, &sig.wots, &at);
    let seed = cx.outside(at.key[0], F::from_bytes(&pk.pub_seed));
    let index = cx.outside(at.key[1], F(leaf as u128));
    let end_values: Vec<F> = ends.iter().flat_map(pair).collect();
    let sent: Vec<Sym> = at.ends.iter().flatten().zip(&end_values).map(|(at, x)| cx.outside(*at, *x)).collect();
    // The key's height, which the prover gives: a bit for each level
    // below it, falling once and for good (the first is one, a height
    // being one at the least, and there is none at the tallest tree's
    // height), so that the level the bits fall at is the height. What a
    // signature is checked by is the same whatever its key's height: a
    // proof of signatures is of one program, of whichever keys.
    let (zero, one) = (cx.constant(F::ZERO), cx.constant(F::ONE));
    let below: Vec<Sym> = (0..=crate::xmss::MAX_HEIGHT)
        .map(|l| match l {
            0 => one.clone(),
            crate::xmss::MAX_HEIGHT => zero.clone(),
            _ => cx.input(F((l < height) as u128)),
        })
        .collect();
    for l in 1..crate::xmss::MAX_HEIGHT {
        assert!((below[l].clone() * below[l].clone() + below[l].clone()).is(&zero));
        assert!((below[l].clone() * (below[l - 1].clone() + one.clone())).is(&zero));
    }
    // Whether the height is `l`, for each it may be; and the height, as
    // the number's element.
    let is_height: Vec<Sym> =
        (1..=crate::xmss::MAX_HEIGHT).map(|l| (below[l - 1].clone() + below[l].clone()).kept()).collect();
    let height_said = (is_height.iter().enumerate())
        .fold(zero.clone(), |sum, (l, is)| sum + is.clone() * cx.constant(F(l as u128 + 1)))
        .kept();
    // A head is the chains' seed, and their leaf under the height and
    // the part.
    let is_head = |found: &[Sym], part: u32| {
        let above = height_said.clone() * cx.constant(F(1 << 64)) + cx.constant(F((part as u128) << 96));
        found[0].is(&seed) && found[1].is(&(index.clone() + above))
    };
    assert!(is_head(&taken, 0));
    let message = [taken[4].clone(), taken[5].clone()];

    // The leaf: two hashes of 31 ends, and one of the last five with
    // those two, which is the leaf the path climbs from.
    let mut parts: Vec<Sym> = Vec::new();
    for part in 0..2 {
        let mut elements = head(pk, leaf, part as u32).to_vec();
        elements.extend(&end_values[2 * part * PK_PART..2 * (part + 1) * PK_PART]);
        let (found, out) = hashed(DOM_XMSS_LEAF, &elements);
        assert!(is_head(&found, part as u32));
        for (x, end) in found[2..].iter().zip(&sent[2 * part * PK_PART..]) {
            assert!(x.is(end));
        }
        parts.extend(out);
    }
    let mut elements = head(pk, leaf, 2).to_vec();
    elements.extend(&end_values[4 * PK_PART..]);
    elements.extend(parts.iter().map(Sym::value));
    let (found, leaf_node) = hashed(DOM_XMSS_LEAF, &elements);
    assert!(is_head(&found, 2));
    for (x, expect) in found[2..].iter().zip(sent[4 * PK_PART..].iter().chain(&parts)) {
        assert!(x.is(expect));
    }
    // The path, a hash a level for as many levels as the tallest tree
    // has: the leaf's index a bit a level (none at or above the
    // height), each bit saying which side the node so far is on. The
    // root is the node at the height; the levels above it hash
    // nothing that counts.
    let mut node = leaf_node;
    let (mut said_index, mut root) = (zero.clone(), [zero.clone(), zero.clone()]);
    for l in 0..crate::xmss::MAX_HEIGHT {
        let bit = cx.input(F(((leaf >> l) & 1) as u128 * (l < height) as u128));
        assert!((bit.clone() * bit.clone() + bit.clone()).is(&zero));
        assert!((bit.clone() * (below[l].clone() + one.clone())).is(&zero));
        said_index = said_index + bit.clone() * cx.constant(F(1 << l));
        let sibling = pair(sig.auth_path.get(l).unwrap_or(&[0; 32])).map(|x| cx.input(x));
        // The node on the left if the bit is none, the sibling if it is
        // one; and the other on the right.
        let sides: Vec<Sym> = (0..4)
            .map(|k| {
                let (own, other) = (node[k % 2].clone(), sibling[k % 2].clone());
                let turned = (own.clone() + other.clone()) * bit.clone();
                (turned + if k < 2 { own } else { other }).kept()
            })
            .collect();
        let values: Vec<F> = sides.iter().map(Sym::value).collect();
        let (found, above) = hashed(DOM_XMSS_TREE, &values);
        for (x, expect) in found.iter().zip(&sides) {
            assert!(x.is(expect));
        }
        node = above;
        for (half, sum) in root.iter_mut().enumerate() {
            *sum = (sum.clone() + is_height[l].clone() * node[half].clone()).kept();
        }
    }
    assert!(said_index.is(&index));

    // The entry: of the root reached.
    let said = [root[0].clone(), root[1].clone(), seed, height_said, message[0].clone(), message[1].clone(), index];
    let values: Vec<F> = said.iter().map(Sym::value).collect();
    let (found, out) = hashed(DOM_SIGNED, &values);
    for (x, expect) in found.iter().zip(&said) {
        assert!(x.is(expect));
    }
    Some(out)
}

/// The checks of up to [`crate::signed::SLOTS`] signatures, each of a
/// key and a message, made rows of `cx` and of `chains` (a table for
/// each run of them, `per_table` signatures in each but the last), and
/// the computation said to be of their entries' root: the root.
pub fn segment_into(
    cx: &Shared,
    chains: &mut Vec<Chains>,
    signed: &[(PublicKey, Digest, Signature)],
    per_table: usize,
) -> Option<Digest> {
    assert!(!signed.is_empty() && signed.len() <= crate::signed::SLOTS);
    let mut entries = Vec::with_capacity(signed.len());
    for (i, (pk, msg, sig)) in signed.iter().enumerate() {
        if i % per_table == 0 {
            chains.push(Chains::default());
        }
        entries.push(check_into(cx, chains.last_mut().expect("pushed above"), pk, msg, sig)?);
    }
    let root = crate::signed::segment_root_into(cx, &entries);
    cx.state(&root);
    let digest: Vec<Digest> = signed.iter().map(|(pk, msg, sig)| entry(pk, msg, sig.index)).collect();
    Some(crate::signed::segment_root(&digest))
}

/// A proof of signatures: of one run of them ([`segment_into`]), with
/// the root of its entries; or of two such proofs joined
/// ([`node_into`]), with what that proof states.
pub enum Signed<'a> {
    Segment(&'a crate::proof::Proved, Digest),
    Node(&'a crate::proof::Proved, &'a [F]),
}

/// Elements a node of signatures states: the hash of what it rested
/// on, its root, and the root's level.
pub const NODE: usize = 5;

/// A level, as proofs hold it: the element `x` to that power, so that
/// a level up is a product (the field's sums are not the numbers').
pub fn level_element(level: usize) -> F {
    (0..level).fold(F::ONE, |p, _| p * F(2))
}

/// A proof of signatures as a circuit that verified it holds it: the
/// program it was verified against, what it rested on in turn (zeros
/// for a run of signatures), the root, and the root's level.
pub struct Verified {
    pub own: Vec<Sym>,
    pub below: Vec<Sym>,
    pub root: [Sym; 2],
    pub level: Sym,
}

impl Signed<'_> {
    /// The root, and the level of the tree it is of: `2^level` slots.
    pub fn root(&self) -> (Digest, usize) {
        match self {
            Signed::Segment(_, root) => (*root, crate::signed::LOG_SLOTS),
            Signed::Node(_, stated) => {
                let bytes = [stated[2].0.to_le_bytes(), stated[3].0.to_le_bytes()].concat();
                let level = (0..=crate::signed::DEPTH).find(|l| level_element(*l) == stated[4]);
                (bytes.try_into().expect("two elements"), level.unwrap_or(usize::MAX))
            }
        }
    }

    /// The proof's verification, made rows of `cx`.
    pub fn verify_into(
        &self,
        cx: &Shared,
        circuits: &crate::proof::Circuits,
        reader: &mut impl crate::structure::Reader<Sym>,
    ) -> Option<Verified> {
        match self {
            Signed::Segment(proof, root) => {
                let of = proof.verify_into(cx, circuits, reader)?;
                let said = cx.stated(&[of[2].clone(), of[3].clone()], &crate::alg::halves(root));
                Some(Verified {
                    own: of[..2].to_vec(),
                    below: vec![cx.constant(F::ZERO), cx.constant(F::ZERO)],
                    root: [said[0].clone(), said[1].clone()],
                    level: cx.constant(level_element(crate::signed::LOG_SLOTS)),
                })
            }
            Signed::Node(proof, stated) => {
                if stated.len() != NODE {
                    return None;
                }
                let of = proof.verify_into(cx, circuits, reader)?;
                let said = cx.stated(&[of[2].clone(), of[3].clone()], stated);
                Some(Verified {
                    own: of[..2].to_vec(),
                    below: said[..2].to_vec(),
                    root: [said[2].clone(), said[3].clone()],
                    level: said[4].clone(),
                })
            }
        }
    }
}

/// A computation, in `cx`, that verifies two proofs of signatures of
/// one level and states the tree over the two: what it states, by the
/// field. That is the hash of what the two were proofs of (their own
/// programs, and what those rested on), the root, and its level.
pub fn node_into(
    cx: &Shared,
    circuits: &crate::proof::Circuits,
    reader: &mut impl crate::structure::Reader<Sym>,
    children: [&Signed; 2],
) -> Option<Vec<F>> {
    let a = children[0].verify_into(cx, circuits, reader)?;
    let b = children[1].verify_into(cx, circuits, reader)?;
    assert!(a.level.is(&b.level));
    let below = cx.hashed(crate::hash::DOM_RESTED, &[a.own, a.below, b.own, b.below].concat());
    let root = crate::signed::pair_into(cx, &[a.root, b.root]);
    let level = a.level * cx.constant(F(2));
    let stated = [below.to_vec(), root.to_vec(), vec![level]].concat();
    cx.state(&stated);
    Some(stated.iter().map(Sym::value).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alg::statement;
    use crate::pcs::Params;
    use crate::proof::{Circuits, Proved, prove};
    use crate::reading::Deferred;
    use crate::structure::Direct;
    use crate::wots;
    use crate::xmss::SecretKey;

    /// A proof of `n` signatures a chain table, the tables of these
    /// sizes (as logs of rows), stating its entries' root: the proof and
    /// the root.
    fn segment(logs: &[usize], seed: usize, params: impl Fn(usize) -> Params) -> (Proved, Digest) {
        let cx = Shared::new();
        let (mut chains, mut entries, mut expect) = (Vec::new(), Vec::new(), Vec::new());
        for (t, log) in logs.iter().enumerate() {
            let mut table = Chains::default();
            let all = signed((1usize << log) / wots::ROWS);
            for (pk, msg, sig) in all.iter().skip(seed + t).chain(all.iter().take(seed + t)) {
                entries.push(check_into(&cx, &mut table, pk, msg, sig).unwrap());
                expect.push(entry(pk, msg, sig.index));
            }
            chains.push(table);
        }
        let n = entries.len().min(crate::signed::SLOTS);
        let root = crate::signed::segment_root(&expect[..n]);
        assert_eq!(cx.state(&crate::signed::segment_root_into(&cx, &entries[..n])), statement(&halves(&root)));
        let p = prove(cx, chains, params);
        assert!(p.holds && p.verifies());
        (p, root)
    }

    /// A circuit that verifies two proofs of signatures and states the
    /// tree over theirs: the computation, what it states, and the root.
    fn node(children: &[(Proved, Digest); 2], circuits: &Circuits) -> (Shared, Vec<F>, Digest) {
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let signed = [Signed::Segment(&children[0].0, children[0].1), Signed::Segment(&children[1].0, children[1].1)];
        let stated = node_into(&cx, circuits, &mut reader, [&signed[0], &signed[1]]).expect("the proofs verify");
        reader.settle(&circuits.all());
        (cx, stated, crate::signed::pair(&children[0].1, &children[1].1))
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn two_proofs_of_signatures_are_joined() {
        let params = |m: usize| Params::plain(m, 1, 4, 4);
        let children = [segment(&[11], 0, params), segment(&[11], 1, params)];
        assert_ne!(children[0].1, children[1].1);
        assert_eq!(children[0].0.program, children[1].0.program);
        let circuits = Circuits::new();
        let (cx, stated, root) = node(&children, &circuits);
        let joined = prove(cx, vec![], params);
        assert!(joined.holds && joined.verifies());
        assert_eq!(joined.statement(), statement(&stated));
        assert_eq!((&stated[2..4], stated[4]), (&halves(&root)[..], level_element(crate::signed::LOG_SLOTS + 1)));
        // And two of those: the tree of four proofs' entries, a level up.
        // A node and a run of signatures are not of one level.
        let node = Signed::Node(&joined, &stated);
        assert_eq!(node.root(), (root, crate::signed::LOG_SLOTS + 1));
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let top = node_into(&cx, &circuits, &mut reader, [&node, &node]).expect("the proofs verify");
        reader.settle(&circuits.all());
        assert!(cx.finish().asm.finish(128).holds);
        assert_eq!(&top[2..4], &halves(&crate::signed::pair(&root, &root))[..]);
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let leaf = Signed::Segment(&children[0].0, children[0].1);
        node_into(&cx, &circuits, &mut reader, [&node, &leaf]).expect("the proofs verify");
        reader.settle(&circuits.all());
        assert!(!cx.finish().asm.finish(128).holds);
        // One child's proof changed: the node's rows do not hold.
        let mut bad = children;
        bad[1].0.proof.tables[0].abc[1] += F::ONE;
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        if bad[1].0.verify_into(&cx, &circuits, &mut reader).is_some() {
            reader.settle(&circuits.all());
            assert!(!cx.finish().asm.finish(128).holds);
        }
    }

    /// What joining two proofs of signatures takes, at the chain's
    /// parameters.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn joining_timing() {
        let tables = std::env::var("TABLES").unwrap_or("16".into());
        let logs: Vec<usize> = tables.split(',').map(|x| x.parse().unwrap()).collect();
        let params = |m: usize| Params::proven(m, 2, crate::pcs::SECURITY);
        let children = [segment(&logs, 0, params), segment(&logs, 1, params)];
        let circuits = Circuits::new();
        let t = std::time::Instant::now();
        let (cx, ..) = node(&children, &circuits);
        let compiled = t.elapsed();
        let (hash, ops) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
        let joined = crate::sym::tests::prove_compiled(cx, params);
        assert!(joined.holds && joined.verifies());
        println!(
            "two proofs of signatures (2^{} elements, {:.2?}, {} KB each) joined: {hash} hash rows, {ops} operations \
             ({} machine rows used), compiled in {compiled:.2?}; 2^{} hash rows, 2^{} machine rows, 2^{} elements, \
             proven in {:.2?}, {} KB",
            children[0].0.params.m,
            children[0].0.proving,
            children[0].0.size() / 1000,
            joined.used,
            joined.rows[0].trailing_zeros(),
            joined.rows[1].trailing_zeros(),
            joined.params.m,
            joined.proving,
            joined.proof.size() / 1000,
        );
    }

    fn digest_of(words: &[u32]) -> Digest {
        crate::blake3::bytes(&std::array::from_fn::<u32, 8, _>(|i| words[i]))
    }

    /// Signatures of `n` keys, each of a message of its own.
    fn signed(n: usize) -> Vec<(PublicKey, Digest, Signature)> {
        let one = |i: usize| {
            let mut sk = SecretKey::generate_with_height(&[i as u8 + 1; 32], 3);
            sk.set_next_index(i as u64 % 8);
            let msg = [i as u8 ^ 0xC3; 32];
            let sig = sk.sign(&msg).unwrap();
            (sk.public_key(), msg, sig)
        };
        (0..n).map(one).collect()
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn signatures_are_checked_by_three_tables() {
        let (cx, mut chains) = (Shared::new(), Chains::default());
        let mut entries = Vec::new();
        let all = signed(2);
        for (pk, msg, sig) in &all {
            assert!(pk.verify(msg, sig));
            let found = check_into(&cx, &mut chains, pk, msg, sig).expect("a signature of the key's height");
            // The entry is the key's: the path reached its root.
            let expect = halves(&entry(pk, msg, sig.index));
            assert_eq!([found[0].value(), found[1].value()], expect);
            entries.extend(found);
        }
        let stated = cx.state(&entries);
        let expect: Vec<F> = all.iter().flat_map(|(pk, msg, sig)| halves(&entry(pk, msg, sig.index))).collect();
        assert_eq!(stated, statement(&expect));
        let p = prove(cx, vec![chains], |m| Params::plain(m, 1, 4, 4));
        assert!(p.holds && p.verifies());
        assert_eq!(digest_of(&p.public), stated);
    }

    /// Keys of trees of any height are checked by one program: a proof
    /// of signatures is the same whichever keys signed. The entry says
    /// the key's height, and a leaf's index is one its tree has.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn keys_of_any_height_are_checked_by_one_program() {
        let proved = |height: usize, leaf: u64| {
            let mut sk = SecretKey::generate_with_height(&[height as u8; 32], height);
            sk.set_next_index(leaf);
            let (pk, msg) = (sk.public_key(), [height as u8 ^ 0x5A; 32]);
            let sig = sk.sign(&msg).unwrap();
            let (cx, mut chains) = (Shared::new(), Chains::default());
            let found = check_into(&cx, &mut chains, &pk, &msg, &sig).expect("a signature of the key's height");
            assert_eq!([found[0].value(), found[1].value()], halves(&entry(&pk, &msg, leaf)));
            cx.state(&found);
            let p = prove(cx, vec![chains], |m| Params::plain(m, 1, 4, 4));
            assert!(p.holds && p.verifies(), "height {height}");
            p
        };
        let (short, plain, tall) = (proved(1, 1), proved(crate::xmss::PLAIN_HEIGHT, 11), proved(9, 300));
        assert_eq!((short.program, short.tables.clone()), (plain.program, plain.tables.clone()));
        assert_eq!((tall.program, tall.tables.clone()), (plain.program, plain.tables.clone()));
    }

    /// Whether what was compiled is rows that meet their tables'
    /// constraints; and, where the build is optimized, whether a proof
    /// of them verifies.
    fn shown(cx: Shared, chains: Vec<Chains>) -> bool {
        if cfg!(debug_assertions) {
            return crate::proof::holds(cx, chains, None);
        }
        let p = prove(cx, chains, |m| Params::plain(m, 1, 4, 4));
        p.holds && p.verifies()
    }

    /// Keys of trees of several heights, each checked by rows that hold
    /// and found to have the entry that is theirs.
    #[test]
    fn a_key_of_any_height_is_checked_by_rows_that_hold() {
        for (height, leaf) in [(1usize, 1u64), (3, 6), (5, 17)] {
            let mut sk = SecretKey::generate_with_height(&[height as u8; 32], height);
            sk.set_next_index(leaf);
            let (pk, msg) = (sk.public_key(), [height as u8 ^ 0x5A; 32]);
            let sig = sk.sign(&msg).unwrap();
            let (cx, mut chains) = (Shared::new(), Chains::default());
            let found = check_into(&cx, &mut chains, &pk, &msg, &sig).expect("a signature of the key's height");
            assert_eq!([found[0].value(), found[1].value()], halves(&entry(&pk, &msg, leaf)));
            cx.state(&found);
            assert!(shown(cx, vec![chains]), "height {height}");
        }
    }

    #[test]
    fn a_signature_that_is_not_the_key_s_has_another_entry() {
        let (pk, msg, sig) = signed(1).swap_remove(0);
        let expect = halves(&entry(&pk, &msg, sig.index));
        let found = |pk: &PublicKey, msg: &Digest, sig: &Signature| {
            let (cx, mut chains) = (Shared::new(), Chains::default());
            let e = check_into(&cx, &mut chains, pk, msg, sig)?;
            let values = [e[0].value(), e[1].value()];
            cx.state(&e);
            // The rows are a true check of something, whatever it is.
            assert!(shown(cx, vec![chains]));
            Some(values)
        };
        assert_eq!(found(&pk, &msg, &sig), Some(expect));
        // Another message, a value of a chain changed, a sibling changed:
        // each is checked, and is the signature of no key of this root.
        let mut other = msg;
        other[0] ^= 1;
        assert!(!pk.verify(&other, &sig));
        assert_ne!(found(&pk, &other, &sig), Some(expect));
        assert_ne!(found(&pk, &other, &sig), Some(halves(&entry(&pk, &other, sig.index))));
        let mut bad = sig.clone();
        bad.wots[7][3] ^= 1;
        assert_ne!(found(&pk, &msg, &bad), Some(expect));
        let mut bad = sig.clone();
        bad.auth_path[1][0] ^= 1;
        assert_ne!(found(&pk, &msg, &bad), Some(expect));
        // A leaf the tree has not, a path of another length: no check.
        let mut bad = sig.clone();
        bad.index += 8;
        assert!(found(&pk, &msg, &bad).is_none());
        bad = sig.clone();
        bad.auth_path.pop();
        assert!(found(&pk, &msg, &bad).is_none());
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn chains_in_several_tables_are_one_proof() {
        // Three signatures, their chains in two tables of unlike sizes.
        let cx = Shared::new();
        let mut chains = vec![Chains::default(), Chains::default()];
        let mut entries = Vec::new();
        for (i, (pk, msg, sig)) in signed(3).iter().enumerate() {
            entries.extend(check_into(&cx, &mut chains[i / 2], pk, msg, sig).unwrap());
        }
        let stated = cx.state(&entries);
        let p = prove(cx, chains, |m| Params::plain(m, 1, 4, 4));
        assert!(p.holds && p.verifies());
        assert_eq!((digest_of(&p.public), p.rows(crate::proof::Kind::Chains)), (stated, vec![2048, 1024]));
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_proof_of_signatures_is_verified_by_rows() {
        // A proof of two signatures' checks, its statement the root of
        // their entries; the verification of that proof compiled, stating
        // the same root, and proven.
        let (cx, mut chains) = (Shared::new(), Chains::default());
        let all = signed(2);
        let entries: Vec<[Sym; 2]> =
            all.iter().map(|(pk, msg, sig)| check_into(&cx, &mut chains, pk, msg, sig).unwrap()).collect();
        let root = crate::signed::segment_root_into(&cx, &entries);
        let stated = cx.state(&root);
        let expect: Vec<Digest> = all.iter().map(|(pk, msg, sig)| entry(pk, msg, sig.index)).collect();
        assert_eq!(stated, statement(&halves(&crate::signed::segment_root(&expect))));
        let params = |m: usize| Params::plain(m, 1, 4, 4);
        let inner = prove(cx, vec![chains], params);
        assert!(inner.holds && inner.verifies());
        let cx = Shared::new();
        let of = inner.verify_into(&cx, &Circuits::new(), &mut Direct).expect("the proof verifies");
        // What it verified: the programs' root, and the statement.
        let values: Vec<F> = of.iter().map(Sym::value).collect();
        assert_eq!(values, [halves(&inner.program), halves(&stated)].concat());
        cx.state(&of);
        assert!(crate::sym::tests::proven(cx).0);
    }

    /// What verifying a proof of signatures costs a circuit.
    #[test]
    #[ignore = "a count; run with --release --nocapture"]
    fn verifying_costs() {
        let tables = std::env::var("TABLES").unwrap_or("16,15".into());
        let logs: Vec<usize> = tables.split(',').map(|x| x.parse().unwrap()).collect();
        let cx = Shared::new();
        let mut chains = Vec::new();
        let mut entries = Vec::new();
        for log in &logs {
            let mut table = Chains::default();
            for (pk, msg, sig) in &signed((1usize << log) / wots::ROWS) {
                entries.push(check_into(&cx, &mut table, pk, msg, sig).unwrap());
            }
            chains.push(table);
        }
        let root = crate::signed::segment_root_into(&cx, &entries[..entries.len().min(crate::signed::SLOTS)]);
        cx.state(&root);
        let p = prove(cx, chains, |m| Params::proven(m, 2, crate::pcs::SECURITY));
        assert!(p.holds && p.verifies());
        let cx = Shared::new();
        let t = std::time::Instant::now();
        p.verify_into(&cx, &Circuits::new(), &mut Direct).unwrap();
        let (hash, ops) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
        let rows = cx.finish().asm.finish(128).inputs.len();
        println!(
            "{} signatures in 2^{} elements ({:.2?}, {} KB): its verifier is {hash} hash rows, {ops} operations, \
             2^{} machine rows; compiled in {:.2?}",
            entries.len(),
            p.params.m,
            p.proving,
            p.size() / 1000,
            rows.trailing_zeros(),
            t.elapsed()
        );
    }

    /// What a proof of many signatures takes, at the chain's parameters.
    /// `TABLES` is the chain tables' sizes as the logs of their rows,
    /// largest first: `17` is one table of 130 signatures, `15,15,15`
    /// three of 32.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn signatures_timing() {
        let tables = std::env::var("TABLES").unwrap_or("15,15,15".into());
        let logs: Vec<usize> = tables.split(',').map(|x| x.parse().unwrap()).collect();
        let cx = Shared::new();
        let mut chains = Vec::new();
        let mut entries = Vec::new();
        let mut n = 0;
        for log in &logs {
            let mut table = Chains::default();
            let fits = (1usize << log) / wots::ROWS;
            for (pk, msg, sig) in &signed(fits) {
                entries.extend(check_into(&cx, &mut table, pk, msg, sig).unwrap());
            }
            n += fits;
            chains.push(table);
        }
        cx.state(&entries[..entries.len().min(60)]);
        let p = prove(cx, chains, |m| Params::proven(m, 2, crate::pcs::SECURITY));
        assert!(p.holds && p.verifies());
        let logs: Vec<u32> = p.tables.iter().map(|(_, r)| r.trailing_zeros()).collect();
        println!(
            "{n} signatures, tables of 2^{logs:?} rows (largest first), 2^{} elements: \
             proven in {:.2?} ({:.0?} a signature), {} KB",
            p.params.m,
            p.proving,
            p.proving / n as u32,
            p.size() / 1000
        );
    }

    /// No word of the tables that check signatures holds up nothing,
    /// in their first rows: of the chains' table and the hashes' none at
    /// all can be changed unseen. Of the machine's, only what a row
    /// computes with (an operand that is multiplied by nothing, say):
    /// those are held to their values by what the tables send each
    /// other, which a table's own constraints say nothing of.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn no_word_of_a_signature_s_tables_is_left_to_the_prover() {
        use crate::proof::Kind;
        let (cx, mut chains) = (Shared::new(), Chains::default());
        let mut entries = Vec::new();
        for (pk, msg, sig) in &signed(2) {
            entries.extend(check_into(&cx, &mut chains, pk, msg, sig).unwrap());
        }
        cx.state(&entries);
        let (held, free) = crate::proof::audit(cx, vec![chains], None, 256);
        assert!(held);
        for (kind, row, word) in &free {
            assert!(*kind == Kind::Machine && *word < 16, "word {word} of row {row} of {kind:?} holds up nothing");
        }
        // (And some of the machine's are: the looking found something.)
        assert!(!free.is_empty());
    }
}
