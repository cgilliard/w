//! Spend policies: the conditions under which an output may be spent, for
//! multisig, HTLCs and eltoo payment channels (see `docs/ELTOO.md`).
//!
//! # Model
//!
//! An output's commitment is `H(policy ‖ amount)`. A plain output's policy
//! is the hash of its XMSS public key, as [`crate::output`] makes it; any
//! other policy is the root of a Merkle tree of [`Leaf`]s, each the
//! conjunction of up to [`LEAF_CONDS`] conditions.
//! Disjunction is separate leaves. A spend reveals one leaf, its index and
//! the sibling digests up to the root, with the data satisfying each
//! condition, to the block prover only: the chain sees the spent position
//! and nothing else, and a policy output is indistinguishable from a plain
//! one.
//!
//! | condition | satisfied when |
//! |---|---|
//! | `Thresh` | exactly `m` of the `n` listed key hashes sign, in `body` mode over the transaction's body hash (as plain inputs do) or in `rebindable` mode over `H(DOM_REBIND, channel ‖ state ‖ covered outputs)`, which does not name the position spent |
//! | `Hash` | the spender reveals `p` with [`hash_lock`]`(p)` equal to it |
//! | `After` | the block's height is at least it (CLTV) |
//! | `Older` | the block's height is at least the output's creation height plus it (CSV) |
//! | `State` | the spending transaction's state number exceeds it |
//! | `Outputs` | the spend's covered outputs (the transaction's first outputs, as many as the input says) are exactly the listed ones, commitment and memo slot (memo and amount) |
//!
//! The covered run is hashed once, [`covered_digest`], and serves both the
//! covenant (its digest is what the leaf holds) and the rebindable
//! message. A transaction has one such run, from its first output: the
//! inputs of one transaction that cover any cover the same, and the
//! transaction's id says how many ([`crate::ledger::Transaction`]).
//!
//! A rebindable signature for state `n` uses leaf index `n` of the signer's
//! key, so a stateful key never reuses a leaf within a channel and each
//! party can check the other's index.
//!
//! # Hashing
//!
//! The hashes are [`crate::conditions`]', which is what the proofs
//! compute: a condition is one block (its tag, a number or two, and a
//! digest: a threshold's keys hashed in a chain, a hash lock's hash, a
//! covenant's outputs hashed in a chain); a leaf is its conditions'
//! hashes in a chain; the tree's nodes hash pairs.
//!
//! The tree is [`POLICY_DEPTH`] deep, leaves padded with the empty
//! digest. State numbers are below `2^30`, and a rebindable
//! signature's leaf index.
//!
//! # Encoding
//!
//! All integers little-endian.
//!
//! ```text
//! leaf   := u8 n_conds, n_conds * cond
//! cond   := u8 0 | u8 mode (0 body, 1 rebindable) | [channel (32) if rebindable] | u8 m | u8 n | n * key hash (32)
//!         | u8 1 | hash (32)
//!         | u8 2 | u32 height
//!         | u8 3 | u32 age
//!         | u8 4 | u32 state
//!         | u8 5 | u8 k | k * (commitment (32) | memo slot (32))  (hashed into the leaf as its covered digest)
//! input  := u64 amount | u64 position | u8 leaf index | POLICY_DEPTH * sibling (32)
//!         | u32 state | u8 covered start | u8 covered count | leaf | per condition: witness
//! witness:= Thresh: u8 count, count * (u8 key, pubkey (49), signature)
//!         | Hash: preimage (32)
//!         | others: nothing
//! ```
//!
//! # Two forms
//!
//! What consensus does with a policy (decode it, hash it, check a spend)
//! is done on *views*: [`PolicyRef`], [`LeafRef`], [`CondRef`] and
//! [`PolicyInputRef`] borrow the encoded bytes and read conditions, keys
//! and signatures out of them where they lie. A view is made by reading
//! the bytes once, which checks the whole encoding (counts within bounds,
//! every element canonical, every signature whole), so what it hands out
//! afterwards cannot fail. A height, an age or a state number must be
//! below `2^30` to be read. Nothing is copied to the heap: checking a spend
//! as it arrived from the network allocates no memory, and holds one
//! signature at a time on the stack.
//!
//! The *owned* forms ([`Policy`], [`Leaf`], [`Cond`], [`PolicyInput`])
//! are for building: a wallet makes a policy from its parties' keys, a
//! spend from a policy, and adds signatures one party at a time. They
//! hold their lists in `Vec`s, encode to the bytes the views read, and
//! hash and check by way of the views, so each rule is written once.

use core::fmt;

use crate::codec::{DIGEST_BYTES, read_digest, read_u32, read_u64};
use crate::conditions;
use crate::error::Error;
use crate::hash::{DOM_COND, DOM_COVERED, DOM_OUT_ITEM, DOM_POLICY_LEAF, DOM_SIGNERS};
use crate::hash::{Digest, EMPTY, digest_from_bytes, digest_to_bytes, hash_domain};
use crate::output::{Commitment, Memo, Output, OutputList, key_commitment, pubkey_hash};
use crate::xmss::{PublicKey, Signature};

/// Conditions a leaf may hold at most.
pub const LEAF_CONDS: usize = 4;
/// Keys a threshold may list at most.
pub const MAX_KEYS: usize = 32;
/// Outputs a covenant may name at most.
pub const MAX_COVENANT: usize = 128;
/// Depth of the policy tree: up to `2^POLICY_DEPTH` leaves.
pub const POLICY_DEPTH: usize = conditions::DEPTH;
/// Leaves a policy may have at most.
pub const MAX_LEAVES: usize = 1 << POLICY_DEPTH;
/// State numbers are below `2^30`: a leaf index of a key.
pub const MAX_STATE: u32 = (1 << 30) - 1;
/// The heights and ages of timelocks are bounded as state numbers are.
pub const MAX_LOCK: u32 = (1 << 30) - 1;

const TAG_THRESH: u8 = 0;
const TAG_HASH: u8 = 1;
const TAG_AFTER: u8 = 2;
const TAG_OLDER: u8 = 3;
const TAG_STATE: u8 = 4;
const TAG_OUTPUTS: u8 = 5;

/// What a threshold's signatures cover.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// The transaction's body hash, as a plain input signs.
    Body,
    /// [`rebind_message`] for this channel: the state number and the
    /// covered outputs, never the position spent.
    Rebindable { channel: Digest },
}

// ---------------------------------------------------------------------------
// Hashes
// ---------------------------------------------------------------------------

/// The hash lock of a preimage.
pub fn hash_lock(preimage: &Digest) -> Digest {
    conditions::hash_lock(preimage)
}

/// The digest of outputs, commitment and memo slot each: each output's
/// hash as a block lists it ([`crate::ledger::Output::item`]), taken in
/// one after another.
fn covered_digest_of(outputs: impl Iterator<Item = (Commitment, Digest)>) -> Digest {
    outputs.fold(EMPTY, |acc, (commitment, slot)| {
        let mut item = [0u8; 64];
        item[..32].copy_from_slice(&commitment);
        // (The slot whole: an output's ends in nothing, as a block lists
        // it, and a covenant's that does not is of no output there
        // could be, to this as to a proof. Were its end left out, two
        // encodings would be one policy, of which only one could be
        // spent here.)
        item[32..].copy_from_slice(&slot);
        let mut pair = [0u8; 64];
        pair[..32].copy_from_slice(&acc);
        pair[32..].copy_from_slice(&hash_domain(DOM_OUT_ITEM, &item));
        hash_domain(DOM_COVERED, &pair)
    })
}

/// The digest of a run of outputs, commitment and memo slot (memo and
/// amount, [`crate::output::memo_slot`]) each: what a covenant holds
/// and a rebindable message covers.
pub fn covered_digest(outputs: &[(Commitment, Digest)]) -> Digest {
    covered_digest_of(outputs.iter().copied())
}

/// [`covered_digest`] of a run of a transaction's outputs.
pub fn covered_digest_outputs(outputs: &[Output]) -> Digest {
    covered_digest_of(outputs.iter().map(|o| (o.commitment, o.slot())))
}

/// The message rebindable signatures sign: the channel, the state number
/// and the digest of the outputs the spend must create.
pub fn rebind_message(channel: &Digest, state: u32, outputs: &[(Commitment, Digest)]) -> Digest {
    rebind_message_from(channel, state, &covered_digest(outputs))
}

/// [`rebind_message`] from the covered outputs' digest.
fn rebind_message_from(channel: &Digest, state: u32, covered: &Digest) -> Digest {
    conditions::rebind_message(channel, covered, state)
}

/// The root from one leaf's hash, its index and siblings.
pub fn root_from_path(leaf: &Digest, index: usize, siblings: &[Digest; POLICY_DEPTH]) -> Digest {
    let mut node = *leaf;
    for (level, sib) in siblings.iter().enumerate() {
        node = if (index >> level) & 1 == 0 { conditions::node(&node, sib) } else { conditions::node(sib, &node) };
    }
    node
}

/// The root over the leaf hashes in `level` (the empty digest where there
/// is no leaf), hashed pairwise, and the siblings of leaf `index`,
/// bottom up.
fn tree(mut level: [Digest; MAX_LEAVES], index: usize) -> (Digest, [Digest; POLICY_DEPTH]) {
    assert!(index < MAX_LEAVES, "no such leaf");
    let mut siblings = [EMPTY; POLICY_DEPTH];
    let (mut n, mut i) = (MAX_LEAVES, index);
    for sib in siblings.iter_mut() {
        *sib = level[i ^ 1];
        n /= 2;
        for k in 0..n {
            level[k] = conditions::node(&level[2 * k], &level[2 * k + 1]);
        }
        i >>= 1;
    }
    (level[0], siblings)
}

// ---------------------------------------------------------------------------
// Reading bytes
// ---------------------------------------------------------------------------

/// A list of digests in their encoding: 32 bytes each.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Digests<'a>(&'a [u8]);

impl<'a> Digests<'a> {
    /// Reads `n` digests from the front of `bytes`, returning the rest.
    fn read(bytes: &'a [u8], n: usize) -> Option<(Digests<'a>, &'a [u8])> {
        let (head, rest) = bytes.split_at_checked(n * DIGEST_BYTES)?;
        for d in head.chunks_exact(DIGEST_BYTES) {
            digest_from_bytes(d)?;
        }
        Some((Digests(head), rest))
    }

    pub fn len(&self) -> usize {
        self.0.len() / DIGEST_BYTES
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The digest at `i`. Panics past the end.
    pub fn get(&self, i: usize) -> Digest {
        digest_from_bytes(&self.0[i * DIGEST_BYTES..(i + 1) * DIGEST_BYTES]).expect("checked when read")
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = Digest> + 'a {
        self.0.chunks_exact(DIGEST_BYTES).map(|d| digest_from_bytes(d).expect("checked when read"))
    }
}

impl fmt::Debug for Digests<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// A covenant's outputs in their encoding: a commitment and a memo slot
/// each.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Pairs<'a>(Digests<'a>);

impl<'a> Pairs<'a> {
    pub fn len(&self) -> usize {
        self.0.len() / 2
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (Commitment, Digest)> + 'a {
        let list = self.0;
        (0..self.len()).map(move |i| (list.get(2 * i), list.get(2 * i + 1)))
    }
}

impl fmt::Debug for Pairs<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// ---------------------------------------------------------------------------
// Views: conditions and leaves
// ---------------------------------------------------------------------------

/// One condition of a leaf, read from its encoding.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CondRef<'a> {
    Thresh { mode: Mode, m: u8, keys: Digests<'a> },
    Hash(Digest),
    After(u32),
    Older(u32),
    State(u32),
    Outputs(Pairs<'a>),
}

impl<'a> CondRef<'a> {
    /// Reads a condition from the front of `bytes`, returning the rest.
    fn read(bytes: &'a [u8]) -> Option<(CondRef<'a>, &'a [u8])> {
        let (&tag, rest) = bytes.split_first()?;
        match tag {
            TAG_THRESH => {
                let (&mode_tag, mut rest) = rest.split_first()?;
                let mode = match mode_tag {
                    0 => Mode::Body,
                    1 => {
                        let (channel, r) = read_digest(rest)?;
                        rest = r;
                        Mode::Rebindable { channel }
                    }
                    _ => return None,
                };
                let (&m, rest) = rest.split_first()?;
                let (&n, rest) = rest.split_first()?;
                if n as usize > MAX_KEYS {
                    return None;
                }
                let (keys, rest) = Digests::read(rest, n as usize)?;
                Some((CondRef::Thresh { mode, m, keys }, rest))
            }
            TAG_HASH => {
                let (h, rest) = read_digest(rest)?;
                Some((CondRef::Hash(h), rest))
            }
            TAG_AFTER | TAG_OLDER => {
                let (v, rest) = read_u32(rest)?;
                if v > MAX_LOCK {
                    return None;
                }
                Some((if tag == TAG_AFTER { CondRef::After(v) } else { CondRef::Older(v) }, rest))
            }
            TAG_STATE => {
                let (v, rest) = read_u32(rest)?;
                if v > MAX_STATE {
                    return None;
                }
                Some((CondRef::State(v), rest))
            }
            TAG_OUTPUTS => {
                let (&k, rest) = rest.split_first()?;
                if k as usize > MAX_COVENANT {
                    return None;
                }
                let (list, rest) = Digests::read(rest, 2 * k as usize)?;
                Some((CondRef::Outputs(Pairs(list)), rest))
            }
            _ => None,
        }
    }

    /// Within bounds and well formed.
    pub fn valid(&self) -> bool {
        match self {
            CondRef::Thresh { m, keys, .. } => *m >= 1 && (*m as usize) <= keys.len() && keys.len() <= MAX_KEYS,
            CondRef::Outputs(list) => !list.is_empty() && list.len() <= MAX_COVENANT,
            CondRef::State(n) => *n <= MAX_STATE,
            CondRef::After(v) | CondRef::Older(v) => *v <= MAX_LOCK,
            CondRef::Hash(_) => true,
        }
    }

    /// Signatures the condition checks: its weight.
    pub fn signatures(&self) -> usize {
        match self {
            CondRef::Thresh { m, .. } => *m as usize,
            _ => 0,
        }
    }

    /// The condition's hash ([`crate::conditions::Cond::digest`]): one
    /// block of its tag, its numbers and a digest.
    fn digest(&self) -> Digest {
        let block = |tag: u32, a: u32, b: u32, digest: &Digest, last: u32| {
            let mut out = [0u8; 64];
            out[..4].copy_from_slice(&tag.to_le_bytes());
            out[4..8].copy_from_slice(&a.to_le_bytes());
            out[8..12].copy_from_slice(&b.to_le_bytes());
            out[16..48].copy_from_slice(digest);
            out[60..].copy_from_slice(&last.to_le_bytes());
            hash_domain(DOM_COND, &out)
        };
        match self {
            CondRef::Thresh { mode, m, keys } => {
                // The keys in a chain: from nothing, or from the channel.
                let (tag, start) = match mode {
                    Mode::Body => (1, EMPTY),
                    Mode::Rebindable { channel } => (7, *channel),
                };
                let chain = keys.iter().fold(start, |acc, key| {
                    let mut pair = [0u8; 64];
                    pair[..32].copy_from_slice(&acc);
                    pair[32..].copy_from_slice(&key);
                    hash_domain(DOM_SIGNERS, &pair)
                });
                block(tag, *m as u32, keys.len() as u32, &chain, 0)
            }
            CondRef::Hash(h) => block(2, 0, 0, h, 0),
            CondRef::After(h) => block(3, 0, 0, &EMPTY, *h),
            CondRef::Older(d) => block(4, 0, 0, &EMPTY, *d),
            CondRef::State(n) => block(5, 0, 0, &EMPTY, *n),
            CondRef::Outputs(list) => block(6, list.len() as u32, 0, &covered_digest_of(list.iter()), 0),
        }
    }

    /// The condition, owned.
    pub fn to_cond(&self) -> Cond {
        match *self {
            CondRef::Thresh { mode, m, keys } => Cond::Thresh { mode, m, keys: keys.iter().collect() },
            CondRef::Hash(h) => Cond::Hash(h),
            CondRef::After(h) => Cond::After(h),
            CondRef::Older(d) => Cond::Older(d),
            CondRef::State(n) => Cond::State(n),
            CondRef::Outputs(list) => Cond::Outputs(list.iter().collect()),
        }
    }
}

/// A leaf in its encoding: a conjunction of conditions.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LeafRef<'a> {
    /// `u8 n_conds`, then the conditions: all read once, so whole.
    bytes: &'a [u8],
}

/// The conditions of a [`LeafRef`], in order.
#[derive(Clone)]
pub struct Conds<'a> {
    rest: &'a [u8],
    left: usize,
}

impl<'a> Iterator for Conds<'a> {
    type Item = CondRef<'a>;

    fn next(&mut self) -> Option<CondRef<'a>> {
        if self.left == 0 {
            return None;
        }
        let (cond, rest) = CondRef::read(self.rest).expect("checked when read");
        self.rest = rest;
        self.left -= 1;
        Some(cond)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }
}

impl ExactSizeIterator for Conds<'_> {}

impl<'a> LeafRef<'a> {
    /// Reads a leaf from the front of `bytes`, returning the rest: one to
    /// [`LEAF_CONDS`] conditions, each whole and its lists within their
    /// bounds. Whether the conditions make sense is [`LeafRef::valid`].
    pub fn read(bytes: &'a [u8]) -> Option<(LeafRef<'a>, &'a [u8])> {
        let (&n, mut rest) = bytes.split_first()?;
        if n == 0 || n as usize > LEAF_CONDS {
            return None;
        }
        for _ in 0..n {
            rest = CondRef::read(rest)?.1;
        }
        Some((LeafRef { bytes: &bytes[..bytes.len() - rest.len()] }, rest))
    }

    /// The leaf's encoding.
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// Its size in bytes.
    pub fn size(&self) -> usize {
        self.bytes.len()
    }

    pub fn conds(&self) -> Conds<'a> {
        Conds { rest: &self.bytes[1..], left: self.bytes[0] as usize }
    }

    /// Within bounds and well formed.
    pub fn valid(&self) -> bool {
        self.conds().all(|c| c.valid())
    }

    /// Signatures the leaf checks: the weight of a spend through it.
    pub fn signatures(&self) -> usize {
        self.conds().map(|c| c.signatures()).sum()
    }

    /// The leaf's hash: its conditions' hashes, one after another
    /// ([`crate::conditions::leaf`]).
    pub fn hash(&self) -> Digest {
        self.conds().fold(EMPTY, |acc, c| {
            let mut pair = [0u8; 64];
            pair[..32].copy_from_slice(&acc);
            pair[32..].copy_from_slice(&c.digest());
            hash_domain(DOM_POLICY_LEAF, &pair)
        })
    }

    /// The leaf, owned.
    pub fn to_leaf(&self) -> Leaf {
        Leaf { conds: self.conds().map(|c| c.to_cond()).collect() }
    }
}

impl fmt::Debug for LeafRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.conds()).finish()
    }
}

// ---------------------------------------------------------------------------
// Views: policies
// ---------------------------------------------------------------------------

/// A policy in its encoding: `u8 n_leaves`, then the leaves, in tree order.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PolicyRef<'a> {
    bytes: &'a [u8],
}

/// The leaves of a [`PolicyRef`], in order.
#[derive(Clone)]
pub struct Leaves<'a> {
    rest: &'a [u8],
    left: usize,
}

impl<'a> Iterator for Leaves<'a> {
    type Item = LeafRef<'a>;

    fn next(&mut self) -> Option<LeafRef<'a>> {
        if self.left == 0 {
            return None;
        }
        let (leaf, rest) = LeafRef::read(self.rest).expect("checked when read");
        self.rest = rest;
        self.left -= 1;
        Some(leaf)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }
}

impl ExactSizeIterator for Leaves<'_> {}

impl<'a> PolicyRef<'a> {
    /// Reads a policy that is the whole of `bytes`: one to [`MAX_LEAVES`]
    /// leaves and nothing after them.
    pub fn from_bytes(bytes: &'a [u8]) -> Result<PolicyRef<'a>, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("spend policy"))
    }

    fn decode(bytes: &'a [u8]) -> Option<PolicyRef<'a>> {
        let (&n, mut rest) = bytes.split_first()?;
        if n == 0 || n as usize > MAX_LEAVES {
            return None;
        }
        for _ in 0..n {
            rest = LeafRef::read(rest)?.1;
        }
        rest.is_empty().then_some(PolicyRef { bytes })
    }

    /// The policy's encoding.
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub fn leaves(&self) -> Leaves<'a> {
        Leaves { rest: &self.bytes[1..], left: self.bytes[0] as usize }
    }

    pub fn valid(&self) -> bool {
        self.leaves().all(|l| l.valid())
    }

    fn leaf_hashes(&self) -> [Digest; MAX_LEAVES] {
        let mut level = [EMPTY; MAX_LEAVES];
        for (h, leaf) in level.iter_mut().zip(self.leaves()) {
            *h = leaf.hash();
        }
        level
    }

    /// The policy hash: what an output commits to with the amount. The
    /// root over the leaves' hashes, padded with the empty digest to
    /// `2^POLICY_DEPTH`.
    pub fn root(&self) -> Digest {
        tree(self.leaf_hashes(), 0).0
    }

    /// The siblings of leaf `index`, bottom up. Panics for an index no
    /// policy has.
    pub fn siblings(&self, index: usize) -> [Digest; POLICY_DEPTH] {
        tree(self.leaf_hashes(), index).1
    }

    /// The policy, owned.
    pub fn to_policy(&self) -> Policy {
        Policy { leaves: self.leaves().map(|l| l.to_leaf()).collect() }
    }
}

impl fmt::Debug for PolicyRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.leaves()).finish()
    }
}

// ---------------------------------------------------------------------------
// Views: spends
// ---------------------------------------------------------------------------

/// One signer of a threshold: which listed key, and the proof.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signer {
    pub key: u8,
    pub pubkey: PublicKey,
    pub signature: Signature,
}

/// The signers of one threshold in their encoding. Iterating decodes one
/// at a time.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Signers<'a> {
    /// `count` of `u8 key, pubkey, signature`: all read once, so whole.
    bytes: &'a [u8],
    left: usize,
}

impl<'a> Signers<'a> {
    /// One signer from the front of `bytes`, and the rest.
    fn one(bytes: &'a [u8]) -> Option<(Signer, &'a [u8])> {
        let (&key, rest) = bytes.split_first()?;
        let (pk, rest) = rest.split_at_checked(PublicKey::SIZE)?;
        let pubkey = PublicKey::from_bytes(pk).ok()?;
        let (sig, rest) = rest.split_at_checked(Signature::size(pubkey.height()))?;
        let signature = Signature::from_bytes(sig, pubkey.height()).ok()?;
        Some((Signer { key, pubkey, signature }, rest))
    }

    /// Reads `u8 count` and that many signers from the front of `bytes`,
    /// returning the rest.
    fn read(bytes: &'a [u8]) -> Option<(Signers<'a>, &'a [u8])> {
        let (&n, list) = bytes.split_first()?;
        if n as usize > MAX_KEYS {
            return None;
        }
        let mut rest = list;
        for _ in 0..n {
            rest = Signers::one(rest)?.1;
        }
        Some((Signers { bytes: &list[..list.len() - rest.len()], left: n as usize }, rest))
    }

    /// How many signers are left to iterate.
    pub fn len(&self) -> usize {
        self.left
    }

    pub fn is_empty(&self) -> bool {
        self.left == 0
    }
}

impl Iterator for Signers<'_> {
    type Item = Signer;

    fn next(&mut self) -> Option<Signer> {
        if self.left == 0 {
            return None;
        }
        let (signer, rest) = Signers::one(self.bytes).expect("checked when read");
        self.bytes = rest;
        self.left -= 1;
        Some(signer)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }
}

impl ExactSizeIterator for Signers<'_> {}

impl fmt::Debug for Signers<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(*self).finish()
    }
}

/// What satisfies one condition, read from a spend's encoding.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WitnessRef<'a> {
    Signatures(Signers<'a>),
    Preimage(Digest),
    None,
}

/// A spend's conditions, each with its witness, in order.
#[derive(Clone)]
pub struct Witnesses<'a> {
    conds: Conds<'a>,
    rest: &'a [u8],
}

impl<'a> Iterator for Witnesses<'a> {
    type Item = (CondRef<'a>, WitnessRef<'a>);

    fn next(&mut self) -> Option<(CondRef<'a>, WitnessRef<'a>)> {
        let cond = self.conds.next()?;
        let witness = match cond {
            CondRef::Thresh { .. } => {
                let (signers, rest) = Signers::read(self.rest).expect("checked when read");
                self.rest = rest;
                WitnessRef::Signatures(signers)
            }
            CondRef::Hash(_) => {
                let (preimage, rest) = read_digest(self.rest).expect("checked when read");
                self.rest = rest;
                WitnessRef::Preimage(preimage)
            }
            _ => WitnessRef::None,
        };
        Some((cond, witness))
    }
}

/// A spend of a policy output in its encoding: the leaf used, its place
/// in the tree, and what satisfies it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PolicyInputRef<'a> {
    amount: u64,
    position: u64,
    index: u8,
    siblings: [Digest; POLICY_DEPTH],
    state: u32,
    covered: (u8, u8),
    leaf: LeafRef<'a>,
    /// One witness per condition of the leaf, as the condition's kind lays
    /// it out: all read once, so whole.
    witness: &'a [u8],
    /// The whole input.
    bytes: &'a [u8],
}

/// The run of `outputs` a spend covers, start and count, as their indexes;
/// `None` if it runs past them.
fn covered_run(covered: (u8, u8), outputs: &(impl OutputList + ?Sized)) -> Option<core::ops::Range<usize>> {
    let start = covered.0 as usize;
    let end = start + covered.1 as usize;
    (end <= outputs.len()).then_some(start..end)
}

impl<'a> PolicyInputRef<'a> {
    /// Offset of the position in an input's encoding: the position is not
    /// signed, so it may be rewritten in place ([`PolicyInputRef::position`]).
    pub const POSITION_AT: usize = 8;

    /// Reads an input from the front of `bytes`, returning the rest. The
    /// whole encoding is checked: the leaf index and the state number in
    /// range, the leaf as [`LeafRef::read`] takes it, and for each of its
    /// conditions the witness of its kind, every signature whole.
    pub fn read(bytes: &'a [u8]) -> Option<(PolicyInputRef<'a>, &'a [u8])> {
        let (amount, rest) = read_u64(bytes)?;
        let (position, rest) = read_u64(rest)?;
        let (&index, mut rest) = rest.split_first()?;
        if index as usize >= MAX_LEAVES {
            return None;
        }
        let mut siblings = [EMPTY; POLICY_DEPTH];
        for s in siblings.iter_mut() {
            let (d, r) = read_digest(rest)?;
            *s = d;
            rest = r;
        }
        let (state, rest) = read_u32(rest)?;
        if state > MAX_STATE {
            return None;
        }
        let (&start, rest) = rest.split_first()?;
        let (&count, rest) = rest.split_first()?;
        let (leaf, witness) = LeafRef::read(rest)?;
        let mut rest = witness;
        for cond in leaf.conds() {
            match cond {
                CondRef::Thresh { .. } => rest = Signers::read(rest)?.1,
                CondRef::Hash(_) => rest = read_digest(rest)?.1,
                _ => {}
            }
        }
        let input = PolicyInputRef {
            amount,
            position,
            index,
            siblings,
            state,
            covered: (start, count),
            leaf,
            witness: &witness[..witness.len() - rest.len()],
            bytes: &bytes[..bytes.len() - rest.len()],
        };
        Some((input, rest))
    }

    /// The input's encoding.
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// Its size in bytes.
    pub fn size(&self) -> usize {
        self.bytes.len()
    }

    pub fn amount(&self) -> u64 {
        self.amount
    }

    /// Where the spent output is: told, not signed.
    pub fn position(&self) -> u64 {
        self.position
    }

    /// Which leaf of the policy this spends through.
    pub fn index(&self) -> u8 {
        self.index
    }

    pub fn siblings(&self) -> &[Digest; POLICY_DEPTH] {
        &self.siblings
    }

    /// The spending transaction's state number (below `2^30`), for `State`
    /// conditions and rebindable signatures, whose leaf index it is.
    pub fn state(&self) -> u32 {
        self.state
    }

    /// The outputs rebindable signatures cover: a run of the transaction's
    /// outputs, start and count.
    pub fn covered(&self) -> (u8, u8) {
        self.covered
    }

    pub fn leaf(&self) -> LeafRef<'a> {
        self.leaf
    }

    /// The leaf's conditions, each with its witness.
    pub fn witnesses(&self) -> Witnesses<'a> {
        Witnesses { conds: self.leaf.conds(), rest: self.witness }
    }

    /// The policy hash this spend reveals.
    pub fn policy(&self) -> Digest {
        root_from_path(&self.leaf.hash(), self.index as usize, &self.siblings)
    }

    /// The commitment of the output this input spends.
    pub fn commitment(&self) -> Commitment {
        key_commitment(&self.policy(), self.amount)
    }

    /// Signatures checked: the weight.
    pub fn signatures(&self) -> usize {
        self.leaf.signatures()
    }

    /// Whether the leaf is satisfied: `body` is the transaction's body hash,
    /// `outputs` its outputs, `height` the block's and `created` the spent
    /// output's creation height. Allocates nothing.
    pub fn check(
        &self,
        body: &Digest,
        outputs: &(impl OutputList + ?Sized),
        height: u32,
        created: u32,
    ) -> Result<(), Error> {
        if !self.leaf.valid() {
            return Err(Error::Malformed("spend policy"));
        }
        // A transaction's covered outputs are its first.
        let run = covered_run(self.covered, outputs).filter(|run| run.start == 0).ok_or(Error::PolicyCovered)?;
        let covered = || run.clone().map(|i| outputs.pair(i));
        for (cond, witness) in self.witnesses() {
            match (cond, witness) {
                (CondRef::Thresh { mode, m, keys }, WitnessRef::Signatures(signers)) => {
                    let msg = match mode {
                        Mode::Body => *body,
                        Mode::Rebindable { channel } => {
                            // A rebindable signature is of outputs.
                            if run.is_empty() {
                                return Err(Error::PolicyCovered);
                            }
                            rebind_message_from(&channel, self.state, &covered_digest_of(covered()))
                        }
                    };
                    let mut seen = [false; MAX_KEYS];
                    let mut good = 0usize;
                    for s in signers {
                        let k = s.key as usize;
                        if k >= keys.len() || seen[k] || pubkey_hash(&s.pubkey) != keys.get(k) {
                            return Err(Error::PolicySignatures);
                        }
                        if matches!(mode, Mode::Rebindable { .. }) && s.signature.index != self.state as u64 {
                            return Err(Error::PolicySignatures);
                        }
                        if !s.pubkey.verify(&msg, &s.signature) {
                            return Err(Error::PolicySignatures);
                        }
                        seen[k] = true;
                        good += 1;
                    }
                    // As many as asked, and no more: what a proof counts.
                    if good != m as usize {
                        return Err(Error::PolicySignatures);
                    }
                }
                (CondRef::Hash(h), WitnessRef::Preimage(p)) => {
                    if hash_lock(&p) != h {
                        return Err(Error::PolicyPreimage);
                    }
                }
                (CondRef::After(h), WitnessRef::None) => {
                    if height < h {
                        return Err(Error::PolicyLocked);
                    }
                }
                (CondRef::Older(d), WitnessRef::None) => {
                    if (height as u64) < created as u64 + d as u64 {
                        return Err(Error::PolicyLocked);
                    }
                }
                (CondRef::State(n), WitnessRef::None) => {
                    if self.state > MAX_STATE || self.state <= n {
                        return Err(Error::PolicyState);
                    }
                }
                (CondRef::Outputs(list), WitnessRef::None) => {
                    let same = list.len() == run.len() && list.iter().eq(covered());
                    if !same {
                        return Err(Error::PolicyCovenant);
                    }
                }
                _ => return Err(Error::PolicyWitness),
            }
        }
        Ok(())
    }

    /// Whether the input is said the one way there is to say it, where
    /// what it is checked by ([`PolicyInputRef::check`], and a proof)
    /// takes more than one: its leaf within bounds; a state number only
    /// where a condition reads it; the signers of each condition in the
    /// order of its keys. None of that is under a transaction's id or a
    /// signature, and whoever passed a transaction on could say it
    /// another way, of the same id: a pool takes the one.
    pub fn canonical(&self) -> bool {
        let read = self
            .leaf
            .conds()
            .any(|c| matches!(c, CondRef::State(_) | CondRef::Thresh { mode: Mode::Rebindable { .. }, .. }));
        self.leaf.valid()
            && (read || self.state == 0)
            && self.witnesses().all(|(_, witness)| match witness {
                WitnessRef::Signatures(signers) => {
                    let keys: Vec<u8> = signers.map(|s| s.key).collect();
                    keys.windows(2).all(|pair| pair[0] < pair[1])
                }
                _ => true,
            })
    }

    /// The input, owned.
    pub fn to_input(&self) -> PolicyInput {
        PolicyInput {
            amount: self.amount,
            position: self.position,
            leaf: self.leaf.to_leaf(),
            index: self.index,
            siblings: self.siblings,
            state: self.state,
            covered: self.covered,
            witness: self
                .witnesses()
                .map(|(_, w)| match w {
                    WitnessRef::Signatures(signers) => CondWitness::Signatures(signers.collect()),
                    WitnessRef::Preimage(p) => CondWitness::Preimage(p),
                    WitnessRef::None => CondWitness::None,
                })
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Owned forms: for building
// ---------------------------------------------------------------------------

/// One condition of a leaf.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Cond {
    Thresh { mode: Mode, m: u8, keys: Vec<Digest> },
    Hash(Digest),
    After(u32),
    Older(u32),
    State(u32),
    Outputs(Vec<(Commitment, Digest)>),
}

/// A conjunction of conditions.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Leaf {
    pub conds: Vec<Cond>,
}

/// A policy: its leaves, in tree order.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Policy {
    pub leaves: Vec<Leaf>,
}

/// The data satisfying one condition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CondWitness {
    Signatures(Vec<Signer>),
    Preimage(Digest),
    None,
}

/// A spend of a policy output: the leaf used, its place in the tree, and
/// what satisfies it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PolicyInput {
    pub amount: u64,
    pub position: u64,
    pub leaf: Leaf,
    pub index: u8,
    pub siblings: [Digest; POLICY_DEPTH],
    /// The spending transaction's state number (below `2^30`), for `State`
    /// conditions and rebindable signatures, whose leaf index it is.
    pub state: u32,
    /// The outputs rebindable signatures cover: a run of the transaction's
    /// outputs, start and count.
    pub covered: (u8, u8),
    /// One per condition of the leaf, in order.
    pub witness: Vec<CondWitness>,
}

impl Cond {
    /// The condition as the proofs' rules hold it
    /// ([`crate::conditions::Cond`]): the same hash.
    pub fn rule(&self) -> conditions::Cond {
        match self {
            Cond::Thresh { mode: Mode::Body, m, keys } => conditions::Cond::Thresh { m: *m as u32, keys: keys.clone() },
            Cond::Thresh { mode: Mode::Rebindable { channel }, m, keys } => {
                conditions::Cond::Rebind { m: *m as u32, keys: keys.clone(), channel: *channel }
            }
            Cond::Hash(h) => conditions::Cond::Hash(*h),
            Cond::After(h) => conditions::Cond::After(*h),
            Cond::Older(d) => conditions::Cond::Older(*d),
            Cond::State(n) => conditions::Cond::State(*n),
            Cond::Outputs(list) => conditions::Cond::Outputs { count: list.len() as u32, digest: covered_digest(list) },
        }
    }

    /// Within bounds and well formed.
    pub fn valid(&self) -> bool {
        match self {
            Cond::Thresh { m, keys, .. } => *m >= 1 && (*m as usize) <= keys.len() && keys.len() <= MAX_KEYS,
            Cond::Outputs(list) => !list.is_empty() && list.len() <= MAX_COVENANT,
            Cond::State(n) => *n <= MAX_STATE,
            Cond::After(v) | Cond::Older(v) => *v <= MAX_LOCK,
            Cond::Hash(_) => true,
        }
    }

    /// Signatures the condition checks: its weight.
    pub fn signatures(&self) -> usize {
        match self {
            Cond::Thresh { m, .. } => *m as usize,
            _ => 0,
        }
    }

    pub fn size(&self) -> usize {
        match self {
            Cond::Thresh { mode, keys, .. } => {
                1 + 1
                    + if matches!(mode, Mode::Rebindable { .. }) { DIGEST_BYTES } else { 0 }
                    + 2
                    + DIGEST_BYTES * keys.len()
            }
            Cond::Hash(_) => 1 + DIGEST_BYTES,
            Cond::After(_) | Cond::Older(_) => 1 + 4,
            Cond::State(_) => 1 + 4,
            Cond::Outputs(list) => 1 + 1 + 2 * DIGEST_BYTES * list.len(),
        }
    }

    fn write(&self, out: &mut Vec<u8>) {
        match self {
            Cond::Thresh { mode, m, keys } => {
                out.push(TAG_THRESH);
                match mode {
                    Mode::Body => out.push(0),
                    Mode::Rebindable { channel } => {
                        out.push(1);
                        out.extend_from_slice(&digest_to_bytes(channel));
                    }
                }
                out.push(*m);
                out.push(keys.len() as u8);
                for k in keys {
                    out.extend_from_slice(&digest_to_bytes(k));
                }
            }
            Cond::Hash(h) => {
                out.push(TAG_HASH);
                out.extend_from_slice(&digest_to_bytes(h));
            }
            Cond::After(h) => {
                out.push(TAG_AFTER);
                out.extend_from_slice(&h.to_le_bytes());
            }
            Cond::Older(d) => {
                out.push(TAG_OLDER);
                out.extend_from_slice(&d.to_le_bytes());
            }
            Cond::State(n) => {
                out.push(TAG_STATE);
                out.extend_from_slice(&n.to_le_bytes());
            }
            Cond::Outputs(list) => {
                out.push(TAG_OUTPUTS);
                out.push(list.len() as u8);
                for (c, m) in list {
                    out.extend_from_slice(&digest_to_bytes(c));
                    out.extend_from_slice(&digest_to_bytes(m));
                }
            }
        }
    }
}

impl Leaf {
    pub fn new(conds: Vec<Cond>) -> Leaf {
        Leaf { conds }
    }

    /// The leaf's conditions as the proofs' rules hold them.
    pub fn rules(&self) -> Vec<conditions::Cond> {
        self.conds.iter().map(Cond::rule).collect()
    }

    /// A plain key's leaf: one body-mode signature.
    pub fn key(key_hash: Digest) -> Leaf {
        Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 1, keys: vec![key_hash] }])
    }

    /// Whether the leaf has an encoding: one to [`LEAF_CONDS`] conditions,
    /// no more keys in a threshold or outputs in a covenant than either
    /// may list, no height, age or state number past its bound.
    fn encodable(&self) -> bool {
        (1..=LEAF_CONDS).contains(&self.conds.len())
            && self.conds.iter().all(|c| match c {
                Cond::Thresh { keys, .. } => keys.len() <= MAX_KEYS,
                Cond::Outputs(list) => list.len() <= MAX_COVENANT,
                Cond::After(v) | Cond::Older(v) => *v <= MAX_LOCK,
                Cond::State(n) => *n <= MAX_STATE,
                Cond::Hash(_) => true,
            })
    }

    /// Within bounds and well formed.
    pub fn valid(&self) -> bool {
        !self.conds.is_empty() && self.conds.len() <= LEAF_CONDS && self.conds.iter().all(Cond::valid)
    }

    /// Signatures the leaf checks: the weight of a spend through it.
    pub fn signatures(&self) -> usize {
        self.conds.iter().map(Cond::signatures).sum()
    }

    /// Runs `f` on the view of this leaf's encoding. Panics for a leaf
    /// with no encoding (more conditions, keys or covenant outputs than a
    /// leaf may hold, or a number past its bound): such a leaf can be
    /// neither committed to nor spent.
    fn with_view<R>(&self, f: impl FnOnce(LeafRef<'_>) -> R) -> R {
        assert!(self.encodable(), "the leaf is out of bounds: it has no encoding");
        let mut bytes = Vec::with_capacity(self.size());
        self.write(&mut bytes);
        let (view, rest) = LeafRef::read(&bytes).expect("a leaf within bounds reads back");
        debug_assert!(rest.is_empty());
        f(view)
    }

    /// The leaf's hash. Panics for a leaf out of bounds.
    pub fn hash(&self) -> Digest {
        self.with_view(|v| v.hash())
    }

    pub fn size(&self) -> usize {
        1 + self.conds.iter().map(Cond::size).sum::<usize>()
    }

    pub fn write(&self, out: &mut Vec<u8>) {
        out.push(self.conds.len() as u8);
        for c in &self.conds {
            c.write(out);
        }
    }

    /// Reads a leaf from the front of `bytes`, returning the rest.
    pub fn read(bytes: &[u8]) -> Option<(Leaf, &[u8])> {
        let (view, rest) = LeafRef::read(bytes)?;
        Some((view.to_leaf(), rest))
    }
}

impl Policy {
    pub fn new(leaves: Vec<Leaf>) -> Policy {
        Policy { leaves }
    }

    pub fn valid(&self) -> bool {
        !self.leaves.is_empty() && self.leaves.len() <= MAX_LEAVES && self.leaves.iter().all(Leaf::valid)
    }

    fn leaf_hashes(&self) -> [Digest; MAX_LEAVES] {
        assert!(self.leaves.len() <= MAX_LEAVES, "the policy has more leaves than its tree holds");
        let mut level = [EMPTY; MAX_LEAVES];
        for (h, leaf) in level.iter_mut().zip(&self.leaves) {
            *h = leaf.hash();
        }
        level
    }

    /// The policy hash: what an output commits to with the amount.
    /// Panics for a policy out of bounds.
    pub fn root(&self) -> Digest {
        tree(self.leaf_hashes(), 0).0
    }

    /// The siblings of leaf `index`, bottom up.
    pub fn siblings(&self, index: usize) -> [Digest; POLICY_DEPTH] {
        tree(self.leaf_hashes(), index).1
    }

    /// `u8 n_leaves`, then the leaves.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![self.leaves.len() as u8];
        for l in &self.leaves {
            l.write(&mut out);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Policy, Error> {
        Ok(PolicyRef::from_bytes(bytes)?.to_policy())
    }

    /// An output paying `amount` under this policy.
    pub fn output(&self, amount: u64, memo: Memo) -> Output {
        Output::with_memo(&self.root(), amount, memo)
    }

    /// A spend through leaf `index`, to be given its witness.
    pub fn spend(&self, index: usize, amount: u64, position: u64) -> PolicyInput {
        let leaf = self.leaves[index].clone();
        let witness = leaf
            .conds
            .iter()
            .map(|c| match c {
                Cond::Thresh { .. } => CondWitness::Signatures(Vec::new()),
                Cond::Hash(_) => CondWitness::Preimage(EMPTY),
                _ => CondWitness::None,
            })
            .collect();
        PolicyInput {
            amount,
            position,
            leaf,
            index: index as u8,
            siblings: self.siblings(index),
            state: 0,
            covered: (0, 0),
            witness,
        }
    }
}

impl PolicyInput {
    /// The policy hash this spend reveals.
    pub fn policy(&self) -> Digest {
        root_from_path(&self.leaf.hash(), self.index as usize, &self.siblings)
    }

    /// The spend as the proofs' rules hold it
    /// ([`crate::conditions::PolicyInput`]), of an output with `memo`
    /// made at height `created`: for each threshold, the keys that sign
    /// in their places with their signatures' leaves.
    pub fn rule(&self, memo: Memo, created: u32) -> conditions::PolicyInput {
        let shown = (self.leaf.conds.iter().zip(&self.witness))
            .map(|(cond, witness)| match (cond, witness) {
                (Cond::Thresh { keys, .. }, CondWitness::Signatures(signers)) => {
                    let mut places = vec![None; keys.len()];
                    for s in signers {
                        if let Some(place) = places.get_mut(s.key as usize) {
                            *place = Some((s.pubkey, s.signature.index));
                        }
                    }
                    conditions::Shown::Signers(places)
                }
                (_, CondWitness::Preimage(p)) => conditions::Shown::Preimage(*p),
                _ => conditions::Shown::Nothing,
            })
            .collect();
        conditions::PolicyInput {
            amount: self.amount,
            memo,
            created,
            position: self.position,
            conds: self.leaf.rules(),
            index: self.index as usize,
            siblings: self.siblings,
            shown,
            state: self.state,
        }
    }

    /// The commitment of the output this input spends.
    pub fn commitment(&self) -> Commitment {
        key_commitment(&self.policy(), self.amount)
    }

    /// Signatures checked: the weight.
    pub fn signatures(&self) -> usize {
        self.leaf.signatures()
    }

    /// The outputs a rebindable signature of this input covers.
    pub fn covered_outputs(&self, outputs: &[Output]) -> Option<Vec<(Commitment, Digest)>> {
        Some(covered_run(self.covered, outputs)?.map(|i| outputs.pair(i)).collect())
    }

    /// Whether each condition has a witness of its kind.
    fn witness_fits(&self) -> bool {
        self.witness.len() == self.leaf.conds.len()
            && self.leaf.conds.iter().zip(&self.witness).all(|(c, w)| {
                matches!(
                    (c, w),
                    (Cond::Thresh { .. }, CondWitness::Signatures(_))
                        | (Cond::Hash(_), CondWitness::Preimage(_))
                        | (Cond::After(_) | Cond::Older(_) | Cond::State(_) | Cond::Outputs(_), CondWitness::None)
                )
            })
    }

    /// Whether the leaf is satisfied ([`PolicyInputRef::check`], which
    /// this encodes the input for). An input with no encoding is
    /// [`Error::Malformed("spend policy")`]; one whose witnesses are not of their
    /// conditions' kinds is [`Error::PolicyWitness`].
    pub fn check(&self, body: &Digest, outputs: &[Output], height: u32, created: u32) -> Result<(), Error> {
        if !self.leaf.valid() || (self.index as usize) >= MAX_LEAVES || self.witness.len() != self.leaf.conds.len() {
            return Err(Error::Malformed("spend policy"));
        }
        if !self.witness_fits() {
            return Err(Error::PolicyWitness);
        }
        let bytes = self.to_bytes();
        match PolicyInputRef::read(&bytes) {
            Some((view, [])) => view.check(body, outputs, height, created),
            _ => Err(Error::Malformed("spend policy")),
        }
    }

    pub fn size(&self) -> usize {
        8 + 8 + 1 + POLICY_DEPTH * DIGEST_BYTES + 4 + 2 + self.leaf.size() + self.witness_size()
    }

    fn witness_size(&self) -> usize {
        self.witness
            .iter()
            .map(|w| match w {
                CondWitness::Signatures(s) => {
                    1 + s.iter().map(|s| 1 + PublicKey::SIZE + Signature::size(s.pubkey.height())).sum::<usize>()
                }
                CondWitness::Preimage(_) => DIGEST_BYTES,
                CondWitness::None => 0,
            })
            .sum()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.size());
        out.extend_from_slice(&self.amount.to_le_bytes());
        out.extend_from_slice(&self.position.to_le_bytes());
        out.push(self.index);
        for s in &self.siblings {
            out.extend_from_slice(&digest_to_bytes(s));
        }
        out.extend_from_slice(&self.state.to_le_bytes());
        out.push(self.covered.0);
        out.push(self.covered.1);
        self.leaf.write(&mut out);
        for w in &self.witness {
            match w {
                CondWitness::Signatures(signers) => {
                    out.push(signers.len() as u8);
                    for s in signers {
                        out.push(s.key);
                        out.extend_from_slice(&s.pubkey.to_bytes());
                        let at = out.len();
                        out.resize(at + Signature::size(s.signature.height()), 0);
                        s.signature.write_bytes(&mut out[at..]);
                    }
                }
                CondWitness::Preimage(p) => out.extend_from_slice(&digest_to_bytes(p)),
                CondWitness::None => {}
            }
        }
        out
    }

    /// Parses an input from the front of `bytes`, returning the rest.
    pub fn read(bytes: &[u8]) -> Option<(PolicyInput, &[u8])> {
        let (view, rest) = PolicyInputRef::read(bytes)?;
        Some((view.to_input(), rest))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::output::{memo_slot, memo5};
    use crate::xmss::SecretKey as Key;

    fn key(tag: u8) -> Key {
        let mut s = [0u8; 32];
        s[0] = tag;
        Key::generate(&s)
    }

    fn d(x: u32) -> Digest {
        let mut v = EMPTY;
        v[..4].copy_from_slice(&x.to_le_bytes());
        v
    }

    #[test]
    fn leaves_hash_and_encode() {
        let (a, b, c) = (key(1), key(2), key(3));
        let keys: Vec<Digest> = [&a, &b, &c].iter().map(|k| pubkey_hash(&k.public_key())).collect();
        let leaf = Leaf::new(vec![
            Cond::Thresh { mode: Mode::Rebindable { channel: d(9) }, m: 2, keys: keys.clone() },
            Cond::State(5),
            Cond::Outputs(vec![(d(1), d(2)), (d(3), d(4))]),
            Cond::Older(144),
        ]);
        assert!(leaf.valid());
        assert_eq!(leaf.signatures(), 2);
        // The policy decoder, fuzzed: no panic, one encoding.
        let policy = Policy::new(vec![leaf.clone(), Leaf::new(vec![Cond::After(100)])]);
        crate::test_util::fuzz_decoder("Policy::from_bytes", &[policy.to_bytes()], 20_000, |b| {
            Policy::from_bytes(b).ok().map(|p| Some(p.to_bytes()))
        });
        let mut bytes = Vec::new();
        leaf.write(&mut bytes);
        assert_eq!(bytes.len(), leaf.size());
        let (back, rest) = Leaf::read(&bytes).unwrap();
        assert!(rest.is_empty());
        assert_eq!(back, leaf);
        assert_eq!(back.hash(), leaf.hash());
        // Any change moves the hash.
        let other = Leaf::new(vec![Cond::State(6)]);
        assert_ne!(other.hash(), Leaf::new(vec![Cond::State(5)]).hash());
        assert_ne!(Leaf::new(vec![Cond::After(5)]).hash(), Leaf::new(vec![Cond::Older(5)]).hash());
        // Bounds.
        assert!(!Leaf::new(vec![]).valid());
        assert!(!Leaf::new(vec![Cond::After(1); LEAF_CONDS + 1]).valid());
        assert!(!Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 2, keys: keys[..1].to_vec() }]).valid());
        assert!(!Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 0, keys: keys.clone() }]).valid());
        assert!(!Leaf::new(vec![Cond::Outputs(vec![])]).valid());
    }

    #[test]
    fn policy_roots_and_paths() {
        let leaves: Vec<Leaf> = (0..5).map(|i| Leaf::new(vec![Cond::After(i)])).collect();
        let p = Policy::new(leaves.clone());
        assert!(p.valid());
        let root = p.root();
        for (i, leaf) in leaves.iter().enumerate() {
            assert_eq!(root_from_path(&leaf.hash(), i, &p.siblings(i)), root);
        }
        assert_ne!(root_from_path(&leaves[0].hash(), 1, &p.siblings(0)), root);
        // The leaf order matters; a one-leaf policy differs from a key hash.
        let swapped = Policy::new(vec![leaves[1].clone(), leaves[0].clone()]);
        assert_ne!(swapped.root(), Policy::new(leaves[..2].to_vec()).root());
        let kh = pubkey_hash(&key(1).public_key());
        assert_ne!(Policy::new(vec![Leaf::key(kh)]).root(), kh);
    }

    #[test]
    fn multisig_htlc_and_channel_leaves_are_checked() {
        let (mut a, mut b, mut c) = (key(1), key(2), key(3));
        let keys: Vec<Digest> = [&a, &b, &c].iter().map(|k| pubkey_hash(&k.public_key())).collect();
        let preimage = d(77);
        let channel = d(5);
        // The covered outputs' commitments and slots: memos and amounts.
        let slot = |n: u32, amount: u64| memo_slot(&memo5(d(n)), amount);
        let settle = vec![(d(11), slot(12, 500)), (d(13), slot(14, 490))];
        let policy = Policy::new(vec![
            // 0: 2-of-3, body mode.
            Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 2, keys: keys.clone() }]),
            // 1: HTLC claim; 2: HTLC refund.
            Leaf::new(vec![
                Cond::Hash(hash_lock(&preimage)),
                Cond::Thresh { mode: Mode::Body, m: 1, keys: keys[1..2].to_vec() },
            ]),
            Leaf::new(vec![Cond::After(100), Cond::Thresh { mode: Mode::Body, m: 1, keys: keys[..1].to_vec() }]),
            // 3: eltoo update; 4: settlement covenant.
            Leaf::new(vec![
                Cond::Thresh { mode: Mode::Rebindable { channel }, m: 2, keys: keys[..2].to_vec() },
                Cond::State(3),
            ]),
            Leaf::new(vec![Cond::Older(144), Cond::Outputs(settle.clone())]),
        ]);
        let amount = 1000;
        let outputs: Vec<Output> = vec![
            Output::with_memo(&d(11), 500, memo5(d(12))),
            Output::with_memo(&d(13), 490, memo5(d(14))),
            Output::with_memo(&d(1), 10, memo5(d(2))),
        ];
        // Fix the commitments to the covenant's: with_memo derives them.
        let outputs: Vec<Output> = outputs
            .into_iter()
            .enumerate()
            .map(|(i, mut o)| {
                if i < 2 {
                    o.commitment = settle[i].0;
                }
                o
            })
            .collect();
        // The body hash of the spending transaction: any digest stands for it here.
        let body = d(4242);

        // 2-of-3 body mode.
        let mut spend = policy.spend(0, amount, 7);
        assert_eq!(spend.commitment(), key_commitment(&policy.root(), amount));
        assert_eq!(spend.check(&body, &outputs, 1, 0), Err(Error::PolicySignatures));
        let sa = Signer { key: 0, pubkey: a.public_key(), signature: a.sign(&body).unwrap() };
        let sc = Signer { key: 2, pubkey: c.public_key(), signature: c.sign(&body).unwrap() };
        spend.witness[0] = CondWitness::Signatures(vec![sa.clone(), sc.clone()]);
        assert_eq!(spend.check(&body, &outputs, 1, 0), Ok(()));
        assert_eq!(spend.signatures(), 2);
        // The same key twice does not count twice; a wrong key is refused.
        spend.witness[0] = CondWitness::Signatures(vec![sa.clone(), sa.clone()]);
        assert_eq!(spend.check(&body, &outputs, 1, 0), Err(Error::PolicySignatures));
        let wrong = Signer { key: 1, ..sa.clone() };
        spend.witness[0] = CondWitness::Signatures(vec![wrong, sc.clone()]);
        assert_eq!(spend.check(&body, &outputs, 1, 0), Err(Error::PolicySignatures));
        // Encoding round trip, with signatures.
        spend.witness[0] = CondWitness::Signatures(vec![sa, sc]);
        let bytes = spend.to_bytes();
        assert_eq!(bytes.len(), spend.size());
        let (back, rest) = PolicyInput::read(&bytes).unwrap();
        assert!(rest.is_empty());
        assert_eq!(back, spend);
        // It is said the one way there is to say it. Its signers the
        // other way about, or a state number that nothing reads, is the
        // same spend to whatever checks it, said another way: which a
        // pool does not take.
        let said = |spend: &PolicyInput| {
            let bytes = spend.to_bytes();
            let view = PolicyInputRef::read(&bytes).unwrap().0;
            (view.check(&body, &outputs, 1, 0), view.canonical())
        };
        assert_eq!(said(&spend), (Ok(()), true));
        let mut other = spend.clone();
        if let CondWitness::Signatures(signers) = &mut other.witness[0] {
            signers.reverse();
        }
        assert_eq!(said(&other), (Ok(()), false));
        let other = PolicyInput { state: 9, ..spend.clone() };
        assert_eq!(said(&other), (Ok(()), false));

        // HTLC claim with the preimage; refund after the timeout.
        let mut claim = policy.spend(1, amount, 7);
        claim.witness[0] = CondWitness::Preimage(preimage);
        claim.witness[1] =
            CondWitness::Signatures(vec![Signer { key: 0, pubkey: b.public_key(), signature: b.sign(&body).unwrap() }]);
        assert_eq!(claim.check(&body, &outputs, 1, 0), Ok(()));
        claim.witness[0] = CondWitness::Preimage(d(78));
        assert_eq!(claim.check(&body, &outputs, 1, 0), Err(Error::PolicyPreimage));
        let mut refund = policy.spend(2, amount, 7);
        refund.witness[1] =
            CondWitness::Signatures(vec![Signer { key: 0, pubkey: a.public_key(), signature: a.sign(&body).unwrap() }]);
        assert_eq!(refund.check(&body, &outputs, 99, 0), Err(Error::PolicyLocked));
        assert_eq!(refund.check(&body, &outputs, 100, 0), Ok(()));

        // Eltoo update: rebindable signatures with leaf index = state over
        // the covered outputs; the state must exceed the output's.
        let mut update = policy.spend(3, amount, 7);
        update.state = 4;
        update.covered = (0, 2);
        let covered = update.covered_outputs(&outputs).unwrap();
        let msg = rebind_message(&channel, 4, &covered);
        let mut a4 = key(1);
        a4.set_next_index(4);
        let mut b4 = key(2);
        b4.set_next_index(4);
        update.witness[0] = CondWitness::Signatures(vec![
            Signer { key: 0, pubkey: a4.public_key(), signature: a4.sign(&msg).unwrap() },
            Signer { key: 1, pubkey: b4.public_key(), signature: b4.sign(&msg).unwrap() },
        ]);
        assert_eq!(update.check(&body, &outputs, 1, 0), Ok(()));
        // The same signatures spend any earlier state: the body is not covered.
        let other_body = d(123);
        assert_eq!(update.check(&other_body, &outputs, 1, 0), Ok(()));
        // But not a lower state, nor with a leaf index other than the state.
        update.state = 3;
        assert_eq!(update.check(&body, &outputs, 1, 0), Err(Error::PolicySignatures));
        update.state = 4;
        let mut a5 = key(1);
        a5.set_next_index(5);
        update.witness[0] = CondWitness::Signatures(vec![
            Signer { key: 0, pubkey: a5.public_key(), signature: a5.sign(&msg).unwrap() },
            Signer { key: 1, pubkey: b4.public_key(), signature: b4.sign(&msg).unwrap() },
        ]);
        assert_eq!(update.check(&body, &outputs, 1, 0), Err(Error::PolicySignatures));
        // State 3 would fail the ordering even with valid signatures.
        let mut stale = policy.spend(3, amount, 7);
        stale.state = 3;
        stale.covered = (0, 2);
        let msg3 = rebind_message(&channel, 3, &covered);
        let mut a3 = key(1);
        a3.set_next_index(3);
        let mut b3 = key(2);
        b3.set_next_index(3);
        stale.witness[0] = CondWitness::Signatures(vec![
            Signer { key: 0, pubkey: a3.public_key(), signature: a3.sign(&msg3).unwrap() },
            Signer { key: 1, pubkey: b3.public_key(), signature: b3.sign(&msg3).unwrap() },
        ]);
        assert_eq!(stale.check(&body, &outputs, 1, 0), Err(Error::PolicyState));

        // Settlement: no signature, after the delay, into the named outputs,
        // which the spend points at as its covered run.
        let mut settle_spend = policy.spend(4, amount, 7);
        settle_spend.covered = (0, 2);
        assert_eq!(settle_spend.signatures(), 0);
        assert_eq!(settle_spend.check(&body, &outputs, 150, 10), Err(Error::PolicyLocked));
        assert_eq!(settle_spend.check(&body, &outputs, 154, 10), Ok(()));
        let without = &outputs[..1];
        assert_eq!(settle_spend.check(&body, without, 154, 10), Err(Error::PolicyCovered));
        let mut wrong_run = settle_spend.clone();
        wrong_run.covered = (0, 1);
        assert_eq!(wrong_run.check(&body, &outputs, 154, 10), Err(Error::PolicyCovenant));
        // A run that is not from the transaction's first output is none.
        let mut later = settle_spend.clone();
        later.covered = (1, 2);
        assert_eq!(later.check(&body, &outputs, 154, 10), Err(Error::PolicyCovered));
        let mut off = settle_spend.clone();
        off.covered = (2, 5);
        assert_eq!(off.check(&body, &outputs, 154, 10), Err(Error::PolicyCovered));
        let _ = (&mut a, &mut b, &mut c);
    }

    // -----------------------------------------------------------------------
    // Views
    // -----------------------------------------------------------------------

    /// A policy of every kind of leaf, its three keys, the outputs of a
    /// transaction spending it (the first two are the covenant's), the
    /// channel and the hash lock's preimage.
    struct Sample {
        policy: Policy,
        keys: [Key; 3],
        outputs: Vec<Output>,
        channel: Digest,
        preimage: Digest,
    }

    const AMOUNT: u64 = 1000;

    fn sample() -> Sample {
        let keys = [key(1), key(2), key(3)];
        let hashes: Vec<Digest> = keys.iter().map(|k| pubkey_hash(&k.public_key())).collect();
        let (channel, preimage) = (d(5), d(77));
        let outputs = vec![
            Output::with_memo(&d(11), 500, memo5(d(12))),
            Output::with_memo(&d(13), 490, memo5(d(14))),
            Output::with_memo(&d(1), 10, memo5(d(2))),
        ];
        let settle: Vec<(Commitment, Digest)> = outputs[..2].iter().map(|o| (o.commitment, o.slot())).collect();
        let policy = Policy::new(vec![
            Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 2, keys: hashes.clone() }]),
            Leaf::new(vec![
                Cond::Hash(hash_lock(&preimage)),
                Cond::Thresh { mode: Mode::Body, m: 1, keys: hashes[1..2].to_vec() },
            ]),
            Leaf::new(vec![Cond::After(100), Cond::Thresh { mode: Mode::Body, m: 1, keys: hashes[..1].to_vec() }]),
            Leaf::new(vec![
                Cond::Thresh { mode: Mode::Rebindable { channel }, m: 2, keys: hashes[..2].to_vec() },
                Cond::State(3),
            ]),
            Leaf::new(vec![Cond::Older(144), Cond::Outputs(settle)]),
        ]);
        Sample { policy, keys, outputs, channel, preimage }
    }

    impl Sample {
        fn signer(&self, key: u8, which: usize, index: u64, msg: &Digest) -> Signer {
            let mut k = self.keys[which].clone();
            k.set_next_index(index);
            Signer { key, pubkey: k.public_key(), signature: k.sign(msg).unwrap() }
        }

        /// A satisfied spend through each leaf, for a transaction of body
        /// `body`: the multisig, the HTLC claim, its refund, the update to
        /// state 4 and the settlement.
        fn spends(&self, body: &Digest) -> Vec<PolicyInput> {
            let mut multisig = self.policy.spend(0, AMOUNT, 7);
            multisig.witness[0] = CondWitness::Signatures(vec![self.signer(0, 0, 0, body), self.signer(2, 2, 0, body)]);
            let mut claim = self.policy.spend(1, AMOUNT, 7);
            claim.witness[0] = CondWitness::Preimage(self.preimage);
            claim.witness[1] = CondWitness::Signatures(vec![self.signer(0, 1, 0, body)]);
            let mut refund = self.policy.spend(2, AMOUNT, 7);
            refund.witness[1] = CondWitness::Signatures(vec![self.signer(0, 0, 1, body)]);
            let mut update = self.policy.spend(3, AMOUNT, 7);
            update.state = 4;
            update.covered = (0, 2);
            let msg = rebind_message(&self.channel, 4, &update.covered_outputs(&self.outputs).unwrap());
            update.witness[0] = CondWitness::Signatures(vec![self.signer(0, 0, 4, &msg), self.signer(1, 1, 4, &msg)]);
            let mut settle = self.policy.spend(4, AMOUNT, 7);
            settle.covered = (0, 2);
            vec![multisig, claim, refund, update, settle]
        }
    }

    /// A policy's view reads what the owned policy wrote: the same leaves,
    /// conditions, hashes, blocks, root and paths, and the same bytes back.
    #[test]
    fn views_read_what_owned_forms_write() {
        let s = sample();
        let bytes = s.policy.to_bytes();
        let view = PolicyRef::from_bytes(&bytes).unwrap();
        assert_eq!(view.as_bytes(), &bytes[..]);
        assert!(view.valid() && s.policy.valid());
        assert_eq!(view.to_policy(), s.policy);
        assert_eq!(view.leaves().len(), s.policy.leaves.len());
        assert_eq!(view.root(), s.policy.root());
        for (i, (leaf, owned)) in view.leaves().zip(&s.policy.leaves).enumerate() {
            assert_eq!(leaf.to_leaf(), *owned);
            assert_eq!(leaf.size(), owned.size());
            assert_eq!(leaf.conds().len(), owned.conds.len());
            assert_eq!((leaf.valid(), leaf.signatures()), (owned.valid(), owned.signatures()));
            // The hash is the one the proofs' rules give the leaf.
            assert_eq!(leaf.hash(), conditions::leaf(&owned.rules()));
            assert_eq!(leaf.hash(), owned.hash());
            assert_eq!(view.siblings(i), s.policy.siblings(i));
            assert_eq!(root_from_path(&leaf.hash(), i, &view.siblings(i)), view.root());
            for (c, o) in leaf.conds().zip(&owned.conds) {
                assert_eq!(c.to_cond(), *o);
                assert_eq!((c.valid(), c.signatures()), (o.valid(), o.signatures()));
            }
            // A leaf's bytes are a leaf, and the policy's bytes hold them.
            let (again, rest) = LeafRef::read(leaf.as_bytes()).unwrap();
            assert!(rest.is_empty());
            assert_eq!(again, leaf);
        }
        // The covered digest and the channel's message are the rules'
        // too, and the tree's root.
        let run: Vec<(Commitment, Digest)> = s.outputs.iter().map(|o| (o.commitment, o.slot())).collect();
        let listed: Vec<crate::ledger::Output> = s.outputs.iter().map(Output::listed).collect();
        assert_eq!(covered_digest_outputs(&s.outputs), covered_digest(&run));
        assert_eq!(covered_digest(&run), conditions::covered(&listed));
        assert_eq!(covered_digest(&[]), EMPTY);
        assert_eq!(rebind_message(&d(9), 4, &run), conditions::rebind_message(&d(9), &covered_digest(&run), 4));
        let rules = conditions::Policy(s.policy.leaves.iter().map(Leaf::rules).collect());
        assert_eq!(s.policy.root(), rules.root());
        assert_eq!(s.policy.siblings(1), rules.path(1));
    }

    /// A spend is checked from its bytes as the owned spend is: for every
    /// leaf, satisfied and not (a height too low, another body, other
    /// outputs, a run past them).
    #[test]
    fn a_spend_is_checked_from_its_bytes() {
        let s = sample();
        let body = d(4242);
        let other_outputs: Vec<Output> = s.outputs.iter().rev().copied().collect();
        let mut verdicts = Vec::new();
        for (i, spend) in s.spends(&body).iter().enumerate() {
            let bytes = spend.to_bytes();
            assert_eq!(bytes.len(), spend.size());
            let (view, rest) = PolicyInputRef::read(&bytes).unwrap();
            assert!(rest.is_empty());
            assert_eq!(view.as_bytes(), &bytes[..]);
            assert_eq!(view.size(), bytes.len());
            assert_eq!(view.to_input(), *spend);
            assert_eq!(
                (view.amount(), view.position(), view.index(), view.state(), view.covered()),
                (spend.amount, spend.position, spend.index, spend.state, spend.covered)
            );
            assert_eq!(view.siblings(), &spend.siblings);
            assert_eq!(view.leaf().to_leaf(), spend.leaf);
            assert_eq!(view.policy(), s.policy.root());
            assert_eq!(view.commitment(), key_commitment(&s.policy.root(), AMOUNT));
            assert_eq!((view.commitment(), view.signatures()), (spend.commitment(), spend.signatures()));
            assert_eq!(view.witnesses().count(), spend.witness.len());
            // The position sits where POSITION_AT says: rewriting it there
            // is the same spend at another position.
            let mut moved = bytes.clone();
            moved[PolicyInputRef::POSITION_AT..PolicyInputRef::POSITION_AT + 8].copy_from_slice(&99u64.to_le_bytes());
            let (moved, _) = PolicyInputRef::read(&moved).unwrap();
            assert_eq!((moved.position(), moved.commitment()), (99, view.commitment()));
            for (height, created) in [(1, 0), (99, 0), (100, 0), (153, 10), (154, 10)] {
                for (b, outs) in [(body, &s.outputs), (d(1), &s.outputs), (body, &other_outputs)] {
                    let got = view.check(&b, outs, height, created);
                    assert_eq!(got, spend.check(&b, outs, height, created), "leaf {i} at {height}/{created}");
                    assert_eq!(moved.check(&b, outs, height, created), got);
                    verdicts.push(got);
                }
            }
            assert_eq!(view.check(&body, &s.outputs, 200, 10), Ok(()), "leaf {i}");
            // Trailing bytes are handed back, not read.
            let longer = [&bytes[..], &[1, 2, 3]].concat();
            let (again, rest) = PolicyInputRef::read(&longer).unwrap();
            assert_eq!((again.as_bytes(), rest), (&bytes[..], &[1u8, 2, 3][..]));
        }
        // Every kind of verdict the sample can give was seen.
        for want in [Ok(()), Err(Error::PolicySignatures), Err(Error::PolicyLocked), Err(Error::PolicyCovenant)] {
            assert!(verdicts.contains(&want), "{want:?} never seen");
        }
        // The update's own failures: a state no newer, a run past the outputs.
        let mut update = s.spends(&body)[3].clone();
        update.covered = (2, 5);
        let bytes = update.to_bytes();
        assert_eq!(PolicyInputRef::read(&bytes).unwrap().0.check(&body, &s.outputs, 1, 0), Err(Error::PolicyCovered));
        let mut stale = s.policy.spend(3, AMOUNT, 7);
        stale.state = 3;
        stale.covered = (0, 2);
        let msg = rebind_message(&s.channel, 3, &stale.covered_outputs(&s.outputs).unwrap());
        stale.witness[0] = CondWitness::Signatures(vec![s.signer(0, 0, 3, &msg), s.signer(1, 1, 3, &msg)]);
        let bytes = stale.to_bytes();
        assert_eq!(PolicyInputRef::read(&bytes).unwrap().0.check(&body, &s.outputs, 1, 0), Err(Error::PolicyState));
        // A wrong preimage.
        let mut claim = s.spends(&body)[1].clone();
        claim.witness[0] = CondWitness::Preimage(d(78));
        let bytes = claim.to_bytes();
        assert_eq!(PolicyInputRef::read(&bytes).unwrap().0.check(&body, &s.outputs, 1, 0), Err(Error::PolicyPreimage));
        // A leaf that reads but makes no sense (a threshold of none of its keys).
        let hollow = Policy::new(vec![Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 0, keys: vec![d(1)] }])]);
        let bytes = hollow.spend(0, 5, 1).to_bytes();
        let (view, _) = PolicyInputRef::read(&bytes).unwrap();
        assert!(!view.leaf().valid());
        assert_eq!(view.check(&body, &s.outputs, 1, 0), Err(Error::Malformed("spend policy")));
    }

    /// Encodings that are not a leaf, a policy or a spend are refused when
    /// read, so a view never holds one.
    #[test]
    fn malformed_encodings_are_refused() {
        let s = sample();
        let body = d(4242);
        let leaf_bytes = |l: &Leaf| {
            let mut b = Vec::new();
            l.write(&mut b);
            b
        };
        let thresh = leaf_bytes(&s.policy.leaves[3]);
        assert!(LeafRef::read(&thresh).is_some());
        // The layout: n_conds, tag, mode, channel (32), m, n, keys.
        let (n_conds, tag, mode, m_at, n_at) = (0, 1, 2, 35, 36);
        assert_eq!((thresh[n_conds], thresh[tag], thresh[mode], thresh[m_at], thresh[n_at]), (2, TAG_THRESH, 1, 2, 2));
        let with = |at: usize, v: u8| {
            let mut b = thresh.clone();
            b[at] = v;
            b
        };
        assert!(LeafRef::read(&with(n_conds, 0)).is_none(), "no conditions");
        assert!(LeafRef::read(&with(n_conds, LEAF_CONDS as u8 + 1)).is_none(), "too many conditions");
        assert!(LeafRef::read(&with(n_conds, 3)).is_none(), "a condition short");
        assert!(LeafRef::read(&with(tag, 6)).is_none(), "an unknown condition");
        assert!(LeafRef::read(&with(mode, 2)).is_none(), "an unknown mode");
        assert!(LeafRef::read(&with(n_at, MAX_KEYS as u8 + 1)).is_none(), "too many keys");
        assert!(LeafRef::read(&with(n_at, 3)).is_none(), "a key short");
        for cut in 0..thresh.len() {
            assert!(LeafRef::read(&thresh[..cut]).is_none(), "cut at {cut}");
        }
        // m is not checked when read: it is `valid`'s to refuse.
        let three_of_two = with(m_at, 3);
        let (hollow, _) = LeafRef::read(&three_of_two).unwrap();
        assert!(!hollow.valid());
        // A covenant of more outputs than one may name; one of none reads
        // and is not valid.
        let covenant = leaf_bytes(&Leaf::new(vec![Cond::Outputs(vec![(d(1), d(2))])]));
        let mut many = covenant.clone();
        many[2] = MAX_COVENANT as u8 + 1;
        assert!(LeafRef::read(&many).is_none());
        let (none, rest) = LeafRef::read(&[1, TAG_OUTPUTS, 0]).unwrap();
        assert!(rest.is_empty() && !none.valid());
        // A height, an age or a state number past its bound is no
        // condition: it is refused when read. The largest of each reads,
        // and hashes.
        for (tag, max) in [(TAG_AFTER, MAX_LOCK), (TAG_OLDER, MAX_LOCK), (TAG_STATE, MAX_STATE)] {
            let leaf = |v: u32| [&[1, tag][..], &v.to_le_bytes()].concat();
            let most = leaf(max);
            let (most, rest) = LeafRef::read(&most).unwrap();
            assert!(rest.is_empty() && most.valid());
            let _ = most.hash();
            for v in [max + 1, 1 << 31, u32::MAX] {
                assert!(LeafRef::read(&leaf(v)).is_none(), "tag {tag} value {v}");
            }
        }
        for cond in [Cond::After(MAX_LOCK + 1), Cond::Older(u32::MAX), Cond::State(MAX_STATE + 1)] {
            let leaf = Leaf::new(vec![cond]);
            assert!(!leaf.valid());
            assert!(LeafRef::read(&leaf_bytes(&leaf)).is_none());
        }

        // Policies: no leaves, too many, bytes after the last.
        let policy = s.policy.to_bytes();
        assert!(PolicyRef::from_bytes(&policy).is_ok());
        assert!(PolicyRef::from_bytes(&[]).is_err());
        assert!(PolicyRef::from_bytes(&[0]).is_err());
        assert!(PolicyRef::from_bytes(&[policy.as_slice(), &[0]].concat()).is_err());
        assert!(PolicyRef::from_bytes(&policy[..policy.len() - 1]).is_err());
        let seventeen = Policy::new(vec![Leaf::new(vec![Cond::After(1)]); MAX_LEAVES + 1]).to_bytes();
        assert!(PolicyRef::from_bytes(&seventeen).is_err());
        let sixteen = Policy::new(vec![Leaf::new(vec![Cond::After(1)]); MAX_LEAVES]).to_bytes();
        assert_eq!(PolicyRef::from_bytes(&sixteen).unwrap().leaves().len(), MAX_LEAVES);

        // Spends: a leaf index or a state number out of range, a signature
        // cut short, a signer too many, a public key of no height.
        let spend = s.spends(&body)[3].to_bytes();
        assert!(PolicyInputRef::read(&spend).is_some());
        let (index_at, state_at) = (16, 17 + POLICY_DEPTH * DIGEST_BYTES);
        let mut b = spend.clone();
        b[index_at] = MAX_LEAVES as u8;
        assert!(PolicyInputRef::read(&b).is_none(), "leaf index");
        let mut b = spend.clone();
        b[state_at..state_at + 4].copy_from_slice(&(MAX_STATE + 1).to_le_bytes());
        assert!(PolicyInputRef::read(&b).is_none(), "state number");
        for cut in [0, 15, state_at, spend.len() - 1, spend.len() - Signature::size(4)] {
            assert!(PolicyInputRef::read(&spend[..cut]).is_none(), "cut at {cut}");
        }
        let witness_at = state_at + 4 + 2 + thresh.len();
        assert_eq!(spend[witness_at], 2, "the signer count");
        let mut b = spend.clone();
        b[witness_at] = 3;
        assert!(PolicyInputRef::read(&b).is_none(), "a signer short");
        let mut b = spend.clone();
        b[witness_at] = MAX_KEYS as u8 + 1;
        assert!(PolicyInputRef::read(&b).is_none(), "too many signers");
        let height_at = witness_at + 1 + 1 + PublicKey::SIZE - 1;
        assert_eq!(spend[height_at], 4, "the first signer's key height");
        let mut b = spend.clone();
        b[height_at] = 0;
        assert!(PolicyInputRef::read(&b).is_none(), "a key of no height");
        // A key of another height says the signature is another length:
        // the bytes after it no longer fit.
        let mut b = spend.clone();
        b[height_at] = 5;
        assert!(PolicyInputRef::read(&b).is_none_or(|(v, rest)| v.size() != spend.len() || !rest.is_empty()));
    }

    /// The decoders of untrusted bytes, fuzzed: nothing makes reading or
    /// checking panic, a view's bytes are the bytes read, and the owned
    /// form it gives encodes to them again.
    #[test]
    fn fuzz_view_decoders() {
        let s = sample();
        let body = d(4242);
        let spends: Vec<Vec<u8>> = s.spends(&body).iter().map(PolicyInput::to_bytes).collect();
        crate::test_util::fuzz_decoder("PolicyInputRef::read", &spends, 4_000, |b| {
            PolicyInputRef::read(b).map(|(view, rest)| {
                assert_eq!(view.to_input().to_bytes(), view.as_bytes());
                let _ = (view.policy(), view.commitment(), view.signatures(), view.leaf().valid());
                let _ = view.check(&body, &s.outputs, 200, 10);
                let _ = format!("{view:?}");
                Some([view.as_bytes(), rest].concat())
            })
        });
        crate::test_util::fuzz_decoder("PolicyRef::from_bytes", &[s.policy.to_bytes()], 20_000, |b| {
            PolicyRef::from_bytes(b).ok().map(|view| {
                assert_eq!(view.to_policy().to_bytes(), view.as_bytes());
                let _ = (view.root(), view.valid(), view.siblings(view.leaves().len() - 1));
                Some(view.as_bytes().to_vec())
            })
        });
    }

    /// Owned forms that have no encoding: validity says so, a check is
    /// `Malformed`, and hashing one panics rather than commit to a policy
    /// that could never be spent. A witness of another kind than its
    /// condition's is `Witness`.
    #[test]
    fn owned_forms_out_of_bounds() {
        let s = sample();
        let body = d(4242);
        let too_many_conds = Leaf::new(vec![Cond::After(1); LEAF_CONDS + 1]);
        let too_many_keys = Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 1, keys: vec![d(1); MAX_KEYS + 1] }]);
        let too_many_outputs = Leaf::new(vec![Cond::Outputs(vec![(d(1), d(2)); MAX_COVENANT + 1])]);
        let too_late = Leaf::new(vec![Cond::After(u32::MAX)]);
        let quiet = crate::test_util::Quiet::new();
        for leaf in [Leaf::new(vec![]), too_many_conds, too_many_keys, too_many_outputs, too_late] {
            assert!(!leaf.valid());
            assert!(std::panic::catch_unwind(|| leaf.hash()).is_err());
            let policy = Policy::new(vec![leaf.clone()]);
            assert!(!policy.valid());
            assert!(std::panic::catch_unwind(|| policy.root()).is_err());
            let mut spend = s.spends(&body)[0].clone();
            spend.leaf = leaf;
            assert_eq!(spend.check(&body, &s.outputs, 1, 0), Err(Error::Malformed("spend policy")));
        }
        let crowded = Policy::new(vec![Leaf::new(vec![Cond::After(1)]); MAX_LEAVES + 1]);
        assert!(!crowded.valid());
        assert!(std::panic::catch_unwind(|| crowded.root()).is_err());
        drop(quiet);
        // The largest leaves there are do hash, and read back.
        let full_keys = Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 32, keys: (0..32).map(d).collect() }; 4]);
        let full_outputs = Leaf::new(vec![Cond::Outputs((0..128).map(|i| (d(i), d(i + 500))).collect())]);
        for leaf in [full_keys, full_outputs] {
            assert!(leaf.valid());
            let mut bytes = Vec::new();
            leaf.write(&mut bytes);
            let (view, rest) = LeafRef::read(&bytes).unwrap();
            assert!(rest.is_empty());
            assert_eq!(view.hash(), leaf.hash());
            assert_eq!(view.to_leaf(), leaf);
        }
        // Witnesses of the wrong kind, a leaf index no tree has, a witness missing.
        let good = s.spends(&body)[1].clone();
        assert_eq!(good.check(&body, &s.outputs, 1, 0), Ok(()));
        let mut swapped = good.clone();
        swapped.witness.swap(0, 1);
        assert_eq!(swapped.check(&body, &s.outputs, 1, 0), Err(Error::PolicyWitness));
        let mut none = good.clone();
        none.witness[0] = CondWitness::None;
        assert_eq!(none.check(&body, &s.outputs, 1, 0), Err(Error::PolicyWitness));
        let mut missing = good.clone();
        missing.witness.pop();
        assert_eq!(missing.check(&body, &s.outputs, 1, 0), Err(Error::Malformed("spend policy")));
        let mut off = good.clone();
        off.index = MAX_LEAVES as u8;
        assert_eq!(off.check(&body, &s.outputs, 1, 0), Err(Error::Malformed("spend policy")));
        assert!(Error::PolicyCovenant.to_string().contains("covenant"));
    }
}
