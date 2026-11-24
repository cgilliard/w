//! The base every module above [`crate::blake3`] hashes with: the digest
//! type, the empty digest, the domain-separated hash and the list of its
//! domain tags.
//!
//! Every use of [`hash_domain`] has a tag of its own, listed here and
//! nowhere else, so that no two uses can share one: a constant added
//! below without a place in [`DOMAINS`], or with a tag already taken,
//! does not compile.
//!
//! # How a domain separates
//!
//! A domain's hash is Blake3's keyed hash under the key whose first four
//! bytes are the tag, little-endian, and whose other bytes are zero. So
//! anyone with a Blake3 library can compute any hash of this chain, and
//! two domains are two keyed functions: no input of one is an input of
//! another.
//!
//! In a circuit the key is the chaining value a hash starts from, a
//! constant. A domain costs a proof nothing: no block is spent on a tag.

use crate::blake3;

/// A hash output: 32 bytes.
pub type Digest = [u8; blake3::OUT_LEN];

/// The all-zero digest: an empty leaf, an absent value, padding.
pub const EMPTY: Digest = [0; blake3::OUT_LEN];

// ---------------------------------------------------------------------------
// Domain tags
// ---------------------------------------------------------------------------

/// A leaf of a Merkle tree over a codeword ([`crate::merkle`]).
pub(crate) const DOM_LEAF: u32 = 1;
/// A node of a Merkle tree: two digests.
pub(crate) const DOM_NODE: u32 = 2;
/// The start of a proof's transcript: its label
/// ([`crate::challenger`]).
pub(crate) const DOM_TRANSCRIPT: u32 = 3;
/// A transcript step that takes in what the prover sent.
pub(crate) const DOM_ABSORB: u32 = 4;
/// A transcript step that gives a challenge.
pub(crate) const DOM_CHALLENGE: u32 = 5;
/// A transcript step that takes in a ground nonce.
pub(crate) const DOM_GRIND: u32 = 6;

/// What a proof of a compiled computation is of: the elements it names,
/// hashed to the digest that is its public value ([`crate::alg`]).
pub(crate) const DOM_STATEMENT: u32 = 7;

/// The digest an XMSS signature signs ([`crate::xmss`]).
pub(crate) const DOM_XMSS_MSG: u32 = 8;
/// An XMSS leaf: the hashes of a WOTS public key's chain ends.
pub(crate) const DOM_XMSS_LEAF: u32 = 9;
/// A node of an XMSS key's tree: two digests.
pub(crate) const DOM_XMSS_TREE: u32 = 10;

/// A signature's entry in the set of what a block's keys signed
/// ([`crate::signature`]).
pub(crate) const DOM_SIGNED: u32 = 11;

/// A node of the tree over a block's entries ([`crate::signed`]).
pub(crate) const DOM_SIGNED_NODE: u32 = 12;

/// The proof of work ([`crate::pow`]): the mark of a dataset item's
/// first key (not a hash's domain), the fold of the mix, the seed of a
/// header's work, and its result.
pub(crate) const DOM_POW_ITEM: u32 = 13;
pub(crate) const DOM_POW_MIX: u32 = 14;
pub(crate) const DOM_POW_SEED: u32 = 15;
pub(crate) const DOM_POW_RESULT: u32 = 16;

/// The ledger ([`crate::ledger`]): a key's hash, an output's
/// commitment, an output as a transaction lists it, an output's leaf in
/// the state, a node of the state, a transaction's body (its head, and
/// an input and an output taken in), and the block's lists of inputs
/// and of outputs.
pub(crate) const DOM_PUBKEY: u32 = 17;
pub(crate) const DOM_COMMITMENT: u32 = 18;
pub(crate) const DOM_OUT_ITEM: u32 = 19;
pub(crate) const DOM_STATE_LEAF: u32 = 20;
pub(crate) const DOM_STATE_NODE: u32 = 21;
pub(crate) const DOM_BODY: u32 = 22;
pub(crate) const DOM_BODY_IN: u32 = 23;
pub(crate) const DOM_BODY_OUT: u32 = 24;
pub(crate) const DOM_INPUTS: u32 = 25;
pub(crate) const DOM_OUTPUTS: u32 = 26;

/// What a join of a block's proofs rested on ([`crate::block_proof`]), and
/// the tree of the block proofs a chain takes ([`crate::chain_proof`]): its
/// leaves and its nodes.
pub(crate) const DOM_RESTED: u32 = 27;
pub(crate) const DOM_PLAN_LEAF: u32 = 28;
pub(crate) const DOM_PLAN_NODE: u32 = 29;

/// Names ([`crate::registry`]): a name's hash, a record's, a name's leaf
/// in the registry and a node of it, a commitment to a name, an
/// operation as a transaction's id takes it, what an owner signs to
/// change a record, and the state's root over outputs and names.
pub(crate) const DOM_NAME: u32 = 30;
pub(crate) const DOM_RECORD: u32 = 31;
pub(crate) const DOM_NAME_LEAF: u32 = 32;
pub(crate) const DOM_NAME_NODE: u32 = 33;
pub(crate) const DOM_COMMIT: u32 = 34;
pub(crate) const DOM_OP: u32 = 35;
pub(crate) const DOM_UPDATE: u32 = 36;
pub(crate) const DOM_STATE: u32 = 37;

/// A name's operation taken into a transaction's body, and into the
/// block's list of what it makes.
pub(crate) const DOM_BODY_OP: u32 = 38;
pub(crate) const DOM_OPS: u32 = 39;

/// Spend policies ([`crate::conditions`]): a condition, a leaf of
/// conditions, a node of a policy's tree, the keys of a threshold, and
/// a hash lock.
pub(crate) const DOM_COND: u32 = 40;
pub(crate) const DOM_POLICY_LEAF: u32 = 41;
pub(crate) const DOM_POLICY_NODE: u32 = 42;
pub(crate) const DOM_SIGNERS: u32 = 43;
pub(crate) const DOM_HASHLOCK: u32 = 44;

/// The outputs a policy's condition is on, hashed one after another;
/// and what a channel's keys sign in place of a transaction's id.
pub(crate) const DOM_COVERED: u32 = 45;
pub(crate) const DOM_REBIND: u32 = 46;

/// What a header's work is done on, and a header's id
/// ([`crate::header`]).
pub(crate) const DOM_HEADER: u32 = 47;
pub(crate) const DOM_BLOCK: u32 = 48;

/// An identity: the hash of a Dilithium public key
/// ([`crate::address`]).
pub(crate) const DOM_ID: u32 = 49;
/// The outputs' tree's nodes still to be joined, as a prover holds
/// them while a run adds outputs ([`crate::segment`]).
pub(crate) const DOM_STACK: u32 = 50;
/// A block's body, by its running hashes; and what the proofs do not
/// read of a header ([`crate::block`]).
pub(crate) const DOM_BLOCK_BODY: u32 = 51;
pub(crate) const DOM_HEADER_REST: u32 = 52;

/// Every tag above.
const DOMAINS: &[u32] = &[
    DOM_LEAF,
    DOM_NODE,
    DOM_TRANSCRIPT,
    DOM_ABSORB,
    DOM_CHALLENGE,
    DOM_GRIND,
    DOM_STATEMENT,
    DOM_XMSS_MSG,
    DOM_XMSS_LEAF,
    DOM_XMSS_TREE,
    DOM_SIGNED,
    DOM_SIGNED_NODE,
    DOM_POW_ITEM,
    DOM_POW_MIX,
    DOM_POW_SEED,
    DOM_POW_RESULT,
    DOM_PUBKEY,
    DOM_COMMITMENT,
    DOM_OUT_ITEM,
    DOM_STATE_LEAF,
    DOM_STATE_NODE,
    DOM_BODY,
    DOM_BODY_IN,
    DOM_BODY_OUT,
    DOM_INPUTS,
    DOM_OUTPUTS,
    DOM_RESTED,
    DOM_PLAN_LEAF,
    DOM_PLAN_NODE,
    DOM_NAME,
    DOM_RECORD,
    DOM_NAME_LEAF,
    DOM_NAME_NODE,
    DOM_COMMIT,
    DOM_OP,
    DOM_UPDATE,
    DOM_STATE,
    DOM_BODY_OP,
    DOM_OPS,
    DOM_COND,
    DOM_POLICY_LEAF,
    DOM_POLICY_NODE,
    DOM_SIGNERS,
    DOM_HASHLOCK,
    DOM_COVERED,
    DOM_REBIND,
    DOM_HEADER,
    DOM_BLOCK,
    DOM_ID,
];

// No two domains share a tag, and none is zero: the zero key is nobody's.
const _: () = {
    let mut i = 0;
    while i < DOMAINS.len() {
        assert!(DOMAINS[i] != 0, "a hash domain has the tag zero");
        let mut j = i + 1;
        while j < DOMAINS.len() {
            assert!(DOMAINS[i] != DOMAINS[j], "two hash domains share a tag");
            j += 1;
        }
        i += 1;
    }
};

// ---------------------------------------------------------------------------
// Hashing
// ---------------------------------------------------------------------------

/// A digest as the bytes it is written as.
pub fn digest_to_bytes(d: &Digest) -> [u8; 32] {
    *d
}

/// The digest 32 bytes are, if they are 32.
pub fn digest_from_bytes(bytes: &[u8]) -> Option<Digest> {
    bytes.try_into().ok()
}

/// A domain's key, as the eight words a hash under it starts from.
pub(crate) const fn domain_key(domain: u32) -> [u32; 8] {
    [domain, 0, 0, 0, 0, 0, 0, 0]
}

/// The hash of `input` in `domain`.
pub(crate) fn hash_domain(domain: u32, input: &[u8]) -> Digest {
    blake3::keyed_hash_words(&domain_key(domain), input)
}

/// [`hash_domain`] of each of the `out.len()` inputs of `item_len` bytes
/// that `input` is, one after another: a level of a Merkle tree.
pub(crate) fn hash_domain_many(domain: u32, input: &[u8], item_len: usize, out: &mut [Digest]) {
    blake3::keyed_hash_many(&domain_key(domain), input, item_len, out);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_domain_is_the_keyed_hash_under_its_tag() {
        let mut key = [0u8; 32];
        key[..4].copy_from_slice(&DOM_NODE.to_le_bytes());
        for len in [0, 1, 64, 65, 3000] {
            let input: Vec<u8> = (0..len).map(|i| i as u8).collect();
            assert_eq!(hash_domain(DOM_NODE, &input), blake3::keyed_hash(&key, &input));
        }
    }

    #[test]
    fn domains_differ_and_none_is_the_plain_hash() {
        let input = [7u8; 64];
        let all: Vec<Digest> = DOMAINS.iter().map(|d| hash_domain(*d, &input)).collect();
        for (i, a) in all.iter().enumerate() {
            assert_ne!(*a, blake3::hash(&input));
            assert!(all[i + 1..].iter().all(|b| a != b));
        }
    }
}
