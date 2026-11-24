//! An output as the chain lists it, and the hashes it is known by.
//!
//! An output pays an amount to a key. On the chain it is a
//! **commitment** (the hash of the key's hash and the amount), a memo
//! and the amount; whose it is stays off the chain. In the state it is a
//! leaf: the hash of all of that and the height of the block that made
//! it.
//!
//! This is the least of the ledger's rules ([`crate::ledger`]), and
//! under the rest of them: the conditions an output is spent on
//! ([`crate::conditions`]) and the names ([`crate::registry`]) are said
//! in terms of it, and the ledger in terms of those.
//!
//! Every hash here is one block of Blake3 in a domain of its own
//! ([`crate::hash`]), so that a circuit pays one row for it.

use crate::hash::{DOM_COMMITMENT, DOM_OUT_ITEM, DOM_PUBKEY, DOM_STATE_LEAF, Digest, hash_domain};
use crate::xmss::PublicKey;

/// Bytes of a memo.
pub const MEMO: usize = 20;
pub type Memo = [u8; MEMO];

/// One block of Blake3, of `parts` end to end: what is left of it zero.
pub(crate) fn block(parts: &[&[u8]]) -> [u8; 64] {
    let mut out = [0u8; 64];
    let mut at = 0;
    for p in parts {
        out[at..at + p.len()].copy_from_slice(p);
        at += p.len();
    }
    out
}

/// A key's hash: of its root, its seed and its tree's height.
pub fn key_hash(pk: &PublicKey) -> Digest {
    hash_domain(DOM_PUBKEY, &block(&[&pk.root, &pk.pub_seed, &(pk.height as u32).to_le_bytes()]))
}

/// An output's commitment: to whose it is and how much.
pub fn commitment(key_hash: &Digest, amount: u64) -> Digest {
    hash_domain(DOM_COMMITMENT, &block(&[key_hash, &amount.to_le_bytes()]))
}

/// An output as the chain lists it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output {
    pub commitment: Digest,
    pub memo: Memo,
    pub amount: u64,
}

impl Output {
    /// An output of `amount` to the key of `key_hash`.
    pub fn to(key_hash: &Digest, amount: u64, memo: Memo) -> Output {
        Output { commitment: commitment(key_hash, amount), memo, amount }
    }

    /// The output as a transaction's id and a block's list take it in.
    pub fn item(&self) -> Digest {
        hash_domain(DOM_OUT_ITEM, &block(&[&self.commitment, &self.memo, &self.amount.to_le_bytes()]))
    }

    /// Its leaf in the state, made at `height`.
    pub fn leaf(&self, height: u32) -> Digest {
        let parts: [&[u8]; 4] = [&self.commitment, &self.memo, &self.amount.to_le_bytes(), &height.to_le_bytes()];
        hash_domain(DOM_STATE_LEAF, &block(&parts))
    }
}
