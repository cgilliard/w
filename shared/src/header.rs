//! A block's header, as far as the proofs need one.
//!
//! A header names the block before it, says what the chain's proof
//! states once its own block is in, and carries what the work was done
//! with. Whatever else a node keeps in a header (a time, a target) is
//! to the proofs one digest, `rest`: they bind it and do not read it.
//!
//! - The **work's hash** is of the header without its nonce and mix:
//!   what a miner hashes with nonces ([`crate::pow`]).
//! - The **id** is of that hash, the nonce and the mix: what the next
//!   header names.
//!
//! A block's proof shows the work of the header *before* it
//! ([`crate::block_proof::root_into`]): a header's own work cannot be in the
//! proof the header names. The chain's step finds that header to be the
//! chain's: naming the id the chain was at, and stating what the
//! chain's proof stated ([`crate::chain_proof::step_into`]). Whether the
//! work's result meets a target is a node's to check, from the header
//! and two hashes ([`crate::pow::result_from_mix`]).

use crate::alg::halves;
use crate::field::{F, as_bytes};
use crate::hash::{DOM_BLOCK, DOM_HEADER, Digest, hash_domain};
use crate::pow::Nonce;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    /// The id of the header before; zeros for the first.
    pub parent: Digest,
    /// What the chain's proof states with this header's block in: the
    /// digest of its statement.
    pub statement: Digest,
    /// Everything else a node keeps in it, hashed.
    pub rest: Digest,
    pub nonce: Nonce,
    pub mix: Digest,
}

/// The work's hash, of the elements the header's digests are.
pub fn work_hash(parent: &Digest, statement: &Digest, rest: &Digest) -> Digest {
    let elements: Vec<F> = [parent, statement, rest].into_iter().flat_map(halves).collect();
    hash_domain(DOM_HEADER, &as_bytes(&elements))
}

/// A header's id, from its work's hash.
pub fn id_of(work_hash: &Digest, nonce: &Nonce, mix: &Digest) -> Digest {
    let elements: Vec<F> = [work_hash, nonce, mix].into_iter().flat_map(halves).collect();
    hash_domain(DOM_BLOCK, &as_bytes(&elements))
}

impl Header {
    pub fn work_hash(&self) -> Digest {
        work_hash(&self.parent, &self.statement, &self.rest)
    }

    pub fn id(&self) -> Digest {
        id_of(&self.work_hash(), &self.nonce, &self.mix)
    }
}
