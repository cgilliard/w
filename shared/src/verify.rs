//! What a block's proof is asked to show, and who checks it.
//!
//! A node checks of a block what it can see: the header's rules, the
//! body's form, that what the block spends is there, the state root, the
//! supply. What it cannot see (that the spenders hold the keys, that no
//! transaction makes coins, that a name's owner signed its update) the
//! block's proof attests to. The [`BlockStatement`] is the public side
//! of that: everything the proof is about, taken from the chain and the
//! block, none of it from the prover. A block's proof is the chain's:
//! it attests to every block before it too
//! ([`crate::chain_proof`]).
//!
//! The chain is written against [`ProofVerifier`], so it stands without
//! the circuits: with [`AcceptAllProofs`] every rule but the proof's is
//! checked, which is how the chain's own tests run.

use crate::block::BodyRef;
use crate::chain_proof::Statement;
use crate::hash::Digest;

/// Statement a block's proof must attest to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlockStatement<'a> {
    /// What the chain's proof states with this block in: the step's
    /// program, the height, the outputs' root and the names' after the
    /// block, the position after its last output, the running hashes
    /// of what it spends, makes and does to names, what its outputs
    /// come to, where the emission stands, and the header before. The
    /// position after the last output is in it, so the proofs of a
    /// chain's blocks say how many outputs there have been: what a
    /// node that takes its state from others has no other way to know.
    pub chain: Statement,
    /// Its digest, which the block's header names and a proof is
    /// verified against.
    pub digest: Digest,
    /// The body, as the block carries it: read where it lies.
    pub body: BodyRef<'a>,
}

/// Verifies a block's validity proof. The real implementation is the STARK
/// verifier for the block circuit.
pub trait ProofVerifier {
    fn verify(&self, statement: &BlockStatement<'_>, proof: &[u8]) -> bool;

    /// Debugging only: whether proofs go unchecked.
    fn is_unchecked(&self) -> bool {
        false
    }

    /// Whether a block's proof attests to the work of every block
    /// before it (that each header's mix is its work's, not that the
    /// work meets a target, which a header says for itself): so that a node that takes its state as of a block
    /// whose proof it checks need not check, from the seed text, the
    /// work of each header under it (the node's `chain::headers`). Not so
    /// unless said.
    fn attests_work(&self) -> bool {
        false
    }
}

/// Accepts every proof. For development and tests only; a node using this
/// trusts block producers completely.
#[derive(Debug, Clone, Copy, Default)]
pub struct AcceptAllProofs;

impl ProofVerifier for AcceptAllProofs {
    fn verify(&self, _: &BlockStatement<'_>, _: &[u8]) -> bool {
        true
    }

    fn is_unchecked(&self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::Body;

    /// A verifier that reads the statement: the trait is usable as one
    /// object, by reference, with a body read in place.
    struct OnlyEmptyBlocks;

    impl ProofVerifier for OnlyEmptyBlocks {
        fn verify(&self, statement: &BlockStatement<'_>, proof: &[u8]) -> bool {
            statement.body.inputs().len() == 0 && proof.is_empty()
        }
    }

    #[test]
    fn a_statement_is_checked_by_whoever_is_asked() {
        let bytes = Body::default().to_bytes();
        let body = BodyRef::from_bytes(&bytes).unwrap();
        let chain = Statement { height: 7, next: 40, tip: [6; 32], ..Statement::genesis() };
        let statement = BlockStatement { chain, digest: chain.digest(), body };
        assert_eq!(statement, statement.clone());
        let verifiers: [&dyn ProofVerifier; 2] = [&AcceptAllProofs, &OnlyEmptyBlocks];
        assert!(verifiers.iter().all(|v| v.verify(&statement, &[])));
        assert!(AcceptAllProofs.verify(&statement, &[1, 2, 3]));
        assert!(!OnlyEmptyBlocks.verify(&statement, &[1]));
        assert!(AcceptAllProofs.is_unchecked() && !OnlyEmptyBlocks.is_unchecked());
    }
}
