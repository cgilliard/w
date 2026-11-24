//! tabshared: what the node, the prover, the miner and the wallet have
//! in common.

pub mod address;
pub mod alg;
pub mod argument;
pub mod arith;
pub mod bip39;
pub mod blake3;
pub mod block;
pub mod block_proof;
pub mod chacha20poly1305;
pub mod chain_proof;
pub mod challenger;
pub mod circuit;
pub mod codec;
pub mod conditions;
pub mod consensus;
pub mod difficulty;
pub mod error;
pub mod field;
pub mod genesis;
pub mod grand;
pub mod hash;
pub mod header;
pub mod heap;
pub mod hidden;
pub mod keccak;
pub mod ledger;
pub mod listed;
pub mod machine;
pub mod merkle;
pub mod mldsa;
pub mod mlkem;
pub mod msg;
pub mod name;
pub mod ntt;
pub mod onion;
pub mod output;
pub mod parallel;
pub mod pcs;
pub mod policy;
pub mod pow;
pub mod proof;
pub mod random;
pub mod reading;
pub mod recursion;
pub mod registry;
pub mod segment;
pub mod sha256;
pub mod signature;
pub mod signed;
pub mod structure;
pub mod subnames;
pub mod sym;
#[cfg(test)]
#[path = "tests/util.rs"]
pub(crate) mod test_util;
pub mod transaction;
pub mod u256;
pub mod work;
pub mod wots;
pub mod xmss;

/// The library's own tests count the memory they hold, as the node
/// does: for the tests that say how much a piece of work takes.
#[cfg(test)]
#[global_allocator]
static HEAP: heap::Counting = heap::Counting;
