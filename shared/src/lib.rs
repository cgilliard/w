//! tabshared: what the node, the prover, the miner and the wallet have
//! in common.

pub mod bip39;
pub mod blake3;
pub mod chacha20poly1305;
pub mod challenger;
pub mod circuit;
pub mod codec;
pub mod difficulty;
pub mod error;
pub mod field;
pub mod genesis;
pub mod hash;
pub mod heap;
pub mod keccak;
pub mod merkle;
pub mod mldsa;
pub mod mlkem;
pub mod ntt;
pub mod parallel;
pub mod pow;
pub mod random;
pub mod sha256;
#[cfg(test)]
#[path = "tests/util.rs"]
pub(crate) mod test_util;
pub mod u256;
pub mod xmss;

/// The library's own tests count the memory they hold, as the node
/// does: for the tests that say how much a piece of work takes.
#[cfg(test)]
#[global_allocator]
static HEAP: heap::Counting = heap::Counting;
