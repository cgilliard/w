//! Mainnet's genesis: the time, the Bitcoin block and the target. They
//! are all there is to say of it, and all this file holds: the header's
//! nonce, its work and the block's id follow, and the program works
//! them out ([`crate::chain::params::ChainParams::genesis`]). A testing
//! genesis: a real one is these changed, just before launch.
//!
//! The genesis block is empty, and its nonce is the hash of a Bitcoin
//! block, so the chain did not exist before that block. Its first
//! blocks need about `2^248 / (TARGET + 1)` hashes each: 65535 at the
//! testing target.

/// Genesis time, unix seconds; the ASERT anchor.
pub const TIMESTAMP: u64 = 1793322871;
/// The Bitcoin block hash, in the byte order block explorers show.
pub const BITCOIN_HASH_HEX: &str = "00000000000000000000c4750b0959be11adfd86268999ae3ca6b95f667e9737";
/// Height and time of that Bitcoin block, for reference.
pub const BITCOIN_HEIGHT: u64 = 973758;
pub const BITCOIN_TIME: u64 = 1793322482;
/// Target of the first block after genesis (little-endian 64-bit limbs).
pub const TARGET: [u64; 4] = [0, 0, 0, 1099511627776];
