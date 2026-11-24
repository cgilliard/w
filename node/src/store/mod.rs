//! The node's storage: its own files, read and written at offsets, with
//! no database beneath and no file mapped into memory.
//!
//! What a node keeps is of two kinds. The state (the unspent outputs and
//! the names, with the Merkle tree over them) changes in place a little
//! with every block and must never be seen half changed. The rest
//! (headers, bodies, the records that undo a block) is written once and
//! read back.
//!
//! The state lives in one file of pages and is never overwritten: how,
//! and the layers that is made of, is `tabshared::store`'s to say, and
//! those layers are given out again here under their own names. One
//! root record carries whatever else must change with the state in one
//! step (the lengths of the files written once), so there is one moment
//! at which a block becomes applied, everywhere.
//!
//! # The node's layers, on those
//!
//! - [`trie`]: a trie over keys that is the Merkle tree of what it holds,
//!   whatever the tree's keys, records and hashes: on the pages.
//! - [`outputs`]: the unspent outputs, a trie over positions.
//! - [`names`]: the names, a trie over the keys of names, hashed by their
//!   own rule.
//! - [`window`]: what undoes each of the last blocks.
//! - [`blocks`]: the headers, the bodies kept and the chain by height,
//!   in tries of the same file.
//! - [`commits`]: which outputs are commits of names, and of what.
//! - [`state`]: the two under one root record, with the block they are
//!   the state after: what a node applies blocks to.
//! - [`receive`]: a state taken from other nodes part by part, each
//!   part checked, until it is one to go on from.

pub mod blocks;
pub mod commits;
pub mod names;
pub mod outputs;
pub mod receive;
pub mod state;
pub mod trie;
pub mod window;

#[cfg(test)]
pub use tabshared::store::testing;
pub use tabshared::store::{Backend, DirLock, FileBackend, ReadReq, WriteReq};
pub use tabshared::store::{Extent, PageFile, Pin, ROOT_MAX, ReadPages, Root, Txn, UNIT};
pub use tabshared::store::{backend, blob, crc32c, freemap, pagefile, partial, sparse};
