//! Storage: a program's own files, read and written at offsets, with no
//! database beneath and no file mapped into memory.
//!
//! Here is what is under both the node's store and the wallet's file:
//! pages that are never overwritten, and what a Merkle tree over them
//! needs. What a node keeps in them (the unspent outputs, the names,
//! the blocks) is the node's own.
//!
//! # Copy on write
//!
//! What is kept lives in one file of pages ([`PageFile`]) and is never
//! overwritten. A change is written as new pages into free space; when
//! they are safely on disk, one small root record is written that points
//! at them. Until that record is on disk the file holds what it held
//! before, whole; from then on what it holds after, whole. A crash at
//! any moment leaves one or the other, and there is nothing to replay
//! or repair on the way up: the last good root record is what is kept.
//!
//! A reader holds the root record it began with ([`PageFile::pin`]) and
//! goes on reading what that points at while changes are made: the
//! pages it can reach are not reused until it lets go.
//!
//! # Layers
//!
//! - [`backend`]: a file as the layers above see it: read here, write
//!   there, make it durable. The real one is a file; the tests' is memory
//!   that can lose power at any write.
//! - [`crc32c`]: the checksum every page and root record carries.
//! - [`freemap`]: which parts of the file are in use.
//! - [`pagefile`]: pages, root records and transactions, on the three
//!   above.
//! - [`blob`]: bytes too many for a page, as pages and a list of them.
//! - [`sparse`]: the hashes of the state's Merkle tree, from the nodes
//!   that are not empty.
//! - [`partial`]: the paths of some leaves, changed in memory: what
//!   proving a block takes from the state.
//!
//! Memory is what these hold and no more: the map of free space (a bit
//! for every 512 bytes of the file), a transaction's write buffer, and
//! whatever buffers a caller reads into.

pub mod backend;
pub mod blob;
pub mod crc32c;
pub mod freemap;
pub mod pagefile;
pub mod partial;
pub mod sparse;
#[cfg(test)]
pub(crate) mod testing;

pub use backend::{Backend, DirLock, FileBackend, ReadReq, WriteReq};
pub use pagefile::{Extent, PageFile, Pin, ROOT_MAX, ReadPages, Root, Txn, UNIT};
