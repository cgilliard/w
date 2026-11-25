//! tabnode: a node of the Tabernacle network.
//!
//! What the four programs share is `tabshared`'s, and is here under the
//! names it has there (`crate::hash`, `crate::block`, and so on): what
//! is the node's own is in the modules below, some of which add to one
//! of those (the store, to the pages and files it is kept in).

pub use tabshared::*;

pub mod chain;
pub mod mempool;
pub mod proving;
pub mod store;
pub mod transport;

/// The library's own tests count the memory they hold, as the node
/// does: for the tests that say how much a piece of work takes.
#[cfg(test)]
#[global_allocator]
static HEAP: heap::Counting = heap::Counting;
