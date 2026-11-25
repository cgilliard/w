//! How nodes talk to each other: what a datagram says, what an object
//! is called, and the settings a node runs with.
//!
//! `docs/WIRE.md` is the account of all of it, message by message, and
//! of why it is as it is. In short:
//!
//! * A datagram is the network's four bytes, a byte saying which
//!   message it is, and the message ([`message`]).
//! * A message is small: it fits its datagram, and so does its answer.
//!   Anything bigger is an *object* with a name ([`object`]), fetched
//!   by [`crate::transport`], whose three datagrams are three of the
//!   messages here.
//! * An object's name fixes its bytes, so that it cannot change under a
//!   fetch, and everything fetched is checked against something already
//!   held: a header, or a root from an object checked before it.
//! * How many peers, how many fetches at once, how long to wait: these
//!   are settings ([`config`]), each with a default.

pub mod circuits;
pub mod config;
pub mod message;
pub mod node;
pub mod object;
pub mod peers;
pub mod sessions;
pub mod snapshot;
pub mod socket;

/// The largest datagram sent: what every path carries unbroken.
pub const MAX_DATAGRAM: usize = 1232;
/// The version of all this. A node of another version is answered, so
/// that it can see why, and otherwise left alone.
pub const VERSION: u32 = 2;
