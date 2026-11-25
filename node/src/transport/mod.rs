//! Objects fetched reliably over datagrams.
//!
//! An object is some bytes of a known greatest length: a block, a
//! transaction, a part of the state. One side holds it and the other
//! wants it; between them are datagrams, which are lost, repeated,
//! delayed and delivered out of order. This module gets the object
//! across whole, or says that it could not.
//!
//! It is not a stream. Nothing is delivered in order, because nothing
//! needs to be: an object is of no use until all of it is here, so its
//! pieces are taken as they come and one that is late holds nothing up.
//! Nor is there a connection: the side that serves keeps nothing about
//! the side that asks beyond what it has still to send it.
//!
//! # How an object crosses
//!
//! The object is cut into chunks of [`CHUNK_BYTES`]. The side that wants
//! it asks for chunks by index, as ranges ([`wire::Get`]), and the side
//! that holds it sends each chunk asked for in a datagram of its own
//! ([`wire::Chunk`]), in the order they were asked. It sends nothing it
//! was not asked for.
//!
//! Everything that makes this reliable is on the asking side
//! ([`fetch::Fetch`]):
//!
//! * **A window.** Only so many chunks are asked for and not yet here at
//!   a time. It doubles each round trip while little is lost, and is
//!   kept for the peer ([`path::Path`]). What loss does to it depends
//!   on why chunks are lost. A narrow path holds so many chunks and
//!   drops the rest, however many are asked for: once the window is
//!   over twice what the path has been seen to hold, the path is known
//!   to be full, and the window is brought down to what it holds. A
//!   path that only loses a share of what crosses it holds the more the
//!   more is asked: loss leaves its window alone, since a smaller one
//!   would lose the same share and carry less.
//! * **Loss seen by what arrives.** Chunks come in the order asked, and
//!   each says which ask it answers. One still missing when a chunk
//!   asked [`REORDER`] places after it has arrived is taken for lost
//!   and asked for again at once; so is one overtaken at all, once
//!   nothing more has come for a short while. If it then turns up after
//!   all, the path delivers further out of order than that, and more is
//!   allowed for on it from then on.
//! * **Loss seen by silence.** When nothing at all arrives for the retry
//!   time, the one chunk waited for longest is asked for again, and its
//!   answer shows whether the rest were lost or only late. The retry
//!   time is measured: the smoothed round trip and four times how much
//!   it varies. It doubles with each silence, and after
//!   [`MAX_RETRIES`] of them with nothing between the fetch is given
//!   up.
//!
//! # What it is for
//!
//! Not speed. A block has minutes to cross. What matters is that it
//! does cross, on any line a node may be at the end of: a satellite's
//! long round trip, a radio link that loses one datagram in five, a
//! line of a few chunks a second. So the window may fall to two chunks,
//! the retry time rise to a minute, and nothing here gives a fetch up
//! for being slow: how fast it is going is reported
//! ([`fetch::Fetch::rate`]), and whether another peer would do better is
//! for the layer above, which knows whether there is one. A fetch given
//! up, by silence or by that layer, keeps what it has and goes on from
//! there, with the same peer or another.
//!
//! The side that serves ([`serve::Serve`]) answers only an address that
//! has shown it receives what is sent to it ([`token::Tokens`]), spreads
//! what it sends over time rather than sending a window in one burst,
//! and takes turns between the addresses it is serving.
//!
//! # What it does not do
//!
//! It does not know what an object is or whether its bytes are the right
//! ones: the layer above names objects and checks what arrives (by its
//! hash). A peer that serves wrong bytes costs one object's download,
//! and the layer above is the one to stop asking it.
//!
//! A chunk is taken only if it carries the number the asking side chose
//! for this fetch ([`wire::Chunk::transfer`]), which nobody off the path
//! between the two can know: so a third party cannot spoil a fetch by
//! sending chunks of its own.
//!
//! # No sockets, no clock
//!
//! Nothing here sends, receives or reads the time. Datagrams and the
//! time are given, and datagrams to send are returned: the same code
//! runs over a socket and over the simulated network of the tests,
//! where every loss is chosen and every run repeats.

pub mod fetch;
pub mod path;
pub mod serve;
#[cfg(test)]
mod sim;
pub mod token;
pub mod wire;

/// A time, in microseconds since whenever the caller counts from. Only
/// differences matter.
pub type Micros = u64;

pub const MILLI: Micros = 1_000;
pub const SECOND: Micros = 1_000_000;

/// The object's bytes in one chunk; the last chunk has what is left.
///
/// With a chunk's twenty bytes of its own this is 1220, and the
/// smallest datagram every path carries unbroken is 1232 (1280, less
/// the forty-eight bytes of the headers under it): twelve bytes are
/// left for the layer above to say what the datagram is.
pub const CHUNK_BYTES: usize = 1200;

/// The window on a path not yet measured: small enough not to swamp a
/// narrow one before anything is known of it.
pub const INITIAL_WINDOW: u32 = 16;
/// The smallest window, however much is lost. A path that carries one
/// chunk a second has to be able to settle near that.
pub const MIN_WINDOW: u32 = 2;
/// The largest window, and the most chunks one request asks for: over
/// two megabytes, a whole block in one round trip on a path that
/// carries it.
pub const MAX_WINDOW: u32 = 2048;
/// More is asked for once this many places in the window are free (or
/// half the window, when that is fewer), so that requests go out in
/// batches rather than one for each chunk that arrives.
pub const REFILL: u32 = 8;
/// A chunk is taken for lost when one asked this many places after it
/// has arrived. Three would do on a path that keeps order; datagrams on
/// real paths overtake one another by a few places.
pub const REORDER: u64 = 8;
/// The most places that is raised to on a path seen to deliver further
/// out of order ([`path::Path::disordered`]). Past this, loss is seen
/// by silence only.
pub const MAX_REORDER: u32 = 512;
/// A round (a window's worth of arrivals) that loses more than one
/// chunk in this many is a round that lost: the window does not grow,
/// and comes down if the path is full ([`path::Path::lost`]). Fewer
/// losses than this are nothing: a chunk goes missing here and there on
/// any path.
pub const LOSS_TOLERANCE: u32 = 50;
/// Silences, one after another with nothing arriving between, before
/// a fetch is given up. Each waits twice as long as the one before, up
/// to [`MAX_RETRY`]: some minutes in all. What had arrived is kept, and
/// the fetch can be taken up again ([`fetch::Fetch::resume`]).
pub const MAX_RETRIES: u32 = 8;
/// The retry time on a path not yet measured.
pub const RETRY: Micros = 400 * MILLI;
/// The least and the greatest a retry time may be. A minute: on a line
/// of a chunk a second a few chunks queued are many seconds of round
/// trip, and a wait shorter than the round trip asks for everything
/// twice.
pub const MIN_RETRY: Micros = 100 * MILLI;
pub const MAX_RETRY: Micros = 60 * SECOND;

/// The number of chunks of an object of `len` bytes.
pub const fn chunk_count(len: u32) -> u32 {
    len.div_ceil(CHUNK_BYTES as u32)
}

/// The bytes of chunk `index` of an object of `len` bytes: none if the
/// object has no such chunk.
pub const fn chunk_len(len: u32, index: u32) -> Option<usize> {
    let start = index as u64 * CHUNK_BYTES as u64;
    if start >= len as u64 {
        return None;
    }
    let left = len as u64 - start;
    Some(if left < CHUNK_BYTES as u64 { left as usize } else { CHUNK_BYTES })
}

/// Chunk `index` of `object`: none if it has no such chunk.
pub fn chunk_of(object: &[u8], index: u32) -> Option<&[u8]> {
    let n = chunk_len(u32::try_from(object.len()).ok()?, index)?;
    let start = index as usize * CHUNK_BYTES;
    Some(&object[start..start + n])
}
