//! The names of the things fetched by [`crate::transport`].
//!
//! A name says which object, and fixes its bytes: a block by its id, a
//! part of the state by the block the state is of. So what is being
//! fetched cannot change while it is fetched, and two nodes asked for
//! one name serve the same bytes.
//!
//! A name is a byte for the kind, then the kind's fields, integers
//! little-endian; [`MAX_NAME`] bytes at most, which is what a
//! transport request carries ([`crate::transport::wire::MAX_NAME`]).

use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};

/// The longest name.
pub const MAX_NAME: usize = 41;
const _: () = assert!(MAX_NAME <= crate::transport::wire::MAX_NAME);

/// The most headers one object holds: about a hundred kilobytes. Both
/// ends agree on it, so that a count over it is a name of nothing.
pub const MAX_HEADERS: u16 = 512;

/// An object's name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Object {
    /// The body of the block of this id.
    Block(Digest),
    /// That body without its proof.
    Lite(Digest),
    /// `count` headers, from height `from` up, of the chain the block
    /// `on` is on. Without `on` the name would be of whatever the
    /// serving node's chain was at the moment; with it, a node whose
    /// chain no longer holds that block has no such object.
    Headers { from: u32, count: u16, on: Digest },
    /// The top of the state after this block, in parts: the roots of
    /// the ranges of the outputs and of the parts of the names.
    Manifest(Digest),
    /// The roots of the parts of the outputs in the range `index` of
    /// the state after `block`.
    Roots { block: Digest, index: u32 },
    /// The part `index` of the outputs of the state after `block`.
    Part { block: Digest, index: u64 },
    /// The part `index` of the names of the state after `block`.
    Names { block: Digest, index: u32 },
    /// The output at `position` in the state after `block`, and its
    /// path to that state's root.
    Proof { block: Digest, position: u64 },
    /// The consensus file of this id.
    File(Digest),
    /// The transaction of this id.
    Tx(Digest),
    /// What the wallet of this id announced ([`crate::msg`]): the one
    /// of this sequence number, asked of the wallet itself; or, with
    /// none (zero), the newest a node that holds a session for it has.
    Announce { id: Digest, seq: u64 },
    /// The sealed message of this id ([`crate::msg::sealed_id`]).
    Sealed(Digest),
    /// Something carried along a way through relays
    /// ([`super::circuits`]), by the number its holder said it has it
    /// under.
    Step(u64),
    /// The certificate by which a wallet is the full name reached by
    /// this id, with what goes with it ([`crate::subnames`]): asked of
    /// the wallet's node.
    Alias(Digest),
}

const BLOCK: u8 = 1;
const LITE: u8 = 2;
const HEADERS: u8 = 3;
const MANIFEST: u8 = 4;
const PART: u8 = 5;
const NAMES: u8 = 6;
const PROOF: u8 = 7;
const FILE: u8 = 8;
const TX: u8 = 9;
const ROOTS: u8 = 10;
const ANNOUNCE: u8 = 11;
const SEALED: u8 = 12;
const STEP: u8 = 13;
const ALIAS: u8 = 14;

impl Object {
    /// What kind of object it is, in a word: for the logs.
    pub fn kind(&self) -> &'static str {
        match self {
            Object::Block(_) => "block",
            Object::Lite(_) => "lite",
            Object::Headers { .. } => "headers",
            Object::Manifest(_) => "manifest",
            Object::Roots { .. } => "roots",
            Object::Part { .. } => "part",
            Object::Names { .. } => "names",
            Object::Proof { .. } => "proof",
            Object::File(_) => "file",
            Object::Tx(_) => "tx",
            Object::Announce { .. } => "announce",
            Object::Sealed(_) => "sealed",
            Object::Step(_) => "step",
            Object::Alias(_) => "alias",
        }
    }

    /// Writes the name to the front of `out` and returns its length.
    pub fn encode(&self, out: &mut [u8; MAX_NAME]) -> usize {
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        match self {
            Object::Block(id) => {
                put(&[BLOCK]);
                put(&digest_to_bytes(id));
            }
            Object::Lite(id) => {
                put(&[LITE]);
                put(&digest_to_bytes(id));
            }
            Object::Headers { from, count, on } => {
                put(&[HEADERS]);
                put(&from.to_le_bytes());
                put(&count.to_le_bytes());
                put(&digest_to_bytes(on));
            }
            Object::Manifest(id) => {
                put(&[MANIFEST]);
                put(&digest_to_bytes(id));
            }
            Object::Roots { block, index } => {
                put(&[ROOTS]);
                put(&digest_to_bytes(block));
                put(&index.to_le_bytes());
            }
            Object::Part { block, index } => {
                put(&[PART]);
                put(&digest_to_bytes(block));
                put(&index.to_le_bytes());
            }
            Object::Names { block, index } => {
                put(&[NAMES]);
                put(&digest_to_bytes(block));
                put(&index.to_le_bytes());
            }
            Object::Proof { block, position } => {
                put(&[PROOF]);
                put(&digest_to_bytes(block));
                put(&position.to_le_bytes());
            }
            Object::File(id) => {
                put(&[FILE]);
                put(&digest_to_bytes(id));
            }
            Object::Tx(id) => {
                put(&[TX]);
                put(&digest_to_bytes(id));
            }
            Object::Announce { id, seq } => {
                put(&[ANNOUNCE]);
                put(&digest_to_bytes(id));
                put(&seq.to_le_bytes());
            }
            Object::Sealed(id) => {
                put(&[SEALED]);
                put(&digest_to_bytes(id));
            }
            Object::Step(name) => {
                put(&[STEP]);
                put(&name.to_le_bytes());
            }
            Object::Alias(n) => {
                put(&[ALIAS]);
                put(&digest_to_bytes(n));
            }
        }
        at
    }

    /// The object these bytes name: exactly a name, of a kind there is,
    /// with nothing after it.
    pub fn decode(bytes: &[u8]) -> Result<Object, Error> {
        const BAD: Error = Error::Malformed("object name");
        let (&kind, rest) = bytes.split_first().ok_or(BAD)?;
        let id = |b: &[u8]| digest_from_bytes(b).ok_or(BAD);
        let with = |n: usize| -> Result<(Digest, &[u8]), Error> {
            let (d, tail) = rest.split_at_checked(32).ok_or(BAD)?;
            if tail.len() != n {
                return Err(BAD);
            }
            Ok((id(d)?, tail))
        };
        Ok(match kind {
            BLOCK => Object::Block(with(0)?.0),
            LITE => Object::Lite(with(0)?.0),
            MANIFEST => Object::Manifest(with(0)?.0),
            FILE => Object::File(with(0)?.0),
            TX => Object::Tx(with(0)?.0),
            SEALED => Object::Sealed(with(0)?.0),
            ALIAS => Object::Alias(with(0)?.0),
            STEP => Object::Step(u64::from_le_bytes(rest.try_into().map_err(|_| BAD)?)),
            ANNOUNCE => {
                let (id, tail) = with(8)?;
                Object::Announce { id, seq: u64::from_le_bytes(tail.try_into().unwrap()) }
            }
            HEADERS => {
                if rest.len() != 38 {
                    return Err(BAD);
                }
                let from = u32::from_le_bytes(rest[..4].try_into().unwrap());
                let count = u16::from_le_bytes(rest[4..6].try_into().unwrap());
                // No headers, more than an object holds, or past the last
                // height there can be: a name of nothing.
                if count == 0 || count > MAX_HEADERS || from.checked_add(count as u32 - 1).is_none() {
                    return Err(BAD);
                }
                Object::Headers { from, count, on: id(&rest[6..])? }
            }
            ROOTS => {
                let (block, tail) = with(4)?;
                Object::Roots { block, index: u32::from_le_bytes(tail.try_into().unwrap()) }
            }
            PART => {
                let (block, tail) = with(8)?;
                Object::Part { block, index: u64::from_le_bytes(tail.try_into().unwrap()) }
            }
            NAMES => {
                let (block, tail) = with(4)?;
                Object::Names { block, index: u32::from_le_bytes(tail.try_into().unwrap()) }
            }
            PROOF => {
                let (block, tail) = with(8)?;
                Object::Proof { block, position: u64::from_le_bytes(tail.try_into().unwrap()) }
            }
            _ => return Err(BAD),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    fn digest(rng: &mut Rng) -> Digest {
        rng.digest()
    }

    fn every(rng: &mut Rng) -> Vec<Object> {
        let d = digest(rng);
        vec![
            Object::Block(d),
            Object::Lite(d),
            Object::Headers { from: rng.next_u64() as u32 / 2, count: 1 + rng.next_u64() as u16 % MAX_HEADERS, on: d },
            Object::Manifest(d),
            Object::Roots { block: d, index: rng.next_u64() as u32 },
            Object::Part { block: d, index: rng.next_u64() },
            Object::Names { block: d, index: rng.next_u64() as u32 },
            Object::Proof { block: d, position: rng.next_u64() },
            Object::File(d),
            Object::Tx(d),
            Object::Announce { id: d, seq: rng.next_u64() },
            Object::Sealed(d),
            Object::Step(rng.next_u64()),
            Object::Alias(d),
        ]
    }

    #[test]
    fn a_name_roundtrips_and_no_two_objects_share_one() {
        let mut rng = Rng::new(1);
        let mut seen = std::collections::HashMap::new();
        let mut longest = 0;
        for _ in 0..200 {
            for object in every(&mut rng) {
                let mut buf = [0u8; MAX_NAME];
                let n = object.encode(&mut buf);
                longest = longest.max(n);
                assert_eq!(Object::decode(&buf[..n]), Ok(object));
                // Not with a byte more, nor with one less.
                assert!(Object::decode(&buf[..n - 1]).is_err());
                let mut longer = buf[..n].to_vec();
                longer.push(0);
                assert!(Object::decode(&longer).is_err());
                if let Some(other) = seen.insert(buf[..n].to_vec(), object) {
                    assert_eq!(other, object);
                }
            }
        }
        assert_eq!(longest, MAX_NAME);
    }

    #[test]
    fn what_names_nothing_is_refused() {
        let d = [7u8; 32];
        let mut buf = [0u8; MAX_NAME];
        let name = |o: Object, buf: &mut [u8; MAX_NAME]| {
            let n = o.encode(buf);
            buf[..n].to_vec()
        };
        // No kind, a kind there is not.
        assert!(Object::decode(&[]).is_err());
        for kind in [0u8, 11, 255] {
            let mut b = name(Object::Block(d), &mut buf);
            b[0] = kind;
            assert!(Object::decode(&b).is_err(), "{kind}");
        }
        // Headers: none, too many, past the last height.
        let headers = |from, count| Object::Headers { from, count, on: d };
        let mut b = name(headers(5, 1), &mut buf);
        assert!(Object::decode(&b).is_ok());
        b[5..7].copy_from_slice(&0u16.to_le_bytes());
        assert!(Object::decode(&b).is_err());
        b[5..7].copy_from_slice(&(MAX_HEADERS + 1).to_le_bytes());
        assert!(Object::decode(&b).is_err());
        b[5..7].copy_from_slice(&MAX_HEADERS.to_le_bytes());
        assert!(Object::decode(&b).is_ok());
        b[1..5].copy_from_slice(&(u32::MAX - MAX_HEADERS as u32 + 2).to_le_bytes());
        assert!(Object::decode(&b).is_err());
        b[1..5].copy_from_slice(&(u32::MAX - MAX_HEADERS as u32 + 1).to_le_bytes());
        assert!(Object::decode(&b).is_ok());
        // Random bytes: refused or taken, never a panic.
        let mut rng = Rng::new(2);
        for _ in 0..5000 {
            let b: Vec<u8> = (0..rng.next_u64() % 50).map(|_| rng.next_u64() as u8).collect();
            let _ = Object::decode(&b);
        }
    }
}
