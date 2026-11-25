//! The datagrams.
//!
//! ```text
//! network (4) | message (1) | body
//! ```
//!
//! The network's four bytes come first so that a datagram of another
//! network is dropped before anything of it is read. Integers are
//! little-endian. A datagram is taken only if it is exactly the
//! encoding of a message: nothing missing, nothing after.
//!
//! Which messages there are, who sends each and what stops each being
//! abused is in `docs/WIRE.md`. Here is only their form.

use std::net::{Ipv4Addr, SocketAddrV4};

use super::MAX_DATAGRAM;
use crate::block::{HEADER_SIZE, Header};
use crate::chain::headers::LOCATOR;
use crate::chain::leaves::{AUX_LEAVES, Leaves};
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::transport::wire::{Chunk, Get, Gone, MAX_CHUNK, MAX_GET};
use crate::u256::U256;

/// The bytes before a message's body.
pub const HEAD: usize = 5;
/// The most addresses in a [`Message::Peers`].
pub const MAX_ADDRS: usize = 32;

const _: () = assert!(HEAD + MAX_CHUNK <= MAX_DATAGRAM && HEAD + MAX_GET <= MAX_DATAGRAM);
const _: () = assert!(HEAD + 9 + LOCATOR * 32 <= MAX_DATAGRAM);

const PING: u8 = 1;
const PONG: u8 = 2;
const GET_PEERS: u8 = 3;
const PEERS: u8 = 4;
const FIND_FORK: u8 = 5;
const FORK: u8 = 6;
const BLOCK: u8 = 7;
const TX: u8 = 8;
const GET_LEAVES: u8 = 9;
const LEAVES: u8 = 10;
const GOODBYE: u8 = 11;
const SESSION: u8 = 12;
const SESSION_STATE: u8 = 13;
const OFFER: u8 = 14;
const NOTICE: u8 = 15;

/// What a [`Message::Notice`] says of a message offered: passed on to
/// the wallet it is for; that wallet is not here to take it; or not
/// taken, by a node that passes nothing on or has no room.
/// The kinds a step on a way is of ([`super::circuits::OPEN`] to
/// [`super::circuits::CLOSE`]).
const STEP_KINDS: std::ops::RangeInclusive<u8> = super::circuits::OPEN..=super::circuits::CLOSE;
pub const NOTICE_PASSED: u8 = 1;
pub const NOTICE_OFFLINE: u8 = 2;
pub const NOTICE_REFUSED: u8 = 3;
const GET: u8 = 16;
const CHUNK: u8 = 17;
const GONE: u8 = 18;
const CARRY: u8 = 19;
const STEPPED: u8 = 20;
const CARRIED: u8 = 21;
const ALIAS: u8 = 22;
const ALIAS_STATE: u8 = 23;

/// The most a [`Message::Stepped`] carries.
pub const MAX_STEPPED: usize = MAX_DATAGRAM - HEAD - 27;
// 32 to 47: kept for the messages of private messaging.

/// What a node says of itself, in every ping and pong.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Status {
    /// Chosen by the one that pings; the pong carries it back, which
    /// shows the pong's sender received the ping.
    pub nonce: u64,
    /// [`super::VERSION`].
    pub version: u32,
    /// What the receiver is to put in its requests to the sender
    /// ([`crate::transport::token`]).
    pub token: u64,
    /// The id of the sender's genesis block: its chain.
    pub genesis: Digest,
    /// The height of its tip.
    pub height: u32,
    /// The lowest height from which it holds every block's body up to
    /// its tip. Below this it serves headers only.
    pub oldest: u32,
    /// The lowest height whose state it can still hand over in parts.
    pub window: u32,
    /// Its tip's id.
    pub tip: Digest,
    /// The work of its chain, in all.
    pub work: U256,
    /// A number the node took by chance when it started: the same in
    /// everything it says, from whatever address it is heard. A node
    /// reached at two addresses (its own and its router's, say) is
    /// known by it for one node, and a node that hears its own knows
    /// it has reached itself.
    pub node: u64,
}

impl Status {
    pub const BYTES: usize = 8 + 4 + 8 + 32 + 4 + 4 + 4 + 32 + 32 + 8;
}

/// Addresses of peers: [`MAX_ADDRS`] at most.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Addrs {
    n: u8,
    a: [SocketAddrV4; MAX_ADDRS],
}

impl Addrs {
    pub const fn new() -> Addrs {
        Addrs { n: 0, a: [SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0); MAX_ADDRS] }
    }

    /// Adds an address; false, and nothing added, when full.
    pub fn push(&mut self, addr: SocketAddrV4) -> bool {
        if self.n as usize == MAX_ADDRS {
            return false;
        }
        self.a[self.n as usize] = addr;
        self.n += 1;
        true
    }

    pub fn as_slice(&self) -> &[SocketAddrV4] {
        &self.a[..self.n as usize]
    }
}

impl Default for Addrs {
    fn default() -> Addrs {
        Addrs::new()
    }
}

/// Ids of blocks of a node's chain, the newest first, further and
/// further apart: by which another node finds the newest block the two
/// have in common. At least one, [`LOCATOR`] at most.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Locator {
    n: u8,
    ids: [Digest; LOCATOR],
}

impl Locator {
    /// Of `ids`: none if there are none, or too many.
    pub fn new(ids: &[Digest]) -> Option<Locator> {
        if ids.is_empty() || ids.len() > LOCATOR {
            return None;
        }
        let mut l = Locator { n: ids.len() as u8, ids: [[0; 32]; LOCATOR] };
        l.ids[..ids.len()].copy_from_slice(ids);
        Some(l)
    }

    pub fn as_slice(&self) -> &[Digest] {
        &self.ids[..self.n as usize]
    }
}

// (A locator makes the largest some 1,000 bytes, and a request for
// chunks the next some 570: a message is read from a datagram and let
// go with it, so it is left as it is.)
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Message<'a> {
    /// "Are you there, and what do you hold?"
    Ping(Status),
    /// The answer, with the ping's nonce.
    Pong(Status),
    /// "Whom else do you know?"
    GetPeers {
        token: u64,
    },
    Peers(Addrs),
    /// "Which is the newest of these blocks on your chain?"
    FindFork {
        token: u64,
        locator: Locator,
    },
    /// The answer: its height and id.
    Fork {
        height: u32,
        id: Digest,
    },
    /// "Here is a new block": its header, and how long its body is, so
    /// that the whole of it can be asked for at once.
    Block {
        header: Header,
        len: u32,
    },
    /// "Here is a new transaction": its id and length.
    Tx {
        id: Digest,
        len: u32,
    },
    /// "What are the aux leaves of this block?"
    GetLeaves {
        token: u64,
        id: Digest,
    },
    Leaves {
        id: Digest,
        leaves: Leaves,
    },
    /// "I am the wallet of this id, and what I last announced has this
    /// number": said to a node the wallet is to be reached at, now and
    /// then, for as long as it is to be. `grant` is the sender's token
    /// for the node, with which the node may ask it for the
    /// announcement ([`crate::net::object::Object::Announce`]).
    Session {
        token: u64,
        grant: u64,
        id: Digest,
        seq: u64,
    },
    /// The answer: the number of the announcement the node holds for
    /// that wallet, zero while it holds none; and the node's token for
    /// whoever asked, which the next asking is to carry. (So a wallet
    /// need be nothing else to the node it is reached at: not its peer,
    /// nor known to it before.) And the token the asking gave it
    /// (`echo`, the asker's `grant`): by which the asker knows the
    /// answer for one to what it asked, from where it asked it, and not
    /// the word of whoever writes that address on a datagram.
    SessionState {
        id: Digest,
        seq: u64,
        token: u64,
        echo: u64,
    },
    /// "Here is a sealed message for this wallet": its id and length,
    /// to be asked for with `grant`, the sender's token for whoever it
    /// is said to. `token` is theirs for the sender, where the sender
    /// has one: a node takes an offer to pass on only with it.
    Offer {
        token: u64,
        grant: u64,
        to: Digest,
        id: Digest,
        len: u32,
    },
    /// What became of a message offered to a node to pass on
    /// ([`NOTICE_PASSED`] and the rest).
    Notice {
        id: Digest,
        what: u8,
    },
    /// "Here is something for the way we both know as `circuit`"
    /// ([`super::circuits`]): of this kind and count and length, to be
    /// asked for by `name` with `grant`, the sender's token for
    /// whoever it is said to.
    Carry {
        grant: u64,
        name: u64,
        circuit: u64,
        kind: u8,
        count: u64,
        len: u32,
    },
    /// The same, of something small enough to be said with it: here it
    /// is. Answered with [`Message::Carried`], and said again until it
    /// is.
    Stepped {
        name: u64,
        circuit: u64,
        kind: u8,
        count: u64,
        bytes: &'a [u8],
    },
    /// "What you said under this name has come."
    Carried {
        name: u64,
    },
    /// "The wallet you hold a session for is this full name, by a
    /// certificate of this number": said by the wallet's node to a
    /// node that name is reached at ([`crate::subnames`]). `n` is the
    /// id the name is reached by; the certificate is asked for with
    /// `grant` if it is not held
    /// ([`crate::net::object::Object::Alias`]).
    Alias {
        token: u64,
        grant: u64,
        n: Digest,
        seq: u64,
    },
    /// And what that node holds for the name: the number of the
    /// certificate, or none (zero).
    AliasState {
        n: Digest,
        seq: u64,
    },
    /// "I am going": the sender is not to be asked anything more.
    Goodbye {
        token: u64,
    },
    /// The transport's request for chunks of an object.
    Get(Get<'a>),
    /// The transport's chunk.
    Chunk(Chunk<'a>),
    /// The transport's "I do not have it".
    Gone(Gone),
}

impl<'a> Message<'a> {
    /// Writes the datagram to the front of `out` and returns its
    /// length.
    pub fn encode(&self, network: [u8; 4], out: &mut [u8; MAX_DATAGRAM]) -> usize {
        out[..4].copy_from_slice(&network);
        let mut w = Out(out, HEAD);
        let kind = match self {
            Message::Ping(s) => {
                w.status(s);
                PING
            }
            Message::Pong(s) => {
                w.status(s);
                PONG
            }
            Message::GetPeers { token } => {
                w.put(&token.to_le_bytes());
                GET_PEERS
            }
            Message::Peers(addrs) => {
                w.put(&[addrs.n]);
                for a in addrs.as_slice() {
                    w.put(&a.ip().octets());
                    w.put(&a.port().to_le_bytes());
                }
                PEERS
            }
            Message::FindFork { token, locator } => {
                w.put(&token.to_le_bytes());
                w.put(&[locator.n]);
                for id in locator.as_slice() {
                    w.put(&digest_to_bytes(id));
                }
                FIND_FORK
            }
            Message::Fork { height, id } => {
                w.put(&height.to_le_bytes());
                w.put(&digest_to_bytes(id));
                FORK
            }
            Message::Block { header, len } => {
                w.put(&header.to_bytes());
                w.put(&len.to_le_bytes());
                BLOCK
            }
            Message::Tx { id, len } => {
                w.put(&digest_to_bytes(id));
                w.put(&len.to_le_bytes());
                TX
            }
            Message::GetLeaves { token, id } => {
                w.put(&token.to_le_bytes());
                w.put(&digest_to_bytes(id));
                GET_LEAVES
            }
            Message::Leaves { id, leaves } => {
                w.put(&digest_to_bytes(id));
                for leaf in leaves {
                    w.put(leaf);
                }
                LEAVES
            }
            Message::Goodbye { token } => {
                w.put(&token.to_le_bytes());
                GOODBYE
            }
            Message::Session { token, grant, id, seq } => {
                w.put(&token.to_le_bytes());
                w.put(&grant.to_le_bytes());
                w.put(&digest_to_bytes(id));
                w.put(&seq.to_le_bytes());
                SESSION
            }
            Message::SessionState { id, seq, token, echo } => {
                w.put(&digest_to_bytes(id));
                w.put(&seq.to_le_bytes());
                w.put(&token.to_le_bytes());
                w.put(&echo.to_le_bytes());
                SESSION_STATE
            }
            Message::Offer { token, grant, to, id, len } => {
                w.put(&token.to_le_bytes());
                w.put(&grant.to_le_bytes());
                w.put(&digest_to_bytes(to));
                w.put(&digest_to_bytes(id));
                w.put(&len.to_le_bytes());
                OFFER
            }
            Message::Notice { id, what } => {
                w.put(&digest_to_bytes(id));
                w.put(&[*what]);
                NOTICE
            }
            Message::Carry { grant, name, circuit, kind, count, len } => {
                w.put(&grant.to_le_bytes());
                w.put(&name.to_le_bytes());
                w.put(&circuit.to_le_bytes());
                w.put(&[*kind]);
                w.put(&count.to_le_bytes());
                w.put(&len.to_le_bytes());
                CARRY
            }
            Message::Stepped { name, circuit, kind, count, bytes } => {
                w.put(&name.to_le_bytes());
                w.put(&circuit.to_le_bytes());
                w.put(&[*kind]);
                w.put(&count.to_le_bytes());
                let bytes = &bytes[..bytes.len().min(MAX_STEPPED)];
                w.put(&(bytes.len() as u16).to_le_bytes());
                w.put(bytes);
                STEPPED
            }
            Message::Carried { name } => {
                w.put(&name.to_le_bytes());
                CARRIED
            }
            Message::Alias { token, grant, n, seq } => {
                w.put(&token.to_le_bytes());
                w.put(&grant.to_le_bytes());
                w.put(&digest_to_bytes(n));
                w.put(&seq.to_le_bytes());
                ALIAS
            }
            Message::AliasState { n, seq } => {
                w.put(&digest_to_bytes(n));
                w.put(&seq.to_le_bytes());
                ALIAS_STATE
            }
            Message::Get(g) => {
                w.1 += g.encode(&mut w.0[HEAD..]);
                GET
            }
            Message::Chunk(c) => {
                w.1 += c.encode(&mut w.0[HEAD..]);
                CHUNK
            }
            Message::Gone(g) => {
                w.1 += g.encode(&mut w.0[HEAD..]);
                GONE
            }
        };
        let len = w.1;
        out[4] = kind;
        len
    }

    /// The message of a datagram of `network`. An error for a datagram
    /// of another network, of a message there is not, or that is not
    /// exactly a message's encoding.
    pub fn decode(network: [u8; 4], bytes: &'a [u8]) -> Result<Message<'a>, Error> {
        const BAD: Error = Error::Malformed("datagram");
        if bytes.len() < HEAD || bytes.len() > MAX_DATAGRAM || bytes[..4] != network {
            return Err(BAD);
        }
        let body = &bytes[HEAD..];
        let mut r = In(body);
        let message = match bytes[4] {
            PING => Message::Ping(r.status().ok_or(BAD)?),
            PONG => Message::Pong(r.status().ok_or(BAD)?),
            GET_PEERS => Message::GetPeers { token: r.u64().ok_or(BAD)? },
            PEERS => {
                let [n] = r.array().ok_or(BAD)?;
                let mut addrs = Addrs::new();
                for _ in 0..n {
                    let ip: [u8; 4] = r.array().ok_or(BAD)?;
                    let port = u16::from_le_bytes(r.array().ok_or(BAD)?);
                    // (An address something could be at, said once.)
                    let addr = SocketAddrV4::new(Ipv4Addr::from(ip), port);
                    if port == 0 || addr.ip().is_unspecified() || addrs.as_slice().contains(&addr) || !addrs.push(addr)
                    {
                        return Err(BAD);
                    }
                }
                Message::Peers(addrs)
            }
            FIND_FORK => {
                let token = r.u64().ok_or(BAD)?;
                let [n] = r.array().ok_or(BAD)?;
                if n == 0 || n as usize > LOCATOR {
                    return Err(BAD);
                }
                let mut locator = Locator { n, ids: [[0; 32]; LOCATOR] };
                for id in locator.ids[..n as usize].iter_mut() {
                    *id = r.digest().ok_or(BAD)?;
                }
                Message::FindFork { token, locator }
            }
            FORK => Message::Fork { height: r.u32().ok_or(BAD)?, id: r.digest().ok_or(BAD)? },
            BLOCK => {
                let header = Header::from_bytes(r.take(HEADER_SIZE).ok_or(BAD)?)?;
                Message::Block { header, len: r.u32().ok_or(BAD)? }
            }
            TX => Message::Tx { id: r.digest().ok_or(BAD)?, len: r.u32().ok_or(BAD)? },
            GET_LEAVES => Message::GetLeaves { token: r.u64().ok_or(BAD)?, id: r.digest().ok_or(BAD)? },
            LEAVES => {
                let id = r.digest().ok_or(BAD)?;
                let mut leaves = [[0u8; 32]; AUX_LEAVES];
                for leaf in leaves.iter_mut() {
                    *leaf = r.array().ok_or(BAD)?;
                }
                Message::Leaves { id, leaves }
            }
            GOODBYE => Message::Goodbye { token: r.u64().ok_or(BAD)? },
            SESSION => Message::Session {
                token: r.u64().ok_or(BAD)?,
                grant: r.u64().ok_or(BAD)?,
                id: r.digest().ok_or(BAD)?,
                seq: r.u64().ok_or(BAD)?,
            },
            SESSION_STATE => Message::SessionState {
                id: r.digest().ok_or(BAD)?,
                seq: r.u64().ok_or(BAD)?,
                token: r.u64().ok_or(BAD)?,
                echo: r.u64().ok_or(BAD)?,
            },
            OFFER => Message::Offer {
                token: r.u64().ok_or(BAD)?,
                grant: r.u64().ok_or(BAD)?,
                to: r.digest().ok_or(BAD)?,
                id: r.digest().ok_or(BAD)?,
                len: r.u32().ok_or(BAD)?,
            },
            NOTICE => {
                let (id, what) = (r.digest().ok_or(BAD)?, r.take(1).ok_or(BAD)?[0]);
                if !(NOTICE_PASSED..=NOTICE_REFUSED).contains(&what) {
                    return Err(BAD);
                }
                Message::Notice { id, what }
            }
            STEPPED => {
                let (name, circuit) = (r.u64().ok_or(BAD)?, r.u64().ok_or(BAD)?);
                let (kind, count) = (r.take(1).ok_or(BAD)?[0], r.u64().ok_or(BAD)?);
                if !STEP_KINDS.contains(&kind) {
                    return Err(BAD);
                }
                let len = u16::from_le_bytes(r.array().ok_or(BAD)?) as usize;
                let bytes = r.take(len).ok_or(BAD)?;
                Message::Stepped { name, circuit, kind, count, bytes }
            }
            CARRIED => Message::Carried { name: r.u64().ok_or(BAD)? },
            ALIAS => Message::Alias {
                token: r.u64().ok_or(BAD)?,
                grant: r.u64().ok_or(BAD)?,
                n: r.digest().ok_or(BAD)?,
                seq: r.u64().ok_or(BAD)?,
            },
            ALIAS_STATE => Message::AliasState { n: r.digest().ok_or(BAD)?, seq: r.u64().ok_or(BAD)? },
            CARRY => {
                let (grant, name, circuit) = (r.u64().ok_or(BAD)?, r.u64().ok_or(BAD)?, r.u64().ok_or(BAD)?);
                let kind = r.take(1).ok_or(BAD)?[0];
                if !STEP_KINDS.contains(&kind) {
                    return Err(BAD);
                }
                Message::Carry { grant, name, circuit, kind, count: r.u64().ok_or(BAD)?, len: r.u32().ok_or(BAD)? }
            }
            // The transport's own, which take the whole body or refuse it.
            GET => return Ok(Message::Get(Get::decode(body)?)),
            CHUNK => return Ok(Message::Chunk(Chunk::decode(body)?)),
            GONE => return Ok(Message::Gone(Gone::decode(body)?)),
            _ => return Err(BAD),
        };
        if !r.0.is_empty() {
            return Err(BAD);
        }
        Ok(message)
    }
}

struct Out<'a>(&'a mut [u8; MAX_DATAGRAM], usize);

impl Out<'_> {
    fn put(&mut self, bytes: &[u8]) {
        self.0[self.1..self.1 + bytes.len()].copy_from_slice(bytes);
        self.1 += bytes.len();
    }

    fn status(&mut self, s: &Status) {
        self.put(&s.nonce.to_le_bytes());
        self.put(&s.version.to_le_bytes());
        self.put(&s.token.to_le_bytes());
        self.put(&digest_to_bytes(&s.genesis));
        self.put(&s.height.to_le_bytes());
        self.put(&s.oldest.to_le_bytes());
        self.put(&s.window.to_le_bytes());
        self.put(&digest_to_bytes(&s.tip));
        self.put(&s.work.to_le_bytes());
        self.put(&s.node.to_le_bytes());
    }
}

struct In<'a>(&'a [u8]);

impl<'a> In<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    fn array<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take(N).map(|b| b.try_into().unwrap())
    }

    fn u32(&mut self) -> Option<u32> {
        self.array().map(u32::from_le_bytes)
    }

    fn u64(&mut self) -> Option<u64> {
        self.array().map(u64::from_le_bytes)
    }

    fn digest(&mut self) -> Option<Digest> {
        digest_from_bytes(self.take(32)?)
    }

    fn status(&mut self) -> Option<Status> {
        Some(Status {
            nonce: self.u64()?,
            version: self.u32()?,
            token: self.u64()?,
            genesis: self.digest()?,
            height: self.u32()?,
            oldest: self.u32()?,
            window: self.u32()?,
            tip: self.digest()?,
            work: U256::from_le_bytes(&self.array()?),
            node: self.u64()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;
    use crate::transport::CHUNK_BYTES;
    use crate::transport::wire::Ranges;

    const NET: [u8; 4] = *b"TEST";

    fn digest(rng: &mut Rng) -> Digest {
        rng.digest()
    }

    fn status(rng: &mut Rng) -> Status {
        Status {
            nonce: rng.next_u64(),
            version: rng.next_u64() as u32,
            token: rng.next_u64(),
            genesis: digest(rng),
            height: rng.next_u64() as u32,
            oldest: rng.next_u64() as u32,
            window: rng.next_u64() as u32,
            tip: digest(rng),
            work: U256(core::array::from_fn(|_| rng.next_u64())),
            node: rng.next_u64(),
        }
    }

    fn header(rng: &mut Rng) -> Header {
        Header {
            prev_hash: digest(rng),
            height: rng.next_u64() as u32,
            timestamp: rng.next_u64(),
            body_commitment: digest(rng),
            state_root: digest(rng),
            statement: digest(rng),
            aux: core::array::from_fn(|_| rng.next_u64() as u8),
            mix: digest(rng),
            nonce: core::array::from_fn(|_| rng.next_u64() as u8),
        }
    }

    /// One of each message, of any size it may be; `data` and `name`
    /// are what the borrowed ones borrow.
    fn every<'a>(rng: &mut Rng, data: &'a [u8], name: &'a [u8]) -> Vec<Message<'a>> {
        let mut addrs = Addrs::new();
        for _ in 0..rng.next_u64() % (MAX_ADDRS as u64 + 1) {
            addrs.push(SocketAddrV4::new(Ipv4Addr::from(rng.next_u64() as u32), rng.next_u64() as u16));
        }
        let ids: Vec<Digest> = (0..1 + rng.next_u64() % LOCATOR as u64).map(|_| digest(rng)).collect();
        let mut ranges = Ranges::new();
        for _ in 0..1 + rng.next_u64() % 200 {
            ranges.push(rng.next_u64() as u32 % 3000);
        }
        let len = 1 + rng.next_u64() as u32 % 100_000;
        let index = rng.next_u64() as u32 % crate::transport::chunk_count(len);
        let n = crate::transport::chunk_len(len, index).unwrap();
        vec![
            Message::Ping(status(rng)),
            Message::Pong(status(rng)),
            Message::GetPeers { token: rng.next_u64() },
            Message::Peers(addrs),
            Message::FindFork { token: rng.next_u64(), locator: Locator::new(&ids).unwrap() },
            Message::Fork { height: rng.next_u64() as u32, id: digest(rng) },
            Message::Block { header: header(rng), len: rng.next_u64() as u32 },
            Message::Tx { id: digest(rng), len: rng.next_u64() as u32 },
            Message::GetLeaves { token: rng.next_u64(), id: digest(rng) },
            Message::Session { token: rng.next_u64(), grant: rng.next_u64(), id: digest(rng), seq: rng.next_u64() },
            Message::SessionState { id: digest(rng), seq: rng.next_u64(), token: rng.next_u64(), echo: rng.next_u64() },
            Message::Offer {
                token: rng.next_u64(),
                grant: rng.next_u64(),
                to: digest(rng),
                id: digest(rng),
                len: rng.next_u64() as u32,
            },
            Message::Notice { id: digest(rng), what: NOTICE_OFFLINE },
            Message::Stepped { name: rng.next_u64(), circuit: rng.next_u64(), kind: 4, count: 9, bytes: &[1, 2, 3] },
            Message::Stepped { name: 1, circuit: 2, kind: 3, count: 4, bytes: &[7; MAX_STEPPED] },
            Message::Carried { name: rng.next_u64() },
            Message::Alias { token: rng.next_u64(), grant: rng.next_u64(), n: digest(rng), seq: rng.next_u64() },
            Message::AliasState { n: digest(rng), seq: rng.next_u64() },
            Message::Carry {
                grant: rng.next_u64(),
                name: rng.next_u64(),
                circuit: rng.next_u64(),
                kind: 3,
                count: rng.next_u64(),
                len: rng.next_u64() as u32,
            },
            Message::Leaves {
                id: digest(rng),
                leaves: core::array::from_fn(|_| core::array::from_fn(|_| rng.next_u64() as u8)),
            },
            Message::Goodbye { token: rng.next_u64() },
            Message::Get(Get {
                token: rng.next_u64(),
                transfer: rng.next_u64(),
                seq: rng.next_u64() as u32,
                name: &name[..rng.next_u64() as usize % (name.len() + 1)],
                ranges,
            }),
            Message::Chunk(Chunk {
                transfer: rng.next_u64(),
                seq: rng.next_u64() as u32,
                len,
                index,
                data: &data[..n],
            }),
            Message::Gone(Gone { transfer: rng.next_u64() }),
        ]
    }

    #[test]
    fn every_message_roundtrips_and_is_exactly_its_bytes() {
        let mut rng = Rng::new(1);
        let data = [0xabu8; CHUNK_BYTES];
        let name = [0x33u8; crate::transport::wire::MAX_NAME];
        let mut buf = [0u8; MAX_DATAGRAM];
        for _ in 0..300 {
            for message in every(&mut rng, &data, &name) {
                let n = message.encode(NET, &mut buf);
                assert!(n <= MAX_DATAGRAM);
                assert_eq!(Message::decode(NET, &buf[..n]), Ok(message));
                // Not of another network.
                assert!(Message::decode(*b"TESU", &buf[..n]).is_err());
                // Not with a byte less, nor with one more.
                assert!(Message::decode(NET, &buf[..n - 1]).is_err(), "{message:?}");
                if n < MAX_DATAGRAM {
                    let mut longer = buf[..n].to_vec();
                    longer.push(0);
                    assert!(Message::decode(NET, &longer).is_err(), "{message:?}");
                }
            }
        }
    }

    #[test]
    fn the_largest_of_each_fits_a_datagram() {
        let mut buf = [0u8; MAX_DATAGRAM];
        let d = [1u8; 32];
        let mut addrs = Addrs::new();
        while addrs.push(SocketAddrV4::new(Ipv4Addr::LOCALHOST, 1)) {}
        assert_eq!(Message::Peers(addrs).encode(NET, &mut buf), HEAD + 1 + 6 * MAX_ADDRS);
        let locator = Locator::new(&[d; LOCATOR]).unwrap();
        assert_eq!(Message::FindFork { token: 0, locator }.encode(NET, &mut buf), HEAD + 9 + 32 * LOCATOR);
        let data = [0u8; CHUNK_BYTES];
        let chunk = Chunk { transfer: 0, seq: 0, len: CHUNK_BYTES as u32, index: 0, data: &data };
        assert_eq!(Message::Chunk(chunk).encode(NET, &mut buf), HEAD + MAX_CHUNK);
        assert_eq!(HEAD + MAX_CHUNK, 1225);
        let mut ranges = Ranges::new();
        for i in 0..crate::transport::wire::MAX_RANGES as u32 {
            ranges.push(2 * i);
        }
        let get = Get { token: 0, transfer: 0, seq: 0, name: &[0; crate::transport::wire::MAX_NAME], ranges };
        assert_eq!(Message::Get(get).encode(NET, &mut buf), HEAD + MAX_GET);
        // A ping is answered with as much as it is, and no more.
        let s = Status {
            nonce: 0,
            version: 0,
            token: 0,
            genesis: d,
            height: 0,
            oldest: 0,
            window: 0,
            tip: d,
            work: U256::ZERO,
            node: 0,
        };
        let ping = Message::Ping(s).encode(NET, &mut buf);
        assert_eq!((ping, Message::Pong(s).encode(NET, &mut buf)), (HEAD + Status::BYTES, HEAD + Status::BYTES));
        assert_eq!(Status::BYTES, 136);
    }

    #[test]
    fn what_is_no_message_is_refused() {
        let mut buf = [0u8; MAX_DATAGRAM];
        let d = [1u8; 32];
        // Too short to say what it is; a message there is not; the
        // messages kept for later.
        assert!(Message::decode(NET, &[]).is_err());
        assert!(Message::decode(NET, b"TEST").is_err());
        let n = Message::Goodbye { token: 1 }.encode(NET, &mut buf);
        for kind in [0u8, 12, 15, 19, 32, 47, 255] {
            buf[4] = kind;
            assert!(Message::decode(NET, &buf[..n]).is_err(), "{kind}");
        }
        // More addresses than there may be, and fewer than it says.
        let mut b = b"TEST\x04\x21".to_vec();
        (0..33u8).for_each(|k| b.extend_from_slice(&[10, 0, 0, k + 1, 1, 1]));
        assert!(Message::decode(NET, &b).is_err());
        b[5] = 32;
        assert!(Message::decode(NET, &b).is_err());
        assert!(Message::decode(NET, &b[..6 + 6 * 32]).is_ok());
        // An address said twice, one nothing is at, and no port.
        for (at, to) in [(6 + 6 + 3, 1u8), (6, 0), (6 + 4, 0)] {
            let mut bad = b[..6 + 6 * 32].to_vec();
            bad[at] = to;
            if at == 6 {
                bad[6..10].fill(0);
            }
            if at == 6 + 4 {
                bad[10..12].fill(0);
            }
            assert!(Message::decode(NET, &bad).is_err(), "{at}");
        }
        // A locator of nothing, and of too much.
        let n = Message::FindFork { token: 1, locator: Locator::new(&[d]).unwrap() }.encode(NET, &mut buf);
        assert!(Message::decode(NET, &buf[..n]).is_ok());
        buf[13] = 0;
        assert!(Message::decode(NET, &buf[..n - 32]).is_err());
        assert!(Locator::new(&[]).is_none() && Locator::new(&[d; LOCATOR + 1]).is_none());
        // Longer than any datagram.
        assert!(Message::decode(NET, &[0; MAX_DATAGRAM + 1]).is_err());
        // Random bytes after a true head: refused or taken, never a
        // panic.
        let mut rng = Rng::new(3);
        for _ in 0..20_000 {
            let mut b = b"TEST".to_vec();
            b.push(rng.next_u64() as u8 % 20);
            b.extend((0..rng.next_u64() % 300).map(|_| rng.next_u64() as u8));
            let _ = Message::decode(NET, &b);
        }
    }
}
