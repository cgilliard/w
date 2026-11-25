//! The three datagrams: a request for chunks, a chunk, and "I do not
//! have it".
//!
//! These are the bodies only. The layer above puts before them whatever
//! says which network the datagram is of and which of its kinds it is,
//! in the twelve bytes [`super::CHUNK_BYTES`] leaves.
//!
//! Integers are little-endian. Nothing is taken that is not exactly the
//! encoding of something that could have been sent.

use super::{CHUNK_BYTES, MAX_WINDOW, chunk_len};
use crate::error::Error;

/// The longest name an object is asked for by.
pub const MAX_NAME: usize = 64;
/// The most ranges in one request.
pub const MAX_RANGES: usize = 64;
/// The longest request.
pub const MAX_GET: usize = 8 + 8 + 4 + 1 + MAX_NAME + 1 + MAX_RANGES * 6;
/// The longest chunk.
pub const MAX_CHUNK: usize = CHUNK_HEAD + CHUNK_BYTES;
const CHUNK_HEAD: usize = 20;

/// Chunks `start`, `start + 1`, ... `count` of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Range {
    pub start: u32,
    pub count: u16,
}

/// Indexes of chunks, as runs: [`MAX_RANGES`] runs and [`MAX_WINDOW`]
/// chunks at most. The order they were added in is the order they are
/// asked, and sent, in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ranges {
    n: usize,
    chunks: u32,
    r: [Range; MAX_RANGES],
}

impl Default for Ranges {
    fn default() -> Ranges {
        Ranges::new()
    }
}

impl Ranges {
    pub const fn new() -> Ranges {
        Ranges { n: 0, chunks: 0, r: [Range { start: 0, count: 0 }; MAX_RANGES] }
    }

    /// Adds `index`, to the last run if it follows it. False, and
    /// nothing added, when there is no room.
    pub fn push(&mut self, index: u32) -> bool {
        if self.chunks == MAX_WINDOW {
            return false;
        }
        if self.n > 0 {
            let last = &mut self.r[self.n - 1];
            if last.start.checked_add(last.count as u32) == Some(index) && last.count < u16::MAX {
                last.count += 1;
                self.chunks += 1;
                return true;
            }
        }
        if self.n == MAX_RANGES {
            return false;
        }
        self.r[self.n] = Range { start: index, count: 1 };
        self.n += 1;
        self.chunks += 1;
        true
    }

    /// Adds a run after the others, joined to the last if it follows
    /// it. False, and nothing added, when there is no room.
    pub fn push_run(&mut self, run: Range) -> bool {
        if run.count == 0 || self.chunks + run.count as u32 > MAX_WINDOW {
            return run.count == 0;
        }
        if self.n > 0 {
            let last = &mut self.r[self.n - 1];
            if last.start.checked_add(last.count as u32) == Some(run.start)
                && let Some(count) = last.count.checked_add(run.count)
            {
                last.count = count;
                self.chunks += run.count as u32;
                return true;
            }
        }
        if self.n == MAX_RANGES {
            return false;
        }
        self.r[self.n] = run;
        self.n += 1;
        self.chunks += run.count as u32;
        true
    }

    pub fn clear(&mut self) {
        self.n = 0;
        self.chunks = 0;
    }

    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// How many chunks.
    pub fn chunks(&self) -> u32 {
        self.chunks
    }

    pub fn as_slice(&self) -> &[Range] {
        &self.r[..self.n]
    }

    /// The indexes, in order.
    pub fn indexes(&self) -> impl Iterator<Item = u32> + '_ {
        self.as_slice().iter().flat_map(|r| (0..r.count as u32).map(move |i| r.start + i))
    }
}

/// A request for chunks of an object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Get<'a> {
    /// What the serving side gave this address to show it is there
    /// ([`super::token::Tokens`]).
    pub token: u64,
    /// The asking side's number for this fetch: every chunk sent in
    /// answer carries it.
    pub transfer: u64,
    /// The number of the first chunk asked for here, as an ask: the
    /// next is one more, and so on through the ranges. Each chunk sent
    /// in answer carries its own back.
    pub seq: u32,
    /// Which object: the layer above's business.
    pub name: &'a [u8],
    pub ranges: Ranges,
}

impl<'a> Get<'a> {
    /// Writes the request to the front of `out`, which is at least
    /// [`MAX_GET`] long, and returns its length.
    pub fn encode(&self, out: &mut [u8]) -> usize {
        assert!(self.name.len() <= MAX_NAME && !self.ranges.is_empty());
        let mut w = Out(out, 0);
        w.put(&self.token.to_le_bytes());
        w.put(&self.transfer.to_le_bytes());
        w.put(&self.seq.to_le_bytes());
        w.put(&[self.name.len() as u8]);
        w.put(self.name);
        w.put(&[self.ranges.n as u8]);
        for r in self.ranges.as_slice() {
            w.put(&r.start.to_le_bytes());
            w.put(&r.count.to_le_bytes());
        }
        w.1
    }

    pub fn decode(bytes: &'a [u8]) -> Result<Get<'a>, Error> {
        const BAD: Error = Error::Malformed("request for chunks");
        let mut r = In(bytes);
        let token = u64::from_le_bytes(r.array().ok_or(BAD)?);
        let transfer = u64::from_le_bytes(r.array().ok_or(BAD)?);
        let seq = u32::from_le_bytes(r.array().ok_or(BAD)?);
        let [name_len] = r.array().ok_or(BAD)?;
        if name_len as usize > MAX_NAME {
            return Err(BAD);
        }
        let name = r.take(name_len as usize).ok_or(BAD)?;
        let [n] = r.array().ok_or(BAD)?;
        if n == 0 || n as usize > MAX_RANGES {
            return Err(BAD);
        }
        let mut ranges = Ranges::new();
        for i in 0..n as usize {
            let start = u32::from_le_bytes(r.array().ok_or(BAD)?);
            let count = u16::from_le_bytes(r.array().ok_or(BAD)?);
            // A run is not empty and does not pass the last index.
            if count == 0 || start.checked_add(count as u32 - 1).is_none() {
                return Err(BAD);
            }
            // (Nor does it follow the one before it, with room in that
            // one: they would have been sent as one.)
            if i > 0 {
                let last = ranges.r[i - 1];
                if last.start.checked_add(last.count as u32) == Some(start) && last.count.checked_add(count).is_some() {
                    return Err(BAD);
                }
            }
            ranges.r[i] = Range { start, count };
            ranges.chunks = ranges.chunks.saturating_add(count as u32);
        }
        ranges.n = n as usize;
        if ranges.chunks > MAX_WINDOW || !r.0.is_empty() {
            return Err(BAD);
        }
        Ok(Get { token, transfer, seq, name, ranges })
    }
}

/// One chunk of an object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Chunk<'a> {
    /// The number of the fetch it answers.
    pub transfer: u64,
    /// The number of the ask it answers ([`Get::seq`]).
    pub seq: u32,
    /// The whole object's length.
    pub len: u32,
    pub index: u32,
    pub data: &'a [u8],
}

impl<'a> Chunk<'a> {
    /// Writes the chunk to the front of `out`, which is at least
    /// [`MAX_CHUNK`] long, and returns its length.
    pub fn encode(&self, out: &mut [u8]) -> usize {
        assert_eq!(chunk_len(self.len, self.index), Some(self.data.len()));
        let mut w = Out(out, 0);
        w.put(&self.transfer.to_le_bytes());
        w.put(&self.seq.to_le_bytes());
        w.put(&self.len.to_le_bytes());
        w.put(&self.index.to_le_bytes());
        w.put(self.data);
        w.1
    }

    /// A chunk whose bytes are as many as an object of its length has
    /// at its index.
    pub fn decode(bytes: &'a [u8]) -> Result<Chunk<'a>, Error> {
        const BAD: Error = Error::Malformed("chunk");
        let mut r = In(bytes);
        let transfer = u64::from_le_bytes(r.array().ok_or(BAD)?);
        let seq = u32::from_le_bytes(r.array().ok_or(BAD)?);
        let len = u32::from_le_bytes(r.array().ok_or(BAD)?);
        let index = u32::from_le_bytes(r.array().ok_or(BAD)?);
        if chunk_len(len, index) != Some(r.0.len()) {
            return Err(BAD);
        }
        Ok(Chunk { transfer, seq, len, index, data: r.0 })
    }
}

/// The serving side does not have the object asked for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gone {
    pub transfer: u64,
}

impl Gone {
    pub const LEN: usize = 8;

    pub fn encode(&self, out: &mut [u8]) -> usize {
        out[..8].copy_from_slice(&self.transfer.to_le_bytes());
        8
    }

    pub fn decode(bytes: &[u8]) -> Result<Gone, Error> {
        match <[u8; 8]>::try_from(bytes) {
            Ok(b) => Ok(Gone { transfer: u64::from_le_bytes(b) }),
            Err(_) => Err(Error::Malformed("no such object")),
        }
    }
}

struct Out<'a>(&'a mut [u8], usize);

impl Out<'_> {
    fn put(&mut self, bytes: &[u8]) {
        self.0[self.1..self.1 + bytes.len()].copy_from_slice(bytes);
        self.1 += bytes.len();
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    #[test]
    fn ranges_are_runs_in_the_order_added() {
        let mut r = Ranges::new();
        for i in [5, 6, 7, 2, 3, 9, 8] {
            assert!(r.push(i));
        }
        assert_eq!(
            r.as_slice(),
            [(5, 3), (2, 2), (9, 1), (8, 1)].map(|(start, count)| Range { start, count }).as_slice()
        );
        assert_eq!(r.indexes().collect::<Vec<_>>(), [5, 6, 7, 2, 3, 9, 8]);
        assert_eq!(r.chunks(), 7);
        // No more runs than fit, though a run may still grow.
        let mut r = Ranges::new();
        for i in 0..MAX_RANGES as u32 {
            assert!(r.push(2 * i));
        }
        assert!(!r.push(1000));
        assert!(r.push(2 * MAX_RANGES as u32 - 1));
        // No more chunks than a window.
        let mut r = Ranges::new();
        for i in 0..MAX_WINDOW {
            assert!(r.push(i));
        }
        assert!(!r.push(MAX_WINDOW));
        assert_eq!((r.as_slice().len(), r.chunks()), (1, MAX_WINDOW));
        // Whole runs: joined where they follow, and all or nothing.
        let mut r = Ranges::new();
        let run = |start, count| Range { start, count };
        assert!(r.push_run(run(10, 5)) && r.push_run(run(15, 5)) && r.push_run(run(40, 2)) && r.push_run(run(0, 0)));
        assert_eq!(r.as_slice(), [run(10, 10), run(40, 2)].as_slice());
        assert!(!r.push_run(run(100, MAX_WINDOW as u16 - 11)));
        assert!(r.push_run(run(100, MAX_WINDOW as u16 - 12)));
        assert_eq!((r.chunks(), r.as_slice().len()), (MAX_WINDOW, 3));
        // The last index there is.
        let mut r = Ranges::new();
        assert!(r.push(u32::MAX - 1) && r.push(u32::MAX) && r.push(0));
        assert_eq!(r.as_slice().len(), 2);
    }

    #[test]
    fn a_request_roundtrips() {
        let mut rng = Rng::new(1);
        let mut buf = [0u8; MAX_GET];
        for _ in 0..500 {
            let mut ranges = Ranges::new();
            for _ in 0..1 + rng.next_u64() % 300 {
                ranges.push(rng.next_u64() as u32 % 5000);
            }
            let name: Vec<u8> = (0..rng.next_u64() % (MAX_NAME as u64 + 1)).map(|_| rng.next_u64() as u8).collect();
            let get = Get {
                token: rng.next_u64(),
                transfer: rng.next_u64(),
                seq: rng.next_u64() as u32,
                name: &name,
                ranges,
            };
            let n = get.encode(&mut buf);
            assert_eq!(Get::decode(&buf[..n]), Ok(get));
            // Not with a byte more, nor with one less.
            assert!(Get::decode(&buf[..n - 1]).is_err());
            let mut longer = buf[..n].to_vec();
            longer.push(0);
            assert!(Get::decode(&longer).is_err());
        }
        // The longest there is fits.
        let mut ranges = Ranges::new();
        for i in 0..MAX_RANGES as u32 {
            ranges.push(2 * i);
        }
        let get = Get { token: 1, transfer: 2, seq: 3, name: &[7; MAX_NAME], ranges };
        assert_eq!(get.encode(&mut buf), MAX_GET);
    }

    #[test]
    fn a_request_that_could_not_have_been_sent_is_refused() {
        let mut buf = [0u8; MAX_GET];
        let mut ranges = Ranges::new();
        ranges.push(3);
        let n = Get { token: 1, transfer: 2, seq: 3, name: b"ab", ranges }.encode(&mut buf);
        let good = buf[..n].to_vec();
        let with = |at: usize, v: &[u8]| {
            let mut b = good.clone();
            b[at..at + v.len()].copy_from_slice(v);
            Get::decode(&b).is_err()
        };
        assert!(Get::decode(&good).is_ok());
        // A name longer than any, no ranges, more ranges than fit.
        assert!(with(20, &[MAX_NAME as u8 + 1]));
        assert!(with(23, &[0]));
        assert!(with(23, &[2]));
        // An empty run, and one that passes the last index.
        assert!(with(28, &[0, 0]));
        assert!(with(24, &[0xff, 0xff, 0xff, 0xff, 2, 0]));
        assert!(!with(24, &[0xff, 0xff, 0xff, 0xff, 1, 0]));
        // More chunks than a window, over two runs.
        let mut b = good[..23].to_vec();
        b.push(2);
        for _ in 0..2 {
            b.extend_from_slice(&0u32.to_le_bytes());
            b.extend_from_slice(&(MAX_WINDOW as u16 / 2 + 1).to_le_bytes());
        }
        assert!(Get::decode(&b).is_err());
        // Nothing at all, and random bytes: refused or taken, never a panic.
        assert!(Get::decode(&[]).is_err());
        let mut rng = Rng::new(2);
        for _ in 0..2000 {
            let b: Vec<u8> = (0..rng.next_u64() % 120).map(|_| rng.next_u64() as u8).collect();
            let _ = Get::decode(&b);
        }
    }

    #[test]
    fn a_chunk_roundtrips_and_is_as_long_as_its_place_says() {
        let mut buf = [0u8; MAX_CHUNK];
        let data = [9u8; CHUNK_BYTES];
        let c = CHUNK_BYTES as u32;
        for (len, index, n) in
            [(1, 0, 1), (c, 0, c), (c + 1, 0, c), (c + 1, 1, 1), (5 * c, 4, c), (u32::MAX, 3579139, 495)]
        {
            let chunk = Chunk { transfer: 77, seq: 0xdead_beef, len, index, data: &data[..n as usize] };
            let m = chunk.encode(&mut buf);
            assert_eq!(m, 20 + n as usize);
            assert_eq!(Chunk::decode(&buf[..m]), Ok(chunk));
            // A byte short, a byte long.
            assert!(Chunk::decode(&buf[..m - 1]).is_err());
            let mut longer = buf[..m].to_vec();
            longer.push(0);
            assert!(Chunk::decode(&longer).is_err());
        }
        // No object has no bytes; no chunk is past the end.
        let mut b = vec![0u8; 20];
        assert!(Chunk::decode(&b).is_err());
        b[12] = 1;
        b[16] = 1;
        assert!(Chunk::decode(&b).is_err());
        assert!(Chunk::decode(&b[..19]).is_err());
        assert_eq!(MAX_CHUNK, 1220);
    }

    #[test]
    fn gone_roundtrips() {
        let mut buf = [0u8; 8];
        assert_eq!(Gone { transfer: 0x0102030405060708 }.encode(&mut buf), Gone::LEN);
        assert_eq!(Gone::decode(&buf), Ok(Gone { transfer: 0x0102030405060708 }));
        assert!(Gone::decode(&buf[..7]).is_err() && Gone::decode(&[0; 9]).is_err());
    }
}
