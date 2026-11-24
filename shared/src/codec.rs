//! Bytes: how proofs are written and read.
//!
//! Numbers are little-endian. A list is its length as four bytes and then
//! its items. A reader never panics on what it is given: every read says
//! whether the bytes were there.

use crate::field::F;
use crate::hash::Digest;

/// Serialized size of a digest.
pub const DIGEST_BYTES: usize = 32;

/// Serialized size of an output's position where blocks carry one: six
/// bytes, for positions below `2^48`. The chain holds `2^41` outputs at
/// most ([`crate::output::OUTPUT_CAPACITY`]), which five bytes fall short of.
pub const POSITION_BYTES: usize = 6;

/// Reads a position of [`POSITION_BYTES`] from the front of `bytes`.
pub fn read_position(bytes: &[u8]) -> Option<(u64, &[u8])> {
    let (head, rest) = bytes.split_at_checked(POSITION_BYTES)?;
    let mut buf = [0u8; 8];
    buf[..POSITION_BYTES].copy_from_slice(head);
    Some((u64::from_le_bytes(buf), rest))
}

/// Writes `position` to `out`, which must be [`POSITION_BYTES`] long.
/// Panics for a position that does not fit: none is cut short silently.
pub fn write_position(out: &mut [u8], position: u64) {
    assert!(position >> (8 * POSITION_BYTES) == 0, "position {position} does not fit {POSITION_BYTES} bytes");
    out.copy_from_slice(&position.to_le_bytes()[..POSITION_BYTES]);
}

pub fn read_u32(bytes: &[u8]) -> Option<(u32, &[u8])> {
    let (head, rest) = bytes.split_at_checked(4)?;
    Some((u32::from_le_bytes(head.try_into().unwrap()), rest))
}

pub fn read_u64(bytes: &[u8]) -> Option<(u64, &[u8])> {
    let (head, rest) = bytes.split_at_checked(8)?;
    Some((u64::from_le_bytes(head.try_into().unwrap()), rest))
}

pub fn read_digest(bytes: &[u8]) -> Option<(Digest, &[u8])> {
    let (head, rest) = bytes.split_at_checked(DIGEST_BYTES)?;
    Some((head.try_into().unwrap(), rest))
}

#[derive(Default)]
pub struct Writer(pub Vec<u8>);

impl Writer {
    pub fn with_capacity(n: usize) -> Writer {
        Writer(Vec::with_capacity(n))
    }

    pub fn finish(self) -> Vec<u8> {
        self.0
    }

    pub fn digest_vec(&mut self, ds: &[Digest]) {
        self.digests(ds);
    }

    /// Bytes, as they are.
    pub fn bytes(&mut self, b: &[u8]) {
        self.0.extend_from_slice(b);
    }

    pub fn u32(&mut self, x: u32) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }

    pub fn u64(&mut self, x: u64) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }

    pub fn f(&mut self, x: F) {
        self.0.extend_from_slice(&x.to_bytes());
    }

    pub fn digest(&mut self, d: &Digest) {
        self.0.extend_from_slice(d);
    }

    /// A list's length.
    pub fn len(&mut self, n: usize) {
        self.u32(u32::try_from(n).expect("a list of a proof is short"));
    }

    pub fn fs(&mut self, xs: &[F]) {
        self.len(xs.len());
        xs.iter().for_each(|x| self.f(*x));
    }

    pub fn digests(&mut self, ds: &[Digest]) {
        self.len(ds.len());
        ds.iter().for_each(|d| self.digest(d));
    }
}

pub struct Reader<'a>(pub &'a [u8]);

impl<'a> Reader<'a> {
    pub fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if self.0.len() < n {
            return None;
        }
        let (head, rest) = self.0.split_at(n);
        self.0 = rest;
        Some(head)
    }

    pub fn u32(&mut self) -> Option<u32> {
        let b = self.take(4)?;
        #[cfg(test)]
        READS.with(|r| {
            if let Some(v) = r.borrow_mut().as_mut() {
                v.push(b.as_ptr() as usize);
            }
        });
        Some(u32::from_le_bytes(b.try_into().unwrap()))
    }

    pub fn digest_vec(&mut self) -> Option<Vec<Digest>> {
        self.digests()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    pub fn f(&mut self) -> Option<F> {
        Some(F::from_bytes(self.take(16)?.try_into().unwrap()))
    }

    pub fn digest(&mut self) -> Option<Digest> {
        Some(self.take(32)?.try_into().unwrap())
    }

    /// A list's length, for items of `item` bytes at least: none if the
    /// bytes left could not hold so many, so that a length is never
    /// taken on trust for an allocation.
    pub fn len(&mut self, item: usize) -> Option<usize> {
        let n = self.u32()? as usize;
        (n.checked_mul(item)? <= self.0.len()).then_some(n)
    }

    pub fn fs(&mut self) -> Option<Vec<F>> {
        let n = self.len(16)?;
        (0..n).map(|_| self.f()).collect()
    }

    pub fn digests(&mut self) -> Option<Vec<Digest>> {
        let n = self.len(32)?;
        (0..n).map(|_| self.digest()).collect()
    }

    /// Whether everything has been read.
    pub fn end(&self) -> bool {
        self.0.is_empty()
    }
}

#[cfg(test)]
thread_local! {
    /// Tests: where each `u32` read came from, while [`u32_fields`] records.
    static READS: std::cell::RefCell<Option<Vec<usize>>> = const { std::cell::RefCell::new(None) };
}

/// Tests: the offsets in `bytes` of every `u32` that `decode` reads from
/// them, in order. Every count, length, height, index and flag of the
/// formats here is one, so this finds a format's structural fields without
/// describing the format. Reads from copies of `bytes` are not seen.
#[cfg(test)]
pub(crate) fn u32_fields(bytes: &[u8], decode: impl FnOnce(&[u8])) -> Vec<usize> {
    READS.with(|r| *r.borrow_mut() = Some(Vec::new()));
    decode(bytes);
    let reads = READS.with(|r| r.borrow_mut().take()).unwrap_or_default();
    let base = bytes.as_ptr() as usize;
    let mut out: Vec<usize> =
        reads.into_iter().filter(|&a| a >= base && a + 4 <= base + bytes.len()).map(|a| a - base).collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Tests: every structural field of `bytes` (see [`u32_fields`]) set in
/// turn to each boundary value (0, 1, 2, 31, 32, 33, 63, 64, 255, 256,
/// 2^31, `u32::MAX`, and one either side of its own), and `check` run on
/// the result: `None` if it does not decode, `Some(accepted)` if it does.
/// Returns the mutants that panicked and those that were accepted; both
/// should be empty. Deterministic, unlike random mutation, which rarely
/// lands a chosen value on a chosen field of a large proof.
#[cfg(test)]
pub(crate) fn sweep_fields(bytes: &[u8], check: impl Fn(&[u8]) -> Option<bool>) -> (usize, Vec<String>, Vec<String>) {
    let fields = u32_fields(bytes, |b| {
        check(b);
    });
    let (mut panicked, mut accepted) = (Vec::new(), Vec::new());
    let quiet = crate::test_util::Quiet::new();
    for &at in &fields {
        let own = u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
        let values =
            [0, 1, 2, 31, 32, 33, 63, 64, 255, 256, 1 << 31, u32::MAX, own.wrapping_add(1), own.wrapping_sub(1)];
        for v in values {
            if v == own {
                continue;
            }
            let mut b = bytes.to_vec();
            b[at..at + 4].copy_from_slice(&v.to_le_bytes());
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&b))) {
                Err(e) => {
                    let msg =
                        e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()));
                    panicked.push(format!("u32 at {at} ({own}) set to {v}: {}", msg.unwrap_or_default()));
                }
                Ok(Some(true)) => accepted.push(format!("u32 at {at} ({own}) set to {v}")),
                Ok(_) => {}
            }
        }
    }
    drop(quiet);
    (fields.len(), panicked, accepted)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn what_is_written_is_read() {
        let mut w = Writer::default();
        w.u32(7);
        w.u64(u64::MAX - 1);
        w.f(F(1 << 100));
        w.digest(&[9; 32]);
        w.fs(&[F(1), F(2)]);
        w.digests(&[[3; 32]]);
        let mut r = Reader(&w.0);
        assert_eq!(
            (r.u32(), r.u64(), r.f(), r.digest()),
            (Some(7), Some(u64::MAX - 1), Some(F(1 << 100)), Some([9; 32]))
        );
        assert_eq!((r.fs(), r.digests()), (Some(vec![F(1), F(2)]), Some(vec![[3; 32]])));
        assert!(r.end() && r.u32().is_none());
    }

    #[test]
    fn a_length_is_not_taken_on_trust() {
        // A list said to be longer than the bytes that follow.
        let mut w = Writer::default();
        w.u32(u32::MAX);
        w.f(F::ONE);
        assert!(Reader(&w.0).fs().is_none());
        assert!(Reader(&w.0).digests().is_none());
        assert!(Reader(&[1, 0, 0]).u32().is_none());
    }

    /// The tests' sweep finds every count a decoder reads and tries the
    /// values at its bounds: a decoder that trusts one is found out.
    #[test]
    fn the_sweep_finds_a_trusted_count() {
        let mut w = Writer::default();
        w.digests(&[[1; 32], [2; 32], [3; 32]]);
        w.u32(9);
        let bytes = w.finish();
        let fields = u32_fields(&bytes, |b| {
            let mut r = Reader(b);
            let _ = (r.digests(), r.u32());
        });
        assert_eq!(fields, vec![0, 100]);
        // A careful decoder: nothing but the bytes it was given decodes.
        let careful = |b: &[u8]| {
            let mut r = Reader(b);
            let (v, n) = (r.digests()?, r.u32()?);
            (r.is_empty() && v.len() == 3 && n == 9).then_some(false)
        };
        let (found, panicked, accepted) = sweep_fields(&bytes, careful);
        assert_eq!((found, panicked.len(), accepted.len()), (2, 0, 0));
        // One that accepts any count, and one that indexes by it.
        let (_, panicked, accepted) = sweep_fields(&bytes, |b| Reader(&b[100..]).u32().map(|_| true));
        assert!(panicked.is_empty() && accepted.len() >= 10);
        let (_, panicked, _) = sweep_fields(&bytes, |b| {
            let n = Reader(&b[100..]).u32()? as usize;
            Some([0u8; 16][n] == 1)
        });
        assert!(!panicked.is_empty());
    }
}
