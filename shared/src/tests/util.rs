//! What tests share.

use crate::field::F;

/// A small generator of test values (splitmix64): the same on every
/// run, and random in no sense a proof needs.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub fn f(&mut self) -> F {
        F((self.next_u64() as u128) << 64 | self.next_u64() as u128)
    }

    /// Any digest.
    pub fn digest(&mut self) -> crate::hash::Digest {
        let mut d = [0u8; 32];
        d.chunks_exact_mut(8).for_each(|c| c.copy_from_slice(&self.next_u64().to_le_bytes()));
        d
    }

    pub fn fs(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.f()).collect()
    }
}

thread_local! {
    static QUIET: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Keeps this thread's panics unreported while it lives (a fuzzer
/// catching the panics it provokes), and only this thread's: the panic
/// hook is the process's, and tests run in parallel, so swapping it
/// would hide other tests' failures, and two swaps overlapping could
/// leave it silent for the rest of the run.
pub(crate) struct Quiet(bool);

impl Quiet {
    pub(crate) fn new() -> Quiet {
        static HOOK: std::sync::Once = std::sync::Once::new();
        HOOK.call_once(|| {
            let report = std::panic::take_hook();
            std::panic::set_hook(Box::new(move |info| {
                if !QUIET.with(|q| q.get()) {
                    report(info)
                }
            }));
        });
        Quiet(QUIET.with(|q| q.replace(true)))
    }
}

impl Drop for Quiet {
    fn drop(&mut self) {
        QUIET.with(|q| q.set(self.0));
    }
}

/// Tests: a fuzzer's iterations and seed: `TABMINER_FUZZ_ITERS`, else
/// `iters` times `TABMINER_FUZZ_SCALE` (1 by default; the nightly run,
/// `fuzz.yml`, sets it), and `TABMINER_FUZZ_SEED`, else `seed`. Prints
/// the seed so a failure can be replayed.
pub(crate) fn fuzz_params(iters: u64, seed: u64) -> (u64, u64) {
    let var = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<u64>().ok());
    let scaled = iters.saturating_mul(var("TABMINER_FUZZ_SCALE").unwrap_or(1));
    let (iters, seed) = (var("TABMINER_FUZZ_ITERS").unwrap_or(scaled), var("TABMINER_FUZZ_SEED").unwrap_or(seed));
    eprintln!("fuzz: {iters} iterations, seed {seed} (TABMINER_FUZZ_SEED={seed} to replay)");
    (iters, seed)
}

/// Fuzzes a decoder of untrusted bytes: `iters` mutants of the valid
/// `samples` (a bit flipped, bytes overwritten, truncated, extended, a
/// slice set to 0xff or duplicated, two samples spliced) and random
/// inputs. `decode` returns `None` when it refuses the bytes, else
/// their encoding again (or `None` inside for a decoder with no
/// encoder). It must never panic, and what it decodes must encode back
/// to the very bytes (one object, one encoding). Returns how many
/// mutants decoded; panics with every failure.
pub fn fuzz_decoder(
    name: &str,
    samples: &[Vec<u8>],
    iters: u64,
    decode: impl Fn(&[u8]) -> Option<Option<Vec<u8>>>,
) -> usize {
    let (iters, seed) = fuzz_params(iters, 0xdec0de);
    let mut rng = Rng(seed | 1);
    for s in samples {
        match decode(s) {
            None => panic!("{name}: a valid sample is refused"),
            Some(Some(again)) => assert_eq!(&again, s, "{name}: a sample encodes to other bytes"),
            Some(None) => {}
        }
    }
    let (mut decoded, mut failures) = (0, Vec::new());
    let quiet = crate::test_util::Quiet::new();
    for n in 0..iters {
        let mut r = |m: usize| (rng.next_u64() % m.max(1) as u64) as usize;
        let si = r(samples.len());
        let mut b = samples[si].clone();
        let (at, len) = (r(b.len().max(1)), 1 + r(64));
        let what = match r(9) {
            0 if !b.is_empty() => {
                b[at] ^= 1 << r(8);
                "bit flipped"
            }
            1 if !b.is_empty() => {
                b[at] = r(256) as u8;
                "byte set"
            }
            2 => {
                for i in at..(at + len).min(b.len()) {
                    b[i] = r(256) as u8;
                }
                "bytes randomized"
            }
            3 => {
                b.truncate(at);
                "truncated"
            }
            4 => {
                b.extend((0..len).map(|_| r(256) as u8));
                "extended"
            }
            5 => {
                for i in at..(at + len).min(b.len()) {
                    b[i] = 0xff;
                }
                "bytes set to 0xff"
            }
            6 if !b.is_empty() => {
                let end = (at + len).min(b.len());
                let slice = b[at..end].to_vec();
                b.splice(at..at, slice);
                "bytes duplicated"
            }
            7 => {
                let other = &samples[r(samples.len())];
                let cut = r(other.len().max(1));
                b.truncate(at);
                b.extend_from_slice(&other[cut.min(other.len())..]);
                "spliced"
            }
            _ => {
                b = (0..r(256)).map(|_| r(256) as u8).collect();
                "random"
            }
        };
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| decode(&b))) {
            Err(_) => failures.push(format!("mutant {n} ({what}): panicked")),
            Ok(Some(Some(again))) if again != b => {
                let at = again.iter().zip(&b).position(|(x, y)| x != y).unwrap_or(again.len().min(b.len()));
                failures.push(format!(
                    "mutant {n} ({what}) of sample {si}: decodes, but encodes to other bytes \
                     (from byte {at}: {:02x?} read, {:02x?} written; {} bytes read, {} written)",
                    &b[at..(at + 8).min(b.len())],
                    &again[at..(at + 8).min(again.len())],
                    b.len(),
                    again.len()
                ))
            }
            Ok(Some(_)) => decoded += 1,
            Ok(None) => {}
        }
    }
    drop(quiet);
    assert!(failures.is_empty(), "{name} (seed {seed}): {} failures\n{}", failures.len(), failures.join("\n"));
    decoded
}
