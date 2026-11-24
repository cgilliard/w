//! Difficulty: targets, Bitcoin's compact encoding of them, and the
//! Bitcoin Cash ASERT retargeting algorithm (`aserti3-2d`).
//!
//! A [`Target`] is what a block's proof of work must not exceed. Nothing
//! here allocates.
//!
//! ASERT sets the next target directly from how far the chain is ahead of or
//! behind its ideal schedule, measured against a fixed anchor block:
//!
//! ```text
//! next_target = anchor_target * 2^((time_delta - ideal_block_time * (height_delta + 1)) / half_life)
//! ```
//!
//! with `time_delta` and `height_delta` taken from the block being evaluated
//! (the parent of the block whose target is wanted) relative to the anchor.
//! The exponent is fixed point with 16 fractional bits and the fractional
//! power of two is a cubic approximation, exactly as specified, so results
//! match the reference test vectors bit for bit.
//!
//! This chain anchors at genesis. The specification requires the anchor's
//! parent timestamp; genesis has no parent, so the anchor parent time is
//! defined as the genesis timestamp minus one block interval, which puts
//! genesis exactly on schedule.

use crate::hash::Digest;
pub use crate::u256::U256;

/// Ideal spacing between blocks, in seconds.
pub const IDEAL_BLOCK_TIME: i64 = 600;
/// ASERT half-life: two days.
pub const HALF_LIFE: i64 = 2 * 24 * 3600;
const RADIX_BITS: u32 = 16;

// ---------------------------------------------------------------------------
// Targets
// ---------------------------------------------------------------------------

/// A 248-bit target as 32 little-endian bytes (the last one zero);
/// `result <= target` passes.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Target(pub [u8; 32]);

/// The 248-bit integer a digest stands for: its first 31 bytes, the
/// first the least; as 32 little-endian bytes with the last one zero.
pub fn digest_to_u248_le(d: &Digest) -> [u8; 32] {
    let mut out = *d;
    out[31] = 0;
    out
}

impl Target {
    /// The largest possible target, 2^248 - 1: every result passes.
    pub const MAX: Target = {
        let mut t = [0xffu8; 32];
        t[31] = 0;
        Target(t)
    };

    /// Target requiring `bits` leading zero bits in the 248-bit result.
    pub fn from_leading_zero_bits(bits: u32) -> Target {
        assert!(bits <= 248);
        let ones = 248 - bits;
        let mut t = [0u8; 32];
        for (i, byte) in t.iter_mut().enumerate() {
            let lo = i as u32 * 8;
            if lo + 8 <= ones {
                *byte = 0xff;
            } else if lo < ones {
                *byte = ((1u32 << (ones - lo)) - 1) as u8;
            }
        }
        Target(t)
    }

    pub fn value(&self) -> U256 {
        U256::from_le_bytes(&self.0)
    }

    pub fn is_met_by(&self, result: &Digest) -> bool {
        U256::from_le_bytes(&digest_to_u248_le(result)) <= self.value()
    }
}

impl PartialOrd for Target {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Target {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.value().cmp(&other.value())
    }
}

impl From<Target> for U256 {
    fn from(t: Target) -> U256 {
        U256::from_le_bytes(&t.0)
    }
}

impl From<U256> for Target {
    fn from(v: U256) -> Target {
        Target(v.to_le_bytes())
    }
}

/// Decodes Bitcoin's compact `nBits` form. Negative or zero encodings give
/// zero; the result is not clamped.
pub fn compact_to_target(bits: u32) -> U256 {
    let size = bits >> 24;
    let mut word = bits & 0x007f_ffff;
    if bits & 0x0080_0000 != 0 || word == 0 {
        return U256::ZERO;
    }
    if size <= 3 {
        word >>= 8 * (3 - size);
        U256::from_u64(word as u64)
    } else {
        let shift = 8 * (size - 3);
        if shift >= 256 || U256::from_u64(word as u64).bits() + shift > 256 {
            // Does not fit: caller should treat as invalid; return MAX so it
            // exceeds any limit.
            return U256::MAX;
        }
        U256::from_u64(word as u64).shift_left(shift)
    }
}

/// Encodes a target in compact form, as Bitcoin does.
pub fn target_to_compact(target: U256) -> u32 {
    let mut size = target.bits().div_ceil(8);
    let mut compact: u64 =
        if size <= 3 { target.0[0] << (8 * (3 - size)) } else { target.shift_right(8 * (size - 3)).0[0] };
    if compact & 0x0080_0000 != 0 {
        compact >>= 8;
        size += 1;
    }
    (compact as u32) | (size << 24)
}

/// When blocks are due and how fast the target follows a chain that is
/// ahead of its schedule or behind it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Schedule {
    /// Seconds between blocks.
    pub block_time: i64,
    /// Seconds ahead of (behind) schedule that halve (double) the target.
    pub half_life: i64,
    /// The schedule starts at block 1 rather than genesis: for a network
    /// whose genesis is fixed long before it runs (`--network dev`), which
    /// would otherwise be behind schedule, at the easiest target, for good.
    pub from_first_block: bool,
}

impl Schedule {
    pub const MAINNET: Schedule =
        Schedule { block_time: IDEAL_BLOCK_TIME, half_life: HALF_LIFE, from_first_block: false };
}

/// Fixed parameters of an ASERT schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Asert {
    pub anchor_height: u64,
    /// Timestamp of the anchor block's parent (virtual for genesis).
    pub anchor_parent_time: i64,
    pub anchor_target: U256,
    /// Easiest permitted target.
    pub max_target: U256,
    pub half_life: i64,
    pub ideal_block_time: i64,
}

impl Asert {
    /// Schedule anchored at a genesis block with the given timestamp and
    /// target, using mainnet constants.
    pub fn from_genesis(genesis_time: i64, genesis_target: U256, max_target: U256) -> Asert {
        Self::anchored(0, genesis_time, genesis_target, max_target, Schedule::MAINNET)
    }

    /// Schedule anchored at the block at `height` with timestamp `time`
    /// and target `target`: its parent is taken to be one block time
    /// before it.
    pub fn anchored(height: u64, time: i64, target: U256, max_target: U256, schedule: Schedule) -> Asert {
        Asert {
            anchor_height: height,
            anchor_parent_time: time - schedule.block_time,
            anchor_target: target,
            max_target,
            half_life: schedule.half_life,
            ideal_block_time: schedule.block_time,
        }
    }

    /// Target of the block following the evaluation block at
    /// `(eval_height, eval_time)`. `eval_height` must not be below the anchor.
    pub fn next_target(&self, eval_height: u64, eval_time: i64) -> U256 {
        assert!(eval_height >= self.anchor_height, "evaluation block precedes anchor");
        let time_delta = eval_time as i128 - self.anchor_parent_time as i128;
        let height_delta = (eval_height - self.anchor_height) as i128;
        let radix: i128 = 1 << RADIX_BITS;
        // Truncating division, per the specification.
        let exponent =
            ((time_delta - self.ideal_block_time as i128 * (height_delta + 1)) * radix) / self.half_life as i128;
        let num_shifts = exponent >> RADIX_BITS; // arithmetic shift == floor division
        let frac = exponent - (num_shifts << RADIX_BITS);
        debug_assert!((0..radix).contains(&frac));
        let factor: i128 =
            ((195_766_423_245_049 * frac + 971_821_376 * frac * frac + 5127 * frac * frac * frac + (1i128 << 47))
                >> 48)
                + 65536;
        let product = self.anchor_target.mul_u64_wide(factor as u64);

        // next = product * 2^(num_shifts - 16)
        let shift = num_shifts - RADIX_BITS as i128;
        let next = if shift <= 0 {
            let s = (-shift).min(320) as u32;
            shr320(product, s)
        } else {
            let s = shift.min(512) as u32;
            if product.iter().all(|&l| l == 0) {
                Some(U256::ZERO)
            } else if bits320(product) + s > 256 {
                None
            } else {
                Some(U256([product[0], product[1], product[2], product[3]]).shift_left(s))
            }
        };
        match next {
            None => self.max_target,
            Some(t) if t.is_zero() => U256::ONE,
            Some(t) if t > self.max_target => self.max_target,
            Some(t) => t,
        }
    }
}

fn bits320(v: [u64; 5]) -> u32 {
    for i in (0..5).rev() {
        if v[i] != 0 {
            return 64 * i as u32 + 64 - v[i].leading_zeros();
        }
    }
    0
}

/// Shifts a five-limb value right; `None` if the result exceeds 256 bits.
fn shr320(v: [u64; 5], n: u32) -> Option<U256> {
    let mut out = [0u64; 5];
    if n < 320 {
        let (words, bits) = ((n / 64) as usize, n % 64);
        for i in 0..5 - words {
            let lo = v[i + words] >> bits;
            let hi = if bits > 0 && i + words + 1 < 5 { v[i + words + 1] << (64 - bits) } else { 0 };
            out[i] = lo | hi;
        }
    }
    if out[4] != 0 { None } else { Some(U256([out[0], out[1], out[2], out[3]])) }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX_BITS: u32 = 0x1d00_ffff;

    /// A target is its 256-bit value, either way.
    #[test]
    fn targets_are_their_values() {
        let a = U256::from_u64(0x1234).shift_left(100);
        let t: Target = a.into();
        assert_eq!((U256::from(t), t.value()), (a, a));
        assert_eq!(U256::from(Target::MAX), U256::MAX.shift_right(8));
        assert!(Target::from(U256::ONE) < Target::from(U256::from_u64(2)));
        assert_eq!(Target::from(U256::ONE).partial_cmp(&Target::MAX), Some(core::cmp::Ordering::Less));
    }

    #[test]
    fn targets() {
        let zero = [0u8; 32];
        let max = [0xffu8; 32];
        assert_eq!(digest_to_u248_le(&zero), [0u8; 32]);
        let packed = digest_to_u248_le(&max);
        assert_eq!((packed[31], &packed[..31]), (0, &max[..31]));

        assert!(Target::MAX.is_met_by(&max));
        assert_eq!(Target::from_leading_zero_bits(0), Target::MAX);
        let t8 = Target::from_leading_zero_bits(8);
        assert_eq!(t8.0[31], 0);
        assert_eq!(t8.0[30], 0);
        assert_eq!(t8.0[29], 0xff);
        let t3 = Target::from_leading_zero_bits(3);
        assert_eq!(t3.0[30], 0x1f);
        assert!(t3 > t8 && Target::MAX > t3);
        assert!(!t8.is_met_by(&max));
        let mut small = zero;
        small[29] = 0xff; // 248 - 8 = 240 bits: bytes 30 and 31 do not count or are zero
        small[31] = 0xff;
        assert!(t8.is_met_by(&small));
        small[30] = 1;
        assert!(!t8.is_met_by(&small));
        assert_eq!(Target::from_leading_zero_bits(248).0, [0u8; 32]);
        assert!(Target::from_leading_zero_bits(248).is_met_by(&zero));
    }

    #[test]
    fn compact_roundtrip() {
        for bits in [MAX_BITS, 0x1a2b_3c4d, 0x0101_0000, 0x1802_aee8, 0x0312_3456, 0x0212_3400, 0x0112_0000] {
            let t = compact_to_target(bits);
            assert_eq!(target_to_compact(t), bits, "{bits:#x}");
        }
        assert_eq!(compact_to_target(MAX_BITS), U256::from_u64(0xffff).shift_left(8 * 26));
        assert_eq!(target_to_compact(U256::ONE), 0x0101_0000);
        assert_eq!(target_to_compact(U256::from_u64(0x80)), 0x0200_8000);
        assert_eq!(compact_to_target(0x0180_0000), U256::ZERO);
        // Non-canonical encodings decode to the same target as their canonical form.
        assert_eq!(compact_to_target(0x0300_1234), compact_to_target(0x0212_3400));
    }

    struct Run {
        anchor_height: u64,
        anchor_parent_time: i64,
        anchor_bits: u32,
        rows: Vec<(u64, i64, u32)>,
    }

    fn parse_run(text: &str) -> Run {
        let field = |key: &str| -> &str {
            let line = text.lines().find(|l| l.contains(key)).unwrap();
            line.split(':').nth(1).unwrap().trim()
        };
        let anchor_bits = u32::from_str_radix(field("anchor nBits").trim_start_matches("0x"), 16).unwrap();
        let rows = text
            .lines()
            .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
            .map(|l| {
                let p: Vec<&str> = l.split_whitespace().collect();
                (
                    p[1].parse().unwrap(),
                    p[2].parse().unwrap(),
                    u32::from_str_radix(p[3].trim_start_matches("0x"), 16).unwrap(),
                )
            })
            .collect();
        Run {
            anchor_height: field("anchor height").parse().unwrap(),
            anchor_parent_time: field("anchor parent time").parse().unwrap(),
            anchor_bits,
            rows,
        }
    }

    #[test]
    fn matches_bitcoin_cash_test_vectors() {
        let runs = [
            include_str!("../testdata/asert/run01"),
            include_str!("../testdata/asert/run02"),
            include_str!("../testdata/asert/run03"),
            include_str!("../testdata/asert/run04"),
            include_str!("../testdata/asert/run05"),
            include_str!("../testdata/asert/run06"),
            include_str!("../testdata/asert/run07"),
            include_str!("../testdata/asert/run08"),
            include_str!("../testdata/asert/run09"),
            include_str!("../testdata/asert/run10"),
            include_str!("../testdata/asert/run11"),
            include_str!("../testdata/asert/run12"),
        ];
        let mut checked = 0;
        for (i, text) in runs.iter().enumerate() {
            let run = parse_run(text);
            let asert = Asert {
                anchor_height: run.anchor_height,
                anchor_parent_time: run.anchor_parent_time,
                anchor_target: compact_to_target(run.anchor_bits),
                max_target: compact_to_target(MAX_BITS),
                half_life: HALF_LIFE,
                ideal_block_time: IDEAL_BLOCK_TIME,
            };
            for (height, time, want) in &run.rows {
                let got = target_to_compact(asert.next_target(*height, *time));
                assert_eq!(got, *want, "run{:02} height {height} time {time}: got {got:#x} want {want:#x}", i + 1);
                checked += 1;
            }
        }
        assert!(checked > 13_000, "only {checked} rows checked");
    }

    #[test]
    fn genesis_anchor_keeps_schedule() {
        let genesis_time = 1_700_000_000;
        let target = compact_to_target(0x1802_aee8);
        let asert = Asert::from_genesis(genesis_time, target, compact_to_target(MAX_BITS));
        // Exactly on schedule: constant target.
        for h in 0..10u64 {
            assert_eq!(asert.next_target(h, genesis_time + h as i64 * IDEAL_BLOCK_TIME), target, "height {h}");
        }
        // One half-life late doubles the target; one early halves it.
        assert_eq!(asert.next_target(0, genesis_time + HALF_LIFE), target.shift_left(1));
        assert_eq!(asert.next_target(0, genesis_time - HALF_LIFE), target.shift_right(1));
        // Faster blocks tighten, slower loosen.
        assert!(asert.next_target(1, genesis_time + 100) < target);
        assert!(asert.next_target(1, genesis_time + 5000) > target);
        // Clamps.
        assert_eq!(asert.next_target(0, genesis_time + 100 * HALF_LIFE), asert.max_target);
        assert_eq!(asert.next_target(0, genesis_time - 300 * HALF_LIFE), U256::ONE);
    }
}
