//! A 256-bit unsigned integer: what targets and accumulated work are
//! counted in. Four 64-bit limbs held in place; no operation allocates.

/// Little-endian 256-bit unsigned integer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct U256(pub [u64; 4]);

impl U256 {
    pub const ZERO: U256 = U256([0; 4]);
    pub const ONE: U256 = U256([1, 0, 0, 0]);
    pub const MAX: U256 = U256([u64::MAX; 4]);

    pub const fn from_u64(v: u64) -> U256 {
        U256([v, 0, 0, 0])
    }

    pub fn is_zero(&self) -> bool {
        self.0 == [0; 4]
    }

    pub fn to_le_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (chunk, limb) in out.chunks_exact_mut(8).zip(self.0) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        out
    }

    pub fn from_le_bytes(b: &[u8; 32]) -> U256 {
        let mut limbs = [0u64; 4];
        for (limb, chunk) in limbs.iter_mut().zip(b.chunks_exact(8)) {
            *limb = u64::from_le_bytes(chunk.try_into().unwrap());
        }
        U256(limbs)
    }

    /// Number of significant bits.
    pub fn bits(&self) -> u32 {
        for i in (0..4).rev() {
            if self.0[i] != 0 {
                return 64 * i as u32 + 64 - self.0[i].leading_zeros();
            }
        }
        0
    }

    #[allow(clippy::needless_range_loop)]
    pub fn shift_left(self, n: u32) -> U256 {
        if n >= 256 {
            return U256::ZERO;
        }
        let (words, bits) = ((n / 64) as usize, n % 64);
        let mut out = [0u64; 4];
        for i in (words..4).rev() {
            let lo = self.0[i - words] << bits;
            let hi = if bits > 0 && i > words { self.0[i - words - 1] >> (64 - bits) } else { 0 };
            out[i] = lo | hi;
        }
        U256(out)
    }

    #[allow(clippy::needless_range_loop)]
    pub fn shift_right(self, n: u32) -> U256 {
        if n >= 256 {
            return U256::ZERO;
        }
        let (words, bits) = ((n / 64) as usize, n % 64);
        let mut out = [0u64; 4];
        for i in 0..4 - words {
            let lo = self.0[i + words] >> bits;
            let hi = if bits > 0 && i + words + 1 < 4 { self.0[i + words + 1] << (64 - bits) } else { 0 };
            out[i] = lo | hi;
        }
        U256(out)
    }

    pub fn saturating_add(self, other: U256) -> U256 {
        let mut out = [0u64; 4];
        let mut carry = 0u64;
        for (o, (a, b)) in out.iter_mut().zip(self.0.into_iter().zip(other.0)) {
            let (s, c1) = a.overflowing_add(b);
            let (s, c2) = s.overflowing_add(carry);
            *o = s;
            carry = u64::from(c1) + u64::from(c2);
        }
        if carry > 0 { U256::MAX } else { U256(out) }
    }

    /// `self - other`, which must not go negative.
    pub fn checked_sub(self, other: U256) -> Option<U256> {
        let mut out = [0u64; 4];
        let mut borrow = 0u64;
        for (o, (a, b)) in out.iter_mut().zip(self.0.into_iter().zip(other.0)) {
            let (d, b1) = a.overflowing_sub(b);
            let (d, b2) = d.overflowing_sub(borrow);
            *o = d;
            borrow = u64::from(b1) + u64::from(b2);
        }
        if borrow > 0 { None } else { Some(U256(out)) }
    }

    pub fn bit(&self, i: u32) -> bool {
        (self.0[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }

    /// `self * m` as five limbs (no overflow possible).
    pub(crate) fn mul_u64_wide(self, m: u64) -> [u64; 5] {
        let mut out = [0u64; 5];
        let mut carry = 0u128;
        for (o, limb) in out.iter_mut().zip(self.0) {
            let t = limb as u128 * m as u128 + carry;
            *o = t as u64;
            carry = t >> 64;
        }
        out[4] = carry as u64;
        out
    }
}

/// `!self`: every bit the other way.
impl std::ops::Not for U256 {
    type Output = U256;

    fn not(self) -> U256 {
        U256(self.0.map(|l| !l))
    }
}

/// `self / divisor` by long division; `divisor` must be nonzero.
impl std::ops::Div for U256 {
    type Output = U256;

    fn div(self, divisor: U256) -> U256 {
        assert!(!divisor.is_zero(), "division by zero");
        let mut quotient = U256::ZERO;
        let mut rem = U256::ZERO;
        for i in (0..256).rev() {
            rem = rem.shift_left(1);
            if self.bit(i) {
                rem.0[0] |= 1;
            }
            if rem >= divisor {
                rem = rem.checked_sub(divisor).unwrap();
                quotient.0[(i / 64) as usize] |= 1 << (i % 64);
            }
        }
        quotient
    }
}

impl PartialOrd for U256 {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for U256 {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        for i in (0..4).rev() {
            match self.0[i].cmp(&other.0[i]) {
                core::cmp::Ordering::Equal => continue,
                o => return o,
            }
        }
        core::cmp::Ordering::Equal
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u256_basics() {
        let a = U256::from_u64(0x1234);
        assert_eq!(a.shift_left(8).0[0], 0x123400);
        assert_eq!(a.shift_left(64).0[1], 0x1234);
        assert_eq!(a.shift_left(64).shift_right(64), a);
        assert_eq!(a.shift_left(200).shift_right(200), a);
        assert_eq!(U256::ONE.shift_left(255).bits(), 256);
        assert_eq!(a.shift_left(255), U256::ZERO); // only bit 0 would survive, and it is clear
        assert_eq!(a.bits(), 13);
        assert_eq!(U256::ZERO.bits(), 0);
        assert!(U256::MAX > a);
        assert_eq!(U256::from_le_bytes(&a.shift_left(100).to_le_bytes()), a.shift_left(100));
        assert_eq!((a.shift_left(256), a.shift_right(256)), (U256::ZERO, U256::ZERO));
        assert_eq!((U256::default(), U256::ZERO.is_zero(), a.is_zero()), (U256::ZERO, true, false));
    }

    /// A value of up to 128 bits, as two limbs.
    fn wide(v: u128) -> U256 {
        U256([v as u64, (v >> 64) as u64, 0, 0])
    }

    /// Arithmetic agrees with `u128` where both hold the result, and
    /// keeps its promises at the edges: sums saturate, a difference that
    /// would be negative is none, dividing by zero panics.
    #[test]
    fn arithmetic_agrees_with_u128() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for round in 0..2000 {
            // Operands of every size up to 127 bits.
            let a = ((next() as u128) << 64 | next() as u128) >> (1 + round % 127);
            let b = ((next() as u128) << 64 | next() as u128) >> (1 + (round * 7) % 127);
            let (wa, wb) = (wide(a), wide(b));
            assert_eq!(wa.saturating_add(wb), wide(a + b));
            assert_eq!(wa.checked_sub(wb), a.checked_sub(b).map(wide));
            assert_eq!(wa.cmp(&wb), a.cmp(&b));
            assert_eq!(wa.partial_cmp(&wb), Some(a.cmp(&b)));
            assert_eq!(wa.bits(), 128 - a.leading_zeros());
            if let Some(quotient) = a.checked_div(b) {
                assert_eq!(wa / wb, wide(quotient));
            }
            let s = (round % 127) as u32;
            assert_eq!(wide(a >> s), wa.shift_right(s));
            assert_eq!(wa.bit(s), (a >> s) & 1 == 1);
            let m = next();
            let product = wa.mul_u64_wide(m);
            // a * m, by the two halves of a.
            let lo = (a as u64 as u128) * m as u128;
            let hi = (a >> 64) * m as u128 + (lo >> 64);
            assert_eq!(product, [lo as u64, hi as u64, (hi >> 64) as u64, 0, 0]);
        }
        // Across all four limbs: (x << n) / (1 << n) is x, and not is the complement.
        let big = U256([1, 2, 3, 4]);
        assert_eq!(big.shift_left(3) / U256::from_u64(8), big);
        assert_eq!(U256::MAX / U256::MAX, U256::ONE);
        assert_eq!(big / U256::MAX, U256::ZERO);
        assert_eq!(!!big, big);
        assert_eq!(big.saturating_add(!big), U256::MAX);
        assert_eq!(U256::MAX.saturating_add(U256::ONE), U256::MAX);
        assert_eq!(U256::MAX.checked_sub(big), Some(!big));
        assert_eq!(U256::ZERO.checked_sub(U256::ONE), None);
        assert_eq!(U256::MAX.mul_u64_wide(u64::MAX), [1, u64::MAX, u64::MAX, u64::MAX, u64::MAX - 1]);
        assert!(std::panic::catch_unwind(|| big / U256::ZERO).is_err());
        // The highest limb decides an order, then the next.
        assert!(U256([0, 0, 0, 1]) > U256([u64::MAX, u64::MAX, u64::MAX, 0]));
        assert!(U256([5, 1, 0, 0]) > U256([9, 0, 0, 0]));
    }
}
