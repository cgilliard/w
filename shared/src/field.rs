//! The field: GF(2^128) as `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`.
//!
//! An element is the 128 coefficients of its polynomial, the lowest
//! degree in bit 0. Addition is XOR. Every challenge, every committed
//! value and every codeword entry is one of these: there is no smaller
//! field under it and no extension over it. Witnesses are bits, 128 to an
//! element.
//!
//! # Multiplication
//!
//! A carry-less product of 255 bits, then a reduction by the modulus.
//!
//! - **Portable** ([`mul_portable`]): the sixteen multiples of one
//!   operand by a nibble, then the other operand a nibble at a time.
//!   This is the meaning of the product on every target, and what the
//!   others are tested against.
//! - **x86-64 with `PCLMULQDQ`**: four carry-less 64-bit products and
//!   two more to reduce. Proving is a few billion of these, so this path
//!   is taken wherever the build's target has the instruction; the
//!   results are the portable ones bit for bit.
//!
//! Neither runs in constant time. Nothing secret is multiplied here: the
//! elements are a proof's public values and a prover's own witness.

use std::ops::{Add, AddAssign, Mul, MulAssign};

#[derive(Clone, Copy, PartialEq, Eq, Default, Debug, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct F(pub u128);

/// The modulus without its leading term: `x^7 + x^2 + x + 1`.
#[cfg(any(test, all(target_arch = "x86_64", target_feature = "pclmulqdq")))]
const LOW: u128 = 0x87;

impl F {
    pub const ZERO: F = F(0);
    pub const ONE: F = F(1);
    /// Bytes an element is written and hashed as.
    pub const BYTES: usize = 16;

    #[inline(always)]
    pub fn square(self) -> F {
        self * self
    }

    /// The inverse, `self^(2^128 - 2)`; zero for zero.
    pub fn inv(self) -> F {
        // 2^128 - 2 is 127 one bits above a zero bit.
        let mut acc = F::ONE;
        let mut sq = self.square();
        for _ in 1..128 {
            acc *= sq;
            sq = sq.square();
        }
        acc
    }

    pub fn from_bytes(b: &[u8; 16]) -> F {
        F(u128::from_le_bytes(*b))
    }

    pub fn to_bytes(self) -> [u8; 16] {
        self.0.to_le_bytes()
    }
}

/// The elements as the bytes they are hashed as: each little-endian, in
/// order.
#[cfg(target_endian = "little")]
pub fn as_bytes(s: &[F]) -> std::borrow::Cow<'_, [u8]> {
    // SAFETY: F is a transparent u128, which has no padding and no
    // invalid values; on a little-endian target its memory is its
    // little-endian bytes. The length is in bytes.
    std::borrow::Cow::Borrowed(unsafe { std::slice::from_raw_parts(s.as_ptr() as *const u8, std::mem::size_of_val(s)) })
}

/// The elements as the bytes they are hashed as: each little-endian, in
/// order.
#[cfg(not(target_endian = "little"))]
pub fn as_bytes(s: &[F]) -> std::borrow::Cow<'_, [u8]> {
    std::borrow::Cow::Owned(s.iter().flat_map(|x| x.to_bytes()).collect())
}

/// `hi x^128 + lo` reduced.
#[inline(always)]
fn reduce(lo: u128, hi: u128) -> u128 {
    // x^128 = x^7 + x^2 + x + 1: `hi` comes down four times shifted, and
    // the seven bits that pushes past the top come down again.
    let over = (hi >> 127) ^ (hi >> 126) ^ (hi >> 121);
    lo ^ hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7) ^ over ^ (over << 1) ^ (over << 2) ^ (over << 7)
}

/// The product on any target.
pub fn mul_portable(a: u128, b: u128) -> u128 {
    // a times each nibble, as 131 bits.
    let mut table = [(0u128, 0u128); 16];
    for i in 1..16usize {
        let (lo, hi) = table[i >> 1];
        let doubled = (lo << 1, hi << 1 | lo >> 127);
        table[i] = if i & 1 == 1 { (doubled.0 ^ a, doubled.1) } else { doubled };
    }
    let (mut lo, mut hi) = (0u128, 0u128);
    for k in (0..32).rev() {
        hi = hi << 4 | lo >> 124;
        lo <<= 4;
        let (tl, th) = table[(b >> (4 * k)) as usize & 15];
        lo ^= tl;
        hi ^= th;
    }
    reduce(lo, hi)
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
#[inline(always)]
fn mul(a: u128, b: u128) -> u128 {
    use std::arch::x86_64::*;
    // SAFETY: the target has PCLMULQDQ and SSE2 (the cfg above); u128 and
    // __m128i are both 16 plain bytes.
    unsafe {
        let a: __m128i = std::mem::transmute(a);
        let b: __m128i = std::mem::transmute(b);
        // The 256-bit product, `lo + hi x^128`.
        let lo = _mm_clmulepi64_si128(a, b, 0x00);
        let hi = _mm_clmulepi64_si128(a, b, 0x11);
        let mid = _mm_xor_si128(_mm_clmulepi64_si128(a, b, 0x10), _mm_clmulepi64_si128(a, b, 0x01));
        let lo = _mm_xor_si128(lo, _mm_slli_si128(mid, 8));
        let hi = _mm_xor_si128(hi, _mm_srli_si128(mid, 8));
        // The top half of `hi` comes down to bit 64, what that pushes
        // past the top into the low half of `hi`, which comes down to
        // bit 0.
        let r = _mm_set_epi64x(0, LOW as i64);
        let t = _mm_clmulepi64_si128(hi, r, 0x01);
        let lo = _mm_xor_si128(lo, _mm_slli_si128(t, 8));
        let hi = _mm_xor_si128(hi, _mm_srli_si128(t, 8));
        let t = _mm_clmulepi64_si128(hi, r, 0x00);
        std::mem::transmute(_mm_xor_si128(lo, t))
    }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq")))]
#[inline(always)]
fn mul(a: u128, b: u128) -> u128 {
    mul_portable(a, b)
}

impl Add for F {
    type Output = F;
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, o: F) -> F {
        F(self.0 ^ o.0)
    }
}

impl AddAssign for F {
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn add_assign(&mut self, o: F) {
        self.0 ^= o.0;
    }
}

impl Mul for F {
    type Output = F;
    #[inline(always)]
    fn mul(self, o: F) -> F {
        F(mul(self.0, o.0))
    }
}

impl MulAssign for F {
    #[inline(always)]
    fn mul_assign(&mut self, o: F) {
        *self = *self * o;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    /// The product by its definition: shift and add, a bit at a time,
    /// the modulus taken off whenever the top bit falls out.
    fn mul_by_bits(a: u128, b: u128) -> u128 {
        let (mut r, mut a) = (0u128, a);
        for i in 0..128 {
            if (b >> i) & 1 == 1 {
                r ^= a;
            }
            let carry = a >> 127;
            a = (a << 1) ^ (carry * LOW);
        }
        r
    }

    #[test]
    fn every_product_is_the_definition_s() {
        let mut rng = Rng(1);
        let mut cases: Vec<(F, F)> = (0..3000).map(|_| (rng.f(), rng.f())).collect();
        let edges = [0, 1, 2, LOW, 1 << 63, 1 << 64, 1 << 127, u128::MAX, u128::MAX - 1, 0xFFFF_FFFF_FFFF_FFFF];
        for a in edges {
            for b in edges {
                cases.push((F(a), F(b)));
            }
        }
        for (a, b) in cases {
            let expect = mul_by_bits(a.0, b.0);
            assert_eq!(mul_portable(a.0, b.0), expect, "portable {a:?} {b:?}");
            assert_eq!((a * b).0, expect, "this target's {a:?} {b:?}");
        }
    }

    #[test]
    fn it_is_a_field() {
        let mut rng = Rng(2);
        for _ in 0..50 {
            let (a, b, c) = (rng.f(), rng.f(), rng.f());
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * b, b * a);
            assert_eq!(a * a.inv(), F::ONE);
        }
        assert_eq!(F::ZERO.inv(), F::ZERO);
        // x * x^127 = x^128 = x^7 + x^2 + x + 1.
        assert_eq!(F(2) * F(1 << 127), F(LOW));
    }

    #[test]
    fn bytes_are_little_endian() {
        let x = F(0x0102_0304_0506_0708_090A_0B0C_0D0E_0F10);
        assert_eq!(x.to_bytes()[0], 0x10);
        assert_eq!(F::from_bytes(&x.to_bytes()), x);
        assert_eq!(&as_bytes(&[x, F::ONE])[..], [x.to_bytes(), F::ONE.to_bytes()].concat());
    }
}
