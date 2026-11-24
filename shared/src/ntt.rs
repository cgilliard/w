//! The additive NTT over the field (Lin, Chung and Han's novel
//! polynomial basis), and the Reed-Solomon code made with it.
//!
//! The domain is the span of `1, x, .., x^(k-1)`: the `2^k` elements
//! whose value as an integer is below `2^k`, so a codeword's index is the
//! point it is the value at. `W_i` is the polynomial that vanishes on the
//! span of the first `i` of them, and `Ŵ_i = W_i / W_i(x^i)`, which is
//! linear over GF(2), zero on that span and one at `x^i`. A message of
//! `2^m` coefficients `c` is the polynomial
//!
//! ```text
//! P = sum_j c[j] X_j,    X_j = product of Ŵ_i over the set bits i of j
//! ```
//!
//! and its codeword at rate `2^-R` is `P` on the whole domain, `k = m + R`.
//!
//! # The transform
//!
//! Layer `i` works on blocks of `2^(i+1)`: block `b` holds a polynomial
//! of `2^(i+1)` coefficients to be evaluated on the points whose bits
//! above `i` are `b`. `Ŵ_i` is the same value `t` on the half of them
//! with bit `i` clear and `t + 1` on the other, so
//!
//! ```text
//! u' = u + t v        v' = v + u'
//! ```
//!
//! with `u` the lower half of the coefficients and `v` the upper, leaves
//! each half a polynomial of half the size for its half of the points.
//! `t` is [`Domain::twiddle`]`(i, b)`. Layers run from the largest block
//! to the smallest.
//!
//! # Folding
//!
//! Undoing layer 0 of a codeword and mixing the pair with a challenge
//! `r`, as `(1 + r) u + r v`, gives a codeword of half the length: that
//! of the message `c'[b] = (1 + r) c[2b] + r c[2b+1]`, in the same basis
//! on the domain one layer up, whose layer 0 is this one's layer 1
//! ([`fold_pair`]; Diamond and Posen's FRI-Binius). Read as a multilinear
//! polynomial by its values on the cube, the message has had its lowest
//! variable set to `r`. After `m` folds every entry is that polynomial at
//! the challenges.

use crate::field::F;
use crate::parallel::{par_chunks_mut, par_chunks2_mut, par_fill};

/// Blocks of this many layers or fewer are transformed where they lie,
/// layer after layer: 4,096 elements, 64 KB.
const LEAF_LAYERS: usize = 12;

pub struct Domain {
    pub k: usize,
    /// `what[i][j] = Ŵ_i(x^j)`: zero for `j < i`, one for `j = i`.
    what: Vec<Vec<F>>,
    /// `W_i(x^i)`: what `W_i` is divided by to make `Ŵ_i`.
    norm: Vec<F>,
    /// Per layer, `Ŵ_i` of every sum of the low and of the high basis
    /// elements above `i`: a twiddle is one of each. Empty in a domain
    /// made for a verifier.
    lo: Vec<Vec<F>>,
    hi: Vec<Vec<F>>,
}

impl Domain {
    /// The domain of `2^k` points, with the prover's tables if `tables`.
    pub fn new(k: usize, tables: bool) -> Domain {
        assert!(k <= 64);
        // w[i][j] = W_i(x^j), by W_(i+1)(y) = W_i(y) (W_i(y) + W_i(x^i)).
        let mut w: Vec<F> = (0..k).map(|j| F(1 << j)).collect();
        let mut what = Vec::with_capacity(k);
        let mut norm = Vec::with_capacity(k);
        for i in 0..k {
            norm.push(w[i]);
            let inv = w[i].inv();
            what.push(w.iter().map(|x| *x * inv).collect::<Vec<F>>());
            let wi = w[i];
            for x in w.iter_mut() {
                *x = *x * (*x + wi);
            }
        }
        let (mut lo, mut hi) = (Vec::new(), Vec::new());
        if tables {
            for i in 0..k {
                let bits = k - 1 - i;
                let lo_bits = bits.div_ceil(2);
                let span = |from: usize, n: usize| {
                    let mut t = vec![F::ZERO; 1 << n];
                    for l in 0..n {
                        for x in 0..1 << l {
                            t[x | 1 << l] = t[x] + what[i][i + 1 + from + l];
                        }
                    }
                    t
                };
                lo.push(span(0, lo_bits));
                hi.push(span(lo_bits, bits - lo_bits));
            }
        }
        Domain { k, what, norm, lo, hi }
    }

    /// `Ŵ_i` at the point whose bits above `i` are `b`.
    #[inline(always)]
    pub fn twiddle(&self, i: usize, b: usize) -> F {
        let lo = &self.lo[i];
        lo[b & (lo.len() - 1)] + self.hi[i][b >> lo.len().trailing_zeros()]
    }

    /// `W_i(x^i)`.
    pub fn norm(&self, i: usize) -> F {
        self.norm[i]
    }

    /// `Ŵ_i(x^j)`.
    pub fn what(&self, i: usize, j: usize) -> F {
        self.what[i][j]
    }

    /// [`Domain::twiddle`] without the tables: a verifier's.
    pub fn twiddle_slow(&self, i: usize, mut b: usize) -> F {
        let mut t = F::ZERO;
        let mut l = i + 1;
        while b != 0 {
            if b & 1 == 1 {
                t += self.what[i][l];
            }
            b >>= 1;
            l += 1;
        }
        t
    }

    /// Layers `layer` down to 0 of the block `b` of that layer.
    fn transform(&self, data: &mut [F], layer: usize, b: usize, up: usize) {
        if layer < LEAF_LAYERS {
            for i in (0..=layer).rev() {
                let half = 1 << i;
                for (j, block) in data.chunks_exact_mut(2 * half).enumerate() {
                    let t = self.twiddle(i + up, (b << (layer - i)) | j);
                    let (lo, hi) = block.split_at_mut(half);
                    for (u, v) in lo.iter_mut().zip(hi) {
                        *u += t * *v;
                        *v += *u;
                    }
                }
            }
        } else {
            let t = self.twiddle(layer + up, b);
            let (lo, hi) = data.split_at_mut(1 << layer);
            for (u, v) in lo.iter_mut().zip(hi.iter_mut()) {
                *u += t * *v;
                *v += *u;
            }
            self.transform(lo, layer - 1, 2 * b, up);
            self.transform(hi, layer - 1, 2 * b + 1, up);
        }
    }

    /// The codeword of `msg`, `2^m` coefficients, on the whole domain.
    pub fn encode(&self, msg: &[F]) -> Vec<F> {
        self.encode_up(msg, 0)
    }

    /// The codeword of `msg` on the domain `up` layers up: the one a
    /// codeword of the whole domain is on once it has been folded `up`
    /// times, a `2^up`-th the size. A codeword of this one can be added
    /// to such a folded codeword, and folds on with it.
    pub fn encode_up(&self, msg: &[F], up: usize) -> Vec<F> {
        let k = self.k - up;
        let m = msg.len().trailing_zeros() as usize;
        assert!(msg.len() == 1 << m && m >= 1 && m <= k);
        // The layers above the message's leave copies of it, one a coset.
        let mut cw = vec![F::ZERO; 1 << k];
        par_chunks_mut(&mut cw, 1 << m.min(16), |i, c| {
            let at = (i << m.min(16)) & (msg.len() - 1);
            c.copy_from_slice(&msg[at..at + c.len()]);
        });
        // Whole passes down to blocks of which there are enough to share
        // out, then each block by itself.
        let task = (m - 1).min(k.saturating_sub(7).max(LEAF_LAYERS));
        for i in (task + 1..m).rev() {
            for (b, block) in cw.chunks_exact_mut(2 << i).enumerate() {
                let t = self.twiddle(i + up, b);
                let (lo, hi) = block.split_at_mut(1 << i);
                par_chunks2_mut(lo, hi, 1 << 14, |_, lo, hi| {
                    for (u, v) in lo.iter_mut().zip(hi) {
                        *u += t * *v;
                        *v += *u;
                    }
                });
            }
        }
        par_chunks_mut(&mut cw, 2 << task, |b, block| self.transform(block, task, b, up));
        cw
    }

    /// The codeword `cw` of a domain's layer `layer` folded with `r`: half
    /// the length, of the next layer.
    pub fn fold(&self, cw: &[F], layer: usize, r: F) -> Vec<F> {
        let mut out = vec![F::ZERO; cw.len() / 2];
        par_fill(&mut out, |b| fold_pair(cw[2 * b], cw[2 * b + 1], self.twiddle(layer, b), r));
        out
    }
}

/// One pair of a codeword, the values at a point with bit `i` clear and
/// at the same with it set, folded with `r`; `t` is the layer's twiddle
/// there.
#[inline(always)]
pub fn fold_pair(y0: F, y1: F, t: F, r: F) -> F {
    let v = y0 + y1;
    let u = y0 + t * v;
    u + r * (u + v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    /// `P` at the point `x`, term by term.
    fn evaluate(d: &Domain, msg: &[F], x: usize) -> F {
        let what_at: Vec<F> =
            (0..d.k).map(|i| (0..d.k).filter(|l| x >> l & 1 == 1).fold(F::ZERO, |a, l| a + d.what[i][l])).collect();
        let mut sum = F::ZERO;
        for (j, c) in msg.iter().enumerate() {
            let mut term = *c;
            for (i, w) in what_at.iter().enumerate() {
                if j >> i & 1 == 1 {
                    term *= *w;
                }
            }
            sum += term;
        }
        sum
    }

    #[test]
    fn a_codeword_is_the_polynomial_at_every_point() {
        let mut rng = Rng(3);
        for (m, k) in [(1, 3), (4, 6), (5, 5), (6, 9)] {
            let d = Domain::new(k, true);
            let msg = rng.fs(1 << m);
            let cw = d.encode(&msg);
            for (x, y) in cw.iter().enumerate() {
                assert_eq!(*y, evaluate(&d, &msg, x), "m {m} k {k} point {x}");
            }
        }
    }

    #[test]
    fn the_large_path_is_the_small_one() {
        // A message past the leaf size and the whole passes, against the
        // term-by-term value at a few points.
        let mut rng = Rng(4);
        let (m, k) = (15, 17);
        let d = Domain::new(k, true);
        let msg = rng.fs(1 << m);
        let cw = d.encode(&msg);
        for x in [0, 1, 4097, (1 << 15) + 5, (1 << 17) - 1, 77777] {
            assert_eq!(cw[x], evaluate(&d, &msg, x));
        }
    }

    #[test]
    fn a_folded_codeword_is_the_folded_message_s() {
        let mut rng = Rng(5);
        let (m, k) = (5, 8);
        let d = Domain::new(k, true);
        let mut msg = rng.fs(1 << m);
        let mut cw = d.encode(&msg);
        for layer in 0..m {
            let r = rng.f();
            cw = d.fold(&cw, layer, r);
            msg = msg.chunks(2).map(|p| p[0] + r * (p[0] + p[1])).collect();
            // The folded message's codeword on the domain `up` layers
            // up: the same sum, every Ŵ and every basis element taken
            // that many higher.
            let up = layer + 1;
            for (x, y) in cw.iter().enumerate() {
                let mut sum = F::ZERO;
                for (j, c) in msg.iter().enumerate() {
                    let mut term = *c;
                    for i in (0..m - up).filter(|i| j >> i & 1 == 1) {
                        term *=
                            (0..k - up).filter(|l| x >> l & 1 == 1).fold(F::ZERO, |a, l| a + d.what[i + up][l + up]);
                    }
                    sum += term;
                }
                assert_eq!(*y, sum, "after {up} folds, point {x}");
            }
        }
        assert!(cw.iter().all(|y| *y == msg[0]));
        assert_eq!(cw.len(), 1 << (k - m));
    }

    #[test]
    fn a_codeword_layers_up_is_the_folded_domain_s() {
        // A message encoded two layers up is what the same message's
        // codeword would be had it come there by folding: the folding of
        // a longer message whose folds leave it. Take the longer message
        // to be this one in its top variables; with challenges of zero a
        // fold keeps the even entries, so the folded message is this one.
        let mut rng = Rng(8);
        let (m, k, up) = (4, 9, 2);
        let d = Domain::new(k, true);
        let msg = rng.fs(1 << m);
        let mut long = vec![F::ZERO; 1 << (m + up)];
        for (i, x) in msg.iter().enumerate() {
            long[i << up] = *x;
        }
        let mut cw = d.encode(&long);
        for layer in 0..up {
            cw = d.fold(&cw, layer, F::ZERO);
        }
        assert_eq!(d.encode_up(&msg, up), cw);
        // And it folds on from there to the message at the challenges.
        let mut cw = d.encode_up(&msg, up);
        let mut folded = msg.clone();
        for layer in 0..m {
            let r = rng.f();
            cw = d.fold(&cw, layer + up, r);
            folded = folded.chunks(2).map(|p| p[0] + r * (p[0] + p[1])).collect();
        }
        assert!(cw.iter().all(|y| *y == folded[0]));
    }

    #[test]
    fn the_slow_twiddle_is_the_table_s() {
        let d = Domain::new(11, true);
        for i in 0..11 {
            for b in 0..1 << (10 - i) {
                assert_eq!(d.twiddle(i, b), d.twiddle_slow(i, b));
            }
        }
    }
}
