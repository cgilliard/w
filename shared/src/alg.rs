//! The verifier's arithmetic, written once: over the field, to verify,
//! and over the values of the machine, to make a circuit that verifies.
//!
//! What a verifier computes is sums and products of what a proof holds
//! and of challenges. Written over [`Alg`], the same code runs on field
//! elements ([`F`]) and on the machine's values ([`crate::sym::Sym`]),
//! whose sums and products become rows as they are made.
//!
//! Here is what the verifier's code is written against, and the field's
//! side of it: the arithmetic ([`Alg`]), a proof's transcript
//! ([`Transcript`]), and the few things every part of a verifier
//! computes with them. The machine's side is [`crate::sym`], which is
//! above everything a verifier is made of; nothing here knows of it.

use crate::challenger::Challenger;
use crate::field::F;
use crate::hash::Digest;
use std::ops::{Add, Mul};

/// What a verifier's arithmetic is written over.
pub trait Alg: Clone + Add<Output = Self> + Mul<Output = Self> {
    /// The constant `c`, where `self` is.
    fn lift(&self, c: F) -> Self;

    /// That `self` is `other`: whether it is, for the field; for the
    /// machine an assertion, and true.
    fn is(&self, other: &Self) -> bool;

    /// `self`, to be used many times: for the machine, made a value now
    /// and not left a sum or a product for each use to make again.
    fn kept(self) -> Self {
        self
    }

    /// The inverse, if `self` is not zero: computed, for the field; for
    /// the machine a value the prover gives, asserted to be it.
    fn inv(&self) -> Option<Self>;
}

impl Alg for F {
    fn lift(&self, c: F) -> F {
        c
    }

    fn is(&self, other: &F) -> bool {
        self == other
    }

    fn inv(&self) -> Option<F> {
        (*self != F::ZERO).then(|| F::inv(*self))
    }
}

/// `eq(a, b)`: in characteristic two, the product of `1 + a_i + b_i`.
pub fn eq<A: Alg>(a: &[A], b: &[A]) -> A {
    eq_onto(a[0].lift(F::ONE), a, b)
}

/// `p eq(a, b)`: a row of the machine for each variable, the product so
/// far times the sum of the two, plus itself.
pub fn eq_onto<A: Alg>(p: A, a: &[A], b: &[A]) -> A {
    a.iter().zip(b).fold(p, |p, (x, y)| (x.clone() + y.clone()) * p.clone() + p)
}

/// `sum_x eq(a, x) eq(b, x + 1)`, the row after all ones being row zero:
/// the weights `eq(b, .)` moved back a row, at `a`.
pub fn successor<A: Alg>(a: &[A], b: &[A]) -> A {
    let n = a.len();
    let one = a[0].lift(F::ONE);
    // x and x + 1 agree above some bit t, where x has 0 and x + 1 has 1;
    // below it x is all ones and x + 1 all zeros.
    let mut above = vec![one.clone(); n + 1];
    for i in (0..n).rev() {
        above[i] = above[i + 1].clone() * (a[i].clone() + b[i].clone() + one.clone());
    }
    let mut below = one.clone();
    let mut sum = a[0].lift(F::ZERO);
    for t in 0..n {
        sum = below.clone() * ((a[t].clone() + one.clone()) * b[t].clone()) * above[t + 1].clone() + sum;
        below = below * (a[t].clone() * (b[t].clone() + one.clone()));
    }
    sum + below
}

/// `eq(z, b)` for every `b` of the cube.
pub fn eq_table<A: Alg>(z: &[A]) -> Vec<A> {
    let Some(first) = z.first() else {
        return Vec::new();
    };
    let one = first.lift(F::ONE);
    let mut e = vec![one.clone()];
    for zi in z {
        // Each entry splits in two: times `zi`, and what is left of it.
        let high: Vec<A> = e.iter().map(|a| a.clone() * zi.clone()).collect();
        let low: Vec<A> = e.iter().zip(&high).map(|(a, b)| a.clone() + b.clone()).collect();
        e = low.into_iter().chain(high).collect();
    }
    e
}

/// [`eq_table`], and for no variables the one entry, one, where `like`
/// is.
pub fn eq_table_like<A: Alg>(z: &[A], like: &A) -> Vec<A> {
    if z.is_empty() { vec![like.lift(F::ONE)] } else { eq_table(z) }
}

/// The powers of `mu`, `n` of them from one.
pub fn powers<A: Alg>(mu: &A, n: usize) -> Vec<A> {
    std::iter::successors(Some(mu.lift(F::ONE)), |p| Some(p.clone() * mu.clone())).take(n).collect()
}

/// A proof's transcript, to whoever verifies the proof: what goes into
/// it comes back as values of the verifier's arithmetic.
pub trait Transcript<A: Alg> {
    /// Field elements the prover sent.
    fn elements(&mut self, xs: &[F]) -> Vec<A>;

    /// A digest the prover sent or the statement names, as the two
    /// elements its bytes are.
    fn digest(&mut self, d: &Digest) -> [A; 2];

    /// Bytes of the statement that the arithmetic does not compute with.
    fn bytes(&mut self, bytes: &[u8]);

    /// A table's public values. A transcript whose arithmetic cannot
    /// know them as constants gives them back as the elements they are.
    fn public(&mut self, words: &[u32]) -> Option<Vec<A>>;

    fn challenge(&mut self) -> A;

    /// Takes in a nonce, and says whether it grinds `bits` bits.
    fn ground(&mut self, bits: usize, nonce: u64) -> bool;

    /// An index below `2^bits`, and the low 31 bits of the state it was
    /// read from, as an element.
    fn index(&mut self, bits: usize) -> (usize, A);

    /// Field elements the prover sent that anyone could work out: sent
    /// as they are even by a proof that hides what it is of.
    fn plain(&mut self, xs: &[F]) -> Vec<A> {
        self.elements(xs)
    }

    /// Whether the sum of the products `a b` of `terms`, each times its
    /// scale if it has one, and of `rest`, is `claim`. A proof that
    /// hides what it is of shows it otherwise ([`crate::hidden`]).
    fn product_sum(&mut self, terms: Vec<(Option<A>, A, A)>, rest: Option<A>, claim: &A) -> bool {
        let mut sum = rest;
        for (scale, a, b) in terms {
            let product = match scale {
                Some(scale) => a * b * scale,
                None => a * b,
            };
            sum = Some(match sum {
                Some(s) => product + s,
                None => product,
            });
        }
        sum.is_some_and(|s| s.is(claim))
    }

    /// `a b`.
    fn mul(&mut self, a: &A, b: &A) -> A {
        a.clone() * b.clone()
    }

    /// `a a`.
    fn square(&mut self, a: &A) -> A {
        a.clone() * a.clone()
    }

    /// [`switched`].
    fn switched(&mut self, twists: &[A], s: &[A]) -> A {
        switched(twists, s)
    }
}

/// What a proof of a compiled computation is of, as its public value:
/// the hash of the elements it names.
pub fn statement(elements: &[F]) -> Digest {
    crate::hash::hash_domain(crate::hash::DOM_STATEMENT, &crate::field::as_bytes(elements))
}

/// A digest as the two elements its bytes are.
pub fn halves(d: &Digest) -> [F; 2] {
    [F::from_bytes(d[..16].try_into().unwrap()), F::from_bytes(d[16..].try_into().unwrap())]
}

impl Transcript<F> for Challenger {
    fn elements(&mut self, xs: &[F]) -> Vec<F> {
        self.absorb_fs(xs);
        xs.to_vec()
    }

    fn digest(&mut self, d: &Digest) -> [F; 2] {
        self.absorb(d);
        halves(d)
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.absorb(bytes);
    }

    fn public(&mut self, words: &[u32]) -> Option<Vec<F>> {
        self.absorb(&words.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>());
        None
    }

    fn challenge(&mut self) -> F {
        Challenger::challenge(self)
    }

    fn ground(&mut self, bits: usize, nonce: u64) -> bool {
        self.check_grind(bits, nonce)
    }

    fn index(&mut self, bits: usize) -> (usize, F) {
        let (index, low) = self.index_and_low(bits);
        (index, F(low as u128))
    }
}

/// `x^(2^(128 - t))` for each `t`: the element whose power `2^t` is `x`.
pub(crate) fn roots_of_x() -> &'static [F; 128] {
    static ROOTS: std::sync::OnceLock<[F; 128]> = std::sync::OnceLock::new();
    ROOTS.get_or_init(|| {
        let mut up = [F(2); 129];
        for t in 1..129 {
            up[t] = up[t - 1].square();
        }
        std::array::from_fn(|t| up[(128 - t) % 128])
    })
}

/// What the 128 sums `s` of a ring switching come to under `phi`, read
/// the other way: the sum over the bit places `c` of `phi(x^c)` times
/// the element whose bit `b` is bit `c` of `s[b]`, which is the sum over
/// `b` of `x^b phi(s[b])`. `twists` are [`crate::argument::twists`] of `omega`.
///
/// Term `t` of that is `omega^t` times the sum over `b` of
/// `x^b s[b]^(2^t)`, which is the power `2^t` of the sum of
/// `k^b s[b]` for the `k` whose power `2^t` is `x`: a polynomial in a
/// constant, by Horner's rule. With `omega^t` brought inside the power
/// the same way, the whole is one chain of 128 squarings. So it costs a
/// product for each sum and each `t`, and no bit of an element is read:
/// what lets the arithmetic of a circuit do it.
pub fn switched<A: Alg>(twists: &[A], s: &[A]) -> A {
    let inner = |t: usize| {
        let k = s[0].lift(roots_of_x()[t]);
        let mut sum = s[s.len() - 1].clone();
        for sb in s[..s.len() - 1].iter().rev() {
            sum = sum * k.clone() + sb.clone();
        }
        sum * twists[t].clone()
    };
    let mut sum = inner(127);
    for t in (0..127).rev() {
        sum = sum.clone() * sum + inner(t);
    }
    sum
}

/// The rounds of a sumcheck under `eq(tau, .)`, from the claim `claim`:
/// the point and the last claim. A round's polynomial `h` is sent as its
/// constant and leading coefficients; the middle one is what makes
/// `(1 + tau) h(0) + tau h(1)` the claim before it. `None` if a `tau`
/// is zero: nothing is divided by then.
pub fn rounds<A: Alg, T: Transcript<A>>(tr: &mut T, polys: &[[F; 2]], tau: &[A], claim: A) -> Option<(Vec<A>, A)> {
    if polys.len() != tau.len() {
        return None;
    }
    let mut claim = claim;
    let mut point = Vec::with_capacity(tau.len());
    for (poly, tau_v) in polys.iter().zip(tau) {
        let h = tr.elements(poly);
        let [h0, h2] = [h[0].clone(), h[1].clone()];
        // h(1) is the claim less (1 + tau) h(0), over tau; the middle
        // coefficient is that less the other two.
        let h1 = (claim + h0.clone()) * tau_v.inv()? + h2.clone();
        let r = tr.challenge();
        claim = (h2 * r.clone() + h1) * r.clone() + h0;
        point.push(r);
    }
    Some((point, claim))
}
