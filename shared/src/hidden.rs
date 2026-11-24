//! Proofs that hide what they are of: what turns the argument of
//! [`crate::argument`] into one whose proofs say nothing of the
//! witness beyond the statement.
//!
//! # What a proof would give away
//!
//! Everything a prover sends after its commitment is a function of the
//! witness: each sumcheck's rounds, the operands at a point, the bus's
//! products, the 128 sums of the ring switching, and in the opening the
//! rounds, the last value and the leaves the queries open. Here each is
//! hidden, as follows; `docs/ZK.md` has the argument at length.
//!
//! # Pads
//!
//! Beside the witness the prover commits to a polynomial of random
//! elements ([`crate::pcs::commit_blind`]). Some of them are **pads**,
//! each used once.
//!
//! Every element the prover sends is sent with a pad added, so what is
//! sent is uniform whatever the witness. The verifier then holds each
//! value not as an element but as what was sent plus a pad it does not
//! know: an affine form over the pads ([`Masked`]). Its arithmetic is
//! the same generic code ([`crate::alg::Alg`]); sums and products by
//! what it knows keep a form a form. What it would check, `a = b`,
//! becomes an **equation** over the pads, kept for later. A challenge
//! batches the equations, with what the ring switching leaves the
//! opening to show, into one sum: of the witness's polynomial under the
//! ring switching's weights and of the pads' under what the equations
//! make theirs. The opening shows that sum.
//!
//! The pads are not in the witness, though it has room no constraint
//! reads. A pad there would be bits of a table too, and the table's own
//! sums (the ring switching's, for one) are sums over all its bits:
//! the pad would be part of the very values pads are there to hide,
//! and what is sent would no longer be uniform for certain.
//!
//! # Products
//!
//! The few checks that multiply two values the verifier does not know
//! (a zerocheck's `a b + c`, a grand product's children, the bus's
//! products over the tables, the squarings of the ring switching) are
//! not affine. For `sum s_t a_t b_t = c`, with pads `alpha_t`,
//! `beta_t` and a committed `gamma_t` (their product, if the prover is
//! honest): the prover sends the cross terms
//! `sum s_t (a_t beta_t + b_t alpha_t)` under a pad, a challenge `e` is
//! drawn, and the prover sends `e a_t + alpha_t` and `e b_t + beta_t`
//! in the clear, uniform for their pads. The product of the two is a
//! polynomial in `e` whose leading coefficient is `a_t b_t`, so
//!
//! ```text
//! e^2 c + e cross + sum s_t gamma_t = sum s_t (e a_t + alpha_t)(e b_t + beta_t)
//! ```
//!
//! is an equation over the pads that holds for a random `e` only if
//! `sum s_t a_t b_t = c`, whatever the prover committed as `gamma_t`:
//! everything in it was fixed before `e`. In characteristic two a
//! square needs no cross term. One `e` serves every product of a proof,
//! drawn when all are known ([`Padded::settle`]).
//!
//! # The opening
//!
//! [`crate::pcs`] says what it needs, and these are in the witness's
//! polynomial, since it is that polynomial's own rounds and leaves
//! they hide: in the last word of the first table's rows, which no
//! constraint reads. They add to nothing that is sent, so that they are
//! bits of a table does no harm. The rounds before the blinding
//! polynomial joins are hidden by 32 random elements that are two
//! leaves' places in the polynomial, four of which the sum weighs by a
//! challenge (the **corners**: the prover says their sum first). The
//! leaves the queries open are hidden by the rest of that word, all of
//! it random ([`Places::good`]). The pads' own polynomial begins with
//! random elements that are no pads, more than there are queries: its
//! entries the queries open, and its last value, are uniform for them.
//!
//! The opening is of the sum, and then of every polynomial at the
//! point the sum's challenges are ([`crate::pcs::open_weighted`]).
//! The second says five things more of the witness's polynomial before
//! a random one joins it: its value at the point, and a coefficient
//! of each of four rounds. The same 32 elements hide those too, with
//! the nine of the sum's first rounds and the leaves
//! (`the_corners_and_the_cover_hide_together`). After those rounds a
//! second random polynomial joins, of its own: the first has hidden
//! the sum's rounds, and its value at the point is sent.

use crate::alg::{Alg, Transcript};
use crate::challenger::Challenger;
use crate::circuit::Circuit;
use crate::field::F;
use crate::hash::Digest;
use crate::structure::{LOG_PACK, LOG_W, Layout, Public, Reader};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::{Add, Mul};
use std::rc::Rc;

/// The corners: of the 32 random elements that are two leaves' places
/// in the witness's polynomial (a last word of the first table), those
/// the opening's sum weighs to hide its first rounds. Two of each
/// leaf's place, not the same two.
pub const WEIGHED: [usize; 4] = [0, 15, 19, 28];
/// The bit that says a pad is of a triple.
const TRIPLE: u32 = 1 << 31;
/// A triple's pads: `alpha`, `beta`, their product, and `alpha` squared.
const FIELDS: u32 = 4;
/// Triples a proof may use.
const TRIPLES: usize = 1 << 10;

/// Where what hides the opening lies in the witness's polynomial: the
/// last word of the first table's rows. Its last group of 128 rows
/// holds the corners; the others hide the leaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Places {
    /// The first table's words a row, as variables, and its groups of
    /// 128 rows.
    pub log_cols: usize,
    pub groups: usize,
}

impl Places {
    /// For tables of these circuits and rows: `None` if the first has
    /// no word to spare, or one group of rows only.
    pub fn of<'a>(mut tables: impl Iterator<Item = (&'a Circuit, usize)>) -> Option<Places> {
        let (circuit, rows) = tables.next()?;
        let groups = rows >> LOG_PACK;
        (circuit.cols < 1 << circuit.log_cols && groups > 1).then_some(Places { log_cols: circuit.log_cols, groups })
    }

    /// Groups of the first table's rows whose last word hides leaves.
    pub fn cover(&self) -> usize {
        self.groups - 1
    }

    /// The element that is bit `bit` of the last word of group `group`.
    pub fn at(&self, layout: &Layout, group: usize, bit: usize) -> usize {
        layout.offset[0] + ((group << self.log_cols | ((1 << self.log_cols) - 1)) << LOG_W | bit)
    }

    /// The element that is the last group's bit `i`: the corners are
    /// among these.
    pub fn corner(&self, layout: &Layout, i: usize) -> usize {
        self.at(layout, self.groups - 1, i)
    }

    /// The weighed corners' part of the opening's weights at its
    /// challenges `r`: `chi` on each.
    pub fn corners_at<A: Alg>(&self, layout: &Layout, r: &[A], chi: &A) -> A {
        // The last word of the last group: every variable above a
        // word's bits is one, up to the table's own.
        let mut scale = layout.weight(0, r) * chi.clone();
        for x in &r[LOG_W..layout.m[0]] {
            scale = scale * x.clone();
        }
        let eq_bit = crate::alg::eq_table(&r[..LOG_W]);
        let bits = WEIGHED.iter().map(|i| eq_bit[*i].clone()).reduce(|s, x| x + s).expect("corners");
        bits * scale
    }

    /// Whether the leaves `indices` of the first codeword, of
    /// `2^step` elements each, are hidden by the first table's last
    /// word.
    ///
    /// A leaf's elements are the values, at one point of the codeword
    /// folded `step` times, of `2^step` polynomials: those of the
    /// coefficients that are the same modulo `2^step`. The last word's
    /// 32 bits are the top coefficients of each group of
    /// `C = 32 2^log_cols`; they give each of those polynomials, with
    /// `q` the point folded on to where a group is one coefficient, the
    /// part `X(y) (p_0(q) + ... + y^(n-1) p_(n-1)(q))` for `n = 32 /
    /// 2^step` and random `p` of degree below [`Places::cover`]. `X`,
    /// the basis polynomial of the first of those coefficients, is zero
    /// at the leaves below `C / 2^(step + 1)` and nowhere else. So the
    /// leaves' elements are uniform if none of them is that low, no more
    /// than `n` have the same `q`, and no more than `cover` different
    /// `q` are met. (The rule asks more than is needed, never less.)
    pub fn good(&self, step: usize, indices: &[usize]) -> bool {
        assert!(step <= LOG_W, "a leaf no wider than a word");
        let fold = LOG_W + self.log_cols - step;
        let mut leaves = indices.to_vec();
        leaves.sort_unstable();
        leaves.dedup();
        let mut by_point: BTreeMap<usize, usize> = BTreeMap::new();
        for leaf in &leaves {
            *by_point.entry(leaf >> fold).or_default() += 1;
        }
        leaves.iter().all(|l| *l >= 1 << (fold - 1))
            && by_point.values().all(|n| *n <= 1 << (LOG_W - step))
            && by_point.len() <= self.cover()
    }
}

/// Where the pads lie in their polynomial: after random elements that
/// are none, more than there are queries; the triples first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Room {
    pub prefix: usize,
    pub len: usize,
}

impl Room {
    /// For proofs under `params`: `None` if the polynomial is too small
    /// to hold a proof's pads.
    pub fn of(params: &crate::pcs::Params) -> Option<Room> {
        let steps = params.steps();
        let len = 1usize << params.m.checked_sub(steps[0]).filter(|_| steps.len() > 1)?;
        let prefix = (params.queries + 2).next_power_of_two();
        // Room for the triples and two thousand pads more at least.
        (len >= prefix + FIELDS as usize * TRIPLES + (1 << 11)).then_some(Room { prefix, len })
    }

    /// A pad's place, if there is one.
    pub fn place(&self, id: u32) -> Option<usize> {
        let triples = FIELDS as usize * TRIPLES;
        let at = if id & TRIPLE != 0 {
            Some((id & !TRIPLE) as usize).filter(|i| *i < triples)?
        } else {
            triples + id as usize
        };
        Some(self.prefix + at).filter(|at| *at < self.len)
    }

    /// What the pads' weights are at the challenges `r` of their
    /// polynomial's variables: `weights` by pad.
    pub fn weight_at<A: Alg>(&self, r: &[A], weights: &BTreeMap<u32, A>) -> Option<A> {
        let places: Vec<(usize, &A)> =
            weights.iter().map(|(id, w)| Some((self.place(*id)?, w))).collect::<Option<_>>()?;
        let most = places.iter().map(|(at, _)| at + 1).max()?;
        let low = most.next_power_of_two().trailing_zeros() as usize;
        let eq = crate::alg::eq_table_like(&r[..low], &r[0].lift(F::ONE));
        let mut sum: Option<A> = None;
        for (at, w) in places {
            let term = w.clone() * eq[at].clone();
            sum = Some(match sum {
                Some(s) => term + s,
                None => term,
            });
        }
        // Above the pads every variable is zero.
        let mut sum = sum?;
        for x in &r[low..] {
            sum = x.clone() * sum.clone() + sum;
        }
        Some(sum)
    }
}

/// Random elements from a seed: element `i` is the keyed hash of `i`.
pub struct Stream(pub [u8; 32]);

impl Stream {
    pub fn at(&self, i: u64) -> F {
        let h = crate::blake3::keyed_hash(&self.0, &i.to_le_bytes());
        F::from_bytes(h[..16].try_into().unwrap())
    }
}

/// What the verifier's checks of values it does not know come to: each
/// an affine form over the pads that must be zero.
type Form<A> = (A, Vec<(u32, A)>);

/// A value as a hiding proof's verifier holds it: what it knows, and
/// pads it does not, each times something it knows.
#[derive(Clone)]
pub struct Masked<A: Alg> {
    pub known: A,
    /// By pad, in order.
    pub pads: Vec<(u32, A)>,
    held: Rc<RefCell<Vec<Form<A>>>>,
}

impl<A: Alg> Masked<A> {
    /// A value with no pad, if this is one.
    pub fn open(self) -> Option<A> {
        self.pads.is_empty().then_some(self.known)
    }

    fn scaled(self, by: &A) -> Masked<A> {
        Masked {
            known: self.known * by.clone(),
            pads: self.pads.into_iter().map(|(id, w)| (id, w * by.clone())).collect(),
            held: self.held,
        }
    }
}

impl<A: Alg> Add for Masked<A> {
    type Output = Masked<A>;
    fn add(self, other: Masked<A>) -> Masked<A> {
        let mut pads = Vec::with_capacity(self.pads.len() + other.pads.len());
        let (mut a, mut b) = (self.pads.into_iter().peekable(), other.pads.into_iter().peekable());
        loop {
            let order = match (a.peek(), b.peek()) {
                (Some(x), Some(y)) => x.0.cmp(&y.0),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => break,
            };
            match order {
                std::cmp::Ordering::Less => pads.push(a.next().unwrap()),
                std::cmp::Ordering::Greater => pads.push(b.next().unwrap()),
                std::cmp::Ordering::Equal => {
                    let ((id, x), (_, y)) = (a.next().unwrap(), b.next().unwrap());
                    pads.push((id, x + y));
                }
            }
        }
        Masked { known: self.known + other.known, pads, held: self.held }
    }
}

impl<A: Alg> Mul for Masked<A> {
    type Output = Masked<A>;
    fn mul(self, other: Masked<A>) -> Masked<A> {
        if other.pads.is_empty() {
            self.scaled(&other.known)
        } else if self.pads.is_empty() {
            other.scaled(&self.known)
        } else {
            panic!("a product of two values the verifier does not know")
        }
    }
}

impl<A: Alg> Alg for Masked<A> {
    fn lift(&self, c: F) -> Masked<A> {
        Masked { known: self.known.lift(c), pads: Vec::new(), held: self.held.clone() }
    }

    /// Of two values it knows, whether they are the same; of others, an
    /// equation kept, and true.
    fn is(&self, other: &Masked<A>) -> bool {
        if self.pads.is_empty() && other.pads.is_empty() {
            return self.known.is(&other.known);
        }
        let sum = self.clone() + other.clone();
        self.held.borrow_mut().push((sum.known, sum.pads));
        true
    }

    fn kept(self) -> Masked<A> {
        Masked {
            known: self.known.kept(),
            pads: self.pads.into_iter().map(|(id, w)| (id, w.kept())).collect(),
            held: self.held,
        }
    }

    fn inv(&self) -> Option<Masked<A>> {
        assert!(self.pads.is_empty(), "the inverse of a value the verifier does not know");
        Some(Masked { known: self.known.inv()?, pads: Vec::new(), held: self.held.clone() })
    }
}

/// A product, or a square, to be shown once the challenge is drawn.
enum Job<A: Alg> {
    /// `sum s a b = claim`, the scale one where there is none.
    Product {
        terms: Vec<(Option<A>, Masked<A>, Masked<A>)>,
        claim: Masked<A>,
    },
    Square {
        of: Masked<A>,
        square: Masked<A>,
    },
}

/// What a hiding proof holds beside the argument's own parts: the
/// elements its products took, in the order they were sent; the nonces
/// ground before the challenge that batches the ring switching's sums,
/// the products' and the equations'; and the corners' sum.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Sent {
    pub extra: Vec<F>,
    pub nonces: [u64; 3],
    pub corners: F,
}

/// The transcript of a hiding proof, to its verifier: what the prover
/// sends comes back with a pad ([`Masked`]), and the products are
/// queued to be shown together.
pub struct Padded<'a, A: Alg, T: Transcript<A>> {
    tr: &'a mut T,
    held: Rc<RefCell<Vec<Form<A>>>>,
    sent: &'a Sent,
    at: usize,
    pads: u32,
    triples: u32,
    queue: Vec<Job<A>>,
    round_bits: usize,
    /// Whether the proof ran out of elements, or a nonce did not grind.
    failed: bool,
}

impl<'a, A: Alg, T: Transcript<A>> Padded<'a, A, T> {
    pub fn new(tr: &'a mut T, sent: &'a Sent, round_bits: usize) -> Padded<'a, A, T> {
        Padded {
            tr,
            held: Rc::new(RefCell::new(Vec::new())),
            sent,
            at: 0,
            pads: 0,
            triples: 0,
            queue: Vec::new(),
            round_bits,
            failed: false,
        }
    }

    fn known(&self, known: A) -> Masked<A> {
        Masked { known, pads: Vec::new(), held: self.held.clone() }
    }

    fn pad(&self, id: u32, like: &A) -> Masked<A> {
        Masked { known: like.lift(F::ZERO), pads: vec![(id, like.lift(F::ONE))], held: self.held.clone() }
    }

    fn next(&mut self) -> F {
        let x = self.sent.extra.get(self.at).copied();
        self.at += 1;
        self.failed |= x.is_none();
        x.unwrap_or(F::ZERO)
    }

    /// One of the proof's further elements, sent under a pad.
    fn hidden(&mut self) -> Masked<A> {
        let x = self.next();
        self.elements(&[x]).swap_remove(0)
    }

    /// One sent as it is.
    fn clear(&mut self) -> A {
        let x = self.next();
        self.tr.elements(&[x]).swap_remove(0)
    }

    fn triple(&mut self) -> u32 {
        self.triples += 1;
        TRIPLE | ((self.triples - 1) * FIELDS)
    }

    /// Shows every product queued, under one challenge. `None` if the
    /// proof has not what it takes.
    pub fn settle(&mut self) -> Option<()> {
        let queue = std::mem::take(&mut self.queue);
        let crosses: Vec<Option<Masked<A>>> =
            queue.iter().map(|job| matches!(job, Job::Product { .. }).then(|| self.hidden())).collect();
        let bits = crate::pcs::grinding(self.round_bits, 2 * queue.len());
        if !self.tr.ground(bits, self.sent.nonces[1]) {
            return None;
        }
        let e = self.tr.challenge();
        let e2 = (e.clone() * e.clone()).kept();
        for (job, cross) in queue.into_iter().zip(crosses) {
            match job {
                Job::Product { terms, claim } => {
                    let mut left = claim.scaled(&e2) + cross.expect("a product's cross terms").scaled(&e);
                    let mut right: Option<A> = None;
                    for (scale, a, b) in terms {
                        let id = self.triple();
                        let (za, zb) = (self.clear(), self.clear());
                        (a.scaled(&e) + self.pad(id, &e)).is(&self.known(za.clone()));
                        (b.scaled(&e) + self.pad(id + 1, &e)).is(&self.known(zb.clone()));
                        let (mut product, mut gamma) = (za * zb, self.pad(id + 2, &e));
                        if let Some(scale) = scale {
                            (product, gamma) = (product * scale.clone(), gamma.scaled(&scale));
                        }
                        left = left + gamma;
                        right = Some(match right {
                            Some(r) => product + r,
                            None => product,
                        });
                    }
                    left.is(&self.known(right.expect("a product")));
                }
                Job::Square { of, square } => {
                    let id = self.triple();
                    let z = self.clear();
                    (of.scaled(&e) + self.pad(id, &e)).is(&self.known(z.clone()));
                    (square.scaled(&e2) + self.pad(id + 3, &e)).is(&self.known(z.clone() * z));
                }
            }
        }
        (!self.failed).then_some(())
    }

    /// The equations kept, if the proof's further elements were all
    /// taken and nothing failed.
    pub fn finish(self) -> Option<Vec<Form<A>>> {
        let done = !self.failed && self.at == self.sent.extra.len() && self.queue.is_empty();
        done.then(|| std::mem::take(&mut *self.held.borrow_mut()))
    }
}

impl<A: Alg, T: Transcript<A>> Transcript<Masked<A>> for Padded<'_, A, T> {
    fn elements(&mut self, xs: &[F]) -> Vec<Masked<A>> {
        let sent = self.tr.elements(xs);
        let masked = sent.into_iter().enumerate().map(|(i, x)| Masked {
            pads: vec![(self.pads + i as u32, x.lift(F::ONE))],
            known: x,
            held: self.held.clone(),
        });
        let masked = masked.collect();
        self.pads += xs.len() as u32;
        masked
    }

    fn plain(&mut self, xs: &[F]) -> Vec<Masked<A>> {
        self.tr.elements(xs).into_iter().map(|x| self.known(x)).collect()
    }

    fn digest(&mut self, d: &Digest) -> [Masked<A>; 2] {
        self.tr.digest(d).map(|x| self.known(x))
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.tr.bytes(bytes);
    }

    fn public(&mut self, words: &[u32]) -> Option<Vec<Masked<A>>> {
        Some(self.tr.public(words)?.into_iter().map(|x| self.known(x)).collect())
    }

    fn challenge(&mut self) -> Masked<A> {
        let c = self.tr.challenge();
        self.known(c)
    }

    fn ground(&mut self, bits: usize, nonce: u64) -> bool {
        self.tr.ground(bits, nonce)
    }

    fn index(&mut self, bits: usize) -> (usize, Masked<A>) {
        let (index, low) = self.tr.index(bits);
        (index, self.known(low))
    }

    fn product_sum(
        &mut self,
        terms: Vec<(Option<Masked<A>>, Masked<A>, Masked<A>)>,
        rest: Option<Masked<A>>,
        claim: &Masked<A>,
    ) -> bool {
        // What is left to show of the products of two it does not know.
        let mut claim = match rest {
            Some(rest) => claim.clone() + rest,
            None => claim.clone(),
        };
        let mut unknown = Vec::new();
        for (scale, a, b) in terms {
            if a.pads.is_empty() || b.pads.is_empty() {
                let product = a * b;
                claim = claim
                    + match scale {
                        Some(scale) => product * scale,
                        None => product,
                    };
            } else {
                let scale = scale.map(|s| s.open().expect("a scale the verifier knows"));
                unknown.push((scale, a, b));
            }
        }
        if unknown.is_empty() {
            return claim.is(&claim.lift(F::ZERO));
        }
        self.queue.push(Job::Product { terms: unknown, claim });
        true
    }

    fn mul(&mut self, a: &Masked<A>, b: &Masked<A>) -> Masked<A> {
        if a.pads.is_empty() || b.pads.is_empty() {
            return a.clone() * b.clone();
        }
        let product = self.hidden();
        self.queue.push(Job::Product { terms: vec![(None, a.clone(), b.clone())], claim: product.clone() });
        product
    }

    fn square(&mut self, a: &Masked<A>) -> Masked<A> {
        if a.pads.is_empty() {
            return a.clone() * a.clone();
        }
        let square = self.hidden();
        self.queue.push(Job::Square { of: a.clone(), square: square.clone() });
        square
    }

    /// [`crate::alg::switched`] of sums the verifier does not know.
    ///
    /// Each of its 128 terms is a sum of all the sums under constants,
    /// and what it squares is a sum of those: forms of every sum's pad,
    /// squared 127 times. So the prover sends the 128 terms, each under
    /// one pad; a challenge batches the 128 claims that they are what
    /// they should be into one equation; and the squarings are of forms
    /// of two pads.
    fn switched(&mut self, twists: &[Masked<A>], s: &[Masked<A>]) -> Masked<A> {
        if s.iter().all(|x| x.pads.is_empty()) {
            return crate::alg::switched(twists, s);
        }
        let terms: Vec<Masked<A>> = (0..128).map(|_| self.hidden()).collect();
        let bits = crate::pcs::grinding(self.round_bits, 128);
        self.failed |= !self.tr.ground(bits, self.sent.nonces[0]);
        let chi = self.tr.challenge();
        let roots = crate::alg::roots_of_x();
        // The claims' sum under the powers of the challenge: on one
        // side the terms; on the other each sum, times the sum over the
        // terms of its constant there.
        let mut power = chi.lift(F::ONE);
        let mut left: Option<Masked<A>> = None;
        let mut by_sum: Vec<Option<A>> = vec![None; s.len()];
        for (t, term) in terms.iter().enumerate() {
            let scaled = term.clone().scaled(&power);
            left = Some(match left {
                Some(l) => scaled + l,
                None => scaled,
            });
            let k = chi.lift(roots[t]);
            let twist = twists[t].clone().open().expect("a challenge's powers");
            let mut weight = (twist * power.clone()).kept();
            for (b, sum) in by_sum.iter_mut().enumerate() {
                *sum = Some(match sum.take() {
                    Some(s) => weight.clone() + s,
                    None => weight.clone(),
                });
                if b + 1 < s.len() {
                    weight = (weight * k.clone()).kept();
                }
            }
            power = (power * chi.clone()).kept();
        }
        let mut right: Option<Masked<A>> = None;
        for (sum, weight) in s.iter().zip(by_sum) {
            let scaled = sum.clone().scaled(&weight.expect("a term"));
            right = Some(match right {
                Some(r) => scaled + r,
                None => scaled,
            });
        }
        left.expect("terms").is(&right.expect("sums"));
        let mut sum = terms[127].clone();
        for t in (0..127).rev() {
            sum = self.square(&sum) + terms[t].clone();
        }
        sum
    }
}

/// A reader of circuits for a verifier of a hiding proof: what it is
/// asked of is all known to the verifier.
pub struct Unmasked<'a, R>(pub &'a mut R);

impl<A: Alg, R: Reader<A>> Reader<Masked<A>> for Unmasked<'_, R> {
    fn constraints(
        &mut self,
        circuit: &Circuit,
        public: &Public<Masked<A>>,
        rho: &[Masked<A>],
        lambda: &Masked<A>,
        rho_e: &[Masked<A>],
        rho_p: &[Masked<A>],
    ) -> [Option<Masked<A>>; 3] {
        let open = |xs: &[Masked<A>]| -> Vec<A> { xs.iter().map(|x| x.clone().open().expect("a challenge")).collect() };
        let elements = public.elements.as_ref().map(|e| open(e));
        let inner = Public { words: public.words, elements };
        let lambda_known = lambda.clone().open().expect("a challenge");
        let at = self.0.constraints(circuit, &inner, &open(rho), &lambda_known, &open(rho_e), &open(rho_p));
        at.map(|x| x.map(|known| Masked { known, pads: Vec::new(), held: lambda.held.clone() }))
    }
}

/// The pads, to the prover: what it adds to what it sends, and the
/// products it has to show.
pub struct Pads {
    /// The pads' polynomial from the first pad that is no triple's.
    sent_with: Vec<F>,
    triples: Vec<[F; FIELDS as usize]>,
    next: usize,
    next_triple: usize,
    queue: Vec<Work>,
    round_bits: usize,
    pub sent: Sent,
}

enum Work {
    Product(Vec<(F, F, F)>),
    Square(F),
}

impl Pads {
    /// Pads from `stream`, with the polynomial they are in: every
    /// element of it random, but a triple's product and square.
    pub fn new(room: &Room, stream: &Stream, round_bits: usize) -> (Pads, Vec<F>) {
        let mut all = vec![F::ZERO; room.len];
        crate::parallel::par_fill(&mut all, |i| stream.at(i as u64));
        let first = room.prefix;
        let triples: Vec<[F; 4]> = (all[first..first + FIELDS as usize * TRIPLES].chunks_exact_mut(4))
            .map(|t| {
                (t[2], t[3]) = (t[0] * t[1], t[0] * t[0]);
                [t[0], t[1], t[2], t[3]]
            })
            .collect();
        let sent_with = all[first + FIELDS as usize * TRIPLES..].to_vec();
        let pads =
            Pads { sent_with, triples, next: 0, next_triple: 0, queue: Vec::new(), round_bits, sent: Sent::default() };
        (pads, all)
    }

    /// The pads' weights as a table over their polynomial.
    pub fn weights(room: &Room, weights: &BTreeMap<u32, F>) -> Vec<F> {
        let mut table = vec![F::ZERO; room.len];
        for (id, w) in weights {
            table[room.place(*id).expect("a pad the prover used")] = *w;
        }
        table
    }

    /// `xs` as they are sent: each with the next pad.
    fn masked(&mut self, xs: &[F]) -> Vec<F> {
        assert!(self.next + xs.len() <= self.sent_with.len(), "more sent than there are pads");
        let sent = xs.iter().zip(&self.sent_with[self.next..]).map(|(x, pad)| *x + *pad).collect();
        self.next += xs.len();
        sent
    }

    fn hidden(&mut self, tr: &mut Challenger, x: F) {
        let sent = self.masked(&[x]);
        tr.absorb_fs(&sent);
        self.sent.extra.push(sent[0]);
    }

    fn clear(&mut self, tr: &mut Challenger, x: F) {
        tr.absorb_fs(&[x]);
        self.sent.extra.push(x);
    }

    /// `sum s a b`, of terms `(s, a, b)`, to be shown what the verifier
    /// holds it to be.
    pub fn product_sum(&mut self, terms: Vec<(F, F, F)>) {
        self.queue.push(Work::Product(terms));
    }

    /// `a b`, sent, and to be shown.
    pub fn mul(&mut self, tr: &mut Challenger, a: F, b: F) -> F {
        self.hidden(tr, a * b);
        self.queue.push(Work::Product(vec![(F::ONE, a, b)]));
        a * b
    }

    fn square(&mut self, tr: &mut Challenger, a: F) -> F {
        self.hidden(tr, a * a);
        self.queue.push(Work::Square(a));
        a * a
    }

    /// The prover's side of [`Padded::switched`].
    pub fn switched(&mut self, tr: &mut Challenger, twists: &[F], s: &[F]) -> F {
        let roots = crate::alg::roots_of_x();
        let terms: Vec<F> =
            (0..128).map(|t| s.iter().rev().fold(F::ZERO, |sum, sb| sum * roots[t] + *sb) * twists[t]).collect();
        for term in &terms {
            self.hidden(tr, *term);
        }
        self.sent.nonces[0] = tr.grind(crate::pcs::grinding(self.round_bits, 128));
        tr.challenge();
        let mut sum = terms[127];
        for t in (0..127).rev() {
            sum = self.square(tr, sum) + terms[t];
        }
        sum
    }

    /// The prover's side of [`Padded::settle`].
    pub fn settle(&mut self, tr: &mut Challenger) {
        let queue = std::mem::take(&mut self.queue);
        // Each product's triples, in the order the verifier takes them.
        let mut at = self.next_triple;
        let mut first = Vec::with_capacity(queue.len());
        for work in &queue {
            first.push(at);
            at += match work {
                Work::Product(terms) => terms.len(),
                Work::Square(_) => 1,
            };
        }
        assert!(at <= self.triples.len(), "more products than there are triples");
        self.next_triple = at;
        for (work, first) in queue.iter().zip(&first) {
            if let Work::Product(terms) = work {
                let cross = (terms.iter().zip(&self.triples[*first..]))
                    .fold(F::ZERO, |sum, ((s, a, b), [alpha, beta, ..])| sum + *s * (*a * *beta + *b * *alpha));
                self.hidden(tr, cross);
            }
        }
        self.sent.nonces[1] = tr.grind(crate::pcs::grinding(self.round_bits, 2 * queue.len()));
        let e = tr.challenge();
        for (work, first) in queue.iter().zip(&first) {
            match work {
                Work::Product(terms) => {
                    for (i, (_, a, b)) in terms.iter().enumerate() {
                        let [alpha, beta, ..] = self.triples[first + i];
                        self.clear(tr, e * *a + alpha);
                        self.clear(tr, e * *b + beta);
                    }
                }
                Work::Square(a) => {
                    let alpha = self.triples[*first][0];
                    self.clear(tr, e * *a + alpha);
                }
            }
        }
    }
}

/// `xs` as a prover sends them: under pads if it has any. Taken into
/// the transcript as sent.
pub fn send(tr: &mut Challenger, pads: &mut Option<Pads>, xs: &[F]) -> Vec<F> {
    let sent = match pads {
        Some(pads) => pads.masked(xs),
        None => xs.to_vec(),
    };
    tr.absorb_fs(&sent);
    sent
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::Domain;
    use crate::test_util::Rng;

    /// The rank of a matrix over the field, by elimination.
    fn rank(mut rows: Vec<Vec<F>>) -> usize {
        let (mut rank, width) = (0, rows[0].len());
        for col in 0..width {
            let Some(pivot) = (rank..rows.len()).find(|r| rows[*r][col] != F::ZERO) else {
                continue;
            };
            rows.swap(rank, pivot);
            let inv = rows[rank][col].inv();
            let (above, below) = rows.split_at_mut(rank + 1);
            for row in below {
                if row[col] != F::ZERO {
                    let scale = row[col] * inv;
                    for (x, pivot) in row[col..].iter_mut().zip(&above[rank][col..]) {
                        *x += scale * *pivot;
                    }
                }
            }
            rank += 1;
            if rank == rows.len() {
                break;
            }
        }
        rank
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn the_last_word_hides_the_leaves_it_is_said_to() {
        // A first table of four words a row and sixteen groups of rows,
        // alone in a polynomial of 2^11 elements, at rate a half: the
        // codeword of each element of its last word by itself, which is
        // that element's part in every entry of the codeword.
        let (log_cols, groups, step) = (2usize, 16usize, 4usize);
        let layout = Layout { m: vec![11], offset: vec![0], total: 11 };
        // (As if every group's last word were cover: seventeen groups.)
        let places = Places { log_cols, groups: groups + 1 };
        let domain = Domain::new(12, true);
        let mut codewords = Vec::new();
        for group in 0..groups {
            for bit in 0..32 {
                let mut message = vec![F::ZERO; 1 << 11];
                message[places.at(&layout, group, bit)] = F::ONE;
                codewords.push(domain.encode(&message));
            }
        }
        // The elements of the leaves opened are uniform if those of the
        // last word are, when the map from the one to the other is onto.
        let hidden = |leaves: &[usize]| {
            let rows: Vec<Vec<F>> = (leaves.iter())
                .flat_map(|l| (0..1 << step).map(move |i| (l << step) + i))
                .map(|at| codewords.iter().map(|c| c[at]).collect())
                .collect();
            rank(rows) == leaves.len() << step
        };
        let mut rng = Rng(70);
        let (mut good, mut bad) = (0, 0);
        for _ in 0..300 {
            let n = 1 + rng.next_u64() as usize % 20;
            let mut leaves: Vec<usize> = (0..n).map(|_| rng.next_u64() as usize % 256).collect();
            leaves.sort_unstable();
            leaves.dedup();
            // What is said to be hidden is; the rule asks more than is
            // needed, never less.
            let said = places.good(step, &leaves);
            assert!(hidden(&leaves) || !said, "{leaves:?}");
            good += said as usize;
            bad += !hidden(&leaves) as usize;
        }
        assert!(good > 20 && bad > 20, "{good} said hidden, {bad} not hidden");
        // Each way of not being: a leaf too low, three at one point,
        // more points than groups.
        assert!(hidden(&[4, 5, 100, 101, 255]) && places.good(step, &[4, 5, 100, 101, 255]));
        assert!(!hidden(&[3]) && !places.good(step, &[3]));
        assert!(!hidden(&[8, 9, 10]) && !places.good(step, &[8, 9, 10]));
        let spread: Vec<usize> = (1..18).map(|point| point * 8).collect();
        assert!(!places.good(step, &spread));
        assert!(hidden(&spread[1..]) && places.good(step, &spread[1..]));
        // More elements opened than the last word has: never.
        let many: Vec<usize> = (4..37).collect();
        assert!(!hidden(&many) && !places.good(step, &many));
    }

    #[test]
    fn the_corners_hide_the_first_rounds() {
        // The opening's first four rounds, of the 32 pads that are two
        // leaves' places: what the prover sends of them (the corners'
        // sum, then each round's two coefficients) as a map from the
        // pads. It is onto: nine values, uniform whatever else the
        // polynomial holds. With the corners' weights alone; and
        // whatever the sum's other weights on those pads are, since the
        // determinant that says so is a polynomial in the corners'
        // challenge whose leading coefficient is the one without them.
        let mut rng = Rng(72);
        for others in [false, true] {
            let chi = rng.f();
            let mut weights: Vec<F> = if others { rng.fs(32) } else { vec![F::ZERO; 32] };
            WEIGHED.iter().for_each(|i| weights[*i] += chi);
            let rs = rng.fs(4);
            let sent = |pads: &[F]| -> Vec<F> {
                let mut out = vec![F::ZERO; 9];
                out[0] = WEIGHED.iter().fold(F::ZERO, |s, i| s + pads[*i]);
                for (f, w) in pads.chunks_exact(16).zip(weights.chunks_exact(16)) {
                    let (mut f, mut w) = (f.to_vec(), w.to_vec());
                    for (i, r) in rs.iter().enumerate() {
                        let pairs = || f.chunks_exact(2).zip(w.chunks_exact(2));
                        out[1 + 2 * i] += pairs().fold(F::ZERO, |s, (f, w)| s + f[0] * w[0]);
                        out[2 + 2 * i] += pairs().fold(F::ZERO, |s, (f, w)| s + (f[0] + f[1]) * (w[0] + w[1]));
                        let fold =
                            |t: &[F]| -> Vec<F> { t.chunks_exact(2).map(|p| p[0] + *r * (p[0] + p[1])).collect() };
                        (f, w) = (fold(&f), fold(&w));
                    }
                }
                out
            };
            let unit = |i: usize| -> Vec<F> { (0..32).map(|j| if i == j { F::ONE } else { F::ZERO }).collect() };
            let columns: Vec<Vec<F>> = (0..32).map(|i| sent(&unit(i))).collect();
            let rows: Vec<Vec<F>> = (0..9).map(|v| columns.iter().map(|c| c[v]).collect()).collect();
            assert_eq!(rank(rows), 9, "other weights: {others}");
        }
        // One leaf's place would not do: what its pads sum to under the
        // weights is what the rounds say it is.
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn the_corners_and_the_cover_hide_together() {
        // The corners hide the first rounds whatever the cover is, and
        // the cover hides the leaves whatever the corners are; but the
        // rounds read the cover too, and the leaves the corners. What
        // is seen of both, as one map from the whole last word, is onto:
        // the corners' sum, eight coefficients, and sixteen elements a
        // leaf, all uniform together. And with them what the opening
        // at the point shows of the polynomial before a random one
        // joins it there: its value at the point, and a coefficient of
        // each of that opening's first rounds, which are of the
        // polynomial under `eq` at the point and by other challenges.
        // (One a round, not the two sent: under `eq` a round's
        // polynomial is `eq` in its variable times a line, so its
        // leading coefficient follows from its constant one and the
        // claim, for anyone.)
        let (log_cols, groups, step) = (2usize, 16usize, 4usize);
        let layout = Layout { m: vec![11], offset: vec![0], total: 11 };
        let places = Places { log_cols, groups };
        let domain = Domain::new(12, true);
        let mut rng = Rng(73);
        // Weights on everything, as the ring switching's are, and the
        // challenge's on the corners.
        let (chi, rs) = (rng.f(), rng.fs(4));
        let point: Vec<F> = rs.iter().copied().chain(rng.fs(7)).collect();
        let (at_point, again) = (crate::pcs::eq_table(&point), rng.fs(4));
        let mut weights = rng.fs(1 << 11);
        WEIGHED.iter().for_each(|i| weights[places.corner(&layout, *i)] += chi);
        let leaves = [9usize, 40, 41, 100, 130, 200, 255];
        assert!(places.good(step, &leaves));
        let seen = |at: usize| -> Vec<F> {
            let mut message = vec![F::ZERO; 1 << 11];
            message[at] = F::ONE;
            let corner = (0..32).position(|i| places.corner(&layout, i) == at);
            let mut out = vec![if corner.is_some_and(|i| WEIGHED.contains(&i)) { F::ONE } else { F::ZERO }];
            let (mut f, mut w) = (message.clone(), weights.clone());
            for r in &rs {
                let pairs = || f.chunks_exact(2).zip(w.chunks_exact(2));
                out.push(pairs().fold(F::ZERO, |s, (f, w)| s + f[0] * w[0]));
                out.push(pairs().fold(F::ZERO, |s, (f, w)| s + (f[0] + f[1]) * (w[0] + w[1])));
                let fold = |t: &[F]| -> Vec<F> { t.chunks_exact(2).map(|p| p[0] + *r * (p[0] + p[1])).collect() };
                (f, w) = (fold(&f), fold(&w));
            }
            out.push(at_point[at]);
            let (mut f, mut w) = (message.clone(), at_point.clone());
            for (i, r) in again.iter().enumerate() {
                let pairs = || f.chunks_exact(2).zip(w.chunks_exact(2));
                let claim = f.iter().zip(&w).fold(F::ZERO, |s, (f, w)| s + *f * *w);
                let c0 = pairs().fold(F::ZERO, |s, (f, w)| s + f[0] * w[0]);
                let c2 = pairs().fold(F::ZERO, |s, (f, w)| s + (f[0] + f[1]) * (w[0] + w[1]));
                assert_eq!(c2, c0 * (F::ONE + point[i]).inv() + (claim + c0) * point[i].inv());
                out.push(c0);
                let fold = |t: &[F]| -> Vec<F> { t.chunks_exact(2).map(|p| p[0] + *r * (p[0] + p[1])).collect() };
                (f, w) = (fold(&f), fold(&w));
            }
            let codeword = domain.encode(&message);
            out.extend(leaves.iter().flat_map(|l| codeword[l << step..(l + 1) << step].iter().copied()));
            out
        };
        let columns: Vec<Vec<F>> = (0..groups)
            .flat_map(|g| (0..32).map(move |bit| (g, bit)))
            .map(|(g, bit)| seen(places.at(&layout, g, bit)))
            .collect();
        let values = 14 + (leaves.len() << step);
        let rows: Vec<Vec<F>> = (0..values).map(|v| columns.iter().map(|c| c[v]).collect()).collect();
        assert_eq!(rank(rows), values);
    }

    #[test]
    fn a_form_over_pads_is_kept_by_sums_and_known_products() {
        // The verifier's arithmetic over what it does not know, against
        // the same with the pads known.
        let mut rng = Rng(71);
        let held = Rc::new(RefCell::new(Vec::new()));
        let pads: Vec<F> = rng.fs(6);
        let known = |x: F| Masked { known: x, pads: Vec::new(), held: held.clone() };
        let under =
            |x: F, id: u32| Masked { known: x + pads[id as usize], pads: vec![(id, F::ONE)], held: held.clone() };
        let value = |m: &Masked<F>| m.pads.iter().fold(m.known, |v, (id, w)| v + *w * pads[*id as usize]);
        let (x, y, z, c) = (rng.f(), rng.f(), rng.f(), rng.f());
        let (mx, my, mz) = (under(x, 0), under(y, 3), under(z, 5));
        assert_eq!((value(&mx), value(&my)), (x, y));
        let form = (mx.clone() + my.clone()) * known(c) + mz.clone() * known(c * c) + mx.clone();
        assert_eq!(value(&form), (x + y) * c + z * c * c + x);
        // A pad met twice is one term; in characteristic two it may go.
        assert_eq!((mx.clone() + mx.clone()).pads.len(), 1);
        assert_eq!(value(&(mx.clone() + mx.clone())), F::ZERO);
        // What would be checked is kept: an equation that holds of the
        // pads when the values are equal, and does not when they are not.
        assert!(form.is(&known((x + y) * c + z * c * c + x)) && mx.is(&my));
        let kept = held.borrow().clone();
        let at =
            |(known, terms): &(F, Vec<(u32, F)>)| terms.iter().fold(*known, |v, (id, w)| v + *w * pads[*id as usize]);
        assert_eq!(kept.len(), 2);
        assert_eq!((at(&kept[0]), at(&kept[1])), (F::ZERO, x + y));
        // Of two values it knows, it says.
        assert!(known(c).is(&known(c)) && !known(c).is(&known(c + F::ONE)));
        assert_eq!(held.borrow().len(), 2);
    }
}
