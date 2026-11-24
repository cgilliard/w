//! Reading a circuit's constraints once for many proofs.
//!
//! A verifier needs, of each table, what the circuit's constraints come
//! to at the points its checks ended at ([`crate::structure`]): a sum
//! over the circuit's terms, which for a circuit of compressions is the
//! better part of what a circuit that verifies has to do. A circuit that
//! verifies several proofs of tables of one circuit would do it once for
//! each.
//!
//! The sum is the same thing every time but for the points. The terms
//! are a table `M` of zeros and ones, by the table a term's word is in,
//! its constraint, its operand, its word, and its shift and rotation;
//! what is wanted is the sum over the terms of `M` times a weight `G`
//! that is a product of a factor for each of those:
//!
//! ```text
//! V = sum_x M[x] G(x),   G(x) = src(x) eq(rho_k, k) lambda^o eq(rho_col, col) S[shift]
//! ```
//!
//! So whoever verifies takes each `V` on the prover's word
//! ([`Deferred`]) and, once all are in, checks them together: under the
//! powers of a challenge they are one sum over `x` of `M` times the
//! weights' sum, which a sumcheck brings to `M` at one random point,
//! read once ([`matrix_at`]), times each weight there, which costs
//! little. The challenges are the verifying circuit's own: hashed, by
//! its rows, from the points and the values.
//!
//! The field's own verifier reads each table directly
//! ([`crate::structure::Direct`]).

use crate::alg::{Alg, Transcript, eq, eq_table, eq_table_like};
use crate::circuit::{Circuit, Pre, Source, Term};
use crate::field::F;
use crate::structure::{Direct, LOG_W, Public, Reader, source_bit};
use crate::sym::{Hashed, Shared, Sym};

/// Bits of a term's place in each part of the table of terms: the
/// source, the constraint, the operand, the word, the shift.
fn shape(circuit: &Circuit) -> [usize; 5] {
    [2, circuit.log_constraints, 2, circuit.log_cols, 7]
}

fn source_index(from: Source) -> usize {
    match from {
        Source::Row => 0,
        Source::Prev => 1,
        Source::Program => 2,
        Source::Public => unreachable!("a public value is a constant"),
    }
}

/// Every term of the circuit's constraints, as its place in each part.
fn terms(circuit: &Circuit) -> Vec<[usize; 5]> {
    let mut out = Vec::with_capacity(circuit.terms());
    for (k, operands) in circuit.constraints.iter().enumerate() {
        for (o, expr) in operands.iter().enumerate() {
            for t in expr.terms.iter().filter(|t| t.from != Source::Public) {
                out.push([source_index(t.from), k, o, t.col as usize, t.pre as usize * 32 + t.rot as usize]);
            }
        }
    }
    out
}

/// The table of terms at the point `r`, its parts' variables one after
/// another: the reading, done once.
pub fn matrix_at<A: Alg>(circuit: &Circuit, r: &[A]) -> A {
    let shape = shape(circuit);
    let mut from = 0;
    let parts: Vec<Vec<A>> = (shape.iter())
        .map(|n| {
            from += n;
            eq_table(&r[from - n..from])
        })
        .collect();
    let [source, constraint, operand, word, shift] = [&parts[0], &parts[1], &parts[2], &parts[3], &parts[4]];
    // A source and a shift together, and with a word: kept, since a
    // word comes into many operands the same way.
    let turned: Vec<A> = (0..3 * 96).map(|i| (source[i / 96].clone() * shift[i % 96].clone()).kept()).collect();
    let mut kept: Vec<Option<A>> = vec![None; (3 * 96) << circuit.log_cols];
    let mut sum: Option<A> = None;
    for (k, operands) in circuit.constraints.iter().enumerate() {
        for (o, expr) in operands.iter().enumerate() {
            let mut part: Option<A> = None;
            for t in expr.terms.iter().filter(|t| t.from != Source::Public) {
                let turn = source_index(t.from) * 96 + t.pre as usize * 32 + t.rot as usize;
                let at = turn << circuit.log_cols | t.col as usize;
                if kept[at].is_none() {
                    kept[at] = Some((turned[turn].clone() * word[t.col as usize].clone()).kept());
                }
                let x = kept[at].clone().expect("made above");
                part = Some(match part {
                    Some(p) => p + x,
                    None => x,
                });
            }
            if let Some(part) = part {
                let x = part * (constraint[k].clone() * operand[o].clone());
                sum = Some(match sum {
                    Some(s) => x + s,
                    None => x,
                });
            }
        }
    }
    sum.expect("a circuit with a term")
}

/// What a claim's weight is made of: the table a term's word is in, the
/// constraints' point, the challenge that batches the operands, and the
/// point of the words' bits (the bit's place, then the word's).
#[derive(Clone)]
struct Weight<A> {
    source: usize,
    rho: Vec<A>,
    lambda: A,
    point: Vec<A>,
}

/// For each place `j` of an operand and each bit `b` of a word, the sum
/// of `shifts` over the shifts and rotations that bring bit `b` to
/// place `j`: with it a weight's part for the shift is a sum over
/// places and bits, not over shifts.
fn places<A: Alg>(shifts: &[A]) -> Vec<Vec<A>> {
    let cell = |j: usize, b: usize| {
        let mut sum: Option<A> = None;
        for (pre, at) in [(Pre::None, Some(b)), (Pre::Shl, (b < 31).then_some(b + 1)), (Pre::Shr, b.checked_sub(1))] {
            if let Some(at) = at {
                let rot = (at + 32 - j) % 32;
                debug_assert_eq!(source_bit(&Term { col: 0, pre, rot: rot as u8, from: Source::Row }, j), Some(b));
                let x = shifts[pre as usize * 32 + rot].clone();
                sum = Some(match sum {
                    Some(s) => s + x,
                    None => x,
                });
            }
        }
        sum.expect("a bit comes unshifted at least").kept()
    };
    (0..32).map(|j| (0..32).map(|b| cell(j, b)).collect()).collect()
}

impl<A: Alg> Weight<A> {
    /// The weight at the point `r` of the table of terms. `places` are
    /// [`places`] of `eq` at the point's part for the shift.
    fn at(&self, circuit: &Circuit, r: &[A], places: &[Vec<A>]) -> A {
        let [ns, nk, no, nc, _] = shape(circuit);
        let one = self.lambda.lift(F::ONE);
        let bit = |b: usize| self.lambda.lift(F((self.source >> b & 1) as u128));
        let mut w = eq(&r[..ns], &[bit(0), bit(1)]);
        w = crate::alg::eq_onto(w, &r[ns..ns + nk], &self.rho[LOG_W..]);
        // The operands' powers of lambda, as a table of four: 1, lambda,
        // its square, nothing.
        let (o0, o1) = (&r[ns + nk], &r[ns + nk + 1]);
        let low = (self.lambda.clone() + one.clone()) * o0.clone() + one.clone();
        let high = self.lambda.clone() * self.lambda.clone() * (o0.clone() + one.clone());
        w = w * ((low.clone() + high) * o1.clone() + low);
        // The word: a program's are the first sixteenth.
        let cols = &r[ns + nk + no..ns + nk + no + nc];
        let own = self.point.len() - LOG_W;
        w = crate::alg::eq_onto(w, &cols[..own], &self.point[LOG_W..]);
        for x in &cols[own..] {
            w = x.clone() * w.clone() + w;
        }
        // The shift: over an operand's places and a word's bits.
        let (places_at, bits_at) = (eq_table(&self.rho[..LOG_W]), eq_table(&self.point[..LOG_W]));
        let mut shift: Option<A> = None;
        for (ej, row) in places_at.iter().zip(places) {
            let mut inner = row[0].clone() * bits_at[0].clone();
            for (q, eb) in row.iter().zip(&bits_at).skip(1) {
                inner = q.clone() * eb.clone() + inner;
            }
            let x = inner * ej.clone();
            shift = Some(match shift {
                Some(s) => x + s,
                None => x,
            });
        }
        w * shift.expect("32 places")
    }
}

impl Weight<F> {
    /// The weight as its five tables, for the prover of the sumcheck.
    fn tables(&self, circuit: &Circuit) -> [Vec<F>; 5] {
        let [_, _, _, nc, _] = shape(circuit);
        let mut source = vec![F::ZERO; 4];
        source[self.source] = F::ONE;
        let mut word = eq_table_like(&self.point[LOG_W..], &F::ONE);
        word.resize(1 << nc, F::ZERO);
        let (ej, eb) = (eq_table(&self.rho[..LOG_W]), eq_table(&self.point[..LOG_W]));
        let mut shift = vec![F::ZERO; 128];
        for (s, x) in shift.iter_mut().enumerate().take(96) {
            let t =
                Term { col: 0, pre: [Pre::None, Pre::Shl, Pre::Shr][s / 32], rot: (s % 32) as u8, from: Source::Row };
            *x = (0..32).filter_map(|j| source_bit(&t, j).map(|b| ej[j] * eb[b])).fold(F::ZERO, |a, b| a + b);
        }
        let operand = vec![F::ONE, self.lambda, self.lambda * self.lambda, F::ZERO];
        [source, eq_table_like(&self.rho[LOG_W..], &F::ONE), operand, word, shift]
    }
}

/// The prover of the sumcheck over the table of terms: each term with
/// the weight of the variables bound so far, and each claim's five
/// tables, folded as their variables are bound.
struct Prover {
    terms: Vec<([usize; 5], F)>,
    claims: Vec<(F, [Vec<F>; 5])>,
    /// The part whose variables are being bound.
    part: usize,
}

impl Prover {
    /// The round's constant and leading coefficients.
    fn round(&self) -> (F, F) {
        let part = self.part;
        let (mut c0, mut c2) = (F::ZERO, F::ZERO);
        for (at, w) in &self.terms {
            let (mut low, mut slope) = (F::ZERO, F::ZERO);
            for (scale, tables) in &self.claims {
                let mut rest = *scale;
                for (p, table) in tables.iter().enumerate().filter(|(p, _)| *p != part) {
                    rest *= table[at[p]];
                }
                let pair = at[part] & !1;
                low += rest * tables[part][pair];
                slope += rest * (tables[part][pair] + tables[part][pair + 1]);
            }
            if at[part] & 1 == 0 {
                c0 += *w * low;
            }
            c2 += *w * slope;
        }
        (c0, c2)
    }

    fn bind(&mut self, r: F) {
        let part = self.part;
        for (at, w) in &mut self.terms {
            *w *= if at[part] & 1 == 1 { r } else { F::ONE + r };
            at[part] >>= 1;
        }
        for (_, tables) in &mut self.claims {
            let t = &mut tables[part];
            *t = t.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect();
        }
        if self.claims[0].1[part].len() == 1 {
            self.part += 1;
        }
    }
}

/// A claim: its weight as the machine's values and as the field's, and
/// the value said.
type Claim = (Weight<Sym>, Weight<F>, Sym);

/// A reader for a circuit that verifies: it takes each table's values
/// from the prover, and checks them all together when
/// [`Deferred::settle`] is called, which it must be.
pub struct Deferred {
    cx: Shared,
    /// For each circuit read (by where it lies), its claims: a weight
    /// as the machine's values and as the field's, and the value said.
    claims: Vec<(*const Circuit, Vec<Claim>)>,
}

impl Deferred {
    pub fn new(cx: &Shared) -> Deferred {
        Deferred { cx: cx.clone(), claims: Vec::new() }
    }

    /// Checks every value taken, a circuit at a time. `circuits` are
    /// the circuits read.
    pub fn settle(&mut self, circuits: &[&Circuit]) {
        let cx = self.cx.clone();
        for (which, claims) in std::mem::take(&mut self.claims) {
            let circuit = *circuits.iter().find(|c| std::ptr::eq(**c, which)).expect("a circuit that was read");
            // The challenges are of everything the claims are of.
            let mut tr = Hashed::new(b"tabminer reading", &cx);
            for (weight, native, value) in &claims {
                let said = [&native.rho[..], &[native.lambda], &native.point[..], &[value.value()]].concat();
                let absorbed = tr.elements(&said);
                let own = weight.rho.iter().chain([&weight.lambda]).chain(&weight.point).chain([value]);
                for (x, y) in absorbed.iter().zip(own) {
                    assert!(x.is(y));
                }
            }
            // (The claims are batched under the powers of one
            // challenge, which errs by as many in `2^128` as there are
            // claims: ground for what that is more than a round may.)
            tr.grind(crate::pcs::grinding(crate::pcs::SECURITY + 1, claims.len()));
            let scales = crate::alg::powers(&tr.challenge(), claims.len());
            let mut claim = claims[0].2.clone() * scales[0].clone();
            for ((.., value), scale) in claims.iter().zip(&scales).skip(1) {
                claim = value.clone() * scale.clone() + claim;
            }
            let mut prover = Prover {
                terms: terms(circuit).into_iter().map(|t| (t, F::ONE)).collect(),
                claims: claims.iter().zip(&scales).map(|((_, n, _), s)| (s.value(), n.tables(circuit))).collect(),
                part: 0,
            };
            let mut r = Vec::new();
            for _ in 0..shape(circuit).iter().sum::<usize>() {
                let (c0, c2) = prover.round();
                let c = tr.elements(&[c0, c2]);
                let x = tr.challenge();
                claim = ((claim + c[1].clone()) + c[1].clone() * x.clone()) * x.clone() + c[0].clone();
                prover.bind(x.value());
                r.push(x);
            }
            // The table at the point, read once, times the weights there.
            let [ns, nk, no, nc, _] = shape(circuit);
            let places = places(&eq_table(&r[ns + nk + no + nc..])[..96]);
            let mut weights = claims[0].0.at(circuit, &r, &places) * scales[0].clone();
            for ((weight, ..), scale) in claims.iter().zip(&scales).skip(1) {
                weights = weight.at(circuit, &r, &places) * scale.clone() + weights;
            }
            assert!((matrix_at(circuit, &r) * weights).is(&claim));
        }
    }
}

impl Reader<Sym> for Deferred {
    fn constraints(
        &mut self,
        circuit: &Circuit,
        public: &Public<Sym>,
        rho: &[Sym],
        lambda: &Sym,
        rho_e: &[Sym],
        rho_p: &[Sym],
    ) -> [Option<Sym>; 3] {
        // What the values are, by the field; then they are the prover's
        // to say, and claims to settle.
        let values = |xs: &[Sym]| xs.iter().map(Sym::value).collect::<Vec<F>>();
        let known = Public { words: public.words, elements: None };
        let (n_rho, n_e, n_p) = (values(rho), values(rho_e), values(rho_p));
        let found = Direct.constraints(circuit, &known, &n_rho, &lambda.value(), &n_e, &n_p);
        let at = match self.claims.iter().position(|(c, _)| std::ptr::eq(*c, circuit)) {
            Some(at) => at,
            None => {
                self.claims.push((circuit, Vec::new()));
                self.claims.len() - 1
            }
        };
        let mut said: [Option<Sym>; 3] = [None, None, None];
        for (source, value) in found.into_iter().enumerate() {
            let Some(value) = value else { continue };
            let value = self.cx.input(value);
            let (point, n_point) = if source == 2 { (rho_p, &n_p) } else { (rho_e, &n_e) };
            let weight = Weight { source, rho: rho.to_vec(), lambda: lambda.clone(), point: point.to_vec() };
            let native = Weight { source, rho: n_rho.clone(), lambda: lambda.value(), point: n_point.clone() };
            self.claims[at].1.push((weight, native, value.clone()));
            said[source] = Some(value);
        }
        said
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;
    use crate::{machine, recursion};

    fn weight(circuit: &Circuit, source: usize, rng: &mut Rng) -> Weight<F> {
        let cols = circuit.log_cols - if source == 2 { crate::circuit::LOG_PROGRAM_SHARE } else { 0 };
        Weight { source, rho: rng.fs(LOG_W + circuit.log_constraints), lambda: rng.f(), point: rng.fs(LOG_W + cols) }
    }

    #[test]
    fn a_reading_is_the_table_of_terms_under_its_weight() {
        // What the direct reader finds is the sum over the terms of the
        // weight's five tables; and the weight at a point is the tables'
        // product there.
        let mut rng = Rng(31);
        for circuit in [machine::circuit(), recursion::circuit()] {
            let (rho, lambda) = (rng.fs(LOG_W + circuit.log_constraints), rng.f());
            let (rho_e, rho_p) = (
                rng.fs(LOG_W + circuit.log_cols),
                rng.fs(LOG_W + circuit.log_cols - crate::circuit::LOG_PROGRAM_SHARE),
            );
            let none = Public { words: &[0; 8], elements: None };
            let found = Direct.constraints(&circuit, &none, &rho, &lambda, &rho_e, &rho_p);
            let all = terms(&circuit);
            let r = rng.fs(shape(&circuit).iter().sum());
            let places = places(&eq_table(&r[r.len() - 7..])[..96]);
            for (source, value) in found.into_iter().enumerate() {
                let point = if source == 2 { &rho_p } else { &rho_e };
                let w = Weight { source, rho: rho.clone(), lambda, point: point.clone() };
                let tables = w.tables(&circuit);
                let sum =
                    all.iter().fold(F::ZERO, |s, at| s + (0..5).map(|p| tables[p][at[p]]).fold(F::ONE, |a, b| a * b));
                assert_eq!(sum, value.unwrap_or(F::ZERO), "source {source}");
                let mut from = 0;
                let product = (0..5).fold(F::ONE, |p, part| {
                    let n = shape(&circuit)[part];
                    from += n;
                    p * crate::pcs::evaluate(&tables[part], &r[from - n..from])
                });
                assert_eq!(w.at(&circuit, &r, &places), product, "source {source}");
            }
            // The table of terms at a point: each term's `eq` there.
            let direct = all.iter().fold(F::ZERO, |s, at| {
                let mut from = 0;
                let one = (0..5).fold(F::ONE, |p, part| {
                    let n = shape(&circuit)[part];
                    from += n;
                    p * eq_table(&r[from - n..from])[at[part]]
                });
                s + one
            });
            assert_eq!(matrix_at(&circuit, &r), direct);
        }
        let _ = weight;
    }

    #[test]
    fn the_sumcheck_s_rounds_sum_to_the_claims() {
        let mut rng = Rng(32);
        let circuit = machine::circuit();
        let weights: Vec<Weight<F>> = (0..4).map(|i| weight(&circuit, i % 3, &mut rng)).collect();
        let scales = rng.fs(4);
        let all = terms(&circuit);
        let value = |w: &Weight<F>| {
            let t = w.tables(&circuit);
            all.iter().fold(F::ZERO, |s, at| s + (0..5).map(|p| t[p][at[p]]).fold(F::ONE, |a, b| a * b))
        };
        let mut claim = weights.iter().zip(&scales).fold(F::ZERO, |s, (w, c)| s + *c * value(w));
        let mut prover = Prover {
            terms: all.iter().map(|t| (*t, F::ONE)).collect(),
            claims: weights.iter().zip(&scales).map(|(w, s)| (*s, w.tables(&circuit))).collect(),
            part: 0,
        };
        let mut r = Vec::new();
        for _ in 0..shape(&circuit).iter().sum::<usize>() {
            let (c0, c2) = prover.round();
            let x = rng.f();
            claim = c0 + x * ((claim + c2) + c2 * x);
            prover.bind(x);
            r.push(x);
        }
        let places = places(&eq_table(&r[r.len() - 7..])[..96]);
        let at = weights.iter().zip(&scales).fold(F::ZERO, |s, (w, c)| s + *c * w.at(&circuit, &r, &places));
        assert_eq!(claim, matrix_at(&circuit, &r) * at);
    }
}
