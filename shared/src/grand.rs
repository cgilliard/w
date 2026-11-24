//! Grand products: the proof that the product of a table of field
//! elements is what the prover says, with nothing committed (the GKR
//! protocol on a tree of products, as Thaler gives it).
//!
//! The table is the leaves of a binary tree; a node is the product of
//! its two children, which lie side by side in the level below. The
//! prover names the root. A claim about a level's values at a point `z`,
//! `V(z) = v`, is
//!
//! ```text
//! sum_x eq(z, x) V'(0, x) V'(1, x) = v
//! ```
//!
//! over the level below, `V'`, whose lowest variable says which child. A
//! sumcheck brings it to a point `r`; the prover sends `V'(0, r)` and
//! `V'(1, r)`, the verifier checks their product against the sumcheck's
//! last claim and takes a challenge `t` for the line between them: the
//! claim is now `V'(t, r)`, a level down. At the leaves it is a claim
//! about the table itself at a point, which is the caller's to settle.
//!
//! Several tables of one size go together: every level's claims are
//! batched with a challenge, and all share the points.
//!
//! # Soundness
//!
//! A sumcheck round here is of degree two under its `eq` and errs with
//! probability `2 / 2^128`; a level's batching and its line, `1 / 2^128`
//! and `1 / 2^128` each. Nothing is ground. There are `d (d - 1) / 2`
//! rounds for `2^d` leaves.

use crate::alg::{self, Alg, Transcript};
use crate::challenger::Challenger;
use crate::codec::{Reader, Writer};
use crate::field::F;
use crate::hidden::{Pads, send};
use crate::pcs::eq_table;

/// One level's part of a proof.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Level {
    /// The sumcheck's rounds: each polynomial's constant and leading
    /// coefficients.
    pub rounds: Vec<[F; 2]>,
    /// For each table, the level below at the point, by child.
    pub ends: Vec<[F; 2]>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Proof {
    /// Each table's product.
    pub products: Vec<F>,
    pub levels: Vec<Level>,
}

impl Proof {
    pub(crate) fn write(&self, w: &mut Writer) {
        w.fs(&self.products);
        w.len(self.levels.len());
        for level in &self.levels {
            w.fs(level.rounds.as_flattened());
            w.fs(level.ends.as_flattened());
        }
    }

    pub(crate) fn read(r: &mut Reader) -> Option<Proof> {
        let products = r.fs()?;
        let n = r.len(8)?;
        let mut levels = Vec::with_capacity(n);
        for _ in 0..n {
            let (rounds, ends) = (r.fs()?, r.fs()?);
            if rounds.len() % 2 != 0 || ends.len() % 2 != 0 {
                return None;
            }
            levels.push(Level {
                rounds: rounds.chunks_exact(2).map(|c| [c[0], c[1]]).collect(),
                ends: ends.chunks_exact(2).map(|c| [c[0], c[1]]).collect(),
            });
        }
        Some(Proof { products, levels })
    }
}

/// The powers of a challenge, one for each table.
fn powers(mu: F, n: usize) -> Vec<F> {
    std::iter::successors(Some(F::ONE), |p| Some(*p * mu)).take(n).collect()
}

/// The zerocheck's state between rounds, on either side.
pub(crate) struct Rounds {
    /// What the round polynomial must sum to, under the round's `eq`.
    pub(crate) claim: F,
    pub(crate) rs: Vec<F>,
    pub(crate) polys: Vec<[F; 2]>,
}

impl Rounds {
    /// The prover's end of a round: `h0 = h(0)` and `h2` its leading
    /// coefficient; `h(1)` is what the claim leaves it to be.
    pub(crate) fn prove(&mut self, tr: &mut Challenger, pads: &mut Option<Pads>, tau: F, h0: F, h2: F) -> F {
        let h_one = (self.claim + (F::ONE + tau) * h0) * tau.inv();
        let [h0, h1, h2] = [h0, h_one + h0 + h2, h2];
        let sent = send(tr, pads, &[h0, h2]);
        self.polys.push([sent[0], sent[1]]);
        let r = tr.challenge();
        self.claim = h0 + r * (h1 + r * h2);
        self.rs.push(r);
        r
    }
}

/// The proof of the products of `tables`, each of `2^d` elements, with
/// the point the leaves are left at (lowest variable first) and each
/// table's value there, and the products as they are. A proof that
/// hides what it is of sends everything under `pads`.
pub fn prove(tables: Vec<Vec<F>>, tr: &mut Challenger, pads: &mut Option<Pads>) -> (Proof, Vec<F>, Vec<F>, Vec<F>) {
    let d = tables[0].len().trailing_zeros() as usize;
    assert!(tables.iter().all(|t| t.len() == 1 << d));
    // Every level of every tree, the leaves last.
    let trees: Vec<Vec<Vec<F>>> = tables
        .into_iter()
        .map(|leaves| {
            let mut levels = vec![leaves];
            while levels.last().unwrap().len() > 1 {
                levels.push(levels.last().unwrap().chunks_exact(2).map(|p| p[0] * p[1]).collect());
            }
            levels.reverse();
            levels
        })
        .collect();
    let products: Vec<F> = trees.iter().map(|t| t[0][0]).collect();
    let products_sent = send(tr, pads, &products);
    let mut values = products.clone();
    let mut z: Vec<F> = Vec::new();
    let mut levels = Vec::with_capacity(d);
    for i in 0..d {
        let scales = powers(tr.challenge(), trees.len());
        let claim = values.iter().zip(&scales).fold(F::ZERO, |s, (v, c)| s + *v * *c);
        // Each tree's level below, as its even and its odd entries.
        let mut sides: Vec<[Vec<F>; 2]> = trees
            .iter()
            .map(|t| {
                [t[i + 1].iter().step_by(2).copied().collect(), t[i + 1].iter().skip(1).step_by(2).copied().collect()]
            })
            .collect();
        let mut st = Rounds { claim, rs: Vec::with_capacity(i), polys: Vec::with_capacity(i) };
        let mut weights = eq_table(&z[1.min(i)..]);
        for z_v in &z {
            let (mut h0, mut h2) = (F::ZERO, F::ZERO);
            for (g, w) in weights.iter().enumerate() {
                let (mut p0, mut p2) = (F::ZERO, F::ZERO);
                for ([a, b], c) in sides.iter().zip(&scales) {
                    p0 += *c * a[2 * g] * b[2 * g];
                    p2 += *c * (a[2 * g] + a[2 * g + 1]) * (b[2 * g] + b[2 * g + 1]);
                }
                h0 += *w * p0;
                h2 += *w * p2;
            }
            let r = st.prove(tr, pads, *z_v, h0, h2);
            for side in sides.iter_mut().flatten() {
                *side = side.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect();
            }
            if weights.len() > 1 {
                weights = weights.chunks_exact(2).map(|p| p[0] + p[1]).collect();
            }
        }
        let ends: Vec<[F; 2]> = sides.iter().map(|[a, b]| [a[0], b[0]]).collect();
        let ends_sent = send(tr, pads, ends.as_flattened());
        if let Some(pads) = pads {
            pads.product_sum(ends.iter().zip(&scales).map(|([a, b], c)| (*c, *a, *b)).collect());
        }
        let t = tr.challenge();
        values = ends.iter().map(|[a, b]| *a + t * (*a + *b)).collect();
        z = std::iter::once(t).chain(st.rs.iter().copied()).collect();
        levels.push(Level { rounds: st.polys, ends: ends_sent.chunks_exact(2).map(|p| [p[0], p[1]]).collect() });
    }
    (Proof { products: products_sent, levels }, z, values, products)
}

/// The verifier's side: for `tables` tables of `2^d` leaves, the
/// products, the point the leaves are left at and each table's value
/// there, which the caller must find to be the tables' own. Over any arithmetic and transcript:
/// the field's to verify, the machine's to make rows that verify.
pub fn verify<A: Alg, T: Transcript<A>>(
    proof: &Proof,
    tables: usize,
    d: usize,
    tr: &mut T,
) -> Option<(Vec<A>, Vec<A>, Vec<A>)> {
    if proof.products.len() != tables || proof.levels.len() != d {
        return None;
    }
    let products = tr.elements(&proof.products);
    let mut values = products.clone();
    let mut z: Vec<A> = Vec::new();
    for (i, level) in proof.levels.iter().enumerate() {
        if level.rounds.len() != i || level.ends.len() != tables {
            return None;
        }
        let scales = alg::powers(&tr.challenge(), tables);
        let weigh = |xs: &[A]| {
            let first = xs[0].clone() * scales[0].clone();
            xs.iter().zip(&scales).skip(1).fold(first, |s, (v, c)| v.clone() * c.clone() + s)
        };
        let (rs, claim) = alg::rounds(tr, &level.rounds, &z, weigh(&values))?;
        let ends = tr.elements(level.ends.as_flattened());
        // The children's products, weighed as the claims were.
        let terms = ends.chunks_exact(2).zip(&scales).map(|(p, c)| (Some(c.clone()), p[0].clone(), p[1].clone()));
        if !tr.product_sum(terms.collect(), None, &claim) {
            return None;
        }
        let t = tr.challenge();
        values = ends.chunks_exact(2).map(|p| (p[0].clone() + p[1].clone()) * t.clone() + p[0].clone()).collect();
        z = std::iter::once(t).chain(rs).collect();
    }
    Some((products, z, values))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::evaluate;
    use crate::test_util::Rng;

    fn run(tables: &[Vec<F>]) -> (Proof, Vec<F>, Vec<F>) {
        let (proof, z, values, _) = prove(tables.to_vec(), &mut Challenger::new(b"t"), &mut None);
        (proof, z, values)
    }

    fn check(proof: &Proof, tables: usize, d: usize) -> Option<(Vec<F>, Vec<F>)> {
        verify(proof, tables, d, &mut Challenger::new(b"t")).map(|(_, z, values)| (z, values))
    }

    #[test]
    fn products_are_proven_down_to_the_tables() {
        let mut rng = Rng(50);
        for (n, d) in [(1, 0), (1, 1), (2, 3), (3, 6), (1, 9)] {
            let tables: Vec<Vec<F>> = (0..n).map(|_| rng.fs(1 << d)).collect();
            let (proof, z, values) = run(&tables);
            for (t, p) in tables.iter().zip(&proof.products) {
                assert_eq!(t.iter().fold(F::ONE, |a, b| a * *b), *p);
            }
            let mut w = Writer::default();
            proof.write(&mut w);
            assert_eq!(Proof::read(&mut Reader(&w.0)).as_ref(), Some(&proof));
            let (vz, vvalues) = check(&proof, n, d).expect("the proof verifies");
            assert_eq!((&vz, &vvalues), (&z, &values));
            assert_eq!(z.len(), d);
            // What is left is each table at the point.
            for (t, v) in tables.iter().zip(&values) {
                assert_eq!(evaluate(t, &z), *v, "{n} tables of 2^{d}");
            }
        }
    }

    #[test]
    fn a_wrong_product_is_not() {
        let mut rng = Rng(51);
        let tables: Vec<Vec<F>> = (0..2).map(|_| rng.fs(64)).collect();
        let (good, ..) = run(&tables);
        assert!(check(&good, 2, 6).is_some());
        let changed = |change: &dyn Fn(&mut Proof)| {
            let mut p = good.clone();
            change(&mut p);
            assert_ne!(p, good);
            // A changed proof either fails, or leaves a claim the tables
            // do not meet.
            match check(&p, 2, 6) {
                None => false,
                Some((z, values)) => tables.iter().zip(&values).all(|(t, v)| evaluate(t, &z) == *v),
            }
        };
        assert!(!changed(&|p| p.products[0] += F::ONE));
        assert!(!changed(&|p| p.products.swap(0, 1)));
        assert!(!changed(&|p| p.levels[0].ends[1][0] += F::ONE));
        assert!(!changed(&|p| p.levels[3].rounds[1][1] += F::ONE));
        assert!(!changed(&|p| p.levels[5].ends[0][1] += F::ONE));
        assert!(!changed(&|p| p.levels[5].rounds[4][0] += F::ONE));
        assert!(!changed(&|p| p.levels.truncate(5)));
        assert!(check(&good, 2, 5).is_none() && check(&good, 1, 6).is_none());
    }
}
