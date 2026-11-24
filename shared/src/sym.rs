//! The verifier's arithmetic over the values of the machine: what makes
//! a circuit that verifies.
//!
//! A verifier's code is written over [`Alg`]. Run over [`Sym`], its
//! sums and products become rows of [`crate::machine`] as they are made:
//! running the verifier over `Sym` on a proof is compiling it, and the
//! rows carry that proof's values. Its transcript is then rows of the
//! hash table ([`Hashed`]), and so are the openings it checks
//! ([`HashedOpens`]).
//!
//! # One row for `(a + d) b + c`
//!
//! A row of the machine is a sum of two values times a third, plus a
//! fourth, and one more if asked. So a `Sym` is not always a row yet: a
//! sum of two values, or a product, waits until what is done with it
//! next is known, and a sum then a product then a sum is one row, not
//! three.
//!
//! # Constants
//!
//! One is a flag of the machine. Any other constant the arithmetic
//! multiplies by is an element the hash table's program sends
//! ([`crate::recursion::Trace::constant`]), read once and copied to its
//! readers; a [`Compiler`] holds both tables for that.

use crate::alg::{Alg, Transcript, halves, statement};
use crate::challenger::Challenger;
use crate::field::F;
use crate::hash::Digest;
use crate::machine::{Assembly, Operand, Value};
use crate::pcs::{Opens, Params, Query, Tree};
use crate::recursion::{Stepped, Trace};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::{Add, Mul};
use std::rc::Rc;

/// The two tables a verifier is compiled into, as they are being made.
pub struct Compiler {
    pub asm: Assembly,
    pub trace: Trace,
    /// Rows of whole numbers ([`crate::arith`]), if the computation has any.
    pub arith: crate::arith::Rows,
    /// The constants read so far, by their bits.
    constants: BTreeMap<u128, Value>,
}

/// A [`Compiler`] that the values made with it share.
#[derive(Clone)]
pub struct Shared(Rc<RefCell<Compiler>>);

impl Default for Shared {
    fn default() -> Shared {
        Shared::new()
    }
}

impl Shared {
    pub fn new() -> Shared {
        Shared(Rc::new(RefCell::new(Compiler {
            asm: Assembly::default(),
            trace: Trace::new(true),
            arith: Default::default(),
            constants: BTreeMap::new(),
        })))
    }

    fn sym(&self, form: Form) -> Sym {
        Sym { cx: self.clone(), form }
    }

    /// A value the prover gives.
    pub fn input(&self, value: F) -> Sym {
        let v = self.0.borrow_mut().asm.input(value);
        self.sym(Form::Val(v))
    }

    /// The value another table sends under `address`.
    pub fn outside(&self, address: u32, value: F) -> Sym {
        let v = self.0.borrow_mut().asm.outside(address, value);
        self.sym(Form::Val(v))
    }

    /// A constant.
    pub fn constant(&self, c: F) -> Sym {
        self.sym(Form::Const(c))
    }

    /// Both tables at once, for what needs the two: a transcript's step
    /// whose values the machine reads.
    pub fn with<R>(&self, f: impl FnOnce(&mut Compiler) -> R) -> R {
        f(&mut self.0.borrow_mut())
    }

    /// The tables as they stand, taken: what is made with this
    /// afterwards is of new ones.
    pub fn finish(&self) -> Compiler {
        let fresh = Compiler {
            asm: Assembly::default(),
            trace: Trace::new(true),
            arith: Default::default(),
            constants: BTreeMap::new(),
        };
        std::mem::replace(&mut self.0.borrow_mut(), fresh)
    }

    /// Says what a proof of the computation is of: the digest of
    /// `elements` ([`statement`]) becomes the machine's public value, the
    /// hash table hashing them and the machine finding them to be these.
    pub fn state(&self, elements: &[Sym]) -> Digest {
        let values: Vec<F> = elements.iter().map(Sym::value).collect();
        let digest = statement(&values);
        let (data, out) = self.with(|c| c.trace.digest(crate::hash::DOM_STATEMENT, &values));
        for ((at, value), element) in data.iter().zip(&values).zip(elements) {
            assert!(self.outside(*at, *value).is(element));
        }
        for (i, (at, half)) in out.iter().zip(halves(&digest)).enumerate() {
            let read = self.outside(*at, half).made();
            self.with(|c| c.asm.public(read, i));
        }
        digest
    }

    /// The elements a statement `digest` is of, given what they are: the
    /// hash table hashes them and the machine finds their digest to be
    /// `digest`. What [`Shared::state`] says, read back by a circuit
    /// that verified the proof.
    pub fn stated(&self, digest: &[Sym; 2], elements: &[F]) -> Vec<Sym> {
        let (data, out) = self.with(|c| c.trace.digest(crate::hash::DOM_STATEMENT, elements));
        for (at, (half, said)) in out.iter().zip(halves(&statement(elements)).into_iter().zip(digest)) {
            assert!(self.outside(*at, half).is(said));
        }
        data.iter().zip(elements).map(|(at, x)| self.outside(*at, *x)).collect()
    }

    /// `a + b`, or `a - b` if `subtract`, as whole numbers of 64 bits,
    /// by a row of [`crate::arith`]: the result, and whether it carried
    /// (for a difference: that `a` is not less than `b`), one or zero.
    /// Both are found to be numbers of 64 bits by it.
    pub fn number(&self, a: &Sym, b: &Sym, subtract: bool) -> (Sym, Sym) {
        let at = [a.send(), b.send(), self.with(|c| c.trace.reserve()), self.with(|c| c.trace.reserve())];
        let (x, y) = (a.value().0 as u64, b.value().0 as u64);
        let (result, carried) = self.with(|c| c.arith.push(x, y, subtract, at));
        (self.outside(at[2], F(result as u128)), self.outside(at[3], F(carried as u128)))
    }

    /// The hash of `elements` in `domain`, by the hash table's rows: the
    /// machine finds what they hashed to be these, and has the digest.
    pub fn hashed(&self, domain: u32, elements: &[Sym]) -> [Sym; 2] {
        let values: Vec<F> = elements.iter().map(Sym::value).collect();
        let (data, out) = self.with(|c| c.trace.digest(domain, &values));
        for ((at, value), element) in data.iter().zip(&values).zip(elements) {
            assert!(self.outside(*at, *value).is(element));
        }
        let digest = halves(&crate::hash::hash_domain(domain, &crate::field::as_bytes(&values)));
        [self.outside(out[0], digest[0]), self.outside(out[1], digest[1])]
    }

    /// The constant `c` as a value of the machine: read from the hash
    /// table's program the first time.
    fn value_of_constant(&self, c: F) -> Value {
        let mut cx = self.0.borrow_mut();
        if let Some(v) = cx.constants.get(&c.0) {
            return *v;
        }
        let at = cx.trace.constant(c);
        let v = cx.asm.outside(at, c);
        cx.constants.insert(c.0, v);
        v
    }

    fn op(&self, a: Value, d: Option<Value>, b: Option<Value>, c: Option<Value>, plus: bool) -> Value {
        let operand = |v: Option<Value>| v.map_or(Operand::None, Operand::Of);
        let b = b.map_or(Operand::One, Operand::Of);
        self.0.borrow_mut().asm.op_plus(a, operand(d), b, operand(c), plus)
    }
}

/// A value being computed by the machine, or about to be.
#[derive(Clone)]
pub struct Sym {
    cx: Shared,
    form: Form,
}

#[derive(Clone, Copy)]
enum Form {
    /// Known without a row.
    Const(F),
    /// A row's result.
    Val(Value),
    /// The sum of two results: no row yet.
    Sum(Value, Value),
    /// `(a + d) b`: no row yet.
    Prod(Value, Option<Value>, Value),
}

impl Sym {
    /// The value in the run being compiled.
    pub fn value(&self) -> F {
        let cx = self.cx.0.borrow();
        let of = |v: Value| cx.asm.value_of(v);
        match self.form {
            Form::Const(c) => c,
            Form::Val(v) => of(v),
            Form::Sum(a, d) => of(a) + of(d),
            Form::Prod(a, d, b) => (of(a) + d.map_or(F::ZERO, of)) * of(b),
        }
    }

    /// The row whose result this is, made now if it was not yet.
    pub fn made(&self) -> Value {
        match self.form {
            Form::Const(c) => self.cx.value_of_constant(c),
            Form::Val(v) => v,
            Form::Sum(a, d) => self.cx.op(a, Some(d), None, None, false),
            Form::Prod(a, d, b) => self.cx.op(a, d, Some(b), None, false),
        }
    }

    /// The address another table can read this under, once.
    pub fn send(&self) -> u32 {
        let v = self.made();
        self.cx.0.borrow_mut().asm.send(v)
    }
}

impl Add for Sym {
    type Output = Sym;
    fn add(self, other: Sym) -> Sym {
        let cx = self.cx.clone();
        let form = match (self.form, other.form) {
            (Form::Const(x), Form::Const(y)) => Form::Const(x + y),
            (Form::Const(F::ZERO), f) | (f, Form::Const(F::ZERO)) => f,
            // One more: a flag of the row the other is, or is made.
            (Form::Const(F::ONE), f) | (f, Form::Const(F::ONE)) => Form::Val(match f {
                Form::Prod(a, d, b) => cx.op(a, d, Some(b), None, true),
                Form::Sum(a, d) => cx.op(a, Some(d), None, None, true),
                _ => cx.op(cx.sym(f).made(), None, None, None, true),
            }),
            // A product and a value: the row.
            (Form::Prod(a, d, b), Form::Val(c)) | (Form::Val(c), Form::Prod(a, d, b)) => {
                Form::Val(cx.op(a, d, Some(b), Some(c), false))
            }
            (Form::Val(x), Form::Val(y)) if x == y => Form::Const(F::ZERO),
            // Three values: one row, so a long sum is a row for two.
            (Form::Sum(a, d), Form::Val(c)) | (Form::Val(c), Form::Sum(a, d)) => {
                Form::Val(cx.op(a, Some(d), None, Some(c), false))
            }
            (Form::Val(x), Form::Val(y)) => Form::Sum(x, y),
            // Anything else: a product keeps waiting for the other, made.
            (Form::Prod(a, d, b), f) | (f, Form::Prod(a, d, b)) => {
                let c = cx.sym(f).made();
                Form::Val(cx.op(a, d, Some(b), Some(c), false))
            }
            (x, y) => Form::Sum(cx.sym(x).made(), cx.sym(y).made()),
        };
        cx.sym(form)
    }
}

impl Mul for Sym {
    type Output = Sym;
    fn mul(self, other: Sym) -> Sym {
        let cx = self.cx.clone();
        let form = match (self.form, other.form) {
            (Form::Const(x), Form::Const(y)) => Form::Const(x * y),
            (Form::Const(F::ZERO), _) | (_, Form::Const(F::ZERO)) => Form::Const(F::ZERO),
            (Form::Const(F::ONE), f) | (f, Form::Const(F::ONE)) => f,
            // A sum of two times a value: no row yet.
            (Form::Sum(a, d), Form::Val(b)) | (Form::Val(b), Form::Sum(a, d)) => Form::Prod(a, Some(d), b),
            (Form::Sum(a, d), f) | (f, Form::Sum(a, d)) => Form::Prod(a, Some(d), cx.sym(f).made()),
            (x, y) => Form::Prod(cx.sym(x).made(), None, cx.sym(y).made()),
        };
        cx.sym(form)
    }
}

impl Alg for Sym {
    fn lift(&self, c: F) -> Sym {
        self.cx.constant(c)
    }

    fn is(&self, other: &Sym) -> bool {
        let (x, y) = (self.made(), other.made());
        self.cx.0.borrow_mut().asm.equal(x, y);
        true
    }

    fn kept(self) -> Sym {
        match self.form {
            Form::Const(_) | Form::Val(_) => self,
            _ => self.cx.sym(Form::Val(self.made())),
        }
    }

    fn inv(&self) -> Option<Sym> {
        let inv = self.cx.input(self.value().inv());
        (self.clone() * inv.clone()).is(&self.cx.constant(F::ONE)).then_some(inv)
    }
}

/// A transcript replayed as rows of the hash table: every step a row or
/// more, which send what the arithmetic computes with, and the machine
/// reads it.
pub struct Hashed {
    tr: Challenger,
    cx: Shared,
    /// Steps already made rows.
    done: usize,
}

impl Hashed {
    /// The transcript of the protocol `label` names, its rows and the
    /// machine's made with `cx`.
    pub fn new(label: &[u8], cx: &Shared) -> Hashed {
        Hashed { tr: Challenger::recording(label), cx: cx.clone(), done: 0 }
    }

    /// Grinds for `bits` before the next challenge, whoever makes the
    /// rows finding the nonce: for a challenge drawn within a circuit,
    /// of a round that errs by more than a round may. Nothing, for no
    /// bits.
    pub fn grind(&mut self, bits: usize) {
        if bits > 0 {
            let nonce = self.tr.clone().grind(bits);
            assert!(Transcript::<Sym>::ground(self, bits, nonce));
        }
    }

    /// The steps made since the last call, as rows.
    fn rows(&mut self, data: bool, challenge: bool, low: bool, ground: usize) -> Vec<Stepped> {
        let log = self.tr.log.as_ref().expect("a recording transcript");
        let mut out = Vec::new();
        for step in &log[self.done..] {
            let first = self.done == 0;
            let stepped = self.cx.with(|c| c.trace.step(step, first, data, challenge, low, ground));
            if first {
                // The state a transcript begins from: the label's hash.
                let state = halves(step.input[..32].try_into().unwrap());
                for (at, half) in stepped.state.iter().zip(state) {
                    assert!(self.cx.outside(*at, half).is(&self.cx.constant(half)));
                }
            }
            out.push(stepped);
            self.done += 1;
        }
        out
    }
}

impl Transcript<Sym> for Hashed {
    fn elements(&mut self, xs: &[F]) -> Vec<Sym> {
        self.tr.absorb_fs(xs);
        let at: Vec<u32> = self.rows(true, false, false, 0).into_iter().flat_map(|s| s.data).collect();
        at.iter().zip(xs).map(|(at, x)| self.cx.outside(*at, *x)).collect()
    }

    fn digest(&mut self, d: &Digest) -> [Sym; 2] {
        self.tr.absorb(d);
        let at: Vec<u32> = self.rows(true, false, false, 0).into_iter().flat_map(|s| s.data).collect();
        let h = halves(d);
        [self.cx.outside(at[0], h[0]), self.cx.outside(at[1], h[1])]
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.tr.absorb(bytes);
        self.rows(false, false, false, 0);
    }

    fn public(&mut self, words: &[u32]) -> Option<Vec<Sym>> {
        assert!(words.len().is_multiple_of(4), "public values that are whole elements");
        let xs: Vec<F> =
            (words.chunks_exact(4)).map(|w| F(w.iter().rev().fold(0, |x, w| x << 32 | *w as u128))).collect();
        // The same bytes, so the same transcript as the field's verifier.
        Some(self.elements(&xs))
    }

    fn challenge(&mut self) -> Sym {
        let value = self.tr.challenge();
        let stepped = self.rows(false, true, false, 0);
        self.cx.outside(stepped[0].challenge, value)
    }

    fn ground(&mut self, bits: usize, nonce: u64) -> bool {
        let ok = self.tr.check_grind(bits, nonce);
        self.rows(false, false, false, bits);
        ok
    }

    fn index(&mut self, bits: usize) -> (usize, Sym) {
        let (index, low) = self.tr.index_and_low(bits);
        let stepped = self.rows(false, false, true, 0);
        (index, self.cx.outside(stepped[0].low, F(low as u128)))
    }
}

/// Openings as rows of the hash table: every query's leaf in every tree
/// hashed and its path climbed by itself, whichever leaves the queries
/// share, so that the rows are the same for every proof. The machine
/// sends each opening its index and reads what the opening sends.
pub struct HashedOpens {
    cx: Shared,
}

impl HashedOpens {
    pub fn new(cx: &Shared) -> HashedOpens {
        HashedOpens { cx: cx.clone() }
    }

    /// One opening, of the leaf the index `raw` names in `tree` (the
    /// index's bits above the tree's height are not read): the leaf, the
    /// index shifted by each of one to `shift` places, and what of it is
    /// above the tree if `high`. `None` if the path does not reach the
    /// root the arithmetic holds.
    fn opening(
        &self,
        tree: &Tree<Sym>,
        leaf: &[F],
        path: &[Digest],
        raw: &Sym,
        shift: usize,
        high: bool,
    ) -> Option<(Vec<Sym>, Vec<Sym>, Option<Sym>)> {
        let cx = &self.cx;
        let index = raw.value().0 as u32;
        let index_at = raw.send();
        let (opened, top) = cx.with(|c| {
            let opened = c.trace.opening(leaf, index, path, index_at, true, shift, high);
            (opened, c.trace.last())
        });
        for (at, (half, root)) in opened.top.iter().zip(halves(&top).into_iter().zip(&tree.at)) {
            if top != *tree.root || !cx.outside(*at, half).is(root) {
                return None;
            }
        }
        let leaf = opened.leaf.iter().zip(leaf).map(|(at, x)| cx.outside(*at, *x)).collect();
        let shifted = (opened.shifted.iter().enumerate()).map(|(b, at)| cx.outside(*at, F((index >> (b + 1)) as u128)));
        let high = high.then(|| cx.outside(opened.high, F((index >> path.len()) as u128)));
        Some((leaf, shifted.collect(), high))
    }
}

/// Each leaf's own path in a tree, from the batch a proof holds, with
/// the leaves' indices: `None` if the batch is not of those leaves.
fn paths(tree: &Tree<Sym>, indices: &[usize], height: usize, leaf: usize) -> Option<(Vec<usize>, Vec<Vec<Digest>>)> {
    let mut distinct = indices.to_vec();
    distinct.sort_unstable();
    distinct.dedup();
    let batch = tree.batch;
    if batch.leaves.len() != distinct.len() || batch.leaves.iter().any(|l| l.len() != leaf) {
        return None;
    }
    let hashes: Vec<Digest> = batch.leaves.iter().map(|l| crate::merkle::leaf_hash(l)).collect();
    crate::merkle::batch_root(&distinct, &hashes, height, &batch.siblings)?;
    let paths = crate::merkle::batch_paths(&distinct, &hashes, height, &batch.siblings);
    Some((distinct, paths))
}

impl Opens<Sym> for HashedOpens {
    fn open(
        &mut self,
        params: &Params,
        trees: &[Tree<Sym>],
        joined: &[Tree<Sym>],
        indices: &[(usize, Sym)],
    ) -> Option<Vec<Query<Sym>>> {
        let shapes = crate::pcs::shapes(params);
        let x = |c: F| indices[0].1.lift(c);
        // A query's leaf in each codeword, and every tree's paths.
        let mut at: Vec<Vec<usize>> = vec![indices.iter().map(|(i, _)| *i).collect()];
        for (_, s) in &shapes[1..] {
            at.push(at[at.len() - 1].iter().map(|i| i >> s).collect());
        }
        let of = |tree: &Tree<Sym>, joined: bool| {
            // A joiner's leaves are the entries of the codeword it
            // joined: a query's is its leaf in the codeword before.
            let (height, s) = shapes[tree.codeword];
            let (height, indices) =
                if joined { (height + s, &at[tree.codeword - 1]) } else { (height, &at[tree.codeword]) };
            paths(tree, indices, height, crate::pcs::leaf_len(params, tree.codeword, joined))
        };
        let own: Vec<_> = trees.iter().map(|t| of(t, false)).collect::<Option<_>>()?;
        let others: Vec<_> = joined.iter().map(|t| of(t, true)).collect::<Option<_>>()?;
        let mut queries = Vec::with_capacity(indices.len());
        for (q, (_, low)) in indices.iter().enumerate() {
            // The index as the transcript gave it, bits above it and all:
            // each opening reads the bits its path needs.
            let mut raw = low.clone();
            let mut query = Query { point: raw.clone(), leaves: vec![], joined: vec![], bits: vec![vec![]] };
            for (t, tree) in trees.iter().enumerate() {
                let (height, _) = shapes[t];
                let leaf_at = |(distinct, paths): &(Vec<usize>, Vec<Vec<Digest>>)| {
                    let i = distinct.binary_search(&at[t][q]).expect("opened");
                    (i, paths[i].clone())
                };
                let shift = shapes.get(t + 1).map_or(0, |next| next.1);
                let (i, path) = leaf_at(&own[t]);
                let (leaf, shifted, high) = self.opening(tree, &tree.batch.leaves[i], &path, &raw, shift, t == 0)?;
                query.leaves.push(leaf);
                if let Some(high) = high {
                    // The leaf's index alone: the transcript's bits less
                    // those above the tree.
                    query.point = high * x(F(1 << height)) + raw.clone();
                }
                for (j, tree) in joined.iter().enumerate().filter(|(_, tree)| tree.codeword == t + 1) {
                    // The entry of the next codeword this leaf folds
                    // to: the same index, in a tree of entries.
                    let (distinct, paths) = &others[j];
                    let i = distinct.binary_search(&at[t][q]).expect("opened");
                    let (leaf, ..) = self.opening(tree, &tree.batch.leaves[i], &paths[i], &raw, 0, false)?;
                    query.joined.push(leaf);
                }
                if shift > 0 {
                    // A bit of the index is the index less twice the index
                    // shifted: the place in the next codeword's leaf.
                    let from = std::iter::once(&raw).chain(&shifted);
                    let bits = from.zip(&shifted).map(|(low, high)| high.clone() * x(F(2)) + low.clone()).collect();
                    query.bits.push(bits);
                    raw = shifted[shift - 1].clone();
                }
            }
            queries.push(query);
        }
        Some(queries)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::alg::{eq, successor};
    use crate::argument::{self, Layout, Part, Program, Table, prove_tables, verify_tables};
    use crate::circuit::{Fixed, Witness};
    use crate::ntt::Domain;
    use crate::pcs::Params;
    use crate::test_util::Rng;
    use crate::{machine, recursion};

    /// What was compiled, proven: the hash table and the machine
    /// together, and what a verifier of the proof needs.
    pub(crate) struct Proven {
        pub params: Params,
        pub program: Digest,
        pub proof: argument::Proof,
        /// Rows of the hash table and of the machine.
        pub rows: [usize; 2],
        /// The machine's rows that are operations.
        pub used: usize,
        /// Whether the machine's assertions hold.
        pub holds: bool,
        /// What the proof is of: the machine's public values.
        pub public: Vec<u32>,
        pub proving: std::time::Duration,
    }

    impl Proven {
        pub fn verifies(&self) -> bool {
            let (hash, machine) = (recursion::circuit(), machine::circuit());
            let tables = [
                Table { circuit: &hash, rows: self.rows[0], public: &[] },
                Table { circuit: &machine, rows: self.rows[1], public: &self.public },
            ];
            let domain = Domain::new(self.params.k(), false);
            verify_tables(&self.params, &domain, &tables, Some(&self.program), &self.proof).is_some()
        }

        /// The verification of this proof, made rows of `cx`: what the
        /// proof was verified against and what it was of, as the
        /// arithmetic holds them (the program's root, then the proof's
        /// statement). `None` if the verifier turns the proof away
        /// before it has made its rows.
        pub fn verify_into(&self, cx: &Shared) -> Option<Vec<Sym>> {
            let (hash, machine) = (recursion::circuit(), machine::circuit());
            let tables = [
                Table { circuit: &hash, rows: self.rows[0], public: &[] },
                Table { circuit: &machine, rows: self.rows[1], public: &self.public },
            ];
            let domain = Domain::new(self.params.k(), false);
            let named = argument::label(&self.params, tables.iter().map(|t| t.rows));
            let (mut tr, mut opens) = (Hashed::new(&named, cx), HashedOpens::new(cx));
            let program = Some(&self.program);
            let taken = argument::check::<Sym, _, _>(
                &self.params,
                &domain,
                &tables,
                program,
                &self.proof,
                &mut tr,
                &mut opens,
            )?;
            let publics = taken.publics.into_iter().flatten().flatten();
            Some(taken.program.into_iter().flatten().chain(publics).collect())
        }

        /// What [`Proven::verify_into`] gives, by the field.
        pub fn verified(&self) -> Vec<F> {
            halves(&self.program).into_iter().chain(halves(&digest_of(&self.public))).collect()
        }

        /// A computation that verifies this proof and states what it
        /// verified.
        pub fn compile(&self) -> Option<Shared> {
            let cx = Shared::new();
            let of = self.verify_into(&cx)?;
            assert_eq!(cx.state(&of), statement(&self.verified()));
            Some(cx)
        }
    }

    /// Public words as the digest they are.
    fn digest_of(words: &[u32]) -> Digest {
        crate::blake3::bytes(&std::array::from_fn::<u32, 8, _>(|i| words[i]))
    }

    /// The proof of what was compiled, under the parameters `params`
    /// gives for the polynomial's size.
    pub(crate) fn prove_compiled(cx: Shared, params: impl Fn(usize) -> Params) -> Proven {
        let Compiler { asm, trace, .. } = cx.finish();
        let rows = asm.finish(128);
        let used = rows.program.chunks(4).filter(|p| p[3] & 4 == 0).count();
        // The hash table is to be the larger: its rows are eight of the
        // machine's.
        let (hash_rows, hash_program) = trace.finish(128.max(rows.inputs.len() / 8));
        let (hash, machine) = (recursion::circuit(), machine::circuit());
        let tables = [(&hash, hash_rows.len()), (&machine, rows.inputs.len())];
        let layout = Layout::of(tables.iter().copied()).expect("the hash table is the larger");
        let params = params(layout.total);
        let domain = Domain::new(params.k(), true);
        let program = Program::of(&params, &domain, &tables, vec![hash_program, rows.program.clone()]);
        let fixed = [
            Fixed { program: &program.words[0], public: &[] },
            Fixed { program: &program.words[1], public: &rows.public },
        ];
        let t = std::time::Instant::now();
        let witness = [
            Witness::new(&hash, hash_rows.len(), |c| _ = recursion::row(c), |i| hash_rows[i], &fixed[0]),
            Witness::new(&machine, rows.inputs.len(), |c| machine::run(c), |i| rows.inputs[i], &fixed[1]),
        ];
        let [a, b] = witness;
        let parts = vec![
            Part { circuit: &hash, witness: a, public: &[] },
            Part { circuit: &machine, witness: b, public: &rows.public },
        ];
        let (proof, _) = prove_tables(&params, &domain, parts, Some(&program));
        Proven {
            params,
            program: program.root(),
            proof,
            rows: [hash_rows.len(), rows.inputs.len()],
            used,
            holds: rows.holds,
            public: rows.public.clone(),
            proving: t.elapsed(),
        }
    }

    /// Whether what was compiled is proven, and the machine's rows that
    /// are operations.
    pub(crate) fn proven(cx: Shared) -> (bool, usize) {
        let p = prove_compiled(cx, |m| Params::plain(m, 1, 4, 4));
        let ok = p.verifies();
        assert!(!ok || p.holds);
        (ok, p.used)
    }

    /// A small computation, compiled: a product chain asserted to be
    /// what it is.
    fn small(seed: u64) -> Shared {
        let cx = Shared::new();
        let mut rng = Rng(seed);
        let xs: Vec<Sym> = rng.fs(40).iter().map(|x| cx.input(*x)).collect();
        let product = xs.iter().cloned().reduce(|p, x| p * x + cx.constant(F(5))).unwrap();
        assert!(product.is(&cx.input(product.value())));
        cx
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_proof_is_verified_by_rows() {
        // A proof of the two tables; its verification compiled to the
        // two tables; that proven, and verified by the field's verifier.
        let params = |m: usize| Params::plain(m, 1, 5, 4);
        let inner = prove_compiled(small(77), params);
        assert!(inner.holds && inner.verifies());
        let outer = prove_compiled(inner.compile().expect("the proof verifies"), params);
        assert!(outer.holds, "the compiled verifier's assertions hold");
        assert!(outer.verifies());
        // It is a proof of having verified that program's proof of that
        // statement, and of nothing else.
        assert_eq!(digest_of(&outer.public), statement(&inner.verified()));
        for word in [0, 7] {
            let mut other = Proven { proof: outer.proof.clone(), public: outer.public.clone(), ..outer };
            other.public[word] ^= 1;
            assert!(!other.verifies());
        }
        // The inner proof is not of another statement either: a
        // verifier compiled for one does not hold.
        let mut other = Proven { proof: inner.proof.clone(), public: inner.public.clone(), ..inner };
        other.public[3] ^= 1;
        assert!(!other.verifies());
        if let Some(cx) = other.compile() {
            let outer = prove_compiled(cx, params);
            assert!(!outer.holds && !outer.verifies());
        }
        // A proof with a value changed: the verifier's rows are made all
        // the same (or it is turned away before), and do not hold.
        let changes: [&dyn Fn(&mut argument::Proof); 5] = [
            &|p| p.tables[1].abc[0] += F::ONE,
            &|p| p.tables[0].u[1] += F::ONE,
            &|p| p.tables[1].s[100] += F::ONE,
            &|p| p.pcs.first_final += F::ONE,
            &|p| p.pcs.openings[1].leaves[0][3] += F::ONE,
        ];
        for (i, change) in changes.iter().enumerate() {
            let mut bad = Proven { proof: inner.proof.clone(), public: inner.public.clone(), ..inner };
            change(&mut bad.proof);
            assert!(!bad.verifies(), "change {i}");
            if let Some(cx) = bad.compile() {
                let outer = prove_compiled(cx, params);
                assert!(!outer.holds && !outer.verifies(), "change {i}");
            }
        }
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn the_verifier_s_program_is_the_same_for_every_proof() {
        // Two proofs of one shape, of different computations' values:
        // the rows that verify them differ, their programs do not.
        let params = |m: usize| Params::plain(m, 1, 5, 4);
        let compiled = |seed: u64| {
            let inner = prove_compiled(small(seed), params);
            let Compiler { asm, trace, .. } = inner.compile().expect("the proof verifies").finish();
            let (rows, (hash_rows, hash_program)) = (asm.finish(128), trace.finish(128));
            (inner.proof, rows.inputs, rows.program, hash_rows, hash_program)
        };
        let (a, b) = (compiled(77), compiled(78));
        assert!(a.0 != b.0 && a.1 != b.1 && a.3 != b.3);
        assert!(a.2 == b.2 && a.4 == b.4);
    }

    /// A proof of proofs of proofs, at the parameters of the chain: what
    /// each level takes, verifying one proof (`PROOFS=1`, the default)
    /// or two as a step of the chain does (`PROOFS=2`).
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn fixed_point_timing() {
        let proofs: usize = std::env::var("PROOFS").ok().and_then(|x| x.parse().ok()).unwrap_or(1);
        let params = |m: usize| Params::proven(m, 2, crate::pcs::SECURITY);
        let mut p = prove_compiled(small(77), params);
        let mut programs = Vec::new();
        for level in 0..4 {
            let t = std::time::Instant::now();
            assert!(p.verifies());
            let verified = t.elapsed();
            println!(
                "level {level}: 2^{} hash rows, 2^{} machine rows ({} used), 2^{} elements: \
                 proven in {:.2?}, {} KB, verified in {verified:.2?}",
                p.rows[0].trailing_zeros(),
                p.rows[1].trailing_zeros(),
                p.used,
                p.params.m,
                p.proving,
                p.proof.size() / 1000,
            );
            programs.push(p.program);
            let t = std::time::Instant::now();
            let cx = Shared::new();
            let of: Vec<Sym> = (0..proofs).flat_map(|_| p.verify_into(&cx).expect("the proof verifies")).collect();
            cx.state(&of);
            let compiled = t.elapsed();
            let (hash, machine) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
            println!(
                "  its verifier, {proofs} times: {hash} hash rows, {machine} operations, compiled in {compiled:.2?}"
            );
            p = prove_compiled(cx, params);
            assert!(p.holds);
        }
        // From the level that verifies a proof of its own shape on, the
        // program is the same: the proof verifies its own kind.
        assert_eq!(programs[2], programs[3]);
    }

    #[test]
    fn the_same_code_verifies_and_compiles() {
        let mut rng = Rng(1);
        let (a, b) = (rng.fs(9), rng.fs(9));
        // Natively: this module's against the argument's own.
        assert_eq!(eq(&a, &b), crate::pcs::eq(&a, &b));
        assert_eq!(successor(&a, &b), argument::successor(&a, &b));
        // Compiled, and asserted to be those values.
        let run = |wrong: bool| {
            let cx = Shared::new();
            let (sa, sb): (Vec<Sym>, Vec<Sym>) =
                (a.iter().map(|x| cx.input(*x)).collect(), b.iter().map(|x| cx.input(*x)).collect());
            let (e, s) = (eq(&sa, &sb), successor(&sa, &sb));
            assert_eq!((e.value(), s.value()), (eq(&a, &b), successor(&a, &b)));
            assert!(e.is(&cx.input(eq(&a, &b) + F(wrong as u128))));
            assert!(s.is(&cx.input(successor(&a, &b))));
            drop((sa, sb, e, s));
            proven(cx)
        };
        let (ok, used) = run(false);
        assert!(ok);
        // `eq` is a row a variable: each factor's sum, product and the
        // one more are one row.
        assert!(used < 160, "{used} rows");
        assert!(!run(true).0);
    }

    #[test]
    fn a_grand_product_is_verified_by_rows() {
        // A grand product's proof, verified by the same code twice: on
        // the field with a transcript, and on the machine with the
        // transcript's steps as rows of the hash table.
        let mut rng = Rng(2);
        let tables: Vec<Vec<F>> = (0..2).map(|_| rng.fs(32)).collect();
        let (proof, z, values, _) = crate::grand::prove(tables.clone(), &mut Challenger::new(b"grand"), &mut None);
        let native = crate::grand::verify::<F, _>(&proof, 2, 5, &mut Challenger::new(b"grand")).unwrap();
        assert_eq!((native.1, native.2), (z.clone(), values.clone()));
        let good = proof.clone();
        let compile = |proof: &crate::grand::Proof| {
            let cx = Shared::new();
            let mut tr = Hashed::new(b"grand", &cx);
            let (_, sz, sv) = crate::grand::verify::<Sym, _>(proof, 2, 5, &mut tr).unwrap();
            // The point is the one the field's verifier finds for this
            // proof; the values there are asserted to be the tables'.
            let point: Vec<F> = sz.iter().map(Sym::value).collect();
            if *proof == good {
                assert_eq!(point, z);
            }
            for (v, table) in sv.iter().zip(&tables) {
                assert!(v.is(&cx.input(crate::pcs::evaluate(table, &point))));
            }
            let steps = cx.with(|c| c.trace.transcript);
            drop((sz, sv, tr));
            (proven(cx), steps)
        };
        let ((ok, used), steps) = compile(&proof);
        assert!(ok);
        // A level's rounds are three rows each, and its ends a few.
        assert!(used < 400 && steps < 120, "{used} rows of the machine, {steps} of the transcript");
        // A proof changed anywhere: an assertion of the machine's fails,
        // or what it reads is not what the transcript's rows send.
        for change in 0..4 {
            let mut bad = proof.clone();
            match change {
                0 => bad.products[1] += F::ONE,
                1 => bad.levels[4].rounds[2][1] += F::ONE,
                2 => bad.levels[4].ends[0][0] += F::ONE,
                _ => bad.levels[1].ends[1][1] += F::ONE,
            }
            assert!(crate::grand::verify::<F, _>(&bad, 2, 5, &mut Challenger::new(b"grand")).is_none());
            assert!(!compile(&bad).0.0, "change {change}");
        }
    }

    #[test]
    fn sums_and_products_are_rows_only_when_they_must_be() {
        let cx = Shared::new();
        let rows = |cx: &Shared| cx.with(|c| c.asm.finish_len());
        let [w, x, y, z] = [3u128, 5, 7, 11].map(|v| cx.input(F(v)));
        let before = rows(&cx);
        // (w + x) y + z: one row.
        let r = (w.clone() + x.clone()) * y.clone() + z.clone();
        assert_eq!(r.value(), (F(3) + F(5)) * F(7) + F(11));
        assert_eq!(rows(&cx) - before, 1);
        // x y + 1: one row, and no constant read.
        let q = x.clone() * y.clone() + cx.constant(F::ONE);
        assert_eq!((q.value(), rows(&cx) - before), (F(5) * F(7) + F::ONE, 2));
        // Constants fold, and zero and one cost nothing.
        let k = cx.constant(F(4)) * cx.constant(F(9)) + cx.constant(F::ZERO);
        assert_eq!(k.value(), F(4) * F(9));
        let same = x.clone() * cx.constant(F::ONE) + cx.constant(F::ZERO);
        assert_eq!((same.value(), rows(&cx) - before), (F(5), 2));
        // x + x is nothing.
        assert_eq!((x.clone() + x.clone()).value(), F::ZERO);
        // A constant that is neither: read once, however often used.
        let c = cx.constant(F(0xABCD));
        let u = c.clone() * w.clone() + (c.clone() * z.clone());
        assert_eq!(u.value(), F(0xABCD) * F(3) + F(0xABCD) * F(11));
        assert_eq!(cx.with(|c| c.constants.len()), 1);
        // Everything made is read or asserted.
        for (v, expect) in [
            (r, (F(3) + F(5)) * F(7) + F(11)),
            (q, F(5) * F(7) + F::ONE),
            (same, F(5)),
            (u, F(0xABCD) * F(3) + F(0xABCD) * F(11)),
        ] {
            assert!(v.is(&cx.input(expect)));
        }
        assert!(k.is(&cx.constant(F(4) * F(9))));
        drop((w, x, y, z, c));
        assert!(proven(cx).0);
    }
}
