//! A circuit's part in what a verifier checks: what its terms come to at
//! the points the argument's checks end at.
//!
//! Each of a table's checks (its constraints, its multiplications, its
//! bus) ends with a value at a point, and that value is a sum, over the
//! rows and under the point's weights of them, of bits of the rows'
//! words, each bit weighed as the circuit's terms say
//! ([`crate::argument`]). The prover makes the weights into tables, an
//! entry a bit. The verifier needs those tables at one point only, and
//! never makes them: it goes through the circuit a term at a time and
//! adds each term's part of that value ([`AtPoint`]), which is what lets
//! a circuit be the verifier.
//!
//! Everything here is over any arithmetic ([`Alg`]): the field's, to
//! verify, or the machine's, to make rows that verify.

use crate::alg::{Alg, eq_table, eq_table_like};
use crate::circuit::{Circuit, Element, Expr, LOG_PROGRAM_SHARE, Pre, Source, Sum, Term};
use crate::field::F;
use std::collections::BTreeMap;

/// Bit places of a word, as variables.
pub const LOG_W: usize = 5;

/// Rows whose bits share a packed element, as variables.
pub(crate) const LOG_PACK: usize = 7;

/// Variables of the packed witness of `rows` rows of `circuit`: what the
/// opening's parameters are made for.
pub fn variables(circuit: &Circuit, rows: usize) -> usize {
    let r = rows.trailing_zeros() as usize;
    assert!(rows.is_power_of_two() && r >= LOG_PACK, "rows are a power of two, 128 at least");
    LOG_W + circuit.log_cols + r - LOG_PACK
}

/// Where each table's words lie in the one polynomial a proof commits
/// to: a block of its own size, the tables one after another, largest
/// first, so that every block begins at a multiple of its size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// Variables of each table's words.
    pub m: Vec<usize>,
    /// The element each table's block begins at.
    pub offset: Vec<usize>,
    /// Variables of the whole: what the opening's parameters are for.
    pub total: usize,
}

impl Layout {
    /// The layout of tables of these circuits and rows, if the rows are
    /// powers of two, 128 at least, and no table is larger than the one
    /// before it.
    pub fn of<'a>(tables: impl Iterator<Item = (&'a Circuit, usize)>) -> Option<Layout> {
        let (mut m, mut offset, mut at) = (Vec::new(), Vec::new(), 0usize);
        for (circuit, rows) in tables {
            if !rows.is_power_of_two() || rows < 1 << LOG_PACK {
                return None;
            }
            let vars = variables(circuit, rows);
            if m.last().is_some_and(|last| vars > *last) {
                return None;
            }
            offset.push(at);
            at += 1 << vars;
            m.push(vars);
        }
        (!m.is_empty()).then(|| Layout { m, offset, total: at.next_power_of_two().trailing_zeros() as usize })
    }

    /// Table `i`'s block of the words, or of the program if `program`:
    /// a program's block is its table's, a sixteenth the size.
    pub(crate) fn block(&self, i: usize, program: bool) -> std::ops::Range<usize> {
        let shift = if program { LOG_PROGRAM_SHARE } else { 0 };
        self.offset[i] >> shift..(self.offset[i] + (1 << self.m[i])) >> shift
    }

    /// The weight, at the opening's challenges `r`, of table `i`'s
    /// block: `eq` of the challenges above the block's own variables
    /// with the block's number.
    pub fn weight<A: Alg>(&self, i: usize, r: &[A]) -> A {
        let number = self.offset[i] >> self.m[i];
        let one = r[0].lift(F::ONE);
        r[self.m[i]..].iter().enumerate().fold(one.clone(), |w, (b, rb)| {
            w * if number >> b & 1 == 1 { rb.clone() } else { rb.clone() + one.clone() }
        })
    }
}

/// A table's public values, to a verifier: the words, and for a verifier
/// that is a circuit the elements they are, as its arithmetic holds
/// them. Such a verifier knows the values as what its transcript took
/// in, not as constants; so it reads a public value as a whole element
/// only, which is how the circuits it verifies use theirs.
pub struct Public<'a, A> {
    pub words: &'a [u32],
    pub elements: Option<Vec<A>>,
}

impl<A: Alg> Public<'_, A> {
    /// A public word, in a constraint.
    fn word(&self, col: usize) -> u32 {
        assert!(self.elements.is_none(), "a compiled verifier reads public values as whole elements");
        self.words[col]
    }

    /// What of `sum` is known: its constant, and its public terms.
    fn known(&self, sum: &Sum, like: &A) -> Option<A> {
        let public = sum.terms.iter().filter(|t| t.from == Source::Public);
        let Some(elements) = &self.elements else {
            let known = public.fold(sum.constant, |s, t| s + t.of(self.words));
            return (known != F::ZERO).then(|| like.lift(known));
        };
        let mut known = (sum.constant != F::ZERO).then(|| like.lift(sum.constant));
        for t in public {
            assert!(t.col % 4 == 0 && t.bit == 0 && t.bits == 128, "a public value read as a whole element");
            add_to(&mut known, elements[t.col as usize / 4].clone() * like.lift(t.scale));
        }
        known
    }
}

/// What goes through a circuit's terms and adds up their part in what a
/// check leaves: each term's weight, to wherever its word is.
pub trait Acc<A: Alg> {
    /// The weights of the 32 places of a word in the check's point:
    /// empty for a check whose values are elements.
    fn eq_j(&self) -> &[A];

    /// `c` more of the constant.
    fn constant(&mut self, c: A);

    /// A term of an operand that weighs `c` in all, its place `j`
    /// weighing `c eq_j[j]`.
    fn term(&mut self, t: &Term, c: &A, public: &Public<A>);

    /// `weight` times a sum of elements.
    fn sum(&mut self, sum: &Sum, weight: &A, public: &Public<A>);

    /// An operand that weighs `c` in all: its constant and its terms.
    fn operand(&mut self, expr: &Expr, c: &A, public: &Public<A>) {
        self.word(expr.constant, c);
        for t in &expr.terms {
            self.term(t, c, public);
        }
    }

    /// A word that is known, in an operand that weighs `c`: its part of
    /// the constant.
    fn word(&mut self, v: u32, c: &A) {
        let set: Vec<A> = (0..32).filter(|j| v >> j & 1 == 1).map(|j| self.eq_j()[j].clone()).collect();
        if let Some(at) = set.into_iter().reduce(|s, x| s + x) {
            self.constant(c.clone() * at);
        }
    }
}

/// The bit of a term's word that the operand's bit `j` is: bit `j + rot`
/// of the shifted word, which is the word's bit below that if it was
/// shifted left, above if right, and no bit where the shift brought in a
/// zero.
pub fn source_bit(t: &Term, j: usize) -> Option<usize> {
    let at = (j + t.rot as usize) % 32;
    match t.pre {
        Pre::None => Some(at),
        Pre::Shl => at.checked_sub(1),
        Pre::Shr => (at < 31).then_some(at + 1),
    }
}

/// A check's constant alone: what the verifier needs before the points
/// of the tables are known.
pub(crate) struct Constant<A> {
    eq_j: Vec<A>,
    pub constant: Option<A>,
    /// The weights of the words met so far: a circuit has few constants
    /// and uses each often.
    words: BTreeMap<u32, A>,
}

impl<A: Alg> Constant<A> {
    pub fn new(eq_j: &[A]) -> Constant<A> {
        Constant { eq_j: eq_j.to_vec(), constant: None, words: BTreeMap::new() }
    }
}

fn add_to<A: Alg>(sum: &mut Option<A>, x: A) {
    *sum = Some(match sum.take() {
        Some(s) => s + x,
        None => x,
    });
}

impl<A: Alg> Acc<A> for Constant<A> {
    fn eq_j(&self) -> &[A] {
        &self.eq_j
    }

    fn constant(&mut self, c: A) {
        add_to(&mut self.constant, c);
    }

    fn word(&mut self, v: u32, c: &A) {
        if v == 0 {
            return;
        }
        if !self.words.contains_key(&v) {
            let set = (0..32).filter(|j| v >> j & 1 == 1).map(|j| self.eq_j[j].clone());
            self.words.insert(v, set.reduce(|s, x| s + x).expect("a bit set").kept());
        }
        self.constant(c.clone() * self.words[&v].clone());
    }

    fn term(&mut self, t: &Term, c: &A, public: &Public<A>) {
        if t.from == Source::Public {
            self.word(t.of(public.word(t.col as usize)), c);
        }
    }

    fn sum(&mut self, sum: &Sum, weight: &A, public: &Public<A>) {
        if let Some(known) = public.known(sum, weight) {
            self.constant(weight.clone() * known);
        }
    }
}

/// The weights of a word's bits at a point, for one of the two
/// polynomials: what [`AtPoint`] needs of where a table is to be
/// evaluated. A point is the bit's place in its word (five variables),
/// then the word's place in its row.
struct Place<A> {
    /// `eq` at the point's part for the word, by word.
    eq_col: Vec<A>,
    /// For a shift and a rotation, the sum over an operand's places `j`
    /// of the check's weight of `j` times the point's weight of the bit
    /// of the word that place is: a term's whole part, but for its word
    /// and its operand. Made when first wanted.
    shift: Vec<Option<A>>,
    /// The value at the point of the table that weighs bit `b` of an
    /// element's word `w` as `x^(32 w + b)`, by `w`. Made when first
    /// wanted.
    element: [Option<A>; 4],
    /// A term's part with its word's, by word, then shift and rotation.
    /// Made when first wanted.
    terms: Vec<Option<A>>,
    /// `eq` at the point's part for the bit's place, by place.
    eq_bit: Vec<A>,
    eq_j: Vec<A>,
}

impl<A: Alg> Place<A> {
    fn new(eq_j: &[A], point: &[A]) -> Place<A> {
        let eq_col = eq_table_like(&point[LOG_W..], &point[0]);
        Place {
            terms: vec![None; if eq_j.is_empty() { 0 } else { eq_col.len() * 96 }],
            eq_col,
            shift: vec![None; 3 * 32],
            element: [None, None, None, None],
            eq_bit: eq_table(&point[..LOG_W]),
            eq_j: eq_j.to_vec(),
        }
    }

    /// The shifts' part, for the shift and rotation numbered `at`.
    fn shift(&mut self, at: usize) -> A {
        if self.shift[at].is_none() {
            let t =
                Term { col: 0, pre: [Pre::None, Pre::Shl, Pre::Shr][at / 32], rot: (at % 32) as u8, from: Source::Row };
            let parts = (0..self.eq_j.len())
                .filter_map(|j| source_bit(&t, j).map(|b| self.eq_j[j].clone() * self.eq_bit[b].clone()));
            self.shift[at] = Some(parts.reduce(|s, x| x + s).expect("an operand of 32 places").kept());
        }
        self.shift[at].clone().expect("made above")
    }

    fn term(&mut self, t: &Term) -> A {
        self.eq_col[t.col as usize].clone() * self.shift(t.pre as usize * 32 + t.rot as usize)
    }

    /// [`Place::term`], kept: a word comes into many operands the same
    /// way, and to a machine a value kept is added, not multiplied.
    fn kept(&mut self, t: &Term) -> A {
        let at = t.col as usize * 96 + t.pre as usize * 32 + t.rot as usize;
        if self.terms[at].is_none() {
            self.terms[at] = Some(self.term(t).kept());
        }
        self.terms[at].clone().expect("made above")
    }

    /// The value at the point of the table that an element is: bit `b`
    /// of it weighing `x^b`, times its constant.
    fn element(&mut self, t: &Element) -> A {
        let (col, bit, bits) = (t.col as usize, t.bit as usize, t.bits as usize);
        let lift = |c: F| self.eq_bit[0].lift(c);
        let sum = if bit == 0 && bits % 32 == 0 {
            // Whole words: a product a word.
            let mut sum = None;
            for w in 0..bits / 32 {
                if self.element[w].is_none() {
                    let parts = (0..32).map(|b| self.eq_bit[b].clone() * lift(F(1 << (32 * w + b))));
                    self.element[w] = parts.reduce(|s, x| x + s);
                }
                add_to(&mut sum, self.eq_col[col + w].clone() * self.element[w].clone().expect("made above"));
            }
            sum.expect("an element of a word at least")
        } else {
            let part = |b: usize| {
                let at = bit + b;
                self.eq_col[col + at / 32].clone() * self.eq_bit[at % 32].clone() * lift(F(1 << b))
            };
            (0..bits).map(part).reduce(|s, x| x + s).expect("an element of a bit at least")
        };
        if t.scale == F::ONE { sum } else { sum * lift(t.scale) }
    }
}

/// A check's tables at a point, without the tables: each table's value
/// at the point of its polynomial, a term at a time.
pub struct AtPoint<A> {
    /// Where the witness's tables are evaluated, and the program's.
    witness: Place<A>,
    program: Option<Place<A>>,
    pub row: Option<A>,
    pub prev: Option<A>,
    pub in_program: Option<A>,
    constant: Constant<A>,
}

impl<A: Alg> AtPoint<A> {
    pub fn new(eq_j: &[A], rho_e: &[A], rho_p: &[A]) -> AtPoint<A> {
        AtPoint {
            witness: Place::new(eq_j, rho_e),
            program: (!rho_p.is_empty()).then(|| Place::new(eq_j, rho_p)),
            row: None,
            prev: None,
            in_program: None,
            constant: Constant::new(eq_j),
        }
    }

    fn add(&mut self, from: Source, part: impl FnOnce(&mut Place<A>) -> A) {
        match from {
            Source::Row => add_to(&mut self.row, part(&mut self.witness)),
            Source::Prev => add_to(&mut self.prev, part(&mut self.witness)),
            Source::Program => {
                let x = part(self.program.as_mut().expect("a circuit with a program"));
                add_to(&mut self.in_program, x);
            }
            Source::Public => unreachable!("a public value is a constant"),
        }
    }
}

impl<A: Alg> Acc<A> for AtPoint<A> {
    fn eq_j(&self) -> &[A] {
        self.constant.eq_j()
    }

    fn constant(&mut self, c: A) {
        self.constant.constant(c);
    }

    fn word(&mut self, v: u32, c: &A) {
        self.constant.word(v, c);
    }

    fn term(&mut self, t: &Term, c: &A, public: &Public<A>) {
        if t.from == Source::Public {
            return self.constant.term(t, c, public);
        }
        self.add(t.from, |place| place.term(t) * c.clone());
    }

    /// The terms' parts summed for each table, then the operand's
    /// weight: a product an operand, not a term. To the machine a term
    /// is then an addend, half a row (grouping the terms that shift
    /// alike was tried and costs more: an operand's terms mostly shift
    /// each its own way).
    fn operand(&mut self, expr: &Expr, c: &A, public: &Public<A>) {
        self.word(expr.constant, c);
        let mut parts: [Option<A>; 3] = [None, None, None];
        for t in &expr.terms {
            match t.from {
                Source::Public => self.constant.term(t, c, public),
                Source::Row => add_to(&mut parts[0], self.witness.kept(t)),
                Source::Prev => add_to(&mut parts[1], self.witness.kept(t)),
                Source::Program => add_to(&mut parts[2], self.program.as_mut().expect("a program").kept(t)),
            }
        }
        for (part, from) in parts.into_iter().zip([Source::Row, Source::Prev, Source::Program]) {
            if let Some(part) = part {
                self.add(from, |_| part * c.clone());
            }
        }
    }

    fn sum(&mut self, sum: &Sum, weight: &A, public: &Public<A>) {
        self.constant.sum(sum, weight, public);
        for t in sum.terms.iter().filter(|t| t.from != Source::Public) {
            self.add(t.from, |place| place.element(t) * weight.clone());
        }
    }
}

/// A circuit's constraints, through an accumulator: the three operands
/// at a point whose part for the constraint's place in its row is
/// `rho_k`, batched as `A + lambda B + lambda^2 C`.
pub fn matrix<A: Alg>(acc: &mut impl Acc<A>, circuit: &Circuit, rho_k: &[A], lambda: &A, public: &Public<A>) {
    let eq_k = eq_table_like(rho_k, lambda);
    let scales = [lambda.lift(F::ONE), lambda.clone(), lambda.clone() * lambda.clone()];
    for (k, operands) in circuit.constraints.iter().enumerate() {
        for (expr, scale) in operands.iter().zip(&scales) {
            if expr.constant == 0 && expr.terms.is_empty() {
                continue;
            }
            let c = eq_k[k].clone() * scale.clone();
            acc.operand(expr, &c, public);
        }
    }
}

/// [`matrix`] for a circuit's multiplications: the three operands at a
/// point whose part for the multiplication's place in the row is
/// `rho_k`, batched with `lambda`.
pub(crate) fn product_matrix<A: Alg>(
    acc: &mut impl Acc<A>,
    circuit: &Circuit,
    rho_k: &[A],
    lambda: &A,
    public: &Public<A>,
) {
    let eq_k = eq_table_like(rho_k, lambda);
    let scales = [lambda.lift(F::ONE), lambda.clone(), lambda.clone() * lambda.clone()];
    for (k, operands) in circuit.products.iter().enumerate() {
        for (sum, scale) in operands.iter().zip(&scales) {
            if sum.terms.is_empty() && sum.constant == F::ZERO {
                continue;
            }
            acc.sum(sum, &(eq_k[k].clone() * scale.clone()), public);
        }
    }
}

/// The multiplications' check, as far as both sides know it once it is
/// done: its point, the three operands there, and the challenges that
/// batch the operands and weigh the whole against the constraints'.
#[derive(Clone)]
pub(crate) struct Products<A> {
    pub rho: Vec<A>,
    pub xyz: [A; 3],
    pub lambda: A,
    pub beta: A,
}

/// The bus's check, as far as both sides know it once it is done: the
/// point its grand products leave the fingerprints at, the two tables of
/// fingerprints there, and the challenges: those of the fingerprints,
/// the one that batches the two ways, and the one that weighs the whole
/// against the constraints'.
#[derive(Clone)]
pub(crate) struct Bus<A> {
    pub point: Vec<A>,
    pub values: [A; 2],
    pub gamma: A,
    pub alpha: A,
    pub kappa: A,
    pub beta: A,
}

/// [`matrix`] for a circuit's bus: the fingerprints of what a row
/// sends, and `kappa` times those of what it receives, at a point whose
/// part for the tuple's place in the row is the first of the bus's. A
/// tuple's fingerprint is `gamma` and its elements under the powers of
/// `alpha`; a place with no tuple is `gamma` alone.
pub(crate) fn bus_matrix<A: Alg>(acc: &mut impl Acc<A>, circuit: &Circuit, bus: &Bus<A>, public: &Public<A>) {
    let eq_slot = eq_table_like(&bus.point[..circuit.log_slots], &bus.gamma);
    let one = bus.gamma.lift(F::ONE);
    // The weights of the places come to one, each way.
    acc.constant(bus.gamma.clone() * (bus.kappa.clone() + one.clone()));
    for (tuples, side) in [(&circuit.sends, one), (&circuit.receives, bus.kappa.clone())] {
        for (tuple, slot) in tuples.iter().zip(&eq_slot) {
            let mut power = slot.clone() * side.clone();
            for sum in tuple {
                acc.sum(sum, &power, public);
                power = power * bus.alpha.clone();
            }
        }
    }
}

/// One check's part in what is left to show: its terms gone through an
/// accumulator, the part of its point that is a row, how the whole is
/// weighed, and the value the check ended at.
pub(crate) struct Group<A, C> {
    pub acc: C,
    pub point: Vec<A>,
    pub scale: A,
    pub value: A,
}

/// What a table's checks ended at.
#[derive(Clone)]
pub(crate) struct Ended<A> {
    pub rho: Vec<A>,
    pub abc: [A; 3],
    pub lambda: A,
    pub products: Option<Products<A>>,
    pub bus: Option<Bus<A>>,
}

/// Every check's [`Group`], in the order their claims are made in: the
/// constraints', the multiplications', the bus's. `make` makes a check's
/// accumulator from its weights of a word's places.
pub(crate) fn groups<A: Alg, C: Acc<A>>(
    circuit: &Circuit,
    public: &Public<A>,
    ended: &Ended<A>,
    make: impl Fn(&[A]) -> C,
    constraints: bool,
) -> Vec<Group<A, C>> {
    let lk = circuit.log_constraints;
    let (rho, lambda) = (&ended.rho, &ended.lambda);
    let batched = |v: &[A; 3], l: &A| (v[2].clone() * l.clone() + v[1].clone()) * l.clone() + v[0].clone();
    let mut out = Vec::with_capacity(3);
    if constraints {
        let mut acc = make(&eq_table(&rho[..LOG_W]));
        matrix(&mut acc, circuit, &rho[LOG_W..LOG_W + lk], lambda, public);
        out.push(Group {
            acc,
            point: rho[LOG_W + lk..].to_vec(),
            scale: lambda.lift(F::ONE),
            value: batched(&ended.abc, lambda),
        });
    }
    if let Some(p) = &ended.products {
        let lp = circuit.log_products;
        let mut acc = make(&[]);
        product_matrix(&mut acc, circuit, &p.rho[..lp], &p.lambda, public);
        out.push(Group { acc, point: p.rho[lp..].to_vec(), scale: p.beta.clone(), value: batched(&p.xyz, &p.lambda) });
    }
    if let Some(b) = &ended.bus {
        let mut acc = make(&[]);
        bus_matrix(&mut acc, circuit, b, public);
        let value = b.values[1].clone() * b.kappa.clone() + b.values[0].clone();
        out.push(Group { acc, point: b.point[circuit.log_slots..].to_vec(), scale: b.beta.clone(), value });
    }
    out
}

/// One sum over the words that a check leaves to be shown, as the
/// verifier holds it: `scale` times the sum over the rows of
/// `eq(point, row)`, or of `eq(point, .)` at the row after if `after`,
/// times the row's bits under a table: of its own words, or of its
/// program's if `program`.
#[derive(Clone)]
pub(crate) struct Claimed<A> {
    pub point: Vec<A>,
    pub after: bool,
    pub scale: A,
    pub program: bool,
}

impl<A: Alg> Claimed<A> {
    /// Its weights' value at `zeta`.
    pub fn weight_at(&self, zeta: &[A]) -> A {
        let at = if self.after { crate::alg::successor(zeta, &self.point) } else { crate::alg::eq(zeta, &self.point) };
        self.scale.clone() * at
    }
}

/// The claims a check makes, at the point's part for the rows: one for a
/// row's own words, one for the row before's, and with a program one for
/// its words.
pub(crate) fn claimed<A: Alg>(with_program: bool, point: &[A], scale: &A) -> Vec<Claimed<A>> {
    let at = |after: bool, program: bool| Claimed { point: point.to_vec(), after, scale: scale.clone(), program };
    let mut claims = vec![at(false, false), at(true, false)];
    if with_program {
        claims.push(at(false, true));
    }
    claims
}

/// What the verifier derives once a table's checks are done: the claims
/// they leave, and what the claims must sum to.
pub(crate) fn reduce_claims<A: Alg>(circuit: &Circuit, public: &Public<A>, ended: &Ended<A>) -> (Vec<Claimed<A>>, A) {
    let mut claims = Vec::new();
    let mut target: Option<A> = None;
    for g in groups(circuit, public, ended, |eq_j| Constant::new(eq_j), true) {
        let value = match g.acc.constant {
            Some(c) => g.value + c,
            None => g.value,
        };
        add_to(&mut target, g.scale.clone() * value);
        claims.extend(claimed(circuit.has_program(), &g.point, &g.scale));
    }
    (claims, target.expect("a table has its constraints' check at least"))
}

/// Whoever says what a circuit's constraints come to at a table's
/// points: for the words' tables of the row, of the row before, and of
/// the program. `rho` is the constraints' point less the rows' part.
pub trait Reader<A: Alg> {
    fn constraints(
        &mut self,
        circuit: &Circuit,
        public: &Public<A>,
        rho: &[A],
        lambda: &A,
        rho_e: &[A],
        rho_p: &[A],
    ) -> [Option<A>; 3];
}

/// Reads the circuit, a term at a time.
pub struct Direct;

impl<A: Alg> Reader<A> for Direct {
    fn constraints(
        &mut self,
        circuit: &Circuit,
        public: &Public<A>,
        rho: &[A],
        lambda: &A,
        rho_e: &[A],
        rho_p: &[A],
    ) -> [Option<A>; 3] {
        let mut acc = AtPoint::new(&eq_table(&rho[..LOG_W]), rho_e, rho_p);
        matrix(&mut acc, circuit, &rho[LOG_W..], lambda, public);
        [acc.row, acc.prev, acc.in_program]
    }
}

/// Each claim's table at the point of its polynomial, in the claims'
/// order: `rho_e` for the witness's words, `rho_p` for the program's. A
/// table with nothing in it is zero.
pub(crate) fn tables_at<A: Alg>(
    circuit: &Circuit,
    public: &Public<A>,
    ended: &Ended<A>,
    rho_e: &[A],
    rho_p: &[A],
    reader: &mut impl Reader<A>,
) -> Vec<A> {
    let zero = rho_e[0].lift(F::ZERO);
    let mut at = Vec::new();
    let mut push = |[row, prev, in_program]: [Option<A>; 3]| {
        at.extend([row, prev].map(|v| v.unwrap_or(zero.clone())));
        if circuit.has_program() {
            at.push(in_program.unwrap_or(zero.clone()));
        }
    };
    // The constraints' tables are the reader's to say; the
    // multiplications' and the bus's, few terms, are read here.
    let rho = &ended.rho[..LOG_W + circuit.log_constraints];
    push(reader.constraints(circuit, public, rho, &ended.lambda, rho_e, rho_p));
    let rest = Ended { rho: ended.rho.clone(), abc: ended.abc.clone(), lambda: ended.lambda.clone(), ..ended.clone() };
    for g in groups(circuit, public, &rest, |eq_j| AtPoint::new(eq_j, rho_e, rho_p), false) {
        push([g.acc.row, g.acc.prev, g.acc.in_program]);
    }
    at
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::LOG_PROGRAM_SHARE;
    use crate::sym::{Shared, Sym};
    use crate::test_util::Rng;
    use crate::{machine, recursion};

    /// What a table's checks might have ended at, for a circuit, and the
    /// points its tables would be wanted at.
    fn ended(circuit: &Circuit, rng: &mut Rng) -> (Ended<F>, Vec<F>, Vec<F>) {
        let rows = 9;
        let three = |rng: &mut Rng| [rng.f(), rng.f(), rng.f()];
        let products = (!circuit.products.is_empty()).then(|| Products {
            rho: rng.fs(circuit.log_products + rows),
            xyz: three(rng),
            lambda: rng.f(),
            beta: rng.f(),
        });
        let bus = circuit.has_bus().then(|| Bus {
            point: rng.fs(circuit.log_slots + rows),
            values: [rng.f(), rng.f()],
            gamma: rng.f(),
            alpha: rng.f(),
            kappa: rng.f(),
            beta: rng.f(),
        });
        let e = Ended {
            rho: rng.fs(LOG_W + circuit.log_constraints + rows),
            abc: three(rng),
            lambda: rng.f(),
            products,
            bus,
        };
        (e, rng.fs(LOG_W + circuit.log_cols), rng.fs(LOG_W + circuit.log_cols - LOG_PROGRAM_SHARE))
    }

    /// No public values read: the circuits here have none in what is
    /// counted.
    fn none<A>() -> Public<'static, A> {
        Public { words: &[0; 8], elements: None }
    }

    /// The same as values of the machine: every element an input.
    fn lifted(cx: &Shared, e: &Ended<F>) -> Ended<Sym> {
        let s = |x: &F| cx.input(*x);
        let v = |xs: &[F]| xs.iter().map(s).collect::<Vec<Sym>>();
        Ended {
            rho: v(&e.rho),
            abc: e.abc.each_ref().map(s),
            lambda: s(&e.lambda),
            products: e.products.as_ref().map(|p| Products {
                rho: v(&p.rho),
                xyz: p.xyz.each_ref().map(s),
                lambda: s(&p.lambda),
                beta: s(&p.beta),
            }),
            bus: e.bus.as_ref().map(|b| Bus {
                point: v(&b.point),
                values: b.values.each_ref().map(s),
                gamma: s(&b.gamma),
                alpha: s(&b.alpha),
                kappa: s(&b.kappa),
                beta: s(&b.beta),
            }),
        }
    }

    /// A circuit's tables at a point and its claims' sum, by the machine:
    /// the rows it took, and whether the values are the field's.
    fn compiled(circuit: &Circuit, seed: u64) -> (Shared, usize) {
        let mut rng = Rng(seed);
        let (e, rho_e, rho_p) = ended(circuit, &mut rng);
        let native = tables_at(circuit, &none(), &e, &rho_e, &rho_p, &mut Direct);
        let (_, target) = reduce_claims(circuit, &none(), &e);
        let cx = Shared::new();
        let se = lifted(&cx, &e);
        let (sr_e, sr_p): (Vec<Sym>, Vec<Sym>) =
            (rho_e.iter().map(|x| cx.input(*x)).collect(), rho_p.iter().map(|x| cx.input(*x)).collect());
        let before = cx.with(|c| c.asm.finish_len());
        let at = tables_at(circuit, &none(), &se, &sr_e, &sr_p, &mut Direct);
        let (claims, sum) = reduce_claims(circuit, &none(), &se);
        let rows = cx.with(|c| c.asm.finish_len()) - before;
        assert_eq!(at.iter().map(Sym::value).collect::<Vec<F>>(), native);
        assert_eq!((sum.value(), claims.len()), (target, native.len()));
        for (v, expect) in at.iter().zip(&native) {
            assert!(v.is(&cx.input(*expect)));
        }
        assert!(sum.is(&cx.input(target)));
        (cx, rows)
    }

    #[test]
    fn a_circuit_is_read_by_the_machine() {
        // The machine's own circuit: its tables at a point, computed by
        // rows of the machine and proven.
        let (cx, rows) = compiled(&machine::circuit(), 1);
        assert!(rows < 6000, "{rows} rows");
        assert!(crate::sym::tests::proven(cx).0);
    }

    /// What reading each of the verifier's two circuits costs the
    /// machine.
    #[test]
    #[ignore = "a count; run with --release --nocapture"]
    fn reading_costs() {
        for (name, circuit) in [("the machine", machine::circuit()), ("the hash table", recursion::circuit())] {
            let (cx, rows) = compiled(&circuit, 2);
            let copies = cx.finish().asm.finish(128).inputs.len();
            println!(
                "{name}: {} terms, {rows} operations, 2^{} rows with copies",
                circuit.terms(),
                copies.trailing_zeros()
            );
        }
    }
}
