//! Circuits of 32-bit words, a row a copy, and Blake3's compression as
//! one.
//!
//! A row is `2^log_cols` committed words. What a circuit says of them:
//!
//! - **Constraints** `A & B = C`, bit by bit, where each operand is the
//!   XOR of words, each rotated, some first shifted by one, and a
//!   constant ([`Expr`]). So XORs and rotations cost nothing: they are
//!   in how operands are written.
//! - **Multiplications** `x y = z` in the field, where each operand is a
//!   sum of elements, an element being up to four words side by side
//!   ([`Sum`]).
//! - **A bus**: tuples of elements a row sends and tuples it receives.
//!   Over all the rows, what is sent must be what is received.
//!
//! # Where a word comes from
//!
//! A term names a word by its place and its [`Source`]: the row, the row
//! before it (the last row is before the first), the program, or the
//! public values.
//!
//! - **The program** is words fixed with the circuit, a sixteenth as
//!   many a row as the row has of its own: the same for every proof,
//!   committed once ([`crate::argument::Program`]). They say what each
//!   row is for.
//! - **The public values** are the same in every row, and are the
//!   statement a proof is of.
//!
//! # What costs
//!
//! - **An addition** `x + y` commits its carries out, a word `k`. With
//!   `c = k << 1` the carries in, a bit's carry out is the majority of
//!   `x`, `y` and `c`, which is `((x ^ c) & (y ^ c)) ^ c`: the constraint
//!   `(x ^ c) & (y ^ c) = k ^ c`. The sum is `x ^ y ^ c`, an expression.
//! - **A checkpoint** commits a word `s` for an expression `x` grown
//!   long, with `(x ^ s) & 1..1 = 0`, and `s` stands for it afterwards.
//!
//! # Writing one
//!
//! A row is written once, against [`Ctx`], and run twice: by
//! [`Symbolic`] for its constraints, and by [`Concrete`] on a row's
//! inputs for its words and its operands' values. What a [`Ctx`] cannot
//! say (terms of the row before, multiplications, the bus) is added to
//! the [`Symbolic`] afterwards, and its values are worked out from the
//! words ([`Witness::new`]).

use crate::blake3::{IV, QUARTERS, SCHEDULE};
use crate::field::F;
use crate::parallel::{par_chunks_mut, par_for_each};

/// What is done to a word before it is rotated.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Pre {
    None,
    /// Shifted left by one.
    Shl,
    /// Shifted right by one.
    Shr,
}

/// Where a term's word is.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Source {
    /// The row's own committed words.
    Row,
    /// The committed words of the row before.
    Prev,
    /// The row's program words.
    Program,
    /// The public values.
    Public,
}

/// The words a row's terms speak of.
#[derive(Clone, Copy)]
pub struct Words<'a> {
    pub row: &'a [u32],
    pub prev: &'a [u32],
    pub program: &'a [u32],
    pub public: &'a [u32],
}

impl<'a> Words<'a> {
    pub fn of(&self, from: Source) -> &'a [u32] {
        match from {
            Source::Row => self.row,
            Source::Prev => self.prev,
            Source::Program => self.program,
            Source::Public => self.public,
        }
    }
}

/// The word `col` of `from`, shifted as `pre` says and rotated right by
/// `rot`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Term {
    pub col: u16,
    pub pre: Pre,
    pub rot: u8,
    pub from: Source,
}

impl Term {
    /// Its value for the word `w`.
    pub fn of(&self, w: u32) -> u32 {
        let w = match self.pre {
            Pre::None => w,
            Pre::Shl => w << 1,
            Pre::Shr => w >> 1,
        };
        w.rotate_right(self.rot as u32)
    }
}

/// The XOR of its terms, in order and each once, and a constant.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct Expr {
    pub terms: Vec<Term>,
    pub constant: u32,
}

impl Expr {
    /// Its value on a row's words.
    pub fn eval(&self, w: &Words) -> u32 {
        self.terms.iter().fold(self.constant, |acc, t| acc ^ t.of(w.of(t.from)[t.col as usize]))
    }

    pub fn constant(c: u32) -> Expr {
        Expr { terms: vec![], constant: c }
    }

    pub fn xor(&self, other: &Expr) -> Expr {
        xor(self, other)
    }

    /// The same of the row before: for an expression of the row's own
    /// words.
    pub fn prev(&self) -> Expr {
        assert!(self.constant == 0 && self.terms.iter().all(|t| t.from == Source::Row));
        Expr { terms: self.terms.iter().map(|t| Term { from: Source::Prev, ..*t }).collect(), constant: 0 }
    }

    /// A word shifted right by one.
    pub fn shr(&self) -> Expr {
        assert!(self.terms.len() == 1 && self.terms[0].pre == Pre::None && self.terms[0].rot == 0);
        Expr { terms: vec![Term { pre: Pre::Shr, ..self.terms[0] }], constant: 0 }
    }

    /// The one word this is, if it is a word as it lies.
    fn plain(&self) -> Option<Term> {
        match self.terms[..] {
            [t] if self.constant == 0 && t.pre == Pre::None && t.rot == 0 => Some(t),
            _ => None,
        }
    }
}

/// Bits of words side by side, as an element of the field, times a
/// constant: the `bits` bits from bit `bit` of the word `col` on, running
/// into the words after it, 128 at most. Bit `bit` is the element's
/// lowest. Whole words, four of them, are an element as it is committed;
/// one bit is a flag or a digit of an index.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Element {
    pub col: u16,
    pub from: Source,
    pub bit: u8,
    pub bits: u8,
    pub scale: F,
}

impl Element {
    /// Its value among the words of its source.
    pub fn of(&self, words: &[u32]) -> F {
        let (bit, bits) = (self.bit as usize, self.bits as usize);
        let mut x = 0u128;
        for b in 0..bits {
            let at = bit + b;
            x |= ((words[self.col as usize + at / 32] >> (at % 32)) as u128 & 1) << b;
        }
        self.scale * F(x)
    }
}

/// An operand of a multiplication, or an entry of a tuple: the sum of
/// its elements and a constant.
#[derive(Clone, Default, Debug, PartialEq)]
pub struct Sum {
    pub terms: Vec<Element>,
    pub constant: F,
}

impl Sum {
    /// The element whose words are `words`, low word first: one to four
    /// words as they lie, one after another in one source.
    pub fn element(words: &[Expr]) -> Sum {
        assert!((1..=4).contains(&words.len()));
        let first = words[0].plain().expect("an element is words as they lie");
        for (i, w) in words.iter().enumerate() {
            assert_eq!(w.plain(), Some(Term { col: first.col + i as u16, ..first }), "an element's words are in a row");
        }
        let whole = Element { col: first.col, from: first.from, bit: 0, bits: 32 * words.len() as u8, scale: F::ONE };
        Sum { terms: vec![whole], constant: F::ZERO }
    }

    /// The `bits` bits of a word from bit `bit` on, as an element: a
    /// digit, or with one bit a flag.
    pub fn bits(word: &Expr, bit: usize, bits: usize) -> Sum {
        assert!(bit + bits <= 32 && bits > 0);
        let mut sum = Sum::word(word);
        (sum.terms[0].bit, sum.terms[0].bits) = (bit as u8, bits as u8);
        sum
    }

    /// A field of `bits` bits that begins `offset` bits into the words
    /// from `first` on, and may run across them: an address in a
    /// program's words, say.
    pub fn field(first: &Expr, offset: usize, bits: usize) -> Sum {
        assert!((1..=128).contains(&bits));
        let mut sum = Sum::word(first);
        let t = &mut sum.terms[0];
        (t.col, t.bit, t.bits) = (t.col + (offset / 32) as u16, (offset % 32) as u8, bits as u8);
        sum
    }

    /// The sum times a constant: a linear map costs nothing.
    pub fn scaled(&self, c: F) -> Sum {
        let terms = self.terms.iter().map(|t| Element { scale: t.scale * c, ..*t }).collect();
        Sum { terms, constant: self.constant * c }
    }

    /// One word as an element: its 32 bits, the rest zero.
    pub fn word(word: &Expr) -> Sum {
        Sum::element(std::slice::from_ref(word))
    }

    pub fn constant(c: F) -> Sum {
        Sum { terms: vec![], constant: c }
    }

    pub fn add(&self, other: &Sum) -> Sum {
        Sum { terms: [&self.terms[..], &other.terms[..]].concat(), constant: self.constant + other.constant }
    }

    /// The same of the row before: for a sum of the row's own elements.
    pub fn prev(&self) -> Sum {
        assert!(self.constant == F::ZERO && self.terms.iter().all(|t| t.from == Source::Row));
        Sum { terms: self.terms.iter().map(|t| Element { from: Source::Prev, ..*t }).collect(), constant: F::ZERO }
    }

    /// Its value on a row's words.
    pub fn eval(&self, w: &Words) -> F {
        self.terms.iter().fold(self.constant, |acc, t| acc + t.of(w.of(t.from)))
    }
}

pub trait Ctx {
    type V: Clone;
    /// The next input of the row, a committed word.
    fn input(&mut self) -> Self::V;
    /// The next word of the row's program.
    fn program(&mut self) -> Self::V;
    /// The next public value.
    fn public(&mut self) -> Self::V;
    fn constant(&mut self, c: u32) -> Self::V;
    fn xor(&mut self, x: &Self::V, y: &Self::V) -> Self::V;
    fn rotr(&mut self, x: &Self::V, n: u32) -> Self::V;
    fn add(&mut self, x: &Self::V, y: &Self::V) -> Self::V;
    fn checkpoint(&mut self, x: &Self::V) -> Self::V;
}

#[derive(Default)]
pub struct Symbolic {
    pub cols: usize,
    pub program_cols: usize,
    pub publics: usize,
    pub constraints: Vec<[Expr; 3]>,
    pub products: Vec<[Sum; 3]>,
    pub sends: Vec<Vec<Sum>>,
    pub receives: Vec<Vec<Sum>>,
}

fn word(col: usize, from: Source) -> Expr {
    Expr { terms: vec![Term { col: col as u16, pre: Pre::None, rot: 0, from }], constant: 0 }
}

impl Symbolic {
    fn col(&mut self) -> Expr {
        self.cols += 1;
        word(self.cols - 1, Source::Row)
    }

    /// `a & b = c`, of expressions a [`Ctx`] cannot write: those of the
    /// row before.
    pub fn constrain(&mut self, a: Expr, b: Expr, c: Expr) {
        self.constraints.push([a, b, c]);
    }

    /// `x = 0` wherever `mask` is set.
    pub fn zero_where(&mut self, mask: &Expr, x: Expr) {
        self.constrain(x, mask.clone(), Expr::default());
    }

    /// `x y = z` in the field.
    pub fn product(&mut self, x: Sum, y: Sum, z: Sum) {
        self.products.push([x, y, z]);
    }

    /// The row puts `tuple` on the bus.
    pub fn send(&mut self, tuple: Vec<Sum>) {
        self.sends.push(tuple);
    }

    /// The row takes `tuple` off the bus.
    pub fn receive(&mut self, tuple: Vec<Sum>) {
        self.receives.push(tuple);
    }
}

fn xor(x: &Expr, y: &Expr) -> Expr {
    // Both in order: a term in both cancels.
    let mut terms = Vec::with_capacity(x.terms.len() + y.terms.len());
    let (mut i, mut j) = (0, 0);
    while i < x.terms.len() && j < y.terms.len() {
        match x.terms[i].cmp(&y.terms[j]) {
            std::cmp::Ordering::Less => {
                terms.push(x.terms[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                terms.push(y.terms[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
    }
    terms.extend_from_slice(&x.terms[i..]);
    terms.extend_from_slice(&y.terms[j..]);
    Expr { terms, constant: x.constant ^ y.constant }
}

impl Ctx for Symbolic {
    type V = Expr;

    fn input(&mut self) -> Expr {
        self.col()
    }

    fn program(&mut self) -> Expr {
        self.program_cols += 1;
        word(self.program_cols - 1, Source::Program)
    }

    fn public(&mut self) -> Expr {
        self.publics += 1;
        word(self.publics - 1, Source::Public)
    }

    fn constant(&mut self, c: u32) -> Expr {
        Expr { terms: vec![], constant: c }
    }

    fn xor(&mut self, x: &Expr, y: &Expr) -> Expr {
        xor(x, y)
    }

    fn rotr(&mut self, x: &Expr, n: u32) -> Expr {
        let mut terms: Vec<Term> =
            x.terms.iter().map(|t| Term { rot: ((t.rot as u32 + n) % 32) as u8, ..*t }).collect();
        terms.sort_unstable();
        Expr { terms, constant: x.constant.rotate_right(n) }
    }

    fn add(&mut self, x: &Expr, y: &Expr) -> Expr {
        let out = self.col();
        let carry_in = Expr { terms: vec![Term { pre: Pre::Shl, ..out.terms[0] }], constant: 0 };
        self.constraints.push([xor(x, &carry_in), xor(y, &carry_in), xor(&out, &carry_in)]);
        xor(&xor(x, y), &carry_in)
    }

    fn checkpoint(&mut self, x: &Expr) -> Expr {
        let s = self.col();
        self.constraints.push([xor(x, &s), Expr { terms: vec![], constant: !0 }, Expr::default()]);
        s
    }
}

/// A row being filled: its words, and each constraint's operands.
pub struct Concrete<'a> {
    inputs: &'a [u32],
    program: &'a [u32],
    public: &'a [u32],
    words: &'a mut [u32],
    a: &'a mut [u32],
    b: &'a mut [u32],
    c: &'a mut [u32],
    next: [usize; 3],
    cols: usize,
    constraints: usize,
}

impl<'a> Concrete<'a> {
    /// A row with these inputs, program words and public values, to be
    /// written into `words` and the operands `a`, `b`, `c`.
    pub fn new(
        inputs: &'a [u32],
        program: &'a [u32],
        public: &'a [u32],
        words: &'a mut [u32],
        [a, b, c]: [&'a mut [u32]; 3],
    ) -> Self {
        Concrete { inputs, program, public, words, a, b, c, next: [0; 3], cols: 0, constraints: 0 }
    }

    fn word(&mut self, w: u32) {
        self.words[self.cols] = w;
        self.cols += 1;
    }

    fn constraint(&mut self, a: u32, b: u32, c: u32) {
        (self.a[self.constraints], self.b[self.constraints], self.c[self.constraints]) = (a, b, c);
        self.constraints += 1;
    }

    fn take(&mut self, which: usize) -> u32 {
        let from = [self.inputs, self.program, self.public][which];
        self.next[which] += 1;
        from[self.next[which] - 1]
    }
}

impl Ctx for Concrete<'_> {
    type V = u32;

    fn input(&mut self) -> u32 {
        let w = self.take(0);
        self.word(w);
        w
    }

    fn program(&mut self) -> u32 {
        self.take(1)
    }

    fn public(&mut self) -> u32 {
        self.take(2)
    }

    fn constant(&mut self, c: u32) -> u32 {
        c
    }

    fn xor(&mut self, x: &u32, y: &u32) -> u32 {
        x ^ y
    }

    fn rotr(&mut self, x: &u32, n: u32) -> u32 {
        x.rotate_right(n)
    }

    fn add(&mut self, x: &u32, y: &u32) -> u32 {
        let sum = x.wrapping_add(*y);
        let carry_in = x ^ y ^ sum;
        let carry_out = (x & y) | ((x ^ y) & carry_in);
        self.word(carry_out);
        self.constraint(x ^ carry_in, y ^ carry_in, carry_out ^ carry_in);
        sum
    }

    fn checkpoint(&mut self, x: &u32) -> u32 {
        self.word(*x);
        self.constraint(0, !0, 0);
        *x
    }
}

/// A row's program is a sixteenth of its own words: what the opening of
/// its polynomial joining the opening asks ([`crate::pcs::Joiner`]).
pub const LOG_PROGRAM_SHARE: usize = 4;

pub struct Circuit {
    /// Inputs a row takes.
    pub inputs: usize,
    /// Words, program words and public values a row has, before rounding
    /// up.
    pub cols: usize,
    pub program_cols: usize,
    pub publics: usize,
    pub constraints: Vec<[Expr; 3]>,
    /// How many of the constraints, the first, are those the row's
    /// [`Ctx`] made: a [`Concrete`] fills their operands as it runs, and
    /// the rest are worked out from the words.
    pub core: usize,
    /// The multiplications of a row, each `x y = z` in the field.
    pub products: Vec<[Sum; 3]>,
    /// What a row puts on the bus and what it takes off it, a tuple of
    /// field elements each: over all the rows, the tuples sent must be
    /// the tuples received, as many times each ([`crate::argument`]).
    pub sends: Vec<Vec<Sum>>,
    pub receives: Vec<Vec<Sum>>,
    /// A row is `2^log_cols` words, `2^log_constraints` constraints,
    /// `2^log_products` multiplications and `2^log_slots` tuples each
    /// way, those past the circuit's own all zero.
    pub log_cols: usize,
    pub log_constraints: usize,
    pub log_products: usize,
    pub log_slots: usize,
}

impl Circuit {
    /// The circuit of a row: `row` runs it against the [`Ctx`], then adds
    /// what a [`Ctx`] cannot say, and returns how many constraints the
    /// [`Ctx`] made.
    pub fn new(row: impl Fn(&mut Symbolic) -> usize, inputs: usize) -> Circuit {
        let mut s = Symbolic::default();
        let core = row(&mut s);
        let log = |n: usize| n.next_power_of_two().trailing_zeros() as usize;
        let mut log_cols = log(s.cols);
        // A row is wide enough for its program to be a sixteenth of it.
        if s.program_cols > 0 {
            log_cols = log_cols.max(log(s.program_cols) + LOG_PROGRAM_SHARE);
        }
        Circuit {
            inputs,
            cols: s.cols,
            program_cols: s.program_cols,
            publics: s.publics,
            core,
            log_cols,
            log_constraints: log(s.constraints.len()).max(2),
            log_products: log(s.products.len()),
            log_slots: log(s.sends.len().max(s.receives.len())),
            constraints: s.constraints,
            products: s.products,
            sends: s.sends,
            receives: s.receives,
        }
    }

    /// Whether a row sends or receives anything.
    pub fn has_bus(&self) -> bool {
        !self.sends.is_empty() || !self.receives.is_empty()
    }

    pub fn has_program(&self) -> bool {
        self.program_cols > 0
    }

    /// Program words a row has room for: what a program is laid out in.
    pub fn program_width(&self) -> usize {
        1 << (self.log_cols - LOG_PROGRAM_SHARE)
    }

    /// Terms in all operands: what working out the constraints' part of
    /// a verifier's check is proportional to.
    pub fn terms(&self) -> usize {
        self.constraints.iter().flatten().map(|e| e.terms.len()).sum()
    }

    /// The words row `i` of `rows` speaks of.
    pub fn words<'a>(&self, words: &'a [u32], fixed: &Fixed<'a>, i: usize, rows: usize) -> Words<'a> {
        let wc = 1 << self.log_cols;
        let before = (i + rows - 1) % rows;
        let pw = self.program_width();
        Words {
            row: &words[i * wc..(i + 1) * wc],
            prev: &words[before * wc..(before + 1) * wc],
            program: if self.has_program() { &fixed.program[i * pw..(i + 1) * pw] } else { &[] },
            public: fixed.public,
        }
    }
}

/// What a proof's witness is made against: the program, row after row
/// in [`Circuit::program_width`] words each, and the public values.
/// Empty for a circuit with neither.
#[derive(Clone, Copy, Default)]
pub struct Fixed<'a> {
    pub program: &'a [u32],
    pub public: &'a [u32],
}

/// The words of every row, row after row, and the operands of every
/// constraint the same way.
pub struct Witness {
    pub rows: usize,
    pub words: Vec<u32>,
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    pub c: Vec<u32>,
    /// The operands of every multiplication, row after row; empty for a
    /// circuit with none.
    pub x: Vec<F>,
    pub y: Vec<F>,
    pub z: Vec<F>,
}

impl Witness {
    /// `rows` rows of `circuit`, row `i` run by `row` on `inputs(i)`.
    pub fn new<const N: usize>(
        circuit: &Circuit,
        rows: usize,
        row: impl Fn(&mut Concrete) + Sync,
        inputs: impl Fn(usize) -> [u32; N] + Sync,
        fixed: &Fixed,
    ) -> Witness {
        assert!(rows.is_power_of_two() && N == circuit.inputs);
        assert_eq!(fixed.public.len(), circuit.publics);
        let (wc, kc, pw) = (1 << circuit.log_cols, 1 << circuit.log_constraints, circuit.program_width());
        assert_eq!(fixed.program.len(), if circuit.has_program() { rows * pw } else { 0 });
        let mut w = Witness {
            rows,
            words: vec![0; rows * wc],
            a: vec![0; rows * kc],
            b: vec![0; rows * kc],
            c: vec![0; rows * kc],
            x: Vec::new(),
            y: Vec::new(),
            z: Vec::new(),
        };
        const CHUNK: usize = 64;
        let pieces = w
            .words
            .chunks_mut(CHUNK * wc)
            .zip(w.a.chunks_mut(CHUNK * kc))
            .zip(w.b.chunks_mut(CHUNK * kc))
            .zip(w.c.chunks_mut(CHUNK * kc))
            .enumerate();
        par_for_each(pieces, |(i, (((words, a), b), c))| {
            let pieces = words.chunks_mut(wc).zip(a.chunks_mut(kc)).zip(b.chunks_mut(kc)).zip(c.chunks_mut(kc));
            for (j, (((words, a), b), c)) in pieces.enumerate() {
                let at = i * CHUNK + j;
                let inputs = inputs(at);
                let program = if circuit.has_program() { &fixed.program[at * pw..(at + 1) * pw] } else { &[] };
                row(&mut Concrete::new(&inputs, program, fixed.public, words, [a, b, c]));
            }
        });
        // The constraints the Ctx did not make, from the words.
        if circuit.core < circuit.constraints.len() {
            let words = &w.words;
            let pieces = w.a.chunks_mut(kc).zip(w.b.chunks_mut(kc)).zip(w.c.chunks_mut(kc)).enumerate();
            par_for_each(pieces, |(i, ((a, b), c))| {
                let at = circuit.words(words, fixed, i, rows);
                for (k, [ea, eb, ec]) in circuit.constraints.iter().enumerate().skip(circuit.core) {
                    (a[k], b[k], c[k]) = (ea.eval(&at), eb.eval(&at), ec.eval(&at));
                }
            });
        }
        if !circuit.products.is_empty() {
            let pc = 1 << circuit.log_products;
            let words = &w.words;
            let operand = |which: usize| {
                let mut out = vec![F::ZERO; rows * pc];
                par_chunks_mut(&mut out, pc, |i, o| {
                    let at = circuit.words(words, fixed, i, rows);
                    for (x, p) in o.iter_mut().zip(&circuit.products) {
                        *x = p[which].eval(&at);
                    }
                });
                out
            };
            (w.x, w.y, w.z) = (operand(0), operand(1), operand(2));
        }
        w
    }

    /// Whether every constraint and every multiplication holds: what a
    /// proof of this witness will show, known beforehand.
    pub fn holds(&self) -> bool {
        (0..self.a.len()).all(|i| self.a[i] & self.b[i] == self.c[i])
            && (0..self.x.len()).all(|i| self.x[i] * self.y[i] == self.z[i])
    }
}

/// Tests: the words of a witness that hold up nothing. Each word of the
/// rows `tried` (a word a row, of the circuit's own: what a prover is
/// free to write) has one bit changed, `bit(row, word)` of it, and every
/// constraint and multiplication of that row and of the row after is
/// held to what results: the row and word of each change that all of
/// them still take. A word that can be changed so says nothing the
/// circuit hears, on that row at the least; whether that is as meant
/// (a word a kind of row has no use for) is for whoever reads the list.
#[cfg(test)]
pub(crate) fn freedoms(
    circuit: &Circuit,
    witness: &Witness,
    fixed: &Fixed,
    tried: &[usize],
    bit: impl Fn(usize, usize) -> u32,
) -> Vec<(usize, usize)> {
    let (rows, wc) = (witness.rows, 1usize << circuit.log_cols);
    let mut words = witness.words.clone();
    let holds = |words: &[u32], i: usize| {
        let at = circuit.words(words, fixed, i, rows);
        circuit.constraints.iter().all(|[a, b, c]| a.eval(&at) & b.eval(&at) == c.eval(&at))
            && circuit.products.iter().all(|[x, y, z]| x.eval(&at) * y.eval(&at) == z.eval(&at))
    };
    let mut free = Vec::new();
    for &i in tried {
        assert!(holds(&words, i) && holds(&words, (i + 1) % rows), "row {i} of a witness that does not hold");
        for col in 0..circuit.cols {
            words[i * wc + col] ^= 1 << (bit(i, col) % 32);
            if holds(&words, i) && holds(&words, (i + 1) % rows) {
                free.push((i, col));
            }
            words[i * wc + col] ^= 1 << (bit(i, col) % 32);
        }
    }
    free
}

/// Inputs of [`compress_row`]: the chaining value, the block, and the
/// counter's two words, the block's length and the flags.
pub const COMPRESS_INPUTS: usize = 28;

/// A compression's words that other constraints speak of.
pub struct Compression<V> {
    pub cv: [V; 8],
    pub m: [V; 16],
    /// The counter's two words, the block's length, the flags.
    pub t: [V; 4],
    pub out: [V; 8],
}

/// One Blake3 compression: its inputs and the eight words of its output,
/// each a committed word. The state is checkpointed after every round.
pub fn compress_row<C: Ctx>(c: &mut C) -> Compression<C::V> {
    let cv: [C::V; 8] = std::array::from_fn(|_| c.input());
    let m: [C::V; 16] = std::array::from_fn(|_| c.input());
    let t: [C::V; 4] = std::array::from_fn(|_| c.input());
    compress(c, cv, m, t)
}

/// One Blake3 compression of values already at hand: the chaining value
/// and the block as committed words or as expressions of them, and the
/// counter, length and flags, which a program may give.
pub fn compress<C: Ctx>(c: &mut C, cv: [C::V; 8], m: [C::V; 16], t: [C::V; 4]) -> Compression<C::V> {
    let mut v: Vec<C::V> = cv.to_vec();
    for iv in &IV[..4] {
        v.push(c.constant(*iv));
    }
    v.extend(t.clone());
    for s in &SCHEDULE {
        for (q, [ia, ib, ic, id]) in QUARTERS.iter().copied().enumerate() {
            for (mi, r1, r2) in [(s[2 * q], 16, 12), (s[2 * q + 1], 8, 7)] {
                let sum = c.add(&v[ia], &v[ib]);
                v[ia] = c.add(&sum, &m[mi]);
                let x = c.xor(&v[id], &v[ia]);
                v[id] = c.rotr(&x, r1);
                v[ic] = c.add(&v[ic], &v[id]);
                let x = c.xor(&v[ib], &v[ic]);
                v[ib] = c.rotr(&x, r2);
            }
        }
        for x in v.iter_mut() {
            *x = c.checkpoint(x);
        }
    }
    let out = std::array::from_fn(|i| {
        let x = c.xor(&v[i], &v[i + 8]);
        c.checkpoint(&x)
    });
    Compression { cv, m, t, out }
}

pub fn blake3_circuit() -> Circuit {
    Circuit::new(
        |s| {
            compress_row(s);
            s.constraints.len()
        },
        COMPRESS_INPUTS,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    fn inputs(seed: u64) -> [u32; COMPRESS_INPUTS] {
        let mut rng = Rng(seed + 1);
        std::array::from_fn(|_| rng.next_u64() as u32)
    }

    #[test]
    fn the_row_is_the_compression() {
        let circuit = blake3_circuit();
        assert_eq!((circuit.cols, circuit.constraints.len()), (28 + 336 + 112 + 8, 336 + 112 + 8));
        assert_eq!((circuit.log_cols, circuit.log_constraints), (9, 9));
        assert!(!circuit.has_program() && !circuit.has_bus() && circuit.products.is_empty());
        for seed in 0..20 {
            let mut inp = inputs(seed);
            if seed == 0 {
                // A counter of zero and a whole block: the hash's own.
                inp[24..].copy_from_slice(&[0, 0, 64, 11]);
            }
            let (mut words, mut a, mut b, mut c) = ([0u32; 512], [0u32; 512], [0u32; 512], [0u32; 512]);
            let out = compress_row(&mut Concrete::new(&inp, &[], &[], &mut words, [&mut a, &mut b, &mut c])).out;
            let cv: [u32; 8] = inp[..8].try_into().unwrap();
            let m: [u32; 16] = inp[8..24].try_into().unwrap();
            let counter = inp[24] as u64 | (inp[25] as u64) << 32;
            assert_eq!(out, crate::blake3::compress(&cv, &m, counter, inp[26], inp[27]));
        }
    }

    #[test]
    fn the_operands_are_the_expressions_and_the_constraints_hold() {
        let circuit = blake3_circuit();
        let fixed = Fixed::default();
        let w = Witness::new(&circuit, 128, |c| _ = compress_row(c), |i| inputs(i as u64), &fixed);
        assert!(w.holds());
        for row in [0, 1, 77, 127] {
            let at = circuit.words(&w.words, &fixed, row, 128);
            for (k, [a, b, c]) in circuit.constraints.iter().enumerate() {
                let i = row * 512 + k;
                assert_eq!((a.eval(&at), b.eval(&at), c.eval(&at)), (w.a[i], w.b[i], w.c[i]));
            }
        }
    }

    #[test]
    fn an_element_is_bits_under_a_constant() {
        let words = [0x8000_0001u32, 0xFFFF_0000, 0x1234_5678, 0x9ABC_DEF0, 0x0F0F_0F0F];
        let w: Vec<Expr> = (0..5).map(|i| word(i, Source::Row)).collect();
        let at = |sum: &Sum| sum.eval(&Words { row: &words, prev: &[], program: &[], public: &[] });
        // Four words, low word first.
        assert_eq!(at(&Sum::element(&w[..4])), F(0x9ABC_DEF0_1234_5678_FFFF_0000_8000_0001));
        assert_eq!(at(&Sum::element(&w[1..3])), F(0x1234_5678_FFFF_0000));
        assert_eq!(at(&Sum::word(&w[4])), F(0x0F0F_0F0F));
        // Bits, from any place.
        assert_eq!(at(&Sum::bits(&w[0], 31, 1)), F::ONE);
        assert_eq!(at(&Sum::bits(&w[0], 1, 30)), F::ZERO);
        assert_eq!(at(&Sum::bits(&w[2], 4, 8)), F(0x67));
        // A constant times it, and sums of such.
        let c = F(0xABCD << 90);
        assert_eq!(at(&Sum::bits(&w[2], 4, 8).scaled(c)), c * F(0x67));
        let sum = Sum::word(&w[4]).scaled(c).add(&Sum::constant(F(5))).scaled(c);
        assert_eq!(at(&sum), c * (c * F(0x0F0F_0F0F) + F(5)));
    }

    #[test]
    fn a_term_finds_its_word() {
        // A row that reads every source: a committed word, the same of
        // the row before, a program word, a public value.
        let circuit = Circuit::new(
            |s| {
                let x = s.input();
                let (p, q) = (s.program(), s.public());
                let core = s.constraints.len();
                let ones = Expr::constant(!0);
                // x ^ x of the row before ^ program ^ public = 0.
                s.zero_where(&ones, x.xor(&x.prev()).xor(&p).xor(&q));
                s.product(Sum::word(&p), Sum::word(&q), Sum::word(&x).add(&Sum::word(&x).prev()));
                core
            },
            1,
        );
        assert_eq!((circuit.program_cols, circuit.publics, circuit.log_cols, circuit.program_width()), (1, 1, 4, 1));
        let rows = 128;
        let public = [0x5555_0000u32];
        // x_i = x_(i-1) ^ program_i ^ public, around the ring: the
        // program words must come to as many publics as rows, an even
        // number, so to zero.
        let mut program: Vec<u32> = (0..rows as u32).map(|i| i.wrapping_mul(0x9E37_79B9)).collect();
        program[0] = program[1..].iter().fold(0, |a, b| a ^ b);
        let mut xs = vec![0u32; rows];
        for i in 1..rows {
            xs[i] = xs[i - 1] ^ program[i] ^ public[0];
        }
        assert_eq!(xs[0], xs[rows - 1] ^ program[0] ^ public[0]);
        let fixed = Fixed { program: &program, public: &public };
        let w = Witness::new(&circuit, rows, |c| _ = (c.input(), c.program(), c.public()), |i| [xs[i]], &fixed);
        assert!((0..w.a.len()).all(|i| w.a[i] & w.b[i] == w.c[i]));
        // The multiplication is of the program word and the public
        // value, and is not their XOR: it does not hold, and says so.
        assert_eq!(w.x[5], F(program[5] as u128));
        assert_eq!(w.y[5], F(public[0] as u128));
        assert_eq!(w.z[5], F((xs[5] ^ xs[4]) as u128));
        assert!(!w.holds());
    }
}
