//! The arithmetic of a verifier, as rows of a circuit: a machine whose
//! every row is one operation on field elements.
//!
//! ```text
//! out = (a + d) b + c
//! ```
//!
//! A row's operands are values other rows made. It does not say which
//! by where they lie but by address, on the bus ([`crate::argument`]):
//! a row sends its result under its own address, and receives each
//! operand under the address its program names. So what a row computes
//! with is what was computed, whichever rows those were, and the rows of
//! a computation may come in any order.
//!
//! # A row
//!
//! Its program is four words: the four operands' addresses, 24 bits
//! each, and flags.
//!
//! | flag | set, it says |
//! |---|---|
//! | `first` | the row's address is [`BASE`]; any other row's is one more than the last row's |
//! | `one` | `b` is one more than what was received for it: with no `b`, the row adds |
//! | `equal` | `out` is zero, and is not sent: `a + d = c` (with `one`), an assertion |
//! | `input` | `out` is what the prover says, and no more: a value from outside |
//! | `again`, seven of them | `out` is sent a second time, a third, and so on to an eighth: it has that many readers |
//! | `no a`, `no b`, `no c`, `no d` | the operand is not read, and is zero |
//! | `plus` | `out` is one more: the constant a computation most often adds |
//! | `public 0`, `public 1` | `a` is the circuit's first public element, or its second: what a proof of the computation is of |
//!
//! An address of zero is no address: an operand not read receives
//! nothing, and a result not sent sends nothing, the tuple of zeros that
//! the bus does not count. Nothing is ever sent under the address zero
//! with a value, so an operand whose address is zero is zero: the bus
//! says so, and the circuit need not.
//!
//! A result with more than eight readers is copied: a row that reads it
//! and sends it eight times ([`Assembly::finish`]).
//!
//! # Addresses
//!
//! The rows' own are [`BASE`] and up, below `2^23`. Addresses from
//! `2^23` to `2^24` are for values another table sends: what the hash
//! table read from a proof, and the challenges it made
//! ([`crate::recursion`]).
//!
//! # What the circuit is
//!
//! Field multiplications and nothing bitwise but the counter's addition:
//! each flag is a bit of the program that multiplies what it gates. The
//! circuit is the same for every row and small, some fifty terms, which
//! is what a verifier of it pays to read it.

use crate::circuit::{Circuit, Ctx, Sum, Symbolic};
use crate::field::F;

/// The first row's address. Zero is no address.
pub const BASE: u32 = 1;
/// Addresses from here on are other tables' to send under.
pub const OUTSIDE: u32 = 1 << 23;
/// Bits of an address.
const ADDRESS: usize = 24;

/// Times a row can send its result.
const SENDS: usize = 8;
/// Words a row takes as inputs: the four operands, the result and the
/// prover's value, the address, and the tuples it sends (an address,
/// and for all but the first the result again).
pub const INPUTS: usize = 26 + 5 * (SENDS - 1);
/// Words of program a row reads.
pub const PROGRAM: usize = 4;

const FIRST: u32 = 1 << 0;
const ONE: u32 = 1 << 1;
const EQUAL: u32 = 1 << 2;
const INPUT: u32 = 1 << 3;
const TWICE: u32 = 1 << 4;
const THRICE: u32 = 1 << 5;
/// The flag that operand `i` (of `a`, `b`, `c`, `d`) is not read.
const fn none(i: usize) -> u32 {
    1 << (6 + i)
}
const PLUS: u32 = 1 << 10;
const FOURTH: u32 = 1 << 11;
/// The flags that the result is sent again: a second time, a third, ..
const AGAIN: [u32; SENDS - 1] = [TWICE, THRICE, FOURTH, 1 << 14, 1 << 15, 1 << 16, 1 << 17];
/// The flag that `a` is public element `i`.
const fn public(i: usize) -> u32 {
    1 << (12 + i)
}
/// Public elements: a digest.
pub const PUBLIC: usize = 2;
/// The public values of a computation that names none.
pub const NO_PUBLIC: [u32; 4 * PUBLIC] = [0; 4 * PUBLIC];

/// A row against any [`Ctx`]: its words, in the order of [`INPUTS`], its
/// address's successor (a committed word the circuit makes), and its
/// program.
struct Row<V> {
    /// `a`, `b`, `c`, `d`, `out`, and the prover's value.
    elements: [[V; 4]; 6],
    address: V,
    next: V,
    /// The addresses the tuples are sent under, and the result as all
    /// but the first send it.
    sent: [V; SENDS],
    again: [[V; 4]; SENDS - 1],
    program: [V; 4],
    public: [[V; 4]; PUBLIC],
}

fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
    let elements = std::array::from_fn(|_| std::array::from_fn(|_| c.input()));
    let address = c.input();
    let one = c.constant(1);
    let sum = c.add(&address, &one);
    let next = c.checkpoint(&sum);
    let first = c.input();
    let rest: [(C::V, [C::V; 4]); SENDS - 1] = std::array::from_fn(|_| (c.input(), std::array::from_fn(|_| c.input())));
    let sent = std::array::from_fn(|i| if i == 0 { first.clone() } else { rest[i - 1].0.clone() });
    let again = std::array::from_fn(|i| rest[i].1.clone());
    Row {
        elements,
        address,
        next,
        sent,
        again,
        program: std::array::from_fn(|_| c.program()),
        public: std::array::from_fn(|_| std::array::from_fn(|_| c.public())),
    }
}

/// The machine's circuit.
pub fn circuit() -> Circuit {
    Circuit::new(
        |s: &mut Symbolic| {
            let r = row(s);
            let core = s.constraints.len();
            let [a, b, c, d, out, free] = r.elements.each_ref().map(|w| Sum::element(w));
            let flag = |bit: u32| Sum::bits(&r.program[3], bit.trailing_zeros() as usize, 1);
            let not = |f: &Sum| f.add(&Sum::constant(F::ONE));
            let zero = Sum::default();
            let address = Sum::word(&r.address);
            // The operation, and what the flags say of its result.
            s.product(a.add(&d), b.add(&flag(ONE)), out.add(&c).add(&free).add(&flag(PLUS)));
            s.product(out.clone(), flag(EQUAL), zero.clone());
            s.product(free, not(&flag(INPUT)), zero.clone());
            // The address: the base in the first row, the last row's
            // successor in every other.
            s.product(address.add(&Sum::constant(F(BASE as u128))), flag(FIRST), zero.clone());
            s.product(address.add(&Sum::word(&r.next).prev()), not(&flag(FIRST)), zero.clone());
            // What is sent: the result under the address, unless it is
            // an assertion's; and again, and a third time, if the flags
            // say so. A tuple not sent is zeros.
            let sent = r.sent.each_ref().map(Sum::word);
            let again = r.again.each_ref().map(|w| Sum::element(w));
            s.product(address.clone(), not(&flag(EQUAL)), sent[0].clone());
            for (i, bit) in AGAIN.into_iter().enumerate() {
                s.product(address.clone(), flag(bit), sent[i + 1].clone());
                s.product(out.clone(), flag(bit), again[i].clone());
            }
            s.send(vec![sent[0].clone(), out.clone()]);
            for i in 1..SENDS {
                s.send(vec![sent[i].clone(), again[i - 1].clone()]);
            }
            // What the proof is of: `a` is a public element where the
            // flags say so.
            for (i, element) in r.public.iter().enumerate() {
                s.product(a.add(&Sum::element(element)), flag(public(i)), zero.clone());
            }
            // What is received: each operand under its address. An
            // operand not read has the address zero, under which nothing
            // but zero is ever sent.
            for (i, operand) in [&a, &b, &c, &d].into_iter().enumerate() {
                s.receive(vec![Sum::field(&r.program[0], i * ADDRESS, ADDRESS), operand.clone()]);
            }
            core
        },
        INPUTS,
    )
}

/// A value of a computation being assembled.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Value(usize);

/// An operand: nothing, a value, or for `b` alone the constant one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Operand {
    None,
    Of(Value),
    One,
}

impl From<Value> for Operand {
    fn from(v: Value) -> Operand {
        Operand::Of(v)
    }
}

struct Op {
    /// `a`, `b`, `c`, `d`.
    operands: [Operand; 4],
    flags: u32,
    /// The address read, for a value another table sends.
    outside: u32,
    /// Whether another table reads the result.
    sent: bool,
    value: F,
}

/// A computation, as the operations of the machine, with the values it
/// has for the inputs it is being run on: what it is, its program, does
/// not depend on them.
#[derive(Default)]
pub struct Assembly {
    ops: Vec<Op>,
    /// What each row that reads another table's value reads.
    outside_value: std::collections::BTreeMap<usize, F>,
    /// The public elements, once a row has said what they are.
    public: [Option<F>; PUBLIC],
    /// Whether every row that names a public element agrees on it.
    disagree: bool,
}

impl Assembly {
    fn value(&self, o: Operand) -> F {
        match o {
            Operand::None => F::ZERO,
            Operand::Of(v) => self.ops[v.0].value,
            Operand::One => F::ONE,
        }
    }

    fn push(&mut self, operands: [Operand; 4], flags: u32, outside: u32, value: F) -> Value {
        assert!(!matches!(operands[0], Operand::One) && !matches!(operands[2], Operand::One));
        assert!(!matches!(operands[3], Operand::One), "only b is one for nothing");
        self.ops.push(Op { operands, flags, outside, sent: false, value });
        Value(self.ops.len() - 1)
    }

    /// `(a + d) b + c`.
    pub fn op(
        &mut self,
        a: impl Into<Operand>,
        d: impl Into<Operand>,
        b: impl Into<Operand>,
        c: impl Into<Operand>,
    ) -> Value {
        self.op_plus(a, d, b, c, false)
    }

    /// `(a + d) b + c`, and one more if `plus`.
    pub fn op_plus(
        &mut self,
        a: impl Into<Operand>,
        d: impl Into<Operand>,
        b: impl Into<Operand>,
        c: impl Into<Operand>,
        plus: bool,
    ) -> Value {
        let operands = [a.into(), b.into(), c.into(), d.into()];
        let [va, vb, vc, vd] = operands.map(|o| self.value(o));
        let flags = if plus { PLUS } else { 0 };
        self.push(operands, flags, 0, (va + vd) * vb + vc + F(plus as u128))
    }

    /// Operations so far.
    pub fn finish_len(&self) -> usize {
        self.ops.len()
    }

    /// The value of `v` in the run being assembled.
    pub fn value_of(&self, v: Value) -> F {
        self.ops[v.0].value
    }

    /// `a b`.
    pub fn mul(&mut self, a: Value, b: Value) -> Value {
        self.op(a, Operand::None, b, Operand::None)
    }

    /// `a + c`.
    pub fn add(&mut self, a: Value, c: Value) -> Value {
        self.op(a, Operand::None, Operand::One, c)
    }

    /// A value from outside: the prover's to say.
    pub fn input(&mut self, value: F) -> Value {
        self.push([Operand::None; 4], INPUT, 0, value)
    }

    /// The value another table sends under `address`, which is its
    /// `value`: read once here, and from here as often as wanted.
    pub fn outside(&mut self, address: u32, value: F) -> Value {
        assert!((OUTSIDE..1 << ADDRESS).contains(&address));
        self.outside_value.insert(self.ops.len(), value);
        self.push([Operand::None, Operand::One, Operand::None, Operand::None], 0, address, value)
    }

    /// The address another table can read `v` under, once: a copy of it
    /// made for that reader.
    pub fn send(&mut self, v: Value) -> u32 {
        let copy = self.op(v, Operand::None, Operand::One, Operand::None);
        self.ops[copy.0].sent = true;
        BASE + copy.0 as u32
    }

    /// The assertion that `x` is public element `i`: the first to say so
    /// says what the element is.
    pub fn public(&mut self, x: Value, i: usize) {
        let value = self.ops[x.0].value;
        self.disagree |= *self.public[i].get_or_insert(value) != value;
        // No `b`: the row computes nothing and sends nothing.
        self.push([x.into(), Operand::None, Operand::None, Operand::None], EQUAL | public(i), 0, F::ZERO);
    }

    /// The assertion that `x` is `y`.
    pub fn equal(&mut self, x: Value, y: Value) {
        let sum = self.ops[x.0].value + self.ops[y.0].value;
        self.push([x.into(), Operand::One, y.into(), Operand::None], EQUAL, 0, sum);
    }

    /// The rows of the computation, each its inputs and its program, and
    /// whether every assertion holds. Results with more than eight
    /// readers are copied in rows after the computation's own; the rows
    /// are filled to a power of two, and to `at_least`, with rows that do
    /// nothing.
    pub fn finish(mut self, at_least: usize) -> Rows {
        let holds = !self.disagree && self.ops.iter().all(|op| op.flags & EQUAL == 0 || op.value == F::ZERO);
        let words = |x: F| -> [u32; 4] { std::array::from_fn(|j| (x.0 >> (32 * j)) as u32) };
        let public = self.public.map(|p| words(p.unwrap_or(F::ZERO))).concat();
        // What nobody reads does nothing: a result is wanted if it is an
        // assertion's, or sent to another table, or read by a row that
        // is wanted. A row not wanted becomes one that computes nothing;
        // if it read another table's value it still takes it, so that
        // what was sent is received.
        let mut wanted: Vec<bool> = self.ops.iter().map(|op| op.flags & EQUAL != 0 || op.sent).collect();
        for i in (0..self.ops.len()).rev() {
            if wanted[i] {
                for operand in self.ops[i].operands {
                    if let Operand::Of(v) = operand {
                        wanted[v.0] = true;
                    }
                }
            }
        }
        for (op, wanted) in self.ops.iter_mut().zip(wanted) {
            if !wanted {
                *op =
                    Op { operands: [Operand::None; 4], flags: EQUAL, outside: op.outside, sent: false, value: F::ZERO };
            }
        }
        // Who reads each value: the operand places, in order.
        let own = self.ops.len();
        let mut readers: Vec<Vec<(usize, usize)>> = vec![Vec::new(); own];
        for (i, op) in self.ops.iter().enumerate() {
            for (place, operand) in op.operands.iter().enumerate() {
                if let Operand::Of(v) = operand {
                    readers[v.0].push((i, place));
                }
            }
        }
        // The address each place reads, and how often each row sends. A
        // row serves eight readers; with more, seven and a row that copies
        // its result, which serves the rest the same way.
        let address = |row: usize| BASE + row as u32;
        let mut reads: Vec<[u32; 4]> = vec![[0; 4]; own];
        for (v, readers) in readers.into_iter().enumerate() {
            let read = !readers.is_empty() || self.ops[v].sent || self.ops[v].flags & EQUAL != 0;
            assert!(read, "a result nobody reads");
            assert!(readers.is_empty() || !self.ops[v].sent, "a result sent to another table is a copy");
            let mut from = v;
            let mut rest = &readers[..];
            while !rest.is_empty() {
                let direct = if rest.len() > SENDS { SENDS - 1 } else { rest.len() };
                for (row, place) in &rest[..direct] {
                    reads[*row][*place] = address(from);
                }
                rest = &rest[direct..];
                let sends = direct + !rest.is_empty() as usize;
                self.ops[from].flags |= AGAIN[..sends.saturating_sub(1)].iter().fold(0, |f, b| f | b);
                if !rest.is_empty() {
                    // A copy: `a 1`, reading the row before it in the chain.
                    let value = self.ops[v].value;
                    self.ops.push(Op { operands: [Operand::None; 4], flags: ONE, outside: 0, sent: false, value });
                    reads.push([address(from), 0, 0, 0]);
                    from = self.ops.len() - 1;
                }
            }
        }
        let n = self.ops.len().max(at_least).next_power_of_two();
        assert!(n < OUTSIDE as usize, "the machine's addresses are below those of other tables");
        let mut rows = Rows { inputs: Vec::with_capacity(n), program: Vec::with_capacity(n * PROGRAM), public, holds };
        for (i, op) in self.ops.iter().enumerate() {
            let copy = i >= own;
            let mut addresses = reads[i];
            let mut flags = op.flags;
            let mut values = [F::ZERO; 4];
            for (place, operand) in op.operands.iter().enumerate() {
                match operand {
                    Operand::Of(v) => values[place] = self.ops[v.0].value,
                    Operand::One => flags |= ONE | none(place),
                    Operand::None => flags |= none(place),
                }
            }
            if copy {
                // The copy reads its `a`, which the operands do not show.
                flags &= !none(0);
                values[0] = op.value;
            }
            if op.outside != 0 {
                addresses[0] = op.outside;
                flags &= !none(0);
                // Read and not wanted: taken, and multiplied by nothing.
                values[0] = if op.flags & EQUAL != 0 { self.outside_value[&i] } else { op.value };
                if op.flags & EQUAL != 0 {
                    flags &= !ONE;
                }
            }
            rows.push(address(i), values, op.value, addresses, flags);
        }
        while rows.inputs.len() < n {
            // A row that does nothing: an assertion that nothing is nothing.
            let all = none(0) | none(1) | none(2) | none(3);
            rows.push(address(rows.inputs.len()), [F::ZERO; 4], F::ZERO, [0; 4], EQUAL | all);
        }
        rows.program[3] |= FIRST;
        rows
    }
}

/// A computation as the machine's rows.
pub struct Rows {
    pub inputs: Vec<[u32; INPUTS]>,
    /// The program, [`PROGRAM`] words a row.
    pub program: Vec<u32>,
    /// The circuit's public values: the public elements' words.
    pub public: Vec<u32>,
    /// Whether every assertion of the computation holds for the values
    /// it was run on.
    pub holds: bool,
}

impl Rows {
    fn push(&mut self, address: u32, [a, b, c, d]: [F; 4], out: F, addresses: [u32; 4], flags: u32) {
        let words = |x: F| -> [u32; 4] { std::array::from_fn(|j| (x.0 >> (32 * j)) as u32) };
        let free = if flags & INPUT != 0 { out } else { F::ZERO };
        let mut r = [0u32; INPUTS];
        for (i, x) in [a, b, c, d, out, free].into_iter().enumerate() {
            r[4 * i..4 * i + 4].copy_from_slice(&words(x));
        }
        r[24] = address;
        r[25] = if flags & EQUAL == 0 { address } else { 0 };
        for (i, bit) in AGAIN.into_iter().enumerate() {
            if flags & bit != 0 {
                r[26 + 5 * i] = address;
                r[27 + 5 * i..31 + 5 * i].copy_from_slice(&words(out));
            }
        }
        self.inputs.push(r);
        // The four addresses, 24 bits each, then the flags' word.
        let packed = addresses.iter().enumerate().fold(0u128, |p, (i, a)| p | (*a as u128) << (ADDRESS * i));
        self.program.extend([packed as u32, (packed >> 32) as u32, (packed >> 64) as u32, flags]);
    }
}

/// The row a [`crate::circuit::Concrete`] runs: every word an input.
pub fn run<C: Ctx>(c: &mut C) {
    row(c);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::argument::{Program, Statement, prove, variables, verify};
    use crate::circuit::{Fixed, Witness};
    use crate::ntt::Domain;
    use crate::pcs::Params;
    use crate::test_util::Rng;

    /// Whether the rows are proven against `program`, the one committed.
    /// The witness is made against `against`, the program the prover
    /// works to.
    fn proves(inputs: &[[u32; INPUTS]], program: &[u32], against: &[u32]) -> bool {
        let circuit = circuit();
        let params = Params::plain(variables(&circuit, inputs.len()), 1, 4, 4);
        let domain = Domain::new(params.k(), true);
        let committed = Program::new(&circuit, &params, &domain, program.to_vec());
        let fixed = Fixed { program: against, public: &NO_PUBLIC };
        let w = Witness::new(&circuit, inputs.len(), |c| run(c), |i| inputs[i], &fixed);
        let (proof, _) = prove(&circuit, &params, &domain, w, Some(&committed), &NO_PUBLIC);
        let root = committed.root();
        let statement = Statement { program: Some(&root), public: &NO_PUBLIC };
        verify(&circuit, &params, &domain, inputs.len(), &proof, &statement).is_some()
    }

    /// A computation with every kind of row: a polynomial of degree 40
    /// at a point, by Horner's rule and term by term, the two asserted
    /// equal. The point is read 80 times, so it is copied.
    fn horner(seed: u64, wrong: bool) -> Rows {
        let mut rng = Rng(seed);
        let mut asm = Assembly::default();
        let x = asm.input(rng.f());
        let coefficients: Vec<Value> = (0..41).map(|_| asm.input(rng.f())).collect();
        // ((c40 x + c39) x + ..) x + c0.
        let mut acc = coefficients[40];
        for c in coefficients[..40].iter().rev() {
            acc = asm.op(acc, Operand::None, x, *c);
        }
        // c0 + c1 x + c2 x^2 + .., the powers kept.
        let mut power = x;
        let mut sum = asm.op(coefficients[1], Operand::None, x, coefficients[0]);
        for c in &coefficients[2..] {
            power = asm.mul(power, x);
            sum = asm.op(*c, Operand::None, power, sum);
        }
        if wrong {
            sum = asm.add(sum, x);
        }
        // `(a + d) b + c` with every operand: (acc + sum) x + acc is acc.
        let both = asm.op(acc, sum, x, acc);
        asm.equal(both, acc);
        asm.equal(acc, sum);
        asm.finish(128)
    }

    #[test]
    fn a_computation_is_proven() {
        let c = circuit();
        assert_eq!((c.log_cols, c.program_width(), c.log_products, c.log_slots), (6, 4, 5, 3));
        assert_eq!((c.cols, c.constraints.len(), c.products.len()), (63, 2, 22));
        // `plus`: one more than the product.
        let mut asm = Assembly::default();
        let (x, y) = (asm.input(F(6)), asm.input(F(7)));
        let z = asm.op_plus(x, Operand::None, y, Operand::None, true);
        assert_eq!(asm.value_of(z), F(6) * F(7) + F::ONE);
        let expect = asm.input(F(6) * F(7) + F::ONE);
        asm.equal(z, expect);
        let plus = asm.finish(128);
        assert!(plus.holds && proves(&plus.inputs, &plus.program, &plus.program));
        let rows = horner(1, false);
        assert!(rows.holds && rows.inputs.len() == 256);
        assert!(proves(&rows.inputs, &rows.program, &rows.program));
        // Other values, the same program; and they are proven against it.
        let other = horner(2, false);
        assert_eq!(other.program, rows.program);
        assert_ne!(other.inputs, rows.inputs);
        assert!(proves(&other.inputs, &rows.program, &rows.program));
    }

    #[test]
    fn a_wrong_computation_is_not() {
        // An assertion that does not hold.
        let wrong = horner(1, true);
        assert!(!wrong.holds);
        assert!(!proves(&wrong.inputs, &wrong.program, &wrong.program));
        let rows = horner(1, false);
        let proven = |inputs: &[[u32; INPUTS]]| proves(inputs, &rows.program, &rows.program);
        // A row's words changed, one at a time: an operand (which is no
        // longer what was sent), a result, a value given for a row that
        // takes none, an address, a tuple sent.
        let op = 50;
        for word in [0, 5, 9, 16, 20, 24, 25] {
            let mut bad = rows.inputs.clone();
            bad[op][word] ^= 1;
            assert!(!proven(&bad), "word {word}");
        }
        // A result and every reader's copy of it changed alike: the
        // multiplication is then wrong.
        let mut bad = rows.inputs.clone();
        bad[op][16] ^= 1;
        for r in bad.iter_mut() {
            for (place, at) in [(0, 0), (1, 4), (2, 8), (3, 12)] {
                let _ = place;
                if r[at..at + 4] == rows.inputs[op][16..20] && r != &rows.inputs[op] {
                    r[at] ^= 1;
                }
            }
        }
        assert!(!proven(&bad));
        // An input's value is the prover's: any will do, if its readers
        // have the same. Here they do not.
        let mut bad = rows.inputs.clone();
        bad[0][16] ^= 1;
        bad[0][20] ^= 1;
        assert!(!proven(&bad));
        // The prover works to a program of its own: an assertion left
        // out, an operand read from another address, a row's result made
        // an input. None is the program committed.
        let last = rows.program.len() / PROGRAM - 1;
        let eq_row =
            (0..=last).rev().find(|r| rows.program[r * 4 + 3] & EQUAL != 0 && rows.inputs[*r][0] != 0).unwrap();
        for change in [(eq_row, 3, EQUAL), (op, 0, 1), (op, 3, INPUT)] {
            let (row, word, bit) = change;
            let mut own = rows.program.clone();
            own[row * 4 + word] ^= bit;
            // The rows are for the program committed, not for this one.
            assert!(!proves(&rows.inputs, &own, &rows.program), "{change:?}");
        }
        // Rows that hold under the prover's program and not under the
        // one committed: an assertion that fails, left out of its own.
        let wrong = horner(1, true);
        let failing =
            (0..=last).rev().find(|r| wrong.program[r * 4 + 3] & EQUAL != 0 && wrong.inputs[*r][16] != 0).unwrap();
        let mut own = wrong.program.clone();
        own[failing * 4 + 3] ^= EQUAL | INPUT;
        let mut inputs = wrong.inputs.clone();
        // As an input the row's result is the prover's, and is sent.
        let out: [u32; 4] = inputs[failing][16..20].try_into().unwrap();
        inputs[failing][20..24].copy_from_slice(&out);
        inputs[failing][25] = inputs[failing][24];
        assert!(!proves(&inputs, &wrong.program, &own));
    }

    #[test]
    fn values_come_from_another_table() {
        // A table that sends elements under addresses its program
        // names, as the hash table sends what it read from a proof; the
        // machine reads three of them and asserts that the third is the
        // product of the first two.
        use crate::argument::{Layout, Part, Table, prove_tables, verify_tables};
        let machine = circuit();
        let source = Circuit::new(
            |s| {
                let w: [crate::circuit::Expr; 4] = std::array::from_fn(|_| s.input());
                let tag = s.program();
                s.send(vec![Sum::word(&tag), Sum::element(&w)]);
                s.constraints.len()
            },
            4,
        );
        let mut rng = Rng(4);
        let (x, y) = (rng.f(), rng.f());
        let run_with = |sent: [F; 3]| {
            let mut asm = Assembly::default();
            let [a, b, c] = std::array::from_fn(|i| asm.outside(OUTSIDE + 7 + i as u32, sent[i]));
            let product = asm.mul(a, b);
            asm.equal(product, c);
            let rows = asm.finish(128);
            // The source: its first three rows send, the rest nothing.
            let words = |v: F| -> [u32; 4] { std::array::from_fn(|j| (v.0 >> (32 * j)) as u32) };
            let sends: Vec<[u32; 4]> = (0..128).map(|i| if i < 3 { words(sent[i]) } else { [0; 4] }).collect();
            let tags: Vec<u32> = (0..128).map(|i| if i < 3 { OUTSIDE + 7 + i as u32 } else { 0 }).collect();
            let tables = [(&machine, rows.inputs.len()), (&source, 128)];
            let layout = Layout::of(tables.iter().copied()).unwrap();
            let params = Params::plain(layout.total, 1, 4, 4);
            let domain = Domain::new(params.k(), true);
            let program = Program::of(&params, &domain, &tables, vec![rows.program.clone(), tags]);
            let fixed = [
                Fixed { program: &program.words[0], public: &NO_PUBLIC },
                Fixed { program: &program.words[1], public: &[] },
            ];
            let parts = vec![
                Part {
                    circuit: &machine,
                    witness: Witness::new(&machine, 128, |c| run(c), |i| rows.inputs[i], &fixed[0]),
                    public: &NO_PUBLIC,
                },
                Part {
                    circuit: &source,
                    witness: Witness::new(
                        &source,
                        128,
                        |c| _ = (std::array::from_fn::<u32, 4, _>(|_| c.input()), c.program()),
                        |i| sends[i],
                        &fixed[1],
                    ),
                    public: &[],
                },
            ];
            let (proof, _) = prove_tables(&params, &domain, parts, Some(&program));
            let tables = [
                Table { circuit: &machine, rows: 128, public: &NO_PUBLIC },
                Table { circuit: &source, rows: 128, public: &[] },
            ];
            let ok = verify_tables(&params, &domain, &tables, Some(&program.root()), &proof).is_some();
            assert!(!ok || rows.holds);
            ok
        };
        assert!(run_with([x, y, x * y]));
        assert!(!run_with([x, y, x * y + F::ONE]));
    }

    /// What the machine's rows cost to prove.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn machine_timing() {
        let circuit = circuit();
        for log_ops in [15, 17] {
            let mut rng = Rng(5);
            let mut asm = Assembly::default();
            let mut acc = asm.input(rng.f());
            let mut x = asm.input(rng.f());
            for i in 0..(1usize << log_ops) - 200 {
                acc = asm.op(acc, x, x, acc);
                if i % 3 == 0 {
                    x = asm.add(x, acc);
                }
            }
            let end = asm.add(acc, x);
            asm.equal(end, end);
            let rows = asm.finish(128);
            let n = rows.inputs.len();
            let params = Params::proven(variables(&circuit, n), 2, crate::pcs::SECURITY);
            let domain = Domain::new(params.k(), true);
            let committed = Program::new(&circuit, &params, &domain, rows.program.clone());
            let fixed = Fixed { program: &committed.words[0], public: &NO_PUBLIC };
            let t = std::time::Instant::now();
            let w = Witness::new(&circuit, n, |c| run(c), |i| rows.inputs[i], &fixed);
            let (proof, times) = prove(&circuit, &params, &domain, w, Some(&committed), &NO_PUBLIC);
            let proved = t.elapsed();
            let root = committed.root();
            let statement = Statement { program: Some(&root), public: &NO_PUBLIC };
            let t = std::time::Instant::now();
            assert!(verify(&circuit, &params, &domain, n, &proof, &statement).is_some());
            println!(
                "2^{} rows of the machine ({:.0} M bits): proven in {proved:.2?} (commit {:.2?}, checks {:.2?}, open {:.2?}), \
                 {} KB, verified in {:.2?}",
                n.trailing_zeros(),
                (128u64 << params.m) as f64 / 1e6,
                times.commit,
                times.zerocheck,
                times.open,
                proof.size() / 1000,
                t.elapsed()
            );
        }
    }

    /// Whether the rows are proven for the public values `public`.
    fn proves_of(rows: &Rows, public: &[u32]) -> bool {
        let circuit = circuit();
        let params = Params::plain(variables(&circuit, rows.inputs.len()), 1, 4, 4);
        let domain = Domain::new(params.k(), true);
        let committed = Program::new(&circuit, &params, &domain, rows.program.clone());
        let fixed = Fixed { program: &rows.program, public: &rows.public };
        let w = Witness::new(&circuit, rows.inputs.len(), |c| run(c), |i| rows.inputs[i], &fixed);
        let (proof, _) = prove(&circuit, &params, &domain, w, Some(&committed), &rows.public);
        let root = committed.root();
        verify(&circuit, &params, &domain, rows.inputs.len(), &proof, &Statement { program: Some(&root), public })
            .is_some()
    }

    #[test]
    fn a_computation_is_of_its_public_values() {
        let of = |x: F, y: F, said: [F; 2]| {
            let mut asm = Assembly::default();
            let (x, y) = (asm.input(x), asm.input(y));
            let product = asm.mul(x, y);
            asm.public(product, 0);
            asm.public(y, 1);
            // Named again: the same element.
            let again = [asm.input(said[0]), asm.input(said[1])];
            asm.public(again[0], 0);
            asm.public(again[1], 1);
            asm.finish(128)
        };
        let rows = of(F(6), F(7), [F(6) * F(7), F(7)]);
        assert!(rows.holds && rows.public[..5] == [18, 0, 0, 0, 7]);
        assert!(proves_of(&rows, &rows.public));
        // Not of other values, either element.
        for word in [0, 4] {
            let mut other = rows.public.clone();
            other[word] ^= 1;
            assert!(!proves_of(&rows, &other));
        }
        // Two rows that say an element is two things: neither holds.
        for said in [[F(41), F(7)], [F(42), F(8)]] {
            let rows = of(F(6), F(7), said);
            assert!(!rows.holds && !proves_of(&rows, &rows.public));
        }
    }

    #[test]
    fn a_value_read_often_is_copied() {
        let mut rng = Rng(3);
        for readers in [1usize, 3, 8, 9, 15, 16, 30, 100] {
            let mut asm = Assembly::default();
            let x = asm.input(rng.f());
            let mut acc = asm.input(rng.f());
            for _ in 0..readers {
                acc = asm.mul(acc, x);
            }
            let again = asm.op(acc, Operand::None, Operand::One, Operand::None);
            asm.equal(acc, again);
            let own = asm.ops.len();
            let rows = asm.finish(128);
            assert!(rows.holds);
            // Seven readers a row, and a copy, until eight are left.
            let copies = if readers <= SENDS { 0 } else { (readers - SENDS).div_ceil(SENDS - 1) };
            let used = rows.program.chunks(4).filter(|p| p[3] & EQUAL == 0).count();
            assert_eq!(used, own - 1 + copies, "{readers} readers");
            assert!(proves(&rows.inputs, &rows.program, &rows.program), "{readers} readers");
        }
    }
}
