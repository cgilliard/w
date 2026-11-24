//! Whole numbers for a compiled computation: a table whose row adds or
//! subtracts two numbers of 64 bits.
//!
//! The machine ([`crate::machine`]) computes in a field where a sum is
//! an exclusive or: it cannot count, nor say which of two numbers is
//! the larger. A row here takes two values off the bus as numbers of 64
//! bits, and sends their sum (or their difference) and whether it
//! carried. A value that is not a number of 64 bits is not taken: the
//! tuple a row takes has no more bits than that. So `a >= b` is "`a - b`
//! carries", and a value is known to be a number by having been here.
//!
//! A row's program names the four addresses and says whether it
//! subtracts.

use crate::circuit::{Circuit, Ctx, Expr, Pre, Sum, Symbolic, Term};

/// Words a row takes as inputs: the two numbers, the result, and the
/// carries.
pub const INPUTS: usize = 11;
/// Words of program a row reads.
pub const PROGRAM: usize = 8;

struct Row<V> {
    a: [V; 2],
    b: [V; 2],
    sum: [V; 2],
    /// The words of carries, and the carry out of each as one bit; the
    /// carry into the first.
    carries: [V; 2],
    out: [V; 2],
    into: V,
    /// The addresses of the two numbers, of the result and of the carry;
    /// and a word of all ones if the row subtracts.
    at: [V; 4],
    negate: V,
}

fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
    let mut two = || [c.input(), c.input()];
    let (a, b, sum, carries, out) = (two(), two(), two(), two(), two());
    let into = c.input();
    let at = std::array::from_fn(|_| c.program());
    let negate = c.program();
    for _ in 5..PROGRAM {
        c.program();
    }
    Row { a, b, sum, carries, out, into, at, negate }
}

/// The row a [`crate::circuit::Concrete`] runs.
pub fn run<C: Ctx>(c: &mut C) {
    row(c);
}

pub fn circuit() -> Circuit {
    Circuit::new(
        |s: &mut Symbolic| {
            let r = row(s);
            let core = s.constraints.len();
            let con = Expr::constant;
            // A difference is a sum with the other number turned over,
            // and one more.
            s.constrain(r.negate.clone(), con(1), r.into.clone());
            let mut carry_in = r.into.clone();
            for i in 0..2 {
                let y = r.b[i].xor(&r.negate);
                let shifted = Expr { terms: vec![Term { pre: Pre::Shl, ..r.carries[i].terms[0] }], constant: 0 };
                let into = shifted.xor(&carry_in);
                s.constrain(r.a[i].xor(&into), y.xor(&into), r.carries[i].xor(&into));
                s.zero_where(&con(!0), r.sum[i].xor(&r.a[i]).xor(&y).xor(&into));
                let mut top = r.carries[i].clone();
                top.terms[0].rot = 31;
                s.constrain(top, con(1), r.out[i].clone());
                carry_in = r.out[i].clone();
            }
            s.receive(vec![Sum::word(&r.at[0]), Sum::element(&r.a)]);
            s.receive(vec![Sum::word(&r.at[1]), Sum::element(&r.b)]);
            s.send(vec![Sum::word(&r.at[2]), Sum::element(&r.sum)]);
            s.send(vec![Sum::word(&r.at[3]), Sum::word(&r.out[1])]);
            core
        },
        INPUTS,
    )
}

/// The rows as their inputs and their program.
#[derive(Default)]
pub struct Rows {
    pub rows: Vec<[u32; INPUTS]>,
    pub program: Vec<[u32; PROGRAM]>,
}

impl Rows {
    /// A row: `a + b`, or `a - b` if `subtract`, taking the numbers under
    /// `at[0]` and `at[1]` and sending the result under `at[2]` and the
    /// carry under `at[3]`. The result and the carry.
    pub fn push(&mut self, a: u64, b: u64, subtract: bool, at: [u32; 4]) -> (u64, bool) {
        let negate = if subtract { !0u32 } else { 0 };
        let mut r = [0u32; INPUTS];
        let mut carry_in = negate & 1;
        for i in 0..2 {
            let (x, y) = ((a >> (32 * i)) as u32, (b >> (32 * i)) as u32 ^ negate);
            let sum = x.wrapping_add(y).wrapping_add(carry_in);
            let into = x ^ y ^ sum;
            let carries = (x & y) | ((x ^ y) & into);
            (r[i], r[2 + i], r[4 + i], r[6 + i], r[8 + i]) = (x, (b >> (32 * i)) as u32, sum, carries, carries >> 31);
            carry_in = carries >> 31;
        }
        r[10] = negate & 1;
        let mut p = [0u32; PROGRAM];
        p[..4].copy_from_slice(&at);
        p[4] = negate;
        self.rows.push(r);
        self.program.push(p);
        (r[4] as u64 | (r[5] as u64) << 32, carry_in == 1)
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// The rows filled to a power of two (and to `at_least`) with rows
    /// that take and send nothing, and the program as words.
    pub fn finish(mut self, at_least: usize) -> (Vec<[u32; INPUTS]>, Vec<u32>) {
        let n = self.rows.len().max(at_least).next_power_of_two();
        self.rows.resize(n, [0; INPUTS]);
        self.program.resize(n, [0; PROGRAM]);
        (self.rows, self.program.concat())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_row_adds_and_subtracts() {
        let c = circuit();
        assert_eq!((c.log_cols, c.program_width(), c.sends.len(), c.receives.len()), (7, PROGRAM, 2, 2));
        let mut rows = Rows::default();
        assert_eq!(rows.push(5, 7, false, [1, 2, 3, 4]), (12, false));
        assert_eq!(rows.push(u64::MAX, 1, false, [1, 2, 3, 4]), (0, true));
        assert_eq!(rows.push(7, 5, true, [1, 2, 3, 4]), (2, true));
        assert_eq!(rows.push(5, 7, true, [1, 2, 3, 4]), (u64::MAX - 1, false));
        assert_eq!(rows.push(1 << 40, 1 << 40, true, [1, 2, 3, 4]), (0, true));
        assert_eq!(rows.push((1 << 32) - 1, 1, false, [1, 2, 3, 4]), (1 << 32, false));
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_computation_counts_with_it() {
        use crate::alg::Alg;
        use crate::field::F;
        use crate::pcs::Params;
        use crate::sym::Shared;
        let run = |a: u128, b: u128| {
            let cx = Shared::new();
            let (x, y) = (cx.input(F(a)), cx.input(F(b)));
            let (sum, carried) = cx.number(&x, &y, false);
            let (difference, not_less) = cx.number(&x, &y, true);
            // What the rows say is what the numbers are.
            let (a, b) = (a as u64, b as u64);
            assert!(sum.is(&cx.input(F(a.wrapping_add(b) as u128))));
            assert!(carried.is(&cx.constant(F(a.checked_add(b).is_none() as u128))));
            assert!(difference.is(&cx.input(F(a.wrapping_sub(b) as u128))));
            assert!(not_less.is(&cx.constant(F((a >= b) as u128))));
            cx.state(&[sum, difference]);
            let p = crate::proof::prove(cx, vec![], |m| Params::plain(m, 1, 4, 4));
            assert_eq!(p.rows(crate::proof::Kind::Numbers), vec![128]);
            p.holds && p.verifies()
        };
        assert!(run(5, 7) && run(7, 5) && run(u64::MAX as u128, 1) && run(1 << 40, 1 << 40));
        // A value that is not a number of 64 bits is not taken.
        assert!(!run(1 << 64, 1));
        assert!(!run(1, 5 | 1 << 100));
    }
}
