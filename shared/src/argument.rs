//! The proof that committed words satisfy a circuit on every row.
//!
//! A circuit ([`crate::circuit`]) says three kinds of thing of a row's
//! words, and this proves each for every row and brings what is left of
//! them all to one opening of the commitment.
//!
//! # The protocol
//!
//! 1. **Commit.** The witness's bits, 128 to a field element
//!    ([`pack`]), committed by [`crate::pcs`]. A circuit's program, if it
//!    has one, was committed the same way beforehand ([`Program`]), and
//!    the statement names its root.
//! 2. **The constraints**, `A & B = C` on bits, a bit for each of: 32
//!    places of a word (`j`, the lowest variable), the constraints of a
//!    row (`k`), the rows. For a random `tau`, a sumcheck of
//!    `sum_x eq(tau, x) (A(x) B(x) + C(x)) = 0` (`zerocheck`). It ends
//!    with the three operands' values at a point `rho`.
//! 3. **The multiplications**, `x y = z` in the field: the same check
//!    over tables of field elements, a value for each multiplication of
//!    each row. It ends at a point of its own.
//! 4. **The bus.** Every tuple a row sends or receives is a fingerprint
//!    `gamma + sum_i alpha^i t_i`, and the product of all sent must be
//!    the product of all received, which two grand products show
//!    ([`crate::grand`]). For multisets that differ the products agree
//!    with a probability the grinding before the challenges keeps below
//!    the level. A row with nothing to say in a place sends and receives
//!    nothing there, `gamma` each way. The products leave the two tables
//!    of fingerprints at a point.
//!
//!    This is what a memory is made of. A value written in one row and
//!    read in another is a tuple sent and received under a tag that only
//!    those two rows use; a value read many times is passed along, each
//!    reader sending it on under the next tag. The tags are the
//!    program's.
//! 5. **To the words.** An operand's bit, an element, a fingerprint: each
//!    is a sum of bits of the row's words, of the row before's, of its
//!    program's, and of the public values, which bits fixed by the
//!    circuit. So what each check left at its point is a constant (the
//!    public values' part, which the verifier works out) and a sum over
//!    the rows, weighted by `eq` at the point, of the row's bits under a
//!    table the verifier works out too (`Tables`); for the row before,
//!    weighted by `eq` at the row after ([`successor`]). Each is a
//!    `Claim`.
//! 6. **To one point.** A sumcheck over the rows alone brings every
//!    claim to one point `zeta` (`Rows`), and a challenge batches the
//!    claims' tables: one table `M` for the witness's words, one for the
//!    program's.
//! 7. **To a point.** A sumcheck over a row's bits brings the sum under
//!    `M` to the bits themselves at a point `rho_e` (`Columns`): what is
//!    left is the words, as a multilinear polynomial of their bits, at
//!    `(rho_e, zeta)`, and the verifier needs `M` at `rho_e` alone. The
//!    same for the program.
//! 8. **To the packed words** (ring switching, after Diamond and Posen).
//!    An element holds one bit place of one word for 128 rows, so the
//!    value is `sum_b eq(zeta_low, b) s_b` with
//!    `s_b = sum_p y[p] W[p, b]` and `y[p] = eq((rho_e, zeta_high), p)`.
//!    The prover sends the 128 `s_b`. Their bits, read the other way,
//!    are 128 sums `sum_p bit_c(y[p]) f[p]` over the packed elements
//!    `f`, which a random combination makes one: `sum_p g[p] f[p]`,
//!    with `g[p]` the map [`phi`] of `y[p]`. The map is a sum of powers
//!    `2^t`, so that the verifier does all of this with sums and
//!    products of elements and reads no bit of one ([`switched`]): a
//!    circuit's arithmetic can be the verifier.
//! 9. **Open.** Every table's sums, the words' and the programs', are
//!    first made one set of 128 under the powers of a challenge, each
//!    scale going inside the map. What they come to is the sum
//!    [`crate::pcs::open_weighted`] has to prove of the words' polynomial
//!    and of the programs', which joins as the opening's second; the
//!    prover says how much of it is the programs' (`Proof::split`). The
//!    verifier works out `g` at the opening's challenges by a closed
//!    formula ([`opening_weights`]).
//!
//! # Hiding
//!
//! With parameters that say so ([`crate::pcs::Params::hiding`]) a proof
//! says nothing of the witness: [`prove_hiding`]. Everything the prover
//! sends before the opening goes under a pad, the verifier's checks
//! become equations over the pads, and the opening shows them with the
//! rest ([`crate::hidden`], which has the reasons, and `docs/ZK.md`).
//! The verifier is the same code over another arithmetic; a circuit
//! that verifies such a proof is made the same way as any.
//!
//! # Several tables
//!
//! A proof may be of several tables, each with a circuit of its own and
//! rows of its own number ([`prove_tables`]): a table of compressions and
//! a narrower one of arithmetic, say. Every table is committed before
//! any challenge, in one commitment. Steps 2 to 8 are each table's own, in the tables'
//! order, on the one transcript. Two things are shared:
//!
//! - **The bus.** Its challenges are drawn once, and what is checked is
//!   that the product of everything sent, over all the tables, is the
//!   product of everything received: a table need not balance by
//!   itself. That is how a value in one table is used in another.
//! - **The commitment and its opening.** The tables' words are one
//!   polynomial, each table in a block of its own size ([`Layout`]), and
//!   so are their programs. A table's sums weigh its block alone; a
//!   challenge batches the tables, and one opening shows them all.
//!
//! # Soundness
//!
//! Counted round by round, as [`crate::pcs`] counts its own, each to err
//! with probability `2^-125` at most for the 124 bits of
//! [`crate::pcs::SECURITY`]. `n` is the number of
//! variables of the constraints' bits, 31 for a table of 2^17 rows.
//!
//! | round | error | bits |
//! |---|---|---|
//! | `tau`: a constraint that fails is seen, after grinding | `n / 2^128` | 125 |
//! | a zerocheck round, of degree 2 under its `eq` | `2 / 2^128` | 127 |
//! | batching the three operands | `2 / 2^128` | 127 |
//! | the multiplications' `tau`, rounds and batching | as the constraints' | 125 |
//! | weighing the multiplications' claims against the constraints' | `1 / 2^128` | 128 |
//! | the bus's challenges, after grinding | `2 rows slots length / 2^128` | 125 |
//! | the bus's grand products | [`crate::grand`]'s | 127 |
//! | batching the bus's two ways, and weighing it | `1 / 2^128` | 128 |
//! | a round over the rows, of degree 2 | `2 / 2^128` | 127 |
//! | batching the claims' tables, nine at most | `8 / 2^128` | 125 |
//! | a round over a row's bits, of degree 2 | `2 / 2^128` | 127 |
//! | batching the 128 sums by the powers of a challenge, and the tables' sums by another's, after grinding | `(126 + 2 tables) / 2^128` | 125 |
//! | the opening | [`crate::pcs`]'s | 125 |
//!
//! A proof that hides what it is of ([`crate::hidden`]) has these more:
//!
//! | round | error | bits |
//! |---|---|---|
//! | batching the 128 terms of the ring switching, after grinding | `127 / 2^128` | 125 |
//! | the products' challenge, after grinding | `2 products / 2^128` | 125 |
//! | batching the equations over the pads, after grinding | `equations / 2^128` | 125 |
//! | weighing the corners | `1 / 2^128` | 128 |
//! | the blinding polynomial joining the opening | a joiner's, [`crate::pcs`] | 125 |
//!
//! Of the rounds here the zerochecks' points, the bus's challenges and
//! the two that batch the sums are ground: the field is 128 bits, and
//! nothing else in them grows with the table. The opening's rounds do,
//! and have it.
//!
//! The verifier turns a proof away if the challenge that batches the
//! 128 sums is zero, or a folding challenge is one: it divides by them.
//! A prover cannot make either happen, and each has one chance in
//! `2^128`.
//!
//! The transcript begins with the witness's root, the program's root and
//! the public values, so every challenge depends on the statement.
//!
//! `docs/SOUNDNESS.md` has what each of these rests on, and the proof
//! that the reduction of step 8 is sound in the form it has here.

use crate::alg::{Alg, Transcript};
use crate::challenger::{Challenger, Step};
use crate::circuit::{Circuit, Fixed, LOG_PROGRAM_SHARE, Source, Sum, Term, Witness};
use crate::codec::{Reader, Writer};
use crate::field::F;
use crate::grand::{self, Rounds};
use crate::hash::Digest;
use crate::hidden::{Masked, Padded, Pads, Places, Room, Sent, Stream, send};
use crate::ntt::Domain;
use crate::parallel::{par_chunks_mut, par_fold};
use crate::pcs::{self, Batched, Committed, Opens, Params, Work, eq_table};
use crate::structure::{self, Acc, Direct, Ended, LOG_PACK, Public, groups, source_bit};
pub use crate::structure::{Layout, variables};
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use crate::structure::LOG_W;
/// Rounds after the bit places' for which the operands stay as words.
const FLY: usize = 2;
/// What the argument's transcript begins from, with what a proof is
/// made to ([`label`]).
pub const LABEL: &[u8] = b"tabminer argument";

/// What the transcript of a proof made to `params`, of tables of these
/// rows, begins from: the argument's name, the parameters and the rows.
/// A proof made to others is of another transcript from its first
/// challenge. (Every verifier holds its parameters and rows for itself,
/// and none takes them from a proof; this is so that one that did would
/// still not take a proof made to weaker ones.)
pub fn label(params: &Params, rows: impl Iterator<Item = usize>) -> Vec<u8> {
    let mut out = LABEL.to_vec();
    let of = [
        params.m,
        params.log_inv_rate,
        params.queries,
        params.arity,
        params.query_grinding,
        params.round_bits,
        params.blind as usize,
        params.last,
    ];
    for x in of.into_iter().chain(rows) {
        out.extend_from_slice(&(x as u64).to_le_bytes());
    }
    out
}

/// One table's part of a proof: everything but the opening, which the
/// tables share.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableProof {
    /// The nonces ground before the zerochecks' points are drawn: the
    /// constraints', and the multiplications' (zero without any).
    pub tau_nonce: u64,
    pub product_nonce: u64,
    /// Each zerocheck round's polynomial: its constant and leading
    /// coefficients. The middle one is what the claim leaves it to be.
    pub rounds: Vec<[F; 2]>,
    /// The operands at the zerocheck's point.
    pub abc: [F; 3],
    /// The multiplications' zerocheck, as the constraints': its rounds,
    /// and the three operands at its point. Empty and zero for a circuit
    /// with no multiplications.
    pub product_rounds: Vec<[F; 2]>,
    pub xyz: [F; 3],
    /// The grand products of what the table sent on the bus and of what
    /// it received. Empty for a circuit with no bus.
    pub bus: grand::Proof,
    /// The sumcheck over the rows: each round's constant and leading
    /// coefficients, and each claim's sum at its point.
    pub row_rounds: Vec<(F, F)>,
    pub u: Vec<F>,
    /// The sumcheck over a row's bits, for the witness's words: its
    /// rounds, and the words' bits at its point and the rows'. Then the
    /// same for the program's words, empty and zero without a program.
    pub col_rounds: Vec<(F, F)>,
    pub v: F,
    pub col_rounds_program: Vec<(F, F)>,
    pub v_program: F,
    /// The sums `s_b` for the witness's words, and for the program's
    /// where there is a program.
    pub s: Vec<F>,
    pub s_program: Vec<F>,
}

impl TableProof {
    fn write(&self, w: &mut Writer) {
        let pairs = |w: &mut Writer, rounds: &[(F, F)]| {
            w.len(rounds.len());
            for (c0, c2) in rounds {
                w.f(*c0);
                w.f(*c2);
            }
        };
        w.u64(self.tau_nonce);
        w.u64(self.product_nonce);
        w.fs(self.rounds.as_flattened());
        w.fs(&self.abc);
        w.fs(self.product_rounds.as_flattened());
        w.fs(&self.xyz);
        self.bus.write(w);
        pairs(w, &self.row_rounds);
        w.fs(&self.u);
        pairs(w, &self.col_rounds);
        w.f(self.v);
        pairs(w, &self.col_rounds_program);
        w.f(self.v_program);
        w.fs(&self.s);
        w.fs(&self.s_program);
    }

    fn read(r: &mut Reader) -> Option<TableProof> {
        let threes = |r: &mut Reader| {
            let xs = r.fs()?;
            (xs.len() % 2 == 0).then(|| xs.chunks_exact(2).map(|c| [c[0], c[1]]).collect::<Vec<[F; 2]>>())
        };
        let three = |r: &mut Reader| <[F; 3]>::try_from(r.fs()?).ok();
        let pairs = |r: &mut Reader| {
            let n = r.len(32)?;
            (0..n).map(|_| Some((r.f()?, r.f()?))).collect::<Option<Vec<(F, F)>>>()
        };
        Some(TableProof {
            tau_nonce: r.u64()?,
            product_nonce: r.u64()?,
            rounds: threes(r)?,
            abc: three(r)?,
            product_rounds: threes(r)?,
            xyz: three(r)?,
            bus: grand::Proof::read(r)?,
            row_rounds: pairs(r)?,
            u: r.fs()?,
            col_rounds: pairs(r)?,
            v: r.f()?,
            col_rounds_program: pairs(r)?,
            v_program: r.f()?,
            s: r.fs()?,
            s_program: r.fs()?,
        })
    }
}

/// A proof: the commitment of every table's words, each table's part,
/// the nonce ground before the bus's challenges (zero if no table has a
/// bus), and the one opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub root: Digest,
    pub tables: Vec<TableProof>,
    pub bus_nonce: u64,
    /// The nonce ground before the challenges that batch the sums of the
    /// ring switching, and the tables'.
    pub omega_nonce: u64,
    /// The programs' part of what the batched sums come to: the sum the
    /// opening shows for the programs' polynomial. Zero without one.
    pub split: F,
    /// What a proof that hides what it is of holds besides
    /// ([`crate::hidden`]); nothing otherwise.
    pub hidden: Sent,
    pub pcs: pcs::Proof,
}

impl Proof {
    /// The proof as bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut w = Writer::default();
        w.digest(&self.root);
        w.len(self.tables.len());
        self.tables.iter().for_each(|t| t.write(&mut w));
        w.u64(self.bus_nonce);
        w.u64(self.omega_nonce);
        w.f(self.split);
        w.fs(&self.hidden.extra);
        self.hidden.nonces.iter().for_each(|n| w.u64(*n));
        w.f(self.hidden.corners);
        self.pcs.write(&mut w);
        w.0
    }

    /// The proof `bytes` are, if they are one and nothing more.
    pub fn from_bytes(bytes: &[u8]) -> Option<Proof> {
        let mut r = Reader(bytes);
        let root = r.digest()?;
        let n = r.len(32)?;
        let tables = (0..n).map(|_| TableProof::read(&mut r)).collect::<Option<_>>()?;
        let (bus_nonce, omega_nonce, split) = (r.u64()?, r.u64()?, r.f()?);
        let hidden = Sent { extra: r.fs()?, nonces: [r.u64()?, r.u64()?, r.u64()?], corners: r.f()? };
        let proof = Proof { root, tables, bus_nonce, omega_nonce, split, hidden, pcs: pcs::Proof::read(&mut r)? };
        r.end().then_some(proof)
    }

    /// Bytes of the proof.
    pub fn size(&self) -> usize {
        self.to_bytes().len()
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Timings {
    pub pack: Duration,
    pub commit: Duration,
    pub zerocheck: Duration,
    pub reduce: Duration,
    pub open: Duration,
}

/// The witness as field elements: element `j | col << 5 | block << ..`
/// has in bit `b` the bit `j` of word `col` of row `128 block + b`.
pub fn pack(words: &[u32], log_cols: usize) -> Vec<F> {
    let wc = 1 << log_cols;
    let per_block = wc << LOG_W;
    let mut f = vec![F::ZERO; words.len() / wc / 128 * per_block];
    par_chunks_mut(&mut f, per_block, |block, out| {
        let rows = &words[block * 128 * wc..(block + 1) * 128 * wc];
        // Half an element at a time, so that a word's 32 places are 32
        // shifts of 64 bits.
        for half in 0..2 {
            let mut acc = vec![0u64; per_block];
            for b in 0..64 {
                let row = &rows[(half * 64 + b) * wc..(half * 64 + b + 1) * wc];
                for (w, places) in row.iter().zip(acc.chunks_exact_mut(32)) {
                    for (j, x) in places.iter_mut().enumerate() {
                        *x |= ((*w >> j) as u64 & 1) << b;
                    }
                }
            }
            for (o, x) in out.iter_mut().zip(&acc) {
                o.0 |= (*x as u128) << (64 * half);
            }
        }
    });
    f
}

/// For each run of eight entries of `e`, the sums of its subsets: table
/// `q` at `v` is the sum of `e[8 q + t]` over the set bits `t` of `v`.
fn byte_tables(e: &[F]) -> Vec<[F; 256]> {
    (0..e.len().div_ceil(8))
        .map(|q| {
            let mut t = [F::ZERO; 256];
            for bit in 0..8.min(e.len() - 8 * q) {
                for v in 0..1 << bit {
                    t[v | 1 << bit] = t[v] + e[8 * q + bit];
                }
            }
            t
        })
        .collect()
}

fn scaled(tables: &[[F; 256]], s: F) -> Vec<[F; 256]> {
    tables.iter().map(|t| t.map(|x| x * s)).collect()
}

/// The sum of `e` over the set bits of `x`, by `tables = byte_tables(e)`.
#[inline(always)]
fn lookup(tables: &[[F; 256]], x: u128) -> F {
    let mut sum = F::ZERO;
    for (q, t) in tables.iter().enumerate() {
        sum += t[(x >> (8 * q)) as usize & 255];
    }
    sum
}

#[inline(always)]
fn lookup32(t: &[[F; 256]], x: u32) -> F {
    t[0][x as usize & 255] + t[1][(x >> 8) as usize & 255] + t[2][(x >> 16) as usize & 255] + t[3][(x >> 24) as usize]
}

type Pair = (F, F);

fn add2(a: Pair, b: Pair) -> Pair {
    (a.0 + b.0, a.1 + b.1)
}

/// The sumcheck of `sum_x eq(tau, x) (A(x) B(x) + C(x)) = 0` over the
/// operands' bits. A round binds a variable `v` and sends
/// `h(X) = sum_x' eq(tau', x') (A B + C)(r, X, x')`, with `r` the
/// challenges so far, `x'` the variables after `v` and `tau'` their part
/// of `tau`: the round's own factor `eq(tau_v, X)` is left to the
/// verifier, who checks `(1 + tau_v) h(0) + tau_v h(1)` against the last
/// round's `h(r)`.
///
/// The operands are bits, and are kept as the words they came in for as
/// long as it pays:
///
/// - **The first round** has bits on both sides of every product, so
///   `h` is a sum of weights picked by a mask.
/// - **The other bit places.** An operand's half of a group of bits,
///   under the challenges so far, is a sum over its set bits: a table
///   lookup. While a half is four bits or fewer the product of two is a
///   lookup as well; after that it is a multiplication.
/// - **Two more rounds**, across the words of a row, the same way: a
///   word under the five challenges is four lookups.
/// - **Then** the operands are tables of field elements, a 128th the
///   size of their bits, and the rounds are the usual ones.
///
/// Returns the rounds, the point, and the operands there.
fn zerocheck(
    w: Witness,
    lk: usize,
    tau: &[F],
    tr: &mut Challenger,
    pads: &mut Option<Pads>,
) -> (Vec<[F; 2]>, Vec<F>, [F; 3]) {
    let kc = 1usize << lk;
    let rows = w.rows;
    let n = tau.len();
    let (a, b, c) = (&w.a[..], &w.b[..], &w.c[..]);
    let eq_k = eq_table(&tau[LOG_W..LOG_W + lk]);
    let eq_row = eq_table(&tau[LOG_W + lk..]);
    let mut st = Rounds { claim: F::ZERO, rs: Vec::with_capacity(n), polys: Vec::with_capacity(n) };

    // Every round below sums, over the rows and a row's words, a pair
    // (to h(0), to the leading coefficient) the word gives under the
    // weights of the bit places left; `word` is that.
    let over_words = |word: &(dyn Fn(u32, u32, u32) -> Pair + Sync)| -> Pair {
        par_fold(
            rows,
            16,
            (F::ZERO, F::ZERO),
            |range| {
                let mut acc = (F::ZERO, F::ZERO);
                for row in range {
                    let mut sum = (F::ZERO, F::ZERO);
                    for (k, eq_k) in eq_k.iter().enumerate() {
                        let at = row * kc + k;
                        // Nothing comes of a word with A and C zero: a
                        // checkpoint that holds, or padding.
                        if a[at] != 0 || c[at] != 0 {
                            let (p0, p2) = word(a[at], b[at], c[at]);
                            sum = add2(sum, (*eq_k * p0, *eq_k * p2));
                        }
                    }
                    acc = add2(acc, (eq_row[row] * sum.0, eq_row[row] * sum.1));
                }
                acc
            },
            add2,
        )
    };

    // Round 0: a group is two bits, and both terms are bits.
    {
        let eq_g = eq_table(&tau[1..LOG_W]);
        let spread: Vec<F> = (0..32).map(|i| if i % 2 == 0 { eq_g[i / 2] } else { F::ZERO }).collect();
        let t = byte_tables(&spread);
        let (h0, h2) = over_words(&|a, b, c| {
            let m0 = ((a & b) ^ c) & 0x5555_5555;
            let m2 = (a ^ (a >> 1)) & (b ^ (b >> 1)) & 0x5555_5555;
            (if m0 == 0 { F::ZERO } else { lookup32(&t, m0) }, lookup32(&t, m2))
        });
        st.prove(tr, pads, tau[0], h0, h2);
    }

    // Rounds 1 to 4: a group is `2 half` bits of a word.
    for v in 1..LOG_W {
        let half = 1usize << v;
        let groups = 32 / (2 * half);
        let e = eq_table(&st.rs[..v]);
        let eq_g = eq_table(&tau[v + 1..LOG_W]);
        let mask = (1u32 << half) - 1;
        let (h0, h2) = if half <= 4 {
            // Products of two halves, by table.
            let l: Vec<F> = (0..1usize << half)
                .map(|x| (0..half).filter(|t| x >> t & 1 == 1).fold(F::ZERO, |s, t| s + e[t]))
                .collect();
            let mut products = vec![F::ZERO; groups << (2 * half)];
            let mut singles = vec![F::ZERO; groups << half];
            for g in 0..groups {
                for x in 0..1 << half {
                    singles[g << half | x] = eq_g[g] * l[x];
                    for y in 0..1 << half {
                        products[g << (2 * half) | x << half | y] = singles[g << half | x] * l[y];
                    }
                }
            }
            over_words(&|a, b, c| {
                let mut p = (F::ZERO, F::ZERO);
                for g in 0..groups {
                    let sh = g * 2 * half;
                    let (al, ah) = ((a >> sh) & mask, (a >> (sh + half)) & mask);
                    let (bl, bh) = ((b >> sh) & mask, (b >> (sh + half)) & mask);
                    let cl = (c >> sh) & mask;
                    let base = g << (2 * half);
                    p.0 += products[base | (al as usize) << half | bl as usize] + singles[g << half | cl as usize];
                    p.1 += products[base | ((al ^ ah) as usize) << half | (bl ^ bh) as usize];
                }
                p
            })
        } else {
            let plain = byte_tables(&e);
            let by_group: Vec<Vec<[F; 256]>> = eq_g.iter().map(|w| scaled(&plain, *w)).collect();
            over_words(&|a, b, c| {
                let mut p = (F::ZERO, F::ZERO);
                for (g, weighted) in by_group.iter().enumerate() {
                    let sh = g * 2 * half;
                    let (al, ah) = ((a >> sh) & mask, (a >> (sh + half)) & mask);
                    let (bl, bh) = ((b >> sh) & mask, (b >> (sh + half)) & mask);
                    let cl = (c >> sh) & mask;
                    p.0 += lookup(weighted, al as u128) * lookup(&plain, bl as u128) + lookup(weighted, cl as u128);
                    p.1 += lookup(weighted, (al ^ ah) as u128) * lookup(&plain, (bl ^ bh) as u128);
                }
                p
            })
        };
        st.prove(tr, pads, tau[v], h0, h2);
    }

    // A word under the bit places' challenges, and under those and the
    // weight of its place in a group of words.
    let word_tables = byte_tables(&eq_table(&st.rs[..LOG_W]));
    let weighted_tables = |e: &[F]| -> Vec<Vec<[F; 256]>> { e.iter().map(|s| scaled(&word_tables, *s)).collect() };
    let run = |t: &[Vec<[F; 256]>], words: &[u32]| -> F {
        let mut sum = F::ZERO;
        for (t, w) in t.iter().zip(words) {
            sum += lookup32(t, *w);
        }
        sum
    };

    // Rounds over the lowest bits of the constraint's index: a group is
    // `2 half` words of a row.
    for u in 1..=FLY {
        let v = LOG_W + u - 1;
        let half = 1usize << (u - 1);
        let t = weighted_tables(&eq_table(&st.rs[LOG_W..v]));
        let eq_g = eq_table(&tau[v + 1..LOG_W + lk]);
        let (h0, h2) = par_fold(
            rows,
            16,
            (F::ZERO, F::ZERO),
            |range| {
                let mut acc = (F::ZERO, F::ZERO);
                for row in range {
                    let mut sum = (F::ZERO, F::ZERO);
                    for (g, weight) in eq_g.iter().enumerate() {
                        let at = row * kc + g * 2 * half;
                        let (lo, hi) = (at..at + half, at + half..at + 2 * half);
                        let (a0, a1) = (run(&t, &a[lo.clone()]), run(&t, &a[hi.clone()]));
                        if a0 == F::ZERO && a1 == F::ZERO && c[lo.clone()].iter().all(|x| *x == 0) {
                            continue;
                        }
                        let (b0, b1) = (run(&t, &b[lo.clone()]), run(&t, &b[hi]));
                        let c0 = run(&t, &c[lo]);
                        sum = add2(sum, (*weight * (a0 * b0 + c0), *weight * ((a0 + a1) * (b0 + b1))));
                    }
                    acc = add2(acc, (eq_row[row] * sum.0, eq_row[row] * sum.1));
                }
                acc
            },
            add2,
        );
        st.prove(tr, pads, tau[v], h0, h2);
    }

    // The operands as tables of field elements.
    let t = weighted_tables(&eq_table(&st.rs[LOG_W..LOG_W + FLY]));
    let materialize = |words: &[u32]| -> Vec<F> {
        let mut out = vec![F::ZERO; words.len() >> FLY];
        par_chunks_mut(&mut out, 1 << 12, |i, o| {
            for (j, x) in o.iter_mut().enumerate() {
                let at = ((i << 12) + j) << FLY;
                *x = run(&t, &words[at..at + (1 << FLY)]);
            }
        });
        out
    };
    let (ta, tb, tc) = (materialize(a), materialize(b), materialize(c));
    drop(w);
    let at = table_rounds(&mut st, ta, tb, tc, &tau[LOG_W + FLY..], tr, pads);
    (st.polys, st.rs, at)
}

/// The rounds of a sumcheck of `sum_x eq(tau, x) (A(x) B(x) + C(x))`
/// over tables of field elements, a round for each of `tau`: `st` holds
/// what the rounds before left. Returns the three tables at the point.
fn table_rounds(
    st: &mut Rounds,
    mut ta: Vec<F>,
    mut tb: Vec<F>,
    mut tc: Vec<F>,
    tau: &[F],
    tr: &mut Challenger,
    pads: &mut Option<Pads>,
) -> [F; 3] {
    assert_eq!(ta.len(), 1 << tau.len());
    let mut weights = eq_table(&tau[1.min(tau.len())..]);
    for tau_v in tau {
        let (h0, h2) = par_fold(
            ta.len() / 2,
            1 << 12,
            (F::ZERO, F::ZERO),
            |range| {
                let mut acc = (F::ZERO, F::ZERO);
                for g in range {
                    let (a0, a1, b0, b1) = (ta[2 * g], ta[2 * g + 1], tb[2 * g], tb[2 * g + 1]);
                    acc.0 += weights[g] * (a0 * b0 + tc[2 * g]);
                    acc.1 += weights[g] * ((a0 + a1) * (b0 + b1));
                }
                acc
            },
            add2,
        );
        let r = st.prove(tr, pads, *tau_v, h0, h2);
        let fold = |t: &mut Vec<F>| {
            let mut out = vec![F::ZERO; t.len() / 2];
            par_chunks_mut(&mut out, 1 << 12, |i, o| {
                for (j, x) in o.iter_mut().enumerate() {
                    let g = (i << 12) + j;
                    *x = t[2 * g] + r * (t[2 * g] + t[2 * g + 1]);
                }
            });
            *t = out;
        };
        fold(&mut ta);
        fold(&mut tb);
        fold(&mut tc);
        if weights.len() > 1 {
            weights = weights.chunks_exact(2).map(|p| p[0] + p[1]).collect();
        }
    }
    [ta[0], tb[0], tc[0]]
}

/// What a check leaves to be shown of the words, as the prover holds
/// it: a table of weights for the bits of a row's own words, one for
/// those of the row before, one for those of its program, and a
/// constant, with which the check's value at its point is the constant
/// and, summed over the rows under the point's weights of them, each
/// row's bits under each table ([`crate::structure`]).
struct Tables {
    eq_j: Vec<F>,
    row: Vec<F>,
    prev: Vec<F>,
    program: Vec<F>,
    constant: F,
}

impl Tables {
    fn new(circuit: &Circuit, eq_j: &[F]) -> Tables {
        let program = if circuit.has_program() { 32 * circuit.program_width() } else { 0 };
        Tables {
            eq_j: eq_j.to_vec(),
            row: vec![F::ZERO; 32 << circuit.log_cols],
            prev: vec![F::ZERO; 32 << circuit.log_cols],
            program: vec![F::ZERO; program],
            constant: F::ZERO,
        }
    }

    fn of(&mut self, from: Source) -> &mut [F] {
        match from {
            Source::Row => &mut self.row,
            Source::Prev => &mut self.prev,
            Source::Program => &mut self.program,
            Source::Public => unreachable!("a public value is a constant"),
        }
    }
}

impl Acc<F> for Tables {
    fn eq_j(&self) -> &[F] {
        &self.eq_j
    }

    fn constant(&mut self, c: F) {
        self.constant += c;
    }

    fn term(&mut self, t: &Term, c: &F, public: &Public<F>) {
        if t.from == Source::Public {
            return self.word(t.of(public.words[t.col as usize]), c);
        }
        let weight: [F; 32] = std::array::from_fn(|j| *c * self.eq_j[j]);
        let row = &mut self.of(t.from)[(t.col as usize) << 5..(t.col as usize + 1) << 5];
        for (j, wj) in weight.iter().enumerate() {
            if let Some(at) = source_bit(t, j) {
                row[at] += *wj;
            }
        }
    }

    fn sum(&mut self, sum: &Sum, weight: &F, public: &Public<F>) {
        let public = public.words;
        self.constant += *weight * sum.constant;
        for t in &sum.terms {
            if t.from == Source::Public {
                self.constant += *weight * t.of(public);
                continue;
            }
            // Bit `b` of an element weighs `x^b`, times its constant.
            let (at, weight) = (((t.col as usize) << 5) + t.bit as usize, *weight * t.scale);
            for (bit, x) in self.of(t.from)[at..at + t.bits as usize].iter_mut().enumerate() {
                *x += weight * F(1 << bit);
            }
        }
    }
}

/// The fingerprints of every tuple one way, the leaves of its grand
/// product: place `slot` of row `row` at `slot | row << log_slots`.
fn fingerprints(circuit: &Circuit, tuples: &[Vec<Sum>], words: &[u32], fixed: &Fixed, gamma: F, alpha: F) -> Vec<F> {
    let slots = 1usize << circuit.log_slots;
    let rows = words.len() >> circuit.log_cols;
    let mut out = vec![gamma; rows * slots];
    par_chunks_mut(&mut out, slots, |i, o| {
        let at = circuit.words(words, fixed, i, rows);
        for (x, tuple) in o.iter_mut().zip(tuples) {
            let mut power = F::ONE;
            for sum in tuple {
                *x += power * sum.eval(&at);
                power *= alpha;
            }
        }
    });
    out
}

/// Elements in all the tuples `rows` rows of a circuit send and receive:
/// the degree, at most, of the bus's products as polynomials in its
/// challenges. Two different multisets of tuples have equal products
/// with a probability of that over the field's size, which the grinding
/// before the challenges brings to the level.
fn bus_degree(circuit: &Circuit, rows: usize) -> usize {
    let longest = circuit.sends.iter().chain(&circuit.receives).map(Vec::len).max().unwrap_or(0);
    if circuit.has_bus() { ((2 * rows) << circuit.log_slots) * longest.max(1) } else { 0 }
}

/// `sum_x eq(a, x) eq(b, x + 1)`, the row after all ones being row zero:
/// the weights `eq(b, .)` moved back a row, at `a`.
pub fn successor(a: &[F], b: &[F]) -> F {
    let n = a.len();
    // x and x + 1 agree above some bit t, where x has 0 and x + 1 has 1;
    // below it x is all ones and x + 1 all zeros.
    let mut above = vec![F::ONE; n + 1];
    for i in (0..n).rev() {
        above[i] = above[i + 1] * (F::ONE + a[i] + b[i]);
    }
    let mut below = F::ONE;
    let mut sum = F::ZERO;
    for t in 0..n {
        sum += below * (F::ONE + a[t]) * b[t] * above[t + 1];
        below *= a[t] * (F::ONE + b[t]);
    }
    sum + below
}

/// One sum over the words that a check leaves to be shown: `scale`
/// times the sum over the rows of `eq(point, row)`, or of `eq(point, .)`
/// at the row after if `after`, times the row's bits under `table`: the
/// bits of its own words, or of its program's if `program`.
struct Claim {
    point: Vec<F>,
    after: bool,
    scale: F,
    table: Vec<F>,
    program: bool,
}

impl Claim {
    /// Its weight of every row.
    fn weights(&self) -> Vec<F> {
        let e = eq_table(&self.point);
        let shift = self.after as usize;
        (0..e.len()).map(|x| self.scale * e[(x + shift) % e.len()]).collect()
    }
}

/// The claims a check makes, at the point's part for the rows: one for a
/// row's own words, one for the row before's, and with a program one for
/// its words, each with its table (which a verifier leaves empty).
fn claim(tables: [Vec<F>; 3], with_program: bool, point: &[F], scale: F, claims: &mut Vec<Claim>) {
    let [row, prev, program] = tables;
    let at = |table: Vec<F>, after: bool, program: bool| Claim { point: point.to_vec(), after, scale, table, program };
    claims.push(at(row, false, false));
    claims.push(at(prev, true, false));
    if with_program {
        claims.push(at(program, false, true));
    }
}

/// The sumcheck over the rows that brings every claim to one point: of
/// the sum, over the claims and the rows, of a claim's weight of a row
/// times the row's bits under its table.
struct Rows;

impl Rows {
    /// A row's bits under each claim's table, for every row, from the
    /// packed words (`f` the witness's, `program` the program's): bit `b`
    /// of an element is a row, so a block's 128 sums come of its
    /// elements' weights bucketed by their bytes.
    fn sums(f: &[F], program: &[F], claims: &[Claim], rows: usize) -> Vec<Vec<F>> {
        let parts = crate::parallel::par_map_min(rows / 128, 1, |block| {
            let mut out = Vec::with_capacity(claims.len());
            for claim in claims {
                let (from, per_block) = (if claim.program { program } else { f }, claim.table.len());
                let mut t = vec![[F::ZERO; 256]; 16];
                for (fp, m) in from[block * per_block..(block + 1) * per_block].iter().zip(&claim.table) {
                    if *m != F::ZERO {
                        for (q, tq) in t.iter_mut().enumerate() {
                            tq[(fp.0 >> (8 * q)) as usize & 255] += *m;
                        }
                    }
                }
                out.push(from_buckets(&t));
            }
            out
        });
        (0..claims.len()).map(|c| parts.iter().flat_map(|block| block[c]).collect()).collect()
    }

    /// The rounds, the point, and each claim's sum there.
    fn prove(
        claims: &[Claim],
        mut sums: Vec<Vec<F>>,
        tr: &mut Challenger,
        pads: &mut Option<Pads>,
    ) -> (Vec<Pair>, Vec<F>, Vec<F>) {
        let mut weights: Vec<Vec<F>> = claims.iter().map(Claim::weights).collect();
        let vars = claims[0].point.len();
        let (mut rounds, mut zeta) = (Vec::with_capacity(vars), Vec::with_capacity(vars));
        for _ in 0..vars {
            let (mut c0, mut c2) = (F::ZERO, F::ZERO);
            for (e, u) in weights.iter().zip(&sums) {
                for g in 0..e.len() / 2 {
                    c0 += e[2 * g] * u[2 * g];
                    c2 += (e[2 * g] + e[2 * g + 1]) * (u[2 * g] + u[2 * g + 1]);
                }
            }
            let sent = send(tr, pads, &[c0, c2]);
            rounds.push((sent[0], sent[1]));
            let r = tr.challenge();
            zeta.push(r);
            for t in weights.iter_mut().chain(sums.iter_mut()) {
                *t = t.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect();
            }
        }
        (rounds, zeta, sums.iter().map(|u| u[0]).collect())
    }
}

/// The sumcheck over a row's bits that turns a table of weights into a
/// point: of `sum_e M[e] V[e]`, where `V[e]` is bit `e` of the rows'
/// words, the rows weighted by `eq` at `zeta`. It ends at a point
/// `rho_e` with `V` there, which is the words' bits as a multilinear
/// polynomial at `(rho_e, zeta)`: a value at a point, whatever `M` was.
/// The verifier needs `M` at `rho_e` only.
struct Columns;

impl Columns {
    /// `V`: for each bit of a row, the rows' sum, from the packed words
    /// of `per_block` elements a block.
    fn values(f: &[F], per_block: usize, zeta: &[F]) -> Vec<F> {
        let low = byte_tables(&eq_table(&zeta[..LOG_PACK]));
        let high = eq_table(&zeta[LOG_PACK..]);
        par_fold(
            high.len(),
            4,
            vec![F::ZERO; per_block],
            |blocks| {
                let mut out = vec![F::ZERO; per_block];
                for block in blocks {
                    for (o, x) in out.iter_mut().zip(&f[block * per_block..(block + 1) * per_block]) {
                        *o += high[block] * lookup(&low, x.0);
                    }
                }
                out
            },
            |mut a, b| {
                a.iter_mut().zip(&b).for_each(|(x, y)| *x += *y);
                a
            },
        )
    }

    /// The rounds, the point, and `V` there.
    fn prove(mut m: Vec<F>, mut v: Vec<F>, tr: &mut Challenger, pads: &mut Option<Pads>) -> (Vec<Pair>, Vec<F>, F) {
        let vars = m.len().trailing_zeros() as usize;
        let (mut rounds, mut point) = (Vec::with_capacity(vars), Vec::with_capacity(vars));
        for _ in 0..vars {
            let (mut c0, mut c2) = (F::ZERO, F::ZERO);
            for g in 0..m.len() / 2 {
                c0 += m[2 * g] * v[2 * g];
                c2 += (m[2 * g] + m[2 * g + 1]) * (v[2 * g] + v[2 * g + 1]);
            }
            let sent = send(tr, pads, &[c0, c2]);
            rounds.push((sent[0], sent[1]));
            let r = tr.challenge();
            point.push(r);
            for t in [&mut m, &mut v] {
                *t = t.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect();
            }
        }
        (rounds, point, v[0])
    }
}

/// The map that batches the 128 sums of a ring switching: `phi(y)` is
/// the sum over `t` of `omega^t y^(2^t)`.
///
/// It is linear over the two elements, as every sum of powers
/// `y^(2^t)` is, so it goes through a sum of bits of the witness. As a
/// way of weighing 128 claims, one for each bit place `c` of an element,
/// it gives claim `c` the weight `phi(x^c)`; were the claims not all
/// true, the weighted sum of what they are off by would be a polynomial
/// in `omega` of degree 127 at most and not zero (the powers
/// `(x^c)^(2^t)` are a matrix that can be inverted, the bit places being
/// independent), so it is zero for 127 of the field's elements at most:
/// what the grinding before `omega` covers.
///
/// It is chosen for what a verifier in a circuit pays: both things the
/// verifier needs of it are sums and products of field elements, with
/// no bit of an element read.
pub fn phi<A: Alg>(omega: &A, y: &A) -> A {
    // Horner's rule from the highest power: the powers of `y` first.
    let mut powers = Vec::with_capacity(128);
    let mut p = y.clone();
    for _ in 0..128 {
        powers.push(p.clone());
        p = p.clone() * p;
    }
    let mut sum = powers.pop().expect("128 powers");
    while let Some(p) = powers.pop() {
        sum = sum * omega.clone() + p;
    }
    sum
}

/// `phi` of every byte in every place of an element: the tables with
/// which the prover applies it to millions of elements, a lookup a byte.
fn phi_tables(omega: F) -> Vec<[F; 256]> {
    let basis: Vec<F> = (0..128).map(|b| phi(&omega, &F(1 << b))).collect();
    byte_tables(&basis)
}

/// What the verifier needs of `omega`: for each `t`, the element whose
/// power `2^t` is `omega^t`. With these, a sum over `t` of `omega^t`
/// times a power `2^t` is one chain of squarings ([`switched`],
/// [`opening_weights`]). `None` if `omega` is zero.
///
/// The element for `t` is `omega^(2^(128 - t))` to the power `t`, so
/// the one below it is its square over the square of
/// `omega^(2^(127 - t))`: two products each, with the inverse of
/// `omega` squared along.
pub fn twists<A: Alg>(omega: &A) -> Option<Vec<A>> {
    let inverse = omega.inv()?;
    // For 127: the square of `omega^127`, which is `omega^128 / omega`.
    let mut high = omega.clone();
    for _ in 0..7 {
        high = high.clone() * high;
    }
    let root = high * inverse.clone();
    let mut twist = (root.clone() * root).kept();
    let mut down = (inverse.clone() * inverse).kept();
    let mut out = vec![twist.clone()];
    for t in (0..127).rev() {
        if t == 0 {
            // `omega^0`.
            out.push(omega.lift(F::ONE));
            break;
        }
        let root = twist * down.clone();
        twist = (root.clone() * root).kept();
        down = (down.clone() * down).kept();
        out.push(twist.clone());
    }
    out.reverse();
    Some(out)
}

/// The opening's weights at its challenges `r`, when the packed words
/// are opened at the point `z` and the table's part is scaled by
/// `scale`: `sum_p eq(r, p) phi(scale eq(z, p))`.
///
/// Raising to a power of two goes through sums and products, so
/// `eq(z, p)^(2^t)` is `eq` at the point `z^(2^t)`, and the sum over `p`
/// under `eq(r, p)` is `eq(r, z^(2^t))`: the weight is the sum over `t`
/// of `omega^t scale^(2^t) eq(r, z^(2^t))`.
pub fn switch_weight_at<A: Alg>(z: &[A], omega: &A, scale: &A, r: &[A]) -> A {
    assert_eq!(z.len(), r.len());
    let (mut z, mut scale) = (z.to_vec(), scale.clone());
    let mut terms = Vec::with_capacity(128);
    for _ in 0..128 {
        terms.push(crate::alg::eq(r, &z) * scale.clone());
        z = z.into_iter().map(|x| x.clone() * x).collect();
        scale = scale.clone() * scale;
    }
    let mut sum = terms.pop().expect("128 terms");
    while let Some(t) = terms.pop() {
        sum = sum * omega.clone() + t;
    }
    sum
}

/// A table's part in the opening, as the verifier holds it: the points
/// its checks left its words' bits at and its program's (empty without
/// one), the rows' point above a packed element, the variables of its
/// block and the block's number, and what its two parts are scaled by.
pub struct Block<A> {
    pub rho_e: Vec<A>,
    pub rho_p: Vec<A>,
    pub zeta_high: Vec<A>,
    pub own: usize,
    pub number: usize,
    pub scale: A,
    pub scale_program: Option<A>,
}

/// The opening's weights at its challenges `r`, for the words' and for
/// the programs': each table's [`switch_weight_at`], in its block, all
/// together.
///
/// A block's weights are zero outside it, and `phi` of zero is zero: so
/// the weight of the whole is `phi` of the table's scale times `eq` at a
/// point that names the block too, and the tables' add up inside one
/// sum over `t`. Term `t` is `omega^t` times a power `2^t`, of the
/// scale and of `eq` between the table's point and the challenges'
/// roots, `r^(2^(128 - t))`; so the whole is a chain of squarings over
/// the [`twists`], and the challenges are squared along, once for all
/// the tables.
pub fn opening_weights<A: Alg>(twists: &[A], r: &[A], blocks: &[Block<A>]) -> (A, Option<A>) {
    let add = |sum: &mut Option<A>, x: A| {
        *sum = Some(match sum.take() {
            Some(s) => x + s,
            None => x,
        })
    };
    let one = r[0].lift(F::ONE);
    let (mut words, mut programs): (Option<A>, Option<A>) = (None, None);
    let mut roots = r.to_vec();
    for t in (0..128).rev() {
        // `r^(2^(128 - t))`: for no squarings, `r` itself.
        if t > 0 {
            roots = roots.iter().map(|x| (x.clone() * x.clone()).kept()).collect();
        }
        let at = if t > 0 { &roots[..] } else { r };
        let (mut term, mut term_program) = (None, None);
        for b in blocks {
            let bits = b.rho_e.len();
            // What the words' weight and the program's share: the rows
            // above a packed element, and the block.
            let mut high = crate::alg::eq_onto(one.clone(), &at[bits..b.own], &b.zeta_high);
            for (j, x) in at[b.own..].iter().enumerate() {
                high = if b.number >> j & 1 == 1 { high * x.clone() } else { x.clone() * high.clone() + high };
            }
            let high = high.kept();
            add(&mut term, crate::alg::eq_onto(high.clone(), &at[..bits], &b.rho_e) * b.scale.clone());
            if let Some(scale) = &b.scale_program {
                let own = crate::alg::eq_onto(high, &at[LOG_PROGRAM_SHARE..bits], &b.rho_p);
                add(&mut term_program, own * scale.clone());
            }
        }
        for (sum, term) in [(&mut words, term), (&mut programs, term_program)] {
            if let Some(term) = term {
                let term = term * twists[t].clone();
                *sum = Some(match sum.take() {
                    Some(s) => s.clone() * s + term,
                    None => term,
                });
            }
        }
    }
    (words.expect("a table"), programs)
}

/// From sums bucketed by the bytes of a 128-bit key, the sums by its
/// bits: entry `b` is the sum of what was added under keys with bit `b`.
fn from_buckets(buckets: &[[F; 256]]) -> [F; 128] {
    std::array::from_fn(|b| {
        let t = &buckets[b / 8];
        (0..256).filter(|v| v >> (b % 8) & 1 == 1).fold(F::ZERO, |s, v| s + t[v])
    })
}

/// What the prover derives once a table's checks are done: the claims
/// they leave about the words, with their tables.
fn reduce(circuit: &Circuit, public: &[u32], ended: &Ended<F>) -> Vec<Claim> {
    let public = &Public { words: public, elements: None };
    let mut claims = Vec::new();
    for g in groups(circuit, public, ended, |eq_j| Tables::new(circuit, eq_j), true) {
        claim([g.acc.row, g.acc.prev, g.acc.program], circuit.has_program(), &g.point, g.scale, &mut claims);
    }
    claims
}

/// The claims about the witness's words, or about the program's, as
/// one, once they are all at one point: their tables under the powers of
/// `nu` (a claim's power is its place among all the claims), and their
/// sums `u` the same way.
fn batch(claims: &[Claim], u: &[F], nu: F, program: bool) -> (Vec<F>, F) {
    let len = claims.iter().find(|c| c.program == program).map_or(0, |c| c.table.len());
    let mut table = vec![F::ZERO; len];
    let (mut sum, mut power) = (F::ZERO, F::ONE);
    for (claim, ui) in claims.iter().zip(u) {
        if claim.program == program {
            for (t, m) in table.iter_mut().zip(&claim.table) {
                *t += power * *m;
            }
            sum += power * *ui;
        }
        power *= nu;
    }
    (table, sum)
}

/// The sums `s_b` for packed words `f` under the table `m` and the
/// blocks' weights `eq_high`: the sum of an element's weight over the
/// elements with bit `b` set, by the bytes of the elements first.
fn switch_sums(f: &[F], m: &[F], eq_high: &[F]) -> Vec<F> {
    const CHUNK: usize = 1 << 14;
    let buckets = par_fold(
        f.len(),
        CHUNK,
        vec![[F::ZERO; 256]; 16],
        |range| {
            let mut t = vec![[F::ZERO; 256]; 16];
            for p in range {
                let (yp, fp) = (eq_high[p / m.len()] * m[p % m.len()], f[p].0);
                for (q, tq) in t.iter_mut().enumerate() {
                    tq[(fp >> (8 * q)) as usize & 255] += yp;
                }
            }
            t
        },
        |mut x, y| {
            for (tx, ty) in x.iter_mut().zip(&y) {
                for (a, b) in tx.iter_mut().zip(ty) {
                    *a += *b;
                }
            }
            x
        },
    );
    from_buckets(&buckets).to_vec()
}

/// The opening's weights of `len` packed elements: `phi` of each
/// element's weight, `phi` the tables of the challenges that batch the
/// 128 sums.
fn switch_weights(len: usize, m: &[F], eq_high: &[F], phi: &[[F; 256]]) -> Vec<F> {
    const CHUNK: usize = 1 << 14;
    let mut g = vec![F::ZERO; len];
    par_chunks_mut(&mut g, CHUNK, |i, o| {
        for (j, x) in o.iter_mut().enumerate() {
            let p = i * CHUNK + j;
            *x = lookup(phi, (eq_high[p / m.len()] * m[p % m.len()]).0);
        }
    });
    g
}

/// The programs of a proof's tables, committed: made once, and the same
/// for every proof of those circuits and sizes. One polynomial, each
/// table's program in the block its words have, a sixteenth the size.
pub struct Program {
    /// Each table's program words, row after row: empty for a circuit
    /// with none.
    pub words: Vec<Vec<u32>>,
    packed: Vec<F>,
    com: Committed,
}

impl Program {
    /// The programs `words` of the tables `tables` (each a circuit and
    /// its rows; [`Circuit::program_width`] words a row), for proofs
    /// under `params`.
    pub fn of(params: &Params, domain: &Domain, tables: &[(&Circuit, usize)], words: Vec<Vec<u32>>) -> Program {
        let layout = Layout::of(tables.iter().copied()).expect("tables that can be laid out");
        assert_eq!((layout.total, words.len()), (params.m, tables.len()));
        let mut packed = vec![F::ZERO; 1 << (params.m - LOG_PROGRAM_SHARE)];
        for (i, ((circuit, rows), words)) in tables.iter().zip(&words).enumerate() {
            assert_eq!(words.len(), if circuit.has_program() { rows * circuit.program_width() } else { 0 });
            if circuit.has_program() {
                packed[layout.block(i, true)].copy_from_slice(&pack(words, circuit.log_cols - LOG_PROGRAM_SHARE));
            }
        }
        let com = pcs::commit_at(params, domain, &packed, LOG_PROGRAM_SHARE);
        Program { words, packed, com }
    }

    /// [`Program::of`] for one table.
    pub fn new(circuit: &Circuit, params: &Params, domain: &Domain, words: Vec<u32>) -> Program {
        let rows = words.len() / circuit.program_width();
        Program::of(params, domain, &[(circuit, rows)], vec![words])
    }

    /// What a verifier knows the programs by.
    pub fn root(&self) -> Digest {
        self.com.tree.root()
    }
}

/// What a proof of one table is of, beside its circuit: the program's
/// commitment, for a circuit that has one, and the public values.
#[derive(Clone, Copy, Default)]
pub struct Statement<'a> {
    pub program: Option<&'a Digest>,
    pub public: &'a [u32],
}

/// One table to prove: a circuit, the witness of its rows, and its
/// public values.
pub struct Part<'a> {
    pub circuit: &'a Circuit,
    pub witness: Witness,
    pub public: &'a [u32],
}

/// One table of a proof, as a verifier knows it.
#[derive(Clone, Copy)]
pub struct Table<'a> {
    pub circuit: &'a Circuit,
    pub rows: usize,
    pub public: &'a [u32],
}

/// The statement, into the transcript: the commitment, the programs',
/// and every table's public values.
fn begin<'a>(tr: &mut Challenger, root: &Digest, program: Option<&Digest>, public: impl Iterator<Item = &'a [u32]>) {
    tr.absorb(root);
    if let Some(program) = program {
        tr.absorb(program);
    }
    for words in public {
        tr.absorb(&words.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>());
    }
}

/// What a table's zerochecks ended at, as both sides hold it.
struct Checked {
    rho: Vec<F>,
    abc: [F; 3],
    lambda: F,
    /// The multiplications' point and operands, and the challenges that
    /// batch them and weigh them.
    products: Option<(Vec<F>, [F; 3], F, F)>,
    /// The bus's point and values, and the challenges that batch its two
    /// ways and weigh it.
    bus: Option<(Vec<F>, [F; 2], F, F)>,
}

impl Checked {
    /// What the checks ended at, with the bus's challenges.
    fn ended(&self, gamma: F, alpha: F) -> Ended<F> {
        Ended {
            rho: self.rho.clone(),
            abc: self.abc,
            lambda: self.lambda,
            products: self.products.as_ref().map(|(rho, xyz, lambda, beta)| structure::Products {
                rho: rho.clone(),
                xyz: *xyz,
                lambda: *lambda,
                beta: *beta,
            }),
            bus: self.bus.as_ref().map(|(point, values, kappa, beta)| structure::Bus {
                point: point.clone(),
                values: *values,
                gamma,
                alpha,
                kappa: *kappa,
                beta: *beta,
            }),
        }
    }
}

/// The powers of a challenge, one for each table.
fn powers(mu: F, n: usize) -> Vec<F> {
    std::iter::successors(Some(F::ONE), |p| Some(*p * mu)).take(n).collect()
}

/// The proof that the witness `w` satisfies `circuit` with the program
/// `program` and the public values `public`: [`prove_tables`] of one
/// table.
pub fn prove(
    circuit: &Circuit,
    params: &Params,
    domain: &Domain,
    w: Witness,
    program: Option<&Program>,
    public: &[u32],
) -> (Proof, Timings) {
    prove_tables(params, domain, vec![Part { circuit, witness: w, public }], program)
}

/// The proof that each of `parts` satisfies its circuit, with the
/// programs `program` if any circuit has one, and that over all of them
/// what is sent on the bus is what is received. The tables come largest
/// first; `params` are for all their words together ([`Layout`]).
pub fn prove_tables(params: &Params, domain: &Domain, parts: Vec<Part>, program: Option<&Program>) -> (Proof, Timings) {
    assert!(!params.blind, "a proof that hides what it is of wants a seed");
    prove_with(params, domain, parts, program, None)
}

/// [`prove_tables`], for a proof that hides what it is of
/// ([`crate::hidden`]; `params` say so): `seed` is where everything
/// random in it comes from, and must be random and never used again.
/// The first table's circuit must have a word to spare.
pub fn prove_hiding(
    params: &Params,
    domain: &Domain,
    parts: Vec<Part>,
    program: Option<&Program>,
    seed: [u8; 32],
) -> (Proof, Timings) {
    assert!(params.blind);
    prove_with(params, domain, parts, program, Some(seed))
}

fn prove_with(
    params: &Params,
    domain: &Domain,
    parts: Vec<Part>,
    program: Option<&Program>,
    seed: Option<[u8; 32]>,
) -> (Proof, Timings) {
    let mut times = Timings::default();
    let layout = Layout::of(parts.iter().map(|p| (p.circuit, p.witness.rows))).expect("tables that can be laid out");
    assert_eq!(layout.total, params.m);
    assert_eq!(program.is_some(), parts.iter().any(|p| p.circuit.has_program()));
    assert!(program.is_none_or(|p| p.words.len() == parts.len()));
    // Every table's words into the one polynomial, and its commitment,
    // before any challenge.
    struct Side<'a> {
        circuit: &'a Circuit,
        public: &'a [u32],
        r_rows: usize,
        /// The table's program words, and its blocks of the two
        /// polynomials.
        program: &'a [u32],
        block: std::ops::Range<usize>,
        program_block: std::ops::Range<usize>,
        words: Vec<u32>,
    }
    let mut f = vec![F::ZERO; 1 << params.m];
    let mut sides: Vec<Side> = Vec::with_capacity(parts.len());
    let mut witnesses = Vec::with_capacity(parts.len());
    let t = Instant::now();
    for (i, part) in parts.into_iter().enumerate() {
        let Part { circuit, mut witness, public } = part;
        assert_eq!(public.len(), circuit.publics);
        f[layout.block(i, false)].copy_from_slice(&pack(&witness.words, circuit.log_cols));
        let with_program = circuit.has_program();
        sides.push(Side {
            circuit,
            public,
            r_rows: witness.rows.trailing_zeros() as usize,
            program: program.filter(|_| with_program).map_or(&[], |p| &p.words[i]),
            block: layout.block(i, false),
            program_block: if with_program { layout.block(i, true) } else { 0..0 },
            // The operands are all that is wanted of the witness from
            // here, and the words for the bus.
            words: std::mem::take(&mut witness.words),
        });
        witnesses.push(witness);
    }
    times.pack += t.elapsed();
    let t = Instant::now();
    // What hides: the pads in a polynomial of their own, a random
    // polynomial that blinds, and in the first table's last word the
    // corners and the leaves' cover.
    let places = seed.map(|_| {
        let places = Places::of(sides.iter().map(|s| (s.circuit, 1 << s.r_rows)));
        places.expect("a first table with a word to spare and rows enough")
    });
    let room = seed.map(|_| Room::of(params).expect("a polynomial large enough for the pads"));
    let mut pads: Option<Pads> = None;
    let (mut blinder, mut pad_values, mut corners): (Vec<F>, Vec<F>, F) = (Vec::new(), Vec::new(), F::ZERO);
    let mut pad_blinder: Vec<F> = Vec::new();
    if let (Some(seed), Some(places), Some(room)) = (seed, &places, &room) {
        let stream = Stream(seed);
        let (made, values) = Pads::new(room, &stream, params.round_bits);
        (pads, pad_values) = (Some(made), values);
        for group in 0..places.groups {
            for bit in 0..32 {
                f[places.at(&layout, group, bit)] = stream.at(1 << 40 | (group * 32 + bit) as u64);
            }
        }
        corners = crate::hidden::WEIGHED.iter().fold(F::ZERO, |sum, i| sum + f[places.corner(&layout, *i)]);
        blinder = vec![F::ZERO; room.len];
        crate::parallel::par_fill(&mut blinder, |i| stream.at(1 << 41 | i as u64));
        pad_blinder = vec![F::ZERO; room.len];
        crate::parallel::par_fill(&mut pad_blinder, |i| stream.at(1 << 42 | i as u64));
    }
    let com = match seed {
        Some(_) => pcs::commit_blind(params, domain, &f, &blinder, &pad_values, &pad_blinder),
        None => pcs::commit(params, domain, &f),
    };
    times.commit += t.elapsed();
    let root = com.tree.root();
    let packed_program: &[F] = program.map_or(&[], |p| &p.packed);
    let mut tr = Challenger::new(&label(params, sides.iter().map(|s| 1 << s.r_rows)));
    begin(&mut tr, &root, program.map(Program::root).as_ref(), sides.iter().map(|s| s.public));

    // Each table's constraints and multiplications.
    let t = Instant::now();
    let mut proofs: Vec<TableProof> = Vec::with_capacity(sides.len());
    let mut checked: Vec<Checked> = Vec::with_capacity(sides.len());
    for (s, mut w) in sides.iter().zip(witnesses) {
        let (circuit, r_rows) = (s.circuit, s.r_rows);
        let n = LOG_W + circuit.log_constraints + r_rows;
        let tau_nonce = tr.grind(pcs::grinding(params.round_bits, n));
        let tau: Vec<F> = (0..n).map(|_| tr.challenge()).collect();
        let (x, y, z) = (std::mem::take(&mut w.x), std::mem::take(&mut w.y), std::mem::take(&mut w.z));
        let (rounds, rho, abc) = zerocheck(w, circuit.log_constraints, &tau, &mut tr, &mut pads);
        let abc_sent = send(&mut tr, &mut pads, &abc);
        if let Some(pads) = &mut pads {
            pads.product_sum(vec![(F::ONE, abc[0], abc[1])]);
        }
        let lambda = tr.challenge();
        // The multiplications: the same check, over tables as they are.
        let (mut product_nonce, mut product_rounds, mut xyz_sent) = (0, Vec::new(), vec![F::ZERO; 3]);
        let mut products = None;
        if !circuit.products.is_empty() {
            let n2 = circuit.log_products + r_rows;
            product_nonce = tr.grind(pcs::grinding(params.round_bits, n2));
            let tau2: Vec<F> = (0..n2).map(|_| tr.challenge()).collect();
            let mut st = Rounds { claim: F::ZERO, rs: Vec::new(), polys: Vec::new() };
            let xyz = table_rounds(&mut st, x, y, z, &tau2, &mut tr, &mut pads);
            product_rounds = st.polys;
            xyz_sent = send(&mut tr, &mut pads, &xyz);
            if let Some(pads) = &mut pads {
                pads.product_sum(vec![(F::ONE, xyz[0], xyz[1])]);
            }
            products = Some((st.rs, xyz, tr.challenge(), tr.challenge()));
        }
        checked.push(Checked { rho, abc, lambda, products, bus: None });
        proofs.push(TableProof {
            tau_nonce,
            product_nonce,
            rounds,
            abc: [abc_sent[0], abc_sent[1], abc_sent[2]],
            product_rounds,
            xyz: [xyz_sent[0], xyz_sent[1], xyz_sent[2]],
            bus: grand::Proof::default(),
            row_rounds: Vec::new(),
            u: Vec::new(),
            col_rounds: Vec::new(),
            v: F::ZERO,
            col_rounds_program: Vec::new(),
            v_program: F::ZERO,
            s: Vec::new(),
            s_program: Vec::new(),
        });
    }

    // The bus, over all the tables: what was sent is what was received,
    // by their products under one pair of challenges.
    let degree: usize = sides.iter().map(|s| bus_degree(s.circuit, 1 << s.r_rows)).sum();
    let (mut bus_nonce, mut gamma, mut alpha) = (0, F::ZERO, F::ZERO);
    let mut whole: [Option<F>; 2] = [None, None];
    if degree > 0 {
        bus_nonce = tr.grind(pcs::grinding(params.round_bits, degree));
        (gamma, alpha) = (tr.challenge(), tr.challenge());
    }
    for (i, s) in sides.iter_mut().enumerate() {
        if s.circuit.has_bus() {
            let fixed = Fixed { program: s.program, public: s.public };
            let sent = fingerprints(s.circuit, &s.circuit.sends, &s.words, &fixed, gamma, alpha);
            let received = fingerprints(s.circuit, &s.circuit.receives, &s.words, &fixed, gamma, alpha);
            let (proof, pi, values, own) = grand::prove(vec![sent, received], &mut tr, &mut pads);
            proofs[i].bus = proof;
            // The tables' products, multiplied as the verifier does.
            if let Some(pads) = &mut pads {
                for (all, own) in whole.iter_mut().zip(own) {
                    *all = Some(match *all {
                        Some(p) => pads.mul(&mut tr, p, own),
                        None => own,
                    });
                }
            }
            checked[i].bus = Some((pi, [values[0], values[1]], tr.challenge(), tr.challenge()));
        }
        s.words = Vec::new();
    }
    times.zerocheck += t.elapsed();

    // Each table's claims to one point, then to the words at a point,
    // then the 128 sums of the packed words: for the witness's words and
    // for the program's.
    let t = Instant::now();
    let mut points: Vec<(Vec<F>, Vec<F>, Vec<F>)> = Vec::with_capacity(sides.len());
    // Every table's sums as they are, for a proof that sends them hidden.
    let mut summed: Vec<(Vec<F>, Vec<F>)> = Vec::new();
    for (i, s) in sides.iter().enumerate() {
        let c = &checked[i];
        let (words, program_words) = (&f[s.block.clone()], &packed_program[s.program_block.clone()]);
        let with_program = s.circuit.has_program();
        let claims = reduce(s.circuit, s.public, &c.ended(gamma, alpha));
        let sums = Rows::sums(words, program_words, &claims, 1 << s.r_rows);
        let (row_rounds, zeta, u) = Rows::prove(&claims, sums, &mut tr, &mut pads);
        let u_sent = send(&mut tr, &mut pads, &u);
        let nu = tr.challenge();
        let (m, _) = batch(&claims, &u, nu, false);
        let (m_program, _) = batch(&claims, &u, nu, true);
        let values = Columns::values(words, m.len(), &zeta);
        let (col_rounds, rho_e, v) = Columns::prove(m, values, &mut tr, &mut pads);
        let (mut col_rounds_program, mut rho_p, mut v_program) = (Vec::new(), Vec::new(), F::ZERO);
        if with_program {
            let values = Columns::values(program_words, m_program.len(), &zeta);
            (col_rounds_program, rho_p, v_program) = Columns::prove(m_program, values, &mut tr, &mut pads);
        }
        let v_sent = send(&mut tr, &mut pads, &[v, v_program]);
        let eq_high = eq_table(&zeta[LOG_PACK..]);
        let sums = switch_sums(words, &eq_table(&rho_e), &eq_high);
        let sums_program =
            if with_program { switch_sums(program_words, &eq_table(&rho_p), &eq_high) } else { Vec::new() };
        let sums_sent = send(&mut tr, &mut pads, &sums);
        let sums_program_sent = send(&mut tr, &mut pads, &sums_program);
        let proof = &mut proofs[i];
        (proof.row_rounds, proof.u, proof.col_rounds, proof.v) = (row_rounds, u_sent, col_rounds, v_sent[0]);
        (proof.col_rounds_program, proof.v_program) = (col_rounds_program, v_sent[1]);
        (proof.s, proof.s_program) = (sums_sent, sums_program_sent);
        if pads.is_some() {
            summed.push((sums, sums_program));
        }
        points.push((zeta, rho_e, rho_p));
    }
    // The weights the batching of the sums leaves the opening to prove a
    // sum under: each table's in its block, the tables under the powers
    // of a challenge; the same for the programs.
    let omega_nonce = tr.grind(pcs::grinding(params.round_bits, 126 + 2 * sides.len()));
    let omega = tr.challenge();
    let phi = phi_tables(omega);
    // A scale for each table's words, then one for each table's program.
    let scales = powers(tr.challenge(), 2 * sides.len());
    if let Some(pads) = &mut pads {
        // What the sums come to, shown without the sums.
        let mut all = vec![F::ZERO; 128];
        for (i, (own, own_program)) in summed.iter().enumerate() {
            for (sums, scale) in [(own, scales[i]), (own_program, scales[sides.len() + i])] {
                all.iter_mut().zip(sums).for_each(|(x, sb)| *x += scale * *sb);
            }
        }
        pads.switched(&mut tr, &twists(&omega).expect("a challenge that is not zero"), &all);
    }
    let weights = |program: bool| {
        let mut g = vec![F::ZERO; if program { packed_program.len() } else { f.len() }];
        for (i, s) in sides.iter().enumerate().filter(|(_, s)| !program || s.circuit.has_program()) {
            let (zeta, rho_e, rho_p) = &points[i];
            let block = if program { s.program_block.clone() } else { s.block.clone() };
            let at = eq_table(if program { rho_p } else { rho_e });
            // The table's scale goes inside the map: on the side of the
            // sums' elements, where a verifier can batch the tables'
            // sums before it reads them the other way.
            let scale = scales[if program { sides.len() + i } else { i }];
            let eq_high: Vec<F> = eq_table(&zeta[LOG_PACK..]).iter().map(|e| scale * *e).collect();
            let own = switch_weights(block.len(), &at, &eq_high, &phi);
            g[block].copy_from_slice(&own);
        }
        g
    };
    // The verifier finds what the words' sum and the programs' come to
    // together; the prover says how much of it is the programs'.
    let joiners: Vec<pcs::Joiner> = program
        .map(|p| pcs::Joiner { com: &p.com, f: &p.packed, weights: weights(true), round: LOG_PROGRAM_SHARE })
        .into_iter()
        .collect();
    let split = joiners.first().map_or(F::ZERO, |j| pcs::inner_product(j.f, &j.weights));
    tr.absorb_fs(&[split]);
    let mut first = weights(false);
    let mut proof = Proof {
        root,
        tables: proofs,
        bus_nonce,
        omega_nonce,
        split,
        hidden: Sent::default(),
        pcs: pcs::Proof::empty(),
    };
    let mut pad_weights = Vec::new();
    if let (Some(mut pads), Some(places), Some(room)) = (pads, &places, &room) {
        // The products; then what a verifier makes of all that was
        // sent, for the pads' weights in the sum to open: found by
        // being one.
        pads.settle(&mut tr);
        proof.hidden = std::mem::take(&mut pads.sent);
        let tables: Vec<Table> =
            sides.iter().map(|s| Table { circuit: s.circuit, rows: 1 << s.r_rows, public: s.public }).collect();
        let program_root = program.map(Program::root);
        let mut again = Challenger::new(&label(params, tables.iter().map(|t| t.rows)));
        let (_, target, equations) =
            hidden_front(params, &tables, program_root.as_ref(), &proof, &mut again, &mut Direct)
                .expect("the prover's own checks hold");
        debug_assert_eq!(again.clone().challenge(), tr.clone().challenge(), "the two transcripts agree");
        proof.hidden.nonces[2] = again.clone().grind(pcs::grinding(params.round_bits, equations.len() + 1));
        proof.hidden.corners = corners;
        let (_, weights, chi) =
            hidden_batch(params, &proof.hidden, target, equations, &mut again).expect("a nonce that grinds");
        tr = again;
        pad_weights = Pads::weights(room, &weights);
        for corner in crate::hidden::WEIGHED {
            first[places.corner(&layout, corner)] += chi;
        }
    }
    times.reduce += t.elapsed();

    let t = Instant::now();
    let step = params.steps()[0];
    let good = |indices: &[usize]| places.is_some_and(|p| p.good(step, indices));
    let blind = seed.map(|_| pcs::Blind {
        g: &blinder,
        pads: &pad_values,
        g2: &pad_blinder,
        weights: pad_weights,
        good: &good,
    });
    proof.pcs = pcs::open_weighted(params, domain, &com, &f, first, joiners, blind, &mut tr);
    times.open += t.elapsed();
    (proof, times)
}

/// Whether `proof` shows a committed witness of `rows` rows to satisfy
/// `circuit` for `statement`: [`verify_tables`] of one table. `domain`
/// needs no tables.
pub fn verify(
    circuit: &Circuit,
    params: &Params,
    domain: &Domain,
    rows: usize,
    proof: &Proof,
    statement: &Statement,
) -> Option<Work> {
    verify_tables(params, domain, &[Table { circuit, rows, public: statement.public }], statement.program, proof)
}

/// Whether `proof` shows committed witnesses to satisfy each of
/// `tables`, with the programs committed as `program` and one bus
/// between them.
pub fn verify_tables(
    params: &Params,
    domain: &Domain,
    tables: &[Table],
    program: Option<&Digest>,
    proof: &Proof,
) -> Option<Work> {
    let named = label(params, tables.iter().map(|t| t.rows));
    let (mut tr, mut opens) = (Challenger::new(&named), Batched::default());
    check(params, domain, tables, program, proof, &mut tr, &mut opens)?;
    Some(Work { compressions: tr.compressions + opens.compressions })
}

/// What a verifier went through, for a circuit that is to do the same.
pub struct Replay {
    pub work: Work,
    /// Every step of its transcript, in order.
    pub log: Vec<Step>,
    /// The queries' leaves in the first committed codeword.
    pub indices: Vec<usize>,
}

/// [`verify_tables`], keeping what the verifier went through.
pub fn verify_logged(
    params: &Params,
    domain: &Domain,
    tables: &[Table],
    program: Option<&Digest>,
    proof: &Proof,
) -> Option<Replay> {
    let named = label(params, tables.iter().map(|t| t.rows));
    let (mut tr, mut opens) = (Challenger::recording(&named), Batched::default());
    let indices = check(params, domain, tables, program, proof, &mut tr, &mut opens)?.indices;
    let work = Work { compressions: tr.compressions + opens.compressions };
    Some(Replay { work, log: tr.log.unwrap_or_default(), indices })
}

/// The rounds of a sumcheck of a product of two tables, each round the
/// constant and the leading coefficient: the point, and the last claim.
fn pair_rounds<A: Alg, T: Transcript<A>>(tr: &mut T, rounds: &[Pair], target: A) -> (Vec<A>, A) {
    let mut claim = target;
    let mut point = Vec::with_capacity(rounds.len());
    for (c0, c2) in rounds {
        let c = tr.elements(&[*c0, *c2]);
        let r = tr.challenge();
        // The middle coefficient is the claim less the others.
        claim = ((claim + c[1].clone()) + c[1].clone() * r.clone()) * r.clone() + c[0].clone();
        point.push(r);
    }
    (point, claim)
}

/// The sum of `xs` under `weights`.
fn weigh<A: Alg>(xs: &[A], weights: &[A]) -> A {
    let first = xs[0].clone() * weights[0].clone();
    xs.iter().zip(weights).skip(1).fold(first, |s, (x, w)| x.clone() * w.clone() + s)
}

/// What [`check`] leaves, of a proof it took: the queries' leaves in
/// the first committed codeword, and the statement as the verifier's
/// arithmetic holds it, for a circuit that is to say what it verified:
/// the programs' root, and each table's public values (for the field's
/// own verifier, which knows them, none).
pub struct Taken<A> {
    pub indices: Vec<usize>,
    pub program: Option<[A; 2]>,
    pub publics: Vec<Option<Vec<A>>>,
}

/// The verifier: whether `proof` shows what [`verify_tables`] says.
///
/// It is written once, over any arithmetic, transcript and way of
/// opening leaves. With the field's own it verifies. With a machine's
/// values, a transcript that is rows of a hash table and openings that
/// are rows too ([`crate::alg`]), running it makes the circuit that
/// verifies: every `is` an assertion, and the proof's values the
/// witness. What it reads of the proof without the arithmetic is shape
/// only: lengths, and the parts that must be absent.
pub fn check<A: Alg, T: Transcript<A>, O: Opens<A>>(
    params: &Params,
    domain: &Domain,
    tables: &[Table],
    program: Option<&Digest>,
    proof: &Proof,
    tr: &mut T,
    opens: &mut O,
) -> Option<Taken<A>> {
    check_with(params, domain, tables, program, proof, tr, opens, &mut Direct)
}

/// [`check`], with whoever reads the circuits' constraints given: a
/// circuit that verifies several proofs reads each circuit once for
/// them all ([`crate::reading`]).
#[allow(clippy::too_many_arguments)]
pub fn check_with<A: Alg, T: Transcript<A>, O: Opens<A>, R: structure::Reader<A>>(
    params: &Params,
    domain: &Domain,
    tables: &[Table],
    program: Option<&Digest>,
    proof: &Proof,
    tr: &mut T,
    opens: &mut O,
    reader: &mut R,
) -> Option<Taken<A>> {
    // Every table's shape, and its place in the polynomial.
    let layout = Layout::of(tables.iter().map(|t| (t.circuit, t.rows)))?;
    if layout.total != params.m
        || proof.tables.len() != tables.len()
        || program.is_some() != tables.iter().any(|t| t.circuit.has_program())
    {
        return None;
    }
    for (table, part) in tables.iter().zip(&proof.tables) {
        let with_program = table.circuit.has_program();
        if table.public.len() != table.circuit.publics
            || part.s.len() != 128
            || part.s_program.len() != if with_program { 128 } else { 0 }
        {
            return None;
        }
    }
    if params.blind != (proof.hidden != Sent::default()) || (program.is_none() && proof.split != F::ZERO) {
        return None;
    }
    if !params.blind {
        let front = front(params, tables, program, proof, tr, reader)?;
        let target = if program.is_some() { front.total.clone() + front.split.clone() } else { front.total.clone() };
        return back(params, domain, tables, &layout, program, proof, front, target, None, tr, opens);
    }
    // A proof that hides what it is of: the same checks over values
    // the verifier holds under pads, then the pads' part of the sum the
    // opening shows.
    let places = Places::of(tables.iter().map(|t| (t.circuit, t.rows)))?;
    let room = Room::of(params)?;
    let (front, target, equations) = hidden_front(params, tables, program, proof, tr, reader)?;
    let (target, weights, chi) = hidden_batch(params, &proof.hidden, target, equations, tr)?;
    let corners = |r: &[A]| places.corners_at(&layout, r, &chi);
    let pads = |r: &[A]| room.weight_at(r, &weights);
    back(params, domain, tables, &layout, program, proof, front, target, Some((&corners, &pads)), tr, opens)
}

/// What a verifier holds once every table's checks are done, before the
/// opening: the statement as its arithmetic took it in, each table's
/// points, the challenges that batch the tables' sums, and what the
/// sums come to, the words' and the programs' together and the
/// programs' alone.
struct Front<A> {
    root_at: [A; 2],
    program_at: Option<[A; 2]>,
    publics: Vec<Option<Vec<A>>>,
    points: Vec<(Vec<A>, Vec<A>, Vec<A>)>,
    scales: Vec<A>,
    twists: Vec<A>,
    total: A,
    split: A,
}

/// The first part of [`check_with`] for a proof that hides what it is
/// of: every check before the opening, over values held under pads
/// ([`crate::hidden`]). With what the verifier then holds, as it knows
/// it: what the opening must show, as a form over the pads, and the
/// equations over them.
#[allow(clippy::type_complexity)]
fn hidden_front<A: Alg, T: Transcript<A>, R: structure::Reader<A>>(
    params: &Params,
    tables: &[Table],
    program: Option<&Digest>,
    proof: &Proof,
    tr: &mut T,
    reader: &mut R,
) -> Option<(Front<A>, Masked<A>, Vec<(A, Vec<(u32, A)>)>)> {
    let mut padded = Padded::new(tr, &proof.hidden, params.round_bits);
    let f = front(params, tables, program, proof, &mut padded, &mut crate::hidden::Unmasked(reader))?;
    let target = if program.is_some() { f.total.clone() + f.split.clone() } else { f.total.clone() };
    padded.settle()?;
    let equations = padded.finish()?;
    let open = |xs: Vec<Masked<A>>| xs.into_iter().map(Masked::open).collect::<Option<Vec<A>>>();
    let pair = |[a, b]: [Masked<A>; 2]| Some([a.open()?, b.open()?]);
    let mut publics = Vec::with_capacity(f.publics.len());
    for public in f.publics {
        publics.push(match public {
            Some(elements) => Some(open(elements)?),
            None => None,
        });
    }
    let mut points = Vec::with_capacity(f.points.len());
    for (zeta, rho_e, rho_p) in f.points {
        points.push((open(zeta)?, open(rho_e)?, open(rho_p)?));
    }
    let front = Front {
        root_at: pair(f.root_at)?,
        program_at: match f.program_at {
            Some(at) => Some(pair(at)?),
            None => None,
        },
        publics,
        points,
        scales: open(f.scales)?,
        twists: open(f.twists)?,
        total: target.known.clone(),
        split: f.split.open()?,
    };
    Some((front, target, equations))
}

/// The second part: the equations and what the opening must show, made
/// one sum under the powers of a challenge; and the corners. What the
/// opening must then show, each pad's weight in it, and the corners'.
#[allow(clippy::type_complexity)]
fn hidden_batch<A: Alg, T: Transcript<A>>(
    params: &Params,
    sent: &Sent,
    target: Masked<A>,
    equations: Vec<(A, Vec<(u32, A)>)>,
    tr: &mut T,
) -> Option<(A, BTreeMap<u32, A>, A)> {
    if !tr.ground(pcs::grinding(params.round_bits, equations.len() + 1), sent.nonces[2]) {
        return None;
    }
    let xi = tr.challenge();
    let mut known = target.known;
    let mut weights: BTreeMap<u32, A> = target.pads.into_iter().collect();
    let mut power = xi.clone();
    for (constant, pads) in equations {
        known = constant * power.clone() + known;
        for (id, w) in pads {
            let term = w * power.clone();
            let sum = match weights.remove(&id) {
                Some(x) => term + x,
                None => term,
            };
            weights.insert(id, sum);
        }
        power = (power * xi.clone()).kept();
    }
    // The corners: their sum as the prover says it, weighed with the
    // rest by a challenge.
    let corners = tr.elements(&[sent.corners]).swap_remove(0);
    let chi = tr.challenge();
    Some((chi.clone() * corners + known, weights, chi))
}

/// Every check of [`check_with`] before the opening.
fn front<A: Alg, T: Transcript<A>, R: structure::Reader<A>>(
    params: &Params,
    tables: &[Table],
    program: Option<&Digest>,
    proof: &Proof,
    tr: &mut T,
    reader: &mut R,
) -> Option<Front<A>> {
    // The statement: the commitment, the programs', the public values.
    let root_at = tr.digest(&proof.root);
    let program_at = program.map(|p| tr.digest(p));
    let publics: Vec<Public<A>> =
        tables.iter().map(|t| Public { words: t.public, elements: tr.public(t.public) }).collect();
    let zero = root_at[0].lift(F::ZERO);

    // Each table's constraints and multiplications.
    let mut ended: Vec<Ended<A>> = Vec::with_capacity(tables.len());
    for (table, part) in tables.iter().zip(&proof.tables) {
        let circuit = table.circuit;
        let r_rows = table.rows.trailing_zeros() as usize;
        let n = LOG_W + circuit.log_constraints + r_rows;
        if !tr.ground(pcs::grinding(params.round_bits, n), part.tau_nonce) {
            return None;
        }
        let tau: Vec<A> = (0..n).map(|_| tr.challenge()).collect();
        let (rho, claim) = crate::alg::rounds(tr, &part.rounds, &tau, zero.clone())?;
        let abc = tr.elements(&part.abc);
        if !tr.product_sum(vec![(None, abc[0].clone(), abc[1].clone())], Some(abc[2].clone()), &claim) {
            return None;
        }
        let lambda = tr.challenge();
        let mut products = None;
        if circuit.products.is_empty() {
            if !part.product_rounds.is_empty() || part.xyz != [F::ZERO; 3] || part.product_nonce != 0 {
                return None;
            }
        } else {
            let n2 = circuit.log_products + r_rows;
            if !tr.ground(pcs::grinding(params.round_bits, n2), part.product_nonce) {
                return None;
            }
            let tau2: Vec<A> = (0..n2).map(|_| tr.challenge()).collect();
            let (rho, claim) = crate::alg::rounds(tr, &part.product_rounds, &tau2, zero.clone())?;
            let xyz = tr.elements(&part.xyz);
            if !tr.product_sum(vec![(None, xyz[0].clone(), xyz[1].clone())], Some(xyz[2].clone()), &claim) {
                return None;
            }
            let xyz = [xyz[0].clone(), xyz[1].clone(), xyz[2].clone()];
            products = Some(structure::Products { rho, xyz, lambda: tr.challenge(), beta: tr.challenge() });
        }
        let abc = [abc[0].clone(), abc[1].clone(), abc[2].clone()];
        ended.push(Ended { rho, abc, lambda, products, bus: None });
    }

    // The bus: over all the tables, what was sent is what was received.
    let degree: usize = tables.iter().map(|t| bus_degree(t.circuit, t.rows)).sum();
    let mut fingerprint = None;
    if degree > 0 {
        if !tr.ground(pcs::grinding(params.round_bits, degree), proof.bus_nonce) {
            return None;
        }
        fingerprint = Some((tr.challenge(), tr.challenge()));
    } else if proof.bus_nonce != 0 {
        return None;
    }
    let (mut sent, mut received): (Option<A>, Option<A>) = (None, None);
    for (i, (table, part)) in tables.iter().zip(&proof.tables).enumerate() {
        let circuit = table.circuit;
        if let (true, Some((gamma, alpha))) = (circuit.has_bus(), &fingerprint) {
            let depth = circuit.log_slots + table.rows.trailing_zeros() as usize;
            let (products, point, values) = grand::verify(&part.bus, 2, depth, tr)?;
            for (all, own) in [&mut sent, &mut received].into_iter().zip(products) {
                *all = Some(match all.take() {
                    Some(p) => tr.mul(&p, &own),
                    None => own,
                });
            }
            ended[i].bus = Some(structure::Bus {
                point,
                values: [values[0].clone(), values[1].clone()],
                gamma: gamma.clone(),
                alpha: alpha.clone(),
                kappa: tr.challenge(),
                beta: tr.challenge(),
            });
        } else if part.bus != grand::Proof::default() {
            return None;
        }
    }
    if let (Some(sent), Some(received)) = (sent, received)
        && !sent.is(&received)
    {
        return None;
    }

    // Each table's claims to one point, then to the words at a point,
    // against the circuit's tables there, a term at a time; then the 128
    // sums of the packed words.
    let mut points: Vec<(Vec<A>, Vec<A>, Vec<A>)> = Vec::with_capacity(tables.len());
    let mut sums: Vec<(Vec<A>, Vec<A>)> = Vec::with_capacity(tables.len());
    for (i, (table, part)) in tables.iter().zip(&proof.tables).enumerate() {
        let (circuit, public) = (table.circuit, &publics[i]);
        let r_rows = table.rows.trailing_zeros() as usize;
        let with_program = circuit.has_program();
        let (claims, target) = structure::reduce_claims(circuit, public, &ended[i]);
        // The rows' sumcheck: every claim to the one point `zeta`.
        if part.row_rounds.len() != r_rows || part.u.len() != claims.len() {
            return None;
        }
        let (zeta, claim) = pair_rounds(tr, &part.row_rounds, target);
        let u = tr.elements(&part.u);
        let weights: Vec<A> = claims.iter().map(|c| c.weight_at(&zeta)).collect();
        if !weigh(&u, &weights).is(&claim) {
            return None;
        }
        // The claims about the witness's words as one, and those about
        // the program's: under the powers of `nu`, a claim's power its
        // place among them all.
        let nu = crate::alg::powers(&tr.challenge(), claims.len());
        let batched = |xs: &[A], program: bool| {
            let of = (xs.iter().zip(&nu).zip(&claims)).filter(|(_, c)| c.program == program);
            of.map(|((x, power), _)| x.clone() * power.clone()).reduce(|s, x| x + s)
        };
        // The columns' sumchecks: each to the words' bits at a point.
        let bits = LOG_W + circuit.log_cols;
        if part.col_rounds.len() != bits {
            return None;
        }
        let (rho_e, claim) = pair_rounds(tr, &part.col_rounds, batched(&u, false).expect("claims about the words"));
        let (rho_p, claim_program) = if with_program {
            if part.col_rounds_program.len() != bits - LOG_PROGRAM_SHARE {
                return None;
            }
            let target = batched(&u, true).expect("claims about the program");
            let (rho_p, claim) = pair_rounds(tr, &part.col_rounds_program, target);
            (rho_p, Some(claim))
        } else if part.col_rounds_program.is_empty() && (params.blind || part.v_program == F::ZERO) {
            // (Under a pad, nothing is zero.)
            (Vec::new(), None)
        } else {
            return None;
        };
        let at = structure::tables_at(circuit, public, &ended[i], &rho_e, &rho_p, reader);
        let v = tr.elements(&[part.v, part.v_program]);
        if !(batched(&at, false).expect("claims about the words") * v[0].clone()).is(&claim) {
            return None;
        }
        if let Some(claim) = claim_program
            && !(batched(&at, true).expect("claims about the program") * v[1].clone()).is(&claim)
        {
            return None;
        }
        // The bits at a point are the 128 sums' under the point's low
        // part.
        let s = tr.elements(&part.s);
        let s_program = tr.elements(&part.s_program);
        let eq_low = crate::alg::eq_table(&zeta[..LOG_PACK]);
        if !weigh(&s, &eq_low).is(&v[0]) || (with_program && !weigh(&s_program, &eq_low).is(&v[1])) {
            return None;
        }
        points.push((zeta, rho_e, rho_p));
        sums.push((s, s_program));
    }

    // The opening: every table's words in the one polynomial, and the
    // programs joining it.
    if !tr.ground(pcs::grinding(params.round_bits, 126 + 2 * tables.len()), proof.omega_nonce) {
        return None;
    }
    let omega = tr.challenge();
    // A scale for each table's words, then one for each table's program.
    let scales = crate::alg::powers(&tr.challenge(), 2 * tables.len());
    // Every table's sums as one set of 128, each scaled: scaling them is
    // scaling the weights inside the map, which is linear over the bits
    // only.
    let mut all: Option<Vec<A>> = None;
    for (i, (s, s_program)) in sums.iter().enumerate() {
        for (own, scale) in [(s, &scales[i]), (s_program, &scales[tables.len() + i])] {
            if !own.is_empty() {
                all = Some(match all {
                    Some(all) => all.into_iter().zip(own).map(|(x, sb)| sb.clone() * scale.clone() + x).collect(),
                    None => own.iter().map(|sb| sb.clone() * scale.clone()).collect(),
                });
            }
        }
    }
    let twists = twists(&omega)?;
    let total = tr.switched(&twists, &all.expect("a table"));
    // What the batched sums come to is the words' sum and the programs':
    // the prover says the programs', which anyone could work out.
    let split = tr.plain(&[proof.split]).swap_remove(0);
    let publics = publics.into_iter().map(|p| p.elements).collect();
    Some(Front { root_at, program_at, publics, points, scales, twists, total, split })
}

/// The last part of [`check_with`]: the opening, of `target`, and what
/// its weights are at its challenges. For a proof that hides, `hiding`
/// gives the corners' weight at the opening's challenges, and the pads'
/// at those of their polynomial's variables.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn back<A: Alg, T: Transcript<A>, O: Opens<A>>(
    params: &Params,
    domain: &Domain,
    tables: &[Table],
    layout: &Layout,
    program: Option<&Digest>,
    proof: &Proof,
    front: Front<A>,
    target: A,
    hiding: Option<(&dyn Fn(&[A]) -> A, &dyn Fn(&[A]) -> Option<A>)>,
    tr: &mut T,
    opens: &mut O,
) -> Option<Taken<A>> {
    let Front { root_at, program_at, publics, points, scales, twists, split, .. } = front;
    let joined: Vec<pcs::Joined<A>> = (program.zip(program_at.clone()))
        .map(|(root, at)| pcs::Joined { root, at, target: split.clone(), round: LOG_PROGRAM_SHARE })
        .into_iter()
        .collect();
    let opened = pcs::verify_weighted(params, domain, (&proof.root, root_at), target, &proof.pcs, &joined, tr, opens)?;
    // What the opening's weights are at its challenges: a table's words
    // are opened at its columns' point and its rows' high part, in its
    // block.
    let blocks: Vec<Block<A>> = (points.into_iter().enumerate())
        .map(|(i, (zeta, rho_e, rho_p))| Block {
            rho_e,
            rho_p,
            zeta_high: zeta[LOG_PACK..].to_vec(),
            own: layout.m[i],
            number: layout.offset[i] >> layout.m[i],
            scale: scales[i].clone(),
            scale_program: tables[i].circuit.has_program().then(|| scales[tables.len() + i].clone()),
        })
        .collect();
    let (mut weight, weight_program) = opening_weights(&twists, &opened.r, &blocks);
    if let Some((corners, _)) = hiding {
        weight = corners(&opened.r) + weight;
    }
    let mut expect = opened.final_value.clone() * weight;
    if let (Some((_, pads)), Some(last)) = (hiding, &opened.pad_final) {
        // The pads' polynomial is its values where the first leaf's
        // variables are zero: it and its weights are each times one and
        // each of those challenges.
        let first = params.steps()[0];
        let one = opened.r[0].lift(F::ONE);
        let scale = opened.r[..first].iter().fold(one.clone(), |s, x| (x.clone() + one.clone()) * s);
        let scale = (scale.clone() * scale).kept();
        expect = pads(&opened.r[first..])? * last.clone() * scale + expect;
    }
    if let Some(weight) = weight_program {
        expect = opened.thetas[0].clone() * opened.joined_finals[0].clone() * weight + expect;
    }
    opened.claim.is(&expect).then_some(Taken { indices: opened.indices, program: program_at, publics })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alg::switched;

    /// Proofs of circuits with no program and no public values.
    fn prove(circuit: &Circuit, params: &Params, domain: &Domain, w: Witness) -> (Proof, Timings) {
        super::prove(circuit, params, domain, w, None, &[])
    }

    fn verify(circuit: &Circuit, params: &Params, domain: &Domain, rows: usize, proof: &Proof) -> Option<Work> {
        super::verify(circuit, params, domain, rows, proof, &Statement::default())
    }

    /// A proof of one table, read as that table's part.
    impl std::ops::Deref for Proof {
        type Target = TableProof;
        fn deref(&self) -> &TableProof {
            &self.tables[0]
        }
    }

    impl std::ops::DerefMut for Proof {
        fn deref_mut(&mut self) -> &mut TableProof {
            &mut self.tables[0]
        }
    }
    use crate::circuit::{COMPRESS_INPUTS, Ctx, Sum, blake3_circuit, compress_row};
    use crate::test_util::Rng;

    fn inputs(i: usize) -> [u32; COMPRESS_INPUTS] {
        let mut rng = Rng(i as u64 + 99);
        std::array::from_fn(|_| rng.next_u64() as u32)
    }

    fn witness(circuit: &Circuit, rows: usize) -> Witness {
        Witness::new(circuit, rows, |c| _ = compress_row(c), inputs, &Fixed::default())
    }

    #[test]
    fn packing_puts_a_row_in_a_bit() {
        let mut rng = Rng(20);
        let words: Vec<u32> = (0..256 * 8).map(|_| rng.next_u64() as u32).collect();
        let f = pack(&words, 3);
        assert_eq!(f.len(), 2 * 8 * 32);
        for (row, col, j) in [(0, 0, 0), (5, 3, 31), (127, 7, 16), (128, 0, 1), (200, 5, 9), (255, 7, 31)] {
            let p = j | col << 5 | (row / 128) << 8;
            assert_eq!((f[p].0 >> (row % 128)) as u32 & 1, words[row * 8 + col] >> j & 1);
        }
    }

    #[test]
    fn a_table_at_a_point_is_its_terms() {
        // Every claim of every kind of check, for a circuit of
        // compressions and for circuits that read every source: the
        // value the verifier adds up a term at a time is the prover's
        // table at the point.
        let mut rng = Rng(23);
        for circuit in [blake3_circuit(), program_circuit(), product_circuit(), bus_circuit(), digit_circuit()] {
            let rows = 7;
            let public: Vec<u32> = (0..circuit.publics).map(|_| rng.next_u64() as u32).collect();
            let three = |rng: &mut Rng| [rng.f(), rng.f(), rng.f()];
            let ended = Ended {
                rho: rng.fs(LOG_W + circuit.log_constraints + rows),
                abc: three(&mut rng),
                lambda: rng.f(),
                products: Some(structure::Products {
                    rho: rng.fs(circuit.log_products + rows),
                    xyz: three(&mut rng),
                    lambda: rng.f(),
                    beta: rng.f(),
                }),
                bus: Some(structure::Bus {
                    point: rng.fs(circuit.log_slots + rows),
                    values: [rng.f(), rng.f()],
                    gamma: rng.f(),
                    alpha: rng.f(),
                    kappa: rng.f(),
                    beta: rng.f(),
                }),
            };
            let rho_e = rng.fs(LOG_W + circuit.log_cols);
            let rho_p =
                if circuit.has_program() { rng.fs(LOG_W + circuit.log_cols - LOG_PROGRAM_SHARE) } else { vec![] };
            let claims = reduce(&circuit, &public, &ended);
            let known = Public { words: &public, elements: None };
            let at = structure::tables_at(&circuit, &known, &ended, &rho_e, &rho_p, &mut Direct);
            assert_eq!(claims.len(), at.len());
            for (i, (c, value)) in claims.iter().zip(&at).enumerate() {
                let point = if c.program { &rho_p } else { &rho_e };
                assert_eq!(pcs::evaluate(&c.table, point), *value, "claim {i}");
            }
            // And the constants agree, by the sums the claims must reach.
            let (bare, target) = structure::reduce_claims(&circuit, &known, &ended);
            assert_eq!(bare.len(), claims.len());
            let make = |eq_j: &[F]| Tables::new(&circuit, eq_j);
            let expect = groups(&circuit, &known, &ended, make, true)
                .iter()
                .fold(F::ZERO, |s, g| s + g.scale * (g.value + g.acc.constant));
            assert_eq!(target, expect);
        }
    }

    #[test]
    fn the_batching_map_is_linear_over_bits() {
        let mut rng = Rng(22);
        let omega = rng.f();
        let tables = phi_tables(omega);
        for _ in 0..4 {
            let (y, w) = (rng.f(), rng.f());
            // The sum of the powers; through a sum; and the prover's
            // tables give it.
            let direct = (0..128).fold((F::ZERO, y, F::ONE), |(s, p, o), _| (s + o * p, p.square(), o * omega)).0;
            assert_eq!(phi(&omega, &y), direct);
            assert_eq!(phi(&omega, &(y + w)), phi(&omega, &y) + phi(&omega, &w));
            assert_eq!(lookup(&tables, y.0), direct);
        }
        // The sums read the other way: bit c of s[b] weighing phi(x^c) x^b.
        let s = rng.fs(128);
        let mut other = F::ZERO;
        for c in 0..128 {
            let u = F((0..128).fold(0u128, |u, b| u | (s[b].0 >> c & 1) << b));
            other += phi(&omega, &F(1 << c)) * u;
        }
        let twists = twists(&omega).unwrap();
        for (t, twist) in twists.iter().enumerate() {
            // Its power `2^t` is `omega^t`.
            let power = (0..t).fold(*twist, |p, _| p.square());
            assert_eq!(power, (0..t).fold(F::ONE, |p, _| p * omega));
        }
        assert_eq!(switched(&twists, &s), other);
        assert_eq!(s.iter().rev().fold(F::ZERO, |sum, sb| sum * F(2) + phi(&omega, sb)), other);
    }

    #[test]
    fn the_weight_at_a_point_is_the_table_s() {
        let mut rng = Rng(21);
        for n in [1, 4, 9] {
            let (z, r, omega, scale) = (rng.fs(n), rng.fs(n), rng.f(), rng.f());
            let phi = phi_tables(omega);
            // The opening's weights as the prover has them: of each
            // element's weight, scaled, the map of it.
            let g: Vec<F> = eq_table(&z).iter().map(|y| lookup(&phi, (scale * *y).0)).collect();
            assert_eq!(switch_weight_at(&z, &omega, &scale, &r), pcs::evaluate(&g, &r), "{n} variables");
        }
    }

    #[test]
    fn the_opening_s_weights_are_each_table_s_in_its_block() {
        let mut rng = Rng(24);
        // Two tables in a polynomial of 12 variables: blocks of 11 and
        // of 9, the second with no program.
        let layout = Layout { m: vec![11, 9], offset: vec![0, 1 << 11], total: 12 };
        let (r, omega) = (rng.fs(12), rng.f());
        let blocks: Vec<Block<F>> = [(11, 7, true), (9, 6, false)]
            .into_iter()
            .enumerate()
            .map(|(i, (own, bits, program))| Block {
                rho_e: rng.fs(bits),
                rho_p: if program { rng.fs(bits - LOG_PROGRAM_SHARE) } else { vec![] },
                zeta_high: rng.fs(own - bits),
                own,
                number: layout.offset[i] >> own,
                scale: rng.f(),
                scale_program: program.then(|| rng.f()),
            })
            .collect();
        let (words, programs) = opening_weights(&twists(&omega).unwrap(), &r, &blocks);
        let (mut expect, mut expect_program) = (F::ZERO, F::ZERO);
        for (i, b) in blocks.iter().enumerate() {
            let z = [&b.rho_e[..], &b.zeta_high[..]].concat();
            expect += layout.weight(i, &r) * switch_weight_at(&z, &omega, &b.scale, &r[..b.own]);
            if let Some(scale) = &b.scale_program {
                let z = [&b.rho_p[..], &b.zeta_high[..]].concat();
                let at = switch_weight_at(&z, &omega, scale, &r[LOG_PROGRAM_SHARE..b.own]);
                expect_program += layout.weight(i, &r) * at;
            }
        }
        assert_eq!((words, programs), (expect, Some(expect_program)));
    }

    /// A proof of compressions that hides them, with the tables it is of.
    fn hiding(rows: usize, seed: u8) -> (Circuit, Params, Domain, Proof) {
        let circuit = blake3_circuit();
        let params = Params::plain(variables(&circuit, rows), 1, 6, 4).hiding();
        let domain = Domain::new(params.k(), true);
        let part = Part { circuit: &circuit, witness: witness(&circuit, rows), public: &[] };
        let (proof, _) = prove_hiding(&params, &domain, vec![part], None, [seed; 32]);
        (circuit, params, domain, proof)
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_proof_that_hides_its_witness_verifies() {
        let rows = 1 << 14;
        let (circuit, params, domain, proof) = hiding(rows, 7);
        assert!(verify(&circuit, &params, &domain, rows, &proof).is_some());
        assert_eq!(Proof::from_bytes(&proof.to_bytes()).as_ref(), Some(&proof));
        // It is not one that hides nothing, nor the other way about.
        let plain = Params { blind: false, ..params };
        assert!(verify(&circuit, &plain, &domain, rows, &proof).is_none());
        // Nothing of it can be changed: what was sent under a pad, a
        // product's part, a nonce, the corners, the blinding sum.
        let changed = |change: &dyn Fn(&mut Proof)| {
            let mut p = proof.clone();
            change(&mut p);
            assert_ne!(p, proof);
            verify(&circuit, &params, &domain, rows, &p).is_some()
        };
        assert!(!changed(&|p| p.abc[0] += F::ONE));
        assert!(!changed(&|p| p.abc[2] += F::ONE));
        assert!(!changed(&|p| p.rounds[3][1] += F::ONE));
        assert!(!changed(&|p| p.u[0] += F::ONE));
        assert!(!changed(&|p| p.v += F::ONE));
        assert!(!changed(&|p| p.s[77] += F::ONE));
        assert!(!changed(&|p| p.col_rounds[2].0 += F::ONE));
        assert!(!changed(&|p| p.hidden.corners += F::ONE));
        assert!(!changed(&|p| p.pcs.blind_sum += F::ONE));
        assert!(!changed(&|p| p.pcs.first_final += F::ONE));
        let n = proof.hidden.extra.len();
        for at in [0, 5, 127, 128, 200, 255, n - 300, n - 2, n - 1] {
            assert!(!changed(&|p| p.hidden.extra[at] += F::ONE), "element {at} of {n}");
        }
        assert!(!changed(&|p| _ = p.hidden.extra.pop()));
        assert!(!changed(&|p| p.hidden.extra.push(F::ZERO)));
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn what_a_hiding_proof_sends_is_the_pads_to_choose() {
        // Two proofs of one witness, from two seeds: nothing a prover
        // sends before the opening is the same in both, and none of it
        // is what a proof that hides nothing sends.
        let rows = 1 << 14;
        let (circuit, params, domain, one) = hiding(rows, 1);
        let (.., other) = hiding(rows, 2);
        let plain = Params { blind: false, query_grinding: 0, ..params };
        let (bare, _) = prove(&circuit, &plain, &domain, witness(&circuit, rows));
        assert!(verify(&circuit, &plain, &domain, rows, &bare).is_some());
        let sent = |p: &Proof| -> Vec<F> {
            let t = &p.tables[0];
            let pairs = |r: &[(F, F)]| r.iter().flat_map(|(a, b)| [*a, *b]).collect::<Vec<F>>();
            let mut all: Vec<F> = t.rounds.as_flattened().to_vec();
            all.extend(t.abc);
            all.extend(pairs(&t.row_rounds));
            all.extend(&t.u);
            all.extend(pairs(&t.col_rounds));
            all.push(t.v);
            all.extend(&t.s);
            all
        };
        let (a, b, c) = (sent(&one), sent(&other), sent(&bare));
        assert_eq!((a.len(), b.len()), (c.len(), c.len()));
        for i in 0..a.len() {
            assert!(a[i] != b[i] && a[i] != c[i] && b[i] != c[i], "element {i}");
        }
        assert_ne!(one.pcs.first_final, other.pcs.first_final);
    }

    #[test]
    fn a_proof_of_compressions_verifies() {
        let circuit = blake3_circuit();
        for rows in [128, 512] {
            let params = Params::plain(variables(&circuit, rows), 2, 10, 4);
            let domain = Domain::new(params.k(), true);
            let (proof, _) = prove(&circuit, &params, &domain, witness(&circuit, rows));
            assert!(verify(&circuit, &params, &domain, rows, &proof).is_some(), "{rows} rows");
        }
    }

    /// A proof comes from whoever cares to send one. Every count,
    /// length and index its bytes hold is set in turn to the values at
    /// its bounds: none of them makes the reading or the checking fail
    /// otherwise than by refusing, and none gives another proof that
    /// verifies.
    #[test]
    fn a_proof_s_counts_are_not_taken_on_trust() {
        let (circuit, rows) = (blake3_circuit(), 128);
        let params = Params::plain(variables(&circuit, rows), 2, 10, 4);
        let domain = Domain::new(params.k(), true);
        let (proof, _) = prove(&circuit, &params, &domain, witness(&circuit, rows));
        let bytes = proof.to_bytes();
        assert_eq!(Proof::from_bytes(&bytes).as_ref(), Some(&proof));
        let (fields, panicked, accepted) = crate::codec::sweep_fields(&bytes, |b| {
            let read = Proof::from_bytes(b)?;
            Some(read != proof && verify(&circuit, &params, &domain, rows, &read).is_some())
        });
        assert!(fields > 4, "{fields} counts found");
        assert!(panicked.is_empty(), "{panicked:#?}");
        assert!(accepted.is_empty(), "{accepted:#?}");
        // Cut short anywhere, or with more after it, it is no proof.
        for cut in [0, 1, 31, 32, 36, bytes.len() / 2, bytes.len() - 1] {
            assert!(Proof::from_bytes(&bytes[..cut]).is_none(), "cut at {cut}");
        }
        assert!(Proof::from_bytes(&[&bytes[..], &[0]].concat()).is_none());
    }

    /// A circuit of multiplications: elements `x`, `y`, `z`, `w`, `v`
    /// and a word `t`, with `x y = z`, `(z of the row before + x) y = w`,
    /// `(x + C) D = v` for constants, and `x & y = t` on their low words.
    fn product_circuit() -> Circuit {
        Circuit::new(
            |s| {
                let e: [[crate::circuit::Expr; 4]; 5] = std::array::from_fn(|_| std::array::from_fn(|_| s.input()));
                let t = s.input();
                let core = s.constraints.len();
                let [x, y, z, w, v] = e.each_ref().map(|words| Sum::element(words));
                s.product(x.clone(), y.clone(), z.clone());
                s.product(z.prev().add(&x), y, w);
                s.product(x.add(&Sum::constant(C)), Sum::constant(D), v);
                s.constrain(e[0][0].clone(), e[1][0].clone(), t);
                core
            },
            21,
        )
    }

    const C: F = F(0x1234_5678_9ABC_DEF0_0FED_CBA9_8765_4321);
    const D: F = F(0xFFFF_0000_FFFF_0000_1111_2222_3333_4444);

    /// Rows of [`product_circuit`] that hold.
    fn product_rows(rows: usize) -> Vec<[u32; 21]> {
        let mut rng = Rng(40);
        let xy: Vec<(F, F)> = (0..rows).map(|_| (rng.f(), rng.f())).collect();
        (0..rows)
            .map(|i| {
                let (x, y) = xy[i];
                let (px, py) = xy[(i + rows - 1) % rows];
                let elements = [x, y, x * y, (px * py + x) * y, (x + C) * D];
                let mut row = [0u32; 21];
                for (e, words) in elements.iter().zip(row.chunks_mut(4)) {
                    for (j, w) in words.iter_mut().enumerate() {
                        *w = (e.0 >> (32 * j)) as u32;
                    }
                }
                row[20] = row[0] & row[4];
                row
            })
            .collect()
    }

    fn prove_products(circuit: &Circuit, rows: &[[u32; 21]]) -> (Params, Domain, Proof) {
        let params = Params::plain(variables(circuit, rows.len()), 1, 6, 4);
        let domain = Domain::new(params.k(), true);
        let w = Witness::new(
            circuit,
            rows.len(),
            |c| {
                for _ in 0..21 {
                    c.input();
                }
            },
            |i| rows[i],
            &Fixed::default(),
        );
        let (proof, _) = prove(circuit, &params, &domain, w);
        (params, domain, proof)
    }

    #[test]
    fn multiplications_are_proven() {
        let circuit = product_circuit();
        assert_eq!((circuit.products.len(), circuit.log_products, circuit.log_cols), (3, 2, 5));
        for n in [128, 512] {
            let rows = product_rows(n);
            let (params, domain, proof) = prove_products(&circuit, &rows);
            assert_eq!(Proof::from_bytes(&proof.to_bytes()).as_ref(), Some(&proof));
            assert!(Proof::from_bytes(&proof.to_bytes()[1..]).is_none());
            assert!(verify(&circuit, &params, &domain, n, &proof).is_some(), "{n} rows");
            assert_eq!((proof.product_rounds.len(), proof.u.len()), (2 + n.trailing_zeros() as usize, 4));
        }
    }

    #[test]
    fn a_wrong_multiplication_is_not() {
        let circuit = product_circuit();
        let rows = product_rows(128);
        let check = |rows: &[[u32; 21]]| {
            let (params, domain, proof) = prove_products(&circuit, rows);
            verify(&circuit, &params, &domain, rows.len(), &proof).is_some()
        };
        assert!(check(&rows));
        // Each element wrong in one bit of one row: a product, the one
        // that reads the row before, the one with constants, an operand.
        for (row, word, bit) in [(5, 8, 0), (5, 11, 31), (77, 12, 3), (127, 16, 9), (0, 2, 17), (64, 7, 30)] {
            let mut bad = rows.clone();
            bad[row][word] ^= 1 << bit;
            assert!(!check(&bad), "row {row} word {word}");
        }
        // A product right in its own row and wrong for the row after.
        let mut bad = rows.clone();
        let x = F(bad[9][..4].iter().rev().fold(0u128, |x, w| x << 32 | *w as u128));
        let y = F(bad[9][4..8].iter().rev().fold(0u128, |x, w| x << 32 | *w as u128));
        bad[9][0] ^= 1;
        let fixed = (x + F::ONE) * y;
        for j in 0..4 {
            bad[9][8 + j] = (fixed.0 >> (32 * j)) as u32;
        }
        assert!(!check(&bad));
        // The constraint on words beside them.
        let mut bad = rows.clone();
        bad[3][20] ^= 4;
        assert!(!check(&bad));
        // Each new part of a good proof changed.
        let (params, domain, good) = prove_products(&circuit, &rows);
        let changed = |change: &dyn Fn(&mut Proof)| {
            let mut p = prove_products(&circuit, &rows).2;
            change(&mut p);
            verify(&circuit, &params, &domain, 128, &p).is_some()
        };
        assert!(verify(&circuit, &params, &domain, 128, &good).is_some());
        assert!(!changed(&|p| p.product_rounds[3][0] += F::ONE));
        assert!(!changed(&|p| p.product_rounds[8][1] += F::ONE));
        assert!(!changed(&|p| p.xyz[1] += F::ONE));
        for i in 0..4 {
            assert!(!changed(&|p| p.u[i] += F::ONE));
        }
        assert!(!changed(&|p| p.u.truncate(2)));
        assert!(!changed(&|p| p.product_rounds.clear()));
        // A proof of a circuit with no multiplications has none.
        let plain = blake3_circuit();
        let params = Params::plain(variables(&plain, 128), 2, 10, 4);
        let domain = Domain::new(params.k(), true);
        let mut p = prove(&plain, &params, &domain, witness(&plain, 128)).0;
        assert!(verify(&plain, &params, &domain, 128, &p).is_some());
        assert_eq!(p.u.len(), 2);
        p.xyz[0] = F::ONE;
        assert!(verify(&plain, &params, &domain, 128, &p).is_none());
    }

    /// A circuit with a bus: a row sends `(tag, value)` and receives
    /// `(want, got)`, a tag a word and a value an element.
    fn bus_circuit() -> Circuit {
        Circuit::new(
            |s| {
                let w: [crate::circuit::Expr; 10] = std::array::from_fn(|_| s.input());
                s.send(vec![Sum::word(&w[0]), Sum::element(&w[1..5])]);
                s.receive(vec![Sum::word(&w[5]), Sum::element(&w[6..10])]);
                s.constraints.len()
            },
            10,
        )
    }

    /// Rows of [`bus_circuit`] that balance: row `i` sends `(i, v_i)` and
    /// receives what row `7 i + 3` sends.
    fn bus_rows(rows: usize) -> Vec<[u32; 10]> {
        let mut rng = Rng(60);
        let values: Vec<[u32; 4]> = (0..rows).map(|_| std::array::from_fn(|_| rng.next_u64() as u32)).collect();
        (0..rows)
            .map(|i| {
                let from = (7 * i + 3) % rows;
                let mut row = [0u32; 10];
                row[0] = i as u32;
                row[1..5].copy_from_slice(&values[i]);
                row[5] = from as u32;
                row[6..10].copy_from_slice(&values[from]);
                row
            })
            .collect()
    }

    fn bus_proof(circuit: &Circuit, rows: &[[u32; 10]], round_bits: usize) -> (Params, Domain, Proof) {
        let params = Params { round_bits, ..Params::plain(variables(circuit, rows.len()), 1, 6, 4) };
        let domain = Domain::new(params.k(), true);
        let w = Witness::new(
            circuit,
            rows.len(),
            |c| {
                for _ in 0..10 {
                    c.input();
                }
            },
            |i| rows[i],
            &Fixed::default(),
        );
        let (proof, _) = prove(circuit, &params, &domain, w);
        (params, domain, proof)
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_proof_that_hides_is_of_a_witness_that_holds() {
        // Multiplications and a bus, hidden: proven of rows that hold,
        // and not of rows that do not.
        let n = 1 << 15;
        let hidden = |circuit: &Circuit, w: Witness| {
            let params = Params::plain(variables(circuit, n), 1, 6, 4).hiding();
            let domain = Domain::new(params.k(), true);
            let part = Part { circuit, witness: w, public: &[] };
            let (proof, _) = prove_hiding(&params, &domain, vec![part], None, [3; 32]);
            verify(circuit, &params, &domain, n, &proof).is_some()
        };
        let products = product_circuit();
        let check = |rows: &[[u32; 21]]| {
            let run = |c: &mut crate::circuit::Concrete| {
                for _ in 0..21 {
                    c.input();
                }
            };
            hidden(&products, Witness::new(&products, n, run, |i| rows[i], &Fixed::default()))
        };
        let rows = product_rows(n);
        assert!(check(&rows));
        for (row, word, bit) in [(5, 8, 0), (20_000, 12, 3), (0, 2, 17)] {
            let mut bad = rows.clone();
            bad[row][word] ^= 1 << bit;
            assert!(!check(&bad), "row {row} word {word}");
        }
        let bus = bus_circuit();
        let check = |rows: &[[u32; 10]]| {
            let run = |c: &mut crate::circuit::Concrete| {
                for _ in 0..10 {
                    c.input();
                }
            };
            hidden(&bus, Witness::new(&bus, n, run, |i| rows[i], &Fixed::default()))
        };
        let rows = bus_rows(n);
        assert!(check(&rows));
        for (row, word, bit) in [(9, 6, 0), (30_000, 1, 5), (0, 4, 30)] {
            let mut bad = rows.clone();
            bad[row][word] ^= 1 << bit;
            assert!(!check(&bad), "row {row} word {word}");
        }
    }

    #[test]
    fn what_is_sent_is_what_is_received() {
        let circuit = bus_circuit();
        assert!(circuit.has_bus() && circuit.log_slots == 0);
        for n in [128, 1024] {
            let rows = bus_rows(n);
            let (params, domain, proof) = bus_proof(&circuit, &rows, 0);
            assert!(verify(&circuit, &params, &domain, n, &proof).is_some(), "{n} rows");
            assert_eq!(proof.u.len(), 4);
            assert_eq!(proof.bus.products[0], proof.bus.products[1]);
        }
        // With grinding: the nonce is checked.
        let rows = bus_rows(128);
        let (params, domain, proof) = bus_proof(&circuit, &rows, 126);
        assert_eq!(pcs::grinding(126, bus_degree(&circuit, 128)), 7);
        assert!(verify(&circuit, &params, &domain, 128, &proof).is_some());
        let mut p = proof.clone();
        p.bus_nonce ^= 1;
        assert!(verify(&circuit, &params, &domain, 128, &p).is_none());
        assert!(verify(&circuit, &Params { round_bits: 0, ..params }, &domain, 128, &proof).is_none());
    }

    #[test]
    fn a_bus_that_does_not_balance_is_not() {
        let circuit = bus_circuit();
        let rows = bus_rows(128);
        let check = |rows: &[[u32; 10]]| {
            let (params, domain, proof) = bus_proof(&circuit, rows, 0);
            verify(&circuit, &params, &domain, rows.len(), &proof).is_some()
        };
        assert!(check(&rows));
        // A value read that was not written; a tag nobody sent; a value
        // written that nobody reads as it is.
        for (row, word, bit) in [(9, 6, 0), (9, 9, 31), (40, 5, 2), (77, 1, 5), (127, 0, 6), (0, 4, 30)] {
            let mut bad = rows.clone();
            bad[row][word] ^= 1 << bit;
            assert!(!check(&bad), "row {row} word {word}");
        }
        // The same value read twice, and another never.
        let mut bad = rows.clone();
        let (a, b) = (bad[20], bad[21]);
        bad[21][5..].copy_from_slice(&a[5..]);
        assert_ne!(bad[21], b);
        assert!(!check(&bad));
        // Reads moved between rows still balance: the bus is a multiset.
        let mut moved = rows.clone();
        let (a, b) = (moved[20], moved[21]);
        moved[20][5..].copy_from_slice(&b[5..]);
        moved[21][5..].copy_from_slice(&a[5..]);
        assert!(check(&moved));
        // Each part of a good proof changed.
        let (params, domain, good) = bus_proof(&circuit, &rows, 0);
        let changed = |change: &dyn Fn(&mut Proof)| {
            let mut p = good.clone();
            change(&mut p);
            verify(&circuit, &params, &domain, 128, &p).is_some()
        };
        assert!(!changed(&|p| p.bus.products[0] += F::ONE));
        assert!(!changed(&|p| {
            p.bus.products[0] += F::ONE;
            p.bus.products[1] += F::ONE;
        }));
        assert!(!changed(&|p| p.bus.levels[4].ends[1][0] += F::ONE));
        assert!(!changed(&|p| p.bus.levels[6].rounds[2][1] += F::ONE));
        assert!(!changed(&|p| p.u[2] += F::ONE));
        assert!(!changed(&|p| p.bus = grand::Proof::default()));
        // A circuit with no bus takes no bus proof.
        let plain = blake3_circuit();
        let params = Params::plain(variables(&plain, 128), 2, 10, 4);
        let domain = Domain::new(params.k(), true);
        let mut p = prove(&plain, &params, &domain, witness(&plain, 128)).0;
        p.bus_nonce = 1;
        assert!(verify(&plain, &params, &domain, 128, &p).is_none());
    }

    /// A circuit that reads every source. A row has a word `x`, the
    /// carry-less product `z` of two words, and a word `got`; its program
    /// is a word `p` and two tags; there is one public value `q`.
    ///
    /// - `x ^ x of the row before ^ p ^ q = 0`.
    /// - `p q = z` in the field.
    /// - The row sends `(tag, x)` and receives `(from, got)`.
    fn program_circuit() -> Circuit {
        Circuit::new(
            |s| {
                let [x, z0, z1, got] = std::array::from_fn(|_| s.input());
                let [p, tag, from] = std::array::from_fn(|_| s.program());
                let q = s.public();
                let core = s.constraints.len();
                s.zero_where(&crate::circuit::Expr::constant(!0), x.xor(&x.prev()).xor(&p).xor(&q));
                s.product(Sum::word(&p), Sum::word(&q), Sum::element(&[z0, z1]));
                s.send(vec![Sum::word(&tag), Sum::word(&x)]);
                s.receive(vec![Sum::word(&from), Sum::word(&got)]);
                core
            },
            4,
        )
    }

    const Q: u32 = 0x5A5A_1234;

    /// A program for [`program_circuit`] and rows that hold under it.
    /// Row `i` is tagged `i` and reads the row tagged `5 i + 2`.
    fn program_rows(rows: usize, seed: u64) -> (Vec<u32>, Vec<[u32; 4]>) {
        let mut rng = Rng(seed);
        let mut ps: Vec<u32> = (0..rows).map(|_| rng.next_u64() as u32).collect();
        // Around the ring the program words come to zero.
        ps[0] = ps[1..].iter().fold(0, |a, b| a ^ b);
        let mut xs = vec![rng.next_u64() as u32; rows];
        for i in 1..rows {
            xs[i] = xs[i - 1] ^ ps[i] ^ Q;
        }
        let program = (0..rows).flat_map(|i| [ps[i], i as u32, ((5 * i + 2) % rows) as u32, 0]).collect();
        let witness = (0..rows)
            .map(|i| {
                let z = F(ps[i] as u128) * F(Q as u128);
                [xs[i], z.0 as u32, (z.0 >> 32) as u32, xs[(5 * i + 2) % rows]]
            })
            .collect();
        (program, witness)
    }

    struct WithProgram {
        circuit: Circuit,
        params: Params,
        domain: Domain,
        program: Program,
    }

    impl WithProgram {
        fn new(rows: usize, words: Vec<u32>) -> WithProgram {
            let circuit = program_circuit();
            let params = Params::plain(variables(&circuit, rows), 1, 6, 4);
            let domain = Domain::new(params.k(), true);
            let program = Program::new(&circuit, &params, &domain, words);
            WithProgram { circuit, params, domain, program }
        }

        /// A proof of `rows`, made against the program words `against`
        /// and the public value `q`.
        fn prove(&self, rows: &[[u32; 4]], against: &[u32], q: u32) -> Proof {
            let fixed = Fixed { program: against, public: &[q] };
            let run = |c: &mut crate::circuit::Concrete| {
                let _: [u32; 4] = std::array::from_fn(|_| c.input());
                let _: [u32; 3] = std::array::from_fn(|_| c.program());
                c.public();
            };
            let w = Witness::new(&self.circuit, rows.len(), run, |i| rows[i], &fixed);
            super::prove(&self.circuit, &self.params, &self.domain, w, Some(&self.program), &[q]).0
        }

        fn verify(&self, rows: usize, proof: &Proof, root: &Digest, q: u32) -> bool {
            let statement = Statement { program: Some(root), public: &[q] };
            super::verify(&self.circuit, &self.params, &self.domain, rows, proof, &statement).is_some()
        }
    }

    #[test]
    fn a_program_and_public_values_are_proven_against() {
        let c = program_circuit();
        assert_eq!((c.program_cols, c.publics, c.log_cols, c.program_width()), (3, 1, 6, 4));
        for n in [128, 512] {
            let (words, rows) = program_rows(n, 70);
            let t = WithProgram::new(n, words.clone());
            let root = t.program.root();
            let proof = t.prove(&rows, &words, Q);
            assert_eq!(Proof::from_bytes(&proof.to_bytes()).as_ref(), Some(&proof));
            assert!(Proof::from_bytes(&proof.to_bytes()[1..]).is_none());
            assert!(t.verify(n, &proof, &root, Q), "{n} rows");
            assert_eq!((proof.u.len(), proof.s_program.len()), (9, 128));
            // Another public value, another program.
            assert!(!t.verify(n, &proof, &root, Q ^ 1));
            let other = WithProgram::new(n, program_rows(n, 71).0).program.root();
            assert_ne!(other, root);
            assert!(!t.verify(n, &proof, &other, Q));
            // No statement at all, or a statement with no program.
            let none = Statement::default();
            assert!(super::verify(&t.circuit, &t.params, &t.domain, n, &proof, &none).is_none());
            let half = Statement { program: None, public: &[Q] };
            assert!(super::verify(&t.circuit, &t.params, &t.domain, n, &proof, &half).is_none());
        }
    }

    #[test]
    fn a_witness_for_another_program_or_value_is_not() {
        let n = 128;
        let (words, rows) = program_rows(n, 72);
        let t = WithProgram::new(n, words.clone());
        let root = t.program.root();
        assert!(t.verify(n, &t.prove(&rows, &words, Q), &root, Q));
        // The prover works to a program of its own: its rows hold under
        // it, and it is not the one committed. Each kind of program
        // word, in turn: the constraint's and the product's, the tag
        // sent under, the tag read.
        let (other_words, other_rows) = program_rows(n, 73);
        assert!(!t.verify(n, &t.prove(&other_rows, &other_words, Q), &root, Q));
        for word in [1, 2] {
            // Two rows trade tags, and the witness is made to balance
            // under the trade: whoever reads what they send, or the two
            // rows themselves, trade what they read.
            let row = 9;
            let mut swapped = words.clone();
            swapped.swap(row * 4 + word, (row + 1) * 4 + word);
            let readers: Vec<usize> = match word {
                1 => [row, row + 1].map(|tag| (0..n).find(|i| (5 * i + 2) % n == tag).unwrap()).to_vec(),
                _ => vec![row, row + 1],
            };
            let mut moved = rows.clone();
            let (x, y) = (moved[readers[0]][3], moved[readers[1]][3]);
            (moved[readers[0]][3], moved[readers[1]][3]) = (y, x);
            assert_ne!(moved, rows);
            let proof = t.prove(&moved, &swapped, Q);
            assert!(!t.verify(n, &proof, &root, Q), "program word {word}");
        }
        // Rows that hold for another public value, proven as for this.
        let mut shifted = rows.clone();
        for (i, r) in shifted.iter_mut().enumerate() {
            let z = F(words[i * 4] as u128) * F((Q ^ 2) as u128);
            (r[1], r[2]) = (z.0 as u32, (z.0 >> 32) as u32);
        }
        assert!(!t.verify(n, &t.prove(&shifted, &words, Q), &root, Q));
        // A witness wrong in each place, against the right program.
        for (row, word) in [(3, 0), (50, 1), (50, 2), (127, 3)] {
            let mut bad = rows.clone();
            bad[row][word] ^= 1 << 7;
            assert!(!t.verify(n, &t.prove(&bad, &words, Q), &root, Q), "row {row} word {word}");
        }
        // Each new part of a good proof changed.
        let good = t.prove(&rows, &words, Q);
        let changed = |change: &dyn Fn(&mut Proof)| {
            let mut p = good.clone();
            change(&mut p);
            assert_ne!(p, good);
            t.verify(n, &p, &root, Q)
        };
        assert!(!changed(&|p| p.s_program[5] += F::ONE));
        assert!(!changed(&|p| p.s_program.clear()));
        assert!(!changed(&|p| p.pcs.joined_finals[0] += F::ONE));
        assert!(!changed(&|p| p.pcs.joined_openings[0].leaves[2][0] += F::ONE));
        for i in 0..9 {
            assert!(!changed(&|p| p.u[i] += F::ONE), "sum {i}");
        }
    }

    /// A circuit whose multiplication reads single bits under constants,
    /// as a fold reads its twiddle off an index: a word `i`, elements
    /// `y` and `z`, and `(sum_l bit_l(i) K_l + K) (D y) = z`, with a
    /// three-bit digit of `i` sent on the bus and received back.
    fn digit_circuit() -> Circuit {
        Circuit::new(
            |s| {
                let i = s.input();
                let y: [crate::circuit::Expr; 4] = std::array::from_fn(|_| s.input());
                let z: [crate::circuit::Expr; 4] = std::array::from_fn(|_| s.input());
                let core = s.constraints.len();
                let twiddle =
                    (0..8).fold(Sum::constant(C), |t, l| t.add(&Sum::bits(&i, l + 3, 1).scaled(digit_constant(l))));
                s.product(twiddle, Sum::element(&y).scaled(D), Sum::element(&z));
                s.send(vec![Sum::bits(&i, 5, 3).scaled(C)]);
                s.receive(vec![Sum::bits(&i, 5, 3).scaled(C)]);
                core
            },
            9,
        )
    }

    fn digit_constant(l: usize) -> F {
        F(0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835 ^ (l as u128) << 100) * D
    }

    fn digit_rows(rows: usize) -> Vec<[u32; 9]> {
        let mut rng = Rng(80);
        (0..rows)
            .map(|_| {
                let (i, y) = (rng.next_u64() as u32, rng.f());
                let twiddle = (0..8).filter(|l| i >> (l + 3) & 1 == 1).fold(C, |t, l| t + digit_constant(l));
                let z = twiddle * (D * y);
                let mut row = [i, 0, 0, 0, 0, 0, 0, 0, 0];
                for j in 0..4 {
                    (row[1 + j], row[5 + j]) = ((y.0 >> (32 * j)) as u32, (z.0 >> (32 * j)) as u32);
                }
                row
            })
            .collect()
    }

    #[test]
    fn bits_under_constants_are_proven() {
        let circuit = digit_circuit();
        let check = |rows: &[[u32; 9]]| {
            let params = Params::plain(variables(&circuit, rows.len()), 1, 6, 4);
            let domain = Domain::new(params.k(), true);
            let run = |c: &mut crate::circuit::Concrete| {
                let _: [u32; 9] = std::array::from_fn(|_| c.input());
            };
            let w = Witness::new(&circuit, rows.len(), run, |i| rows[i], &Fixed::default());
            let holds = w.holds();
            let (proof, _) = prove(&circuit, &params, &domain, w);
            let ok = verify(&circuit, &params, &domain, rows.len(), &proof).is_some();
            assert_eq!(ok, holds);
            ok
        };
        let rows = digit_rows(128);
        assert!(check(&rows));
        // A bit the twiddle reads, one it does not; the product.
        for (word, bit, holds) in
            [(0, 3, false), (0, 10, false), (0, 0, true), (0, 11, true), (0, 31, true), (6, 5, false)]
        {
            let mut bad = rows.clone();
            bad[40][word] ^= 1 << bit;
            assert_eq!(check(&bad), holds, "word {word} bit {bit}");
        }
    }

    /// Two tables on one bus. The larger sends `(tag, value)` from every
    /// row, and receives a tuple of its own choosing; the smaller, a
    /// sixteenth its size and with a program, receives `(want, v)` under
    /// its program's tag and shows `v v = y`. Their words are one
    /// polynomial, the smaller table's after the larger's.
    struct TwoTables {
        sender: Circuit,
        receiver: Circuit,
        params: Params,
        domain: Domain,
        program: Program,
    }

    const SENDER_ROWS: usize = 1 << 11;
    const RECEIVER_ROWS: usize = 1 << 7;

    impl TwoTables {
        fn new() -> TwoTables {
            let sender = Circuit::new(
                |s| {
                    let w: [crate::circuit::Expr; 10] = std::array::from_fn(|_| s.input());
                    s.send(vec![Sum::word(&w[0]), Sum::element(&w[1..5])]);
                    s.receive(vec![Sum::word(&w[5]), Sum::element(&w[6..10])]);
                    s.constraints.len()
                },
                10,
            );
            let receiver = Circuit::new(
                |s| {
                    let w: [crate::circuit::Expr; 8] = std::array::from_fn(|_| s.input());
                    let want = s.program();
                    let v = Sum::element(&w[..4]);
                    s.product(v.clone(), v.clone(), Sum::element(&w[4..]));
                    s.receive(vec![Sum::word(&want), v]);
                    s.constraints.len()
                },
                8,
            );
            assert_eq!((sender.log_cols, receiver.log_cols), (4, 4));
            // The sender's words are 2^13 elements and the receiver's 2^9,
            // after them: 2^14 in all.
            let tables = [(&sender, SENDER_ROWS), (&receiver, RECEIVER_ROWS)];
            let layout = Layout::of(tables.iter().copied()).unwrap();
            assert_eq!(layout, Layout { m: vec![13, 9], offset: vec![0, 1 << 13], total: 14 });
            let params = Params::plain(layout.total, 1, 6, 4);
            let domain = Domain::new(params.k(), true);
            // The receiver's row j wants what is tagged j + 1.
            let words = (0..RECEIVER_ROWS as u32).map(|j| j + 1).collect();
            let program = Program::of(&params, &domain, &tables, vec![vec![], words]);
            TwoTables { sender, receiver, params, domain, program }
        }

        /// Rows that balance: the sender's row `i` sends `(i + 1, v_i)`
        /// and receives its own again, but the first rows, whose tuples
        /// the receiver takes: they receive nothing.
        fn rows() -> (Vec<[u32; 10]>, Vec<[u32; 8]>) {
            let mut rng = Rng(90);
            let values: Vec<F> = (0..SENDER_ROWS).map(|_| rng.f()).collect();
            let words = |x: F| -> [u32; 4] { std::array::from_fn(|j| (x.0 >> (32 * j)) as u32) };
            let sender = (0..SENDER_ROWS)
                .map(|i| {
                    let mut row = [0u32; 10];
                    row[0] = i as u32 + 1;
                    row[1..5].copy_from_slice(&words(values[i]));
                    if i >= RECEIVER_ROWS {
                        let (sent, received) = row.split_at_mut(5);
                        received.copy_from_slice(sent);
                    }
                    row
                })
                .collect();
            let receiver = (0..RECEIVER_ROWS)
                .map(|j| {
                    let mut row = [0u32; 8];
                    row[..4].copy_from_slice(&words(values[j]));
                    row[4..].copy_from_slice(&words(values[j] * values[j]));
                    row
                })
                .collect();
            (sender, receiver)
        }

        fn prove(&self, sender: &[[u32; 10]], receiver: &[[u32; 8]]) -> Proof {
            let run10 = |c: &mut crate::circuit::Concrete| _ = std::array::from_fn::<u32, 10, _>(|_| c.input());
            let run8 = |c: &mut crate::circuit::Concrete| {
                let _: [u32; 8] = std::array::from_fn(|_| c.input());
                c.program();
            };
            let a = Witness::new(&self.sender, sender.len(), run10, |i| sender[i], &Fixed::default());
            let fixed = Fixed { program: &self.program.words[1], public: &[] };
            let b = Witness::new(&self.receiver, receiver.len(), run8, |i| receiver[i], &fixed);
            let parts = vec![
                Part { circuit: &self.sender, witness: a, public: &[] },
                Part { circuit: &self.receiver, witness: b, public: &[] },
            ];
            prove_tables(&self.params, &self.domain, parts, Some(&self.program)).0
        }

        fn tables(&self) -> [Table<'_>; 2] {
            [
                Table { circuit: &self.sender, rows: SENDER_ROWS, public: &[] },
                Table { circuit: &self.receiver, rows: RECEIVER_ROWS, public: &[] },
            ]
        }

        fn verify(&self, proof: &Proof) -> bool {
            verify_tables(&self.params, &self.domain, &self.tables(), Some(&self.program.root()), proof).is_some()
        }
    }

    #[test]
    fn tables_are_proven_together() {
        let t = TwoTables::new();
        let (sender, receiver) = TwoTables::rows();
        let proof = t.prove(&sender, &receiver);
        assert!(t.verify(&proof));
        assert_eq!((proof.tables.len(), proof.pcs.joined_finals.len()), (2, 1));
        assert_eq!(Proof::from_bytes(&proof.to_bytes()).as_ref(), Some(&proof));
        // Neither table balances by itself: only the two together.
        let (a, b) = (&proof.tables[0].bus.products, &proof.tables[1].bus.products);
        assert_ne!(a[0], a[1]);
        assert_ne!(b[0], b[1]);
        assert_eq!(a[0] * b[0], a[1] * b[1]);
        // The tables in the other order, one alone, one twice.
        let root = t.program.root();
        let [first, second] = t.tables();
        for tables in [vec![second, first], vec![first], vec![first, second, second]] {
            assert!(verify_tables(&t.params, &t.domain, &tables, Some(&root), &proof).is_none());
        }
        // Other programs, or none.
        let tables = [(&t.sender, SENDER_ROWS), (&t.receiver, RECEIVER_ROWS)];
        let other = Program::of(&t.params, &t.domain, &tables, vec![vec![], vec![7; RECEIVER_ROWS]]).root();
        assert!(verify_tables(&t.params, &t.domain, &t.tables(), Some(&other), &proof).is_none());
        assert!(verify_tables(&t.params, &t.domain, &t.tables(), None, &proof).is_none());
    }

    #[test]
    fn tables_that_disagree_are_not() {
        let t = TwoTables::new();
        let (sender, receiver) = TwoTables::rows();
        assert!(t.verify(&t.prove(&sender, &receiver)));
        // The receiver takes a value the sender did not send, and its
        // multiplication holds for it.
        let mut bad = receiver.clone();
        let v = F(0x1234_5678_9ABC);
        bad[9][0] = v.0 as u32;
        bad[9][1] = (v.0 >> 32) as u32;
        bad[9][2..4].fill(0);
        let y = v * v;
        for j in 0..4 {
            bad[9][4 + j] = (y.0 >> (32 * j)) as u32;
        }
        assert!(!t.verify(&t.prove(&sender, &bad)));
        // The sender sends another value where the receiver reads; a row
        // of the sender's takes back what the receiver took too.
        let mut bad = sender.clone();
        bad[9][2] ^= 1;
        assert!(!t.verify(&t.prove(&bad, &receiver)));
        let mut bad = sender.clone();
        let (sent, received) = bad[9].split_at_mut(5);
        received.copy_from_slice(sent);
        assert!(!t.verify(&t.prove(&bad, &receiver)));
        // The receiver's multiplication wrong, the bus right.
        let mut bad = receiver.clone();
        bad[100][5] ^= 1;
        assert!(!t.verify(&t.prove(&sender, &bad)));
        // Each table's part of a good proof changed, and the shared.
        let good = t.prove(&sender, &receiver);
        let changed = |change: &dyn Fn(&mut Proof)| {
            let mut p = good.clone();
            change(&mut p);
            assert_ne!(p, good);
            t.verify(&p)
        };
        for i in 0..2 {
            assert!(!changed(&|p| p.tables[i].bus.products[0] += F::ONE), "table {i}");
            assert!(!changed(&|p| p.tables[i].u[0] += F::ONE));
            assert!(!changed(&|p| p.tables[i].v += F::ONE));
            assert!(!changed(&|p| p.tables[i].s[3] += F::ONE));
        }
        assert!(!changed(&|p| p.root[0] ^= 1));
        assert!(!changed(&|p| p.pcs.joined_finals[0] += F::ONE));
        assert!(!changed(&|p| p.pcs.first_final += F::ONE));
        assert!(!changed(&|p| p.tables[1].xyz[0] += F::ONE));
        assert!(!changed(&|p| p.tables[1].s_program[0] += F::ONE));
        assert!(!changed(&|p| p.tables.swap(0, 1)));
        assert!(!changed(&|p| {
            // One table's products for the other's: each still what its
            // own grand product does not show.
            let (a, b) = (p.tables[0].bus.products.clone(), p.tables[1].bus.products.clone());
            (p.tables[0].bus.products, p.tables[1].bus.products) = (b, a);
        }));
    }

    /// What proving compressions costs at the proven parameters.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn proven_timing() {
        let circuit = blake3_circuit();
        for log_rows in [13, 15, 17] {
            let rows = 1 << log_rows;
            let params = Params::proven(variables(&circuit, rows), 2, pcs::SECURITY);
            let domain = Domain::new(params.k(), true);
            let t = std::time::Instant::now();
            let w = witness(&circuit, rows);
            let (proof, times) = prove(&circuit, &params, &domain, w);
            let proved = t.elapsed();
            let t = std::time::Instant::now();
            let work = verify(&circuit, &params, &domain, rows, &proof).expect("the proof verifies");
            println!(
                "2^{log_rows} compressions, rate 1/4, {} queries: proved in {proved:.2?} \
                 (commit {:.2?}, zerocheck {:.2?}, open {:.2?}), verified in {:.2?}, \
                 {} KB, {} compressions",
                params.queries,
                times.commit,
                times.zerocheck,
                times.open,
                t.elapsed(),
                proof.size() / 1000,
                work.compressions
            );
        }
    }

    #[test]
    fn a_wrong_witness_or_proof_does_not() {
        let circuit = blake3_circuit();
        let rows = 128;
        let params = Params::plain(variables(&circuit, rows), 2, 10, 4);
        let domain = Domain::new(params.k(), true);
        let check = |p: &Proof| verify(&circuit, &params, &domain, rows, p).is_some();
        // A carry wrong in one row: the operands are those of the words.
        for (row, col) in [(3, 40), (100, 300), (127, 483)] {
            let mut w = witness(&circuit, rows);
            w.words[row * 512 + col] ^= 1 << 9;
            let all = w.words.clone();
            let at = circuit.words(&all, &Fixed::default(), row, rows);
            for (k, [a, b, c]) in circuit.constraints.iter().enumerate() {
                let i = row * 512 + k;
                (w.a[i], w.b[i], w.c[i]) = (a.eval(&at), b.eval(&at), c.eval(&at));
            }
            assert!(!check(&prove(&circuit, &params, &domain, w).0), "row {row} word {col}");
        }
        // Operands that hold, and are not the committed words'.
        let mut w = witness(&circuit, rows);
        w.words[5 * 512 + 100] ^= 1;
        assert!(!check(&prove(&circuit, &params, &domain, w).0));
        // Each part of a good proof changed.
        let good = || prove(&circuit, &params, &domain, witness(&circuit, rows)).0;
        assert!(check(&good()));
        let mut p = good();
        p.rounds[7][1] += F::ONE;
        assert!(!check(&p));
        let mut p = good();
        p.abc[2] += F::ONE;
        assert!(!check(&p));
        let mut p = good();
        p.s[77] += F::ONE;
        assert!(!check(&p));
        let mut p = good();
        p.pcs.first_final += F::ONE;
        assert!(!check(&p));
        let mut p = good();
        p.pcs.rounds[2].0 += F::ONE;
        assert!(!check(&p));
    }
}
