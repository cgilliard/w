//! The chain's proof: one proof that every block so far was proven.
//!
//! A **step** verifies two proofs: a block's ([`crate::block_proof`]) and the
//! chain's as it was before that block, and states where the chain now
//! is ([`Statement`]). The proof before a chain's first block is of a
//! computation that states where a chain begins ([`genesis_into`]),
//! made to the step's own shape, so that a step verifies either with
//! the same rows: it is the step's program for every block.
//!
//! # Which programs
//!
//! A proof is of a program, and a proof of anything else proves
//! nothing of the chain. So a step finds:
//!
//! - the block's proof to be of the root program it is given, and what
//!   that proof rested on to be the programs it is given ([`Plan`]);
//! - the chain's proof before to be of the genesis program, if this is
//!   the first block, or else of the program this step **names as its
//!   own**. A program cannot hold its own root, so the step takes it as
//!   a value, states it, and requires the step before to have stated
//!   the same. Whoever takes a chain's proof checks that the root it
//!   verified the proof against is the one the proof states: then every
//!   step back to the first was of that program.
//!
//! - Blocks come in shapes (how many runs, with signatures or
//!   without), each a root program of its own. A step holds the root of
//!   a tree over the shapes it takes, and finds the block's to be a
//!   leaf.
//!
//! # The emission
//!
//! A block's inputs and its subsidy come to its outputs
//! ([`crate::block_proof`]); the step finds the subsidy to be what the
//! emission pays at the block's height. Its arithmetic has no numbers
//! to count blocks with, so where the emission stands is carried as an
//! era and a count of the blocks left in it, the count a power of a
//! fixed element: a block fewer is a division by it.

use crate::alg::{Alg, halves};
use crate::block_proof::{PROGRAMS, Tables};
use crate::field::{F, as_bytes};
use crate::hash::{DOM_PLAN_LEAF, DOM_PLAN_NODE, Digest, EMPTY, hash_domain};
use crate::ledger::{self, Emission};
use crate::proof::Proved;
use crate::structure::Reader;
use crate::sym::{Shared, Sym};

/// What a chain's proof is of: the step's program, and where the chain
/// is after its last block, with what that block did (for whoever has
/// the block to compare) and where the emission stands.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Statement {
    pub program: Digest,
    pub height: u32,
    pub root: Digest,
    pub next: u64,
    /// The last block's running hashes of positions spent and outputs
    /// made, and what its inputs with its subsidy, and its outputs, came
    /// to.
    pub inputs: Digest,
    pub outputs: Digest,
    pub sum_in: u128,
    pub sum_out: u128,
    /// The era of the emission the last block was in (0 before the
    /// first block, one past the last era once nothing is paid), and the
    /// blocks left in it.
    pub era: u32,
    pub left: u32,
    /// The registry's root.
    pub names: Digest,
    /// The id of the header before the last block's: the last header
    /// whose work a block's proof has shown. Zeros before the first.
    pub tip: Digest,
    /// The last block's running hash of its operations on names.
    pub ops: Digest,
    /// Which table the work of the last block's header is of (0 before
    /// the first block, then one more than the times the table has
    /// doubled), and the blocks left before it doubles
    /// ([`Statement::table_at`]).
    pub table: u32,
    pub grows: u32,
}

/// Elements of a [`Statement`].
pub const STATEMENT: usize = 22;

/// What counts blocks down: a block fewer is this many times less.
const COUNT: F = F(2);

fn power(mut base: F, mut e: u128) -> F {
    let mut out = F::ONE;
    while e > 0 {
        if e & 1 == 1 {
            out *= base;
        }
        base = base.square();
        e >>= 1;
    }
    out
}

/// The polynomial through `points`, its coefficients lowest first.
fn interpolate(points: &[(F, F)]) -> Vec<F> {
    let mut out = vec![F::ZERO; points.len()];
    for (i, (xi, yi)) in points.iter().enumerate() {
        // The product of `X - x_j` over the others, over its value at x_i.
        let mut basis = vec![F::ONE];
        let mut at = F::ONE;
        for (xj, _) in points.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, p)| p) {
            basis.push(F::ZERO);
            for k in (1..basis.len()).rev() {
                basis[k] = basis[k - 1] + basis[k] * *xj;
            }
            basis[0] *= *xj;
            at *= *xi + *xj;
        }
        let scale = *yi * at.inv();
        out.iter_mut().zip(&basis).for_each(|(o, b)| *o += scale * *b);
    }
    out
}

/// A polynomial at `x`, by Horner's rule.
fn at<A: Alg>(coefficients: &[F], x: &A) -> A {
    let mut sum = x.lift(coefficients[coefficients.len() - 1]);
    for c in coefficients[..coefficients.len() - 1].iter().rev() {
        sum = sum * x.clone() + x.lift(*c);
    }
    sum
}

/// The emission as a circuit's arithmetic follows it. It has no
/// numbers to count with, so an era is an element, the blocks left in
/// it a power of [`COUNT`], and what an era pays, which era is next and
/// how long it is are polynomials in the era.
struct Eras {
    next: Vec<F>,
    reset: Vec<F>,
    pays: Vec<F>,
}

impl Eras {
    fn of(emission: &Emission) -> Eras {
        let n = emission.0.len();
        let era = |i: usize| F(i as u128);
        // Era 0 is before the first block; era `n + 1` is after the last,
        // which is its own next and whose count never runs out.
        let blocks = |i: usize| emission.0.get(i.wrapping_sub(1)).map(|e| e.0);
        let pays = |i: usize| emission.0.get(i.wrapping_sub(1)).map_or(F::ZERO, |e| F(e.1 as u128));
        let reset = |i: usize| blocks(i).map_or(F::ZERO, |b| power(COUNT, b as u128 - 1));
        let points = |f: &dyn Fn(usize) -> F| interpolate(&(0..n + 2).map(|i| (era(i), f(i))).collect::<Vec<_>>());
        Eras { next: points(&|i| era((i + 1).min(n + 1))), reset: points(&reset), pays: points(&pays) }
    }
}

/// The table of the proof of work as a circuit's arithmetic follows it,
/// as it follows the emission ([`Eras`]): which table it is is an
/// element, the blocks left before it doubles a power of [`COUNT`], and
/// which is next, how long that one lasts and the mask of a pair's
/// index in it ([`crate::work::pairs_mask`]) are polynomials in the
/// first.
struct Sizes {
    next: Vec<F>,
    reset: Vec<F>,
    mask: Vec<F>,
}

impl Sizes {
    fn of(pow: &crate::pow::PowParams) -> Sizes {
        let room = (pow.max_log_dataset_items - pow.log_dataset_items) as usize;
        let table = |i: usize| F(i as u128);
        // Table 0 is before the first block, whose header's work is of
        // the first table as block one's is; table `room + 1` is the
        // last, which is its own next and whose count never runs out.
        let log = |i: usize| pow.log_dataset_items + (i.max(1) - 1) as u32;
        let mask = |i: usize| F(crate::work::pairs_mask(log(i)) as u128);
        // The first block is the first of its table's that has a
        // header before it; every other table begins with a block that
        // has a whole epoch after it.
        let reset = |i: usize| match i {
            0 => F::ZERO,
            i if i > room => F::ZERO,
            1 => power(COUNT, pow.epoch_blocks as u128 - 2),
            _ => power(COUNT, pow.epoch_blocks as u128 - 1),
        };
        let points = |f: &dyn Fn(usize) -> F| interpolate(&(0..room + 2).map(|i| (table(i), f(i))).collect::<Vec<_>>());
        Sizes { next: points(&|i| table((i + 1).min(room + 1))), reset: points(&reset), mask: points(&mask) }
    }
}

impl Statement {
    /// Where a chain begins: no block, an empty state.
    pub fn genesis() -> Statement {
        Statement {
            program: [0; 32],
            height: 0,
            root: ledger::empty_roots()[ledger::OUTPUTS_HEIGHT],
            next: 0,
            inputs: [0; 32],
            outputs: [0; 32],
            sum_in: 0,
            sum_out: 0,
            era: 0,
            left: 0,
            names: crate::registry::empty_roots()[crate::registry::HEIGHT],
            tip: [0; 32],
            ops: [0; 32],
            table: 0,
            grows: 0,
        }
    }

    pub fn elements(&self) -> Vec<F> {
        let mut out = halves(&self.program).to_vec();
        out.push(F(self.height as u128));
        out.extend(halves(&self.root));
        out.push(F(self.next as u128));
        out.extend(halves(&self.inputs).into_iter().chain(halves(&self.outputs)));
        out.extend([F(self.sum_in), F(self.sum_out), F(self.era as u128)]);
        // An era with no end has no count.
        out.push(if self.left == u32::MAX { F::ZERO } else { power(COUNT, self.left as u128) });
        out.extend(halves(&self.names));
        out.extend(halves(&self.tip));
        out.extend(halves(&self.ops));
        // A table that grows no more has no count.
        out.push(F(self.table as u128));
        out.push(if self.grows == u32::MAX { F::ZERO } else { power(COUNT, self.grows as u128) });
        out
    }

    /// Which table the work of the header at `height` is of, as a
    /// statement says it (one more than the times the table has
    /// doubled; 0 at height 0, whose header has none before it), and
    /// the blocks left after that one before it doubles.
    pub fn table_at(pow: &crate::pow::PowParams, height: u32) -> (u32, u32) {
        let room = pow.max_log_dataset_items - pow.log_dataset_items;
        let epoch = pow.epoch_of(height as u64);
        match height {
            0 => (0, 0),
            _ if epoch >= room => (room + 1, u32::MAX),
            _ => (epoch + 1, pow.epoch_blocks - 1 - height % pow.epoch_blocks),
        }
    }

    /// The digest a proof of the statement has as its public value, and
    /// a block's header names ([`crate::block::Header`]).
    pub fn digest(&self) -> Digest {
        crate::alg::statement(&self.elements())
    }

    /// The era of the emission a block at `height` is in (one past the
    /// last once nothing is paid), and the blocks left in it after that
    /// block.
    pub fn era_at(emission: &Emission, height: u32) -> (u32, u32) {
        let mut end = 0u64;
        for (i, (blocks, _)) in emission.0.iter().enumerate() {
            end += *blocks as u64;
            if height as u64 <= end {
                return (i as u32 + 1, (end - height as u64) as u32);
            }
        }
        (emission.0.len() as u32 + 1, u32::MAX)
    }

    /// The statement after `block`, by the step of program `program`,
    /// under `emission` and with the tables of `pow`.
    pub fn after(
        program: &Digest,
        block: &crate::block_proof::Statement,
        emission: &Emission,
        pow: &crate::pow::PowParams,
    ) -> Statement {
        let (era, left) = Statement::era_at(emission, block.height);
        let (table, grows) = Statement::table_at(pow, block.height);
        Statement {
            program: *program,
            height: block.height,
            root: block.root[1],
            next: block.next[1],
            inputs: block.inputs,
            outputs: block.outputs,
            sum_in: block.sum_in,
            sum_out: block.sum_out,
            era,
            left,
            names: block.names[1],
            tip: crate::header::id_of(&block.work[0], &block.work[1], &block.work[2]),
            ops: block.ops,
            table,
            grows,
        }
    }
}

/// A computation, in `cx`, that states where a chain begins.
pub fn genesis_into(cx: &Shared) -> Vec<F> {
    let stated = Statement::genesis().elements();
    cx.state(&stated.iter().map(|x| cx.constant(*x)).collect::<Vec<Sym>>());
    stated
}

/// A kind of block a chain takes: the program of its root, and what a
/// root of that program states it rested on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Shape {
    pub root: Digest,
    pub rested: [Digest; PROGRAMS],
}

impl Shape {
    fn elements(&self) -> Vec<F> {
        std::iter::once(&self.root).chain(&self.rested).flat_map(halves).collect()
    }
}

/// The blocks a chain takes, and how it begins and pays: a tree over
/// the shapes of block (its root is all a step holds of them), the
/// program of the computation that states where a chain begins, and
/// the emission.
#[derive(Clone)]
pub struct Plan {
    shapes: Vec<Shape>,
    depth: usize,
    pub genesis: Digest,
    pub emission: Emission,
    /// The network's proof of work: how large its table is, and when
    /// it doubles.
    pub pow: crate::pow::PowParams,
}

impl Plan {
    pub fn new(shapes: Vec<Shape>, genesis: Digest, emission: Emission, pow: crate::pow::PowParams) -> Plan {
        assert!(!shapes.is_empty() && emission.0.len() <= 6 && emission.0.iter().all(|e| e.0 > 0));
        assert!(pow.max_log_dataset_items >= pow.log_dataset_items && pow.epoch_blocks >= 2);
        let depth = shapes.len().next_power_of_two().trailing_zeros().max(1) as usize;
        Plan { shapes, depth, genesis, emission, pow }
    }

    fn node(&self, level: usize, index: usize) -> Digest {
        if level == 0 {
            return self.shapes.get(index).map_or(EMPTY, |s| hash_domain(DOM_PLAN_LEAF, &as_bytes(&s.elements())));
        }
        let children = [self.node(level - 1, 2 * index), self.node(level - 1, 2 * index + 1)];
        hash_domain(DOM_PLAN_NODE, children.as_flattened())
    }

    /// The shapes of block the plan lists, in their order.
    pub fn shapes(&self) -> &[Shape] {
        &self.shapes
    }

    /// The root of the tree of shapes.
    pub fn root(&self) -> Digest {
        self.node(self.depth, 0)
    }

    fn path(&self, index: usize) -> Vec<Digest> {
        (0..self.depth).map(|level| self.node(level, (index >> level) ^ 1)).collect()
    }
}

/// A proof with what it states.
pub struct Stated<'a> {
    pub proof: &'a Proved,
    pub stated: &'a [F],
}

/// A step of the chain, in `cx`: it verifies `block`'s proof (of the
/// plan's shape `shape`) and the chain's proof `before` (the genesis
/// computation's, if `first`), finds the block to follow from where the
/// chain was and to pay what the emission says, finds the work the
/// block's proof showed to be of the header before it (whose other
/// fields hash to `rest`; [`crate::header`]), and states where the
/// chain now is. `own` is the root of this step's own program
/// ([`crate::proof::program_of`]). What it states, by the field.
#[allow(clippy::too_many_arguments)]
pub fn step_into(
    cx: &Shared,
    tables: &Tables,
    reader: &mut impl Reader<Sym>,
    plan: &Plan,
    shape: usize,
    block: &Stated,
    before: &Stated,
    first: bool,
    own: &Digest,
    rest: &Digest,
) -> Option<Vec<F>> {
    let constants = |d: &Digest| halves(d).map(|x| cx.constant(x));
    let (zero, one) = (cx.constant(F::ZERO), cx.constant(F::ONE));
    // The block: of a shape in the plan's tree. The leaf is what the
    // proof was verified against and what it states it rested on; the
    // path, climbed by rows, reaches the plan's root.
    let of = block.proof.verify_into(cx, &tables.compiled, reader)?;
    let b = cx.stated(&[of[2].clone(), of[3].clone()], block.stated);
    let leaf: Vec<Sym> = of[..2].iter().chain(&b[..2 * PROGRAMS]).cloned().collect();
    let values: Vec<F> = leaf.iter().map(Sym::value).collect();
    let index = cx.input(F(shape as u128));
    let index_at = index.send();
    let (opened, top) = cx.with(|c| {
        let domains = [DOM_PLAN_LEAF, DOM_PLAN_NODE];
        let opened = c.trace.opening_in(domains, &values, shape as u32, &plan.path(shape), index_at, true, 0, true);
        (opened, c.trace.last())
    });
    for ((at, value), expect) in opened.leaf.iter().zip(&values).zip(&leaf) {
        assert!(cx.outside(*at, *value).is(expect));
    }
    assert!(cx.outside(opened.high, F((shape >> plan.depth) as u128)).is(&zero));
    for ((at, half), expect) in opened.top.iter().zip(halves(&top)).zip(constants(&plan.root())) {
        assert!(cx.outside(*at, half).is(&expect));
    }
    let st = &b[2 * PROGRAMS..];

    // The chain before: of the genesis program if this is the first
    // block, of this step's own if not; and, if not, stating the same
    // program as its own.
    let of = before.proof.verify_into(cx, &tables.compiled, reader)?;
    let p = cx.stated(&[of[2].clone(), of[3].clone()], before.stated);
    let is_first = cx.input(F(first as u128));
    assert!((is_first.clone() * is_first.clone() + is_first.clone()).is(&zero));
    let own: Vec<Sym> = halves(own).iter().map(|x| cx.input(*x)).collect();
    for (h, genesis) in constants(&plan.genesis).into_iter().enumerate() {
        let program = (genesis + own[h].clone()) * is_first.clone() + own[h].clone();
        assert!(of[h].is(&program));
        assert!(((p[h].clone() + own[h].clone()) * (is_first.clone() + one.clone())).is(&zero));
    }
    // The block follows: the height before it, the state it began from
    // and the first position it gave out are the chain's.
    assert!(p[2].is(&st[15]));
    assert!(p[3].is(&st[0]) && p[4].is(&st[1]));
    assert!(p[5].is(&st[10]));
    assert!(p[14].is(&st[17]) && p[15].is(&st[18]));

    // The emission. If no block was left of the era before (its count
    // is one), this block is the next era's first; `ended` is that, and
    // cannot be otherwise: a count less one has an inverse or is zero.
    let eras = Eras::of(&plan.emission);
    let (era, count) = (&p[12], &p[13]);
    let run_out = count.value() == F::ONE;
    let less = count.clone() + one.clone();
    let ended = cx.input(F(run_out as u128));
    let inverse = cx.input(less.value().inv());
    assert!((less.clone() * ended.clone()).is(&zero));
    assert!((less * inverse).is(&(ended.clone() + one.clone())));
    let era = ((at(&eras.next, era) + era.clone()) * ended.clone() + era.clone()).kept();
    let fewer = (count.clone() * cx.constant(COUNT.inv())).kept();
    let count = (at(&eras.reset, &era) + fewer.clone()) * ended + fewer;
    assert!(st[16].is(&at(&eras.pays, &era)));

    // The table. The work the block's proof showed is of the header
    // before this block, and of the table the chain said that header's
    // work is of: no other, larger or smaller. Then, as with the
    // emission: if no block was left before the table doubles, this
    // block's header is the next one's first.
    let sizes = Sizes::of(&plan.pow);
    let (table, grows) = (&p[20], &p[21]);
    assert!(st[29].is(&at(&sizes.mask, table)));
    let doubled = grows.value() == F::ONE;
    let less = grows.clone() + one.clone();
    let turned = cx.input(F(doubled as u128));
    let inverse = cx.input(less.value().inv());
    assert!((less.clone() * turned.clone()).is(&zero));
    assert!((less * inverse).is(&(turned.clone() + one.clone())));
    let table = ((at(&sizes.next, table) + table.clone()) * turned.clone() + table.clone()).kept();
    let fewer = (grows.clone() * cx.constant(COUNT.inv())).kept();
    let grows = (at(&sizes.reset, &table) + fewer.clone()) * turned + fewer;

    let mut stated = own;
    stated.extend([st[12].clone(), st[2].clone(), st[3].clone(), st[11].clone()]);
    stated.extend(st[4..8].iter().cloned().chain([st[13].clone(), st[14].clone(), era, count]));
    stated.extend([st[19].clone(), st[20].clone()]);

    // The work the block's proof showed is of the header before this
    // block: one that names the header the chain was at, and states
    // what the chain's proof before stated. The rest of it is the
    // prover's to give, and is bound by the id.
    let rest = halves(rest).map(|x| cx.input(x));
    let header = [p[16].clone(), p[17].clone(), of[2].clone(), of[3].clone(), rest[0].clone(), rest[1].clone()];
    let work_hash = cx.hashed(crate::hash::DOM_HEADER, &header);
    assert!(work_hash[0].is(&st[23]) && work_hash[1].is(&st[24]));
    let named: Vec<Sym> = work_hash.iter().chain(&st[25..29]).cloned().collect();
    stated.extend(cx.hashed(crate::hash::DOM_BLOCK, &named));
    stated.extend([st[21].clone(), st[22].clone()]);
    stated.extend([table, grows]);
    cx.state(&stated);
    Some(stated.iter().map(Sym::value).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alg::statement;
    use crate::block_proof::{Runs, Worked, root_into};
    use crate::header::Header;
    use crate::ledger::{MAINNET_EMISSION, MEMO, Output, Outputs, Record, Transaction, key_hash};
    use crate::pcs::Params;
    use crate::proof::{program_of, prove, prove_hidden};
    use crate::reading::Deferred;
    use crate::segment::{self, Run, closed};
    use crate::structure::Direct;
    use crate::xmss::SecretKey;

    /// Two blocks at 50, one at 20, and nothing after.
    const EMISSION: Emission = Emission(&[(2, 50), (1, 20)]);

    fn params(m: usize) -> Params {
        Params::plain(m, 1, 4, 4)
    }

    /// The proof of the work of a header of this work's hash, with a
    /// nonce: the proof, what it states, and the mix.
    fn worked(source: &impl crate::pow::ItemSource, work_hash: &Digest, nonce: u64) -> (Proved, Vec<F>, Digest) {
        let nonce = crate::pow::nonce_from_u64(nonce);
        let cx = Shared::new();
        let (work, stated) = crate::work::work_into(&cx, source, work_hash, &nonce);
        let proof = crate::proof::prove_with(cx, vec![], Some(work), params, [128, 128]);
        assert!(proof.holds && proof.verifies());
        (proof, stated, crate::pow::hashimoto(source, work_hash, &nonce).mix)
    }

    /// A block that pays its reward and nothing else, at `height`, on
    /// `state`, with the work of the header before it: its root's
    /// proof, what that states, and its statement.
    fn reward(
        tables: &Tables,
        state: &mut Outputs,
        height: u32,
        work: &(Proved, Vec<F>, Digest),
    ) -> (Proved, Vec<F>, crate::block_proof::Statement) {
        let pays = EMISSION.subsidy(height);
        let to = key_hash(&SecretKey::generate_with_height(&[7; 32], 1).public_key());
        let tx = Transaction {
            inputs: vec![],
            outputs: vec![Output::to(&to, pays, [height as u8; MEMO])],
            ops: vec![],
            policy: vec![],
            covered: 0,
        };
        let set = crate::signed::empty_roots()[crate::signed::DEPTH];
        let start = Record::block(state, height, pays);
        let mut run = Run::new(&start, closed(), &set);
        run.frontier(&state.frontier());
        run.head(&tx);
        run.output(&tx.outputs[0], &to);
        let mut record = start;
        record.apply(state, &tx).unwrap();
        let run = segment::prove(run, 512, params);
        let cx = Shared::new();
        let shown = Worked { proof: &work.0, stated: &work.1 };
        let stated = root_into(&cx, tables, &mut Direct, &Runs::One(&run), None, Some(&shown), height).unwrap();
        let proof = prove(cx, vec![], params);
        assert!(proof.holds && proof.verifies());
        let digest = |x: &[F]| -> Digest { [x[0].0.to_le_bytes(), x[1].0.to_le_bytes()].concat().try_into().unwrap() };
        let work = [digest(&work.1[0..]), digest(&work.1[2..]), digest(&work.1[4..])];
        (
            proof,
            stated,
            crate::block_proof::Statement { work, ..crate::block_proof::Statement::of(&record, pays, &set) },
        )
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_chain_of_blocks_is_one_proof() {
        let tables = Tables::new();
        let text = crate::pow::SeedText::new(crate::pow::PowParams::DEV);
        let source = text.table(10);
        let digest = |x: &[F]| -> Digest { [x[0].0.to_le_bytes(), x[1].0.to_le_bytes()].concat().try_into().unwrap() };
        // A block of the one shape there is, of some header's work: for
        // the program of its root, and what that rests on.
        let sample = reward(&tables, &mut Outputs::default(), 1, &worked(&source, &[1; 32], 0));
        let rested = std::array::from_fn(|i| digest(&sample.1[2 * i..]));

        // The shape of a chain's proof: enough rows for a step, found by
        // trying, and for the pads of a proof that hides what it is of.
        // The genesis proof is made to it. A chain's proofs are the ones
        // published: each hides the block's proofs and the proof before.
        let mut shape = [1 << 9, 1 << 15];
        let (genesis, began, plan, own) = loop {
            let cx = Shared::new();
            let began = genesis_into(&cx);
            let genesis = prove_hidden(cx, params, shape, [0xA0; 32]);
            assert!(genesis.holds && genesis.verifies() && genesis.params.blind);
            let plan = Plan::new(
                vec![Shape { root: [3; 32], rested }, Shape { root: sample.0.program, rested }],
                genesis.program,
                EMISSION,
                crate::pow::PowParams::DEV,
            );
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let (block, before) =
                (Stated { proof: &sample.0, stated: &sample.1 }, Stated { proof: &genesis, stated: &began });
            step_into(&cx, &tables, &mut reader, &plan, 1, &block, &before, true, &[0; 32], &[0; 32]).unwrap();
            reader.settle(&tables.all());
            let (hash, machine) = cx.with(|c| (c.trace.rows.len(), 2 * c.asm.finish_len()));
            if hash <= shape[0] && machine <= shape[1] {
                break (genesis, began, plan, program_of(cx, params, shape));
            }
            shape = [shape[0].max(hash.next_power_of_two()), shape[1].max(machine.next_power_of_two())];
        };

        // Four blocks, each with the work of the header before it: the
        // header that names the one the chain was at and states what the
        // chain's proof stated. Each step is of the one program, which
        // it names.
        let mut state = Outputs::default();
        let mut blocks = Vec::new();
        let mut headers: Vec<Header> = Vec::new();
        let mut chain: Vec<(Proved, Vec<F>)> = Vec::new();
        for i in 0..4 {
            let (before, tip) = match chain.last() {
                Some((proof, stated)) => (Stated { proof, stated }, digest(&stated[16..])),
                None => (Stated { proof: &genesis, stated: &began }, [0; 32]),
            };
            let rest = [0x50 + i as u8; 32];
            let work_hash = crate::header::work_hash(&tip, &before.proof.statement(), &rest);
            let work = worked(&source, &work_hash, i as u64);
            let header = Header {
                parent: tip,
                statement: before.proof.statement(),
                rest,
                nonce: crate::pow::nonce_from_u64(i as u64),
                mix: work.2,
            };
            let (proof, stated, block) = reward(&tables, &mut state, i as u32 + 1, &work);
            assert_eq!((proof.program, &stated[..2 * PROGRAMS]), (sample.0.program, &sample.1[..2 * PROGRAMS]));
            assert_eq!(block.work, [header.work_hash(), header.nonce, header.mix]);
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let this = Stated { proof: &proof, stated: &stated };
            let said = step_into(&cx, &tables, &mut reader, &plan, 1, &this, &before, i == 0, &own, &rest).unwrap();
            reader.settle(&tables.all());
            let step = prove_hidden(cx, params, shape, [0xA1 + i as u8; 32]);
            assert!(step.holds && step.verifies() && step.params.blind, "block {}", i + 1);
            assert_eq!(step.program, own, "block {}", i + 1);
            let expect = Statement::after(&own, &block, &EMISSION, &crate::pow::PowParams::DEV);
            assert_eq!((expect.era, expect.left), [(1, 1), (1, 0), (2, 0), (3, u32::MAX)][i]);
            // The chain is now at the header whose work was shown.
            assert_eq!(expect.tip, header.id());
            assert_eq!((said.clone(), step.statement()), (expect.elements(), statement(&expect.elements())));
            chain.push((step, said));
            blocks.push((proof, stated));
            headers.push(header);
        }
        assert_eq!(chain[3].1.len(), STATEMENT);
        // Each header names the one before it.
        assert!(headers.windows(2).all(|h| h[1].parent == h[0].id()));

        // What does not follow does not hold: a block out of its place,
        // a first block claimed where there was a chain, a step naming
        // another program as its own, a header that is not the one the
        // work was done on.
        let holds = |block: usize, before: Option<usize>, first: bool, own: &Digest, shape: usize, rest: &Digest| {
            let cx = Shared::new();
            let (proof, stated) = &blocks[block];
            let before = match before {
                Some(i) => Stated { proof: &chain[i].0, stated: &chain[i].1 },
                None => Stated { proof: &genesis, stated: &began },
            };
            let this = Stated { proof, stated };
            step_into(&cx, &tables, &mut Direct, &plan, shape, &this, &before, first, own, rest).unwrap();
            cx.finish().asm.finish(128).holds
        };
        let rest = headers[1].rest;
        assert!(holds(1, Some(0), false, &own, 1, &rest));
        assert!(!holds(2, Some(0), false, &own, 1, &headers[2].rest));
        assert!(!holds(1, None, true, &own, 1, &rest));
        assert!(!holds(1, Some(0), true, &own, 1, &rest));
        assert!(!holds(0, None, false, &own, 1, &headers[0].rest));
        assert!(!holds(1, Some(0), false, &[1; 32], 1, &rest));
        assert!(!holds(1, Some(0), false, &own, 1, &headers[0].rest));
        // A block of a shape that is not the plan's leaf it is said to be.
        assert!(!holds(1, Some(0), false, &own, 0, &rest));
    }

    /// The most memory the process has held, in megabytes; and the mark
    /// set back to what it holds now.
    fn peak() -> usize {
        let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
        let kb =
            status.lines().find(|l| l.starts_with("VmHWM")).and_then(|l| l.split_whitespace().nth(1)?.parse().ok());
        let _ = std::fs::write("/proc/self/clear_refs", "5");
        kb.unwrap_or(0usize) / 1024
    }

    /// What a block of a reward alone costs at the chain's parameters:
    /// each proof under it, and the chain's proof, which is what a node
    /// is sent.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn reward_block_timing() {
        use std::time::Instant;
        let params = |m: usize| Params::proven(m, 2, crate::pcs::SECURITY);
        // The chain's proof is the one published: it grinds its queries
        // more, for fewer of them.
        let grind: usize = std::env::var("GRIND").ok().and_then(|g| g.parse().ok()).unwrap_or(24);
        let published = move |m: usize| Params::proven_ground(m, 2, crate::pcs::SECURITY, grind);
        let tables = Tables::new();
        let text = crate::pow::SeedText::new(crate::pow::PowParams::MAINNET);
        let source = text.table(crate::pow::PowParams::MAINNET.log_dataset_items);
        let digest = |x: &[F]| -> Digest { [x[0].0.to_le_bytes(), x[1].0.to_le_bytes()].concat().try_into().unwrap() };
        let set = crate::signed::empty_roots()[crate::signed::DEPTH];
        let to = key_hash(&SecretKey::generate_with_height(&[7; 32], 1).public_key());
        // A block's proofs, each timed: the work of the header before,
        // the run of its one transaction, and the root over both.
        let block = |state: &mut Outputs, height: u32, work_hash: &Digest, say: bool| {
            let nonce = crate::pow::nonce_from_u64(height as u64);
            peak();
            let t = Instant::now();
            let cx = Shared::new();
            let (work, worked) = crate::work::work_into(&cx, &source, work_hash, &nonce);
            let work = crate::proof::prove_with(cx, vec![], Some(work), params, [128, 128]);
            let (work_time, work_peak) = (t.elapsed(), peak());
            let pays = MAINNET_EMISSION.subsidy(height);
            let tx = Transaction {
                inputs: vec![],
                outputs: vec![Output::to(&to, pays, [height as u8; MEMO])],
                ops: vec![],
                policy: vec![],
                covered: 0,
            };
            let start = Record::block(state, height, pays);
            let t = Instant::now();
            let mut run = Run::new(&start, closed(), &set);
            run.frontier(&state.frontier());
            run.head(&tx);
            run.output(&tx.outputs[0], &to);
            let run = segment::prove(run, 512, params);
            let (run_time, run_peak) = (t.elapsed(), peak());
            let mut record = start;
            record.apply(state, &tx).unwrap();
            let t = Instant::now();
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let shown = Worked { proof: &work, stated: &worked };
            let stated = root_into(&cx, &tables, &mut reader, &Runs::One(&run), None, Some(&shown), height).unwrap();
            reader.settle(&tables.all());
            let root = prove(cx, vec![], params);
            let (root_time, root_peak) = (t.elapsed(), peak());
            assert!(work.holds && root.holds);
            if say {
                let rows = |p: &Proved| format!("2^{} elements", p.params.m);
                println!("  work:  {work_time:.2?}, {work_peak} MB, {} KB, {}", work.size() / 1000, rows(&work));
                println!("  run:   {run_time:.2?}, {run_peak} MB, {} KB", run.proof.size() / 1000);
                println!(
                    "  root:  {root_time:.2?}, {root_peak} MB, {} KB, {} ({:?})",
                    root.size() / 1000,
                    rows(&root),
                    root.tables
                );
            }
            (root, stated, work_time + run_time + root_time, work_peak.max(run_peak).max(root_peak))
        };
        let mut state = Outputs::default();
        let first = block(&mut state, 1, &[1; 32], false);
        let rested = std::array::from_fn(|i| digest(&first.1[2 * i..]));
        // The chain's shape, found by trying from the one expected.
        let mut shape = [1 << 16, 1 << 19];
        let (genesis, began, plan, own) = loop {
            let cx = Shared::new();
            let began = genesis_into(&cx);
            let genesis = prove_hidden(cx, published, shape, [0xB0; 32]);
            let plan = Plan::new(
                vec![Shape { root: first.0.program, rested }],
                genesis.program,
                MAINNET_EMISSION,
                crate::pow::PowParams::MAINNET,
            );
            let step = || {
                let cx = Shared::new();
                let mut reader = Deferred::new(&cx);
                let (this, before) =
                    (Stated { proof: &first.0, stated: &first.1 }, Stated { proof: &genesis, stated: &began });
                step_into(&cx, &tables, &mut reader, &plan, 0, &this, &before, true, &[0; 32], &[0; 32]).unwrap();
                reader.settle(&tables.all());
                cx
            };
            // The rows a step takes, by making them.
            let made = step().finish();
            let (hash, machine) = (made.trace.rows.len(), made.asm.finish(128).inputs.len());
            println!(
                "a step: {hash} hash rows, 2^{} machine rows; shape 2^{}, 2^{}",
                machine.trailing_zeros(),
                shape[0].trailing_zeros(),
                shape[1].trailing_zeros()
            );
            if hash <= shape[0] && machine <= shape[1] {
                let own = program_of(step(), published, shape);
                break (genesis, began, plan, own);
            }
            shape = [shape[0].max(hash.next_power_of_two()), shape[1].max(machine)];
        };
        // Two blocks: the second's step verifies a step's proof, as
        // every step after it does.
        let mut state = Outputs::default();
        let mut last: Option<(Proved, Vec<F>)> = None;
        for i in 0..2u32 {
            let (before, tip) = match &last {
                Some((proof, stated)) => (Stated { proof, stated }, digest(&stated[16..])),
                None => (Stated { proof: &genesis, stated: &began }, [0; 32]),
            };
            let rest = [0x60 + i as u8; 32];
            let work_hash = crate::header::work_hash(&tip, &before.proof.statement(), &rest);
            println!("block {}:", i + 1);
            let (root, stated, under, under_peak) = block(&mut state, i + 1, &work_hash, true);
            peak();
            let t = Instant::now();
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let this = Stated { proof: &root, stated: &stated };
            let said = step_into(&cx, &tables, &mut reader, &plan, 0, &this, &before, i == 0, &own, &rest).unwrap();
            reader.settle(&tables.all());
            let (hash, machine) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
            let step = prove_hidden(cx, published, shape, [0xB1 + i as u8; 32]);
            let (step_time, step_peak) = (t.elapsed(), peak());
            assert!(step.holds && step.program == own);
            let t = Instant::now();
            assert!(step.verifies());
            let (verify_time, verify_peak) = (t.elapsed(), peak());
            println!(
                "  step:  {step_time:.2?}, {step_peak} MB, 2^{} elements; {hash} of {} hash rows, {} machine rows used of {} ({machine} operations)",
                step.params.m, shape[0], step.used, shape[1]
            );
            println!(
                "  block {}: {:.2?} in all, {} MB at most; the chain's proof {} bytes, verified in {verify_time:.2?} ({verify_peak} MB held, the circuits made with it)",
                i + 1,
                under + step_time,
                under_peak.max(step_peak),
                step.size()
            );
            // The proof as a node is sent it, for a process that only
            // verifies ([`a_chain_s_proof_is_verified`]).
            if let Ok(path) = std::env::var("DUMP") {
                let words = step.public.iter().flat_map(|w| w.to_le_bytes());
                let bytes: Vec<u8> = step.program.into_iter().chain(words).chain(step.proof.to_bytes()).collect();
                std::fs::write(path, bytes).unwrap();
            }
            last = Some((step, said));
        }
    }

    /// A block of 256 signatures, from its signatures to the chain's
    /// proof, at the chain's parameters: 128 payments of two inputs and
    /// two outputs, spending what the block before made. What each proof
    /// takes, what can be made before the block is known, and the most
    /// memory held.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn full_small_block_timing() {
        use crate::block_proof::{Beside, beside_into, root_with};
        use crate::ledger::Input;
        use crate::signature::{Signed, node_into, segment_into};
        use crate::signed;
        use std::time::{Duration, Instant};
        let params = |m: usize| Params::proven(m, 2, crate::pcs::SECURITY);
        let published = |m: usize| Params::proven_ground(m, 2, crate::pcs::SECURITY, 24);
        let tables = Tables::new();
        let text = crate::pow::SeedText::new(crate::pow::PowParams::MAINNET);
        let source = text.table(crate::pow::PowParams::MAINNET.log_dataset_items);
        let digest = |x: &[F]| -> Digest { [x[0].0.to_le_bytes(), x[1].0.to_le_bytes()].concat().try_into().unwrap() };
        let (payments, per_proof) = (128usize, 64usize);
        let mut most = 0usize;
        let mut timed = |name: &str, t: Instant, what: String| -> Duration {
            let (took, held) = (t.elapsed(), peak());
            most = most.max(held);
            println!("  {name}: {took:.2?}, {held} MB{what}");
            took
        };
        let shape = |p: &Proved| format!(", {} KB, 2^{} elements", p.size() / 1000, p.params.m);
        let worked = |work_hash: &Digest, n: u64| {
            let cx = Shared::new();
            let (work, stated) = crate::work::work_into(&cx, &source, work_hash, &crate::pow::nonce_from_u64(n));
            (crate::proof::prove_with(cx, vec![], Some(work), params, [128, 128]), stated)
        };

        // The block before: one transaction that makes the 256 outputs,
        // each a key's. Its proofs are not what is measured.
        let mut keys: Vec<SecretKey> = (0..2 * payments)
            .map(|i| SecretKey::generate_with_height(&[i as u8, (i >> 8) as u8 + 1].repeat(16).try_into().unwrap(), 2))
            .collect();
        let hashes: Vec<Digest> = keys.iter().map(|k| key_hash(&k.public_key())).collect();
        let pays = MAINNET_EMISSION.subsidy(1);
        let amount = |i: usize| if i == 0 { pays - 100 * (2 * payments as u64 - 1) } else { 100 };
        let made = Transaction {
            inputs: vec![],
            outputs: (0..2 * payments).map(|i| Output::to(&hashes[i], amount(i), [i as u8; MEMO])).collect(),
            ops: vec![],
            policy: vec![],
            covered: 0,
        };
        let nothing = signed::empty_roots()[signed::DEPTH];
        let mut state = Outputs::default();
        let start = Record::block(&state, 1, pays);
        let mut run = Run::new(&start, closed(), &nothing);
        run.head(&made);
        let mut owned = Vec::new();
        for (i, output) in made.outputs.iter().enumerate() {
            run.output(output, &hashes[i]);
            let position = state.insert(output, 1);
            owned.push(Input {
                key: keys[i].public_key(),
                amount: amount(i),
                memo: [i as u8; MEMO],
                created: 1,
                position,
            });
        }
        let run = segment::prove(run, 512, params);
        let first_work = worked(&[1; 32], 0);
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let shown = Worked { proof: &first_work.0, stated: &first_work.1 };
        let first_stated = root_into(&cx, &tables, &mut reader, &Runs::One(&run), None, Some(&shown), 1).unwrap();
        reader.settle(&tables.all());
        let first_root = prove(cx, vec![], params);
        assert!(first_root.holds);

        // The block measured. Its signatures, in four proofs; the three
        // that join them: all of it before any block is known.
        println!("made ahead:");
        peak();
        let subsidy = MAINNET_EMISSION.subsidy(2);
        let txs: Vec<Transaction> = (0..payments)
            .map(|t| {
                let total = owned[2 * t].amount + owned[2 * t + 1].amount + if t == 0 { subsidy } else { 0 };
                Transaction {
                    inputs: vec![owned[2 * t].clone(), owned[2 * t + 1].clone()],
                    outputs: vec![Output::to(&hashes[0], total - 50, [9; MEMO]), Output::to(&hashes[1], 50, [8; MEMO])],
                    ops: vec![],
                    policy: vec![],
                    covered: 0,
                }
            })
            .collect();
        let mut signatures = Vec::new();
        for (t, tx) in txs.iter().enumerate() {
            for k in [2 * t, 2 * t + 1] {
                let sig = keys[k].sign(&tx.id()).unwrap();
                signatures.push((keys[k].public_key(), tx.id(), sig));
            }
        }
        let mut ahead = Duration::ZERO;
        let mut segments: Vec<(Proved, Digest)> = Vec::new();
        for some in signatures.chunks(per_proof) {
            let t = Instant::now();
            let cx = Shared::new();
            let mut chains = Vec::new();
            let root = segment_into(&cx, &mut chains, some, per_proof).unwrap();
            let proof = prove(cx, chains, params);
            assert!(proof.holds);
            ahead += timed(&format!("{} signatures", some.len()), t, shape(&proof));
            segments.push((proof, root));
        }
        let mut node = |name: &str, a: &Signed, b: &Signed| {
            let t = Instant::now();
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let stated = node_into(&cx, &tables.compiled, &mut reader, [a, b]).unwrap();
            reader.settle(&tables.all());
            let proof = prove(cx, vec![], params);
            assert!(proof.holds);
            ahead += timed(name, t, shape(&proof));
            (proof, stated)
        };
        let leaves: Vec<Signed> = segments.iter().map(|(p, root)| Signed::Segment(p, *root)).collect();
        let left = node("two proofs of signatures joined", &leaves[0], &leaves[1]);
        let right = node("two proofs of signatures joined", &leaves[2], &leaves[3]);
        let top = node("the two joins joined", &Signed::Node(&left.0, &left.1), &Signed::Node(&right.0, &right.1));
        let all = Signed::Node(&top.0, &top.1);
        let (entries_root, level) = all.root();
        let set = signed::lift(&entries_root, level, signed::DEPTH);
        // Every entry's place in the set: a proof's slots, one proof
        // after another.
        let mut slots = vec![crate::hash::EMPTY; segments.len() * signed::SLOTS];
        for (i, (pk, msg, sig)) in signatures.iter().enumerate() {
            slots[i / per_proof * signed::SLOTS + i % per_proof] = crate::signature::entry(pk, msg, sig.index);
        }
        let tree = signed::Tree::new(&slots);
        assert_eq!(tree.root(), entries_root);

        // The chain so far: its beginning, and the block before.
        let (genesis, began, plan, own, sized) = {
            // The two shapes of block: one whose root verifies the work
            // alone, and one whose root verifies signatures and work as
            // one proof. The second's programs are known once it is
            // made; for the plan it is made below, of this block.
            let _ = &first_stated;
            (None::<Proved>, None::<Vec<F>>, None::<Plan>, None::<Digest>, [1usize << 16, 1 << 19])
        };
        let _ = (genesis, began, plan, own);

        println!("after the block before is known:");
        let mut after = Duration::ZERO;
        // The chain's proof before this block states what the header
        // before must: so the block before is stepped first (not timed),
        // with a plan that names this block's shape, which needs this
        // block's root's programs. Those do not depend on what the block
        // holds: a root made of this block against any header gives them.
        let rest = [0x71; 32];
        let build = |work: &(Proved, Vec<F>)| {
            let start = Record::block(&state, 2, subsidy);
            let mut local = state.clone();
            let mut run = Run::new(&start, closed(), &set);
            let spent = txs.iter().flat_map(|tx| tx.inputs.iter().map(|i| i.position));
            run.frontier(&state.frontier_without(spent));
            let mut record = start;
            let mut applied = state.clone();
            for (n, tx) in txs.iter().enumerate() {
                run.head(tx);
                for (k, input) in tx.inputs.iter().enumerate() {
                    let i = 2 * n + k;
                    let place = i / per_proof * signed::SLOTS + i % per_proof;
                    let mut siblings = tree.path(place).siblings;
                    siblings.extend_from_slice(&signed::empty_roots()[level..signed::DEPTH]);
                    run.input(input, &local.path(input.position), signatures[i].2.index, &(place as u64, siblings));
                    local.set(input.position, crate::hash::EMPTY);
                }
                // (What the run makes is in the root at its end: its
                // paths are the tree's without.)
                for output in &tx.outputs {
                    let to = if output.amount == 50 { &hashes[1] } else { &hashes[0] };
                    run.output(output, to);
                }
                record.apply(&mut applied, tx).unwrap();
            }
            let run = segment::prove(run, 512, params);
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let shown = Worked { proof: &work.0, stated: &work.1 };
            let both = beside_into(&cx, &tables, &mut reader, &all, &shown).unwrap();
            reader.settle(&tables.all());
            let beside = prove(cx, vec![], params);
            assert!(beside.holds);
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let stated =
                root_with(&cx, &tables, &mut reader, &Runs::One(&run), &Beside::Joined(&beside, &both), 2).unwrap();
            reader.settle(&tables.all());
            let root = prove(cx, vec![], params);
            assert!(root.holds);
            (root, stated)
        };
        // (The closure above is run twice: once for the shape, once
        // against the real header, timed by hand below.)
        let sample = build(&first_work);
        let rested = |stated: &[F]| -> [Digest; PROGRAMS] { std::array::from_fn(|i| digest(&stated[2 * i..])) };
        let shapes = vec![
            Shape { root: first_root.program, rested: rested(&first_stated) },
            Shape { root: sample.0.program, rested: rested(&sample.1) },
        ];
        let cx = Shared::new();
        let began = genesis_into(&cx);
        let genesis = prove_hidden(cx, published, sized, [0xC0; 32]);
        let plan = Plan::new(shapes, genesis.program, MAINNET_EMISSION, crate::pow::PowParams::MAINNET);
        let step = |index: usize, this: &Stated, before: &Stated, first: bool, own: &Digest, rest: &Digest| {
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let said = step_into(&cx, &tables, &mut reader, &plan, index, this, before, first, own, rest).unwrap();
            reader.settle(&tables.all());
            (cx, said)
        };
        let origin = Stated { proof: &genesis, stated: &began };
        let first_block = Stated { proof: &first_root, stated: &first_stated };
        let own = program_of(step(0, &first_block, &origin, true, &[0; 32], &[0; 32]).0, published, sized);
        // The block before's real root: against the header the chain
        // begins from.
        let genesis_header = crate::header::work_hash(&[0; 32], &genesis.statement(), &[0x70; 32]);
        let work_one = worked(&genesis_header, 1);
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let shown = Worked { proof: &work_one.0, stated: &work_one.1 };
        let one_stated = root_into(&cx, &tables, &mut reader, &Runs::One(&run), None, Some(&shown), 1).unwrap();
        reader.settle(&tables.all());
        let one_root = prove(cx, vec![], params);
        let (cx, one_said) =
            step(0, &Stated { proof: &one_root, stated: &one_stated }, &origin, true, &own, &[0x70; 32]);
        let one_step = prove_hidden(cx, published, sized, [0xC1; 32]);
        assert!(one_step.holds && one_step.program == own);
        peak();

        // Now the block measured, against the header before it.
        let before = Stated { proof: &one_step, stated: &one_said };
        let work_hash = crate::header::work_hash(&digest(&one_said[16..]), &one_step.statement(), &rest);
        let t = Instant::now();
        let work = worked(&work_hash, 2);
        after += timed("the work of the header before", t, shape(&work.0));
        let t = Instant::now();
        let (root, stated) = build(&work);
        after += timed("the run, signatures and work as one, and the root", t, shape(&root));
        let t = Instant::now();
        let (cx, _) = step(1, &Stated { proof: &root, stated: &stated }, &before, false, &own, &rest);
        let (hash, used) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
        let last = prove_hidden(cx, published, sized, [0xC2; 32]);
        assert!(last.holds && last.program == own && last.verifies());
        after += timed("the chain's step", t, format!("{}; {hash} hash rows, {used} operations", shape(&last)));
        println!(
            "a block of {} signatures in {payments} payments: {:.1?} made ahead, {:.1?} after; {:.1?} in all; \
             {most} MB at most; the chain's proof {} bytes",
            signatures.len(),
            ahead,
            after,
            ahead + after,
            last.size()
        );
    }

    /// What verifying a chain's proof takes of a process that does
    /// nothing else: the proof is read from the file `DUMP` names,
    /// which the timing above wrote.
    #[test]
    #[ignore = "timing; run with --release --nocapture, after the block's timing with DUMP set"]
    fn a_chain_s_proof_is_verified() {
        let bytes = std::fs::read(std::env::var("DUMP").expect("a file to read")).unwrap();
        let grind: usize = std::env::var("GRIND").ok().and_then(|g| g.parse().ok()).unwrap_or(24);
        let program: Digest = bytes[..32].try_into().unwrap();
        let public: Vec<u32> = bytes[32..64].chunks(4).map(|w| u32::from_le_bytes(w.try_into().unwrap())).collect();
        let proof = crate::argument::Proof::from_bytes(&bytes[64..]).expect("a proof");
        let before = peak();
        let t = std::time::Instant::now();
        let (hash, machine) = (crate::recursion::circuit(), crate::machine::circuit());
        let made = t.elapsed();
        let tables = [
            crate::argument::Table { circuit: &hash, rows: 1 << 16, public: &[] },
            crate::argument::Table { circuit: &machine, rows: 1 << 19, public: &public },
        ];
        let params = Params::proven_ground(24, 2, crate::pcs::SECURITY, grind).hiding();
        let domain = crate::ntt::Domain::new(params.k(), false);
        let t = std::time::Instant::now();
        let work = crate::argument::verify_tables(&params, &domain, &tables, Some(&program), &proof);
        let took = t.elapsed();
        assert!(work.is_some());
        println!(
            "a chain's proof of {} bytes: verified in {took:.2?} ({} compressions), the two circuits made in {made:.2?}; \
             the process held {} MB at most ({before} MB before it began)",
            bytes.len() - 64,
            work.unwrap().compressions,
            peak()
        );
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_block_that_pays_itself_too_much_is_no_block() {
        // The third block is the second era's: it pays 20. One that
        // takes 50 has a root that holds (its sums agree) and a step
        // that does not; one whose outputs are more than it says it
        // pays has no root.
        let tables = Tables::new();
        let to = key_hash(&SecretKey::generate_with_height(&[7; 32], 1).public_key());
        let state = Outputs::default();
        let set = crate::signed::empty_roots()[crate::signed::DEPTH];
        let root_holds = |says: u64, takes: u64| {
            let tx = Transaction {
                inputs: vec![],
                outputs: vec![Output::to(&to, takes, [0; MEMO])],
                ops: vec![],
                policy: vec![],
                covered: 0,
            };
            let start = Record::block(&state, 3, says);
            let mut run = Run::new(&start, closed(), &set);
            run.frontier(&state.frontier());
            run.head(&tx);
            run.output(&tx.outputs[0], &to);
            let run = segment::prove(run, 512, params);
            let cx = Shared::new();
            root_into(&cx, &tables, &mut Direct, &Runs::One(&run), None, None, 3).unwrap();
            cx.finish().asm.finish(128).holds
        };
        assert!(root_holds(20, 20) && root_holds(50, 50));
        assert!(!root_holds(20, 50) && !root_holds(20, 19));
        // Nor has one whose transactions carry an operation on a name
        // that is not done, or that does one none carried: done after
        // the transactions, they are the ones carried.
        let named = |carried: bool, done: bool| {
            let (commit, memo) = ([3; 32], [4; MEMO]);
            let op = crate::registry::Op::Commit { commit, memo };
            let tx = Transaction {
                inputs: vec![],
                outputs: vec![Output::to(&to, 20, [0; MEMO])],
                ops: if carried { vec![op.clone()] } else { vec![] },
                policy: vec![],
                covered: 0,
            };
            let start = Record::block(&state, 3, 20);
            let mut run = Run::new(&start, closed(), &set);
            run.head(&tx);
            run.output(&tx.outputs[0], &to);
            if carried {
                run.carried(&op.digest());
            }
            if done {
                run.commit(&commit, &memo);
            }
            let run = segment::prove(run, 512, params);
            let cx = Shared::new();
            root_into(&cx, &tables, &mut Direct, &Runs::One(&run), None, None, 3).unwrap();
            cx.finish().asm.finish(128).holds
        };
        assert!(named(true, true));
        assert!(!named(true, false) && !named(false, true));
        // The schedule, as the step's arithmetic has it.
        let eras = Eras::of(&EMISSION);
        let pays: Vec<F> = (0..4).map(|e| at(&eras.pays, &F(e))).collect();
        assert_eq!(pays, [F(0), F(50), F(20), F(0)]);
        assert_eq!((0..4).map(|e| at(&eras.next, &F(e))).collect::<Vec<_>>(), [F(1), F(2), F(3), F(3)]);
        assert_eq!(at(&eras.reset, &F(1)), COUNT);
        assert_eq!(
            (EMISSION.subsidy(0), EMISSION.subsidy(2), EMISSION.subsidy(3), EMISSION.subsidy(4)),
            (0, 50, 20, 0)
        );
        // The count's element does not come back to one within any era:
        // its order has a prime of 47 bits in it.
        let large = 67_280_421_310_721u128;
        assert_eq!(u128::MAX % large, 0);
        assert_ne!(power(COUNT, u128::MAX / large), F::ONE);
    }

    /// The table a statement says the next work is of, and its count,
    /// go from block to block by the step's arithmetic as the chain's
    /// own rule has them; and the mask the step holds a work to is that
    /// of the table the chain checks that header's work with. For a
    /// table that doubles twice, one that doubles five times, and one
    /// that does not grow.
    #[test]
    fn the_table_is_followed_from_block_to_block() {
        use crate::pow::PowParams;
        let small = |room: u32, epoch_blocks: u32| PowParams {
            log_dataset_items: 10,
            max_log_dataset_items: 10 + room,
            epoch_blocks,
            ..PowParams::DEV
        };
        for pow in [small(2, 4), small(5, 3), small(1, 2), PowParams::DEV] {
            let sizes = Sizes::of(&pow);
            let count = |left: u32| if left == u32::MAX { F::ZERO } else { power(COUNT, left as u128) };
            assert_eq!(Statement::table_at(&pow, 0), (0, 0));
            for height in 0..40u32 {
                let (table, grows) = Statement::table_at(&pow, height);
                // The work of the header at this height is of this table.
                let mask = crate::work::pairs_mask(pow.log_items_at(height as u64));
                assert_eq!(at(&sizes.mask, &F(table as u128)), F(mask as u128), "height {height}");
                // The step: one block fewer, or the next table.
                let (t, c) = (F(table as u128), count(grows));
                let turned = if c == F::ONE { F::ONE } else { F::ZERO };
                let next = (at(&sizes.next, &t) + t) * turned + t;
                let fewer = c * COUNT.inv();
                let left = (at(&sizes.reset, &next) + fewer) * turned + fewer;
                let (table, grows) = Statement::table_at(&pow, height + 1);
                assert_eq!((next, left), (F(table as u128), count(grows)), "after height {height}");
            }
        }
        // The main network's: its first table for a year of blocks, and
        // the sixth for good.
        let main = PowParams::MAINNET;
        assert_eq!(Statement::table_at(&main, 1), (1, main.epoch_blocks - 2));
        assert_eq!(Statement::table_at(&main, main.epoch_blocks - 1), (1, 0));
        assert_eq!(Statement::table_at(&main, main.epoch_blocks), (2, main.epoch_blocks - 1));
        assert_eq!(Statement::table_at(&main, 5 * main.epoch_blocks), (6, u32::MAX));
        assert_eq!(Statement::table_at(&main, u32::MAX), (6, u32::MAX));
    }
}
