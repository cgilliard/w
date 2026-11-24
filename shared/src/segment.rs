//! A run of a block's transactions, as rows of a circuit: the proof
//! that the state went from one root to another by payments whose keys
//! signed them and by operations on names ([`crate::ledger`],
//! [`crate::registry`]).
//!
//! A row is one compression and says of itself what it is for, by a
//! bit set among three words, its **kind**. Beside the compression a row
//! holds registers, each as the row before left it or set as the kind
//! says, and which kind may follow which is fixed. So the rows are a
//! small machine whose program is the block's to choose, within what
//! the kinds allow.
//!
//! # An input (110 rows)
//!
//! | kind | the row hashes | and so |
//! |---|---|---|
//! | `KEY` | the key | its hash |
//! | `ENT1`, `ENT2` | the key again, then the transaction's id and a leaf's index | the entry a signature of the id by the key would have ([`crate::signature::entry`]) |
//! | `SN`, 21 | a pair of the signed set, by the bits of a place the prover names | the entry is in the set: its key signed |
//! | `COMMIT` | the key's hash and an amount | the commitment |
//! | `BODYIN` | the body so far and the commitment | the id is of this input |
//! | `LEAF` | commitment, memo, amount, a height | the output's leaf |
//! | `OLD`, `NEW`, 41 of each | a level of the leaf's path, and of the same path from nothing | the leaf is in the state, and the state without it |
//! | `ISP` | the block's spent positions so far and this one | the root, the sum |
//!
//! # An output (8 rows, and 2 for each node it is joined with)
//!
//! `OUTC` (a key's hash and the amount: the commitment, so that the
//! amount on the chain is the amount to spend), `OLEAF` (the leaf, at
//! the block's height), `OITEM` (the output as the id and the block
//! take it), `BODYOUT`, then the leaf joins the tree's nodes that are
//! held (below), and `OSP`.
//!
//! # The outputs a run makes
//!
//! Outputs are made at one position after another, so all that making
//! them needs of the tree is the nodes to the left of the next
//! position's path: one at each level the position has a bit at. The
//! run holds them as a chain of hashes, the lowest last. A leaf at a
//! position is joined with the node held at each level the position
//! has a bit at, lowest first (`POP`, which opens the chain, and `MRG`,
//! which hashes the pair), and what that leaves is held in its turn
//! (`PUSH`). A row or three a leaf, about: where a path of its own is
//! two rows a level.
//!
//! The run's outputs come into the root at its end, by two walks up the
//! tree, each from an empty leaf with the nodes held to its left and
//! nothing to its right (`SETL`; a level is `WPOP` and `WNODEL` where
//! the position has a bit and `WNODER` where it has none, and `WEMP`
//! for the next level's nothing; `WEND1`, `WEND2`):
//!
//! - from the position the run began at, with the chain it began with,
//!   to the root as the run's spending left it: so the nodes the prover
//!   said it held are the tree's, and nothing was to their right;
//! - from the next position, with the chain as it is now, to the root
//!   with the outputs in it.
//!
//! So what a run spends is the tree's without the outputs the run
//! itself makes, and a run that made outputs does not end before they
//! are in.
//!
//! # A transaction
//!
//! `HEAD` hashes its counts: the body's start. It may come only when
//! the transaction before is whole: no input left and nothing left to
//! make, and the body's hash the id every entry was looked up under.
//! Within a run inputs come before what is made; the id is of the items
//! in the order they were taken in, each marked as what it is.
//!
//! # Names
//!
//! A transaction carries its operations on names by their hashes:
//! `OPBODY` takes one into the id, `OPSGN` into the block's running
//! hash of what its transactions carry. Nothing is done there. The
//! operations are done after the block's last transaction, each taken
//! into a second running hash, of what is done; a block's root finds
//! the two the same. So what a block lists says nothing of which
//! transaction an operation came with: a commitment's output comes
//! after every payment's, a reveal's spending after every input's.
//!
//! - **Commit**: `OPC` (the operation's hash) · `CLEAF` (the
//!   commitment's leaf, an output of no amount) · the leaf joins the
//!   nodes held · `OPSP`.
//! - **Reveal**: `REC1`, `REC2` (the record's hash) · `COM1`, `COM2`
//!   (the commitment, of the record's name and owner and a salt) ·
//!   `RLEAF` (the commitment's leaf; made 1 to 288 blocks ago) · the
//!   outputs' walk · `ISP` · `NLEAFR` (the name's leaf; nothing at its
//!   place) · the registry's walk, 128 of (`NOLD`, `NNEW`) · `NEND` ·
//!   `OPX` · `OPABS`.
//! - **Update**: `REC1`, `REC2` · `UMSG` (what the owner signs) ·
//!   `UKEY`, `ENT1`, `ENT2U`, 21 × `SN` (the owner's entry in the signed
//!   set) · `OREC1`, `OREC2` (the old record's hash, its owner that
//!   key's hash) · `NLEAFO`, `NLEAFN` · the registry's walk · `NEND` ·
//!   `OPX` · `OPABS`.
//! - **Sweep**, after the operations: `SLEAF` (a commitment's leaf, made
//!   more than 288 blocks ago) · the outputs' walk · `ISP`.
//!
//! Two registers say that operations have begun, after which no
//! transaction begins, and that sweeps have, after which no operation
//! is done.
//!
//! A register, the **flow**, says which of these is in hand, so that a
//! row that belongs to one cannot be reached from another. How many of
//! each a block has had is a bit moving up a word, and a row that would
//! move it past the block's cap is refused.
//!
//! Left to the node, which has the block: that a name is of the
//! characters a name may have, and that an update's owner is another
//! than the name had.
//!
//! # What a run is of
//!
//! Its public values are the registers a block's runs are joined by,
//! as the first row has them and as the last leaves them: the outputs'
//! root and the registry's, the running hashes of positions spent, of
//! outputs made, and of operations carried and done, the next position,
//! the sums, the counts of names' operations and how far the block is
//! (transactions, operations, sweeps), and the transaction in hand (its id, its body so far,
//! what is left of it), so a transaction may lie across two runs; with
//! the height and the signed set's root. A run must end between items.

use crate::alg::Alg;
use crate::argument::{self, Program, Proof, Statement, Table, variables};
use crate::blake3::{self, CHUNK_END, CHUNK_START, KEYED_HASH, ROOT};
use crate::circuit::{Circuit, Ctx, Expr, Fixed, Pre, Sum, Symbolic, Term, Witness, compress};
use crate::hash::{
    DOM_BODY, DOM_BODY_IN, DOM_BODY_OP, DOM_BODY_OUT, DOM_COMMIT, DOM_COMMITMENT, DOM_COND, DOM_COVERED, DOM_HASHLOCK,
    DOM_INPUTS, DOM_NAME_LEAF, DOM_NAME_NODE, DOM_OP, DOM_OPS, DOM_OUT_ITEM, DOM_OUTPUTS, DOM_POLICY_LEAF,
    DOM_POLICY_NODE, DOM_PUBKEY, DOM_REBIND, DOM_RECORD, DOM_SIGNED, DOM_SIGNED_NODE, DOM_SIGNERS, DOM_STACK,
    DOM_STATE_LEAF, DOM_STATE_NODE, DOM_UPDATE, Digest,
};
use crate::ledger::{Input, Memo, OUTPUTS_HEIGHT, Output, Record, Transaction};
use crate::ntt::Domain;
use crate::pcs::Params;
use crate::registry::{self, MAX_COMMITS, MAX_REVEAL, MAX_REVEALS, MAX_SWEEPS, MAX_UPDATES};
use crate::signed;
use crate::structure::Reader;
use crate::sym::{Hashed, HashedOpens, Shared, Sym};
use crate::xmss::PublicKey;

const START: usize = 0;
const HEAD: usize = 1;
const KEY: usize = 2;
const ENT1: usize = 3;
const ENT2: usize = 4;
const SN: usize = 5;
const COMMIT: usize = 6;
const BODYIN: usize = 7;
const LEAF: usize = 8;
const OLD: usize = 9;
const NEW: usize = 10;
const ISP: usize = 11;
const OUTC: usize = 12;
const OLEAF: usize = 13;
const OITEM: usize = 14;
const BODYOUT: usize = 15;
const OSP: usize = 16;
const PAD: usize = 17;
const OPC: usize = 18;
const CLEAF: usize = 19;
const OPSGN: usize = 20;
const OPSP: usize = 21;
const REC1: usize = 22;
const REC2: usize = 23;
const COM1: usize = 24;
const COM2: usize = 25;
const RLEAF: usize = 26;
const NLEAFR: usize = 27;
const NOLD: usize = 28;
const NNEW: usize = 29;
const NEND: usize = 30;
const OPX: usize = 31;
const OPBODY: usize = 32;
const OPABS: usize = 33;
const UMSG: usize = 34;
const UKEY: usize = 35;
const ENT2U: usize = 36;
const OREC1: usize = 37;
const OREC2: usize = 38;
const NLEAFO: usize = 39;
const NLEAFN: usize = 40;
const SLEAF: usize = 41;
const PSTART: usize = 42;
const TSTART: usize = 43;
const PKEY: usize = 44;
const ENT2P: usize = 45;
const PSIG: usize = 46;
const PSKIP: usize = 47;
const CTHRESH: usize = 48;
const CHASHP: usize = 49;
const CHASH: usize = 50;
const CAFTER: usize = 51;
const COLDER: usize = 52;
const PLEAF: usize = 53;
const PNODE: usize = 54;
const PCOMMIT: usize = 55;
const PSLEAF: usize = 56;
const COVR: usize = 57;
const COUTS: usize = 58;
const CSTATE: usize = 59;
const RSTART: usize = 60;
const RMSG2: usize = 61;
const ENT2R: usize = 62;
const CREBIND: usize = 63;
const POP: usize = 64;
const MRG: usize = 65;
const PUSH: usize = 66;
const SETL: usize = 67;
const WPOP: usize = 68;
const WNODEL: usize = 69;
const WNODER: usize = 70;
const WEMP: usize = 71;
const WEND1: usize = 72;
const WEND2: usize = 73;
const KINDS: usize = 74;
/// Words the kind's bit is among.
const KIND_WORDS: usize = KINDS.div_ceil(32);
/// Words of a row before its flags: the compression's, and the kind's.
const FRONT: usize = 26 + KIND_WORDS;

const FULL: u32 = KEYED_HASH | CHUNK_START | CHUNK_END | ROOT;
const BEGUN: u32 = KEYED_HASH | CHUNK_START;
const ENDED: u32 = KEYED_HASH | CHUNK_END | ROOT;

/// Between a transaction's items, or between transactions.
const BETWEEN: [usize; 8] = [START, HEAD, ISP, OSP, OPSP, OPABS, OPSGN, WEND2];

/// What a kind's row hashes with, and what may come before it: the
/// domain (none for a row that goes on with the hash before it, or
/// hashes nothing that counts), whether it goes on, the block's length,
/// the flags, and the kinds before.
struct Spec {
    domain: Option<u32>,
    goes_on: bool,
    len: u32,
    flags: u32,
    before: &'static [usize],
}

const fn spec(domain: u32, before: &'static [usize]) -> Spec {
    Spec { domain: Some(domain), goes_on: false, len: 64, flags: FULL, before }
}

const fn begun(domain: u32, before: &'static [usize]) -> Spec {
    Spec { domain: Some(domain), goes_on: false, len: 64, flags: BEGUN, before }
}

const fn ended(len: u32, before: &'static [usize]) -> Spec {
    Spec { domain: None, goes_on: true, len, flags: ENDED, before }
}

const fn idle(before: &'static [usize]) -> Spec {
    Spec { domain: None, goes_on: false, len: 64, flags: FULL, before }
}

const SPECS: [Spec; KINDS] = [
    idle(&[]),
    spec(DOM_BODY, &[START, HEAD, ISP, OSP, OPSP, OPABS, OPSGN, WEND2, PAD]),
    spec(DOM_PUBKEY, &[START, HEAD, ISP]),
    begun(DOM_SIGNED, &[KEY, UKEY, PKEY]),
    ended(48, &[ENT1]),
    spec(DOM_SIGNED_NODE, &[ENT2, ENT2U, ENT2P, ENT2R, SN]),
    spec(DOM_COMMITMENT, &[SN]),
    spec(DOM_BODY_IN, &[COMMIT, PCOMMIT]),
    spec(DOM_STATE_LEAF, &[BODYIN]),
    spec(DOM_STATE_NODE, &[LEAF, NEW, RLEAF, SLEAF, PSLEAF]),
    spec(DOM_STATE_NODE, &[OLD]),
    spec(DOM_INPUTS, &[NEW]),
    spec(DOM_COMMITMENT, &BETWEEN),
    spec(DOM_STATE_LEAF, &[OUTC]),
    spec(DOM_OUT_ITEM, &[OLEAF]),
    spec(DOM_BODY_OUT, &[OITEM]),
    spec(DOM_OUTPUTS, &[PUSH]),
    idle(&[START, HEAD, ISP, OSP, OPSP, OPABS, OPSGN, WEND2, PAD]),
    spec(DOM_OP, &BETWEEN),
    spec(DOM_STATE_LEAF, &[OPC]),
    spec(DOM_OPS, &[OPBODY]),
    spec(DOM_OPS, &[PUSH]),
    begun(DOM_RECORD, &BETWEEN),
    ended(64, &[REC1]),
    begun(DOM_COMMIT, &[REC2]),
    ended(32, &[COM1]),
    spec(DOM_STATE_LEAF, &[COM2]),
    spec(DOM_NAME_LEAF, &[ISP]),
    spec(DOM_NAME_NODE, &[NLEAFR, NLEAFN, NNEW]),
    spec(DOM_NAME_NODE, &[NOLD]),
    idle(&[NNEW]),
    spec(DOM_OP, &[NEND]),
    spec(DOM_BODY_OP, &BETWEEN),
    spec(DOM_OPS, &[OPX]),
    Spec { domain: Some(DOM_UPDATE), goes_on: false, len: 32, flags: FULL, before: &[REC2] },
    spec(DOM_PUBKEY, &[UMSG]),
    ended(48, &[ENT1]),
    begun(DOM_RECORD, &[SN]),
    ended(64, &[OREC1]),
    spec(DOM_NAME_LEAF, &[OREC2]),
    spec(DOM_NAME_LEAF, &[NLEAFO]),
    spec(DOM_STATE_LEAF, &[START, ISP, OSP, OPSP, OPABS, OPSGN, WEND2, PAD]),
    idle(&[START, HEAD, ISP]),
    idle(&[PSTART, PLEAF]),
    spec(DOM_PUBKEY, &[TSTART, RMSG2, PSIG, PSKIP]),
    ended(48, &[ENT1]),
    spec(DOM_SIGNERS, &[SN]),
    spec(DOM_SIGNERS, &[TSTART, RMSG2, PSIG, PSKIP]),
    spec(DOM_COND, &[TSTART, PSIG, PSKIP]),
    spec(DOM_HASHLOCK, &[PSTART, PLEAF]),
    spec(DOM_COND, &[CHASHP]),
    spec(DOM_COND, &[PSTART, PLEAF]),
    spec(DOM_COND, &[PSTART, PLEAF]),
    spec(DOM_POLICY_LEAF, &[CTHRESH, CHASH, CAFTER, COLDER, COUTS, CSTATE, CREBIND]),
    spec(DOM_POLICY_NODE, &[PLEAF, PNODE]),
    spec(DOM_COMMITMENT, &[PNODE]),
    spec(DOM_STATE_LEAF, &[BODYIN]),
    spec(DOM_COVERED, &[BODYOUT]),
    spec(DOM_COND, &[PSTART, PLEAF]),
    spec(DOM_COND, &[PSTART, PLEAF]),
    begun(DOM_REBIND, &[PSTART, PLEAF]),
    ended(4, &[RSTART]),
    ended(48, &[ENT1]),
    spec(DOM_COND, &[RMSG2, PSIG, PSKIP]),
    spec(DOM_STACK, &[BODYOUT, COVR, CLEAF, MRG]),
    spec(DOM_STATE_NODE, &[POP]),
    spec(DOM_STACK, &[BODYOUT, COVR, CLEAF, MRG]),
    idle(&BETWEEN),
    spec(DOM_STACK, &[SETL, WEMP, WEND1]),
    spec(DOM_STATE_NODE, &[WPOP]),
    spec(DOM_STATE_NODE, &[SETL, WEMP, WEND1]),
    spec(DOM_STATE_NODE, &[WNODEL, WNODER]),
    idle(&[WEMP]),
    idle(&[WEMP]),
];

/// The kinds a run may end with: between items.
const ENDS: [usize; 9] = [START, HEAD, ISP, OSP, OPSP, OPABS, OPSGN, WEND2, PAD];

/// The flows a register tells apart: a payment's input, a reveal, an
/// update (a reveal's and an update's are their operations' tags).
const PAYING: u32 = 1;
const REVEALING: u32 = 2;
const UPDATING: u32 = 3;
const POLICY: u32 = 4;
const COMMITTING: u32 = 5;
const MAKING: u32 = 6;

/// Which kind counts against which cap, and the cap.
const CAPS: [(usize, usize); 4] = [(OPC, MAX_COMMITS), (COM1, MAX_REVEALS), (UKEY, MAX_UPDATES), (SLEAF, MAX_SWEEPS)];

/// Words a row takes as inputs.
pub const INPUTS: usize = FRONT + 1 + KINDS + STATE + 1 + AUX;
/// Words of the registers.
const STATE: usize = 202;
/// Public elements: what a run is joined to the next by, as its first
/// row has it ([`CHAINED`] elements), what does not change ([`FIXED`]:
/// the signed set's root, the height before the block's), and the
/// chained again as its last row leaves them.
pub const CHAINED: usize = 27;
pub const FIXED: usize = 3;
pub const PUBLIC: usize = 4 * (2 * CHAINED + FIXED);
/// Words of program a row reads (two of them are used).
pub const PROGRAM: usize = 64;

/// The registers, as words in a row.
#[derive(Clone)]
struct Registers<V> {
    root: [V; 8],
    isp: [V; 8],
    osp: [V; 8],
    signed: [V; 8],
    id: [V; 8],
    body: [V; 8],
    /// Inputs left, things to make left, the height.
    counts: [V; 3],
    /// The height before the block's: one less.
    before: V,
    next: [V; 2],
    sum_in: [V; 4],
    sum_out: [V; 4],
    hold: [V; 8],
    amount: [V; 2],
    pos: [V; 2],
    pos0: [V; 2],
    cnt: V,
    w: [V; 8],
    v: [V; 8],
    /// All ones while a removal's walk is in hand, none for an
    /// insertion's.
    input: V,
    /// The registry's root; a name's hash, its owner and its record's
    /// hash; the name's place as it is walked.
    names: [V; 8],
    name: [V; 8],
    owner: [V; 8],
    record: [V; 8],
    place: [V; 4],
    flow: V,
    /// Commits, reveals, updates and sweeps so far: a bit a word.
    caps: [V; 4],
    /// A threshold's signers and keys so far; and the height a policy's
    /// output is said to have been made at, until its leaf says so.
    counted: [V; 2],
    made: V,
    /// The hash a transaction says its covered outputs have, the hash
    /// of those met so far, and how many are still to come.
    cover: [V; 8],
    covered: [V; 8],
    take: V,
    /// A policy spend's state; what a channel's keys sign; and all ones
    /// while a threshold in hand is a channel's.
    state: V,
    rebind: [V; 8],
    rebinding: V,
    /// The running hashes of the operations on names the transactions
    /// carry, and of those done; and all ones once operations are being
    /// done, and once commitments are being swept.
    sgn: [V; 8],
    app: [V; 8],
    phase: [V; 2],
    /// The outputs' tree's nodes still to be joined, as a chain of
    /// hashes, the lowest last; the chain as the run began with it; the
    /// position that was next then; and how far the run's outputs are
    /// from being in the root (0: not begun; all ones: they are).
    stk: [V; 8],
    stk0: [V; 8],
    next0: [V; 2],
    stage: V,
}

/// A row against any [`Ctx`].
struct Row<V> {
    cv: [V; 8],
    m: [V; 16],
    len: V,
    bflags: V,
    out: [V; 8],
    kind: [V; KIND_WORDS],
    flags: [V; KINDS],
    dom: V,
    r: Registers<V>,
    dir: V,
    /// What the rest is: carries and the like, in the order the circuit
    /// reads them.
    aux: Vec<V>,
    first: V,
    last: V,
    public: Vec<V>,
}

/// Auxiliary words a row has.
const AUX: usize = 67;

fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
    let cv: [C::V; 8] = std::array::from_fn(|_| c.input());
    let m: [C::V; 16] = std::array::from_fn(|_| c.input());
    let (len, bflags) = (c.input(), c.input());
    let zero = c.constant(0);
    let hash = compress(c, cv.clone(), m.clone(), [zero.clone(), zero, len.clone(), bflags.clone()]);
    let kind = std::array::from_fn(|_| c.input());
    let flags = std::array::from_fn(|_| c.input());
    let dom = c.input();
    let mut words = |n: usize| -> Vec<C::V> { (0..n).map(|_| c.input()).collect() };
    macro_rules! group {
        ($n:expr) => {
            words($n).try_into().ok().unwrap()
        };
    }
    let r = Registers {
        root: group!(8),
        isp: group!(8),
        osp: group!(8),
        signed: group!(8),
        id: group!(8),
        body: group!(8),
        counts: group!(3),
        before: words(1).remove(0),
        next: group!(2),
        sum_in: group!(4),
        sum_out: group!(4),
        hold: group!(8),
        amount: group!(2),
        pos: group!(2),
        pos0: group!(2),
        cnt: words(1).remove(0),
        w: group!(8),
        v: group!(8),
        input: words(1).remove(0),
        names: group!(8),
        name: group!(8),
        owner: group!(8),
        record: group!(8),
        place: group!(4),
        flow: words(1).remove(0),
        caps: group!(4),
        counted: group!(2),
        made: words(1).remove(0),
        cover: group!(8),
        covered: group!(8),
        take: words(1).remove(0),
        state: words(1).remove(0),
        rebind: group!(8),
        rebinding: words(1).remove(0),
        sgn: group!(8),
        app: group!(8),
        phase: group!(2),
        stk: group!(8),
        stk0: group!(8),
        next0: group!(2),
        stage: words(1).remove(0),
    };
    let dir = c.input();
    let aux = (0..AUX).map(|_| c.input()).collect();
    let (first, last) = (c.program(), c.program());
    for _ in 2..PROGRAM {
        c.program();
    }
    let public = (0..PUBLIC).map(|_| c.public()).collect();
    Row { cv, m, len, bflags, out: hash.out, kind, flags, dom, r, dir, aux, first, last, public }
}

/// The row a [`crate::circuit::Concrete`] runs.
pub fn run<C: Ctx>(c: &mut C) {
    row(c);
}

fn ones() -> Expr {
    Expr::constant(!0)
}

fn turned(x: &Expr, by: u8) -> Expr {
    let mut t = x.clone();
    t.terms[0].rot = by;
    t
}

fn shifted_left(x: &Expr) -> Expr {
    Expr { terms: vec![Term { pre: Pre::Shl, ..x.terms[0] }], constant: 0 }
}

/// A full adder of 32 bits written out: `carry` is the word of the
/// carries out of each place, `carry_in` a word that is zero or one.
/// The sum.
fn adder(s: &mut Symbolic, x: &Expr, y: &Expr, carry_in: Option<&Expr>, carry: &Expr) -> Expr {
    let mut into = shifted_left(carry);
    if let Some(bit) = carry_in {
        into = into.xor(bit);
    }
    s.constrain(x.xor(&into), y.xor(&into), carry.xor(&into));
    x.xor(y).xor(&into)
}

pub fn circuit() -> Circuit {
    Circuit::new(
        |s: &mut Symbolic| {
            let row = row(s);
            let core = s.constraints.len();
            let Row { cv, m, len, bflags, out, kind, flags, dom, r, dir, aux, first, last: last_row, public } = &row;
            let f = |k: usize| flags[k].clone();
            let any = |ks: &[usize]| ks.iter().fold(Expr::constant(0), |x, k| x.xor(&flags[*k]));
            let con = Expr::constant;
            let mut aux = aux.iter();
            let mut next_aux = || aux.next().expect("an auxiliary word").clone();
            let p = |x: &Expr| x.prev();
            let top = |s: &mut Symbolic, carry: &Expr, bit: Expr| {
                s.constrain(turned(carry, 31), con(1), bit.clone());
                bit
            };

            // The kind: one bit among its words, and each flag that bit
            // in every place.
            for (i, word) in kind.iter().enumerate() {
                let less = adder(s, word, &ones(), None, &next_aux());
                s.constrain(word.clone(), less, con(0));
                let used = (KINDS - 32 * i).min(32);
                if used < 32 {
                    s.constrain(word.clone(), con(!((1 << used) - 1)), con(0));
                }
            }
            for (k, flag) in flags.iter().enumerate() {
                s.zero_where(&con(1 << (k % 32)), flag.xor(&kind[k / 32]));
                s.zero_where(&ones(), flag.xor(&turned(flag, 1)));
            }
            s.zero_where(&con(1), any(&(0..KINDS).collect::<Vec<_>>()).xor(&con(1)));
            // (A word has one bit at most and the flags are odd in
            // number, which three are: no two words have a bit. A row
            // of three kinds would be held to no rule two of them
            // share.)
            let within = |i: usize| any(&(32 * i..KINDS.min(32 * (i + 1))).collect::<Vec<_>>());
            for i in 0..KIND_WORDS {
                for j in i + 1..KIND_WORDS {
                    s.constrain(within(i), within(j), con(0));
                }
            }
            // Which kind follows which; where a run starts and ends.
            for (k, spec) in SPECS.iter().enumerate().skip(1) {
                let allowed = spec.before.iter().fold(ones(), |x, j| x.xor(&flags[*j].prev()));
                s.zero_where(&f(k), allowed);
            }
            s.zero_where(first, f(START).xor(&ones()));
            s.zero_where(&f(START), first.xor(&ones()));
            s.zero_where(last_row, any(&ENDS).xor(&ones()));

            // The compression: from a domain's key, or going on; the
            // block's length and the flags.
            let of = |pick: &dyn Fn(&Spec) -> bool| (0..KINDS).filter(|k| pick(&SPECS[*k])).collect::<Vec<usize>>();
            let going_on = any(&of(&|s| s.goes_on));
            // (An input is taken into the id under the place of the
            // output it spends, which is in the key beside the domain:
            // the two words after it, there and nowhere else. The leaf
            // that follows is walked from that place.)
            let placed = going_on.xor(&ones()).xor(&f(BODYIN));
            for i in 0..8 {
                let key = if i == 0 { dom.clone() } else { con(0) };
                let free = if i == 1 || i == 2 { &placed } else { &going_on.xor(&ones()) };
                s.zero_where(free, cv[i].xor(&key));
                s.zero_where(&going_on, cv[i].xor(&out[i].prev()));
            }
            for (k, spec) in SPECS.iter().enumerate() {
                if let Some(d) = spec.domain {
                    s.zero_where(&f(k), dom.xor(&con(d)));
                }
            }
            for l in [64, 48, 32, 4] {
                s.zero_where(&any(&of(&|s| s.len == l)), len.xor(&con(l)));
            }
            for fl in [FULL, BEGUN, ENDED] {
                s.zero_where(&any(&of(&|s| s.flags == fl)), bflags.xor(&con(fl)));
            }

            // The arithmetic, each always done and used where a kind says.
            let less_in = adder(s, &p(&r.counts[0]), &ones(), None, &next_aux());
            let less_out = adder(s, &p(&r.counts[1]), &ones(), None, &next_aux());
            let more = adder(s, &p(&r.cnt), &con(1), None, &next_aux());
            let (c0, b0, c1) = (next_aux(), next_aux(), next_aux());
            let next_low = adder(s, &p(&r.next[0]), &con(1), None, &c0);
            let b0 = top(s, &c0, b0);
            let next_high = adder(s, &p(&r.next[1]), &con(0), Some(&b0), &c1);
            let mut sum = |s: &mut Symbolic, of: &[Expr; 4]| -> Vec<Expr> {
                let mut carry_in: Option<Expr> = None;
                let mut words = Vec::new();
                for (i, word) in of.iter().enumerate() {
                    let add = if i < 2 { r.amount[i].clone() } else { con(0) };
                    let (carry, bit) = (next_aux(), next_aux());
                    words.push(adder(s, &p(word), &add, carry_in.as_ref(), &carry));
                    carry_in = Some(top(s, &carry, bit));
                }
                words
            };
            let (sum_in, sum_out) = (sum(s, &r.sum_in), sum(s, &r.sum_out));
            // The height before: one less than the block's, in every row.
            let below = adder(s, &r.counts[2], &ones(), None, &next_aux());
            s.zero_where(&ones(), r.before.xor(&below));
            // How long ago a leaf was made, where the block's last word is
            // the height it was made at: the height less it (which
            // carries if it is not in the future), that less one, and
            // the longest a commitment may wait less that.
            let mut less = |s: &mut Symbolic, x: &Expr, y: &Expr| {
                let (carry, bit) = (next_aux(), next_aux());
                let difference = adder(s, x, &y.xor(&ones()), Some(&con(1)), &carry);
                (difference, top(s, &carry, bit))
            };
            let (age, not_future) = less(s, &r.counts[2], &m[15]);
            let (_, not_now) = less(s, &age, &con(1));
            let (_, in_time) = less(s, &con(MAX_REVEAL), &age);
            for bit in [&not_future, &not_now, &in_time] {
                s.zero_where(&f(RLEAF), bit.xor(&con(1)));
            }
            s.zero_where(&f(SLEAF), not_future.xor(&con(1)));
            s.zero_where(&f(SLEAF), in_time);
            // A position shifted right by a place, across its words: the
            // outputs', and a name's.
            let mut across = |s: &mut Symbolic, words: &[Expr]| -> Vec<Expr> {
                let mut out = Vec::new();
                for (i, w) in words.iter().enumerate() {
                    let mut shifted = p(w).shr();
                    if let Some(above) = words.get(i + 1) {
                        let bit = next_aux();
                        s.constrain(turned(&p(above), 1), con(1 << 31), bit.clone());
                        shifted = shifted.xor(&bit);
                    }
                    out.push(shifted);
                }
                out
            };
            let (shifted, placed) = (across(s, &r.pos), across(s, &r.place));

            // Walks: which way, and the pair a row hashes.
            s.zero_where(&ones(), dir.xor(&turned(dir, 1)));
            for (kinds, from) in [(&[SN, OLD, PNODE][..], &r.pos[0]), (&[NOLD][..], &r.place[0])] {
                let low = next_aux();
                s.constrain(any(kinds), con(1), low.clone());
                s.zero_where(&low, dir.xor(&p(from)));
            }
            s.zero_where(&any(&[NEW, NNEW]), dir.xor(&p(dir)));
            let mut sides = |s: &mut Symbolic, ks: &[usize]| {
                let (left, right) = (next_aux(), next_aux());
                s.constrain(any(ks), dir.xor(&ones()), left.clone());
                s.constrain(any(ks), dir.clone(), right.clone());
                (left, right)
            };
            // Up the signed set from the last output; up either tree from
            // the old walk's node, or the new walk's.
            let (sn, old, new) = (sides(s, &[SN, PNODE]), sides(s, &[OLD, NOLD]), sides(s, &[NEW, NNEW]));
            for i in 0..8 {
                for ((left, right), child) in [(&sn, p(&out[i])), (&old, p(&r.w[i])), (&new, p(&r.v[i]))] {
                    s.zero_where(left, m[i].xor(&child));
                    s.zero_where(right, m[8 + i].xor(&child));
                }
                // The new walk's sibling is the old walk's.
                s.zero_where(&new.0, m[8 + i].xor(&p(&m[8 + i])));
                s.zero_where(&new.1, m[i].xor(&p(&m[i])));
            }

            // What each kind's block is. A rule that several kinds share
            // is one constraint under their flags together.
            let same = |s: &mut Symbolic, ks: &[usize], words: &[Expr], as_: &[Expr]| {
                let mask = ks.iter().fold(con(0), |x, k| x.xor(&flags[*k]));
                for (w, x) in words.iter().zip(as_) {
                    s.zero_where(&mask, w.xor(x));
                }
            };
            let before = |words: &[Expr]| words.iter().map(|w| w.prev()).collect::<Vec<Expr>>();
            // The block's words that are zero, by word: the words from
            // some place on, for each kind that has any.
            let zeros: &[(usize, std::ops::Range<usize>)] = &[
                (HEAD, 3..16),
                (KEY, 13..16),
                (UKEY, 13..16),
                (ENT2, 12..16),
                (ENT2U, 12..16),
                (COMMIT, 10..16),
                (ISP, 10..16),
                (OUTC, 10..16),
                (OITEM, 15..16),
                (OPC, 14..16),
                (CLEAF, 13..15),
                (COM2, 8..16),
                (RLEAF, 13..15),
                (SLEAF, 13..15),
                (OPX, 9..16),
                (UMSG, 8..16),
                (PKEY, 13..16),
                (ENT2P, 12..16),
                (CTHRESH, 3..4),
                (CTHRESH, 12..16),
                (CHASHP, 8..16),
                (CHASH, 1..4),
                (CHASH, 12..16),
                (CAFTER, 1..15),
                (COLDER, 1..15),
                (PCOMMIT, 10..16),
                (COUTS, 2..4),
                (COUTS, 12..16),
                (CSTATE, 1..15),
                (RMSG2, 1..16),
                (ENT2R, 9..16),
                (CREBIND, 3..4),
                (CREBIND, 12..16),
            ];
            for (i, word) in m.iter().enumerate() {
                let kinds: Vec<usize> = zeros.iter().filter(|(_, at)| at.contains(&i)).map(|(k, _)| *k).collect();
                if !kinds.is_empty() {
                    s.zero_where(&any(&kinds), word.clone());
                }
            }
            same(s, &[ENT1], &m[..], &before(&m[..]));
            same(s, &[ENT2, ENT2P], &m[..8], &r.id);
            same(s, &[ENT2U], &m[..8], &r.w);
            same(s, &[COMMIT], &m[..8], &before(&r.hold));
            same(s, &[BODYIN, BODYOUT, OPBODY], &m[..8], &before(&r.body));
            same(s, &[BODYIN, BODYOUT, PLEAF], &m[8..], &before(&out[..]));
            same(s, &[OPSGN, OPSP, OSP, OPABS, COVR], &m[8..], &r.hold);
            same(s, &[LEAF, PSLEAF], &m[..8], &r.hold);
            same(s, &[LEAF, PSLEAF, OLEAF], &m[13..15], &r.amount);
            same(s, &[ISP], &m[..8], &before(&r.isp));
            same(s, &[ISP], &m[8..10], &r.pos0);
            // (The leaf walked is at the place the id took the input
            // in under: the row before a spent leaf is that one.)
            same(s, &[LEAF, PSLEAF], &r.pos, &[p(&cv[1]), p(&cv[2])]);
            same(s, &[OLEAF, RLEAF, PCOMMIT], &m[..8], &before(&out[..]));
            same(s, &[OLEAF, CLEAF], &m[15..], &r.counts[2..]);
            same(s, &[OITEM], &m[..15], &before(&m[..15]));
            same(s, &[OSP], &m[..8], &before(&r.osp));
            same(s, &[OPSGN], &m[..8], &before(&r.sgn));
            same(s, &[OPSP, OPABS], &m[..8], &before(&r.app));
            // An operation's hash: its tag, then the commitment with its
            // memo, or the record's hash.
            same(s, &[OPC], &m[..1], &[con(1)]);
            same(s, &[OPX], &m[..1], std::slice::from_ref(&r.flow));
            same(s, &[OPX], &m[1..9], &r.record);
            same(s, &[CLEAF], &m[..13], &before(&m[1..14]));
            same(s, &[COM1, OREC1, NLEAFR, NLEAFO, NLEAFN], &m[..8], &r.name);
            same(s, &[COM2], &m[..8], &r.owner);
            same(s, &[NLEAFR, NLEAFN], &m[8..], &r.record);
            same(s, &[UMSG], &m[..8], &r.record);
            same(s, &[OREC1, PSIG], &m[8..], &r.hold);
            // A policy: the keys' chain, the conditions, the leaf's chain.
            same(s, &[PSIG, PSKIP], &m[..8], &before(&r.v));
            same(s, &[CTHRESH], &m[..1], &[con(1)]);
            same(s, &[CREBIND], &m[..1], &[con(7)]);
            same(s, &[CTHRESH, CREBIND], &m[1..3], &[p(&r.counted[0]), p(&r.counted[1])]);
            same(s, &[CTHRESH, CREBIND], &m[4..12], &before(&r.v));
            // A covenant, a state, and what a channel's keys sign.
            same(s, &[COVR], &m[..8], &before(&r.covered));
            same(s, &[COUTS], &m[..2], &[con(6), r.take.clone()]);
            same(s, &[COUTS], &m[4..12], &r.cover);
            same(s, &[CSTATE], &m[..1], &[con(5)]);
            same(s, &[RSTART], &m[8..], &r.cover);
            same(s, &[RMSG2], &m[..1], std::slice::from_ref(&r.state));
            same(s, &[ENT2R], &m[..8], &r.rebind);
            same(s, &[ENT2R], &m[8..9], std::slice::from_ref(&r.state));
            same(s, &[ENT2P, CTHRESH], std::slice::from_ref(&r.rebinding), &[con(0)]);
            same(s, &[ENT2R, CREBIND], std::slice::from_ref(&r.rebinding), &[ones()]);
            same(s, &[CHASH], &m[..1], &[con(2)]);
            same(s, &[CHASH], &m[4..12], &before(&out[..]));
            same(s, &[CAFTER], &m[..1], &[con(3)]);
            same(s, &[COLDER], &m[..1], &[con(4)]);
            same(s, &[PLEAF], &m[..8], &before(&r.w));
            same(s, &[PSLEAF], &m[15..], std::slice::from_ref(&r.made));
            same(s, &[NLEAFO], &m[8..], &before(&out[..]));

            // What each kind asks of what came before.
            same(s, &[HEAD, SLEAF, OPC, REC1], &before(&r.counts[..2]), &[con(0), con(0)]);
            same(s, &[HEAD, SLEAF, OPC, REC1], &before(&r.body), &before(&r.id));
            // (And none of the outputs its conditions are on still to
            // come: a transaction that said two and made one is not
            // ended by the next one's beginning.)
            same(s, &[HEAD, SLEAF, OPC, REC1], &[p(&r.take)], &[con(0)]);
            // Transactions, then the operations on names they carried,
            // then sweeps.
            same(s, &[HEAD], &[p(&r.phase[0])], &[con(0)]);
            same(s, &[OPC, REC1], &[p(&r.phase[1])], &[con(0)]);
            same(s, &[COMMIT, OREC1, PSIG], &[p(&r.cnt)], &[con(signed::DEPTH as u32)]);
            same(s, &[COMMIT, OREC1, PSIG], &before(&out[..]), &before(&r.signed));
            same(s, &[PCOMMIT], &[p(&r.cnt)], &[con(crate::conditions::DEPTH as u32)]);
            s.zero_where(&f(CAFTER), not_future.xor(&con(1)));
            same(s, &[OUTC], &[p(&r.counts[0])], &[con(0)]);
            same(s, &[ISP, WEND1, WEND2], &[p(&r.cnt)], &[con(OUTPUTS_HEIGHT as u32)]);
            same(s, &[ISP, WEND1, WEND2], &before(&r.pos), &[con(0), con(0)]);
            same(s, &[ISP], &before(&r.w), &before(&r.root));
            same(s, &[ISP], &[p(&r.input)], &[ones()]);
            same(s, &[NEND], &[p(&r.cnt)], &[con(registry::HEIGHT as u32)]);
            same(s, &[NEND], &before(&r.w), &before(&r.names));
            // The flow a row is of.
            same(s, &[ENT2, COMMIT, LEAF], std::slice::from_ref(&r.flow), &[con(PAYING)]);
            same(s, &[OSP], std::slice::from_ref(&r.flow), &[con(MAKING)]);
            same(s, &[OPSP], std::slice::from_ref(&r.flow), &[con(COMMITTING)]);
            same(s, &[ENT2P, ENT2R, PSIG, PLEAF, PSLEAF], std::slice::from_ref(&r.flow), &[con(POLICY)]);
            same(s, &[NLEAFR], std::slice::from_ref(&r.flow), &[con(REVEALING)]);
            same(s, &[ENT2U, OREC1], std::slice::from_ref(&r.flow), &[con(UPDATING)]);
            // The caps: a kind that counts is refused once its bit is at
            // the cap.
            for (i, (k, cap)) in CAPS.iter().enumerate() {
                let had = next_aux();
                s.constrain(p(&r.caps[i]), f(*k), had.clone());
                s.zero_where(&con(1 << cap), had);
            }

            // The registers: held, but where a kind sets them; kinds that
            // set one alike share the constraint.
            let register = |s: &mut Symbolic, words: &[Expr], set: &[(&[usize], Option<Vec<Expr>>)]| {
                let held =
                    set.iter().flat_map(|(ks, _)| ks.iter()).fold(f(START).xor(&ones()), |x, k| x.xor(&flags[*k]));
                for (i, w) in words.iter().enumerate() {
                    s.zero_where(&held, w.xor(&w.prev()));
                    for (ks, to) in set {
                        if let Some(to) = to {
                            s.zero_where(&any(ks), w.xor(&to[i]));
                        }
                    }
                }
            };
            let to = |words: &[Expr]| Some(words.to_vec());
            let nothing = |n: usize| Some(vec![con(0); n]);
            let one = std::slice::from_ref;
            register(s, &r.root, &[(&[ISP, WEND2], to(&before(&r.v)))]);
            register(s, &r.isp, &[(&[ISP], to(&out[..]))]);
            register(s, &r.osp, &[(&[OSP], to(&out[..]))]);
            register(s, &r.sgn, &[(&[OPSGN], to(&out[..]))]);
            register(s, &r.app, &[(&[OPSP, OPABS], to(&out[..]))]);
            register(s, &r.phase[..1], &[(&[OPC, REC1, SLEAF], to(&[ones()]))]);
            register(s, &r.phase[1..], &[(&[SLEAF], to(&[ones()]))]);
            register(s, &r.signed, &[]);
            register(s, &r.id, &[(&[HEAD], None)]);
            register(s, &r.body, &[(&[HEAD, BODYIN, BODYOUT, OPBODY], to(&out[..]))]);
            register(s, &r.counts[..1], &[(&[HEAD], to(&m[..1])), (&[BODYIN], to(&[less_in]))]);
            register(s, &r.counts[1..2], &[(&[HEAD], to(&m[1..2])), (&[BODYOUT, OPBODY], to(&[less_out]))]);
            register(s, &r.counts[2..], &[]);
            register(s, &r.next, &[(&[OSP, OPSP], to(&[next_low, next_high]))]);
            register(s, &r.sum_in, &[(&[ISP], to(&sum_in))]);
            register(s, &r.sum_out, &[(&[OSP, OPSP], to(&sum_out))]);
            register(
                s,
                &r.hold,
                &[(&[KEY, UKEY, PKEY, COMMIT, PCOMMIT, OITEM, OPC, OPX], to(&out[..])), (&[OPBODY], to(&m[8..]))],
            );
            register(s, &r.amount, &[(&[COMMIT, OUTC, PCOMMIT], to(&m[8..10])), (&[CLEAF, RLEAF, SLEAF], nothing(2))]);
            let leaves = [
                (&[ENT2, ENT2U, ENT2P, ENT2R, PLEAF, LEAF, PSLEAF, RLEAF, SLEAF][..], None),
                (&[SN, PNODE, NEW, MRG, WNODEL, WNODER][..], to(&shifted)),
                (&[OLEAF, CLEAF, WEND1][..], to(&before(&r.next))),
                (&[SETL][..], to(&before(&r.next0))),
            ];
            register(s, &r.pos, &leaves);
            register(s, &r.pos0, &[(&[LEAF, PSLEAF, RLEAF, SLEAF], to(&r.pos))]);
            let begun = [
                ENT2, ENT2U, ENT2P, ENT2R, PLEAF, LEAF, PSLEAF, OLEAF, CLEAF, RLEAF, SLEAF, NLEAFR, NLEAFN, SETL, WEND1,
            ];
            let counted = [SN, PNODE, NEW, NNEW, WNODEL, WNODER];
            register(s, one(&r.cnt), &[(&begun, to(&[con(0)])), (&counted, to(&[more]))]);
            register(
                s,
                &r.w,
                &[
                    (&[LEAF, PSLEAF, PLEAF, OLD, NOLD, RLEAF, SLEAF, UMSG, NLEAFO, WEMP], to(&out[..])),
                    (&[OLEAF, CLEAF, NLEAFR, PSTART, SETL, WEND1], nothing(8)),
                ],
            );
            register(
                s,
                &r.v,
                &[
                    (&[LEAF, PSLEAF, RLEAF, SLEAF, TSTART, SETL, WEND1], nothing(8)),
                    (&[NEW, NNEW, OLEAF, CLEAF, NLEAFR, NLEAFN, PSIG, PSKIP, MRG, WNODEL, WNODER], to(&out[..])),
                    (&[RSTART], to(&m[..8])),
                ],
            );
            register(
                s,
                one(&r.input),
                &[(&[LEAF, PSLEAF, RLEAF, SLEAF], to(&[ones()])), (&[OLEAF, CLEAF], to(&[con(0)]))],
            );
            register(s, &r.names, &[(&[NEND], to(&before(&r.v)))]);
            register(s, &r.name, &[(&[REC1], to(&m[..8]))]);
            register(s, &r.owner, &[(&[REC1], to(&m[8..]))]);
            register(s, &r.record, &[(&[REC2], to(&out[..]))]);
            register(s, &r.place, &[(&[NLEAFR, NLEAFN], to(&r.name[..4])), (&[NNEW], to(&placed))]);
            let flows = [
                (&[KEY][..], PAYING),
                (&[COM1][..], REVEALING),
                (&[UKEY][..], UPDATING),
                (&[SLEAF][..], 0),
                (&[PSTART][..], POLICY),
                (&[OPC][..], COMMITTING),
                (&[OUTC][..], MAKING),
            ];
            register(s, one(&r.flow), &flows.map(|(ks, flow)| (ks, to(&[con(flow)]))));
            for (i, (k, _)) in CAPS.iter().enumerate() {
                register(s, one(&r.caps[i]), &[(&[*k], to(&[shifted_left(&p(&r.caps[i]))]))]);
            }
            // A threshold's counts; and how old a policy's output is,
            // against what a condition asks.
            let signers = adder(s, &p(&r.counted[0]), &con(1), None, &next_aux());
            let keys = adder(s, &p(&r.counted[1]), &con(1), None, &next_aux());
            register(s, one(&r.counted[0]), &[(&[TSTART, RSTART], to(&[con(0)])), (&[PSIG], to(&[signers]))]);
            register(s, one(&r.counted[1]), &[(&[TSTART, RSTART], to(&[con(0)])), (&[PSIG, PSKIP], to(&[keys]))]);
            register(s, one(&r.made), &[(&[PSTART], None)]);
            let mut less = |s: &mut Symbolic, x: &Expr, y: &Expr| {
                let (carry, bit) = (next_aux(), next_aux());
                let difference = adder(s, x, &y.xor(&ones()), Some(&con(1)), &carry);
                (difference, top(s, &carry, bit))
            };
            let (old, not_after) = less(s, &r.counts[2], &r.made);
            let (_, old_enough) = less(s, &old, &m[15]);
            for bit in [&not_after, &old_enough] {
                s.zero_where(&f(COLDER), bit.xor(&con(1)));
            }
            // The covered outputs. A transaction says at its head how many
            // of its outputs conditions are on, and what they hash to;
            // each of those outputs is then taken into a hash of its own
            // before it is walked into the state, and when the last is
            // in, the hash is what was said. The three are a run's from the
            // one before, as the transaction in hand is: a run may end
            // while outputs conditions are on are still to come.
            let (carry, bit) = (next_aux(), next_aux());
            let fewer = adder(s, &p(&r.take), &ones(), None, &carry);
            let some_left = top(s, &carry, bit);
            let (carry, bit) = (next_aux(), next_aux());
            adder(s, &fewer, &ones(), None, &carry);
            let more_left = top(s, &carry, bit);
            let (last, ending, skipped) = (next_aux(), next_aux(), next_aux());
            s.zero_where(&ones(), last.xor(&turned(&last, 1)));
            s.zero_where(&con(1), last.xor(&more_left).xor(&con(1)));
            s.constrain(f(COVR), last, ending.clone());
            for (word, said) in out.iter().zip(&r.cover) {
                s.zero_where(&ending, word.xor(said));
            }
            s.zero_where(&any(&[COVR, COUTS, RSTART]), some_left.xor(&con(1)));
            s.constrain(any(&[POP, PUSH]), p(&f(BODYOUT)), skipped.clone());
            s.zero_where(&skipped, r.take.clone());
            register(s, &r.cover, &[(&[HEAD], None)]);
            register(s, &r.covered, &[(&[HEAD], nothing(8)), (&[COVR], to(&out[..]))]);
            register(s, one(&r.take), &[(&[HEAD], to(&m[2..3])), (&[COVR], to(&[fewer]))]);
            // A spend's state, above what a condition asks; what a
            // channel's keys sign.
            register(s, one(&r.state), &[(&[PSTART], None)]);
            let (carry, bit) = (next_aux(), next_aux());
            adder(s, &r.state, &m[15].xor(&ones()), None, &carry);
            let above = top(s, &carry, bit);
            s.zero_where(&f(CSTATE), above.xor(&con(1)));
            register(s, &r.rebind, &[(&[RMSG2], to(&out[..]))]);
            register(s, one(&r.rebinding), &[(&[RSTART], to(&[ones()])), (&[TSTART], to(&[con(0)]))]);

            // The outputs a run makes. The tree's nodes to the left of
            // the next position's path are held as a chain of hashes, the
            // lowest last. A leaf is joined with the node at each level
            // its position has a bit at, and what that leaves is held
            // in its turn: a row or three a leaf, where a path of its own
            // would be two rows a level.
            let zeros8 = vec![con(0); 8];
            same(s, &[POP], &out[..], &before(&r.stk));
            same(s, &[WPOP], &out[..], &before(&r.stk0));
            same(s, &[MRG, WNODEL], &m[..8], &before(&m[8..]));
            same(s, &[MRG, WNODEL, PUSH], &m[8..], &before(&r.v));
            same(s, &[PUSH], &m[..8], &before(&r.stk));
            same(s, &[WNODER], &m[..8], &before(&r.v));
            same(s, &[WNODER, WEMP], &m[8..], &before(&r.w));
            same(s, &[WEMP], &m[..8], &before(&r.w));
            let (odd, even) = (next_aux(), next_aux());
            s.constrain(any(&[POP, WPOP]), con(1), odd.clone());
            s.zero_where(&odd, p(&r.pos[0]).xor(&con(1)));
            s.constrain(any(&[PUSH, WNODER]), con(1), even.clone());
            s.zero_where(&even, p(&r.pos[0]));
            register(s, &r.stk, &[(&[POP], to(&m[..8])), (&[PUSH], to(&out[..]))]);
            // The run's outputs come into the root at its end, in two
            // walks up the tree from the nodes held, each with nothing to
            // the right of it: from the position the run began at and the
            // nodes it began with, to the root as the run's spending left
            // it, which shows them to be the tree's; and from the next
            // position and the nodes now held, to the root with the
            // outputs in it.
            same(s, &[WEND1, WEND2], &before(&r.stk0), &zeros8);
            same(s, &[WEND1], &before(&r.v), &before(&r.root));
            same(s, &[SETL], &[p(&r.stage)], &[con(0)]);
            same(s, &[WEND1], &[p(&r.stage)], &[con(1)]);
            same(s, &[WEND2], &[p(&r.stage)], &[con(2)]);
            same(s, &[OLEAF, CLEAF], one(&r.stage), &[con(0)]);
            same(s, &[START], &r.stk0, &r.stk);
            same(s, &[START], &r.next0, &r.next);
            same(s, &[START], one(&r.stage), &[con(0)]);
            register(s, &r.stk0, &[(&[WPOP], to(&m[..8])), (&[WEND1], to(&before(&r.stk)))]);
            register(s, &r.next0, &[(&[WEND1], to(&before(&r.next)))]);
            let stages = [(&[SETL][..], con(1)), (&[WEND1][..], con(2)), (&[WEND2][..], ones())];
            register(s, one(&r.stage), &stages.map(|(ks, stage)| (ks, to(&[stage]))));
            // A run that made outputs does not end before they are in.
            // A reveal that has spent its commitment goes on to the
            // name: the row after a spend made while revealing is the
            // name's leaf, and no other is. (Stopped there, with the
            // commitment gone and nothing registered, a reveal would be
            // anyone's to undo who had seen it: the flows' numbers are
            // such that only revealing has this bit of those a spend
            // is made in.)
            const { assert!(REVEALING == 2 && (PAYING | POLICY) & 2 == 0) };
            let spent_in = next_aux();
            s.constrain(p(&f(ISP)), p(&r.flow), spent_in.clone());
            s.zero_where(&con(2), spent_in.xor(&f(NLEAFR)));
            let open = next_aux();
            s.constrain(last_row.clone(), r.stage.xor(&ones()), open.clone());
            for (now, then) in r.next.iter().zip(&r.next0) {
                s.zero_where(&open, now.xor(then));
            }

            // The public values: the registers of the first row, then of
            // the last.
            let mut public = public.chunks(4);
            let mut bind = |s: &mut Symbolic, words: &[Expr], at: &Expr| {
                for part in words.chunks(4) {
                    let said = Sum::element(public.next().expect("a public element"));
                    s.product(Sum::element(part).add(&said), Sum::bits(at, 0, 1), Sum::default());
                }
            };
            for (at, is_first) in [(first, true), (last_row, false)] {
                let chained: [&[Expr]; 17] = [
                    &r.root,
                    &r.isp,
                    &r.osp,
                    &r.id,
                    &r.body,
                    &r.counts,
                    &r.next,
                    &r.sum_in,
                    &r.sum_out,
                    &r.names,
                    &r.caps,
                    &r.sgn,
                    &r.app,
                    &r.phase,
                    &r.cover,
                    &r.covered,
                    one(&r.take),
                ];
                for words in chained {
                    bind(s, words, at);
                }
                if is_first {
                    bind(s, &r.signed, at);
                    bind(s, one(&r.before), at);
                }
            }
            core
        },
        INPUTS,
    )
}

/// The registers' values.
#[derive(Clone, Copy, Default)]
struct State {
    root: [u32; 8],
    isp: [u32; 8],
    osp: [u32; 8],
    signed: [u32; 8],
    id: [u32; 8],
    body: [u32; 8],
    counts: [u32; 3],
    next: [u32; 2],
    sum_in: [u32; 4],
    sum_out: [u32; 4],
    hold: [u32; 8],
    amount: [u32; 2],
    pos: [u32; 2],
    pos0: [u32; 2],
    cnt: u32,
    w: [u32; 8],
    v: [u32; 8],
    input: u32,
    names: [u32; 8],
    name: [u32; 8],
    owner: [u32; 8],
    record: [u32; 8],
    place: [u32; 4],
    flow: u32,
    caps: [u32; 4],
    counted: [u32; 2],
    made: u32,
    cover: [u32; 8],
    covered: [u32; 8],
    take: u32,
    state: u32,
    rebind: [u32; 8],
    rebinding: u32,
    sgn: [u32; 8],
    app: [u32; 8],
    phase: [u32; 2],
    stk: [u32; 8],
    stk0: [u32; 8],
    next0: [u32; 2],
    stage: u32,
}

/// Where the chains of nodes held are among a row's words, and the
/// word that says whether a run's outputs are still to come in.
const STK_AT: usize = FRONT + 1 + KINDS + STATE - 19;
const OPEN_AT: usize = FRONT + 1 + KINDS + STATE + 1 + AUX - 1;

impl State {
    fn words(&self) -> Vec<u32> {
        let mut out = Vec::with_capacity(STATE);
        for part in [&self.root[..], &self.isp, &self.osp, &self.signed, &self.id, &self.body, &self.counts] {
            out.extend(part);
        }
        out.push(self.counts[2].wrapping_sub(1));
        for part in [&self.next[..], &self.sum_in, &self.sum_out, &self.hold, &self.amount, &self.pos, &self.pos0] {
            out.extend(part);
        }
        out.push(self.cnt);
        out.extend(self.w);
        out.extend(self.v);
        out.push(self.input);
        for part in [&self.names[..], &self.name, &self.owner, &self.record, &self.place] {
            out.extend(part);
        }
        out.push(self.flow);
        out.extend(self.caps);
        out.extend(self.counted);
        out.push(self.made);
        out.extend(self.cover);
        out.extend(self.covered);
        out.extend([self.take, self.state]);
        out.extend(self.rebind);
        out.push(self.rebinding);
        for part in [&self.sgn[..], &self.app, &self.phase, &self.stk, &self.stk0, &self.next0] {
            out.extend(part);
        }
        out.push(self.stage);
        assert_eq!(out.len(), STATE);
        out
    }

    /// The public elements' words, for the first row or for the last.
    fn public(&self, last: bool) -> Vec<u32> {
        let mut out = Vec::new();
        let mut push = |words: &[u32]| {
            for part in words.chunks(4) {
                out.extend((0..4).map(|i| part.get(i).copied().unwrap_or(0)));
            }
        };
        let take = [self.take];
        let chained: [&[u32]; 17] = [
            &self.root,
            &self.isp,
            &self.osp,
            &self.id,
            &self.body,
            &self.counts,
            &self.next,
            &self.sum_in,
            &self.sum_out,
            &self.names,
            &self.caps,
            &self.sgn,
            &self.app,
            &self.phase,
            &self.cover,
            &self.covered,
            &take,
        ];
        for words in chained {
            push(words);
        }
        if !last {
            push(&self.signed);
            push(&[self.counts[2].wrapping_sub(1)]);
        }
        out
    }
}

/// The carries of `x + y + carry_in`, a word of them, and the sum.
fn carries(x: u32, y: u32, carry_in: u32) -> (u32, u32) {
    let sum = x.wrapping_add(y).wrapping_add(carry_in);
    let into = x ^ y ^ sum;
    ((x & y) | ((x ^ y) & into), sum)
}

/// A row's auxiliary words, in the circuit's order: `old` are the
/// registers of the row before, `to` its own, `made` the last word of
/// its block.
fn auxiliary(old: &State, to: &State, kind: usize, before: usize, dir: u32, made: u32) -> Vec<u32> {
    let mut aux = Vec::with_capacity(AUX);
    let bits = 1u128 << kind;
    aux.extend((0..KIND_WORDS).map(|w| carries((bits >> (32 * w)) as u32, !0, 0).0));
    aux.push(carries(old.counts[0], !0, 0).0);
    aux.push(carries(old.counts[1], !0, 0).0);
    aux.push(carries(old.cnt, 1, 0).0);
    let (c0, _) = carries(old.next[0], 1, 0);
    aux.extend([c0, c0 >> 31, carries(old.next[1], 0, c0 >> 31).0]);
    for sum in [&old.sum_in, &old.sum_out] {
        let mut carry_in = 0;
        for (i, word) in sum.iter().enumerate() {
            let (c, _) = carries(*word, if i < 2 { to.amount[i] } else { 0 }, carry_in);
            carry_in = c >> 31;
            aux.extend([c, carry_in]);
        }
    }
    aux.push(carries(to.counts[2], !0, 0).0);
    // The age of what the block's last word says was made then.
    let (c, age) = carries(to.counts[2], !made, 1);
    aux.extend([c, c >> 31]);
    let (c, _) = carries(age, !1, 1);
    aux.extend([c, c >> 31]);
    let (c, _) = carries(MAX_REVEAL, !age, 1);
    aux.extend([c, c >> 31]);
    aux.push(old.pos[1].rotate_right(1) & (1 << 31));
    for i in 1..4 {
        aux.push(old.place[i].rotate_right(1) & (1 << 31));
    }
    aux.push((kind == SN || kind == OLD || kind == PNODE) as u32);
    aux.push((kind == NOLD) as u32);
    for kinds in [&[SN, PNODE][..], &[OLD, NOLD], &[NEW, NNEW]] {
        let on = if kinds.contains(&kind) { !0u32 } else { 0 };
        aux.extend([on & !dir, on & dir]);
    }
    for (i, (k, _)) in CAPS.iter().enumerate() {
        aux.push(if kind == *k { old.caps[i] } else { 0 });
    }
    aux.extend([carries(old.counted[0], 1, 0).0, carries(old.counted[1], 1, 0).0]);
    let (c, old_by) = carries(to.counts[2], !to.made, 1);
    aux.extend([c, c >> 31]);
    let (c, _) = carries(old_by, !made, 1);
    aux.extend([c, c >> 31]);
    // The covered outputs still to come, less one, and less two.
    let (c, fewer) = carries(old.take, !0, 0);
    aux.extend([c, c >> 31]);
    let (c, _) = carries(fewer, !0, 0);
    let last = if c >> 31 == 0 { !0u32 } else { 0 };
    aux.extend([c, c >> 31, last, if kind == COVR { last } else { 0 }]);
    aux.push(if (kind == POP || kind == PUSH) && before == BODYOUT { !0 } else { 0 });
    let (c, _) = carries(to.state, !made, 0);
    aux.extend([c, c >> 31]);
    aux.extend([(kind == POP || kind == WPOP) as u32, (kind == PUSH || kind == WNODER) as u32]);
    // The flow in hand at a spend, on the row after it.
    aux.push(if before == ISP { old.flow } else { 0 });
    // Whether the run's outputs are still to come in: the last row's to
    // say ([`Run::finish`]).
    aux.push(0);
    assert_eq!(aux.len(), AUX);
    aux
}

fn words(d: &Digest) -> [u32; 8] {
    blake3::words(d)
}

fn split(x: u64) -> [u32; 2] {
    [x as u32, (x >> 32) as u32]
}

/// A run's rows as they are made: their inputs, the registers as the
/// last row left them, and that row's kind, direction and output.
pub struct Run {
    pub rows: Vec<[u32; INPUTS]>,
    state: State,
    kind: usize,
    dir: u32,
    out: [u32; 8],
    start: State,
    /// The nodes held, the lowest last, each with the chain below it;
    /// and the same as the run began with them.
    stack: Vec<([u32; 8], [u32; 8])>,
    stack0: Vec<([u32; 8], [u32; 8])>,
    /// Where the output lies that the input in hand spends: what its
    /// row of the id is keyed by.
    placing: [u32; 2],
}

/// Where a signature's entry is in the signed set: its place and its
/// siblings, the lowest first.
pub type Signed = (u64, Vec<Digest>);

impl Run {
    /// A run from the state `record` starts in, with the transaction in
    /// hand `carry` (its id, its body so far, inputs and things to make
    /// left) and the signed set of root `signed`.
    pub fn new(record: &Record, carry: Carry, signed: &Digest) -> Run {
        let state = State {
            root: words(&record.root[0]),
            isp: words(&record.inputs[0]),
            osp: words(&record.outputs[0]),
            signed: words(signed),
            id: words(&carry.0),
            body: words(&carry.1),
            counts: [carry.2, carry.3, record.height],
            cover: words(&carry.4.0),
            covered: words(&carry.4.1),
            take: carry.4.2,
            next: split(record.next[0]),
            sum_in: std::array::from_fn(|w| (record.sum_in >> (32 * w)) as u32),
            sum_out: std::array::from_fn(|w| (record.sum_out >> (32 * w)) as u32),
            names: words(&record.names[0]),
            caps: [1; 4],
            sgn: words(&record.ops[0]),
            app: words(&record.done[0]),
            ..State::default()
        };
        Run::from(state)
    }

    fn from(state: State) -> Run {
        // The nodes held are a run's own: none until it is told them.
        let state = State { stk: [0; 8], stk0: [0; 8], next0: state.next, stage: 0, ..state };
        let (stack, stack0) = (Vec::new(), Vec::new());
        let mut run = Run {
            rows: Vec::new(),
            state,
            kind: START,
            dir: 0,
            out: [0; 8],
            start: state,
            stack,
            stack0,
            placing: [0; 2],
        };
        run.push(START, [0; 16], state);
        run
    }

    /// A run that goes on from where `before` ends: the same registers,
    /// in a first row of its own.
    pub fn after(before: &Run) -> Run {
        assert!(ENDS.contains(&before.kind), "a run ends between items");
        assert!(before.settled(), "a run's outputs are in the root before it ends");
        Run::from(before.state)
    }

    /// Whether the run's outputs, if it made any, are in the root.
    fn settled(&self) -> bool {
        self.state.stage == !0 || (self.state.stage == 0 && self.state.next == self.state.next0)
    }

    /// The chain of nodes held with `item` on it.
    fn held(below: &[u32; 8], item: &[u32; 8]) -> [u32; 8] {
        blake3::compress(&[DOM_STACK, 0, 0, 0, 0, 0, 0, 0], &Self::pair(below, item), 0, 64, FULL)
    }

    /// Tells the run the nodes of the outputs' tree to the left of the
    /// next position's path, the lowest first, as they are once
    /// everything the run spends is gone
    /// ([`crate::ledger::Outputs::frontier`]): before it makes an
    /// output, where the next position is not the tree's first.
    pub fn frontier(&mut self, nodes: &[Digest]) {
        assert!(self.stack.is_empty() && self.state.stage == 0 && self.state.next == self.state.next0);
        let next = self.state.next[0] as u64 | (self.state.next[1] as u64) << 32;
        assert_eq!(nodes.len(), next.count_ones() as usize, "a node for each bit of the next position");
        let mut chain = [0u32; 8];
        for node in nodes.iter().rev() {
            let node = words(node);
            self.stack.push((node, chain));
            chain = Self::held(&chain, &node);
        }
        self.stack0 = self.stack.clone();
        // The chain is a register no row has set yet: every row's.
        for row in &mut self.rows {
            row[STK_AT..STK_AT + 8].copy_from_slice(&chain);
            row[STK_AT + 8..STK_AT + 16].copy_from_slice(&chain);
        }
        (self.state.stk, self.state.stk0) = (chain, chain);
        (self.start.stk, self.start.stk0) = (chain, chain);
    }

    fn halved(pos: [u32; 2]) -> [u32; 2] {
        split((pos[0] as u64 | (pos[1] as u64) << 32) >> 1)
    }

    /// The leaf in hand joins the nodes held: with each that its
    /// position has a bit at, and what that leaves is held.
    fn append(&mut self) {
        while self.state.pos[0] & 1 == 1 {
            let (node, below) = self.stack.pop().expect("the tree's nodes to the left: Run::frontier");
            self.step(POP, Self::pair(&below, &node), |s, _| s.stk = below);
            let block = Self::pair(&node, &self.state.v);
            self.step(MRG, block, |s, out| (s.v, s.pos) = (out, Self::halved(s.pos)));
        }
        let (below, node) = (self.state.stk, self.state.v);
        self.step(PUSH, Self::pair(&below, &node), |s, out| s.stk = out);
        self.stack.push((node, below));
    }

    /// A walk up the tree from an empty leaf at the position in hand,
    /// with `held` to its left and nothing to its right.
    fn walk(&mut self, mut held: Vec<([u32; 8], [u32; 8])>) {
        for _ in 0..OUTPUTS_HEIGHT {
            let up = |s: &mut State, out: [u32; 8]| (s.v, s.pos, s.cnt) = (out, Self::halved(s.pos), s.cnt + 1);
            if self.state.pos[0] & 1 == 1 {
                let (node, below) = held.pop().expect("a node for each bit of the position");
                self.step(WPOP, Self::pair(&below, &node), |s, _| s.stk0 = below);
                let block = Self::pair(&node, &self.state.v);
                self.step(WNODEL, block, up);
            } else {
                let block = Self::pair(&self.state.v, &self.state.w);
                self.step(WNODER, block, up);
            }
            let block = Self::pair(&self.state.w, &self.state.w);
            self.step(WEMP, block, |s, out| s.w = out);
        }
        assert!(held.is_empty());
    }

    /// The run's outputs come into the root: nothing more is made in
    /// this run. Does nothing if it made none.
    pub fn settle(&mut self) {
        if self.state.stage != 0 || self.state.next == self.state.next0 {
            return;
        }
        assert!(BETWEEN.contains(&self.kind), "outputs come into the root between items");
        self.step(SETL, [0; 16], |s, _| (s.v, s.w, s.pos, s.cnt, s.stage) = ([0; 8], [0; 8], s.next0, 0, 1));
        // (Where the nodes told are not the tree's, less what the run
        // spends, this walk does not reach the root, and the rows are
        // not proven.)
        self.walk(self.stack0.clone());
        self.step(WEND1, [0; 16], |s, _| {
            (s.stk0, s.next0, s.pos) = (s.stk, s.next, s.next);
            (s.v, s.w, s.cnt, s.stage) = ([0; 8], [0; 8], 0, 2);
        });
        self.walk(self.stack.clone());
        self.step(WEND2, [0; 16], |s, _| (s.root, s.stage) = (s.v, !0));
    }

    /// The compression a row of `kind` does of `block`.
    fn hash(&self, kind: usize, block: &[u32; 16]) -> ([u32; 8], [u32; 8]) {
        let spec = &SPECS[kind];
        let mut cv = if spec.goes_on { self.out } else { [spec.domain.unwrap_or(0), 0, 0, 0, 0, 0, 0, 0] };
        if kind == BODYIN {
            cv[1..3].copy_from_slice(&self.placing);
        }
        (cv, blake3::compress(&cv, block, 0, spec.len, spec.flags))
    }

    /// A row of `kind` hashing `block`, the registers then `to`.
    fn push(&mut self, kind: usize, block: [u32; 16], to: State) {
        let old = self.state;
        let spec = &SPECS[kind];
        let (cv, out) = self.hash(kind, &block);
        let dir = match kind {
            SN | OLD | PNODE => 0u32.wrapping_sub(old.pos[0] & 1),
            NOLD => 0u32.wrapping_sub(old.place[0] & 1),
            NEW | NNEW => self.dir,
            _ => 0,
        };
        let mut r = [0u32; INPUTS];
        r[..8].copy_from_slice(&cv);
        r[8..24].copy_from_slice(&block);
        (r[24], r[25]) = (spec.len, spec.flags);
        r[26 + kind / 32] = 1 << (kind % 32);
        r[FRONT + kind] = !0;
        r[FRONT + KINDS] = spec.domain.unwrap_or(0);
        let state = to.words();
        let at = FRONT + 1 + KINDS;
        r[at..at + STATE].copy_from_slice(&state);
        r[at + STATE] = dir;
        let aux = auxiliary(&old, &to, kind, self.kind, dir, block[15]);
        r[at + STATE + 1..at + STATE + 1 + aux.len()].copy_from_slice(&aux);
        self.rows.push(r);
        (self.state, self.kind, self.dir, self.out) = (to, kind, dir, out);
    }

    /// A row, then the registers the kind sets from its output.
    fn step(&mut self, kind: usize, block: [u32; 16], set: impl FnOnce(&mut State, [u32; 8])) {
        let (_, out) = self.hash(kind, &block);
        let mut to = self.state;
        set(&mut to, out);
        self.push(kind, block, to);
    }

    fn pair(left: &[u32], right: &[u32]) -> [u32; 16] {
        std::array::from_fn(|i| if i < 8 { left[i] } else { right[i - 8] })
    }

    /// A level of the outputs' walk: a row for the old path and one for
    /// the new.
    fn level(&mut self, sibling: &Digest) {
        let sibling = words(sibling);
        let right = self.state.pos[0] & 1 == 1;
        let of = |child: &[u32; 8]| if right { Self::pair(&sibling, child) } else { Self::pair(child, &sibling) };
        let block = of(&self.state.w);
        self.step(OLD, block, |s, out| s.w = out);
        let block = of(&self.state.v);
        self.step(NEW, block, |s, out| {
            s.v = out;
            let pos = (s.pos[0] as u64 | (s.pos[1] as u64) << 32) >> 1;
            (s.pos, s.cnt) = (split(pos), s.cnt + 1);
        });
    }

    /// The registry's walk from the leaves in hand, and its end.
    fn registry(&mut self, path: &[Digest]) {
        for sibling in path {
            let sibling = words(sibling);
            let right = self.state.place[0] & 1 == 1;
            let of = |child: &[u32; 8]| if right { Self::pair(&sibling, child) } else { Self::pair(child, &sibling) };
            let block = of(&self.state.w);
            self.step(NOLD, block, |s, out| s.w = out);
            let block = of(&self.state.v);
            self.step(NNEW, block, |s, out| {
                s.v = out;
                let place = (0..4).fold(0u128, |x, i| x | (s.place[i] as u128) << (32 * i)) >> 1;
                (s.place, s.cnt) = (std::array::from_fn(|i| (place >> (32 * i)) as u32), s.cnt + 1);
            });
        }
        self.step(NEND, [0; 16], |s, _| s.names = s.v);
    }

    /// A transaction begins: its counts, and the id its inputs' entries
    /// are to be looked up under.
    pub fn head(&mut self, tx: &Transaction) {
        let mut block = [0u32; 16];
        (block[0], block[1]) = ((tx.inputs.len() + tx.policy.len()) as u32, (tx.outputs.len() + tx.ops.len()) as u32);
        block[2] = tx.covered;
        let id = words(&tx.id());
        let cover = tx.cover().map_or([0; 8], |(_, digest)| words(&digest));
        self.step(HEAD, block, |s, out| {
            (s.body, s.id, s.counts[0], s.counts[1]) = (out, id, block[0], block[1]);
            (s.cover, s.covered, s.take) = (cover, [0; 8], block[2]);
        });
    }

    /// The rows that find a key's entry in the signed set: the key, the
    /// entry of its signature (with `leaf`) of the message in hand, and
    /// the path. `kinds` are the key's row's and the entry's second
    /// row's: a payment's, an update's (whose message is not the id), or
    /// a policy's.
    fn entry(&mut self, key: &PublicKey, leaf: u64, signed: &Signed, kinds: (usize, usize)) {
        let mut block = [0u32; 16];
        block[..8].copy_from_slice(&words(&key.root));
        block[8..12].copy_from_slice(&blake3::words::<4>(&key.pub_seed));
        block[12] = key.height as u32;
        self.step(kinds.0, block, |s, out| {
            s.hold = out;
            match kinds.0 {
                KEY => s.flow = PAYING,
                UKEY => (s.flow, s.caps[2]) = (UPDATING, s.caps[2] << 1),
                _ => {}
            }
        });
        self.step(ENT1, block, |_, _| {});
        let mut entry = [0u32; 16];
        let message = match kinds.1 {
            ENT2U => &self.state.w,
            ENT2R => &self.state.rebind,
            _ => &self.state.id,
        };
        entry[..8].copy_from_slice(message);
        entry[8..10].copy_from_slice(&split(leaf));
        let place = split(signed.0);
        self.step(kinds.1, entry, |s, _| (s.cnt, s.pos) = (0, place));
        self.climb(SN, &signed.1);
    }

    /// Rows of `kind` up a tree from the last output, by the bits of the
    /// position in hand.
    fn climb(&mut self, kind: usize, siblings: &[Digest]) {
        for sibling in siblings {
            let (own, sibling) = (self.out, words(sibling));
            let block =
                if self.state.pos[0] & 1 == 1 { Self::pair(&sibling, &own) } else { Self::pair(&own, &sibling) };
            self.step(kind, block, |s, _| {
                let pos = (s.pos[0] as u64 | (s.pos[1] as u64) << 32) >> 1;
                (s.pos, s.cnt) = (split(pos), s.cnt + 1);
            });
        }
    }

    /// An input that spends a policy's output: the conditions of the
    /// leaf shown, each with what is shown for it, the leaf's path to
    /// the policy's root, and the output's removal by `path`. `signed`
    /// are the places in the signed set of the signers' entries, in the
    /// order the signers come.
    pub fn policy_input(&mut self, input: &crate::conditions::PolicyInput, path: &[Digest], signed: &[Signed]) {
        use crate::conditions::{Cond, Shown};
        let mut signed = signed.iter();
        self.step(PSTART, [0; 16], |s, _| {
            (s.flow, s.w, s.made, s.state) = (POLICY, [0; 8], input.created, input.state)
        });
        let cond = |tag: u32, a: u32, b: u32, digest: &[u32; 8], last: u32| {
            let mut block = [0u32; 16];
            (block[0], block[1], block[2], block[15]) = (tag, a, b, last);
            block[4..12].copy_from_slice(digest);
            block
        };
        for (c, shown) in input.conds.iter().zip(&input.shown) {
            match (c, shown) {
                (Cond::Thresh { keys, .. }, Shown::Signers(signers)) => {
                    self.step(TSTART, [0; 16], |s, _| (s.v, s.counted, s.rebinding) = ([0; 8], [0; 2], 0));
                    for (hash, signer) in keys.iter().zip(signers) {
                        match signer {
                            Some((key, leaf)) => {
                                self.entry(key, *leaf, signed.next().expect("a signer's place"), (PKEY, ENT2P));
                                let block = Self::pair(&self.state.v, &self.state.hold);
                                self.step(PSIG, block, |s, out| {
                                    (s.v, s.counted) = (out, [s.counted[0] + 1, s.counted[1] + 1])
                                });
                            }
                            None => {
                                let block = Self::pair(&self.state.v, &words(hash));
                                self.step(PSKIP, block, |s, out| (s.v, s.counted[1]) = (out, s.counted[1] + 1));
                            }
                        }
                    }
                    let block = cond(1, self.state.counted[0], self.state.counted[1], &self.state.v, 0);
                    self.step(CTHRESH, block, |_, _| {});
                }
                (Cond::Hash(_), Shown::Preimage(preimage)) => {
                    self.step(CHASHP, Self::pair(&words(preimage), &[0; 8]), |_, _| {});
                    let block = cond(2, 0, 0, &self.out, 0);
                    self.step(CHASH, block, |_, _| {});
                }
                (Cond::Rebind { keys, channel, .. }, Shown::Signers(signers)) => {
                    let channel = words(channel);
                    let block = Self::pair(&channel, &self.state.cover);
                    self.step(RSTART, block, |s, _| (s.v, s.counted, s.rebinding) = (channel, [0; 2], !0));
                    let mut block = [0u32; 16];
                    block[0] = self.state.state;
                    self.step(RMSG2, block, |s, out| s.rebind = out);
                    for (hash, signer) in keys.iter().zip(signers) {
                        match signer {
                            Some((key, leaf)) => {
                                self.entry(key, *leaf, signed.next().expect("a signer's place"), (PKEY, ENT2R));
                                let block = Self::pair(&self.state.v, &self.state.hold);
                                self.step(PSIG, block, |s, out| {
                                    (s.v, s.counted) = (out, [s.counted[0] + 1, s.counted[1] + 1])
                                });
                            }
                            None => {
                                let block = Self::pair(&self.state.v, &words(hash));
                                self.step(PSKIP, block, |s, out| (s.v, s.counted[1]) = (out, s.counted[1] + 1));
                            }
                        }
                    }
                    let block = cond(7, self.state.counted[0], self.state.counted[1], &self.state.v, 0);
                    self.step(CREBIND, block, |_, _| {});
                }
                (Cond::State(above), _) => self.step(CSTATE, cond(5, 0, 0, &[0; 8], *above), |_, _| {}),
                (Cond::Outputs { count, digest }, _) => {
                    self.step(COUTS, cond(6, *count, 0, &words(digest), 0), |_, _| {})
                }
                (Cond::After(height), _) => self.step(CAFTER, cond(3, 0, 0, &[0; 8], *height), |_, _| {}),
                (Cond::Older(blocks), _) => self.step(COLDER, cond(4, 0, 0, &[0; 8], *blocks), |_, _| {}),
                _ => panic!("what is shown is not for the condition"),
            }
            let block = Self::pair(&self.state.w, &self.out);
            let index = split(input.index as u64);
            self.step(PLEAF, block, |s, out| (s.w, s.cnt, s.pos) = (out, 0, index));
        }
        self.climb(PNODE, &input.siblings);
        let amount = split(input.amount);
        let mut block = [0u32; 16];
        block[..8].copy_from_slice(&self.out);
        block[8..10].copy_from_slice(&amount);
        self.step(PCOMMIT, block, |s, out| (s.hold, s.amount) = (out, amount));
        let block = Self::pair(&self.state.body, &self.out);
        let pos = split(input.position);
        self.placing = pos;
        self.step(BODYIN, block, |s, out| (s.body, s.counts[0]) = (out, s.counts[0].wrapping_sub(1)));
        let block = Self::leaf_block(&self.state.hold, &input.memo, input.amount, input.created);
        self.step(PSLEAF, block, |s, out| (s.w, s.v, s.cnt, s.pos, s.pos0, s.input) = (out, [0; 8], 0, pos, pos, !0));
        self.removal(path, input.amount);
    }

    /// The outputs' walk of a leaf that leaves the state, and its end.
    fn removal(&mut self, path: &[Digest], amount: u64) {
        for sibling in path {
            self.level(sibling);
        }
        let mut block = [0u32; 16];
        block[..8].copy_from_slice(&self.state.isp);
        block[8..10].copy_from_slice(&self.state.pos0);
        self.step(ISP, block, |s, out| {
            (s.isp, s.root) = (out, s.v);
            let sum = (0..4).fold(0u128, |x, i| x | (s.sum_in[i] as u128) << (32 * i)) + amount as u128;
            s.sum_in = std::array::from_fn(|i| (sum >> (32 * i)) as u32);
        });
    }

    /// The leaf in hand joins the nodes held, at the next position; and
    /// the row of `kind` that takes what was made into its running
    /// hash.
    fn made(&mut self, kind: usize, amount: u64) {
        self.append();
        let so_far = if kind == OSP { self.state.osp } else { self.state.app };
        let block = Self::pair(&so_far, &self.state.hold);
        self.step(kind, block, |s, out| {
            if kind == OSP {
                s.osp = out;
            } else {
                s.app = out;
            }
            s.next = split((s.next[0] as u64 | (s.next[1] as u64) << 32) + 1);
            let sum = (0..4).fold(0u128, |x, i| x | (s.sum_out[i] as u128) << (32 * i)) + amount as u128;
            s.sum_out = std::array::from_fn(|i| (sum >> (32 * i)) as u32);
        });
    }

    /// A leaf of the outputs' tree, as a block.
    fn leaf_block(commitment: &[u32; 8], memo: &Memo, amount: u64, height: u32) -> [u32; 16] {
        let mut block = [0u32; 16];
        block[..8].copy_from_slice(commitment);
        block[8..13].copy_from_slice(&blake3::words::<5>(memo));
        block[13..15].copy_from_slice(&split(amount));
        block[15] = height;
        block
    }

    /// An input: the output it spends leaves the state by `path` (the
    /// tree's as the run has it: without the outputs it has made, which
    /// are in the root only at its end), and
    /// the entry of the key's signature with `leaf` is in the signed set
    /// at `signed`.
    pub fn input(&mut self, input: &Input, path: &[Digest], leaf: u64, signed: &Signed) {
        self.input_at(input, path, leaf, signed, input.position)
    }

    /// [`Run::input`], the leaf walked being the one at `walked`: the
    /// input's own place, but in a test.
    fn input_at(&mut self, input: &Input, path: &[Digest], leaf: u64, signed: &Signed, walked: u64) {
        self.entry(&input.key, leaf, signed, (KEY, ENT2));
        let amount = split(input.amount);
        let mut block = [0u32; 16];
        block[..8].copy_from_slice(&self.state.hold);
        block[8..10].copy_from_slice(&amount);
        self.step(COMMIT, block, |s, out| (s.hold, s.amount) = (out, amount));
        let block = Self::pair(&self.state.body, &self.out);
        self.placing = split(input.position);
        let pos = split(walked);
        self.step(BODYIN, block, |s, out| (s.body, s.counts[0]) = (out, s.counts[0].wrapping_sub(1)));
        let block = Self::leaf_block(&self.state.hold, &input.memo, input.amount, input.created);
        self.step(LEAF, block, |s, out| (s.w, s.v, s.cnt, s.pos, s.pos0, s.input) = (out, [0; 8], 0, pos, pos, !0));
        self.removal(path, input.amount);
    }

    /// An output of the key of `key_hash`, made at the next position.
    pub fn output(&mut self, output: &Output, key_hash: &Digest) {
        assert!(self.state.stage == 0, "the run's outputs are in the root: no more are made in it");
        let amount = split(output.amount);
        let mut block = [0u32; 16];
        block[..8].copy_from_slice(&words(key_hash));
        block[8..10].copy_from_slice(&amount);
        self.step(OUTC, block, |s, _| (s.amount, s.flow) = (amount, MAKING));
        let mut block = Self::leaf_block(&self.out, &output.memo, output.amount, self.state.counts[2]);
        self.step(OLEAF, block, |s, out| (s.w, s.v, s.cnt, s.pos, s.input) = ([0; 8], out, 0, s.next, 0));
        block[15] = 0;
        self.step(OITEM, block, |s, out| s.hold = out);
        let block = Self::pair(&self.state.body, &self.out);
        self.step(BODYOUT, block, |s, out| (s.body, s.counts[1]) = (out, s.counts[1].wrapping_sub(1)));
        if self.state.take > 0 {
            // One of the outputs conditions are on.
            let block = Self::pair(&self.state.covered, &self.state.hold);
            self.step(COVR, block, |s, out| (s.covered, s.take) = (out, s.take - 1));
        }
        self.made(OSP, output.amount);
    }

    /// An operation on a name that the transaction in hand carries, by
    /// its hash: into the transaction's id and into the block's hash of
    /// what its transactions carry. It is done after them
    /// ([`Run::commit`], [`Run::reveal`], [`Run::update`]).
    pub fn carried(&mut self, op: &Digest) {
        let op = words(op);
        let block = Self::pair(&self.state.body, &op);
        self.step(OPBODY, block, |s, out| (s.body, s.counts[1], s.hold) = (out, s.counts[1].wrapping_sub(1), op));
        let block = Self::pair(&self.state.sgn, &self.state.hold);
        self.step(OPSGN, block, |s, out| s.sgn = out);
    }

    /// A commitment to a name, done: an output of no amount at the next
    /// position.
    pub fn commit(&mut self, commit: &Digest, memo: &Memo) {
        assert!(self.state.stage == 0, "the run's outputs are in the root: no more are made in it");
        let mut block = [0u32; 16];
        block[0] = 1;
        block[1..9].copy_from_slice(&words(commit));
        block[9..14].copy_from_slice(&blake3::words::<5>(memo));
        self.step(OPC, block, |s, out| {
            (s.hold, s.flow, s.phase[0]) = (out, COMMITTING, !0);
            s.caps[0] <<= 1;
        });
        let block = Self::leaf_block(&words(commit), memo, 0, self.state.counts[2]);
        self.step(CLEAF, block, |s, out| {
            (s.w, s.v, s.cnt, s.pos, s.input, s.amount) = ([0; 8], out, 0, s.next, 0, [0; 2])
        });
        self.made(OPSP, 0);
    }

    /// The rows that hash `record`: its name's hash, its owner and its
    /// hash are then in hand.
    fn record(&mut self, record: &registry::Record) {
        let block = Self::pair(&words(&registry::name_hash(&record.name)), &words(&record.owner));
        self.step(REC1, block, |s, _| {
            (s.name, s.owner, s.phase[0]) = (block[..8].try_into().unwrap(), block[8..].try_into().unwrap(), !0)
        });
        let block = Self::pair(&words(&record.value), &words(&record.memo));
        self.step(REC2, block, |s, out| s.record = out);
    }

    /// The operation's hash, into the block's hash of those done.
    fn op_done(&mut self) {
        let mut block = [0u32; 16];
        block[0] = self.state.flow;
        block[1..9].copy_from_slice(&self.state.record);
        self.step(OPX, block, |s, out| s.hold = out);
        let block = Self::pair(&self.state.app, &self.state.hold);
        self.step(OPABS, block, |s, out| s.app = out);
    }

    /// A reveal: the commitment of `record` with `salt`, made at height
    /// `made` with `memo`, leaves the state at `position` by `path`, and
    /// the record comes into the registry by `names`, the path of its
    /// place.
    #[allow(clippy::too_many_arguments)]
    pub fn reveal(
        &mut self,
        record: &registry::Record,
        salt: &Digest,
        memo: &Memo,
        made: u32,
        position: u64,
        path: &[Digest],
        names: &[Digest],
    ) {
        self.reveal_spend(record, salt, memo, made, position, path);
        let block = Self::pair(&self.state.name, &self.state.record);
        self.step(NLEAFR, block, |s, out| {
            (s.w, s.v, s.cnt, s.place) = ([0; 8], out, 0, s.name[..4].try_into().unwrap())
        });
        self.registry(names);
        self.op_done();
    }

    /// The first part of a reveal: its record, and its commitment
    /// spent.
    fn reveal_spend(
        &mut self,
        record: &registry::Record,
        salt: &Digest,
        memo: &Memo,
        made: u32,
        position: u64,
        path: &[Digest],
    ) {
        self.record(record);
        let block = Self::pair(&self.state.name, &words(salt));
        self.step(COM1, block, |s, _| {
            s.flow = REVEALING;
            s.caps[1] <<= 1;
        });
        let block = Self::pair(&self.state.owner, &[0; 8]);
        self.step(COM2, block, |_, _| {});
        let block = Self::leaf_block(&self.out, memo, 0, made);
        let pos = split(position);
        self.step(RLEAF, block, |s, out| {
            (s.w, s.v, s.cnt, s.pos, s.pos0, s.input, s.amount) = (out, [0; 8], 0, pos, pos, !0, [0; 2])
        });
        self.removal(path, 0);
    }

    /// An update: `record` takes the place of `old`, whose owner is the
    /// hash of `key`; the entry of that key's signature (with `leaf`) of
    /// the update's message is in the signed set at `signed`; `names` is
    /// the path of the name's place.
    pub fn update(
        &mut self,
        record: &registry::Record,
        old: &registry::Record,
        key: &PublicKey,
        leaf: u64,
        signed: &Signed,
        names: &[Digest],
    ) {
        self.record(record);
        let block = Self::pair(&self.state.record, &[0; 8]);
        self.step(UMSG, block, |s, out| s.w = out);
        self.entry(key, leaf, signed, (UKEY, ENT2U));
        let block = Self::pair(&self.state.name, &self.state.hold);
        self.step(OREC1, block, |_, _| {});
        let block = Self::pair(&words(&old.value), &words(&old.memo));
        self.step(OREC2, block, |_, _| {});
        let block = Self::pair(&self.state.name, &self.out);
        self.step(NLEAFO, block, |s, out| s.w = out);
        let block = Self::pair(&self.state.name, &self.state.record);
        self.step(NLEAFN, block, |s, out| (s.v, s.cnt, s.place) = (out, 0, s.name[..4].try_into().unwrap()));
        self.registry(names);
        self.op_done();
    }

    /// A sweep, between transactions: the commitment `commit` made at
    /// height `made` with `memo` leaves the state at `position` by
    /// `path`.
    pub fn sweep(&mut self, commit: &Digest, memo: &Memo, made: u32, position: u64, path: &[Digest]) {
        let block = Self::leaf_block(&words(commit), memo, 0, made);
        let pos = split(position);
        self.step(SLEAF, block, |s, out| {
            (s.w, s.v, s.cnt, s.pos, s.pos0, s.input, s.amount, s.flow) = (out, [0; 8], 0, pos, pos, !0, [0; 2], 0);
            (s.caps[3], s.phase) = (s.caps[3] << 1, [!0; 2]);
        });
        self.removal(path, 0);
    }

    /// A row with the flags of several kinds at once, as no honest run
    /// has: for the test that it is refused.
    #[cfg(test)]
    fn push_multi(&mut self, kinds: &[usize], dom: u32, block: [u32; 16], set: impl FnOnce(&mut State, [u32; 8])) {
        let old = self.state;
        let cv = [dom, 0, 0, 0, 0, 0, 0, 0];
        let out = blake3::compress(&cv, &block, 0, 64, FULL);
        let mut to = self.state;
        set(&mut to, out);
        let mut r = [0u32; INPUTS];
        r[..8].copy_from_slice(&cv);
        r[8..24].copy_from_slice(&block);
        (r[24], r[25]) = (64, FULL);
        for kind in kinds {
            r[26 + kind / 32] |= 1 << (kind % 32);
            r[FRONT + kind] = !0;
        }
        r[FRONT + KINDS] = dom;
        let state = to.words();
        let at = FRONT + 1 + KINDS;
        r[at..at + STATE].copy_from_slice(&state);
        r[at + STATE] = 0;
        let mut aux = auxiliary(&old, &to, kinds[0], self.kind, 0, block[15]);
        for (w, a) in aux.iter_mut().enumerate().take(KIND_WORDS) {
            let word = r[26 + w];
            *a = carries(word, !0, 0).0;
        }
        r[at + STATE + 1..at + STATE + 1 + aux.len()].copy_from_slice(&aux);
        self.rows.push(r);
        (self.state, self.kind, self.dir, self.out) = (to, kinds[0], 0, out);
    }

    /// A head that says a cover the transaction does not have.
    #[cfg(test)]
    fn head_saying(&mut self, tx: &Transaction, cover: [u32; 8]) {
        let mut block = [0u32; 16];
        (block[0], block[1]) = ((tx.inputs.len() + tx.policy.len()) as u32, (tx.outputs.len() + tx.ops.len()) as u32);
        block[2] = tx.covered;
        let id = words(&tx.id());
        self.step(HEAD, block, |s, out| {
            (s.body, s.id, s.counts[0], s.counts[1]) = (out, id, block[0], block[1]);
            (s.cover, s.covered, s.take) = (cover, [0; 8], block[2]);
        });
    }

    /// Rows so far.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// The rows filled to a power of two (and to `at_least`), the
    /// program, and the public values.
    pub fn finish(mut self, at_least: usize) -> (Vec<[u32; INPUTS]>, Vec<u32>, Vec<u32>) {
        self.settle();
        assert!(ENDS.contains(&self.kind), "a run ends between items");
        let n = self.rows.len().max(at_least).next_power_of_two();
        while self.rows.len() < n {
            self.push(PAD, [0; 16], self.state);
        }
        // The first row's row before is the last: its carries are of
        // the last row's registers.
        let aux = auxiliary(&self.state, &self.start, START, self.kind, 0, 0);
        let from = FRONT + 1 + KINDS + STATE + 1;
        self.rows[0][from..from + aux.len()].copy_from_slice(&aux);
        self.rows[n - 1][OPEN_AT] = !self.state.stage;
        let mut program = vec![0u32; n * PROGRAM];
        program[0] = !0;
        program[(n - 1) * PROGRAM + 1] = !0;
        let public = [self.start.public(false), self.state.public(true)].concat();
        (self.rows, program, public)
    }
}

/// The most rows a transaction takes in a run, whatever the state: for
/// whoever must say beforehand whether one fits.
pub fn rows_bound(tx: &Transaction) -> usize {
    // An output joins a node at each level, at the most.
    let output = 7 + 2 * OUTPUTS_HEIGHT;
    1 + tx.inputs.len() * INPUT_ROWS
        + tx.policy.iter().map(policy_rows).sum::<usize>()
        + tx.outputs.len() * output
        + 2 * tx.ops.len()
}

/// A key's entry in the signed set: its row, the entry's two, the path.
const ENTRY_ROWS: usize = 3 + signed::DEPTH;
/// A leaf's removal: its path, old and new, and the row that ends it.
const REMOVAL_ROWS: usize = 2 * OUTPUTS_HEIGHT + 1;
/// The rows of an input a key signs for.
pub const INPUT_ROWS: usize = ENTRY_ROWS + 3 + REMOVAL_ROWS;

/// The rows of a policy's input: they are one run's, whatever else of
/// its transaction is.
pub fn policy_rows(input: &crate::conditions::PolicyInput) -> usize {
    use crate::conditions::{Cond, Shown};
    let signers = |shown: &Shown| match shown {
        Shown::Signers(signers) => signers.iter().map(|s| if s.is_some() { ENTRY_ROWS + 1 } else { 1 }).sum::<usize>(),
        _ => 0,
    };
    let conds = (input.conds.iter().zip(&input.shown))
        .map(|(cond, shown)| match cond {
            Cond::Thresh { .. } => 2 + signers(shown),
            Cond::Rebind { .. } => 3 + signers(shown),
            Cond::Hash(_) => 2,
            _ => 1,
        })
        .sum::<usize>();
    // The leaf's chain, its path, the commitment, the body, the leaf.
    1 + conds + input.conds.len() + crate::conditions::DEPTH + 3 + REMOVAL_ROWS
}

/// A transaction in hand: its id, its body's hash so far, the inputs
/// and outputs left of it, and its outputs conditions are on
/// ([`Covering`]).
pub type Carry = (Digest, Digest, u32, u32, Covering);

/// The outputs of a transaction in hand that conditions are on: the
/// hash it says they have, the hash of those met so far, and how many
/// are still to come.
pub type Covering = (Digest, Digest, u32);

/// The public values of a run that took the ledger from `before` to
/// `after` (the sums are the block's so far), of the signed set of root
/// `signed`, with the transaction in hand at its start and at its end:
/// what a verifier checks a proof of the run against. `caps` are the
/// counts of names' operations before and after, each a bit ([`counted`]);
/// `phase`, whether operations were being done, and commitments swept
/// (all ones if so).
pub fn public(
    before: &Record,
    after: &Record,
    signed: &Digest,
    carry: [Carry; 2],
    caps: [[u32; 4]; 2],
    phase: [[u32; 2]; 2],
) -> Vec<u32> {
    let side = |record: &Record, i: usize, carry: &Carry| State {
        root: words(&record.root[i]),
        isp: words(&record.inputs[i]),
        osp: words(&record.outputs[i]),
        signed: words(signed),
        id: words(&carry.0),
        body: words(&carry.1),
        counts: [carry.2, carry.3, record.height],
        cover: words(&carry.4.0),
        covered: words(&carry.4.1),
        take: carry.4.2,
        next: [record.next[i] as u32, (record.next[i] >> 32) as u32],
        sum_in: std::array::from_fn(|w| (record.sum_in >> (32 * w)) as u32),
        sum_out: std::array::from_fn(|w| (record.sum_out >> (32 * w)) as u32),
        names: words(&record.names[i]),
        caps: caps[i],
        sgn: words(&record.ops[i]),
        app: words(&record.done[i]),
        phase: phase[i],
        ..State::default()
    };
    [side(before, 0, &carry[0]).public(false), side(after, 1, &carry[1]).public(true)].concat()
}

/// The counts of a block that has had so many commits, reveals,
/// updates and sweeps: a bit a count.
pub fn counted(had: [u32; 4]) -> [u32; 4] {
    had.map(|n| 1 << n)
}

/// The carry of no transaction in hand: one that is whole.
pub fn closed() -> Carry {
    ([0; 32], [0; 32], 0, 0, ([0; 32], [0; 32], 0))
}

/// What a transaction in hand is once all of it is done: its id is its
/// body's hash and nothing is left; the outputs conditions are on, if
/// it had any, hash to what it said.
pub fn whole(tx: &Transaction) -> Carry {
    let cover = tx.cover().map_or([0; 32], |(_, digest)| digest);
    (tx.id(), tx.id(), 0, 0, (cover, cover, 0))
}

/// A proof of a run, with what a verifier needs beside it.
pub struct Proved {
    pub params: Params,
    /// The root of the table's program: which rows are first and last.
    pub program: Digest,
    pub proof: Proof,
    pub rows: usize,
    pub public: Vec<u32>,
    pub proving: std::time::Duration,
}

/// The proof of `run`, filled to `at_least` rows, under the parameters
/// `params` gives for its size.
pub fn prove(run: Run, at_least: usize, params: impl Fn(usize) -> Params) -> Proved {
    let (rows, program, public) = run.finish(at_least);
    prove_rows(&rows, program, public, params)
}

/// Whether rows ([`Run::finish`]) meet every constraint, with `public`
/// as what is said of them: what a proof of them would show, known
/// without making one.
pub fn holds(rows: &[[u32; INPUTS]], program: &[u32], public: &[u32]) -> bool {
    let c = circuit();
    let fixed = Fixed { program, public };
    Witness::new(&c, rows.len(), |c| self::run(c), |i| rows[i], &fixed).holds()
}

/// [`prove`], of a run's rows as [`Run::finish`] gives them.
pub fn prove_rows(
    rows: &[[u32; INPUTS]],
    program: Vec<u32>,
    public: Vec<u32>,
    params: impl Fn(usize) -> Params,
) -> Proved {
    let c = circuit();
    let params = params(variables(&c, rows.len()));
    let domain = Domain::new(params.k(), true);
    let committed = Program::new(&c, &params, &domain, program);
    let fixed = Fixed { program: &committed.words[0], public: &public };
    let t = std::time::Instant::now();
    let w = Witness::new(&c, rows.len(), |c| self::run(c), |i| rows[i], &fixed);
    let (proof, _) = argument::prove(&c, &params, &domain, w, Some(&committed), &public);
    Proved { params, program: committed.root(), proof, rows: rows.len(), public, proving: t.elapsed() }
}

impl Proved {
    pub fn verifies(&self) -> bool {
        let c = circuit();
        let domain = Domain::new(self.params.k(), false);
        let statement = Statement { program: Some(&self.program), public: &self.public };
        argument::verify(&c, &self.params, &domain, self.rows, &self.proof, &statement).is_some()
    }

    /// The proof's verification, made rows of `cx`: the program's root
    /// it was verified against, and its public elements, as the
    /// arithmetic holds them. `circuit` is this table's, which `reader`
    /// reads.
    pub fn verify_into(
        &self,
        cx: &Shared,
        circuit: &Circuit,
        reader: &mut impl Reader<Sym>,
    ) -> Option<(Vec<Sym>, Vec<Sym>)> {
        let domain = Domain::new(self.params.k(), false);
        let tables = [Table { circuit, rows: self.rows, public: &self.public }];
        let named = argument::label(&self.params, tables.iter().map(|t| t.rows));
        let (mut tr, mut opens) = (Hashed::new(&named, cx), HashedOpens::new(cx));
        let program = Some(&self.program);
        let taken = argument::check_with::<Sym, _, _, _>(
            &self.params,
            &domain,
            &tables,
            program,
            &self.proof,
            &mut tr,
            &mut opens,
            reader,
        )?;
        let public = taken.publics.into_iter().flatten().flatten().collect();
        Some((taken.program.into_iter().flatten().collect(), public))
    }
}

/// What two runs, one after the other, are together: the first's start
/// and the second's end, having found the second to start where the
/// first ended and both to be of one signed set. Each is a run's
/// public elements (or a joined pair's: the same).
pub fn join(first: &[Sym], second: &[Sym]) -> Vec<Sym> {
    let ins = CHAINED + FIXED;
    for (out, into) in first[ins..].iter().zip(&second[..CHAINED]) {
        assert!(out.is(into));
    }
    for (a, b) in first[CHAINED..ins].iter().zip(&second[CHAINED..ins]) {
        assert!(a.is(b));
    }
    [&first[..ins], &second[ins..]].concat()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::F;
    use crate::hash::EMPTY;
    use crate::ledger::{MEMO, Outputs, key_hash};
    use crate::reading::Deferred;
    use crate::xmss::{PublicKey, SecretKey};

    fn key(i: u8) -> PublicKey {
        SecretKey::generate_with_height(&[i; 32], 1).public_key()
    }

    /// The signed set over `entries`, the rest empty: its root, and an
    /// entry's place and siblings.
    struct Set(Vec<Digest>);

    impl Set {
        fn node(&self, level: usize, index: u64) -> Digest {
            if (index << level) as usize >= self.0.len() {
                return signed::empty_roots()[level];
            }
            if level == 0 {
                return self.0[index as usize];
            }
            signed::pair(&self.node(level - 1, 2 * index), &self.node(level - 1, 2 * index + 1))
        }

        fn root(&self) -> Digest {
            self.node(signed::DEPTH, 0)
        }

        fn at(&self, place: u64) -> Signed {
            (place, (0..signed::DEPTH).map(|level| self.node(level, (place >> level) ^ 1)).collect())
        }
    }

    /// A state with four outputs of 100 to keys 0 to 3, two payments
    /// that spend three of them, and the signed set of their entries.
    struct Scene {
        state: Outputs,
        txs: Vec<Transaction>,
        set: Set,
        height: u32,
    }

    fn a_scene() -> Scene {
        let mut state = Outputs::default();
        let owned: Vec<Input> = (0..4u8)
            .map(|i| {
                let out = Output::to(&key_hash(&key(i)), 100, [i; MEMO]);
                let position = state.insert(&out, 1);
                Input { key: key(i), amount: 100, memo: [i; MEMO], created: 1, position }
            })
            .collect();
        let pay = |inputs: &[usize], amounts: &[u64]| Transaction {
            inputs: inputs.iter().map(|i| owned[*i].clone()).collect(),
            outputs: amounts.iter().map(|a| Output::to(&key_hash(&key(9)), *a, [3; MEMO])).collect(),
            ops: vec![],
            policy: vec![],
            covered: 0,
        };
        let txs = vec![pay(&[0, 2], &[150, 40]), pay(&[1], &[130])];
        // Every input's entry, with some others around them.
        let mut entries = vec![[5u8; 32]; 3];
        for tx in &txs {
            for input in &tx.inputs {
                entries.push(crate::signature::entry(&input.key, &tx.id(), 1));
            }
        }
        Scene { state, txs, set: Set(entries), height: 2 }
    }

    /// The positions transactions spend.
    fn spent(txs: &[Transaction]) -> Vec<u64> {
        let of = |tx: &Transaction| {
            let policy = tx.policy.iter().map(|i| i.position);
            tx.inputs.iter().map(|i| i.position).chain(policy).collect::<Vec<u64>>()
        };
        txs.iter().flat_map(of).collect()
    }

    /// The run of the scene's transactions, with what it should be of.
    fn run_of(scene: &Scene, change: impl Fn(&mut Run, usize)) -> (Run, Record) {
        let mut state = scene.state.clone();
        let mut record = Record::start(&state, EMPTY, EMPTY, scene.height);
        let mut run = Run::new(&record, closed(), &scene.set.root());
        run.frontier(&state.frontier_without(spent(&scene.txs)));
        // The tree as the run has it: without the outputs it makes.
        let mut tree = state.clone();
        let mut entry = 3;
        for (t, tx) in scene.txs.iter().enumerate() {
            run.head(tx);
            for input in &tx.inputs {
                run.input(input, &tree.path(input.position), 1, &scene.set.at(entry));
                tree.set(input.position, EMPTY);
                state.set(input.position, EMPTY);
                entry += 1;
            }
            for output in &tx.outputs {
                run.output(output, &key_hash(&key(9)));
                state.insert(output, scene.height);
            }
            change(&mut run, t);
        }
        run.settle();
        // The record by the ledger's rules, where they take the
        // transactions at all.
        let mut applied = scene.state.clone();
        if scene.txs.iter().all(|tx| record.apply(&mut applied, tx).is_ok()) {
            assert_eq!(applied.root(), state.root());
        }
        (run, record)
    }

    /// Whether the run's rows meet the constraints, with `public` said
    /// of them if not what they are of. Where the build is optimized a
    /// proof is made as well, and verified against what is said: it
    /// verifies when the rows hold and not otherwise.
    fn proves(run: Run, public: Option<&[u32]>) -> bool {
        shown(run.finish(128), public)
    }

    /// [`proves`], of a run's rows as they are finished.
    fn shown((rows, program, made): (Vec<[u32; INPUTS]>, Vec<u32>, Vec<u32>), public: Option<&[u32]>) -> bool {
        let said = public.unwrap_or(&made);
        let held = holds(&rows, &program, said);
        if !cfg!(debug_assertions) {
            let mut p = prove_rows(&rows, program, made.clone(), |m| Params::plain(m, 1, 4, 4));
            p.public = said.to_vec();
            assert_eq!(p.verifies(), held, "a proof verifies when its rows hold");
        }
        held
    }

    /// A transaction that says conditions are on two of its outputs
    /// and makes one is not ended by another's beginning: the output
    /// it made is nobody's to choose.
    #[test]
    fn a_transaction_does_not_end_with_outputs_owed() {
        use crate::conditions::{Cond, Policy, PolicyInput, Shown, covered};
        let mine = key_hash(&key(0));
        let thief = key_hash(&key(7));
        let fixed = [Output::to(&mine, 20, [1; MEMO]), Output::to(&mine, 40, [2; MEMO])];
        let policy = Policy(vec![vec![Cond::Outputs { count: 2, digest: covered(&fixed) }]]);
        let mut tree = Outputs::default();
        let position = tree.insert(&Output::to(&policy.root(), 60, [4; MEMO]), 90);
        let input = PolicyInput {
            amount: 60,
            memo: [4; MEMO],
            created: 90,
            position,
            conds: policy.0[0].clone(),
            index: 0,
            siblings: policy.path(0),
            shown: vec![Shown::Nothing],
            state: 0,
        };
        let set = Set(vec![[5u8; 32]]);
        let stolen = Output::to(&thief, 60, [9; MEMO]);
        let tx =
            Transaction { inputs: vec![], outputs: vec![stolen], ops: vec![], policy: vec![input.clone()], covered: 2 };
        let outputs = tree.clone();
        let mut start = Record::start(&outputs, EMPTY, EMPTY, 100);
        // The ledger's rules refuse it.
        assert!(start.apply(&mut tree.clone(), &tx).is_err());
        let start = Record::start(&outputs, EMPTY, EMPTY, 100);
        let mut run = Run::new(&start, closed(), &set.root());
        run.head_saying(&tx, words(&covered(&fixed)));
        run.frontier(&outputs.frontier_without([position]));
        run.policy_input(&input, &outputs.path(position), &[]);
        run.output(&stolen, &thief);
        run.head(&Transaction::default());
        let (rows, program, public) = run.finish(128);
        assert!(!holds(&rows, &program, &public));
    }

    /// A row is of one kind: one of three, a bit in each word of its
    /// kind, would be held to no rule two of them share, and here
    /// would leave an operation on a name out of what the block
    /// carries.
    #[test]
    fn a_row_of_three_kinds_is_refused() {
        use crate::registry::{Op, commit, name_hash};
        let outputs = Outputs::default();
        let set = Set(vec![[5u8; 32]]);
        let op = Op::Commit { commit: commit(&name_hash("dave"), &[1; 32], &[2; 32]), memo: [5; MEMO] };
        let tx = Transaction { inputs: vec![], outputs: vec![], ops: vec![op.clone()], policy: vec![], covered: 0 };
        let start = Record::start(&outputs, EMPTY, EMPTY, 100);
        let mut run = Run::new(&start, closed(), &set.root());
        run.head(&tx);
        let opw = words(&op.digest());
        let block = Run::pair(&run.state.body, &opw);
        run.push_multi(&[PAD, OPBODY, SETL], DOM_BODY_OP, block, |s, out| {
            (s.body, s.counts[1], s.hold) = (out, s.counts[1].wrapping_sub(1), opw);
            (s.v, s.w, s.pos, s.cnt, s.stage) = ([0; 8], [0; 8], s.next0, 0, 1);
        });
        run.head(&Transaction::default());
        let (rows, program, public) = run.finish(128);
        assert!(!holds(&rows, &program, &public));
    }

    #[test]
    fn the_row_is_what_it_was_planned_as() {
        let c = circuit();
        println!(
            "{} words, {} constraints, {} products, {} terms",
            c.cols,
            c.constraints.len(),
            c.products.len(),
            c.terms()
        );
        assert_eq!((c.log_cols, c.log_constraints, c.program_width(), c.publics), (10, 11, PROGRAM, PUBLIC));
        assert!(
            c.cols <= 1024 && c.constraints.len() <= 2048 && c.products.len() == 2 * CHAINED + FIXED && !c.has_bus()
        );
    }

    #[test]
    fn a_run_of_payments_is_proven_to_be_its_record() {
        let scene = a_scene();
        let (run, record) = run_of(&scene, |_, _| {});
        // Three inputs; three outputs, the second joined with the first;
        // and the two walks that bring them into the root, from positions
        // of one bit and of three.
        assert_eq!(run.len(), 1 + 2 + 3 * 110 + (6 + 8 + 6) + (1 + 83 + 1 + 85 + 1));
        // What the run says it is of is what the ledger's rules make of
        // the transactions.
        let last = whole(&scene.txs[1]);
        let start = Record::start(&scene.state, EMPTY, EMPTY, scene.height);
        let expect = public(&start, &record, &scene.set.root(), [closed(), last], [counted([0; 4]); 2], [[0; 2]; 2]);
        let (_, _, own) = run_of(&scene, |_, _| {}).0.finish(128);
        assert_eq!(own, expect);
        assert!(proves(run, Some(&expect)));
        // And of nothing else: another root after, another sum, another
        // signed set.
        for word in [100 + 3, 100 + 48, 88 + 3, 96] {
            let mut other = expect.clone();
            other[word] ^= 1;
            assert!(!proves(run_of(&scene, |_, _| {}).0, Some(&other)), "word {word}");
        }
    }

    #[test]
    fn rows_that_break_a_rule_are_not_proven() {
        let scene = a_scene();
        // A word of a row changed after the run was made, one row at a
        // time: an amount where it is committed to, a sibling on the way
        // to the signed set and on the way to the state, a counter, the
        // id an entry is looked up under.
        // And where the second output joins the first: the chain of
        // nodes held, and the node joined.
        let places: [(usize, usize); 8] = [
            (3 + 24, 8 + 8),
            (3 + 5, 8 + 9),
            (3 + 40, 8 + 12),
            (3 + 60, FRONT + 1 + KINDS + 77),
            (5, 8),
            (3 + 27, 8 + 14),
            (232, 8 + 3),
            (233, 8 + 12),
        ];
        for (row, word) in places {
            let (mut run, _) = run_of(&scene, |_, _| {});
            run.rows[row][word] ^= 1;
            assert!(!proves(run, None), "row {row} word {word}");
        }
        // Nodes told that are not the tree's.
        let mut state = scene.state.clone();
        let record = Record::start(&state, EMPTY, EMPTY, scene.height);
        let mut run = Run::new(&record, closed(), &scene.set.root());
        let mut nodes = state.frontier_without(spent(&scene.txs));
        nodes[0][0] ^= 1;
        run.frontier(&nodes);
        let mut entry = 3;
        for tx in &scene.txs {
            run.head(tx);
            for input in &tx.inputs {
                run.input(input, &state.path(input.position), 1, &scene.set.at(entry));
                state.set(input.position, EMPTY);
                entry += 1;
            }
            tx.outputs.iter().for_each(|output| run.output(output, &key_hash(&key(9))));
        }
        assert!(!proves(run, None));
        // An input whose entry is not in the set; an output that is not
        // in the state where it says; a key that is not the output's.
        let mut other = a_scene();
        other.set.0[3] = [9; 32];
        assert!(!proves(run_of(&other, |_, _| {}).0, None));
        let mut other = a_scene();
        other.txs[0].inputs[0].created = 7;
        let id = scene.txs[0].id();
        assert_eq!(other.txs[0].id(), id);
        assert!(!proves(run_of(&other, |_, _| {}).0, None));
        let mut other = a_scene();
        other.txs[1].inputs[0].key = key(7);
        other.set.0[5] = crate::signature::entry(&key(7), &other.txs[1].id(), 1);
        assert!(!proves(run_of(&other, |_, _| {}).0, None));
    }

    /// A block at height 400 with a payment that also commits to a
    /// name, reveals one committed the block before and updates a
    /// registered one, and a sweep of a commitment long unrevealed.
    struct Named {
        outputs: Outputs,
        names: crate::registry::Names,
        tx: Transaction,
        payer: Input,
        /// The revealed name's commitment: its salt, memo, height and
        /// position.
        revealed: (Digest, Memo, u32, u64),
        /// The updated name's record before, and its owner's key.
        old: (crate::registry::Record, PublicKey),
        /// The swept commitment, its memo, height and position.
        stale: (Digest, Memo, u32, u64),
        set: Set,
    }

    const HEIGHT: u32 = 400;

    fn named() -> Named {
        named_made(HEIGHT - 1, 100)
    }

    /// [`named`], with the revealed commitment and the swept one made at
    /// these heights.
    fn named_made(revealed_at: u32, stale_at: u32) -> Named {
        use crate::registry::{Names, Op, Record as Name, commit, commit_output, name_hash, update_message};
        let (mut outputs, mut names) = (Outputs::default(), Names::default());
        let payer_out = Output::to(&key_hash(&key(0)), 100, [1; MEMO]);
        let payer =
            Input { key: key(0), amount: 100, memo: [1; MEMO], created: 7, position: outputs.insert(&payer_out, 7) };
        let alice = Name { name: "alice".into(), owner: key_hash(&key(1)), value: [5; 32], memo: [6; 32] };
        let salt = [9; 32];
        let committed = commit(&name_hash("alice"), &salt, &alice.owner);
        let revealed =
            (salt, [2; MEMO], revealed_at, outputs.insert(&commit_output(&committed, [2; MEMO]), revealed_at));
        let old_commit = commit(&name_hash("carol"), &[8; 32], &[0; 32]);
        let stale = (old_commit, [3; MEMO], stale_at, outputs.insert(&commit_output(&old_commit, [3; MEMO]), stale_at));
        let bob = Name { name: "bob".into(), owner: key_hash(&key(2)), value: [1; 32], memo: [2; 32] };
        names.set(bob.clone());
        let bob_now = Name { owner: key_hash(&key(3)), value: [7; 32], ..bob.clone() };
        let tx = Transaction {
            inputs: vec![payer.clone()],
            outputs: vec![Output::to(&key_hash(&key(0)), 100, [4; MEMO])],
            ops: vec![
                Op::Commit { commit: commit(&name_hash("dave"), &[1; 32], &[2; 32]), memo: [5; MEMO] },
                Op::Reveal { record: alice, salt, position: revealed.3 },
                Op::Update { record: bob_now.clone() },
            ],
            policy: vec![],
            covered: 0,
        };
        let entries = vec![
            [5u8; 32],
            crate::signature::entry(&key(0), &tx.id(), 1),
            crate::signature::entry(&key(2), &update_message(&bob_now), 0),
        ];
        Named { outputs, names, tx, payer, revealed, old: (bob, key(2)), stale, set: Set(entries) }
    }

    /// The run of a named block, as the prover would make it: the
    /// payment, which carries the operations, then the operations, then
    /// the sweep.
    fn named_run(n: &Named, sweep: bool) -> (Run, Record, Record) {
        use crate::registry::{Op, key as place, name_hash};
        let (mut outputs, mut names) = (n.outputs.clone(), n.names.clone());
        let start = Record::start(&outputs, EMPTY, EMPTY, HEIGHT).on(&names);
        let mut run = Run::new(&start, closed(), &n.set.root());
        // What the run spends: the payment's input, the revealed
        // commitment and the swept one.
        let reveals = n.tx.ops.iter().filter_map(|op| match op {
            Op::Reveal { position, .. } => Some(*position),
            _ => None,
        });
        let gone: Vec<u64> = [n.payer.position].into_iter().chain(reveals).chain(sweep.then_some(n.stale.3)).collect();
        run.frontier(&outputs.frontier_without(gone));
        run.head(&n.tx);
        run.input(&n.payer, &outputs.path(n.payer.position), 1, &n.set.at(1));
        outputs.set(n.payer.position, EMPTY);
        // What the run makes is in the root at its end: its paths are
        // the tree's without.
        run.output(&n.tx.outputs[0], &key_hash(&key(0)));
        for op in &n.tx.ops {
            run.carried(&op.digest());
        }
        for op in &n.tx.ops {
            match op {
                Op::Commit { commit, memo } => run.commit(commit, memo),
                Op::Reveal { record, salt, position } => {
                    let (_, memo, made, _) = n.revealed;
                    let at = place(&name_hash(&record.name));
                    run.reveal(record, salt, &memo, made, *position, &outputs.path(*position), &names.path(at));
                    outputs.set(*position, EMPTY);
                    names.set(record.clone());
                }
                Op::Update { record } => {
                    let at = place(&name_hash(&record.name));
                    run.update(record, &n.old.0, &n.old.1, 0, &n.set.at(2), &names.path(at));
                    names.set(record.clone());
                }
            }
        }
        if sweep {
            let (commit, memo, made, position) = n.stale;
            run.sweep(&commit, &memo, made, position, &outputs.path(position));
        }
        run.settle();
        // The record by the ledger's rules, where they take the block.
        let mut record = start;
        let (mut outputs, mut names) = (n.outputs.clone(), n.names.clone());
        let done = record.apply(&mut outputs, &n.tx).is_ok()
            && n.tx.ops.iter().all(|op| record.op(&mut outputs, &mut names, op).is_ok());
        if done && sweep {
            let _ = record.sweep(&mut outputs, n.stale.3);
        }
        (run, start, record)
    }

    #[test]
    fn names_are_committed_revealed_updated_and_swept() {
        let n = named();
        let (run, start, record) = named_run(&n, true);
        println!("{} rows", run.len());
        let counts = [counted([0; 4]), counted([1; 4])];
        let expect = public(&start, &record, &n.set.root(), [closed(), whole(&n.tx)], counts, [[0; 2], [!0; 2]]);
        // The operations done are those the payment carried.
        assert_eq!(record.ops[1], record.done[1]);
        assert_ne!(record.ops[1], EMPTY);
        assert_ne!(record.names[0], record.names[1]);
        assert!(proves(run, Some(&expect)));
        // Not of another registry after, nor of other counts, nor of
        // other operations done.
        for word in [100 + 4 * 14, 100 + 4 * 16 + 1, 100 + 4 * 19] {
            let mut other = expect.clone();
            other[word] ^= 1;
            assert!(!proves(named_run(&n, true).0, Some(&other)), "word {word}");
        }
    }

    /// What is signed spends one output: a transaction made to spend
    /// one of two outputs of the same key and amount is not rows that
    /// hold when the other is the leaf walked.
    #[test]
    fn a_signature_spends_the_output_it_names() {
        let mine = key_hash(&key(0));
        let mut tree = Outputs::default();
        let places = [0, 1].map(|_| tree.insert(&Output::to(&mine, 60, [4; MEMO]), 90));
        let input = Input { key: key(0), amount: 60, memo: [4; MEMO], created: 90, position: places[0] };
        let out = Output::to(&key_hash(&key(7)), 60, [9; MEMO]);
        let tx = Transaction { inputs: vec![input], outputs: vec![out], ops: vec![], policy: vec![], covered: 0 };
        let set = Set(vec![[5u8; 32], crate::signature::entry(&key(0), &tx.id(), 1)]);
        let spent_as = |walked: u64| {
            let start = Record::start(&tree, EMPTY, EMPTY, 100);
            let mut run = Run::new(&start, closed(), &set.root());
            run.frontier(&tree.frontier_without([walked]));
            run.head(&tx);
            run.input_at(&tx.inputs[0], &tree.path(walked), 1, &set.at(1), walked);
            run.output(&out, &key_hash(&key(7)));
            run.settle();
            let (rows, program, public) = run.finish(128);
            holds(&rows, &program, &public)
        };
        assert!(spent_as(places[0]));
        assert!(!spent_as(places[1]));
    }

    /// A reveal that spends its commitment registers its name: rows
    /// that stop at the spend, and go on to something else, are not
    /// rows that hold. (Whoever saw a reveal waiting could else spend
    /// its commitment in a block and register nothing.)
    #[test]
    fn a_reveal_does_not_stop_at_its_spend() {
        use crate::registry::Op;
        let n = named();
        let found = n.tx.ops.iter().find_map(|op| match op {
            Op::Reveal { record, salt, position } => Some((record, salt, *position)),
            _ => None,
        });
        let (record, salt, position) = found.expect("a reveal among them");
        let (_, memo, made, _) = n.revealed;
        let stopped = |then: &dyn Fn(&mut Run)| {
            let start = Record::start(&n.outputs, EMPTY, EMPTY, HEIGHT).on(&n.names);
            let mut run = Run::new(&start, closed(), &n.set.root());
            run.frontier(&n.outputs.frontier_without([position]));
            run.reveal_spend(record, salt, &memo, made, position, &n.outputs.path(position));
            then(&mut run);
            let (rows, program, public) = run.finish(128);
            holds(&rows, &program, &public)
        };
        // Stopped there; and gone on to a transaction's head.
        assert!(!stopped(&|_| {}));
        assert!(!stopped(&|run| run.head(&Transaction::default())));
    }

    /// Operations on names are done after every transaction, and sweeps
    /// after them: nothing else is rows that are proven.
    #[test]
    fn operations_are_done_after_the_transactions() {
        use crate::registry::Op;
        let n = named();
        let Op::Commit { commit, memo } = &n.tx.ops[0] else { unreachable!() };
        // The payment, its operations carried; `then` goes on from there.
        let made = |early: bool, swept: bool, then: &dyn Fn(&mut Run, &Outputs)| {
            let mut outputs = n.outputs.clone();
            let start = Record::start(&outputs, EMPTY, EMPTY, HEIGHT).on(&n.names);
            let mut run = Run::new(&start, closed(), &n.set.root());
            let gone = [n.payer.position].into_iter().chain(swept.then_some(n.stale.3));
            run.frontier(&outputs.frontier_without(gone));
            run.head(&n.tx);
            run.input(&n.payer, &outputs.path(n.payer.position), 1, &n.set.at(1));
            outputs.set(n.payer.position, EMPTY);
            if early {
                // The commitment done while the payment's output is
                // still to come.
                run.commit(commit, memo);
            }
            run.output(&n.tx.outputs[0], &key_hash(&key(0)));
            n.tx.ops.iter().for_each(|op| run.carried(&op.digest()));
            then(&mut run, &outputs);
            proves(run, None)
        };
        let sweep = |run: &mut Run, outputs: &Outputs| {
            let (stale, memo, made, position) = n.stale;
            run.sweep(&stale, &memo, made, position, &outputs.path(position));
        };
        assert!(made(false, false, &|run, _| run.commit(commit, memo)));
        assert!(made(false, true, &|run, outputs| {
            run.commit(commit, memo);
            sweep(run, outputs);
        }));
        // In the middle of a transaction.
        assert!(!made(true, false, &|_, _| {}));
        // A transaction after an operation is done; after a sweep.
        let empty = Transaction::default();
        assert!(made(false, false, &|run, _| run.head(&empty)));
        assert!(!made(false, false, &|run, _| {
            run.commit(commit, memo);
            run.head(&empty);
        }));
        assert!(!made(false, true, &|run, outputs| {
            sweep(run, outputs);
            run.head(&empty);
        }));
        // An operation after a sweep.
        assert!(!made(false, true, &|run, outputs| {
            sweep(run, outputs);
            run.commit(commit, memo);
        }));
    }

    #[test]
    fn names_rules_are_the_rows_too() {
        use crate::registry::{Op, commit};
        let made = |revealed_at: u32, stale_at: u32, change: &dyn Fn(&mut Named), sweep: bool| {
            let mut n = named_made(revealed_at, stale_at);
            change(&mut n);
            let (run, _, record) = named_run(&n, sweep);
            // Whether the rows are proven, and whether the ledger's rules
            // took the block (the registry moved).
            (proves(run, None), record.names[0] != record.names[1])
        };
        let run = |change: &dyn Fn(&mut Named), sweep: bool| made(HEIGHT - 1, 100, change, sweep).0;
        assert!(run(&|_| {}, false));
        // The window: a commitment made 1 to 288 blocks ago, by the rows
        // as by the rules.
        for (at, ok) in
            [(HEIGHT, false), (HEIGHT - 1, true), (HEIGHT - 288, true), (HEIGHT - 289, false), (HEIGHT + 1, false)]
        {
            assert_eq!(made(at, 100, &|_| {}, false), (ok, ok), "made at {at}");
        }
        // A commitment said to be made when it was not; one of another
        // salt; a name that is taken.
        assert!(!run(&|n| n.revealed.2 -= 1, false));
        assert!(!run(
            &|n| {
                let Op::Reveal { salt, .. } = &mut n.tx.ops[1] else { unreachable!() };
                salt[0] ^= 1;
            },
            false
        ));
        assert!(!run(
            &|n| {
                let Op::Reveal { record, .. } = &n.tx.ops[1] else { unreachable!() };
                n.names.set(crate::registry::Record { owner: [1; 32], ..record.clone() });
            },
            false
        ));
        // An update the owner's key did not sign; an update of a record
        // that is not the name's.
        assert!(!run(&|n| n.set.0[2] = [7; 32], false));
        assert!(!run(&|n| n.old.0.value[0] ^= 1, false));
        assert!(!run(&|n| n.old.1 = key(5), false));
        // A sweep: only of a commitment out of its time.
        for (at, ok) in [(100, true), (HEIGHT - 289, true), (HEIGHT - 288, false), (HEIGHT - 1, false)] {
            assert_eq!(made(HEIGHT - 1, at, &|_| {}, true).0, ok, "made at {at}");
        }
        // A second commitment in the block: one too many.
        assert!(!run(
            &|n| {
                let extra = Op::Commit { commit: commit(&[1; 32], &[2; 32], &[3; 32]), memo: [0; MEMO] };
                n.tx.ops.insert(1, extra);
                n.set.0[1] = crate::signature::entry(&key(0), &n.tx.id(), 1);
            },
            false
        ));
    }

    /// A block that spends a policy's output: two of three keys, a hash
    /// lock, a height and an age, all on one leaf of two.
    struct Guarded {
        outputs: Outputs,
        tx: Transaction,
        set: Set,
        height: u32,
    }

    fn guarded(change: &dyn Fn(&mut crate::conditions::PolicyInput, &mut Vec<Digest>, &mut u32)) -> Guarded {
        use crate::conditions::{Cond, Policy, PolicyInput, Shown, hash_lock};
        let keys: Vec<PublicKey> = (0..3).map(key).collect();
        let hashes: Vec<Digest> = keys.iter().map(key_hash).collect();
        let secret = [9u8; 32];
        let conds = vec![
            Cond::Thresh { m: 2, keys: hashes.clone() },
            Cond::Hash(hash_lock(&secret)),
            Cond::After(100),
            Cond::Older(10),
        ];
        let policy = Policy(vec![vec![Cond::After(1_000_000)], conds.clone()]);
        let mut outputs = Outputs::default();
        let memo = [3; MEMO];
        let position = outputs.insert(&Output::to(&policy.root(), 70, memo), 95);
        let mut input = PolicyInput {
            amount: 70,
            memo,
            created: 95,
            position,
            conds,
            index: 1,
            siblings: policy.path(1),
            shown: vec![
                Shown::Signers(vec![Some((keys[0], 1)), None, Some((keys[2], 0))]),
                Shown::Preimage(secret),
                Shown::Nothing,
                Shown::Nothing,
            ],
            state: 0,
        };
        let mut height = 105;
        let mut entries = vec![[5u8; 32]];
        // What is changed here is changed before anything is signed.
        let mut tx = Transaction {
            inputs: vec![],
            outputs: vec![Output::to(&hashes[0], 70, [0; MEMO])],
            ops: vec![],
            policy: vec![input.clone()],
            covered: 0,
        };
        entries.push(crate::signature::entry(&keys[0], &tx.id(), 1));
        entries.push(crate::signature::entry(&keys[2], &tx.id(), 0));
        change(&mut input, &mut entries, &mut height);
        tx.policy[0] = input;
        Guarded { outputs, tx, set: Set(entries), height }
    }

    /// The run of a guarded block, and what the ledger's rules make of
    /// it (nothing, if they refuse it).
    fn guarded_run(g: &Guarded) -> (Run, Record, Option<Record>) {
        let mut outputs = g.outputs.clone();
        let start = Record::start(&outputs, EMPTY, EMPTY, g.height);
        let mut run = Run::new(&start, closed(), &g.set.root());
        run.head(&g.tx);
        let input = &g.tx.policy[0];
        run.frontier(&outputs.frontier_without([input.position]));
        run.policy_input(input, &outputs.path(input.position), &[g.set.at(1), g.set.at(2)]);
        outputs.set(input.position, EMPTY);
        run.output(&g.tx.outputs[0], &key_hash(&key(0)));
        run.settle();
        let mut record = start;
        let applied = record.apply(&mut g.outputs.clone(), &g.tx).is_ok();
        (run, start, applied.then_some(record))
    }

    #[test]
    fn a_policy_s_output_is_spent_by_its_conditions() {
        use crate::conditions::{Cond, Shown};
        let g = guarded(&|_, _, _| {});
        let (run, start, record) = guarded_run(&g);
        let record = record.expect("the rules take it");
        let expect =
            public(&start, &record, &g.set.root(), [closed(), whole(&g.tx)], [counted([0; 4]); 2], [[0; 2]; 2]);
        assert!(proves(run, Some(&expect)));
        // Each condition, not met: by the rows as by the rules.
        let refused = |change: &dyn Fn(&mut crate::conditions::PolicyInput, &mut Vec<Digest>, &mut u32)| {
            let g = guarded(change);
            let (run, _, record) = guarded_run(&g);
            // The rules know nothing of signatures: where only those fail
            // they take the block and the rows do not.
            (proves(run, None), record.is_some())
        };
        assert_eq!(refused(&|_, _, _| {}), (true, true));
        assert_eq!(refused(&|i, _, _| i.shown[1] = Shown::Preimage([8; 32])), (false, false));
        assert_eq!(refused(&|_, _, height| *height = 99), (false, false));
        assert_eq!(refused(&|_, _, height| *height = 104), (false, false));
        // A signature that is not in the set; a signer that is not the
        // key listed; one signer of the two; all three.
        assert_eq!(refused(&|_, entries, _| entries[2] = [1; 32]), (false, true));
        assert!(!refused(&|i, _, _| i.shown[0] = Shown::Signers(vec![Some((key(1), 1)), None, Some((key(2), 0))])).0);
        assert!(!refused(&|i, _, _| i.shown[0] = Shown::Signers(vec![Some((key(0), 1)), None, None])).0);
        // Another leaf's place, a leaf of other conditions, an output
        // said to be older than it is.
        assert!(!refused(&|i, _, _| i.index = 0).0);
        assert!(!refused(&|i, _, _| i.conds[2] = Cond::After(1)).0);
        assert!(!refused(&|i, _, _| i.created = 90).0);
    }

    /// A channel's output: one leaf lets its two keys replace it by a
    /// later state, whatever output of the channel it is; another lets
    /// anyone spend it, once it is old enough, into one output fixed
    /// when it was made.
    struct Channel {
        outputs: Outputs,
        policy: crate::conditions::Policy,
        channel: Digest,
        settle: Output,
        position: u64,
    }

    fn channel() -> Channel {
        use crate::conditions::{Cond, Policy, covered};
        let keys = vec![key_hash(&key(0)), key_hash(&key(1))];
        let channel = [0xC4; 32];
        let settle = Output::to(&key_hash(&key(0)), 60, [1; MEMO]);
        let policy = Policy(vec![
            vec![Cond::State(4), Cond::Rebind { m: 2, keys, channel }],
            vec![Cond::Outputs { count: 1, digest: covered(&[settle]) }, Cond::Older(5)],
        ]);
        let mut outputs = Outputs::default();
        let position = outputs.insert(&Output::to(&policy.root(), 60, [2; MEMO]), 90);
        Channel { outputs, policy, channel, settle, position }
    }

    /// Whether a spend of the channel's output by `leaf`, in a
    /// transaction of these outputs with `covered` of them covered, is
    /// proven at height 100; and whether the ledger's rules take it.
    /// `signs` are the leaves the two keys sign with, and what they sign
    /// if not what the rules say.
    #[allow(clippy::type_complexity)]
    fn spends(
        c: &Channel,
        leaf: usize,
        state: u32,
        outs: Vec<(Output, Digest)>,
        covered: u32,
        signs: Option<([u64; 2], Option<Digest>)>,
    ) -> (bool, bool) {
        let (run, tx) = spend_run(c, leaf, state, outs, covered, signs);
        let mut record = Record::start(&c.outputs, EMPTY, EMPTY, 100);
        (proves(run, None), record.apply(&mut c.outputs.clone(), &tx).is_ok())
    }

    /// The run of such a spend, and its transaction.
    #[allow(clippy::type_complexity)]
    fn spend_run(
        c: &Channel,
        leaf: usize,
        state: u32,
        outs: Vec<(Output, Digest)>,
        covered: u32,
        signs: Option<([u64; 2], Option<Digest>)>,
    ) -> (Run, Transaction) {
        use crate::conditions::{PolicyInput, Shown, rebind_message};
        let conds = c.policy.0[leaf].clone();
        let owners: Vec<Digest> = outs.iter().map(|o| o.1).collect();
        let outs: Vec<Output> = outs.into_iter().map(|o| o.0).collect();
        let mut tx = Transaction { inputs: vec![], outputs: outs, ops: vec![], policy: vec![], covered };
        let shown = match signs {
            Some((leaves, _)) => {
                vec![Shown::Nothing, Shown::Signers(vec![Some((key(0), leaves[0])), Some((key(1), leaves[1]))])]
            }
            None => vec![Shown::Nothing, Shown::Nothing],
        };
        let input = PolicyInput {
            amount: 60,
            memo: [2; MEMO],
            created: 90,
            position: c.position,
            conds,
            index: leaf,
            siblings: c.policy.path(leaf),
            shown,
            state,
        };
        tx.policy.push(input.clone());
        // The signed set: the two keys' signatures of the channel's
        // message for this state and these covered outputs.
        let mut entries = vec![[5u8; 32]];
        if let Some((leaves, other)) = signs {
            let cover = tx.cover().map_or(EMPTY, |(_, digest)| digest);
            let message = other.unwrap_or(rebind_message(&c.channel, &cover, state));
            entries.extend((0..2).map(|k| crate::signature::entry(&key(k as u8), &message, leaves[k])));
        }
        let set = Set(entries);
        let mut outputs = c.outputs.clone();
        let start = Record::start(&outputs, EMPTY, EMPTY, 100);
        let mut run = Run::new(&start, closed(), &set.root());
        run.head(&tx);
        let places: Vec<Signed> = (1..set.0.len()).map(|i| set.at(i as u64)).collect();
        run.frontier(&outputs.frontier_without([c.position]));
        run.policy_input(&input, &outputs.path(c.position), &places);
        outputs.set(c.position, EMPTY);
        for (output, owner) in tx.outputs.iter().zip(&owners) {
            run.output(output, owner);
            outputs.insert(output, 100);
        }
        run.settle();
        (run, tx)
    }

    #[test]
    fn a_covenant_fixes_the_outputs() {
        let c = channel();
        let mine = key_hash(&key(0));
        let other = Output::to(&mine, 60, [9; MEMO]);
        // Into the output fixed.
        assert_eq!(spends(&c, 1, 0, vec![(c.settle, mine)], 1, None), (true, true));
        // Into another output; with none said to be covered; into the
        // fixed one's key and memo but less, and the rest elsewhere.
        assert_eq!(spends(&c, 1, 0, vec![(other, mine)], 1, None), (false, false));
        assert_eq!(spends(&c, 1, 0, vec![(c.settle, mine)], 0, None), (false, false));
        let part = Output::to(&mine, 30, [1; MEMO]);
        let rest = Output::to(&mine, 30, [9; MEMO]);
        assert_eq!(spends(&c, 1, 0, vec![(part, mine), (rest, mine)], 1, None), (false, false));
    }

    /// A transaction that spends a policy's output may lie across runs,
    /// cut anywhere between its parts: the outputs its conditions are
    /// on, those met and those still to come, are the next run's from
    /// the one before.
    #[test]
    fn a_covenant_s_outputs_may_lie_across_runs() {
        use crate::conditions::{Cond, Policy, PolicyInput, Shown, covered};
        let mine = key_hash(&key(0));
        let fixed = [Output::to(&mine, 20, [1; MEMO]), Output::to(&mine, 25, [2; MEMO])];
        let free = Output::to(&mine, 10, [3; MEMO]);
        let policy = Policy(vec![vec![Cond::Outputs { count: 2, digest: covered(&fixed) }]]);
        let mut tree = Outputs::default();
        let position = tree.insert(&Output::to(&policy.root(), 60, [4; MEMO]), 90);
        let input = PolicyInput {
            amount: 60,
            memo: [4; MEMO],
            created: 90,
            position,
            conds: policy.0[0].clone(),
            index: 0,
            siblings: policy.path(0),
            shown: vec![Shown::Nothing],
            state: 0,
        };
        let set = Set(vec![[5u8; 32]]);
        // The transaction's outputs as it says them, and as the runs
        // make them; the first run ends after `cut` of them.
        let made = |cut: usize, second: &Output| {
            let said = vec![fixed[0], fixed[1], free];
            let tx =
                Transaction { inputs: vec![], outputs: said, ops: vec![], policy: vec![input.clone()], covered: 2 };
            let makes = [fixed[0], *second, free];
            let mut outputs = tree.clone();
            let start = Record::start(&outputs, EMPTY, EMPTY, 100);
            let mut run = Run::new(&start, closed(), &set.root());
            run.head(&tx);
            run.frontier(&outputs.frontier_without([position]));
            run.policy_input(&input, &outputs.path(position), &[]);
            outputs.set(position, EMPTY);
            for output in &makes[..cut] {
                run.output(output, &mine);
                outputs.insert(output, 100);
            }
            run.settle();
            let mut next = Run::after(&run);
            next.frontier(&outputs.frontier_without(std::iter::empty()));
            for output in &makes[cut..] {
                next.output(output, &mine);
            }
            next.settle();
            // The second begins as the first ended.
            let (first, then) = (run.finish(128), next.finish(128));
            let ins = 4 * (CHAINED + FIXED);
            assert_eq!(first.2[ins..], then.2[..4 * CHAINED]);
            shown(first, None) & shown(then, None)
        };
        for cut in 0..=3 {
            assert!(made(cut, &fixed[1]), "cut after {cut} outputs");
            // Another output where the second fixed one is to be.
            assert!(!made(cut, &Output::to(&mine, 25, [9; MEMO])), "cut after {cut} outputs, another output");
        }
    }

    #[test]
    fn a_channel_s_keys_sign_a_state_not_a_transaction() {
        use crate::conditions::{covered, rebind_message};
        let c = channel();
        let root = c.policy.root();
        let next = (Output::to(&root, 60, [7; MEMO]), root);
        // State 7 replaces the output (it is above 4): both keys signed
        // the channel, the state and the output it goes to, each with its
        // seventh leaf.
        assert_eq!(spends(&c, 0, 7, vec![next], 1, Some(([7, 7], None))), (true, true));
        // A state that is not above; a signature with another leaf than
        // the state; signatures of another state, or of something else;
        // no output covered.
        assert_eq!(spends(&c, 0, 4, vec![next], 1, Some(([4, 4], None))), (false, false));
        assert_eq!(spends(&c, 0, 7, vec![next], 1, Some(([7, 6], None))), (false, false));
        let wrong = rebind_message(&c.channel, &covered(&[next.0]), 8);
        assert!(!spends(&c, 0, 7, vec![next], 1, Some(([7, 7], Some(wrong)))).0);
        assert!(!spends(&c, 0, 7, vec![next], 1, Some(([7, 7], Some([3; 32])))).0);
        assert_eq!(spends(&c, 0, 7, vec![next], 0, Some(([7, 7], None))), (false, false));
        // The signatures do not serve for another output than they name.
        let mine = key_hash(&key(1));
        let elsewhere = (Output::to(&mine, 60, [7; MEMO]), mine);
        let signed_for = rebind_message(&c.channel, &covered(&[next.0]), 7);
        assert!(!spends(&c, 0, 7, vec![elsewhere], 1, Some(([7, 7], Some(signed_for)))).0);
    }

    /// The elements public words are.
    fn elements(words: &[u32]) -> Vec<F> {
        words.chunks(4).map(|w| F(w.iter().rev().fold(0, |x, w| x << 32 | *w as u128))).collect()
    }

    /// A computation that verifies two runs' proofs and states what they
    /// are together.
    fn joined(runs: &[Proved; 2], c: &Circuit) -> Shared {
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let (program, first) = runs[0].verify_into(&cx, c, &mut reader).expect("the proof verifies");
        let (again, second) = runs[1].verify_into(&cx, c, &mut reader).expect("the proof verifies");
        reader.settle(&[c]);
        assert!(program[0].is(&again[0]) && program[1].is(&again[1]));
        cx.state(&[program, join(&first, &second)].concat());
        cx
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn two_runs_are_joined_and_a_transaction_may_lie_across_them() {
        // The scene's payments in two runs, the first ending after the
        // first payment's inputs: its outputs are the second run's.
        let scene = a_scene();
        let mut state = scene.state.clone();
        let start = Record::start(&state, EMPTY, EMPTY, scene.height);
        let mut run = Run::new(&start, closed(), &scene.set.root());
        let mut runs = Vec::new();
        let mut entry = 3;
        // The tree as a run has it: without the outputs it makes.
        let mut tree = state.clone();
        for (t, tx) in scene.txs.iter().enumerate() {
            run.head(tx);
            for input in &tx.inputs {
                run.input(input, &tree.path(input.position), 1, &scene.set.at(entry));
                tree.set(input.position, EMPTY);
                state.set(input.position, EMPTY);
                entry += 1;
            }
            if t == 0 {
                // The second run spends the second payment's input.
                let mut next = Run::after(&run);
                next.frontier(&state.frontier_without(spent(&scene.txs[1..])));
                runs.push(std::mem::replace(&mut run, next));
            }
            for output in &tx.outputs {
                run.output(output, &key_hash(&key(9)));
                state.insert(output, scene.height);
            }
        }
        run.settle();
        runs.push(run);
        let params = |m: usize| Params::plain(m, 1, 4, 4);
        let proved: Vec<Proved> = runs.into_iter().map(|r| prove(r, 512, params)).collect();
        assert!(proved.iter().all(Proved::verifies));
        assert_eq!(proved[0].program, proved[1].program);
        // The first run leaves a transaction in hand: outputs left.
        assert_eq!(proved[0].public[4 * (CHAINED + FIXED) + 4 * 10 + 1], 2);
        let c = circuit();
        let proved: [Proved; 2] = proved.try_into().ok().unwrap();
        let node = crate::proof::prove(joined(&proved, &c), vec![], params);
        assert!(node.holds && node.verifies());
        // Together they are the two payments' record, whole.
        let mut record = start;
        let mut applied = scene.state.clone();
        scene.txs.iter().for_each(|tx| record.apply(&mut applied, tx).unwrap());
        let last = whole(&scene.txs[1]);
        let all = public(&start, &record, &scene.set.root(), [closed(), last], [counted([0; 4]); 2], [[0; 2]; 2]);
        let expect = [crate::alg::halves(&proved[0].program).to_vec(), elements(&all)].concat();
        assert_eq!(node.statement(), crate::alg::statement(&expect));
        // The runs the other way round do not join.
        let [a, b] = proved;
        let cx = joined(&[b, a], &c);
        assert!(!cx.finish().asm.finish(128).holds);
    }

    /// What joining two runs takes, at the chain's parameters.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn joining_timing() {
        let n: usize = std::env::var("PAYMENTS").ok().and_then(|x| x.parse().ok()).unwrap_or(165);
        let params = |m: usize| Params::proven(m, 2, crate::pcs::SECURITY);
        let (first, second) = payments(n, 2);
        let proved = [prove(first, 128, params), prove(second, 128, params)];
        let c = circuit();
        let t = std::time::Instant::now();
        let cx = joined(&proved, &c);
        let compiled = t.elapsed();
        let (hash, ops) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
        let node = crate::proof::prove(cx, vec![], params);
        assert!(node.holds && node.verifies());
        println!(
            "two runs of {n} payments (2^{} elements, {:.2?}, {} KB each) joined: {hash} hash rows, {ops} operations \
             ({} machine rows used), compiled in {compiled:.2?}; 2^{} elements, proven in {:.2?}, {} KB",
            proved[0].params.m,
            proved[0].proving,
            proved[0].proof.size() / 1000,
            node.used,
            node.params.m,
            node.proving,
            node.size() / 1000,
        );
    }

    /// Two runs, one after the other, of `n` payments of two inputs and
    /// two outputs each (or one run of them, and an empty one).
    fn payments(n: usize, runs: usize) -> (Run, Run) {
        let keys: Vec<PublicKey> = (0..8).map(key).collect();
        let mut state = Outputs::default();
        let total = n * runs;
        let owned: Vec<Input> = (0..2 * total)
            .map(|i| {
                let (k, memo) = (&keys[i % 8], [i as u8; MEMO]);
                let position = state.insert(&Output::to(&key_hash(k), 100, memo), 1);
                Input { key: *k, amount: 100, memo, created: 1, position }
            })
            .collect();
        let txs: Vec<Transaction> = (0..total)
            .map(|t| Transaction {
                inputs: owned[2 * t..2 * t + 2].to_vec(),
                outputs: vec![
                    Output::to(&key_hash(&keys[0]), 120, [1; MEMO]),
                    Output::to(&key_hash(&keys[1]), 80, [2; MEMO]),
                ],
                ops: vec![],
                policy: vec![],
                covered: 0,
            })
            .collect();
        let entries = txs.iter().flat_map(|tx| tx.inputs.iter().map(|i| crate::signature::entry(&i.key, &tx.id(), 1)));
        let set = Set(entries.collect());
        let record = Record::start(&state, EMPTY, EMPTY, 2);
        let mut run = Run::new(&record, closed(), &set.root());
        run.frontier(&state.frontier_without(spent(&txs[..n])));
        // The tree as a run has it: without the outputs it makes.
        let mut tree = state.clone();
        let mut done = Vec::new();
        for (t, tx) in txs.iter().enumerate() {
            if t == n {
                run.settle();
                let mut next = Run::after(&run);
                next.frontier(&state.frontier_without(spent(&txs[n..])));
                done.push(std::mem::replace(&mut run, next));
                tree = state.clone();
            }
            run.head(tx);
            for (i, input) in tx.inputs.iter().enumerate() {
                run.input(input, &tree.path(input.position), 1, &set.at((2 * t + i) as u64));
                tree.set(input.position, EMPTY);
                state.set(input.position, EMPTY);
            }
            for output in &tx.outputs {
                run.output(output, &key_hash(&keys[if output.amount == 120 { 0 } else { 1 }]));
                state.insert(output, 2);
            }
        }
        run.settle();
        match done.pop() {
            Some(first) => (first, run),
            None => {
                let next = Run::after(&run);
                (run, next)
            }
        }
    }

    /// What a run of payments of two inputs and two outputs takes, at
    /// the chain's parameters. `PAYMENTS` is how many.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn payments_timing() {
        let n: usize = std::env::var("PAYMENTS").ok().and_then(|x| x.parse().ok()).unwrap_or(165);
        let (run, _) = payments(n, 1);
        let used = run.len();
        let p = prove(run, 128, |m| Params::proven(m, 2, crate::pcs::SECURITY));
        assert!(p.verifies());
        println!(
            "{n} payments of two inputs and two outputs: {used} rows of 2^{}, 2^{} elements: proven in {:.2?} \
             ({:.0?} a payment), {} KB",
            p.rows.trailing_zeros(),
            p.params.m,
            p.proving,
            p.proving / n as u32,
            p.proof.size() / 1000
        );
    }

    /// No word of a run's rows holds up nothing, but one that is meant
    /// to: a bit of each word of a row of every kind there is, in a run
    /// of payments and in one of names, is changed, and some constraint
    /// of that row or the next refuses it. A word that could be changed
    /// unseen is one a prover may write as it likes: a rule that was
    /// meant and is not there.
    ///
    /// The one word that may be: the key of a hash's domain, on a row
    /// that goes on with the hash of the row before and has none.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn no_word_of_a_row_is_left_to_the_prover() {
        let c = circuit();
        let n = named();
        let wc = 1usize << c.log_cols;
        // (And two spends of a policy's output: one by a covenant, one
        // by a channel's two keys.)
        let ch = channel();
        let mine = key_hash(&key(0));
        let covenant = spend_run(&ch, 1, 0, vec![(ch.settle, mine)], 1, None).0;
        let root = ch.policy.root();
        let next = (Output::to(&root, 60, [7; MEMO]), root);
        let rebound = spend_run(&ch, 0, 7, vec![next], 1, Some(([7, 7], None))).0;
        let runs = [run_of(&a_scene(), |_, _| {}).0, named_run(&n, true).0, covenant, rebound];
        let mut kinds = std::collections::BTreeSet::new();
        for run in runs {
            let (rows, program, public) = run.finish(128);
            let fixed = Fixed { program: &program, public: &public };
            let w = Witness::new(&c, rows.len(), |c| self::run(c), |i| rows[i], &fixed);
            assert!(w.holds());
            // Where the domain's key is among a row's words: the word
            // that changes with it.
            let at = FRONT + KINDS;
            let mut other = rows.clone();
            other[0][at] ^= 1;
            let changed = Witness::new(&c, rows.len(), |c| self::run(c), |i| other[i], &fixed);
            let domain: Vec<usize> = (0..c.cols).filter(|col| changed.words[*col] != w.words[*col]).collect();
            assert_eq!(domain.len(), 1);
            // The first row of each kind.
            let kind_of = |row: &[u32; INPUTS]| (0..KINDS).find(|k| row[FRONT + k] != 0).expect("a kind");
            let mut first = std::collections::BTreeMap::new();
            for (i, row) in rows.iter().enumerate() {
                first.entry(kind_of(row)).or_insert(i);
            }
            kinds.extend(first.keys().copied());
            let tried: Vec<usize> = first.values().copied().collect();
            for bit in [0u32, 13, 31] {
                for (i, col) in crate::circuit::freedoms(&c, &w, &fixed, &tried, |_, _| bit) {
                    let kind = kind_of(&rows[i]);
                    let meant = col == domain[0] && SPECS[kind].goes_on && SPECS[kind].domain.is_none();
                    assert!(meant, "bit {bit} of word {col} of a row of kind {kind} (row {i}) holds up nothing");
                }
            }
            // (And the words past a row's own are nobody's: of nothing.)
            assert!(w.words.chunks(wc).all(|row| row[c.cols..].iter().all(|word| *word == 0)));
        }
        // Nearly every kind there is was among them.
        assert!(kinds.len() >= 65, "{} of {KINDS} kinds", kinds.len());
    }
}
