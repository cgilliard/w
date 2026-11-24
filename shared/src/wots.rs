//! The chains of XMSS signatures, as rows of a circuit: a row is one
//! WOTS chain step ([`crate::xmss`]), 1,005 of the 1,047 compressions it
//! takes to verify a signature.
//!
//! A signature's 67 chains come one after another, 15 rows each: a row
//! for every step a chain can have. The verifier of a signature walks
//! chain `c` from the value the signature gives for it, at step `d` (the
//! chain's digit of the message digest), to the chain's end. So:
//!
//! - A row is **active** if its step is `d` or later: the word `active`
//!   is one bit in every place, and the bit is that `digit + 15 - step`
//!   does not carry out of four bits.
//! - The block of an active row is the output of the row before if that
//!   row was active (and of this chain); otherwise it is free, which is
//!   the signature's value where the chain is entered.
//! - The chain's **end** is the last row's output if that row is active,
//!   and its block if not: a digit of 15 leaves no step, and the
//!   signature's value is the end.
//!
//! # The digits
//!
//! The message digest is not made here. Its two halves come off the bus
//! as elements, into a register of four words; a chain's digit is the
//! low four bits of the register's first word, which turns by four bits
//! for the next chain, and the register moves a word every eighth
//! chain. The checksum is a running sum of `15 - digit` over the message's
//! 64 chains; the last three chains read their digits from it.
//!
//! # What goes on the bus
//!
//! Every tuple is an address, which the program names, and one element,
//! as the tuples of [`crate::recursion`] and [`crate::machine`] are.
//!
//! | | |
//! |---|---|
//! | taken | the digest's halves, at chains 0 and 32 |
//! | sent | each chain's end, as its two halves |
//! | sent | the public seed, and the leaf's index, at a signature's first row |
//!
//! The seed and the leaf's index are the first five words of every
//! row's tweak, held from row to row across a signature. Whoever reads
//! the tuples (the arithmetic, beside the hashes of the leaf, the path
//! and the digest) ties the ends, the seed, the leaf and the digest to
//! one signature of one key.
//!
//! # The row
//!
//! One compression, whose tweak's last three words and whose block's
//! second half are the program's or constants, and 47 words more. It
//! fits the 512 words and 512 constraints of a row; what gates a value
//! onto the bus, and what chooses the end, are products of field
//! elements with a bit, which do not count against those.

use crate::blake3::{self, CHUNK_END, CHUNK_START, KEYED_HASH, ROOT};
use crate::circuit::{Circuit, Compression, Ctx, Expr, Sum, Symbolic, compress};
use crate::hash::Digest;
use crate::xmss::{CHAINS, MARKER, MSG_CHAINS, PubSeed, TAG_CHAIN, W};

/// Words a row takes as inputs.
pub const INPUTS: usize = 47;
/// Words of program a row reads.
pub const PROGRAM: usize = 32;
/// Rows of a chain: its steps.
pub const STEPS: usize = W - 1;
/// Rows of a signature.
pub const ROWS: usize = CHAINS * STEPS;

/// The flags of a chain step's one block.
const FLAGS: u32 = KEYED_HASH | CHUNK_START | CHUNK_END | ROOT;

/// Bits of the program's word of what goes on the bus.
const SEND_END: u32 = 1 << 0;
const TAKE_DIGEST: u32 = 1 << 1;
const SEND_KEY: u32 = 1 << 2;

/// A row against any [`Ctx`].
struct Row<V> {
    hash: Compression<V>,
    active: V,
    digit: V,
    /// `digit + 15 - step`.
    sum: V,
    /// The row before was active, and of this chain.
    link: V,
    /// The digest's register, and its copy taken off the bus.
    register: [V; 4],
    taken: [V; 4],
    /// The checksum: what is kept of it, what is added, and it.
    kept: V,
    added: V,
    total: V,
    /// `active` times the output less the block; the end as it is sent;
    /// the seed and leaf as they are sent.
    choice: [V; 8],
    end: [V; 8],
    key: [V; 5],
    p: Program<V>,
}

/// A row's program, in the order it is read.
struct Program<V> {
    /// The tweak's word of the chain and the step.
    extra: V,
    /// `15 - step`.
    left: V,
    /// Masks, each a word of all ones or none: the row is not a chain's
    /// first; not a signature's first; the register's first word is the
    /// last row's, or that turned, or the register moves a word, or its
    /// other words are the last row's, or its first is the checksum.
    not_first: V,
    same_signature: V,
    same: V,
    turn: V,
    shift: V,
    hold: V,
    checksum: V,
    /// Fifteen where a digit is added to the checksum.
    count: V,
    /// What goes on the bus, a bit each, and the addresses.
    bus: V,
    end_at: [V; 2],
    digest_at: V,
    key_at: [V; 2],
}

fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
    let seed_and_leaf: [C::V; 5] = std::array::from_fn(|_| c.input());
    let block: [C::V; 8] = std::array::from_fn(|_| c.input());
    let p = Program {
        extra: c.program(),
        left: c.program(),
        not_first: c.program(),
        same_signature: c.program(),
        same: c.program(),
        turn: c.program(),
        shift: c.program(),
        hold: c.program(),
        checksum: c.program(),
        count: c.program(),
        bus: c.program(),
        end_at: std::array::from_fn(|_| c.program()),
        digest_at: c.program(),
        key_at: std::array::from_fn(|_| c.program()),
    };
    let zero = c.constant(0);
    let [s0, s1, s2, s3, leaf] = seed_and_leaf;
    let cv = [s0, s1, s2, s3, leaf, zero.clone(), p.extra.clone(), c.constant(MARKER | TAG_CHAIN)];
    let m: [C::V; 16] = std::array::from_fn(|i| if i < 8 { block[i].clone() } else { zero.clone() });
    let t = [zero.clone(), zero, c.constant(32), c.constant(FLAGS)];
    let hash = compress(c, cv, m, t);
    let (active, digit) = (c.input(), c.input());
    let sum = c.add(&digit, &p.left);
    let link = c.input();
    let register = std::array::from_fn(|_| c.input());
    let taken = std::array::from_fn(|_| c.input());
    let (kept, added) = (c.input(), c.input());
    let total = c.add(&kept, &added);
    let total = c.checkpoint(&total);
    Row {
        hash,
        active,
        digit,
        sum,
        link,
        register,
        taken,
        kept,
        added,
        total,
        choice: std::array::from_fn(|_| c.input()),
        end: std::array::from_fn(|_| c.input()),
        key: std::array::from_fn(|_| c.input()),
        p,
    }
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
            let (h, p) = (&r.hash, &r.p);
            let ones = Expr::constant(!0);
            let turned = |x: &Expr, by: u8| {
                let mut t = x.clone();
                t.terms[0].rot = by;
                t
            };
            // The seed and the leaf: a signature's rows have one.
            for word in &h.cv[..5] {
                s.zero_where(&p.same_signature, word.xor(&word.prev()));
            }
            // The digit, and whether the step is at or past it: `active`
            // is one bit in every place, the sum's fifth turned over.
            s.constrain(r.register[0].clone(), Expr::constant(15), r.digit.clone());
            s.zero_where(&Expr::constant(16), r.active.xor(&r.sum).xor(&Expr::constant(16)));
            s.zero_where(&ones, r.active.xor(&turned(&r.active, 1)));
            // A row after an active one of its chain goes on from it.
            s.constrain(r.active.prev(), p.not_first.clone(), r.link.clone());
            for i in 0..8 {
                s.zero_where(&r.link, h.m[i].xor(&h.out[i].prev()));
            }
            // The register: as it was; turned by a digit; moved a word;
            // or, for the checksum's chains, the checksum.
            let first = &r.register[0];
            s.zero_where(&p.same, first.xor(&first.prev()));
            s.zero_where(&p.turn, first.xor(&turned(&first.prev(), 4)));
            s.zero_where(&p.checksum, first.xor(&r.total.prev()));
            for i in 0..3 {
                s.zero_where(&p.shift, r.register[i].xor(&r.register[i + 1].prev()));
                s.zero_where(&p.hold, r.register[i + 1].xor(&r.register[i + 1].prev()));
            }
            // The checksum: what it was, within a signature, and fifteen
            // less the digit where a chain of the message begins.
            s.constrain(r.total.prev(), p.same_signature.clone(), r.kept.clone());
            s.constrain(r.digit.xor(&Expr::constant(15)), p.count.clone(), r.added.clone());
            // The end: the block, or the output if the row is active.
            let bit = |b: u32| Sum::bits(&p.bus, b.trailing_zeros() as usize, 1);
            for half in 0..2 {
                let of = |words: &[Expr]| Sum::element(&words[4 * half..4 * half + 4]);
                let (block, choice) = (of(&h.m[..8]), of(&r.choice));
                s.product(block.add(&of(&h.out)), Sum::bits(&r.active, 0, 1), choice.clone());
                s.product(block.add(&choice), bit(SEND_END), of(&r.end));
                s.send(vec![Sum::word(&p.end_at[half]), of(&r.end)]);
            }
            // The digest's half, taken into the register.
            s.product(Sum::element(&r.register), bit(TAKE_DIGEST), Sum::element(&r.taken));
            s.receive(vec![Sum::word(&p.digest_at), Sum::element(&r.taken)]);
            // The seed and the leaf, sent.
            s.product(Sum::element(&h.cv[..4]), bit(SEND_KEY), Sum::element(&r.key[..4]));
            s.product(Sum::word(&h.cv[4]), bit(SEND_KEY), Sum::word(&r.key[4]));
            s.send(vec![Sum::word(&p.key_at[0]), Sum::element(&r.key[..4])]);
            s.send(vec![Sum::word(&p.key_at[1]), Sum::word(&r.key[4])]);
            core
        },
        INPUTS,
    )
}

/// The addresses a signature's rows send and take under.
#[derive(Clone, Debug)]
pub struct Addresses {
    /// Of the digest's two halves, taken.
    pub digest: [u32; 2],
    /// Of each chain's end, as two halves.
    pub ends: Vec<[u32; 2]>,
    /// Of the seed and of the leaf's index.
    pub key: [u32; 2],
}

/// The rows as their inputs and their program, signature after
/// signature.
#[derive(Default)]
pub struct Chains {
    pub rows: Vec<[u32; INPUTS]>,
    pub program: Vec<[u32; PROGRAM]>,
    /// What the last row left: its output, whether it was active, the
    /// register and the checksum.
    out: [u32; 8],
    active: bool,
    register: [u32; 4],
    total: u32,
}

/// What a row is, of what its program says.
#[derive(Clone, Copy, Default)]
struct Plan {
    extra: u32,
    left: u32,
    not_first: bool,
    same_signature: bool,
    same: bool,
    turn: bool,
    shift: bool,
    hold: bool,
    checksum: bool,
    count: bool,
    end_at: [u32; 2],
    digest_at: u32,
    key_at: [u32; 2],
}

impl Chains {
    /// A row: its tweak's seed and leaf, its block and its register.
    fn push(&mut self, seed_and_leaf: [u32; 5], block: [u32; 8], register: [u32; 4], plan: Plan) {
        let flag = |b: bool| if b { !0 } else { 0u32 };
        let [s0, s1, s2, s3, leaf] = seed_and_leaf;
        let cv = [s0, s1, s2, s3, leaf, 0, plan.extra, MARKER | TAG_CHAIN];
        let m: [u32; 16] = std::array::from_fn(|i| if i < 8 { block[i] } else { 0 });
        let out = blake3::compress(&cv, &m, 0, 32, FLAGS);
        let digit = register[0] & 15;
        let active = (digit + plan.left) >> 4 == 0;
        let link = self.active && plan.not_first;
        let kept = if plan.same_signature { self.total } else { 0 };
        let added = if plan.count { digit ^ 15 } else { 0 };
        let (send_end, take, send_key) = (plan.end_at[0] != 0, plan.digest_at != 0, plan.key_at[0] != 0);
        let mut r = [0u32; INPUTS];
        r[..5].copy_from_slice(&seed_and_leaf);
        r[5..13].copy_from_slice(&block);
        (r[13], r[14], r[15]) = (flag(active), digit, flag(link));
        r[16..20].copy_from_slice(&register);
        if take {
            r[20..24].copy_from_slice(&register);
        }
        (r[24], r[25]) = (kept, added);
        for i in 0..8 {
            let choice = if active { block[i] ^ out[i] } else { 0 };
            r[26 + i] = choice;
            r[34 + i] = if send_end { block[i] ^ choice } else { 0 };
        }
        if send_key {
            r[42..47].copy_from_slice(&seed_and_leaf);
        }
        let bus = flag(send_end) & SEND_END | flag(take) & TAKE_DIGEST | flag(send_key) & SEND_KEY;
        let mut p = [0u32; PROGRAM];
        p[..16].copy_from_slice(&[
            plan.extra,
            plan.left,
            flag(plan.not_first),
            flag(plan.same_signature),
            flag(plan.same),
            flag(plan.turn),
            flag(plan.shift),
            flag(plan.hold),
            flag(plan.checksum),
            if plan.count { 15 } else { 0 },
            bus,
            plan.end_at[0],
            plan.end_at[1],
            plan.digest_at,
            plan.key_at[0],
            plan.key_at[1],
        ]);
        (self.out, self.active, self.register, self.total) = (out, active, register, kept + added);
        self.rows.push(r);
        self.program.push(p);
    }

    /// The chains of one signature: of the key with `seed`, at `leaf`,
    /// over the message digest `digest`, with the signature's values
    /// `wots`. The chains' ends, as the rows send them.
    pub fn signature(
        &mut self,
        seed: &PubSeed,
        leaf: u32,
        digest: &Digest,
        wots: &[Digest; CHAINS],
        at: &Addresses,
    ) -> [Digest; CHAINS] {
        let s: [u32; 4] = blake3::words(seed);
        let seed_and_leaf = [s[0], s[1], s[2], s[3], leaf];
        let d: [u32; 8] = blake3::words(digest);
        let mut ends = [[0u8; 32]; CHAINS];
        for chain in 0..CHAINS {
            for step in 0..STEPS {
                let first = step == 0;
                // The register, as this row has it.
                let old = self.register;
                let (load, word) = (first && chain % 32 == 0 && chain < MSG_CHAINS, first && chain % 8 == 0);
                let checksum = first && chain == MSG_CHAINS;
                let register = if load {
                    std::array::from_fn(|i| d[chain / 8 + i])
                } else if checksum {
                    [self.total, 0, 0, 0]
                } else if word {
                    [old[1], old[2], old[3], 0]
                } else if first {
                    [old[0].rotate_right(4), old[1], old[2], old[3]]
                } else {
                    old
                };
                let digit = (register[0] & 15) as usize;
                // The block: the signature's value where the chain is
                // entered (or, with no step to take, where it ends), the
                // last output after that.
                let block = if step > digit {
                    self.out
                } else if step == digit || (digit == STEPS && step == STEPS - 1) {
                    blake3::words(&wots[chain])
                } else {
                    [0; 8]
                };
                let turn = first && !load && !word && !checksum;
                let plan = Plan {
                    extra: chain as u32 | (step as u32) << 16,
                    left: (STEPS - step) as u32,
                    not_first: !first,
                    same_signature: chain > 0 || step > 0,
                    same: !first,
                    turn,
                    shift: first && word && !load && !checksum,
                    hold: !first || turn,
                    checksum,
                    count: first && chain < MSG_CHAINS,
                    end_at: if step == STEPS - 1 { at.ends[chain] } else { [0; 2] },
                    digest_at: if load { at.digest[chain / 32] } else { 0 },
                    key_at: if chain == 0 && first { at.key } else { [0; 2] },
                };
                self.push(seed_and_leaf, block, register, plan);
            }
            let end = if self.active { self.out } else { blake3::words(&wots[chain]) };
            ends[chain] = blake3::bytes(&end);
        }
        ends
    }

    /// The rows, filled to a power of two (and to `at_least`) with rows
    /// that send nothing, and the program as words.
    pub fn finish(mut self, at_least: usize) -> (Vec<[u32; INPUTS]>, Vec<u32>) {
        let n = self.rows.len().max(at_least).next_power_of_two();
        while self.rows.len() < n {
            self.push([0; 5], [0; 8], [0; 4], Plan::default());
        }
        (self.rows, self.program.concat())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::argument::{Layout, Part, Program, Table, prove_tables, verify_tables};
    use crate::circuit::{Fixed, Witness};
    use crate::ntt::Domain;
    use crate::pcs::Params;
    use crate::xmss::{SecretKey, Signature, digits, message_digest};

    /// A table that sends and takes whatever its rows say: the other
    /// end of the bus. A row sends one element under one address and
    /// takes one under another, either or both of them nothing.
    fn peer() -> Circuit {
        Circuit::new(
            |s: &mut Symbolic| {
                let words: [Expr; 8] = std::array::from_fn(|_| s.input());
                let (send_at, take_at) = (s.program(), s.program());
                s.send(vec![Sum::word(&send_at), Sum::element(&words[..4])]);
                s.receive(vec![Sum::word(&take_at), Sum::element(&words[4..])]);
                0
            },
            8,
        )
    }

    fn element(words: &[u32]) -> [u32; 4] {
        std::array::from_fn(|i| words.get(i).copied().unwrap_or(0))
    }

    /// A key, a message and its signature, with the digest it signs.
    fn signed(seed: u8) -> (SecretKey, Signature, Digest) {
        let mut sk = SecretKey::generate_with_height(&[seed; 32], 2);
        sk.set_next_index(seed as u64 % 4);
        let msg = [seed ^ 0x5A; 32];
        let sig = sk.sign(&msg).unwrap();
        let pk = sk.public_key();
        assert!(pk.verify(&msg, &sig));
        let digest = message_digest(&pk.pub_seed, sig.index, pk.height, &sig.randomizer, &msg);
        (sk, sig, digest)
    }

    /// Whether the chains' rows are proven beside a peer that sends
    /// `digests` and takes `ends`, the seed and the leaf: each
    /// signature's, in order.
    fn proves(chains: Chains, expect: &[(Digest, [Digest; CHAINS], PubSeed, u32)], at: &[Addresses]) -> bool {
        let (rows, program) = chains.finish(128);
        let mut peer_rows: Vec<[u32; 8]> = Vec::new();
        let mut peer_program: Vec<u32> = Vec::new();
        let mut tuple = |send: u32, take: u32, words: [u32; 4]| {
            let mut r = [0u32; 8];
            r[if send != 0 { 0 } else { 4 }..][..4].copy_from_slice(&words);
            peer_rows.push(r);
            peer_program.extend([send, take]);
        };
        for ((digest, ends, seed, leaf), at) in expect.iter().zip(at) {
            let d: [u32; 8] = blake3::words(digest);
            tuple(at.digest[0], 0, element(&d[..4]));
            tuple(at.digest[1], 0, element(&d[4..]));
            for (end, at) in ends.iter().zip(&at.ends) {
                let e: [u32; 8] = blake3::words(end);
                tuple(0, at[0], element(&e[..4]));
                tuple(0, at[1], element(&e[4..]));
            }
            tuple(0, at.key[0], blake3::words(seed));
            tuple(0, at.key[1], element(&[*leaf]));
        }
        let n = peer_rows.len().next_power_of_two().max(128);
        peer_rows.resize(n, [0; 8]);
        peer_program.resize(2 * n, 0);
        let (wots, peer) = (circuit(), peer());
        let tables = [(&wots, rows.len()), (&peer, n)];
        let layout = Layout::of(tables.iter().copied()).expect("the chains' table is the larger");
        let params = Params::plain(layout.total, 1, 4, 4);
        let domain = Domain::new(params.k(), true);
        let committed = Program::of(&params, &domain, &tables, vec![program, peer_program]);
        let fixed =
            [Fixed { program: &committed.words[0], public: &[] }, Fixed { program: &committed.words[1], public: &[] }];
        let a = Witness::new(&wots, rows.len(), |c| run(c), |i| rows[i], &fixed[0]);
        let b = Witness::new(
            &peer,
            n,
            |c| _ = std::array::from_fn::<u32, 8, _>(|_| c.input()),
            |i| peer_rows[i],
            &fixed[1],
        );
        let held = a.holds();
        let parts =
            vec![Part { circuit: &wots, witness: a, public: &[] }, Part { circuit: &peer, witness: b, public: &[] }];
        let (proof, _) = prove_tables(&params, &domain, parts, Some(&committed));
        let tables =
            [Table { circuit: &wots, rows: rows.len(), public: &[] }, Table { circuit: &peer, rows: n, public: &[] }];
        let ok = verify_tables(&params, &domain, &tables, Some(&committed.root()), &proof).is_some();
        assert!(!ok || held);
        ok
    }

    /// Addresses for signature `i`, all its own.
    fn addresses(i: u32) -> Addresses {
        let base = 1 + 1000 * i;
        Addresses {
            digest: [base, base + 1],
            ends: (0..CHAINS as u32).map(|c| [base + 2 + 2 * c, base + 3 + 2 * c]).collect(),
            key: [base + 500, base + 501],
        }
    }

    #[test]
    fn the_row_fits() {
        let c = circuit();
        assert!(c.cols <= 512 && c.constraints.len() <= 512, "{} words, {} constraints", c.cols, c.constraints.len());
        assert_eq!((c.log_cols, c.log_constraints, c.program_width()), (9, 9, PROGRAM));
        assert_eq!((c.products.len(), c.sends.len(), c.receives.len()), (7, 4, 1));
        println!("{} words, {} constraints, {} terms", c.cols, c.constraints.len(), c.terms());
    }

    #[test]
    fn the_chains_of_signatures_are_proven() {
        let mut chains = Chains::default();
        let (mut expect, mut at) = (Vec::new(), Vec::new());
        for i in 0..2u32 {
            let (sk, sig, digest) = signed(3 + i as u8);
            let pk = sk.public_key();
            at.push(addresses(i));
            let ends = chains.signature(&pk.pub_seed, sig.index as u32, &digest, &sig.wots, &at[i as usize]);
            expect.push((digest, ends, pk.pub_seed, sig.index as u32));
        }
        assert_eq!(chains.rows.len(), 2 * ROWS);
        assert!(proves(chains, &expect, &at));
    }

    #[test]
    fn the_ends_are_the_public_key_s() {
        // The ends the rows send are what the leaf is the hash of: with
        // them the signature's path reaches the key's root.
        let (sk, sig, digest) = signed(9);
        let pk = sk.public_key();
        let mut chains = Chains::default();
        let ends = chains.signature(&pk.pub_seed, sig.index as u32, &digest, &sig.wots, &addresses(0));
        let mut node = crate::xmss::wots_pk_from_ends(&pk.pub_seed, sig.index, pk.height, &ends);
        let mut index = sig.index;
        for sibling in &sig.auth_path {
            node = if index & 1 == 0 {
                crate::xmss::tree_node(&node, sibling)
            } else {
                crate::xmss::tree_node(sibling, &node)
            };
            index >>= 1;
        }
        assert_eq!(node, pk.root);
    }

    #[test]
    fn chains_that_are_not_the_signature_s_are_not() {
        let (sk, sig, digest) = signed(5);
        let pk = sk.public_key();
        let at = [addresses(0)];
        let leaf = sig.index as u32;
        let honest = |digest: &Digest, wots: &[Digest; CHAINS], seed: &PubSeed, leaf: u32| {
            let mut chains = Chains::default();
            let ends = chains.signature(seed, leaf, digest, wots, &at[0]);
            (chains, ends)
        };
        let (chains, ends) = honest(&digest, &sig.wots, &pk.pub_seed, leaf);
        let expect = [(digest, ends, pk.pub_seed, leaf)];
        assert!(proves(chains, &expect, &at));
        // Chains walked for another digest, seed or leaf, or from another
        // value: the ends are not the key's, and whoever takes the true
        // ones, digest, seed and leaf does not find them.
        let mut other = digest;
        other[0] ^= 1;
        assert!(!proves(honest(&other, &sig.wots, &pk.pub_seed, leaf).0, &expect, &at));
        let mut wots = sig.wots;
        wots[40][0] ^= 1;
        assert!(!proves(honest(&digest, &wots, &pk.pub_seed, leaf).0, &expect, &at));
        assert!(!proves(honest(&digest, &sig.wots, &[1; 16], leaf).0, &expect, &at));
        assert!(!proves(honest(&digest, &sig.wots, &pk.pub_seed, leaf ^ 1).0, &expect, &at));
        // A row's words changed after the fact: a block where the chain
        // goes on, `active`, the digit, the register, the checksum.
        let d = digits(&digest);
        let chain = (0..MSG_CHAINS).find(|c| d[*c] < 13).unwrap();
        let going = chain * STEPS + d[chain] as usize + 1;
        for word in [5, 13, 14, 16, 24, 25] {
            let (mut chains, _) = honest(&digest, &sig.wots, &pk.pub_seed, leaf);
            chains.rows[going][word] ^= 1;
            assert!(!proves(chains, &expect, &at), "word {word}");
        }
    }
}
