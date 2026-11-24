//! The hashing of a verifier, as rows of a circuit: the transcript it
//! replays and the Merkle openings it checks, and what of them the
//! arithmetic ([`crate::machine`]) needs.
//!
//! A row is one compression ([`crate::circuit::compress`]). How a row
//! follows from the one before is its program's to say: three flags,
//! each a word of all ones or of none, with the block's length, its
//! Blake3 flags and the domain it hashes in.
//!
//! | program word | set, it says |
//! |---|---|
//! | `chain` | the chaining value is the last row's output: the next block of an input longer than one |
//! | `left` | the block's first half is the last row's output: a transcript step, which begins with the state |
//! | `node` | the block is two digests, one the last row's output: a step up a Merkle path |
//!
//! A row whose `chain` is clear starts a hash: its chaining value is the
//! key of its domain. What the proof decides is witness: three words.
//!
//! | witness word | |
//! |---|---|
//! | `dir` | which half of a node's block is the last row's output: the index's lowest bit, as a word of all ones or none |
//! | `right` | `node` and `dir` |
//! | `index` | what is left of the opening's index; a `node` row's is the last row's shifted right |
//!
//! # What a row sends
//!
//! The values the arithmetic computes with are in these rows: what the
//! transcript took in, the challenges it gave, the leaves that were
//! opened, the digests the paths reached. A row puts them on the bus
//! ([`crate::argument`]) under addresses its program names:
//!
//! | sent | |
//! |---|---|
//! | the four elements of the block | what a transcript step took in, or a leaf's elements |
//! | the two halves of the output | a challenge; the digest at the top of a path |
//! | the index, and the index but for its lowest bit | for the opening of the next codeword, and to take the bits above a path's height off an index |
//! | the low 31 bits of the output's first word | a query's index, as the transcript gives it |
//! | two constants | elements the program holds, for the arithmetic's use |
//!
//! and takes one thing off it: the index an opening is of, at its first
//! row.
//!
//! A row's program has one word more, a mask: the bits of the output's
//! first word that must be zero. That is a ground nonce's check
//! ([`crate::challenger`]): the step that takes the nonce in must leave
//! a state that ends in so many zero bits. A row that sends nothing of a kind must send zeros, which the bus
//! does not count; so each value sent is a copy of the row's word times a
//! bit of the program, a multiplication, and not the word itself.
//!
//! # What this binds
//!
//! Every transcript step takes the state the step before left; every
//! opening hashes its leaf in the domain of leaves and climbs by its
//! index in the domain of nodes. The program is committed, so which row
//! does which, and what it sends under which address, is not the
//! prover's to choose. That a path's top is the root the transcript took
//! in, and its index the one the transcript gave, is for whoever reads
//! what the rows send to say: the arithmetic.

use crate::argument;
use crate::blake3::{self, CHUNK_END, CHUNK_START, KEYED_HASH, ROOT};
use crate::challenger::Step;
use crate::circuit::{Circuit, Compression, Ctx, Expr, Sum, Symbolic, compress};
use crate::field::{F, as_bytes};
use crate::hash::{DOM_LEAF, DOM_NODE, Digest, domain_key};
use crate::machine::OUTSIDE;
use crate::merkle;
use crate::pcs::{Batch, Params};
use std::collections::VecDeque;

/// Words a row takes as inputs: the chaining value, the block, the three
/// words of the path, and the copies it sends.
pub const INPUTS: usize = 55;
/// Words of program a row reads.
pub const PROGRAM: usize = 32;
/// Constants a row's program can send.
const CONSTANTS: usize = 2;

/// Bits of the program's word of what is sent: the block's four
/// elements, the output's halves, the index, the index above its lowest
/// bit, the index received, and the output's low 31 bits.
const SEND_BLOCK: u32 = 1 << 0;
const SEND_OUT: u32 = 1 << 4;
const SEND_INDEX: u32 = 1 << 6;
const SEND_HIGH: u32 = 1 << 7;
const TAKE_INDEX: u32 = 1 << 8;
const SEND_LOW: u32 = 1 << 9;

/// A row against any [`Ctx`].
pub struct Row<V> {
    pub hash: Compression<V>,
    /// `dir`, `right`, `index`.
    path: [V; 3],
    /// The copies sent: the block's elements, the output's halves, and
    /// the four single words (the index, the index above its lowest bit,
    /// the index received, the output's low bits).
    block: [[V; 4]; 4],
    out: [[V; 4]; 2],
    words: [V; 4],
    /// The domain's tag, and `chain`, `left`, `node`.
    flags: [V; 4],
    /// The addresses: of the block's elements, the output's halves, and
    /// the four words.
    block_at: [V; 4],
    out_at: [V; 2],
    words_at: [V; 4],
    /// What is sent, a bit each.
    sends: V,
    /// The constants: an address and four words each.
    constants: [[V; 5]; CONSTANTS],
    /// The bits of the output's first word that are zero.
    mask: V,
}

pub fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
    let cv: [C::V; 8] = std::array::from_fn(|_| c.input());
    let m: [C::V; 16] = std::array::from_fn(|_| c.input());
    let zero = c.constant(0);
    let t = [zero.clone(), zero, c.program(), c.program()];
    let hash = compress(c, cv, m, t);
    Row {
        hash,
        path: std::array::from_fn(|_| c.input()),
        block: std::array::from_fn(|_| std::array::from_fn(|_| c.input())),
        out: std::array::from_fn(|_| std::array::from_fn(|_| c.input())),
        words: std::array::from_fn(|_| c.input()),
        flags: std::array::from_fn(|_| c.program()),
        block_at: std::array::from_fn(|_| c.program()),
        out_at: std::array::from_fn(|_| c.program()),
        words_at: std::array::from_fn(|_| c.program()),
        sends: c.program(),
        constants: std::array::from_fn(|_| std::array::from_fn(|_| c.program())),
        mask: c.program(),
    }
}

pub fn circuit() -> Circuit {
    Circuit::new(
        |s: &mut Symbolic| {
            let r = row(s);
            let core = s.constraints.len();
            let h = &r.hash;
            let [domain, chain, left, node] = &r.flags;
            let [dir, right, index] = &r.path;
            let ones = Expr::constant(!0);
            let fresh = chain.xor(&ones);
            // The first half is the last output on a transcript row, and
            // on a node row whose index bit is clear.
            let first = left.xor(node).xor(right);
            for i in 0..8 {
                let last = h.out[i].prev();
                s.zero_where(chain, h.cv[i].xor(&last));
                // A hash starts from its domain's key: the tag, then zeros.
                let key = if i == 0 { domain.clone() } else { Expr::constant(0) };
                s.zero_where(&fresh, h.cv[i].xor(&key));
                s.zero_where(&first, h.m[i].xor(&last));
                s.zero_where(right, h.m[8 + i].xor(&last));
            }
            s.constrain(node.clone(), dir.clone(), right.clone());
            // `dir` is one bit in every place, and that bit is the index's lowest.
            let turned = {
                let mut t = dir.clone();
                t.terms[0].rot = 1;
                t
            };
            s.zero_where(&ones, dir.xor(&turned));
            s.zero_where(&Expr::constant(1), dir.xor(index));
            s.zero_where(node, index.xor(&index.prev().shr()));
            s.zero_where(chain, index.xor(&index.prev()));
            s.zero_where(&r.mask, h.out[0].clone());
            // What is sent: each a copy of the row's own times its bit.
            let bit = |b: u32, i: usize| Sum::bits(&r.sends, b.trailing_zeros() as usize + i, 1);
            for i in 0..4 {
                let copy = Sum::element(&r.block[i]);
                s.product(Sum::element(&h.m[4 * i..4 * i + 4]), bit(SEND_BLOCK, i), copy.clone());
                s.send(vec![Sum::word(&r.block_at[i]), copy]);
            }
            for i in 0..2 {
                let copy = Sum::element(&r.out[i]);
                s.product(Sum::element(&h.out[4 * i..4 * i + 4]), bit(SEND_OUT, i), copy.clone());
                s.send(vec![Sum::word(&r.out_at[i]), copy]);
            }
            let words = [
                (Sum::bits(index, 0, 31), SEND_INDEX),
                (Sum::bits(index, 1, 31), SEND_HIGH),
                (Sum::bits(index, 1, 31), TAKE_INDEX),
                (Sum::bits(&h.out[0], 0, 31), SEND_LOW),
            ];
            for (i, (own, b)) in words.into_iter().enumerate() {
                let copy = Sum::word(&r.words[i]);
                s.product(own, bit(b, 0), copy.clone());
                let tuple = vec![Sum::word(&r.words_at[i]), copy];
                if b == TAKE_INDEX { s.receive(tuple) } else { s.send(tuple) }
            }
            for constant in &r.constants {
                s.send(vec![Sum::word(&constant[0]), Sum::element(&constant[1..])]);
            }
            core
        },
        INPUTS,
    )
}

/// What a row sends and takes, as its program says it: for each thing
/// the address, zero for none.
#[derive(Clone, Copy, Default)]
struct Sends {
    block: [u32; 4],
    out: [u32; 2],
    /// The index; the index above its lowest bit; the index taken; the
    /// output's low bits.
    words: [u32; 4],
}

/// A row's program: what it is for.
#[derive(Clone, Copy, Default)]
struct Plan {
    len: u32,
    flags: u32,
    domain: u32,
    chain: bool,
    left: bool,
    node: bool,
    sends: Sends,
    /// The bits of the output's first word that must be zero.
    mask: u32,
}

/// What the proof decides of a row.
#[derive(Clone, Copy, Default)]
struct Link {
    dir: bool,
    node: bool,
    index: u32,
}

/// What a transcript step sent: the addresses of the elements it took
/// in, of its output as a challenge, and of its output's low 31 bits.
/// Zero where the step sent none.
#[derive(Clone, Debug, Default)]
pub struct Stepped {
    /// The two halves of the state a first step began from.
    pub state: [u32; 2],
    pub data: Vec<u32>,
    pub challenge: u32,
    pub low: u32,
}

/// What an opening sent: the addresses of its leaf's elements, of the
/// two halves of the digest its path reached, of its index shifted by
/// one place, by two and so on (the last is the index of the next
/// codeword's opening, and each with the one before gives a bit of the
/// place in that codeword's leaf), and of the bits of its index above
/// the path's height.
#[derive(Clone, Debug, Default)]
pub struct Opened {
    pub leaf: Vec<u32>,
    pub top: [u32; 2],
    pub shifted: Vec<u32>,
    pub high: u32,
}

/// The rows as their inputs and their program, in order, each made with
/// the output of the one before at hand.
pub struct Trace {
    pub rows: Vec<[u32; INPUTS]>,
    /// The program, [`PROGRAM`] words a row.
    pub program: Vec<[u32; PROGRAM]>,
    last: [u32; 8],
    /// Rows of transcript steps, and of openings.
    pub transcript: usize,
    pub openings: usize,
    /// Whether the rows send anything: without, they are the hashing
    /// alone, for measuring.
    bound: bool,
    next: u32,
    /// Constants waiting for a row with room to send them.
    constants: VecDeque<(u32, F)>,
}

fn words_of(x: F) -> [u32; 4] {
    std::array::from_fn(|j| (x.0 >> (32 * j)) as u32)
}

impl Trace {
    /// A trace whose rows send what they hold, if `bound`.
    pub fn new(bound: bool) -> Trace {
        Trace {
            rows: Vec::new(),
            program: Vec::new(),
            last: [0; 8],
            transcript: 0,
            openings: 0,
            bound,
            next: OUTSIDE,
            constants: VecDeque::new(),
        }
    }

    /// A new address, if anything is sent.
    fn address(&mut self, wanted: bool) -> u32 {
        if !(self.bound && wanted) {
            return 0;
        }
        self.next += 1;
        assert!(self.next < 2 * OUTSIDE, "the addresses of what the rows send are 2^23");
        self.next - 1
    }

    /// The address a constant will be sent under, once: by whichever row
    /// next has room.
    pub fn constant(&mut self, value: F) -> u32 {
        assert!(self.bound);
        let at = self.address(true);
        self.constants.push_back((at, value));
        at
    }

    fn push(&mut self, cv: [u32; 8], block: [u32; 16], plan: Plan, link: Link) {
        let flag = |b: bool| if b { !0 } else { 0 };
        let out = blake3::compress(&cv, &block, 0, plan.len, plan.flags);
        let sends = &plan.sends;
        let mut r = [0u32; INPUTS];
        r[..8].copy_from_slice(&cv);
        r[8..24].copy_from_slice(&block);
        r[24..27].copy_from_slice(&[flag(link.dir), flag(link.node && link.dir), link.index]);
        // The copies: the row's own where its program sends it.
        let mut bits = 0u32;
        for i in 0..4 {
            if sends.block[i] != 0 {
                r[27 + 4 * i..31 + 4 * i].copy_from_slice(&block[4 * i..4 * i + 4]);
                bits |= SEND_BLOCK << i;
            }
        }
        for i in 0..2 {
            if sends.out[i] != 0 {
                r[43 + 4 * i..47 + 4 * i].copy_from_slice(&out[4 * i..4 * i + 4]);
                bits |= SEND_OUT << i;
            }
        }
        let own = [link.index & 0x7FFF_FFFF, link.index >> 1, link.index >> 1, out[0] & 0x7FFF_FFFF];
        for (i, b) in [SEND_INDEX, SEND_HIGH, TAKE_INDEX, SEND_LOW].into_iter().enumerate() {
            if sends.words[i] != 0 {
                r[51 + i] = own[i];
                bits |= b;
            }
        }
        let mut p = [0u32; PROGRAM];
        p[..6].copy_from_slice(&[
            plan.len,
            plan.flags,
            plan.domain,
            flag(plan.chain),
            flag(plan.left),
            flag(plan.node),
        ]);
        p[6..10].copy_from_slice(&sends.block);
        p[10..12].copy_from_slice(&sends.out);
        p[12..16].copy_from_slice(&sends.words);
        p[16] = bits;
        p[17 + 5 * CONSTANTS] = plan.mask;
        for slot in p[17..17 + 5 * CONSTANTS].chunks_exact_mut(5) {
            if let Some((at, value)) = self.constants.pop_front() {
                slot[0] = at;
                slot[1..].copy_from_slice(&words_of(value));
            }
        }
        self.last = out;
        self.rows.push(r);
        self.program.push(p);
    }

    /// The hash of `input` in `domain`, a row a block. `first` and `link`
    /// are the first row's; the rows after it chain, keeping its index.
    /// `sends(block)` is what the row of that block sends.
    fn hash(&mut self, domain: u32, input: &[u8], first: Plan, link: Link, sends: impl Fn(usize) -> Sends) {
        let n = blake3::compressions(input.len());
        assert!(input.len() <= blake3::CHUNK_LEN, "an input is a chunk at most");
        for (i, block) in input.chunks(64).enumerate() {
            let mut flags = KEYED_HASH;
            if i == 0 {
                flags |= CHUNK_START;
            }
            if i == n - 1 {
                flags |= CHUNK_END | ROOT;
            }
            let (len, sends) = (block.len() as u32, sends(i));
            // A mask is of the hash's output: its last block's.
            let mask = if i == n - 1 { first.mask } else { 0 };
            let (cv, plan) = if i == 0 {
                (domain_key(domain), Plan { len, flags, domain, sends, mask, ..first })
            } else {
                (self.last, Plan { len, flags, domain, chain: true, sends, mask, ..Plan::default() })
            };
            self.push(cv, blake3::words(block), plan, link);
        }
    }

    /// A transcript's step, after the one before it (`first` if there is
    /// none). It sends the elements it took in if `data`, its output as a
    /// challenge if `challenge`, and its output's low 31 bits if `low`;
    /// and its output ends in `ground` zero bits, 32 at most.
    pub fn step(&mut self, step: &Step, first: bool, data: bool, challenge: bool, low: bool, ground: usize) -> Stepped {
        let before = self.rows.len();
        if !first {
            assert_eq!(blake3::words::<8>(&step.input[..32]), self.last, "the steps are a chain");
        }
        // The elements taken in lie two in the first block, after the
        // state, and four in each block after.
        let elements = (step.input.len() - 32).div_ceil(16);
        let stepped = Stepped {
            // The state a transcript begins from is its label's hash,
            // which whoever reads this must find it to be.
            state: [self.address(first), self.address(first)],
            data: (0..elements).map(|_| self.address(data)).collect(),
            challenge: self.address(challenge),
            low: self.address(low),
        };
        let blocks = blake3::compressions(step.input.len());
        let sends = |block: usize| {
            let mut s = Sends::default();
            for slot in 0..4usize {
                let element = if block == 0 { slot.checked_sub(2) } else { Some(4 * block - 2 + slot) };
                s.block[slot] = element.and_then(|e| stepped.data.get(e).copied()).unwrap_or(0);
            }
            if block == 0 {
                s.block[..2].copy_from_slice(&stepped.state);
            }
            if block == blocks - 1 {
                (s.out[0], s.words[3]) = (stepped.challenge, stepped.low);
            }
            s
        };
        let mask = ((1u64 << ground) - 1) as u32;
        assert!(ground <= 32);
        self.hash(step.domain, &step.input, Plan { left: !first, mask, ..Plan::default() }, Link::default(), sends);
        self.transcript += self.rows.len() - before;
        stepped
    }

    /// The hash of `elements` in `domain`, by itself: the addresses its
    /// rows send the elements under, and the two halves of the digest.
    pub fn digest(&mut self, domain: u32, elements: &[F]) -> (Vec<u32>, [u32; 2]) {
        let data: Vec<u32> = (0..elements.len()).map(|_| self.address(true)).collect();
        let out = [self.address(true), self.address(true)];
        let blocks = elements.len().div_ceil(4);
        let sends = |block: usize| {
            let mut s = Sends::default();
            for slot in 0..4 {
                s.block[slot] = data.get(4 * block + slot).copied().unwrap_or(0);
            }
            if block == blocks - 1 {
                s.out = out;
            }
            s
        };
        self.hash(domain, &as_bytes(elements), Plan::default(), Link::default(), sends);
        (data, out)
    }

    /// A transcript's steps, in order, none sending anything.
    pub fn transcript(&mut self, log: &[Step]) {
        for (i, step) in log.iter().enumerate() {
            self.step(step, i == 0, false, false, false, 0);
        }
    }

    /// An opening of the leaf `leaf` at `index`: its hash, then a row for
    /// each sibling of `path`. The index may have bits above the path's
    /// height, which the path does not read. The opening takes its index
    /// from `index_at`, if that is an address; it sends its leaf's
    /// elements if `leaf_sent`, its index as it stands one row up the
    /// path, two, and so on to `shift` rows, and what of the index is
    /// above the path if `high`.
    #[allow(clippy::too_many_arguments)]
    pub fn opening(
        &mut self,
        leaf: &[F],
        index: u32,
        path: &[Digest],
        index_at: u32,
        leaf_sent: bool,
        shift: usize,
        high: bool,
    ) -> Opened {
        self.opening_in([DOM_LEAF, DOM_NODE], leaf, index, path, index_at, leaf_sent, shift, high)
    }

    /// An address for another table to send under: one nothing else has.
    pub fn reserve(&mut self) -> u32 {
        self.address(true)
    }

    /// [`Trace::opening`] in a tree whose leaves are hashed in the first
    /// of `domains` and whose nodes in the second.
    #[allow(clippy::too_many_arguments)]
    pub fn opening_in(
        &mut self,
        domains: [u32; 2],
        leaf: &[F],
        index: u32,
        path: &[Digest],
        index_at: u32,
        leaf_sent: bool,
        shift: usize,
        high: bool,
    ) -> Opened {
        let before = self.rows.len();
        assert!(index < 1 << 31 && shift < path.len().max(1) && !path.is_empty());
        let opened = Opened {
            leaf: (0..leaf.len()).map(|_| self.address(leaf_sent)).collect(),
            top: [self.address(true), self.address(true)],
            shifted: (0..shift).map(|_| self.address(true)).collect(),
            high: self.address(high),
        };
        // The leaf's rows hold the index a place up, so that every node
        // row's is the last row's shifted.
        let take = if self.bound { index_at } else { 0 };
        let sends = |block: usize| {
            let mut s = Sends::default();
            for slot in 0..4 {
                s.block[slot] = opened.leaf.get(4 * block + slot).copied().unwrap_or(0);
            }
            if block == 0 {
                s.words[2] = take;
            }
            s
        };
        self.hash(domains[0], &as_bytes(leaf), Plan::default(), Link { index: index << 1, ..Link::default() }, sends);
        for (level, sibling) in path.iter().enumerate() {
            let at = index >> level;
            let dir = at & 1 == 1;
            let own = blake3::bytes(&self.last);
            let pair = if dir { [&sibling[..], &own[..]].concat() } else { [&own[..], &sibling[..]].concat() };
            let mut sends = Sends::default();
            if (1..=shift).contains(&level) {
                sends.words[0] = opened.shifted[level - 1];
            }
            if level == path.len() - 1 {
                sends.out = opened.top;
                sends.words[1] = opened.high;
            }
            let plan = Plan {
                len: 64,
                flags: KEYED_HASH | CHUNK_START | CHUNK_END | ROOT,
                domain: domains[1],
                node: true,
                sends,
                ..Plan::default()
            };
            self.push(domain_key(domains[1]), blake3::words(&pair), plan, Link { dir, node: true, index: at });
        }
        self.openings += self.rows.len() - before;
        opened
    }

    /// The digest the last row made: after an opening, what its path
    /// reached.
    pub fn last(&self) -> Digest {
        blake3::bytes(&self.last)
    }

    /// Every opening of a batch, each path whole and none sending
    /// anything: `indices` are the queries' leaves in the tree of `root`
    /// and `height`.
    fn batch(&mut self, root: &Digest, batch: &Batch, indices: &[usize], height: usize) {
        let mut distinct = indices.to_vec();
        distinct.sort_unstable();
        distinct.dedup();
        let hashes: Vec<Digest> = batch.leaves.iter().map(|l| merkle::leaf_hash(l)).collect();
        let paths = merkle::batch_paths(&distinct, &hashes, height, &batch.siblings);
        // A row for every query, in the queries' order: the same leaf
        // opened twice is shown twice, so that the rows do not depend on
        // which queries met.
        for i in indices {
            let at = distinct.binary_search(i).expect("the batch opens every query's leaf");
            self.opening(&batch.leaves[at], *i as u32, &paths[at], 0, false, 0, false);
            assert_eq!(self.last(), *root, "the opening reaches its root");
        }
    }

    /// All the hashing of verifying `proof`, sending nothing: the
    /// transcript `log` its verifier made, and every query's openings,
    /// those of the programs' codeword among them if the proof has one
    /// (`program` its root). `indices` are the queries' leaves in the
    /// first committed codeword.
    pub fn verifier(
        &mut self,
        params: &Params,
        proof: &argument::Proof,
        program: Option<&Digest>,
        log: &[Step],
        indices: &[usize],
    ) {
        assert!(!self.bound);
        let from = self.rows.len();
        for (i, step) in log.iter().enumerate() {
            self.step(step, from == self.rows.len() && i == 0, false, false, false, 0);
        }
        let steps = params.steps();
        let mut indices = indices.to_vec();
        let mut layer = 0;
        for (t, s) in steps.iter().enumerate().take(proof.pcs.openings.len()) {
            if let (1, Some(program)) = (t, program) {
                self.batch(program, &proof.pcs.joined_openings[0], &indices, params.k() - layer);
            }
            if t > 0 {
                indices.iter_mut().for_each(|i| *i >>= s);
            }
            let root = if t == 0 { &proof.root } else { &proof.pcs.roots[t - 1] };
            let height = params.k() - layer - s;
            self.batch(root, &proof.pcs.openings[t], &indices, height);
            layer += s;
        }
    }

    /// The rows and the program, filled to a power of two (and to
    /// `at_least`) with rows that hash nothing and follow from nothing:
    /// as many as it takes to send the constants that are waiting.
    pub fn finish(mut self, at_least: usize) -> (Vec<[u32; INPUTS]>, Vec<u32>) {
        let need = self.rows.len() + self.constants.len().div_ceil(CONSTANTS);
        let n = need.max(at_least).next_power_of_two();
        while self.rows.len() < n {
            self.push([0; 8], [0; 16], Plan::default(), Link::default());
        }
        (self.rows, self.program.into_iter().flatten().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::argument::{
        Layout, Part, Program, Statement, Table, prove, prove_tables, variables, verify, verify_logged, verify_tables,
    };
    use crate::circuit::{COMPRESS_INPUTS, Fixed, Witness, blake3_circuit, compress_row};
    use crate::machine::{self, Assembly};
    use crate::ntt::Domain;
    use crate::test_util::Rng;

    /// A small proof of compressions, with what its verifier went
    /// through.
    fn a_proof(seed: u64) -> (Params, argument::Proof, argument::Replay) {
        let inner = blake3_circuit();
        let rows = 128;
        let p = Params::plain(variables(&inner, rows), 1, 3, 4);
        let domain = Domain::new(p.k(), true);
        let inputs = |i: usize| {
            let mut rng = Rng(i as u64 + seed);
            std::array::from_fn::<u32, COMPRESS_INPUTS, _>(|_| rng.next_u64() as u32)
        };
        let w = Witness::new(&inner, rows, |c| _ = compress_row(c), inputs, &Fixed::default());
        let (proof, _) = prove(&inner, &p, &domain, w, None, &[]);
        let table = Table { circuit: &inner, rows, public: &[] };
        let replay = verify_logged(&p, &domain, &[table], None, &proof).unwrap();
        (p, proof, replay)
    }

    /// The rows and program of a proof's verifier's hashing, sending
    /// nothing.
    fn rows_of_a_proof(seed: u64) -> (Vec<[u32; INPUTS]>, Vec<u32>) {
        let (p, proof, replay) = a_proof(seed);
        let mut trace = Trace::new(false);
        trace.verifier(&p, &proof, None, &replay.log, &replay.indices);
        assert!(trace.transcript > 100 && trace.openings > 100);
        trace.finish(128)
    }

    struct Outer {
        circuit: Circuit,
        params: Params,
        domain: Domain,
        program: Program,
    }

    impl Outer {
        fn new(program: Vec<u32>) -> Outer {
            let circuit = circuit();
            let rows = program.len() / circuit.program_width();
            let params = Params::plain(variables(&circuit, rows), 1, 4, 4);
            let domain = Domain::new(params.k(), true);
            let program = Program::new(&circuit, &params, &domain, program);
            Outer { circuit, params, domain, program }
        }

        /// Whether `rows` are proven against the program. The witness is
        /// made against `against`, the program the prover works to.
        fn proves(&self, rows: &[[u32; INPUTS]], against: &[u32]) -> bool {
            let fixed = Fixed { program: against, public: &[] };
            let w = Witness::new(&self.circuit, rows.len(), |ctx| _ = row(ctx), |i| rows[i], &fixed);
            let holds = w.holds();
            let (proof, _) = prove(&self.circuit, &self.params, &self.domain, w, Some(&self.program), &[]);
            let root = self.program.root();
            let statement = Statement { program: Some(&root), public: &[] };
            let ok = verify(&self.circuit, &self.params, &self.domain, rows.len(), &proof, &statement).is_some();
            assert!(!ok || holds, "a proof that verifies is of rows that hold");
            ok
        }
    }

    #[test]
    fn the_hashing_of_a_verifier_is_proven_and_nothing_else_is() {
        let c = circuit();
        assert_eq!((c.cols, c.constraints.len(), c.program_cols), (24 + 336 + 112 + 8 + 31, 456 + 38, 28));
        assert_eq!((c.log_cols, c.log_constraints, c.program_width()), (9, 9, 32));
        assert_eq!((c.products.len(), c.sends.len(), c.receives.len()), (10, 11, 1));
        let (rows, program) = rows_of_a_proof(7);
        let outer = Outer::new(program.clone());
        assert!(outer.proves(&rows, &program));
        let width = c.program_width();
        let flag = |r: usize, i: usize| program[r * width + i] != 0;
        // A transcript step that does not take the last state.
        let at = (0..rows.len()).find(|r| flag(*r, 4)).unwrap();
        let mut bad = rows.clone();
        bad[at][8] ^= 1;
        assert!(!outer.proves(&bad, &program));
        // The other order at one level of a path, the index as it was;
        // an index that is not the last row's, shifted; a chaining value
        // that is not the domain's key.
        let node = (0..rows.len()).find(|r| flag(*r, 5)).unwrap();
        let mut bad = rows.clone();
        let (l, r) = bad[node][8..24].split_at_mut(8);
        l.swap_with_slice(r);
        assert!(!outer.proves(&bad, &program));
        let mut bad = rows.clone();
        bad[node + 1][26] ^= 2;
        assert!(!outer.proves(&bad, &program));
        let mut bad = rows.clone();
        bad[node][0] ^= 1;
        assert!(!outer.proves(&bad, &program));
        // Something sent that the program does not send.
        let mut bad = rows.clone();
        bad[node][43] = 1;
        assert!(!outer.proves(&bad, &program));
        // The prover works to a program of its own, under which its rows
        // hold: a leaf's second block hashed as the start of an input.
        // The program committed is not that one.
        let chained = (0..rows.len()).find(|r| flag(*r, 3) && rows[*r][26] != 0).unwrap();
        let mut own = program.clone();
        own[chained * width + 3] = 0;
        let mut bad = rows.clone();
        bad[chained][..8].copy_from_slice(&domain_key(DOM_LEAF));
        assert!(!outer.proves(&bad, &own));
    }

    #[test]
    fn the_program_is_the_same_for_every_proof() {
        // Two proofs of one shape: other rows, one program.
        let (rows_a, program_a) = rows_of_a_proof(7);
        let (rows_b, program_b) = rows_of_a_proof(8);
        assert_ne!(rows_a, rows_b);
        assert_eq!(program_a, program_b);
        let outer = Outer::new(program_a.clone());
        assert!(outer.proves(&rows_b, &program_a));
    }

    /// The rows of the two tables, the hash table's and the machine's,
    /// that show a proof's openings to be of what its transcript took in
    /// and gave: every path's top is the root absorbed, every query's
    /// index is the one the transcript made, each opening's index is the
    /// one before's shifted, and an index is the path's part of it and
    /// the bits above.
    struct Bound {
        hash: (Vec<[u32; INPUTS]>, Vec<u32>),
        machine: machine::Rows,
    }

    fn bind(p: &Params, proof: &argument::Proof, replay: &argument::Replay, spoil: usize) -> Bound {
        let steps = p.steps();
        let mut trace = Trace::new(true);
        let mut asm = Assembly::default();
        // The transcript. A root is the two elements a step took in after
        // the commitment's own step or a round's; an index is the low
        // bits of the output of each of the last steps.
        let queries = replay.indices.len();
        let all_roots: Vec<&Digest> = std::iter::once(&proof.root).chain(&proof.pcs.roots).collect();
        let root_steps: Vec<usize> = replay
            .log
            .iter()
            .enumerate()
            .filter(|(_, s)| all_roots.iter().any(|r| s.input[32..] == r[..]))
            .map(|(i, _)| i)
            .collect();
        let first_index = replay.log.len() - queries;
        let mut roots: Vec<[machine::Value; 2]> = Vec::new();
        let mut lows = Vec::new();
        let elem = |bytes: &[u8]| F::from_bytes(bytes.try_into().unwrap());
        for (i, step) in replay.log.iter().enumerate() {
            let is_root = root_steps.contains(&i);
            let stepped = trace.step(step, i == 0, is_root, false, i >= first_index, 0);
            if i == 0 {
                // The state the transcript begins from is sent; here it
                // is read and nothing made of it.
                for (h, at) in stepped.state.iter().enumerate() {
                    asm.outside(*at, elem(&step.input[16 * h..16 * h + 16]));
                }
            }
            if is_root {
                let halves = [elem(&step.input[32..48]), elem(&step.input[48..64])];
                roots.push(std::array::from_fn(|h| asm.outside(stepped.data[h], halves[h])));
            }
            if i >= first_index {
                lows.push((stepped.low, F((blake3::words::<8>(&trace.last())[0] & 0x7FFF_FFFF) as u128)));
            }
        }
        // The roots absorbed: the commitment's first, then each folded
        // codeword's, in the order the openings are of.
        assert_eq!(roots.len(), steps.len());
        for (q, (low_at, low)) in lows.into_iter().enumerate() {
            let mut raw = asm.outside(low_at, low);
            let mut index = low.0 as u32;
            let mut clean = replay.indices[q];
            let mut layer = 0;
            for (t, s) in steps.iter().enumerate() {
                if t > 0 {
                    clean >>= s;
                }
                let height = p.k() - layer - s;
                // The opening, by its own path out of the batch.
                let batch = &proof.pcs.openings[t];
                let mut distinct: Vec<usize> = replay.indices.iter().map(|i| i >> (layer + s - steps[0])).collect();
                distinct.sort_unstable();
                distinct.dedup();
                let hashes: Vec<Digest> = batch.leaves.iter().map(|l| merkle::leaf_hash(l)).collect();
                let paths = merkle::batch_paths(&distinct, &hashes, height, &batch.siblings);
                let at = distinct.binary_search(&clean).unwrap();
                let shift = steps.get(t + 1).copied().unwrap_or(0);
                // The machine sends the opening its index, and reads
                // what the opening sends.
                let index_at = asm.send(raw);
                let opened = trace.opening(&batch.leaves[at], index, &paths[at], index_at, false, shift, true);
                let top = blake3::words::<8>(&trace.last());
                let half = |h: usize| F(top[4 * h..4 * h + 4].iter().rev().fold(0u128, |x, w| x << 32 | *w as u128));
                for (h, root) in roots[t].iter().enumerate() {
                    let reached = asm.outside(opened.top[h], half(h) + F((spoil == 1 + q) as u128));
                    asm.equal(reached, *root);
                }
                // The index is the path's part of it and what is above:
                // `raw = clean + x^height high`.
                let high = asm.outside(opened.high, F((index >> height) as u128));
                let power = trace.constant(F(1 << height));
                let power = asm.outside(power, F(1 << height));
                let low_part = asm.op(high, machine::Operand::None, power, raw);
                let expect = asm.input(F(clean as u128));
                asm.equal(low_part, expect);
                // Every shift of the index is read; the last is the next
                // opening's.
                for at in &opened.shifted {
                    index >>= 1;
                    raw = asm.outside(*at, F(index as u128));
                }
                layer += s;
            }
        }
        Bound { hash: trace.finish(128), machine: asm.finish(128) }
    }

    /// Whether the two tables are proven together.
    fn bound_proves(b: &Bound) -> bool {
        let (hash, machine) = (circuit(), machine::circuit());
        let (hash_rows, machine_rows) = (b.hash.0.len(), b.machine.inputs.len());
        let tables = [(&hash, hash_rows), (&machine, machine_rows)];
        let layout = Layout::of(tables.iter().copied()).expect("the hash table is the larger");
        let params = Params::plain(layout.total, 1, 4, 4);
        let domain = Domain::new(params.k(), true);
        let program = Program::of(&params, &domain, &tables, vec![b.hash.1.clone(), b.machine.program.clone()]);
        let fixed = [
            Fixed { program: &program.words[0], public: &[] },
            Fixed { program: &program.words[1], public: &machine::NO_PUBLIC },
        ];
        let parts = vec![
            Part {
                circuit: &hash,
                witness: Witness::new(&hash, hash_rows, |c| _ = row(c), |i| b.hash.0[i], &fixed[0]),
                public: &[],
            },
            Part {
                circuit: &machine,
                witness: Witness::new(&machine, machine_rows, |c| machine::run(c), |i| b.machine.inputs[i], &fixed[1]),
                public: &machine::NO_PUBLIC,
            },
        ];
        let (proof, _) = prove_tables(&params, &domain, parts, Some(&program));
        let tables = [
            Table { circuit: &hash, rows: hash_rows, public: &[] },
            Table { circuit: &machine, rows: machine_rows, public: &machine::NO_PUBLIC },
        ];
        verify_tables(&params, &domain, &tables, Some(&program.root()), &proof).is_some()
    }

    #[test]
    fn openings_are_of_what_the_transcript_took_in_and_gave() {
        let (p, proof, replay) = a_proof(7);
        let good = bind(&p, &proof, &replay, 0);
        assert!(good.machine.holds);
        assert!(bound_proves(&good));
        // Another proof of the shape: the same two programs.
        let (p2, proof2, replay2) = a_proof(8);
        let other = bind(&p2, &proof2, &replay2, 0);
        assert_eq!((&other.hash.1, &other.machine.program), (&good.hash.1, &good.machine.program));
        // The machine told a path reached something else than it did:
        // what it reads is not what the hash table sends.
        let lied = bind(&p, &proof, &replay, 1);
        assert!(!bound_proves(&lied));
        // An opening of another leaf than the transcript's index says:
        // the paths are right, each for its own index, and the first
        // codeword's is not the index the transcript gave.
        let mut replay3 = verify_logged_again(&p, &proof);
        replay3.indices.swap(0, 1);
        if replay3.indices[0] != replay3.indices[1] {
            let swapped = bind(&p, &proof, &replay3, 0);
            assert!(!swapped.machine.holds);
            assert!(!bound_proves(&swapped));
        }
    }

    fn verify_logged_again(p: &Params, proof: &argument::Proof) -> argument::Replay {
        let inner = blake3_circuit();
        let domain = Domain::new(p.k(), false);
        let table = Table { circuit: &inner, rows: 128, public: &[] };
        verify_logged(p, &domain, &[table], None, proof).unwrap()
    }

    /// A proof of compressions, then proofs each of the hashing of
    /// verifying two of the proof below, at the proven parameters: what
    /// the hashing of a chain step costs, and that it comes to a size
    /// that stays.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn fixed_point_timing() {
        let security = crate::pcs::SECURITY;
        let mut circuit = blake3_circuit();
        let mut rows = 1 << 13;
        let mut params = Params::proven(variables(&circuit, rows), 2, security);
        let mut domain = Domain::new(params.k(), true);
        let inputs = |i: usize| {
            let mut rng = Rng(i as u64 + 1);
            std::array::from_fn::<u32, COMPRESS_INPUTS, _>(|_| rng.next_u64() as u32)
        };
        let w = Witness::new(&circuit, rows, |c| _ = compress_row(c), inputs, &Fixed::default());
        let t = std::time::Instant::now();
        let (mut proof, _) = prove(&circuit, &params, &domain, w, None, &[]);
        println!("level 0: 2^13 compressions proven in {:.2?}, {} KB", t.elapsed(), proof.size() / 1000);
        let mut root: Option<Digest> = None;
        for level in 1..=3 {
            let table = Table { circuit: &circuit, rows, public: &[] };
            let replay = verify_logged(&params, &domain, &[table], root.as_ref(), &proof).expect("it verifies");
            let mut trace = Trace::new(false);
            for _ in 0..2 {
                trace.verifier(&params, &proof, root.as_ref(), &replay.log, &replay.indices);
            }
            let (transcript, openings) = (trace.transcript, trace.openings);
            let (inputs, program) = trace.finish(128);
            circuit = super::circuit();
            rows = inputs.len();
            params = Params::proven(variables(&circuit, rows), 2, security);
            domain = Domain::new(params.k(), true);
            let t = std::time::Instant::now();
            let committed = Program::new(&circuit, &params, &domain, program);
            let program_time = t.elapsed();
            let fixed = Fixed { program: &committed.words[0], public: &[] };
            let t = std::time::Instant::now();
            let w = Witness::new(&circuit, rows, |ctx| _ = row(ctx), |i| inputs[i], &fixed);
            let (next, times) = prove(&circuit, &params, &domain, w, Some(&committed), &[]);
            let proved = t.elapsed();
            root = Some(committed.root());
            let statement = Statement { program: root.as_ref(), public: &[] };
            let t = std::time::Instant::now();
            let work = verify(&circuit, &params, &domain, rows, &next, &statement).expect("it verifies");
            println!(
                "level {level}: {transcript} rows of transcript and {openings} of openings in 2^{} ({}% full); \
                 proven in {proved:.2?} (commit {:.2?}, zerocheck {:.2?}, open {:.2?}; the program, once, {program_time:.2?}), \
                 {} KB, verified in {:.2?}: {} compressions",
                rows.trailing_zeros(),
                100 * (transcript + openings) / rows,
                times.commit,
                times.zerocheck,
                times.open,
                next.size() / 1000,
                t.elapsed(),
                work.compressions
            );
            proof = next;
        }
    }
}
