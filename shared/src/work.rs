//! The proof of work's dataset items, as rows of a circuit: the proof
//! that the items a header's work read are made from the seed text
//! ([`crate::pow`]).
//!
//! A row is one step of an item: a keyed hash whose key is the last
//! row's output (or, at an item's first row, the item's index under its
//! mark) and whose block is the window of the text the key picks. The
//! last row of an item sends the item, its last two keys; the first
//! sends its index.
//!
//! # Reading the text
//!
//! The table has a row for every window of the text, and row `i`'s
//! program holds window `i`. A step reads whichever window its key
//! picks, any number of times; so the text is read as a memory is
//! checked: each window is put on the bus once with a count of one and
//! taken back once with its last count, and a read takes a window with
//! a count and puts it back with the count times a fixed element. What
//! was read is then what the program holds, or the tuples do not
//! balance: a window that was never put there has nothing to be taken
//! from. (A sum of inverses, the usual lookup, would not do in a field
//! of characteristic two, where two equal reads cancel.)
//!
//! Every row is a step and a read, the rows that fill the table too: an
//! item more than the work needs, which nobody takes.

use crate::blake3::{self, CHUNK_END, CHUNK_START, KEYED_HASH, ROOT};
use crate::circuit::{Circuit, Ctx, Expr, Sum, Symbolic, compress};
use crate::field::F;
use crate::hash::DOM_POW_ITEM;
use crate::pow::{Item, LOG_WINDOWS, SeedText, WINDOWS, first_key};

/// Words a row takes as inputs.
pub const INPUTS: usize = 54;
/// Words of program a row reads.
pub const PROGRAM: usize = 32;
/// What a read multiplies a window's count by.
pub const COUNT: F = F(2);

const FLAGS: u32 = KEYED_HASH | CHUNK_START | CHUNK_END | ROOT;
const FIRST: u32 = 1;
const LAST: u32 = 2;

struct Row<V> {
    cv: [V; 8],
    m: [V; 16],
    out: [V; 8],
    /// The window read; its count as taken and as put back; and the
    /// last count of the window this row holds.
    window: V,
    count: [V; 4],
    inverse: [V; 4],
    last: [V; 4],
    /// The item, as the item's last row sends it, and the index as its
    /// first does.
    item: [V; 16],
    index: V,
    /// The window this row holds, and which it is.
    text: [V; 16],
    at: V,
    /// Masks: the row goes on from the last, or is an item's first; a
    /// bit for an item's first row and one for its last; the addresses
    /// of the item's four elements and of the index.
    goes_on: V,
    first: V,
    bits: V,
    item_at: [V; 4],
    index_at: V,
}

fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
    let cv: [C::V; 8] = std::array::from_fn(|_| c.input());
    let m: [C::V; 16] = std::array::from_fn(|_| c.input());
    let zero = c.constant(0);
    let t = [zero.clone(), zero, c.constant(64), c.constant(FLAGS)];
    let hash = compress(c, cv.clone(), m.clone(), t);
    let window = c.input();
    let count = std::array::from_fn(|_| c.input());
    let inverse = std::array::from_fn(|_| c.input());
    let last = std::array::from_fn(|_| c.input());
    let item = std::array::from_fn(|_| c.input());
    let index = c.input();
    let text = std::array::from_fn(|_| c.program());
    let at = c.program();
    let (goes_on, first, bits) = (c.program(), c.program(), c.program());
    let item_at = std::array::from_fn(|_| c.program());
    let index_at = c.program();
    for _ in 25..PROGRAM {
        c.program();
    }
    Row {
        cv,
        m,
        out: hash.out,
        window,
        count,
        inverse,
        last,
        item,
        index,
        text,
        at,
        goes_on,
        first,
        bits,
        item_at,
        index_at,
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
            let con = Expr::constant;
            // The key: the last row's output, or an item's index under
            // its mark.
            for i in 0..8 {
                s.zero_where(&r.goes_on, r.cv[i].xor(&r.out[i].prev()));
                if i > 0 {
                    s.zero_where(&r.first, r.cv[i].xor(&con(if i == 2 { DOM_POW_ITEM } else { 0 })));
                }
            }
            // The window the key picks.
            s.constrain(r.cv[0].clone(), con(WINDOWS as u32 - 1), r.window.clone());
            let elements = |words: &[Expr]| -> Vec<Sum> { words.chunks(4).map(Sum::element).collect() };
            let tuple = |at: &Expr, words: &[Expr], count: Sum| -> Vec<Sum> {
                std::iter::once(Sum::word(at)).chain(elements(words)).chain([count]).collect()
            };
            // The text: this row's window put on the bus with a count of
            // one, and taken back with its last.
            s.send(tuple(&r.at, &r.text, Sum::constant(F::ONE)));
            s.receive(tuple(&r.at, &r.text, Sum::element(&r.last)));
            // The read: the block is a window taken with a count, and put
            // back with the count times the fixed element. The count is
            // not zero, having an inverse: with none, what is put back
            // is what was taken, and the block is nobody's text.
            s.product(Sum::element(&r.count), Sum::element(&r.inverse), Sum::constant(F::ONE));
            s.receive(tuple(&r.window, &r.m, Sum::element(&r.count)));
            s.send(tuple(&r.window, &r.m, Sum::element(&r.count).scaled(COUNT)));
            // The item, from its last row: the output and the key. The
            // index, from its first.
            let bit = |b: u32| Sum::bits(&r.bits, b.trailing_zeros() as usize, 1);
            let both: Vec<Expr> = r.out.iter().chain(&r.cv).cloned().collect();
            for (i, part) in elements(&both).into_iter().enumerate() {
                let copy = Sum::element(&r.item[4 * i..4 * i + 4]);
                s.product(part, bit(LAST), copy.clone());
                s.send(vec![Sum::word(&r.item_at[i]), copy]);
            }
            s.product(Sum::word(&r.cv[0]), bit(FIRST), Sum::word(&r.index));
            s.send(vec![Sum::word(&r.index_at), Sum::word(&r.index)]);
            core
        },
        INPUTS,
    )
}

/// How often each window has been read: by the steps here, and by
/// whoever else reads the text on the same bus.
pub struct Reads(pub Vec<u32>);

impl Default for Reads {
    fn default() -> Reads {
        Reads(vec![0; WINDOWS])
    }
}

fn power(mut e: u32) -> F {
    let (mut base, mut out) = (COUNT, F::ONE);
    while e > 0 {
        if e & 1 == 1 {
            out *= base;
        }
        base = base.square();
        e >>= 1;
    }
    out
}

fn element(x: F) -> [u32; 4] {
    std::array::from_fn(|j| (x.0 >> (32 * j)) as u32)
}

impl Reads {
    /// A read of window `w`: its count as it is taken, and that
    /// count's inverse. (It is put back with the count times
    /// [`COUNT`].)
    pub fn read(&mut self, w: usize) -> ([u32; 4], [u32; 4]) {
        self.0[w] += 1;
        let count = power(self.0[w] - 1);
        (element(count), element(count.inv()))
    }
}

/// The addresses an item's rows send under: its four elements, and its
/// index.
#[derive(Clone, Copy, Debug)]
pub struct ItemAt {
    pub item: [u32; 4],
    pub index: u32,
}

/// The rows as their inputs and their program, item after item.
#[derive(Default)]
pub struct Steps {
    pub rows: Vec<[u32; INPUTS]>,
    pub program: Vec<[u32; PROGRAM]>,
}

impl Steps {
    /// The steps of item `index`, which reads `text`; what it sends
    /// goes under `at` (nothing, for none). The item.
    pub fn item(&mut self, text: &SeedText, reads: &mut Reads, index: usize, at: Option<ItemAt>) -> Item {
        let parents = text.params().parents;
        let (mut key, mut before) = (first_key(index), [0u32; 8]);
        for step in 0..parents {
            let w = key[0] as usize & (WINDOWS - 1);
            let block: [u32; 16] = blake3::words(text.window(w));
            let out = blake3::compress(&key, &block, 0, 64, FLAGS);
            let (first, last) = (step == 0, step == parents - 1);
            let (count, inverse) = reads.read(w);
            let mut r = [0u32; INPUTS];
            r[..8].copy_from_slice(&key);
            r[8..24].copy_from_slice(&block);
            r[24] = w as u32;
            r[25..29].copy_from_slice(&count);
            r[29..33].copy_from_slice(&inverse);
            let sends = at.filter(|_| last);
            if sends.is_some() {
                r[37..45].copy_from_slice(&out);
                r[45..53].copy_from_slice(&key);
            }
            let named = at.filter(|_| first);
            if named.is_some() {
                r[53] = key[0];
            }
            let mut p = [0u32; PROGRAM];
            (p[17], p[18]) = (if first { 0 } else { !0 }, if first { !0 } else { 0 });
            p[19] = if named.is_some() { FIRST } else { 0 } | if sends.is_some() { LAST } else { 0 };
            if let Some(at) = sends {
                p[20..24].copy_from_slice(&at.item);
            }
            if let Some(at) = named {
                p[24] = at.index;
            }
            self.rows.push(r);
            self.program.push(p);
            (before, key) = (key, out);
        }
        std::array::from_fn(|i| if i < 8 { key[i] } else { before[i - 8] })
    }

    /// The rows filled to one a window with steps of items nobody takes,
    /// each holding its window and that window's last count (`reads`
    /// must by now have every read of the text there is), and the
    /// program as words.
    pub fn finish(mut self, text: &SeedText, reads: &mut Reads) -> (Vec<[u32; INPUTS]>, Vec<u32>) {
        let parents = text.params().parents;
        assert!(self.rows.len() <= WINDOWS, "more steps than the text has windows");
        let mut filler = 0;
        while self.rows.len() < WINDOWS {
            // An item's steps, cut short where the table ends.
            let mut more = Steps::default();
            more.item(text, &mut Reads(reads.0.clone()), filler, None);
            let take = (WINDOWS - self.rows.len()).min(parents);
            for (r, p) in more.rows[..take].iter().zip(&more.program) {
                let w = r[24] as usize;
                let (count, inverse) = reads.read(w);
                let mut r = *r;
                r[25..29].copy_from_slice(&count);
                r[29..33].copy_from_slice(&inverse);
                self.rows.push(r);
                self.program.push(*p);
            }
            filler += 1;
        }
        for (i, (r, p)) in self.rows.iter_mut().zip(&mut self.program).enumerate() {
            r[33..37].copy_from_slice(&element(power(reads.0[i])));
            p[..16].copy_from_slice(&blake3::words::<16>(text.window(i)));
            p[16] = i as u32;
        }
        let _ = LOG_WINDOWS;
        (self.rows, self.program.concat())
    }
}

// ---------------------------------------------------------------------------
// The accesses
// ---------------------------------------------------------------------------

/// The mixing of a header's work, as rows of a second circuit: a row an
/// access. It takes the two items the access reads and their indices
/// off the bus (the steps' table sends them), reads a window of the
/// text as the steps do, and folds all three into the mix: each word
/// times the prime, less carries a sum of five shifts of it. The first
/// row's mix is the seed, taken off the bus; the last row sends the mix.
pub mod mix {
    use super::*;
    use crate::circuit::{Pre, Term};
    use crate::pow::{ItemSource, PowParams};

    /// Words a row takes as inputs.
    pub const INPUTS: usize = 512;
    /// Words of program a row reads.
    pub const PROGRAM: usize = 32;
    /// Rows: an access each, and as many again that fill the table.
    pub const ROWS: usize = 128;

    /// The prime is one and these powers of two: `0x01000193`.
    const FNV_SHIFTS: [u8; 5] = [1, 4, 7, 8, 24];

    struct Row<V> {
        mix: [V; 32],
        seed: [V; 8],
        seed_taken: [V; 8],
        items: [V; 32],
        window: [V; 16],
        count: [V; 4],
        inverse: [V; 4],
        out: [V; 32],
        /// For each product by the prime (the 32 words, then the two
        /// selectors): five shifts and five words of carries.
        products: Vec<[V; 10]>,
        pair: V,
        picked: V,
        sent: [V; 32],
        /// The mask of a pair's index, which says how large the table
        /// is: in a row that is an access, and nothing in one that is
        /// not. And the same as the first row takes it.
        masked: V,
        mask_taken: V,
        /// The access's number; masks for the first row and the others;
        /// a mask for a row that is an access; bits for the first row,
        /// the last and a row that is an access; the addresses; a mask
        /// for an access after the first; where the pairs' mask is
        /// taken from.
        number: V,
        first: V,
        goes_on: V,
        access: V,
        bits: V,
        seed_at: [V; 2],
        item_at: [V; 8],
        index_at: [V; 2],
        out_at: [V; 8],
        later: V,
        mask_at: V,
    }

    const FIRST: u32 = 1;
    const LAST: u32 = 2;
    const ACCESS: u32 = 4;

    fn row<C: Ctx>(c: &mut C) -> Row<C::V> {
        macro_rules! words {
            ($n:expr) => {
                std::array::from_fn::<C::V, $n, _>(|_| c.input())
            };
        }
        let (mix, seed, seed_taken, items, window) = (words!(32), words!(8), words!(8), words!(32), words!(16));
        let (count, inverse, out) = (words!(4), words!(4), words!(32));
        let products = (0..34).map(|_| words!(10)).collect();
        let (pair, picked, sent) = (c.input(), c.input(), words!(32));
        let (masked, mask_taken) = (c.input(), c.input());
        let (number, first, goes_on, access, bits) = (c.program(), c.program(), c.program(), c.program(), c.program());
        let seed_at = std::array::from_fn(|_| c.program());
        let item_at = std::array::from_fn(|_| c.program());
        let index_at = std::array::from_fn(|_| c.program());
        let out_at = std::array::from_fn(|_| c.program());
        let (later, mask_at) = (c.program(), c.program());
        for _ in 27..PROGRAM {
            c.program();
        }
        Row {
            mix,
            seed,
            seed_taken,
            items,
            window,
            count,
            inverse,
            out,
            products,
            pair,
            picked,
            sent,
            masked,
            mask_taken,
            number,
            first,
            goes_on,
            access,
            bits,
            seed_at,
            item_at,
            index_at,
            out_at,
            later,
            mask_at,
        }
    }

    /// The row a [`crate::circuit::Concrete`] runs.
    pub fn run<C: Ctx>(c: &mut C) {
        row(c);
    }

    fn turned_left(x: &Expr, by: u8) -> Expr {
        let terms = x.terms.iter().map(|t| Term { rot: (t.rot + 32 - by) % 32, ..*t }).collect();
        Expr { terms, constant: x.constant.rotate_left(by as u32) }
    }

    /// `x` times the prime: `x` and five shifts of it, added. `words`
    /// are the shifts and the carries.
    fn times_prime(s: &mut Symbolic, x: &Expr, words: &[Expr; 10]) -> Expr {
        let mut sum = x.clone();
        for (i, by) in FNV_SHIFTS.iter().enumerate() {
            s.constrain(turned_left(x, *by), Expr::constant(!0 << by), words[i].clone());
            let carry = &words[5 + i];
            let into = Expr { terms: vec![Term { pre: Pre::Shl, ..carry.terms[0] }], constant: 0 };
            s.constrain(sum.xor(&into), words[i].xor(&into), carry.xor(&into));
            sum = sum.xor(&words[i]).xor(&into);
        }
        sum
    }

    pub fn circuit() -> Circuit {
        Circuit::new(
            |s: &mut Symbolic| {
                let r = row(s);
                let core = s.constraints.len();
                let con = Expr::constant;
                let ones = con(!0);
                for k in 0..32 {
                    // The mix: the row before's, or the seed in the first.
                    s.zero_where(&r.goes_on, r.mix[k].xor(&r.out[k].prev()));
                    s.zero_where(&r.first, r.mix[k].xor(&r.seed[k % 8]));
                    // Each word: times the prime, with the item's word and
                    // the window's.
                    let product = times_prime(s, &r.mix[k], &r.products[k]);
                    s.zero_where(&ones, r.out[k].xor(&product).xor(&r.items[k]).xor(&r.window[k % 16]));
                }
                for j in 0..8 {
                    s.zero_where(&r.goes_on, r.seed[j].xor(&r.seed[j].prev()));
                }
                // The selectors: of the access's number and the seed, and
                // of the mix.
                let pick = times_prime(s, &r.seed[0].xor(&r.number), &r.products[32]).xor(&r.mix[0]);
                // (Under the mask of a pair's index: how large the table
                // is. It is no part of the program, which is then one
                // for a table of any size: it is the same in every
                // access, nothing in a row that is none, and what the
                // first row takes it to be, which the work states.)
                s.constrain(pick, r.masked.clone(), r.pair.clone());
                s.zero_where(&r.access.xor(&ones), r.masked.clone());
                s.zero_where(&r.later, r.masked.xor(&r.masked.prev()));
                let pick = times_prime(s, &r.seed[1].xor(&r.number), &r.products[33]).xor(&r.mix[16]);
                s.constrain(pick, con(WINDOWS as u32 - 1), r.picked.clone());

                let bit = |b: u32| Sum::bits(&r.bits, b.trailing_zeros() as usize, 1);
                let elements = |words: &[Expr]| -> Vec<Sum> { words.chunks(4).map(Sum::element).collect() };
                // The seed, taken by the first row.
                for h in 0..2 {
                    let taken = Sum::element(&r.seed_taken[4 * h..4 * h + 4]);
                    s.product(Sum::element(&r.seed[4 * h..4 * h + 4]), bit(FIRST), taken.clone());
                    s.receive(vec![Sum::word(&r.seed_at[h]), taken]);
                }
                s.product(Sum::word(&r.masked), bit(FIRST), Sum::word(&r.mask_taken));
                s.receive(vec![Sum::word(&r.mask_at), Sum::word(&r.mask_taken)]);
                // The two items, and that they are the pair picked: the
                // even item of the pair, and the one after it.
                for (e, part) in elements(&r.items).into_iter().enumerate() {
                    s.receive(vec![Sum::word(&r.item_at[e]), part]);
                }
                let even = Sum::word(&r.pair).scaled(F(2));
                s.receive(vec![Sum::word(&r.index_at[0]), even.clone()]);
                s.receive(vec![Sum::word(&r.index_at[1]), even.add(&bit(ACCESS))]);
                // The window, read as the steps read theirs.
                s.product(Sum::element(&r.count), Sum::element(&r.inverse), Sum::constant(F::ONE));
                let read = |count: Sum| -> Vec<Sum> {
                    std::iter::once(Sum::word(&r.picked)).chain(elements(&r.window)).chain([count]).collect()
                };
                s.receive(read(Sum::element(&r.count)));
                s.send(read(Sum::element(&r.count).scaled(COUNT)));
                // The mix, sent by the last row.
                for (e, part) in elements(&r.out).into_iter().enumerate() {
                    let copy = Sum::element(&r.sent[4 * e..4 * e + 4]);
                    s.product(part, bit(LAST), copy.clone());
                    s.send(vec![Sum::word(&r.out_at[e]), copy]);
                }
                core
            },
            INPUTS,
        )
    }

    /// The addresses the rows take and send under.
    #[derive(Clone, Debug)]
    pub struct At {
        /// Of the seed's two halves, taken.
        pub seed: [u32; 2],
        /// Of each access's two items: their eight elements, and their
        /// two indices.
        pub items: Vec<([u32; 8], [u32; 2])>,
        /// Of the mix's eight elements, sent.
        pub out: [u32; 8],
        /// Of the mask of a pair's index, taken.
        pub mask: u32,
    }

    /// The shifts and carries of a product by the prime, and the product.
    fn product_words(x: u32) -> ([u32; 10], u32) {
        let mut words = [0u32; 10];
        let mut sum = x;
        for (i, by) in FNV_SHIFTS.iter().enumerate() {
            let y = x << by;
            let (carry, next) = carries(sum, y);
            (words[i], words[5 + i]) = (y, carry);
            sum = next;
        }
        (words, sum)
    }

    fn carries(x: u32, y: u32) -> (u32, u32) {
        let sum = x.wrapping_add(y);
        let into = x ^ y ^ sum;
        ((x & y) | ((x ^ y) & into), sum)
    }

    /// The rows of the accesses of the work whose seed is `seed`, with
    /// `source` for the items (it says the table's size) and the text:
    /// the rows, the program, the indices of the items read in order, and
    /// the mix they end with.
    #[allow(clippy::type_complexity)]
    pub fn rows<S: ItemSource>(
        source: &S,
        reads: &mut Reads,
        seed: [u32; 8],
        at: &At,
    ) -> (Vec<[u32; INPUTS]>, Vec<u32>, Vec<usize>, [u32; 32]) {
        let params: &PowParams = source.params();
        assert!(params.accesses <= ROWS);
        let pairs = super::pairs_mask(source.log_items());
        let text = source.seed();
        let mut mix: [u32; 32] = std::array::from_fn(|k| seed[k % 8]);
        let (mut rows, mut program, mut indices) = (Vec::new(), Vec::new(), Vec::new());
        let mut last = mix;
        for i in 0..ROWS {
            let access = i < params.accesses;
            let mut r = [0u32; INPUTS];
            let mut p = [0u32; PROGRAM];
            r[..32].copy_from_slice(&mix);
            r[32..40].copy_from_slice(&seed);
            let mut products = [[0u32; 10]; 34];
            let (words, picked) = product_words(seed[0] ^ i as u32);
            products[32] = words;
            let pair = (picked ^ mix[0]) & if access { pairs } else { 0 };
            let (words, picked) = product_words(seed[1] ^ i as u32);
            products[33] = words;
            let window = ((picked ^ mix[16]) as usize) & (WINDOWS - 1);
            let mut items = [0u32; 32];
            if access {
                let index = 2 * pair as usize;
                indices.extend([index, index + 1]);
                items[..16].copy_from_slice(&source.item(index));
                items[16..].copy_from_slice(&source.item(index + 1));
            }
            let x: [u32; 16] = blake3::words(text.window(window));
            let (count, inverse) = reads.read(window);
            let mut out = [0u32; 32];
            for k in 0..32 {
                let (words, product) = product_words(mix[k]);
                products[k] = words;
                out[k] = product ^ items[k] ^ x[k % 16];
            }
            if i == 0 {
                r[40..48].copy_from_slice(&seed);
            }
            r[48..80].copy_from_slice(&items);
            r[80..96].copy_from_slice(&x);
            r[96..100].copy_from_slice(&count);
            r[100..104].copy_from_slice(&inverse);
            r[104..136].copy_from_slice(&out);
            r[136..476].copy_from_slice(products.as_flattened());
            (r[476], r[477]) = (pair, window as u32);
            let is_last = i + 1 == params.accesses;
            if is_last {
                r[478..510].copy_from_slice(&out);
                last = out;
            }
            (r[510], r[511]) = (if access { pairs } else { 0 }, if i == 0 { pairs } else { 0 });
            (p[0], p[1], p[2], p[3]) =
                (i as u32, if i == 0 { !0 } else { 0 }, if i == 0 { 0 } else { !0 }, if access { !0 } else { 0 });
            (p[25], p[26]) = (if access && i > 0 { !0 } else { 0 }, if i == 0 { at.mask } else { 0 });
            p[4] = if i == 0 { FIRST } else { 0 } | if is_last { LAST } else { 0 } | if access { ACCESS } else { 0 };
            if i == 0 {
                p[5..7].copy_from_slice(&at.seed);
            }
            if access {
                p[7..15].copy_from_slice(&at.items[i].0);
                p[15..17].copy_from_slice(&at.items[i].1);
            }
            if is_last {
                p[17..25].copy_from_slice(&at.out);
            }
            rows.push(r);
            program.push(p);
            mix = out;
        }
        (rows, program.concat(), indices, last)
    }
}

// ---------------------------------------------------------------------------
// A header's work, whole
// ---------------------------------------------------------------------------

/// The mask of a pair's index in a table of `2^log_items` items: what
/// says, in a proof of work, which table the work is of.
pub fn pairs_mask(log_items: u32) -> u32 {
    (1u32 << (log_items - 1)) - 1
}

/// The work's two tables, as rows and programs.
pub struct Work {
    pub steps: (Vec<[u32; INPUTS]>, Vec<u32>),
    pub mix: (Vec<[u32; mix::INPUTS]>, Vec<u32>),
}

/// The check of a header's work, made rows of `cx` and of the work's
/// two tables: the seed hashed from the header's hash and the nonce,
/// the accesses and the items they read, the mix hashed, and the result.
/// The computation is said to be of the header's hash, the nonce, the
/// mix and the result, and of a table of a size: those, as elements,
/// the size as the mask of a pair's index ([`pairs_mask`]). `source`
/// gives the items and says which table the work is of.
pub fn work_into<S: crate::pow::ItemSource>(
    cx: &crate::sym::Shared,
    source: &S,
    header: &crate::hash::Digest,
    nonce: &crate::pow::Nonce,
) -> (Work, Vec<F>) {
    use crate::alg::halves;
    use crate::hash::{DOM_POW_MIX, DOM_POW_RESULT, DOM_POW_SEED, hash_domain};
    use crate::sym::Sym;
    let accesses = source.params().accesses;
    // The seed: hashed by the hash table, read by the machine, which
    // sends it on to the first access.
    let said: Vec<F> = halves(header).into_iter().chain(halves(nonce)).collect();
    let (data, out) = cx.with(|c| c.trace.digest(DOM_POW_SEED, &said));
    let seed_digest = hash_domain(DOM_POW_SEED, &crate::field::as_bytes(&said));
    let of: Vec<Sym> = data.iter().zip(&said).map(|(at, x)| cx.outside(*at, *x)).collect();
    let seed: Vec<Sym> = out.iter().zip(halves(&seed_digest)).map(|(at, x)| cx.outside(*at, x)).collect();
    let reserve = || cx.with(|c| c.trace.reserve());
    let mask = cx.input(F(pairs_mask(source.log_items()) as u128));
    let at = mix::At {
        mask: mask.send(),
        seed: [seed[0].send(), seed[1].send()],
        items: (0..accesses)
            .map(|_| (std::array::from_fn(|_| reserve()), std::array::from_fn(|_| reserve())))
            .collect(),
        out: std::array::from_fn(|_| reserve()),
    };
    let mut reads = Reads::default();
    let (mix_rows, mix_program, indices, last) = mix::rows(source, &mut reads, blake3::words(&seed_digest), &at);
    // The items the accesses read, each by its steps.
    let text = source.seed();
    let mut steps = Steps::default();
    for (j, index) in indices.iter().enumerate() {
        let (items, named) = at.items[j / 2];
        let item_at = ItemAt { item: std::array::from_fn(|e| items[4 * (j % 2) + e]), index: named[j % 2] };
        steps.item(text, &mut reads, *index, Some(item_at));
    }
    let steps = steps.finish(text, &mut reads);
    // The mix, hashed; and with the seed, the result.
    let word = |e: usize| F((0..4).rev().fold(0u128, |x, w| x << 32 | last[4 * e + w] as u128));
    let mixed: Vec<Sym> = (0..8).map(|e| cx.outside(at.out[e], word(e))).collect();
    let mix = cx.hashed(DOM_POW_MIX, &mixed);
    let result = cx.hashed(DOM_POW_RESULT, &[mix[0].clone(), mix[1].clone(), seed[0].clone(), seed[1].clone()]);
    let stated: Vec<Sym> = of.into_iter().chain(mix).chain(result).chain([mask]).collect();
    cx.state(&stated);
    (Work { steps, mix: (mix_rows, mix_program) }, stated.iter().map(Sym::value).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::argument::{Layout, Part, Program, Table, prove_tables, verify_tables};
    use crate::circuit::{Fixed, Witness};
    use crate::ntt::Domain;
    use crate::pcs::Params;
    use crate::pow::PowParams;

    /// A table that takes whatever its rows say: the other end of the
    /// bus, for the items and their indices.
    fn peer() -> Circuit {
        Circuit::new(
            |s: &mut Symbolic| {
                let words: [Expr; 4] = std::array::from_fn(|_| s.input());
                let at = s.program();
                s.receive(vec![Sum::word(&at), Sum::element(&words)]);
                0
            },
            4,
        )
    }

    /// Whether the steps are proven beside a peer that takes `expect`:
    /// each an address and an element.
    fn proves(steps: Steps, reads: &mut Reads, text: &SeedText, expect: &[(u32, [u32; 4])]) -> bool {
        let (rows, program) = steps.finish(text, reads);
        let n = expect.len().next_power_of_two().max(128);
        let mut peer_rows: Vec<[u32; 4]> = expect.iter().map(|e| e.1).collect();
        let mut peer_program: Vec<u32> = expect.iter().map(|e| e.0).collect();
        peer_rows.resize(n, [0; 4]);
        peer_program.resize(n, 0);
        let (work, peer) = (circuit(), peer());
        let tables = [(&work, rows.len()), (&peer, n)];
        let layout = Layout::of(tables.iter().copied()).unwrap();
        let params = Params::plain(layout.total, 1, 4, 4);
        let domain = Domain::new(params.k(), true);
        let committed = Program::of(&params, &domain, &tables, vec![program, peer_program]);
        let fixed =
            [Fixed { program: &committed.words[0], public: &[] }, Fixed { program: &committed.words[1], public: &[] }];
        let a = Witness::new(&work, rows.len(), |c| run(c), |i| rows[i], &fixed[0]);
        let b = Witness::new(
            &peer,
            n,
            |c| _ = std::array::from_fn::<u32, 4, _>(|_| c.input()),
            |i| peer_rows[i],
            &fixed[1],
        );
        let held = a.holds();
        let parts =
            vec![Part { circuit: &work, witness: a, public: &[] }, Part { circuit: &peer, witness: b, public: &[] }];
        let (proof, _) = prove_tables(&params, &domain, parts, Some(&committed));
        let tables =
            [Table { circuit: &work, rows: rows.len(), public: &[] }, Table { circuit: &peer, rows: n, public: &[] }];
        verify_tables(&params, &domain, &tables, Some(&committed.root()), &proof).is_some() && held
    }

    /// Three items' steps, and what they send.
    fn three(text: &SeedText, change: impl Fn(&mut Steps)) -> (Steps, Reads, Vec<(u32, [u32; 4])>) {
        let (mut steps, mut reads) = (Steps::default(), Reads::default());
        let mut expect = Vec::new();
        for (j, index) in [5usize, 6, 900].into_iter().enumerate() {
            let base = 10 * j as u32 + 1;
            let at = ItemAt { item: [base, base + 1, base + 2, base + 3], index: base + 4 };
            let item = steps.item(text, &mut reads, index, Some(at));
            assert_eq!(item, text.calc_dataset_item(index));
            expect.extend((0..4).map(|e| (at.item[e], std::array::from_fn(|w| item[4 * e + w]))));
            expect.push((at.index, [index as u32, 0, 0, 0]));
        }
        change(&mut steps);
        (steps, reads, expect)
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn items_are_proven_to_be_the_text_s() {
        let c = circuit();
        assert!(c.cols <= 512 && c.constraints.len() <= 512, "{} words, {} constraints", c.cols, c.constraints.len());
        assert_eq!((c.log_cols, c.program_width()), (9, PROGRAM));
        let text = SeedText::new(PowParams::DEV);
        let (steps, mut reads, expect) = three(&text, |_| {});
        assert!(proves(steps, &mut reads, &text, &expect));
        // An item that is not the text's is not taken: another item
        // said, or another index.
        let mut other = expect.clone();
        other[0].1[0] ^= 1;
        let (steps, mut reads, _) = three(&text, |_| {});
        assert!(!proves(steps, &mut reads, &text, &other));
        let mut other = expect.clone();
        other[4].1[0] ^= 1;
        let (steps, mut reads, _) = three(&text, |_| {});
        assert!(!proves(steps, &mut reads, &text, &other));
        // A step that hashes something other than the window its key
        // picks: the read has nothing to be taken from.
        let (steps, mut reads, expect) = three(&text, |s| s.rows[40][8 + 3] ^= 1);
        assert!(!proves(steps, &mut reads, &text, &expect));
        // A step that reads another window than its key picks.
        let (steps, mut reads, expect) = three(&text, |s| s.rows[40][24] ^= 1);
        assert!(!proves(steps, &mut reads, &text, &expect));
        // A read with a count of nothing, which is taken and put back
        // as the same thing and so is of no text at all: it has no
        // inverse. (The last row's, whose window none reads after.)
        let (mut steps, mut reads, expect) = three(&text, |_| {});
        let last = steps.rows.last_mut().unwrap();
        last[25..33].fill(0);
        reads.0[last[24] as usize] -= 1;
        assert!(!proves(steps, &mut reads, &text, &expect));
    }

    /// A header's work as rows: they meet their tables' constraints,
    /// and state the work as the miner computes it.
    #[test]
    fn a_header_s_work_is_rows_that_hold() {
        use crate::alg::halves;
        use crate::pow::{hashimoto, nonce_from_u64};
        use crate::sym::Shared;
        let text = SeedText::new(PowParams::DEV);
        let source = text.table(10);
        let (header, nonce) = ([7u8; 32], nonce_from_u64(11));
        let out = hashimoto(&source, &header, &nonce);
        let cx = Shared::new();
        let (work, stated) = work_into(&cx, &source, &header, &nonce);
        // (And of which table: the mask of a pair's index in it.)
        let table = F(pairs_mask(crate::pow::ItemSource::log_items(&source)) as u128);
        let expect: Vec<F> = [header, nonce, out.mix, out.result].iter().flat_map(halves).chain([table]).collect();
        assert_eq!(stated, expect);
        assert!(crate::proof::holds(cx, vec![], Some(work)));
        for (table, row, word) in [(0, 300, 8), (1, 5, 48), (1, 9, 80), (1, 63, 104)] {
            let cx = Shared::new();
            let (mut work, _) = work_into(&cx, &source, &header, &nonce);
            if table == 0 {
                work.steps.0[row][word] ^= 1;
            } else {
                work.mix.0[row][word] ^= 1;
            }
            // Work with an item that is not the text's, or a window that
            // is not: rows that do not hold.
            assert!(!crate::proof::holds(cx, vec![], Some(work)), "table {table} row {row} word {word}");
        }
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_header_s_work_is_proven() {
        use crate::alg::{halves, statement};
        use crate::pow::{hashimoto, nonce_from_u64};
        use crate::sym::Shared;
        let m = mix::circuit();
        assert!(m.cols <= 512 && m.constraints.len() <= 512, "{} words, {} constraints", m.cols, m.constraints.len());
        let text = SeedText::new(PowParams::DEV);
        let source = text.table(10);
        let (header, nonce) = ([7u8; 32], nonce_from_u64(11));
        let out = hashimoto(&source, &header, &nonce);
        let cx = Shared::new();
        let (work, stated) = work_into(&cx, &source, &header, &nonce);
        // What the rows are of is the work as the miner computes it.
        // (And of which table: the mask of a pair's index in it.)
        let table = F(pairs_mask(crate::pow::ItemSource::log_items(&source)) as u128);
        let expect: Vec<F> = [header, nonce, out.mix, out.result].iter().flat_map(halves).chain([table]).collect();
        assert_eq!(stated, expect);
        assert_eq!((work.steps.0.len(), work.mix.0.len()), (WINDOWS, mix::ROWS));
        let p = crate::proof::prove_with(cx, vec![], Some(work), |m| Params::plain(m, 1, 4, 4), [128, 128]);
        assert!(p.holds && p.verifies());
        assert_eq!(p.statement(), statement(&expect));
        // Work with an item that is not the text's, or a window that is
        // not: not proven.
        for (table, row, word) in [(0, 300, 8), (1, 5, 48), (1, 9, 80), (1, 63, 104)] {
            let cx = Shared::new();
            let (mut work, _) = work_into(&cx, &source, &header, &nonce);
            if table == 0 {
                work.steps.0[row][word] ^= 1;
            } else {
                work.mix.0[row][word] ^= 1;
            }
            let p = crate::proof::prove_with(cx, vec![], Some(work), |m| Params::plain(m, 1, 4, 4), [128, 128]);
            assert!(!p.verifies(), "table {table} row {row} word {word}");
        }
    }

    /// No word of the tables of a header's work holds up nothing, in
    /// their first rows, but what the tables send each other holds to
    /// its value, which a table's own constraints say nothing of: the
    /// machine's operands, and of a step the count its window of the
    /// text was last taken with, one element, which nothing but what is
    /// sent speaks of.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn no_word_of_the_work_s_tables_is_left_to_the_prover() {
        use crate::pow::nonce_from_u64;
        use crate::proof::Kind;
        use crate::sym::Shared;
        let text = SeedText::new(PowParams::DEV);
        let cx = Shared::new();
        let (work, _) = work_into(&cx, &text.table(10), &[7u8; 32], &nonce_from_u64(11));
        let (held, free) = crate::proof::audit(cx, vec![], Some(work), 128);
        assert!(held);
        let mut of_steps = std::collections::BTreeSet::new();
        for (kind, row, word) in &free {
            match kind {
                Kind::Machine => assert!(*word < 16, "word {word} of row {row} of the machine"),
                Kind::Steps => _ = of_steps.insert(*word),
                _ => panic!("word {word} of row {row} of {kind:?} holds up nothing"),
            }
        }
        // One element: four words, one after another.
        let words: Vec<usize> = of_steps.into_iter().collect();
        assert_eq!((words.len(), words[3] - words[0]), (4, 3), "{words:?}");
    }
}
