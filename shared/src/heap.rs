//! How much memory the program holds: every allocation counted, and
//! counted to the part of the program it was made for.
//!
//! [`Counting`] is the system's allocator with numbers beside it: the
//! bytes held now and the most ever held, of the whole program and of
//! each [`Part`] of it. A program that makes it its allocator
//! (`#[global_allocator]`, as the node does) can say them at any
//! moment, on any system. Where it is not the allocator (a program
//! that uses the library otherwise) every number is zero.
//!
//! A thread says which part it is working for ([`enter`]); what it
//! allocates meanwhile is that part's, and stays that part's whichever
//! thread frees it: the part is written in sixteen bytes ahead of
//! every allocation (more, for what is aligned to more).
//!
//! What is counted is what was asked for: not those bytes ahead, nor
//! what the system's allocator keeps besides, nor the stacks of
//! threads, nor the program itself. It is the part of a node's memory
//! that the node decides.
//!
//! # Memory of a fixed size
//!
//! One part's large blocks can be kept and not given back ([`pool`]):
//! taken from the system once, when the program starts, and handed out
//! again and again. That is for the part whose work is the same every
//! time, and large: proving, which asks for some tens of gigabytes to
//! make a proof and holds a few of them at once. Nothing that asks for
//! memory is written any differently for it.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

static NOW: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

/// What memory is held for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Part {
    /// Whatever is not said to be another's: the network, the chain,
    /// the store's caches, the logs.
    Node = 0,
    /// The transactions waiting, and what is known of them.
    Pool = 1,
    /// The wallet's tables.
    Wallet = 2,
    /// What proving needs that is the same for every block, made once.
    Setup = 3,
    /// The table of the proof of work.
    Table = 4,
    /// What proving a block holds while it is proven.
    Proving = 5,
    /// Nothing of a node's: for the test of the counting itself.
    #[cfg(test)]
    Test = 6,
}

impl Part {
    /// Every part.
    #[cfg(not(test))]
    pub const ALL: [Part; 6] = [Part::Node, Part::Pool, Part::Wallet, Part::Setup, Part::Table, Part::Proving];
    #[cfg(test)]
    pub const ALL: [Part; 7] =
        [Part::Node, Part::Pool, Part::Wallet, Part::Setup, Part::Table, Part::Proving, Part::Test];

    /// As it is said to whoever runs the node.
    pub fn name(self) -> &'static str {
        match self {
            Part::Node => "the node",
            Part::Pool => "the pool",
            Part::Wallet => "the wallet",
            Part::Setup => "the proofs' setup",
            Part::Table => "the table of the proof of work",
            Part::Proving => "proving",
            #[cfg(test)]
            Part::Test => "a test",
        }
    }

    fn of(tag: usize) -> Part {
        Part::ALL.get(tag).copied().unwrap_or(Part::Node)
    }
}

const PARTS: usize = Part::ALL.len();
static HELD: [AtomicUsize; PARTS] = [const { AtomicUsize::new(0) }; PARTS];
static MOST: [AtomicUsize; PARTS] = [const { AtomicUsize::new(0) }; PARTS];

thread_local! {
    /// The part this thread is working for. (No destructor and nothing
    /// made on first use: safe to read from within the allocator.)
    static IN: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

/// The part this thread is working for.
pub fn part() -> Part {
    Part::of(IN.try_with(|p| p.get()).unwrap_or(0) as usize)
}

/// Until what is returned is dropped, what this thread allocates is
/// `part`'s; then it is again whose it was.
pub fn enter(part: Part) -> Entered {
    let before = IN.try_with(|p| p.replace(part as u8)).unwrap_or(0);
    Entered(before, std::marker::PhantomData)
}

/// A thread working for a part ([`enter`]).
pub struct Entered(u8, std::marker::PhantomData<*const ()>);

impl Drop for Entered {
    fn drop(&mut self) {
        let _ = IN.try_with(|p| p.set(self.0));
    }
}

/// `f`, to be run on another thread for the part this thread is
/// working for now: what a thread begun for a piece of some work
/// allocates is that work's.
pub fn within<T>(f: impl FnOnce() -> T) -> impl FnOnce() -> T {
    let part = part();
    move || {
        let _in = enter(part);
        f()
    }
}

/// The system's allocator, counted.
pub struct Counting;

fn took(part: usize, bytes: usize) {
    let now = NOW.fetch_add(bytes, Ordering::Relaxed) + bytes;
    PEAK.fetch_max(now, Ordering::Relaxed);
    let held = HELD[part].fetch_add(bytes, Ordering::Relaxed) + bytes;
    MOST[part].fetch_max(held, Ordering::Relaxed);
}

fn gave(part: usize, bytes: usize) {
    NOW.fetch_sub(bytes, Ordering::Relaxed);
    HELD[part].fetch_sub(bytes, Ordering::Relaxed);
}

/// What is asked of the system for `layout`, and how far into it what
/// is handed out begins: room ahead for the part, at the same
/// alignment. None if it is too large to ask for.
fn ahead(layout: Layout, size: usize) -> Option<(Layout, usize)> {
    let align = layout.align().max(core::mem::align_of::<usize>());
    let ahead = align.max(16);
    Some((Layout::from_size_align(size.checked_add(ahead)?, align).ok()?, ahead))
}

/// Writes the part ahead of what is handed out of `p`, and counts it.
///
/// # Safety
/// `p` is null or an allocation of at least `ahead` bytes aligned to a
/// `usize`, and `ahead` is at least a `usize` and a multiple of one.
unsafe fn handed(p: *mut u8, ahead: usize, size: usize) -> *mut u8 {
    if p.is_null() {
        return p;
    }
    let part = part() as usize;
    // SAFETY: within the allocation and aligned, by the contract.
    unsafe {
        let out = p.add(ahead);
        out.cast::<usize>().sub(1).write(part);
        took(part, size);
        out
    }
}

/// The part written ahead of `p`.
///
/// # Safety
/// `p` was handed out by [`handed`].
unsafe fn part_of(p: *mut u8) -> usize {
    // SAFETY: written there by `handed`.
    let part = unsafe { p.cast::<usize>().sub(1).read() };
    part.min(PARTS - 1)
}

// SAFETY: every call is the system allocator's own, for a layout that
// much larger that the part fits ahead at the same alignment; what is
// handed out lies within it, aligned as asked; and what is given back
// is given back as it was taken.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let Some((whole, ahead)) = ahead(layout, layout.size()) else { return core::ptr::null_mut() };
        // SAFETY: `whole` is not of size zero; and `handed`'s contract
        // is what `ahead` gives, of the system's blocks and of the
        // pool's, which are the system's for this same `whole`.
        unsafe {
            let kept = pool::take(&whole, layout.size(), false, part() as usize);
            handed(if kept.is_null() { System.alloc(whole) } else { kept }, ahead, layout.size())
        }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let Some((whole, ahead)) = ahead(layout, layout.size()) else { return core::ptr::null_mut() };
        // SAFETY: as in `alloc`; and a block of the pool's, which holds
        // whatever was last written to it, is cleared where it is
        // handed out: `ahead` bytes in, for the size asked.
        unsafe {
            let kept = pool::take(&whole, layout.size(), true, part() as usize);
            if kept.is_null() {
                return handed(System.alloc_zeroed(whole), ahead, layout.size());
            }
            kept.add(ahead).write_bytes(0, layout.size());
            handed(kept, ahead, layout.size())
        }
    }

    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        let Some((whole, ahead)) = ahead(layout, layout.size()) else { return };
        // SAFETY: `p` was handed out here for this layout, `ahead`
        // bytes into an allocation of `whole`: the pool's to keep, or
        // the system's to have back.
        unsafe {
            let part = part_of(p);
            if !pool::give(p.sub(ahead), &whole, layout.size(), part) {
                System.dealloc(p.sub(ahead), whole);
            }
            gave(part, layout.size());
        }
    }

    unsafe fn realloc(&self, p: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let (Some((whole, ahead)), Some((new, _))) = (ahead(layout, layout.size()), ahead(layout, new_size)) else {
            return core::ptr::null_mut();
        };
        // SAFETY: as in `dealloc`; the system keeps what was written
        // ahead, the part with it, which stays whose it was. Where the
        // pool keeps blocks of the part, the new block is `new`, taken
        // as `alloc` takes one, with the part written ahead of it as
        // `handed` writes it; the two do not overlap, and the old one
        // is given back as `dealloc` gives one.
        unsafe {
            let part = part_of(p);
            if pool::moves(&whole, layout.size(), new_size, part) {
                // Another block, the pool's or the system's, for the
                // part this one is of; what this one holds, as far as
                // it fits; and this one given back.
                let kept = pool::take(&new, new_size, false, part);
                let base = if kept.is_null() { System.alloc(new) } else { kept };
                if base.is_null() {
                    return base;
                }
                let q = base.add(ahead);
                q.cast::<usize>().sub(1).write(part);
                core::ptr::copy_nonoverlapping(p, q, layout.size().min(new_size));
                if !pool::give(p.sub(ahead), &whole, layout.size(), part) {
                    System.dealloc(p.sub(ahead), whole);
                }
                gave(part, layout.size());
                took(part, new_size);
                return q;
            }
            let q = System.realloc(p.sub(ahead), whole, new.size());
            if q.is_null() {
                return q;
            }
            gave(part, layout.size());
            took(part, new_size);
            q.add(ahead)
        }
    }
}

/// One part's large blocks, kept: taken from the system once and handed
/// out again whenever one of the same size is asked for.
///
/// A block is kept by its size and alignment, exactly: what a part
/// asks for in making one proof is what it asks for in making the next,
/// to the byte, so a block that is given back is the block that is
/// asked for later. Blocks under [`MIN`](pool::MIN) are left to the
/// system, which is good at those.
///
/// It is used in one of two ways. [`reserve`](pool::reserve) takes a
/// given number of blocks of given sizes from the system, there and
/// then, and keeps that many and no more: what the part holds is then
/// of a fixed size, held from the start, and a program that has not the
/// memory for it finds out when it starts and not in the middle of its
/// work. A block asked for that the pool has none of is the system's
/// after all, and is counted ([`misses`](pool::misses)): what was
/// reserved was not enough. [`learn`](pool::learn) keeps every block
/// given back, of whatever size, and counts how many of each were out
/// at once ([`seen`](pool::seen)): which is how the numbers to reserve
/// are found.
///
/// Nothing here asks for memory while it holds its lock, and its own
/// records are of a fixed size: it is under the allocator, and cannot
/// ask it for anything.
pub mod pool {
    use super::Part;
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::cell::UnsafeCell;
    use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};

    /// The smallest block that is kept.
    pub const MIN: usize = 1 << 20;
    /// Sizes that can be kept, and blocks of one size.
    const CLASSES: usize = 128;
    const SLOTS: usize = 64;
    /// Bytes ahead of what is handed out, in a block that is kept
    /// ([`super::ahead`]): those of an alignment of sixteen or less.
    const AHEAD: usize = 16;
    /// No part's blocks are kept.
    const NONE: u8 = u8::MAX;

    /// Blocks of one size to keep.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct Blocks {
        /// The bytes asked for, and the alignment they are asked at.
        pub size: usize,
        pub align: usize,
        pub count: usize,
    }

    /// What became of the blocks of one size.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct Seen {
        pub size: usize,
        pub align: usize,
        /// How many are kept at the most, and how many are there now.
        pub kept: usize,
        pub idle: usize,
        /// The most that were out at once.
        pub most: usize,
        /// Times one was asked for: and of those, the times the pool
        /// had one, the times it had none, and the times it was asked
        /// for cleared.
        pub asked: u64,
        pub hits: u64,
        pub misses: u64,
        pub cleared: u64,
    }

    struct Class {
        size: usize,
        /// The alignment the system was asked for: eight or sixteen.
        align: usize,
        cap: usize,
        n: usize,
        out: usize,
        most: usize,
        hits: u64,
        misses: u64,
        cleared: u64,
        free: [*mut u8; SLOTS],
    }

    const EMPTY: Class = Class {
        size: 0,
        align: 0,
        cap: 0,
        n: 0,
        out: 0,
        most: 0,
        hits: 0,
        misses: 0,
        cleared: 0,
        free: [core::ptr::null_mut(); SLOTS],
    };

    struct Classes {
        len: usize,
        /// Whether a size not seen before is kept from then on.
        learning: bool,
        all: [Class; CLASSES],
    }

    impl Classes {
        fn find(&mut self, size: usize, align: usize) -> Option<&mut Class> {
            self.all[..self.len].iter_mut().find(|c| c.size == size && c.align == align)
        }

        fn add(&mut self, size: usize, align: usize, cap: usize) -> Option<&mut Class> {
            let class = self.all.get_mut(self.len)?;
            *class = Class { size, align, cap: cap.min(SLOTS), ..EMPTY };
            self.len += 1;
            Some(class)
        }
    }

    struct Shared(UnsafeCell<Classes>);
    // SAFETY: read and written only by whoever holds `LOCK` ([`with`]).
    unsafe impl Sync for Shared {}

    static POOL: Shared = Shared(UnsafeCell::new(Classes { len: 0, learning: false, all: [EMPTY; CLASSES] }));
    static LOCK: AtomicBool = AtomicBool::new(false);
    /// The part whose blocks are kept.
    static PART: AtomicU8 = AtomicU8::new(NONE);
    /// Bytes of the blocks that are kept and not out, and the most
    /// that may be.
    static IDLE: AtomicUsize = AtomicUsize::new(0);
    static LIMIT: AtomicUsize = AtomicUsize::new(usize::MAX);

    /// `f`, with the pool's records and nobody else at them. It is to
    /// be short, to ask for no memory, and not to panic: large blocks
    /// are asked for a few hundred times in a proof, so whoever waits
    /// here waits by spinning, and not for long.
    fn with<R>(f: impl FnOnce(&mut Classes) -> R) -> R {
        while LOCK.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            std::hint::spin_loop();
        }
        // SAFETY: the lock is held, so this is the only reference.
        let r = f(unsafe { &mut *POOL.0.get() });
        LOCK.store(false, Ordering::Release);
        r
    }

    /// Whether a block of `size`, asked of the system as `whole`, for
    /// `part`, is one the pool may keep.
    fn ours(whole: &Layout, size: usize, part: usize) -> bool {
        size >= MIN && whole.align() <= AHEAD && PART.load(Ordering::Relaxed) as usize == part
    }

    /// A block the pool has for `size`, asked of the system as `whole`
    /// for `part`: where the system's block begins. Null if it has
    /// none, or keeps none of that kind for that part.
    pub(super) fn take(whole: &Layout, size: usize, cleared: bool, part: usize) -> *mut u8 {
        if !ours(whole, size, part) {
            return core::ptr::null_mut();
        }
        with(|classes| {
            let learning = classes.learning;
            let class = match classes.find(size, whole.align()) {
                Some(class) => class,
                None if learning => match classes.add(size, whole.align(), SLOTS) {
                    Some(class) => class,
                    None => return core::ptr::null_mut(),
                },
                None => return core::ptr::null_mut(),
            };
            class.out += 1;
            class.most = class.most.max(class.out);
            class.cleared += u64::from(cleared);
            if class.n == 0 {
                class.misses += 1;
                return core::ptr::null_mut();
            }
            class.n -= 1;
            class.hits += 1;
            IDLE.fetch_sub(size, Ordering::Relaxed);
            class.free[class.n]
        })
    }

    /// Keeps the block that begins at `base`, which was of `size` for
    /// `part` and the system's as `whole`, if the pool keeps such and
    /// has room: whether it did.
    pub(super) fn give(base: *mut u8, whole: &Layout, size: usize, part: usize) -> bool {
        if !ours(whole, size, part) {
            return false;
        }
        with(|classes| {
            let Some(class) = classes.find(size, whole.align()) else { return false };
            class.out = class.out.saturating_sub(1);
            if class.n >= class.cap || IDLE.load(Ordering::Relaxed).saturating_add(size) > LIMIT.load(Ordering::Relaxed)
            {
                return false;
            }
            class.free[class.n] = base;
            class.n += 1;
            IDLE.fetch_add(size, Ordering::Relaxed);
            true
        })
    }

    /// A block of `part`'s that was of `size` is now of `new_size`, and
    /// the system's still: it is out of the one size, and out in the
    /// other.
    /// Whether a block of `part`'s that is of `size`, the system's as
    /// `whole`, is to be made one of `new_size` by taking another and
    /// giving this one back: so, where either is one the pool keeps,
    /// which is then not lost to it by being grown where it lies.
    pub(super) fn moves(whole: &Layout, size: usize, new_size: usize, part: usize) -> bool {
        ours(whole, size.max(new_size), part)
    }

    /// What the system is asked for a block of `size` at `align`.
    fn whole(size: usize, align: usize) -> Option<Layout> {
        let align = align.max(core::mem::align_of::<usize>());
        (size >= MIN && align <= AHEAD).then(|| Layout::from_size_align(size.checked_add(AHEAD)?, align).ok())?
    }

    /// Keeps every large block `part` gives back, of whatever size, from
    /// now on, until `at_most` bytes are kept and not out: for a part
    /// that is to find its own size, and to find out what it asks for
    /// ([`seen`]). What was kept before is let go.
    pub fn learn(part: Part, at_most: usize) {
        release();
        with(|classes| classes.learning = true);
        LIMIT.store(at_most, Ordering::Relaxed);
        PART.store(part as u8, Ordering::Relaxed);
    }

    /// Takes `blocks` from the system now, for `part`, and keeps those
    /// and no more from now on: every page of them written to, so that
    /// they are held and not only promised. What was kept before is let
    /// go. False, with nothing kept, if the system has not the memory,
    /// or `blocks` are more sizes, or more of one size, than can be
    /// kept, or smaller than [`MIN`].
    pub fn reserve(part: Part, blocks: &[Blocks]) -> bool {
        release();
        let fits =
            blocks.len() <= CLASSES && blocks.iter().all(|b| b.count <= SLOTS && whole(b.size, b.align).is_some());
        if !fits {
            return false;
        }
        for b in blocks {
            let Some(layout) = whole(b.size, b.align) else { return false };
            with(|classes| classes.add(b.size, layout.align(), b.count).is_some());
            for _ in 0..b.count {
                // SAFETY: a layout of a megabyte or more.
                let base = unsafe { System.alloc(layout) };
                if base.is_null() {
                    release();
                    return false;
                }
                // SAFETY: within the block just taken, a page at a time.
                (0..layout.size()).step_by(4096).for_each(|at| unsafe { base.add(at).write(0) });
                with(|classes| {
                    if let Some(class) = classes.find(b.size, layout.align()) {
                        class.free[class.n] = base;
                        class.n += 1;
                    }
                });
                IDLE.fetch_add(b.size, Ordering::Relaxed);
            }
        }
        PART.store(part as u8, Ordering::Relaxed);
        true
    }

    /// Gives back to the system every block that is kept and not out,
    /// and keeps none from now on. A block that is out is the system's
    /// when it is given back.
    pub fn release() {
        PART.store(NONE, Ordering::Relaxed);
        LIMIT.store(usize::MAX, Ordering::Relaxed);
        loop {
            let next = with(|classes| {
                let found = classes.all[..classes.len].iter_mut().find(|c| c.n > 0).map(|class| {
                    class.n -= 1;
                    (class.free[class.n], class.size, class.align)
                });
                if found.is_none() {
                    classes.len = 0;
                    classes.learning = false;
                }
                found
            });
            let Some((base, size, align)) = next else { break };
            IDLE.fetch_sub(size, Ordering::Relaxed);
            if let Ok(layout) = Layout::from_size_align(size + AHEAD, align) {
                // SAFETY: the system's block, of this layout, and nobody's now.
                unsafe { System.dealloc(base, layout) };
            }
        }
    }

    /// Bytes of the blocks that are kept and not out: held of the
    /// system, and counted to no part until they are handed out.
    pub fn idle() -> usize {
        IDLE.load(Ordering::Relaxed)
    }

    /// What became of the blocks of each size, the largest first.
    pub fn seen() -> Vec<Seen> {
        let mut all = Vec::with_capacity(CLASSES);
        with(|classes| {
            for c in &classes.all[..classes.len] {
                all.push(Seen {
                    size: c.size,
                    align: c.align,
                    kept: c.cap,
                    idle: c.n,
                    most: c.most,
                    asked: c.hits + c.misses,
                    hits: c.hits,
                    misses: c.misses,
                    cleared: c.cleared,
                });
            }
        });
        all.sort_by_key(|s| (std::cmp::Reverse(s.size), s.align));
        all
    }

    /// Times a block was asked for that the pool keeps the size of, and
    /// had none: none, where what was reserved is enough.
    pub fn misses() -> u64 {
        with(|classes| classes.all[..classes.len].iter().map(|c| c.misses).sum())
    }
}

/// The bytes held now.
pub fn now() -> usize {
    NOW.load(Ordering::Relaxed)
}

/// The most bytes ever held at once, since the program began or since
/// [`reset_peak`].
pub fn peak() -> usize {
    PEAK.load(Ordering::Relaxed)
}

/// Counts the most held afresh, from what is held now: for the most a
/// stretch of work holds.
pub fn reset_peak() {
    PEAK.store(now(), Ordering::Relaxed);
}

/// The bytes held now for `part`.
pub fn held(part: Part) -> usize {
    HELD[part as usize].load(Ordering::Relaxed)
}

/// The most bytes ever held at once for `part`, since the program
/// began or since [`reset_most`].
pub fn most(part: Part) -> usize {
    MOST[part as usize].load(Ordering::Relaxed)
}

/// Counts the most held for `part` afresh, from what is held now.
pub fn reset_most(part: Part) {
    MOST[part as usize].store(held(part), Ordering::Relaxed);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Held by a test that counts what [`Part::Test`] holds: one at a
    /// time, the harness running them side by side.
    static ONE: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// The allocator asked itself, for a part no other test holds
    /// anything for: what it hands out
    /// is aligned as asked and keeps what is written through growing
    /// and shrinking, and each part is counted what it holds, whoever
    /// gives it back.
    #[test]
    fn each_part_is_counted_what_it_holds() {
        let _one = ONE.lock().unwrap_or_else(|e| e.into_inner());
        let a = Counting;
        let before: Vec<usize> = Part::ALL.iter().map(|p| held(*p)).collect();
        for align in [1usize, 2, 8, 16, 64, 4096] {
            let layout = Layout::from_size_align(100, align).unwrap();
            let in_pool = enter(Part::Test);
            // SAFETY: a layout of a size that is not zero.
            let p = unsafe { a.alloc(layout) };
            drop(in_pool);
            assert!(!p.is_null() && (p as usize).is_multiple_of(align));
            assert_eq!(held(Part::Test) - before[Part::Test as usize], 100);
            // SAFETY: a hundred bytes of ours.
            unsafe { core::slice::from_raw_parts_mut(p, 100).iter_mut().enumerate().for_each(|(i, b)| *b = i as u8) };
            // Grown by a thread working for another part: the pool's still.
            let in_wallet = enter(Part::Wallet);
            // SAFETY: `p` is of `layout`, and the new size is not zero.
            let q = unsafe { a.realloc(p, layout, 5000) };
            assert!(!q.is_null() && (q as usize).is_multiple_of(align));
            assert_eq!(held(Part::Test) - before[Part::Test as usize], 5000);
            // SAFETY: the first hundred bytes are as they were.
            assert!(unsafe { core::slice::from_raw_parts(q, 100) }.iter().enumerate().all(|(i, b)| *b == i as u8));
            let grown = Layout::from_size_align(5000, align).unwrap();
            // SAFETY: `q` is of `grown`.
            let r = unsafe { a.realloc(q, grown, 10) };
            assert!(unsafe { core::slice::from_raw_parts(r, 10) }.iter().enumerate().all(|(i, b)| *b == i as u8));
            // SAFETY: `r` is of ten bytes at this alignment.
            unsafe { a.dealloc(r, Layout::from_size_align(10, align).unwrap()) };
            drop(in_wallet);
            assert_eq!(held(Part::Test), before[Part::Test as usize]);
            // SAFETY: zeroed, and given back.
            unsafe {
                let z = a.alloc_zeroed(layout);
                assert!(core::slice::from_raw_parts(z, 100).iter().all(|b| *b == 0));
                a.dealloc(z, layout);
            }
        }
        assert!(most(Part::Test) >= 5000);
        assert_eq!(part(), Part::Node);
        // A thread begun for a part's work is that part's.
        let _in = enter(Part::Test);
        assert_eq!(std::thread::scope(|s| s.spawn(within(part)).join().unwrap()), Part::Test);
    }

    /// A block of `size` at `align`, asked of the allocator for the
    /// part this thread is working for.
    fn block(size: usize, align: usize, cleared: bool) -> (*mut u8, Layout) {
        let layout = Layout::from_size_align(size, align).unwrap();
        // SAFETY: a layout of a size that is not zero.
        let p = unsafe { if cleared { Counting.alloc_zeroed(layout) } else { Counting.alloc(layout) } };
        assert!(!p.is_null() && (p as usize).is_multiple_of(align));
        (p, layout)
    }

    fn back((p, layout): (*mut u8, Layout)) {
        // SAFETY: handed out by `block`, for this layout.
        unsafe { Counting.dealloc(p, layout) }
    }

    /// What the pool says of the blocks of `size` for elements.
    fn seen_of(size: usize) -> pool::Seen {
        pool::seen().into_iter().find(|s| s.size == size && s.align == 16).expect("a size the pool has seen")
    }

    /// One part's large blocks are kept and handed out again, the same
    /// blocks; nobody else's are, nor small ones; and what the parts
    /// are counted to hold is what they would be without.
    #[test]
    fn large_blocks_of_one_part_are_kept() {
        let _one = ONE.lock().unwrap_or_else(|e| e.into_inner());
        const BIG: usize = 2 << 20;
        let before = held(Part::Test);
        pool::learn(Part::Test, usize::MAX);
        let in_test = enter(Part::Test);
        // Given back, it is kept; asked for again, it is the same one.
        let first = block(BIG, 16, false);
        assert_eq!((held(Part::Test) - before, pool::idle()), (BIG, 0));
        // SAFETY: two megabytes of ours.
        unsafe { first.0.write_bytes(0xAB, BIG) };
        let at = first.0;
        back(first);
        assert_eq!((held(Part::Test), pool::idle()), (before, BIG));
        let again = block(BIG, 16, false);
        assert_eq!((again.0, pool::idle()), (at, 0));
        back(again);
        // Asked for cleared, it is cleared, whatever was written to it.
        let cleared = block(BIG, 16, true);
        assert_eq!(cleared.0, at);
        // SAFETY: two megabytes of ours.
        assert!(unsafe { core::slice::from_raw_parts(cleared.0, BIG) }.iter().all(|b| *b == 0));
        // A second while the first is out is the system's, and both are
        // kept afterwards.
        let second = block(BIG, 16, false);
        assert_ne!(second.0, at);
        back(cleared);
        back(second);
        assert_eq!(pool::idle(), 2 * BIG);
        let said = seen_of(BIG);
        assert_eq!((said.asked, said.hits, said.misses, said.cleared, said.most, said.idle), (4, 2, 2, 1, 2, 2));
        // Another alignment is another kind of block: a block for bytes
        // is not handed out for elements.
        let bytes = block(BIG, 1, false);
        assert_eq!(pool::idle(), 2 * BIG);
        back(bytes);
        assert_eq!(pool::idle(), 3 * BIG);
        // Not a small block; not one aligned to more than sixteen; and
        // not another part's.
        for (size, align) in [(pool::MIN - 1, 16), (BIG, 4096)] {
            back(block(size, align, false));
            assert_eq!(pool::idle(), 3 * BIG);
        }
        drop(in_test);
        back(block(BIG, 16, false));
        assert_eq!((pool::idle(), seen_of(BIG).asked), (3 * BIG, 4));
        // A vector is such a block: made, dropped, and made of the same
        // memory.
        let in_test = enter(Part::Test);
        let made = vec![7u128; BIG / 16];
        let at = made.as_ptr();
        drop(made);
        let made = vec![9u128; BIG / 16];
        assert_eq!(made.as_ptr(), at);
        drop(made);
        // One that grows keeps what it held, and leaves its block to
        // the pool: the next of that size is the same block.
        let mut grown: Vec<u128> = Vec::with_capacity(BIG / 16);
        let at = grown.as_ptr();
        grown.resize(BIG / 16, 3);
        grown.push(4);
        assert!(grown.as_ptr() != at && grown[..BIG / 16].iter().all(|x| *x == 3) && grown[BIG / 16] == 4);
        let next = vec![1u128; BIG / 16];
        assert_eq!(next.as_ptr(), at);
        // And one that shrinks to less than the pool keeps.
        grown.truncate(10);
        grown.shrink_to_fit();
        assert_eq!(grown, [3; 10]);
        drop((grown, next));
        assert_eq!(seen_of(BIG).most, 2);
        // From many threads at once: every block asked for is had, and
        // every one is given back.
        let asked = seen_of(BIG).asked;
        std::thread::scope(|s| {
            for t in 0..8u8 {
                s.spawn(within(move || {
                    for _ in 0..50 {
                        let b = block(BIG, 16, false);
                        // SAFETY: two megabytes of this thread's.
                        unsafe {
                            b.0.write_bytes(t, BIG);
                            assert!(core::slice::from_raw_parts(b.0, BIG).iter().all(|x| *x == t));
                        }
                        back(b);
                    }
                }));
            }
        });
        let said = seen_of(BIG);
        assert_eq!((said.asked - asked, said.hits + said.misses, held(Part::Test)), (400, said.asked, before));
        assert!(said.most <= 8 + 2);
        drop(in_test);
        // No more is kept than it was told to keep.
        pool::learn(Part::Test, BIG);
        let _in = enter(Part::Test);
        let (a, b) = (block(BIG, 16, false), block(BIG, 16, false));
        back(a);
        back(b);
        assert_eq!(pool::idle(), BIG);
        // Let go, nothing is kept, and nothing more is.
        pool::release();
        assert_eq!((pool::idle(), pool::seen().len()), (0, 0));
        back(block(BIG, 16, false));
        assert_eq!(pool::idle(), 0);
    }

    /// What is reserved is held from the start, is all that is kept,
    /// and is counted short where it was not enough.
    #[test]
    fn a_reserve_is_of_a_fixed_size() {
        let _one = ONE.lock().unwrap_or_else(|e| e.into_inner());
        const BIG: usize = 3 << 20;
        // Not what cannot be kept: too small, too many of a size.
        assert!(!pool::reserve(Part::Test, &[pool::Blocks { size: pool::MIN - 1, align: 16, count: 1 }]));
        assert!(!pool::reserve(Part::Test, &[pool::Blocks { size: BIG, align: 16, count: 1000 }]));
        assert_eq!(pool::idle(), 0);
        assert!(pool::reserve(Part::Test, &[pool::Blocks { size: BIG, align: 16, count: 2 }]));
        assert_eq!((pool::idle(), pool::misses()), (2 * BIG, 0));
        let _in = enter(Part::Test);
        let (a, b) = (block(BIG, 16, false), block(BIG, 16, true));
        assert_eq!((pool::idle(), pool::misses()), (0, 0));
        // A third is the system's, and is said; given back, it is not
        // kept: what is kept is what was reserved.
        let c = block(BIG, 16, false);
        assert_eq!(pool::misses(), 1);
        for each in [a, b, c] {
            back(each);
        }
        assert_eq!(pool::idle(), 2 * BIG);
        // A size that was not reserved is not kept at all.
        back(block(2 * BIG, 16, false));
        assert_eq!((pool::idle(), pool::seen().len()), (2 * BIG, 1));
        pool::release();
        assert_eq!(pool::idle(), 0);
    }
}
