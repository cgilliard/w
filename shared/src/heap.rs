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
        // is what `ahead` gives.
        unsafe { handed(System.alloc(whole), ahead, layout.size()) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let Some((whole, ahead)) = ahead(layout, layout.size()) else { return core::ptr::null_mut() };
        // SAFETY: as in `alloc`.
        unsafe { handed(System.alloc_zeroed(whole), ahead, layout.size()) }
    }

    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        let Some((whole, ahead)) = ahead(layout, layout.size()) else { return };
        // SAFETY: `p` was handed out here for this layout, `ahead`
        // bytes into an allocation of `whole`.
        unsafe {
            let part = part_of(p);
            System.dealloc(p.sub(ahead), whole);
            gave(part, layout.size());
        }
    }

    unsafe fn realloc(&self, p: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let (Some((whole, ahead)), Some((new, _))) = (ahead(layout, layout.size()), ahead(layout, new_size)) else {
            return core::ptr::null_mut();
        };
        // SAFETY: as in `dealloc`; the system keeps what was written
        // ahead, the part with it, which stays whose it was.
        unsafe {
            let part = part_of(p);
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

    /// The allocator asked itself, for a part no other test holds
    /// anything for: what it hands out
    /// is aligned as asked and keeps what is written through growing
    /// and shrinking, and each part is counted what it holds, whoever
    /// gives it back.
    #[test]
    fn each_part_is_counted_what_it_holds() {
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
}
