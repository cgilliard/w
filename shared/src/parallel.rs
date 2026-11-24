//! Minimal data parallelism over scoped threads.
//!
//! Work is split into contiguous ranges, one per thread, so the helpers
//! suit loops whose iterations cost about the same. The thread count is
//! `available_parallelism`, overridable with the `TABMINER_THREADS`
//! environment variable; small inputs run on the calling thread.

use std::sync::OnceLock;

static THREADS: OnceLock<usize> = OnceLock::new();

/// Sets the number of worker threads, if it has not been asked for
/// yet: for a node told how many to use. Whether it was set.
pub fn set_threads(n: usize) -> bool {
    n > 0 && THREADS.set(n).is_ok()
}

/// How many cores the machine has: cores, not the threads the system
/// counts where each core runs two. What a node uses unless told how
/// many threads to use: a second thread on a core adds little to work
/// that is all arithmetic, and a machine with every thread taken has
/// none left for anything else.
///
/// Where the system does not say (or says it in a way not read here),
/// the threads it counts.
pub fn cores() -> usize {
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    physical_cores().filter(|n| (1..=threads).contains(n)).unwrap_or(threads)
}

/// On Linux: the threads that share a core are listed for each
/// (`thread_siblings_list`), the same list for each of them; so there
/// are as many cores as there are different lists.
#[cfg(target_os = "linux")]
fn physical_cores() -> Option<usize> {
    let mut cores = std::collections::BTreeSet::new();
    for entry in std::fs::read_dir("/sys/devices/system/cpu").ok()?.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        // (`cpu0`, `cpu1`, ...: not `cpufreq` or `cpuidle`.)
        if name.strip_prefix("cpu").is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit())) {
            // A thread that is switched off has no topology: not counted.
            let Ok(siblings) = std::fs::read_to_string(entry.path().join("topology/thread_siblings_list")) else {
                continue;
            };
            // (With its package: two packages number their cores alike.)
            let package =
                std::fs::read_to_string(entry.path().join("topology/physical_package_id")).unwrap_or_default();
            cores.insert((package.trim().to_string(), siblings.trim().to_string()));
        }
    }
    (!cores.is_empty()).then_some(cores.len())
}

/// On macOS the system says, by name.
#[cfg(target_os = "macos")]
fn physical_cores() -> Option<usize> {
    unsafe extern "C" {
        fn sysctlbyname(name: *const u8, old: *mut u8, old_len: *mut usize, new: *const u8, new_len: usize) -> i32;
    }
    let (mut cores, mut len) = (0i32, std::mem::size_of::<i32>());
    // SAFETY: a name that ends in a zero byte, and room for the four
    // bytes of the answer, its length said.
    let ok = unsafe {
        sysctlbyname(c"hw.physicalcpu".as_ptr().cast(), (&raw mut cores).cast(), &raw mut len, std::ptr::null(), 0)
    };
    (ok == 0 && cores > 0).then_some(cores as usize)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn physical_cores() -> Option<usize> {
    None
}

/// Number of worker threads.
pub fn threads() -> usize {
    *THREADS.get_or_init(|| {
        std::env::var("TABMINER_THREADS")
            .ok()
            .and_then(|s| s.parse().ok())
            .filter(|&n| n > 0)
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
    })
}

/// Below this many items a loop runs serially.
const MIN_PARALLEL: usize = 1024;

/// Splits `0..n` into at most `threads()` contiguous ranges.
fn ranges(n: usize, min_per_thread: usize) -> Vec<std::ops::Range<usize>> {
    let t = threads().min(n / min_per_thread.max(1)).max(1);
    let per = n.div_ceil(t);
    (0..t).map(|k| (k * per).min(n)..((k + 1) * per).min(n)).filter(|r| !r.is_empty()).collect()
}

/// `(0..n).map(f)` evaluated in parallel.
pub fn par_map<T: Send, F: Fn(usize) -> T + Sync>(n: usize, f: F) -> Vec<T> {
    par_map_min(n, MIN_PARALLEL, f)
}

/// As [`par_map`], but with an explicit serial threshold: parallel only
/// when at least `min_per_thread` items fall to each thread.
pub fn par_map_min<T: Send, F: Fn(usize) -> T + Sync>(n: usize, min_per_thread: usize, f: F) -> Vec<T> {
    let ranges = ranges(n, min_per_thread);
    if ranges.len() <= 1 {
        return (0..n).map(f).collect();
    }
    let f = &f;
    let parts: Vec<Vec<T>> = std::thread::scope(|s| {
        let handles: Vec<_> =
            ranges.into_iter().map(|r| s.spawn(crate::heap::within(move || r.map(f).collect::<Vec<T>>()))).collect();
        handles.into_iter().map(|h| h.join().expect("worker panicked")).collect()
    });
    let mut out = Vec::with_capacity(n);
    for p in parts {
        out.extend(p);
    }
    out
}

/// As [`par_map`], with per-thread state made by `init` and passed to
/// every call (scratch buffers, say).
pub fn par_map_with<S, T: Send, I: Fn() -> S + Sync, F: Fn(&mut S, usize) -> T + Sync>(
    n: usize,
    init: I,
    f: F,
) -> Vec<T> {
    let ranges = ranges(n, MIN_PARALLEL);
    if ranges.len() <= 1 {
        let mut state = init();
        return (0..n).map(|i| f(&mut state, i)).collect();
    }
    let (f, init) = (&f, &init);
    let parts: Vec<Vec<T>> = std::thread::scope(|s| {
        let handles: Vec<_> = ranges
            .into_iter()
            .map(|r| {
                s.spawn(crate::heap::within(move || {
                    let mut state = init();
                    r.map(|i| f(&mut state, i)).collect::<Vec<T>>()
                }))
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("worker panicked")).collect()
    });
    let mut out = Vec::with_capacity(n);
    for p in parts {
        out.extend(p);
    }
    out
}

/// Sets `out[i] = f(i)` for every `i`, in parallel: [`par_map`] into a
/// buffer the caller holds, so the results are computed where they stay
/// and nothing is allocated for them.
pub fn par_fill<T: Send, F: Fn(usize) -> T + Sync>(out: &mut [T], f: F) {
    par_fill_min(out, MIN_PARALLEL, f)
}

/// As [`par_fill`], but with an explicit serial threshold: parallel only
/// when at least `min_per_thread` items fall to each thread.
pub fn par_fill_min<T: Send, F: Fn(usize) -> T + Sync>(out: &mut [T], min_per_thread: usize, f: F) {
    let n = out.len();
    let t = threads().min(n / min_per_thread.max(1)).max(1);
    if t <= 1 {
        for (i, x) in out.iter_mut().enumerate() {
            *x = f(i);
        }
        return;
    }
    // One contiguous run of `per` items per thread, the last one shorter.
    let per = n.div_ceil(t);
    let f = &f;
    std::thread::scope(|s| {
        for (k, run) in out.chunks_mut(per).enumerate() {
            s.spawn(crate::heap::within(move || {
                for (i, x) in run.iter_mut().enumerate() {
                    *x = f(k * per + i);
                }
            }));
        }
    });
}

/// Runs `f(chunk_index, chunk)` over `data.chunks_mut(chunk)` in parallel.
/// Each thread takes a contiguous run of whole chunks; no list of the
/// chunks is made, so the cost does not grow with their number.
pub fn par_chunks_mut<T: Send, F: Fn(usize, &mut [T]) + Sync>(data: &mut [T], chunk: usize, f: F) {
    assert!(chunk > 0);
    let n = data.len().div_ceil(chunk);
    let t = threads().min(n).max(1);
    if t <= 1 {
        for (i, c) in data.chunks_mut(chunk).enumerate() {
            f(i, c);
        }
        return;
    }
    // `per` chunks per thread, the last thread's run shorter.
    let per = n.div_ceil(t);
    let f = &f;
    std::thread::scope(|s| {
        for (k, run) in data.chunks_mut(per * chunk).enumerate() {
            s.spawn(crate::heap::within(move || {
                for (i, c) in run.chunks_mut(chunk).enumerate() {
                    f(k * per + i, c);
                }
            }));
        }
    });
}

/// Runs `f(chunk_index, a_chunk, b_chunk)` over the chunks of two slices
/// of one length, pair by pair, in parallel: [`par_chunks_mut`] for work
/// that reads and writes two buffers in step.
pub fn par_chunks2_mut<T: Send, F: Fn(usize, &mut [T], &mut [T]) + Sync>(a: &mut [T], b: &mut [T], chunk: usize, f: F) {
    assert!(chunk > 0 && a.len() == b.len());
    let n = a.len().div_ceil(chunk);
    let t = threads().min(n).max(1);
    if t <= 1 {
        for (i, (x, y)) in a.chunks_mut(chunk).zip(b.chunks_mut(chunk)).enumerate() {
            f(i, x, y);
        }
        return;
    }
    let per = n.div_ceil(t);
    let f = &f;
    std::thread::scope(|s| {
        for (k, (ra, rb)) in a.chunks_mut(per * chunk).zip(b.chunks_mut(per * chunk)).enumerate() {
            s.spawn(crate::heap::within(move || {
                for (i, (x, y)) in ra.chunks_mut(chunk).zip(rb.chunks_mut(chunk)).enumerate() {
                    f(k * per + i, x, y);
                }
            }));
        }
    });
}

/// `f` of each run of `run` items of `0..n`, in parallel, and the
/// results folded in order from `zero` by `add`: a sum over a range too
/// long to take one item at a time.
pub fn par_fold<R: Send, F: Fn(std::ops::Range<usize>) -> R + Sync, A: Fn(R, R) -> R>(
    n: usize,
    run: usize,
    zero: R,
    f: F,
    add: A,
) -> R {
    assert!(run > 0);
    par_map_min(n.div_ceil(run), 1, |i| f(i * run..n.min((i + 1) * run))).into_iter().fold(zero, add)
}

/// `f` of every item of `items`, in parallel, in no order: for work
/// whose pieces are more than a slice or two, zipped. Each thread takes
/// the next item when it is free, so the pieces should be few and large.
pub fn par_for_each<I, F>(items: I, f: F)
where
    I: Iterator + Send,
    I::Item: Send,
    F: Fn(I::Item) + Sync,
{
    if threads() <= 1 {
        items.for_each(f);
        return;
    }
    let items = std::sync::Mutex::new(items);
    let (f, items) = (&f, &items);
    std::thread::scope(|s| {
        for _ in 0..threads() {
            s.spawn(crate::heap::within(move || {
                loop {
                    let next = items.lock().unwrap_or_else(|e| e.into_inner()).next();
                    match next {
                        Some(x) => f(x),
                        None => break,
                    }
                }
            }));
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// `par_map` and `par_map_with` give `(0..n).map(f)` in order, below
    /// the serial threshold and above it. The state of `par_map_with` is
    /// made once per thread and carried from one item to the next: each
    /// thread sees its items in order, a contiguous run.
    #[test]
    fn par_map_with_carries_state_per_thread() {
        for n in [0, 1, 5, MIN_PARALLEL - 1, MIN_PARALLEL, 4 * MIN_PARALLEL + 3, 100_003] {
            let want: Vec<usize> = (0..n).map(|i| 3 * i + 1).collect();
            assert_eq!(par_map(n, |i| 3 * i + 1), want, "par_map of {n}");
            let made = AtomicUsize::new(0);
            let got = par_map_with(
                n,
                || {
                    made.fetch_add(1, Ordering::Relaxed);
                    None::<usize>
                },
                |last, i| {
                    assert!(last.is_none_or(|l| l + 1 == i), "item {i} after {last:?}");
                    *last = Some(i);
                    3 * i + 1
                },
            );
            assert_eq!(got, want, "par_map_with of {n}");
            let made = made.load(Ordering::Relaxed);
            let most = threads().min(n / MIN_PARALLEL).max(1);
            assert!((1..=most).contains(&made), "{made} states for {n} items, at most {most} threads");
        }
    }

    /// `par_fill` sets every item to `f` of its index, below the serial
    /// threshold and above it, as `par_map` would return them.
    #[test]
    fn par_fill_matches_serial() {
        for n in [0, 1, 5, MIN_PARALLEL - 1, MIN_PARALLEL, 4 * MIN_PARALLEL + 3, 100_003] {
            let want: Vec<usize> = (0..n).map(|i| 3 * i + 1).collect();
            let mut got = vec![usize::MAX; n];
            par_fill(&mut got, |i| 3 * i + 1);
            assert_eq!(got, want, "par_fill of {n}");
            for min in [1, 7, n.max(1)] {
                let mut got = vec![usize::MAX; n];
                par_fill_min(&mut got, min, |i| 3 * i + 1);
                assert_eq!(got, want, "par_fill_min of {n}, at least {min} a thread");
            }
        }
    }

    /// Every chunk is seen once, whole, under its own index: for lengths
    /// that the chunk size divides and that it does not, chunks of one
    /// item, and a chunk longer than the data.
    #[test]
    fn par_chunks_mut_gives_each_chunk_its_index() {
        for len in [0usize, 1, 7, 100, 4096, 10_007] {
            for chunk in [1usize, 3, 64, 100, 10_007, 20_000] {
                let mut v = vec![0usize; len];
                let seen = AtomicUsize::new(0);
                par_chunks_mut(&mut v, chunk, |k, c| {
                    seen.fetch_add(1, Ordering::Relaxed);
                    let whole = (k + 1) * chunk <= len;
                    assert_eq!(c.len(), if whole { chunk } else { len - k * chunk }, "chunk {k} of {len} by {chunk}");
                    for (j, x) in c.iter_mut().enumerate() {
                        *x += k * chunk + j + 1;
                    }
                });
                assert_eq!(seen.load(Ordering::Relaxed), len.div_ceil(chunk), "{len} by {chunk}");
                assert!(v.iter().enumerate().all(|(i, x)| *x == i + 1), "{len} by {chunk}");
            }
        }
    }

    /// A panic in a worker reaches the caller: none is lost, whichever
    /// thread it happens on.
    #[test]
    fn a_panic_in_a_worker_reaches_the_caller() {
        for n in [10usize, 50_000] {
            for at in [0, n / 2, n - 1] {
                let hit = |i: usize| if i == at { panic!("item {i} fails") } else { i };
                assert!(catch_unwind(AssertUnwindSafe(|| par_map_min(n, 1, hit))).is_err(), "par_map_min {n} at {at}");
                assert!(catch_unwind(AssertUnwindSafe(|| par_map(n, hit))).is_err(), "par_map {n} at {at}");
                assert!(
                    catch_unwind(AssertUnwindSafe(|| par_map_with(n, || (), |_, i| hit(i)))).is_err(),
                    "par_map_with {n} at {at}"
                );
                let mut filled = vec![0usize; n];
                assert!(
                    catch_unwind(AssertUnwindSafe(|| par_fill_min(&mut filled, 1, hit))).is_err(),
                    "par_fill_min {n} at {at}"
                );
                let mut v = vec![0usize; n];
                let chunked = catch_unwind(AssertUnwindSafe(|| {
                    par_chunks_mut(&mut v, 7, |k, c| {
                        for (j, x) in c.iter_mut().enumerate() {
                            *x = hit(7 * k + j);
                        }
                    })
                }));
                assert!(chunked.is_err(), "par_chunks_mut {n} at {at}");
            }
        }
    }

    #[test]
    fn par_map_matches_serial() {
        for n in [0, 1, 5, 1000, 4096, 100_003] {
            let got = par_map_min(n, 1, |i| i * i + 1);
            let want: Vec<usize> = (0..n).map(|i| i * i + 1).collect();
            assert_eq!(got, want);
        }
    }

    /// `par_fold` is the serial fold, whatever the run; `par_for_each`
    /// visits every item once.
    #[test]
    fn par_fold_and_par_for_each_cover_everything() {
        for (n, run) in [(0, 4), (3, 4), (1000, 1), (10_000, 333)] {
            let sum = par_fold(n, run, 0usize, |r| r.sum::<usize>(), |a, b| a + b);
            assert_eq!(sum, (0..n).sum::<usize>(), "n {n} run {run}");
            let seen = AtomicUsize::new(0);
            par_for_each(0..n, |i| {
                seen.fetch_add(i + 1, Ordering::Relaxed);
            });
            assert_eq!(seen.load(Ordering::Relaxed), (1..=n).sum::<usize>());
        }
    }

    /// `par_chunks2_mut` gives each pair of chunks its index and every
    /// element of both slices once, whole chunks and a short last one.
    #[test]
    fn par_chunks2_mut_pairs_the_chunks() {
        for (n, chunk) in [(0, 3), (5, 8), (4096, 1), (10_001, 7)] {
            let mut a = vec![0usize; n];
            let mut b = vec![0usize; n];
            par_chunks2_mut(&mut a, &mut b, chunk, |i, x, y| {
                assert_eq!(x.len(), y.len());
                for (j, (u, v)) in x.iter_mut().zip(y.iter_mut()).enumerate() {
                    *u += i * chunk + j + 1;
                    *v += 2 * (i * chunk + j) + 1;
                }
            });
            assert!(a.iter().enumerate().all(|(i, x)| *x == i + 1), "n {n} chunk {chunk}");
            assert!(b.iter().enumerate().all(|(i, x)| *x == 2 * i + 1), "n {n} chunk {chunk}");
        }
    }

    #[test]
    fn par_chunks_mut_touches_every_element_once() {
        let mut v = vec![0u32; 10_007];
        par_chunks_mut(&mut v, 100, |i, c| {
            for (k, x) in c.iter_mut().enumerate() {
                *x += (i * 100 + k) as u32;
            }
        });
        assert!(v.iter().enumerate().all(|(i, x)| *x == i as u32));
    }
}

#[cfg(test)]
mod core_tests {
    /// As many cores as the system counts threads, or fewer: and, on
    /// Linux, as many as its own list of processors says.
    #[test]
    fn cores_are_counted() {
        let threads = std::thread::available_parallelism().unwrap().get();
        let cores = super::cores();
        assert!((1..=threads).contains(&cores), "{cores} of {threads}");
        #[cfg(target_os = "linux")]
        if let Ok(info) = std::fs::read_to_string("/proc/cpuinfo") {
            // (Where the list says which core each processor is of.)
            let of = |key: &str| -> Vec<&str> {
                info.lines().filter(|l| l.starts_with(key)).filter_map(|l| l.split(':').nth(1)).map(str::trim).collect()
            };
            let (packages, ids) = (of("physical id"), of("core id"));
            if !ids.is_empty() && packages.len() == ids.len() {
                let mut pairs: Vec<_> = packages.iter().zip(&ids).collect();
                pairs.sort();
                pairs.dedup();
                assert_eq!(cores, pairs.len());
            }
        }
    }
}
