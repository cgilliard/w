//! Which units of a file are in use: a bit for each.
//!
//! The map is kept in memory only. It is rebuilt when a file is opened,
//! by marking everything the root record reaches, so it cannot disagree
//! with the file and nothing of it needs to survive a crash.
//!
//! Space is taken where the last was taken, going on through the file
//! and round again: what is written together lies together. When no gap
//! is long enough the file grows.

/// A map of the units in use. Units from `end` on have never been used.
pub struct FreeMap {
    /// A set bit is a unit in use.
    words: Vec<u64>,
    /// Units at the start that are never given out.
    reserved: u64,
    /// One past the last unit in use.
    end: u64,
    used: u64,
    /// Where the last allocation ended.
    cursor: u64,
    /// The least length that a search of the whole map last failed to
    /// find, if nothing has been released since: a search for as much or
    /// more would fail again.
    no_run_of: u32,
}

impl FreeMap {
    /// A map with only its first `reserved` units in use.
    pub fn new(reserved: u64) -> FreeMap {
        let mut map =
            FreeMap { words: Vec::new(), reserved, end: reserved, used: 0, cursor: reserved, no_run_of: u32::MAX };
        map.set(0, reserved, true);
        map
    }

    /// Units in use, the reserved ones among them.
    pub fn used(&self) -> u64 {
        self.used
    }

    /// One past the last unit in use: the length the file needs.
    pub fn end(&self) -> u64 {
        self.end
    }

    /// Bytes the map itself holds.
    pub fn memory(&self) -> usize {
        self.words.capacity() * 8
    }

    fn bit(&self, i: u64) -> bool {
        self.words.get((i / 64) as usize).is_some_and(|w| w >> (i % 64) & 1 == 1)
    }

    fn set(&mut self, start: u64, n: u64, used: bool) {
        let last = (start + n).div_ceil(64) as usize;
        if used && last > self.words.len() {
            self.words.resize(last, 0);
        }
        for i in start..start + n {
            let (w, b) = ((i / 64) as usize, i % 64);
            debug_assert_ne!(self.words[w] >> b & 1 == 1, used);
            self.words[w] ^= 1 << b;
        }
        if used {
            self.used += n;
            self.end = self.end.max(start + n);
        } else {
            self.used -= n;
        }
    }

    /// Whether every unit of `start..start + n` is in use.
    pub fn is_used(&self, start: u64, n: u64) -> bool {
        (start..start + n).all(|i| self.bit(i))
    }

    /// Whether no unit of `start..start + n` is in use.
    pub fn is_free(&self, start: u64, n: u64) -> bool {
        (start..start + n).all(|i| !self.bit(i))
    }

    /// Marks `start..start + n` in use, as a file's reachable pages are
    /// when it is opened. `false`, and nothing marked, if any of them
    /// already is: two things claim the same space.
    pub fn mark(&mut self, start: u64, n: u64) -> bool {
        if n == 0 || !self.is_free(start, n) {
            return false;
        }
        self.set(start, n, true);
        true
    }

    /// Gives `start..start + n` back. They must all be in use, and not
    /// reserved.
    pub fn release(&mut self, start: u64, n: u64) {
        assert!(start >= self.reserved && self.is_used(start, n), "released units that were not in use");
        self.set(start, n, false);
        self.no_run_of = u32::MAX;
        // The end falls back over a free tail, so that the file does not
        // keep growing past space it has given up.
        if start + n == self.end {
            let mut end = start;
            while end > self.reserved && !self.bit(end - 1) {
                end -= 1;
            }
            self.end = end;
            self.cursor = self.cursor.min(end);
        }
    }

    /// Takes `n` units that lie together, and returns the first: after
    /// the last taken if there is room before the end, else from the
    /// start, else past the end.
    pub fn alloc(&mut self, n: u32) -> u64 {
        assert!(n > 0);
        let start = if n >= self.no_run_of {
            self.end
        } else if let Some(at) =
            self.find(self.cursor, self.end, n).or_else(|| self.find(self.reserved, self.cursor, n))
        {
            at
        } else {
            self.no_run_of = n;
            self.end
        };
        self.set(start, n as u64, true);
        self.cursor = start + n as u64;
        start
    }

    /// The first run of `n` free units within `from..to`.
    fn find(&self, from: u64, to: u64, n: u32) -> Option<u64> {
        let n = n as u64;
        let (mut i, mut run) = (from, 0u64);
        while i < to {
            if i % 64 == 0 && i + 64 <= to {
                // A whole word at a step where it is all one way.
                match self.words.get((i / 64) as usize).copied().unwrap_or(0) {
                    u64::MAX => {
                        run = 0;
                        i += 64;
                        continue;
                    }
                    0 => {
                        if run + 64 >= n {
                            return Some(i - run);
                        }
                        run += 64;
                        i += 64;
                        continue;
                    }
                    _ => {}
                }
            }
            if self.bit(i) {
                run = 0;
            } else {
                run += 1;
                if run == n {
                    return Some(i + 1 - n);
                }
            }
            i += 1;
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    #[test]
    fn space_is_taken_in_order_and_gaps_are_reused() {
        let mut m = FreeMap::new(16);
        assert_eq!((m.used(), m.end()), (16, 16));
        assert_eq!(m.alloc(2), 16);
        assert_eq!(m.alloc(8), 18);
        assert_eq!(m.alloc(1), 26);
        assert_eq!((m.used(), m.end()), (27, 27));
        // A gap of eight in the middle: too short for nine, right for
        // eight, and found again after the end is reached.
        m.release(18, 8);
        assert_eq!(m.alloc(9), 27);
        assert_eq!(m.alloc(3), 18);
        assert_eq!(m.alloc(5), 21);
        assert_eq!(m.alloc(1), 36);
        assert!(m.is_used(16, 21) && m.is_free(37, 100));
        // A free tail gives the end back.
        m.release(36, 1);
        m.release(27, 9);
        assert_eq!(m.end(), 27);
        assert_eq!(m.alloc(4), 27);
    }

    #[test]
    fn marking_refuses_what_is_already_claimed() {
        let mut m = FreeMap::new(16);
        assert!(m.mark(100, 8));
        assert!(m.mark(200, 2));
        assert!(!m.mark(107, 2), "overlaps the first by one");
        assert!(!m.mark(8, 2), "reserved");
        assert!(!m.mark(300, 0));
        assert!(m.is_free(108, 92) && m.is_used(100, 8));
        assert_eq!((m.used(), m.end()), (26, 202));
        // The space between is given out before the file grows.
        assert_eq!(m.alloc(84), 16);
        assert_eq!(m.alloc(92), 108);
        assert_eq!(m.alloc(1), 202);
    }

    #[test]
    #[should_panic(expected = "not in use")]
    fn releasing_free_space_is_a_bug() {
        let mut m = FreeMap::new(16);
        let at = m.alloc(4);
        m.release(at, 5);
    }

    /// Against a list of flags, through many allocations and releases of
    /// every length: nothing is given out twice, the counts agree, and
    /// the file does not grow while a gap would have done.
    #[test]
    fn agrees_with_a_model() {
        let mut rng = Rng::new(0xf7ee);
        for reserved in [0u64, 16, 64, 70] {
            let mut m = FreeMap::new(reserved);
            let mut model: Vec<bool> = vec![true; reserved as usize];
            let mut held: Vec<(u64, u32)> = Vec::new();
            for step in 0..6000 {
                let grow = held.len() < 40 || (rng.next_u64() % 100 < 50 && held.len() < 400);
                if grow {
                    let n = match rng.next_u64() % 10 {
                        0 => 1 + (rng.next_u64() % 200) as u32,
                        1..=3 => 8,
                        _ => 1 + (rng.next_u64() % 4) as u32,
                    };
                    // Whether a gap of n existed before the end.
                    let had_gap = model[reserved as usize..].split(|u| *u).any(|gap| gap.len() >= n as usize);
                    let end_before = m.end();
                    let at = m.alloc(n);
                    assert!(at >= reserved);
                    if model.len() < (at + n as u64) as usize {
                        model.resize((at + n as u64) as usize, false);
                    }
                    for u in &mut model[at as usize..(at + n as u64) as usize] {
                        assert!(!*u, "step {step}: unit given out twice");
                        *u = true;
                    }
                    if had_gap {
                        assert!(at + n as u64 <= end_before, "step {step}: grew past a gap of {n}");
                    } else {
                        assert_eq!(at, end_before, "step {step}");
                    }
                    held.push((at, n));
                } else {
                    let (at, n) = held.swap_remove(rng.next_u64() as usize % held.len());
                    m.release(at, n as u64);
                    model[at as usize..(at + n as u64) as usize].fill(false);
                    while model.len() > reserved as usize && !model[model.len() - 1] {
                        model.pop();
                    }
                }
                assert_eq!(m.used(), model.iter().filter(|u| **u).count() as u64);
                assert_eq!(m.end(), model.len() as u64, "step {step}");
            }
            for (i, u) in model.iter().enumerate() {
                assert_eq!(m.is_used(i as u64, 1), *u);
            }
        }
    }
}
