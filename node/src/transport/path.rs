//! What has been learned of the path to one peer: how long an answer
//! takes, and how much the path carries at once.
//!
//! It outlives a fetch. The next object from the same peer starts with
//! the window the last one ended with, so a peer already measured sends
//! a block in as few round trips as its path allows.

use super::{INITIAL_WINDOW, MAX_REORDER, MAX_RETRY, MAX_WINDOW, MIN_RETRY, MIN_WINDOW, Micros, REORDER, RETRY};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Path {
    window: u32,
    /// Where the window was last brought down to: below it the window
    /// doubles each round, at and above it grows by an eighth. Zero
    /// before any loss.
    threshold: u32,
    /// The smoothed round trip and its variation, in microseconds; no
    /// round trip measured while `measured` is false.
    srtt: u32,
    rttvar: u32,
    measured: bool,
    /// The most chunks the path has been seen to hold at once, of late:
    /// how many arrived between a chunk's being asked for and its
    /// arriving. Zero before any has been measured.
    carried: u32,
    /// The most seen this round.
    seen: u32,
    /// The shortest round trip measured, let rise a little each round
    /// so that one from before the path changed is forgotten; and the
    /// shortest measured this round. Zero: none.
    least: u32,
    round_least: u32,
    /// The last round's shortest round trip was half as long again as
    /// the shortest of all: chunks are waiting their turn somewhere.
    queued: bool,
    /// The path has been found full: asked for twice what it holds, it
    /// held no more. Zero, or what it held when that was found.
    full: u32,
    /// How many places a chunk must be overtaken by to be taken for
    /// lost: more on a path seen to deliver out of order.
    reorder: u32,
}

impl Default for Path {
    fn default() -> Path {
        Path::new()
    }
}

impl Path {
    pub const fn new() -> Path {
        Path {
            window: INITIAL_WINDOW,
            threshold: 0,
            srtt: 0,
            rttvar: 0,
            measured: false,
            carried: 0,
            seen: 0,
            least: 0,
            round_least: 0,
            queued: false,
            full: 0,
            reorder: REORDER as u32,
        }
    }

    /// Chunks that may be asked for and not yet here.
    pub fn window(&self) -> u32 {
        self.window
    }

    /// The smoothed round trip, once one has been measured.
    pub fn round_trip(&self) -> Option<Micros> {
        self.measured.then_some(self.srtt as Micros)
    }

    /// Takes a measured round trip (RFC 6298): the smoothed round trip
    /// moves an eighth of the way to it, the variation a quarter of the
    /// way to how far off it was.
    pub fn sample(&mut self, rtt: Micros) {
        // An hour is as good as forever, and keeps the sums in range.
        let r = (rtt.min(3_600_000_000) as u32).max(1);
        self.least = if self.least == 0 { r } else { self.least.min(r) };
        self.round_least = if self.round_least == 0 { r } else { self.round_least.min(r) };
        self.smooth(r);
    }

    fn smooth(&mut self, r: u32) {
        if !self.measured {
            self.srtt = r;
            self.rttvar = r / 2;
            self.measured = true;
        } else {
            let off = self.srtt.abs_diff(r);
            self.rttvar = ((3 * self.rttvar as u64 + off as u64) / 4) as u32;
            self.srtt = ((7 * self.srtt as u64 + r as u64) / 8) as u32;
        }
    }

    /// How long a silence is a loss: the smoothed round trip and four
    /// times its variation, within [`MIN_RETRY`] and [`MAX_RETRY`];
    /// [`RETRY`] before any round trip is measured.
    pub fn retry(&self) -> Micros {
        if !self.measured {
            return RETRY;
        }
        (self.srtt as Micros + 4 * self.rttvar as Micros).clamp(MIN_RETRY, MAX_RETRY)
    }

    /// How many places a chunk must be overtaken by to be taken for
    /// lost.
    pub fn reorder(&self) -> u64 {
        self.reorder as u64
    }

    /// How long after a chunk was overtaken, with nothing more
    /// arriving, it is taken for lost though fewer than
    /// [`Path::reorder`] have overtaken it: a quarter of the round
    /// trip (five milliseconds at the least), and as many times more as
    /// the places allowed have been raised.
    ///
    /// A small window never has enough in it to overtake a chunk by
    /// many places. Without this every loss in one would wait out the
    /// whole retry time.
    pub fn grace(&self) -> Micros {
        let quarter = if self.measured { self.srtt as Micros / 4 } else { RETRY / 4 };
        // (Never as long as a silence is: where it was, the silence
        // came first every time, and this never.)
        (quarter.max(5_000) * self.reorder as Micros / REORDER).min(self.retry() / 2)
    }

    /// A chunk taken for lost had only been overtaken: the path
    /// delivers further out of order than was allowed for. Twice as
    /// much is allowed, up to [`MAX_REORDER`].
    pub fn disordered(&mut self) {
        self.reorder = (2 * self.reorder).min(MAX_REORDER);
    }

    /// A round passed in which that did not happen: a sixteenth less
    /// (one less, at the least) is allowed, down to [`REORDER`].
    pub fn ordered(&mut self) {
        self.reorder = (self.reorder - (self.reorder / 16).max(1)).max(REORDER as u32);
    }

    /// A chunk arrived, and `held` others had arrived since it was
    /// asked for: the path held that many at once.
    pub fn carry(&mut self, held: u32) {
        self.seen = self.seen.max(held);
    }

    /// The most chunks the path has been seen to hold at once, of late.
    pub fn carried(&self) -> u32 {
        self.carried
    }

    /// Whether the path has been found full.
    pub fn full(&self) -> bool {
        self.full != 0
    }

    /// Whether chunks were waiting their turn somewhere on the path in
    /// the last round: its quickest answer took half as long again as
    /// the quickest ever.
    pub fn queued(&self) -> bool {
        self.queued
    }

    /// A round has ended. What the path holds is the most seen in it,
    /// or a sixteenth less than it was held to be, whichever is more:
    /// so a path that has narrowed is found out in a few rounds. A path
    /// found full that now holds a quarter more than it did is full no
    /// longer. The shortest round trip rises by a sixty-fourth towards
    /// the round's.
    pub fn round(&mut self) {
        if self.round_least != 0 {
            self.queued = 2 * self.round_least as u64 > 3 * self.least as u64;
            self.least = (self.least + (self.least / 64).max(1)).min(self.round_least);
            self.round_least = 0;
        }
        self.carried = self.seen.max(self.carried - self.carried.div_ceil(16));
        self.seen = 0;
        if self.full != 0 && self.carried >= self.full + self.full.div_ceil(4) {
            self.full = 0;
        }
    }

    /// Chunks were lost, more than a few. Whether the window comes down
    /// depends on why.
    ///
    /// A narrow path holds what it holds however much is asked of it,
    /// makes the rest wait, and drops what there is no room to keep
    /// waiting. A path that merely loses a share of what crosses it
    /// holds the more the more is asked, and keeps nothing waiting. So
    /// a path is shown to be full by either of two things: answers that
    /// come late, all of them, because they queued
    /// ([`Path::queued`]); or a window over twice what the path has
    /// been seen to hold. It is marked full, and from then on loss
    /// brings the window down to what the path holds (though not under
    /// three quarters of what it held when it was found full, lest a
    /// lossy path once taken for a full one be brought down round after
    /// round). Until a path is found full, loss does not bring its
    /// window down at all: on such a path a smaller window loses the
    /// same share and only carries less.
    ///
    /// Neither sign means anything unless the window was `pressed`:
    /// filled with asks. An object of five chunks shows nothing of a
    /// path that would hold fifty.
    ///
    /// Where nothing has yet been seen to arrive, the window halves.
    /// Never under [`MIN_WINDOW`].
    pub fn lost(&mut self, pressed: bool) {
        if self.carried == 0 {
            self.window = (self.window / 2).max(MIN_WINDOW);
            self.threshold = self.window;
            return;
        }
        if pressed && (self.window > 2 * self.carried || (self.queued && self.full == 0)) {
            self.full = self.carried;
        }
        let to = self.carried.max(self.full - self.full / 4).max(MIN_WINDOW);
        if self.full != 0 && self.window > to {
            self.window = to;
            self.threshold = self.window;
        }
    }

    /// A round ended with the window full and no reason to bring it
    /// down: it doubles while it has never been cut or is under where
    /// it was cut to, and grows by an eighth (one, at the least)
    /// otherwise.
    pub fn grow(&mut self) {
        let w = self.window;
        let grown = if self.threshold != 0 && w >= self.threshold { w + (w / 8).max(1) } else { 2 * w };
        self.window = grown.min(MAX_WINDOW);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transport::MILLI;

    #[test]
    fn the_retry_time_is_the_round_trip_and_four_times_its_variation() {
        let mut p = Path::new();
        assert_eq!((p.retry(), p.round_trip()), (RETRY, None));
        // The first sample: itself, and half of itself as the variation.
        p.sample(200 * MILLI);
        assert_eq!((p.round_trip(), p.retry()), (Some(200 * MILLI), 600 * MILLI));
        // A steady path: the variation dies away to the floor.
        for _ in 0..40 {
            p.sample(200 * MILLI);
        }
        assert_eq!(p.round_trip(), Some(200 * MILLI));
        assert!(p.retry() < 201 * MILLI);
        // One slow answer moves the round trip an eighth, the variation a
        // quarter of the difference.
        p.sample(1000 * MILLI);
        assert_eq!(p.round_trip(), Some(300 * MILLI));
        assert_eq!(p.retry(), 300 * MILLI + 4 * (800 * MILLI / 4));
        // Within its bounds, whatever is measured.
        let mut fast = Path::new();
        fast.sample(50);
        assert_eq!(fast.retry(), MIN_RETRY);
        let mut slow = Path::new();
        slow.sample(u64::MAX);
        assert_eq!(slow.retry(), MAX_RETRY);
        for _ in 0..100 {
            slow.sample(u64::MAX);
        }
        assert_eq!(slow.retry(), MAX_RETRY);
    }

    #[test]
    fn disorder_is_allowed_for_quickly_and_forgotten_slowly() {
        let mut p = Path::new();
        assert_eq!(p.reorder(), REORDER);
        p.ordered();
        assert_eq!(p.reorder(), REORDER);
        p.disordered();
        p.disordered();
        assert_eq!(p.reorder(), 4 * REORDER);
        p.ordered();
        assert_eq!(p.reorder(), 4 * REORDER - REORDER / 4);
        p.ordered();
        assert_eq!(p.reorder(), 4 * REORDER - REORDER / 4 - 1);
        for _ in 0..20 {
            p.disordered();
        }
        assert_eq!(p.reorder(), MAX_REORDER as u64);
        for _ in 0..200 {
            p.ordered();
        }
        assert_eq!(p.reorder(), REORDER);
    }

    #[test]
    fn the_window_doubles_then_creeps() {
        let mut p = Path::new();
        assert_eq!(p.window(), INITIAL_WINDOW);
        p.grow();
        p.grow();
        assert_eq!(p.window(), 4 * INITIAL_WINDOW);
        // Nothing seen to arrive: halved, and from there by eighths.
        p.lost(true);
        assert_eq!(p.window(), 2 * INITIAL_WINDOW);
        p.grow();
        assert_eq!(p.window(), 2 * INITIAL_WINDOW + INITIAL_WINDOW / 4);
        // Never under the least (from which it grows by one), never
        // over the most.
        for _ in 0..10 {
            p.lost(true);
        }
        assert_eq!(p.window(), MIN_WINDOW);
        p.grow();
        assert_eq!(p.window(), MIN_WINDOW + 1);
        for _ in 0..100 {
            p.grow();
        }
        assert_eq!(p.window(), MAX_WINDOW);
    }

    #[test]
    fn loss_brings_the_window_down_only_on_a_full_path() {
        // A path that loses a fifth of everything: asked for sixty-four,
        // it holds fifty. Loss changes nothing.
        let mut p = Path::new();
        p.grow();
        p.grow();
        p.carry(50);
        p.carry(31);
        p.round();
        assert_eq!((p.carried(), p.full()), (50, false));
        p.lost(true);
        assert_eq!((p.window(), p.full()), (64, false));
        // A narrow path: asked for sixty-four, it holds six. Found
        // full, and the window is what it holds.
        let mut p = Path::new();
        p.grow();
        p.grow();
        p.carry(6);
        p.round();
        p.lost(true);
        assert_eq!((p.window(), p.full()), (6, true));
        // It tries for more, an eighth (or one) a round; a loss while
        // full brings it straight back.
        p.grow();
        assert_eq!(p.window(), 7);
        p.carry(6);
        p.round();
        p.lost(true);
        assert_eq!(p.window(), 6);
        // The path widens: holding a quarter more than when it was found
        // full, it is full no longer, and loss is only loss again.
        p.grow();
        p.grow();
        p.carry(8);
        p.round();
        assert!(!p.full());
        p.lost(true);
        assert_eq!(p.window(), 8);
        // What a path holds is forgotten a sixteenth a round, so that a
        // path that has narrowed is found full again.
        let mut p = Path::new();
        p.carry(160);
        p.round();
        for _ in 0..5 {
            p.grow();
        }
        p.lost(true);
        assert_eq!((p.window(), p.full()), (160, true));
        for _ in 0..30 {
            p.carry(20);
            p.round();
        }
        assert_eq!(p.carried(), 20);
        p.lost(true);
        assert_eq!(p.window(), 20);
        // And never under the least.
        let mut p = Path::new();
        p.carry(1);
        p.round();
        p.lost(true);
        assert_eq!((p.window(), p.full()), (MIN_WINDOW, true));
        // A window that was never filled shows nothing: five chunks
        // were all there were.
        let mut p = Path::new();
        p.carry(5);
        p.round();
        p.lost(false);
        assert_eq!((p.window(), p.full()), (INITIAL_WINDOW, false));
        // Answers that all come late show a queue, and a queue a full
        // path, though the window is not twice what it holds.
        let mut p = Path::new();
        p.sample(100 * MILLI);
        p.carry(12);
        p.round();
        assert!(!p.queued());
        p.lost(true);
        assert_eq!((p.window(), p.full()), (INITIAL_WINDOW, false));
        for rtt in [900, 700, 800] {
            p.sample(rtt * MILLI);
        }
        p.carry(12);
        p.round();
        assert!(p.queued());
        p.lost(true);
        assert_eq!((p.window(), p.full()), (12, true));
    }
}
