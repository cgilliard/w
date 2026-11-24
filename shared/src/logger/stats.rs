//! How the node is doing, written down every few seconds.
//!
//! A [`Stats`] is a list of numbers the node keeps as it goes: so many
//! requests, so many bytes sent, so many peers live. Whoever does a
//! thing adds to its number ([`Stats::add`]), which costs one atomic
//! add and nothing else. A thread of its own ([`StatsLog`]) reads them
//! and writes the stats log, a line at a time, in columns:
//!
//! ```text
//! Uptime: 300:00:00         Requests_______BytesSent_________PeersLive
//! [2026-10-17 19:30:44:000] 3,000          1,000,003         14
//! 10s ending 19:30:54:      3              100               13
//! 10s ending 19:31:04:      4              105               15
//! 10s ending 19:31:14:      5              200               12
//! 10s ending 19:31:24:      10             1,000             12
//! 10s ending 19:31:34:      1              900               15
//! 10s ending 19:31:44:      0              30                15
//! Uptime: 300:01:00         Requests_______BytesSent_________PeersLive
//! [2026-10-17 19:31:44:000] 3,023          1,002,338         15
//! 10s ending 19:31:54:      43             1,030             13
//! ```
//!
//! * Every ten seconds (unless set otherwise): what happened in those
//!   seconds, after how long they were and the time they ended at.
//! * Every minute (unless set otherwise), after the interval's line
//!   that ends it: the columns' names, with how long the node has been
//!   up, and under them the whole since it started, with the time.
//!
//! # What the numbers are
//!
//! A number that is **counted** (requests, bytes) shows in an
//! interval's line how many there were in it, and in a line of the
//! whole how many there have been in all. The two agree: a whole is the
//! whole before it and the intervals between them, added up. (In the
//! lines above, 3,000 and the six intervals' 23 are 3,023.) The same
//! reading of the numbers is used for the last interval's line and the
//! whole that follows it, so that this is exact, and the two are
//! written at one moment.
//!
//! A number that is a **level** (peers live) is not added up: it shows,
//! in every line, what it was at that moment.
//!
//! Intervals are counted from when the node started, not each from the
//! one before, so they do not drift: so many of them make a whole (six,
//! as set by default), always. When the node stops, what happened since
//! the last interval's line is written as a last, shorter interval,
//! and then the whole, so that the last whole adds up as every other.

use std::io;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;
use std::time::Duration;

use super::fmt::{column, commas, decimal, short_seconds, uptime};
use super::{Logger, Moment};

/// What kind of number a stat is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Things counted.
    Count,
    /// Bytes counted: a wider column, for they are many.
    Bytes,
    /// How much of something there is now (peers, fetches under way).
    Level,
    /// An average: the stat itself is a sum that is added to (the
    /// microseconds requests took), and what is shown is that sum over
    /// the count at the place given (the requests), to one decimal:
    /// for an interval, of that interval; for the whole, of the whole.
    /// `-` where there was nothing to take an average of.
    Average(usize),
}

/// A sum over how many it is the sum of, as it is shown.
fn average(sum: u64, count: u64) -> String {
    match count {
        0 => "-".to_string(),
        _ => decimal(sum as f64 / count as f64, 1),
    }
}

/// How wide the first column is: the time before a line, and a space.
const FIRST: usize = 26;

/// What is called before the stats are read ([`Stats::refreshed_by`]).
type Refresh = Box<dyn Fn(&Stats) + Send + Sync>;

/// The numbers a node keeps of itself.
pub struct Stats {
    /// Each one's name, kind, and the width of its column.
    names: Vec<(String, Kind, usize)>,
    values: Vec<AtomicU64>,
    /// Which of them the log shows, in what order, and how wide each
    /// column is: all of them as they come, unless set.
    shown: Vec<(usize, usize)>,
    /// Called before the stats are read to be written down: so that
    /// what is a level is what it is at that moment.
    refresh: Option<Refresh>,
}

impl Stats {
    /// Stats of these names and kinds, in the order of their columns.
    /// A name is one word (`BytesSent`), since columns are told apart
    /// by the space between them.
    pub fn new(names: &[(&str, Kind)]) -> Stats {
        let width = |name: &str, kind: Kind| {
            // Room for a number in the billions (bytes: in the
            // trillions), and for the name and two more.
            let least = if kind == Kind::Bytes { 18 } else { 15 };
            least.max(name.chars().count() + 2)
        };
        let names: Vec<(String, Kind, usize)> = names.iter().map(|(n, k)| (n.to_string(), *k, width(n, *k))).collect();
        Stats {
            shown: names.iter().enumerate().map(|(i, (_, _, width))| (i, *width)).collect(),
            values: names.iter().map(|_| AtomicU64::new(0)).collect(),
            names,
            refresh: None,
        }
    }

    /// The same, but the log shows these only, in this order, each in a
    /// column this wide (its place in the names given, and the width).
    /// The rest are kept all the same, to be read.
    pub fn showing(mut self, columns: &[(usize, usize)]) -> Stats {
        self.shown = columns.iter().copied().filter(|(i, _)| *i < self.names.len()).collect();
        self
    }

    /// Has `refresh` called before the stats are read to be written
    /// down, to set what is a level to what it is then.
    pub fn refreshed_by(mut self, refresh: Box<dyn Fn(&Stats) + Send + Sync>) -> Stats {
        self.refresh = Some(refresh);
        self
    }

    /// Every stat as it stands, for the log: the levels set afresh.
    fn read_fresh(&self) -> Vec<u64> {
        if let Some(refresh) = &self.refresh {
            refresh(self);
        }
        self.read()
    }

    /// Adds `n` to the stat at `index` (its place in the names given).
    pub fn add(&self, index: usize, n: u64) {
        self.values[index].fetch_add(n, Ordering::Relaxed);
    }

    /// Sets the stat at `index`: for a [`Kind::Level`].
    pub fn set(&self, index: usize, value: u64) {
        self.values[index].store(value, Ordering::Relaxed);
    }

    /// Every stat as it stands.
    pub fn read(&self) -> Vec<u64> {
        self.values.iter().map(|v| v.load(Ordering::Relaxed)).collect()
    }

    /// A line: `first` in the first column, then `cell` of each stat in
    /// its own, filled out with `fill`; the last is not filled out, so
    /// that no line ends in spaces.
    fn line(&self, first: &str, fill: char, cell: impl Fn(usize) -> String) -> String {
        let mut out = column(first, FIRST, ' ');
        for (k, (i, width)) in self.shown.iter().enumerate() {
            match k + 1 == self.shown.len() {
                true => out += &cell(*i),
                false => out += &column(&cell(*i), *width, fill),
            }
        }
        out.push('\n');
        out
    }

    /// The rule drawn under a whole, to set it off from the intervals
    /// that follow: as wide as the names above it.
    pub fn rule(&self) -> String {
        let wide = self.names(0).lines().map(|l| l.chars().count()).max().unwrap_or(0);
        format!("{}\n", "-".repeat(wide))
    }

    /// The columns' names, after how long the node has been up:
    /// `Uptime: 300:00:00         Requests_______BytesSent_________PeersLive`.
    pub fn names(&self, up_seconds: u64) -> String {
        self.line(&format!("Uptime: {}", uptime(up_seconds)), '_', |i| self.names[i].0.clone())
    }

    /// The whole since the start, after the time:
    /// `[2026-10-17 19:30:44:000] 3,000          1,000,003         14`.
    pub fn whole(&self, moment: &Moment, now: &[u64]) -> String {
        self.line(&moment.header(), ' ', |i| match self.names[i].1 {
            Kind::Average(over) => average(now[i], now[over]),
            _ => commas(now[i]),
        })
    }

    /// What happened in the interval of `millis` that ended at
    /// `moment`, from the stats as they were `before` it to as they
    /// are `now`:
    /// `10s ending 19:30:54:      3              100               13`.
    pub fn interval(&self, millis: u64, moment: &Moment, before: &[u64], now: &[u64]) -> String {
        let first =
            format!("{} ending {:02}:{:02}:{:02}:", short_seconds(millis), moment.hour, moment.minute, moment.second);
        self.line(&first, ' ', |i| match self.names[i].1 {
            Kind::Level => commas(now[i]),
            Kind::Count | Kind::Bytes => commas(now[i].saturating_sub(before[i])),
            Kind::Average(over) => average(now[i].saturating_sub(before[i]), now[over].saturating_sub(before[over])),
        })
    }
}

/// When the stats are written down.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Every {
    /// How often what happened since the last time is written, in
    /// milliseconds.
    pub interval: u64,
    /// How often the names and the whole since the start are, in
    /// milliseconds: taken to the nearest whole number of intervals,
    /// one at the least.
    pub summary: u64,
}

impl Default for Every {
    /// Every ten seconds, and the whole every minute: six intervals to
    /// a whole.
    fn default() -> Every {
        Every { interval: 10_000, summary: 60_000 }
    }
}

/// The thread that writes the stats log.
pub struct StatsLog {
    stop: Arc<(Mutex<bool>, Condvar)>,
    thread: Option<JoinHandle<()>>,
}

impl StatsLog {
    /// Starts writing `stats` to `logger`, as often as `every` says:
    /// the names and the whole at once, and then as time passes.
    pub fn start(logger: Logger, stats: Arc<Stats>, every: Every) -> io::Result<StatsLog> {
        let stop = Arc::new((Mutex::new(false), Condvar::new()));
        let thread = {
            let stop = Arc::clone(&stop);
            std::thread::Builder::new().name("log stats".into()).spawn(move || write(&logger, &stats, every, &stop))?
        };
        Ok(StatsLog { stop, thread: Some(thread) })
    }
}

impl Drop for StatsLog {
    /// The whole since the start is written once more, and the thread
    /// ends.
    fn drop(&mut self) {
        *self.stop.0.lock().unwrap_or_else(|e| e.into_inner()) = true;
        self.stop.1.notify_all();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn write(logger: &Logger, stats: &Stats, every: Every, stop: &(Mutex<bool>, Condvar)) {
    let interval = every.interval.max(1);
    // So many intervals to a whole.
    let to_a_whole = ((every.summary + interval / 2) / interval).max(1);
    let started = logger.now();
    let whole = |now: u64, values: &[u64]| {
        let up = now.saturating_sub(started) / 1000;
        logger.write_at(now, &(stats.names(up) + &stats.whole(&Moment::of(now), values) + &stats.rule()));
    };
    // The stats as of the last interval's line, when that was, and how
    // many intervals have been written.
    let (mut last, mut last_at, mut written) = (stats.read_fresh(), started, 0u64);
    whole(started, &last);
    loop {
        // Until the next interval is over, counted from the start, or
        // until told to stop.
        let due = started + (written + 1) * interval;
        let stopped = stop.0.lock().unwrap_or_else(|e| e.into_inner());
        let wait = Duration::from_millis(due.saturating_sub(logger.now()).max(1));
        let (stopped, _) =
            stop.1.wait_timeout_while(stopped, wait, |stopped| !*stopped).unwrap_or_else(|e| e.into_inner());
        // One reading, for the interval's line and for the whole that
        // may follow it: so that the wholes add up.
        let (now, values) = (logger.now(), stats.read_fresh());
        if *stopped {
            // What happened since the last line, as a last interval of
            // whatever length it was; and the whole. (Of no length at
            // all, if it is told to stop in the millisecond a line was
            // written and something has been counted since: the wholes
            // add up all the same.)
            if now > last_at || values != last {
                logger.write_at(now, &stats.interval(now - last_at, &Moment::of(now), &last, &values));
            }
            return whole(now, &values);
        }
        drop(stopped);
        if now < due {
            continue;
        }
        logger.write_at(now, &stats.interval(interval, &Moment::of(now), &last, &values));
        written += 1;
        if written.is_multiple_of(to_a_whole) {
            whole(now, &values);
        }
        logger.rotate_if_due();
        (last, last_at) = (values, now);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logger::Rotation;

    /// 2026-10-17 19:30:44.000 UTC.
    const T: u64 = 1_792_265_444_000;

    fn stats() -> Stats {
        Stats::new(&[("Requests", Kind::Count), ("BytesSent", Kind::Bytes), ("PeersLive", Kind::Level)])
    }

    /// An average is of its own span: an interval's of the interval,
    /// the whole's of the whole; and of nothing, it is not a number.
    #[test]
    fn an_average_is_the_sum_over_the_count_of_its_own_span() {
        let s =
            Stats::new(&[("Requests", Kind::Count), ("AvgLatency(us)", Kind::Average(0)), ("PeersLive", Kind::Level)]);
        // 3,000 requests took 120,000 microseconds; then 4 took 1,000.
        let (before, now) = ([3000, 120_000, 14], [3004, 121_000, 13]);
        assert_eq!(
            [
                s.names(7),
                s.whole(&Moment::of(T), &before),
                s.interval(10_000, &Moment::of(T + 10_000), &before, &now),
                s.interval(10_000, &Moment::of(T + 20_000), &now, &now),
                s.whole(&Moment::of(T + 20_000), &now),
            ]
            .concat(),
            "Uptime: 0:00:07           Requests_______AvgLatency(us)__PeersLive\n\
             [2026-10-17 19:30:44:000] 3,000          40.0            14\n\
             10s ending 19:30:54:      4              250.0           13\n\
             10s ending 19:31:04:      0              -               13\n\
             [2026-10-17 19:31:04:000] 3,004          40.3            13\n"
        );
        assert_eq!(s.whole(&Moment::of(T), &[0, 0, 0]), "[2026-10-17 19:30:44:000] 0              -               0\n");
    }

    /// The log shows the columns it is set to, as wide as it is set
    /// to; the rest are kept, and read, all the same.
    #[test]
    fn the_log_shows_the_columns_it_is_set_to() {
        let all =
            [("Requests", Kind::Count), ("BytesSent", Kind::Bytes), ("Peers", Kind::Level), ("Mined", Kind::Count)];
        let s = Stats::new(&all).showing(&[(0, 11), (3, 6), (2, 6)]);
        let (before, now) = ([3000, 1_000_003, 14, 7], [3003, 1_000_103, 13, 9]);
        assert_eq!(
            [
                s.names(7),
                s.whole(&Moment::of(T), &before),
                s.rule(),
                s.interval(10_000, &Moment::of(T + 10_000), &before, &now)
            ]
            .concat(),
            "Uptime: 0:00:07           Requests___Mined_Peers\n\
             [2026-10-17 19:30:44:000] 3,000      7     14\n\
             ------------------------------------------------\n\
             10s ending 19:30:54:      3          2     13\n"
        );
        s.add(1, 5);
        assert_eq!(s.read()[1], 5);
        // What is a level is set afresh before it is written down.
        let s = Stats::new(&all).refreshed_by(Box::new(|s| s.set(2, 99)));
        assert_eq!((s.read()[2], s.read_fresh()[2]), (0, 99));
    }

    /// The lines of the sample (`docs`), with these columns' widths.
    #[test]
    fn the_lines_are_in_columns() {
        let s = stats();
        let lines = [
            s.names(300 * 3600),
            s.whole(&Moment::of(T), &[3000, 1_000_003, 14]),
            s.interval(10_000, &Moment::of(T + 10_000), &[3000, 1_000_003, 14], &[3003, 1_000_103, 13]),
            s.interval(10_000, &Moment::of(T + 20_000), &[3003, 1_000_103, 13], &[3007, 1_000_208, 15]),
            s.interval(10_000, &Moment::of(T + 60_000), &[3023, 1_002_308, 15], &[3023, 1_002_338, 15]),
            s.names(300 * 3600 + 60),
            s.whole(&Moment::of(T + 60_000), &[3023, 1_002_338, 15]),
        ];
        assert_eq!(
            lines.concat(),
            "Uptime: 300:00:00         Requests_______BytesSent_________PeersLive\n\
             [2026-10-17 19:30:44:000] 3,000          1,000,003         14\n\
             10s ending 19:30:54:      3              100               13\n\
             10s ending 19:31:04:      4              105               15\n\
             10s ending 19:31:44:      0              30                15\n\
             Uptime: 300:01:00         Requests_______BytesSent_________PeersLive\n\
             [2026-10-17 19:31:44:000] 3,023          1,002,338         15\n"
        );
        // Each column begins at the same place in every line, and no
        // line ends in spaces.
        for line in lines.iter().map(|l| l.trim_end_matches('\n')) {
            assert!(!line.ends_with(' '));
            for at in [26, 41, 59] {
                assert!(&line[at - 1..at] != "," && !line[at..].starts_with([' ', '_']), "{line}");
            }
        }
    }

    #[test]
    fn a_column_is_as_wide_as_its_name_and_its_numbers_need() {
        let s = Stats::new(&[
            ("N", Kind::Count),
            ("AVeryLongNameForAColumn", Kind::Level),
            ("B", Kind::Bytes),
            ("Last", Kind::Count),
        ]);
        assert_eq!(
            s.names(7),
            "Uptime: 0:00:07           N______________AVeryLongNameForAColumn__B_________________Last\n"
        );
        // A number too wide for its column moves the rest of its line
        // over, and is not run into.
        let line = s.interval(250, &Moment::of(T), &[0; 4], &[u64::MAX, 5, 12_345_678_901_234, 1]);
        assert_eq!(
            line,
            "0.25s ending 19:30:44:    18,446,744,073,709,551,615 5                        12,345,678,901,234 1\n"
        );
    }

    /// The thread writes the names and the whole at once, then so many
    /// intervals to each whole, and every whole is the one before it
    /// and the intervals between, added up: to the last, written when
    /// it is stopped.
    #[test]
    fn the_wholes_are_the_intervals_added_up() {
        let dir = std::env::temp_dir().join(format!("tabminer-stats-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let stats = Arc::new(stats());
        let logger = Logger::open(dir.join("stats.log"), Rotation::default()).unwrap();
        // Three intervals to a whole.
        let log = StatsLog::start(logger, Arc::clone(&stats), Every { interval: 30, summary: 90 }).unwrap();
        let adding = {
            let stats = Arc::clone(&stats);
            std::thread::spawn(move || {
                for n in 0..4000u64 {
                    stats.add(0, 1);
                    stats.add(1, 24);
                    stats.set(2, 9 + n % 5);
                    if n % 10 == 0 {
                        std::thread::sleep(Duration::from_millis(1));
                    }
                }
            })
        };
        adding.join().unwrap();
        drop(log);
        let text = std::fs::read_to_string(dir.join("stats.log")).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        let number = |word: &str| word.replace(',', "").parse::<u64>().unwrap();
        // The lines in order: what is expected of a whole from the one
        // before it and the intervals since.
        let (mut requests, mut bytes, mut since_whole, mut wholes) = (0u64, 0u64, 0, 0);
        let mut at = 0;
        while at < lines.len() {
            let words: Vec<&str> = lines[at].split_whitespace().collect();
            if lines[at].starts_with("Uptime: ") {
                assert!(lines[at].ends_with("Requests_______BytesSent_________PeersLive"));
                let whole: Vec<&str> = lines[at + 1].split_whitespace().collect();
                assert!(whole[0].starts_with('[') && whole.len() == 5, "{}", lines[at + 1]);
                // (The first is whatever there was when the thread began:
                // from it on, each is the one before and what came between.)
                if wholes == 0 {
                    (requests, bytes) = (number(whole[2]), number(whole[3]));
                }
                assert_eq!((number(whole[2]), number(whole[3])), (requests, bytes), "the whole at line {at}\n{text}");
                // Three intervals to a whole: but before the first,
                // which has none, and the last, which has what there
                // was time for and one shorter.
                // And under the whole, a rule as wide as the names.
                assert_eq!(lines[at + 2], "-".repeat(lines[at].len()), "{text}");
                let last = at + 3 == lines.len();
                assert!(wholes == 0 || since_whole == 3 || (last && since_whole <= 3), "{since_whole}\n{text}");
                (since_whole, wholes, at) = (0, wholes + 1, at + 3);
            } else {
                assert_eq!((words[1], words.len()), ("ending", 6), "{}", lines[at]);
                assert!(words[2].len() == 9 && words[2].ends_with(':'), "{}", lines[at]);
                let n = words.len();
                requests += number(words[n - 3]);
                bytes += number(words[n - 2]);
                // A level is what it was then, and is not added up.
                assert!((9..14).contains(&number(words[n - 1])));
                (since_whole, at) = (since_whole + 1, at + 1);
            }
        }
        // The last whole is everything.
        assert_eq!((requests, bytes), (4000, 96_000));
        assert!(wholes >= 3, "{text}");
        assert!(lines.iter().filter(|l| l.starts_with("0.03s ending ")).count() >= 6, "{text}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
