//! Logs: lines written to a file, with the time before each, and the
//! file put aside for a new one when it has grown too large or too old.
//!
//! A [`Logger`] is one log. A node has several (what it does, what it
//! is asked, how it is doing), each its own `Logger` on its own file.
//!
//! # Writing
//!
//! * [`Logger::log`] writes a line with the time before it:
//!   `[2026-10-17 19:49:31:471] the line`.
//! * [`Logger::log_no_header`] writes the line as it is given, for a log
//!   whose lines are laid out by whoever writes them.
//! * [`Logger::log_all`] is [`Logger::log`], and the same line to the
//!   terminal (standard error) as well.
//!
//! Each call is one line and one write: lines from several threads are
//! never mixed into one another, and what was written before a crash
//! is in the file.
//!
//! The time is by the universal clock (UTC), not the place's: the
//! standard library knows of no time zones, and a log that is compared
//! with another node's is better off without them.
//!
//! # Rotation
//!
//! Before a line is written, the file is put aside if either limit of
//! [`Rotation`] is passed: it has been written to for longer than
//! [`Rotation::max_age`], or the line would take it over
//! [`Rotation::max_size`]. Put aside means renamed, with the time it
//! was put aside in its name, and a new file begun under the old name:
//!
//! ```text
//! tabernacle.log  ->  tabernacle_R_02_03_2026_10_00.log
//!                     (month, day, year, hour, minute)
//! ```
//!
//! A line is never split between two files. If two files are put aside
//! within one minute, the second and later have a count after the
//! minute (`..._10_00_02.log`, `..._10_00_03.log`), so that none is
//! written over. Files put aside are never deleted here: that is for
//! whoever keeps the machine.
//!
//! # The first line of a file put aside
//!
//! A file put aside begins with a line saying what it is and when it
//! was begun: the log's name (the file's, without its directory) and
//! the moment, to the second:
//!
//! ```text
//! tabernacle.log_02_03_2026_10_30_04
//! (month, day, year, hour, minute, second)
//! ```
//!
//! So it still says which log it was and when it began, whatever name
//! it has been given. The file being written to has no such line: it is
//! the log's lines and nothing else. (The line is put in when the file
//! is put aside, by copying the file in under it.) A file that holds
//! nothing is not put aside: there is nothing in it to keep.
//!
//! # The logs of a node
//!
//! * The **main** log: how the node was started and with what settings,
//!   then only what is wrong or what matters (an error, a critical
//!   event, stopping), and each time one of the other logs' files was
//!   put aside, with the name it was given
//!   ([`Logger::report_rotations_to`]). It is written by whoever calls
//!   it, on their own thread: there is little of it, and what there is
//!   should be in the file before anything else happens.
//! * The **request** log: what the node was asked. There is a great
//!   deal of it, and whoever answers a request must not wait on a disk
//!   for it: it is written by a thread of its own, from a queue of a
//!   size that is set ([`queued::Queued`]). A queue that overflows
//!   drops lines, and says so in the main log.
//! * The **stats** log: how the node is doing, every few seconds for
//!   those seconds and every minute for the whole time since it
//!   started, in columns ([`stats`]). Also a thread of its own.
//!
//! Numbers and times are written the same way in all of them
//! ([`fmt`]).
//!
//! # A log must not bring the node down
//!
//! Nothing here returns an error or panics once the log is open. A line
//! that cannot be written is counted ([`Logger::failures`]), and the
//! first such failure is said once on the terminal.

use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

pub mod fmt;
pub mod queued;
pub mod stats;

/// When a log's file is put aside for a new one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rotation {
    /// The longest a file is written to, in seconds; zero for no limit.
    pub max_age: u64,
    /// The most bytes a file holds; zero for no limit. A single line
    /// longer than this is written all the same, to a file of its own.
    pub max_size: u64,
}

impl Default for Rotation {
    /// An hour, or a mebibyte, whichever comes first.
    fn default() -> Rotation {
        Rotation { max_age: 3600, max_size: 1 << 20 }
    }
}

/// A time by the calendar and the clock, in UTC.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Moment {
    pub year: u64,
    pub month: u64,
    pub day: u64,
    pub hour: u64,
    pub minute: u64,
    pub second: u64,
    pub milli: u64,
}

impl Moment {
    /// The moment `millis` milliseconds after the start of 1970.
    pub fn of(millis: u64) -> Moment {
        let (seconds, milli) = (millis / 1000, millis % 1000);
        let (days, of_day) = (seconds / 86_400, seconds % 86_400);
        // Days to a date, by the calendar's cycle of four hundred years
        // (146,097 days), counted from the first of March so that the
        // day a leap year adds is the last of its year.
        let z = days + 719_468;
        let (era, day_of_era) = (z / 146_097, z % 146_097);
        let year_of_era = (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
        let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
        let march_month = (5 * day_of_year + 2) / 153;
        let day = day_of_year - (153 * march_month + 2) / 5 + 1;
        let month = if march_month < 10 { march_month + 3 } else { march_month - 9 };
        let year = year_of_era + era * 400 + (month <= 2) as u64;
        Moment { year, month, day, hour: of_day / 3600, minute: of_day % 3600 / 60, second: of_day % 60, milli }
    }

    /// What goes before a line: `[2026-10-17 19:49:31:471]`.
    pub fn header(&self) -> String {
        format!(
            "[{:04}-{:02}-{:02} {:02}:{:02}:{:02}:{:03}]",
            self.year, self.month, self.day, self.hour, self.minute, self.second, self.milli
        )
    }

    /// The moment as the startup message says it:
    /// `02-03-2026 00:00:02 UTC` (month, day, year).
    pub fn started(&self) -> String {
        format!(
            "{:02}-{:02}-{:04} {:02}:{:02}:{:02} UTC",
            self.month, self.day, self.year, self.hour, self.minute, self.second
        )
    }

    /// What goes into the name of a file put aside at this moment:
    /// `_R_02_03_2026_10_00` (month, day, year, hour, minute).
    pub fn rotated(&self) -> String {
        format!("_R_{:02}_{:02}_{:04}_{:02}_{:02}", self.month, self.day, self.year, self.hour, self.minute)
    }

    /// What goes after a log's name in the first line of a file begun
    /// at this moment: `_02_03_2026_10_30_04` (month, day, year, hour,
    /// minute, second).
    pub fn begun(&self) -> String {
        format!(
            "_{:02}_{:02}_{:04}_{:02}_{:02}_{:02}",
            self.month, self.day, self.year, self.hour, self.minute, self.second
        )
    }
}

/// The clock: milliseconds since the start of 1970.
type Clock = Box<dyn Fn() -> u64 + Send + Sync>;

fn system_clock() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64)
}

struct Inner {
    /// The file being written to; none if it could not be opened after
    /// the last was put aside, and is to be tried again.
    file: Option<File>,
    /// Bytes in it.
    size: u64,
    /// Whether it holds anything.
    written: bool,
    /// When it began to be written to, by this logger.
    since: u64,
}

/// What is told of each file put aside.
type OnRotate = Box<dyn Fn(&Path) + Send + Sync>;

/// One log.
pub struct Logger {
    path: PathBuf,
    rotation: Rotation,
    clock: Clock,
    inner: Mutex<Inner>,
    failures: AtomicU64,
    /// Whether [`Logger::log_all`] still writes to the terminal too.
    terminal: AtomicBool,
    /// Told of each file put aside: the name it was given.
    on_rotate: Option<OnRotate>,
}

impl Logger {
    /// Opens the log at `path`, which is made if it is not there and
    /// added to if it is. Its directory must exist.
    ///
    /// A file found there counts as begun now: how long it had been
    /// written to before is not known. What it holds counts towards
    /// its size.
    pub fn open(path: impl Into<PathBuf>, rotation: Rotation) -> io::Result<Logger> {
        Logger::with_clock(path, rotation, Box::new(system_clock))
    }

    fn with_clock(path: impl Into<PathBuf>, rotation: Rotation, clock: Clock) -> io::Result<Logger> {
        let logger = Logger {
            path: path.into(),
            rotation,
            clock,
            inner: Mutex::new(Inner { file: None, size: 0, written: false, since: 0 }),
            failures: AtomicU64::new(0),
            terminal: AtomicBool::new(true),
            on_rotate: None,
        };
        logger.recover();
        let now = (logger.clock)();
        logger.begin(&mut logger.lock(), now)?;
        Ok(logger)
    }

    /// What a run that stopped between the two steps of putting a
    /// file aside left: the lines under the name they were held by,
    /// and beside them a file of the name they were to have, empty or
    /// part written. The lines are given that name, without their
    /// first line.
    fn recover(&self) {
        let Some(name) = self.path.file_stem().map(|s| s.to_string_lossy().into_owned()) else { return };
        let Ok(entries) = self.path.parent().map_or_else(|| std::fs::read_dir("."), std::fs::read_dir) else { return };
        for entry in entries.flatten() {
            let held = entry.path();
            let Some(file) = held.file_name().map(|n| n.to_string_lossy().into_owned()) else { continue };
            if let Some(aside) = file.strip_suffix(".moving").filter(|aside| aside.starts_with(&name)) {
                let aside = held.with_file_name(aside);
                let _ = std::fs::remove_file(&aside);
                let _ = std::fs::rename(&held, &aside);
            }
        }
    }

    /// Opens the file to be written to, at `now`: added to if it is
    /// there, made if it is not.
    fn begin(&self, inner: &mut Inner, now: u64) -> io::Result<()> {
        let file = OpenOptions::new().create(true).append(true).open(&self.path)?;
        let size = file.metadata()?.len();
        (inner.size, inner.written, inner.since) = (size, size > 0, now);
        inner.file = Some(file);
        Ok(())
    }

    /// Puts what the log's file holds into `aside`, under a first line
    /// that says which log it is and when the file was begun
    /// (`request.log_02_03_2026_10_30_04`), and empties the log's file.
    ///
    /// The line is of the file put aside only: the file being written
    /// to is lines of the log and nothing else. So the file cannot
    /// simply be given another name: it is copied in under the line.
    /// If that fails, nothing is lost: what there is of `aside` is
    /// removed and the log's file is left as it was.
    ///
    /// In two steps. With the log held, the file is only given another
    /// name ([`Logger::take_aside`]), which takes no time, and a new
    /// one begun: whoever has a line to write waits for no more than
    /// that. The copying, which is as long as the file is, is done
    /// after ([`Logger::set_aside`]) by whoever found the file due,
    /// with the log let go.
    fn take_aside(&self, aside: &Path, begun: u64) -> io::Result<Aside> {
        let held = held_of(aside);
        // (The name is taken from here on, though nothing is in it yet.)
        OpenOptions::new().write(true).create_new(true).open(aside)?;
        if let Err(e) = std::fs::rename(&self.path, &held) {
            let _ = std::fs::remove_file(aside);
            return Err(e);
        }
        Ok(Aside { held, aside: aside.to_path_buf(), begun })
    }

    /// The second step: the lines, under their first line, in the file
    /// of the name they are put aside under. If that fails, they are
    /// there without the line.
    fn set_aside(&self, taken: &Aside) -> io::Result<()> {
        let name = self.path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let copy = || -> io::Result<()> {
            let mut to = OpenOptions::new().write(true).truncate(true).open(&taken.aside)?;
            to.write_all(format!("{name}{}\n", Moment::of(taken.begun).begun()).as_bytes())?;
            io::copy(&mut std::fs::File::open(&taken.held)?, &mut to)?;
            to.sync_all()
        };
        match copy() {
            Ok(()) => std::fs::remove_file(&taken.held),
            Err(e) => {
                let _ = std::fs::remove_file(&taken.aside);
                std::fs::rename(&taken.held, &taken.aside)?;
                Err(e)
            }
        }
    }

    /// Has each file this log puts aside told of in `main`, by the name
    /// it was given: so that the main log says where the others' lines
    /// of any time are to be found.
    pub fn report_rotations_to(mut self, main: std::sync::Arc<Logger>) -> Logger {
        let name = self.path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        self.on_rotate = Some(Box::new(move |aside: &Path| {
            let aside = aside.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
            main.log(&format!("{name} rotated to {aside}"));
        }));
        self
    }

    /// The time by this log's clock: milliseconds since the start of
    /// 1970.
    pub fn now(&self) -> u64 {
        (self.clock)()
    }

    /// Writes `text`, a line or several with their ends, as of the
    /// moment `now`: for a line whose time was taken when it was said
    /// and that is written later ([`queued`]), and for lines laid out
    /// by whoever writes them ([`stats`]).
    pub fn write_at(&self, now: u64, text: &str) {
        self.write(now, text);
    }

    /// The file being written to.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Lines that could not be written.
    pub fn failures(&self) -> u64 {
        self.failures.load(Ordering::Relaxed)
    }

    /// Writes `line` with the time before it.
    pub fn log(&self, line: &str) {
        let now = (self.clock)();
        self.write(now, &format!("{} {line}\n", Moment::of(now).header()));
    }

    /// Writes `line` as it is, with nothing before it.
    pub fn log_no_header(&self, line: &str) {
        self.write((self.clock)(), &format!("{line}\n"));
    }

    /// Writes `line` with the time before it, to the log and to the
    /// terminal (standard error) alike.
    ///
    /// Once [`Logger::file_only`] has been called, to the log alone.
    pub fn log_all(&self, line: &str) {
        let now = (self.clock)();
        let text = format!("{} {line}\n", Moment::of(now).header());
        // (The terminal may be gone; the log is what matters.)
        if self.terminal.load(Ordering::Relaxed) {
            let _ = io::stderr().write_all(text.as_bytes());
        }
        self.write(now, &text);
    }

    /// From here on [`Logger::log_all`] and
    /// [`Logger::log_all_no_header`] write to the log alone: the
    /// terminal is for whoever is at it. A node says how it started
    /// there, and nothing after.
    pub fn file_only(&self) {
        self.terminal.store(false, Ordering::Relaxed);
    }

    /// Writes `line` as it is, to the log and to the terminal alike:
    /// for the rules drawn across the startup messages.
    pub fn log_all_no_header(&self, line: &str) {
        let text = format!("{line}\n");
        if self.terminal.load(Ordering::Relaxed) {
            let _ = io::stderr().write_all(text.as_bytes());
        }
        self.write((self.clock)(), &text);
    }

    /// Puts the file aside if it has been written to for longer than it
    /// may be, though nothing is being written: for a caller that looks
    /// to it now and then, so that a quiet log is still put aside on
    /// time.
    pub fn rotate_if_due(&self) {
        let now = (self.clock)();
        let mut inner = self.lock();
        if inner.written && self.aged(&inner, now) {
            let taken = self.rotate_locked(&mut inner, now);
            drop(inner);
            self.finish(taken);
        }
    }

    /// Puts the file aside now, whatever its age and size, and begins a
    /// new one. The name it was given: none if it held nothing but its
    /// first line (not worth keeping) or could not be renamed.
    pub fn rotate(&self) -> Option<PathBuf> {
        let now = (self.clock)();
        let mut inner = self.lock();
        let taken = self.rotate_locked(&mut inner, now);
        drop(inner);
        self.finish(taken)
    }

    /// What is left of putting a file aside, done with the log let go:
    /// the name it was given.
    fn finish(&self, taken: Option<Aside>) -> Option<PathBuf> {
        let taken = taken?;
        if let Err(e) = self.set_aside(&taken) {
            self.failed("put aside", &e);
        }
        if let Some(tell) = &self.on_rotate {
            tell(&taken.aside);
        }
        Some(taken.aside)
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Inner> {
        self.inner.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn aged(&self, inner: &Inner, now: u64) -> bool {
        self.rotation.max_age > 0 && now.saturating_sub(inner.since) >= self.rotation.max_age.saturating_mul(1000)
    }

    fn failed(&self, what: &str, e: &io::Error) {
        if self.failures.fetch_add(1, Ordering::Relaxed) == 0 {
            let _ = writeln!(io::stderr(), "the log {} cannot be {what}: {e}", self.path.display());
        }
    }

    fn write(&self, now: u64, text: &str) {
        let mut inner = self.lock();
        let over = self.rotation.max_size > 0 && inner.size + text.len() as u64 > self.rotation.max_size;
        // (A file with nothing in it is not put
        // aside: for its age there is nothing to keep, and a line too
        // long for any file goes into this one.)
        let taken = match inner.written && (over || self.aged(&inner, now)) {
            true => self.rotate_locked(&mut inner, now),
            false => None,
        };
        if inner.file.is_none()
            && let Err(e) = self.begin(&mut inner, now)
        {
            return self.failed("opened", &e);
        }
        match inner.file.as_mut().expect("opened above").write_all(text.as_bytes()) {
            Ok(()) => {
                inner.size += text.len() as u64;
                inner.written = true;
            }
            Err(e) => self.failed("written to", &e),
        }
        drop(inner);
        self.finish(taken);
    }

    /// The name a file put aside at `moment` is given: the log's own,
    /// with the moment before its ending, and a count after that if
    /// the name is taken.
    fn aside(&self, moment: &Moment) -> PathBuf {
        let stem = self.path.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
        let ending = self.path.extension().map(|e| format!(".{}", e.to_string_lossy())).unwrap_or_default();
        let named = |count: u32| {
            let count = if count == 1 { String::new() } else { format!("_{count:02}") };
            self.path.with_file_name(format!("{stem}{}{count}{ending}", moment.rotated()))
        };
        (1..).map(named).find(|p| !p.exists() && !held_of(p).exists()).expect("some count is free")
    }

    fn rotate_locked(&self, inner: &mut Inner, now: u64) -> Option<Aside> {
        if !inner.written {
            inner.since = now;
            return None;
        }
        // Closed before it is given another name: some systems will not
        // do that to a file that is open.
        inner.file = None;
        let aside = self.aside(&Moment::of(now));
        let taken = self.take_aside(&aside, inner.since);
        if let Err(e) = &taken {
            // The same file goes on being written to.
            self.failed("put aside", e);
        }
        if let Err(e) = self.begin(inner, now) {
            self.failed("opened", &e);
        }
        taken.ok()
    }
}

/// A file being put aside: where its lines are meanwhile, the name they
/// are put aside under, and when the file was begun.
struct Aside {
    held: PathBuf,
    aside: PathBuf,
    begun: u64,
}

/// Where a file's lines are while they are put aside under `aside`.
fn held_of(aside: &Path) -> PathBuf {
    let mut name = aside.file_name().map(|n| n.to_os_string()).unwrap_or_default();
    name.push(".moving");
    aside.with_file_name(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    /// A directory of this test's own, removed when it is done.
    struct Dir(PathBuf);

    impl Dir {
        fn new(name: &str) -> Dir {
            static COUNT: AtomicU64 = AtomicU64::new(0);
            let unique =
                format!("tabminer-log-{name}-{}-{}", std::process::id(), COUNT.fetch_add(1, Ordering::Relaxed));
            let path = std::env::temp_dir().join(unique);
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).unwrap();
            Dir(path)
        }

        /// The names of the files in it, in order.
        fn files(&self) -> Vec<String> {
            let mut names: Vec<String> = std::fs::read_dir(&self.0)
                .unwrap()
                .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
                .collect();
            names.sort();
            names
        }

        fn read(&self, name: &str) -> String {
            std::fs::read_to_string(self.0.join(name)).unwrap()
        }
    }

    impl Drop for Dir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// A clock the test moves.
    fn clock(start: u64) -> (Arc<AtomicU64>, Clock) {
        let now = Arc::new(AtomicU64::new(start));
        let read = Arc::clone(&now);
        (now, Box::new(move || read.load(Ordering::Relaxed)))
    }

    /// 2026-10-17 19:49:31.471 UTC.
    const T: u64 = 1_792_266_571_471;

    #[test]
    fn a_moment_is_its_date_and_time() {
        let m = |millis| {
            let m = Moment::of(millis);
            (m.year, m.month, m.day, m.hour, m.minute, m.second, m.milli)
        };
        assert_eq!(m(0), (1970, 1, 1, 0, 0, 0, 0));
        assert_eq!(m(T), (2026, 10, 17, 19, 49, 31, 471));
        // The last and the first moment of a year; the day a leap year
        // adds, in a year that has it, one that does not, and the two
        // centuries that differ.
        assert_eq!(m(1_767_225_599_999), (2025, 12, 31, 23, 59, 59, 999));
        assert_eq!(m(1_767_225_600_000), (2026, 1, 1, 0, 0, 0, 0));
        assert_eq!(m(1_709_164_800_000), (2024, 2, 29, 0, 0, 0, 0));
        assert_eq!(m(1_677_628_800_000), (2023, 3, 1, 0, 0, 0, 0));
        assert_eq!(m(951_782_400_000), (2000, 2, 29, 0, 0, 0, 0));
        assert_eq!(m(4_107_542_400_000), (2100, 3, 1, 0, 0, 0, 0));
        // Every day for four hundred years follows the one before.
        let (mut last, mut seen) = ((1969u64, 12u64, 31u64), 0u64);
        for day in 0..146_097u64 {
            let d = Moment::of(day * 86_400_000);
            let leap = d.year.is_multiple_of(4) && (!d.year.is_multiple_of(100) || d.year.is_multiple_of(400));
            let days_in = [31, 28 + leap as u64, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][d.month as usize - 1];
            assert!(d.day >= 1 && d.day <= days_in, "{d:?}");
            let next = match (d.day, d.month) {
                (1, 1) => (d.year - 1, 12, 31) == last,
                (1, _) => (d.year, d.month - 1) == (last.0, last.1),
                _ => (d.year, d.month, d.day - 1) == last,
            };
            assert!(next, "{last:?} then {d:?}");
            last = (d.year, d.month, d.day);
            seen += 1;
        }
        assert_eq!((seen, last), (146_097, (2369, 12, 31)));
    }

    #[test]
    fn the_header_and_the_name_put_aside_are_as_laid_down() {
        assert_eq!(Moment::of(T).header(), "[2026-10-17 19:49:31:471]");
        assert_eq!(Moment::of(5).header(), "[1970-01-01 00:00:00:005]");
        // Month, day, year, hour, minute.
        assert_eq!(Moment::of(T).rotated(), "_R_10_17_2026_19_49");
        assert_eq!(Moment::of(1_770_112_800_000).rotated(), "_R_02_03_2026_10_00");
        // Month, day, year, hour, minute, second.
        assert_eq!(Moment::of(1_770_114_604_000).begun(), "_02_03_2026_10_30_04");
        assert_eq!(Moment::of(T).begun(), "_10_17_2026_19_49_31");
        assert_eq!(Moment::of(1_770_076_802_000).started(), "02-03-2026 00:00:02 UTC");
    }

    #[test]
    fn lines_are_written_with_the_time_or_as_they_are() {
        let dir = Dir::new("lines");
        let (now, clock) = clock(T);
        let log = Logger::with_clock(dir.0.join("tabernacle.log"), Rotation::default(), clock).unwrap();
        log.log("started");
        now.store(T + 1529, Ordering::Relaxed);
        log.log_no_header("peers 14 blocks 3");
        log.log("a line\nof two lines");
        log.log_all("to the terminal as well");
        log.log("");
        assert_eq!(
            dir.read("tabernacle.log"),
            "[2026-10-17 19:49:31:471] started\n\
             peers 14 blocks 3\n\
             [2026-10-17 19:49:33:000] a line\nof two lines\n\
             [2026-10-17 19:49:33:000] to the terminal as well\n\
             [2026-10-17 19:49:33:000] \n"
        );
        assert_eq!((log.failures(), dir.files()), (0, vec!["tabernacle.log".to_string()]));
        // Opened again, it is added to. (The file being written to has
        // nothing in it but the log's lines.)
        drop(log);
        let log = Logger::open(dir.0.join("tabernacle.log"), Rotation::default()).unwrap();
        log.log_no_header("again");
        let text = dir.read("tabernacle.log");
        assert!(text.ends_with("[2026-10-17 19:49:33:000] \nagain\n"));
        assert_eq!(text.matches("tabernacle.log_").count(), 0);
    }

    #[test]
    fn a_file_grown_too_large_is_put_aside() {
        let dir = Dir::new("size");
        let (now, clock) = clock(T);
        let rotation = Rotation { max_age: 0, max_size: 100 };
        let log = Logger::with_clock(dir.0.join("node.log"), rotation, clock).unwrap();
        // Of lines of thirty bytes, three fit in a hundred and a fourth
        // does not.
        let first = "node.log_10_17_2026_19_49_31\n";
        let line = |n: u32| format!("{n:029}");
        let lines = |from: u32, to: u32| (from..to).map(|n| line(n) + "\n").collect::<String>();
        for n in 0..5 {
            log.log_no_header(&line(n));
        }
        assert_eq!(dir.files(), ["node.log", "node_R_10_17_2026_19_49.log"]);
        // No line is lost, none is split, and they are in order: what
        // was put aside, then the file itself. The file put aside says
        // in its first line which log it is and when it was begun; the
        // file being written to is the log's lines and nothing else.
        assert_eq!(dir.read("node_R_10_17_2026_19_49.log"), format!("{first}{}", lines(0, 3)));
        assert_eq!(dir.read("node.log"), lines(3, 5));
        // A second in the same minute, and a tenth, are counted with two
        // digits as every other number in the name is.
        for n in 5..32 {
            log.log_no_header(&line(n));
        }
        assert_eq!(dir.read("node_R_10_17_2026_19_49_02.log"), format!("{first}{}", lines(3, 6)));
        assert!(dir.files().contains(&"node_R_10_17_2026_19_49_10.log".to_string()));
        // Another minute, another name: and the file begun then says
        // so, when it is put aside in its turn.
        now.store(T + 60_000, Ordering::Relaxed);
        log.log_no_header(&line(32));
        log.log_no_header(&line(33));
        assert_eq!(dir.read("node_R_10_17_2026_19_50.log"), format!("{first}{}", lines(30, 33)));
        // A line longer than any file may be is written all the same, to
        // a file of its own.
        let long = "x".repeat(300);
        log.log_no_header(&long);
        assert_eq!(dir.read("node.log"), format!("{long}\n"));
        assert_eq!(
            dir.read("node_R_10_17_2026_19_50_02.log"),
            format!("node.log_10_17_2026_19_50_31\n{}", lines(33, 34))
        );
        log.log_no_header("after");
        assert_eq!(dir.read("node.log"), "after\n");
        assert_eq!(dir.read("node_R_10_17_2026_19_50_03.log"), format!("node.log_10_17_2026_19_50_31\n{long}\n"));
        assert_eq!(log.failures(), 0);
    }

    #[test]
    fn a_file_written_to_for_too_long_is_put_aside() {
        let dir = Dir::new("age");
        let (now, clock) = clock(T);
        let rotation = Rotation { max_age: 3600, max_size: 0 };
        let log = Logger::with_clock(dir.0.join("stats.log"), rotation, clock).unwrap();
        log.log("first");
        now.store(T + 3_599_999, Ordering::Relaxed);
        log.log("within the hour");
        assert_eq!(dir.files(), ["stats.log"]);
        // The hour is up: the next line begins a new file.
        now.store(T + 3_600_000, Ordering::Relaxed);
        log.log("the next hour");
        assert_eq!(dir.files(), ["stats.log", "stats_R_10_17_2026_20_49.log"]);
        let aside = dir.read("stats_R_10_17_2026_20_49.log");
        assert!(aside.starts_with("stats.log_10_17_2026_19_49_31\n[") && aside.ends_with("within the hour\n"));
        assert_eq!(dir.read("stats.log"), "[2026-10-17 20:49:31:471] the next hour\n");
        // A quiet log is put aside when it is looked to, though nothing
        // is written; one with nothing in it is not.
        now.store(T + 2 * 3_600_000, Ordering::Relaxed);
        log.rotate_if_due();
        assert_eq!(dir.files().len(), 3);
        assert_eq!(dir.read("stats.log"), "");
        now.store(T + 9 * 3_600_000, Ordering::Relaxed);
        log.rotate_if_due();
        log.log("after a long quiet");
        assert_eq!(dir.files().len(), 3, "a file of nothing was not worth keeping");
        assert!(dir.read("stats.log").starts_with("[2026-10-18 04:49:31:471] after"));
        // And when asked to, whatever its age.
        assert!(log.rotate().is_some_and(|p| p.ends_with("stats_R_10_18_2026_04_49.log")));
        assert_eq!(log.rotate(), None);
    }

    /// The main log is told of every file another log puts aside.
    #[test]
    fn the_main_log_says_where_the_others_went() {
        let dir = Dir::new("main");
        let (now, main_clock) = clock(T);
        let read = Arc::clone(&now);
        let main = Arc::new(Logger::with_clock(dir.0.join("main.log"), Rotation::default(), main_clock).unwrap());
        let rotation = Rotation { max_age: 0, max_size: 60 };
        let requests =
            Logger::with_clock(dir.0.join("request.log"), rotation, Box::new(move || read.load(Ordering::Relaxed)))
                .unwrap()
                .report_rotations_to(Arc::clone(&main));
        for n in 0..5 {
            requests.log_no_header(&format!("request {n:020}"));
            now.fetch_add(1000, Ordering::Relaxed);
        }
        assert_eq!(
            dir.read("main.log"),
            "[2026-10-17 19:49:33:471] request.log rotated to request_R_10_17_2026_19_49.log\n\
             [2026-10-17 19:49:35:471] request.log rotated to request_R_10_17_2026_19_49_02.log\n"
        );
        // Its own files are put aside without a word.
        let aside = main.rotate().unwrap();
        assert_eq!(dir.read("main.log"), "");
        assert!(std::fs::read_to_string(aside).unwrap().starts_with("main.log_10_17_2026_19_49_31\n["));
    }

    /// A run that stopped while a file was being put aside left its
    /// lines under the name they were held by: the next run gives them
    /// the name they were to have, and that name is not avoided for
    /// ever. Another log's are left alone.
    #[test]
    fn what_was_left_half_put_aside_is_finished() {
        let dir = Dir::new("left");
        let write = |name: &str, lines: &str| std::fs::write(dir.0.join(name), lines).unwrap();
        write("request.log", "three\n");
        write("request_R_10_17_2026_19_49.log", "request.log_10_17");
        write("request_R_10_17_2026_19_49.log.moving", "one\ntwo\n");
        write("stat_R_10_17_2026_19_49.log.moving", "theirs\n");
        let (_, clock) = clock(T);
        let log = Logger::with_clock(dir.0.join("request.log"), Rotation::default(), clock).unwrap();
        let theirs = "stat_R_10_17_2026_19_49.log.moving";
        assert_eq!(dir.files(), ["request.log", "request_R_10_17_2026_19_49.log", theirs]);
        assert_eq!(dir.read("request_R_10_17_2026_19_49.log"), "one\ntwo\n");
        // (And what is put aside in the same minute has the next name.)
        assert!(log.rotate().is_some());
        assert_eq!(dir.read("request_R_10_17_2026_19_49_02.log"), "request.log_10_17_2026_19_49_31\nthree\n");
    }

    #[test]
    fn a_name_without_an_ending_is_put_aside_without_one() {
        let dir = Dir::new("plain");
        let (_, clock) = clock(T);
        let log = Logger::with_clock(dir.0.join("requests"), Rotation::default(), clock).unwrap();
        log.log_no_header("one");
        assert!(log.rotate().is_some());
        assert_eq!(dir.files(), ["requests", "requests_R_10_17_2026_19_49"]);
        assert_eq!(dir.read("requests_R_10_17_2026_19_49"), "requests_10_17_2026_19_49_31\none\n");
    }

    #[test]
    fn lines_from_many_threads_are_whole() {
        let dir = Dir::new("threads");
        let rotation = Rotation { max_age: 0, max_size: 20_000 };
        let log = Arc::new(Logger::open(dir.0.join("busy.log"), rotation).unwrap());
        let threads: Vec<_> = (0..8u32)
            .map(|t| {
                let log = Arc::clone(&log);
                std::thread::spawn(move || {
                    for n in 0..500u32 {
                        log.log(&format!("thread {t} line {n:04} {}", "=".repeat(20)));
                    }
                })
            })
            .collect();
        threads.into_iter().for_each(|t| t.join().unwrap());
        // Four thousand lines over many files, each whole, each thread's
        // in the order it wrote them.
        let files = dir.files();
        assert!(files.len() > 10);
        let mut seen = vec![Vec::new(); 8];
        let mut paths: Vec<PathBuf> = files.iter().map(|f| dir.0.join(f)).collect();
        paths.sort_by_key(|p| std::fs::metadata(p).unwrap().modified().unwrap());
        let mut lines = 0;
        for path in &paths {
            let text = std::fs::read_to_string(path).unwrap();
            // A file put aside has its first line, over and above what a
            // file may hold; the one being written to has none.
            let aside = text.starts_with("busy.log_");
            assert_eq!(aside, *path != dir.0.join("busy.log"));
            let first = if aside { text.find('\n').unwrap() + 1 } else { 0 };
            assert!(text.len() - first <= 20_000 && (text.is_empty() || text.ends_with('\n')));
            for line in text[first..].lines() {
                assert!(line.starts_with('[') && line.ends_with(&"=".repeat(20)), "{line}");
                let words: Vec<&str> = line.split(' ').collect();
                seen[words[3].parse::<usize>().unwrap()].push(words[5].parse::<u32>().unwrap());
                lines += 1;
            }
        }
        assert_eq!(lines, 4000);
        for mine in &mut seen {
            mine.sort();
            assert_eq!(*mine, (0..500).collect::<Vec<u32>>());
        }
        assert_eq!(log.failures(), 0);
    }

    #[test]
    fn a_log_that_cannot_be_written_does_not_stop_anything() {
        let dir = Dir::new("gone");
        assert!(Logger::open(dir.0.join("no-such-directory").join("x.log"), Rotation::default()).is_err());
        let (now, clock) = clock(T);
        let rotation = Rotation { max_age: 60, max_size: 0 };
        let log = Logger::with_clock(dir.0.join("node.log"), rotation, clock).unwrap();
        log.log("one");
        // Its directory goes: the file cannot be put aside, nor a new
        // one begun.
        std::fs::remove_dir_all(&dir.0).unwrap();
        now.store(T + 61_000, Ordering::Relaxed);
        log.log("two");
        log.log_all("three");
        log.rotate_if_due();
        assert!(log.failures() >= 1);
        // It comes back: so does the log.
        std::fs::create_dir_all(&dir.0).unwrap();
        log.log("four");
        assert!(dir.read("node.log").ends_with("four\n"));
    }
}
