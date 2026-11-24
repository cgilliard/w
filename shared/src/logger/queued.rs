//! A log written by a thread of its own, from a queue.
//!
//! Whoever says a line does not wait for the disk: the line is put on a
//! queue, with the time it was said, and a thread that does nothing
//! else writes it. The time before a line is when it was said, not
//! when it was written.
//!
//! The queue holds so many lines and no more. When it is full a line is
//! dropped, not waited for: a node that is being asked more than its
//! disk can note down should go on answering. That it happened is said
//! in the main log there and then, by whoever's line was dropped, and
//! not again for [`TOLD_EVERY`] while it goes on:
//!
//! ```text
//! [2026-10-17 19:49:31:471] dropped request log queued items
//! ```
//!
//! As a rule the queue empties as fast as the disk takes its lines, and
//! the log goes on from there with nothing more said.
//!
//! The thread also puts the file aside when it is due though nothing is
//! being said ([`super::Logger::rotate_if_due`]).

use std::io;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender, TrySendError, sync_channel};
use std::thread::JoinHandle;
use std::time::Duration;

use super::{Logger, Moment};

enum Said {
    /// A line whole, with its end, and when it was said.
    Line(u64, String),
    /// Answered when everything said before it has been written.
    Flush(SyncSender<()>),
    /// Tests: says it has got this far, and waits there until told to
    /// go on.
    #[cfg(test)]
    Hold(SyncSender<()>, Receiver<()>),
}

/// How often the thread looks to the file's age, when nothing is said.
const LOOK: Duration = Duration::from_secs(1);
/// How long after the main log was told of lines dropped before it is
/// told again, in milliseconds.
pub const TOLD_EVERY: u64 = 5_000;

/// A log written from a queue.
pub struct Queued {
    said: Option<SyncSender<Said>>,
    logger: Arc<Logger>,
    capacity: usize,
    dropped: AtomicU64,
    /// The main log, what is said in it of lines dropped, and when it
    /// was last said (and one, so that nothing is never).
    main: Arc<Logger>,
    saying: String,
    told_at: AtomicU64,
    thread: Option<JoinHandle<()>>,
}

impl Queued {
    /// Starts the thread that writes `logger`, from a queue of
    /// `capacity` lines. That lines were dropped is said in `main`.
    pub fn start(logger: Logger, capacity: usize, main: Arc<Logger>) -> io::Result<Queued> {
        let capacity = capacity.max(1);
        let (said, queue) = sync_channel::<Said>(capacity);
        let logger = Arc::new(logger);
        let name = logger.path().file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        // "request.log" is the request log.
        let stem = logger.path().file_stem().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let thread = {
            let logger = Arc::clone(&logger);
            std::thread::Builder::new().name(format!("log {name}")).spawn(move || write_from(queue, &logger))?
        };
        Ok(Queued {
            said: Some(said),
            logger,
            capacity,
            dropped: AtomicU64::new(0),
            main,
            saying: format!("dropped {stem} log queued items"),
            told_at: AtomicU64::new(0),
            thread: Some(thread),
        })
    }

    /// Says `line`, with the time now before it.
    pub fn log(&self, line: &str) {
        let now = self.logger.now();
        self.say(now, format!("{} {line}\n", Moment::of(now).header()));
    }

    /// Says `line` as it is.
    pub fn log_no_header(&self, line: &str) {
        self.say(self.logger.now(), format!("{line}\n"));
    }

    fn say(&self, now: u64, text: String) {
        let Some(said) = &self.said else { return };
        match said.try_send(Said::Line(now, text)) {
            Ok(()) => {}
            // Full, or the thread is gone: the line is lost. Said in
            // the main log, by whoever is first to find it so in a
            // while.
            Err(TrySendError::Full(_) | TrySendError::Disconnected(_)) => {
                self.dropped.fetch_add(1, Ordering::Relaxed);
                let told = self.told_at.load(Ordering::Relaxed);
                if (told == 0 || now.saturating_sub(told - 1) >= TOLD_EVERY)
                    && self.told_at.compare_exchange(told, now + 1, Ordering::Relaxed, Ordering::Relaxed).is_ok()
                {
                    self.main.log(&self.saying);
                }
            }
        }
    }

    /// Lines dropped because the queue was full: for the stats.
    pub fn dropped(&self) -> u64 {
        self.dropped.load(Ordering::Relaxed)
    }

    /// How many lines the queue holds.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// The log being written.
    pub fn logger(&self) -> &Logger {
        &self.logger
    }

    /// Waits until everything said so far has been written.
    pub fn flush(&self) {
        let (done, wait) = sync_channel(1);
        if let Some(said) = &self.said
            && said.send(Said::Flush(done)).is_ok()
        {
            let _ = wait.recv();
        }
    }
}

impl Drop for Queued {
    /// What is in the queue is written before the thread ends.
    fn drop(&mut self) {
        self.said = None;
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn write_from(queue: Receiver<Said>, logger: &Logger) {
    loop {
        match queue.recv_timeout(LOOK) {
            Ok(Said::Line(now, text)) => logger.write_at(now, &text),
            Ok(Said::Flush(done)) => {
                let _ = done.send(());
            }
            #[cfg(test)]
            Ok(Said::Hold(here, go)) => {
                let _ = here.send(());
                let _ = go.recv();
            }
            Err(RecvTimeoutError::Timeout) => logger.rotate_if_due(),
            Err(RecvTimeoutError::Disconnected) => return,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logger::Rotation;
    use std::path::PathBuf;

    fn dir(name: &str) -> PathBuf {
        static COUNT: AtomicU64 = AtomicU64::new(0);
        let unique = format!("tabminer-queued-{name}-{}-{}", std::process::id(), COUNT.fetch_add(1, Ordering::Relaxed));
        let path = std::env::temp_dir().join(unique);
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        path
    }

    fn lines(path: &std::path::Path) -> Vec<String> {
        std::fs::read_to_string(path).unwrap().lines().map(String::from).collect()
    }

    #[test]
    fn what_is_said_is_written_in_order_by_another_thread() {
        let dir = dir("order");
        let main = Arc::new(Logger::open(dir.join("main.log"), Rotation::default()).unwrap());
        let log = Queued::start(
            Logger::open(dir.join("request.log"), Rotation::default()).unwrap(),
            10_000,
            Arc::clone(&main),
        )
        .unwrap();
        let me = std::thread::current().id();
        for n in 0..5000 {
            match n % 2 {
                0 => log.log(&format!("request {n}")),
                _ => log.log_no_header(&format!("request {n}")),
            }
        }
        log.flush();
        let written = lines(&dir.join("request.log"));
        assert_eq!(written.len(), 5000);
        for (n, line) in written.iter().enumerate() {
            assert!(line.ends_with(&format!("request {n}")), "{line}");
            assert_eq!(line.starts_with('['), n % 2 == 0, "{line}");
        }
        assert_eq!((log.dropped(), log.capacity()), (0, 10_000));
        // Written by a thread of its own, named for its log; and the
        // rest of what was said is written before that thread ends.
        assert!(log.thread.as_ref().unwrap().thread().id() != me);
        assert_eq!(log.thread.as_ref().unwrap().thread().name(), Some("log request.log"));
        log.log("the last");
        drop(log);
        assert_eq!(lines(&dir.join("request.log")).len(), 5001);
        assert_eq!(lines(&dir.join("main.log")), [] as [String; 0]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A queue that is full drops what it cannot hold, never makes its
    /// caller wait, and the main log says so.
    #[test]
    fn a_full_queue_drops_lines_and_the_main_log_says_so() {
        let dir = dir("full");
        let main = Arc::new(Logger::open(dir.join("main.log"), Rotation::default()).unwrap());
        let log =
            Queued::start(Logger::open(dir.join("request.log"), Rotation::default()).unwrap(), 8, Arc::clone(&main))
                .unwrap();
        // The writer is held up, as by a slow disk, with the queue empty.
        let ((here, there), (go, held)) = (sync_channel(1), sync_channel(0));
        log.said.as_ref().unwrap().send(Said::Hold(here, held)).unwrap();
        there.recv().unwrap();
        let start = std::time::Instant::now();
        for n in 0..1000 {
            log.log_no_header(&format!("line {n}"));
        }
        assert!(start.elapsed() < Duration::from_secs(2), "nobody waited for the disk");
        assert_eq!(log.dropped(), 992);
        go.send(()).unwrap();
        log.flush();
        // The first eight are there; the rest were never written.
        assert_eq!(lines(&dir.join("request.log")), (0..8).map(|n| format!("line {n}")).collect::<Vec<_>>());
        // Said once, not nine hundred times, and at the time.
        let said = lines(&dir.join("main.log"));
        assert_eq!(said.len(), 1, "{said:?}");
        assert!(said[0].starts_with('[') && said[0].ends_with("] dropped request log queued items"), "{}", said[0]);
        // After it, lines are taken again, with nothing more said.
        log.log_no_header("after");
        log.flush();
        assert_eq!(lines(&dir.join("request.log")).last().unwrap(), "after");
        assert_eq!(lines(&dir.join("main.log")).len(), 1);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The files it puts aside are told of in the main log.
    #[test]
    fn a_queued_log_is_put_aside_like_any_other() {
        let dir = dir("rotate");
        let main = Arc::new(Logger::open(dir.join("main.log"), Rotation::default()).unwrap());
        let rotation = Rotation { max_age: 0, max_size: 200 };
        let logger = Logger::open(dir.join("request.log"), rotation).unwrap().report_rotations_to(Arc::clone(&main));
        let log = Queued::start(logger, 1000, Arc::clone(&main)).unwrap();
        for n in 0..30 {
            log.log_no_header(&format!("a request of some length, number {n:04}"));
        }
        log.flush();
        let told = lines(&dir.join("main.log"));
        assert!(told.len() >= 4, "{told:?}");
        assert!(told.iter().all(|l| l.contains("request.log rotated to request_R_")));
        let files = std::fs::read_dir(&dir).unwrap().count();
        assert_eq!(files, told.len() + 2);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
