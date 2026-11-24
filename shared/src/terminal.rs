//! The line typed at the prompt: edited here, a key at a time.
//!
//! A terminal left to itself gives a program whole lines, and does the
//! editing of them: which is a backspace and no more. To bring back
//! what was typed before with the up arrow, and to finish a word with
//! tab, the program takes the keys as they are struck, with the
//! terminal's own echo and editing off, and draws the line itself.
//!
//! There are three parts:
//!
//! - [`Line`]: the line being typed, and what each key does to it.
//!   Nothing of a terminal is in it: it is tried by the tests.
//! - What a [`Line`] looks like on a terminal of so many columns
//!   ([`Line::draw`]): text and the few sequences that move the
//!   cursor and clear to the end of a line.
//! - The terminal itself ([`Prompt`]): its settings changed for as
//!   long as a line is being read and put back after, by the system's
//!   own calls (there is no library here). On Linux and macOS; on any
//!   other system, and where what is read from is no terminal (a file,
//!   a pipe, a test), lines are read whole as before. (A Windows
//!   console recalls and edits lines itself.)
//!
//! What other threads say while a line is being typed ([`say`]) is
//! written above it, and the line drawn again under it.

use std::io::{self, Read, Write};
use std::sync::Mutex;

/// A key, as the line takes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Key {
    Char(char),
    Enter,
    /// Backspace, which is also what ctrl-h sends.
    Backspace,
    Delete,
    Left,
    Right,
    Home,
    End,
    Up,
    Down,
    Tab,
    /// Ctrl-d: the end of what there is to read, on an empty line; a
    /// delete, on any other.
    EndOfInput,
    /// Ctrl-k and ctrl-u: to the end of the line, and all of it.
    KillToEnd,
    KillLine,
    /// Ctrl-w: the word before the cursor.
    KillWord,
    /// Ctrl-l.
    Clear,
}

/// What came of a key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Came {
    /// The line is other than it was, or the cursor is elsewhere.
    Changed,
    Nothing,
    /// The line is done: this is it.
    Line(String),
    /// There is no more to read.
    End,
    /// These are to be listed under the line: what tab could mean.
    List(Vec<String>),
    /// The screen is to be cleared.
    Clear,
}

/// What a word begun could be, for tab: given the line up to the
/// cursor, where the word begins in it (in characters) and what it
/// could be finished as, each whole.
pub type Completer = Box<dyn Fn(&str) -> (usize, Vec<String>) + Send>;

/// The line being typed.
pub struct Line {
    text: Vec<char>,
    /// The cursor: before the character of this index.
    at: usize,
    /// What was typed before, the oldest first.
    history: Vec<String>,
    /// Which of them is shown (as many as there are: none, the line
    /// being typed), and the line that was being typed when the first
    /// was brought back.
    shown: usize,
    typing: Vec<char>,
    /// Whether the key before this was a tab that changed nothing.
    tabbed: bool,
    complete: Completer,
}

/// Lines remembered, at the most.
const REMEMBERED: usize = 1000;

impl Line {
    pub fn new(complete: Completer) -> Line {
        Line { text: Vec::new(), at: 0, history: Vec::new(), shown: 0, typing: Vec::new(), tabbed: false, complete }
    }

    pub fn text(&self) -> String {
        self.text.iter().collect()
    }

    /// The cursor's place, in characters.
    pub fn cursor(&self) -> usize {
        self.at
    }

    /// A line that was typed is remembered: but not an empty one, nor
    /// the same as the last twice.
    pub fn remember(&mut self, line: &str) {
        if !line.trim().is_empty() && self.history.last().map(String::as_str) != Some(line) {
            self.history.push(line.to_string());
            if self.history.len() > REMEMBERED {
                self.history.remove(0);
            }
        }
    }

    fn set(&mut self, text: Vec<char>) {
        self.at = text.len();
        self.text = text;
    }

    /// Takes a key.
    pub fn key(&mut self, key: Key) -> Came {
        let tabbed = std::mem::take(&mut self.tabbed);
        match key {
            Key::Char(c) => {
                self.text.insert(self.at, c);
                self.at += 1;
            }
            Key::Enter => {
                let line = self.text();
                self.remember(&line);
                (self.text, self.at, self.shown, self.typing) = (Vec::new(), 0, self.history.len(), Vec::new());
                return Came::Line(line);
            }
            Key::EndOfInput if self.text.is_empty() => return Came::End,
            Key::EndOfInput | Key::Delete if self.at < self.text.len() => drop(self.text.remove(self.at)),
            Key::Backspace if self.at > 0 => {
                self.at -= 1;
                self.text.remove(self.at);
            }
            Key::Left if self.at > 0 => self.at -= 1,
            Key::Right if self.at < self.text.len() => self.at += 1,
            Key::Home if self.at > 0 => self.at = 0,
            Key::End if self.at < self.text.len() => self.at = self.text.len(),
            // What was typed before: back through it, and forward
            // again to the line that was being typed.
            Key::Up if self.shown.min(self.history.len()) > 0 => {
                self.shown = self.shown.min(self.history.len());
                if self.shown == self.history.len() {
                    self.typing = self.text.clone();
                }
                self.shown -= 1;
                let line = self.history[self.shown].chars().collect();
                self.set(line);
            }
            Key::Down if self.shown < self.history.len() => {
                self.shown += 1;
                let line = match self.history.get(self.shown) {
                    Some(line) => line.chars().collect(),
                    None => std::mem::take(&mut self.typing),
                };
                self.set(line);
            }
            Key::KillToEnd if self.at < self.text.len() => self.text.truncate(self.at),
            Key::KillLine if !self.text.is_empty() => self.set(Vec::new()),
            Key::KillWord if self.at > 0 => {
                let mut from = self.at;
                while from > 0 && self.text[from - 1] == ' ' {
                    from -= 1;
                }
                while from > 0 && self.text[from - 1] != ' ' {
                    from -= 1;
                }
                self.text.drain(from..self.at);
                self.at = from;
            }
            Key::Clear => return Came::Clear,
            Key::Tab => return self.tab(tabbed),
            _ => return Came::Nothing,
        }
        // (A line that has been changed is the one being typed: the
        // arrows go from the newest again.)
        if !matches!(key, Key::Up | Key::Down | Key::Left | Key::Right | Key::Home | Key::End) {
            self.shown = self.history.len();
        }
        Came::Changed
    }

    /// Tab, as a shell has it: where one thing fits, the word is
    /// finished, with a space after it; where several do, as much as
    /// they have in common is filled in; and where that is nothing
    /// more, a second tab lists them.
    fn tab(&mut self, again: bool) -> Came {
        let before: String = self.text[..self.at].iter().collect();
        let (from, mut could) = (self.complete)(&before);
        could.sort();
        could.dedup();
        let from = from.min(self.at);
        let begun = self.at - from;
        let fill = |line: &mut Line, with: &str| {
            let with: Vec<char> = with.chars().collect();
            line.text.splice(from..line.at, with.iter().copied());
            line.at = from + with.len();
        };
        match &could[..] {
            [] => Came::Nothing,
            [one] => {
                // (A directory is gone on into, not ended.)
                let done = if one.ends_with('/') { one.clone() } else { format!("{one} ") };
                fill(self, &done);
                self.shown = self.history.len();
                Came::Changed
            }
            several => {
                let first: Vec<char> = several[0].chars().collect();
                let common = several.iter().fold(first.len(), |n, other| {
                    first.iter().zip(other.chars()).take(n).take_while(|(a, b)| **a == *b).count()
                });
                if common > begun {
                    let with: String = first[..common].iter().collect();
                    fill(self, &with);
                    self.shown = self.history.len();
                    return Came::Changed;
                }
                self.tabbed = true;
                match again {
                    true => Came::List(several.to_vec()),
                    false => Came::Nothing,
                }
            }
        }
    }

    /// What is written to draw the line, after `prompt`, on a terminal
    /// `cols` wide, where the line as last drawn had its cursor on row
    /// `row` of `rows` (none, if nothing of it is drawn): and the row
    /// the cursor is on and the rows there are, from here on.
    pub fn draw(&self, prompt: &str, cols: usize, was: (usize, usize)) -> (String, (usize, usize)) {
        let cols = cols.max(8);
        let plen = prompt.chars().count();
        let len = plen + self.text.len();
        let mut out = String::new();
        // To the last row of what was drawn, and up through it,
        // clearing each row.
        let (was_row, was_rows) = was;
        if was_rows > was_row {
            out.push_str(&format!("\x1b[{}B", was_rows - was_row));
        }
        for _ in 1..was_rows.max(1) {
            out.push_str("\r\x1b[0K\x1b[1A");
        }
        out.push_str("\r\x1b[0K");
        out.push_str(prompt);
        out.extend(self.text.iter());
        // (A cursor after the last column of a row is on the next,
        // which is not there until something is written to it.)
        let mut rows = len.div_ceil(cols).max(1);
        if self.at == self.text.len() && len > 0 && len.is_multiple_of(cols) {
            out.push_str("\n\r");
            rows += 1;
        }
        // The cursor to where it is.
        let place = plen + self.at;
        let row = place / cols + 1;
        if rows > row {
            out.push_str(&format!("\x1b[{}A", rows - row));
        }
        match place % cols {
            0 => out.push('\r'),
            col => out.push_str(&format!("\r\x1b[{col}C")),
        }
        (out, (row, rows))
    }
}

/// The keys in what was read, with what is left over: the beginning
/// of a key whose end has not come yet.
pub fn keys(bytes: &[u8]) -> (Vec<Key>, usize) {
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let (key, used) = match bytes[i] {
            b'\r' | b'\n' => (Some(Key::Enter), 1),
            0x7f | 0x08 => (Some(Key::Backspace), 1),
            b'\t' => (Some(Key::Tab), 1),
            0x01 => (Some(Key::Home), 1),
            0x02 => (Some(Key::Left), 1),
            0x04 => (Some(Key::EndOfInput), 1),
            0x05 => (Some(Key::End), 1),
            0x06 => (Some(Key::Right), 1),
            0x0b => (Some(Key::KillToEnd), 1),
            0x0c => (Some(Key::Clear), 1),
            0x0e => (Some(Key::Down), 1),
            0x10 => (Some(Key::Up), 1),
            0x15 => (Some(Key::KillLine), 1),
            0x17 => (Some(Key::KillWord), 1),
            0x1b => match bytes.get(i + 1) {
                None => break,
                Some(b'[' | b'O') => {
                    // Its numbers, and the letter (or `~`) that ends it.
                    let rest = &bytes[i + 2..];
                    let Some(end) = rest.iter().position(|b| (0x40..=0x7e).contains(b)) else { break };
                    let key = match (&rest[..end], rest[end]) {
                        (_, b'A') => Some(Key::Up),
                        (_, b'B') => Some(Key::Down),
                        (_, b'C') => Some(Key::Right),
                        (_, b'D') => Some(Key::Left),
                        (_, b'H') => Some(Key::Home),
                        (_, b'F') => Some(Key::End),
                        (b"1" | b"7", b'~') => Some(Key::Home),
                        (b"4" | b"8", b'~') => Some(Key::End),
                        (b"3", b'~') => Some(Key::Delete),
                        _ => None,
                    };
                    (key, 3 + end)
                }
                // (Escape and another key: nothing here.)
                Some(_) => (None, 2),
            },
            // Any other control: nothing.
            0..0x20 => (None, 1),
            // A character: as many bytes as its first says.
            first => {
                let n = match first {
                    0..0x80 => 1,
                    0xc0..0xe0 => 2,
                    0xe0..0xf0 => 3,
                    0xf0..0xf8 => 4,
                    _ => 1,
                };
                if i + n > bytes.len() {
                    break;
                }
                let c = std::str::from_utf8(&bytes[i..i + n]).ok().and_then(|s| s.chars().next());
                (c.map(Key::Char), n)
            }
        };
        out.extend(key);
        i += used;
    }
    (out, i)
}

/// What the terminal shows of a line being typed, for whoever writes
/// above it ([`say`]): the prompt, the line, and how it was last drawn.
struct Shown {
    prompt: String,
    line: Line,
    drawn: (usize, usize),
}

static SHOWN: Mutex<Option<Shown>> = Mutex::new(None);

fn shown() -> std::sync::MutexGuard<'static, Option<Shown>> {
    SHOWN.lock().unwrap_or_else(|e| e.into_inner())
}

/// Writes `line` for whoever is at the terminal: above the line being
/// typed, if one is, which is then drawn again under it. False if no
/// line is being typed here: the caller writes it as it would.
pub fn say(line: &str) -> bool {
    let mut shown = shown();
    let Some(s) = shown.as_mut() else { return false };
    let mut out = io::stdout().lock();
    // (The line as it is drawn is cleared by drawing an empty one.)
    let empty = Line::new(Box::new(|_| (0, Vec::new())));
    let (clear, _) = empty.draw("", sys::columns(), s.drawn);
    let (draw, drawn) = s.line.draw(&s.prompt, sys::columns(), (0, 0));
    let _ = write!(out, "{clear}{line}\n{draw}");
    let _ = out.flush();
    s.drawn = drawn;
    true
}

/// The prompt: lines read from the terminal, edited as they are typed
/// where that can be done, and whole where it cannot.
pub struct Prompt {
    /// The line that goes on from one reading to the next (what was
    /// typed before is in it), while none is being read.
    line: Option<Line>,
    /// Whether keys are taken one at a time.
    edited: bool,
    /// What was read and is not yet a key.
    pending: Vec<u8>,
}

impl Prompt {
    /// A prompt that finishes words with `complete`. Lines are edited
    /// here if both what is read from and what is written to are a
    /// terminal, on a system whose terminals this knows how to set.
    pub fn new(complete: Completer) -> Prompt {
        use std::io::IsTerminal;
        let edited = sys::CAN && io::stdin().is_terminal() && io::stdout().is_terminal();
        Prompt { line: Some(Line::new(complete)), edited, pending: Vec::new() }
    }

    /// Whether lines are edited here (and what other threads say is to
    /// go by [`say`]).
    pub fn edited(&self) -> bool {
        self.edited
    }

    /// Reads a line, after `prompt`: `None` when there is no more to
    /// read.
    pub fn read(&mut self, prompt: &str) -> io::Result<Option<String>> {
        if !self.edited {
            print!("{prompt}");
            io::stdout().flush()?;
            let mut line = String::new();
            return Ok(match io::stdin().read_line(&mut line)? {
                0 => None,
                _ => Some(line.trim_end_matches(['\n', '\r']).to_string()),
            });
        }
        let _raw = sys::Raw::enter(false)?;
        let line = self.line.take().expect("no line is being read");
        let (draw, drawn) = line.draw(prompt, sys::columns(), (0, 0));
        *shown() = Some(Shown { prompt: prompt.to_string(), line, drawn });
        print!("{draw}");
        io::stdout().flush()?;
        let came = self.keys();
        // (Whatever came of it, the line is this prompt's again.)
        let was = shown().take().expect("the line being read");
        self.line = Some(was.line);
        came
    }

    /// Takes keys until a line is done.
    fn keys(&mut self) -> io::Result<Option<String>> {
        let mut buf = [0u8; 256];
        loop {
            let (keys, used) = keys(&self.pending);
            self.pending.drain(..used);
            for key in keys {
                let mut shown = shown();
                let s = shown.as_mut().expect("the line being read");
                let cols = sys::columns();
                let mut out = io::stdout().lock();
                match s.line.key(key) {
                    Came::Nothing => {}
                    Came::Changed => {
                        let (draw, drawn) = s.line.draw(&s.prompt, cols, s.drawn);
                        write!(out, "{draw}")?;
                        s.drawn = drawn;
                    }
                    Came::Clear => {
                        let (draw, drawn) = s.line.draw(&s.prompt, cols, (0, 0));
                        write!(out, "\x1b[H\x1b[2J{draw}")?;
                        s.drawn = drawn;
                    }
                    // What tab could mean, in columns under the line;
                    // and the line again under those.
                    Came::List(could) => {
                        let wide = could.iter().map(|c| c.chars().count()).max().unwrap_or(0) + 2;
                        let across = (cols / wide).max(1);
                        if s.drawn.1 > s.drawn.0 {
                            write!(out, "\x1b[{}B", s.drawn.1 - s.drawn.0)?;
                        }
                        writeln!(out)?;
                        for row in could.chunks(across) {
                            let row: String = row.iter().map(|c| format!("{c:<wide$}")).collect();
                            writeln!(out, "\r{}", row.trim_end())?;
                        }
                        let (draw, drawn) = s.line.draw(&s.prompt, cols, (0, 0));
                        write!(out, "{draw}")?;
                        s.drawn = drawn;
                    }
                    // Done: the cursor to under the line, and whatever
                    // comes next is written from there.
                    done @ (Came::Line(_) | Came::End) => {
                        if s.drawn.1 > s.drawn.0 {
                            write!(out, "\x1b[{}B", s.drawn.1 - s.drawn.0)?;
                        }
                        write!(out, "\r\n")?;
                        out.flush()?;
                        return Ok(match done {
                            Came::Line(line) => Some(line),
                            _ => None,
                        });
                    }
                }
                out.flush()?;
            }
            match io::stdin().lock().read(&mut buf)? {
                0 => return Ok(None),
                n => self.pending.extend_from_slice(&buf[..n]),
            }
        }
    }

    /// Reads a line that is not to be seen as it is typed, nor
    /// remembered: a password. Where lines are not edited here it is
    /// read as any line is.
    pub fn read_secret(&mut self, prompt: &str) -> io::Result<Option<String>> {
        print!("{prompt}");
        io::stdout().flush()?;
        let _raw = if self.edited { Some(sys::Raw::enter(true)?) } else { None };
        let mut line = String::new();
        let read = io::stdin().read_line(&mut line)?;
        if self.edited {
            println!();
        }
        Ok((read > 0).then(|| line.trim_end_matches(['\n', '\r']).to_string()))
    }
}

/// Asks on the terminal, before there is a prompt, for a line that is
/// not to be seen as it is typed: a password, when the program
/// starts. `asking` is said where errors are, so that what the
/// program prints is not mixed with it. Where what is typed is not a
/// terminal's (a file, another program) it is read as any line is.
/// None when there is nothing more to read.
pub fn ask_secret(asking: &str) -> io::Result<Option<String>> {
    use std::io::IsTerminal;
    eprint!("{asking}");
    io::stderr().flush()?;
    let hidden = sys::CAN && io::stdin().is_terminal();
    let raw = if hidden { Some(sys::Raw::enter(true)?) } else { None };
    let mut line = String::new();
    let read = io::stdin().read_line(&mut line)?;
    drop(raw);
    // (The end of the line was not shown either.)
    if hidden {
        eprintln!();
    }
    Ok((read > 0).then(|| line.trim_end_matches(['\n', '\r']).to_string()))
}

/// The terminal's settings, by the system's own calls.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod sys {
    use std::io;
    use std::sync::atomic::{AtomicBool, Ordering};

    pub const CAN: bool = true;

    unsafe extern "C" {
        fn tcgetattr(fd: i32, termios: *mut u8) -> i32;
        fn tcsetattr(fd: i32, when: i32, termios: *const u8) -> i32;
        fn ioctl(fd: i32, request: core::ffi::c_ulong, ...) -> i32;
        fn signal(signal: i32, handler: usize) -> usize;
        fn raise(signal: i32) -> i32;
        fn atexit(call: extern "C" fn()) -> i32;
    }

    // Where the settings that matter lie in what the system keeps of a
    // terminal, which is laid out differently on each: the flags of
    // how what is typed is treated, and the two numbers that say how
    // much is waited for before a read returns.
    #[cfg(target_os = "linux")]
    mod at {
        pub const LOCAL: usize = 12;
        pub const FLAG_BYTES: usize = 4;
        pub const ICANON: u64 = 0x2;
        pub const ECHO: u64 = 0x8;
        pub const VMIN: usize = 17 + 6;
        pub const VTIME: usize = 17 + 5;
        pub const WINSZ: core::ffi::c_ulong = 0x5413;
    }
    #[cfg(target_os = "macos")]
    mod at {
        pub const LOCAL: usize = 24;
        pub const FLAG_BYTES: usize = 8;
        pub const ICANON: u64 = 0x100;
        pub const ECHO: u64 = 0x8;
        pub const VMIN: usize = 32 + 16;
        pub const VTIME: usize = 32 + 17;
        pub const WINSZ: core::ffi::c_ulong = 0x4008_7468;
    }

    /// Room for the settings, whatever the system's layout of them:
    /// more than any has, and laid as its widest numbers want.
    #[repr(C, align(8))]
    #[derive(Clone, Copy)]
    struct Settings([u8; 256]);

    /// The settings as they were before this program changed them, to
    /// be put back whenever the program ends, however it ends.
    static mut WERE: Settings = Settings([0; 256]);
    static KEPT: AtomicBool = AtomicBool::new(false);
    static CHANGED: AtomicBool = AtomicBool::new(false);

    /// Puts the terminal back as it was. (Nothing here but what may
    /// be done when a signal comes.)
    extern "C" fn put_back() {
        if CHANGED.swap(false, Ordering::SeqCst) {
            // SAFETY: the settings were read whole from the system
            // before `CHANGED` was first set, and are not written to
            // after.
            unsafe { tcsetattr(0, 0, (&raw const WERE).cast()) };
        }
    }

    /// A signal that ends the program: the terminal is put back, and
    /// the signal then does what it does.
    extern "C" fn ended(sig: i32) {
        put_back();
        // SAFETY: both may be called when a signal comes; zero is the
        // system's own handling of it.
        unsafe {
            signal(sig, 0);
            raise(sig);
        }
    }

    /// The terminal taking keys one at a time, with nothing shown of
    /// them (or, for a password, whole lines with nothing shown), for
    /// as long as this is kept.
    pub struct Raw;

    impl Raw {
        pub fn enter(line_at_a_time: bool) -> io::Result<Raw> {
            let mut now = Settings([0; 256]);
            // SAFETY: room for more than the system writes.
            if unsafe { tcgetattr(0, now.0.as_mut_ptr()) } != 0 {
                return Err(io::Error::last_os_error());
            }
            if !KEPT.swap(true, Ordering::SeqCst) {
                // SAFETY: written once, here, before anything reads it
                // (`CHANGED` is not yet set); the handlers are the
                // system's to call.
                unsafe {
                    WERE = now;
                    atexit(put_back);
                    // (Interrupt, quit, hang-up and terminate.)
                    for sig in [2, 3, 1, 15] {
                        signal(sig, ended as extern "C" fn(i32) as usize);
                    }
                }
            }
            let mut flags = [0u8; 8];
            flags[..at::FLAG_BYTES].copy_from_slice(&now.0[at::LOCAL..at::LOCAL + at::FLAG_BYTES]);
            let off = if line_at_a_time { at::ECHO } else { at::ECHO | at::ICANON };
            let flags = (u64::from_ne_bytes(flags) & !off).to_ne_bytes();
            now.0[at::LOCAL..at::LOCAL + at::FLAG_BYTES].copy_from_slice(&flags[..at::FLAG_BYTES]);
            if !line_at_a_time {
                // (A read returns as soon as there is a byte.)
                (now.0[at::VMIN], now.0[at::VTIME]) = (1, 0);
            }
            CHANGED.store(true, Ordering::SeqCst);
            // SAFETY: the settings the system gave, changed in place.
            if unsafe { tcsetattr(0, 0, now.0.as_ptr()) } != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(Raw)
        }
    }

    impl Drop for Raw {
        fn drop(&mut self) {
            put_back();
        }
    }

    /// How wide the terminal is: eighty columns, if it does not say.
    pub fn columns() -> usize {
        let mut size = [0u16; 4];
        // SAFETY: the system writes four numbers of sixteen bits.
        let said = unsafe { ioctl(1, at::WINSZ, size.as_mut_ptr()) };
        if said == 0 && size[1] > 0 { size[1] as usize } else { 80 }
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
mod sys {
    use std::io;

    pub const CAN: bool = false;

    pub struct Raw;

    impl Raw {
        pub fn enter(_: bool) -> io::Result<Raw> {
            Ok(Raw)
        }
    }

    pub fn columns() -> usize {
        80
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line(could: &'static [&'static str]) -> Line {
        Line::new(Box::new(move |before: &str| {
            let from = before.rfind(' ').map_or(0, |at| at + 1);
            let begun = &before[from..];
            (
                before[..from].chars().count(),
                could.iter().filter(|c| c.starts_with(begun)).map(|c| c.to_string()).collect(),
            )
        }))
    }

    fn typed(line: &mut Line, text: &str) {
        for c in text.chars() {
            assert_eq!(line.key(Key::Char(c)), Came::Changed);
        }
    }

    /// What is typed is the line; it is edited where the cursor is,
    /// which the arrows and the keys of a shell move.
    #[test]
    fn a_line_is_typed_and_edited() {
        let mut l = line(&[]);
        typed(&mut l, "sned 5");
        for _ in 0..5 {
            l.key(Key::Left);
        }
        // Backspace, and ctrl-h, which is the same key; delete.
        assert_eq!((l.key(Key::Backspace), l.text(), l.cursor()), (Came::Changed, "ned 5".to_string(), 0));
        assert_eq!(l.key(Key::Backspace), Came::Nothing);
        typed(&mut l, "se");
        l.key(Key::Right);
        l.key(Key::Delete);
        assert_eq!(l.text(), "send 5");
        // (Ctrl-d on a line that is not empty deletes, as delete does.)
        l.key(Key::Left);
        assert_eq!((l.key(Key::EndOfInput), l.text()), (Came::Changed, "sed 5".to_string()));
        typed(&mut l, "n");
        assert_eq!((l.text(), l.cursor()), ("send 5".to_string(), 3));
        // To the ends, and past neither.
        assert_eq!((l.key(Key::End), l.cursor(), l.key(Key::End)), (Came::Changed, 6, Came::Nothing));
        assert_eq!((l.key(Key::Home), l.cursor(), l.key(Key::Left)), (Came::Changed, 0, Came::Nothing));
        // Killed: a word, to the end, all of it.
        l.key(Key::End);
        typed(&mut l, " tab1abc  ");
        assert_eq!((l.key(Key::KillWord), l.text()), (Came::Changed, "send 5 ".to_string()));
        l.key(Key::Home);
        l.key(Key::Right);
        assert_eq!((l.key(Key::KillToEnd), l.text()), (Came::Changed, "s".to_string()));
        assert_eq!(
            (l.key(Key::KillLine), l.text(), l.key(Key::KillLine)),
            (Came::Changed, String::new(), Came::Nothing)
        );
        // Entered: the line, and an empty one after it. No more to
        // read is said only of an empty line.
        typed(&mut l, "status");
        assert_eq!(l.key(Key::Enter), Came::Line("status".to_string()));
        assert_eq!((l.text(), l.key(Key::EndOfInput)), (String::new(), Came::End));
    }

    /// The up arrow brings back what was typed before, a line each
    /// time; the down arrow goes forward again, to the line that was
    /// being typed. The same line twice running is remembered once,
    /// and an empty one not at all.
    #[test]
    fn what_was_typed_is_brought_back() {
        let mut l = line(&[]);
        assert_eq!(l.key(Key::Up), Came::Nothing);
        for said in ["status", "", "peers", "peers", "  "] {
            typed(&mut l, said);
            assert_eq!(l.key(Key::Enter), Came::Line(said.to_string()));
        }
        typed(&mut l, "bal");
        assert_eq!((l.key(Key::Up), l.text()), (Came::Changed, "peers".to_string()));
        assert_eq!((l.key(Key::Up), l.text(), l.cursor()), (Came::Changed, "status".to_string(), 6));
        assert_eq!(l.key(Key::Up), Came::Nothing);
        assert_eq!((l.key(Key::Down), l.text()), (Came::Changed, "peers".to_string()));
        assert_eq!((l.key(Key::Down), l.text()), (Came::Changed, "bal".to_string()));
        assert_eq!(l.key(Key::Down), Came::Nothing);
        // One brought back and changed is a new line: the first is as
        // it was, and the arrows go from the newest again.
        l.key(Key::Up);
        typed(&mut l, " now");
        assert_eq!(l.key(Key::Enter), Came::Line("peers now".to_string()));
        assert_eq!((l.key(Key::Up), l.text()), (Came::Changed, "peers now".to_string()));
        assert_eq!((l.key(Key::Up), l.text()), (Came::Changed, "peers".to_string()));
    }

    /// Tab, as a shell has it: one thing that fits is filled in, with
    /// a space; several are filled in as far as they agree; and where
    /// they agree no further, the second tab lists them.
    #[test]
    fn tab_finishes_what_is_begun() {
        let mut l = line(&["send", "send-file", "seed", "status", "supply", "pending", "mined"]);
        // One: finished.
        typed(&mut l, "sta");
        assert_eq!((l.key(Key::Tab), l.text(), l.cursor()), (Came::Changed, "status ".to_string(), 7));
        l.key(Key::KillLine);
        // Several, agreeing further: as far as they agree. Then no
        // further: nothing at the first tab, the list at the second.
        typed(&mut l, "s");
        assert_eq!((l.key(Key::Tab), l.text()), (Came::Nothing, "s".to_string()));
        typed(&mut l, "en");
        assert_eq!((l.key(Key::Tab), l.text()), (Came::Changed, "send".to_string()));
        assert_eq!(l.key(Key::Tab), Came::Nothing);
        assert_eq!(l.key(Key::Tab), Came::List(vec!["send".to_string(), "send-file".to_string()]));
        // (A key between two tabs: the next is a first again.)
        assert_eq!(l.key(Key::Tab), Came::List(vec!["send".to_string(), "send-file".to_string()]));
        l.key(Key::Left);
        l.key(Key::Right);
        assert_eq!(l.key(Key::Tab), Came::Nothing);
        typed(&mut l, "-");
        assert_eq!((l.key(Key::Tab), l.text()), (Came::Changed, "send-file ".to_string()));
        // Nothing fits: nothing.
        typed(&mut l, "zz");
        assert_eq!(l.key(Key::Tab), Came::Nothing);
        // The word under the cursor is the one finished, with what is
        // after the cursor left as it is.
        l.key(Key::KillLine);
        typed(&mut l, "txs pe now");
        for _ in 0..4 {
            l.key(Key::Left);
        }
        assert_eq!((l.key(Key::Tab), l.text(), l.cursor()), (Came::Changed, "txs pending  now".to_string(), 12));
    }

    /// The keys of a terminal, as it sends them: characters of more
    /// than one byte, the arrows in their two forms, and a key whose
    /// end has not been read yet, which is left for when it has.
    #[test]
    fn what_a_terminal_sends_is_read_as_keys() {
        use Key::*;
        assert_eq!(keys(b"ab\r"), (vec![Char('a'), Char('b'), Enter], 3));
        assert_eq!(keys(b"\x7f\x08\t\x04"), (vec![Backspace, Backspace, Tab, EndOfInput], 4));
        assert_eq!(keys(b"\x1b[A\x1b[B\x1b[C\x1b[D"), (vec![Up, Down, Right, Left], 12));
        assert_eq!(keys(b"\x1bOA\x1b[H\x1b[F\x1b[1~\x1b[4~\x1b[3~"), (vec![Up, Home, End, Home, End, Delete], 21));
        assert_eq!(keys(b"\x1b[1;5C"), (vec![Right], 6));
        assert_eq!(keys(b"\x01\x05\x02\x06\x10\x0e\x0b\x15\x17\x0c").0.len(), 10);
        assert_eq!(keys("é€".as_bytes()), (vec![Char('é'), Char('€')], 5));
        // Not whole yet: left over.
        assert_eq!(keys(b"a\x1b"), (vec![Char('a')], 1));
        assert_eq!(keys(b"a\x1b["), (vec![Char('a')], 1));
        assert_eq!(keys(b"a\x1b[1"), (vec![Char('a')], 1));
        assert_eq!(keys(&"é".as_bytes()[..1]), (vec![], 0));
        // What is no key of these is passed over.
        assert_eq!(keys(b"\x1b[5~x\x00y\x1bz"), (vec![Char('x'), Char('y')], 9));
    }

    /// A line is drawn after its prompt, over as many rows as it is
    /// long; the line before it is cleared first, row by row; and the
    /// cursor ends where it is in the line.
    #[test]
    fn a_line_is_drawn_over_as_many_rows_as_it_needs() {
        let mut l = line(&[]);
        typed(&mut l, "status");
        let (draw, at) = l.draw("> ", 20, (0, 0));
        assert_eq!((draw.as_str(), at), ("\r\x1b[0K> status\r\x1b[8C", (1, 1)));
        // The cursor in the middle: back to the row's start and along.
        l.key(Key::Home);
        assert_eq!(l.draw("> ", 20, (1, 1)), ("\r\x1b[0K> status\r\x1b[2C".to_string(), (1, 1)));
        // Longer than the terminal is wide: on two rows, the cursor on
        // the second; drawn again, both rows are cleared first.
        l.key(Key::End);
        typed(&mut l, " and more than twenty");
        let (draw, at) = l.draw("> ", 20, (1, 1));
        assert_eq!(at, (2, 2));
        assert!(draw.ends_with("\r\x1b[9C"), "{draw:?}");
        let (again, at) = l.draw("> ", 20, at);
        assert!(again.starts_with("\r\x1b[0K\x1b[1A\r\x1b[0K> status"), "{again:?}");
        assert_eq!(at, (2, 2));
        // The cursor on the first row of two: up one from the last.
        l.key(Key::Home);
        let (draw, at) = l.draw("> ", 20, at);
        assert!(draw.ends_with("\x1b[1A\r\x1b[2C") && at == (1, 2), "{draw:?}");
        // And drawn from there, the last row is gone down to first.
        assert!(l.draw("> ", 20, at).0.starts_with("\x1b[1B\r\x1b[0K\x1b[1A\r\x1b[0K"));
        // A line that ends at the right edge: the cursor is on a row
        // of its own, which is made for it.
        let mut l = line(&[]);
        typed(&mut l, "123456");
        let (draw, at) = l.draw("> ", 8, (0, 0));
        assert_eq!((draw.as_str(), at), ("\r\x1b[0K> 123456\n\r\r", (2, 2)));
    }
}
