//! How a program is told what to do: its options, the help that lists
//! them, and the reading of what was given.
//!
//! A program's options are one list ([`Options`]), from which its help
//! is written and its command line is read, so that the two cannot
//! disagree. What each option means is the program's own to say: here
//! is only what was given ([`Given`]), option by option, with the
//! values read as the numbers, times and sizes they are.
//!
//! * An option that is not one is refused by name:
//!   `unknown configuration option: '--prot'`.
//! * `--help`, anywhere on the line, is the help and nothing else.
//! * A word `@FILE` is a file of options: one to a line, written as on
//!   the command line, with `#` before anything that is not one. What
//!   the command line says is taken before what a file says, and a
//!   later file before an earlier; an option that may be given many
//!   times has the values of all of them.

use std::path::{Path, PathBuf};

use crate::logger::fmt::column;

/// What an option takes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Takes {
    /// Nothing: it is given or it is not.
    Nothing,
    /// A value, called this in the help.
    Value(&'static str),
    /// A value, and the option may be given more than once.
    Values(&'static str),
}

/// An option: its name, as it is given after `--`; what it takes; and
/// what the help says of it. A line break is a line break there.
#[derive(Clone, Copy, Debug)]
pub struct Opt {
    pub name: &'static str,
    pub takes: Takes,
    pub help: &'static str,
}

/// A program's options: what its help begins with (what the program
/// is, and how it is used), and the options, in the sections and the
/// order of the help.
#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub about: &'static str,
    pub sections: &'static [(&'static str, &'static [Opt])],
}

/// Why a program does not start on what it was given.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refused {
    /// `--help` was given: the help is what was asked for.
    Help,
    /// Something given is wrong: what, as it is said after `Error: `.
    Wrong(String),
}

impl Refused {
    /// What the program says, and the code it ends with. Asked for, the
    /// help is all there is and nothing is wrong (0); something wrong
    /// is said first, then the help, and that is a failure (-1).
    pub fn said(&self, options: &Options) -> (String, i32) {
        match self {
            Refused::Help => (options.help(), 0),
            Refused::Wrong(what) => (format!("Error: {what}\n\n{}", options.help()), -1),
        }
    }
}

/// A path as it was given, from the root: one that is not is from
/// `here`, where the program was started.
pub fn whole(here: &Path, given: &str) -> PathBuf {
    let p = Path::new(given);
    if p.is_absolute() { p.to_path_buf() } else { here.join(p) }
}

impl Options {
    fn all(&self) -> impl Iterator<Item = &'static Opt> {
        self.sections.iter().flat_map(|(_, opts)| opts.iter())
    }

    /// The help: what the options are, by section.
    pub fn help(&self) -> String {
        let mut out = String::from(self.about);
        // The widest option, with what it takes, sets where the telling
        // begins.
        let shown = |o: &Opt| match o.takes {
            Takes::Nothing => format!("--{}", o.name),
            Takes::Value(v) | Takes::Values(v) => format!("--{} {v}", o.name),
        };
        let wide = self.all().map(|o| shown(o).len()).max().unwrap_or(0) + 2;
        for (section, opts) in self.sections {
            out += &format!("\n{section}\n");
            for o in *opts {
                for (k, line) in o.help.lines().enumerate() {
                    let first = if k == 0 { shown(o) } else { String::new() };
                    out += &format!("  {}{line}\n", column(&first, wide, ' '));
                }
            }
        }
        out += "\nA TIME is so many seconds, or a number and s, m, h or d: 90, 90s, 60m, 1h, 7d.\n";
        out += "A SIZE is so many bytes, or a number and k, m or g, each 1024 of the one before:\n";
        out += "1048576, 1024k, 1m.\n";
        out += "\nOptions can be kept in a file and given as @FILE: one to a line, as they are\n";
        out += "written here, with # before anything that is not one. What is on the command\n";
        out += "line is taken before what is in a file.\n";
        out
    }

    /// What `args` give, option by option: the command line, and the
    /// files of options it names, each read with `load`.
    ///
    /// Beyond reading those files, nothing is opened or made: this
    /// reads only, and what the values mean is for whoever asks for
    /// them ([`Given`]).
    pub fn read(
        &self,
        args: &[String],
        here: &Path,
        load: &dyn Fn(&Path) -> std::io::Result<String>,
    ) -> Result<Given, Refused> {
        // `--help` anywhere is the help, whatever else is there.
        if args.iter().any(|a| a == "--help") {
            return Err(Refused::Help);
        }
        let wrong = |what: String| Refused::Wrong(what);
        let mut given = Given::default();
        let mut files = Vec::new();
        for file in args.iter().filter_map(|a| a.strip_prefix('@')) {
            if file.is_empty() {
                return Err(wrong("@ needs the name of a file after it".into()));
            }
            let path = whole(here, file);
            let text = load(&path).map_err(|e| wrong(format!("{} cannot be read: {e}", path.display())))?;
            for (number, line) in text.lines().enumerate() {
                // What comes after a # is for whoever reads the file.
                let line = line.split('#').next().unwrap_or("").trim();
                if line.is_empty() {
                    continue;
                }
                // An option, and the rest of the line its value: so
                // that a path may have spaces in it.
                let words: Vec<&str> = line.splitn(2, char::is_whitespace).map(str::trim).collect();
                let place = format!("{} line {}: ", path.display(), number + 1);
                match words[0] {
                    "--help" => return Err(wrong(format!("{place}--help is for the command line"))),
                    word if word.starts_with('@') => {
                        return Err(wrong(format!("{place}a file of options cannot name another")));
                    }
                    _ => self.take(&mut given, &words, files.len(), &place)?,
                }
            }
            files.push(path);
        }
        let line: Vec<&str> = args.iter().filter(|a| !a.starts_with('@')).map(String::as_str).collect();
        self.take(&mut given, &line, files.len(), "")?;
        Ok(given)
    }

    /// The options of `words` (a command line, or one line of a file),
    /// added to `given` as from `source`. `place` is said before what is
    /// wrong: nothing for the command line, the file and line for a file.
    fn take(&self, given: &mut Given, words: &[&str], source: usize, place: &str) -> Result<(), Refused> {
        let wrong = |what: String| Refused::Wrong(format!("{place}{what}"));
        let mut at = 0;
        while at < words.len() {
            let word = words[at];
            let known = word.strip_prefix("--").and_then(|name| self.all().find(|o| o.name == name));
            let Some(opt) = known else {
                return Err(wrong(format!("unknown configuration option: '{word}'")));
            };
            match opt.takes {
                Takes::Nothing => {
                    // (Given in a file and on the command line is given.)
                    if !given.flags.contains(&opt.name) {
                        given.flags.push(opt.name);
                    }
                }
                Takes::Value(_) | Takes::Values(_) => {
                    let Some(value) = words.get(at + 1).filter(|v| !v.starts_with("--")) else {
                        return Err(wrong(format!("--{} needs a value", opt.name)));
                    };
                    // Twice in one place is a mistake; in two places, the
                    // nearer is taken.
                    let twice = given.values.iter().any(|(n, _, from)| *n == opt.name && *from == source);
                    if matches!(opt.takes, Takes::Value(_)) && twice {
                        return Err(wrong(format!("--{} was given twice", opt.name)));
                    }
                    given.values.push((opt.name, value.to_string(), source));
                    at += 1;
                }
            }
            at += 1;
        }
        Ok(())
    }
}

/// A number and what it is counted in, as `60m` or `1024k`: the number
/// times what its last letter stands for among `units`, or the number
/// alone. None if it is not that, or too large to count.
fn with_unit(value: &str, units: &[(char, u64)]) -> Option<u64> {
    let last = value.chars().last()?.to_ascii_lowercase();
    let (digits, times) = match units.iter().find(|(letter, _)| *letter == last) {
        Some((_, times)) => (&value[..value.len() - 1], *times),
        None => (value, 1),
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse::<u64>().ok()?.checked_mul(times)
}

/// What was given, option by option, before it is made sense of: from
/// files, and from the command line, which is taken before them.
#[derive(Default, Debug)]
pub struct Given {
    /// An option's name, its value, and where it was given: the place
    /// of its file among the files, or past them all for the command
    /// line.
    values: Vec<(&'static str, String, usize)>,
    flags: Vec<&'static str>,
}

impl Given {
    /// Whether an option that takes nothing was given.
    pub fn flag(&self, name: &str) -> bool {
        self.flags.contains(&name)
    }

    /// Every value of an option that may be given more than once: the
    /// files' and the command line's together.
    pub fn all<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a str> + 'a {
        self.values.iter().filter(move |(n, _, _)| *n == name).map(|(_, v, _)| v.as_str())
    }

    /// The value of an option: where it was given in more than one
    /// place, the nearest (the command line, then the last file).
    pub fn one(&self, name: &str) -> Option<&str> {
        self.values.iter().filter(|(n, _, _)| *n == name).max_by_key(|(_, _, from)| *from).map(|(_, v, _)| v.as_str())
    }

    /// A path, if the option was given: from the root, or from `here`
    /// ([`whole`]).
    pub fn path(&self, name: &str, here: &Path) -> Result<Option<PathBuf>, Refused> {
        match self.one(name) {
            Some("") => Err(Refused::Wrong(format!("--{name}: no path was given"))),
            Some(p) => Ok(Some(whole(here, p))),
            None => Ok(None),
        }
    }

    /// A time in seconds, if the option was given: so many seconds, or
    /// a number and `s`, `m`, `h` or `d`. No less than `least`.
    pub fn time(&self, name: &str, least: u64) -> Result<Option<u64>, Refused> {
        let units = [('s', 1), ('m', 60), ('h', 3600), ('d', 86_400)];
        self.counted(name, least, &units, "a time (as 90, 90s, 60m or 1h)")
    }

    /// A size in bytes, if the option was given: so many bytes, or a
    /// number and `k`, `m` or `g`.
    pub fn size(&self, name: &str, least: u64) -> Result<Option<u64>, Refused> {
        let units = [('k', 1 << 10), ('m', 1 << 20), ('g', 1 << 30)];
        self.counted(name, least, &units, "a size (as 1048576, 1024k or 1m)")
    }

    fn counted(&self, name: &str, least: u64, units: &[(char, u64)], what: &str) -> Result<Option<u64>, Refused> {
        let Some(value) = self.one(name) else {
            return Ok(None);
        };
        let n = with_unit(value, units).ok_or_else(|| Refused::Wrong(format!("--{name}: '{value}' is not {what}")))?;
        if n < least {
            return Err(Refused::Wrong(format!("--{name}: {value} is under the least it may be ({least})")));
        }
        Ok(Some(n))
    }

    /// A whole number, if the option was given: no less than `least`.
    pub fn number(&self, name: &str, least: u64) -> Result<Option<u64>, Refused> {
        let Some(value) = self.one(name) else {
            return Ok(None);
        };
        let n: u64 = value.parse().map_err(|_| Refused::Wrong(format!("--{name}: '{value}' is not a number")))?;
        if n < least {
            return Err(Refused::Wrong(format!("--{name}: {value} is under the least it may be ({least})")));
        }
        Ok(Some(n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const OPTIONS: Options = Options {
        about: "a program for the tests.\n\nusage: program [options]\n",
        sections: &[
            (
                "General",
                &[
                    Opt { name: "help", takes: Takes::Nothing, help: "print this and exit" },
                    Opt { name: "data-dir", takes: Takes::Value("DIR"), help: "where things are kept\n(default here)" },
                    Opt { name: "quiet", takes: Takes::Nothing, help: "say nothing" },
                ],
            ),
            (
                "Network",
                &[
                    Opt { name: "peer", takes: Takes::Values("ADDR"), help: "a peer; may be repeated" },
                    Opt { name: "wait", takes: Takes::Value("TIME"), help: "how long" },
                    Opt { name: "room", takes: Takes::Value("SIZE"), help: "how much" },
                    Opt { name: "tries", takes: Takes::Value("N"), help: "how often" },
                ],
            ),
        ],
    };

    fn read_with(args: &[&str], files: &[(&str, &str)]) -> Result<Given, Refused> {
        let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
        let load = |path: &Path| {
            let found = files.iter().find(|(name, _)| Path::new(name) == path);
            found.map(|(_, text)| text.to_string()).ok_or_else(|| std::io::Error::other("no such file"))
        };
        OPTIONS.read(&args, Path::new("/here"), &load)
    }

    fn read(args: &[&str]) -> Given {
        read_with(args, &[]).unwrap()
    }

    fn wrong(args: &[&str]) -> String {
        match read_with(args, &[]) {
            Err(Refused::Wrong(what)) => what,
            other => panic!("{args:?}: {other:?}"),
        }
    }

    /// What is given is what is had: flags, values, and the values of
    /// an option given more than once, in the order given.
    #[test]
    fn what_is_given_is_what_is_had() {
        let none = read(&[]);
        assert!(!none.flag("quiet") && none.one("data-dir").is_none() && none.all("peer").count() == 0);
        let given = read(&["--quiet", "--data-dir", "/srv", "--peer", "a:1", "--peer", "b:2", "--quiet"]);
        assert!(given.flag("quiet") && !given.flag("help"));
        assert_eq!(given.one("data-dir"), Some("/srv"));
        assert_eq!(given.all("peer").collect::<Vec<_>>(), ["a:1", "b:2"]);
        // A path is from the root, or from where the program was begun.
        let here = Path::new("/here");
        assert_eq!(given.path("data-dir", here), Ok(Some(PathBuf::from("/srv"))));
        assert_eq!(read(&["--data-dir", "kept"]).path("data-dir", here), Ok(Some(PathBuf::from("/here/kept"))));
        assert_eq!(read(&[]).path("data-dir", here), Ok(None));
        assert_eq!(whole(here, "a/b"), PathBuf::from("/here/a/b"));
    }

    /// What is wrong is said by the option's name.
    #[test]
    fn what_is_wrong_is_said_by_name() {
        assert_eq!(wrong(&["--prot"]), "unknown configuration option: '--prot'");
        assert_eq!(wrong(&["stray"]), "unknown configuration option: 'stray'");
        assert_eq!(wrong(&["--data-dir"]), "--data-dir needs a value");
        assert_eq!(wrong(&["--data-dir", "--quiet"]), "--data-dir needs a value");
        assert_eq!(wrong(&["--data-dir", "a", "--data-dir", "b"]), "--data-dir was given twice");
        assert_eq!(wrong(&["@"]), "@ needs the name of a file after it");
        assert_eq!(wrong(&["@missing"]), "/here/missing cannot be read: no such file");
    }

    /// `--help` anywhere is the help; asked for, it is no failure, and
    /// after something wrong it is.
    #[test]
    fn help_anywhere_is_help() {
        assert_eq!(read_with(&["--quiet", "--help", "--prot"], &[]).unwrap_err(), Refused::Help);
        let (said, code) = Refused::Help.said(&OPTIONS);
        assert_eq!((said.as_str(), code), (OPTIONS.help().as_str(), 0));
        let (said, code) = Refused::Wrong("it is wrong".into()).said(&OPTIONS);
        assert_eq!((said, code), (format!("Error: it is wrong\n\n{}", OPTIONS.help()), -1));
    }

    /// The help is the list: what the program is, then every option
    /// under its section, with what it takes, the telling in one
    /// column.
    #[test]
    fn the_help_is_the_list() {
        let help = OPTIONS.help();
        assert!(help.starts_with("a program for the tests.\n\nusage: program [options]\n\nGeneral\n"));
        // (The widest is `--data-dir DIR`, fourteen: two more, and two
        // before.)
        assert!(help.contains("\n  --help          print this and exit\n"));
        assert!(help.contains("\n  --data-dir DIR  where things are kept\n                  (default here)\n"));
        assert!(help.contains("\nNetwork\n  --peer ADDR     a peer; may be repeated\n"));
        assert!(help.ends_with("line is taken before what is in a file.\n"));
        for o in OPTIONS.all() {
            assert_eq!(help.matches(&format!("\n  --{}", o.name)).count(), 1, "--{}", o.name);
        }
    }

    /// Times and sizes take units; a number takes none; and none is
    /// under the least it may be.
    #[test]
    fn times_and_sizes_take_units() {
        for (given, seconds) in [("90", 90), ("90s", 90), ("60m", 3600), ("2h", 7200), ("7d", 604_800), ("1H", 3600)] {
            assert_eq!(read(&["--wait", given]).time("wait", 0), Ok(Some(seconds)), "{given}");
        }
        for (given, bytes) in [("1048576", 1 << 20), ("1024k", 1 << 20), ("1m", 1 << 20), ("2g", 2 << 30), ("3K", 3072)]
        {
            assert_eq!(read(&["--room", given]).size("room", 0), Ok(Some(bytes)), "{given}");
        }
        assert_eq!(read(&["--tries", "12"]).number("tries", 0), Ok(Some(12)));
        assert_eq!(
            (read(&[]).time("wait", 5), read(&[]).size("room", 5), read(&[]).number("tries", 5)),
            (Ok(None), Ok(None), Ok(None))
        );
        let said = |r: Result<Option<u64>, Refused>| match r {
            Err(Refused::Wrong(what)) => what,
            other => panic!("{other:?}"),
        };
        assert_eq!(
            said(read(&["--wait", "soon"]).time("wait", 0)),
            "--wait: 'soon' is not a time (as 90, 90s, 60m or 1h)"
        );
        assert_eq!(said(read(&["--wait", "m"]).time("wait", 0)), "--wait: 'm' is not a time (as 90, 90s, 60m or 1h)");
        assert_eq!(said(read(&["--wait", "1k"]).time("wait", 0)), "--wait: '1k' is not a time (as 90, 90s, 60m or 1h)");
        assert_eq!(
            said(read(&["--room", "1h"]).size("room", 0)),
            "--room: '1h' is not a size (as 1048576, 1024k or 1m)"
        );
        assert_eq!(
            said(read(&["--room", "99999999999999999999g"]).size("room", 0)),
            "--room: '99999999999999999999g' is not a size (as 1048576, 1024k or 1m)"
        );
        assert_eq!(said(read(&["--tries", "1m"]).number("tries", 0)), "--tries: '1m' is not a number");
        assert_eq!(said(read(&["--wait", "4s"]).time("wait", 5)), "--wait: 4s is under the least it may be (5)");
        assert_eq!(said(read(&["--tries", "4"]).number("tries", 5)), "--tries: 4 is under the least it may be (5)");
        let no_path = read(&["--data-dir", ""]).path("data-dir", Path::new("/"));
        assert_eq!(no_path, Err(Refused::Wrong("--data-dir: no path was given".into())));
    }

    /// A file of options is given with an `@`: a line an option, with
    /// the rest of the line its value; the command line before a file,
    /// and a later file before an earlier.
    #[test]
    fn a_file_of_options() {
        let first = "# what this node is told\n--data-dir /srv/a dir with spaces   # where\n\n--peer a:1\n--quiet\n";
        let second = "--data-dir /srv/second\n--peer b:2\n--wait 5m\n";
        let files = [("/here/first", first), ("/etc/second", second)];
        let given = read_with(&["@first", "--peer", "c:3", "@/etc/second"], &files).unwrap();
        assert!(given.flag("quiet"));
        assert_eq!(given.one("data-dir"), Some("/srv/second"));
        assert_eq!(given.all("peer").collect::<Vec<_>>(), ["a:1", "b:2", "c:3"]);
        assert_eq!(given.time("wait", 0), Ok(Some(300)));
        let over = read_with(&["--data-dir", "/mine", "@first", "@/etc/second"], &files).unwrap();
        assert_eq!(over.one("data-dir"), Some("/mine"));
        assert_eq!(read_with(&["@first"], &files).unwrap().one("data-dir"), Some("/srv/a dir with spaces"));
        // What is wrong in a file is said with the file and the line.
        let said = |text: &str| match read_with(&["@f"], &[("/here/f", text)]) {
            Err(Refused::Wrong(what)) => what,
            other => panic!("{other:?}"),
        };
        assert_eq!(said("--quiet\n--prot 1\n"), "/here/f line 2: unknown configuration option: '--prot'");
        assert_eq!(said("\n\n--data-dir\n"), "/here/f line 3: --data-dir needs a value");
        assert_eq!(said("--data-dir a\n--data-dir b\n"), "/here/f line 2: --data-dir was given twice");
        assert_eq!(said("--help\n"), "/here/f line 1: --help is for the command line");
        assert_eq!(said("@other\n"), "/here/f line 1: a file of options cannot name another");
    }
}
