//! The votes for a consensus file, and what names one.
//!
//! The message layer of the network is run by a file its miners agree
//! on. A miner that favours a file sets leaf 0 of the leaves its
//! header's auxiliary bytes commit to ([`crate::chain_proof::leaves`]) to the
//! file's SHA-256: a vote. A node that follows the chain counts the
//! votes over the last [`WINDOW`] blocks of the chain and fetches the
//! files they name, the most voted first.
//!
//! This is the count, and the constants of the rule. What a file says,
//! and which of the files voted for is in force, is the message layer's
//! to read.

use crate::hash::Digest;

/// Blocks over which votes are counted.
pub const WINDOW: u32 = 144;
/// The file in force changes only at heights that are multiples of this,
/// decided from the window ending there.
pub const EPOCH: u32 = WINDOW;
/// Blocks from a boundary `B` over which a change is made: both files
/// stand from `B` to `B + GRACE - 2`, the old one goes at `B + GRACE - 1`.
pub const GRACE: u32 = 6;
/// From `B + SWITCH` senders prefer the new file.
pub const SWITCH: u32 = 2;
/// Largest file.
pub const MAX_CONSENSUS: usize = 1 << 20;

/// The last boundary at or below `height`.
pub fn boundary(height: u32) -> u32 {
    height / EPOCH * EPOCH
}

/// A file's vote value: its SHA-256.
pub type Hash = [u8; 32];

/// The votes over a window of the chain's blocks.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Votes {
    /// Each hash voted for, with its votes and the highest height that
    /// voted for it, most votes first, then most recent.
    pub counts: Vec<(Hash, u32, u32)>,
    /// Blocks of the window whose headers commit to leaves that are not
    /// here yet, so whose vote is unknown: their id and height.
    pub missing: Vec<(Digest, u32)>,
    /// Blocks in the window.
    pub blocks: u32,
    /// The window's first and last heights.
    pub range: (u32, u32),
}

impl Votes {
    /// Builds the count from each block's vote, `None` for a block whose
    /// leaves are missing.
    pub fn tally(range: (u32, u32), blocks: impl Iterator<Item = (Digest, u32, Option<Hash>)>) -> Votes {
        let mut counts: Vec<(Hash, u32, u32)> = Vec::new();
        let mut missing = Vec::new();
        let mut n = 0;
        for (id, height, vote) in blocks {
            n += 1;
            match vote {
                None => missing.push((id, height)),
                Some(h) if h == [0u8; 32] => {}
                Some(h) => match counts.iter_mut().find(|c| c.0 == h) {
                    Some(c) => {
                        c.1 += 1;
                        c.2 = c.2.max(height);
                    }
                    None => counts.push((h, 1, height)),
                },
            }
        }
        counts.sort_by_key(|c| std::cmp::Reverse((c.1, c.2)));
        Votes { counts, missing, blocks: n, range }
    }

    /// Votes cast, for any file.
    pub fn cast(&self) -> u32 {
        self.counts.iter().map(|c| c.1).sum()
    }
}

/// The transfer id of the file with SHA-256 `hash`: the hash. A file is
/// checked by it once it arrives.
pub fn file_id(hash: &Hash) -> Digest {
    *hash
}

/// Whether `bytes` are the file `hash` names.
pub fn file_matches(hash: &Hash, bytes: &[u8]) -> bool {
    crate::sha256::sha256(bytes) == *hash
}

/// Relays a file may list at the most.
pub const MAX_RELAYS: usize = 8192;

/// Fewest relays an onion-mode file may list: a participant's three
/// rendezvous points must be distinct.
pub const MIN_RELAYS: usize = 3;

/// Which mode a file puts the network in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// No relays: the seed nodes stand in for them.
    Init,
    /// The listed relays carry the traffic.
    Onion,
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Mode::Init => "init",
            Mode::Onion => "onion",
        })
    }
}

/// A `relay` line: the relay's id (the hash of its Dilithium key) and its
/// UDP address as written (`host:port`, not resolved here). Every relay
/// may serve any role: a hop, or a rendezvous point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Relay {
    pub id: Digest,
    pub addr: String,
}

/// A parsed `consensus.txt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct File {
    pub mode: Mode,
    /// The relays, sorted by id (the order rendezvous points are chosen
    /// in); empty in init mode.
    pub relays: Vec<Relay>,
}

/// Why a file is invalid; the line number counts from 1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseError {
    TooLarge(usize),
    NotText,
    /// The first directive is not `mode init` or `mode onion`.
    NoMode,
    BadMode(usize),
    /// A `relay` line that is not an id and an address.
    BadRelay(usize),
    BadId(usize),
    BadAddress(usize),
    DuplicateRelay(usize),
    TooManyRelays,
    TooFewRelays(usize),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::TooLarge(n) => write!(f, "{n} bytes, over the {MAX_CONSENSUS} allowed"),
            ParseError::NotText => f.write_str("not UTF-8 text"),
            ParseError::NoMode => f.write_str("the first directive must be `mode init` or `mode onion`"),
            ParseError::BadMode(l) => write!(f, "line {l}: the mode must be init or onion"),
            ParseError::BadRelay(l) => write!(f, "line {l}: a relay line is `relay ID HOST:PORT`"),
            ParseError::BadId(l) => write!(f, "line {l}: the id must be a tab1… address"),
            ParseError::BadAddress(l) => write!(f, "line {l}: the address must be HOST:PORT"),
            ParseError::DuplicateRelay(l) => write!(f, "line {l}: the relay is listed already"),
            ParseError::TooManyRelays => write!(f, "more than {MAX_RELAYS} relays"),
            ParseError::TooFewRelays(n) => write!(f, "onion mode lists {n} relays, fewer than the {MIN_RELAYS} needed"),
        }
    }
}

impl std::error::Error for ParseError {}

/// Whether `addr` reads as `HOST:PORT`: a host name or an IPv4 address,
/// and a port. IPv6 is not spoken, so a bracketed address is refused.
fn address_ok(addr: &str) -> bool {
    let Some((host, port)) = addr.rsplit_once(':') else {
        return false;
    };
    if port.parse::<u16>().is_err() {
        return false;
    }
    !host.is_empty() && host.len() <= 253 && host.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-')
}

impl File {
    /// Parses and validates a `consensus.txt`: UTF-8,
    /// one directive per line, `#` comments, blank lines ignored, the
    /// first directive the mode. In init mode the rest is ignored; in
    /// onion mode `relay ID HOST:PORT` lines list the relays,
    /// between [`MIN_RELAYS`] and [`MAX_RELAYS`] of them, no id twice.
    /// Unknown directives are ignored.
    pub fn parse(bytes: &[u8]) -> Result<File, ParseError> {
        if bytes.len() > MAX_CONSENSUS {
            return Err(ParseError::TooLarge(bytes.len()));
        }
        let text = std::str::from_utf8(bytes).map_err(|_| ParseError::NotText)?;
        let mut mode = None;
        let mut relays: Vec<Relay> = Vec::new();
        for (i, raw) in text.lines().enumerate() {
            let line = i + 1;
            let content = raw.split('#').next().unwrap_or("").trim();
            if content.is_empty() {
                continue;
            }
            let mut words = content.split_whitespace();
            let directive = words.next().unwrap();
            let Some(mode) = mode else {
                if directive != "mode" {
                    return Err(ParseError::NoMode);
                }
                mode = Some(match (words.next(), words.next()) {
                    (Some("init"), None) => Mode::Init,
                    (Some("onion"), None) => Mode::Onion,
                    _ => return Err(ParseError::BadMode(line)),
                });
                continue;
            };
            if mode == Mode::Init || directive != "relay" {
                continue;
            }
            let (Some(id), Some(addr), None) = (words.next(), words.next(), words.next()) else {
                return Err(ParseError::BadRelay(line));
            };
            let id = crate::address::decode(id).ok_or(ParseError::BadId(line))?;
            if !address_ok(addr) {
                return Err(ParseError::BadAddress(line));
            }
            if relays.iter().any(|r| r.id == id) {
                return Err(ParseError::DuplicateRelay(line));
            }
            if relays.len() >= MAX_RELAYS {
                return Err(ParseError::TooManyRelays);
            }
            relays.push(Relay { id, addr: addr.to_string() });
        }
        let mode = mode.ok_or(ParseError::NoMode)?;
        if mode == Mode::Onion && relays.len() < MIN_RELAYS {
            return Err(ParseError::TooFewRelays(relays.len()));
        }
        relays.sort_by_key(|r| r.id);
        Ok(File { mode, relays })
    }
}

/// Why a voted-for file does not count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Skip {
    /// Not fetched (yet).
    NotHeld,
    Invalid(ParseError),
    /// No more than half the window's blocks voted, for any file: so
    /// many must.
    TooFew(u32),
}

impl std::fmt::Display for Skip {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Skip::NotHeld => f.write_str("not fetched"),
            Skip::Invalid(e) => write!(f, "invalid: {e}"),
            Skip::TooFew(needed) => write!(f, "too few blocks voted: {needed} of the window's must, for any file"),
        }
    }
}

/// The file in force. If more than half the window's blocks voted, for
/// any file: the most voted of the files that is held and valid, ties
/// to the most recently committed. If no more than half voted, or
/// there is no such file: init mode. (So it is those who make most of
/// the blocks who say which relays there are, and a few blocks of
/// somebody else's while nobody is voting say nothing.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Current {
    pub mode: Mode,
    /// The file in force, its hash and its votes.
    pub winner: Option<(Hash, u32)>,
    pub file: Option<File>,
    /// The files voted for more than the winner (every one, without a
    /// winner) that do not count, most voted first, and why: a node
    /// fetches those not held, since one may yet win.
    pub skipped: Vec<(Hash, u32, Skip)>,
}

impl Current {
    /// How many of a window of `of` blocks must vote, for any file,
    /// for one to be in force: more than half.
    pub fn needed(of: u32) -> u32 {
        of / 2 + 1
    }

    /// Decides from the votes over a window of `of` blocks, given the
    /// bytes of each file held.
    pub fn decide(votes: &Votes, of: u32, mut held: impl FnMut(&Hash) -> Option<Vec<u8>>) -> Current {
        let mut skipped = Vec::new();
        let (needed, cast) = (Self::needed(of), votes.cast());
        for &(hash, n, _) in &votes.counts {
            match held(&hash).map(|b| File::parse(&b)) {
                None => skipped.push((hash, n, Skip::NotHeld)),
                Some(Err(e)) => skipped.push((hash, n, Skip::Invalid(e))),
                Some(Ok(_)) if cast < needed => skipped.push((hash, n, Skip::TooFew(needed))),
                Some(Ok(file)) => {
                    return Current { mode: file.mode, winner: Some((hash, n)), file: Some(file), skipped };
                }
            }
        }
        Current { mode: Mode::Init, winner: None, file: None, skipped }
    }

    /// What is still wanted before it is known which file is in force,
    /// if anything is: the files voted for that are not held and would
    /// be in force if they were sound, and how many blocks' votes are
    /// missing where those could change which file has most, or
    /// whether enough voted at all. `None`: it is known, whatever else
    /// is lacking.
    ///
    /// A node that decided without these would hold another file to be
    /// in force than the rest do, or none, for as long as it was kept
    /// from them: so it does not decide, and keeps to what it knew.
    /// (Where no more than half the window's blocks could have voted,
    /// counting those whose votes are missing, nothing is in force and
    /// nothing is waited for: a network that is beginning.)
    pub fn undecided(&self, votes: &Votes, of: u32) -> Option<(Vec<Hash>, u32)> {
        let (needed, cast, missing) = (Self::needed(of), votes.cast(), votes.missing.len() as u32);
        if cast + missing < needed {
            return None;
        }
        // (Votes that are missing matter if they could bring the count
        // to what is needed, or take the first place from whichever
        // has it: all of them for the second, or for one with none.)
        let lead = match votes.counts[..] {
            [] => 0,
            [first] => first.1,
            [first, second, ..] => first.1 - second.1,
        };
        let votes_wanted = if missing > 0 && (cast < needed || lead <= missing) { missing } else { 0 };
        // (A file not held counts once enough have voted; before that,
        // only the missing votes could make it count.)
        let files: Vec<Hash> = match cast + votes_wanted >= needed {
            true => self.unfetched().copied().collect(),
            false => Vec::new(),
        };
        (!files.is_empty() || votes_wanted > 0).then_some((files, votes_wanted))
    }

    /// The files to fetch: voted for more than the winner, not held.
    pub fn unfetched(&self) -> impl Iterator<Item = &Hash> {
        self.skipped.iter().filter(|s| s.2 == Skip::NotHeld).map(|s| &s.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::digest_to_bytes;

    fn id(i: u32) -> Digest {
        core::array::from_fn(|k| (i * 8 + k as u32) as u8)
    }

    #[test]
    fn votes_count_and_break_ties_by_recency() {
        let (a, b) = ([1u8; 32], [2u8; 32]);
        let blocks = vec![
            (id(1), 10, Some(a)),
            (id(2), 11, Some(b)),
            (id(3), 12, Some([0u8; 32])),
            (id(4), 13, None),
            (id(5), 14, Some(b)),
            (id(6), 15, Some(a)),
        ];
        let v = Votes::tally((10, 15), blocks.into_iter());
        // Two votes each: the one voted for last comes first.
        assert_eq!(v.counts, vec![(a, 2, 15), (b, 2, 14)]);
        assert_eq!(v.missing, vec![(id(4), 13)]);
        assert_eq!((v.blocks, v.cast(), v.range), (6, 4, (10, 15)));
        let more = Votes::tally((1, 3), [(id(1), 1, Some(b)), (id(2), 2, Some(b)), (id(3), 3, Some(a))].into_iter());
        assert_eq!(more.counts, vec![(b, 2, 2), (a, 1, 3)]);
        assert_eq!(Votes::tally((0, 0), std::iter::empty()), Votes { range: (0, 0), ..Votes::default() });
    }

    /// Which file is in force is not decided while a file that would
    /// be is not held, or votes are missing that could change the
    /// count; and is, when neither could matter.
    #[test]
    fn what_is_in_force_is_not_decided_while_it_could_be_otherwise() {
        let (a, b) = ([1u8; 32], [2u8; 32]);
        let file = b"mode init\n".to_vec();
        // Of a window of ten: `for_a` votes for a, `for_b` for b,
        // `missing` blocks whose votes are not had, the rest for none.
        let tally = |for_a: u32, for_b: u32, missing: u32| {
            let blocks = (0..10u32).map(|i| {
                let vote = match i {
                    i if i < for_a => Some(a),
                    i if i < for_a + for_b => Some(b),
                    i if i < for_a + for_b + missing => None,
                    _ => Some([0u8; 32]),
                };
                (id(i), i, vote)
            });
            Votes::tally((0, 9), blocks)
        };
        let decide = |votes: &Votes, held: &[Hash]| {
            let current = Current::decide(votes, 10, |hash| held.contains(hash).then(|| file.clone()));
            current.undecided(votes, 10)
        };
        // Nobody votes, or too few could have: known, with nothing had.
        assert_eq!(decide(&tally(0, 0, 0), &[]), None);
        assert_eq!(decide(&tally(3, 0, 2), &[]), None);
        // Enough voted for a file that is not held: that file is wanted.
        assert_eq!(decide(&tally(7, 0, 0), &[]), Some((vec![a], 0)));
        assert_eq!(decide(&tally(7, 0, 0), &[a]), None);
        // The most voted is not held, and a lesser one is: still wanted.
        assert_eq!(decide(&tally(4, 2, 0), &[b]), Some((vec![a], 0)));
        assert_eq!(decide(&tally(4, 2, 0), &[a]), None);
        // Votes missing that could bring the count to what is needed.
        assert_eq!(decide(&tally(4, 0, 3), &[a]), Some((vec![], 3)));
        assert_eq!(decide(&tally(4, 0, 3), &[]), Some((vec![a], 3)));
        // Votes missing that could change which has most; and that
        // could not.
        assert_eq!(decide(&tally(4, 3, 2), &[a, b]), Some((vec![], 2)));
        assert_eq!(decide(&tally(6, 1, 2), &[a, b]), None);
        assert_eq!(decide(&tally(6, 0, 2), &[a]), None);
    }

    #[test]
    fn file_ids_are_their_hashes() {
        let hash: Hash = core::array::from_fn(|i| 0xff - i as u8);
        let fid = file_id(&hash);
        assert_eq!(crate::hash::digest_from_bytes(&digest_to_bytes(&fid)), Some(fid));
        assert_ne!(file_id(&[1; 32]), file_id(&[2; 32]));
        assert_eq!(file_id(&hash), fid);
        assert!(file_matches(&crate::sha256::sha256(b"mode init\n"), b"mode init\n"));
        assert!(!file_matches(&crate::sha256::sha256(b"mode init\n"), b"mode init"));
    }

    #[test]
    fn files_parse_and_invalid_ones_are_refused() {
        let ids: Vec<Digest> = (1..=4).map(id).collect();
        let addr = |i: usize| crate::address::encode(&ids[i]);
        assert_eq!(File::parse(b"mode init\n"), Ok(File { mode: Mode::Init, relays: vec![] }));
        // Comments, blank lines, and in init mode anything else, are ignored.
        let init = "# a comment\n\n  mode init  # trailing\nrelay garbage\nfuture directive\n";
        assert_eq!(File::parse(init.as_bytes()).unwrap().mode, Mode::Init);
        let onion = format!(
            "mode onion\nrelay {} relay3.example.org:3737\nrelay {} 10.0.0.2:3737\n\
             relay {} 10.0.0.3:3737\nfuture directive\n",
            addr(2),
            addr(0),
            addr(1)
        );
        let f = File::parse(onion.as_bytes()).unwrap();
        assert_eq!(f.mode, Mode::Onion);
        // Sorted by id, whatever the order written.
        assert_eq!(f.relays.iter().map(|r| r.id).collect::<Vec<_>>(), ids[..3].to_vec());
        assert_eq!(f.relays[2].addr, "relay3.example.org:3737");
        let hex: String = digest_to_bytes(&ids[0]).iter().map(|b| format!("{b:02x}")).collect();
        let bad = [
            ("".to_string(), ParseError::NoMode),
            ("# only a comment\n".to_string(), ParseError::NoMode),
            ("relay x y\nmode init\n".to_string(), ParseError::NoMode),
            ("mode tor\n".to_string(), ParseError::BadMode(1)),
            ("mode init now\n".to_string(), ParseError::BadMode(1)),
            ("mode onion\n".to_string(), ParseError::TooFewRelays(0)),
            ("mode onion\nrelay\n".to_string(), ParseError::BadRelay(2)),
            ("mode onion\nrelay tab1qqqq 1.2.3.4:1\n".to_string(), ParseError::BadId(2)),
            // (An id is an address: its bytes written out are not one.)
            (format!("mode onion\nrelay {hex} 1.2.3.4:1\n"), ParseError::BadId(2)),
        ];
        for (text, err) in bad {
            assert_eq!(File::parse(text.as_bytes()), Err(err), "{text:?}");
        }
        let with = |line: &str| format!("mode onion\nrelay {} a:1\nrelay {} b:2\n{line}\n", addr(0), addr(1));
        for (line, err) in [
            (format!("relay {} c", addr(2)), ParseError::BadAddress(4)),
            (format!("relay {} :3737", addr(2)), ParseError::BadAddress(4)),
            (format!("relay {} c:99999", addr(2)), ParseError::BadAddress(4)),
            (format!("relay {} [::1]:3737", addr(2)), ParseError::BadAddress(4)),
            // No flags: any relay serves any role.
            (format!("relay {} c:1 exit", addr(2)), ParseError::BadRelay(4)),
            (format!("relay {} c:1", addr(1)), ParseError::DuplicateRelay(4)),
        ] {
            assert_eq!(File::parse(with(&line).as_bytes()), Err(err), "{line}");
        }
        assert_eq!(File::parse(&[0xffu8, 0xfe]), Err(ParseError::NotText));
        assert!(matches!(File::parse(&vec![b' '; MAX_CONSENSUS + 1]), Err(ParseError::TooLarge(_))));
        assert_eq!(ParseError::TooFewRelays(2).to_string(), "onion mode lists 2 relays, fewer than the 3 needed");
        // The decision: if more than half the window's blocks voted, for
        // any file, the most voted file held and valid, whatever its
        // mode; files not held or invalid count for nothing. If no more
        // than half voted, nothing is in force.
        let (x, y, z) = ([1u8; 32], [2u8; 32], [3u8; 32]);
        let cast = [(1, x), (2, x), (3, x), (4, y), (5, y), (6, z)];
        let votes = Votes::tally((1, 6), cast.into_iter().map(|(h, file)| (id(h), h, Some(file))));
        assert_eq!((Current::needed(7), Current::needed(144), Current::needed(6), votes.cast()), (4, 73, 4, 6));
        fn files<'a>(
            x: Option<&'a [u8]>,
            y: Option<&'a [u8]>,
            z: Option<&'a [u8]>,
        ) -> impl FnMut(&Hash) -> Option<Vec<u8>> + 'a {
            move |h: &Hash| [x, y, z][h[0] as usize - 1].map(|b| b.to_vec())
        }
        let none = Current { mode: Mode::Init, winner: None, file: None, skipped: vec![] };
        assert_eq!(Current::decide(&Votes::default(), 6, |_| None), none);
        // Nothing held: init, and every file is to be fetched.
        let c = Current::decide(&votes, 6, files(None, None, None));
        assert_eq!((c.mode, c.winner), (Mode::Init, None));
        assert_eq!(c.unfetched().collect::<Vec<_>>(), vec![&x, &y, &z]);
        // The leader is not held: the next, valid, is in force meanwhile,
        // and the leader is still wanted.
        let c = Current::decide(&votes, 6, files(None, Some(onion.as_bytes()), None));
        assert_eq!((c.mode, c.winner), (Mode::Onion, Some((y, 2))));
        assert_eq!(c.file.as_ref().unwrap().relays.len(), 3);
        assert_eq!(c.unfetched().collect::<Vec<_>>(), vec![&x]);
        // The leader is invalid: it counts for nothing.
        let c = Current::decide(&votes, 6, files(Some(b"mode tor\n"), Some(onion.as_bytes()), None));
        assert_eq!(c.winner, Some((y, 2)));
        assert!(matches!(c.skipped[..], [(h, 3, Skip::Invalid(ParseError::BadMode(1)))] if h == x));
        assert_eq!(c.unfetched().count(), 0);
        // An explicit vote for init wins like any other.
        let c = Current::decide(&votes, 6, files(Some(b"mode init\n"), Some(onion.as_bytes()), None));
        assert_eq!((c.mode, c.winner), (Mode::Init, Some((x, 3))));
        // Only invalid files: init, with nothing in force.
        let c = Current::decide(&votes, 6, files(Some(b"x"), Some(b"y"), Some(b"z")));
        assert_eq!((c.mode, c.winner, c.skipped.len()), (Mode::Init, None, 3));
        // The most voted wins though it has fewer than half itself: it
        // is that most of the blocks voted, for whatever, that counts.
        // (Six of eleven blocks voted, three of them for the first.)
        let c = Current::decide(&votes, 11, files(Some(onion.as_bytes()), Some(b"mode init\n"), None));
        assert_eq!((c.mode, c.winner), (Mode::Onion, Some((x, 3))));
        // No more than half the window's blocks voted: nothing is in
        // force, whatever they voted for. (Six of twelve is half; six
        // of a hundred and forty-four, a few blocks of somebody's.)
        for of in [12, 144] {
            let c = Current::decide(&votes, of, files(Some(onion.as_bytes()), Some(onion.as_bytes()), None));
            assert_eq!((c.mode, c.winner), (Mode::Init, None), "of {of}");
            let needed = Current::needed(of);
            assert!(
                matches!(c.skipped[..2], [(_, 3, Skip::TooFew(n)), (_, 2, Skip::TooFew(m))] if n == needed && m == needed)
            );
            assert_eq!(c.unfetched().collect::<Vec<_>>(), vec![&z], "one not held is still wanted");
        }
    }

    #[test]
    fn boundaries() {
        assert_eq!((boundary(0), boundary(143), boundary(144), boundary(300)), (0, 0, 144, 288));
        const { assert!(SWITCH < GRACE && GRACE < EPOCH) };
    }
}
