//! JSON: what the node's ports say to whoever asks, where it is for a
//! person or a script to read, and what they say to it.
//!
//! All of JSON is read (RFC 8259), and no more than JSON: what is not
//! quite it is refused, with where it went wrong, since what comes in
//! at a port comes from anyone. What is read is no deeper than
//! [`MAX_DEPTH`], and an object that names a member twice is refused:
//! which of the two was meant is not for the reader to choose.
//!
//! # Numbers
//!
//! A number that is whole is kept whole ([`Json::Int`]), of any size a
//! count, a height or a time may have. An amount is not written as a
//! number at all: amounts are of 64 and 128 bits, more than the numbers
//! of most things that read JSON hold, and are written as strings of
//! digits ([`Json::amount`], [`Json::as_amount`]). So are hashes, in
//! hex.

/// How deep what is read may be: arrays in arrays, objects in objects.
pub const MAX_DEPTH: usize = 32;

/// A JSON value. An object's members are in the order they were
/// written.
#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// A whole number.
    Int(i128),
    /// A number with a fraction or an exponent.
    Float(f64),
    Str(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

/// Why what was given is not JSON: what is wrong, and at which byte.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotJson {
    pub what: &'static str,
    pub at: usize,
}

impl std::fmt::Display for NotJson {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "not JSON: {} at byte {}", self.what, self.at)
    }
}

impl Json {
    /// An object of `members`, in their order.
    pub fn object<const N: usize>(members: [(&str, Json); N]) -> Json {
        Json::Object(members.into_iter().map(|(name, value)| (name.to_string(), value)).collect())
    }

    /// A string.
    pub fn str(text: impl Into<String>) -> Json {
        Json::Str(text.into())
    }

    /// A count, a height, a time: a whole number.
    pub fn int(n: impl Into<i128>) -> Json {
        Json::Int(n.into())
    }

    /// An amount, as the string of its digits.
    pub fn amount(units: u128) -> Json {
        Json::Str(units.to_string())
    }

    /// Bytes, as hex.
    pub fn hex(bytes: &[u8]) -> Json {
        Json::Str(bytes.iter().map(|b| format!("{b:02x}")).collect())
    }

    /// The member `name` of an object.
    pub fn get(&self, name: &str) -> Option<&Json> {
        match self {
            Json::Object(members) => members.iter().find(|(n, _)| n == name).map(|(_, v)| v),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// A whole number that is not negative and is no more than 64 bits.
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Json::Int(n) => u64::try_from(*n).ok(),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Array(items) => Some(items),
            _ => None,
        }
    }

    /// An amount: a string of digits and nothing else, of a number that
    /// 128 bits hold.
    pub fn as_amount(&self) -> Option<u128> {
        let digits = self.as_str()?;
        (!digits.is_empty() && digits.len() <= 39 && digits.bytes().all(|b| b.is_ascii_digit()))
            .then(|| digits.parse().ok())?
    }

    /// Bytes written as hex: so many of them exactly.
    pub fn as_hex<const N: usize>(&self) -> Option<[u8; N]> {
        let text = self.as_str()?.as_bytes();
        if text.len() != 2 * N {
            return None;
        }
        let digit = |c: u8| (c as char).to_digit(16).filter(|_| !c.is_ascii_uppercase());
        let mut out = [0u8; N];
        for (byte, pair) in out.iter_mut().zip(text.chunks_exact(2)) {
            *byte = (digit(pair[0])? << 4 | digit(pair[1])?) as u8;
        }
        Some(out)
    }

    /// What `text` says, if it is JSON and nothing else.
    pub fn read(text: &[u8]) -> Result<Json, NotJson> {
        let text =
            std::str::from_utf8(text).map_err(|e| NotJson { what: "bytes that are not text", at: e.valid_up_to() })?;
        let mut reader = Reader { text: text.as_bytes(), at: 0 };
        reader.space();
        let value = reader.value(0)?;
        reader.space();
        match reader.at == reader.text.len() {
            true => Ok(value),
            false => Err(reader.wrong("something after the value")),
        }
    }

    /// The value as text: with no space in it that is not in a string.
    pub fn write(&self) -> String {
        let mut out = String::new();
        self.write_to(&mut out);
        out
    }

    fn write_to(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Int(n) => out.push_str(&n.to_string()),
            // (What is no number JSON has is said to be nothing.)
            Json::Float(x) if !x.is_finite() => out.push_str("null"),
            Json::Float(x) => {
                let text = format!("{x:?}");
                out.push_str(&text);
            }
            Json::Str(s) => write_str(s, out),
            Json::Array(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.write_to(out);
                }
                out.push(']');
            }
            Json::Object(members) => {
                out.push('{');
                for (i, (name, value)) in members.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_str(name, out);
                    out.push(':');
                    value.write_to(out);
                }
                out.push('}');
            }
        }
    }
}

fn write_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

struct Reader<'a> {
    text: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn wrong(&self, what: &'static str) -> NotJson {
        NotJson { what, at: self.at }
    }

    fn peek(&self) -> Option<u8> {
        self.text.get(self.at).copied()
    }

    fn space(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.at += 1;
        }
    }

    /// `word`, if it is next.
    fn word(&mut self, word: &str, value: Json) -> Result<Json, NotJson> {
        if !self.text[self.at..].starts_with(word.as_bytes()) {
            return Err(self.wrong("a value was expected"));
        }
        self.at += word.len();
        Ok(value)
    }

    fn value(&mut self, depth: usize) -> Result<Json, NotJson> {
        match self.peek() {
            None => Err(self.wrong("it ends where a value was expected")),
            Some(b'n') => self.word("null", Json::Null),
            Some(b't') => self.word("true", Json::Bool(true)),
            Some(b'f') => self.word("false", Json::Bool(false)),
            Some(b'"') => self.string().map(Json::Str),
            Some(b'-' | b'0'..=b'9') => self.number(),
            Some(b'[' | b'{') if depth >= MAX_DEPTH => Err(self.wrong("it is too deep")),
            Some(b'[') => {
                self.at += 1;
                let mut items = Vec::new();
                self.space();
                if self.peek() == Some(b']') {
                    self.at += 1;
                    return Ok(Json::Array(items));
                }
                loop {
                    self.space();
                    items.push(self.value(depth + 1)?);
                    self.space();
                    match self.peek() {
                        Some(b',') => self.at += 1,
                        Some(b']') => {
                            self.at += 1;
                            return Ok(Json::Array(items));
                        }
                        _ => return Err(self.wrong("a comma or the end of the array was expected")),
                    }
                }
            }
            Some(b'{') => {
                self.at += 1;
                let mut members: Vec<(String, Json)> = Vec::new();
                self.space();
                if self.peek() == Some(b'}') {
                    self.at += 1;
                    return Ok(Json::Object(members));
                }
                loop {
                    self.space();
                    if self.peek() != Some(b'"') {
                        return Err(self.wrong("a member's name was expected"));
                    }
                    let named = self.at;
                    let name = self.string()?;
                    if members.iter().any(|(n, _)| *n == name) {
                        return Err(NotJson { what: "a member is named twice", at: named });
                    }
                    self.space();
                    if self.peek() != Some(b':') {
                        return Err(self.wrong("a colon was expected after a member's name"));
                    }
                    self.at += 1;
                    self.space();
                    let value = self.value(depth + 1)?;
                    members.push((name, value));
                    self.space();
                    match self.peek() {
                        Some(b',') => self.at += 1,
                        Some(b'}') => {
                            self.at += 1;
                            return Ok(Json::Object(members));
                        }
                        _ => return Err(self.wrong("a comma or the end of the object was expected")),
                    }
                }
            }
            Some(_) => Err(self.wrong("a value was expected")),
        }
    }

    /// Four hex digits, after `\u`.
    fn four(&mut self) -> Result<u32, NotJson> {
        let digits = self.text.get(self.at..self.at + 4).ok_or(self.wrong("four hex digits were expected"))?;
        let mut n = 0;
        for d in digits {
            n = n << 4 | (*d as char).to_digit(16).ok_or(self.wrong("four hex digits were expected"))?;
        }
        self.at += 4;
        Ok(n)
    }

    fn string(&mut self) -> Result<String, NotJson> {
        self.at += 1;
        let mut out = String::new();
        loop {
            let from = self.at;
            // As much as is written as it is: taken whole.
            while matches!(self.peek(), Some(c) if c != b'"' && c != b'\\' && c >= 0x20) {
                self.at += 1;
            }
            // (The text was text before any of it was read, and what
            // ends a run here is one byte of ASCII: so a run is text.)
            out.push_str(
                std::str::from_utf8(&self.text[from..self.at]).map_err(|_| self.wrong("a string is not text"))?,
            );
            match self.peek() {
                None => return Err(self.wrong("a string does not end")),
                Some(b'"') => {
                    self.at += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.at += 1;
                    let c = self.peek().ok_or(self.wrong("a string does not end"))?;
                    self.at += 1;
                    match c {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let first = self.four()?;
                            let code = match first {
                                // The first half of a pair: the second
                                // must follow.
                                0xD800..=0xDBFF => {
                                    if !self.text[self.at..].starts_with(b"\\u") {
                                        return Err(self.wrong("half of a pair of escapes"));
                                    }
                                    self.at += 2;
                                    let second = self.four()?;
                                    if !(0xDC00..=0xDFFF).contains(&second) {
                                        return Err(self.wrong("half of a pair of escapes"));
                                    }
                                    0x10000 + ((first - 0xD800) << 10) + (second - 0xDC00)
                                }
                                0xDC00..=0xDFFF => return Err(self.wrong("half of a pair of escapes")),
                                other => other,
                            };
                            out.push(char::from_u32(code).ok_or(self.wrong("an escape that is no character"))?);
                        }
                        _ => {
                            self.at -= 1;
                            return Err(self.wrong("an escape that is not one"));
                        }
                    }
                }
                Some(_) => return Err(self.wrong("a control character in a string")),
            }
        }
    }

    fn digits(&mut self) -> usize {
        let from = self.at;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.at += 1;
        }
        self.at - from
    }

    fn number(&mut self) -> Result<Json, NotJson> {
        let from = self.at;
        if self.peek() == Some(b'-') {
            self.at += 1;
        }
        let whole = self.at;
        match self.digits() {
            0 => return Err(self.wrong("a digit was expected")),
            n if n > 1 && self.text[whole] == b'0' => {
                self.at = whole;
                return Err(self.wrong("a number begins with a zero"));
            }
            _ => {}
        }
        let mut is_whole = true;
        if self.peek() == Some(b'.') {
            self.at += 1;
            is_whole = false;
            if self.digits() == 0 {
                return Err(self.wrong("a digit was expected after the point"));
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.at += 1;
            is_whole = false;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.at += 1;
            }
            if self.digits() == 0 {
                return Err(self.wrong("a digit was expected in the exponent"));
            }
        }
        let text = std::str::from_utf8(&self.text[from..self.at]).expect("digits and signs");
        let too_large = NotJson { what: "a number too large to keep", at: from };
        match is_whole {
            true => text.parse().map(Json::Int).map_err(|_| too_large),
            false => text.parse::<f64>().ok().filter(|x| x.is_finite()).map(Json::Float).ok_or(too_large),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(text: &str) -> Result<Json, NotJson> {
        Json::read(text.as_bytes())
    }

    fn wrong(text: &str) -> (&'static str, usize) {
        match read(text) {
            Err(e) => (e.what, e.at),
            Ok(value) => panic!("{text:?} was read as {value:?}"),
        }
    }

    /// Every kind of value is read, with space wherever it may be, and
    /// written back as the same value.
    #[test]
    fn what_is_written_is_what_is_read() {
        let text = r#" { "height" : 12 , "tip":"00ff", "peers":[ ] ,"ok":true,"none":null,
            "fees": [1, -2, 3.5, 1e3, -0.25E-2, 0, -0],"nested":{"a":{"b":[[],{}]}} } "#;
        let value = read(text).unwrap();
        assert_eq!(value.get("height"), Some(&Json::Int(12)));
        assert_eq!(value.get("tip").and_then(Json::as_str), Some("00ff"));
        assert_eq!(value.get("peers"), Some(&Json::Array(vec![])));
        assert_eq!((value.get("ok").and_then(Json::as_bool), value.get("none")), (Some(true), Some(&Json::Null)));
        let fees = value.get("fees").and_then(Json::as_array).unwrap();
        let want = [Json::Int(1), Json::Int(-2), Json::Float(3.5), Json::Float(1000.0), Json::Float(-0.0025)];
        assert_eq!(fees[..5], want);
        assert_eq!((&fees[5], &fees[6]), (&Json::Int(0), &Json::Int(0)));
        assert_eq!(value.get("missing"), None);
        let written = value.write();
        assert_eq!(
            written,
            r#"{"height":12,"tip":"00ff","peers":[],"ok":true,"none":null,"fees":[1,-2,3.5,1000.0,-0.0025,0,0],"nested":{"a":{"b":[[],{}]}}}"#
        );
        assert_eq!(read(&written).unwrap(), value);
        // Each alone, too.
        for (text, value) in
            [("null", Json::Null), ("false", Json::Bool(false)), ("7", Json::Int(7)), ("\"\"", Json::str(""))]
        {
            assert_eq!(read(text).unwrap(), value);
            assert_eq!(value.write(), text);
        }
    }

    /// A string is read with its escapes, and written with those it
    /// needs.
    #[test]
    fn strings_and_their_escapes() {
        let read_str = |text: &str| read(text).unwrap().as_str().unwrap().to_string();
        assert_eq!(read_str(r#""a\"b\\c\/d\b\f\n\r\t""#), "a\"b\\c/d\u{8}\u{c}\n\r\t");
        assert_eq!(read_str(r#""\u0041\u00e9\u20ac""#), "A\u{e9}\u{20ac}");
        // A pair of escapes is one character, beyond the first 65,536.
        assert_eq!(read_str(r#""\ud83d\ude00""#), "\u{1f600}");
        assert_eq!(read_str("\"caf\u{e9} \u{1f600}\""), "caf\u{e9} \u{1f600}");
        let all = Json::str("quote \" slash \\ line \n tab \t bell \u{7} caf\u{e9} \u{1f600}");
        assert_eq!(all.write(), "\"quote \\\" slash \\\\ line \\n tab \\t bell \\u0007 caf\u{e9} \u{1f600}\"");
        assert_eq!(read(&all.write()).unwrap(), all);
        for (text, what) in [
            ("\"abc", "a string does not end"),
            ("\"a\\", "a string does not end"),
            ("\"a\nb\"", "a control character in a string"),
            ("\"\\x\"", "an escape that is not one"),
            ("\"\\u12g4\"", "four hex digits were expected"),
            ("\"\\u12\"", "four hex digits were expected"),
            ("\"\\ud83d\"", "half of a pair of escapes"),
            ("\"\\ud83d\\u0041\"", "half of a pair of escapes"),
            ("\"\\ude00\"", "half of a pair of escapes"),
        ] {
            assert_eq!(wrong(text).0, what, "{text}");
        }
        assert_eq!(Json::read(b"\"\xff\"").unwrap_err().what, "bytes that are not text");
    }

    /// Whole numbers are kept whole, of any size a count may have;
    /// amounts are strings of digits, and hashes hex.
    #[test]
    fn numbers_amounts_and_hashes() {
        assert_eq!(read("18446744073709551615").unwrap().as_u64(), Some(u64::MAX));
        assert_eq!(read("18446744073709551616").unwrap().as_u64(), None);
        assert_eq!(read("-1").unwrap().as_u64(), None);
        assert_eq!(read("1.0").unwrap().as_u64(), None);
        assert_eq!(Json::int(u64::MAX).write(), "18446744073709551615");
        assert_eq!(Json::int(-5i64).write(), "-5");
        assert_eq!((Json::Float(f64::NAN).write(), Json::Float(f64::INFINITY).write()), ("null".into(), "null".into()));
        // An amount of all 128 bits, there and back.
        assert_eq!(Json::amount(u128::MAX).write(), "\"340282366920938463463374607431768211455\"");
        assert_eq!(Json::amount(u128::MAX).as_amount(), Some(u128::MAX));
        assert_eq!(Json::amount(0).as_amount(), Some(0));
        for not in ["", "12a", "-1", "+1", " 1", "1.0", "340282366920938463463374607431768211456", "0x10"] {
            assert_eq!(Json::str(not).as_amount(), None, "{not:?}");
        }
        assert_eq!(Json::Int(5).as_amount(), None);
        // Hex, of the length asked for and in small letters.
        assert_eq!(Json::hex(&[0, 0xab, 0xff]).write(), "\"00abff\"");
        assert_eq!(Json::hex(&[0, 0xab, 0xff]).as_hex::<3>(), Some([0, 0xab, 0xff]));
        assert_eq!(Json::str("00abff").as_hex::<2>(), None);
        assert_eq!(Json::str("00ABFF").as_hex::<3>(), None);
        assert_eq!(Json::str("00abfg").as_hex::<3>(), None);
        for (text, what) in [
            ("01", "a number begins with a zero"),
            ("-", "a digit was expected"),
            ("1.", "a digit was expected after the point"),
            ("1e", "a digit was expected in the exponent"),
            ("1e+", "a digit was expected in the exponent"),
            (".5", "a value was expected"),
            ("+1", "a value was expected"),
            ("1e999", "a number too large to keep"),
            ("999999999999999999999999999999999999999999", "a number too large to keep"),
        ] {
            assert_eq!(wrong(text).0, what, "{text}");
        }
    }

    /// What is not quite JSON is refused, with where.
    #[test]
    fn what_is_not_json_is_refused() {
        for (text, what, at) in [
            ("", "it ends where a value was expected", 0),
            ("   ", "it ends where a value was expected", 3),
            ("nul", "a value was expected", 0),
            ("True", "a value was expected", 0),
            ("'a'", "a value was expected", 0),
            ("[1,]", "a value was expected", 3),
            ("[1 2]", "a comma or the end of the array was expected", 3),
            ("[1", "a comma or the end of the array was expected", 2),
            ("{\"a\":1,}", "a member's name was expected", 7),
            ("{a:1}", "a member's name was expected", 1),
            ("{\"a\" 1}", "a colon was expected after a member's name", 5),
            ("{\"a\":1 \"b\":2}", "a comma or the end of the object was expected", 7),
            ("{\"a\":1,\"a\":2}", "a member is named twice", 7),
            ("1 2", "something after the value", 2),
            ("{} x", "something after the value", 3),
            ("// no\n1", "a value was expected", 0),
        ] {
            assert_eq!(wrong(text), (what, at), "{text}");
        }
    }

    /// No deeper than it may be: so that nobody makes the reader go as
    /// deep as they care to write brackets.
    #[test]
    fn no_deeper_than_it_may_be() {
        let deep = |n: usize| format!("{}{}", "[".repeat(n), "]".repeat(n));
        assert!(read(&deep(MAX_DEPTH)).is_ok());
        assert_eq!(wrong(&deep(MAX_DEPTH + 1)), ("it is too deep", MAX_DEPTH));
        assert_eq!(wrong(&"[".repeat(100_000)).0, "it is too deep");
        let objects = format!("{}1{}", "{\"a\":".repeat(MAX_DEPTH + 1), "}".repeat(MAX_DEPTH + 1));
        assert_eq!(wrong(&objects).0, "it is too deep");
    }

    /// An object is made and asked in the order it was written.
    #[test]
    fn an_object_keeps_its_order() {
        let made = Json::object([("z", Json::int(1u8)), ("a", Json::str("two")), ("m", Json::Array(vec![Json::Null]))]);
        assert_eq!(made.write(), r#"{"z":1,"a":"two","m":[null]}"#);
        assert_eq!(made.get("a").and_then(Json::as_str), Some("two"));
        assert_eq!((Json::Null.get("a"), made.as_str(), made.as_array()), (None, None, None));
    }
}
