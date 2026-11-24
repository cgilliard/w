//! HTTP: as much of it as the node's ports speak, and no more.
//!
//! The node is asked things at two ports, by the wallet and by the
//! programs that work for it, and HTTP is how: so that a script, or
//! `curl`, can ask as well. What is here is HTTP/1.1 at its plainest,
//! written out, and whatever is not that is refused by its number:
//!
//! * A request is a line, headers, and a body of the length its
//!   `Content-Length` says. A body sent in chunks is not taken (501):
//!   nothing here sends one.
//! * The head of a request is of [`MAX_HEAD`] bytes at the most (431),
//!   and its body of what the port allows (413), which is said before
//!   any of the body is read.
//! * A port that has a secret takes no request without it
//!   (`Authorization: Bearer`, 401), and reads no body of one.
//! * So many connections are open at once, and no more (503); one on
//!   which nothing comes for a while is closed.
//! * There is no TLS. A port is for the machine it is on; from another,
//!   it is reached through a tunnel, or a proxy that has TLS.
//!
//! A connection is kept between requests, and each has a thread of its
//! own for as long as it is open. So an answer may be a long time
//! coming: whoever is asked may wait until there is something to say,
//! which is how a program that works for the node is told of work.
//!
//! [`Server`] is the port; [`Client`] is whoever asks at one.

use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crate::json::Json;

/// The most a request's line and headers may come to, in bytes; and a
/// response's, to whoever asks.
pub const MAX_HEAD: usize = 8 << 10;

/// What something is, as HTTP says it: JSON, or bytes as they are.
pub const JSON: &str = "application/json";
pub const BYTES: &str = "application/octet-stream";

/// A request, as whoever answers it has it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    /// `GET`, `POST`, `PUT` or `DELETE`.
    pub method: String,
    /// The path, with what was written as `%41` an `A`.
    pub path: String,
    /// What follows the path's `?`, a name and a value at a time.
    pub query: Vec<(String, String)>,
    /// The headers, their names in small letters.
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

impl Request {
    /// The header `name` (in small letters), if it was sent.
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers.iter().find(|(n, _)| n == name).map(|(_, v)| v.as_str())
    }

    /// The value of `name` in the query, if it is there.
    pub fn asked(&self, name: &str) -> Option<&str> {
        self.query.iter().find(|(n, _)| n == name).map(|(_, v)| v.as_str())
    }

    /// The body as JSON, if it is that.
    pub fn json(&self) -> Option<Json> {
        Json::read(&self.body).ok()
    }
}

/// An answer: its number, what its body is, and the body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Response {
    pub status: u16,
    pub kind: String,
    pub body: Vec<u8>,
}

impl Response {
    /// `value`, with the number `status`.
    pub fn json(status: u16, value: &Json) -> Response {
        Response { status, kind: JSON.into(), body: value.write().into_bytes() }
    }

    /// `body` as it is, and 200.
    pub fn bytes(body: Vec<u8>) -> Response {
        Response { status: 200, kind: BYTES.into(), body }
    }

    /// What is wrong, as `{"error": why}`, with the number `status`.
    pub fn error(status: u16, why: &str) -> Response {
        Response::json(status, &Json::object([("error", Json::str(why))]))
    }

    /// Whether the number is one of those that say all went well.
    pub fn ok(&self) -> bool {
        (200..300).contains(&self.status)
    }

    /// The body as JSON, if it is that.
    pub fn as_json(&self) -> Option<Json> {
        Json::read(&self.body).ok()
    }
}

/// What a number is called.
fn reason(status: u16) -> &'static str {
    match status {
        200 => "OK",
        201 => "Created",
        202 => "Accepted",
        204 => "No Content",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        408 => "Request Timeout",
        409 => "Conflict",
        413 => "Content Too Large",
        431 => "Request Header Fields Too Large",
        500 => "Internal Server Error",
        501 => "Not Implemented",
        503 => "Service Unavailable",
        _ => "Unknown",
    }
}

/// What a port is held to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// The largest body of a request, in bytes.
    pub body: usize,
    /// Connections open at once.
    pub connections: usize,
    /// How long a connection may send nothing, between requests or in
    /// the middle of one, before it is closed. (Not how long an answer
    /// may take: that is for whoever answers.)
    pub idle: Duration,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits { body: 1 << 20, connections: 64, idle: Duration::from_secs(60) }
    }
}

/// `%41` as `A`, and so on: None if a `%` is not followed by two hex
/// digits, or what comes of it is not text.
fn unescape(text: &str, plus_is_space: bool) -> Option<String> {
    let (bytes, mut out, mut at) = (text.as_bytes(), Vec::with_capacity(text.len()), 0);
    while at < bytes.len() {
        match bytes[at] {
            b'%' => {
                let hex = bytes.get(at + 1..at + 3)?;
                let digit = |c: u8| (c as char).to_digit(16);
                out.push((digit(hex[0])? << 4 | digit(hex[1])?) as u8);
                at += 3;
            }
            b'+' if plus_is_space => {
                out.push(b' ');
                at += 1;
            }
            c => {
                out.push(c);
                at += 1;
            }
        }
    }
    String::from_utf8(out).ok()
}

/// `text` as it is written in a path or a query: letters, digits and
/// `-._~` as they are, and every other byte as `%` and two hex digits.
pub fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for b in text.bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' => out.push(b as char),
            other => out.push_str(&format!("%{other:02X}")),
        }
    }
    out
}

/// Whether two secrets are the same, in a time that does not say where
/// they first differ.
fn same(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && a.iter().zip(b).fold(0u8, |d, (x, y)| d | (x ^ y)) == 0
}

/// A request that is refused before anyone is asked: the number, why,
/// and whether the connection can go on after it is said.
struct Refused {
    status: u16,
    why: &'static str,
    close: bool,
}

fn refused(status: u16, why: &'static str) -> Refused {
    Refused { status, why, close: true }
}

/// A connection: its stream, and what has been read from it and not
/// yet made anything of.
struct Connection {
    stream: TcpStream,
    read: Vec<u8>,
}

impl Connection {
    /// More from the stream, onto what is read: how many bytes. Nothing
    /// is the stream's end.
    fn more(&mut self) -> io::Result<usize> {
        let mut some = [0u8; 16 << 10];
        let n = self.stream.read(&mut some)?;
        self.read.extend_from_slice(&some[..n]);
        Ok(n)
    }

    /// The next head, to its blank line and without it: none if the
    /// stream ended before any of one came. It is to be here whole by
    /// `until`, and of [`MAX_HEAD`] bytes at the most.
    fn head(&mut self, until: Instant) -> io::Result<Option<String>> {
        loop {
            let found = self.read.windows(4).position(|w| w == b"\r\n\r\n");
            if found.is_some_and(|end| end > MAX_HEAD) {
                return Err(io::ErrorKind::FileTooLarge.into());
            }
            if let Some(end) = found {
                let head: Vec<u8> = self.read.drain(..end + 4).take(end).collect();
                return String::from_utf8(head).map(Some).map_err(|_| io::ErrorKind::InvalidData.into());
            }
            if self.read.len() > MAX_HEAD {
                return Err(io::ErrorKind::FileTooLarge.into());
            }
            if Instant::now() >= until {
                return Err(io::ErrorKind::TimedOut.into());
            }
            if self.more()? == 0 {
                return match self.read.is_empty() {
                    true => Ok(None),
                    false => Err(io::ErrorKind::UnexpectedEof.into()),
                };
            }
        }
    }

    /// A body of `len` bytes: taken as it comes, so that nobody has
    /// room made for a body they do not then send.
    fn body(&mut self, len: usize) -> io::Result<Vec<u8>> {
        while self.read.len() < len {
            if self.more()? == 0 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
        }
        Ok(self.read.drain(..len).collect())
    }
}

/// The headers of a head's lines after the first: names in small
/// letters. None if a line is not a header.
fn headers<'a>(lines: impl Iterator<Item = &'a str>) -> Option<Vec<(String, String)>> {
    let mut all = Vec::new();
    for line in lines {
        let (name, value) = line.split_once(':')?;
        let named = !name.is_empty() && name.bytes().all(|b| b.is_ascii_graphic());
        if !named {
            return None;
        }
        all.push((name.to_ascii_lowercase(), value.trim().to_string()));
    }
    Some(all)
}

/// The length a body is said to have: nothing said is nothing; None if
/// it is said twice, or is not a number.
fn length(headers: &[(String, String)]) -> Option<usize> {
    let mut said = headers.iter().filter(|(n, _)| n == "content-length");
    match (said.next(), said.next()) {
        (None, _) => Some(0),
        (Some((_, v)), None) if !v.is_empty() && v.bytes().all(|b| b.is_ascii_digit()) => v.parse().ok(),
        _ => None,
    }
}

/// What whoever answers is.
type Answering = dyn Fn(&Request) -> Response + Send + Sync;

/// What a port's connections share.
struct Port {
    limits: Limits,
    secret: Option<String>,
    answer: Box<Answering>,
    open: AtomicUsize,
    stopping: AtomicBool,
}

impl Port {
    /// The next request on a connection: none when it has ended, and
    /// whether the connection is to go on after it is answered.
    fn request(&self, c: &mut Connection) -> Result<Option<(Request, bool)>, Refused> {
        let head = match c.head(Instant::now() + self.limits.idle) {
            Ok(Some(head)) => head,
            Ok(None) => return Ok(None),
            Err(e) if e.kind() == io::ErrorKind::FileTooLarge => {
                return Err(refused(431, "the request's head is too long"));
            }
            Err(e) if e.kind() == io::ErrorKind::InvalidData => {
                return Err(refused(400, "the request's head is not text"));
            }
            // (Nothing came, or the other end went: nothing is said.)
            Err(_) => return Ok(None),
        };
        let mut lines = head.split("\r\n");
        let first: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        let [method, target, version] = first[..] else {
            return Err(refused(400, "the request's first line is not one"));
        };
        let newer = match version {
            "HTTP/1.1" => true,
            "HTTP/1.0" => false,
            _ => return Err(refused(400, "the request's first line is not one")),
        };
        if !matches!(method, "GET" | "POST" | "PUT" | "DELETE") {
            return Err(refused(405, "GET, POST, PUT and DELETE are taken"));
        }
        let headers = headers(lines).ok_or(refused(400, "a header is not one"))?;
        let find = |name: &str| headers.iter().find(|(n, _)| n == name).map(|(_, v)| v.as_str());
        // Before anything else of it is read: whether it may ask at all.
        if let Some(secret) = &self.secret {
            let given = find("authorization").and_then(|v| v.strip_prefix("Bearer "));
            if !given.is_some_and(|given| same(given.as_bytes(), secret.as_bytes())) {
                return Err(refused(401, "this port's secret is wanted"));
            }
        }
        let (path, query) = target.split_once('?').unwrap_or((target, ""));
        let path = unescape(path, false).filter(|p| p.starts_with('/')).ok_or(refused(400, "the path is not one"))?;
        let mut asked = Vec::new();
        for pair in query.split('&').filter(|p| !p.is_empty()) {
            let (name, value) = pair.split_once('=').unwrap_or((pair, ""));
            let both = unescape(name, true).zip(unescape(value, true));
            asked.push(both.ok_or(refused(400, "the query is not one"))?);
        }
        if find("transfer-encoding").is_some() {
            return Err(refused(501, "a body is taken by its Content-Length alone"));
        }
        let len = length(&headers).ok_or(refused(400, "the Content-Length is not one"))?;
        if len > self.limits.body {
            return Err(refused(413, "the body is larger than this port takes"));
        }
        // (Whoever waits to be told to send its body is told.)
        if len > 0 && find("expect").is_some_and(|v| v.eq_ignore_ascii_case("100-continue")) {
            let _ = c.stream.write_all(b"HTTP/1.1 100 Continue\r\n\r\n");
        }
        let Ok(body) = c.body(len) else { return Ok(None) };
        let goes_on = match find("connection").map(str::to_ascii_lowercase).as_deref() {
            Some("close") => false,
            Some("keep-alive") => true,
            _ => newer,
        };
        let request = Request { method: method.to_string(), path, query: asked, headers, body };
        Ok(Some((request, goes_on)))
    }

    /// A connection's life: its requests, one after another, each
    /// answered.
    fn serve(&self, stream: TcpStream) {
        let _ = stream.set_read_timeout(Some(self.limits.idle));
        let _ = stream.set_write_timeout(Some(self.limits.idle));
        let _ = stream.set_nodelay(true);
        let mut c = Connection { stream, read: Vec::new() };
        loop {
            let (response, goes_on) = match self.request(&mut c) {
                Ok(None) => return,
                Ok(Some((request, goes_on))) => {
                    // (Whoever answers may panic: that is its answer's
                    // failing, not the port's.)
                    let answered = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| (self.answer)(&request)));
                    (answered.unwrap_or_else(|_| Response::error(500, "the request could not be answered")), goes_on)
                }
                Err(no) => (Response::error(no.status, no.why), !no.close),
            };
            let goes_on = goes_on && !self.stopping.load(Ordering::Relaxed);
            if send(&mut c.stream, &response, goes_on).is_err() || !goes_on {
                return;
            }
        }
    }
}

/// Writes `response` to `stream`, and says whether the connection goes
/// on after it.
fn send(stream: &mut TcpStream, response: &Response, goes_on: bool) -> io::Result<()> {
    let mut head = format!("HTTP/1.1 {} {}\r\n", response.status, reason(response.status));
    head += &format!("Content-Type: {}\r\nContent-Length: {}\r\n", response.kind, response.body.len());
    if response.status == 401 {
        head += "WWW-Authenticate: Bearer\r\n";
    }
    head += if goes_on { "Connection: keep-alive\r\n\r\n" } else { "Connection: close\r\n\r\n" };
    stream.write_all(head.as_bytes())?;
    stream.write_all(&response.body)?;
    stream.flush()
}

/// A port that is listened at: its requests answered, each connection
/// on a thread of its own, until it is stopped.
pub struct Server {
    addr: SocketAddr,
    port: Arc<Port>,
    accepting: Option<std::thread::JoinHandle<()>>,
}

impl Server {
    /// Listens at `at`, and has every request answered by `answer`:
    /// those that come with `secret`, where there is one. An error if
    /// the address cannot be listened at.
    pub fn start(
        at: SocketAddr,
        limits: Limits,
        secret: Option<String>,
        answer: impl Fn(&Request) -> Response + Send + Sync + 'static,
    ) -> io::Result<Server> {
        let listener = TcpListener::bind(at)?;
        let addr = listener.local_addr()?;
        let port = Arc::new(Port {
            limits,
            secret,
            answer: Box::new(answer),
            open: AtomicUsize::new(0),
            stopping: AtomicBool::new(false),
        });
        let accepting = {
            let port = Arc::clone(&port);
            std::thread::Builder::new().name("port".into()).spawn(move || accept(&listener, &port))?
        };
        Ok(Server { addr, port, accepting: Some(accepting) })
    }

    /// Where it listens: the port it was given, if it was told to take
    /// any (port 0).
    pub fn addr(&self) -> SocketAddr {
        self.addr
    }

    /// Connections open now.
    pub fn open(&self) -> usize {
        self.port.open.load(Ordering::Relaxed)
    }

    /// Listens no more. Connections that are open end when the request
    /// they are in is answered, or when nothing more comes on them.
    pub fn stop(mut self) {
        self.end();
    }

    fn end(&mut self) {
        let Some(accepting) = self.accepting.take() else { return };
        self.port.stopping.store(true, Ordering::Relaxed);
        // (Whoever is waiting for a connection is given one, to see
        // that it is to stop.)
        let _ = TcpStream::connect_timeout(&self.addr, Duration::from_secs(1));
        let _ = accepting.join();
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.end();
    }
}

/// One fewer connection is open, when this is dropped.
struct Open<'a>(&'a AtomicUsize);

impl Drop for Open<'_> {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::Relaxed);
    }
}

fn accept(listener: &TcpListener, port: &Arc<Port>) {
    for stream in listener.incoming() {
        if port.stopping.load(Ordering::Relaxed) {
            return;
        }
        let Ok(mut stream) = stream else { continue };
        // One more than there may be is told so, and closed.
        if port.open.fetch_add(1, Ordering::Relaxed) >= port.limits.connections {
            port.open.fetch_sub(1, Ordering::Relaxed);
            let _ = stream.set_write_timeout(Some(Duration::from_secs(1)));
            let _ = send(&mut stream, &Response::error(503, "too many connections are open"), false);
            continue;
        }
        let serving = Arc::clone(port);
        let begun = std::thread::Builder::new().name("connection".into()).spawn(move || {
            let _open = Open(&serving.open);
            serving.serve(stream);
        });
        if begun.is_err() {
            port.open.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

/// Whoever asks at a port: one connection, kept between requests and
/// made again when it has gone.
pub struct Client {
    addr: SocketAddr,
    secret: Option<String>,
    /// How long an answer may be waited for, and the largest it may be.
    wait: Duration,
    most: usize,
    connection: Option<Connection>,
}

impl Client {
    /// For the port at `addr`, with its secret if it has one. An answer
    /// is waited for a minute, and may be of 64 MB, unless told
    /// otherwise ([`Client::waiting`], [`Client::taking`]).
    pub fn new(addr: SocketAddr, secret: Option<String>) -> Client {
        Client { addr, secret, wait: Duration::from_secs(60), most: 64 << 20, connection: None }
    }

    /// The same, waiting `wait` for an answer: longer, for one that is
    /// a long time coming.
    pub fn waiting(self, wait: Duration) -> Client {
        Client { wait, ..self }
    }

    /// The same, taking answers of up to `most` bytes.
    pub fn taking(self, most: usize) -> Client {
        Client { most, ..self }
    }

    pub fn get(&mut self, target: &str) -> io::Result<Response> {
        self.send("GET", target, JSON, &[])
    }

    pub fn post(&mut self, target: &str, value: &Json) -> io::Result<Response> {
        self.send("POST", target, JSON, value.write().as_bytes())
    }

    pub fn post_bytes(&mut self, target: &str, body: &[u8]) -> io::Result<Response> {
        self.send("POST", target, BYTES, body)
    }

    /// Asks, and has the answer. `target` is the path and the query, as
    /// they are written ([`escape`]).
    ///
    /// Where the connection kept from the request before turns out to
    /// have gone, before anything of an answer came, a new one is made
    /// and the request sent again, once.
    pub fn send(&mut self, method: &str, target: &str, kind: &str, body: &[u8]) -> io::Result<Response> {
        let kept = self.connection.is_some();
        match self.once(method, target, kind, body) {
            Err((e, true)) if kept => {
                let _ = e;
                self.once(method, target, kind, body).map_err(|(e, _)| e)
            }
            other => other.map_err(|(e, _)| e),
        }
    }

    /// One try. An error says whether nothing of an answer had come: so
    /// that the request may be sent again.
    fn once(&mut self, method: &str, target: &str, kind: &str, body: &[u8]) -> Result<Response, (io::Error, bool)> {
        let mut c = match self.connection.take() {
            Some(c) => c,
            None => {
                let stream = TcpStream::connect_timeout(&self.addr, self.wait).map_err(|e| (e, false))?;
                let _ = stream.set_nodelay(true);
                Connection { stream, read: Vec::new() }
            }
        };
        let _ = c.stream.set_read_timeout(Some(self.wait));
        let _ = c.stream.set_write_timeout(Some(self.wait));
        let mut head = format!("{method} {target} HTTP/1.1\r\nHost: {}\r\n", self.addr);
        if let Some(secret) = &self.secret {
            head += &format!("Authorization: Bearer {secret}\r\n");
        }
        if !body.is_empty() || method != "GET" {
            head += &format!("Content-Type: {kind}\r\nContent-Length: {}\r\n", body.len());
        }
        head += "\r\n";
        let sent =
            c.stream.write_all(head.as_bytes()).and_then(|_| c.stream.write_all(body)).and_then(|_| c.stream.flush());
        sent.map_err(|e| (e, true))?;
        let head = match c.head(Instant::now() + self.wait) {
            Ok(Some(head)) => head,
            // (It closed with nothing said: it had gone before this was
            // asked of it.)
            Ok(None) => return Err((io::ErrorKind::UnexpectedEof.into(), true)),
            Err(e) => {
                let nothing =
                    c.read.is_empty() && e.kind() != io::ErrorKind::TimedOut && e.kind() != io::ErrorKind::WouldBlock;
                return Err((e, nothing));
            }
        };
        let not = |what: &'static str| (io::Error::new(io::ErrorKind::InvalidData, what), false);
        let mut lines = head.split("\r\n");
        let first = lines.next().unwrap_or("");
        let status = first.strip_prefix("HTTP/1.1 ").or_else(|| first.strip_prefix("HTTP/1.0 "));
        let status: u16 =
            status.and_then(|rest| rest.get(..3)?.parse().ok()).ok_or(not("the answer's first line is not one"))?;
        let headers = headers(lines).ok_or(not("a header of the answer is not one"))?;
        let find = |name: &str| headers.iter().find(|(n, _)| n == name).map(|(_, v)| v.as_str());
        if find("transfer-encoding").is_some() {
            return Err(not("the answer's body is not by its Content-Length"));
        }
        let len = length(&headers).ok_or(not("the answer's Content-Length is not one"))?;
        if len > self.most {
            return Err(not("the answer is larger than is taken"));
        }
        let body = c.body(len).map_err(|e| (e, false))?;
        let kind = find("content-type").unwrap_or(BYTES).to_string();
        if !find("connection").is_some_and(|v| v.eq_ignore_ascii_case("close")) {
            self.connection = Some(c);
        }
        Ok(Response { status, kind, body })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Condvar, Mutex};

    fn local() -> SocketAddr {
        "127.0.0.1:0".parse().unwrap()
    }

    /// A port that says back what it was asked.
    fn echo(limits: Limits, secret: Option<&str>) -> Server {
        Server::start(local(), limits, secret.map(str::to_string), |r| match r.path.as_str() {
            "/bytes" => Response::bytes(r.body.clone()),
            "/panic" => panic!("whoever answers fails"),
            "/missing" => Response::error(404, "there is no such thing"),
            _ => {
                let pairs = |all: &[(String, String)]| {
                    Json::Array(
                        all.iter()
                            .map(|(n, v)| Json::Array(vec![Json::str(n.as_str()), Json::str(v.as_str())]))
                            .collect(),
                    )
                };
                let said = Json::object([
                    ("method", Json::str(r.method.as_str())),
                    ("path", Json::str(r.path.as_str())),
                    ("query", pairs(&r.query)),
                    ("body", r.json().unwrap_or(Json::Null)),
                    ("length", Json::int(r.body.len() as u64)),
                ]);
                Response::json(200, &said)
            }
        })
        .unwrap()
    }

    /// What is sent as it is, and all that comes back, until the other
    /// end closes or `wait` passes with nothing more.
    fn raw(addr: SocketAddr, sent: &[u8], wait: Duration) -> String {
        let mut stream = TcpStream::connect(addr).unwrap();
        stream.set_read_timeout(Some(wait)).unwrap();
        stream.write_all(sent).unwrap();
        let mut back = Vec::new();
        let _ = stream.read_to_end(&mut back);
        String::from_utf8_lossy(&back).into_owned()
    }

    fn short() -> Duration {
        Duration::from_millis(300)
    }

    /// What is asked is what whoever answers has, and what it says is
    /// what comes back: a path and a query, JSON, and bytes as they are.
    #[test]
    fn what_is_asked_is_answered() {
        let server = echo(Limits { body: 4 << 20, ..Limits::default() }, None);
        let mut client = Client::new(server.addr(), None);
        let target = format!("/names/{}?from=10&note={}&bare", escape("caf\u{e9} one"), escape("a&b=c d"));
        let back = client.get(&target).unwrap();
        assert!(back.ok() && back.kind == JSON);
        let said = back.as_json().unwrap();
        assert_eq!(said.get("method").and_then(Json::as_str), Some("GET"));
        assert_eq!(said.get("path").and_then(Json::as_str), Some("/names/caf\u{e9} one"));
        assert_eq!(said.get("query").unwrap().write(), r#"[["from","10"],["note","a&b=c d"],["bare",""]]"#);
        // JSON there, and back.
        let sent = Json::object([("amount", Json::amount(u128::MAX)), ("to", Json::str("tab1"))]);
        let said = client.post("/send", &sent).unwrap().as_json().unwrap();
        assert_eq!((said.get("method").and_then(Json::as_str), said.get("body")), (Some("POST"), Some(&sent)));
        // Bytes of every value, a few megabytes of them, as they are.
        let bytes: Vec<u8> = (0..3_000_000u32).map(|i| ((i * 31) >> 3) as u8).collect();
        let back = client.post_bytes("/bytes", &bytes).unwrap();
        assert!(back.kind == BYTES && back.body == bytes);
        // A number that says it did not go well is an answer too.
        let back = client.get("/missing").unwrap();
        assert_eq!((back.status, back.ok()), (404, false));
        assert_eq!(back.as_json().unwrap().get("error").and_then(Json::as_str), Some("there is no such thing"));
        // All of that on one connection.
        assert_eq!(server.open(), 1);
        assert_eq!(client.send("PUT", "/leaves/3", JSON, b"1").unwrap().status, 200);
        assert_eq!(client.send("DELETE", "/x", JSON, b"").unwrap().status, 200);
    }

    /// A connection is kept between requests, unless it is asked not to
    /// be; and one that sends nothing for a while is closed.
    #[test]
    fn a_connection_is_kept() {
        let server = echo(Limits { idle: short(), ..Limits::default() }, None);
        let two = b"GET /a HTTP/1.1\r\n\r\nGET /b HTTP/1.1\r\nConnection: close\r\n\r\n";
        let back = raw(server.addr(), two, Duration::from_secs(5));
        assert_eq!(back.matches("HTTP/1.1 200 OK\r\n").count(), 2);
        assert!(back.contains("\"path\":\"/a\"") && back.contains("\"path\":\"/b\""));
        assert!(back.contains("Connection: keep-alive\r\n") && back.ends_with("\"length\":0}"));
        // The older way closes unless it is asked to keep.
        let old = raw(server.addr(), b"GET /a HTTP/1.0\r\n\r\n", Duration::from_secs(5));
        assert!(old.contains("Connection: close\r\n") && old.matches("HTTP/1.1 200").count() == 1);
        // Nothing sent: closed, and nothing said.
        let began = Instant::now();
        assert_eq!(raw(server.addr(), b"", Duration::from_secs(5)), "");
        assert!(began.elapsed() < Duration::from_secs(3));
        // Whoever asks makes another connection when the one it kept
        // has been closed under it.
        let mut client = Client::new(server.addr(), None);
        assert!(client.get("/first").unwrap().ok());
        std::thread::sleep(3 * short());
        assert_eq!(server.open(), 0);
        assert!(client.get("/second").unwrap().ok());
    }

    /// A port with a secret takes nothing without it, and reads no body
    /// of what it does not take.
    #[test]
    fn a_secret_is_wanted() {
        let server = echo(Limits::default(), Some("s3cret"));
        for secret in [None, Some("wrong!"), Some("s3cre"), Some("s3crett"), Some("")] {
            let back = Client::new(server.addr(), secret.map(str::to_string)).get("/status").unwrap();
            assert_eq!(back.status, 401, "{secret:?}");
        }
        assert!(Client::new(server.addr(), Some("s3cret".into())).get("/status").unwrap().ok());
        let back = raw(server.addr(), b"POST /x HTTP/1.1\r\nContent-Length: 999999\r\n\r\n", Duration::from_secs(5));
        assert!(back.starts_with("HTTP/1.1 401 Unauthorized\r\n") && back.contains("WWW-Authenticate: Bearer\r\n"));
        assert!(back.contains("Connection: close\r\n"));
        // (Not by another scheme, nor in other letters.)
        let basic =
            raw(server.addr(), b"GET / HTTP/1.1\r\nAuthorization: Basic s3cret\r\n\r\n", Duration::from_secs(5));
        assert!(basic.starts_with("HTTP/1.1 401"));
        assert!(same(b"abc", b"abc") && !same(b"abc", b"abd") && !same(b"abc", b"ab") && same(b"", b""));
    }

    /// What is not a request this port takes is refused by its number,
    /// and the port goes on.
    #[test]
    fn what_is_not_taken_is_refused() {
        let server = echo(Limits { body: 1000, idle: short(), ..Limits::default() }, None);
        let long = format!("GET / HTTP/1.1\r\nX-Long: {}\r\n\r\n", "a".repeat(MAX_HEAD));
        for (sent, status) in [
            ("GARBAGE\r\n\r\n", "400 Bad Request"),
            ("GET /\r\n\r\n", "400 Bad Request"),
            ("GET / HTTP/2\r\n\r\n", "400 Bad Request"),
            ("GET nopath HTTP/1.1\r\n\r\n", "400 Bad Request"),
            ("GET /%zz HTTP/1.1\r\n\r\n", "400 Bad Request"),
            ("GET /%ff HTTP/1.1\r\n\r\n", "400 Bad Request"),
            ("GET /?a=%4 HTTP/1.1\r\n\r\n", "400 Bad Request"),
            ("GET / HTTP/1.1\r\nno colon here\r\n\r\n", "400 Bad Request"),
            ("GET / HTTP/1.1\r\n folded: x\r\n\r\n", "400 Bad Request"),
            ("POST / HTTP/1.1\r\nContent-Length: ten\r\n\r\n", "400 Bad Request"),
            ("POST / HTTP/1.1\r\nContent-Length: -1\r\n\r\n", "400 Bad Request"),
            ("POST / HTTP/1.1\r\nContent-Length: 1\r\nContent-Length: 1\r\n\r\nx", "400 Bad Request"),
            ("PATCH / HTTP/1.1\r\n\r\n", "405 Method Not Allowed"),
            ("HEAD / HTTP/1.1\r\n\r\n", "405 Method Not Allowed"),
            ("POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n", "501 Not Implemented"),
            ("POST / HTTP/1.1\r\nContent-Length: 1001\r\n\r\n", "413 Content Too Large"),
            (long.as_str(), "431 Request Header Fields Too Large"),
        ] {
            let back = raw(server.addr(), sent.as_bytes(), Duration::from_secs(5));
            let shown = &sent[..sent.len().min(60)];
            assert!(
                back.starts_with(&format!("HTTP/1.1 {status}\r\n")),
                "{shown:?}: {:?}",
                &back[..back.len().min(60)]
            );
            assert!(back.contains("Connection: close\r\n") && back.contains("{\"error\":\""), "{shown:?}");
        }
        // A body of the most it takes is taken; and one that stops
        // short is not waited for for ever.
        let most = format!("POST /a HTTP/1.1\r\nConnection: close\r\nContent-Length: 1000\r\n\r\n{}", "7".repeat(1000));
        assert!(raw(server.addr(), most.as_bytes(), Duration::from_secs(5)).contains("\"length\":1000"));
        assert_eq!(
            raw(server.addr(), b"POST /a HTTP/1.1\r\nContent-Length: 10\r\n\r\nabc", Duration::from_secs(5)),
            ""
        );
        // Whoever answers fails: that is said, and the next is answered.
        let mut client = Client::new(server.addr(), None);
        assert_eq!(client.get("/panic").unwrap().status, 500);
        assert!(client.get("/after").unwrap().ok());
    }

    /// Whoever waits to be told to send its body is told.
    #[test]
    fn a_body_is_asked_for() {
        let server = echo(Limits::default(), None);
        let mut stream = TcpStream::connect(server.addr()).unwrap();
        stream.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        stream
            .write_all(b"POST /a HTTP/1.1\r\nExpect: 100-continue\r\nConnection: close\r\nContent-Length: 2\r\n\r\n")
            .unwrap();
        let mut told = [0u8; 25];
        stream.read_exact(&mut told).unwrap();
        assert_eq!(&told, b"HTTP/1.1 100 Continue\r\n\r\n");
        stream.write_all(b"17").unwrap();
        let mut back = String::new();
        stream.read_to_string(&mut back).unwrap();
        assert!(back.starts_with("HTTP/1.1 200 OK\r\n") && back.contains("\"body\":17"));
    }

    /// So many connections are open at once, and one more is told so.
    #[test]
    fn no_more_connections_than_there_may_be() {
        let server = echo(Limits { connections: 2, ..Limits::default() }, None);
        let mut held: Vec<Client> = (0..2).map(|_| Client::new(server.addr(), None)).collect();
        for client in &mut held {
            assert!(client.get("/").unwrap().ok());
        }
        assert_eq!(server.open(), 2);
        let third = Client::new(server.addr(), None).get("/").unwrap();
        assert_eq!(third.status, 503);
        // One let go, and there is room again.
        held.pop();
        let until = Instant::now() + Duration::from_secs(5);
        while server.open() > 1 && Instant::now() < until {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(Client::new(server.addr(), None).get("/").unwrap().ok());
    }

    /// An answer may be a long time coming: whoever answers waits until
    /// there is something to say, and others are answered meanwhile.
    #[test]
    fn an_answer_may_wait() {
        let news = Arc::new((Mutex::new(None::<u64>), Condvar::new()));
        let waiting = Arc::clone(&news);
        let server = Server::start(local(), Limits::default(), None, move |r| match r.path.as_str() {
            "/job" => {
                let (job, told) = &*waiting;
                let mut job = job.lock().unwrap();
                while job.is_none() {
                    job = told.wait(job).unwrap();
                }
                Response::json(200, &Json::object([("job", Json::int(job.unwrap()))]))
            }
            _ => Response::json(200, &Json::Null),
        })
        .unwrap();
        let addr = server.addr();
        let asker = std::thread::spawn(move || Client::new(addr, None).get("/job").unwrap());
        // Others are answered while that one waits.
        let mut other = Client::new(addr, None);
        for _ in 0..20 {
            assert!(other.get("/status").unwrap().ok());
        }
        assert!(!asker.is_finished());
        *news.0.lock().unwrap() = Some(41);
        news.1.notify_all();
        assert_eq!(asker.join().unwrap().as_json().unwrap().get("job"), Some(&Json::Int(41)));
        // And whoever asks does not wait longer than it said it would.
        let mut hasty = Client::new(addr, None).waiting(short());
        *news.0.lock().unwrap() = None;
        let began = Instant::now();
        assert!(hasty.get("/job").is_err() && began.elapsed() < Duration::from_secs(3));
        *news.0.lock().unwrap() = Some(1);
        news.1.notify_all();
    }

    /// Stopped, it listens no more.
    #[test]
    fn stopped_it_listens_no_more() {
        let server = echo(Limits::default(), None);
        let addr = server.addr();
        assert!(Client::new(addr, None).get("/").unwrap().ok());
        server.stop();
        assert!(Client::new(addr, None).waiting(short()).get("/").is_err());
    }

    /// Whoever asks takes an answer by its length alone, of no more
    /// than it said it would take, and says what is wrong with one
    /// that is not an answer.
    #[test]
    fn an_answer_that_is_not_one() {
        let said = |answer: &'static [u8]| {
            let listener = TcpListener::bind(local()).unwrap();
            let addr = listener.local_addr().unwrap();
            let serving = std::thread::spawn(move || {
                let (mut stream, _) = listener.accept().unwrap();
                let mut asked = [0u8; 4096];
                let _ = stream.read(&mut asked);
                let _ = stream.write_all(answer);
            });
            let back = Client::new(addr, None).waiting(short()).taking(100).get("/");
            serving.join().unwrap();
            back.map(|r| (r.status, r.body)).map_err(|e| e.to_string())
        };
        assert_eq!(said(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi"), Ok((200, b"hi".to_vec())));
        assert_eq!(said(b"HTTP/1.1 204 No Content\r\n\r\n"), Ok((204, vec![])));
        assert_eq!(
            said(b"HTTP/1.1 200 OK\r\nContent-Length: 101\r\n\r\n").unwrap_err(),
            "the answer is larger than is taken"
        );
        assert_eq!(
            said(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n").unwrap_err(),
            "the answer's body is not by its Content-Length"
        );
        assert_eq!(said(b"SSH-2.0-OpenSSH\r\n\r\n").unwrap_err(), "the answer's first line is not one");
        assert_eq!(said(b"HTTP/1.1 OK\r\n\r\n").unwrap_err(), "the answer's first line is not one");
        assert!(said(b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhi").is_err());
        assert!(said(b"").is_err());
    }

    /// Paths and queries are written so that anything can be in them.
    #[test]
    fn anything_can_be_in_a_path() {
        assert_eq!(escape("az09-._~"), "az09-._~");
        assert_eq!(escape("a b/c?d=e&f%"), "a%20b%2Fc%3Fd%3De%26f%25");
        for text in ["", "plain", "a b/c?d=e&f%+", "caf\u{e9} \u{1f600}", "\n\t\0"] {
            assert_eq!(unescape(&escape(text), true).as_deref(), Some(text));
        }
        assert_eq!(unescape("a+b", true).as_deref(), Some("a b"));
        assert_eq!(unescape("a+b", false).as_deref(), Some("a+b"));
        assert_eq!(
            (unescape("%", true), unescape("%4", true), unescape("%zz", true), unescape("%ff", true)),
            (None, None, None, None)
        );
    }
}
