//! Reverse-proxy backend dialling: the host side of the proxy forward.
//!
//! The proven core (`Reactor.ProxyDial`, exported as `drorb_proxy_pick`) decides
//! WHICH backend a request goes to — `Proxy.selectChain` over the eligible
//! (healthy ∧ active) pool, honouring live health, the circuit breaker, and
//! session affinity. This module is the HOST side of that split: it opens the
//! real TCP connection to the chosen backend, forwards the request bytes, and
//! returns the upstream's response bytes. No selection logic lives here — the
//! backend id always comes from the proven pick; this module only maps that id to
//! a configured socket, dials it, and moves bytes.
//!
//! The split mirrors `drorb_serve`: the core is sans-IO and decides meaning; the
//! host owns the sockets. Before this module, the proxy LB ran inside the core and
//! stamped its choice into a header, but nothing ever opened a socket to a backend
//! — the forward was proven-but-not-connected. This closes it.
//!
//! ## Live inputs the host contributes to the proven pick
//!
//! * **health mask** — `Fleet` runs active TCP probes against each backend and
//!   packs an up/down bit per backend into a `u8`. A backend that fails to accept
//!   is marked down; the proven selector (fed this mask) then never chooses it
//!   (`Reactor.ProxyDial.pick_health_ejects`).
//! * **circuit breaker** — after `breaker_threshold` consecutive forward failures
//!   a backend's bit is forced down (breaker open); a success closes it again.
//!   Same mechanism, same proven ejection.
//! * **affinity key** — [`sticky_key`] extracts the session key (a `sid` cookie,
//!   else the request target) and feeds it to the pick; rendezvous hashing pins a
//!   session to one backend across requests.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// A configured backend fleet: the id→socket map plus live health and breaker
/// state. Ids match the proven `Reactor.ProxyDial.fleet` backend ids (0,1,2,…).
pub struct Fleet {
    /// backend id → its socket address.
    by_id: HashMap<u32, SocketAddr>,
    /// Live health bitmask: bit `i` set ⇒ backend `i` is up (probe OK AND breaker
    /// closed). This is the `mask` byte handed to the proven `drorb_proxy_pick`.
    health: AtomicU32,
    /// Per-backend consecutive-failure counter for the circuit breaker.
    breaker: Mutex<HashMap<u32, u32>>,
    /// Per-backend in-flight forward count (incremented around the upstream dial),
    /// for operator introspection (`/admin/backends`). One atomic per configured
    /// backend, so the hot path is lock-free.
    inflight: HashMap<u32, AtomicU32>,
    /// Consecutive forward failures that open a backend's breaker.
    breaker_threshold: u32,
    /// How long to wait dialling / probing a backend before giving up.
    dial_timeout: Duration,
}

/// A read-only snapshot of one backend's operational health, for the admin
/// surface (`/admin/backends`). Assembled by [`Fleet::snapshot`].
pub struct BackendHealth {
    /// The proven-pick backend id.
    pub id: u32,
    /// The configured socket address.
    pub addr: SocketAddr,
    /// Whether the backend is currently eligible (probe OK and breaker closed) —
    /// its bit in the live mask the proven selector consumes.
    pub up: bool,
    /// Forwards currently in flight to this backend.
    pub inflight: u32,
    /// Consecutive forward failures recorded against the breaker.
    pub breaker_failures: u32,
    /// Whether the breaker has tripped open (`breaker_failures ≥ threshold`).
    pub breaker_open: bool,
}

impl Fleet {
    /// Build a fleet from a spec string like `0=127.0.0.1:9400,1=127.0.0.1:9401`.
    /// All configured backends start assumed-up; the health loop / breaker demote
    /// them on real failures. Returns `None` if the spec names no backend.
    pub fn parse(spec: &str, breaker_threshold: u32, dial_timeout: Duration) -> Option<Fleet> {
        let mut by_id = HashMap::new();
        let mut mask: u32 = 0;
        for entry in spec.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let (id_s, addr_s) = entry.split_once('=')?;
            let id: u32 = id_s.trim().parse().ok()?;
            let addr: SocketAddr = addr_s.trim().parse().ok()?;
            by_id.insert(id, addr);
            mask |= 1 << id;
        }
        if by_id.is_empty() {
            return None;
        }
        let inflight = by_id.keys().map(|&id| (id, AtomicU32::new(0))).collect();
        Some(Fleet {
            by_id,
            health: AtomicU32::new(mask),
            breaker: Mutex::new(HashMap::new()),
            inflight,
            breaker_threshold,
            dial_timeout,
        })
    }

    /// Read the fleet spec from `DRORB_PROXY_BACKENDS` (see [`Fleet::parse`]).
    pub fn from_env() -> Option<Fleet> {
        let spec = std::env::var("DRORB_PROXY_BACKENDS").ok()?;
        let thr = std::env::var("DRORB_PROXY_BREAKER")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3);
        Fleet::parse(&spec, thr, Duration::from_millis(500))
    }

    /// The live health bitmask, low 8 bits, as the `mask` byte the proven pick
    /// consumes. Bit `i` ⇒ backend `i` is up.
    pub fn mask(&self) -> u8 {
        (self.health.load(Ordering::SeqCst) & 0xff) as u8
    }

    /// The socket for a backend id, if configured.
    pub fn addr(&self, id: u32) -> Option<SocketAddr> {
        self.by_id.get(&id).copied()
    }

    fn set_up(&self, id: u32, up: bool) {
        let bit = 1u32 << id;
        if up {
            self.health.fetch_or(bit, Ordering::SeqCst);
        } else {
            self.health.fetch_and(!bit, Ordering::SeqCst);
        }
    }

    /// A successful forward: close the breaker and mark the backend up.
    pub fn record_success(&self, id: u32) {
        self.breaker.lock().unwrap().insert(id, 0);
        self.set_up(id, true);
    }

    /// A failed forward: bump the breaker; once it trips, force the backend down
    /// (breaker open) so the proven selector routes around it.
    pub fn record_failure(&self, id: u32) {
        let mut b = self.breaker.lock().unwrap();
        let n = b.entry(id).or_insert(0);
        *n += 1;
        if *n >= self.breaker_threshold {
            self.set_up(id, false);
        }
    }

    fn inflight_inc(&self, id: u32) {
        if let Some(c) = self.inflight.get(&id) {
            c.fetch_add(1, Ordering::SeqCst);
        }
    }

    fn inflight_dec(&self, id: u32) {
        if let Some(c) = self.inflight.get(&id) {
            c.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// A per-backend health snapshot for operator introspection
    /// (`/admin/backends`): address, live up/down, in-flight forwards, and breaker
    /// state, ordered by backend id. Read-only — it never touches the mask the
    /// proven selector consumes.
    pub fn snapshot(&self) -> Vec<BackendHealth> {
        let mask = self.health.load(Ordering::SeqCst);
        let breaker = self.breaker.lock().unwrap();
        let mut out: Vec<BackendHealth> = self
            .by_id
            .iter()
            .map(|(&id, &addr)| {
                let failures = breaker.get(&id).copied().unwrap_or(0);
                BackendHealth {
                    id,
                    addr,
                    up: mask & (1 << id) != 0,
                    inflight: self
                        .inflight
                        .get(&id)
                        .map(|c| c.load(Ordering::SeqCst))
                        .unwrap_or(0),
                    breaker_failures: failures,
                    breaker_open: failures >= self.breaker_threshold,
                }
            })
            .collect();
        out.sort_by_key(|b| b.id);
        out
    }

    /// One active-health sweep: TCP-probe every configured backend and set its
    /// bit up iff the connection is accepted (a breaker-open backend stays down
    /// until a probe succeeds). Returns the resulting mask.
    pub fn probe_once(&self) -> u8 {
        for (&id, &addr) in &self.by_id {
            let up = TcpStream::connect_timeout(&addr, self.dial_timeout).is_ok();
            if up {
                // Probe recovered the backend: clear any open breaker.
                self.breaker.lock().unwrap().insert(id, 0);
            }
            self.set_up(id, up);
        }
        self.mask()
    }

    /// Spawn the background active-health loop: sweep every `interval` until the
    /// process exits. The mask it maintains is what the proven selector sees.
    pub fn spawn_health_checks(self: Arc<Self>, interval: Duration) {
        std::thread::Builder::new()
            .name("drorb-proxy-health".into())
            .spawn(move || {
                loop {
                    self.probe_once();
                    std::thread::sleep(interval);
                }
            })
            .expect("failed to spawn the proxy health-check thread");
    }
}

/// The request target (the path in the request line), as bytes.
fn request_target(req: &[u8]) -> Option<&[u8]> {
    let line_end = req.windows(2).position(|w| w == b"\r\n")?;
    let line = &req[..line_end];
    let mut it = line.splitn(3, |&c| c == b' ');
    it.next()?; // method
    it.next() // target
}

/// Is this request one the reverse proxy should forward? Targets under `/api`.
pub fn is_proxy_path(req: &[u8]) -> bool {
    match request_target(req) {
        Some(t) => t == b"/api" || t.starts_with(b"/api/") || t.starts_with(b"/api?"),
        None => false,
    }
}

/// Extract the session-affinity key: the `sid=` cookie value if present, else the
/// request target. These bytes are hashed by the proven rendezvous policy, so one
/// session pins to one backend across requests.
pub fn sticky_key(req: &[u8]) -> Vec<u8> {
    // Scan headers for a Cookie line and a `sid=` crumb.
    let head_end = req
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(req.len());
    let head = &req[..head_end];
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 7 && line[..7].eq_ignore_ascii_case(b"cookie:") {
            for crumb in line[7..].split(|&c| c == b';') {
                let crumb = trim_ascii(crumb);
                if let Some(v) = crumb.strip_prefix(b"sid=") {
                    return v.to_vec();
                }
            }
        }
    }
    request_target(req).map(|t| t.to_vec()).unwrap_or_default()
}

fn trim_ascii(mut b: &[u8]) -> &[u8] {
    while let [f, rest @ ..] = b {
        if f.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., l] = b {
        if l.is_ascii_whitespace() {
            b = rest;
        } else {
            break;
        }
    }
    b
}

/// Forward `req` to `addr` over a fresh TCP connection and return the upstream's
/// full response bytes. The connection is opened, the request is written verbatim
/// (the proven core already produced a forwardable request head; the host adds no
/// meaning), and the response is read until the upstream signals completion by
/// Content-Length or by closing. This is a REAL socket to a REAL backend — the
/// forward the "no upstream connection" gap was missing.
pub fn forward(addr: SocketAddr, req: &[u8], timeout: Duration) -> std::io::Result<Vec<u8>> {
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(req)?;
    up.flush()?;
    read_response(&mut up)
}

/// Read one full HTTP/1.1 response: headers, then the Content-Length body if
/// present, else to EOF. Enough for a reverse-proxy hop over loopback backends.
fn read_response(sock: &mut TcpStream) -> std::io::Result<Vec<u8>> {
    let mut buf = Vec::with_capacity(4096);
    let mut chunk = [0u8; 16384];
    // 1. Read at least the header block.
    let head_end = loop {
        if let Some(p) = find(&buf, b"\r\n\r\n") {
            break p + 4;
        }
        let n = sock.read(&mut chunk)?;
        if n == 0 {
            return Ok(buf); // closed before a full header block
        }
        buf.extend_from_slice(&chunk[..n]);
    };
    // 2. If Content-Length is given, read exactly that many body bytes; otherwise
    //    read until the peer closes (Connection: close framing).
    match content_length(&buf[..head_end]) {
        Some(clen) => {
            let want = head_end + clen;
            while buf.len() < want {
                let n = sock.read(&mut chunk)?;
                if n == 0 {
                    break;
                }
                buf.extend_from_slice(&chunk[..n]);
            }
        }
        None => loop {
            let n = sock.read(&mut chunk)?;
            if n == 0 {
                break;
            }
            buf.extend_from_slice(&chunk[..n]);
        },
    }
    Ok(buf)
}

pub(crate) fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

pub(crate) fn content_length(head: &[u8]) -> Option<usize> {
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 15 && line[..15].eq_ignore_ascii_case(b"content-length:") {
            let v = trim_ascii(&line[15..]);
            return std::str::from_utf8(v).ok()?.trim().parse().ok();
        }
    }
    None
}

/// Whether the response head declares `Transfer-Encoding: chunked`.
pub(crate) fn is_chunked(head: &[u8]) -> bool {
    for line in head.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.len() >= 18 && line[..18].eq_ignore_ascii_case(b"transfer-encoding:") {
            let v = trim_ascii(&line[18..]).to_ascii_lowercase();
            return v.windows(7).any(|w| w == b"chunked");
        }
    }
    false
}

/// The outcome of a STREAMED proxy forward: the metadata the host records for a
/// response whose body it wrote straight to the client instead of buffering.
pub struct Streamed {
    /// The response head (status line + headers, through CRLFCRLF) as written to
    /// the client — annotated with the host's connection disposition. The host
    /// reads only the status line off it (metrics / access log).
    pub head: Vec<u8>,
    /// Total bytes written to the client (annotated head + streamed body).
    pub bytes: u64,
    /// Whether the upstream framing lets the client connection stay open
    /// (Content-Length or chunked, AND the request asked for keep-alive, AND the
    /// body streamed to its framed end). A close-delimited body or a mid-stream
    /// error forces the connection closed.
    pub keepalive: bool,
    /// Whether the body reached its framed end with no upstream/client error — a
    /// clean forward, for the circuit breaker.
    pub complete: bool,
}

/// The bounded copy buffer for the streaming body pump: one block held at a time,
/// so peak host memory for a forward is this plus the response head regardless of
/// the upstream body size. A slow client back-pressures the upstream because the
/// next upstream read only happens after the current block is written to the
/// client (TCP flow control on the upstream socket then throttles the backend).
const STREAM_CHUNK: usize = 64 * 1024;

/// Forward `req` to `addr` and STREAM the upstream response to `client` as it
/// arrives — the head first (so time-to-first-byte tracks the upstream, not the
/// whole body), then the body copied block-by-block with a bounded buffer — rather
/// than reading the whole reply into memory and returning it. The host annotates
/// the head with its keep-alive disposition (never overriding an upstream
/// `Connection` header, preserving the proven serve's header contract), then
/// frames the body by Content-Length, chunked (streamed verbatim up to its
/// terminating zero-chunk), or, with neither, connection close (streamed to EOF).
///
/// `Err` is returned ONLY when nothing has reached the client yet (dial failure,
/// request-write failure, or the upstream closing before a full response head) so
/// the caller may still send a 502. Once the head is on the wire a later error
/// just stops the stream and surfaces as `complete = false`; the caller closes the
/// connection rather than corrupting the response already in flight.
pub fn forward_streaming<W: Write>(
    addr: SocketAddr,
    req: &[u8],
    timeout: Duration,
    keepalive_req: bool,
    client: &mut W,
) -> std::io::Result<Streamed> {
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(req)?;
    up.flush()?;

    // 1. Read the response head (through CRLFCRLF). A single read may over-read
    //    into the body; those bytes are kept in `buf` past `head_end`.
    let mut buf = Vec::with_capacity(4096);
    let mut chunk = vec![0u8; STREAM_CHUNK];
    let head_end = loop {
        if let Some(p) = find(&buf, b"\r\n\r\n") {
            break p + 4;
        }
        let n = up.read(&mut chunk)?;
        if n == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "upstream closed before a full response head",
            ));
        }
        buf.extend_from_slice(&chunk[..n]);
    };

    // 2. Framing + keep-alive disposition from the head.
    let clen = content_length(&buf[..head_end]);
    let chunked = is_chunked(&buf[..head_end]);
    let self_delimited = clen.is_some() || chunked;
    let keepalive = keepalive_req && self_delimited;

    // 3. Annotate the head with the host's connection disposition (only when the
    //    upstream states none), then write it. From here a failure is mid-stream.
    let mut head = buf[..head_end].to_vec();
    crate::http::annotate_connection(&mut head, keepalive);
    if client.write_all(&head).is_err() {
        return Ok(Streamed {
            head,
            bytes: 0,
            keepalive: false,
            complete: false,
        });
    }
    let mut bytes = head.len() as u64;

    // 4. Stream the body per its framing. `leftover` is the body bytes already
    //    read while finding the head end.
    let leftover = &buf[head_end..];
    let complete = match clen {
        Some(clen) => stream_fixed(&mut up, client, leftover, clen, &mut chunk, &mut bytes),
        None if chunked => stream_chunked(&mut up, client, leftover, &mut chunk, &mut bytes),
        None => stream_to_eof(&mut up, client, leftover, &mut chunk, &mut bytes),
    };

    Ok(Streamed {
        head,
        bytes,
        keepalive: keepalive && complete,
        complete,
    })
}

/// Stream exactly `clen` body bytes from `up` to `client`, starting with the
/// already-read `leftover`. Returns whether the full body was delivered.
fn stream_fixed<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    clen: usize,
    chunk: &mut [u8],
    bytes: &mut u64,
) -> bool {
    let mut remaining = clen;
    let take = leftover.len().min(remaining);
    if take > 0 {
        if client.write_all(&leftover[..take]).is_err() {
            return false;
        }
        *bytes += take as u64;
        remaining -= take;
    }
    while remaining > 0 {
        let n = match up.read(chunk) {
            Ok(0) => return false, // upstream truncated the body
            Ok(n) => n,
            Err(_) => return false,
        };
        let w = n.min(remaining);
        if client.write_all(&chunk[..w]).is_err() {
            return false;
        }
        *bytes += w as u64;
        remaining -= w;
    }
    true
}

/// Stream a close-delimited body (no Content-Length, not chunked) to EOF. The
/// connection cannot be kept alive, but events are forwarded as they arrive — an
/// upstream that drips (e.g. `text/event-stream`) reaches the client incrementally.
fn stream_to_eof<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    chunk: &mut [u8],
    bytes: &mut u64,
) -> bool {
    if !leftover.is_empty() {
        if client.write_all(leftover).is_err() {
            return false;
        }
        *bytes += leftover.len() as u64;
    }
    loop {
        let n = match up.read(chunk) {
            Ok(0) => return true, // upstream closed: the response is complete
            Ok(n) => n,
            Err(_) => return false,
        };
        if client.write_all(&chunk[..n]).is_err() {
            return false;
        }
        *bytes += n as u64;
    }
}

/// Stream a chunked body verbatim to the client, parsing a copy just enough to
/// detect the terminating zero-chunk so the client connection can stay open
/// without waiting for the upstream to close. Same bounded buffer / back-pressure
/// as the fixed path. Returns whether the terminator was reached cleanly.
fn stream_chunked<W: Write>(
    up: &mut TcpStream,
    client: &mut W,
    leftover: &[u8],
    chunk: &mut [u8],
    bytes: &mut u64,
) -> bool {
    let mut parser = ChunkedParser::new();
    if !leftover.is_empty() {
        if client.write_all(leftover).is_err() {
            return false;
        }
        *bytes += leftover.len() as u64;
        if parser.advance(leftover) {
            return true;
        }
    }
    loop {
        let n = match up.read(chunk) {
            Ok(0) => return false, // upstream closed before the terminating chunk
            Ok(n) => n,
            Err(_) => return false,
        };
        if client.write_all(&chunk[..n]).is_err() {
            return false;
        }
        *bytes += n as u64;
        if parser.advance(&chunk[..n]) {
            return true;
        }
    }
}

/// An incremental HTTP/1.1 chunked-transfer parser. It never buffers the body; it
/// only tracks enough state across streamed blocks to report when the terminating
/// zero-length chunk (and its trailer/CRLF) has been fully seen.
pub(crate) struct ChunkedParser {
    st: ChunkSt,
    size: usize,
}

enum ChunkSt {
    /// Reading the chunk-size hex line; `size` accumulates.
    Size,
    /// In a chunk extension (`;…`) on the size line — skip to CR.
    SizeExt,
    /// Saw the CR of the size line; the next byte is its LF.
    SizeCr,
    /// Consuming this many remaining data bytes of the current chunk.
    Data(usize),
    /// After the chunk data, the CR of its trailing CRLF.
    DataCr,
    /// After the chunk-data CR, its LF.
    DataLf,
    /// Start of a trailer line after the last-chunk (or the final CRLF).
    TrailerStart,
    /// Within a trailer line, before its CR.
    TrailerLine,
    /// Saw the CR of a trailer line; the next byte is its LF.
    TrailerLineCr,
    /// Saw the CR of the final empty line; the next byte is its LF → done.
    TrailerFinalCr,
    /// The terminating zero-chunk has been fully consumed.
    Done,
}

impl ChunkedParser {
    pub(crate) fn new() -> Self {
        ChunkedParser {
            st: ChunkSt::Size,
            size: 0,
        }
    }

    /// Advance the parser over `data`. Returns `true` once the terminating
    /// zero-chunk (with any trailers and the final CRLF) has been consumed.
    pub(crate) fn advance(&mut self, data: &[u8]) -> bool {
        let mut i = 0;
        while i < data.len() {
            match self.st {
                ChunkSt::Size => {
                    let b = data[i];
                    match b {
                        b'0'..=b'9' => {
                            self.size = self.size * 16 + (b - b'0') as usize;
                            i += 1;
                        }
                        b'a'..=b'f' => {
                            self.size = self.size * 16 + (b - b'a' + 10) as usize;
                            i += 1;
                        }
                        b'A'..=b'F' => {
                            self.size = self.size * 16 + (b - b'A' + 10) as usize;
                            i += 1;
                        }
                        b'\r' => {
                            self.st = ChunkSt::SizeCr;
                            i += 1;
                        }
                        b';' => {
                            self.st = ChunkSt::SizeExt;
                            i += 1;
                        }
                        _ => i += 1, // tolerate stray whitespace on the size line
                    }
                }
                ChunkSt::SizeExt => {
                    if data[i] == b'\r' {
                        self.st = ChunkSt::SizeCr;
                    }
                    i += 1;
                }
                ChunkSt::SizeCr => {
                    i += 1; // consume the LF
                    self.st = if self.size == 0 {
                        ChunkSt::TrailerStart
                    } else {
                        ChunkSt::Data(self.size)
                    };
                }
                ChunkSt::Data(n) => {
                    let take = n.min(data.len() - i);
                    i += take;
                    let left = n - take;
                    self.st = if left == 0 {
                        ChunkSt::DataCr
                    } else {
                        ChunkSt::Data(left)
                    };
                }
                ChunkSt::DataCr => {
                    i += 1; // consume the CR after the chunk data
                    self.st = ChunkSt::DataLf;
                }
                ChunkSt::DataLf => {
                    i += 1; // consume the LF
                    self.size = 0;
                    self.st = ChunkSt::Size;
                }
                ChunkSt::TrailerStart => {
                    if data[i] == b'\r' {
                        self.st = ChunkSt::TrailerFinalCr;
                        i += 1;
                    } else {
                        self.st = ChunkSt::TrailerLine;
                    }
                }
                ChunkSt::TrailerLine => {
                    if data[i] == b'\r' {
                        self.st = ChunkSt::TrailerLineCr;
                    }
                    i += 1;
                }
                ChunkSt::TrailerLineCr => {
                    i += 1; // consume the LF ending a trailer line
                    self.st = ChunkSt::TrailerStart;
                }
                ChunkSt::TrailerFinalCr => {
                    // The final LF closes the terminating zero-chunk; the response
                    // is done and any bytes past it belong to no more of this reply.
                    self.st = ChunkSt::Done;
                    return true;
                }
                ChunkSt::Done => return true,
            }
        }
        matches!(self.st, ChunkSt::Done)
    }
}

/// A `502 Bad Gateway` response (the chosen backend could not be reached).
pub fn bad_gateway() -> Vec<u8> {
    b"HTTP/1.1 502 Bad Gateway\r\nContent-Length: 11\r\nConnection: close\r\n\r\nbad gateway"
        .to_vec()
}

/// A `503 Service Unavailable` response (no backend is eligible — every backend
/// down or breaker-open, so the proven pick returned nothing).
pub fn service_unavailable() -> Vec<u8> {
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Length: 19\r\nConnection: close\r\n\r\nno healthy upstream"
        .to_vec()
}

/// What the host records after a STREAMED proxy hop: the response head (status
/// line for metrics / the access log), the total bytes written, whether the
/// client connection may stay open, and the dialled backend (for the log / metric
/// per-backend counter). The body itself was already written straight to the
/// client by [`forward_streaming`], never buffered.
pub struct StreamOutcome {
    pub head: Vec<u8>,
    pub bytes: u64,
    pub keepalive: bool,
    pub backend: Option<String>,
}

/// The whole streaming reverse-proxy hop for one request: the proven pick +
/// breaker + sticky-affinity discipline, but the upstream response is STREAMED to
/// `client` as it arrives (via [`forward_streaming`]) instead of buffered and
/// returned. The backend is ALWAYS the proven pick's; this function never selects.
///
/// It writes the whole response (a streamed upstream reply, or a 502/503 when no
/// backend is eligible / reachable) to `client` and returns the [`StreamOutcome`]
/// the host records. `Err` is only the case where a client write failed and the
/// connection must be dropped.
pub fn handle_streaming<P, W: Write>(
    req: &[u8],
    keepalive_req: bool,
    fleet: &Fleet,
    client: &mut W,
    pick: P,
) -> std::io::Result<StreamOutcome>
where
    P: Fn(u8, &[u8]) -> Option<u32>,
{
    let key = sticky_key(req);
    let id = match pick(fleet.mask(), &key) {
        Some(id) => id,
        None => {
            let resp = service_unavailable();
            client.write_all(&resp)?;
            return Ok(StreamOutcome {
                bytes: resp.len() as u64,
                head: resp,
                keepalive: false,
                backend: None,
            });
        }
    };
    let addr = match fleet.addr(id) {
        Some(a) => a,
        None => {
            let resp = bad_gateway();
            client.write_all(&resp)?;
            return Ok(StreamOutcome {
                bytes: resp.len() as u64,
                head: resp,
                keepalive: false,
                backend: None,
            });
        }
    };
    fleet.inflight_inc(id);
    let out = forward_streaming(addr, req, fleet.dial_timeout, keepalive_req, client);
    fleet.inflight_dec(id);
    match out {
        Ok(s) => {
            // A clean forward closes the breaker; a mid-stream truncation counts
            // as a failure, the same as a buffered forward that errored.
            if s.complete {
                fleet.record_success(id);
            } else {
                fleet.record_failure(id);
            }
            Ok(StreamOutcome {
                head: s.head,
                bytes: s.bytes,
                keepalive: s.keepalive,
                backend: Some(addr.to_string()),
            })
        }
        Err(_) => {
            // Nothing reached the client yet (dial / no valid response head): the
            // breaker takes the failure and the host can still send a real 502.
            fleet.record_failure(id);
            let resp = bad_gateway();
            client.write_all(&resp)?;
            Ok(StreamOutcome {
                bytes: resp.len() as u64,
                head: resp,
                keepalive: false,
                backend: None,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_fleet_spec_and_mask() {
        let f = Fleet::parse(
            "0=127.0.0.1:9400,2=127.0.0.1:9402",
            3,
            Duration::from_millis(50),
        )
        .unwrap();
        assert_eq!(f.mask(), 0b101);
        assert_eq!(f.addr(0), Some("127.0.0.1:9400".parse().unwrap()));
        assert_eq!(f.addr(1), None);
    }

    #[test]
    fn breaker_opens_after_threshold() {
        let f = Fleet::parse("1=127.0.0.1:9401", 2, Duration::from_millis(50)).unwrap();
        assert_eq!(f.mask(), 0b010);
        f.record_failure(1);
        assert_eq!(f.mask(), 0b010); // one failure: still up
        f.record_failure(1);
        assert_eq!(f.mask(), 0b000); // threshold: breaker open, bit cleared
        f.record_success(1);
        assert_eq!(f.mask(), 0b010); // success closes the breaker
    }

    #[test]
    fn detects_proxy_path_and_sticky_key() {
        assert!(is_proxy_path(b"GET /api/users HTTP/1.1\r\nHost: x\r\n\r\n"));
        assert!(is_proxy_path(b"GET /api HTTP/1.1\r\n\r\n"));
        assert!(!is_proxy_path(b"GET /health HTTP/1.1\r\n\r\n"));
        assert_eq!(
            sticky_key(b"GET /api HTTP/1.1\r\nCookie: a=1; sid=SESSION42; b=2\r\n\r\n"),
            b"SESSION42".to_vec()
        );
        assert_eq!(
            sticky_key(b"GET /api/x HTTP/1.1\r\nHost: y\r\n\r\n"),
            b"/api/x".to_vec()
        );
    }

    #[test]
    fn chunked_parser_detects_terminator() {
        // Two data chunks then the last-chunk with no trailers.
        let body = b"5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n";
        let mut p = ChunkedParser::new();
        assert!(p.advance(body));

        // Split across feeds: the terminator must be detected on the last feed.
        let mut p = ChunkedParser::new();
        assert!(!p.advance(b"5\r\nhel"));
        assert!(!p.advance(b"lo\r\n0\r\n"));
        assert!(p.advance(b"\r\n"));

        // A trailer line before the final CRLF is consumed too.
        let mut p = ChunkedParser::new();
        assert!(p.advance(b"0\r\nX-Trailer: v\r\n\r\n"));

        // An unterminated stream is not "done".
        let mut p = ChunkedParser::new();
        assert!(!p.advance(b"5\r\nhello\r\n"));
    }

    #[test]
    fn detects_chunked_and_content_length() {
        assert!(is_chunked(
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"
        ));
        assert!(is_chunked(
            b"HTTP/1.1 200 OK\r\ntransfer-encoding: gzip, chunked\r\n\r\n"
        ));
        assert!(!is_chunked(b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n\r\n"));
        assert_eq!(
            content_length(b"HTTP/1.1 200 OK\r\nContent-Length: 42\r\n\r\n"),
            Some(42)
        );
    }
}
