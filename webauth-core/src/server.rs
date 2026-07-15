//! The forward-auth HTTP server — the web edge that sits in front of a
//! capability-gated surface (an operator dashboard, a launchpad's create/publish
//! API, a per-vat computer) and turns a reverse proxy's `forward_auth` subrequest
//! into a `200`/`401`/`403` decision over a presented `dga1_` credential.
//!
//! Pure `std` (a **bounded worker pool**, HTTP/1.1 with keep-alive) so it
//! cross-builds trivially and carries no async runtime. It stands entirely on the
//! offline decision core in this crate ([`crate::decide`], [`crate::credext`],
//! [`crate::challenge`]) — the server is transport + operability, not policy.
//!
//! ## Operability (what makes it an *edge*, not a demo)
//! * **Bounded worker pool + backpressure** — a fixed pool services connections
//!   off a bounded queue; a connection flood is *shed* with `503` rather than
//!   spawning unbounded OS threads ([`crate::config::WebAuthConfig::max_in_flight`]).
//! * **Per-client rate limiting + escalating lockout** — `/auth`, `/login`, and
//!   `/login/challenge` are throttled per client IP; failed break-glass / PoP
//!   attempts arm an exponential lockout ([`crate::ratelimit`]).
//! * **Hot revocation** — the revocation file is polled and applied live behind
//!   an `Arc<RwLock<…>>`, so a leaked token dies with no restart
//!   ([`crate::config::Revocations`]).
//! * **Single-use login PoP** — a bounded seen-nonce cache upgrades the login
//!   challenge from time-bounded to genuinely single-use ([`crate::replay`]).
//! * **Audit + metrics** — a structured JSON line per decision and a Prometheus
//!   `GET /metrics` exposition ([`crate::observe`]).
//!
//! | Method + path        | Serves                                                    |
//! |----------------------|-----------------------------------------------------------|
//! | `GET /auth`          | the forward-auth decision (2xx admit / 302→login on deny) |
//! | `GET /whoami`        | session introspection (JSON `{authenticated, subject}`)   |
//! | `GET /login`         | the login page (paste / wallet-sign a `dga1_…` credential)|
//! | `GET /login/challenge` | a fresh proof-of-possession nonce (JSON)                |
//! | `POST /login`        | accept the credential → set the session cookie → redirect |
//! | `GET /logout`        | clear the session cookie                                  |
//! | `GET /metrics`       | Prometheus exposition (always open)                       |
//! | `GET /healthz`       | liveness (always open)                                    |
//!
//! ## TLS / deployment posture (READ THIS)
//! This crate speaks plain HTTP/1.1. Its `Secure` session cookie and its
//! no-forged-`X-Dregg-*`-header discipline both ASSUME a trusted TLS-terminating
//! reverse proxy in front and a private upstream — it is **forward-auth behind a
//! proxy**, not a standalone internet-facing server. Set
//! `DREGG_WEBAUTH_BEHIND_PROXY=1` to acknowledge that fronting; run without it and
//! `serve` logs a loud standalone-insecurity warning at startup. See
//! `deploy/webauth-edge/Caddyfile.capauth` for the reverse-proxy idiom (including
//! the mandatory identity-header strip that makes the `X-Dregg-Subject` echo
//! forge-proof).

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::mpsc::{TrySendError, sync_channel};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use dregg_agent::cred::{Credential, PublicKey};

use crate::config::WebAuthConfig;
use crate::credext::{CredentialExt, Validity, verify_pop};
use crate::observe::{AuditRecord, Metrics, elapsed_ms};
use crate::ratelimit::{Lockout, TokenBucket};
use crate::replay::NonceCache;
use crate::{AuthInput, Verdict, decide, subject_of, subject_of_credential};

const MAX_HEADER_BYTES: usize = 64 * 1024;
const MAX_BODY_BYTES: usize = 256 * 1024;

/// Per-connection socket timeout. Bounds a slow-loris connection that dribbles a
/// request (or never finishes one) so it cannot pin a worker thread forever.
const CONN_TIMEOUT: Duration = Duration::from_secs(30);

// ===========================================================================
// Runtime — the cfg + the shared operability state the handlers consult.
// ===========================================================================

/// The shared serving state: the immutable decision config plus the mutable
/// operability machinery (metrics, per-client limiters, the single-use nonce
/// cache). Cheap to share as an `Arc` across the worker pool.
pub struct Runtime {
    pub cfg: Arc<WebAuthConfig>,
    pub metrics: Arc<Metrics>,
    limiter: TokenBucket,
    lockout: Lockout,
    replay: NonceCache,
    started: Instant,
}

impl Runtime {
    /// Build the runtime from a config, wiring the limiters to its knobs.
    pub fn new(cfg: Arc<WebAuthConfig>) -> Self {
        let max_keys = cfg.max_in_flight.saturating_mul(16).max(4096);
        let limiter = TokenBucket::new(cfg.rate_burst, cfg.rate_per_min, max_keys);
        let lockout = Lockout::new(
            cfg.lockout_threshold,
            cfg.lockout_base_secs,
            cfg.lockout_max_secs,
            max_keys,
        );
        let replay = NonceCache::new(
            cfg.pop_single_use,
            cfg.max_in_flight.saturating_mul(8).max(4096),
        );
        Self {
            cfg,
            metrics: Arc::new(Metrics::default()),
            limiter,
            lockout,
            replay,
            started: Instant::now(),
        }
    }

    fn uptime_secs(&self) -> u64 {
        self.started.elapsed().as_secs()
    }

    /// A runtime for tests: audit silenced so the test output stays clean.
    #[cfg(test)]
    fn for_test(mut cfg: WebAuthConfig) -> Arc<Self> {
        cfg.audit_log = false;
        Arc::new(Self::new(Arc::new(cfg)))
    }
}

/// The identity of the connecting client, used to key rate limiting / lockout and
/// stamp the audit line. The peer socket address, or a trusted `X-Forwarded-For`
/// when [`WebAuthConfig::trust_forwarded_for`] is set.
#[derive(Clone, Debug)]
pub struct Client {
    pub ip: String,
}

impl Client {
    fn from_peer(peer: Option<std::net::SocketAddr>) -> Self {
        Self {
            ip: peer
                .map(|a| a.ip().to_string())
                .unwrap_or_else(|| "unknown".to_string()),
        }
    }
    /// Resolve the effective client identity, honoring a trusted XFF header.
    fn resolve(mut self, req: &Request, cfg: &WebAuthConfig) -> Self {
        if cfg.trust_forwarded_for {
            if let Some(xff) = req.header("x-forwarded-for") {
                if let Some(first) = xff.split(',').next() {
                    let first = first.trim();
                    if !first.is_empty() {
                        self.ip = first.to_string();
                    }
                }
            }
        }
        self
    }
    #[cfg(test)]
    fn test() -> Self {
        Self {
            ip: "127.0.0.1".to_string(),
        }
    }
}

/// The per-request evaluation context threaded through the handlers.
struct Ctx<'a> {
    rt: &'a Runtime,
    client: &'a Client,
    keep_alive: bool,
    now: u64,
    now_ms: u64,
    t0: Instant,
}

impl Ctx<'_> {
    fn cfg(&self) -> &WebAuthConfig {
        &self.rt.cfg
    }
    fn metrics(&self) -> &Metrics {
        &self.rt.metrics
    }
    fn audit(&self, rec: AuditRecord) {
        if self.cfg().audit_log {
            rec.str("client", &self.client.ip)
                .int("latency_ms", elapsed_ms(self.t0))
                .emit();
        }
    }
}

// ===========================================================================
// serve — bind, spawn the pool + the reload thread, accept with backpressure.
// ===========================================================================

/// Run the server forever on the configured bind address.
pub fn serve(cfg: WebAuthConfig) -> std::io::Result<()> {
    let listener = TcpListener::bind(&cfg.bind)?;
    startup_banner(&cfg);

    let cfg = Arc::new(cfg);
    let rt = Arc::new(Runtime::new(Arc::clone(&cfg)));
    spawn_revocation_reload(&cfg, Arc::clone(&rt.metrics));

    // Bounded worker pool + bounded queue = the backpressure ceiling. Jobs beyond
    // the queue depth are shed at accept time with a 503 rather than spawning
    // unbounded threads.
    let worker_count = resolve_worker_count(cfg.worker_threads);
    let (tx, rx) = sync_channel::<(TcpStream, Client)>(cfg.max_in_flight);
    let rx = Arc::new(Mutex::new(rx));
    for _ in 0..worker_count {
        let rx = Arc::clone(&rx);
        let rt = Arc::clone(&rt);
        std::thread::spawn(move || {
            loop {
                let job = {
                    let guard = rx.lock().unwrap();
                    guard.recv()
                };
                match job {
                    Ok((stream, client)) => {
                        let _ = handle_conn(stream, &rt, client);
                    }
                    Err(_) => break, // all senders dropped
                }
            }
        });
    }
    eprintln!(
        "webauth-edge: {worker_count} workers, max-in-flight {}",
        cfg.max_in_flight
    );

    for stream in listener.incoming() {
        let stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let client = Client::from_peer(stream.peer_addr().ok());
        match tx.try_send((stream, client)) {
            Ok(()) => {}
            Err(TrySendError::Full((mut stream, _))) => {
                // Backpressure: the pool is saturated. Shed this connection fast.
                Metrics::incr(&rt.metrics.shed);
                let _ = stream.set_write_timeout(Some(Duration::from_secs(2)));
                let _ = stream.write_all(&service_unavailable());
            }
            Err(TrySendError::Disconnected(_)) => break,
        }
    }
    Ok(())
}

fn startup_banner(cfg: &WebAuthConfig) {
    eprintln!("webauth-edge: forward-auth on http://{}", cfg.bind);
    eprintln!(
        "  root pubkey: {}",
        cfg.root_pubkey_hex
            .as_deref()
            .unwrap_or("(NONE — every cap check will DENY)")
    );
    eprintln!(
        "  break-glass: {}",
        if cfg.break_glass.is_some() {
            "configured"
        } else {
            "(disabled)"
        }
    );
    eprintln!("  host→cap map: {} entries", cfg.host_caps.len());
    eprintln!(
        "  revocation: {} entries{}",
        cfg.revoked.len(),
        match (&cfg.revoked_file, cfg.revoked_reload_secs) {
            (Some(p), n) if n > 0 => format!(", hot-reload {p} every {n}s"),
            (Some(p), _) => format!(", file {p} (reload disabled)"),
            _ => String::new(),
        }
    );
    eprintln!(
        "  rate limit: {}/min burst {}, lockout after {} fails",
        cfg.rate_per_min, cfg.rate_burst, cfg.lockout_threshold
    );
    if !cfg.behind_proxy {
        eprintln!(
            "  \x1b[33mWARNING\x1b[0m: DREGG_WEBAUTH_BEHIND_PROXY is not set. This edge speaks\n\
             \x20 plain HTTP/1.1 and its Secure cookie + no-forged-header discipline ASSUME a\n\
             \x20 trusted TLS-terminating proxy in front on a private upstream. Do NOT expose\n\
             \x20 this port directly to the internet. Set DREGG_WEBAUTH_BEHIND_PROXY=1 once the\n\
             \x20 fronting proxy is in place to silence this warning."
        );
    }
}

/// Resolve the worker-thread count: an explicit config value, else a modest
/// multiple of the available parallelism (blocking IO benefits from more threads
/// than cores), clamped to a sane band.
fn resolve_worker_count(configured: usize) -> usize {
    if configured > 0 {
        return configured;
    }
    let cores = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    (cores * 4).clamp(8, 256)
}

/// Poll the revocation file for changes and apply them live (hot revocation).
/// Merges the inline (`DREGG_WEBAUTH_REVOKED`) entries on each reload so they
/// survive. A no-op when no file / a zero interval is configured.
fn spawn_revocation_reload(cfg: &Arc<WebAuthConfig>, metrics: Arc<Metrics>) {
    let (Some(path), interval) = (cfg.revoked_file.clone(), cfg.revoked_reload_secs) else {
        return;
    };
    if interval == 0 {
        return;
    }
    let revoked = cfg.revoked.clone(); // shared Arc<RwLock<…>> handle
    let inline = cfg.revoked_inline.clone();
    std::thread::spawn(move || {
        let mut last_mtime: Option<SystemTime> = std::fs::metadata(&path)
            .ok()
            .and_then(|m| m.modified().ok());
        loop {
            std::thread::sleep(Duration::from_secs(interval));
            let mtime = std::fs::metadata(&path)
                .ok()
                .and_then(|m| m.modified().ok());
            if mtime == last_mtime {
                continue;
            }
            last_mtime = mtime;
            match std::fs::read_to_string(&path) {
                Ok(contents) => {
                    let mut set = crate::config::parse_revoked(&contents);
                    set.extend(inline.iter().cloned());
                    let n = set.len();
                    revoked.replace_all(set);
                    Metrics::incr(&metrics.reloads);
                    eprintln!("webauth-edge: revocation reloaded from {path} ({n} entries)");
                }
                Err(_) => {
                    eprintln!(
                        "webauth-edge: WARN revocation file {path} vanished/unreadable on reload"
                    );
                }
            }
        }
    });
}

// ===========================================================================
// Connection handling — keep-alive loop over a bounded request parser.
// ===========================================================================

fn handle_conn(stream: TcpStream, rt: &Runtime, client: Client) -> std::io::Result<()> {
    let _ = stream.set_read_timeout(Some(CONN_TIMEOUT));
    let _ = stream.set_write_timeout(Some(CONN_TIMEOUT));
    let mut reader = BufReader::new(stream);
    let max_reqs = rt.cfg.max_keepalive_requests.max(1);
    let mut served = 0u32;
    loop {
        let parsed = match read_request(&mut reader) {
            Ok(Some(r)) => r,
            Ok(None) => break, // clean EOF between requests
            Err(ReadError::Io(_)) => break,
            Err(ReadError::Malformed(msg)) => {
                Metrics::incr(&rt.metrics.bad_request);
                let bytes = bad_request(&msg, false);
                let _ = reader.get_mut().write_all(&bytes);
                break;
            }
        };
        served += 1;
        // Keep-alive: HTTP/1.1 defaults to keep-alive unless `Connection: close`;
        // HTTP/1.0 defaults to close unless `Connection: keep-alive`. Also close
        // once the per-connection request budget is spent.
        let conn_hdr = parsed.header("connection").map(|s| s.to_ascii_lowercase());
        let client_keep = match parsed.version.as_str() {
            "HTTP/1.0" => conn_hdr.as_deref() == Some("keep-alive"),
            _ => conn_hdr.as_deref() != Some("close"),
        };
        let keep_alive = client_keep && served < max_reqs;

        let client = client.clone().resolve(&parsed, &rt.cfg);
        let ctx = Ctx {
            rt,
            client: &client,
            keep_alive,
            now: now_secs(),
            now_ms: now_millis(),
            t0: Instant::now(),
        };
        let resp = route(&parsed, &ctx);
        reader.get_mut().write_all(&resp)?;
        reader.get_mut().flush()?;
        if !keep_alive {
            break;
        }
    }
    Ok(())
}

/// A parsed request: method, path, query, headers (lowercased keys), body.
struct Request {
    method: String,
    path: String,
    version: String,
    query: Vec<(String, String)>,
    headers: Vec<(String, String)>,
    body: String,
}

impl Request {
    fn header(&self, name: &str) -> Option<&str> {
        let name = name.to_ascii_lowercase();
        self.headers
            .iter()
            .find(|(k, _)| *k == name)
            .map(|(_, v)| v.as_str())
    }
    fn query_get(&self, key: &str) -> Option<&str> {
        self.query
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }
    fn cookie(&self, name: &str) -> Option<String> {
        let raw = self.header("cookie")?;
        for part in raw.split(';') {
            let part = part.trim();
            if let Some((k, v)) = part.split_once('=') {
                if k.trim() == name {
                    return Some(v.trim().to_string());
                }
            }
        }
        None
    }
}

/// Why request parsing stopped.
enum ReadError {
    Io(std::io::Error),
    Malformed(String),
}
impl From<std::io::Error> for ReadError {
    fn from(e: std::io::Error) -> Self {
        ReadError::Io(e)
    }
}

fn read_request(reader: &mut BufReader<TcpStream>) -> Result<Option<Request>, ReadError> {
    let mut request_line = String::new();
    if reader.read_line(&mut request_line)? == 0 {
        return Ok(None);
    }
    // Ignore a stray leading blank line (tolerated per RFC 7230 §3.5).
    if request_line.trim().is_empty() {
        return Ok(None);
    }
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_string();
    let target = parts.next().unwrap_or("/").to_string();
    let version = parts.next().unwrap_or("HTTP/1.1").to_string();
    if method.is_empty() {
        return Err(ReadError::Malformed("empty request method".to_string()));
    }
    let (path, query) = split_target(&target);

    let mut headers: Vec<(String, String)> = Vec::new();
    let mut total = request_line.len();
    loop {
        let mut line = String::new();
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            break;
        }
        total += n;
        if total > MAX_HEADER_BYTES {
            return Err(ReadError::Malformed(
                "request headers exceed the limit".to_string(),
            ));
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if let Some((k, v)) = trimmed.split_once(':') {
            headers.push((k.trim().to_ascii_lowercase(), v.trim().to_string()));
        }
    }

    let header = |name: &str| {
        headers
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v.as_str())
    };

    // Body: honor `Transfer-Encoding: chunked` first, else `Content-Length`.
    let te_chunked = header("transfer-encoding")
        .map(|v| {
            v.to_ascii_lowercase()
                .split(',')
                .any(|t| t.trim() == "chunked")
        })
        .unwrap_or(false);
    let body = if te_chunked {
        read_chunked_body(reader)?
    } else if let Some(len) = header("content-length") {
        match len.parse::<usize>() {
            Ok(len) => {
                let len = len.min(MAX_BODY_BYTES);
                let mut buf = vec![0u8; len];
                reader.read_exact(&mut buf)?;
                String::from_utf8_lossy(&buf).into_owned()
            }
            Err(_) => return Err(ReadError::Malformed("invalid Content-Length".to_string())),
        }
    } else {
        String::new()
    };

    Ok(Some(Request {
        method,
        path,
        version,
        query,
        headers,
        body,
    }))
}

/// Decode an HTTP/1.1 `Transfer-Encoding: chunked` body (bounded).
fn read_chunked_body(reader: &mut BufReader<TcpStream>) -> Result<String, ReadError> {
    let mut out: Vec<u8> = Vec::new();
    loop {
        let mut size_line = String::new();
        if reader.read_line(&mut size_line)? == 0 {
            return Err(ReadError::Malformed("truncated chunked body".to_string()));
        }
        // A chunk-size line may carry `;ext`; the size is the leading hex.
        let hex = size_line.trim().split(';').next().unwrap_or("").trim();
        let size = usize::from_str_radix(hex, 16)
            .map_err(|_| ReadError::Malformed("invalid chunk size".to_string()))?;
        if size == 0 {
            // Consume the (possibly empty) trailer up to the final CRLF.
            let mut trailer = String::new();
            loop {
                trailer.clear();
                if reader.read_line(&mut trailer)? == 0 {
                    break;
                }
                if trailer.trim().is_empty() {
                    break;
                }
            }
            break;
        }
        if out.len() + size > MAX_BODY_BYTES {
            return Err(ReadError::Malformed(
                "chunked body exceeds the limit".to_string(),
            ));
        }
        let mut buf = vec![0u8; size];
        reader.read_exact(&mut buf)?;
        out.extend_from_slice(&buf);
        // Trailing CRLF after each chunk.
        let mut crlf = [0u8; 2];
        reader.read_exact(&mut crlf)?;
    }
    Ok(String::from_utf8_lossy(&out).into_owned())
}

fn split_target(target: &str) -> (String, Vec<(String, String)>) {
    match target.split_once('?') {
        Some((p, q)) => (p.to_string(), parse_query(q)),
        None => (target.to_string(), Vec::new()),
    }
}

fn parse_query(q: &str) -> Vec<(String, String)> {
    q.split('&')
        .filter(|s| !s.is_empty())
        .map(|pair| match pair.split_once('=') {
            Some((k, v)) => (url_decode(k), url_decode(v)),
            None => (url_decode(pair), String::new()),
        })
        .collect()
}

fn url_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'%' if i + 2 < bytes.len() => {
                let hi = (bytes[i + 1] as char).to_digit(16);
                let lo = (bytes[i + 2] as char).to_digit(16);
                if let (Some(hi), Some(lo)) = (hi, lo) {
                    out.push((hi * 16 + lo) as u8);
                    i += 3;
                    continue;
                }
                out.push(b'%');
                i += 1;
            }
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}
fn now_millis() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

// ===========================================================================
// Routing.
// ===========================================================================

fn route(req: &Request, ctx: &Ctx) -> Vec<u8> {
    Metrics::incr(&ctx.metrics().requests);
    // Sensitive verbs are throttled + lockout-gated per client. Public reads
    // (health, metrics, the login page, logout, whoami) are not.
    let sensitive = matches!(
        (req.method.as_str(), req.path.as_str()),
        ("GET", "/auth") | ("GET", "/login/challenge") | ("POST", "/login")
    );
    if sensitive {
        if !ctx.rt.lockout.allowed(&ctx.client.ip, ctx.now_ms) {
            Metrics::incr(&ctx.metrics().locked_out);
            ctx.audit(
                AuditRecord::new("locked_out")
                    .str("path", &req.path)
                    .int("status", 429),
            );
            return too_many(ctx.keep_alive, "too many failed attempts — locked out");
        }
        if !ctx.rt.limiter.allow(&ctx.client.ip, ctx.now_ms) {
            Metrics::incr(&ctx.metrics().rate_limited);
            ctx.audit(
                AuditRecord::new("rate_limited")
                    .str("path", &req.path)
                    .int("status", 429),
            );
            return too_many(ctx.keep_alive, "rate limit exceeded");
        }
    }

    match (req.method.as_str(), req.path.as_str()) {
        ("GET", "/healthz") => text(200, "ok", ctx.keep_alive),
        ("GET", "/metrics") => text_ct(
            200,
            "text/plain; version=0.0.4; charset=utf-8",
            &ctx.metrics().render_prometheus(ctx.rt.uptime_secs()),
            ctx.keep_alive,
        ),
        ("GET", "/auth") => handle_auth(req, ctx),
        ("GET", "/whoami") => handle_whoami(req, ctx),
        ("GET", "/login") => login_page(req, ctx),
        ("GET", "/login/challenge") => login_challenge(ctx),
        ("POST", "/login") => login_submit(req, ctx),
        ("GET", "/logout") => logout(ctx),
        _ => text(404, "not found", ctx.keep_alive),
    }
}

// ---------------------------------------------------------------------------
// /auth — the forward-auth decision
// ---------------------------------------------------------------------------

fn extract_credential(req: &Request, cfg: &WebAuthConfig) -> Option<String> {
    if let Some(c) = req.cookie(&cfg.cookie_name) {
        if !c.is_empty() {
            return Some(c);
        }
    }
    if let Some(h) = req.header("x-dregg-credential") {
        if !h.is_empty() {
            return Some(h.to_string());
        }
    }
    if let Some(auth) = req.header("authorization") {
        if let Some(tok) = auth.strip_prefix("Bearer ") {
            if tok.starts_with("dga1_") {
                return Some(tok.trim().to_string());
            }
        }
    }
    None
}

fn extract_break_glass(req: &Request) -> Option<String> {
    req.header("x-dregg-break-glass")
        .filter(|h| !h.is_empty())
        .map(str::to_string)
}

fn handle_auth(req: &Request, ctx: &Ctx) -> Vec<u8> {
    let cfg = ctx.cfg();
    let query_cap = req.query_get("cap");
    let fwd_host = req
        .header("x-forwarded-host")
        .or_else(|| req.header("host"));
    let required_cap = cfg.required_cap(query_cap, fwd_host);
    let attempted_break_glass = req
        .header("x-dregg-break-glass")
        .map(|h| !h.is_empty())
        .unwrap_or(false);

    let input = AuthInput {
        credential: extract_credential(req, cfg),
        break_glass: extract_break_glass(req),
        required_cap: required_cap.clone(),
        now: ctx.now,
    };

    let verdict = decide(cfg, &input);
    match &verdict {
        Verdict::Admit { how, cap } => {
            let subject = input
                .credential
                .as_deref()
                .and_then(subject_of)
                .unwrap_or_else(|| "dregg:break-glass".to_string());
            if how.contains("break-glass") {
                Metrics::incr(&ctx.metrics().break_glass);
                // A successful break-glass clears any accumulated failure count.
                ctx.rt.lockout.record_success(&ctx.client.ip);
            }
            Metrics::incr(&ctx.metrics().admit);
            ctx.audit(
                AuditRecord::new("auth")
                    .str("decision", "admit")
                    .str("how", how)
                    .opt_str("cap", cap.as_deref())
                    .str("subject", &subject)
                    .int("status", 200),
            );
            let mut headers = vec![
                ("X-Dregg-Auth".to_string(), how.clone()),
                ("X-Dregg-Subject".to_string(), subject),
            ];
            if let Some(cap) = cap {
                headers.push(("X-Dregg-Cap".to_string(), cap.clone()));
            }
            response(
                200,
                "text/plain; charset=utf-8",
                "authorized",
                &headers,
                ctx.keep_alive,
            )
        }
        Verdict::Deny {
            reason,
            authenticated,
        } => {
            let status = verdict.status();
            if reason.starts_with("credential is revoked") {
                Metrics::incr(&ctx.metrics().revoked_hits);
            }
            // A failed break-glass attempt is a brute-force signal → arm lockout.
            if attempted_break_glass {
                Metrics::incr(&ctx.metrics().break_glass_fail);
                ctx.rt.lockout.record_failure(&ctx.client.ip, ctx.now_ms);
            }
            if status == 403 {
                Metrics::incr(&ctx.metrics().deny_403);
            } else {
                Metrics::incr(&ctx.metrics().deny_401);
            }
            ctx.audit(
                AuditRecord::new("auth")
                    .str("decision", "deny")
                    .bool("authenticated", *authenticated)
                    .opt_str("cap", required_cap.as_deref())
                    .str("reason", reason)
                    .int("status", status as u64),
            );

            let wants_html = req
                .header("accept")
                .map(|a| a.contains("text/html"))
                .unwrap_or(false);
            if wants_html && !*authenticated {
                let rd = req.header("x-forwarded-uri").unwrap_or("/");
                let loc = format!("{}/login?rd={}", cfg.login_base, url_encode(rd));
                redirect(302, &loc, &[], ctx.keep_alive)
            } else if status == 403 {
                response(
                    403,
                    "text/plain; charset=utf-8",
                    &format!("webauth: forbidden — {reason}\n"),
                    &[],
                    ctx.keep_alive,
                )
            } else {
                response(
                    401,
                    "text/plain; charset=utf-8",
                    &format!("webauth: {reason}\n"),
                    &[("WWW-Authenticate".to_string(), "Dregg-Cap".to_string())],
                    ctx.keep_alive,
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// /whoami — session introspection (for the frontend, not the proxy)
// ---------------------------------------------------------------------------

fn handle_whoami(req: &Request, ctx: &Ctx) -> Vec<u8> {
    let cfg = ctx.cfg();
    let enc = extract_credential(req, cfg);
    let (authed, subject, wire_err) = match enc.as_deref() {
        None => (false, None, false),
        Some(enc) => match session_identity(cfg, enc, ctx.now) {
            Ok(subj) => (subj.is_some(), subj, false),
            Err(()) => (false, None, true),
        },
    };
    if wire_err {
        // The credential wire form could not be read (a schema bump) — a 500, not
        // a misleading "not authenticated".
        Metrics::incr(&ctx.metrics().server_error);
        return server_error_json(ctx.keep_alive);
    }
    let mut obj = crate::json::JsonObject::new();
    obj.bool("authenticated", authed);
    match &subject {
        Some(s) => {
            obj.str("subject", s);
        }
        None => {
            obj.null("subject");
        }
    }
    response(
        200,
        "application/json; charset=utf-8",
        &obj.finish(),
        &[],
        ctx.keep_alive,
    )
}

/// The verified subject of a presented session, `Ok(None)` if the session is not
/// genuine, `Err(())` if the credential wire form is unreadable (→ 500). Shared
/// by `/whoami` and the login `POST` so there is ONE definition of "a real
/// session" (decode → revoke deny-set → chain genuineness → temporal validity).
fn session_identity(cfg: &WebAuthConfig, enc: &str, now: u64) -> Result<Option<String>, ()> {
    let Ok(credential) = Credential::decode(enc) else {
        return Ok(None);
    };
    let subject = subject_of_credential(&credential);
    if cfg.is_revoked(&credential.tail_hex(), subject.as_deref()) {
        return Ok(None);
    }
    let Some(pk_hex) = cfg.root_pubkey_hex.as_deref() else {
        return Ok(None);
    };
    let Ok(root) = PublicKey::from_hex(pk_hex) else {
        return Ok(None);
    };
    if credential.verify_chain(&root).is_err() {
        return Ok(None);
    }
    // Honor BOTH ends of the validity window (expired OR not-yet-valid is not a
    // live session), and surface an unreadable wire as a 500.
    match credential.validity(now) {
        Ok(Validity::Valid) => Ok(subject),
        Ok(Validity::Expired) | Ok(Validity::NotYetValid) => Ok(None),
        Err(_) => Err(()),
    }
}

// ---------------------------------------------------------------------------
// /login — the login flow
// ---------------------------------------------------------------------------

fn login_challenge(ctx: &Ctx) -> Vec<u8> {
    let cfg = ctx.cfg();
    let challenge = crate::challenge::issue(&cfg.challenge_key, ctx.now, cfg.challenge_ttl_secs);
    let not_after = ctx.now + cfg.challenge_ttl_secs;
    let ctx_hex = crate::credext::hex(crate::challenge::LOGIN_CHALLENGE_CTX);
    let mut obj = crate::json::JsonObject::new();
    obj.str("challenge", &challenge)
        .int("not_after", not_after as i64)
        .str("alg", "ed25519-pop")
        .str("context_hex", &ctx_hex);
    response(
        200,
        "application/json; charset=utf-8",
        &obj.finish(),
        &[],
        ctx.keep_alive,
    )
}

fn login_page(req: &Request, ctx: &Ctx) -> Vec<u8> {
    let cfg = ctx.cfg();
    let rd = req.query_get("rd").unwrap_or("/");
    let rd_attr = html_escape(rd);
    let action = format!("{}/login", cfg.login_base);
    let login_base_js = crate::json::escape(&cfg.login_base);
    let page = format!(
        r#"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Sign in with your capability</title>
<style>
  body {{ font-family: system-ui, sans-serif; max-width: 40rem; margin: 4rem auto; padding: 0 1rem; color: #1a1a2e; }}
  h1 {{ font-size: 1.4rem; }}
  textarea {{ width: 100%; height: 7rem; font-family: ui-monospace, monospace; font-size: 0.85rem; }}
  button {{ padding: 0.6rem 1.2rem; font-size: 1rem; cursor: pointer; }}
  .hint {{ color: #555; font-size: 0.9rem; }}
  code {{ background: #f0f0f5; padding: 0 0.2rem; }}
</style>
</head>
<body>
<h1>Sign in with your capability</h1>
<p class="hint">Paste the <code>dga1_…</code> capability your wallet holds for this
surface. It is verified offline against the surface's required capability; no
password, no node round-trip. Attenuated capabilities only reach the surfaces they
were narrowed to.</p>
<form method="POST" action="{action}" id="loginform">
  <input type="hidden" name="rd" value="{rd_attr}">
  <input type="hidden" name="challenge" id="challenge">
  <input type="hidden" name="signature" id="signature">
  <p><textarea name="credential" id="credential" placeholder="dga1_..." autofocus></textarea></p>
  <p><button type="submit">Present capability</button></p>
</form>
<p class="hint" id="wallet"></p>
<script>
const base = {login_base_js};
if (window.dregg && typeof window.dregg.presentCredential === 'function') {{
  const el = document.getElementById('wallet');
  const btn = document.createElement('button');
  btn.textContent = 'Sign in with your wallet';
  btn.onclick = async () => {{
    try {{
      const credential = await window.dregg.presentCredential({{ origin: location.host }});
      const chal = await (await fetch(base + '/login/challenge')).json();
      let signature = '';
      if (typeof window.dregg.signChallenge === 'function') {{
        signature = await window.dregg.signChallenge({{ credential, challenge: chal.challenge }});
      }}
      document.getElementById('credential').value = credential;
      document.getElementById('challenge').value = signature ? chal.challenge : '';
      document.getElementById('signature').value = signature;
      document.getElementById('loginform').submit();
    }} catch (e) {{ el.textContent = 'wallet declined: ' + e; }}
  }};
  el.appendChild(btn);
}}
</script>
</body>
</html>
"#
    );
    response(200, "text/html; charset=utf-8", &page, &[], ctx.keep_alive)
}

fn field<'a>(form: &'a [(String, String)], key: &str) -> Option<&'a str> {
    form.iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
        .filter(|v| !v.trim().is_empty())
}

fn login_submit(req: &Request, ctx: &Ctx) -> Vec<u8> {
    let cfg = ctx.cfg();
    let wants_json = req
        .header("accept")
        .map(|a| a.contains("application/json"))
        .unwrap_or(false)
        || {
            let form = parse_query(&req.body);
            field(&form, "format") == Some("json")
        };

    // Content-Type validation: this endpoint consumes a urlencoded form. Reject a
    // wrong/absent type with 415 rather than silently mis-parsing.
    match req.header("content-type") {
        Some(ct)
            if ct
                .to_ascii_lowercase()
                .contains("application/x-www-form-urlencoded") => {}
        Some(_) => {
            Metrics::incr(&ctx.metrics().bad_request);
            return login_error(
                wants_json,
                415,
                "POST /login expects application/x-www-form-urlencoded",
                ctx.keep_alive,
            );
        }
        None => {
            Metrics::incr(&ctx.metrics().bad_request);
            return login_error(
                wants_json,
                415,
                "POST /login requires a Content-Type of application/x-www-form-urlencoded",
                ctx.keep_alive,
            );
        }
    }

    let form = parse_query(&req.body);
    let rd = field(&form, "rd").unwrap_or("/").to_string();

    let fail = |status: u16, reason: &str| {
        Metrics::incr(&ctx.metrics().logins_fail);
        login_error(wants_json, status, reason, ctx.keep_alive)
    };

    let Some(cred_str) = field(&form, "credential") else {
        return fail(400, "no credential presented");
    };
    let cred_str = cred_str.trim();

    let credential = match Credential::decode(cred_str) {
        Ok(c) => c,
        Err(_) => return fail(400, "that is not a valid dga1_ capability"),
    };

    let now = ctx.now;

    // Proof-of-possession, if a challenge + signature were supplied.
    match (field(&form, "challenge"), field(&form, "signature")) {
        (Some(challenge), Some(sig_hex)) => {
            if let Err(e) = crate::challenge::verify(&cfg.challenge_key, challenge, now) {
                ctx.rt.lockout.record_failure(&ctx.client.ip, ctx.now_ms);
                return fail(401, &format!("challenge rejected: {e}"));
            }
            // Genuine single-use: consume the nonce; a replay within the TTL is
            // rejected here even though the MAC still validates.
            if let Some((nonce, exp)) = crate::challenge::nonce_and_exp(challenge) {
                if !ctx.rt.replay.consume(nonce, exp, now) {
                    Metrics::incr(&ctx.metrics().replay_blocked);
                    return fail(401, "challenge already used (replay) — request a fresh one");
                }
            }
            let Some(sig) = decode_sig64(sig_hex) else {
                return fail(400, "signature is not 64 hex-encoded bytes");
            };
            let msg = crate::challenge::signing_message(challenge);
            let pubkey = match credential.try_proof_public() {
                Ok(pk) => pk,
                Err(_) => {
                    Metrics::incr(&ctx.metrics().server_error);
                    return login_error(
                        wants_json,
                        500,
                        "credential wire form unreadable (schema mismatch)",
                        ctx.keep_alive,
                    );
                }
            };
            if !verify_pop(&pubkey, &msg, &sig) {
                Metrics::incr(&ctx.metrics().pop_fail);
                ctx.rt.lockout.record_failure(&ctx.client.ip, ctx.now_ms);
                return fail(
                    401,
                    "proof-of-possession failed: signature does not verify under the credential's tail key",
                );
            }
        }
        (Some(_), None) | (None, Some(_)) => {
            return fail(
                400,
                "both `challenge` and `signature` are required for proof-of-possession login",
            );
        }
        (None, None) => { /* paste fallback — no PoP */ }
    }

    // Genuine-issuance gate: chain-verify under the issuer root and reject a token
    // outside its validity window (expired OR not-yet-valid).
    if let Some(pk_hex) = &cfg.root_pubkey_hex {
        match PublicKey::from_hex(pk_hex) {
            Ok(root) => {
                if credential.verify_chain(&root).is_err() {
                    return fail(
                        401,
                        "credential is not genuine under this service's issuer root",
                    );
                }
            }
            Err(_) => { /* misconfigured root — /auth will fail closed anyway */ }
        }
    }
    match credential.validity(now) {
        Ok(Validity::Valid) => {}
        Ok(Validity::Expired) => return fail(401, "credential has already expired"),
        Ok(Validity::NotYetValid) => {
            return fail(
                401,
                "credential is not valid yet (its start time is in the future)",
            );
        }
        Err(_) => {
            Metrics::incr(&ctx.metrics().server_error);
            return login_error(
                wants_json,
                500,
                "credential wire form unreadable (schema mismatch)",
                ctx.keep_alive,
            );
        }
    }

    // Success: clear any brute-force lockout state and mint the session cookie.
    ctx.rt.lockout.record_success(&ctx.client.ip);
    Metrics::incr(&ctx.metrics().logins_ok);

    let subject = subject_of(cred_str).unwrap_or_else(|| "dregg:unknown".to_string());
    let max_age = cfg.session_ttl_secs.unwrap_or(86_400);
    let cookie = set_cookie(
        &cfg.cookie_name,
        cred_str,
        cfg.cookie_domain.as_deref(),
        max_age,
    );
    ctx.audit(
        AuditRecord::new("login")
            .str("decision", "ok")
            .str("subject", &subject)
            .int("status", if wants_json { 200 } else { 302 }),
    );

    if wants_json {
        let expires = now + max_age;
        let mut obj = crate::json::JsonObject::new();
        obj.str("session", cred_str)
            .str("subject", &subject)
            .int("expires", expires as i64);
        response(
            200,
            "application/json; charset=utf-8",
            &obj.finish(),
            &[("Set-Cookie".to_string(), cookie)],
            ctx.keep_alive,
        )
    } else {
        redirect(
            302,
            &safe_redirect(&rd),
            &[("Set-Cookie".to_string(), cookie)],
            ctx.keep_alive,
        )
    }
}

fn login_error(wants_json: bool, status: u16, reason: &str, keep_alive: bool) -> Vec<u8> {
    if wants_json {
        let mut obj = crate::json::JsonObject::new();
        obj.str("error", reason);
        response(
            status,
            "application/json; charset=utf-8",
            &obj.finish(),
            &[],
            keep_alive,
        )
    } else {
        let page = format!(
            "<p>Login failed: {}. <a href=\"/login\">try again</a></p>",
            html_escape(reason)
        );
        response(status, "text/html; charset=utf-8", &page, &[], keep_alive)
    }
}

fn decode_sig64(s: &str) -> Option<[u8; 64]> {
    let s = s.trim();
    if s.len() != 128 || !s.is_ascii() {
        return None;
    }
    let mut out = [0u8; 64];
    for (i, chunk) in s.as_bytes().chunks_exact(2).enumerate() {
        let hi = (chunk[0] as char).to_digit(16)?;
        let lo = (chunk[1] as char).to_digit(16)?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Some(out)
}

fn logout(ctx: &Ctx) -> Vec<u8> {
    let cfg = ctx.cfg();
    let cookie = clear_cookie(&cfg.cookie_name, cfg.cookie_domain.as_deref());
    let loc = format!("{}/login", cfg.login_base);
    redirect(
        302,
        &loc,
        &[("Set-Cookie".to_string(), cookie)],
        ctx.keep_alive,
    )
}

fn safe_redirect(rd: &str) -> String {
    if rd.starts_with('/') && !rd.starts_with("//") {
        rd.to_string()
    } else {
        "/".to_string()
    }
}

// ---------------------------------------------------------------------------
// Cookie + response helpers
// ---------------------------------------------------------------------------

fn set_cookie(name: &str, value: &str, domain: Option<&str>, max_age: u64) -> String {
    let mut c =
        format!("{name}={value}; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age={max_age}");
    if let Some(d) = domain {
        c.push_str(&format!("; Domain={d}"));
    }
    c
}

fn clear_cookie(name: &str, domain: Option<&str>) -> String {
    let mut c = format!("{name}=; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age=0");
    if let Some(d) = domain {
        c.push_str(&format!("; Domain={d}"));
    }
    c
}

fn text(status: u16, body: &str, keep_alive: bool) -> Vec<u8> {
    response(status, "text/plain; charset=utf-8", body, &[], keep_alive)
}
fn text_ct(status: u16, ct: &str, body: &str, keep_alive: bool) -> Vec<u8> {
    response(status, ct, body, &[], keep_alive)
}
fn too_many(keep_alive: bool, reason: &str) -> Vec<u8> {
    response(
        429,
        "text/plain; charset=utf-8",
        &format!("webauth: {reason}\n"),
        &[("Retry-After".to_string(), "2".to_string())],
        keep_alive,
    )
}
fn bad_request(reason: &str, keep_alive: bool) -> Vec<u8> {
    response(
        400,
        "text/plain; charset=utf-8",
        &format!("webauth: {reason}\n"),
        &[],
        keep_alive,
    )
}
fn service_unavailable() -> Vec<u8> {
    // Sent from the accept thread when the pool is saturated (no keep-alive).
    response(
        503,
        "text/plain; charset=utf-8",
        "webauth: overloaded, retry shortly\n",
        &[("Retry-After".to_string(), "1".to_string())],
        false,
    )
}
fn server_error_json(keep_alive: bool) -> Vec<u8> {
    let mut obj = crate::json::JsonObject::new();
    obj.str("error", "internal error reading the credential");
    response(
        500,
        "application/json; charset=utf-8",
        &obj.finish(),
        &[],
        keep_alive,
    )
}

fn redirect(status: u16, location: &str, extra: &[(String, String)], keep_alive: bool) -> Vec<u8> {
    let mut headers = vec![("Location".to_string(), location.to_string())];
    headers.extend_from_slice(extra);
    response(
        status,
        "text/plain; charset=utf-8",
        "redirecting",
        &headers,
        keep_alive,
    )
}

fn response(
    status: u16,
    content_type: &str,
    body: &str,
    headers: &[(String, String)],
    keep_alive: bool,
) -> Vec<u8> {
    let reason = status_reason(status);
    let mut out = format!("HTTP/1.1 {status} {reason}\r\n");
    out.push_str(&format!("Content-Type: {content_type}\r\n"));
    out.push_str(&format!("Content-Length: {}\r\n", body.len()));
    out.push_str(if keep_alive {
        "Connection: keep-alive\r\n"
    } else {
        "Connection: close\r\n"
    });
    for (k, v) in headers {
        out.push_str(&format!("{k}: {v}\r\n"));
    }
    out.push_str("\r\n");
    let mut bytes = out.into_bytes();
    bytes.extend_from_slice(body.as_bytes());
    bytes
}

fn status_reason(status: u16) -> &'static str {
    match status {
        200 => "OK",
        302 => "Found",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        415 => "Unsupported Media Type",
        429 => "Too Many Requests",
        500 => "Internal Server Error",
        503 => "Service Unavailable",
        _ => "Status",
    }
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

fn url_encode(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' | b'/' => {
                out.push(b as char)
            }
            _ => out.push_str(&format!("%{b:02X}")),
        }
    }
    out
}

// ===========================================================================
// Tests — the routing + the 200/401/403 split + the forge-proof subject echo
// over synthesized requests (no socket), PLUS integration tests that bind a real
// socket and drive raw HTTP bytes (keep-alive, chunked, oversized, malformed,
// slow-loris) through `serve`/`handle_conn`, and unit tests for rate limiting,
// lockout, single-use PoP, hot revocation, and the /metrics surface.
// ===========================================================================
#[cfg(test)]
mod tests {
    include!("server_tests.rs");
}
