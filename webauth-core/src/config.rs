// PORTED dregg-native from the prior operated layer (verbatim; unhex32 from credext).

//! Runtime configuration for the forward-auth service, read from the
//! environment (the compose / systemd path).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, RwLock};

/// The **revocation deny-set** with interior mutability, so a leaked token can be
/// killed *without a restart*. A cloned `Revocations` shares one underlying set
/// (an `Arc<RwLock<…>>`), so the background reload thread and every request
/// handler see the same live set: the server holds an `Arc<WebAuthConfig>`, the
/// reload thread holds a cheap clone of this handle, and a hot reload
/// ([`Revocations::replace_all`]) is visible to the next `/auth` immediately.
///
/// Entries are lowercased tail-commitment hex ([`crate::credext`] canonical) or a
/// `dregg:…` account subject; a read is a brief shared lock (auth is not a
/// high-frequency inner loop, so this is not a contention concern).
#[derive(Clone, Debug, Default)]
pub struct Revocations(Arc<RwLock<BTreeSet<String>>>);

impl Revocations {
    pub fn new() -> Self {
        Self::default()
    }
    /// Add one entry (lowercased). Interior mutability — takes `&self`.
    pub fn insert(&self, entry: impl Into<String>) {
        self.0
            .write()
            .expect("revocation lock not poisoned")
            .insert(entry.into().to_ascii_lowercase());
    }
    /// Is `entry` present (exact match; the caller lowercases tail hex)?
    pub fn contains(&self, entry: &str) -> bool {
        self.0
            .read()
            .expect("revocation lock not poisoned")
            .contains(entry)
    }
    pub fn is_empty(&self) -> bool {
        self.0
            .read()
            .expect("revocation lock not poisoned")
            .is_empty()
    }
    pub fn len(&self) -> usize {
        self.0.read().expect("revocation lock not poisoned").len()
    }
    /// Atomically replace the whole set (the hot-reload path).
    pub fn replace_all(&self, set: BTreeSet<String>) {
        *self.0.write().expect("revocation lock not poisoned") = set;
    }
    /// A snapshot copy of the current set.
    pub fn snapshot(&self) -> BTreeSet<String> {
        self.0.read().expect("revocation lock not poisoned").clone()
    }
}

impl From<BTreeSet<String>> for Revocations {
    fn from(set: BTreeSet<String>) -> Self {
        Self(Arc::new(RwLock::new(set)))
    }
}

/// The forward-auth service configuration.
#[derive(Clone, Debug)]
pub struct WebAuthConfig {
    /// Address to bind (`DREGG_WEBAUTH_BIND`, default `0.0.0.0:8099`).
    pub bind: String,
    /// The issuer's ed25519 public key, hex (`DREGG_WEBAUTH_ROOT_PUBKEY`).
    /// REQUIRED in production: credentials verify under this and only this key.
    pub root_pubkey_hex: Option<String>,
    /// Break-glass override token (`DREGG_WEBAUTH_BREAK_GLASS`). When set, a
    /// request presenting this exact token in the `X-Dregg-Break-Glass` header
    /// or `dregg_break_glass` cookie is admitted regardless of the cap flow —
    /// so the operator is never locked out if the cap flow breaks. Unset
    /// (default) disables the override entirely.
    pub break_glass: Option<String>,
    /// Maps a request Host (the surface) to its required capability, so the
    /// service can derive the cap from the `X-Forwarded-Host` Caddy passes
    /// when no explicit `?cap=` query is present. Read from
    /// `DREGG_WEBAUTH_HOST_CAPS` as `host=cap,host2=cap2`.
    pub host_caps: BTreeMap<String, String>,
    /// The cookie name carrying the session credential (default `dregg_session`).
    pub cookie_name: String,
    /// Cookie/redirect domain for the login flow (`DREGG_WEBAUTH_COOKIE_DOMAIN`).
    pub cookie_domain: Option<String>,
    /// The PUBLIC path prefix the login flow is reachable at, as seen by the
    /// browser through Caddy (`DREGG_WEBAUTH_LOGIN_BASE`, default empty). In the
    /// deployment Caddy maps `<base>/*` to this service (stripping the prefix),
    /// so `<base>` must be a path that does NOT collide with the gated upstream
    /// (grafana and ops both serve their own `/login`). Set it to e.g.
    /// `/.dregg-auth`; the `/auth` deny-redirect and the form action both honor it.
    pub login_base: String,
    /// The **revocation deny-set** — the cloud-side analogue of
    /// `Effect::RevokeCapability` (Tier 0 compromise response). A presented
    /// credential is refused, AFTER its signature/cap checks would otherwise
    /// admit it, iff EITHER its tail commitment hex
    /// (`Credential::tail_hex`) OR its account subject
    /// ([`crate::subject_of`]) appears here. Keying on the tail kills exactly one
    /// leaked session token; keying on the subject kills every session for a
    /// compromised account (the proactive "rotate-out" companion). Offline-
    /// distributable: a signed list the forward-auth service loads
    /// (`DREGG_WEBAUTH_REVOKED` inline, `DREGG_WEBAUTH_REVOKED_FILE` a path).
    ///
    /// HOT: this is interior-mutable ([`Revocations`]); the server polls
    /// `revoked_file` for changes and applies them live (see
    /// [`crate::server::serve`]), so adding a leaked token to the file kills it on
    /// the next `/auth` with no restart — delivering the compromise-response speed
    /// the Tier-0 design promises.
    pub revoked: Revocations,
    /// The inline (`DREGG_WEBAUTH_REVOKED`) entries, kept separately so a hot
    /// reload of `revoked_file` can re-union them (a reload replaces the whole
    /// set; the inline entries must survive it).
    pub revoked_inline: BTreeSet<String>,
    /// The path to the revocation file (`DREGG_WEBAUTH_REVOKED_FILE`), retained so
    /// the reload thread can re-read it when its mtime changes.
    pub revoked_file: Option<String>,
    /// How often (seconds) to poll `revoked_file` for changes and apply them
    /// live (`DREGG_WEBAUTH_REVOKED_RELOAD`, default 5; `0` disables hot reload).
    pub revoked_reload_secs: u64,
    /// Default Time-To-Live (seconds) stamped as a `NotAfter` expiry on a freshly
    /// minted / re-issued session credential (`DREGG_WEBAUTH_SESSION_TTL`, default
    /// 24h). Bounds the blast radius of a leaked bearer token even before it is
    /// explicitly revoked: it self-expires. `0`/unset on the mint path means "no
    /// default expiry" (the legacy behaviour), but the deployment SHOULD set it.
    /// Also caps the session cookie's `Max-Age`.
    pub session_ttl_secs: Option<u64>,
    /// The key that authenticates login **challenges** (the stateless
    /// proof-of-possession nonce). Set from `DREGG_WEBAUTH_CHALLENGE_KEY` (hex,
    /// 32 bytes); if unset a fresh per-process random key is generated (a pending
    /// challenge then simply does not survive a webauth restart — fine for a
    /// 2-minute window). Set it explicitly across replicas so a challenge issued
    /// by one instance verifies at another.
    pub challenge_key: [u8; 32],
    /// The login challenge lifetime in seconds (`DREGG_WEBAUTH_CHALLENGE_TTL`,
    /// default [`crate::challenge::DEFAULT_CHALLENGE_TTL_SECS`]).
    pub challenge_ttl_secs: u64,

    // ---- serving / operability limits (the socket server, not the core) -----
    /// Number of worker threads in the bounded pool that services connections
    /// (`DREGG_WEBAUTH_WORKERS`, `0` = auto from available parallelism). Replaces
    /// the prior unbounded thread-per-connection model.
    pub worker_threads: usize,
    /// The maximum number of connections that may be queued/in-flight before the
    /// accept loop sheds new connections with a `503` (`DREGG_WEBAUTH_MAX_INFLIGHT`,
    /// default 512). Backpressure — bounds memory/FDs under a connection flood.
    pub max_in_flight: usize,
    /// Maximum requests served on one keep-alive connection before it is closed
    /// (`DREGG_WEBAUTH_MAX_KEEPALIVE`, default 100; `1` disables keep-alive).
    pub max_keepalive_requests: u32,
    /// Sustained per-client request budget per minute on sensitive endpoints
    /// (`/auth`, `/login`, `/login/challenge`) — `DREGG_WEBAUTH_RATE_PER_MIN`,
    /// default 120; `0` disables rate limiting.
    pub rate_per_min: u32,
    /// Burst capacity for the per-client token bucket
    /// (`DREGG_WEBAUTH_RATE_BURST`, default 30).
    pub rate_burst: u32,
    /// Consecutive failed break-glass / proof-of-possession attempts from one
    /// client before an escalating lockout arms (`DREGG_WEBAUTH_LOCKOUT_THRESHOLD`,
    /// default 5; `0` disables lockout).
    pub lockout_threshold: u32,
    /// The first lockout window in seconds; it doubles per further failure up to
    /// `lockout_max_secs` (`DREGG_WEBAUTH_LOCKOUT_BASE`, default 2).
    pub lockout_base_secs: u64,
    /// The cap on the escalating lockout window in seconds
    /// (`DREGG_WEBAUTH_LOCKOUT_MAX`, default 900 = 15 min).
    pub lockout_max_secs: u64,
    /// Make the login proof-of-possession challenge genuinely SINGLE-USE via a
    /// bounded seen-nonce cache (`DREGG_WEBAUTH_POP_SINGLE_USE`, default true).
    /// When false, replay is only bounded by the ~120s challenge TTL.
    pub pop_single_use: bool,
    /// Emit a structured JSON audit line per decision to stderr
    /// (`DREGG_WEBAUTH_AUDIT`, default true).
    pub audit_log: bool,
    /// Trust a client-supplied `X-Forwarded-For` as the rate-limit / audit client
    /// identity (`DREGG_WEBAUTH_TRUST_XFF`, default false). Only enable when a
    /// trusted proxy sets it — otherwise a client forges its own throttle key.
    pub trust_forwarded_for: bool,
    /// Acknowledge that this edge runs behind a TLS-terminating trusted proxy on a
    /// private upstream (`DREGG_WEBAUTH_BEHIND_PROXY`, default false). This crate
    /// speaks plain HTTP/1.1 and its `Secure` cookie + no-forged-header discipline
    /// ASSUME that fronting. When false, `serve` logs a loud standalone-insecurity
    /// warning at startup (it does not refuse to run, so a `localhost` dev bind is
    /// still convenient).
    pub behind_proxy: bool,
}

/// The recommended default session lifetime: 24 hours. Short enough that a
/// leaked bearer token self-expires within a day, long enough not to nag a
/// working operator. Re-issued on each login.
pub const DEFAULT_SESSION_TTL_SECS: u64 = 24 * 60 * 60;

impl Default for WebAuthConfig {
    fn default() -> Self {
        Self {
            bind: "0.0.0.0:8099".to_string(),
            root_pubkey_hex: None,
            break_glass: None,
            host_caps: BTreeMap::new(),
            cookie_name: "dregg_session".to_string(),
            cookie_domain: None,
            login_base: String::new(),
            revoked: Revocations::new(),
            revoked_inline: BTreeSet::new(),
            revoked_file: None,
            revoked_reload_secs: 5,
            session_ttl_secs: Some(DEFAULT_SESSION_TTL_SECS),
            challenge_key: random_key(),
            challenge_ttl_secs: crate::challenge::DEFAULT_CHALLENGE_TTL_SECS,
            worker_threads: 0,
            max_in_flight: 512,
            max_keepalive_requests: 100,
            rate_per_min: 120,
            rate_burst: 30,
            lockout_threshold: 5,
            lockout_base_secs: 2,
            lockout_max_secs: 900,
            pop_single_use: true,
            audit_log: true,
            trust_forwarded_for: false,
            behind_proxy: false,
        }
    }
}

/// A fresh 32-byte key from OS randomness (the per-process challenge key when
/// `DREGG_WEBAUTH_CHALLENGE_KEY` is not set).
fn random_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    getrandom::fill(&mut k).expect("operating-system randomness is available");
    k
}

impl WebAuthConfig {
    /// Is `tail_hex` / `subject` revoked? Either matching the deny-set refuses.
    pub fn is_revoked(&self, tail_hex: &str, subject: Option<&str>) -> bool {
        if self.revoked.is_empty() {
            return false;
        }
        if self.revoked.contains(tail_hex) {
            return true;
        }
        matches!(subject, Some(s) if self.revoked.contains(s))
    }

    /// Read configuration from the environment.
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Ok(bind) = std::env::var("DREGG_WEBAUTH_BIND") {
            if !bind.trim().is_empty() {
                cfg.bind = bind;
            }
        }
        cfg.root_pubkey_hex = non_empty("DREGG_WEBAUTH_ROOT_PUBKEY");
        cfg.break_glass = non_empty("DREGG_WEBAUTH_BREAK_GLASS");
        cfg.cookie_domain = non_empty("DREGG_WEBAUTH_COOKIE_DOMAIN");
        if let Some(name) = non_empty("DREGG_WEBAUTH_COOKIE_NAME") {
            cfg.cookie_name = name;
        }
        if let Some(base) = non_empty("DREGG_WEBAUTH_LOGIN_BASE") {
            // Normalize: no trailing slash; the routes append `/login` etc.
            cfg.login_base = base.trim_end_matches('/').to_string();
        }
        if let Some(raw) = non_empty("DREGG_WEBAUTH_HOST_CAPS") {
            cfg.host_caps = parse_host_caps(&raw);
        }
        // The revocation deny-set: an inline comma/whitespace list and/or a file
        // of newline-separated entries (a tail hex or a `dregg:…` subject each).
        // The inline set is kept aside so a hot reload of the file re-unions it.
        let mut initial = BTreeSet::new();
        if let Some(raw) = non_empty("DREGG_WEBAUTH_REVOKED") {
            cfg.revoked_inline = parse_revoked(&raw);
            initial.extend(cfg.revoked_inline.iter().cloned());
        }
        if let Some(path) = non_empty("DREGG_WEBAUTH_REVOKED_FILE") {
            match std::fs::read_to_string(&path) {
                Ok(contents) => initial.extend(parse_revoked(&contents)),
                Err(_) => {
                    eprintln!("webauth-core: WARN revocation file `{path}` could not be read")
                }
            }
            cfg.revoked_file = Some(path);
        }
        cfg.revoked = initial.into();
        if let Some(v) = non_empty("DREGG_WEBAUTH_REVOKED_RELOAD") {
            if let Ok(n) = v.trim().parse::<u64>() {
                cfg.revoked_reload_secs = n;
            }
        }
        match std::env::var("DREGG_WEBAUTH_SESSION_TTL") {
            Ok(v) if !v.trim().is_empty() => {
                cfg.session_ttl_secs = v.trim().parse::<u64>().ok().filter(|n| *n > 0);
            }
            _ => {}
        }
        // The challenge-authentication key (hex, 32 bytes). If set, challenges
        // issued by any replica sharing it verify at every replica; if unset the
        // per-process random key from `Default` stands (single-instance safe).
        if let Some(hex) = non_empty("DREGG_WEBAUTH_CHALLENGE_KEY") {
            match crate::credext::unhex32(hex.trim()) {
                Ok(k) => cfg.challenge_key = k,
                Err(_) => eprintln!(
                    "webauth-core: WARN DREGG_WEBAUTH_CHALLENGE_KEY is not 64 hex chars — using a per-process random key"
                ),
            }
        }
        if let Some(v) = non_empty("DREGG_WEBAUTH_CHALLENGE_TTL") {
            if let Some(n) = v.trim().parse::<u64>().ok().filter(|n| *n > 0) {
                cfg.challenge_ttl_secs = n;
            }
        }

        // Serving / operability limits.
        if let Some(n) = env_parse::<usize>("DREGG_WEBAUTH_WORKERS") {
            cfg.worker_threads = n;
        }
        if let Some(n) = env_parse::<usize>("DREGG_WEBAUTH_MAX_INFLIGHT").filter(|n| *n > 0) {
            cfg.max_in_flight = n;
        }
        if let Some(n) = env_parse::<u32>("DREGG_WEBAUTH_MAX_KEEPALIVE").filter(|n| *n > 0) {
            cfg.max_keepalive_requests = n;
        }
        if let Some(n) = env_parse::<u32>("DREGG_WEBAUTH_RATE_PER_MIN") {
            cfg.rate_per_min = n;
        }
        if let Some(n) = env_parse::<u32>("DREGG_WEBAUTH_RATE_BURST").filter(|n| *n > 0) {
            cfg.rate_burst = n;
        }
        if let Some(n) = env_parse::<u32>("DREGG_WEBAUTH_LOCKOUT_THRESHOLD") {
            cfg.lockout_threshold = n;
        }
        if let Some(n) = env_parse::<u64>("DREGG_WEBAUTH_LOCKOUT_BASE").filter(|n| *n > 0) {
            cfg.lockout_base_secs = n;
        }
        if let Some(n) = env_parse::<u64>("DREGG_WEBAUTH_LOCKOUT_MAX").filter(|n| *n > 0) {
            cfg.lockout_max_secs = n;
        }
        if let Some(b) = env_bool("DREGG_WEBAUTH_POP_SINGLE_USE") {
            cfg.pop_single_use = b;
        }
        if let Some(b) = env_bool("DREGG_WEBAUTH_AUDIT") {
            cfg.audit_log = b;
        }
        if let Some(b) = env_bool("DREGG_WEBAUTH_TRUST_XFF") {
            cfg.trust_forwarded_for = b;
        }
        if let Some(b) = env_bool("DREGG_WEBAUTH_BEHIND_PROXY") {
            cfg.behind_proxy = b;
        }
        cfg
    }

    /// The capability required for a request, given the explicit `?cap=` query
    /// (Caddy's `forward_auth` copy_headers / query) and the forwarded Host.
    /// An explicit query wins; otherwise the host map is consulted.
    pub fn required_cap(&self, query_cap: Option<&str>, host: Option<&str>) -> Option<String> {
        if let Some(c) = query_cap {
            if !c.is_empty() {
                return Some(c.to_string());
            }
        }
        let host = host?;
        // Strip any port suffix from the Host header before matching.
        let host = host.split(':').next().unwrap_or(host);
        self.host_caps.get(host).cloned()
    }
}

fn non_empty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|v| !v.trim().is_empty())
}

/// Parse an env var as `T`, `None` if unset/blank/unparseable.
fn env_parse<T: std::str::FromStr>(key: &str) -> Option<T> {
    non_empty(key).and_then(|v| v.trim().parse::<T>().ok())
}

/// Parse an env var as a boolean (`1`/`true`/`yes`/`on` = true; `0`/`false`/
/// `no`/`off` = false; anything else / unset = `None`).
fn env_bool(key: &str) -> Option<bool> {
    match non_empty(key)?.trim().to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" | "on" => Some(true),
        "0" | "false" | "no" | "off" => Some(false),
        _ => None,
    }
}

/// Parse a revocation list — entries separated by commas, whitespace, or
/// newlines; `#`-prefixed lines are comments. Each entry is a credential tail
/// hex or a `dregg:…` subject. Lowercased so tail-hex matching is canonical.
pub fn parse_revoked(raw: &str) -> BTreeSet<String> {
    raw.lines()
        .flat_map(|line| {
            let line = line.split('#').next().unwrap_or("");
            line.split([',', ' ', '\t'])
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(|s| s.to_ascii_lowercase())
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Parse `host=cap,host2=cap2` into a map.
pub fn parse_host_caps(raw: &str) -> BTreeMap<String, String> {
    raw.split(',')
        .filter_map(|pair| {
            let (h, c) = pair.split_once('=')?;
            let h = h.trim();
            let c = c.trim();
            if h.is_empty() || c.is_empty() {
                return None;
            }
            Some((h.to_string(), c.to_string()))
        })
        .collect()
}
