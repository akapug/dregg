//! `dreggnet-audit` — the INTERACTION ENVELOPE around every bot turn.
//!
//! Shared audit facility for `discord-bot`, `dreggnet-telegram`, `dreggnet-web`
//! per `docs/BOT-AUDIT-LOGGING-DESIGN.md`. (The design named this crate
//! `dregg-audit`; that package name was already taken by the ZK token-audit
//! crate at `audit/`, so the bot-envelope facility lives here as
//! `dreggnet-audit` — same design, non-colliding name.)
//!
//! The receipt chain records every committed MOVE. This crate records the
//! envelope the receipt chain never sees: who pressed/typed/POSTed what, on
//! which surface, attributed how strongly; what the frontend DECIDED (routed /
//! refused / gated / error); and what came back — including the `turn_hash`
//! join to the receipt chain when a turn landed, and every refusal that
//! committed nothing.
//!
//! Storage: append-only JSONL, one event per line, in a per-deploy directory.
//! Files are named PER PROCESS — `audit-YYYY-MM-DD.<platform>-<pid>.NN.jsonl` —
//! so several services can share ONE correlate-able directory without ever
//! contending on a single file (concurrent `O_APPEND` + a looping `write_all`
//! can interleave partial lines — the same tear class as the link registry);
//! the `.NN` suffix byte-rolls a burst so no single file grows unbounded. A
//! shared dir + `auditq correlate` therefore joins a chain across services.
//! Non-blocking: the hot path serializes once and `try_send`s to a writer
//! thread; a full queue DROPS the line (counted, reported on the next
//! successful write) — a turn never waits on the log. Durability is ON by
//! default: the writer `fsync`s the tail periodically and on drain, OFF the
//! per-line hot path (`DREGG_AUDIT_FSYNC=0` opts out); [`AuditLog::sync`] is the
//! shutdown/test barrier that makes everything emitted-so-far durable.
//!
//! Secret hygiene is a HARD RULE: bot tokens, `BOT_SECRET`/master secrets,
//! derived seeds, provider keys, and the raw Telegram initData string must
//! NEVER enter a record. Redaction happens AT the emit point (the module that
//! knows what it collected) via [`Input::redacted`]; [`find_leak`] backs the
//! standing canary tests here and in each frontend.

use serde::{Deserialize, Serialize};
use std::fs::{File, OpenOptions};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender, TrySendError, sync_channel};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Current schema version stamped into every event.
pub const SCHEMA_VERSION: u16 = 1;

/// Bounded queue depth between emitters and the writer thread.
const QUEUE_CAP: usize = 4096;

/// Default byte size at which a segment file rolls to the next `.NN` — bounds a
/// burst so no single file grows unbounded. Override with `DREGG_AUDIT_MAX_BYTES`.
const DEFAULT_MAX_BYTES: u64 = 64 * 1024 * 1024;

/// Default periodic-durability interval: the longest a written-but-unsynced tail
/// may sit before the writer `fsync`s it, batched OFF the per-line hot path.
/// Override with `DREGG_AUDIT_SYNC_MS`.
const DEFAULT_SYNC_MS: u64 = 1000;

// ─────────────────────────────────────────────────────────────────────────────
// Event shape (§3 of the design)
// ─────────────────────────────────────────────────────────────────────────────

/// One audited interaction. Serialized as a single JSON line. Schema-versioned.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AuditEvent {
    /// Schema version (see [`SCHEMA_VERSION`]).
    pub v: u16,
    /// Unix millis, assigned at emit.
    pub ts_ms: u64,
    /// Unique per interaction: 6-byte timestamp + 8-byte random, hex
    /// (sortable-ish, cheap).
    pub correlation_id: String,
    /// "discord" | "telegram" | "web" | "tg-miniapp".
    pub platform: String,
    pub actor: Actor,
    pub surface: Surface,
    pub input: Input,
    pub decision: Decision,
    pub outcome: AuditOutcome,
    /// The offering session, when one is in play (joins to the move-log file).
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub session_id: Option<String>,
    /// The offering key ("dungeon", "market", …), when known.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub offering: Option<String>,
}

impl AuditEvent {
    /// A fresh event: `v`/`ts_ms`/`correlation_id` assigned now, decision
    /// `routed`, outcome `None`. Fill decision/outcome/session via the
    /// `with_*` builders once the frontend has seen them (ingress and outcome
    /// are the same stack frame in all three frontends).
    pub fn new(platform: impl Into<String>, actor: Actor, surface: Surface, input: Input) -> Self {
        AuditEvent {
            v: SCHEMA_VERSION,
            ts_ms: now_ms(),
            correlation_id: correlation_id(),
            platform: platform.into(),
            actor,
            surface,
            input,
            decision: Decision::routed(),
            outcome: AuditOutcome::None,
            session_id: None,
            offering: None,
        }
    }

    pub fn with_decision(mut self, decision: Decision) -> Self {
        self.decision = decision;
        self
    }

    pub fn with_outcome(mut self, outcome: AuditOutcome) -> Self {
        self.outcome = outcome;
        self
    }

    pub fn with_session(mut self, session_id: impl Into<String>) -> Self {
        self.session_id = Some(session_id.into());
        self
    }

    pub fn with_offering(mut self, offering: impl Into<String>) -> Self {
        self.offering = Some(offering.into());
        self
    }

    /// Set the decision from its taxonomy words — the string-shaped twin of
    /// [`AuditEvent::with_decision`] for sites that compute `(kind, reason)`
    /// dynamically. `kind` must be one of the `DECISION_*` words.
    pub fn decided(mut self, kind: impl Into<String>, reason: impl Into<String>) -> Self {
        self.decision = Decision {
            kind: kind.into(),
            reason: reason.into(),
        };
        self
    }

    /// Reuse a caller-minted correlation id (so one request's gate + outcome
    /// events join, and the id can be pre-announced in a reply).
    pub fn correlated(mut self, correlation_id: impl Into<String>) -> Self {
        self.correlation_id = correlation_id.into();
        self
    }

    /// Attach the offering + session this interaction played in (both
    /// optional — the `Option`-shaped twin of [`AuditEvent::with_session`] /
    /// [`AuditEvent::with_offering`]).
    pub fn in_session(mut self, offering: Option<String>, session_id: Option<String>) -> Self {
        self.offering = offering;
        self.session_id = session_id;
        self
    }
}

/// Attribution grades — the codebase's own trust vocabulary.
pub const GRADE_ASSERTED: &str = "asserted";
pub const GRADE_CUSTODIAL: &str = "custodial";
pub const GRADE_INITDATA_VERIFIED: &str = "initdata-verified";
pub const GRADE_SIGNED: &str = "signed";
/// A refused auth gate: no attribution was earned, nothing is claimed.
pub const GRADE_UNATTRIBUTED: &str = "unattributed";
/// Process-initiated work (boot resume, chain reactor).
pub const GRADE_SYSTEM: &str = "system";

/// Who acted, and how strongly the attribution holds.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Actor {
    /// Platform-native id: Discord uid / Telegram uid / web cookie label.
    /// NOT a secret.
    pub platform_id: String,
    /// The derived dregg identity (hex pubkey / cell id), when derivable at
    /// the site. PUBLIC material only.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub dregg_identity: Option<String>,
    /// "asserted" (forgeable cookie) | "custodial" (bot-derived from platform
    /// uid) | "initdata-verified" (HMAC-checked Telegram attestation) |
    /// "signed" (user-held key).
    pub grade: String,
}

impl Actor {
    fn graded(platform_id: impl Into<String>, identity: Option<String>, grade: &str) -> Self {
        Actor {
            platform_id: platform_id.into(),
            dregg_identity: identity,
            grade: grade.to_string(),
        }
    }
    /// Forgeable web cookie / self-asserted label.
    pub fn asserted(platform_id: impl Into<String>) -> Self {
        Self::graded(platform_id, None, GRADE_ASSERTED)
    }
    /// Bot-derived identity from the platform uid (cipherclerk derivation).
    pub fn custodial(platform_id: impl Into<String>, dregg_identity: impl Into<String>) -> Self {
        Self::graded(platform_id, Some(dregg_identity.into()), GRADE_CUSTODIAL)
    }
    /// HMAC-verified Telegram Mini App initData attribution.
    pub fn initdata_verified(
        platform_id: impl Into<String>,
        dregg_identity: Option<String>,
    ) -> Self {
        Self::graded(platform_id, dregg_identity, GRADE_INITDATA_VERIFIED)
    }
    /// User-held Ed25519 key (act-signed): the strongest grade.
    pub fn signed(platform_id: impl Into<String>, actor_pubkey_hex: impl Into<String>) -> Self {
        Self::graded(platform_id, Some(actor_pubkey_hex.into()), GRADE_SIGNED)
    }
    /// No attribution was earned (a refused auth gate): nothing is claimed.
    pub fn unattributed() -> Self {
        Self::graded(GRADE_UNATTRIBUTED, None, GRADE_UNATTRIBUTED)
    }
    /// Process-initiated work (boot resume, chain reactor) — `what` names the
    /// initiator ("boot-resume", "bot-reactor", …).
    pub fn system(what: impl Into<String>) -> Self {
        Self::graded(what, None, GRADE_SYSTEM)
    }
    /// Attach (or replace) the derived dregg identity — for grades whose
    /// constructor does not carry one (e.g. an asserted cookie whose custodial
    /// identity IS derivable at the site). PUBLIC material only.
    pub fn with_identity(mut self, dregg_identity: impl Into<String>) -> Self {
        self.dregg_identity = Some(dregg_identity.into());
        self
    }
}

/// Hex-encode a 32-byte hash — the `turn_hash` wire form (64 lowercase hex
/// chars), the receipt-chain join every frontend stamps into
/// [`AuditOutcome::Landed`].
pub fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        use std::fmt::Write as _;
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// Where the interaction entered. Serialized as lowercase snake_case strings.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Surface {
    /// Slash command / TG text command.
    Command,
    /// Discord button/select press.
    Component,
    /// Discord modal submit.
    Modal,
    /// TG inline-button callback.
    Callback,
    /// TG Mini App sendData round-trip.
    WebAppData,
    /// Web catalog GET/POST (incl. act-signed).
    Http,
    /// `/tg` Mini App authenticated routes.
    InitData,
    /// Channel message driving a turn (hermes_channel).
    Message,
    /// bot_reactor: turn fired from an on-chain command.
    ChainCommand,
    /// Boot-time session resume decision.
    Resume,
}

/// What was submitted. `detail` carries the typed substance — user content IS
/// the audit trail — EXCEPT on redact-listed inputs, which use
/// [`Input::redacted`] at the emit point.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Input {
    /// The command name / custom_id prefix / route, e.g. "descent",
    /// "offering:fire", "POST /tg/offerings/{key}/session/{id}/act".
    pub kind: String,
    /// `{turn, arg, text?}` for an act; subcommand + options for a slash
    /// command; callback_data for a press. SECRET-REDACTED where applicable.
    pub detail: serde_json::Value,
}

impl Input {
    pub fn new(kind: impl Into<String>, detail: serde_json::Value) -> Self {
        Input {
            kind: kind.into(),
            detail,
        }
    }
    /// An input whose substance must never be recorded (provider keys,
    /// credential modals). Records only WHAT CLASS of thing was collected.
    pub fn redacted(kind: impl Into<String>, label: &str) -> Self {
        Input {
            kind: kind.into(),
            detail: serde_json::json!({ "redacted": label }),
        }
    }
}

/// Decision kinds (the frontends all emit the SAME words).
pub const DECISION_ROUTED: &str = "routed";
pub const DECISION_REFUSED: &str = "refused";
pub const DECISION_GATED: &str = "gated";
pub const DECISION_ERROR: &str = "error";

/// What the frontend decided about the input, BEFORE/WITHOUT the substrate.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Decision {
    /// "routed" | "refused" | "gated" | "error".
    pub kind: String,
    /// Machine reason: "not_offered", "no_session", "stale_surface",
    /// "initdata:bad_hmac", "policy", "usage", "unknown_command",
    /// "sig:stale_counter", "resume:tampered", … Empty for "routed".
    pub reason: String,
}

impl Decision {
    /// The input reached the substrate (or a handler that owns the outcome).
    pub fn routed() -> Self {
        Decision {
            kind: DECISION_ROUTED.into(),
            reason: String::new(),
        }
    }
    /// Frontend-level refusal before the substrate (not_offered, usage, …).
    pub fn refused(reason: impl Into<String>) -> Self {
        Decision {
            kind: DECISION_REFUSED.into(),
            reason: reason.into(),
        }
    }
    /// An auth/policy gate stopped it (initdata:*, sig:*, policy, …).
    pub fn gated(reason: impl Into<String>) -> Self {
        Decision {
            kind: DECISION_GATED.into(),
            reason: reason.into(),
        }
    }
    /// The frontend itself failed while deciding.
    pub fn error(reason: impl Into<String>) -> Self {
        Decision {
            kind: DECISION_ERROR.into(),
            reason: reason.into(),
        }
    }
}

/// What came back. `Landed.turn_hash` is THE JOIN to the receipt chain
/// (`hex(TurnReceipt.turn_hash)`, 64 chars).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AuditOutcome {
    /// A turn landed and committed.
    Landed { turn_hash: String, ended: bool },
    /// The executor refused (anti-ghost: nothing committed).
    Refused { why: String },
    /// A verify ran: the report verdict.
    Verified { verified: bool, turns: u64 },
    /// The interaction never reached the substrate, or a read-only surface
    /// answered.
    None,
    /// Transport/HTTP/internal error, stringified (no secrets in Display
    /// impls — keep it that way).
    Error { what: String },
}

// ─────────────────────────────────────────────────────────────────────────────
// The log: non-blocking bounded queue → writer thread → O_APPEND JSONL (§4)
// ─────────────────────────────────────────────────────────────────────────────

enum Msg {
    Line(String),
    /// Block-until-drained barrier; the ack is sent after everything queued
    /// before it has been written and flushed.
    Sync(SyncSender<()>),
}

/// Handle to the audit log. Cheap to clone; every clone feeds the same writer
/// thread. Dropping the last clone disconnects the channel and the writer
/// drains + exits.
#[derive(Clone)]
pub struct AuditLog {
    tx: Option<SyncSender<Msg>>,
    dropped: Arc<AtomicU64>,
    platform: &'static str,
}

impl AuditLog {
    /// Open (or create) `dir` and spawn the writer thread. NEVER fails the
    /// caller: an unopenable dir warns once on stderr and returns a disabled
    /// log that counts drops — mirroring the session stores'
    /// degrade-with-warning posture.
    pub fn open(dir: impl Into<PathBuf>, platform: &'static str) -> AuditLog {
        Self::open_inner(dir.into(), platform, resolve_max_bytes())
    }

    /// The body behind [`AuditLog::open`], with an EXPLICIT per-segment byte cap
    /// (so the rotation tests can force a roll without racing the global
    /// `DREGG_AUDIT_MAX_BYTES` env against parallel tests). `fsync`, retention,
    /// and the sync interval still come from env — defaults are durable.
    fn open_inner(dir: PathBuf, platform: &'static str, max_bytes: u64) -> AuditLog {
        if let Err(e) = std::fs::create_dir_all(&dir) {
            eprintln!(
                "[dreggnet-audit] WARNING: cannot open audit dir {} ({e}); \
                 audit logging DISABLED for {platform} (drops counted)",
                dir.display()
            );
            return Self::disabled_with(platform);
        }
        let retain_days = std::env::var("DREGG_AUDIT_RETAIN_DAYS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok());
        let (tx, rx) = sync_channel::<Msg>(QUEUE_CAP);
        let dropped = Arc::new(AtomicU64::new(0));
        let writer = Writer {
            dir,
            // Per-process tag: two services sharing one dir land in DISTINCT
            // files, so neither `O_APPEND` nor byte-rolling ever contends.
            proc_tag: format!("{platform}-{}", std::process::id()),
            fsync: resolve_fsync(),
            retain_days,
            max_bytes,
            sync_interval: Duration::from_millis(resolve_sync_ms()),
            dropped: Arc::clone(&dropped),
            file: None,
            file_day: i64::MIN,
            seq: 0,
            bytes_written: 0,
            warned_io: AtomicBool::new(false),
        };
        std::thread::Builder::new()
            .name("dreggnet-audit-writer".into())
            .spawn(move || writer.run(rx))
            .expect("spawn audit writer thread");
        AuditLog {
            tx: Some(tx),
            dropped,
            platform,
        }
    }

    /// A deliberately-disabled log — every emit is a counted no-op.
    pub fn disabled() -> AuditLog {
        Self::disabled_with("disabled")
    }

    fn disabled_with(platform: &'static str) -> AuditLog {
        AuditLog {
            tx: None,
            dropped: Arc::new(AtomicU64::new(0)),
            platform,
        }
    }

    /// Resolve from env: `DREGG_AUDIT_DIR` ("off" → disabled; unset →
    /// `default_dir`, or disabled with one warning if there is no default).
    pub fn from_env(default_dir: Option<PathBuf>, platform: &'static str) -> AuditLog {
        Self::resolve(
            std::env::var("DREGG_AUDIT_DIR").ok().as_deref(),
            default_dir,
            platform,
        )
    }

    /// Pure resolution behind [`AuditLog::from_env`] (testable without env
    /// mutation).
    pub fn resolve(
        env_dir: Option<&str>,
        default_dir: Option<PathBuf>,
        platform: &'static str,
    ) -> AuditLog {
        match env_dir {
            Some("off") => Self::disabled_with(platform),
            Some(dir) if !dir.is_empty() => Self::open(PathBuf::from(dir), platform),
            _ => match default_dir {
                Some(dir) => Self::open(dir, platform),
                None => {
                    eprintln!(
                        "[dreggnet-audit] WARNING: no DREGG_AUDIT_DIR and no default \
                         audit dir for {platform}; audit logging DISABLED"
                    );
                    Self::disabled_with(platform)
                }
            },
        }
    }

    /// Whether emits can reach a writer (false = disabled/degraded).
    pub fn is_enabled(&self) -> bool {
        self.tx.is_some()
    }

    /// The platform tag this log was opened for.
    pub fn platform(&self) -> &'static str {
        self.platform
    }

    /// A fresh event pre-filled with this log's platform tag.
    pub fn new_event(&self, actor: Actor, surface: Surface, input: Input) -> AuditEvent {
        AuditEvent::new(self.platform, actor, surface, input)
    }

    /// NON-BLOCKING emit: serialize on the caller, `try_send` to the writer.
    /// A full queue (or a disabled log) DROPS the event and bumps the counter
    /// — never blocks a turn on a log write. The drop count is written as an
    /// `audit_meta` line on the next successful write. Takes the event by
    /// reference or by value (`Borrow`) — inline builder chains hand it over
    /// owned, retained events lend it.
    pub fn emit(&self, ev: impl std::borrow::Borrow<AuditEvent>) {
        let ev: &AuditEvent = ev.borrow();
        let Some(tx) = &self.tx else {
            self.dropped.fetch_add(1, Ordering::Relaxed);
            return;
        };
        let line = match serde_json::to_string(ev) {
            Ok(l) => l,
            Err(_) => {
                self.dropped.fetch_add(1, Ordering::Relaxed);
                return;
            }
        };
        match tx.try_send(Msg::Line(line)) {
            Ok(()) => {}
            Err(TrySendError::Full(_)) | Err(TrySendError::Disconnected(_)) => {
                self.dropped.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    /// Events dropped so far (full queue / disabled log / serialize failure).
    pub fn dropped_count(&self) -> u64 {
        self.dropped.load(Ordering::Relaxed)
    }

    /// Block until everything emitted before this call has been written and
    /// flushed. For shutdown paths and tests — NOT the hot path.
    pub fn sync(&self) {
        let Some(tx) = &self.tx else { return };
        let (ack_tx, ack_rx) = sync_channel::<()>(0);
        if tx.send(Msg::Sync(ack_tx)).is_ok() {
            let _ = ack_rx.recv();
        }
    }
}

/// Fresh correlation id: 6-byte unix-millis timestamp + 8-byte xorshift
/// random, hex (28 chars, sortable-ish). Also usable by callers that
/// pre-announce it in a reply.
pub fn correlation_id() -> String {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let seed = (now.as_nanos() as u64)
        ^ COUNTER.fetch_add(1, Ordering::Relaxed).rotate_left(32)
        ^ 0x9e37_79b9_7f4a_7c15;
    // xorshift64
    let mut x = if seed == 0 {
        0xdead_beef_cafe_f00d
    } else {
        seed
    };
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    let ts48 = now.as_millis() as u64 & 0xffff_ffff_ffff;
    format!("{ts48:012x}{x:016x}")
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

/// Durability posture: fsync is ON by default (a crash keeps the recorded tail);
/// `DREGG_AUDIT_FSYNC` in {`0`,`off`,`false`,`no`} opts OUT (still flushes, just
/// does not force the disk sync). The sync itself is batched off the hot path.
fn resolve_fsync() -> bool {
    match std::env::var("DREGG_AUDIT_FSYNC") {
        Ok(v) => !matches!(v.trim(), "0" | "off" | "false" | "no"),
        Err(_) => true,
    }
}

/// Per-segment byte cap from `DREGG_AUDIT_MAX_BYTES` (positive integer), else
/// [`DEFAULT_MAX_BYTES`].
fn resolve_max_bytes() -> u64 {
    std::env::var("DREGG_AUDIT_MAX_BYTES")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|n| *n > 0)
        .unwrap_or(DEFAULT_MAX_BYTES)
}

/// Periodic-fsync interval (ms) from `DREGG_AUDIT_SYNC_MS`, else
/// [`DEFAULT_SYNC_MS`]. Clamped to at least 1ms.
fn resolve_sync_ms() -> u64 {
    std::env::var("DREGG_AUDIT_SYNC_MS")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .map(|n| n.max(1))
        .unwrap_or(DEFAULT_SYNC_MS)
}

// ─────────────────────────────────────────────────────────────────────────────
// Writer thread: per-process segment files (day + byte rotation), batched fsync,
// retention prune. One write(2) per line; durability off the hot path.
// ─────────────────────────────────────────────────────────────────────────────

struct Writer {
    dir: PathBuf,
    /// `<platform>-<pid>` — the per-process filename segment.
    proc_tag: String,
    fsync: bool,
    retain_days: Option<u64>,
    /// Roll to the next `.NN` segment once the current file crosses this size.
    max_bytes: u64,
    /// How long a written-but-unsynced tail may sit before a periodic fsync.
    sync_interval: Duration,
    dropped: Arc<AtomicU64>,
    file: Option<File>,
    file_day: i64,
    /// The current segment's `.NN` sequence within `(file_day, proc_tag)`.
    seq: u32,
    /// Bytes appended to the current segment (its on-open length + our writes),
    /// so byte-rolling does not stat the file per line.
    bytes_written: u64,
    warned_io: AtomicBool,
}

impl Writer {
    fn run(mut self, rx: Receiver<Msg>) {
        let interval = self.sync_interval;
        // `dirty` = there are written lines not yet fsynced. We fsync at natural
        // idle points (queue drained) or after `interval`, NEVER per line.
        let mut dirty = false;
        let mut last_sync = Instant::now();
        loop {
            match rx.recv_timeout(interval) {
                Ok(msg) => {
                    self.handle(msg, &mut dirty, &mut last_sync);
                    // Coalesce the rest of a burst without blocking, so the
                    // fsync is amortized across the whole batch.
                    while let Ok(msg) = rx.try_recv() {
                        self.handle(msg, &mut dirty, &mut last_sync);
                    }
                }
                Err(RecvTimeoutError::Timeout) => {}
                Err(RecvTimeoutError::Disconnected) => break,
            }
            if dirty && last_sync.elapsed() >= interval {
                self.fsync_now();
                dirty = false;
                last_sync = Instant::now();
            }
        }
        // Channel disconnected: every queued line has been drained above; make
        // the tail durable and exit.
        self.fsync_now();
    }

    fn handle(&mut self, msg: Msg, dirty: &mut bool, last_sync: &mut Instant) {
        match msg {
            Msg::Line(line) => {
                self.write_line(line);
                *dirty = true;
            }
            Msg::Sync(ack) => {
                // The barrier: everything emitted before this call is now on
                // disk. FIFO delivery means all prior lines were already
                // written; fsync makes them durable, then we ack.
                self.fsync_now();
                *dirty = false;
                *last_sync = Instant::now();
                let _ = ack.send(());
            }
        }
    }

    /// Flush + (unless opted out) fsync the current segment. Off the hot path:
    /// called at idle/interval/shutdown/`sync()`, never per line.
    fn fsync_now(&mut self) {
        if let Some(f) = self.file.as_mut() {
            let _ = f.flush();
            if self.fsync {
                let _ = f.sync_data();
            }
        }
    }

    fn write_line(&mut self, mut line: String) {
        let today = (now_ms() / 86_400_000) as i64;
        if self.file.is_none() || self.file_day != today {
            self.roll_new_day(today);
        }
        if self.file.is_none() {
            self.dropped.fetch_add(1, Ordering::Relaxed);
            return;
        }

        // Report accumulated drops as their own meta line, first (tiny; no roll).
        let pending_drops = self.dropped.swap(0, Ordering::Relaxed);
        if pending_drops > 0 {
            let meta = format!(
                "{{\"v\":{SCHEMA_VERSION},\"ts_ms\":{},\"audit_meta\":{{\"dropped\":{pending_drops}}}}}\n",
                now_ms()
            );
            if !self.append(meta.as_bytes()) {
                // Fold the report back in; it will retry on the next write.
                self.dropped.fetch_add(pending_drops, Ordering::Relaxed);
            }
        }

        line.push('\n');
        // Byte-size rotation: roll to a fresh `.NN` before an append that would
        // cross the cap — UNLESS the current segment is empty, so a single line
        // larger than the cap still lands (in its own segment) not an infinite roll.
        if self.bytes_written > 0
            && self.bytes_written.saturating_add(line.len() as u64) > self.max_bytes
        {
            self.advance_segment();
            if self.file.is_none() {
                self.dropped.fetch_add(1, Ordering::Relaxed);
                return;
            }
        }
        if !self.append(line.as_bytes()) {
            self.dropped.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Append raw bytes to the current segment, updating the byte counter.
    /// Returns false (and disarms the file for a reopen on the next line) on I/O
    /// error, warning once.
    fn append(&mut self, bytes: &[u8]) -> bool {
        let Some(f) = self.file.as_mut() else {
            return false;
        };
        match f.write_all(bytes) {
            Ok(()) => {
                self.bytes_written = self.bytes_written.saturating_add(bytes.len() as u64);
                true
            }
            Err(e) => {
                if !self.warned_io.swap(true, Ordering::Relaxed) {
                    eprintln!(
                        "[dreggnet-audit] WARNING: audit write failed ({e}); \
                         dropping lines (counted)"
                    );
                }
                self.file = None;
                false
            }
        }
    }

    /// Open the day's segment: continue the current tail (a restart APPENDS to
    /// the live `.NN`, append-only) and keep byte-rolling from it. Prunes old
    /// files once the day's file is open.
    fn roll_new_day(&mut self, day: i64) {
        let (seq, len) = latest_segment(&self.dir, day, &self.proc_tag);
        self.file_day = day;
        self.open_segment(day, seq, len);
        if self.file.is_some()
            && let Some(retain) = self.retain_days
        {
            prune_old(&self.dir, day, retain);
        }
    }

    /// Roll to the next `.NN` on a byte-cap crossing.
    fn advance_segment(&mut self) {
        let next = self.seq.saturating_add(1);
        self.open_segment(self.file_day, next, 0);
    }

    fn open_segment(&mut self, day: i64, seq: u32, initial_len: u64) {
        let path = self.dir.join(audit_file_name(day, &self.proc_tag, seq));
        match OpenOptions::new().create(true).append(true).open(&path) {
            Ok(f) => {
                self.file = Some(f);
                self.seq = seq;
                self.bytes_written = initial_len;
            }
            Err(e) => {
                if !self.warned_io.swap(true, Ordering::Relaxed) {
                    eprintln!(
                        "[dreggnet-audit] WARNING: cannot open {} ({e}); \
                         dropping lines (counted)",
                        path.display()
                    );
                }
                self.file = None;
            }
        }
    }
}

/// The per-process, byte-sequenced segment file name (UTC):
/// `audit-YYYY-MM-DD.<platform>-<pid>.NN.jsonl`.
fn audit_file_name(days_since_epoch: i64, proc_tag: &str, seq: u32) -> String {
    let (y, m, d) = civil_from_days(days_since_epoch);
    format!("audit-{y:04}-{m:02}-{d:02}.{proc_tag}.{seq:02}.jsonl")
}

/// The `audit-YYYY-MM-DD` stem shared by every segment of a day.
fn date_stem(days_since_epoch: i64) -> String {
    let (y, m, d) = civil_from_days(days_since_epoch);
    format!("audit-{y:04}-{m:02}-{d:02}")
}

/// Highest existing segment seq for `(day, proc_tag)` in `dir`, and that file's
/// current byte length — so a restart APPENDS to the live tail (append-only) and
/// keeps byte-rolling from it, rather than clobbering or losing the count. No
/// existing segment → `(0, 0)`.
fn latest_segment(dir: &Path, day: i64, proc_tag: &str) -> (u32, u64) {
    let prefix = format!("{}.{proc_tag}.", date_stem(day));
    let mut best: Option<(u32, u64)> = None;
    if let Ok(entries) = std::fs::read_dir(dir) {
        for e in entries.flatten() {
            let name = e.file_name();
            let Some(name) = name.to_str() else { continue };
            let Some(seq_str) = name
                .strip_prefix(&prefix)
                .and_then(|r| r.strip_suffix(".jsonl"))
            else {
                continue;
            };
            let Ok(seq) = seq_str.parse::<u32>() else {
                continue;
            };
            let len = e.metadata().map(|m| m.len()).unwrap_or(0);
            match best {
                Some((bs, _)) if seq <= bs => {}
                _ => best = Some((seq, len)),
            }
        }
    }
    best.unwrap_or((0, 0))
}

/// Parse the day from an audit file name. Accepts BOTH the per-process form
/// `audit-YYYY-MM-DD.<proc>.NN.jsonl` and the legacy `audit-YYYY-MM-DD.jsonl`
/// (older stores stay readable). Returns days-since-epoch, or `None` for any
/// name that is not an audit file.
fn day_from_file_name(name: &str) -> Option<i64> {
    let rest = name.strip_prefix("audit-")?.strip_suffix(".jsonl")?;
    // The date is the fixed first 10 chars. A per-process name then carries a
    // `.` separator; the legacy name ends right there.
    let date = rest.get(0..10)?;
    let db = date.as_bytes();
    if db[4] != b'-' || db[7] != b'-' {
        return None;
    }
    match rest.as_bytes().get(10) {
        None | Some(b'.') => {}
        Some(_) => return None,
    }
    let y: i64 = date.get(0..4)?.parse().ok()?;
    let m: u32 = date.get(5..7)?.parse().ok()?;
    let d: u32 = date.get(8..10)?.parse().ok()?;
    if !(1..=12).contains(&m) || !(1..=31).contains(&d) {
        return None;
    }
    Some(days_from_civil(y, m, d))
}

/// Remove audit files strictly older than `retain_days` before `today`.
/// Append-only otherwise: nothing rewrites an existing line, ever.
fn prune_old(dir: &Path, today: i64, retain_days: u64) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        let Some(file_day) = day_from_file_name(name) else {
            continue;
        };
        if today - file_day > retain_days as i64 {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

// Howard Hinnant's civil-date algorithms (proleptic Gregorian, UTC).

/// Days-since-epoch → `(year, month, day)` (UTC, proleptic Gregorian). Public
/// for tool-side timestamp formatting (`auditq`).
pub fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// `(year, month, day)` (UTC) → days-since-epoch. Public for tool-side
/// time-range parsing (`auditq --since 2026-07-16`).
pub fn days_from_civil(y: i64, m: u32, d: u32) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = (y - era * 400) as u64;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) as u64 + 2) / 5 + d as u64 - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe as i64 - 719_468
}

// ─────────────────────────────────────────────────────────────────────────────
// Reading back (auditq + tests): torn-tail-tolerant JSONL readers
// ─────────────────────────────────────────────────────────────────────────────

/// Parse one audit file. Lines that do not parse as [`AuditEvent`] (a torn
/// final line after a crash, or `audit_meta` drop-count lines) are skipped
/// and counted in the second return.
pub fn read_events_file(path: &Path) -> std::io::Result<(Vec<AuditEvent>, usize)> {
    let content = std::fs::read_to_string(path)?;
    let mut events = Vec::new();
    let mut skipped = 0usize;
    for line in content.lines() {
        if line.trim().is_empty() {
            continue;
        }
        match serde_json::from_str::<AuditEvent>(line) {
            Ok(ev) => events.push(ev),
            Err(_) => skipped += 1,
        }
    }
    Ok((events, skipped))
}

/// Parse every `audit-*.jsonl` in `dir`, in filename (= date) order.
pub fn read_events_dir(dir: &Path) -> std::io::Result<(Vec<AuditEvent>, usize)> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)?
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| day_from_file_name(n).is_some())
        })
        .collect();
    files.sort();
    let mut events = Vec::new();
    let mut skipped = 0usize;
    for f in files {
        let (mut evs, s) = read_events_file(&f)?;
        events.append(&mut evs);
        skipped += s;
    }
    Ok((events, skipped))
}

// ─────────────────────────────────────────────────────────────────────────────
// Secret hygiene (§8): the canary primitive
// ─────────────────────────────────────────────────────────────────────────────

/// Return the first denylisted value found in `serialized`, if any. Backs the
/// standing canary tests: serialize representative events from each frontend
/// fixture and assert `find_leak(json, &[token, secret_hex, init_data]) ==
/// None`. Empty denylist entries never match.
pub fn find_leak<'a>(serialized: &str, denylist: &[&'a str]) -> Option<&'a str> {
    denylist
        .iter()
        .find(|s| !s.is_empty() && serialized.contains(**s))
        .copied()
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp_dir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "dreggnet-audit-test-{tag}-{}-{}",
            std::process::id(),
            correlation_id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn sample_event(platform: &str, sid: &str) -> AuditEvent {
        AuditEvent::new(
            platform,
            Actor::custodial("123456789", "ab".repeat(32)),
            Surface::Callback,
            Input::new(
                "offering:fire",
                serde_json::json!({ "turn": "fire", "arg": "goblin", "text": "attack the goblin!" }),
            ),
        )
        .with_session(sid)
        .with_offering("dungeon")
        .with_outcome(AuditOutcome::Landed {
            turn_hash: "cd".repeat(32),
            ended: false,
        })
    }

    #[test]
    fn event_round_trips_through_store() {
        let dir = tmp_dir("roundtrip");
        let log = AuditLog::open(&dir, "telegram");
        assert!(log.is_enabled());

        let ev = sample_event("telegram", "sess-42");
        log.emit(&ev);
        let refusal = log
            .new_event(
                Actor::asserted("cookie-7"),
                Surface::Http,
                Input::new(
                    "POST /offerings/market/session/s1/act",
                    serde_json::json!({"turn": "bid"}),
                ),
            )
            .with_decision(Decision::refused("not_offered"));
        log.emit(&refusal);
        log.sync();

        let (events, skipped) = read_events_dir(&dir).unwrap();
        assert_eq!(skipped, 0);
        assert_eq!(events.len(), 2);
        assert_eq!(events[0], ev);
        assert_eq!(events[1], refusal);
        // The receipt join survives the trip.
        assert_eq!(
            events[0].outcome,
            AuditOutcome::Landed {
                turn_hash: "cd".repeat(32),
                ended: false
            }
        );
        assert_eq!(events[1].decision, Decision::refused("not_offered"));
        assert_eq!(log.dropped_count(), 0);
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn store_survives_restart_append_only() {
        let dir = tmp_dir("restart");
        {
            let log = AuditLog::open(&dir, "web");
            log.emit(&sample_event("web", "sess-a"));
            log.sync();
        } // "process exit": last handle dropped, writer drains
        // A second "boot" appends; never rewrites.
        let before = std::fs::read_dir(&dir).unwrap().count();
        assert_eq!(before, 1, "one dated file after first run");
        {
            let log = AuditLog::open(&dir, "web");
            log.emit(&sample_event("web", "sess-b"));
            log.sync();
        }
        let (events, skipped) = read_events_dir(&dir).unwrap();
        assert_eq!(skipped, 0);
        assert_eq!(events.len(), 2, "restart appended, did not truncate");
        assert_eq!(events[0].session_id.as_deref(), Some("sess-a"));
        assert_eq!(events[1].session_id.as_deref(), Some("sess-b"));
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn torn_tail_line_is_skipped() {
        let dir = tmp_dir("torn");
        let log = AuditLog::open(&dir, "web");
        log.emit(&sample_event("web", "sess-t"));
        log.sync();
        drop(log);
        // Simulate a crash mid-write: append a torn (truncated) JSON line.
        let file = std::fs::read_dir(&dir)
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        let mut f = OpenOptions::new().append(true).open(&file).unwrap();
        f.write_all(b"{\"v\":1,\"ts_ms\":17").unwrap();
        drop(f);
        let (events, skipped) = read_events_file(&file).unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(skipped, 1, "torn tail counted, not fatal");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn secret_shaped_values_are_redacted_and_canary_catches_leaks() {
        // Fixture secrets, one per class in the §8 denylist.
        let bot_token = "MTIzNDU2Nzg5.FIXTURE.bot-token-fixture-value";
        let bot_secret_hex = "ee".repeat(32);
        let provider_key = "sk-fixture-provider-key-123456";
        let raw_init_data =
            "query_id=AAF1&user=%7B%22id%22%3A99%7D&auth_date=1752700000&hash=deadbeef00";
        let denylist = [
            bot_token,
            bot_secret_hex.as_str(),
            provider_key,
            raw_init_data,
        ];

        // The /key-class emit point records only the CLASS of what it took.
        let key_portin = AuditEvent::new(
            "discord",
            Actor::custodial("42", "ab".repeat(32)),
            Surface::Modal,
            Input::redacted("key:portin", "provider-key"),
        );
        // The Mini App emit point records the verified uid + auth_date, never
        // the raw initData string.
        let miniapp = AuditEvent::new(
            "tg-miniapp",
            Actor::initdata_verified("99", Some("cd".repeat(32))),
            Surface::InitData,
            Input::new(
                "POST /tg/offerings/dungeon/session/s9/act",
                serde_json::json!({ "turn": "go", "arg": "north", "auth_date": 1752700000u64 }),
            ),
        )
        .with_decision(Decision::gated("initdata:stale"));

        for ev in [&key_portin, &miniapp] {
            let json = serde_json::to_string(ev).unwrap();
            assert_eq!(
                find_leak(&json, &denylist),
                None,
                "no fixture secret may appear in an audit line: {json}"
            );
        }
        // The redaction really replaced the substance.
        let json = serde_json::to_string(&key_portin).unwrap();
        assert!(json.contains("\"redacted\":\"provider-key\""));

        // And the canary DOES catch a leak when an emit site regresses.
        let leaky = AuditEvent::new(
            "discord",
            Actor::custodial("42", "ab".repeat(32)),
            Surface::Modal,
            Input::new("key:portin", serde_json::json!({ "key": provider_key })),
        );
        let json = serde_json::to_string(&leaky).unwrap();
        assert_eq!(find_leak(&json, &denylist), Some(provider_key));

        // User content, identities, turn hashes ARE the trail — they stay.
        let json = serde_json::to_string(&sample_event("telegram", "s")).unwrap();
        assert!(json.contains("attack the goblin!"));
        assert!(json.contains(&"cd".repeat(32)));
    }

    #[test]
    fn disabled_log_counts_drops_and_never_blocks() {
        let log = AuditLog::disabled();
        assert!(!log.is_enabled());
        log.emit(&sample_event("web", "s"));
        log.emit(&sample_event("web", "s"));
        log.sync(); // no-op, returns immediately
        assert_eq!(log.dropped_count(), 2);
    }

    #[test]
    fn resolve_env_off_and_defaults() {
        assert!(!AuditLog::resolve(Some("off"), None, "web").is_enabled());
        assert!(!AuditLog::resolve(None, None, "web").is_enabled());
        let dir = tmp_dir("resolve");
        let log = AuditLog::resolve(None, Some(dir.clone()), "web");
        assert!(log.is_enabled());
        drop(log);
        let explicit = tmp_dir("resolve-explicit");
        let log = AuditLog::resolve(Some(explicit.to_str().unwrap()), None, "web");
        assert!(log.is_enabled());
        drop(log);
        std::fs::remove_dir_all(&dir).ok();
        std::fs::remove_dir_all(&explicit).ok();
    }

    #[test]
    fn date_math_and_segment_names() {
        // Known anchors — per-process, byte-sequenced names.
        assert_eq!(civil_from_days(0), (1970, 1, 1));
        assert_eq!(
            audit_file_name(0, "web-1", 0),
            "audit-1970-01-01.web-1.00.jsonl"
        );
        let d = days_from_civil(2026, 7, 17);
        assert_eq!(civil_from_days(d), (2026, 7, 17));
        assert_eq!(
            audit_file_name(d, "telegram-42", 3),
            "audit-2026-07-17.telegram-42.03.jsonl"
        );
        // Leap day round-trip.
        let leap = days_from_civil(2024, 2, 29);
        assert_eq!(civil_from_days(leap), (2024, 2, 29));
        // The reader recovers the day from the per-process names (incl. a
        // hyphen-bearing platform), the legacy name, and rejects non-audit files.
        assert_eq!(
            day_from_file_name("audit-2026-07-17.web-99.00.jsonl"),
            Some(d)
        );
        assert_eq!(
            day_from_file_name("audit-2026-07-17.tg-miniapp-7.12.jsonl"),
            Some(d)
        );
        assert_eq!(day_from_file_name("audit-2026-07-17.jsonl"), Some(d));
        assert_eq!(day_from_file_name("audit-index.sqlite"), None);
        assert_eq!(day_from_file_name("audit-2026-7-17.jsonl"), None);
        assert_eq!(day_from_file_name("audit-2026-07-17-web.jsonl"), None);
        // Today's writer file really is named for today.
        let today = (now_ms() / 86_400_000) as i64;
        assert_eq!(
            day_from_file_name(&audit_file_name(today, "web-1", 0)),
            Some(today)
        );
    }

    #[test]
    fn byte_size_rotation_rolls_and_reads_back_across_segments() {
        let dir = tmp_dir("byteroll");
        // A tiny per-segment cap so each event (well over 200 bytes serialized)
        // lands in its own `.NN`. Explicit cap avoids racing DREGG_AUDIT_MAX_BYTES.
        let log = AuditLog::open_inner(dir.clone(), "web", 200);
        for i in 0..4 {
            log.emit(&sample_event("web", &format!("s{i}")));
        }
        log.sync();
        drop(log);

        let segments = std::fs::read_dir(&dir)
            .unwrap()
            .flatten()
            .filter(|e| {
                e.file_name()
                    .to_str()
                    .is_some_and(|n| day_from_file_name(n).is_some())
            })
            .count();
        assert!(
            segments >= 2,
            "a burst past the byte cap rolled into multiple segments, got {segments}"
        );
        // Every event across the segments is read back, in order.
        let (events, skipped) = read_events_dir(&dir).unwrap();
        assert_eq!(skipped, 0);
        assert_eq!(events.len(), 4, "no event lost across a byte roll");
        for (i, ev) in events.iter().enumerate() {
            assert_eq!(ev.session_id.as_deref(), Some(format!("s{i}").as_str()));
        }
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn retention_prunes_only_old_audit_files() {
        let dir = tmp_dir("prune");
        let today = (now_ms() / 86_400_000) as i64;
        let old = audit_file_name(today - 10, "web-1", 0);
        let recent = audit_file_name(today - 2, "web-1", 0);
        let unrelated = "audit-index.sqlite";
        for name in [old.as_str(), recent.as_str(), unrelated] {
            std::fs::write(dir.join(name), b"x\n").unwrap();
        }
        prune_old(&dir, today, 7);
        assert!(
            !dir.join(&old).exists(),
            "10-day-old file pruned at retain=7"
        );
        assert!(dir.join(&recent).exists(), "2-day-old file kept");
        assert!(dir.join(unrelated).exists(), "non-audit files untouched");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn drop_counter_is_reported_in_stream() {
        let dir = tmp_dir("dropreport");
        let log = AuditLog::open(&dir, "web");
        // Simulate drops (as a full queue would produce), then a real write.
        log.dropped.fetch_add(3, Ordering::Relaxed);
        log.emit(&sample_event("web", "s"));
        log.sync();
        drop(log);
        let file = std::fs::read_dir(&dir)
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        let content = std::fs::read_to_string(&file).unwrap();
        assert!(
            content.contains("\"audit_meta\":{\"dropped\":3}"),
            "drop count surfaces in the stream: {content}"
        );
        // Meta lines are skipped (counted) by the reader, events still parse.
        let (events, skipped) = read_events_file(&file).unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(skipped, 1);
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn correlation_ids_are_unique_and_well_formed() {
        let mut seen = std::collections::HashSet::new();
        for _ in 0..1000 {
            let id = correlation_id();
            assert_eq!(id.len(), 28);
            assert!(id.chars().all(|c| c.is_ascii_hexdigit()));
            assert!(seen.insert(id), "correlation ids must not repeat");
        }
    }

    #[test]
    fn taxonomy_serializes_to_the_designed_words() {
        let ev = sample_event("discord", "s1");
        let json = serde_json::to_string(&ev).unwrap();
        assert!(json.contains("\"surface\":\"callback\""));
        assert!(json.contains("\"outcome\":{\"kind\":\"landed\""));
        assert!(json.contains("\"grade\":\"custodial\""));
        let gated = ev
            .with_decision(Decision::gated("sig:stale_counter"))
            .with_outcome(AuditOutcome::None);
        let json = serde_json::to_string(&gated).unwrap();
        assert!(
            json.contains("\"decision\":{\"kind\":\"gated\",\"reason\":\"sig:stale_counter\"}")
        );
        assert!(json.contains("\"outcome\":{\"kind\":\"none\"}"));
        let surfaces = [
            (Surface::Command, "command"),
            (Surface::WebAppData, "web_app_data"),
            (Surface::InitData, "init_data"),
            (Surface::ChainCommand, "chain_command"),
        ];
        for (s, want) in surfaces {
            assert_eq!(serde_json::to_string(&s).unwrap(), format!("\"{want}\""));
        }
    }
}
