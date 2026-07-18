//! # audit — the INTERACTION-ENVELOPE emitter (this crate's face of `dreggnet-audit`).
//!
//! docs/BOT-AUDIT-LOGGING-DESIGN.md §3–§4: one [`AuditEvent`] JSON line per interaction —
//! who pressed/typed what, on which surface, attributed how strongly, what the frontend
//! DECIDED, and what came back (the `turn_hash` join to the receipt chain on a landed turn;
//! the refusal reason otherwise). Refusals and errors are exactly the events the receipt
//! chain never records — this log is that trail.
//!
//! The event shape, writer thread, rotation/retention, and readers all live in the shared
//! [`dreggnet_audit`] facility (re-exported here); this module carries only the
//! telegram-deploy log resolution: [`init`] / [`log`] over `DREGG_AUDIT_DIR`, defaulting to
//! a sibling `audit/` beside `TELEGRAM_SESSION_DIR`.
//!
//! ## Secret hygiene (§8 — HARD RULES)
//! NEVER in an audit record: the bot token, `TELEGRAM_BOT_SECRET` / any master secret,
//! derived Ed25519 seeds, provider keys, the initData HMAC secret, the raw initData string.
//! FINE to log (they ARE the trail): platform uids, derived PUBLIC identities (pubkey hex),
//! turn hashes, session ids, offering keys, `{turn, arg}`, user free text. The standing
//! canary test below serializes representative events through [`find_leak`].

use std::path::PathBuf;
use std::sync::OnceLock;

pub use dreggnet_audit::{
    Actor, AuditEvent, AuditLog, AuditOutcome, Decision, GRADE_ASSERTED, GRADE_CUSTODIAL,
    GRADE_INITDATA_VERIFIED, GRADE_SIGNED, GRADE_SYSTEM, GRADE_UNATTRIBUTED, Input, SCHEMA_VERSION,
    Surface, correlation_id, find_leak, hex32, read_events_dir, read_events_file,
};

/// The env var naming the audit directory everywhere (`off` disables; unset falls back to
/// the deploy default — here, a sibling of `TELEGRAM_SESSION_DIR`).
pub const DREGG_AUDIT_DIR_ENV: &str = "DREGG_AUDIT_DIR";

static LOG: OnceLock<AuditLog> = OnceLock::new();

/// Arm the crate-wide audit log EXPLICITLY (the bin calls this with the resolved sibling of
/// its session dir, before any emit). Idempotent-first-wins; returns the live handle.
pub fn init(default_dir: Option<PathBuf>) -> &'static AuditLog {
    LOG.get_or_init(|| resolve(default_dir))
}

/// The crate-wide audit log. If [`init`] was never called (tests, library embedding), it
/// resolves from env alone: `DREGG_AUDIT_DIR`, else `<TELEGRAM_SESSION_DIR>/../audit`, else
/// DISABLED (emits are no-ops) — a test process without the deploy env writes nothing.
pub fn log() -> &'static AuditLog {
    LOG.get_or_init(|| resolve(default_audit_dir()))
}

/// The shared-facility resolution, quiet when there is nothing to resolve (a test process
/// with neither the env var nor a session dir gets a silent disabled log, not a warning).
fn resolve(default_dir: Option<PathBuf>) -> AuditLog {
    let env = std::env::var(DREGG_AUDIT_DIR_ENV).ok();
    if env.is_none() && default_dir.is_none() {
        return AuditLog::disabled();
    }
    AuditLog::resolve(env.as_deref(), default_dir, "telegram")
}

/// The deploy default: a sibling `audit/` beside the durable session store.
fn default_audit_dir() -> Option<PathBuf> {
    let d = std::env::var("TELEGRAM_SESSION_DIR")
        .ok()
        .filter(|d| !d.trim().is_empty())?;
    let session = PathBuf::from(d);
    Some(match session.parent() {
        Some(p) if p.as_os_str().is_empty() => PathBuf::from("audit"),
        Some(p) => p.join("audit"),
        None => session.join("audit"),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — shape + the standing secret-hygiene canary (§8 layer 3).
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    #[test]
    fn an_event_serializes_to_one_line_with_the_taxonomy_words() {
        let ev = AuditEvent::new(
            "telegram",
            Actor::custodial("42424242", "aabbccdd"),
            Surface::Callback,
            Input::new(
                "callback",
                serde_json::json!({ "callback_data": "bid:500" }),
            ),
        )
        .in_session(Some("market".into()), Some("tg:42".into()))
        .with_outcome(AuditOutcome::Landed {
            turn_hash: hex32(&[0x9f; 32]),
            ended: false,
        });
        let line = serde_json::to_string(&ev).unwrap();
        assert!(!line.contains('\n'), "one line");
        let v: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(v["v"], 1);
        assert_eq!(v["platform"], "telegram");
        assert_eq!(v["actor"]["grade"], "custodial");
        assert_eq!(v["surface"], "callback");
        assert_eq!(v["decision"]["kind"], "routed");
        assert_eq!(v["outcome"]["kind"], "landed");
        assert_eq!(v["outcome"]["turn_hash"].as_str().unwrap().len(), 64);
        assert_eq!(v["session_id"], "tg:42");
        // Round-trips (the auditq consumer's contract).
        let back: AuditEvent = serde_json::from_str(&line).unwrap();
        assert_eq!(back.correlation_id, ev.correlation_id);
    }

    /// The standing SECRET CANARY: a representative event built the way the emit points build
    /// them, serialized, must not contain the fixture secrets that were IN SCOPE at the site
    /// (token, master-secret hex, raw initData blob). If a future emit site starts leaking,
    /// extend the fixture here — this test is the §8 layer-3 tripwire.
    #[test]
    fn the_serialized_event_never_carries_the_in_scope_secrets() {
        let bot_token = "7654321:SECRET-fixture-token-AAAA";
        let master_secret_hex = "de..ad".repeat(8);
        let raw_init_data = "query_id=AAtest&user=%7B%22id%22%3A42%7D&auth_date=1&hash=deadbeef";
        // The emit sites record uid + derived PUBLIC identity + the pressed data — never the
        // secrets above.
        let ev = AuditEvent::new(
            "telegram",
            Actor::custodial("42", "aabb"),
            Surface::Command,
            Input::new("/act", serde_json::json!({ "text": "/act bid 500" })),
        )
        .decided("refused", "usage");
        let line = serde_json::to_string(&ev).unwrap();
        assert_eq!(
            find_leak(
                &line,
                &[bot_token, master_secret_hex.as_str(), raw_init_data]
            ),
            None,
            "audit line must not contain a secret: {line}"
        );
    }

    #[test]
    fn a_disabled_log_swallows_emits() {
        let log = AuditLog::disabled();
        assert!(!log.is_enabled());
        log.emit(AuditEvent::new(
            "telegram",
            Actor::system("test"),
            Surface::Command,
            Input::new("noop", Value::Null),
        ));
        assert_eq!(log.dropped_count(), 1, "disabled log counts the drop");
    }
}
