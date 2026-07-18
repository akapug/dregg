//! # audit — the INTERACTION-ENVELOPE emitter (this crate's face of `dreggnet-audit`).
//!
//! docs/BOT-AUDIT-LOGGING-DESIGN.md §3–§4: one [`AuditEvent`] JSON line per interaction —
//! who GET/POSTed what, on which surface, attributed how strongly (this crate's three grades:
//! `asserted` cookie, `initdata-verified` Mini App, `signed` act-signed), what the handler
//! DECIDED (routed / refused / gated / error), and what came back (the `turn_hash` join to
//! the receipt chain on a landed turn; the refusal reason otherwise). The initData gate
//! events (`surface: "init_data"`, accept AND refuse with the named [`InitDataError`
//! ](crate::telegram_miniapp::InitDataError) gate) are the trail the live HMAC-mismatch
//! debugging reads.
//!
//! The event shape, writer thread, rotation/retention, and readers all live in the shared
//! [`dreggnet_audit`] facility (re-exported here); this module carries only the web-deploy
//! log resolution: [`log`] over `DREGG_AUDIT_DIR`, defaulting to a sibling `audit/` beside
//! `DREGGNET_WEB_SESSION_DIR`.
//!
//! ## Secret hygiene (§8 — HARD RULES)
//! NEVER in an audit record: the bot token, `TELEGRAM_BOT_SECRET` / any master secret,
//! derived Ed25519 seeds, provider keys, the initData HMAC secret, and **the raw initData
//! string** (it embeds `hash` — the verified uid + `auth_date` are recorded instead, the
//! same rule `telegram_miniapp` already enforces). FINE to log (they ARE the trail):
//! platform uids, derived PUBLIC identities (pubkey hex), turn hashes, session ids,
//! offering keys, `{turn, arg}`, user free text, act-signed pubkey/counter/signature
//! (public material). The standing canary test below runs [`find_leak`] over
//! representative events.

use std::path::PathBuf;
use std::sync::OnceLock;

pub use dreggnet_audit::{
    Actor, AuditEvent, AuditLog, AuditOutcome, Decision, GRADE_ASSERTED, GRADE_CUSTODIAL,
    GRADE_INITDATA_VERIFIED, GRADE_SIGNED, GRADE_SYSTEM, GRADE_UNATTRIBUTED, Input, SCHEMA_VERSION,
    Surface, correlation_id, find_leak, hex32, read_events_dir, read_events_file,
};

/// The env var naming the audit directory everywhere (`off` disables; unset falls back to
/// the deploy default — here, a sibling of `DREGGNET_WEB_SESSION_DIR`).
pub const DREGG_AUDIT_DIR_ENV: &str = "DREGG_AUDIT_DIR";

static LOG: OnceLock<AuditLog> = OnceLock::new();

/// The crate-wide audit log, resolved once from env: `DREGG_AUDIT_DIR` (`off` disables),
/// else `<DREGGNET_WEB_SESSION_DIR>/../audit` (a sibling of the durable session store), else
/// DISABLED (emits are no-ops) — a test process without the deploy env writes nothing.
pub fn log() -> &'static AuditLog {
    LOG.get_or_init(|| {
        let env = std::env::var(DREGG_AUDIT_DIR_ENV).ok();
        let default_dir = default_audit_dir();
        if env.is_none() && default_dir.is_none() {
            // Quiet disabled log (no warning): a test/dev process without the deploy env.
            tracing::info!(
                "audit log disabled ({DREGG_AUDIT_DIR_ENV} unset and no session-dir sibling)"
            );
            return AuditLog::disabled();
        }
        AuditLog::resolve(env.as_deref(), default_dir, "web")
    })
}

/// The deploy default: a sibling `audit/` beside the durable session store.
fn default_audit_dir() -> Option<PathBuf> {
    let d = std::env::var("DREGGNET_WEB_SESSION_DIR")
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
            "tg-miniapp",
            Actor::initdata_verified("42424242", Some("aabbccdd".into())),
            Surface::Http,
            Input::new(
                "POST /tg/offerings/{key}/session/{id}/act",
                serde_json::json!({ "turn": "choose", "arg": 3 }),
            ),
        )
        .in_session(Some("dungeon".into()), Some("tg-dungeon-aabb".into()))
        .with_outcome(AuditOutcome::Landed {
            turn_hash: hex32(&[0x9f; 32]),
            ended: false,
        });
        let line = serde_json::to_string(&ev).unwrap();
        assert!(!line.contains('\n'), "one line");
        let v: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(v["v"], 1);
        assert_eq!(v["platform"], "tg-miniapp");
        assert_eq!(v["actor"]["grade"], "initdata-verified");
        assert_eq!(v["surface"], "http");
        assert_eq!(v["decision"]["kind"], "routed");
        assert_eq!(v["outcome"]["kind"], "landed");
        assert_eq!(v["outcome"]["turn_hash"].as_str().unwrap().len(), 64);
        // Round-trips (the auditq consumer's contract).
        let back: AuditEvent = serde_json::from_str(&line).unwrap();
        assert_eq!(back.correlation_id, ev.correlation_id);
    }

    /// The standing SECRET CANARY: a representative event built the way the emit points build
    /// them, serialized, must not contain the fixture secrets that were IN SCOPE at the site
    /// (token, HMAC secret hex, raw initData blob). If a future emit site starts leaking,
    /// extend the fixture here — this test is the §8 layer-3 tripwire.
    #[test]
    fn the_serialized_event_never_carries_the_in_scope_secrets() {
        let bot_token = "7654321:SECRET-fixture-token-AAAA";
        let secret_key_hex = "de..ad".repeat(8);
        let raw_init_data = "query_id=AAtest&user=%7B%22id%22%3A42%7D&auth_date=1&hash=deadbeef";
        // A refused initData gate records the ERROR + status — never the raw string.
        let ev = AuditEvent::new(
            "tg-miniapp",
            Actor::unattributed(),
            Surface::InitData,
            Input::new(
                "POST /tg/offerings/{key}/session/{id}/act",
                serde_json::json!({
                    "error": "HMAC did not verify over the data-check-string",
                    "status": 403
                }),
            ),
        )
        .decided("gated", "initdata:bad_hmac");
        let line = serde_json::to_string(&ev).unwrap();
        assert_eq!(
            find_leak(&line, &[bot_token, secret_key_hex.as_str(), raw_init_data]),
            None,
            "audit line must not contain a secret: {line}"
        );
    }

    #[test]
    fn a_disabled_log_swallows_emits() {
        let log = AuditLog::disabled();
        assert!(!log.is_enabled());
        log.emit(AuditEvent::new(
            "web",
            Actor::system("test"),
            Surface::Http,
            Input::new("noop", Value::Null),
        ));
        assert_eq!(log.dropped_count(), 1, "disabled log counts the drop");
    }
}
