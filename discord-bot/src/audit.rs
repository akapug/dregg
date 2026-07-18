//! **The interaction-envelope audit log** — the discord-bot face of the shared
//! [`dreggnet_audit`] facility (`docs/BOT-AUDIT-LOGGING-DESIGN.md`).
//!
//! One JSON line per interaction decision: who pressed/typed what, on which surface,
//! attributed how strongly, what the frontend decided, and what came back (the
//! `turn_hash` when a turn landed — the join to the receipt chain; the refusal reason
//! when it did not — exactly the events the receipt chain never records).
//!
//! The event shape, non-blocking writer thread, daily rotation/retention, and readers
//! all live in `dreggnet-audit` (re-exported here). This module carries only:
//!
//! * the process-global handle ([`install`] / [`log`] — a disabled no-op until `main`
//!   installs one, so the sync cores and their tests emit through the same seam with
//!   zero plumbing and zero side effects);
//! * the Discord-side helpers: actor constructors over the derived identity, the
//!   substrate [`Outcome`] → [`AuditOutcome`] map, and the SECRET-REDACTED input
//!   builders ([`redacted_fields`] / [`modal_detail`] / [`options_detail`] — design §8:
//!   a denylist on field/option names + form ids; platform uids, derived PUBLIC
//!   identities, turn hashes, session ids and user free text ARE the trail), plus the
//!   standing canary test over [`find_leak`].

use serde_json::{Value, json};
use serenity::all::{ActionRowComponent, CommandDataOption, CommandDataOptionValue};
use std::sync::OnceLock;

use dreggnet_offerings::{DreggIdentity, Outcome};

pub use dreggnet_audit::{
    Actor, AuditEvent, AuditLog, AuditOutcome, Decision, GRADE_ASSERTED, GRADE_CUSTODIAL,
    GRADE_INITDATA_VERIFIED, GRADE_SIGNED, GRADE_SYSTEM, GRADE_UNATTRIBUTED, Input, SCHEMA_VERSION,
    Surface, correlation_id, find_leak, hex32, read_events_dir, read_events_file,
};

use crate::BotState;

// ─────────────────────────────────────────────────────────────────────────────
// The process-global handle: installed once at boot, no-op until then (so the
// sync cores — and their tests — emit through the same seam without plumbing).
// ─────────────────────────────────────────────────────────────────────────────

static GLOBAL: OnceLock<AuditLog> = OnceLock::new();
static FALLBACK: OnceLock<AuditLog> = OnceLock::new();

/// Install the process's audit log (first install wins; called once from `main`).
pub fn install(log: AuditLog) {
    if GLOBAL.set(log).is_err() {
        tracing::warn!("audit log installed twice; keeping the first");
    }
}

/// The process's audit log — a disabled no-op until [`install`] runs (tests never
/// install one, so the sync cores stay driveable with zero audit side effects).
pub fn log() -> &'static AuditLog {
    GLOBAL
        .get()
        .unwrap_or_else(|| FALLBACK.get_or_init(AuditLog::disabled))
}

// ─────────────────────────────────────────────────────────────────────────────
// Discord-side helpers: actors, outcomes, and SECRET-REDACTED input details.
// ─────────────────────────────────────────────────────────────────────────────

/// The custodial actor for a Discord uid: the uid + the derived dregg identity
/// (Ed25519 public key hex — PUBLIC material; the derivation secret never leaves
/// `UserCipherclerk::derive`).
pub fn custodial_actor(state: &BotState, discord_uid: u64) -> Actor {
    Actor::custodial(
        discord_uid.to_string(),
        crate::commands::offering::identity_of(state, discord_uid).0,
    )
}

/// A custodial actor from an already-derived dregg identity (the press paths hold one).
pub fn actor_of(discord_uid: u64, identity: &DreggIdentity) -> Actor {
    Actor::custodial(discord_uid.to_string(), identity.0.clone())
}

/// Map a substrate [`Outcome`] to the audit outcome — the `turn_hash` on a landed
/// turn IS the join to the receipt chain; a refusal carries the executor's reason.
pub fn outcome_of(outcome: &Outcome) -> AuditOutcome {
    match outcome {
        Outcome::Landed { receipt, ended } => AuditOutcome::Landed {
            turn_hash: hex::encode(&receipt.turn_hash[..]),
            ended: *ended,
        },
        Outcome::Refused(why) => AuditOutcome::Refused { why: why.clone() },
    }
}

/// Whether a field/option/form name is on the secret denylist (design §8): anything
/// key/secret/token/seed-shaped is redacted AT the emit point, never serialized.
pub fn sensitive_name(name: &str) -> bool {
    let n = name.to_ascii_lowercase();
    [
        "key",
        "secret",
        "token",
        "seed",
        "password",
        "credential",
        "mnemonic",
    ]
    .iter()
    .any(|w| n.contains(w))
}

/// Redact a modal's `(field_id, typed_value)` pairs: a sensitive form id redacts
/// EVERY field (the Set-key modal), a sensitive field id redacts that field. User
/// free text on non-sensitive fields is carried verbatim — it IS the audit trail.
pub fn redacted_fields(fields: &[(String, String)], form_id: &str) -> Value {
    let redact_all = sensitive_name(form_id);
    let mut map = serde_json::Map::new();
    for (id, value) in fields {
        if redact_all || sensitive_name(id) {
            map.insert(id.clone(), json!({ "redacted": true }));
        } else {
            map.insert(id.clone(), json!(value));
        }
    }
    Value::Object(map)
}

/// A modal submit's redacted detail: the custom id + every typed field through
/// [`redacted_fields`].
pub fn modal_detail(modal: &serenity::all::ModalInteraction) -> Value {
    let mut fields: Vec<(String, String)> = Vec::new();
    for row in &modal.data.components {
        for component in &row.components {
            if let ActionRowComponent::InputText(input) = component {
                fields.push((
                    input.custom_id.clone(),
                    input.value.clone().unwrap_or_default(),
                ));
            }
        }
    }
    json!({
        "custom_id": modal.data.custom_id,
        "fields": redacted_fields(&fields, &modal.data.custom_id),
    })
}

/// A slash command's options as redacted JSON (subcommand nesting preserved;
/// sensitive option names redacted by [`sensitive_name`]).
pub fn options_detail(options: &[CommandDataOption]) -> Value {
    let mut map = serde_json::Map::new();
    for o in options {
        map.insert(o.name.clone(), option_json(&o.name, &o.value));
    }
    Value::Object(map)
}

fn option_json(name: &str, value: &CommandDataOptionValue) -> Value {
    use CommandDataOptionValue as V;
    if sensitive_name(name) {
        return json!({ "redacted": true });
    }
    match value {
        V::SubCommand(inner) | V::SubCommandGroup(inner) => options_detail(inner),
        V::String(s) => json!(s),
        V::Integer(i) => json!(i),
        V::Number(n) => json!(n),
        V::Boolean(b) => json!(b),
        V::User(id) => json!(id.get()),
        V::Channel(id) => json!(id.get()),
        V::Role(id) => json!(id.get()),
        V::Mentionable(id) => json!(id.get()),
        V::Attachment(id) => json!(id.get()),
        _ => Value::Null,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the taxonomy serialization and the SECRET CANARY.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correlation_ids_are_unique() {
        let a = correlation_id();
        let b = correlation_id();
        assert_ne!(a, b);
        assert_eq!(a.len(), 28);
    }

    fn fixture_event(detail: Value) -> AuditEvent {
        AuditEvent::new(
            "discord",
            Actor::custodial("123456789", "aa".repeat(32)),
            Surface::Modal,
            Input::new("identity", detail),
        )
    }

    /// THE STANDING CANARY (design §8): a redact-listed value must never reach a
    /// serialized audit line — neither via a sensitive FIELD id nor a sensitive
    /// FORM id. If a future emit site routes secrets around `redacted_fields`,
    /// extend this fixture set.
    #[test]
    fn secret_canary_never_serializes() {
        let provider_key = "sk-THIS-IS-A-PROVIDER-KEY-b3f1";
        let bot_secret_hex = "d2ad".repeat(16);

        // A sensitive field id inside a benign form.
        let by_field = redacted_fields(
            &[
                ("provider_key".to_string(), provider_key.to_string()),
                ("note".to_string(), "public words".to_string()),
            ],
            "start:modal:send",
        );
        // A sensitive FORM id redacts every field, whatever it is named.
        let by_form = redacted_fields(
            &[("value".to_string(), bot_secret_hex.clone())],
            "start:modal:setkey",
        );

        for detail in [by_field, by_form] {
            let line = serde_json::to_string(&fixture_event(detail)).unwrap();
            assert_eq!(
                find_leak(&line, &[provider_key, bot_secret_hex.as_str()]),
                None,
                "leaked a redact-listed value: {line}"
            );
        }

        // The benign free text DOES survive — user content is the trail.
        let benign = redacted_fields(
            &[("note".to_string(), "public words".to_string())],
            "start:modal:send",
        );
        let line = serde_json::to_string(&fixture_event(benign)).unwrap();
        assert!(line.contains("public words"));
    }

    #[test]
    fn outcome_taxonomy_serializes_landed_join() {
        let ev = fixture_event(json!({})).with_outcome(AuditOutcome::Landed {
            turn_hash: "ab".repeat(32),
            ended: false,
        });
        let line = serde_json::to_string(&ev).unwrap();
        assert!(line.contains("\"kind\":\"landed\""));
        assert!(line.contains(&"ab".repeat(32)));
    }
}
