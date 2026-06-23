//! **dregg semantic objects over Matrix** — the generalized envelope.
//!
//! `membrane.rs` proved one thing: a deos semantic object can ride inside an
//! ordinary `m.room.message` as a namespaced custom field, so a non-deos client
//! (nheko, Element) sees a readable `body` fallback while a deos client extracts
//! and renders the rich object. This module **generalizes** that single envelope
//! into a `kind`-tagged carrier for ANY dregg semantic object — so a Matrix room
//! becomes a dregg object-exchange channel, not just a membrane transport.
//!
//! ## The wire shape
//!
//! Every dregg object rides under one custom content key
//! ([`DREGG_OBJECT_KEY`] = `software.ember.deos.object`) inside a normal
//! `m.room.message`:
//!
//! ```json
//! {
//!   "msgtype": "m.text",
//!   "body": "<human-readable fallback so non-deos clients read sensibly>",
//!   "software.ember.deos.object": {
//!     "version": 1,
//!     "kind": "transclusion",          // the tag that selects the payload
//!     "payload": { ...kind-specific... }
//!   }
//! }
//! ```
//!
//! ## Fail-closed forward-compat (the load-bearing tooth)
//!
//! An object whose envelope `version` is newer than this build, OR whose `kind`
//! string this build does not know, is treated as **absent**: the message renders
//! as its plain text fallback and the rich object is never half-acted-on. This is
//! the same discipline `membrane.rs` already enforces (`is_rehydratable`),
//! generalized: a deos client never guesses at a future object, never fires an
//! affordance it cannot fully understand. Unknown ⇒ text, never a partial act.
//!
//! ## The kinds
//!
//! Each kind is a *citation* of a dregg semantic object — inert bytes the recipient
//! materializes against its OWN held authority, never a transfer of mutable state:
//!
//!   * [`DreggObject::Membrane`] — the existing rehydratable cap-bounded world-fork
//!     (the [`crate::membrane::MembraneEnvelope`]); render → a "rehydrate" affordance.
//!   * [`DreggObject::Cell`] — a reference to a cell (id + a short descriptor);
//!     render → an "open this cell" action.
//!   * [`DreggObject::Capability`] — a shareable sturdyref/cap (a bearer token a
//!     recipient may accept into their powerbox); render → "accept into powerbox".
//!   * [`DreggObject::Transclusion`] — a provenanced quote of a cell field (the live
//!     value plus where it came from + the root that binds it); render → the quoted
//!     value, live.
//!   * [`DreggObject::Affordance`] — a fireable cap-gated button (a named action on a
//!     cell, gated by a cap the recipient must hold); render → a fireable button.
//!   * [`DreggObject::Receipt`] — a turn receipt digest (proof a turn committed);
//!     render → the receipt summary.

use serde::{Deserialize, Serialize};

use crate::cell::CellId;
use crate::membrane::MembraneEnvelope;

/// The single custom message-content key every dregg object rides under, inside a
/// normal `m.room.message`. Distinct from the legacy [`crate::membrane::MEMBRANE_EVENT_KEY`]
/// (which the membrane kind still round-trips for back-compat — see
/// [`crate::client`]); new sends use THIS key with a `kind` tag.
pub const DREGG_OBJECT_KEY: &str = "software.ember.deos.object";

/// The envelope wire-format version this build emits. An object whose `version`
/// exceeds this is fail-closed (rendered as text, never acted on).
pub const OBJECT_VERSION: u16 = 1;

/// A dregg semantic object as it travels in a Matrix message: a `kind`-tagged,
/// version-stamped, capability-bounded *citation*. The bytes are inert until a
/// recipient materializes them against its own held authority.
///
/// Serializes to/from the wire shape `{ version, kind, payload }` via
/// [`Self::to_wire`] / [`Self::from_wire`]. The `#[serde(tag = "kind", ...)]`
/// representation puts the kind tag inline and the variant body under `payload`,
/// matching the documented JSON exactly.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "payload", rename_all = "snake_case")]
pub enum DreggObject {
    /// The existing rehydratable cap-bounded world-fork (the star feature).
    Membrane(MembraneEnvelope),
    /// A reference to a cell — the recipient can open/inspect it (against their own
    /// read authority over the web of cells).
    Cell(CellRef),
    /// A shareable capability (a bearer sturdyref) a recipient may accept into
    /// their powerbox. Attenuated by the sender; accepting can only narrow it.
    Capability(CapabilityGrant),
    /// A provenanced quote of a cell field — the live value plus where it came from
    /// and the root that binds it (so the quote is verifiable, not hearsay).
    Transclusion(Transclusion),
    /// A fireable, cap-gated button: a named action on a cell, gated by a cap the
    /// recipient must hold. Rendered as a button; firing exercises the cap.
    Affordance(Affordance),
    /// A turn receipt digest — proof a turn committed (pre/post root + index).
    Receipt(ReceiptObject),
}

/// A reference to a cell: its content-address plus a short human descriptor and an
/// optional kind word (so the UI can label "open this <kind>").
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellRef {
    /// The cell's content-address.
    pub cell_id: CellId,
    /// A short human label for the cell ("the deos-lab room cell", "ember").
    pub label: String,
    /// The cell's kind word, if known ("room", "identity", "document", …). Drives
    /// the open-action label; absent ⇒ a generic "cell".
    pub cell_kind: Option<String>,
}

/// A shareable capability grant: a `dregg://` sturdyref a recipient may accept into
/// their powerbox, with the attenuated lineage bytes (the same `SurfaceCapability`
/// canonical form the membrane's `lineage` carries — meeting with the recipient's
/// own cap can only attenuate).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilityGrant {
    /// The `dregg://` sturdyref this cap names.
    pub sturdyref: String,
    /// A short human label for what the cap grants ("post to deos-lab",
    /// "read the ledger root").
    pub label: String,
    /// The attenuated authority bytes (canonical `SurfaceCapability`). A recipient's
    /// powerbox meets THIS with their own held cap; the meet only attenuates.
    pub lineage: Vec<u8>,
}

/// A provenanced quote of a cell field — a transclusion in the Xanadu sense, made
/// verifiable: the live value, where it came from, and the root that binds it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transclusion {
    /// The cell the quoted field lives in.
    pub source_cell: CellId,
    /// The field path within the cell (`"balance"`, `"title"`, `"members.count"`).
    pub field: String,
    /// The quoted value, rendered to a string for display (the live value at quote
    /// time). A deos client can re-resolve it live against `source_cell`.
    pub value: String,
    /// The cell's state root at quote time — the anti-substitution tooth. A deos
    /// recipient verifies the live cell still reproduces this (or shows "drifted").
    pub bound_root: [u8; 32],
}

/// A fireable, cap-gated affordance: a named action on a cell, gated by a cap the
/// recipient must hold. The recipient fires it only if their powerbox holds a cap
/// that meets the required authority — else the button renders disabled.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Affordance {
    /// The cell this action targets.
    pub target_cell: CellId,
    /// The action's verb ("approve", "transfer", "rehydrate", "sign").
    pub action: String,
    /// A human label for the button ("Approve the merge").
    pub label: String,
    /// The `dregg://` sturdyref of the cap required to fire this action. The
    /// recipient's powerbox must hold a cap that meets this; absent ⇒ disabled.
    pub required_cap: String,
}

/// A turn receipt digest — the byte-identical proof a turn produced, compact enough
/// to ride in a message. Mirrors [`crate::cell::SendReceipt`]'s shape but is the
/// general (not send-specific) receipt object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptObject {
    /// The cell the turn committed against.
    pub cell_id: CellId,
    /// The turn's index in that cell's history.
    pub turn_index: u64,
    /// The cell root after the turn (the new tooth).
    pub post_root: [u8; 32],
}

/// The on-wire form: `{ version, <flattened kind+payload> }`. Splitting the version
/// out keeps the forward-compat tooth (`version`) visible at the top level while the
/// `kind`/`payload` come from the `DreggObject` enum's serde representation.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Wire {
    version: u16,
    #[serde(flatten)]
    object: DreggObject,
}

impl DreggObject {
    /// The `kind` tag string for this object (the wire discriminant). Stable; used
    /// for the human fallback and for kind-specific routing in the UI.
    pub fn kind(&self) -> &'static str {
        match self {
            DreggObject::Membrane(_) => "membrane",
            DreggObject::Cell(_) => "cell",
            DreggObject::Capability(_) => "capability",
            DreggObject::Transclusion(_) => "transclusion",
            DreggObject::Affordance(_) => "affordance",
            DreggObject::Receipt(_) => "receipt",
        }
    }

    /// Serialize to the wire `serde_json::Value` that rides under
    /// [`DREGG_OBJECT_KEY`] in an `m.room.message` content object.
    pub fn to_wire(&self) -> serde_json::Value {
        serde_json::to_value(Wire {
            version: OBJECT_VERSION,
            object: self.clone(),
        })
        .expect("DreggObject is always serializable")
    }

    /// Parse a dregg object from the wire value found under [`DREGG_OBJECT_KEY`].
    ///
    /// **Fail-closed**: returns `None` for a newer `version`, an unknown `kind`, or
    /// a malformed payload. The caller then renders the message's text fallback and
    /// never half-acts on the object (the load-bearing forward-compat tooth).
    pub fn from_wire(value: &serde_json::Value) -> Option<DreggObject> {
        // Check the version FIRST — a newer envelope is refused before we even try
        // to interpret a `kind` whose meaning may have changed.
        let version = value.get("version").and_then(|v| v.as_u64())?;
        if version > OBJECT_VERSION as u64 {
            return None;
        }
        // Deserialize the kind+payload. An unknown `kind` (a future object type) or a
        // payload that does not match its kind fails here → None → text fallback.
        let wire: Wire = serde_json::from_value(value.clone()).ok()?;
        // A membrane carries its OWN forward-compat tooth; honor it (a membrane with a
        // newer inner version is unrehydratable, so render-as-text).
        if let DreggObject::Membrane(env) = &wire.object {
            if !env.is_rehydratable() {
                return None;
            }
        }
        Some(wire.object)
    }

    /// The graceful human-readable fallback a non-deos client shows in `body`. Each
    /// kind reads sensibly so the conversation is legible everywhere.
    pub fn text_fallback(&self) -> String {
        match self {
            DreggObject::Membrane(env) => env.text_fallback(),
            DreggObject::Cell(c) => format!(
                "[deos cell · {} · {}:{}]",
                c.label,
                c.cell_kind.as_deref().unwrap_or("cell"),
                c.cell_id.short()
            ),
            DreggObject::Capability(c) => {
                format!("[deos capability · {} · {}]", c.label, c.sturdyref)
            }
            DreggObject::Transclusion(t) => {
                format!("[deos transclusion · {}.{} = {}]", t.source_cell.short(), t.field, t.value)
            }
            DreggObject::Affordance(a) => {
                format!("[deos affordance · {} · {}:{}]", a.label, a.action, a.target_cell.short())
            }
            DreggObject::Receipt(r) => format!(
                "[deos receipt · turn {} · {} · root {}]",
                r.turn_index,
                r.cell_id.short(),
                hex8(&r.post_root)
            ),
        }
    }

    /// Build the full `m.room.message`-content JSON object (msgtype/body + the
    /// namespaced object field). The caller `send_raw("m.room.message", ..)`s this.
    /// `body` empty ⇒ the kind's [`Self::text_fallback`] is used.
    pub fn to_message_content(&self, body: &str) -> serde_json::Value {
        let fallback = if body.trim().is_empty() {
            self.text_fallback()
        } else {
            body.to_string()
        };
        serde_json::json!({
            "msgtype": "m.text",
            "body": fallback,
            DREGG_OBJECT_KEY: self.to_wire(),
        })
    }

    /// Extract a dregg object from the RAW JSON of an `m.room.message` event, if it
    /// carries one under [`DREGG_OBJECT_KEY`] inside `content`. Fail-closed (see
    /// [`Self::from_wire`]); a plain message or an unknown/future object ⇒ `None`.
    pub fn extract(raw_event_json: &str) -> Option<DreggObject> {
        let value: serde_json::Value = serde_json::from_str(raw_event_json).ok()?;
        let field = value.get("content")?.get(DREGG_OBJECT_KEY)?;
        DreggObject::from_wire(field)
    }
}

fn hex8(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(8);
    for byte in &b[..4] {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::membrane::MockMembraneHost;

    fn cell_id(seed: u8) -> CellId {
        let mut b = [0u8; 32];
        b[0] = seed;
        CellId(b)
    }

    /// Every kind round-trips mint → wire → extract, preserving the object exactly.
    #[test]
    fn every_kind_round_trips_through_the_wire() {
        let objects = vec![
            DreggObject::Membrane(MockMembraneHost::sample_envelope()),
            DreggObject::Cell(CellRef {
                cell_id: cell_id(1),
                label: "the deos-lab room cell".into(),
                cell_kind: Some("room".into()),
            }),
            DreggObject::Capability(CapabilityGrant {
                sturdyref: "dregg://cell/deadbeef".into(),
                label: "post to deos-lab".into(),
                lineage: vec![0xca, 0x9a, 0xb1, 0xe],
            }),
            DreggObject::Transclusion(Transclusion {
                source_cell: cell_id(2),
                field: "balance".into(),
                value: "42 gold".into(),
                bound_root: [0xab; 32],
            }),
            DreggObject::Affordance(Affordance {
                target_cell: cell_id(3),
                action: "approve".into(),
                label: "Approve the merge".into(),
                required_cap: "dregg://cap/approve".into(),
            }),
            DreggObject::Receipt(ReceiptObject {
                cell_id: cell_id(4),
                turn_index: 7,
                post_root: [0xef; 32],
            }),
        ];

        for obj in objects {
            // mint → message content (the exact JSON send_raw posts).
            let content = obj.to_message_content("");
            // The non-deos fallback is a readable body.
            let body = content.get("body").and_then(|b| b.as_str()).unwrap();
            assert!(body.starts_with("[deos "), "fallback readable: {body}");
            // Wrap as a full event the homeserver returns, then extract.
            let event = serde_json::json!({
                "type": "m.room.message",
                "event_id": "$x:deos.local",
                "sender": "@grok:deos.local",
                "origin_server_ts": 1_718_000_000_000u64,
                "content": content,
            });
            let back = DreggObject::extract(&event.to_string())
                .unwrap_or_else(|| panic!("kind {} round-trips", obj.kind()));
            assert_eq!(back, obj, "kind {} preserved exactly", obj.kind());
        }
    }

    /// A plain message carries no dregg object.
    #[test]
    fn plain_message_has_no_object() {
        let event = serde_json::json!({
            "type": "m.room.message",
            "content": { "msgtype": "m.text", "body": "hello" },
        });
        assert!(DreggObject::extract(&event.to_string()).is_none());
    }

    /// An unknown future `kind` fails closed (rendered as text, never half-acted).
    #[test]
    fn unknown_kind_fails_closed() {
        let wire = serde_json::json!({
            "version": OBJECT_VERSION,
            "kind": "wormhole",          // a kind this build has never heard of
            "payload": { "anything": 1 },
        });
        assert!(DreggObject::from_wire(&wire).is_none());
    }

    /// A newer envelope version fails closed BEFORE the kind is interpreted.
    #[test]
    fn future_version_fails_closed() {
        let mut wire = DreggObject::Cell(CellRef {
            cell_id: cell_id(1),
            label: "x".into(),
            cell_kind: None,
        })
        .to_wire();
        wire["version"] = serde_json::json!(OBJECT_VERSION + 1);
        assert!(DreggObject::from_wire(&wire).is_none());
    }

    /// A membrane with a newer INNER version fails closed too (the membrane's own
    /// rehydratable tooth is honored through the general envelope).
    #[test]
    fn membrane_inner_future_version_fails_closed() {
        let mut env = MockMembraneHost::sample_envelope();
        env.version = MembraneEnvelope::VERSION + 1;
        let wire = DreggObject::Membrane(env).to_wire();
        assert!(DreggObject::from_wire(&wire).is_none());
    }

    /// The wire shape is exactly the documented `{version, kind, payload}`.
    #[test]
    fn wire_shape_is_kind_tagged() {
        let obj = DreggObject::Cell(CellRef {
            cell_id: cell_id(9),
            label: "doc".into(),
            cell_kind: Some("document".into()),
        });
        let wire = obj.to_wire();
        assert_eq!(wire["version"], serde_json::json!(OBJECT_VERSION));
        assert_eq!(wire["kind"], serde_json::json!("cell"));
        assert!(wire.get("payload").is_some(), "payload present");
        assert_eq!(wire["payload"]["label"], serde_json::json!("doc"));
    }
}
