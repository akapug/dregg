//! # nameservice — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui
//! pixels in the cockpit, a browser-loadable HTML document, and a discord embed —
//! all from this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`
//! for the three renderers and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native
//! elephants, so it is a STANDALONE workspace EXCLUDED from the repo-root
//! workspace (see its `Cargo.toml`). A starbridge-app must never depend on it —
//! that would feature-unify the elephants onto the main build. So the app's
//! contribution is the **view-tree JSON** (this module): pure `serde_json`, no
//! elephant. The deos world's renderers consume it; this module owns the card
//! definition and proves it is well-formed.
//!
//! ## The card shape — a rich, live NAME-cell surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live registration
//!     stage as a WORD (`REGISTERED`; the palette also carries `EXPIRING` /
//!     `AVAILABLE`), and a `breadcrumb` of the whole name lifecycle
//!     (available → registered → expiring → revoked) with the current step marked;
//!   - a **"Record" `section`** surfacing the LIVE per-name cell state (the model
//!     whose teeth are `WriteOnce(NAME)` · `Monotonic(EXPIRY)` · `WriteOnce(REVOKED)`):
//!     a `gauge` bound to [`EXPIRY_SLOT`](crate::EXPIRY_SLOT) (the rent horizon, against
//!     a [`DEFAULT_RENT_EPOCH_BLOCKS`](crate::DEFAULT_RENT_EPOCH_BLOCKS) epoch), plus
//!     `bind`s on the name, the owner key, the expiry block, the revocation marker,
//!     and the resolve target — each a fine-grained signal that re-reads the live
//!     value (the SAME witnessed read a native `bind` closure makes), so the surface
//!     advances when a fired turn commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`register` / `renew` / `revoke` / `resolve`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names ARE the app's method vocabulary: `register` / `resolve`
//! are the registry-face symbols ([`service::METHOD_REGISTER`](crate::service::METHOD_REGISTER)
//! / [`service::METHOD_RESOLVE`](crate::service::METHOD_RESOLVE)); `renew` / `revoke`
//! are the per-name-cell owner-lifecycle symbols ([`METHOD_RENEW`](crate::METHOD_RENEW)
//! / [`METHOD_REVOKE`](crate::METHOD_REVOKE), the same constants `name_app`'s
//! affordances and the `fire_*` helpers route) — so the card and the cells speak
//! the same registry.

use serde_json::{Value, json};

use crate::service::{METHOD_REGISTER, METHOD_RESOLVE};
use crate::{
    DEFAULT_RENT_EPOCH_BLOCKS, EXPIRY_SLOT, METHOD_RENEW, METHOD_REVOKE, NAME_HASH_SLOT,
    OWNER_HASH_SLOT, RESOLVE_TARGET_SLOT, REVOKED_SLOT,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases` (the first `{value,label,tag}` matching the slot wins).
/// `text`/`tag` are the static fallback (discord, or no match).
fn pill_live(slot: usize, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot, "cases": cases } })
}

/// A `deos.ui.icon` node — a glyph indicator tinted by `tag`.
fn icon(glyph: &str, tag: &str) -> Value {
    json!({ "kind": "icon", "props": { "glyph": glyph, "tag": tag } })
}

/// A `deos.ui.divider` node — a full-width groove rule.
fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// and a display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"`
/// grouped / `"raw"` plain) so an opaque key/digest paints short + friendly.
/// `adept` hides the row in the simple projection (it duplicates a friendlier signal
/// or is a raw internal numeric); revealed in the adept "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection; revealed in the adept view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — the lifecycle path; the `active` step is marked `›`.
fn breadcrumb(steps: &[&str], active: usize) -> Value {
    let items: Vec<Value> = steps
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let label = if i == active {
                format!("› {s}")
            } else {
                s.to_string()
            };
            json!({ "label": label })
        })
        .collect();
    json!({ "kind": "breadcrumb", "props": { "items": items } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// An action row — an `icon` + a lifecycle `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The nameservice card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live NAME-cell surface: a status header (name + `REGISTERED` pill +
/// lifecycle breadcrumb), a "Record" section surfacing the live rent-horizon gauge
/// and the name / owner / expiry / revoked / target binds, and an "Actions" section
/// of the four icon-labelled lifecycle buttons. Renderer-independent DATA: hand it
/// to any `deos-view` renderer (native / web / discord) to paint the SAME card. The
/// button `turn` names are the app's method symbols (registry-face `register` /
/// `resolve`; per-name-cell `renew` / `revoke`).
pub fn nameservice_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Name Service"), pill_live(REVOKED_SLOT, "REGISTERED", "good", json!([
                { "value": 0, "label": "REGISTERED", "tag": "good" },
                { "value": 1, "label": "REVOKED",    "tag": "bad" },
            ]))]),
            breadcrumb(&["Available", "Registered", "Expiring", "Revoked"], 1),
            divider(),
            section("Record", "genuine", vec![
                gauge(EXPIRY_SLOT, DEFAULT_RENT_EPOCH_BLOCKS, "rent horizon ", false),
                bind(NAME_HASH_SLOT, "name · ", "hash", false),
                bind(OWNER_HASH_SLOT, "owner key · ", "id", false),
                bind(EXPIRY_SLOT, "expiry block · ", "raw", true),
                bind(REVOKED_SLOT, "revoked · ", "raw", true),
                bind(RESOLVE_TARGET_SLOT, "target · ", "id", false),
            ]),
            section("Actions", "", vec![
                action("+", "Register", METHOD_REGISTER),
                action("↻", "Renew",    METHOD_RENEW),
                action("⊘", "Revoke",   METHOD_REVOKE),
                action("→", "Resolve",  METHOD_RESOLVE),
            ]),
        ]
    })
}

/// **The nameservice card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn nameservice_card_json() -> String {
    serde_json::to_string(&nameservice_card_value()).expect("the nameservice card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect<'a>(node: &'a Value, kind: &str, out: &mut Vec<&'a Value>) {
        if node["kind"] == kind {
            out.push(node);
        }
        if let Some(children) = node["children"].as_array() {
            for c in children {
                collect(c, kind, out);
            }
        }
    }

    fn of_kind<'a>(card: &'a Value, kind: &str) -> Vec<&'a Value> {
        let mut out = Vec::new();
        collect(card, kind, &mut out);
        out
    }

    #[test]
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_status_pill() {
        let card = nameservice_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Name Service"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads REVOKED_SLOT and maps the marker to a word.
        assert_eq!(
            pills[0]["props"]["text"], "REGISTERED",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["slot"], REVOKED_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(
            cases.len(),
            2,
            "active (0) → REGISTERED, tombstoned (1) → REVOKED"
        );
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "REGISTERED");
        assert_eq!(cases[1]["value"], 1);
        assert_eq!(cases[1]["label"], "REVOKED");
    }

    #[test]
    fn the_name_and_identity_binds_carry_their_display_fmt() {
        let card = nameservice_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        assert_eq!(
            fmt(NAME_HASH_SLOT),
            "hash",
            "the name hash paints short hex"
        );
        assert_eq!(
            fmt(OWNER_HASH_SLOT),
            "id",
            "the owner key paints an avatar handle"
        );
        assert_eq!(
            fmt(RESOLVE_TARGET_SLOT),
            "id",
            "the resolve target paints an avatar handle"
        );
        assert_eq!(fmt(EXPIRY_SLOT), "raw", "the expiry block stays raw");
    }

    #[test]
    fn the_devy_internal_binds_are_marked_adept() {
        let card = nameservice_card_value();
        let binds = of_kind(&card, "bind");
        let adept = |slot: usize| -> bool {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["adept"].as_bool())
                .unwrap()
        };
        // The expiry block (the gauge already shows the rent horizon) + the raw
        // revoked marker (the live pill already says the word) hide by default.
        assert!(adept(EXPIRY_SLOT), "the expiry block duplicates the gauge");
        assert!(
            adept(REVOKED_SLOT),
            "the revoked marker duplicates the live pill"
        );
        // The human-meaningful name / owner / target stay in the simple projection.
        assert!(!adept(NAME_HASH_SLOT));
        assert!(!adept(OWNER_HASH_SLOT));
        assert!(!adept(RESOLVE_TARGET_SLOT));
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = nameservice_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(
            items.len(),
            4,
            "available → registered → expiring → revoked"
        );
        assert_eq!(
            items[1]["label"], "› Registered",
            "the active step is marked"
        );
    }

    #[test]
    fn the_record_section_surfaces_the_live_name_cell_slots() {
        let card = nameservice_card_value();
        // The rent-horizon gauge reads the live EXPIRY slot.
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1);
        assert_eq!(gauges[0]["props"]["slot"], EXPIRY_SLOT);
        assert_eq!(gauges[0]["props"]["max"], DEFAULT_RENT_EPOCH_BLOCKS);

        // The binds surface name / owner / expiry / revoked / target, in order.
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                NAME_HASH_SLOT as u64,
                OWNER_HASH_SLOT as u64,
                EXPIRY_SLOT as u64,
                REVOKED_SLOT as u64,
                RESOLVE_TARGET_SLOT as u64,
            ],
            "the binds surface the per-name-cell record"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = nameservice_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the app's method vocabulary: the registry-face
        // register/resolve and the per-name-cell renew/revoke owner-lifecycle ops.
        assert_eq!(
            turns,
            vec![METHOD_REGISTER, METHOD_RENEW, METHOD_REVOKE, METHOD_RESOLVE]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = nameservice_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, record section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
