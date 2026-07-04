//! # storage-gateway-mandate — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui
//! pixels in the cockpit, a browser-loadable HTML document, and a discord embed —
//! all from this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`
//! and `docs/deos/DEOS-VIEW-RICHNESS-EXPANSION.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native
//! elephants, so it is a STANDALONE workspace EXCLUDED from the repo-root
//! workspace. A starbridge-app must never depend on it — that would feature-unify
//! the elephants onto the main build. So the app's contribution is the
//! **view-tree JSON** (this module): pure `serde_json`, no elephant. The deos
//! world's renderers consume it; this module owns the card definition and proves
//! it is well-formed.
//!
//! ## The card shape — a rich, live storage-quota surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a LIVE `pill` reading
//!     [`LAST_OP_SLOT`](crate::LAST_OP_SLOT) and naming the last gateway op as a WORD
//!     (`GET` / `PUT` / `LIST`, falling back to `ACTIVE` before any op), and a
//!     `breadcrumb` of the quota lifecycle (empty → filling → full) with the current
//!     band marked;
//!   - a **"Quota" `section`** surfacing the LIVE cell state: the KILLER VISUAL is a
//!     `gauge` bound to [`VOLUME_SPENT_SLOT`](crate::VOLUME_SPENT_SLOT) over the
//!     [`DEFAULT_VOLUME_CEILING`](crate::DEFAULT_VOLUME_CEILING) — the storage budget
//!     filling as objects are `put` — plus `bind`s on the spent meter, the
//!     [`VOLUME_CEILING_SLOT`](crate::VOLUME_CEILING_SLOT), the last
//!     [`OBJECT_KEY_SLOT`](crate::OBJECT_KEY_SLOT) and the last
//!     [`LAST_OP_SLOT`](crate::LAST_OP_SLOT) — each a fine-grained signal that
//!     re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances when a fired `put` commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per service operation
//!     (`put` / `get` / `list`), each `button` carrying its `onClick = { turn, arg }`
//!     — the EXACT cap-gated verified turn a click fires through the
//!     [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_PUT`](crate::service::METHOD_PUT), …) so the card and the service cell
//! speak the same storage operations.

use serde_json::{Value, json};

use crate::service::{METHOD_GET, METHOD_LIST, METHOD_PUT};
use crate::{
    DEFAULT_VOLUME_CEILING, LAST_OP_SLOT, OBJECT_KEY_SLOT, VOLUME_CEILING_SLOT, VOLUME_SPENT_SLOT,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a word +
/// color via `cases` (the first `{value,label,tag}` matching the slot wins). `text`/`tag` are
/// the static fallback (discord, or no match).
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped digits /
/// `"raw"` plain) so an opaque key/amount paints short + friendly. `adept` tags a dev-y row
/// (a raw enum/counter integer) hidden in the simple projection, revealed in the adept
/// "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: usize, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
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

/// An action row — an `icon` + an operation `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The storage-gateway card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live storage-quota surface: a status header (name + `ACTIVE` pill +
/// quota-lifecycle breadcrumb), a "Quota" section whose KILLER VISUAL is the
/// `VOLUME_SPENT / VOLUME_CEILING` gauge (the budget filling as objects are `put`)
/// plus the spent / ceiling / last-key / last-op binds, and an "Actions" section of
/// the three icon-labelled operation buttons. Renderer-independent DATA: hand it to
/// any `deos-view` renderer (native / web / discord) to paint the SAME card. The
/// button `turn` names are the [`service`](crate::service) method symbols.
pub fn gateway_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header pill reads the LIVE last-op slot and names it as a WORD (GET/PUT/LIST;
            // StorageOp encoding Get=0/Put=1/List=2), falling back to ACTIVE before any op.
            row(vec![text("Storage Gateway"), pill_live(LAST_OP_SLOT as usize, "ACTIVE", "good", json!([
                { "value": 0, "label": "GET",  "tag": "accent" },
                { "value": 1, "label": "PUT",  "tag": "good" },
                { "value": 2, "label": "LIST", "tag": "muted" },
            ]))]),
            breadcrumb(&["Empty", "Filling", "Full"], 1),
            divider(),
            section("Quota", "genuine", vec![
                // THE KILLER VISUAL: the storage budget filling as objects are put —
                // VOLUME_SPENT over the ceiling, read immediate-mode off the live cell.
                gauge(VOLUME_SPENT_SLOT as usize, DEFAULT_VOLUME_CEILING, "volume used "),
                bind(VOLUME_SPENT_SLOT as usize, "spent · ", "amount", false),
                bind(VOLUME_CEILING_SLOT as usize, "ceiling · ", "amount", false),
                bind(OBJECT_KEY_SLOT as usize, "last key · ", "hash", false),
                // The raw StorageOp integer duplicates the header's GET/PUT/LIST word — adept-only.
                bind(LAST_OP_SLOT as usize, "last op · ", "raw", true),
            ]),
            section("Actions", "", vec![
                action("↑", "Put",  METHOD_PUT),
                action("↓", "Get",  METHOD_GET),
                action("≡", "List", METHOD_LIST),
            ]),
        ]
    })
}

/// **The storage-gateway card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn gateway_card_json() -> String {
    serde_json::to_string(&gateway_card_value()).expect("the gateway card serializes")
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
        let card = gateway_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Storage Gateway"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads LAST_OP_SLOT and names the op as a word.
        assert_eq!(
            pills[0]["props"]["text"], "ACTIVE",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["slot"], LAST_OP_SLOT as usize);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 3, "GET / PUT / LIST");
        assert_eq!(cases[1]["value"], 1, "StorageOp::Put encodes to 1");
        assert_eq!(cases[1]["label"], "PUT");
    }

    #[test]
    fn the_quota_binds_carry_their_display_fmt() {
        let card = gateway_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: u8| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        assert_eq!(
            fmt(VOLUME_SPENT_SLOT),
            "amount",
            "the spent meter groups digits"
        );
        assert_eq!(
            fmt(VOLUME_CEILING_SLOT),
            "amount",
            "the ceiling groups digits"
        );
        assert_eq!(
            fmt(OBJECT_KEY_SLOT),
            "hash",
            "the object key paints short hex"
        );
        assert_eq!(fmt(LAST_OP_SLOT), "raw", "the raw op integer stays plain");
        // The raw last-op integer is adept-only (the header pill shows it as a word).
        let last_op = binds
            .iter()
            .find(|b| b["props"]["slot"].as_u64() == Some(LAST_OP_SLOT as u64))
            .unwrap();
        assert_eq!(last_op["props"]["adept"], true, "the raw op row is dev-y");
    }

    #[test]
    fn the_quota_lifecycle_breadcrumb_marks_the_current_band() {
        let card = gateway_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3, "empty → filling → full");
        assert_eq!(items[1]["label"], "› Filling", "the active band is marked");
    }

    #[test]
    fn the_volume_gauge_reads_the_live_spent_slot_over_the_ceiling() {
        let card = gateway_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "the killer visual: the quota gauge");
        assert_eq!(gauges[0]["props"]["slot"], VOLUME_SPENT_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], DEFAULT_VOLUME_CEILING);

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                VOLUME_SPENT_SLOT as u64,
                VOLUME_CEILING_SLOT as u64,
                OBJECT_KEY_SLOT as u64,
                LAST_OP_SLOT as u64
            ],
            "the binds surface spent / ceiling / last-key / last-op"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = gateway_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(turns, vec![METHOD_PUT, METHOD_GET, METHOD_LIST]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = gateway_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, quota section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
