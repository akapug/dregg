//! # escrow-market — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui
//! pixels in the cockpit, a browser-loadable HTML document, and a discord embed —
//! all from this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native
//! elephants, so it is a STANDALONE workspace EXCLUDED from the repo-root
//! workspace. A starbridge-app must never depend on it — that would feature-unify
//! the elephants onto the main build. So the app's contribution is the
//! **view-tree JSON** (this module): pure `serde_json`, no elephant.
//!
//! ## The card shape
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) carrying:
//!   - a `text` header (`"Sealed Escrow"`) and a LIVE leg-status `pill` reading
//!     [`STATE_SLOT`](crate::STATE_SLOT) — the value maps to a word + color
//!     (`LISTED`/`FUNDED`/`SHIPPED`/`SETTLED`);
//!   - an "Escrow" `section` surfacing the live parties + amounts: the seller /
//!     buyer key `bind`s paint emoji-avatar handles (`fmt:"id"`), the ceiling /
//!     escrowed `bind`s group their digits (`fmt:"amount"`);
//!   - one `button` per swap-lifecycle method (`open` / `deposit` / `settle` /
//!     `reclaim`), each carrying its `onClick = { turn, arg }` — the method symbol
//!     the [`service`](crate::service) face routes.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_OPEN`](crate::service::METHOD_OPEN), …) so the card and the service
//! cell speak the same sealed-escrow lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_DEPOSIT, METHOD_OPEN, METHOD_RECLAIM, METHOD_SETTLE};
use crate::{
    BUYER_HASH_SLOT, CEILING_SLOT, ESCROWED_SLOT, SELLER_HASH_SLOT, STATE_FUNDED, STATE_LISTED,
    STATE_SETTLED, STATE_SHIPPED, STATE_SLOT,
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

/// A `deos.ui.section` node — a titled, bordered container.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and
/// a display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped /
/// `"raw"` plain) so an opaque 20-digit key/amount paints short + friendly.
fn bind(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// **The escrow-market card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A `vstack` of a header + LIVE status pill, an "Escrow" section surfacing the live
/// parties (avatar handles) + amounts (grouped digits), and the four sealed-escrow
/// lifecycle buttons. Renderer-independent DATA: hand it to any `deos-view` renderer
/// (native / web / discord) to paint the SAME card. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn escrow_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Sealed Escrow"), pill_live(STATE_SLOT, "LISTED", "muted", json!([
                { "value": STATE_LISTED,  "label": "LISTED",  "tag": "warn" },
                { "value": STATE_FUNDED,  "label": "FUNDED",  "tag": "accent" },
                { "value": STATE_SHIPPED, "label": "SHIPPED", "tag": "accent" },
                { "value": STATE_SETTLED, "label": "SETTLED", "tag": "good" },
            ]))]),
            section("Escrow", "genuine", vec![
                bind(SELLER_HASH_SLOT, "seller · ", "id"),
                bind(BUYER_HASH_SLOT,  "buyer · ",  "id"),
                bind(CEILING_SLOT,     "ceiling · ", "amount"),
                bind(ESCROWED_SLOT,    "escrowed · ", "amount"),
            ]),
            button("Open",    METHOD_OPEN,    0),
            button("Deposit", METHOD_DEPOSIT, 0),
            button("Settle",  METHOD_SETTLE,  0),
            button("Reclaim", METHOD_RECLAIM, 0),
        ]
    })
}

/// **The escrow-market card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn escrow_card_json() -> String {
    serde_json::to_string(&escrow_card_value()).expect("the escrow card serializes")
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
    fn the_card_is_a_vstack_with_a_header_a_live_status_pill_and_four_buttons() {
        let card = escrow_card_value();
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header row, escrow section, open, deposit, settle, reclaim
        assert_eq!(children.len(), 6);
        let texts = of_kind(&card, "text");
        assert!(texts.iter().any(|t| t["props"]["text"] == "Sealed Escrow"));
    }

    #[test]
    fn the_status_pill_reads_the_leg_state_live() {
        let card = escrow_card_value();
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(pills[0]["props"]["slot"], STATE_SLOT as u64);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 4, "LISTED / FUNDED / SHIPPED / SETTLED");
        assert_eq!(cases[3]["value"], STATE_SETTLED);
        assert_eq!(cases[3]["label"], "SETTLED");
    }

    #[test]
    fn the_party_and_amount_binds_carry_their_display_fmt() {
        let card = escrow_card_value();
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
            fmt(SELLER_HASH_SLOT),
            "id",
            "seller paints an avatar handle"
        );
        assert_eq!(fmt(BUYER_HASH_SLOT), "id", "buyer paints an avatar handle");
        assert_eq!(fmt(CEILING_SLOT), "amount", "the ceiling groups digits");
        assert_eq!(
            fmt(ESCROWED_SLOT),
            "amount",
            "the escrowed amount groups digits"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = escrow_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![METHOD_OPEN, METHOD_DEPOSIT, METHOD_SETTLE, METHOD_RECLAIM]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = escrow_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
