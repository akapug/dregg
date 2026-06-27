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
//!   - a `text` header (`"Sealed Escrow"`);
//!   - a `bind` re-reading the live escrow leg status off the committed heap;
//!   - one `button` per swap-lifecycle method (`open` / `deposit` / `settle` /
//!     `reclaim`), each carrying its `onClick = { turn, arg }` — the method symbol
//!     the [`service`](crate::service) face routes.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_OPEN`](crate::service::METHOD_OPEN), …) so the card and the service
//! cell speak the same sealed-escrow lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_DEPOSIT, METHOD_OPEN, METHOD_RECLAIM, METHOD_SETTLE};

/// The renderer tag for the escrow's live leg-status binding (a `deos.ui.bind`
/// re-reads the committed leg state off the host cell's heap).
pub const STATUS_BIND: &str = "escrow-status";

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.bind` node tagged with the model `key` it re-reads + a label prefix
/// (the engine drops the closure on serialize, so the key is tagged).
fn bind(key: &str, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "key": key, "label": label } })
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
/// A `vstack` of a header, a live `bind` on the escrow's leg status, and the four
/// sealed-escrow lifecycle buttons. Renderer-independent DATA: hand it to any
/// `deos-view` renderer (native / web / discord) to paint the SAME card. The
/// button `turn` names are the [`service`](crate::service) method symbols.
pub fn escrow_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            text("Sealed Escrow"),
            bind(STATUS_BIND, "status: "),
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

    #[test]
    fn the_card_is_a_vstack_with_a_header_a_status_bind_and_four_buttons() {
        let card = escrow_card_value();
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header, bind, open, deposit, settle, reclaim
        assert_eq!(children.len(), 6);
        assert_eq!(children[0]["kind"], "text");
        assert_eq!(children[0]["props"]["text"], "Sealed Escrow");
    }

    #[test]
    fn the_status_bind_reads_the_leg_state() {
        let card = escrow_card_value();
        let b = &card["children"][1];
        assert_eq!(b["kind"], "bind");
        assert_eq!(b["props"]["key"], STATUS_BIND);
        assert_eq!(b["props"]["label"], "status: ");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = escrow_card_value();
        let children = card["children"].as_array().unwrap();
        let buttons: Vec<&Value> = children.iter().filter(|c| c["kind"] == "button").collect();
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
