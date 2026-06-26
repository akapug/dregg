//! # privacy-voting — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos world
//! by shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The SAME
//! tree renders three ways (the renderer-independence seam): native gpui pixels in the
//! cockpit, a browser-loadable HTML document, and a discord embed — all from this one
//! piece of DATA. See `deos-view/src/{render,web,discord}.rs` for the three renderers
//! and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants, so
//! it is a STANDALONE workspace EXCLUDED from the repo-root workspace (see its
//! `Cargo.toml`). A starbridge-app must never depend on it — that would feature-unify
//! the elephants onto the main build. So the app's contribution is the **view-tree
//! JSON** (this module): pure `serde_json`, no elephant. The deos world's renderers
//! consume it; this module owns the card definition and proves it is well-formed.
//!
//! ## The card shape
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) carrying:
//!   - a `text` header (`"Privacy Voting"`);
//!   - a `bind` on [`TALLY_YES_SLOT`](crate::TALLY_YES_SLOT) — a fine-grained signal
//!     that re-reads the live YES tally off the ledger (the SAME witnessed read a
//!     native `bind` closure makes), so the displayed count advances when a fired turn
//!     commits;
//!   - one `button` per lifecycle method (`open_poll` / `cast_vote` / `record_tally` /
//!     `close_poll`), each carrying its `onClick = { turn, arg }` — the EXACT cap-gated
//!     verified turn a click fires through the [`invoke()`](crate::service)/affordance
//!     seam (the button's payload is the method symbol the service routes).
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_OPEN_POLL`](crate::service::METHOD_OPEN_POLL), …) so the card and the
//! service cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::TALLY_YES_SLOT;
use crate::service::{METHOD_CAST_VOTE, METHOD_CLOSE_POLL, METHOD_OPEN_POLL, METHOD_RECORD_TALLY};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// (the engine drops the closure on serialize, so the slot is tagged).
fn bind(slot: usize, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// **The privacy-voting card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A `vstack` of a header, a live `bind` on the [`TALLY_YES_SLOT`], and the four
/// lifecycle buttons. Renderer-independent DATA: hand it to any `deos-view` renderer
/// (native / web / discord) to paint the SAME card. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn voting_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            text("Privacy Voting"),
            bind(TALLY_YES_SLOT, "yes: "),
            button("Open Poll",    METHOD_OPEN_POLL,    0),
            button("Cast Vote",    METHOD_CAST_VOTE,    0),
            button("Record Tally", METHOD_RECORD_TALLY, 0),
            button("Close Poll",   METHOD_CLOSE_POLL,   0),
        ]
    })
}

/// **The privacy-voting card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn voting_card_json() -> String {
    serde_json::to_string(&voting_card_value()).expect("the voting card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_card_is_a_vstack_with_a_header_a_tally_bind_and_four_buttons() {
        let card = voting_card_value();
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header, bind, open_poll, cast_vote, record_tally, close_poll
        assert_eq!(children.len(), 6);
        assert_eq!(children[0]["kind"], "text");
        assert_eq!(children[0]["props"]["text"], "Privacy Voting");
    }

    #[test]
    fn the_tally_bind_reads_the_yes_tally_slot() {
        let card = voting_card_value();
        let bind = &card["children"][1];
        assert_eq!(bind["kind"], "bind");
        assert_eq!(bind["props"]["slot"], TALLY_YES_SLOT);
        assert_eq!(bind["props"]["label"], "yes: ");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = voting_card_value();
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
            vec![
                METHOD_OPEN_POLL,
                METHOD_CAST_VOTE,
                METHOD_RECORD_TALLY,
                METHOD_CLOSE_POLL
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = voting_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
