//! # governed-namespace — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos
//! world by shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui pixels
//! in the cockpit, a browser-loadable HTML document, and a discord embed — all from
//! this one piece of DATA. See `deos-view/src/{render,web,discord}.rs` for the three
//! renderers and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants,
//! so it is a STANDALONE workspace EXCLUDED from the repo-root workspace (see its
//! `Cargo.toml`). A starbridge-app must never depend on it — that would
//! feature-unify the elephants onto the main build. So the app's contribution is the
//! **view-tree JSON** (this module): pure `serde_json`, no elephant. The deos
//! world's renderers consume it; this module owns the card definition and proves it
//! is well-formed.
//!
//! ## The card shape — a rich, live GOVERNANCE surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live governance
//!     stage as a WORD (`VOTING`), and a `breadcrumb` of the whole constitutional
//!     lifecycle (draft → proposed → voting → committed) with the current step
//!     marked;
//!   - a **"Proposal" `section`** surfacing the LIVE cell state: the KILLER
//!     governance visual — a `gauge` bound to
//!     [`PENDING_PROPOSAL_ROOT_SLOT`](crate::PENDING_PROPOSAL_ROOT_SLOT) (the running
//!     vote tally the service / reactor advance) over the
//!     [`QUORUM`] denominator, so the bar fills `votes / M` toward quorum — plus
//!     `bind`s on the proposed route ([`ROUTE_TABLE_ROOT_SLOT`](crate::ROUTE_TABLE_ROOT_SLOT)),
//!     the votes count, the quorum threshold ([`THRESHOLD_SLOT`](crate::THRESHOLD_SLOT)),
//!     the committee ([`GOVERNANCE_COMMITTEE_ROOT_SLOT`](crate::GOVERNANCE_COMMITTEE_ROOT_SLOT)),
//!     and the version ([`VERSION_SLOT`](crate::VERSION_SLOT)) — each a fine-grained
//!     signal that re-reads the live value (the SAME witnessed read a native `bind`
//!     closure makes), so the quorum bar climbs as votes commit;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`propose` / `vote` / `commit` / `register`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_PROPOSE`](crate::service::METHOD_PROPOSE), …) so the card (AX4), the
//! service (AX3), and the reactor (AX5) all speak the one governance lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_COMMIT, METHOD_PROPOSE, METHOD_REGISTER, METHOD_VOTE};
use crate::{
    GOVERNANCE_COMMITTEE_ROOT_SLOT, PENDING_PROPOSAL_ROOT_SLOT, ROUTE_TABLE_ROOT_SLOT,
    THRESHOLD_SLOT, VERSION_SLOT,
};

/// The quorum bar's denominator — a representative M-of-N committee threshold so a
/// proposal that has gathered `QUORUM` approving votes fills the gauge (the killer
/// governance visual: votes_for / M). A live cell reads its real `M` from
/// [`THRESHOLD_SLOT`](crate::THRESHOLD_SLOT); this is the card's display ceiling, the
/// same representative-max idiom the bounty-board reward gauge uses.
pub const QUORUM: u64 = 3;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge.
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix.
fn bind(slot: u8, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot as usize, "label": label } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: u8, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot as usize, "max": max, "label": label } })
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

/// **The governed-namespace card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live governance surface: a status header (name + `VOTING` pill + lifecycle
/// breadcrumb), a "Proposal" section surfacing the killer quorum gauge (`votes / M`)
/// plus the proposed-route / votes / quorum / committee / version binds, and an
/// "Actions" section of the four icon-labelled lifecycle buttons. Renderer-independent
/// DATA. The button `turn` names are the [`service`](crate::service) method symbols.
pub fn governance_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Governed Namespace"), pill("VOTING", "accent")]),
            breadcrumb(&["Draft", "Proposed", "Voting", "Committed"], 2),
            divider(),
            section("Proposal", "genuine", vec![
                // THE killer governance visual: the running vote tally toward quorum.
                gauge(PENDING_PROPOSAL_ROOT_SLOT, QUORUM, "quorum "),
                bind(ROUTE_TABLE_ROOT_SLOT, "proposed route · "),
                bind(PENDING_PROPOSAL_ROOT_SLOT, "votes · "),
                bind(THRESHOLD_SLOT, "quorum (M) · "),
                bind(GOVERNANCE_COMMITTEE_ROOT_SLOT, "committee · "),
                bind(VERSION_SLOT, "version · "),
            ]),
            section("Actions", "", vec![
                action("+", "Propose",  METHOD_PROPOSE),
                action("✓", "Vote",     METHOD_VOTE),
                action("⚖", "Commit",   METHOD_COMMIT),
                action("⛓", "Register", METHOD_REGISTER),
            ]),
        ]
    })
}

/// **The governed-namespace card as serialized `deos.ui.*` JSON** — byte-for-byte
/// the `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn governance_card_json() -> String {
    serde_json::to_string(&governance_card_value()).expect("the governance card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_stage_pill() {
        let card = governance_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Governed Namespace"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(pills[0]["props"]["text"], "VOTING");
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = governance_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "draft → proposed → voting → committed");
        assert_eq!(items[2]["label"], "› Voting", "the active step is marked");
    }

    #[test]
    fn the_quorum_gauge_reads_the_live_vote_tally_toward_m() {
        // The killer governance visual: the running tally (PENDING_PROPOSAL_ROOT_SLOT)
        // over the representative quorum M, so the bar fills votes_for / M.
        let card = governance_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "a single quorum-progress gauge");
        assert_eq!(
            gauges[0]["props"]["slot"],
            PENDING_PROPOSAL_ROOT_SLOT as usize
        );
        assert_eq!(gauges[0]["props"]["max"], QUORUM);
    }

    #[test]
    fn the_proposal_binds_surface_the_live_governance_state() {
        let card = governance_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                ROUTE_TABLE_ROOT_SLOT as u64,
                PENDING_PROPOSAL_ROOT_SLOT as u64,
                THRESHOLD_SLOT as u64,
                GOVERNANCE_COMMITTEE_ROOT_SLOT as u64,
                VERSION_SLOT as u64,
            ],
            "the binds surface route / votes / quorum / committee / version"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = governance_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![METHOD_PROPOSE, METHOD_VOTE, METHOD_COMMIT, METHOD_REGISTER]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = governance_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, proposal section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
