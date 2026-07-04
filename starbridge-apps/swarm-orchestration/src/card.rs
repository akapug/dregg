//! # swarm-orchestration — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos world
//! by shipping its surface as a **renderer-independent card** — a serializable
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
//! `Cargo.toml`). A starbridge-app must never depend on it — that would feature-unify
//! the elephants onto the main build. So the app's contribution is the **view-tree
//! JSON** (this module): pure `serde_json`, no elephant. The deos world's renderers
//! consume it; this module owns the card definition and proves it is well-formed.
//!
//! ## The card shape — a rich, live dispatch-board surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a LIVE `pill` reading
//!     [`EPOCH_SLOT`](crate::EPOCH_SLOT) and naming the swarm phase as a WORD (`OPEN` at
//!     epoch 0, `DISPATCHING` once a committed dispatch advances the counter), and a
//!     `breadcrumb` of the dispatch lifecycle
//!     (Closed → Open → Dispatching → Spent) with the current step marked;
//!   - a **"Budget" `section`** surfacing the LIVE budget gate — the KILLER VISUAL: a
//!     `gauge` per worker meter ([`SPENT_A_SLOT`](crate::SPENT_A_SLOT) /
//!     [`SPENT_B_SLOT`](crate::SPENT_B_SLOT)) filling toward the shared `BUDGET`
//!     ceiling, so the two meters together VISUALIZE the atomic budget gate
//!     `spent_a + spent_b <= budget` (the `AffineLe` tooth the executor enforces — the
//!     two bars can never collectively overrun the ceiling). Plus `bind`s on the
//!     [`LEAD_SLOT`](crate::LEAD_SLOT) (the provenance anchor), the
//!     [`BUDGET_SLOT`](crate::BUDGET_SLOT) (the mandate), both spend meters, and the
//!     [`EPOCH_SLOT`](crate::EPOCH_SLOT) dispatch counter — each a fine-grained signal
//!     that re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances when a fired dispatch commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per mutating method
//!     (`open_board` / `dispatch` / `grant_worker`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_OPEN_BOARD`](crate::service::METHOD_OPEN_BOARD), …) so the card and the
//! service cell speak the same swarm.

use serde_json::{Value, json};

use crate::service::{METHOD_DISPATCH, METHOD_GRANT_WORKER, METHOD_OPEN_BOARD};
use crate::{BUDGET_SLOT, EPOCH_SLOT, LEAD_SLOT, SPENT_A_SLOT, SPENT_B_SLOT};

/// The budget gauge's denominator — a representative swarm mandate so a worker's
/// spend meter fills its bar as the budget is consumed (the seeded board opens with a
/// `1_000` budget; see [`seed_board`](crate::seed_board)). Both worker gauges share
/// this ceiling: their two fills together CANNOT overrun it (the `AffineLe` gate).
const BUDGET_GAUGE_MAX: u64 = 1_000;

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
/// (a raw counter integer) hidden in the simple projection, revealed in the adept
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

/// An action row — an `icon` + a mutating-method `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The swarm-orchestration card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live dispatch-board surface: a status header (name + `DISPATCHING` pill +
/// dispatch-lifecycle breadcrumb), a "Budget" section surfacing the KILLER VISUAL — the
/// two per-worker spend gauges filling toward the shared `BUDGET` ceiling (the
/// `AffineLe(spent_a + spent_b <= budget)` gate visualized) — plus the lead / budget /
/// meters / epoch binds, and an "Actions" section of the three icon-labelled mutating
/// buttons. Renderer-independent DATA. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn board_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header pill reads the LIVE epoch counter: a freshly-opened board (epoch 0)
            // reads OPEN, and every committed dispatch advances it into DISPATCHING (fallback).
            row(vec![text("Swarm Orchestration"), pill_live(EPOCH_SLOT as usize, "DISPATCHING", "accent", json!([
                { "value": 0, "label": "OPEN", "tag": "good" },
            ]))]),
            breadcrumb(&["Closed", "Open", "Dispatching", "Spent"], 2),
            divider(),
            section("Budget", "genuine", vec![
                // THE KILLER VISUAL — the two worker meters filling toward the shared
                // budget ceiling: together they CANNOT overrun it (the AffineLe gate).
                gauge(SPENT_A_SLOT as usize, BUDGET_GAUGE_MAX, "worker-a spend "),
                gauge(SPENT_B_SLOT as usize, BUDGET_GAUGE_MAX, "worker-b spend "),
                bind(LEAD_SLOT as usize, "lead · ", "id", false),
                bind(BUDGET_SLOT as usize, "budget · ", "amount", false),
                bind(SPENT_A_SLOT as usize, "spent A · ", "amount", false),
                bind(SPENT_B_SLOT as usize, "spent B · ", "amount", false),
                // The raw dispatch counter is dev-y — the header pill + breadcrumb show the phase.
                bind(EPOCH_SLOT as usize, "epoch · ", "raw", true),
            ]),
            section("Actions", "", vec![
                action("+", "Open Board",   METHOD_OPEN_BOARD),
                action("→", "Dispatch",     METHOD_DISPATCH),
                action("⑂", "Grant Worker", METHOD_GRANT_WORKER),
            ]),
        ]
    })
}

/// **The swarm-orchestration card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn board_card_json() -> String {
    serde_json::to_string(&board_card_value()).expect("the swarm card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_state_pill() {
        let card = board_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Swarm Orchestration"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads the dispatch counter and names the phase.
        assert_eq!(
            pills[0]["props"]["text"], "DISPATCHING",
            "the static fallback word (epoch advanced)"
        );
        assert_eq!(pills[0]["props"]["slot"], EPOCH_SLOT as usize);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "epoch 0 reads OPEN");
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "OPEN");
    }

    #[test]
    fn the_budget_binds_carry_their_display_fmt() {
        let card = board_card_value();
        let binds = of_kind(&card, "bind");
        let prop = |slot: u8, key: &str| -> Value {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .map(|b| b["props"][key].clone())
                .unwrap()
        };
        assert_eq!(
            prop(LEAD_SLOT, "fmt"),
            "id",
            "the lead paints an avatar handle"
        );
        assert_eq!(
            prop(BUDGET_SLOT, "fmt"),
            "amount",
            "the budget groups digits"
        );
        assert_eq!(prop(SPENT_A_SLOT, "fmt"), "amount", "spent A groups digits");
        assert_eq!(prop(SPENT_B_SLOT, "fmt"), "amount", "spent B groups digits");
        assert_eq!(
            prop(EPOCH_SLOT, "fmt"),
            "raw",
            "the raw counter stays plain"
        );
        // The raw dispatch counter is adept-only (the header pill + breadcrumb show the phase).
        assert_eq!(
            prop(EPOCH_SLOT, "adept"),
            true,
            "the epoch counter is dev-y"
        );
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = board_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "closed → open → dispatching → spent");
        assert_eq!(
            items[2]["label"], "› Dispatching",
            "the active step is marked"
        );
    }

    #[test]
    fn the_budget_gauges_read_the_two_worker_spend_meters() {
        let card = board_card_value();
        let gauges = of_kind(&card, "gauge");
        // THE KILLER VISUAL: a gauge per worker meter, both maxing at the shared budget
        // ceiling — together they visualize `spent_a + spent_b <= budget`.
        assert_eq!(gauges.len(), 2, "one gauge per worker spend meter");
        assert_eq!(gauges[0]["props"]["slot"], SPENT_A_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], BUDGET_GAUGE_MAX);
        assert_eq!(gauges[1]["props"]["slot"], SPENT_B_SLOT as usize);
        assert_eq!(
            gauges[1]["props"]["max"], BUDGET_GAUGE_MAX,
            "both worker gauges share the budget ceiling"
        );
    }

    #[test]
    fn the_binds_surface_lead_budget_meters_and_epoch() {
        let card = board_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                LEAD_SLOT as u64,
                BUDGET_SLOT as u64,
                SPENT_A_SLOT as u64,
                SPENT_B_SLOT as u64,
                EPOCH_SLOT as u64,
            ],
            "the binds surface lead / budget / meters / epoch"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = board_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![METHOD_OPEN_BOARD, METHOD_DISPATCH, METHOD_GRANT_WORKER]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = board_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, budget section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
