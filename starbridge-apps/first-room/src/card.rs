//! # first-room — the composed room as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! first-room is a **composition exemplar**, not a four-axis app (see `README.md`): it
//! WELDS other apps' organs (the colonist job, the escrow economy, the room model) into
//! one runnable scenario, and owns no verified primitive of its own. So it has no
//! `FactoryDescriptor`, no service interface, no `DeosApp` — those belong to the organs it
//! composes. What it CAN ship, coherently, is the modern app's renderer-independent CARD
//! axis: a `deos.ui.*` view-tree that SHOWS the composed room — the inhabitants, their
//! held mandates, their genuine (receipted) actions, the pay, and every in-room refusal
//! with the receipt-why.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants, so it
//! is a STANDALONE workspace EXCLUDED from the repo-root workspace. A starbridge-app must
//! never depend on it — that would feature-unify the elephants onto the main build. So the
//! app's contribution is the **view-tree JSON** (this module): pure `serde_json`, no
//! elephant. The deos world's renderers consume it; this module owns the card definition
//! and proves it is well-formed.
//!
//! Unlike the lifecycle cards (`bounty-board`, `swarm-orchestration`), this card carries
//! NO action buttons: the room is a read-only COMPOSED VIEW (a render of the welded
//! scenario), and the actions live on the organs' own service/affordance surfaces. The
//! card renders the [`Room`](crate::Room) the [`scenario`](crate::scenario) driver
//! produced from the REAL executor's receipts/refusals — the genuine activity and the
//! anti-ghost refusals, side by side.

use serde_json::{Value, json};

use crate::room::{InhabitantView, Room, RoomView};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.vstack` node wrapping `children`.
fn vstack(children: Vec<Value>) -> Value {
    json!({ "kind": "vstack", "props": {}, "children": children })
}

/// Render ONE inhabitant as a `deos.ui.vstack` section: a name header, the held mandate,
/// the pay, then the GENUINE (receipted) actions and the in-room REFUSALS (each tagged so
/// a renderer can style the two distinctly — the anti-ghost tooth made visible).
fn inhabitant_section(i: &InhabitantView) -> Value {
    let mut children = vec![
        text(&format!("{} ({})", i.name, i.short)),
        text(&format!("mandate: {}", i.mandate)),
        text(&format!("paid: {}", i.paid)),
    ];
    for a in &i.committed_actions {
        children.push(json!({
            "kind": "text",
            "props": { "text": format!("✓ {}", a.summary), "tag": "genuine" }
        }));
    }
    for r in &i.refusals {
        children.push(json!({
            "kind": "text",
            "props": { "text": format!("✗ {} — {}", r.attempted, r.reason), "tag": "refusal" }
        }));
    }
    vstack(children)
}

/// **The first-room card as a `deos.ui.*` view-tree** (a `serde_json::Value`) for a
/// rendered [`RoomView`].
///
/// A `vstack` of a room header and one nested `vstack` per inhabitant (its mandate,
/// genuine actions, and in-room refusals). Renderer-independent DATA: hand it to any
/// `deos-view` renderer (native / web / discord) to paint the SAME composed room.
pub fn room_card_value(room: &RoomView) -> Value {
    let mut children = vec![text(&format!("First Room — {}", room.name))];
    for i in &room.inhabitants {
        children.push(inhabitant_section(i));
    }
    vstack(children)
}

/// **The first-room card as a `deos.ui.*` view-tree for a live [`Room`]** — the
/// convenience over [`room_card_value`] that renders the room first.
pub fn card_for_room(room: &Room) -> Value {
    room_card_value(&room.render())
}

/// **The first-room card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses. This is the string a host
/// serves / embeds.
pub fn room_card_json(room: &RoomView) -> String {
    serde_json::to_string(&room_card_value(room)).expect("the first-room card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::room::{GenuineAction, InRoomRefusal, InhabitantView, Room};
    use crate::run_first_room;
    use dregg_app_framework::CellId;

    fn demo_room() -> Room {
        let mut room = Room::new(CellId::from_bytes([1u8; 32]), "the workshop");
        room.enter(InhabitantView {
            cell: CellId::from_bytes([2u8; 32]),
            short: "0202…".into(),
            name: "the colonist".into(),
            mandate: "JOB: gather→make→hand-off".into(),
            committed_actions: vec![GenuineAction {
                summary: "Gather (step 0→1)".into(),
                receipt_hash: [7u8; 32],
            }],
            refusals: vec![InRoomRefusal {
                attempted: "skip a prerequisite step".into(),
                reason: "refused by MonotonicSequence(JOB_CURSOR) — program".into(),
            }],
            paid: 800,
        });
        room
    }

    #[test]
    fn the_card_is_a_vstack_with_a_header_and_a_section_per_inhabitant() {
        let room = demo_room();
        let card = card_for_room(&room);
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header + one inhabitant section
        assert_eq!(children.len(), 2);
        assert_eq!(children[0]["kind"], "text");
        assert_eq!(children[0]["props"]["text"], "First Room — the workshop");
        assert_eq!(children[1]["kind"], "vstack", "the inhabitant section");
    }

    #[test]
    fn the_inhabitant_section_tags_genuine_actions_and_refusals_distinctly() {
        let room = demo_room();
        let card = card_for_room(&room);
        let section = &card["children"][1];
        let nodes = section["children"].as_array().unwrap();
        // name, mandate, paid, one genuine, one refusal
        assert_eq!(nodes.len(), 5);
        let genuine = nodes
            .iter()
            .find(|n| n["props"]["tag"] == "genuine")
            .unwrap();
        assert!(genuine["props"]["text"].as_str().unwrap().starts_with("✓"));
        let refusal = nodes
            .iter()
            .find(|n| n["props"]["tag"] == "refusal")
            .unwrap();
        assert!(refusal["props"]["text"].as_str().unwrap().starts_with("✗"));
        assert!(
            refusal["props"]["text"]
                .as_str()
                .unwrap()
                .contains("refused by")
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = room_card_json(&demo_room().render());
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
    }

    #[test]
    fn the_card_renders_the_real_welded_scenario_room() {
        // The card renders the ACTUAL room the scenario produces from the real executor —
        // the colonist + the payer, the genuine job steps, the pay, and all five in-room
        // refusals from the try-to-cheat battery.
        let t = run_first_room();
        let card = card_for_room(&t.room);
        let children = card["children"].as_array().unwrap();
        // header + two inhabitant sections (the colonist + the payer).
        assert_eq!(children.len(), 1 + t.room.occupancy());
        // The colonist section carries its five refusals (the anti-ghost surface).
        let colonist = &children[1];
        let refusals = colonist["children"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|n| n["props"]["tag"] == "refusal")
            .count();
        assert_eq!(refusals, 5, "the five cheat refusals render in-room");
    }
}
