//! THE DISCORD PROJECTION, IN THE TEST SUITE: the SAME deos-js card view-tree the native
//! render proof paints to gpui pixels — and the web renderer paints to HTML — renders,
//! gpui-FREE, to a serenity `CreateEmbed` + button components. Same DATA, four renderers ⇒
//! the card is renderer-INDEPENDENT, and the discord-bot's surfaces ARE these cards.
//!
//! This test is gpui-FREE and deos-js-FREE: it runs under
//! `cargo test -p deos-view --no-default-features --features discord`. It is the Discord
//! mirror of `web_projection_renders_card` (which asserts the HTML shape): there,
//! `ViewNode → HTML`; here, `ViewNode → CreateEmbed`. We assert the embed SHAPE by
//! serializing the builders (serenity's `CreateEmbed`/`CreateActionRow` are `Serialize`)
//! to JSON — title / description / fields / components match the tree.
#![cfg(feature = "discord")]

use deos_view::discord::{affordance_custom_id, parse_affordance_id, render_card};
use deos_view::parse_view_tree;

/// The EXACT `JSON.stringify(tree)` the SpiderMonkey engine produces for the counter card —
/// byte-for-byte the same serialized tree the web/native proofs consume.
const COUNTER_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Counter applet" } },
    { "kind": "bind", "props": { "slot": 0, "label": "count: " } },
    { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
  ]
}"#;

#[test]
fn counter_card_view_tree_renders_to_a_discord_embed_with_a_live_bind() {
    let tree = parse_view_tree(COUNTER_CARD_JSON).expect("parse the engine counter card");

    // Frame 0: the un-driven start (count = 0).
    let card0 = render_card("deos counter", &tree, &[0]);
    let embed0 = serde_json::to_value(&card0.embed).expect("embed serializes");

    assert_eq!(embed0["title"], "deos counter", "the title heads the embed");
    let desc0 = embed0["description"].as_str().unwrap_or("");
    assert!(
        desc0.contains("Counter applet"),
        "the text node became a description line"
    );
    assert!(
        desc0.contains("count: 0"),
        "the bind painted its live value 0 into the description"
    );

    // THE AFFORDANCE SURVIVED THE DISCORD PROJECTION — the button became a component whose
    // custom-id carries the engine's `{turn:"inc", arg:1}` (Discord's `data-turn`).
    let rows = serde_json::to_value(&card0.components).expect("components serialize");
    let button = &rows[0]["components"][0];
    assert_eq!(button["label"], "+1", "the button label survived");
    assert_eq!(
        button["custom_id"], "deosturn:inc:1",
        "the affordance payload rides the custom-id"
    );

    // Frame 1: the IDENTICAL tree at the post-`inc` value (count = 1) — the bind re-paint.
    let card1 = render_card("deos counter", &tree, &[1]);
    let embed1 = serde_json::to_value(&card1.embed).unwrap();
    assert!(
        embed1["description"].as_str().unwrap().contains("count: 1"),
        "frame 1 paints the advanced bound value 1"
    );
    assert_ne!(
        embed0, embed1,
        "the two frames DIFFER — the bind re-painted"
    );
}

#[test]
fn the_affordance_custom_id_round_trips() {
    // The Discord analogue of the web `data-turn`/`data-arg`: a button's `{turn, arg}` rides
    // the custom-id and a bot's component handler decodes it to fire a verified turn.
    let id = affordance_custom_id("inc", 7);
    assert_eq!(id, "deosturn:inc:7");
    assert_eq!(parse_affordance_id(&id), Some(("inc".to_string(), 7)));
    // A custom-id that is not ours is ignored.
    assert_eq!(parse_affordance_id("other:thing"), None);
}

#[test]
fn discord_renderer_maps_rows_tables_and_multi_button_rows() {
    // A tally-board-shaped card: a table of rows, each a named tally with its live bind value
    // and +1/−1 affordance buttons. This proves the LAYOUT nodes (`row`/`table`) become embed
    // FIELDS and the per-row buttons become a component grid — the same multi-affordance shape
    // the web renderer's tally board drives.
    let json = r#"{
      "kind": "vstack", "props": {}, "children": [
        { "kind": "text", "props": { "text": "Tally board" } },
        { "kind": "table", "props": {}, "children": [
            { "kind": "row", "props": {}, "children": [
                { "kind": "text", "props": { "text": "apples" } },
                { "kind": "bind", "props": { "slot": 0, "label": "" } },
                { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "apples", "arg": 1 } } },
                { "kind": "button", "props": { "label": "-1", "onClick": { "turn": "apples", "arg": -1 } } }
            ] },
            { "kind": "row", "props": {}, "children": [
                { "kind": "text", "props": { "text": "pears" } },
                { "kind": "bind", "props": { "slot": 1, "label": "" } },
                { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "pears", "arg": 1 } } }
            ] }
        ] }
      ]
    }"#;
    let tree = parse_view_tree(json).expect("parse the tally board");
    let card = render_card("Tally board", &tree, &[5, 9]);

    let embed = serde_json::to_value(&card.embed).unwrap();
    assert!(
        embed["description"]
            .as_str()
            .unwrap()
            .contains("Tally board"),
        "the heading text became the description"
    );

    // Two table rows → two embed fields, each `name → value` carrying its OWN bind value
    // (cursor advances in pre-order: apples=5 then pears=9).
    let fields = embed["fields"].as_array().expect("the rows became fields");
    assert_eq!(fields.len(), 2, "one field per table row");
    assert_eq!(fields[0]["name"], "apples");
    assert_eq!(fields[0]["value"], "5");
    assert_eq!(fields[1]["name"], "pears");
    assert_eq!(fields[1]["value"], "9");

    // The per-row buttons formed a component grid: apples +1/−1 then pears +1 (3 buttons),
    // each with its affordance in the custom-id.
    let rows = serde_json::to_value(&card.components).unwrap();
    let buttons = rows[0]["components"].as_array().expect("a button row");
    assert_eq!(buttons.len(), 3, "three affordance buttons across the rows");
    assert_eq!(buttons[0]["custom_id"], "deosturn:apples:1");
    assert_eq!(buttons[1]["custom_id"], "deosturn:apples:-1");
    assert_eq!(buttons[2]["custom_id"], "deosturn:pears:1");
}
