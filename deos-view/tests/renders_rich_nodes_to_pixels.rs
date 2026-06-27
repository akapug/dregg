//! THE PROOF, BY RUNNING: the RICHNESS-EXPANSION nodes (`section`, `tabs`, `gauge`,
//! `divider` — batch 1 of growing deos-view toward native-cockpit parity) round-trip the
//! `{kind, props, children}` wire format AND render to REAL gpui-component pixels, and a
//! `tabs` selection — driven by a REAL cap-gated verified turn — visibly switches the
//! displayed panel. This is the expansion path proven end-to-end: a card can now express a
//! titled section, a bound gauge bar, a divider, and a stateful tab-strip whose switch is a
//! turn — none of which the 8-node vocabulary could.
//!
//! The flow (one big-stack thread — the same harness the applet/inspector/layout proofs use):
//!   1. Build a view-tree JSON using all four new nodes; parse it and ASSERT the typed shape
//!      (the serde round-trip on the new `RawProps` fields: title/tag/max/tabs/selectedSlot/
//!      selectTurn).
//!   2. Render it over a live applet (tab 0 = the State panel, showing a live `bind` of the
//!      gauged slot) → PNG #1.
//!   3. Fire `select(1)` — a REAL verified turn writing the selected-tab slot — switching to
//!      the Actions panel; re-render → PNG #2, which DIFFERS from #1 (the tab switch changed
//!      the displayed panel).

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView, ViewNode};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

/// A card whose model carries: slot 0 = a gauged value (seed 40, the gauge's `slot`); slot 1
/// = the selected-tab index (seed 0). Affordances: `select` writes its arg into slot 1 (a tab
/// switch IS a verified turn); `inc` bumps slot 0. Authority `None` so the test fires freely.
fn rich_card() -> Applet {
    let select = Affordance {
        name: "select".into(),
        required: AuthRequired::None,
        apply: Box::new(|_model, arg| vec![(1usize, pack_u64(arg.max(0) as u64))]),
    };
    let inc = Affordance {
        name: "inc".into(),
        required: AuthRequired::None,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    Applet::mint(
        [0x5E; 32],
        [0u8; 32],
        &[(0usize, pack_u64(40)), (1usize, pack_u64(0))],
        vec![select, inc],
        AuthRequired::None,
    )
}

/// The view-tree exercising all four batch-1 nodes: a titled `section` (genuine-tagged) holding
/// a bound `gauge` (slot 0 / max 100), a `divider`, and a `tabs` (slot 1) whose State panel shows
/// a live `bind` of slot 0 and whose Actions panel holds an `inc` button.
const RICH_VIEW_JSON: &str = r#"{
  "kind": "section",
  "props": { "title": "Rich nodes", "tag": "genuine" },
  "children": [
    { "kind": "gauge", "props": { "slot": 0, "max": 100, "label": "balance " } },
    { "kind": "divider", "props": {} },
    {
      "kind": "tabs",
      "props": { "tabs": ["State", "Actions"], "selectedSlot": 1, "selectTurn": "select" },
      "children": [
        { "kind": "vstack", "props": {}, "children": [
          { "kind": "text", "props": { "text": "live balance:" } },
          { "kind": "bind", "props": { "slot": 0, "label": "= " } }
        ]},
        { "kind": "vstack", "props": {}, "children": [
          { "kind": "button", "props": { "label": "inc +5", "onClick": { "turn": "inc", "arg": 5 } } }
        ]}
      ]
    }
  ]
}"#;

#[test]
fn the_rich_nodes_round_trip_and_render_and_a_tab_switch_is_a_turn() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("rich-nodes render proof thread");
}

fn body() {
    let out = out_dir();

    // ── 1. ROUND-TRIP: the JSON parses into the typed shape (the new RawProps fields land) ──
    let tree = parse_view_tree(RICH_VIEW_JSON).expect("parse the rich view-tree");
    let ViewNode::Section {
        title,
        tag,
        children,
    } = &tree
    else {
        panic!("root is a section");
    };
    assert_eq!(title, "Rich nodes", "the section title round-tripped");
    assert_eq!(tag, "genuine", "the section tag round-tripped");
    assert!(
        matches!(
            children.first(),
            Some(ViewNode::Gauge {
                slot: 0,
                max: 100,
                ..
            })
        ),
        "the gauge node round-tripped (slot 0, max 100)"
    );
    assert!(
        matches!(children.get(1), Some(ViewNode::Divider)),
        "the divider node round-tripped"
    );
    let tabs_node = children.get(2).expect("the tabs node");
    let ViewNode::Tabs {
        tabs,
        selected_slot,
        select_turn,
        panels,
    } = tabs_node
    else {
        panic!("the third child is a tabs node");
    };
    assert_eq!(
        tabs,
        &["State".to_string(), "Actions".to_string()],
        "tab labels round-tripped"
    );
    assert_eq!(*selected_slot, 1, "the selectedSlot round-tripped");
    assert_eq!(select_turn, "select", "the selectTurn round-tripped");
    assert_eq!(panels.len(), 2, "both tab panels round-tripped");

    // ── 2. Render over a live applet → PNG #1 (tab 0 = State, the bound balance row) ─────────
    let shared = Rc::new(RefCell::new(rich_card()));
    assert_eq!(
        shared.borrow().get_u64(1),
        0,
        "tab 0 (State) is selected at seed"
    );

    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let tree0 = parse_view_tree(RICH_VIEW_JSON).expect("re-parse for the view");
    let a0 = shared.clone();
    let window = hr
        .open(520.0, 760.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(a0, tree0))
        })
        .expect("open the rich-nodes window");
    let frame0 = hr.capture(window.into()).expect("capture frame 0");
    let png0 = out.join("rich-nodes-state.png");
    frame0.save(&png0).expect("save PNG #0");
    assert!(
        frame0.width() > 0 && frame0.height() > 0,
        "frame 0 has pixels"
    );

    // ── 3. FIRE select(1) — a REAL verified turn switching to the Actions tab → PNG #2 ───────
    let receipt = shared
        .borrow_mut()
        .fire("select", 1)
        .expect("the tab-select affordance fires a verified turn");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "a real TurnReceipt committed"
    );
    assert_eq!(
        shared.borrow().get_u64(1),
        1,
        "the selected-tab slot advanced 0 -> 1"
    );

    // The `tabs` arm reads its selected slot immediate-mode, so a window refresh repaints the
    // newly-selected panel (no fine-grained hook needed for the tab switch itself).
    hr.update(|cx| cx.refresh_windows());
    let frame1 = hr.capture(window.into()).expect("capture frame 1");
    let png1 = out.join("rich-nodes-actions.png");
    frame1.save(&png1).expect("save PNG #1");
    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the tab switch (a verified turn) changed the displayed panel — the frame differs"
    );

    println!("RENDERED RICH-NODES PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  state (tab 0)   : {}", png0.display());
    println!("  actions (tab 1) : {}", png1.display());
}
