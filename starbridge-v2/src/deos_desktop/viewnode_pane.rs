//! **THE CONTENT-IR BRIDGE** — a desktop window whose body IS a real
//! [`deos_view::ViewNode`] (a card-as-cell), rendered through deos-view's NATIVE
//! renderer beside the native-chrome surfaces.
//!
//! Every other desktop window is raw native gpui chrome (the NT inspector, the
//! World Explorer, the Document Explorer): the shell paints those directly. THIS
//! window proves the shell can ALSO host PORTABLE-IR content — a view-tree authored
//! as backend-independent DATA ([`deos_view::ViewNode`], the Rust mirror of the
//! `deos.ui.*` element-tree) and walked into pixels by the SAME renderer
//! ([`deos_view::AppletView`]) the card-pane / cockpit use, the SAME tree a web
//! renderer would walk into HTML ([`deos_view::web`]). One IR, two backends; the
//! native desktop is one of them.
//!
//! ## Light by construction
//!
//! We do NOT reach for the mozjs/SpiderMonkey authoring path (`build_card_over_live`)
//! here — that would balloon the surface with a JS engine just to BUILD a tree. The
//! point is to prove the desktop RENDERS the IR, so we take a STATIC tree:
//!
//!   * [`VIEWNODE_CARD_JSON`] is the portable boundary — the exact serialized
//!     `deos.ui.*` element-tree DATA a deos-js applet (or any authoring tool) emits.
//!     [`card_tree`] parses it with [`deos_view::parse_view_tree`] into the typed
//!     [`deos_view::ViewNode`] both renderers consume.
//!   * [`card_applet`] mints the backing [`deos_js::Applet`] on a fresh EMBEDDED
//!     verified executor (no mozjs): a `bind` re-reads its real cell slot, and the
//!     `+1` button fires the `bump` affordance = ONE cap-gated verified turn.
//!   * [`build_viewnode_view`] welds the two into a [`deos_view::AppletView`] gpui
//!     entity — deos-view's native renderer — for the desktop to host as a window
//!     body (the same way `dock::card_surface` hosts a `CardPane`).
//!
//! Gated on `card-pane` (which pulls `deos-view` + `deos-js` via `agent-js`); the
//! desktop's window-type registration falls back to the inspector body when the
//! feature is off, so the gpui-free / headless builds still compile.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{App, AppContext, Entity};

use deos_js::applet::{Slot, pack_u64};
use deos_js::{Affordance, Applet, CellModel};
use deos_view::{AppletView, SharedApplet, ViewNode, parse_view_tree};
use dregg_cell::AuthRequired;

/// The model slot the card's `bind` re-reads (the counter) and the `bump` affordance
/// writes — slot 0, the canonical counter shape the cockpit's cards use.
pub const VIEWNODE_CARD_SLOT: Slot = 0;

/// The genesis value seeded into [`VIEWNODE_CARD_SLOT`] — so the `bind` shows a real,
/// witnessed value on first paint (before any turn fires).
pub const VIEWNODE_CARD_SEED: u64 = 7;

/// The window title shown above the IR-rendered body (the surface chrome).
pub const VIEWNODE_CARD_TITLE: &str = "Portable IR · deos_view::ViewNode";

/// **The portable IR — the serialized `deos.ui.*` element-tree, as DATA.**
///
/// This is exactly the JSON a deos-js applet's `JSON.stringify(deos.ui.vstack(...))`
/// emits — the backend-independent boundary. [`card_tree`] parses it into the typed
/// [`ViewNode`] the NATIVE renderer ([`AppletView`]) and the WEB renderer
/// ([`deos_view::web`]) BOTH consume, node-for-node. Hosting this in a desktop window
/// proves the native shell renders the same IR a browser would.
pub const VIEWNODE_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "children": [
    { "kind": "text", "props": { "text": "Portable-IR card — hosted by the deos desktop" } },
    { "kind": "row", "children": [
      { "kind": "text", "props": { "text": "a real deos_view::ViewNode, rendered through AppletView" } }
    ]},
    { "kind": "bind", "props": { "slot": 0, "label": "live count: " } },
    { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "bump", "arg": 1 } } }
  ]
}"#;

/// Parse [`VIEWNODE_CARD_JSON`] into the typed [`ViewNode`] — the SAME tree the web
/// renderer renders. The constant is a fixed, valid `deos.ui.*` document, so a parse
/// failure here is a programming error (caught by [`tests`]).
pub fn card_tree() -> ViewNode {
    parse_view_tree(VIEWNODE_CARD_JSON).expect("the portable card IR must parse")
}

/// Mint the card's backing applet on a fresh EMBEDDED verified executor (no mozjs):
/// one sovereign cell, slot 0 seeded to [`VIEWNODE_CARD_SEED`], with a single `bump`
/// affordance that increments slot 0 by its arg. A rendered `bind` reads slot 0 off
/// this cell (a witnessed read); the `+1` button's `on_click` fires `bump` = ONE
/// cap-gated verified turn on this embedded ledger, leaving a real `TurnReceipt`.
pub fn card_applet() -> Applet {
    // A deterministic identity for the card cell (the desktop's IR demo cell).
    let public_key = [0x2au8; 32];
    let token_id = [0x1du8; 32];

    // `bump(arg)` — the counter affordance: write slot 0 := current + max(arg, 0).
    let bump = Affordance {
        name: "bump".to_string(),
        required: AuthRequired::Signature,
        apply: Box::new(|model: &CellModel, arg: i64| {
            let cur = model.field_u64(VIEWNODE_CARD_SLOT);
            let next = cur.wrapping_add(arg.max(0) as u64);
            vec![(VIEWNODE_CARD_SLOT, pack_u64(next))]
        }),
    };

    Applet::mint(
        public_key,
        token_id,
        &[(VIEWNODE_CARD_SLOT, pack_u64(VIEWNODE_CARD_SEED))],
        vec![bump],
        // Single-custody embedded world: the driver holds Signature, which satisfies
        // the `bump` affordance's `required` (the cap tooth still runs before each fire).
        AuthRequired::Signature,
    )
}

/// **Build the content-IR pane** — a [`deos_view::AppletView`] gpui entity over the
/// static portable [`ViewNode`] backed by the embedded [`card_applet`]. This IS
/// deos-view's native renderer; the desktop hosts the returned entity as a window
/// body (exactly as `dock::card_surface` hosts a `CardPane`), so a desktop window's
/// body becomes a rendered portable-IR surface.
pub fn build_viewnode_view(cx: &mut App) -> Entity<AppletView> {
    let applet: SharedApplet = Rc::new(RefCell::new(card_applet()));
    let tree = card_tree();
    cx.new(|_cx| AppletView::new(applet, tree))
}

/// Render the SAME portable tree through the WEB renderer (HTML) — the renderer-
/// independence proof the bake asserts beside the live native pane. The web renderer
/// walks the IDENTICAL [`ViewNode`] [`build_viewnode_view`] hands the native renderer,
/// so the produced markup carries the card's text, the seeded `bind` value, and the
/// button's `{turn, arg}` payload — the exact same content the desktop window paints.
pub fn card_html() -> String {
    let tree = card_tree();
    deos_view::web::render_card_document(VIEWNODE_CARD_TITLE, &tree, &[VIEWNODE_CARD_SEED])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn portable_ir_parses_to_the_expected_shape() {
        // The portable JSON parses to a vstack whose 4 children are the card's nodes.
        match card_tree() {
            ViewNode::VStack(children) => {
                assert_eq!(children.len(), 4, "card vstack: text, row, bind, button");
                assert!(matches!(children[0], ViewNode::Text(_)));
                assert!(matches!(children[1], ViewNode::Row(_)));
                match &children[2] {
                    ViewNode::Bind { slot, label } => {
                        assert_eq!(*slot, VIEWNODE_CARD_SLOT);
                        assert_eq!(label, "live count: ");
                    }
                    other => panic!("expected a bind node, got {other:?}"),
                }
                match &children[3] {
                    ViewNode::Button { label, turn, arg } => {
                        assert_eq!(label, "+1");
                        assert_eq!(turn, "bump");
                        assert_eq!(*arg, 1);
                    }
                    other => panic!("expected a button node, got {other:?}"),
                }
            }
            other => panic!("expected a vstack root, got {other:?}"),
        }
    }

    #[test]
    fn backing_applet_reads_seed_and_fires_a_real_turn() {
        let mut applet = card_applet();
        // The `bind` reads the seeded counter off the live embedded ledger.
        assert_eq!(applet.get_u64(VIEWNODE_CARD_SLOT), VIEWNODE_CARD_SEED);
        // The `+1` button fires `bump` = one cap-gated verified turn; the counter advances.
        applet
            .fire("bump", 1)
            .expect("the bump affordance must commit");
        assert_eq!(applet.get_u64(VIEWNODE_CARD_SLOT), VIEWNODE_CARD_SEED + 1);
    }

    #[test]
    fn the_web_renderer_renders_the_same_tree() {
        // The IDENTICAL portable tree the native renderer hosts also renders to HTML —
        // carrying the card's text, the seeded bind value, and the button payload.
        let html = card_html();
        assert!(html.contains("Portable-IR card"));
        assert!(
            html.contains("live count: 7"),
            "the seeded bind value paints"
        );
        assert!(
            html.contains("data-turn=\"bump\""),
            "the button's affordance payload"
        );
    }
}
