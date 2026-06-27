//! CARD PANE — mount a hyperdreggmedia CARD (a deos-js applet's view-tree) as a LIVE
//! cockpit surface, backed by the cockpit's REAL `World`.
//!
//! This is the visible counterpart to [`crate::agent_attach`]. Where `agent_attach`
//! proves the AGENT'S HANDS drive the live ledger headlessly, this proves the CARD —
//! the operator-facing applet view — renders as real gpui-component pixels IN the
//! cockpit, and its button fires a real verified turn on the SAME live `World` the
//! cockpit inspector reads.
//!
//! ## The seam it closes
//!
//! `deos-view` ([`deos_view::AppletView`]) already renders a deos-js applet's view-tree
//! to real gpui-component widgets — but over the EMBEDDED [`deos_js::Applet`] (which
//! mints its own throwaway single-cell world). The cockpit's live substance is the
//! ATTACHED applet ([`deos_js::AttachedApplet`]), whose `fire` commits THROUGH
//! [`crate::agent_attach::WorldSinkAdapter::live`] onto the operator's real cells.
//!
//! [`CardPane`] is the small weld: it walks the SAME `deos.ui.*` view-tree
//! ([`deos_view::ViewNode`], parsed by [`deos_view::parse_view_tree`] from the REAL
//! engine-produced JSON) into the SAME gpui-component vocabulary, but binds + fires
//! against the live `AttachedApplet`:
//!
//!   * a `bind` node re-reads the bound model slot off the LIVE ledger
//!     (`AttachedApplet::get_u64` → a witnessed read of the operator's real cell); and
//!   * a `button`'s `on_click` calls `AttachedApplet::fire` = ONE cap-gated verified
//!     turn committed through `World::commit_turn` onto the live ledger (a receipt that
//!     lands on the cockpit's own provenance log).
//!
//! The view-tree is AUTHORED gpui-free (the JS builds `deos.ui.*` data + `JSON.stringify`s
//! it into the applet's ephemeral view-state — NO turn), so a throwaway embedded engine
//! authors the tree, and the LIVE `AttachedApplet` is the substance the rendered widgets
//! drive. (The cap tooth still runs in deos-js before every committed fire.)

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, App, ClickEvent, Context, FontWeight, IntoElement, ParentElement, Render, Styled,
    Window,
};
use gpui_component::button::{Button, ButtonVariants};
use gpui_component::label::Label;
use gpui_component::{h_flex, v_flex, ActiveTheme};

use deos_js::AttachedApplet;
use deos_view::{parse_view_tree, ViewNode};

/// A shared, interior-mutable handle on the LIVE attached applet. The card reads the
/// model through it (a `bind` re-read off the live ledger) and a button's `on_click`
/// fires a verified turn through it (a real turn on the cockpit's World). One handle,
/// shared by every widget — the single sovereign cell behind the whole card.
pub type SharedAttached = Rc<RefCell<AttachedApplet>>;

/// The cockpit surface that renders a deos-js CARD over the LIVE `World`. A real gpui
/// `Render` entity: open it in a (headless or windowed) window and it paints the card's
/// widgets, and a button fires a real verified turn on the live ledger.
pub struct CardPane {
    /// The live attached applet (shared so button handlers fire live turns + binds
    /// re-read the live ledger).
    applet: SharedAttached,
    /// The extracted view-tree (the real `deos.ui.*` element-tree the JS authored).
    tree: ViewNode,
    /// A short title shown above the card (the surface chrome).
    title: String,
}

impl CardPane {
    /// Build a card pane from a shared live applet + its view-tree + a title.
    pub fn new(applet: SharedAttached, tree: ViewNode, title: impl Into<String>) -> Self {
        Self {
            applet,
            tree,
            title: title.into(),
        }
    }

    /// The shared live applet handle (for the caller to inspect receipts / the live
    /// ledger after a turn fires — the SAME applet the widgets drive).
    pub fn applet(&self) -> SharedAttached {
        self.applet.clone()
    }

    /// **Replace the rendered view-tree** — the edit-from-within hook. After a
    /// [`deos_js::card_editor::ViewPatch`] re-folds the card's view document, the
    /// caller bridges the new tree to a [`ViewNode`] and swaps it in here, so the next
    /// paint draws the reshaped surface. The live applet (the substance binds/fires
    /// drive) is untouched — only the view changed (the view is data, not code).
    pub fn set_tree(&mut self, tree: ViewNode) {
        self.tree = tree;
    }

    /// The card's current rendered view-tree (read-only) — so a mount can re-derive
    /// the surface or assert its shape after a reshape.
    pub fn tree(&self) -> &ViewNode {
        &self.tree
    }

    /// Render one view-tree node into a gpui element. Recursive: containers render
    /// their children with the same vocabulary `deos_view::AppletView` uses, but a
    /// `bind` re-reads the LIVE ledger and a `button` fires a LIVE turn.
    fn node(&self, node: &ViewNode, _window: &mut Window, cx: &mut App) -> gpui::AnyElement {
        let theme_fg = cx.theme().foreground;
        match node {
            ViewNode::VStack(children) => {
                let mut col = v_flex().gap_2().p_3();
                for c in children {
                    col = col.child(self.node(c, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Row(children) => {
                let mut row = h_flex().gap_2().items_center();
                for c in children {
                    row = row.child(self.node(c, _window, cx));
                }
                row.into_any_element()
            }
            ViewNode::Text(s) => Label::new(s.clone())
                .text_color(theme_fg)
                .into_any_element(),
            ViewNode::Bind { slot, label } => {
                // THE SIGNAL BINDING over the LIVE ledger — re-read the bound model slot
                // off the cockpit's real cell (the same witnessed read the JS closure
                // made, now through `AttachedApplet`). Immediate-mode: this re-runs every
                // render, so after a live turn the new value shows.
                let value = self.applet.borrow().get_u64(*slot);
                let text = if label.is_empty() {
                    value.to_string()
                } else {
                    format!("{label}{value}")
                };
                Label::new(text)
                    .font_weight(FontWeight::BOLD)
                    .text_color(theme_fg)
                    .into_any_element()
            }
            ViewNode::Button { label, turn, arg } => {
                // THE REAL LIVE TURN — a button's onClick fires the applet's affordance =
                // ONE cap-gated verified turn committed THROUGH `World::commit_turn` onto
                // the live ledger. The handler captures the shared live applet + the
                // (turn, arg) from the view-tree.
                let applet = self.applet.clone();
                let turn = turn.clone();
                let arg = *arg;
                Button::new(("deos-card-aff", label_hash(label)))
                    .primary()
                    .label(label.clone())
                    .on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Fire the verified turn on the live World. A cap refusal /
                        // executor reject is surfaced to stderr (the screenshot stays
                        // honest); the live model simply does not advance.
                        //
                        // GUARDED at the event boundary: gpui dispatches this click from a
                        // `nounwind` Obj-C callback, so a panic crossing it would
                        // `process::abort` the whole cockpit. The `fire` is Result-typed,
                        // but `applet.borrow_mut()` would PANIC if the shared applet were
                        // already borrowed (e.g. a re-entrant fire), so contain any panic
                        // as a logged no-op rather than abort the process.
                        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                                eprintln!(
                                    "card-pane: live affordance '{turn}' did not commit: {e}"
                                );
                            }
                        }))
                        .map_err(|_| {
                            eprintln!(
                                "card-pane: live affordance '{turn}' PANICKED — contained \
                                 (no-op) instead of aborting (the gpui event boundary is \
                                 nounwind)."
                            );
                        });
                    })
                    .into_any_element()
            }
            ViewNode::Input { bind_view } => {
                // Ephemeral view-state (draft text) — NOT cell state, never a turn.
                let draft = self
                    .applet
                    .borrow()
                    .get_view(bind_view)
                    .unwrap_or("")
                    .to_string();
                h_flex()
                    .px_2()
                    .py_1()
                    .border_1()
                    .border_color(cx.theme().border)
                    .rounded(px(4.))
                    .child(Label::new(if draft.is_empty() {
                        format!("‹{bind_view}›")
                    } else {
                        draft
                    }))
                    .into_any_element()
            }
            ViewNode::List(items) => {
                let mut col = v_flex().gap_1();
                for it in items {
                    col = col.child(self.node(it, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Table(rows) => {
                let mut col = v_flex().gap_1().border_1().border_color(cx.theme().border);
                for r in rows {
                    col = col.child(self.node(r, _window, cx));
                }
                col.into_any_element()
            }

            // ── The RICHNESS EXPANSION (batch 1) — mirror `deos_view::render`'s arms, but
            //    bound + fired against the LIVE attached applet. ──────────────────────────
            ViewNode::Section {
                title,
                tag,
                children,
            } => {
                // A titled, bordered container — the uniform "styled section". `tag=="genuine"`
                // accents the border (the existing `props.tag` styling convention).
                let accent = if tag == "genuine" {
                    theme_fg
                } else {
                    cx.theme().border
                };
                let mut card = v_flex().gap_1().p_2().border_1().border_color(accent);
                if !title.is_empty() {
                    card = card.child(
                        Label::new(title.clone())
                            .font_weight(FontWeight::BOLD)
                            .text_color(theme_fg),
                    );
                }
                for c in children {
                    card = card.child(self.node(c, _window, cx));
                }
                card.into_any_element()
            }
            ViewNode::Tabs {
                tabs,
                selected_slot,
                select_turn,
                panels,
            } => {
                // The active tab index lives in a MODEL SLOT (read live off the ledger), so a
                // tab switch is a REAL cap-gated verified turn — reflective + replayable.
                let active = self.applet.borrow().get_u64(*selected_slot) as usize;
                // The tab strip: one Button per label, the active one `.primary()`; each fires
                // `select_turn` with `arg = its index` (a verified turn through the live applet).
                let mut strip = h_flex().gap_1();
                for (i, label) in tabs.iter().enumerate() {
                    let applet = self.applet.clone();
                    let turn = select_turn.clone();
                    let idx = i as i64;
                    let mut b =
                        Button::new(("deos-card-tab", label_hash(&format!("{select_turn}:{i}"))))
                            .label(label.clone());
                    if i == active {
                        b = b.primary();
                    }
                    strip = strip.child(b.on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Same nounwind-boundary guard as a `button` fire (the gpui Obj-C
                        // callback is `nounwind`; contain a re-entrant-borrow panic as a no-op).
                        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if let Err(e) = applet.borrow_mut().fire(&turn, idx) {
                                eprintln!("card-pane: tab select '{turn}' did not commit: {e}");
                            }
                        }))
                        .map_err(|_| {
                            eprintln!(
                                "card-pane: tab select '{turn}' PANICKED — contained (no-op)."
                            );
                        });
                    }));
                }
                // card_pane reads slots immediate-mode (no bind cursor), so render ONLY the
                // selected panel; out-of-range falls back to the first.
                let shown = if active < panels.len() { active } else { 0 };
                let mut col = v_flex().gap_2().child(strip);
                if let Some(panel) = panels.get(shown) {
                    col = col.child(self.node(panel, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Gauge { slot, max, label } => {
                // A bound progress / balance bar — reads its slot IMMEDIATE-MODE off the live
                // ledger. The fill width is `value / max`, clamped to `[0,1]`.
                let value = self.applet.borrow().get_u64(*slot);
                let ratio = if *max == 0 {
                    0.0
                } else {
                    (value as f64 / *max as f64).clamp(0.0, 1.0)
                };
                let track_w = 140.0_f32;
                let fill_w = (track_w as f64 * ratio) as f32;
                let text = if label.is_empty() {
                    format!("{value}/{max}")
                } else {
                    format!("{label}{value}/{max}")
                };
                v_flex()
                    .gap_1()
                    .child(Label::new(text).text_color(theme_fg))
                    .child(
                        div()
                            .w(px(track_w))
                            .h(px(8.))
                            .rounded(px(4.))
                            .bg(cx.theme().border)
                            .child(
                                div()
                                    .w(px(fill_w.max(0.0)))
                                    .h(px(8.))
                                    .rounded(px(4.))
                                    .bg(theme_fg),
                            ),
                    )
                    .into_any_element()
            }
            ViewNode::Divider => div()
                .h(px(1.))
                .w_full()
                .bg(cx.theme().border)
                .into_any_element(),
            ViewNode::Host { cell, view } => {
                // The COMPOSITION KEYSTONE — mount a cell's WHOLE hosted view-tree as a
                // subtree. A bordered frame with a muted `⌂ <cell>` header; an UNRESOLVED host
                // paints an honest placeholder (it has no tree to mount yet).
                let head = format!("⌂ {}", short_cell(cell));
                let mut frame = v_flex()
                    .gap_1()
                    .p_2()
                    .border_1()
                    .border_color(cx.theme().border)
                    .child(
                        Label::new(head)
                            .text_color(cx.theme().muted_foreground)
                            .into_any_element(),
                    );
                match view {
                    Some(v) => frame = frame.child(self.node(v, _window, cx)),
                    None => {
                        frame = frame.child(
                            Label::new(format!("‹mount cell {}: unresolved›", short_cell(cell)))
                                .text_color(cx.theme().muted_foreground),
                        )
                    }
                }
                frame.into_any_element()
            }
        }
    }
}

/// Truncate a hex cell-id for a compact host header (mirrors `deos_view::render::short_cell`).
fn short_cell(cell: &str) -> String {
    if cell.len() > 12 {
        format!("{}…", &cell[..12])
    } else {
        cell.to_string()
    }
}

impl Render for CardPane {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let title = self.title.clone();
        let app: &mut App = cx;
        let header_fg = app.theme().muted_foreground;
        let border = app.theme().border;
        let background = app.theme().background;
        let foreground = app.theme().foreground;
        // Walk the view-tree by BORROW (`&self.tree`) — it can be a large `ViewNode`,
        // and a deep clone every paint is pure waste; `node` only reads it. `self` is
        // borrowed immutably here, `app` is `cx` (a distinct object), so the two
        // borrows don't conflict.
        let body = self.node(&self.tree, window, app);
        div()
            .size_full()
            .bg(background)
            .text_color(foreground)
            .child(
                // The surface chrome — a titled card frame so it reads as a cockpit pane.
                v_flex()
                    .size_full()
                    .child(
                        div().px_3().py_2().border_b_1().border_color(border).child(
                            Label::new(title)
                                .font_weight(FontWeight::BOLD)
                                .text_color(header_fg),
                        ),
                    )
                    .child(body),
            )
    }
}

/// Author a card's view-tree by running `applet_js` in real SpiderMonkey against the
/// LIVE attached applet, then extract the engine-produced `deos.ui.*` tree.
///
/// The JS MUST build a `deos.ui.*` tree and stash it under [`deos_view::view_tree_key`]
/// via `app.view.set(...)` (ephemeral view-state — NO turn). The view-tree build commits
/// NOTHING; only a button's later `fire` does. The driven [`AttachedApplet`] is handed
/// back (its `WorldSink` reads + commits onto the live World) paired with the parsed
/// [`ViewNode`] — ready for [`CardPane::new`].
///
/// SpiderMonkey's engine is a process-global, thread-bound singleton, so `rt` is passed
/// in (the caller boots it once for the whole bake).
pub fn build_card_over_live(
    rt: &mut deos_js::JsRuntime,
    applet: AttachedApplet,
    applet_js: &str,
) -> Result<(AttachedApplet, ViewNode), String> {
    let outcome = rt
        .run_attached(applet, applet_js)
        .map_err(|e| format!("card view-tree authoring on the live World: {e}"))?;
    // The authoring JS stashes the stringified tree into the attached applet's ephemeral
    // view-state (NO turn) — and must commit no fires.
    if outcome.fires_committed != 0 {
        return Err(format!(
            "card view-tree authoring committed {} turn(s) — it must only build data",
            outcome.fires_committed
        ));
    }
    let attached = outcome.applet;
    let key = deos_view::view_tree_key();
    let json = attached
        .get_view(key)
        .ok_or_else(|| format!("card JS did not stash a view-tree under view-state '{key}'"))?
        .to_string();
    let tree = parse_view_tree(&json)?;
    Ok((attached, tree))
}

/// The ephemeral view-state key the card's authoring JS stashes its stringified
/// view-tree under (the SAME key [`build_card_over_live`] reads it back from). Exposed
/// so a bake's JS can name it consistently without depending on `deos-view` directly.
pub fn view_tree_key_for_card() -> &'static str {
    deos_view::view_tree_key()
}

/// A stable id salt for a button from its label (so two buttons in one card differ).
fn label_hash(label: &str) -> u64 {
    let mut h: u64 = 1469598103934665603; // FNV-1a offset
    for b in label.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    h
}
