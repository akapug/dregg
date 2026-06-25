//! THE TOUCH SHELL — deos on a phone (the graphideOS / mobile shape).
//!
//! This is the FOURTH target-shape's UI layer (`docs/deos/MOBILE-DEOS.md`): the
//! same model (cell · cap · turn · receipt) and the same gpui renderer, re-bodied
//! for a thumb. It is DISTINCT from the mouse/keyboard desktop cockpit
//! ([`crate::cockpit`]) — it does not disturb it; it reuses the same gpui-free
//! view model the cockpit and the desktop drive (the live [`World`], the
//! [`WonderRoom`] cell projection, the uniform [`reflect`] object), and renders it
//! with `gpui-component`'s touch material (a bottom tab bar, large hit targets, a
//! bottom sheet).
//!
//! THE TOUCH MAPPING (`MOBILE-DEOS.md` §3, obeying `HIG.md`):
//!
//!   * **Tap = actuate.** A cell is a card you tap. Tap is the primary affordance
//!     — the "child taps a glowing cell and something delightful happens" of `HIG`
//!     principle 2, now literal. (Here: tap a cell → open its face sheet; tap the
//!     "actuate" face → a real verified turn.)
//!   * **Long-press = the flip / halo → the seven faces.** Right-click→actuate and
//!     the cell-flip-to-faces collapse onto **long-press → a bottom sheet** carrying
//!     the cell's faces (state · caps · links · history · the affordances it holds
//!     caps for, lit; ungranted ones dim, never hidden). `HIG`'s "reflection is one
//!     gesture" becomes one *touch* gesture. (gpui has no native long-press; the
//!     touch shell synthesizes it from a held pointer — see [`TouchShell::on_cell_press`].)
//!   * **The five modes → a thumb-reachable bottom tab bar**, not a side rail:
//!     Inhabit · Author · Dev · Inspect · Operate. `HIG` principle 4 ("one focused
//!     thing per screen") *wants* this — the phone enforces one surface in the body
//!     by physics.
//!   * **The home garden is the landing** — your cells as a scrollable wall of live
//!     glowing cards (the AOL-wonder home, `WonderRoom`), the launcher that replaces
//!     the icon grid.
//!
//! gpui is single-threaded; the [`World`] is shared as `Rc<RefCell<World>>`, exactly
//! as the cockpit shares it. A tap that actuates mutates it through the REAL executor
//! (predict-then-commit, [`crate::wonder::DragValue`] / [`crate::simulate`]) and the
//! garden re-renders from the post-state — the commit is the feedback (`HIG` principle 5).

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    ClickEvent, Context, FocusHandle, IntoElement, ParentElement, Render, SharedString, Styled,
    Window, div, prelude::*, px,
};

use gpui_component::Sizable;
use gpui_component::button::{Button, ButtonVariants};
use gpui_component::tab::{Tab, TabBar};

use dregg_cell::CellId;

use crate::reflect::{self, FieldValue, Inspectable};
use crate::views::theme;
use crate::wonder::{Halo, WonderRoom};
use crate::world::World;

// ===========================================================================
// THE FIVE MODES — the bottom tab bar (the thumb-reachable mode switch).
// ===========================================================================

/// The five deos modes, re-bodied as a bottom tab bar (`MOBILE-DEOS.md` §3). The
/// desktop's left rail of rooms becomes five tabs at the thumb edge; the body is
/// the ONE focused surface for the active mode (`HIG` principle 4).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// INHABIT — the home garden: your cells as a wall of live glowing cards, the
    /// AOL-wonder launcher ([`WonderRoom`]). The landing.
    Inhabit,
    /// AUTHOR — make things: a tappable list of the documents/cards in the image
    /// (cells carrying authored state), each opening to its faces.
    Author,
    /// DEV — the maker surface: the live image's cells as a developer sees them
    /// (balances, cap-webs), the touch form of the OBJECTS/inspector list.
    Dev,
    /// INSPECT — reflection: the focused cell projected through the uniform
    /// [`reflect`] object, its faces laid out for a thumb.
    Inspect,
    /// OPERATE — run the machine: the image's vitals (height, cell count, recent
    /// activity) — the touch form of the operator's dashboard.
    Operate,
}

impl Mode {
    /// The five modes in bottom-bar order (Inhabit first — the landing).
    pub const ALL: [Mode; 5] = [
        Mode::Inhabit,
        Mode::Author,
        Mode::Dev,
        Mode::Inspect,
        Mode::Operate,
    ];

    /// The tab's label (the word under the glyph).
    fn label(self) -> &'static str {
        match self {
            Mode::Inhabit => "Inhabit",
            Mode::Author => "Author",
            Mode::Dev => "Dev",
            Mode::Inspect => "Inspect",
            Mode::Operate => "Operate",
        }
    }

    /// The tab's glyph (a child reads the glyph; an adept reads the label — the
    /// wonder-first/depth-on-demand pairing of `HIG` principle 2).
    fn glyph(self) -> &'static str {
        match self {
            Mode::Inhabit => "🏡",
            Mode::Author => "✎",
            Mode::Dev => "⊹",
            Mode::Inspect => "◉",
            Mode::Operate => "⚙",
        }
    }

    fn index(self) -> usize {
        Mode::ALL.iter().position(|m| *m == self).unwrap_or(0)
    }

    fn from_index(ix: usize) -> Mode {
        Mode::ALL.get(ix).copied().unwrap_or(Mode::Inhabit)
    }
}

// ===========================================================================
// THE TOUCH SHELL — the whole phone surface over the live image.
// ===========================================================================

/// THE TOUCH SHELL — the phone-shaped deos surface. Owns the shared live
/// [`World`] (exactly as the cockpit does), the active [`Mode`], and the
/// optional open face-sheet (the long-press product). It renders three bands:
/// a slim status strip (authority always in view — `HIG` principle 5), the
/// ONE focused mode surface (the garden / lists / inspector), and the
/// thumb-reachable bottom tab bar.
pub struct TouchShell {
    /// The live local dregg image — shared `Rc<RefCell<World>>` (gpui is
    /// single-threaded; a tap that actuates mutates this through the real executor).
    world: Rc<RefCell<World>>,
    /// The active mode (the bottom-bar selection) — the free in-memory selector.
    mode: Mode,
    /// The cell whose FACE SHEET is open (the long-press product), if any. `None`
    /// = no sheet (the body surface is the whole screen). Opening it is the
    /// flip-to-faces gesture; tapping the scrim or a face's affordance closes /
    /// actuates.
    sheet: Option<CellId>,
    /// The cell the INSPECT mode is focused on (the reflected object). `None`
    /// focuses the first cell. A tap on a garden card in INSPECT mode sets this.
    inspect_focus: Option<CellId>,
    /// The last actuation outcome — a short human banner (committed / refused),
    /// shown on the open sheet. `HIG` principle 3: human words, never "T1 REJECT".
    last_outcome: Option<String>,
    /// Focus handle so the shell receives key/pointer events.
    focus: FocusHandle,
}

impl TouchShell {
    /// Build the touch shell over a shared live world.
    pub fn new(world: Rc<RefCell<World>>, focus: FocusHandle) -> Self {
        Self {
            world,
            mode: Mode::Inhabit,
            sheet: None,
            inspect_focus: None,
            last_outcome: None,
            focus,
        }
    }

    /// Select a mode by name (for the `--render-touch` bake's `--render-mode`).
    /// Returns `false` for an unknown name (the caller keeps the default).
    pub fn select_mode_named(&mut self, name: &str) -> bool {
        let target = Mode::ALL
            .into_iter()
            .find(|m| m.label().eq_ignore_ascii_case(name));
        match target {
            Some(m) => {
                self.mode = m;
                true
            }
            None => false,
        }
    }

    /// Open the face sheet on `cell` (the long-press / flip-to-faces gesture).
    /// Bake-driving entry: the screenshot bake opens it to show a long-press sheet.
    pub fn open_sheet(&mut self, cell: CellId) {
        self.sheet = Some(cell);
    }

    /// The live garden projection (the wonder room over the current image).
    fn garden(&self) -> WonderRoom {
        WonderRoom::build(&self.world.borrow())
    }

    // --- the gestures ------------------------------------------------------

    /// THE LONG-PRESS gesture — flip the cell to its faces (open the bottom sheet).
    /// gpui has no native long-press, so the shell treats a press on a card's
    /// dedicated "⋯ faces" affordance as the flip (the touch form of the desktop
    /// right-click→faces); a plain tap actuates instead (see [`Self::on_cell_tap`]).
    fn on_cell_press(&mut self, cell: CellId, cx: &mut Context<Self>) {
        self.open_sheet(cell);
        cx.notify();
    }

    /// THE TAP gesture — actuate (the primary affordance). In INSPECT mode a tap
    /// re-focuses the reflected object; elsewhere it opens the cell's faces (the
    /// safe, wonder-first default — a tap never silently commits; actuation is an
    /// explicit face inside the sheet). `HIG` principle 2.
    fn on_cell_tap(&mut self, cell: CellId, cx: &mut Context<Self>) {
        match self.mode {
            Mode::Inspect => self.inspect_focus = Some(cell),
            _ => self.sheet = Some(cell),
        }
        cx.notify();
    }

    /// THE ACTUATE face — fire a real verified turn from the sheet. The cell sends
    /// value to the image's brightest OTHER cell (a concrete, conserving
    /// [`Effect::Transfer`]), predicted-then-committed through the same machinery the
    /// COMPOSER uses ([`crate::wonder::DragValue`]). An over-reach is REFUSED in the
    /// prediction — surfaced as the human banner, never a faked move.
    fn actuate(&mut self, cell: CellId, cx: &mut Context<Self>) {
        let target = {
            let world = self.world.borrow();
            let room = WonderRoom::build(&world);
            // Pick the brightest cell that ISN'T the source (a real, live target).
            room.cells
                .iter()
                .filter(|c| c.cell != cell && c.balance >= 0)
                .max_by(|a, b| {
                    a.liveliness
                        .partial_cmp(&b.liveliness)
                        .unwrap_or(std::cmp::Ordering::Equal)
                })
                .map(|c| c.cell)
        };
        let Some(target) = target else {
            self.last_outcome =
                Some("Nothing to send to yet — this image has only one cell.".into());
            cx.notify();
            return;
        };
        let outcome = {
            let mut world = self.world.borrow_mut();
            let drag = crate::wonder::DragValue {
                source: cell,
                target,
                amount: 1,
            };
            drag.resolve(&mut world)
        };
        self.last_outcome = Some(match outcome {
            crate::wonder::DragOutcome::Moved(_) => {
                format!(
                    "Sent 1 to {} — the receipt is on its lineage.",
                    short(&target)
                )
            }
            crate::wonder::DragOutcome::Refused { reason } => {
                // Human words, not compiler (HIG principle 3) — the executor's reason
                // is shown verbatim only as the honest detail.
                format!("Refused — {reason}")
            }
        });
        cx.notify();
    }
}

/// A short hex tag for a cell id (the same short form `reflect` uses for cards).
fn short(id: &CellId) -> String {
    reflect::short_hex(id.as_bytes())
}

// ===========================================================================
// THE RENDER — three bands (status strip · mode surface · bottom tab bar).
// ===========================================================================

impl Render for TouchShell {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let (height, cell_count) = {
            let w = self.world.borrow();
            (w.height(), w.ledger().len())
        };

        // The slim STATUS STRIP — authority/vitals always in view, never anxious
        // (HIG principle 5). On the phone the desktop top-bar's identity + world-clock
        // fold to this one strip.
        let status = div()
            .flex()
            .flex_row()
            .items_center()
            .justify_between()
            .w_full()
            .px_4()
            .py_2()
            .bg(theme::panel())
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .flex()
                    .flex_row()
                    .items_center()
                    .gap_2()
                    .child(div().text_color(theme::accent()).child("deos"))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(SharedString::from(format!("{cell_count} cells"))),
                    ),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(SharedString::from(format!("turn {height}"))),
            );

        // The ONE focused MODE SURFACE (the body) — physics enforces one thing.
        let _ = window;
        let body = self.render_body(cx);

        // The thumb-reachable BOTTOM TAB BAR (the five modes).
        let tab_bar = self.render_tab_bar(cx);

        // The whole phone column: status · body (flex-grow, scrolls) · bottom bar,
        // with the optional face SHEET as a bottom-anchored overlay on top.
        div()
            .track_focus(&self.focus)
            .relative()
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            .child(status)
            .child(
                div()
                    .id("touch-body")
                    .flex_1()
                    .overflow_y_scroll()
                    .child(body),
            )
            .child(tab_bar)
            .children(self.sheet.map(|cell| self.render_sheet(cell, cx)))
    }
}

impl TouchShell {
    /// THE BOTTOM TAB BAR — the five modes, thumb-reachable at the bottom edge
    /// (`MOBILE-DEOS.md` §3). The real `gpui-component` [`TabBar`], so the touch
    /// shell uses the SAME widget material as the desktop (`HIG` principle 7), not a
    /// bespoke phone grid. A tab tap switches the body surface.
    fn render_tab_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let active = self.mode.index();
        let mut bar = TabBar::new("touch-modes")
            .selected_index(active)
            .on_click(cx.listener(|this, ix: &usize, _window, cx| {
                this.mode = Mode::from_index(*ix);
                this.sheet = None;
                cx.notify();
            }));
        for m in Mode::ALL {
            bar = bar.child(Tab::new().label(SharedString::from(format!(
                "{}  {}",
                m.glyph(),
                m.label()
            ))));
        }
        div()
            .w_full()
            .border_t_1()
            .border_color(theme::border())
            .bg(theme::panel())
            .py_1()
            .child(bar)
    }

    /// The body for the active mode (one focused surface — `HIG` principle 4).
    fn render_body(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        match self.mode {
            Mode::Inhabit => self.render_garden(cx),
            Mode::Author => self.render_list("Your authored cells", true, cx),
            Mode::Dev => self.render_list("The image's cells", false, cx),
            Mode::Inspect => self.render_inspect(cx),
            Mode::Operate => self.render_operate(cx),
        }
    }

    /// THE HOME GARDEN (INHABIT) — the AOL-wonder landing: every live cell a glowing
    /// pokeable CARD in a scrollable wall (`MOBILE-DEOS.md` §3 · [`WonderRoom`]). Tap
    /// a card to actuate / open its faces; the "⋯ faces" affordance is the long-press
    /// flip. The glow is REAL (the live dynamics stream), never decorative.
    fn render_garden(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let room = self.garden();
        let mut wall = div()
            .flex()
            .flex_col()
            .gap_3()
            .p_4()
            .child(
                div()
                    .text_lg()
                    .text_color(theme::text())
                    .child("Your world"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("Tap a card to open it · hold ⋯ for its faces"),
            );

        for g in &room.cells {
            wall = wall.child(self.card(g.cell, g.balance, g.cap_count, g.liveliness, cx));
        }
        wall.into_any_element()
    }

    /// ONE GLOWING CELL CARD — the touch target. A large, tappable card carrying the
    /// cell's identity, value + cap-web, a glow bar (the real liveliness), and a
    /// "⋯ faces" affordance (the long-press flip). `HIG`: the cell is the one noun,
    /// drawn the one coherent way; same shape whether doc / agent / room.
    fn card(
        &self,
        cell: CellId,
        balance: i64,
        cap_count: usize,
        liveliness: f32,
        cx: &mut Context<Self>,
    ) -> gpui::AnyElement {
        // The glow → a left accent bar whose brightness IS the liveliness.
        let glow = if liveliness > 0.66 {
            theme::good()
        } else if liveliness > 0.0 {
            theme::accent()
        } else {
            theme::border()
        };
        let value = if balance < 0 {
            format!("issuer well · backs {} supply", -balance)
        } else {
            format!("holds {balance}")
        };
        let web = match cap_count {
            0 => "reaches nothing yet".to_string(),
            1 => "reaches 1 cell".to_string(),
            n => format!("reaches {n} cells"),
        };

        let cell_for_tap = cell;
        let cell_for_press = cell;

        div()
            .id((
                "touch-card",
                cell.as_bytes()[0] as usize ^ (cell.as_bytes()[1] as usize) << 4,
            ))
            .flex()
            .flex_row()
            .items_center()
            .gap_3()
            .w_full()
            .min_h(px(72.0)) // a thumb-sized hit target (HIG principle 7 · large targets)
            .p_3()
            .rounded_lg()
            .bg(theme::panel())
            .border_1()
            .border_color(theme::border())
            // TAP = actuate / open (the primary affordance).
            .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
                this.on_cell_tap(cell_for_tap, cx);
            }))
            // The glow accent bar (real liveliness).
            .child(div().w(px(6.0)).h(px(44.0)).rounded_full().bg(glow))
            // The cell's identity + facts.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .flex_1()
                    .gap_1()
                    .child(
                        div()
                            .text_color(theme::text())
                            .child(SharedString::from(format!("cell {}", short(&cell)))),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(SharedString::from(format!("{value} · {web}"))),
                    ),
            )
            // The "⋯ faces" affordance — the long-press / flip-to-faces gesture made
            // an explicit thumb target (gpui has no native long-press).
            .child(
                Button::new(("touch-faces", cell.as_bytes()[2] as usize))
                    .ghost()
                    .small()
                    .label("⋯ faces")
                    .on_click(cx.listener(move |this, _ev, _window, cx| {
                        this.on_cell_press(cell_for_press, cx);
                    })),
            )
            .into_any_element()
    }

    /// A tappable LIST of cells (AUTHOR / DEV modes) — the touch form of the
    /// OBJECTS/inspector list. `authored_only` filters to cells carrying authored
    /// state (a non-zero balance or caps), the "your documents" cut.
    fn render_list(
        &self,
        title: &str,
        authored_only: bool,
        cx: &mut Context<Self>,
    ) -> gpui::AnyElement {
        let room = self.garden();
        let mut list = div().flex().flex_col().gap_2().p_4().child(
            div()
                .text_lg()
                .text_color(theme::text())
                .child(SharedString::from(title.to_string())),
        );

        for g in &room.cells {
            if authored_only && g.balance == 0 && g.cap_count == 0 {
                continue;
            }
            list = list.child(self.card(g.cell, g.balance, g.cap_count, g.liveliness, cx));
        }
        list.into_any_element()
    }

    /// THE INSPECT SURFACE — the focused cell projected through the uniform
    /// [`reflect`] object, its fields laid out for a thumb. A tap on a card in this
    /// mode re-focuses; the same generic reflection the desktop OBJECTS tab shows.
    fn render_inspect(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let world = self.world.borrow();
        let focus = self.inspect_focus.or_else(|| {
            let mut ids: Vec<CellId> = world.ledger().iter().map(|(id, _)| *id).collect();
            ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
            ids.first().copied()
        });
        let Some(focus) = focus else {
            return div()
                .p_4()
                .text_color(theme::muted())
                .child("No cells yet.")
                .into_any_element();
        };
        let Some(cell) = world.ledger().get(&focus) else {
            return div()
                .p_4()
                .text_color(theme::muted())
                .child("That cell is gone.")
                .into_any_element();
        };
        let obj = reflect::reflect_cell(&focus, cell);
        drop(world);

        let mut col = div()
            .flex()
            .flex_col()
            .gap_2()
            .p_4()
            .child(div().text_lg().text_color(theme::text()).child("Inspect"))
            .child(
                div()
                    .text_color(theme::accent())
                    .child(SharedString::from(format!("cell {}", short(&focus)))),
            );
        col = col.child(self.faces_of(&obj));
        // A footer hint: tap any card (in Dev/Inhabit) to re-focus the inspector.
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child("Tap a card in Dev or Inhabit to focus it here."),
        );
        let _ = cx;
        col.into_any_element()
    }

    /// THE OPERATE SURFACE — the image's vitals (the touch form of the operator
    /// dashboard): height, cell count, the brightest live cell (the current hotspot).
    fn render_operate(&self, _cx: &mut Context<Self>) -> gpui::AnyElement {
        let room = self.garden();
        let hot = room
            .brightest()
            .map(|g| format!("cell {} (the hotspot)", short(&g.cell)))
            .unwrap_or_else(|| "at rest".to_string());
        div()
            .flex()
            .flex_col()
            .gap_3()
            .p_4()
            .child(div().text_lg().text_color(theme::text()).child("Operate"))
            .child(self.vital("turns committed", room.height.to_string()))
            .child(self.vital("cells in the image", room.cells.len().to_string()))
            .child(self.vital("recent-activity window", room.window.to_string()))
            .child(self.vital("most alive", hot))
            .into_any_element()
    }

    /// One vital row (label · value) for the OPERATE dashboard.
    fn vital(&self, label: &str, value: String) -> impl IntoElement {
        div()
            .flex()
            .flex_row()
            .items_center()
            .justify_between()
            .w_full()
            .p_3()
            .rounded_lg()
            .bg(theme::panel())
            .border_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_color(theme::muted())
                    .child(SharedString::from(label.to_string())),
            )
            .child(
                div()
                    .text_color(theme::text())
                    .child(SharedString::from(value)),
            )
    }

    /// Lay out a reflected object's fields as a thumb-friendly card stack (the
    /// "faces" of a cell — its state, the uniform [`reflect`] presentation).
    fn faces_of(&self, obj: &Inspectable) -> impl IntoElement {
        let mut col = div().flex().flex_col().gap_2();
        for field in &obj.fields {
            let value = render_field_value(&field.value);
            col = col.child(
                div()
                    .flex()
                    .flex_row()
                    .items_center()
                    .justify_between()
                    .w_full()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(SharedString::from(field.key.clone())),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(SharedString::from(value)),
                    ),
            );
        }
        col
    }

    /// THE FACE SHEET — the long-press product (the flip-to-faces). A bottom-anchored
    /// sheet over a dimming scrim (`MOBILE-DEOS.md` §3: "sheets instead of popovers").
    /// It carries the cell's faces (state · the reflected fields) and the lit
    /// affordances (here the ACTUATE face — a real verified turn; ungranted ones would
    /// render dim, never hidden). Tapping the scrim closes it.
    fn render_sheet(&self, cell: CellId, cx: &mut Context<Self>) -> gpui::AnyElement {
        let world = self.world.borrow();
        let obj = world
            .ledger()
            .get(&cell)
            .map(|c| reflect::reflect_cell(&cell, c));
        drop(world);

        // The dimming scrim — a full-bleed tap target that closes the sheet.
        let scrim = div()
            .id("touch-sheet-scrim")
            .absolute()
            .inset_0()
            .bg(gpui::hsla(0.0, 0.0, 0.0, 0.55))
            .on_click(cx.listener(|this, _ev: &ClickEvent, _window, cx| {
                this.sheet = None;
                this.last_outcome = None;
                cx.notify();
            }));

        let mut panel = div()
            .id("touch-sheet-panel")
            .flex()
            .flex_col()
            .gap_3()
            .w_full()
            .max_h(px(440.0))
            .overflow_y_scroll()
            .p_4()
            .rounded_t_xl()
            .bg(theme::panel())
            .border_t_1()
            .border_color(theme::border())
            // The grabber + title row.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .w(px(40.0))
                            .h(px(4.0))
                            .rounded_full()
                            .bg(theme::border()),
                    )
                    .child(
                        div()
                            .text_lg()
                            .text_color(theme::text())
                            .child(SharedString::from(format!("cell {}", short(&cell)))),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("The seven faces — state, caps, links, history."),
                    ),
            );

        // The FACES (the reflected state) — the same uniform object the desktop shows.
        if let Some(obj) = &obj {
            panel = panel.child(self.faces_of(obj));
        }

        // The lit AFFORDANCES — the ACTUATE face (a real verified turn). Held caps lit;
        // an over-reach is refused in the prediction (surfaced below, never faked).
        let cell_for_act = cell;
        panel = panel.child(
            div()
                .flex()
                .flex_row()
                .gap_2()
                .child(
                    Button::new("touch-actuate")
                        .primary()
                        .label("⚡ actuate (send value)")
                        .on_click(cx.listener(move |this, _ev, _window, cx| {
                            this.actuate(cell_for_act, cx);
                        })),
                )
                .child(
                    Button::new("touch-inspect-face")
                        .ghost()
                        .label("◉ inspect")
                        .on_click(cx.listener(move |this, _ev, _window, cx| {
                            this.inspect_focus = Some(cell_for_act);
                            this.mode = Mode::Inspect;
                            this.sheet = None;
                            cx.notify();
                        })),
                ),
        );

        // The actuation banner — human words (HIG principle 3).
        if let Some(outcome) = &self.last_outcome {
            panel = panel.child(
                div()
                    .w_full()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .text_xs()
                    .text_color(theme::accent())
                    .child(SharedString::from(outcome.clone())),
            );
        }

        // The halo legend — the small command ring every cell carries, for teaching.
        let halos = Halo::ring()
            .iter()
            .map(|h| format!("{} {}", h.glyph(), h.label()))
            .collect::<Vec<_>>()
            .join("   ");
        panel = panel.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child(SharedString::from(format!("halo · {halos}"))),
        );

        // The sheet = scrim + bottom-anchored panel.
        div()
            .absolute()
            .inset_0()
            .flex()
            .flex_col()
            .justify_end()
            .child(scrim)
            .child(div().absolute().bottom_0().left_0().right_0().child(panel))
            .into_any_element()
    }
}

/// Render a reflected [`FieldValue`] as a compact string for a thumb card.
fn render_field_value(v: &FieldValue) -> String {
    match v {
        FieldValue::Text(s) => s.clone(),
        FieldValue::Balance(n) => {
            if *n < 0 {
                format!("−{} (issuer well)", -n)
            } else {
                n.to_string()
            }
        }
        FieldValue::Count(n) => n.to_string(),
        FieldValue::Bool(b) => if *b { "yes" } else { "no" }.to_string(),
        FieldValue::Id(bytes) => format!("→ {}", reflect::short_hex(bytes)),
        FieldValue::Hash(bytes) => reflect::short_hex(bytes),
        FieldValue::CapEdge { target, slot } => {
            format!("⇒ {} (slot {slot})", reflect::short_hex(target))
        }
        FieldValue::FieldSlot { index, hex } => format!("[{index}] {hex}"),
    }
}
