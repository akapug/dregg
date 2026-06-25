//! **THE deos DESKTOP** — a Windows-NT / Pharo-Smalltalk workbench over the live
//! verified World.
//!
//! This is the answer to the cockpit's three holes: NO WAY TO ACTUATE OR COMPOSE
//! the parts, ZERO METAPHORS, ZERO SPATIAL PERSISTENCE. The desktop gives the user
//! the oldest, densest, most legible metaphors there are — a **desktop of icons**,
//! **overlapping windows**, **right-click context menus**, a **menu bar**, and a
//! reflexive **inspector** — and wires every one of them to REAL substance:
//!
//!   * **Icons ARE cells.** Each icon on the desktop is one sovereign cell read off
//!     the live `World` ledger ([`crate::world::World`]): its id, its kind, its
//!     balance/nonce/lifecycle. Drag it and it MOVES; its position is SAVED.
//!   * **Spatial persistence** (the #1 missing thing). The desktop layout — every
//!     icon position, every open window's geometry — is real state, serialized to a
//!     sidecar ([`DesktopLayout`]) and RESTORED on reopen. You arrange your world
//!     and it STAYS.
//!   * **Windows.** Double-click an icon → it opens in a movable NT window (title
//!     bar, min/max/close, a dense inspector body). Windows overlap; their geometry
//!     persists too.
//!   * **Right-click context menus** — the ACTUATION. Right-click any cell-icon → a
//!     menu of EVERY action available on it (inspect, fire its affordances as
//!     verified turns, grant a cap, transfer), lit if the cap is held, dim if not.
//!     This is Smalltalk "do it": the user actually DOES things to the parts.
//!   * **Compose** — drag one cell-icon ONTO another to act across them (transfer /
//!     grant), the dropped affordance.
//!
//! REAL UNDERNEATH: a fired action commits a real `dregg_turn` through the embedded
//! verified executor ([`crate::world::World::commit_turn`]) leaving a `TurnReceipt`;
//! the inspector shows the cell's real reflected faces; the layout persists as real
//! JSON state. Built NEW, beside the cockpit — it does not touch the cockpit tree.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use gpui::prelude::FluentBuilder;
use gpui::{
    AnyElement, ClickEvent, Context, Div, FontWeight, InteractiveElement, IntoElement, MouseButton,
    MouseDownEvent, MouseMoveEvent, MouseUpEvent, ParentElement, Pixels, Point, Render, Stateful,
    StatefulInteractiveElement, Styled, Window, div, px,
};

use dregg_cell::lifecycle::CellLifecycle;
use dregg_types::CellId;

use crate::world::{World, grant_capability, transfer};

/// The full hex id of a cell (a stable layout/persistence key, and the inspector's
/// identity row). [`CellId`] carries the raw bytes; this is the canonical render.
pub fn id_hex(cell: &CellId) -> String {
    cell.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

/// A short legible id (first 4 bytes) — the icon caption / window-title id.
fn id_short(cell: &CellId) -> String {
    cell.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// `Pixels` → `f32` (the field is private; the `From` impl is the supported route).
fn pxf(p: Pixels) -> f32 {
    f32::from(p)
}

// ── The NT palette ──────────────────────────────────────────────────────────────
// Deliberately sterile / technical: a 3D-beveled gray chrome over a teal void, the
// way an NT workstation reads. Dense, not calm; detailed, not minimal.
const NT_DESKTOP_BG: u32 = 0x0a3a4a; // the classic teal void
const NT_FACE: u32 = 0xc0c0c0; // button-face gray
const NT_FACE_DARK: u32 = 0x9a9a9a;
const NT_HILIGHT: u32 = 0xffffff; // top-left bevel
const NT_SHADOW: u32 = 0x404040; // bottom-right bevel
const NT_TEXT: u32 = 0x101010;
const NT_TITLE_ACTIVE: u32 = 0x000080; // navy active title bar
const NT_TITLE_TEXT: u32 = 0xffffff;
const NT_ICON_LABEL: u32 = 0xf0f0f0;
const NT_SELECT: u32 = 0x000080;
const NT_MENU_HILIGHT: u32 = 0x000080;
const NT_DIM: u32 = 0x707070; // a disabled / unheld affordance

const ICON_W: f32 = 92.0;
const ICON_H: f32 = 76.0;
const WIN_MIN_W: f32 = 280.0;
const WIN_MIN_H: f32 = 180.0;
const MENUBAR_H: f32 = 26.0;

// ── Persisted layout (the SPATIAL PERSISTENCE — real saved state) ─────────────────

/// A persisted desktop position for one cell-icon (`(x, y)` on the desktop) — keyed
/// by the cell's hex id so it survives across worlds with the same cells.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct IconPos {
    pub cell: String,
    pub x: f32,
    pub y: f32,
}

/// A persisted open-window geometry for one cell (id + frame). Persisting this is
/// what makes "you arrange your world and it STAYS" true for windows too.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct WinGeom {
    pub cell: String,
    pub x: f32,
    pub y: f32,
    pub w: f32,
    pub h: f32,
    pub minimized: bool,
}

/// **THE DESKTOP LAYOUT — the load-bearing spatial-persistence state.** The whole
/// arrangement of the user's world: every icon position and every open window's
/// geometry. Serialized to a sidecar JSON file ([`DesktopLayout::path`]) on every
/// drag/move/resize and reloaded on open, so the spatial arrangement is durable
/// state, not ephemeral view-state.
#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct DesktopLayout {
    pub icons: Vec<IconPos>,
    pub windows: Vec<WinGeom>,
}

impl DesktopLayout {
    /// The default sidecar path (under the user's data dir, falling back to a temp
    /// path). The desktop saves here on every spatial change and loads here on open.
    pub fn default_path() -> PathBuf {
        if let Some(dir) = dirs_next_data() {
            dir.join("deos-desktop-layout.json")
        } else {
            std::env::temp_dir().join("deos-desktop-layout.json")
        }
    }

    /// Load a persisted layout from `path`, or an empty layout if none exists / it
    /// is corrupt (a fresh desktop falls back to the auto-arranged grid).
    pub fn load(path: &PathBuf) -> Self {
        std::fs::read(path)
            .ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
            .unwrap_or_default()
    }

    /// **Persist the layout** to `path` (atomic-ish: write then rename). Called on
    /// every drag-end / window move / resize — this is the act that makes the
    /// arrangement durable. Errors are swallowed (a read-only FS still gives a live
    /// desktop; only persistence is lost).
    pub fn save(&self, path: &PathBuf) {
        if let Ok(json) = serde_json::to_vec_pretty(self) {
            let tmp = path.with_extension("json.tmp");
            if std::fs::write(&tmp, &json).is_ok() {
                let _ = std::fs::rename(&tmp, path);
            }
        }
    }

    fn icon_pos(&self, cell: &str) -> Option<Point<Pixels>> {
        self.icons
            .iter()
            .find(|p| p.cell == cell)
            .map(|p| Point::new(px(p.x), px(p.y)))
    }

    fn set_icon_pos(&mut self, cell: &str, x: f32, y: f32) {
        if let Some(p) = self.icons.iter_mut().find(|p| p.cell == cell) {
            p.x = x;
            p.y = y;
        } else {
            self.icons.push(IconPos {
                cell: cell.to_string(),
                x,
                y,
            });
        }
    }

    fn win_geom(&self, cell: &str) -> Option<WinGeom> {
        self.windows.iter().find(|w| w.cell == cell).cloned()
    }

    fn set_win_geom(&mut self, g: WinGeom) {
        if let Some(w) = self.windows.iter_mut().find(|w| w.cell == g.cell) {
            *w = g;
        } else {
            self.windows.push(g);
        }
    }

    fn drop_win(&mut self, cell: &str) {
        self.windows.retain(|w| w.cell != cell);
    }
}

/// A platform-appropriate data dir (no extra dep): `$XDG_DATA_HOME` /
/// `~/Library/Application Support` / `~/.local/share`.
fn dirs_next_data() -> Option<PathBuf> {
    if let Ok(x) = std::env::var("XDG_DATA_HOME") {
        if !x.is_empty() {
            return Some(PathBuf::from(x).join("deos"));
        }
    }
    let home = std::env::var("HOME").ok()?;
    #[cfg(target_os = "macos")]
    {
        Some(PathBuf::from(home).join("Library/Application Support/deos"))
    }
    #[cfg(not(target_os = "macos"))]
    {
        Some(PathBuf::from(home).join(".local/share/deos"))
    }
}

// ── A live, open inspector window over one cell ───────────────────────────────────

/// The faces an inspector window shows of a cell (read fresh off the live ledger
/// each render — a fired affordance updates them in place).
struct WindowState {
    /// The cell this window inspects (also the `HashMap` key; kept inline so a
    /// `WindowState` is self-describing when iterated).
    #[allow(dead_code)]
    cell: CellId,
    title: String,
    x: f32,
    y: f32,
    w: f32,
    h: f32,
    minimized: bool,
    z: u32,
}

// ── The actuation surface: every action available on a cell ───────────────────────

/// One entry of a cell's right-click context menu — an action the user can "do it"
/// on. `held` reflects whether the user holds the cap for it (lit vs. dim).
struct MenuAction {
    label: String,
    held: bool,
    kind: ActionKind,
}

#[derive(Clone)]
enum ActionKind {
    /// Open the inspector window on the cell.
    Inspect,
    /// Fire a real verified turn: transfer `amount` from this cell to the
    /// desktop's "user" anchor (a self-contained demo of actuation).
    Transfer { amount: u64 },
    /// Grant a capability reaching `target` to this cell at the next free slot
    /// (the ocap "grant" verb) — a real `GrantCapability` turn.
    Grant { target: CellId },
    /// Bump the cell's nonce via a real `IncrementNonce` turn (the simplest
    /// always-available affordance — proves the actuation path lands a receipt).
    BumpNonce,
}

// ── A floating context menu (rendered as an NT popup overlay) ─────────────────────

struct OpenMenu {
    cell: CellId,
    at: Point<Pixels>,
    actions: Vec<MenuAction>,
}

// ── A live drag in flight (an icon being moved, or a window being moved/resized) ───

enum Drag {
    Icon {
        cell: CellId,
        // The grab offset from the icon's top-left to the mouse.
        grab: Point<Pixels>,
    },
    WinMove {
        cell: CellId,
        grab: Point<Pixels>,
    },
    WinResize {
        cell: CellId,
        // The window's top-left at grab; we resize the bottom-right corner.
        origin: Point<Pixels>,
    },
}

/// **THE deos DESKTOP** — the root `Render` view. Owns the live `World`, the icon
/// layout, the open inspector windows, the in-flight drag, the open context menu,
/// and the persisted [`DesktopLayout`]. Every spatial gesture mutates the layout and
/// re-saves it; every actuation commits a real verified turn on the World.
pub struct DeosDesktop {
    world: Rc<RefCell<World>>,
    /// The cells to show as icons (the live ledger's cells, ordered stably by id).
    cells: Vec<CellId>,
    /// The "user" anchor — the default transfer/grant counterparty for the demo
    /// actuation verbs (so a context-menu action is fully self-contained).
    user: CellId,
    layout: DesktopLayout,
    layout_path: PathBuf,
    windows: HashMap<CellId, WindowState>,
    open_menu: Option<OpenMenu>,
    drag: Option<Drag>,
    next_z: u32,
    /// A short log of the last actuations (receipt height / outcome) shown in the
    /// status bar — the user sees their "do it" landed a real verified turn.
    status: String,
}

impl DeosDesktop {
    /// Open the desktop over a live `World`, restoring the persisted layout. `user`
    /// is the default counterparty for the demo transfer/grant verbs.
    pub fn new(
        world: Rc<RefCell<World>>,
        user: CellId,
        layout_path: PathBuf,
        _window: &mut Window,
        _cx: &mut Context<Self>,
    ) -> Self {
        let cells: Vec<CellId> = {
            let w = world.borrow();
            let mut v: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
            v.sort();
            v
        };
        let layout = DesktopLayout::load(&layout_path);

        let mut desk = DeosDesktop {
            world,
            cells,
            user,
            layout,
            layout_path,
            windows: HashMap::new(),
            open_menu: None,
            drag: None,
            next_z: 1,
            status: "deos desktop — right-click a cell to actuate · double-click to inspect · \
                     drag to arrange (persisted)"
                .to_string(),
        };
        // Re-open any windows the persisted layout remembers (spatial persistence
        // for windows, not just icons).
        let geoms: Vec<WinGeom> = desk.layout.windows.clone();
        for g in geoms {
            if let Some(cell) = desk.cells.iter().find(|c| id_hex(&c) == g.cell).copied() {
                desk.open_window_at(cell, g.x, g.y, g.w, g.h, g.minimized);
            }
        }
        desk
    }

    /// The auto-arranged default grid position for a cell with no persisted slot —
    /// a left-edge column of icons (so a fresh desktop is legible before any drag).
    fn default_icon_pos(&self, idx: usize) -> Point<Pixels> {
        let col = (idx / 6) as f32;
        let row = (idx % 6) as f32;
        Point::new(
            px(24.0 + col * (ICON_W + 16.0)),
            px(MENUBAR_H + 18.0 + row * (ICON_H + 14.0)),
        )
    }

    fn icon_pos(&self, idx: usize, cell: &CellId) -> Point<Pixels> {
        self.layout
            .icon_pos(&id_hex(&cell))
            .unwrap_or_else(|| self.default_icon_pos(idx))
    }

    fn open_window_at(&mut self, cell: CellId, x: f32, y: f32, w: f32, h: f32, minimized: bool) {
        let z = self.next_z;
        self.next_z += 1;
        let title = format!("Cell {} — Inspector", id_short(&cell));
        self.windows.insert(
            cell,
            WindowState {
                cell,
                title,
                x,
                y,
                w: w.max(WIN_MIN_W),
                h: h.max(WIN_MIN_H),
                minimized,
                z,
            },
        );
    }

    /// Open (or focus) an inspector window on `cell`, restoring its persisted
    /// geometry if any, else a cascade default.
    fn open_window(&mut self, cell: CellId) {
        if let Some(ws) = self.windows.get_mut(&cell) {
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
            return;
        }
        if let Some(g) = self.layout.win_geom(&id_hex(&cell)) {
            self.open_window_at(cell, g.x, g.y, g.w, g.h, false);
        } else {
            let n = self.windows.len() as f32;
            self.open_window_at(cell, 300.0 + n * 28.0, 80.0 + n * 28.0, 360.0, 280.0, false);
        }
        self.persist_window(cell);
    }

    fn close_window(&mut self, cell: CellId) {
        self.windows.remove(&cell);
        self.layout.drop_win(&id_hex(&cell));
        self.layout.save(&self.layout_path);
    }

    fn persist_window(&mut self, cell: CellId) {
        if let Some(ws) = self.windows.get(&cell) {
            self.layout.set_win_geom(WinGeom {
                cell: id_hex(&cell),
                x: ws.x,
                y: ws.y,
                w: ws.w,
                h: ws.h,
                minimized: ws.minimized,
            });
            self.layout.save(&self.layout_path);
        }
    }

    /// Whether the user holds the authority to act on a cell. The embedded World is
    /// single-custody (the operator is the authority), so every action is HELD here;
    /// a federated/cap-bounded desktop would dim the ones the held cap can't reach.
    /// We mark the issuer well (negative balance) as "system" (dim) to show the
    /// lit/dim distinction the metaphor needs.
    fn holds(&self, cell: &CellId) -> bool {
        self.cell_balance(cell) >= 0
    }

    fn cell_balance(&self, cell: &CellId) -> i64 {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    }

    fn cell_nonce(&self, cell: &CellId) -> u64 {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    fn cell_lifecycle(&self, cell: &CellId) -> String {
        match self
            .world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.lifecycle.clone())
        {
            Some(CellLifecycle::Live) => "Live".into(),
            Some(CellLifecycle::Sealed { .. }) => "Sealed".into(),
            Some(CellLifecycle::Migrated { .. }) => "Migrated".into(),
            Some(CellLifecycle::Destroyed { .. }) => "Destroyed".into(),
            Some(CellLifecycle::Archived { .. }) => "Archived".into(),
            None => "—".into(),
        }
    }

    fn cell_cap_count(&self, cell: &CellId) -> usize {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.capabilities.iter().count())
            .unwrap_or(0)
    }

    /// A short kind label for a cell, derived from its balance — the icon's caption.
    fn cell_kind(&self, cell: &CellId) -> &'static str {
        let b = self.cell_balance(cell);
        if b < 0 {
            "issuer well"
        } else if b > 500_000 {
            "treasury"
        } else if b == 0 {
            "service"
        } else {
            "account"
        }
    }

    /// **The actuation surface for `cell`** — every action the right-click menu
    /// offers. The transfer/grant verbs target the `user` anchor (a self-contained
    /// demo of cross-cell actuation); `BumpNonce` is the always-available one.
    fn actions_for(&self, cell: CellId) -> Vec<MenuAction> {
        let held = self.holds(&cell);
        let mut v = vec![MenuAction {
            label: "Inspect…".into(),
            held: true,
            kind: ActionKind::Inspect,
        }];
        // Bump nonce — the simplest verified turn, always available, lands a receipt.
        v.push(MenuAction {
            label: "Bump nonce  (verified turn)".into(),
            held,
            kind: ActionKind::BumpNonce,
        });
        // Transfer to the user anchor (only meaningful if the cell has balance).
        if cell != self.user {
            v.push(MenuAction {
                label: format!("Transfer 1,000 → {}", id_short(&self.user)),
                held: held && self.cell_balance(&cell) >= 1_000,
                kind: ActionKind::Transfer { amount: 1_000 },
            });
        }
        // Grant a cap reaching the user anchor (the ocap "grant" verb).
        v.push(MenuAction {
            label: format!("Grant cap → {}", id_short(&self.user)),
            held,
            kind: ActionKind::Grant { target: self.user },
        });
        v
    }

    /// **DO IT** — fire a real verified turn for a context-menu action, commit it on
    /// the live World, and record the outcome in the status bar. This is the ACTUATION:
    /// the user's right-click "do it" lands a real `TurnReceipt` on the cell's chain.
    fn actuate(&mut self, cell: CellId, kind: &ActionKind) {
        match kind {
            ActionKind::Inspect => {
                self.open_window(cell);
                self.status = format!(
                    "Inspecting {} ({}).",
                    id_short(&cell),
                    self.cell_kind(&cell)
                );
            }
            ActionKind::BumpNonce => {
                let turn = {
                    let w = self.world.borrow();
                    w.turn(
                        cell,
                        vec![dregg_turn::action::Effect::IncrementNonce { cell }],
                    )
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "Bump nonce on {} → {} (height {}).",
                    id_short(&cell),
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
            ActionKind::Transfer { amount } => {
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![transfer(cell, self.user, *amount)])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "Transfer {} {} → {} → {} (height {}).",
                    amount,
                    id_short(&cell),
                    id_short(&self.user),
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
            ActionKind::Grant { target } => {
                let slot = self.cell_cap_count(&cell) as u32 + 1;
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![grant_capability(cell, cell, *target, slot)])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "Grant cap {} → {} @{} → {} (height {}).",
                    id_short(&cell),
                    id_short(&target),
                    slot,
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
        }
    }

    /// **COMPOSE** — drop cell `src` ONTO cell `dst`: act across them with the
    /// dropped affordance. A transfer when `src` has balance, else a cap grant. This
    /// is the spatial compose gesture (drag one icon onto another).
    fn compose_drop(&mut self, src: CellId, dst: CellId) {
        if src == dst {
            return;
        }
        let bal = self.cell_balance(&src);
        if bal >= 1_000 {
            let turn = {
                let w = self.world.borrow();
                w.turn(src, vec![transfer(src, dst, 1_000)])
            };
            let outcome = self.world.borrow_mut().commit_turn(turn);
            self.status = format!(
                "COMPOSE: dropped {} → {}: transfer 1,000 {} (height {}).",
                id_short(&src),
                id_short(&dst),
                if outcome.is_committed() {
                    "committed"
                } else {
                    "rejected"
                },
                self.world.borrow().height()
            );
        } else {
            let slot = self.cell_cap_count(&src) as u32 + 1;
            let turn = {
                let w = self.world.borrow();
                w.turn(src, vec![grant_capability(src, src, dst, slot)])
            };
            let outcome = self.world.borrow_mut().commit_turn(turn);
            self.status = format!(
                "COMPOSE: dropped {} → {}: grant cap @{} {} (height {}).",
                id_short(&src),
                id_short(&dst),
                slot,
                if outcome.is_committed() {
                    "committed"
                } else {
                    "rejected"
                },
                self.world.borrow().height()
            );
        }
    }

    // ── Global mouse handling for the in-flight drag ─────────────────────────────

    fn on_mouse_move(&mut self, ev: &MouseMoveEvent, cx: &mut Context<Self>) {
        let Some(drag) = &self.drag else { return };
        match drag {
            Drag::Icon { cell, grab } => {
                let cell = *cell;
                let nx = pxf(ev.position.x - grab.x).max(0.0);
                let ny = pxf(ev.position.y - grab.y).max(MENUBAR_H);
                self.layout.set_icon_pos(&id_hex(&cell), nx, ny);
                cx.notify();
            }
            Drag::WinMove { cell, grab } => {
                let cell = *cell;
                let nx = pxf(ev.position.x - grab.x);
                let ny = pxf(ev.position.y - grab.y).max(MENUBAR_H);
                if let Some(ws) = self.windows.get_mut(&cell) {
                    ws.x = nx;
                    ws.y = ny;
                }
                cx.notify();
            }
            Drag::WinResize { cell, origin } => {
                let cell = *cell;
                let nw = pxf(ev.position.x - origin.x).max(WIN_MIN_W);
                let nh = pxf(ev.position.y - origin.y).max(WIN_MIN_H);
                if let Some(ws) = self.windows.get_mut(&cell) {
                    ws.w = nw;
                    ws.h = nh;
                }
                cx.notify();
            }
        }
    }

    fn on_mouse_up(&mut self, ev: &MouseUpEvent, cx: &mut Context<Self>) {
        let Some(drag) = self.drag.take() else { return };
        match drag {
            Drag::Icon { cell, .. } => {
                // Persist the new icon position (the spatial-persistence write).
                self.layout.save(&self.layout_path);
                // COMPOSE: if released over ANOTHER cell-icon, act across them.
                if let Some(dst) = self.icon_under(ev.position, Some(cell)) {
                    self.compose_drop(cell, dst);
                }
            }
            Drag::WinMove { cell, .. } | Drag::WinResize { cell, .. } => {
                self.persist_window(cell);
            }
        }
        cx.notify();
    }

    /// Which cell-icon (other than `exclude`) sits under `p` — used by the compose
    /// drop to find the drop target.
    fn icon_under(&self, p: Point<Pixels>, exclude: Option<CellId>) -> Option<CellId> {
        for (idx, cell) in self.cells.iter().enumerate() {
            if Some(*cell) == exclude {
                continue;
            }
            let pos = self.icon_pos(idx, cell);
            let within_x = p.x >= pos.x && p.x <= pos.x + px(ICON_W);
            let within_y = p.y >= pos.y && p.y <= pos.y + px(ICON_H);
            if within_x && within_y {
                return Some(*cell);
            }
        }
        None
    }

    // ── Bake / test hooks (drive the live gestures headlessly) ───────────────────
    // These mirror exactly what the interactive mouse handlers do, so a headless
    // bake (or a test) can open windows, fire an actuation, and persist a drag —
    // and assert the real verified turn landed and the layout saved.

    /// Open an inspector window on `cell` (what a double-click does).
    pub fn bake_open_window(&mut self, cell: CellId) {
        self.open_window(cell);
    }

    /// Fire a transfer actuation `src → dst` of `amount` (what the right-click
    /// "Transfer" menu action does) — a REAL verified turn on the live World.
    pub fn bake_actuate_transfer(&mut self, src: CellId, _dst: CellId, amount: u64) {
        self.actuate(src, &ActionKind::Transfer { amount });
    }

    /// Move `cell`'s icon to `(x, y)` and persist the layout (what a drag-end does).
    pub fn bake_drag_icon(&mut self, cell: CellId, x: f32, y: f32) {
        self.layout.set_icon_pos(&id_hex(&cell), x, y);
        self.layout.save(&self.layout_path);
    }

    /// Open the right-click context menu on `cell` at `(x, y)` (the ACTUATION
    /// surface) so it is visible in a bake.
    pub fn bake_open_menu(&mut self, cell: CellId, x: f32, y: f32) {
        self.open_menu = Some(OpenMenu {
            cell,
            at: Point::new(px(x), px(y)),
            actions: self.actions_for(cell),
        });
    }
}

// ── Rendering ─────────────────────────────────────────────────────────────────────

/// An NT 3D bevel (raised) — a light face with a 2px top-left highlight border (the
/// raised-button look). Generic over any [`Styled`] element so it composes onto a
/// plain `div()` or an `.id()`'d `Stateful<Div>`.
fn bevel_raised<E: Styled>(d: E) -> E {
    d.border_t_2()
        .border_l_2()
        .border_color(gpui::rgb(NT_HILIGHT))
        .bg(gpui::rgb(NT_FACE))
}

impl Render for DeosDesktop {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let mut root = div()
            .id("deos-desktop-root")
            .size_full()
            .bg(gpui::rgb(NT_DESKTOP_BG))
            .text_color(gpui::rgb(NT_TEXT))
            .font_family("Lilex")
            .text_size(px(12.0))
            // Global drag handling (move/up anywhere on the desktop drive the
            // in-flight icon/window drag).
            .on_mouse_move(
                cx.listener(|this, ev: &MouseMoveEvent, _w, cx| this.on_mouse_move(ev, cx)),
            )
            .on_mouse_up(
                MouseButton::Left,
                cx.listener(|this, ev: &MouseUpEvent, _w, cx| this.on_mouse_up(ev, cx)),
            )
            // A left-click on the bare desktop dismisses an open context menu.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                    if this.open_menu.take().is_some() {
                        cx.notify();
                    }
                }),
            );

        // ── The menu bar (NT-style) ──────────────────────────────────────────────
        root = root.child(self.render_menubar(cx));

        // ── The desktop icons (cells) ────────────────────────────────────────────
        let cells = self.cells.clone();
        for (idx, cell) in cells.iter().enumerate() {
            root = root.child(self.render_icon(idx, *cell, cx));
        }

        // ── The open windows (z-ordered) ─────────────────────────────────────────
        let mut wins: Vec<CellId> = self.windows.keys().copied().collect();
        wins.sort_by_key(|c| self.windows[c].z);
        for cell in wins {
            root = root.child(self.render_window(cell, cx));
        }

        // ── The context menu overlay (the ACTUATION) ─────────────────────────────
        if self.open_menu.is_some() {
            root = root.child(self.render_context_menu(cx));
        }

        // ── The status bar (the receipt of the last actuation) ───────────────────
        root = root.child(self.render_statusbar());

        root
    }
}

impl DeosDesktop {
    fn render_menubar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let menus = ["World", "Cell", "View", "Window", "Help"];
        let mut bar = div()
            .absolute()
            .left(px(0.0))
            .top(px(0.0))
            .w_full()
            .h(px(MENUBAR_H))
            .flex()
            .flex_row()
            .items_center()
            .bg(gpui::rgb(NT_FACE))
            .border_b_1()
            .border_color(gpui::rgb(NT_SHADOW));
        // The deos mark on the far left (the "Start"-equivalent system menu).
        bar = bar.child(
            div()
                .px_2()
                .h_full()
                .flex()
                .items_center()
                .bg(gpui::rgb(NT_FACE_DARK))
                .child(div().font_weight(FontWeight::BOLD).child("◆ deos")),
        );
        for name in menus {
            bar = bar.child(
                div()
                    .id(gpui::SharedString::from(format!("menu-{name}")))
                    .px_3()
                    .h_full()
                    .flex()
                    .items_center()
                    .hover(|s| {
                        s.bg(gpui::rgb(NT_MENU_HILIGHT))
                            .text_color(gpui::rgb(NT_TITLE_TEXT))
                    })
                    .child(name.to_string()),
            );
        }
        // A live height/cell-count readout on the far right (the World face).
        let h = self.world.borrow().height();
        let n = self.cells.len();
        bar = bar.child(
            div()
                .ml_auto()
                .px_3()
                .h_full()
                .flex()
                .items_center()
                .text_color(gpui::rgb(NT_DIM))
                .child(format!("World · {n} cells · height {h}")),
        );
        let _ = cx;
        bar
    }

    fn render_icon(&self, idx: usize, cell: CellId, cx: &mut Context<Self>) -> impl IntoElement {
        let pos = self.icon_pos(idx, &cell);
        let kind = self.cell_kind(&cell);
        let bal = self.cell_balance(&cell);
        let held = self.holds(&cell);
        let glyph = match kind {
            "treasury" => "▣",
            "issuer well" => "◈",
            "service" => "⚙",
            _ => "▤",
        };
        let label = format!("{}\n{}\n{}", kind, id_short(&cell), fmt_balance(bal));

        div()
            .id(gpui::SharedString::from(format!("icon-{}", id_hex(&cell))))
            .absolute()
            .left(pos.x)
            .top(pos.y)
            .w(px(ICON_W))
            .h(px(ICON_H))
            .flex()
            .flex_col()
            .items_center()
            .justify_start()
            .pt_1()
            // Drag to move; the mouse-down records the grab offset and starts a drag.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = None;
                    let idx = this.cells.iter().position(|c| *c == cell).unwrap_or(0);
                    let p = this.icon_pos(idx, &cell);
                    this.drag = Some(Drag::Icon {
                        cell,
                        grab: Point::new(ev.position.x - p.x, ev.position.y - p.y),
                    });
                    cx.notify();
                }),
            )
            // Double-click opens the inspector window.
            .on_click(cx.listener(move |this, ev: &ClickEvent, _w, cx| {
                if ev.click_count() >= 2 {
                    this.open_window(cell);
                    cx.notify();
                }
            }))
            // Right-click opens the context menu (the ACTUATION surface).
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell,
                        at: ev.position,
                        actions: this.actions_for(cell),
                    });
                    cx.notify();
                }),
            )
            .child(
                // The 32x32 glyph tile (a raised NT bevel face).
                bevel_raised(div())
                    .w(px(40.0))
                    .h(px(40.0))
                    .flex()
                    .items_center()
                    .justify_center()
                    .text_size(px(22.0))
                    .when(!held, |d| d.opacity(0.55))
                    .child(glyph),
            )
            .child(
                div()
                    .mt_1()
                    .px_1()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_ICON_LABEL))
                    .text_center()
                    .child(label),
            )
    }

    fn render_window(&self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        let (x, y, w, h, title, minimized) = {
            let ws = &self.windows[&cell];
            (ws.x, ws.y, ws.w, ws.h, ws.title.clone(), ws.minimized)
        };

        if minimized {
            // A minimized window collapses to a title-bar stub at its origin.
            return div()
                .id(gpui::SharedString::from(format!(
                    "winmin-{}",
                    id_hex(&cell)
                )))
                .absolute()
                .left(px(x))
                .top(px(y))
                .w(px(180.0))
                .child(self.render_titlebar(cell, &title, true, cx))
                .into_any_element();
        }

        // The cell's faces (read fresh off the live ledger).
        let bal = self.cell_balance(&cell);
        let nonce = self.cell_nonce(&cell);
        let lifecycle = self.cell_lifecycle(&cell);
        let caps = self.cell_cap_count(&cell);
        let kind = self.cell_kind(&cell);

        let body = div()
            .id(gpui::SharedString::from(format!(
                "winbody-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0xf4f4f4))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Identity"))
            .child(face_row("id", &id_hex(&cell)))
            .child(face_row("kind", kind))
            .child(face_section("State (live)"))
            .child(face_row("balance", &fmt_balance(bal)))
            .child(face_row("nonce", &nonce.to_string()))
            .child(face_row("lifecycle", &lifecycle))
            .child(face_row("capabilities", &caps.to_string()))
            .child(face_section("Affordances (do it)"))
            .child(self.affordance_button(cell, "Bump nonce", ActionKind::BumpNonce, cx))
            .child(self.affordance_button(
                cell,
                &format!("Transfer 1,000 → {}", id_short(&self.user)),
                ActionKind::Transfer { amount: 1_000 },
                cx,
            ))
            .child(self.affordance_button(
                cell,
                &format!("Grant cap → {}", id_short(&self.user)),
                ActionKind::Grant { target: self.user },
                cx,
            ));

        let resize_grip = div()
            .id(gpui::SharedString::from(format!(
                "resize-{}",
                id_hex(&cell)
            )))
            .absolute()
            .right(px(0.0))
            .bottom(px(0.0))
            .w(px(14.0))
            .h(px(14.0))
            .bg(gpui::rgb(NT_FACE_DARK))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get(&cell) {
                        this.drag = Some(Drag::WinResize {
                            cell,
                            origin: Point::new(px(ws.x), px(ws.y)),
                        });
                    }
                    cx.notify();
                }),
            )
            .child("◢");

        div()
            .id(gpui::SharedString::from(format!("win-{}", id_hex(&cell))))
            .absolute()
            .left(px(x))
            .top(px(y))
            .w(px(w))
            .h(px(h))
            .flex()
            .flex_col()
            .bg(gpui::rgb(NT_FACE))
            .border_2()
            .border_color(gpui::rgb(NT_SHADOW))
            // Clicking anywhere in the window raises it.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get_mut(&cell) {
                        ws.z = this.next_z;
                        this.next_z += 1;
                    }
                    cx.notify();
                }),
            )
            .child(self.render_titlebar(cell, &title, false, cx))
            .child(body)
            .child(resize_grip)
            .into_any_element()
    }

    fn render_titlebar(
        &self,
        cell: CellId,
        title: &str,
        minimized: bool,
        cx: &mut Context<Self>,
    ) -> Stateful<Div> {
        // NT navy title bar with min/max/close glyph buttons. The bar grabs a
        // window-move drag on mouse-down; the buttons fire close/minimize.
        div()
            .id(gpui::SharedString::from(format!("title-{}", id_hex(&cell))))
            .h(px(22.0))
            .flex()
            .flex_row()
            .items_center()
            .bg(gpui::rgb(NT_TITLE_ACTIVE))
            .text_color(gpui::rgb(NT_TITLE_TEXT))
            .px_1()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get(&cell) {
                        this.drag = Some(Drag::WinMove {
                            cell,
                            grab: Point::new(ev.position.x - px(ws.x), ev.position.y - px(ws.y)),
                        });
                    }
                    cx.notify();
                }),
            )
            .child(div().px_1().child("▣"))
            .child(
                div()
                    .flex_1()
                    .px_1()
                    .text_size(px(11.0))
                    .font_weight(FontWeight::BOLD)
                    .child(title.to_string()),
            )
            .child(self.title_btn(cell, "_", TitleBtn::Minimize, cx))
            .child(self.title_btn(
                cell,
                if minimized { "▢" } else { "❐" },
                TitleBtn::Maximize,
                cx,
            ))
            .child(self.title_btn(cell, "✕", TitleBtn::Close, cx))
    }

    fn title_btn(
        &self,
        cell: CellId,
        glyph: &str,
        which: TitleBtn,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let glyph = glyph.to_string();
        div()
            .id(gpui::SharedString::from(format!(
                "titlebtn-{}-{glyph}",
                id_hex(&cell)
            )))
            .ml_1()
            .w(px(16.0))
            .h(px(14.0))
            .flex()
            .items_center()
            .justify_center()
            .bg(gpui::rgb(NT_FACE))
            .text_color(gpui::rgb(NT_TEXT))
            .text_size(px(9.0))
            .border_1()
            .border_color(gpui::rgb(NT_SHADOW))
            .hover(|s| s.bg(gpui::rgb(NT_FACE_DARK)))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    // Swallow the title-drag the parent bar would otherwise start, and
                    // perform the window-control action.
                    this.drag = None;
                    match which {
                        TitleBtn::Close => this.close_window(cell),
                        TitleBtn::Minimize => {
                            if let Some(ws) = this.windows.get_mut(&cell) {
                                ws.minimized = true;
                            }
                            this.persist_window(cell);
                        }
                        TitleBtn::Maximize => {
                            if let Some(ws) = this.windows.get_mut(&cell) {
                                ws.minimized = false;
                            }
                            this.persist_window(cell);
                        }
                    }
                    cx.notify();
                }),
            )
            .child(glyph)
    }

    /// A title-bar action wired through the desktop (close/min uses a click handler
    /// on the wrapping element; broken out so the drag handler can sit on the bar).
    fn affordance_button(
        &self,
        cell: CellId,
        label: &str,
        kind: ActionKind,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let held = match &kind {
            ActionKind::Transfer { amount } => {
                self.holds(&cell) && self.cell_balance(&cell) >= *amount as i64
            }
            _ => self.holds(&cell),
        };
        let kind2 = kind.clone();
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "aff-{}-{label}",
                    id_hex(&cell)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .when(!held, |d| d.opacity(0.5).text_color(gpui::rgb(NT_DIM)))
        .when(held, |d| {
            d.on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.actuate(cell, &kind2);
                    cx.notify();
                }),
            )
        })
        .child(label.to_string())
    }

    fn render_context_menu(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let menu = self.open_menu.as_ref().unwrap();
        let cell = menu.cell;
        let mut m = div()
            .absolute()
            .left(menu.at.x)
            .top(menu.at.y)
            .w(px(248.0))
            .bg(gpui::rgb(NT_FACE))
            .border_2()
            .border_color(gpui::rgb(NT_SHADOW))
            .py_1()
            .flex()
            .flex_col();
        // A header naming the cell the menu acts on.
        m = m.child(
            div()
                .px_2()
                .py_1()
                .text_size(px(10.0))
                .text_color(gpui::rgb(NT_DIM))
                .border_b_1()
                .border_color(gpui::rgb(NT_FACE_DARK))
                .child(format!("{} · {}", self.cell_kind(&cell), id_short(&cell))),
        );
        for action in &menu.actions {
            let kind = action.kind.clone();
            let held = action.held;
            let row = div()
                .id(gpui::SharedString::from(format!(
                    "ctx-{}-{}",
                    id_hex(&cell),
                    action.label
                )))
                .px_3()
                .py_1()
                .text_size(px(12.0))
                .when(!held, |d| d.opacity(0.45).text_color(gpui::rgb(NT_DIM)))
                .when(held, |d| {
                    d.hover(|s| {
                        s.bg(gpui::rgb(NT_SELECT))
                            .text_color(gpui::rgb(NT_TITLE_TEXT))
                    })
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.actuate(cell, &kind);
                            this.open_menu = None;
                            cx.notify();
                        }),
                    )
                })
                .child(action.label.clone());
            m = m.child(row);
        }
        m
    }

    fn render_statusbar(&self) -> impl IntoElement {
        div()
            .absolute()
            .left(px(0.0))
            .bottom(px(0.0))
            .w_full()
            .h(px(22.0))
            .flex()
            .items_center()
            .px_2()
            .bg(gpui::rgb(NT_FACE))
            .border_t_2()
            .border_color(gpui::rgb(NT_HILIGHT))
            .text_size(px(11.0))
            .text_color(gpui::rgb(NT_TEXT))
            .child(self.status.clone())
    }
}

#[derive(Clone, Copy)]
enum TitleBtn {
    Minimize,
    Maximize,
    Close,
}

// ── Small render helpers ──────────────────────────────────────────────────────────

fn face_section(title: &str) -> impl IntoElement {
    div()
        .mt_1()
        .text_size(px(10.0))
        .font_weight(FontWeight::BOLD)
        .text_color(gpui::rgb(0x000080))
        .child(format!("── {title} "))
}

fn face_row(key: &str, value: &str) -> impl IntoElement {
    div()
        .flex()
        .flex_row()
        .text_size(px(11.0))
        .child(
            div()
                .w(px(96.0))
                .text_color(gpui::rgb(0x505050))
                .child(format!("{key}:")),
        )
        .child(div().flex_1().child(value.to_string()))
}

fn fmt_balance(b: i64) -> String {
    if b < 0 {
        format!("−{}", group(-b as u64))
    } else {
        group(b as u64)
    }
}

/// Group an integer with thousands separators (NT-dense numerics).
fn group(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::new();
    let bytes = s.as_bytes();
    let len = bytes.len();
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}
