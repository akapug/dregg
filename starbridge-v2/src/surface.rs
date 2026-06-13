//! Surfaces — cap-confined cell views (the apps-as-cells primitive).
//!
//! The desktop-OS pillar: every dregg CELL can be opened as its own SURFACE (a
//! window) in the shell. A surface is not a free-floating widget — it is OWNED
//! via an unforgeable [`SurfaceCapability`], and only the cap-holder may render
//! or drive it. This is the ocap discipline the rest of dregg runs, applied to
//! the *window manager itself*: there is no ambient authority to raise, move,
//! focus, or close a window — you must present the capability that authorizes
//! it.
//!
//! A surface is backed by a REAL cell (`CellId`) viewed through the embedded
//! [`World`](crate::world::World): its title, its trusted-path identity label,
//! and its body all read the live ledger — there are NO mock surfaces. When a
//! turn changes the cell, the surface re-reads and reflects it.
//!
//! This module is gpui-free and `cargo test`-able. The shell ([`crate::shell`])
//! owns the surfaces + the z-order + the capability registry; the cockpit maps
//! the shell's composed scene onto gpui.

use dregg_cell::CellId;

/// A monotonic surface handle (stable across the surface's life; the shell
/// assigns these in open order). Distinct from the backing `CellId` so the same
/// cell can (in principle) back more than one surface, and so a closed-then-
/// reopened cell gets a fresh, non-confusable surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SurfaceId(pub u64);

impl SurfaceId {
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

/// An UNFORGEABLE token that confers ownership of a surface. The shell mints one
/// when a surface opens and hands it to the opener; every window op
/// (focus/raise/move/resize/close/minimize) requires presenting the matching
/// cap. A cap carries:
///   * the `surface` it authorizes (so a cap for one surface can't drive
///     another — no cap confusion), and
///   * a `secret` the shell drew at mint time (so a cap cannot be FORGED by
///     guessing the surface id: an attacker who knows a `SurfaceId` still cannot
///     fabricate its cap without the secret).
///
/// This is the window-manager analogue of the executor's no-amplification rule:
/// authority over a surface is exactly the set of held `SurfaceCapability`s, and
/// it can only be obtained by being *granted* one (the shell never reveals a
/// surface's secret), never by naming the surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SurfaceCapability {
    surface: SurfaceId,
    secret: u64,
}

impl SurfaceCapability {
    /// The surface this capability authorizes.
    pub fn surface(&self) -> SurfaceId {
        self.surface
    }

    /// Construct a capability from its parts. CRATE-PRIVATE: only the shell (the
    /// trusted authority that draws the secret + tracks issuance) mints these,
    /// so a cap cannot be forged from outside. The pair is the unforgeable
    /// witness the shell checks.
    pub(crate) fn new(surface: SurfaceId, secret: u64) -> Self {
        SurfaceCapability { surface, secret }
    }

    /// The secret half — crate-private, used only by the shell to authenticate a
    /// presented cap against the one it minted. Never exposed beyond the shell.
    pub(crate) fn secret(&self) -> u64 {
        self.secret
    }
}

/// What a surface presents. The cockpit is ONE privileged surface (the master
/// console); every other surface is a cap-confined VIEW of a single cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SurfaceKind {
    /// The privileged master-console surface (the cockpit itself). It is still a
    /// surface in the shell — focusable, stackable — but it is the system's own
    /// trusted root, labelled as such (it is not a spoofable cell identity).
    Console,
    /// A cap-confined view of a single cell (apps-as-cells). The body reads the
    /// backing cell from the live ledger.
    CellView,
}

impl SurfaceKind {
    pub fn label(self) -> &'static str {
        match self {
            SurfaceKind::Console => "console",
            SurfaceKind::CellView => "cell",
        }
    }
}

/// A rectangle in shell-space (logical pixels). Plain data so the model stays
/// gpui-free; the cockpit maps it onto gpui `px()` bounds.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Rect {
    pub x: f32,
    pub y: f32,
    pub w: f32,
    pub h: f32,
}

impl Rect {
    pub fn new(x: f32, y: f32, w: f32, h: f32) -> Self {
        Rect { x, y, w, h }
    }

    /// Whether a point lies inside the rect (used for hit-testing focus).
    pub fn contains(&self, px: f32, py: f32) -> bool {
        px >= self.x && px <= self.x + self.w && py >= self.y && py <= self.y + self.h
    }

    /// Translate the rect by a delta, clamping the top-left to `>= 0` so a
    /// surface can't be dragged off the top/left of the shell (it stays
    /// reachable — a trusted-path property: a surface you own can't be hidden).
    pub fn translated(&self, dx: f32, dy: f32) -> Rect {
        Rect {
            x: (self.x + dx).max(0.0),
            y: (self.y + dy).max(0.0),
            w: self.w,
            h: self.h,
        }
    }
}

/// A live surface: a cap-confined window backed by a real cell.
///
/// The surface holds NO copy of the cell's state — it holds the cell's id and
/// re-reads the live ledger when it renders, so it cannot drift from what the
/// executor holds. The geometry/stacking fields are the window-manager state the
/// shell maintains; mutating them goes through the shell's CAP-GATED ops, never
/// directly.
#[derive(Clone, Debug)]
pub struct Surface {
    id: SurfaceId,
    kind: SurfaceKind,
    /// The cell this surface is a view OF. For the console this is the operator/
    /// system identity the console runs as; for a cell-view it is the viewed cell.
    cell: CellId,
    /// The window title (operator-facing). The TRUSTED-PATH identity label is
    /// derived separately from the live cell id (see [`crate::shell`]) so a
    /// surface's title can never *be* the spoof — the identity chrome is the
    /// shell's, drawn from the ledger, not the surface's self-description.
    title: String,
    /// Window geometry in shell-space.
    rect: Rect,
    /// Stacking order — higher is nearer the front. The shell keeps these dense
    /// and unique; the compositor paints in ascending z.
    z: u32,
    /// Whether the surface is minimized (collapsed out of the scene body but
    /// still owned + present in the shell, reachable via its cap).
    minimized: bool,
}

impl Surface {
    /// CRATE-PRIVATE constructor: only the shell creates surfaces (it owns the
    /// id allocator + the cap registry), so a `Surface` cannot be conjured
    /// outside the trusted window manager.
    pub(crate) fn new(
        id: SurfaceId,
        kind: SurfaceKind,
        cell: CellId,
        title: String,
        rect: Rect,
        z: u32,
    ) -> Self {
        Surface {
            id,
            kind,
            cell,
            title,
            rect,
            z,
            minimized: false,
        }
    }

    pub fn id(&self) -> SurfaceId {
        self.id
    }
    pub fn kind(&self) -> SurfaceKind {
        self.kind
    }
    /// The backing cell id — the surface's REAL anchor in the live ledger.
    pub fn cell(&self) -> CellId {
        self.cell
    }
    pub fn title(&self) -> &str {
        &self.title
    }
    pub fn rect(&self) -> Rect {
        self.rect
    }
    pub fn z(&self) -> u32 {
        self.z
    }
    pub fn is_minimized(&self) -> bool {
        self.minimized
    }
    pub fn is_console(&self) -> bool {
        matches!(self.kind, SurfaceKind::Console)
    }

    // --- crate-private mutators (the shell drives these AFTER a cap check) ----

    pub(crate) fn set_z(&mut self, z: u32) {
        self.z = z;
    }
    pub(crate) fn set_rect(&mut self, rect: Rect) {
        self.rect = rect;
    }
    pub(crate) fn set_minimized(&mut self, m: bool) {
        self.minimized = m;
    }
    pub(crate) fn set_title(&mut self, title: String) {
        self.title = title;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rect_contains_and_translate_clamp() {
        let r = Rect::new(10.0, 20.0, 100.0, 80.0);
        assert!(r.contains(50.0, 50.0));
        assert!(!r.contains(5.0, 50.0));
        assert!(r.contains(10.0, 20.0)); // top-left corner inclusive
        // Translating past the top-left clamps to 0 (can't be dragged off-screen).
        let t = r.translated(-1000.0, -1000.0);
        assert_eq!(t.x, 0.0);
        assert_eq!(t.y, 0.0);
        // The size is preserved under translation.
        assert_eq!(t.w, 100.0);
        assert_eq!(t.h, 80.0);
    }

    #[test]
    fn a_capability_names_exactly_one_surface() {
        let cap = SurfaceCapability::new(SurfaceId(7), 0xABCD);
        assert_eq!(cap.surface(), SurfaceId(7));
        // Two caps for the same surface but different secrets are distinct
        // tokens (the secret is load-bearing — a forged-id guess is not enough).
        let other = SurfaceCapability::new(SurfaceId(7), 0x1234);
        assert_ne!(cap, other);
    }
}
