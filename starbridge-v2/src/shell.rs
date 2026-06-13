//! The shell — a cap-first window manager + compositor over real cells.
//!
//! This is the native desktop-OS pillar of the master interface. The [`Shell`]
//! owns a set of [`Surface`]s, the z-order stack, the focus, and the registry of
//! issued [`SurfaceCapability`]s. It is a CAP-FIRST window manager: every window
//! op — focus, raise, move, resize, minimize, close — is GATED by the surface's
//! capability. There is no ambient authority over a window; you drive a surface
//! only by presenting the cap the shell minted when it opened.
//!
//! Each surface is a view of a REAL cell in the embedded [`World`](crate::world)
//! (apps-as-cells). The shell reads the live ledger to:
//!   * derive each surface's TRUSTED-PATH identity label (the owning cell's real
//!     id + lifecycle) — anti-spoof chrome the shell draws, not the surface, so
//!     a surface cannot impersonate another cell, and
//!   * compose a [`Scene`]: the ordered, gpui-free description of what to paint
//!     (back-to-front), which the cockpit maps onto a gpui scene.
//!
//! The compositor framing: the cockpit is ONE privileged [`SurfaceKind::Console`]
//! surface; the other surfaces are cap-confined cell views, tiled/floated/
//! stacked in z-order. Surfaces show real cell state and react to real turns
//! (re-read each frame).
//!
//! This module is gpui-free and `cargo test`-able. The cockpit owns the gpui
//! mapping + the input routing.

use dregg_cell::lifecycle::CellLifecycle;
use dregg_cell::CellId;

use crate::surface::{Rect, Surface, SurfaceCapability, SurfaceId, SurfaceKind};
use crate::world::World;

/// Why a window op was refused. The shell's refusals are a FEATURE — they are
/// the ocap discipline of the window manager firing (the same spirit as the
/// executor rejecting an over-grant), surfaced so the operator can see WHY an
/// op was denied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShellError {
    /// The presented capability does not authenticate against any live surface
    /// (wrong secret, or a surface that no longer exists). The op is refused:
    /// authority over a surface is exactly its un-forgeable cap.
    Unauthorized,
    /// The named surface does not exist (already closed, or never opened).
    NoSuchSurface(SurfaceId),
    /// A protected op on the console surface (the console can't be closed — it
    /// is the trusted root; closing it would orphan the whole shell).
    ConsoleProtected,
}

/// How the shell lays out surfaces. The compositor supports three classic
/// arrangements; all paint in z-order, but the geometry the shell assigns
/// differs. (Float = the surfaces keep their own rects; tile/stack = the shell
/// arranges them.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    /// Surfaces float at their own rects (free placement; move/resize honored).
    Float,
    /// Non-console surfaces tile the work area in a simple grid; the console
    /// keeps its rect (it is the anchored master console).
    Tile,
    /// Non-console surfaces stack centered + offset (a cascade); the front one
    /// is fully visible.
    Stack,
}

impl Layout {
    pub fn label(self) -> &'static str {
        match self {
            Layout::Float => "float",
            Layout::Tile => "tile",
            Layout::Stack => "stack",
        }
    }
}

/// The trusted-path identity of a surface, drawn by the SHELL from the live
/// ledger (never from the surface's self-description). This is the anti-spoof
/// chrome: a surface labels itself with a title, but the *identity badge* — the
/// owning cell's real id + whether that cell is live/sealed/destroyed/missing —
/// comes from the shell reading the ledger, so a surface cannot impersonate
/// another cell's identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityLabel {
    /// The owning cell id (the REAL anchor — what the surface is a view of).
    pub cell: CellId,
    /// A short, operator-legible identity string (the cell id, abbreviated).
    pub short: String,
    /// The live lifecycle of the backing cell, as a badge ("live"/"sealed"/
    /// "destroyed"/"migrated"/"archived"), or "missing" if the cell is gone from
    /// the ledger (a dangling surface — the shell tells the truth about it).
    pub lifecycle: &'static str,
    /// Whether this is the trusted system console (labelled distinctly so it is
    /// never confused with a cell-owned surface).
    pub is_console: bool,
    /// Whether the backing cell is actually present in the live ledger. A
    /// cell-view whose cell was destroyed/removed is `false` — the chrome shows
    /// it as a dangling/missing view rather than letting it masquerade as live.
    pub backed: bool,
}

/// One painted item in the composed scene: a surface plus its shell-derived
/// chrome (identity label, focus, z). The cockpit renders these back-to-front.
#[derive(Clone, Debug)]
pub struct SceneItem {
    pub surface: Surface,
    pub identity: IdentityLabel,
    /// Whether this surface currently holds focus (drawn with an active border).
    pub focused: bool,
}

/// The composed scene: the ordered (back-to-front) list of surfaces to paint,
/// plus the shell's current layout. Gpui-free — a pure description.
#[derive(Clone, Debug)]
pub struct Scene {
    pub items: Vec<SceneItem>,
    pub layout: Layout,
    /// The focused surface id, if any (also flagged per-item).
    pub focused: Option<SurfaceId>,
}

impl Scene {
    /// The front-most (top of z-order) surface in the scene, if any.
    pub fn front(&self) -> Option<&SceneItem> {
        self.items.last()
    }
}

/// The cap-first window manager. Owns the surfaces, the z-order, the focus, the
/// layout, and the capability registry (the secrets it minted).
pub struct Shell {
    surfaces: Vec<Surface>,
    /// The capability registry: surface id → the secret the shell minted for it.
    /// A presented cap authenticates iff its `(surface, secret)` matches an entry
    /// here. The shell NEVER reveals these — a cap is obtained only by holding
    /// one the shell granted (open returns it), never by naming a surface.
    secrets: Vec<(SurfaceId, u64)>,
    /// The focused surface, if any.
    focus: Option<SurfaceId>,
    /// The current compositor layout.
    layout: Layout,
    /// Monotonic surface-id allocator.
    next_id: u64,
    /// A simple deterministic counter mixed into minted secrets (so two surfaces
    /// opened in a session get distinct caps without an RNG dependency; the
    /// secret is an unforgeability barrier within this process, not a
    /// cryptographic key).
    secret_seq: u64,
    /// The shell's logical work-area size (for tile/stack arrangement).
    area: Rect,
}

impl Default for Shell {
    fn default() -> Self {
        Self::new()
    }
}

impl Shell {
    /// A fresh shell with no surfaces, floating layout, and a default work area.
    pub fn new() -> Self {
        Shell {
            surfaces: Vec::new(),
            secrets: Vec::new(),
            focus: None,
            layout: Layout::Float,
            next_id: 1,
            secret_seq: 0x9E37_79B9_7F4A_7C15, // a fixed odd seed (Weyl-ish)
            area: Rect::new(0.0, 0.0, 1280.0, 760.0),
        }
    }

    // --- opening / closing surfaces (the cap-MINTING + cap-gated paths) ------

    /// Open the privileged CONSOLE surface (the cockpit's own window). Returns
    /// its [`SurfaceCapability`] — the console is cap-owned like any surface
    /// (the operator holds its cap), it is just the trusted root that can't be
    /// closed. `cell` is the identity the console runs as (the operator cell).
    pub fn open_console(&mut self, cell: CellId, title: impl Into<String>) -> SurfaceCapability {
        let rect = Rect::new(0.0, 0.0, self.area.w, self.area.h);
        self.open_surface(SurfaceKind::Console, cell, title.into(), rect)
    }

    /// Open a cap-confined VIEW of `cell` as a new floating surface. Returns the
    /// [`SurfaceCapability`] the opener now holds — the ONLY authority over the
    /// new surface. The surface is raised to the front + focused on open.
    pub fn open_cell_view(
        &mut self,
        cell: CellId,
        title: impl Into<String>,
    ) -> SurfaceCapability {
        // Cascade fresh cell views so they don't all stack on the origin.
        let n = self.surfaces.iter().filter(|s| !s.is_console()).count() as f32;
        let rect = Rect::new(
            80.0 + n * 36.0,
            80.0 + n * 36.0,
            420.0,
            300.0,
        );
        self.open_surface(SurfaceKind::CellView, cell, title.into(), rect)
    }

    /// The single surface-creation path: allocate an id, mint a fresh secret +
    /// its capability, install the surface at the top of the z-order, focus it,
    /// and hand back the cap. (Crate-internal — `open_console`/`open_cell_view`
    /// are the public doors.)
    fn open_surface(
        &mut self,
        kind: SurfaceKind,
        cell: CellId,
        title: String,
        rect: Rect,
    ) -> SurfaceCapability {
        let id = SurfaceId(self.next_id);
        self.next_id += 1;
        let secret = self.mint_secret();
        let z = self.top_z() + 1;
        let surface = Surface::new(id, kind, cell, title, rect, z);
        self.surfaces.push(surface);
        self.secrets.push((id, secret));
        self.focus = Some(id);
        SurfaceCapability::new(id, secret)
    }

    /// Close the surface the capability authorizes. Refuses if the cap doesn't
    /// authenticate, or if it names the console (the trusted root is protected).
    /// On success the surface + its secret are dropped (the cap becomes dead),
    /// and focus moves to the new front-most surface.
    pub fn close(&mut self, cap: &SurfaceCapability) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get(id) {
            if s.is_console() {
                return Err(ShellError::ConsoleProtected);
            }
        }
        self.surfaces.retain(|s| s.id() != id);
        self.secrets.retain(|(sid, _)| *sid != id);
        if self.focus == Some(id) {
            self.focus = self.front_id();
        }
        Ok(())
    }

    // --- cap-gated window ops (each authenticates the cap FIRST) --------------

    /// Focus + raise the capability's surface to the front of the z-order. The
    /// canonical "click to bring forward" op — but it is the *cap*, not a click,
    /// that authorizes it.
    pub fn focus(&mut self, cap: &SurfaceCapability) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        self.raise_to_front(id);
        self.focus = Some(id);
        Ok(())
    }

    /// Raise the capability's surface to the front WITHOUT changing focus
    /// (rarely needed alone; `focus` is the usual op). Cap-gated.
    pub fn raise(&mut self, cap: &SurfaceCapability) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        self.raise_to_front(id);
        Ok(())
    }

    /// Move the capability's surface by `(dx, dy)` (honored under `Float`; under
    /// tile/stack the shell re-derives geometry, so a move is recorded but the
    /// arrangement overrides it until the layout returns to float). Cap-gated.
    pub fn move_by(
        &mut self,
        cap: &SurfaceCapability,
        dx: f32,
        dy: f32,
    ) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            let r = s.rect().translated(dx, dy);
            s.set_rect(r);
        }
        Ok(())
    }

    /// Resize the capability's surface to `(w, h)` (clamped to a sane minimum).
    /// Cap-gated.
    pub fn resize(
        &mut self,
        cap: &SurfaceCapability,
        w: f32,
        h: f32,
    ) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            let r = s.rect();
            s.set_rect(Rect::new(r.x, r.y, w.max(140.0), h.max(90.0)));
        }
        Ok(())
    }

    /// Minimize / restore the capability's surface (collapse out of the scene
    /// body but keep it owned + present). Cap-gated. Minimizing the focused
    /// surface moves focus to the new front.
    pub fn set_minimized(
        &mut self,
        cap: &SurfaceCapability,
        minimized: bool,
    ) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            s.set_minimized(minimized);
        }
        if minimized && self.focus == Some(id) {
            self.focus = self.front_id();
        } else if !minimized {
            // Restoring raises + focuses it.
            self.raise_to_front(id);
            self.focus = Some(id);
        }
        Ok(())
    }

    /// Rename the capability's surface title. Cap-gated — only the owner may
    /// change the (operator-facing) title. (The IDENTITY label is shell-derived
    /// from the ledger and is NOT affected by this — anti-spoof.)
    pub fn set_title(
        &mut self,
        cap: &SurfaceCapability,
        title: impl Into<String>,
    ) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            s.set_title(title.into());
        }
        Ok(())
    }

    // --- layout (a shell-global op; not surface-scoped) ----------------------

    /// Set the compositor layout (float/tile/stack). This is a shell-wide op the
    /// operator (console) drives, not a per-surface one, so it is not cap-gated
    /// on an individual surface — it rearranges the whole scene.
    pub fn set_layout(&mut self, layout: Layout) {
        self.layout = layout;
    }

    pub fn layout(&self) -> Layout {
        self.layout
    }

    /// Cycle the layout float → tile → stack → float (the console's "rearrange"
    /// affordance / a palette command).
    pub fn cycle_layout(&mut self) {
        self.layout = match self.layout {
            Layout::Float => Layout::Tile,
            Layout::Tile => Layout::Stack,
            Layout::Stack => Layout::Float,
        };
    }

    /// Set the shell's logical work-area size (the cockpit calls this with the
    /// window size so tile/stack arrange to fit).
    pub fn set_area(&mut self, w: f32, h: f32) {
        self.area = Rect::new(0.0, 0.0, w.max(320.0), h.max(240.0));
    }

    // --- read surface --------------------------------------------------------

    /// The number of surfaces currently open (including the console).
    pub fn surface_count(&self) -> usize {
        self.surfaces.len()
    }

    /// The focused surface id, if any.
    pub fn focused(&self) -> Option<SurfaceId> {
        self.focus
    }

    /// Whether the capability still authenticates (its surface is live + the
    /// secret matches). Lets a holder check liveness without performing an op.
    pub fn validates(&self, cap: &SurfaceCapability) -> bool {
        self.authorize(cap).is_ok()
    }

    /// All open surfaces in z-order (back-to-front). Read-only.
    pub fn surfaces_in_z_order(&self) -> Vec<&Surface> {
        let mut v: Vec<&Surface> = self.surfaces.iter().collect();
        v.sort_by_key(|s| s.z());
        v
    }

    /// Compose the [`Scene`] to paint, reading the live `World` for each
    /// surface's trusted-path identity chrome + (under tile/stack) arranging the
    /// geometry. Back-to-front order; the front-most is last. This is the
    /// COMPOSITOR: it turns the owned-surface set + the live ledger into an
    /// ordered paint list.
    pub fn compose(&self, world: &World) -> Scene {
        // Order by z (back-to-front).
        let mut ordered: Vec<&Surface> = self.surfaces.iter().collect();
        ordered.sort_by_key(|s| s.z());

        // Geometry per layout. Float honors each surface's own rect; tile/stack
        // arrange the NON-console surfaces (the console keeps its anchored rect).
        let tiled = self.arranged_rects(&ordered);

        let items = ordered
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let rect = tiled.get(i).copied().unwrap_or_else(|| s.rect());
                let mut surface = (*s).clone();
                surface.set_rect(rect);
                let identity = self.identity_of(s, world);
                SceneItem {
                    surface,
                    identity,
                    focused: self.focus == Some(s.id()),
                }
            })
            .collect();

        Scene {
            items,
            layout: self.layout,
            focused: self.focus,
        }
    }

    /// Hit-test: the front-most non-minimized surface containing the point, if
    /// any (the cockpit uses this to translate a click in the scene into a
    /// focus, but only the CAP it then looks up authorizes the focus — the click
    /// is a hint, the cap is the authority).
    pub fn hit_test(&self, px: f32, py: f32, world: &World) -> Option<SurfaceId> {
        let scene = self.compose(world);
        // Front-to-back: the topmost hit wins.
        scene
            .items
            .iter()
            .rev()
            .find(|it| !it.surface.is_minimized() && it.surface.rect().contains(px, py))
            .map(|it| it.surface.id())
    }

    // --- internals -----------------------------------------------------------

    /// Authenticate a presented capability: it must name a live surface AND
    /// carry the secret the shell minted for it. Returns the authorized surface
    /// id, or [`ShellError::Unauthorized`]. THIS is the ocap check at the heart
    /// of the cap-first window manager — every op routes through it.
    fn authorize(&self, cap: &SurfaceCapability) -> Result<SurfaceId, ShellError> {
        let ok = self
            .secrets
            .iter()
            .any(|(sid, secret)| *sid == cap.surface() && *secret == cap.secret());
        if ok {
            Ok(cap.surface())
        } else {
            Err(ShellError::Unauthorized)
        }
    }

    /// Derive a surface's trusted-path identity from the LIVE ledger (anti-spoof
    /// chrome). The console is labelled as the trusted root; a cell-view's badge
    /// reflects the backing cell's real lifecycle (or "missing" if it's gone).
    fn identity_of(&self, s: &Surface, world: &World) -> IdentityLabel {
        let cell = s.cell();
        let short = crate::reflect::short_hex(cell.as_bytes());
        let backed = world.ledger().contains(&cell);
        let lifecycle = if s.is_console() {
            "system"
        } else {
            match world.ledger().get(&cell).map(|c| &c.lifecycle) {
                Some(CellLifecycle::Live) => "live",
                Some(CellLifecycle::Sealed { .. }) => "sealed",
                Some(CellLifecycle::Destroyed { .. }) => "destroyed",
                Some(CellLifecycle::Migrated { .. }) => "migrated",
                Some(CellLifecycle::Archived { .. }) => "archived",
                None => "missing",
            }
        };
        IdentityLabel {
            cell,
            short,
            lifecycle,
            is_console: s.is_console(),
            backed,
        }
    }

    /// Compute the per-surface rects for the current layout, in the SAME order
    /// as `ordered`. Float → each surface's own rect; tile → a grid of the
    /// non-console surfaces in the work area; stack → a centered cascade.
    fn arranged_rects(&self, ordered: &[&Surface]) -> Vec<Rect> {
        match self.layout {
            Layout::Float => ordered.iter().map(|s| s.rect()).collect(),
            Layout::Tile => self.tile_rects(ordered),
            Layout::Stack => self.stack_rects(ordered),
        }
    }

    fn tile_rects(&self, ordered: &[&Surface]) -> Vec<Rect> {
        // Tiles only the non-console, non-minimized surfaces; the console keeps
        // its anchored rect; minimized surfaces keep their own rect (they're not
        // painted in the body anyway).
        let tileable: Vec<usize> = ordered
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.is_console() && !s.is_minimized())
            .map(|(i, _)| i)
            .collect();
        let n = tileable.len().max(1);
        // A near-square grid.
        let cols = (n as f32).sqrt().ceil() as usize;
        let rows = n.div_ceil(cols);
        let pad = 8.0;
        let cw = (self.area.w - pad * (cols as f32 + 1.0)) / cols as f32;
        let ch = (self.area.h - pad * (rows as f32 + 1.0)) / rows as f32;

        let mut out: Vec<Rect> = ordered.iter().map(|s| s.rect()).collect();
        for (k, &idx) in tileable.iter().enumerate() {
            let col = k % cols;
            let row = k / cols;
            let x = pad + col as f32 * (cw + pad);
            let y = pad + row as f32 * (ch + pad);
            out[idx] = Rect::new(x, y, cw.max(140.0), ch.max(90.0));
        }
        out
    }

    fn stack_rects(&self, ordered: &[&Surface]) -> Vec<Rect> {
        let mut out: Vec<Rect> = ordered.iter().map(|s| s.rect()).collect();
        let w = (self.area.w * 0.6).max(360.0);
        let h = (self.area.h * 0.6).max(260.0);
        let base_x = (self.area.w - w) / 2.0;
        let base_y = (self.area.h - h) / 2.0;
        let mut k = 0.0;
        for (idx, s) in ordered.iter().enumerate() {
            if s.is_console() || s.is_minimized() {
                continue;
            }
            let off = k * 28.0;
            out[idx] = Rect::new(base_x + off, base_y + off, w, h);
            k += 1.0;
        }
        out
    }

    fn mint_secret(&mut self) -> u64 {
        // Advance a deterministic odd-step counter and scramble it. Distinct per
        // surface within the session; the unforgeability barrier is that this is
        // never revealed, only handed back inside the minted cap.
        self.secret_seq = self
            .secret_seq
            .wrapping_mul(0xD1B5_4A32_D192_ED03)
            .wrapping_add(0x9E37_79B9_7F4A_7C15);
        self.secret_seq ^ (self.next_id.wrapping_mul(0xA24B_AED4_963E_E407))
    }

    fn top_z(&self) -> u32 {
        self.surfaces.iter().map(|s| s.z()).max().unwrap_or(0)
    }

    /// The id of the front-most (highest z) surface that is ELIGIBLE for focus —
    /// i.e. not minimized. (A minimized surface is collapsed out of the body and
    /// must not become the focus target; focus falls through to the next visible
    /// surface, and to the console if nothing else remains.)
    fn front_id(&self) -> Option<SurfaceId> {
        self.surfaces
            .iter()
            .filter(|s| !s.is_minimized())
            .max_by_key(|s| s.z())
            .map(|s| s.id())
    }

    /// Raise a surface to the front by giving it `top_z + 1` (keeps the relative
    /// order of the rest). Idempotent if it is already on top.
    fn raise_to_front(&mut self, id: SurfaceId) {
        let top = self.top_z();
        if let Some(s) = self.get_mut(id) {
            if s.z() <= top {
                s.set_z(top + 1);
            }
        }
    }

    fn get(&self, id: SurfaceId) -> Option<&Surface> {
        self.surfaces.iter().find(|s| s.id() == id)
    }

    fn get_mut(&mut self, id: SurfaceId) -> Option<&mut Surface> {
        self.surfaces.iter_mut().find(|s| s.id() == id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::demo_world;

    // A small helper: a fresh shell over the demo world + a console.
    fn shell_with_console() -> (Shell, World, [CellId; 3], SurfaceCapability) {
        let (world, anchors) = demo_world();
        let mut shell = Shell::new();
        let console_cap = shell.open_console(anchors[0], "Console");
        (shell, world, anchors, console_cap)
    }

    #[test]
    fn opening_a_surface_mints_an_authorizing_cap() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        let [_treasury, service, _user] = anchors;
        let cap = shell.open_cell_view(service, "Service");
        // The cap authenticates; a window op succeeds.
        assert!(shell.validates(&cap));
        assert!(shell.focus(&cap).is_ok());
        // It is backed by the real service cell.
        let scene = shell.compose(&world);
        let item = scene.items.iter().find(|it| it.surface.cell() == service).unwrap();
        assert!(item.identity.backed, "the cell-view is backed by a real ledger cell");
        assert_eq!(item.identity.lifecycle, "live");
    }

    #[test]
    fn a_forged_capability_is_refused_every_op() {
        // The ocap heart: an op presented with a cap the shell never minted is
        // refused. Knowing the SurfaceId is NOT enough — the secret is required.
        let (mut shell, _world, anchors, _console) = shell_with_console();
        let real = shell.open_cell_view(anchors[1], "Service");
        // Forge a cap for the SAME surface id but a guessed secret.
        let forged = SurfaceCapability::new(real.surface(), real.secret().wrapping_add(1));
        assert!(!shell.validates(&forged));
        assert_eq!(shell.focus(&forged), Err(ShellError::Unauthorized));
        assert_eq!(shell.move_by(&forged, 10.0, 10.0), Err(ShellError::Unauthorized));
        assert_eq!(shell.close(&forged), Err(ShellError::Unauthorized));
        // A cap for a surface that doesn't exist is likewise refused.
        let nobody = SurfaceCapability::new(SurfaceId(9999), 0xDEAD);
        assert_eq!(shell.focus(&nobody), Err(ShellError::Unauthorized));
    }

    #[test]
    fn focus_raises_to_front_of_the_z_order() {
        let (mut shell, world, anchors, console) = shell_with_console();
        let [_t, service, user] = anchors;
        let a = shell.open_cell_view(service, "Service");
        let b = shell.open_cell_view(user, "User");
        // b opened last → it's the front. Focusing a raises it above b.
        assert_eq!(shell.compose(&world).front().unwrap().surface.cell(), user);
        shell.focus(&a).unwrap();
        assert_eq!(shell.compose(&world).front().unwrap().surface.cell(), service);
        // The console is still present, behind.
        assert!(shell.validates(&console));
        assert_eq!(shell.surface_count(), 3);
        let _ = b;
    }

    #[test]
    fn closing_a_surface_kills_its_capability() {
        let (mut shell, _world, anchors, _console) = shell_with_console();
        let cap = shell.open_cell_view(anchors[1], "Service");
        assert_eq!(shell.surface_count(), 2);
        assert!(shell.close(&cap).is_ok());
        assert_eq!(shell.surface_count(), 1);
        // The cap is now dead — further ops refuse.
        assert!(!shell.validates(&cap));
        assert_eq!(shell.focus(&cap), Err(ShellError::Unauthorized));
    }

    #[test]
    fn the_console_is_protected_from_close() {
        let (mut shell, _world, _anchors, console) = shell_with_console();
        // Even WITH the console's real cap, close is refused (trusted root).
        assert_eq!(shell.close(&console), Err(ShellError::ConsoleProtected));
        assert_eq!(shell.surface_count(), 1);
    }

    #[test]
    fn move_is_cap_gated_and_honored_under_float() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        let cap = shell.open_cell_view(anchors[1], "Service");
        let before = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == anchors[1])
            .unwrap()
            .surface
            .rect();
        shell.move_by(&cap, 50.0, 25.0).unwrap();
        let after = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == anchors[1])
            .unwrap()
            .surface
            .rect();
        assert_eq!(after.x, before.x + 50.0);
        assert_eq!(after.y, before.y + 25.0);
    }

    #[test]
    fn the_trusted_path_label_tracks_the_live_cell_lifecycle() {
        // Anti-spoof: the identity badge is the SHELL's, read from the ledger.
        // Seal the backing cell through the real executor and the badge follows.
        let (mut shell, mut world, _anchors, _console) = shell_with_console();
        // Open a view of a fresh cell we then seal.
        let fresh = world.genesis_cell(0x5A, 0);
        let _cap = shell.open_cell_view(fresh, "Fresh");
        let live_badge = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == fresh)
            .unwrap()
            .identity
            .lifecycle;
        assert_eq!(live_badge, "live");

        // Seal it (agent == target) through the verified executor.
        let t = world.turn(fresh, vec![crate::world::seal(fresh, "lock")]);
        assert!(world.commit_turn(t).is_committed());
        let sealed_badge = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == fresh)
            .unwrap()
            .identity
            .lifecycle;
        assert_eq!(sealed_badge, "sealed", "the shell's identity badge follows the live ledger");
    }

    #[test]
    fn a_dangling_surface_is_labelled_missing_not_spoofable() {
        // A surface whose backing cell is NOT in the ledger is shown as
        // unbacked/missing — it can't masquerade as a live cell.
        let (mut shell, world, _anchors, _console) = shell_with_console();
        let ghost = CellId::from_bytes([0x77; 32]); // never installed
        let _cap = shell.open_cell_view(ghost, "Ghost");
        let item = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == ghost)
            .cloned()
            .unwrap();
        assert!(!item.identity.backed, "an un-installed cell is not backed");
        assert_eq!(item.identity.lifecycle, "missing");
    }

    #[test]
    fn layout_tiles_and_stacks_the_non_console_surfaces() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        let _a = shell.open_cell_view(anchors[1], "Service");
        let _b = shell.open_cell_view(anchors[2], "User");

        shell.set_area(1200.0, 700.0);
        shell.set_layout(Layout::Tile);
        let scene = shell.compose(&world);
        assert_eq!(scene.layout, Layout::Tile);
        // The two cell views tile to non-overlapping, in-bounds rects.
        let cell_rects: Vec<Rect> = scene
            .items
            .iter()
            .filter(|it| !it.surface.is_console())
            .map(|it| it.surface.rect())
            .collect();
        assert_eq!(cell_rects.len(), 2);
        for r in &cell_rects {
            assert!(r.x >= 0.0 && r.y >= 0.0);
            assert!(r.x + r.w <= 1200.0 + 1.0);
        }

        // Cycle to stack: the front view is centered-ish and large.
        shell.set_layout(Layout::Stack);
        let scene = shell.compose(&world);
        assert_eq!(scene.layout, Layout::Stack);
        let front = scene.front().unwrap();
        assert!(!front.surface.is_console());
        assert!(front.surface.rect().w >= 360.0);
    }

    #[test]
    fn minimize_drops_focus_to_the_front_and_restore_refocuses() {
        let (mut shell, _world, anchors, _console) = shell_with_console();
        let a = shell.open_cell_view(anchors[1], "Service");
        let b = shell.open_cell_view(anchors[2], "User");
        // b is focused (opened last). Minimize b → focus falls to the new front.
        shell.set_minimized(&b, true).unwrap();
        assert_ne!(shell.focused(), Some(b.surface()));
        // Restoring b raises + refocuses it.
        shell.set_minimized(&b, false).unwrap();
        assert_eq!(shell.focused(), Some(b.surface()));
        let _ = a;
    }

    #[test]
    fn hit_test_finds_the_front_surface_under_a_point() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        shell.set_layout(Layout::Float);
        let a = shell.open_cell_view(anchors[1], "Service");
        // Place a known rect and hit its center.
        shell.resize(&a, 200.0, 150.0).unwrap();
        // Move it to a clear spot.
        let item = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == anchors[1])
            .unwrap()
            .surface
            .rect();
        let cx = item.x + item.w / 2.0;
        let cy = item.y + item.h / 2.0;
        assert_eq!(shell.hit_test(cx, cy, &world), Some(a.surface()));
        // A point far outside any surface hits nothing... unless the console
        // (full-area) is under it — the console spans the work area, so a point
        // inside the area but outside the cell view falls through to the console.
        let hit = shell.hit_test(5.0, 5.0, &world);
        assert!(hit.is_some(), "a point in the work area hits at least the console");
    }

    #[test]
    fn cycle_layout_rotates_float_tile_stack() {
        let mut shell = Shell::new();
        assert_eq!(shell.layout(), Layout::Float);
        shell.cycle_layout();
        assert_eq!(shell.layout(), Layout::Tile);
        shell.cycle_layout();
        assert_eq!(shell.layout(), Layout::Stack);
        shell.cycle_layout();
        assert_eq!(shell.layout(), Layout::Float);
    }
}
