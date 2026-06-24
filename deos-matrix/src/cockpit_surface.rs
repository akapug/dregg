//! The cockpit-surface adapter — mount [`ChatView`] as a dock pane in
//! starbridge-v2.
//!
//! starbridge-v2's dock hosts any `CockpitSurface` (the slim ~8-method item trait
//! in `starbridge-v2/src/dock/surface.rs`). deos-matrix is its OWN workspace, so
//! it cannot `use` that trait directly; the split mirrors `deos-zed`:
//!
//!   * **here** — [`ChatSurface`], a concrete handle holding the [`ChatView`]
//!     entity, exposing `item_id` / `tab_label` / `render_body` / `focus_handle` /
//!     `is_dirty` / `boxed_clone` as plain inherent methods (the real, tested
//!     logic).
//!   * **`starbridge-v2/src/dock/chat_surface.rs`** (the ready-to-drop forwarder,
//!     in the doc) — a ~20-line `impl CockpitSurface for ChatSurface` forwarding
//!     each trait method here, plus a one-line `pub mod chat_surface;` in
//!     `dock/mod.rs` and a `deos-matrix` path dependency.
//!
//! Because both crates pin the same gpui fork, the `Entity<ChatView>` here is
//! byte-identical to the one starbridge-v2 sees — the forward is a plain call.

use std::sync::Arc;

use gpui::{
    AnyElement, App, AppContext as _, Entity, FocusHandle, Focusable as _, IntoElement, Window,
};

use crate::chat::ChatView;
use crate::source::ChatSource;

/// A mounted chat surface: the [`ChatView`] entity, addressable by a stable
/// surface id. Hand this to starbridge-v2's `CockpitSurface` impl.
#[derive(Clone)]
pub struct ChatSurface {
    id: u64,
    view: Entity<ChatView>,
}

impl ChatSurface {
    /// Build a chat surface over a [`ChatSource`]. `id` is the stable surface
    /// identity within a pane (the host supplies a monotonic counter or a `Tab`
    /// discriminant).
    pub fn new(id: u64, source: Arc<dyn ChatSource>, window: &mut Window, cx: &mut App) -> Self {
        let view = cx.new(|cx| ChatView::new(source, window, cx));
        Self { id, view }
    }

    /// Stable identity within a pane (`CockpitSurface::item_id`).
    pub fn item_id(&self) -> u64 {
        self.id
    }

    /// The tab label (`CockpitSurface::tab_label`).
    pub fn tab_label(&self) -> &'static str {
        "chat"
    }

    /// Render the body (`CockpitSurface::render_body`).
    pub fn render_body(&mut self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        self.view.clone().into_any_element()
    }

    /// The focus handle (`CockpitSurface::focus_handle`).
    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.view.read(cx).focus_handle(cx)
    }

    /// The chat surface is never "dirty" in the editor sense (no unsaved buffer);
    /// the composer's draft is transient (`CockpitSurface::is_dirty`).
    pub fn is_dirty(&self, _cx: &App) -> bool {
        false
    }

    /// Clone into a fresh box (`CockpitSurface::boxed_clone`). Thin handle — cheap.
    pub fn boxed_clone(&self) -> Self {
        self.clone()
    }
}
