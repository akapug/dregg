//! Mount [`deos_zed::Editor`] as a [`CockpitSurface`] — the deos editor pane.
//!
//! This forwards the cockpit's [`CockpitSurface`] trait to the inherent methods
//! on [`deos_zed::cockpit_surface::EditorSurface`]. It is mounted in
//! `dock/mod.rs`; the live cockpit opens it from
//! `cockpit/panels_workspace.rs::open_editor_pane`.
//!
//! ## Backing store: FirmamentFs by DEFAULT (saves = receipted turns)
//!
//! With starbridge-v2's `firmament` feature on (it rides `dev-surfaces` →
//! `native-full`), [`EditorPane::new`] builds a **firmament-backed** pane: the
//! editor edits sovereign cells over an in-process `Ledger` + `TurnExecutor`,
//! and EVERY SAVE is a real cap-gated `SetField` turn leaving a verifiable
//! `TurnReceipt`. The `RealFs` (disk) handle the caller passes is then only the
//! file-tree root hint — the editor buffer is on-ledger, not disk. The status
//! line's `N saves · on-ledger` is the genuine ledger receipt count.
//!
//! With the feature off, [`EditorPane::new`] is the original disk pane over the
//! passed `Arc<dyn Fs>` (so a `RealFs` build still works). The default
//! cockpit build (`native-full`) carries `firmament`, so the running editor is
//! firmament-backed. See `deos-zed/FIRMAMENT-FS-SEAM.md`.

use deos_zed::cockpit_surface::EditorSurface;
use gpui::{AnyElement, App, FocusHandle, IntoElement, SharedString, Window};

use super::surface::{CockpitSurface, SurfaceId};

/// A dock-hostable wrapper around a deos-zed editor surface.
pub struct EditorPane(EditorSurface);

/// The seed project a firmament-backed editor pane opens onto: a couple of
/// file-cells with real content so the editor opens on something editable and
/// the file tree shows a project. The FIRST entry is the file opened in the
/// buffer; saving it fires a real turn. Mirrors the showcase's seeded slice but
/// over genuine cells (not an in-memory string).
#[cfg(feature = "firmament")]
const FIRMAMENT_SEED: &[(&str, &str)] = &[
    (
        "/deos/main.rs",
        "// edit me — every save here is a RECEIPTED dregg turn on the live ledger.\n\
         fn main() {\n    println!(\"hello from a sovereign cell\");\n}\n",
    ),
    (
        "/deos/notes.md",
        "# on-ledger notes\n\nThis file is a cell. Saving it is a cap-gated turn,\n\
         not a disk write — the status line shows the real receipt count.\n",
    ),
];

impl EditorPane {
    /// Build the cockpit editor pane. With the `firmament` feature on (the
    /// default cockpit build), this is FIRMAMENT-BACKED — saves are receipted
    /// turns, `fs`/`root` only hint the file-tree root. Off, it is the disk pane
    /// over the passed `fs`.
    pub fn new(
        id: u64,
        fs: std::sync::Arc<dyn deos_zed::fs::Fs>,
        root: std::path::PathBuf,
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        #[cfg(feature = "firmament")]
        {
            let _ = fs; // disk handle unused: the firmament pane is cell-backed.
            match EditorSurface::firmament(id, root.clone(), FIRMAMENT_SEED, window, cx) {
                Ok(surface) => return EditorPane(surface),
                Err(e) => {
                    // Fail-soft to the disk pane so a firmament mount error can
                    // never take down the cockpit — but say so loudly.
                    eprintln!("EditorPane::new: firmament mount failed, falling back to disk: {e:#}");
                    return EditorPane(EditorSurface::new(id, deos_zed::fs::RealFs::arc(), root, window, cx));
                }
            }
        }
        #[cfg(not(feature = "firmament"))]
        EditorPane(EditorSurface::new(id, fs, root, window, cx))
    }

    /// Build a firmament-backed pane explicitly (independent of the feature gate
    /// at the call site): the editor edits sovereign cells, saves are receipted
    /// turns. `files` is the seed project (first entry opened in the buffer).
    /// Exposes the typed handle so the host/test can read the live receipt log.
    #[cfg(feature = "firmament")]
    pub fn firmament(
        id: u64,
        root: std::path::PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        Ok(EditorPane(EditorSurface::firmament(id, root, files, window, cx)?))
    }

    /// The real on-ledger receipt count (genuine `TurnReceipt`s), if this pane is
    /// firmament-backed. The honest `N saves · on-ledger` truth.
    #[cfg(feature = "firmament")]
    pub fn receipt_count(&self) -> Option<usize> {
        self.0.receipt_count()
    }

    /// The typed firmament fs handle, if firmament-backed — for host/test reads
    /// (last receipt, conservation Σδ=0, cell lookup).
    #[cfg(feature = "firmament")]
    pub fn firmament_fs(&self) -> Option<&std::sync::Arc<deos_zed::fs::FirmamentFs>> {
        self.0.firmament_fs()
    }

    /// Build a SEEDED editor pane: an in-memory buffer filled with `revisions`
    /// (the last shown; priors are on-ledger patches) under the virtual `name`
    /// (drives syntax highlighting), plus a real file tree over `fs`/`root`. What
    /// the headless showcase bake uses — disk-free highlighted code with a real
    /// `N patches · on-ledger` status.
    pub fn seeded(
        id: u64,
        fs: std::sync::Arc<dyn deos_zed::fs::Fs>,
        root: std::path::PathBuf,
        name: &str,
        revisions: &[&str],
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        EditorPane(EditorSurface::seeded(id, fs, root, name, revisions, window, cx))
    }

    /// Access the underlying editor entity (host-side open/save).
    pub fn editor(&self) -> &gpui::Entity<deos_zed::editor::Editor> {
        self.0.editor()
    }
}

impl CockpitSurface for EditorPane {
    fn item_id(&self) -> SurfaceId {
        SurfaceId(self.0.surface_id())
    }

    fn tab_label(&self) -> SharedString {
        // CockpitSurface::tab_label takes no cx; the live title is rendered in
        // tab_content instead. This static label is the stable fallback.
        SharedString::from("editor")
    }

    fn tab_content(&self, _window: &mut Window, cx: &mut App) -> AnyElement {
        use gpui::{div, ParentElement};
        div().child(self.0.tab_label(cx)).into_any_element()
    }

    fn render_body(&mut self, window: &mut Window, cx: &mut App) -> AnyElement {
        self.0.render_body(window, cx)
    }

    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.0.focus_handle(cx)
    }

    fn is_dirty(&self, cx: &App) -> bool {
        self.0.is_dirty(cx)
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(EditorPane(self.0.clone()))
    }
}
