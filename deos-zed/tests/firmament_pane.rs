//! THE THROUGH-THE-PANE firmament test: the cockpit editor surface, built
//! firmament-backed, opens a seeded file-cell THROUGH the editor's own
//! `open()`, a host-driven edit + `save()` fires a REAL cap-gated turn, and the
//! genuine `TurnReceipt` lands on the in-process ledger.
//!
//! This is the honest discipline the seam owes: not the gpui-free `Fs`-trait
//! test (that already exists in `firmament_fs.rs`), but the SAME path the
//! running pane uses — a real gpui `Editor` entity in a headless gpui app,
//! constructed by `EditorSurface::firmament` (exactly what `starbridge-v2`'s
//! `EditorPane::new` calls under the `firmament` feature), opened + edited +
//! saved through the editor entity.
//!
//! Gated on `firmament` (the live FS) + `cockpit-surface` (the surface) +
//! `screenshot` (the headless gpui harness — `HeadlessAppContext` + offscreen
//! renderer + no-system-fonts text). Run with:
//!   cargo test --features "firmament screenshot" --test firmament_pane

#![cfg(all(feature = "firmament", feature = "cockpit-surface", feature = "screenshot"))]

use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use gpui::{px, size, AppContext as _, HeadlessAppContext, IntoElement, PlatformTextSystem, Render};
use gpui_wgpu::CosmicTextSystem;

use deos_zed::cockpit_surface::EditorSurface;
use deos_zed::fs::{Fs, FirmamentFs};

// The same OFL fonts the screenshot harness ships, so text shaping is real and
// deterministic with no system fonts.
static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A trivial gpui root view holding the surface so we can drive it through the
/// window's typed entity handle (the surface itself isn't a `Render` root).
struct PaneHolder {
    surface: EditorSurface,
}

impl Render for PaneHolder {
    fn render(
        &mut self,
        window: &mut gpui::Window,
        cx: &mut gpui::Context<Self>,
    ) -> impl IntoElement {
        self.surface.render_body(window, cx)
    }
}

#[test]
fn cockpit_editor_pane_save_is_a_receipted_turn_through_the_pane() {
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("load fonts");

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(|cx| gpui_component::init(cx));

    let path = "/deos/main.rs";
    let seed = "fn main() {\n    println!(\"before\");\n}\n";
    let edited = "fn main() {\n    println!(\"AFTER — a receipted turn\");\n}\n";

    // Build the FIRMAMENT-backed surface — the exact constructor
    // `EditorPane::new` routes to under the `firmament` feature. The first
    // seeded file is opened THROUGH the editor's `open()` in the constructor.
    let window = cx
        .open_window(size(px(900.), px(600.)), |window, cx| {
            cx.new(|cx| {
                let surface = EditorSurface::firmament(
                    7,
                    PathBuf::from("/deos"),
                    &[(path, seed)],
                    window,
                    cx,
                )
                .expect("firmament surface mounts");
                PaneHolder { surface }
            })
        })
        .expect("headless window");

    cx.run_until_parked();

    // 1. The buffer opened onto the CELL content (open() read the cell, not disk),
    //    and no save has run yet.
    window
        .update(&mut cx, |holder, _window, cx| {
            let buf = holder.surface.editor().read(cx).text(cx);
            assert_eq!(buf, seed, "the pane opened onto the seeded cell content");
            assert_eq!(
                holder.surface.receipt_count(),
                Some(0),
                "no saves yet — a seed is genesis, not a turn"
            );
        })
        .unwrap();

    // 2. Drive a host edit + save THROUGH the editor entity (the running pane's
    //    own path: set the buffer, then `save()` -> `fs.save` -> a real turn).
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.surface.editor().clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edited, window, cx);
                ed.save(cx).expect("save commits a turn");
            });
        })
        .unwrap();

    cx.run_until_parked();

    // 3. A REAL receipt landed on the ledger; the cell content updated.
    window
        .update(&mut cx, |holder, _window, cx| {
            let surface = &holder.surface;

            assert_eq!(surface.receipt_count(), Some(1), "the save produced ONE receipt");
            let firm: &Arc<FirmamentFs> = surface.firmament_fs().expect("firmament-backed");
            let receipt = firm.last_receipt().expect("a receipt was recorded");
            assert_eq!(receipt.agent, firm.editor_id(), "the editor cell is the turn's agent");
            assert_ne!(
                receipt.pre_state_hash, receipt.post_state_hash,
                "the edit moved the ledger state (the save landed on-ledger)"
            );

            // The cell now holds the edited content, read back FROM THE LEDGER
            // through the same Fs handle the pane uses.
            let on_ledger = firm.load(Path::new(path)).expect("load the cell");
            assert_eq!(
                on_ledger, edited,
                "the edited content round-trips through the ledger, not disk"
            );

            // The editor's buffer matches, and the status reflects the REAL
            // on-ledger save (not a disk write / patch-history count).
            let buf = surface.editor().read(cx).text(cx);
            assert_eq!(buf, edited);
            let status = surface.editor().read(cx).status().to_string();
            assert!(
                status.contains("on-ledger"),
                "the status line reflects the real on-ledger save: {status}"
            );
        })
        .unwrap();
}
