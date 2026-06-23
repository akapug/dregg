//! deos-zed demo — open a real file, edit it, save it, verify it changed on disk.
//!
//! Two modes:
//!
//!   * `demo` (default): open a gpui window with the file tree + editor over a
//!     scratch file in a temp dir. Edit it live; Cmd/Ctrl-S saves through the
//!     [`Fs`] seam back to disk.
//!
//!   * `demo --verify`: headless. Drive the [`Fs`] seam directly — write a
//!     scratch file, load it, mutate it, save it, re-load it — and assert the
//!     bytes on disk actually changed. Exits 0 on success, 1 on failure. This is
//!     the CI-runnable proof that a real file edits + saves THROUGH the trait
//!     (no display needed).

use std::path::PathBuf;
use std::sync::Arc;

use deos_zed::fs::{Fs, RealFs};

fn scratch_path() -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("deos-zed-demo-{}.rs", std::process::id()));
    p
}

/// Headless proof: a real file edits + saves through the `Fs` trait.
fn verify() -> anyhow::Result<()> {
    let fs: Arc<dyn Fs> = RealFs::arc();
    let path = scratch_path();

    let original = "fn main() {\n    println!(\"before\");\n}\n";
    let edited = "fn main() {\n    println!(\"AFTER — edited through the Fs seam\");\n}\n";

    // 1. Seed a real file on disk (through the seam).
    fs.save(&path, original)?;
    println!("seeded   {} ({} bytes)", path.display(), original.len());

    // 2. Load it back (this is exactly what Editor::open does).
    let loaded = fs.load(&path)?;
    anyhow::ensure!(loaded == original, "load did not round-trip the seed");
    println!("loaded   {} bytes — matches seed", loaded.len());

    // 3. Mutate in memory (the editor's rope buffer) and save (this is
    //    Editor::save → fs.save; with FirmamentFs this becomes a receipted turn).
    fs.save(&path, edited)?;
    println!("saved    edited buffer through fs.save (backend: {})", fs.backend_label());

    // 4. Verify the bytes on disk ACTUALLY changed — read with std::fs directly
    //    (NOT the seam) so this is an independent witness, not the seam grading
    //    its own homework.
    let on_disk = std::fs::read_to_string(&path)?;
    anyhow::ensure!(
        on_disk == edited,
        "disk content did not match the edited buffer!\n--- on disk ---\n{on_disk}\n--- expected ---\n{edited}"
    );
    anyhow::ensure!(on_disk != original, "disk content did not change from the original");
    println!("VERIFIED disk content changed: read-back == edited buffer (independent std::fs witness)");

    // 5. read_dir + metadata through the seam (the file-tree path).
    let dir = path.parent().unwrap();
    let entries = fs.read_dir(dir)?;
    anyhow::ensure!(
        entries.iter().any(|e| e.path == path),
        "read_dir did not list the scratch file"
    );
    let md = fs.metadata(&path)?;
    anyhow::ensure!(!md.is_dir && md.len as usize == edited.len(), "metadata wrong");
    println!("VERIFIED read_dir lists the file; metadata len={} is_dir={}", md.len, md.is_dir);

    let _ = std::fs::remove_file(&path);
    println!("\nALL CHECKS PASSED — a real file edits + saves through the Fs seam.");
    Ok(())
}

/// Headless proof that SAVE IS A TURN: drive a [`FirmamentFs`] directly — seed a
/// file as a cell, load it from the ledger, edit + save (a real cap-gated turn
/// producing a `TurnReceipt`), then re-load and assert the content round-trips
/// through the LEDGER, not disk. Exits 0 on success. The `firmament` feature must
/// be built in (`cargo run --bin demo --features firmament -- --firmament`).
#[cfg(feature = "firmament")]
fn verify_firmament() -> anyhow::Result<()> {
    use deos_zed::fs::FirmamentFs;

    let fs = FirmamentFs::new();
    let path = PathBuf::from("/proj/src/main.rs");

    let original = "fn main() {\n    println!(\"before\");\n}\n";
    let edited = "fn main() {\n    println!(\"AFTER — this save is a receipted turn\");\n}\n";

    // 1. Seed the file AS A CELL (genesis): a file IS a cell on the ledger.
    let file = fs.seed_file(&path, original)?;
    println!(
        "seeded   {} -> cell {} ({} bytes, genesis)",
        path.display(),
        hex8(file.0),
        original.len()
    );

    // 2. Load it back — read from the CELL's committed content, not disk.
    let loaded = fs.load(&path)?;
    anyhow::ensure!(loaded == original, "load did not round-trip the seeded cell");
    println!("loaded   {} bytes from the ledger — matches seed", loaded.len());
    anyhow::ensure!(fs.receipt_count() == 0, "a seed is genesis, not a turn");

    // 3. Save the edited buffer — THIS IS A TURN: a cap-gated SetField over the
    //    file cell, driven through the real executor, leaving a receipt.
    fs.save(&path, edited)?;
    let receipt = fs
        .last_receipt()
        .ok_or_else(|| anyhow::anyhow!("no receipt produced"))?;
    println!(
        "saved    edited buffer AS A TURN — receipt {} (agent {}, {} action(s), state {} -> {})",
        hex8(receipt.receipt_hash()),
        hex8(receipt.agent.0),
        receipt.action_count,
        hex8(receipt.pre_state_hash),
        hex8(receipt.post_state_hash),
    );
    anyhow::ensure!(fs.receipt_count() == 1, "the save produced exactly one receipt");
    anyhow::ensure!(receipt.agent == fs.editor_id(), "the editor is the turn's agent");
    anyhow::ensure!(
        receipt.pre_state_hash != receipt.post_state_hash,
        "the save must move the ledger state (the edit landed on-ledger)"
    );

    // 4. Re-load — the edited content comes BACK FROM THE LEDGER (the cell's
    //    committed map the turn wrote), an independent witness that the save's
    //    bytes are the ledger's, not a disk side-effect.
    let reloaded = fs.load(&path)?;
    anyhow::ensure!(
        reloaded == edited,
        "ledger content did not match the edited buffer!\n--- ledger ---\n{reloaded}\n--- expected ---\n{edited}"
    );
    anyhow::ensure!(reloaded != original, "ledger content did not change from the original");
    println!(
        "VERIFIED ledger content changed: re-load == edited buffer (read from the cell, NOT disk)"
    );

    // 5. read_dir + metadata through the seam (the file-tree path over cells).
    let entries = fs.read_dir(std::path::Path::new("/proj/src"))?;
    anyhow::ensure!(
        entries.iter().any(|e| e.path == path),
        "read_dir did not list the file cell"
    );
    let md = fs.metadata(&path)?;
    anyhow::ensure!(!md.is_dir && md.len as usize == edited.len(), "metadata wrong");
    println!(
        "VERIFIED read_dir lists the file cell; metadata len={} is_dir={}",
        md.len, md.is_dir
    );

    println!("\nALL CHECKS PASSED — a file is a cell, and a SAVE is a receipted dregg turn.");
    Ok(())
}

/// Short hex of a 32-byte id/hash for legible demo output.
#[cfg(feature = "firmament")]
fn hex8(b: [u8; 32]) -> String {
    b[..4].iter().map(|x| format!("{x:02x}")).collect()
}

/// Seed a real sample file so the screenshot shows syntax-highlighted code (not an
/// empty buffer). We copy this very demo's source so the capture is a real,
/// multi-line, rust-highlighted file. Returns `(root_dir, file_to_open)`.
#[cfg(feature = "screenshot")]
fn seed_sample(fs: &std::sync::Arc<dyn Fs>) -> anyhow::Result<(PathBuf, PathBuf)> {
    let scratch = scratch_path();
    // Use this binary's own source if we can find it, else a representative snippet.
    let body = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/editor.rs"))
        .unwrap_or_else(|_| {
            "//! deos-zed sample buffer.\n\nuse std::sync::Arc;\n\nfn main() {\n    \
             let xs: Vec<i32> = (0..10).map(|x| x * x).collect();\n    \
             println!(\"squares: {xs:?}\");\n}\n"
                .to_string()
        });
    fs.save(&scratch, &body)?;
    let root = scratch.parent().unwrap().to_path_buf();
    Ok((root, scratch))
}

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().skip(1);
    let mut screenshot_out: Option<PathBuf> = None;
    let mut headless = false;
    let mut firmament = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--verify" | "--headless" => headless = true,
            "--firmament" => firmament = true,
            "--screenshot" => {
                screenshot_out = Some(PathBuf::from(
                    args.next()
                        .ok_or_else(|| anyhow::anyhow!("--screenshot needs an <out.png> path"))?,
                ));
            }
            _ => {}
        }
    }

    if let Some(out) = screenshot_out {
        #[cfg(feature = "screenshot")]
        {
            return shot::run(&out);
        }
        #[cfg(not(feature = "screenshot"))]
        {
            let _ = out;
            anyhow::bail!("built without the `screenshot` feature; rebuild with --features screenshot");
        }
    }

    if firmament {
        #[cfg(feature = "firmament")]
        {
            return verify_firmament();
        }
        #[cfg(not(feature = "firmament"))]
        {
            anyhow::bail!(
                "built without the `firmament` feature; rebuild with \
                 `--features firmament` for the save-is-a-turn proof"
            );
        }
    }

    if headless {
        return verify();
    }
    #[cfg(feature = "gui-demo")]
    {
        gui::run();
        Ok(())
    }
    #[cfg(not(feature = "gui-demo"))]
    {
        eprintln!(
            "deos-zed demo: built without the `gui-demo` feature.\n\
             Run `cargo run --bin demo --features gui-demo` for the window, or\n\
             `cargo run --bin demo -- --verify` for the headless edit+save proof."
        );
        verify()
    }
}

/// Offscreen screenshot mode: render the Editor surface (file tree + syntax-
/// highlighted code + line numbers) to a PNG with no window. Mirrors the windowed
/// `gui::run` layout but drives the headless capture in `deos_zed::screenshot`.
#[cfg(feature = "screenshot")]
mod shot {
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use deos_zed::editor::Editor;
    use deos_zed::file_tree::FileTree;
    use deos_zed::fs::{Fs, RealFs};
    use deos_zed::screenshot::capture_surface;
    use gpui::{
        div, px, App, AppContext as _, Context, Entity, FocusHandle, Focusable,
        InteractiveElement as _, IntoElement, ParentElement as _, Render, Styled as _, Window,
    };
    use gpui_component::{h_flex, v_flex, ActiveTheme as _, Root, TitleBar};

    struct ShotApp {
        editor: Entity<Editor>,
        tree: FileTree,
        focus: FocusHandle,
    }

    impl ShotApp {
        fn new(
            fs: Arc<dyn Fs>,
            root: PathBuf,
            open: PathBuf,
            window: &mut Window,
            cx: &mut Context<Self>,
        ) -> Self {
            let editor = cx.new(|cx| Editor::new(fs.clone(), window, cx));
            let tree = FileTree::new(fs, root, cx);
            editor.update(cx, |ed, cx| {
                let _ = ed.open(open, window, cx);
            });
            Self { editor, tree, focus: cx.focus_handle() }
        }
    }

    impl Focusable for ShotApp {
        fn focus_handle(&self, _: &App) -> FocusHandle {
            self.focus.clone()
        }
    }

    impl Render for ShotApp {
        fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
            let editor = self.editor.clone();
            let tree_el = self.tree.render(
                cx.entity(),
                |_this: &mut ShotApp, _path, _window, _cx| {},
                cx,
            );
            v_flex()
                .size_full()
                .track_focus(&self.focus)
                .child(TitleBar::new().child("deos-zed — editor over the Fs seam"))
                .child(
                    h_flex()
                        .flex_1()
                        .min_h(px(0.))
                        .child(div().w(px(240.)).h_full().child(tree_el))
                        .child(
                            div()
                                .flex_1()
                                .h_full()
                                .border_l_1()
                                .border_color(cx.theme().border)
                                .child(editor),
                        ),
                )
        }
    }

    pub fn run(out: &Path) -> anyhow::Result<()> {
        let fs: Arc<dyn Fs> = RealFs::arc();
        let (root, open) = super::seed_sample(&fs)?;
        let (w, h) = (1100.0_f32, 720.0_f32);
        let (cw, ch) = capture_surface(out, w, h, move |window, cx| {
            let view = cx.new(|cx| ShotApp::new(fs, root, open, window, cx));
            cx.new(|cx| Root::new(view, window, cx))
        })?;
        let _ = std::fs::remove_file(super::scratch_path());
        println!(
            "OK headless editor screenshot -> {} ({cw}x{ch}, logical {w}x{h}); \
             file tree + syntax-highlighted code via offscreen wgpu.",
            out.display()
        );
        Ok(())
    }
}

#[cfg(feature = "gui-demo")]
mod gui {
    use std::path::PathBuf;
    use std::sync::Arc;

    use deos_zed::editor::Editor;
    use deos_zed::file_tree::FileTree;
    use deos_zed::fs::{Fs, RealFs};
    use gpui::{
        div, px, size, App, AppContext as _, Context, Entity, FocusHandle, Focusable,
        InteractiveElement as _, IntoElement, KeyBinding, ParentElement as _, Render, Styled as _,
        Window, WindowBounds, WindowOptions,
    };
    use gpui_component::{h_flex, v_flex, ActiveTheme as _, Root, TitleBar};

    gpui::actions!(deos_zed_demo, [Save]);

    struct DemoApp {
        editor: Entity<Editor>,
        tree: FileTree,
        focus: FocusHandle,
    }

    impl DemoApp {
        fn new(fs: Arc<dyn Fs>, root: PathBuf, window: &mut Window, cx: &mut Context<Self>) -> Self {
            let editor = cx.new(|cx| Editor::new(fs.clone(), window, cx));
            let tree = FileTree::new(fs, root, cx);
            // Open the seeded scratch file straight away.
            let scratch = super::scratch_path();
            editor.update(cx, |ed, cx| {
                let _ = ed.open(scratch, window, cx);
            });
            Self { editor, tree, focus: cx.focus_handle() }
        }

        fn save(&mut self, _: &Save, _window: &mut Window, cx: &mut Context<Self>) {
            self.editor.update(cx, |ed, cx| {
                let _ = ed.save(cx);
            });
        }
    }

    impl Focusable for DemoApp {
        fn focus_handle(&self, _: &App) -> FocusHandle {
            self.focus.clone()
        }
    }

    impl Render for DemoApp {
        fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
            let editor = self.editor.clone();
            let tree_el = self.tree.render(cx.entity(), move |this: &mut DemoApp, path, window, cx| {
                this.editor.update(cx, |ed, cx| {
                    let _ = ed.open(path, window, cx);
                });
            }, cx);

            v_flex()
                .size_full()
                .track_focus(&self.focus)
                .key_context("DemoApp")
                .on_action(cx.listener(Self::save))
                .child(TitleBar::new().child("deos-zed — editor over the Fs seam (Cmd/Ctrl-S saves)"))
                .child(
                    h_flex()
                        .flex_1()
                        .min_h(px(0.))
                        .child(div().w(px(240.)).h_full().child(tree_el))
                        .child(div().flex_1().h_full().border_l_1().border_color(cx.theme().border).child(editor)),
                )
        }
    }

    pub fn run() {
        // Seed a real scratch file so there's something concrete to edit + save.
        let fs = RealFs::arc();
        let scratch = super::scratch_path();
        let _ = fs.save(
            &scratch,
            "// deos-zed demo scratch file — edit me, then Cmd/Ctrl-S to save.\n\
             fn main() {\n    println!(\"hello from deos-zed\");\n}\n",
        );
        let root = scratch.parent().unwrap().to_path_buf();

        let app = gpui_platform::application().with_assets(gpui_component_assets::Assets);
        app.run(move |cx| {
            gpui_component::init(cx);
            cx.bind_keys([
                KeyBinding::new("cmd-s", Save, Some("DemoApp")),
                KeyBinding::new("ctrl-s", Save, Some("DemoApp")),
            ]);
            cx.activate(true);

            let opts = WindowOptions {
                window_bounds: Some(WindowBounds::centered(size(px(1100.), px(720.)), cx)),
                ..Default::default()
            };
            let fs = fs.clone();
            let root = root.clone();
            cx.spawn(async move |cx| {
                cx.open_window(opts, |window, cx| {
                    let view = cx.new(|cx| DemoApp::new(fs, root, window, cx));
                    cx.new(|cx| Root::new(view, window, cx))
                })
                .expect("open window");
            })
            .detach();
        });
    }
}
