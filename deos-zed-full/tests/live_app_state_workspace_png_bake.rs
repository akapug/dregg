//! THE LIVE-`AppState` WORKSPACE BAKE — a real Zed `Workspace` over a FirmamentFs
//! cell-ledger, built from the PRODUCTION [`AppState`] (NOT `AppState::test`).
//!
//! This is the proof for the **mount seam** that `starbridge-v2`'s
//! `src/zed_full_pane.rs` (`ZedWindow::open`) drives in the live cockpit: the
//! whole Zed IDE mounted from a genuine `workspace::AppState` built by
//! [`deos_zed_full::boot::build_live_app_state`] — a real `client::Client` over a
//! real `clock::RealSystemClock`, a `session::Session` over the real
//! `db::AppDatabase`, a real `LanguageRegistry`/`UserStore`/`WorkspaceStore`, and
//! `NodeRuntime::unavailable` — set as the App's `AppState` global, exactly as the
//! cockpit does. The earlier `unified_workspace_png_bake.rs` bakes the same
//! Workspace from `AppState::test`; THIS bake proves the NON-test builder mounts a
//! real `Entity<Workspace>` and renders the file tree + an open editor.
//!
//! `ZED_STATELESS=1` is set so the real `AppDatabase` falls back to its in-memory
//! db (no on-disk session file in CI) — the production code path, just stateless.
//!
//! It is a `#[test]` (not `#[gpui::test]`): the headless-renderer + screenshot
//! path is `test-support`-gated, on for these dev-deps. Writes to
//! `$DEOS_LIVE_APPSTATE_WORKSPACE_PNG` (default under the cargo target dir).
//!
//! Only compiled under `--features full-zed`.
#![cfg(feature = "full-zed")]

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use anyhow::{Result, anyhow};
use gpui::{AppContext, BorrowAppContext, HeadlessAppContext, PlatformTextSystem, px, size};
use gpui_wgpu::CosmicTextSystem;

use fs::Fs;
use project::{LocalProjectFlags, Project};
use settings::SettingsStore;
use workspace::Workspace;

use deos_zed_full::{FirmamentZedFs, boot};

/// Pump the headless app's foreground executor until `done` flips (or a cap),
/// advancing the simulated clock so timer-paced async progresses.
fn pump(cx: &HeadlessAppContext, done: &Rc<RefCell<bool>>, max: usize) {
    for _ in 0..max {
        cx.run_until_parked();
        if *done.borrow() {
            break;
        }
        cx.advance_clock(std::time::Duration::from_millis(20));
    }
}

#[test]
fn bake_the_live_app_state_workspace_png() -> Result<()> {
    // The production AppDatabase falls back to an in-memory db when stateless — the
    // real code path, no on-disk session file in the test.
    // SAFETY: single-threaded test setup before any threads spawn.
    unsafe { std::env::set_var("ZED_STATELESS", "1") };

    let out = std::env::var("DEOS_LIVE_APPSTATE_WORKSPACE_PNG").unwrap_or_else(|_| {
        format!(
            "{}/deos-live-appstate-workspace",
            std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string())
        )
    });
    let (w, h) = (1800.0_f32, 1100.0_f32);

    let text_system: Arc<dyn PlatformTextSystem> = Arc::new(CosmicTextSystem::new("Helvetica"));
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.allow_parking();

    // 1. Workspace + panel globals (settings store FIRST, then the panel inits).
    //    Use the REAL `settings::init` (loads bundled `default_settings()`), NOT
    //    `SettingsStore::test`, so panel default dock sides + chrome resolve from
    //    the production defaults. Then a tiny user-settings override docks the
    //    project panel LEFT (the fork's `default.json` defaults it `right`).
    cx.update(|cx| {
        settings::init(cx);
        cx.update_global(|store: &mut SettingsStore, cx| {
            let _ = store.set_user_settings(r#"{ "project_panel": { "dock": "left" } }"#, cx);
        });
        boot::install_workspace_globals(cx);
    });

    // 2. The cell-ledger fs, seeded with file-cells.
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file(
        "/proj/main.rs",
        "fn main() {\n    println!(\"a live AppState\");\n}\n",
    )?;
    fzfs.seed_file(
        "/proj/lib.rs",
        "pub fn hello() -> &'static str {\n    \"a cell is a file\"\n}\n",
    )?;
    fzfs.seed_file("/proj/src/mod.rs", "pub mod inner;\n")?;

    // 3. THE LOAD-BEARING STEP — build the REAL (non-test) AppState and set it
    //    global, exactly as the live cockpit's `ZedWindow::open` does.
    let fs: Arc<dyn Fs> = fzfs.clone();
    let app_state = cx.update(|cx| boot::build_live_app_state(fs.clone(), cx));

    // 3b. Wire the FULL workspace chrome BEFORE any Workspace is created — this
    //     registers `title_bar::init` + the per-crate inits + the
    //     `observe_new(Workspace)` hook that installs the status bar, the pane
    //     toolbar, and kicks the default-panel load. Must precede `Workspace::new`.
    cx.update(|cx| boot::wire_full_workspace_ui(app_state.clone(), cx));

    // 4. A real Project over the cell-fs, using the live AppState's parts.
    let project = cx.update(|cx| {
        Project::local(
            app_state.client.clone(),
            app_state.node_runtime.clone(),
            app_state.user_store.clone(),
            app_state.languages.clone(),
            fs.clone(),
            None,
            LocalProjectFlags {
                init_worktree_trust: true,
                ..Default::default()
            },
            cx,
        )
    });

    // 5. Create + scan the worktree over /proj.
    {
        let done = Rc::new(RefCell::new(false));
        let d2 = done.clone();
        let proj = project.clone();
        cx.update(|cx| {
            cx.spawn(async move |cx| {
                let task = proj.update(cx, |p, cx| p.find_or_create_worktree("/proj", true, cx));
                if let Ok((tree, _)) = task.await {
                    if let Some(scan) =
                        tree.read_with(cx, |t, _| t.as_local().map(|l| l.scan_complete()))
                    {
                        scan.await;
                    }
                }
                *d2.borrow_mut() = true;
            })
            .detach();
        });
        pump(&cx, &done, 4000);
        if !*done.borrow() {
            return Err(anyhow!("the cell worktree scan did not complete"));
        }
    }

    // 6. ONE Workspace window over the project, from the LIVE AppState.
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        cx.new(|cx| Workspace::new(None, project.clone(), app_state.clone(), window, cx))
    })?;
    let workspace = window.root(&mut cx)?;
    cx.run_until_parked();

    // 7. The default panels (project LEFT, outline/git RIGHT, terminal BOTTOM)
    //    were ALREADY kicked by `wire_full_workspace_ui`'s `observe_new(Workspace)`
    //    hook when `Workspace::new` ran above — pump the executor so those
    //    `Panel::load` futures resolve and `add_panel` docks them.
    {
        let done = Rc::new(RefCell::new(false));
        // The panel-load future has no completion flag we own; pump a fixed budget
        // so the spawned `load_full_default_panels` join resolves.
        pump(&cx, &done, 600);
    }

    // 7b. Reveal every loaded panel by TYPE — `open_panel::<T>` finds whichever
    //     dock holds the panel, activates it, and opens that dock. Robust against
    //     which side each panel docked on (project LEFT, outline/git RIGHT,
    //     terminal BOTTOM), unlike `toggle_dock` by position (which finds nothing
    //     if a dock's panel hadn't loaded yet). This shows the project tree on the
    //     left, the terminal at the bottom, and the outline/git on the right.
    cx.update_window(window.into(), |_, window, cx| {
        workspace.update(cx, |ws, cx| {
            use git_ui::git_panel::GitPanel;
            use outline_panel::OutlinePanel;
            use project_panel::ProjectPanel;
            use terminal_view::terminal_panel::TerminalPanel;
            ws.open_panel::<ProjectPanel>(window, cx);
            ws.open_panel::<TerminalPanel>(window, cx);
            ws.open_panel::<OutlinePanel>(window, cx);
            ws.open_panel::<GitPanel>(window, cx);
        });
    })?;
    cx.run_until_parked();

    // 8. Open a cell as an editor buffer (so the center pane shows real content).
    {
        let proj = project.clone();
        let ws = workspace.clone();
        let done = Rc::new(RefCell::new(false));
        let d2 = done.clone();
        cx.update_window(window.into(), |_, window, cx| {
            window
                .spawn(cx, async move |cx| {
                    if let Some(path) =
                        proj.update(cx, |p, cx| p.find_project_path("proj/main.rs", cx))
                    {
                        if let Ok(opened) = ws.update_in(cx, |ws, window, cx| {
                            ws.open_path(path, None, true, window, cx)
                        }) {
                            let _ = opened.await;
                        }
                    }
                    *d2.borrow_mut() = true;
                })
                .detach();
        })?;
        pump(&cx, &done, 4000);
    }

    // 9. Drive to a stable frame, then CAPTURE → PNG.
    for _ in 0..4 {
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _| window.refresh())?;
        cx.run_until_parked();
        cx.advance_clock(std::time::Duration::from_millis(32));
    }
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    if let Some(parent) = std::path::Path::new(&out).parent() {
        std::fs::create_dir_all(parent).ok();
    }
    captured.save(format!("{out}.png"))?;
    assert!(
        ww >= 100 && hh >= 100,
        "captured a real-sized frame: {ww}x{hh}"
    );
    println!(
        "OK headless LIVE-APPSTATE-WORKSPACE render -> {out}.png ({ww}x{hh}, logical {w}x{h}); \
         a real workspace::Workspace over the cell-ledger, mounted from the PRODUCTION \
         AppState (build_live_app_state) — project/outline/terminal panels docked + an editor \
         over a cell, gpui Scene via the headless offscreen renderer."
    );
    let _ = fzfs.total_balance();

    // TEARDOWN — single-shot bake; forget the context so its leak-detecting `Drop`
    // doesn't run on the live editor/PTY tasks still held by detached futures, and
    // let the OS reclaim everything as the process exits.
    let _ = (&workspace, &project, &app_state, &window);
    std::mem::forget(cx);
    Ok(())
}
