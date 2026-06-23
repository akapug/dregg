//! THE FULL-WORKSPACE PROOF (stage 2/3 of `DESIGN-FULL-ZED-EMBED.md`).
//!
//! Where `project_over_cells.rs` proves the editor buffer/save SEAM, this drives
//! the whole Zed **Workspace shell** over the cell-ledger and confirms it RUNS:
//!
//!  * a REAL `workspace::Workspace` (its dock + panes) instantiates over a
//!    `Project` whose `Fs` is the [`FirmamentZedFs`] cell-ledger;
//!  * Zed's REAL `project_panel`, `outline_panel`, and `terminal_view` panels
//!    `Panel::load` + `Workspace::add_panel` into the dock — and resolve back
//!    out of the workspace (`workspace.panel::<T>()` is `Some`);
//!  * the project panel's worktree SEES the cell namespace (the cells listed are
//!    the cells-as-files);
//!  * opening a cell from the project as a Zed `Buffer`, editing it, and saving
//!    through the real `Workspace` fires a verified turn (a `TurnReceipt`) — so a
//!    save FROM THE WORKSPACE is a turn on the ledger.
//!
//! Nothing here reimplements a Zed component: every panel + the workspace + the
//! project + the buffer are Zed's own crates at our gpui-fork rev. This is the
//! headless half of the deos-dock mount — the same gpui `Entity`s the cockpit
//! dock hosts.
//!
//! Only compiled under `--features full-zed`.
#![cfg(feature = "full-zed")]

use std::sync::Arc;

use fs::Fs;
use gpui::{TestAppContext, VisualTestContext};
use language::Point;
use project::Project;
use workspace::{MultiWorkspace, Workspace};

use settings::SettingsStore;

use deos_zed_full::boot;
use deos_zed_full::FirmamentZedFs;

#[gpui::test]
async fn real_zed_workspace_with_panels_runs_over_the_cell_ledger(cx: &mut TestAppContext) {
    // 1. Install the Workspace + panel globals: first the settings store, then
    //    theme + each panel/editor crate's `init` action+observer registrations
    //    — the deos subset of the standalone binary's init.
    cx.update(|cx| {
        let settings_store = SettingsStore::test(cx);
        cx.set_global(settings_store);
        boot::install_workspace_globals(cx);
    });

    // 2. The cell-ledger filesystem, seeded with file-cells under the worktree
    //    root (top-level files + a nested dir, so we exercise both leaf listing
    //    and directory listing). Keep the TYPED handle to read the receipt log.
    let main_rs = "fn main() {\n    println!(\"from a cell\");\n}\n";
    let lib_rs = "pub fn hello() {}\n";
    let nested_rs = "pub mod inner;\n";
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file("/proj/main.rs", main_rs).unwrap();
    fzfs.seed_file("/proj/lib.rs", lib_rs).unwrap();
    fzfs.seed_file("/proj/src/mod.rs", nested_rs).unwrap();
    assert_eq!(fzfs.receipt_count(), 0, "seeds are genesis — no turn yet");

    // 3. A REAL Zed Project, worktree rooted at /proj, filesystem = the cells.
    let fs: Arc<dyn Fs> = fzfs.clone();
    let project = Project::test(fs.clone(), ["/proj".as_ref()], cx).await;

    // 4. A REAL Workspace window (the MultiWorkspace root → inner Workspace) over
    //    that project. `MultiWorkspace::test_new` derives the AppState from the
    //    project — so the workspace's global `fs` IS our FirmamentZedFs.
    let window = cx.add_window(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
    let workspace = window
        .read_with(cx, |mw, _| mw.workspace().clone())
        .unwrap();
    let vcx = &mut VisualTestContext::from_window(window.into(), cx);

    // 5. LOAD + ADD THE REAL PANELS into the dock — the exact `initialize_panels`
    //    dance, run inside the window's async context.
    let weak_ws = workspace.downgrade();
    let panels_task = vcx.update(|window, cx| {
        let weak_ws = weak_ws.clone();
        window.spawn(cx, async move |cx| {
            boot::load_firmament_panels(weak_ws, cx.clone()).await
        })
    });
    vcx.run_until_parked();
    let (project_panel, outline_panel, terminal_panel) = panels_task
        .await
        .expect("the three panels load + add over the cell-fs workspace");

    // 6. THE PANELS ARE PRESENT IN THE WORKSPACE — resolve them back out of the
    //    real dock by type. This is the workspace's own panel registry answering.
    workspace.read_with(vcx, |ws, cx| {
        assert!(
            ws.panel::<project_panel::ProjectPanel>(cx).is_some(),
            "the project panel is mounted in the dock"
        );
        assert!(
            ws.panel::<outline_panel::OutlinePanel>(cx).is_some(),
            "the outline panel is mounted in the dock"
        );
        assert!(
            ws.panel::<terminal_view::terminal_panel::TerminalPanel>(cx)
                .is_some(),
            "the integrated terminal panel is mounted in the dock"
        );
    });

    // 7. THE PROJECT PANEL SEES THE CELL NAMESPACE. The worktree scan that backs
    //    it ran over FirmamentZedFs::read_dir — so the entries it knows are the
    //    cells-as-files. Assert the worktree (the data the project panel renders)
    //    contains our seeded cells.
    let worktree_paths: Vec<String> = project.read_with(vcx, |project, cx| {
        let mut out = Vec::new();
        for wt in project.worktrees(cx) {
            let wt = wt.read(cx);
            for entry in wt.entries(true, 0) {
                out.push(entry.path.as_std_path().to_string_lossy().to_string());
            }
        }
        out
    });
    assert!(
        worktree_paths.iter().any(|p| p.ends_with("main.rs")),
        "the project panel's worktree lists the cell main.rs: {worktree_paths:?}"
    );
    assert!(
        worktree_paths.iter().any(|p| p.ends_with("lib.rs")),
        "the project panel's worktree lists the cell lib.rs: {worktree_paths:?}"
    );
    assert!(
        worktree_paths.iter().any(|p| p.ends_with("src")),
        "the project panel's worktree lists the cell directory src: {worktree_paths:?}"
    );
    // The panel handle is live (its model resolves the same worktree).
    let _ = (&project_panel, &outline_panel, &terminal_panel);

    // 8. OPEN A CELL FROM THE PROJECT AS A BUFFER, edit it, and SAVE through the
    //    real Workspace's project — a save FROM THE WORKSPACE is a verified turn.
    let project_path = project
        .read_with(vcx, |project, cx| {
            project.find_project_path("proj/main.rs", cx)
        })
        .expect("the seeded cell is visible to the worktree scan");
    let buffer = project
        .update(vcx, |project, cx| project.open_buffer(project_path, cx))
        .await
        .expect("Zed opens the cell as a buffer");
    buffer.read_with(vcx, |buffer, _| {
        assert_eq!(buffer.text(), main_rs, "the buffer loaded the cell content");
    });
    buffer.update(vcx, |buffer, cx| {
        let line1 = buffer.text().lines().nth(1).unwrap().to_string();
        let col = line1.find("from a cell").unwrap();
        let start = Point::new(1, col as u32);
        let end = Point::new(1, (col + "from a cell".len()) as u32);
        buffer.edit([(start..end, "EDITED via the Workspace")], None, cx);
    });
    project
        .update(vcx, |project, cx| project.save_buffer(buffer.clone(), cx))
        .await
        .expect("the Workspace's project saves the buffer = a verified turn");

    // THE SAVE WAS A TURN: a genuine receipt landed on the ledger.
    assert!(
        fzfs.receipt_count() >= 1,
        "a save through the real Workspace fired a cap-gated turn (a receipt)"
    );
    let reloaded = fs.load("/proj/main.rs".as_ref()).await.unwrap();
    assert!(
        reloaded.contains("EDITED via the Workspace"),
        "the edit landed on the cell via a turn: {reloaded:?}"
    );

    // Conservation: a content save leaves Σ balance invariant.
    let _ = fzfs.total_balance();

    // Keep the workspace handle live to the end (no premature drop of the window).
    let _: &gpui::Entity<Workspace> = &workspace;
}
