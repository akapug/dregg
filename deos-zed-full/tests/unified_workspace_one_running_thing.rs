//! THE WHOLE ZED WORKSPACE AS ONE RUNNING THING — over a FirmamentFs cell-ledger.
//!
//! The earlier proofs landed the panels in SEPARATE tests:
//!  * `full_workspace_over_cells.rs` — project_panel + outline_panel + terminal_view + PTY;
//!  * `hermes_agent_panel.rs`        — the confined-Hermes agent panel;
//!  * `git_panel_auto_discovery.rs`  — git-over-cells auto-discovery (bare project).
//!
//! THIS test instantiates a SINGLE `workspace::Workspace` and proves the WHOLE
//! IDE is one running thing in that one instance — every surface docked +
//! resolvable at once:
//!
//!   * project panel   (cells-as-files)      → `workspace.panel::<ProjectPanel>()`   is `Some`
//!   * outline panel                          → `workspace.panel::<OutlinePanel>()`    is `Some`
//!   * terminal panel  (real OS PTY shell)    → `workspace.panel::<TerminalPanel>()`   is `Some`
//!   * Hermes agent panel (confined, receipted)→ `workspace.panel::<HermesPanel>()`    is `Some`
//!   * git    (auto-discovered cell-ledger repo)→ `project.repositories()` has the repo
//!   * search (a real `ProjectSearchView` pane item, deployed) → active item downcasts
//!   * command palette (the real modal, toggled) → `workspace.active_modal::<CommandPalette>()` is `Some`
//!
//! and the load-bearing invariant: a SAVE through this one Workspace is a real
//! `TurnReceipt` on the cell-ledger.
//!
//! Nothing here reimplements a Zed component — every panel + the workspace + the
//! project + the buffer + the git repo + the search view + the command palette
//! are Zed's own crates at our gpui-fork rev, all alive in ONE Workspace entity
//! on the SAME gpui the deos cockpit dock hosts.
//!
//! Only compiled under `--features full-zed`.
#![cfg(feature = "full-zed")]

use std::sync::Arc;
use std::sync::RwLock;

use command_palette::CommandPalette;
use fs::Fs;
use gpui::{TestAppContext, VisualTestContext};
use language::Point;
use project::Project;
use search::ProjectSearchView;
use settings::SettingsStore;
use terminal_view::terminal_panel::TerminalPanel;
use terminal_view::TerminalView;
use workspace::{MultiWorkspace, Workspace};

use deos_hermes::cockpit_surface::HermesSession;
use deos_hermes::{AgentCipherclerk, AgentRuntime, GrantRegistry, HermesGateway, HeldToken};

use deos_zed_full::hermes_panel::HermesPanel;
use deos_zed_full::{boot, FirmamentZedFs};

/// A confined, persistent gateway for the docked agent panel — the standard
/// per-tool floors plus a tightened `terminal` rate so the panel's budget bar is
/// non-trivial. The runtime is leaked (`'static`), exactly as the live dock holds
/// it.
fn confined_gateway() -> HermesGateway<'static> {
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[7u8; 32], "deos");
    let rt: &'static AgentRuntime =
        Box::leak(Box::new(AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos")));
    let registry = GrantRegistry::default_for_session(1000)
        .with_standard_tool_grants(1000)
        .with_tool_grant("terminal", 4, 1000);
    HermesGateway::new(rt, root, registry)
}

#[gpui::test]
async fn the_whole_zed_workspace_is_one_running_thing_over_the_cell_ledger(
    cx: &mut TestAppContext,
) {
    // 1. Install the Workspace + panel globals (settings store, theme, the
    //    editor/panel/command-palette/search crate registrations) — the deos
    //    subset of the standalone binary's init.
    cx.update(|cx| {
        let settings_store = SettingsStore::test(cx);
        cx.set_global(settings_store);
        boot::install_workspace_globals(cx);
    });
    // The worktree scanner + the terminal PTY both run on real OS threads; let the
    // test executor park on them so those real-threaded scans run to completion.
    cx.executor().allow_parking();

    // 2. The cell-ledger filesystem, seeded with file-cells (top-level + nested).
    let main_rs = "fn main() {\n    println!(\"from a cell\");\n}\n";
    let lib_rs = "pub fn hello() {}\n";
    let nested_rs = "pub mod inner;\n";
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file("/proj/main.rs", main_rs).unwrap();
    fzfs.seed_file("/proj/lib.rs", lib_rs).unwrap();
    fzfs.seed_file("/proj/src/mod.rs", nested_rs).unwrap();
    assert_eq!(fzfs.receipt_count(), 0, "seeds are genesis — no turn yet");

    // 2b. ARM THE CELL-LEDGER GIT SURFACE *before* the project scans, so the
    //     worktree's git-detection path fires during the same scan that lists the
    //     cells and auto-discovers the repo — the git surface is part of the ONE
    //     running Workspace, not a side test.
    let cell_git = fzfs.enable_git("/proj", cx.executor());
    // A real modified-since-HEAD divergence so the discovered repo surfaces REAL
    // cell-ledger status (one file modified), not an empty/host repo.
    cell_git.set_live(
        "/proj/main.rs",
        "fn main() {\n    println!(\"DIRTY edit\");\n}\n",
    );

    // 3. A REAL Zed Project, worktree rooted at /proj, fs = the cells. Trust the
    //    worktree so the discovered git backend is trusted.
    let fs: Arc<dyn Fs> = fzfs.clone();
    let project = Project::test_with_worktree_trust(fs.clone(), ["/proj".as_ref()], cx).await;

    // 4. ONE REAL Workspace window over that project.
    let window = cx.add_window(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
    let workspace = window
        .read_with(cx, |mw, _| mw.workspace().clone())
        .unwrap();
    let vcx = &mut VisualTestContext::from_window(window.into(), cx);

    // 5. LOAD + DOCK ALL PANELS INTO THE ONE WORKSPACE: project / outline /
    //    terminal AND the confined-Hermes agent panel — the full dock complement,
    //    via `boot::load_all_panels` (the same `Panel::load`→`add_panel` dance).
    let session = HermesSession::with_gateway("sess-unified", confined_gateway(), 100);
    let weak_ws = workspace.downgrade();
    let panels_task = vcx.update(|window, cx| {
        let weak_ws = weak_ws.clone();
        window.spawn(cx, async move |cx| {
            boot::load_all_panels(weak_ws, session, "sess-unified", cx.clone()).await
        })
    });
    vcx.run_until_parked();
    let (project_panel, outline_panel, terminal_panel, hermes_panel) = panels_task
        .await
        .expect("all four panels load + add over the one cell-fs workspace");

    // 6. EVERY DOCK PANEL IS PRESENT IN THE ONE WORKSPACE — resolve each back out
    //    of the real dock BY TYPE. The workspace's own panel registry answers.
    workspace.read_with(vcx, |ws, cx| {
        assert!(
            ws.panel::<project_panel::ProjectPanel>(cx).is_some(),
            "the project panel is docked"
        );
        assert!(
            ws.panel::<outline_panel::OutlinePanel>(cx).is_some(),
            "the outline panel is docked"
        );
        assert!(
            ws.panel::<TerminalPanel>(cx).is_some(),
            "the integrated terminal panel is docked"
        );
        assert!(
            ws.panel::<HermesPanel>(cx).is_some(),
            "the confined-Hermes agent panel is docked"
        );
    });
    // Keep the panel handles live.
    let _ = (&project_panel, &outline_panel, &terminal_panel, &hermes_panel);

    // 6b. Drive the worktree scan to a quiesced full scan (the cell namespace is
    //     materialized; the git-detection path has fired).
    let scan_done = project
        .read_with(vcx, |project, cx| {
            project
                .worktrees(cx)
                .next()
                .map(|wt| wt.read(cx).as_local().unwrap().scan_complete())
        })
        .expect("the cell worktree exists");
    scan_done.await;
    vcx.run_until_parked();

    // 7. THE PROJECT PANEL SEES THE CELL NAMESPACE (the worktree the panel
    //    renders lists the cells-as-files).
    let worktree_paths: Vec<String> = project.read_with(vcx, |project, cx| {
        let mut out = Vec::new();
        for wt in project.worktrees(cx) {
            for entry in wt.read(cx).entries(true, 0) {
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
        worktree_paths.iter().any(|p| p.ends_with("src")),
        "the project panel's worktree lists the cell directory src: {worktree_paths:?}"
    );

    // 8. GIT IS ALIVE IN THE ONE WORKSPACE — the project's GitStore auto-discovered
    //    the cell-ledger repository from the SAME worktree scan (this is exactly
    //    what `git_ui` reads). Poll a few scan cycles for the discovery event.
    let repo_entity = {
        let mut found = None;
        for _ in 0..50 {
            let r = project.read_with(vcx, |project, cx| {
                project.repositories(cx).values().next().cloned()
            });
            if r.is_some() {
                found = r;
                break;
            }
            vcx.run_until_parked();
            vcx.executor()
                .advance_clock(std::time::Duration::from_millis(20));
        }
        found
    };
    let repo_entity = repo_entity.expect(
        "the one Workspace's project auto-discovered the cell-ledger git repo from the worktree scan",
    );
    // Its HEAD branch is the cell-ledger's synthetic `main`, and its status shows
    // the modified cell — REAL cell-ledger VCS, surfaced in this Workspace.
    {
        let mut head_branch = None;
        for _ in 0..50 {
            let b = repo_entity.read_with(vcx, |repo, _| {
                repo.branch.as_ref().map(|b| b.ref_name.to_string())
            });
            if b.is_some() {
                head_branch = b;
                break;
            }
            vcx.run_until_parked();
            vcx.executor()
                .advance_clock(std::time::Duration::from_millis(20));
        }
        assert_eq!(
            head_branch.as_deref(),
            Some("refs/heads/main"),
            "the discovered repo's HEAD branch is the cell-ledger's synthetic main"
        );
    }
    let saw_modified = {
        let mut modified = false;
        for _ in 0..100 {
            let statuses: Vec<(String, bool)> = repo_entity.read_with(vcx, |repo, _| {
                repo.cached_status()
                    .map(|e| {
                        (
                            e.repo_path.as_std_path().to_string_lossy().to_string(),
                            e.status.is_modified(),
                        )
                    })
                    .collect()
            });
            if statuses.iter().any(|(p, m)| p.ends_with("main.rs") && *m) {
                modified = true;
                break;
            }
            vcx.run_until_parked();
            vcx.executor()
                .advance_clock(std::time::Duration::from_millis(20));
        }
        modified
    };
    assert!(
        saw_modified,
        "the discovered repo's panel-facing status lists main.rs modified (real cell-ledger VCS)"
    );

    // 9. SEARCH IS ALIVE — deploy a REAL `ProjectSearchView` into the workspace's
    //    active pane (the exact path the `DeploySearch` action runs). It becomes a
    //    real pane item, downcastable from the workspace's active item.
    workspace.update_in(vcx, |ws, window, cx| {
        ProjectSearchView::deploy_search(ws, &workspace::DeploySearch::default(), window, cx);
    });
    vcx.run_until_parked();
    workspace.read_with(vcx, |ws, cx| {
        let active = ws
            .active_pane()
            .read(cx)
            .active_item()
            .expect("the workspace pane has an active item after deploying search");
        assert!(
            active.downcast::<ProjectSearchView>().is_some(),
            "the active workspace item is a real ProjectSearchView (search is open in the Workspace)"
        );
    });

    // 10. THE COMMAND PALETTE IS ALIVE — toggle the REAL modal (the same call the
    //     `command_palette::Toggle` action runs) and confirm it is the active modal
    //     in this Workspace. Its candidate list is `window.available_actions()` —
    //     all the actions every docked panel/editor registered, so the palette
    //     over THIS Workspace can dispatch the whole IDE's commands.
    workspace.update_in(vcx, |ws, window, cx| {
        CommandPalette::toggle(ws, "", window, cx);
    });
    vcx.run_until_parked();
    let palette = workspace.read_with(vcx, |ws, cx| ws.active_modal::<CommandPalette>(cx));
    assert!(
        palette.is_some(),
        "the command palette is the active modal in the one Workspace"
    );
    // Close it again so the subsequent buffer save's focus path is clean.
    workspace.update_in(vcx, |ws, window, cx| {
        ws.hide_modal(window, cx);
    });
    vcx.run_until_parked();

    // 11. A SAVE THROUGH THE ONE WORKSPACE IS A TURN. Open a cell from the project
    //     as a buffer, edit it, save through the Workspace's project — a real
    //     cap-gated turn leaving a `TurnReceipt` on the ledger.
    let project_path = project
        .read_with(vcx, |project, cx| project.find_project_path("proj/main.rs", cx))
        .expect("the seeded cell is visible to the worktree scan");
    let buffer = project
        .update(vcx, |project, cx| project.open_buffer(project_path, cx))
        .await
        .expect("Zed opens the cell as a buffer");
    buffer.update(vcx, |buffer, cx| {
        // The live (working-tree) content of main.rs is the DIRTY edit we set for
        // git; append a workspace edit on top of whatever line 1 holds.
        let text = buffer.text();
        let end = Point::new(
            (text.lines().count().max(1) - 1) as u32,
            text.lines().last().unwrap_or("").len() as u32,
        );
        buffer.edit([(end..end, "\n// EDITED via the one Workspace\n")], None, cx);
    });
    let receipts_before = fzfs.receipt_count();
    project
        .update(vcx, |project, cx| project.save_buffer(buffer.clone(), cx))
        .await
        .expect("the one Workspace's project saves the buffer = a verified turn");
    assert!(
        fzfs.receipt_count() > receipts_before,
        "a save through the one Workspace fired a cap-gated turn (a new receipt)"
    );
    let reloaded = fs.load("/proj/main.rs".as_ref()).await.unwrap();
    assert!(
        reloaded.contains("EDITED via the one Workspace"),
        "the edit landed on the cell via a turn: {reloaded:?}"
    );

    // 12. THE TERMINAL IS A REAL RUNNING PTY in the docked panel — open an actual
    //     shell and run a command, draining its output back through the grid.
    vcx.executor().allow_parking();
    let terminal = workspace
        .update_in(vcx, |workspace, window, cx| {
            TerminalPanel::add_center_terminal(workspace, window, cx, |project, cx| {
                project.create_terminal_shell(None, cx)
            })
        })
        .await
        .expect("a real PTY shell terminal opens in the docked TerminalPanel")
        .upgrade()
        .expect("the spawned terminal entity is live");
    vcx.run_until_parked();
    workspace.read_with(vcx, |workspace, cx| {
        let active = workspace
            .active_pane()
            .read(cx)
            .active_item()
            .expect("the workspace pane has an active item after opening the terminal");
        assert!(
            active.downcast::<TerminalView>().is_some(),
            "the active workspace item is a real TerminalView (the terminal is running)"
        );
    });
    terminal.update(vcx, |term, _| {
        term.input(b"echo deos-one-workspace\n".to_vec());
    });
    let mut saw_output = false;
    for _ in 0..200 {
        vcx.run_until_parked();
        let content = terminal.update_in(vcx, |term, window, cx| {
            term.sync(window, cx);
            term.last_content
                .cells
                .iter()
                .map(|c| c.cell.character())
                .collect::<String>()
        });
        if content.contains("deos-one-workspace") {
            saw_output = true;
            break;
        }
        vcx.executor()
            .advance_clock(std::time::Duration::from_millis(20));
    }
    assert!(
        saw_output,
        "the real PTY shell ran `echo deos-one-workspace` and its output reached the grid"
    );

    // THE WHOLE-WORKSPACE INVARIANT: ONE `workspace::Workspace` entity carried,
    // all at once, every docked panel (project / outline / terminal / Hermes), a
    // live auto-discovered cell-ledger git repo, a real deployed search view, the
    // command-palette modal, a running PTY — and a save through it was a verified
    // turn. The whole Zed IDE is one running thing over the cell-ledger.
    let _: &gpui::Entity<Workspace> = &workspace;
    let _ = fzfs.total_balance();
}
