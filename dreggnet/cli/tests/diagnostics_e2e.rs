//! First-impression polish proofs against the `dregg-cloud` binary:
//!
//! - `run` surfaces the REAL workload failure (a missing `run` export) instead of
//!   misdiagnosing it as a budget/lease lapse, and a SUCCESSFUL run leaves stderr
//!   clean (no leaked duroxide `Database locked` WARN noise).
//! - `verify --tamper` is a one-command self-demo: it flips a served byte and the
//!   check catches it (✗ MISMATCH), exiting 0 because a caught tamper is intended.

use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_dregg-cloud")
}

fn open_lease(state: &std::path::Path) -> String {
    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(state)
        .args([
            "lease",
            "open",
            "--cap-tier",
            "sandboxed",
            "--budget",
            "100",
        ])
        .output()
        .expect("lease open");
    assert!(out.status.success());
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .find_map(|l| l.strip_prefix("lease opened: "))
        .expect("lease id")
        .trim()
        .to_string()
}

/// A workload whose WASM exports `main` instead of `run` must report the REAL cause,
/// not the misleading budget-lapse message.
#[test]
fn run_surfaces_the_real_export_error() {
    let dir = tempfile::tempdir().unwrap();
    let state = dir.path();
    let source = state.join("bad.wat");
    // Exports `main`, not the required `run` ABI.
    std::fs::write(
        &source,
        "(module (func (export \"main\") (result i32) (i32.const 42)))",
    )
    .unwrap();
    let lease = open_lease(state);

    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(state)
        .args(["run", "--lease", &lease, "--source"])
        .arg(&source)
        .output()
        .expect("run");
    let stdout = String::from_utf8_lossy(&out.stdout);

    // The real cause is surfaced (the missing `run` export), with the ABI hint.
    assert!(
        stdout.contains("the workload failed") && stdout.contains("export `run` not found"),
        "must surface the real export error:\n{stdout}"
    );
    assert!(
        stdout.contains("must export a function named `run`"),
        "must give the ABI hint:\n{stdout}"
    );
    // It must NOT misdiagnose a program error as a budget/lease lapse.
    assert!(
        !stdout.contains("lapsed (over budget)")
            && !stdout.contains("no output — the lease lapsed"),
        "must not blame the budget:\n{stdout}"
    );
}

/// A SUCCESSFUL run leaves stderr clean — no leaked duroxide WARN noise (the #1
/// first-impression liability).
#[test]
fn a_successful_run_has_clean_stderr() {
    let dir = tempfile::tempdir().unwrap();
    let state = dir.path();
    let source = state.join("ok.wat");
    std::fs::write(
        &source,
        "(module (func (export \"run\") (result i32) (i32.const 42)))",
    )
    .unwrap();
    let lease = open_lease(state);

    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(state)
        .args(["run", "--lease", &lease, "--source"])
        .arg(&source)
        .output()
        .expect("run");
    assert!(out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.to_ascii_lowercase().contains("database locked"),
        "duroxide `Database locked` noise leaked to stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("WARN"),
        "WARN noise leaked to a successful run's stderr:\n{stderr}"
    );
}

/// Build a tiny local git repo with one commit.
fn fixture_repo(files: &[(&str, &str)]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path();
    let run = |args: &[&str]| {
        assert!(
            Command::new("git")
                .arg("-C")
                .arg(p)
                .args(args)
                .output()
                .unwrap()
                .status
                .success(),
            "git {args:?}"
        );
    };
    run(&["init", "-q"]);
    run(&["config", "user.email", "t@dregg.test"]);
    run(&["config", "user.name", "dregg test"]);
    run(&["config", "commit.gpgsign", "false"]);
    for (path, body) in files {
        std::fs::write(p.join(path), body).unwrap();
    }
    run(&["add", "-A"]);
    run(&["commit", "-q", "-m", "fixture"]);
    dir
}

/// `verify --tamper` flips a served byte and PROVES the check catches it, exiting 0
/// (a caught tamper is the intended outcome — the cloud CLI's own tamper-demo).
#[test]
fn verify_tamper_self_demo_catches_and_exits_zero() {
    let src = fixture_repo(&[("index.html", "<h1>genuine</h1>")]);
    let state = tempfile::tempdir().unwrap();

    let deploy = Command::new(bin())
        .args(["--state-dir"])
        .arg(state.path())
        .args(["deploy"])
        .arg(src.path())
        .args(["--name", "blog"])
        .output()
        .expect("deploy");
    assert!(
        deploy.status.success(),
        "deploy failed:\n{}\n{}",
        String::from_utf8_lossy(&deploy.stdout),
        String::from_utf8_lossy(&deploy.stderr)
    );

    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(state.path())
        .args(["verify", "blog", "--tamper"])
        .output()
        .expect("verify --tamper");
    let stdout = String::from_utf8_lossy(&out.stdout);
    // A caught tamper exits 0 (the demo succeeded), prints the flip + the ✗ + the
    // "caught" confirmation.
    assert!(
        out.status.success(),
        "a caught tamper must exit 0:\n{stdout}"
    );
    assert!(
        stdout.contains("[tamper] flipped"),
        "missing the flip line:\n{stdout}"
    );
    assert!(
        stdout.contains("✗ MISMATCH"),
        "missing the mismatch:\n{stdout}"
    );
    assert!(
        stdout.contains("tamper was CAUGHT"),
        "missing the caught confirmation:\n{stdout}"
    );
}

/// A plain `verify` (no `--tamper`) of a clean deploy still passes — the demo did
/// not change the honest path.
#[test]
fn verify_without_tamper_still_passes() {
    let src = fixture_repo(&[("index.html", "<h1>genuine</h1>")]);
    let state = tempfile::tempdir().unwrap();
    let deploy = Command::new(bin())
        .args(["--state-dir"])
        .arg(state.path())
        .args(["deploy"])
        .arg(src.path())
        .args(["--name", "blog"])
        .output()
        .expect("deploy");
    assert!(deploy.status.success());

    let out = Command::new(bin())
        .args(["--state-dir"])
        .arg(state.path())
        .args(["verify", "blog"])
        .output()
        .expect("verify");
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("✓ verified"));
}
