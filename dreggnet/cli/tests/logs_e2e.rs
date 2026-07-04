//! End-to-end test of the REAL per-tenant logs path against the `dregg-cloud`
//! binary: `lease open` → `run` (which captures the workload's output into the
//! durable log store) → `logs <workload>` tails the genuine output lines (not
//! cached metadata) → `--search` filters → a second `logs` invocation (a fresh
//! process) proves the store survives → a logged-in mismatched identity is refused
//! (the cap-scoping teeth). Closes the LOG blocker in
//! `docs/CLOUD-PROVIDER-READINESS.md`.

use std::path::Path;
use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_dregg-cloud")
}

fn run(state: &Path, args: &[&str]) -> String {
    let out = Command::new(bin())
        .arg("--state-dir")
        .arg(state)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("spawn dregg-cloud {args:?}: {e}"));
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "dregg-cloud {args:?} failed:\n{stdout}\n{stderr}"
    );
    stdout
}

fn run_fail(state: &Path, args: &[&str]) -> (String, String) {
    let out = Command::new(bin())
        .arg("--state-dir")
        .arg(state)
        .args(args)
        .output()
        .unwrap();
    assert!(
        !out.status.success(),
        "dregg-cloud {args:?} unexpectedly succeeded"
    );
    (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// Open a lease (lessee `tenant-a`), run a wat workload that returns 42, and
/// return (state_dir, workload_id).
fn lease_and_run(dir: &Path) -> String {
    let source = dir.join("workload.wat");
    std::fs::write(
        &source,
        "(module (func (export \"run\") (result i32) (i32.const 42)))",
    )
    .unwrap();

    let open = run(
        dir,
        &[
            "lease",
            "open",
            "--cap-tier",
            "sandboxed",
            "--budget",
            "100",
            "--lessee",
            "tenant-a",
        ],
    );
    let lease_id = open
        .lines()
        .find_map(|l| l.strip_prefix("lease opened: "))
        .expect("lease id")
        .trim()
        .to_string();

    let run_out = run(
        dir,
        &[
            "run",
            "--lease",
            &lease_id,
            "--lang",
            "wat",
            "--source",
            source.to_str().unwrap(),
        ],
    );
    // Find the `workload <id>` header line (tracing logs may interleave).
    run_out
        .lines()
        .find_map(|l| l.trim().strip_prefix("workload "))
        .expect("workload id")
        .trim()
        .to_string()
}

#[test]
fn run_captures_then_logs_tails_the_real_output() {
    let dir = tempfile::tempdir().unwrap();
    let wl = lease_and_run(dir.path());

    // `logs <workload>` shows the REAL captured output line (42), tagged `out` —
    // not the old metadata stub.
    let logs = run(dir.path(), &["logs", &wl]);
    assert!(logs.contains("out"), "a stdout line is tagged out:\n{logs}");
    assert!(
        logs.contains("42"),
        "the real workload output 42 is tailed:\n{logs}"
    );
    assert!(
        !logs.contains("no captured runtime logs"),
        "capture should have landed real logs, not the metadata fallback:\n{logs}"
    );
}

#[test]
fn logs_search_filters_lines() {
    let dir = tempfile::tempdir().unwrap();
    let wl = lease_and_run(dir.path());

    // A matching search finds the line.
    let hit = run(dir.path(), &["logs", &wl, "--search", "42"]);
    assert!(hit.contains("42"), "search 42 finds the line:\n{hit}");

    // A non-matching search returns zero lines (header says 0).
    let miss = run(dir.path(), &["logs", &wl, "--search", "zzz-no-such-line"]);
    assert!(miss.contains("(0 lines)"), "search miss is empty:\n{miss}");
}

#[test]
fn logs_survive_a_restart() {
    let dir = tempfile::tempdir().unwrap();
    let wl = lease_and_run(dir.path());

    // Each `dregg-cloud logs` is a brand-new process reading the durable store —
    // so a second invocation seeing the same lines IS the restart-survival proof.
    let first = run(dir.path(), &["logs", &wl]);
    let second = run(dir.path(), &["logs", &wl]);
    assert!(
        first.contains("42") && second.contains("42"),
        "logs persist across processes"
    );
}

#[test]
fn a_mismatched_identity_cannot_read_anothers_logs() {
    let dir = tempfile::tempdir().unwrap();
    let wl = lease_and_run(dir.path());

    // Connect a DIFFERENT cap-account (a fresh local subject, != the `tenant-a`
    // lessee that owns the workload's logs). The cap-scoping teeth: `logs` is now
    // refused because the caller is not the owner.
    run(dir.path(), &["login", "--new"]);
    let (out, err) = run_fail(dir.path(), &["logs", &wl]);
    let combined = format!("{out}{err}");
    assert!(
        combined.contains("forbidden") && combined.contains("own"),
        "a non-owner identity is refused:\n{combined}"
    );
}
