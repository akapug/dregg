//! End-to-end test for the `dregg-cloud verify` verb against the `dregg-cloud` binary.
//!
//! Deploys a real local git repo fixture, then runs `dregg-cloud verify <site>` and
//! asserts the "you verify, you don't trust" check passes (served bytes match the
//! committed content root, the receipt chain verifies, the source-commitment
//! manifest matches). Then it TAMPERS the served bytes in the recorded bundle —
//! exactly what a lying host would do — and asserts verify REFUSES it.

use std::path::PathBuf;
use std::process::Command;

/// Build a tiny local git repo with one commit; return (dir, commit).
fn fixture_repo(files: &[(&str, &str)]) -> (tempfile::TempDir, String) {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path();
    let run = |args: &[&str]| {
        let ok = Command::new("git")
            .arg("-C")
            .arg(p)
            .args(args)
            .output()
            .unwrap()
            .status
            .success();
        assert!(ok, "git {args:?}");
    };
    run(&["init", "-q"]);
    run(&["config", "user.email", "t@dregg.test"]);
    run(&["config", "user.name", "dregg test"]);
    run(&["config", "commit.gpgsign", "false"]);
    for (path, body) in files {
        let fp = p.join(path);
        if let Some(parent) = fp.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(fp, body).unwrap();
    }
    run(&["add", "-A"]);
    run(&["commit", "-q", "-m", "fixture"]);
    let out = Command::new("git")
        .arg("-C")
        .arg(p)
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap();
    let commit = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (dir, commit)
}

fn deploy(bin: &str, state: &std::path::Path, repo: &std::path::Path) {
    let out = Command::new(bin)
        .args(["--state-dir"])
        .arg(state)
        .args(["deploy"])
        .arg(repo)
        .args(["--name", "blog"])
        .output()
        .expect("run deploy");
    assert!(
        out.status.success(),
        "deploy failed:\n{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

/// The single persisted bundle file under `<state>/receipts/`.
fn the_bundle_file(state: &std::path::Path) -> PathBuf {
    let dir = state.join("receipts");
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("receipts dir exists after a signed deploy")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "json").unwrap_or(false))
        .collect();
    entries.sort();
    assert_eq!(entries.len(), 1, "exactly one deploy bundle: {entries:?}");
    entries.pop().unwrap()
}

#[test]
fn deploy_then_verify_passes_and_matches_the_commit() {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let (src, commit) = fixture_repo(&[
        ("index.html", "<!doctype html><h1>verify me</h1>"),
        ("style.css", "h1{color:teal}"),
    ]);
    let state = tempfile::tempdir().unwrap();

    deploy(bin, state.path(), src.path());

    // The "you verify, you don't trust" check: re-witness by site name.
    let out = Command::new(bin)
        .args(["--state-dir"])
        .arg(state.path())
        .args(["verify", "blog"])
        .output()
        .expect("run verify");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "verify should pass:\n{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(stdout.contains("✓ verified"), "prints the ✓: {stdout}");
    assert!(
        stdout.contains(&commit),
        "the verified source-commitment manifest carries the deploy commit: {stdout}"
    );
    assert!(
        stdout.contains("matches the recorded deploy commit"),
        "the commit cross-check passes: {stdout}"
    );
}

#[test]
fn a_tampered_served_byte_is_refused() {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let (src, _commit) = fixture_repo(&[("index.html", "<h1>genuine</h1>")]);
    let state = tempfile::tempdir().unwrap();

    deploy(bin, state.path(), src.path());

    // A lying host flips a served byte in the bundle it hands out. Mutate the
    // recorded bundle's served content the way a tampering host would.
    let path = the_bundle_file(state.path());
    let raw = std::fs::read(&path).unwrap();
    let mut bundle: serde_json::Value = serde_json::from_slice(&raw).unwrap();
    let body = bundle["content"]["assets"]["/index.html"]["body"]
        .as_array_mut()
        .expect("the index.html asset has a byte body");
    assert!(!body.is_empty());
    // Flip the first byte to a different value — the content root will move.
    let first = body[0].as_u64().unwrap();
    body[0] = serde_json::json!((first ^ 0xff) & 0xff);
    std::fs::write(&path, serde_json::to_vec(&bundle).unwrap()).unwrap();

    // Verify must now REFUSE: the served bytes no longer re-hash to the committed,
    // signed content root — the lying host is caught.
    let out = Command::new(bin)
        .args(["--state-dir"])
        .arg(state.path())
        .args(["verify", "blog"])
        .output()
        .expect("run verify");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        !out.status.success(),
        "verify must FAIL on a tampered byte:\n{stdout}"
    );
    assert!(stdout.contains("✗ MISMATCH"), "prints the ✗: {stdout}");
}
