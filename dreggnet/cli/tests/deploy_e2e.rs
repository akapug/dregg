//! End-to-end test for the `dregg-cloud deploy` verb against the `dregg-cloud` binary.
//!
//! Builds a real local git repo fixture, runs `dregg-cloud deploy <repo> --name blog` against a
//! temp state dir, and asserts the operator face drives the clone→detect→build→publish durable
//! workflow and prints + persists the verifiable receipt (the live URL + the source commit).

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

#[test]
fn cli_deploy_clones_builds_and_publishes_with_commit() {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let (src, commit) = fixture_repo(&[
        (
            "index.html",
            "<!doctype html><h1>shipped via dregg deploy</h1>",
        ),
        ("style.css", "h1{color:rebeccapurple}"),
    ]);
    let state = tempfile::tempdir().unwrap();

    // dregg-cloud --state-dir <dir> deploy <repo> --name blog
    let out = Command::new(bin)
        .args(["--state-dir"])
        .arg(state.path())
        .args(["deploy"])
        .arg(src.path())
        .args(["--name", "blog"])
        .output()
        .expect("run `deploy`");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "deploy failed:\nstdout: {stdout}\nstderr: {stderr}"
    );

    // The operator face printed the live URL, the build plan, and the SOURCE COMMITMENT.
    assert!(stdout.contains("blog.example.com"), "live URL: {stdout}");
    assert!(stdout.contains("static"), "build plan: {stdout}");
    assert!(
        stdout.contains(&commit),
        "the printed receipt carries the cloned commit: {stdout}"
    );

    // The deploy is recorded in the state dir, commit and all.
    let state_json =
        std::fs::read_to_string(state.path().join("state.json")).expect("state.json written");
    assert!(
        state_json.contains(&commit),
        "the recorded deploy carries the commit"
    );
    assert!(
        state_json.contains("blog"),
        "the recorded deploy names the site"
    );
}

#[test]
fn cli_deploy_rejects_an_underfunded_budget() {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let (src, _commit) = fixture_repo(&[("index.html", "<h1>x</h1>")]);
    let state = tempfile::tempdir().unwrap();

    // Budget 2 cannot cover clone+build+publish (3 steps).
    let out = Command::new(bin)
        .args(["--state-dir"])
        .arg(state.path())
        .args(["deploy"])
        .arg(src.path())
        .args(["--name", "blog", "--budget", "2"])
        .output()
        .expect("run `deploy`");
    assert!(!out.status.success(), "an underfunded deploy must fail");
}
