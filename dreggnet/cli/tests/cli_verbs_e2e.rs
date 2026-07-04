//! End-to-end tests for the developer CLI verbs against the `dregg-cloud` binary:
//! `login`, `domains add/list/verify`, `ls`, `logs`, `destroy` — each driven over
//! the local/in-process path (the state dir + the real dregg-domains registry +
//! the webauth cred core), exactly as a developer would drive them.

use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_dregg-cloud")
}

/// Run `dregg-cloud --state-dir <state> <args...>`; assert success; return stdout.
fn run(state: &std::path::Path, args: &[&str]) -> String {
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

/// Run expecting FAILURE; return (stdout, stderr).
fn run_fail(state: &std::path::Path, args: &[&str]) -> (String, String) {
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

/// Build a tiny local git repo with one commit; return (dir, commit).
fn fixture_repo(files: &[(&str, &str)]) -> (tempfile::TempDir, String) {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path();
    let git = |args: &[&str]| {
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
    git(&["init", "-q"]);
    git(&["config", "user.email", "t@dregg.test"]);
    git(&["config", "user.name", "dregg test"]);
    git(&["config", "commit.gpgsign", "false"]);
    for (path, body) in files {
        std::fs::write(p.join(path), body).unwrap();
    }
    git(&["add", "-A"]);
    git(&["commit", "-q", "-m", "fixture"]);
    let out = Command::new("git")
        .arg("-C")
        .arg(p)
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap();
    (dir, String::from_utf8_lossy(&out.stdout).trim().to_string())
}

#[test]
fn login_mints_and_binds_a_cap_account() {
    let state = tempfile::tempdir().unwrap();
    let out = run(state.path(), &["login", "--new"]);
    assert!(
        out.contains("logged in as dregg:"),
        "login prints the subject: {out}"
    );
    assert!(
        out.contains("dga1_"),
        "login prints the bound credential: {out}"
    );

    // The account is persisted + surfaced by `ls`.
    let ls = run(state.path(), &["ls"]);
    assert!(ls.contains("account  dregg:"), "ls shows the account: {ls}");
}

#[test]
fn domains_add_then_verify_refuses_an_unowned_domain() {
    // DOM-1 fix: `verify` queries REAL DNS for the challenge record — it is never
    // seeded from the `--txt`/`--cname` the caller passes. So claiming a domain you
    // do not control (no published `_dregg-verify.<domain>` TXT) is REFUSED, and no
    // cert/route is granted — the binding stays pending. (The legit path requires a
    // real published DNS record; it cannot be exercised offline, by design.)
    let state = tempfile::tempdir().unwrap();
    run(state.path(), &["login", "--new"]);

    // BIND a custom domain (cap-gated by the local account) → pending + a challenge.
    let add = run(
        state.path(),
        &["domains", "add", "shop.example.com", "--site", "blog"],
    );
    assert!(
        add.contains("shop.example.com"),
        "add names the domain: {add}"
    );
    assert!(add.contains("pending"), "fresh binding is pending: {add}");
    assert!(add.contains("TXT"), "a TXT challenge is emitted: {add}");

    // The printed `verify ... --txt <value>` hint carries the expected nonce — but
    // passing it back NO LONGER tautologically verifies: the check is live DNS, and
    // example.com publishes no such `_dregg-verify` record, so it is refused.
    let value = add
        .lines()
        .find_map(|l| l.split("--txt ").nth(1))
        .map(|s| s.trim().to_string())
        .expect("the add output suggests the verify command with the TXT value");

    let list_pending = run(state.path(), &["domains", "list"]);
    assert!(
        list_pending.contains("pending"),
        "still pending pre-proof: {list_pending}"
    );

    // Echoing the printed nonce back is REFUSED (no real DNS record) — the squat
    // attack the red-team flagged (DOM-1) no longer mints a cert.
    let (_o, err) = run_fail(
        state.path(),
        &["domains", "verify", "shop.example.com", "--txt", &value],
    );
    assert!(
        err.contains("verify failed"),
        "unowned domain refused: {err}"
    );

    // The binding stays pending: no routing, no cert for a domain we cannot prove.
    let still_pending = run(state.path(), &["domains", "list"]);
    assert!(
        still_pending.contains("pending"),
        "an unproven domain stays pending: {still_pending}"
    );
    assert!(
        !still_pending.contains("verified"),
        "never verified without real DNS: {still_pending}"
    );
}

#[test]
fn ls_logs_and_destroy_over_a_deploy() {
    let state = tempfile::tempdir().unwrap();
    let (src, commit) = fixture_repo(&[
        ("index.html", "<!doctype html><h1>hi</h1>"),
        ("style.css", "h1{color:teal}"),
    ]);

    // Deploy a static site (the keystone verb), then exercise ls / logs / destroy.
    let repo = src.path().to_str().unwrap();
    let deploy = run(state.path(), &["deploy", repo, "--name", "blog"]);
    assert!(deploy.contains("blog.example.com"), "deployed: {deploy}");

    // ls lists the site.
    let ls = run(state.path(), &["ls"]);
    assert!(ls.contains("blog.example.com"), "ls lists the site: {ls}");

    // logs <commit-or-id>: pull the deploy id out of `ls` (first column of the site row).
    let id = ls
        .lines()
        .find(|l| l.contains("blog.example.com"))
        .and_then(|l| l.trim().split_whitespace().next())
        .expect("a site row with an id")
        .to_string();
    let logs = run(state.path(), &["logs", &id]);
    assert!(
        logs.contains(&commit),
        "logs carry the source commit: {logs}"
    );
    assert!(logs.contains("static"), "logs name the build plan: {logs}");

    // destroy by id prefix removes the site.
    let destroy = run(state.path(), &["destroy", &id]);
    assert!(
        destroy.contains("destroyed site blog"),
        "destroy reports it: {destroy}"
    );
    let ls_after = run(state.path(), &["ls"]);
    assert!(
        !ls_after.contains("blog.example.com"),
        "the site is gone: {ls_after}"
    );
}

#[test]
fn login_requires_a_credential_or_new() {
    let state = tempfile::tempdir().unwrap();
    let (_o, _e) = run_fail(state.path(), &["login"]);
}

#[test]
fn destroy_a_bound_domain_by_name() {
    let state = tempfile::tempdir().unwrap();
    run(state.path(), &["login", "--new"]);
    run(
        state.path(),
        &["domains", "add", "api.example.org", "--site", "svc"],
    );
    let destroy = run(state.path(), &["destroy", "api.example.org"]);
    assert!(
        destroy.contains("destroyed domain api.example.org"),
        "{destroy}"
    );
    let list = run(state.path(), &["domains", "list"]);
    assert!(!list.contains("api.example.org"), "domain removed: {list}");
}

/// FRICTION 1: every printed next-step prompt names the ACTUAL binary (`dregg-cloud`),
/// never bare `dregg` (which would collide with the substrate CLI). The binary's
/// argv[0] basename is `dregg-cloud`, so the derived prompts must say `dregg-cloud …`.
#[test]
fn printed_prompts_name_the_real_binary_not_dregg() {
    let state = tempfile::tempdir().unwrap();
    run(state.path(), &["login", "--new"]);

    // `domains add` prints the exact next command — it must be `dregg-cloud domains verify`.
    let add = run(
        state.path(),
        &["domains", "add", "shop.example.com", "--site", "blog"],
    );
    assert!(
        add.contains("dregg-cloud domains verify"),
        "next-step prompt names the binary: {add}"
    );
    // No prompt should tell the user to run a bare `dregg <verb>` (the wrong/other tool).
    assert!(
        !add.contains("dregg domains verify"),
        "must not print a bare `dregg` prompt: {add}"
    );

    // `ls` with no account points at `dregg-cloud login`, not `dregg login`.
    let fresh = tempfile::tempdir().unwrap();
    let ls = run(fresh.path(), &["ls"]);
    assert!(
        ls.contains("dregg-cloud login"),
        "ls names the binary: {ls}"
    );
    assert!(
        !ls.contains("(none — `dregg login`)"),
        "no bare dregg prompt: {ls}"
    );
}

/// FRICTION 2: `deploy` is HONEST — it does not print a bare live URL as if it
/// resolves; it says the content is published locally, points at the verify
/// manifest, and tells the user how to actually serve it.
#[test]
fn deploy_output_is_honest_not_a_dead_live_url() {
    let state = tempfile::tempdir().unwrap();
    let (src, _commit) = fixture_repo(&[("index.html", "<h1>hi</h1>")]);
    let repo = src.path().to_str().unwrap();
    let deploy = run(state.path(), &["deploy", repo, "--name", "blog"]);

    assert!(
        deploy.contains("published locally"),
        "honest publish framing: {deploy}"
    );
    assert!(
        !deploy.contains("deployed: http"),
        "must not claim a dead live URL: {deploy}"
    );
    assert!(
        deploy.contains("dregg-deploy.json"),
        "points at the verify manifest: {deploy}"
    );
    assert!(
        deploy.contains("--serve"),
        "tells the user how to serve it: {deploy}"
    );
}

/// FRICTION 5: `login --new` redacts the bearer credential by default, reveals it
/// only with `--show-credential`, and persists `state.json` 0600.
#[test]
fn login_new_redacts_secret_and_locks_state_file() {
    let state = tempfile::tempdir().unwrap();

    // Default: the credential is redacted in stdout (no full token), warned on stderr.
    let out = Command::new(bin())
        .arg("--state-dir")
        .arg(state.path())
        .args(["login", "--new"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "login failed: {stdout}\n{stderr}");
    assert!(
        stdout.contains("secret — hidden"),
        "credential redacted by default: {stdout}"
    );
    assert!(
        stderr.contains("BEARER SECRET"),
        "secret warning on stderr: {stderr}"
    );

    // The persisted state file is owner-only (0600).
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let md = std::fs::metadata(state.path().join("state.json")).unwrap();
        assert_eq!(
            md.permissions().mode() & 0o777,
            0o600,
            "state.json must be 0600"
        );
    }

    // --show-credential reveals the full token (a fresh state dir).
    let state2 = tempfile::tempdir().unwrap();
    let shown = run(state2.path(), &["login", "--new", "--show-credential"]);
    // The full token line is `account <dga1_…full…>` with no "hidden" marker.
    assert!(shown.contains("dga1_"), "shows the token: {shown}");
    assert!(
        !shown.contains("secret — hidden"),
        "not redacted when shown: {shown}"
    );
}

/// FRICTION 5 (split-brain): a wallet-bound login that carries the verifying root
/// (`--credential … --root <hex>`) can ALSO bind domains — not a dead-end.
#[test]
fn wallet_login_with_root_can_bind_domains() {
    // Mint a local account first to obtain a real (credential, root) pair to replay
    // as a "wallet" login into a fresh state dir.
    let minted = tempfile::tempdir().unwrap();
    let out = run(minted.path(), &["login", "--new", "--show-credential"]);
    let cred = out
        .lines()
        .find_map(|l| l.trim().strip_prefix("account "))
        .expect("the shown credential")
        .trim()
        .to_string();
    let root = out
        .lines()
        .find_map(|l| l.trim().strip_prefix("root "))
        .expect("the root pubkey")
        .trim()
        .to_string();

    // A fresh state dir: log in as a "wallet" credential, carrying the verifying root.
    let state = tempfile::tempdir().unwrap();
    run(
        state.path(),
        &["login", "--credential", &cred, "--root", &root],
    );

    // domains add now works (it has a local root to verify the binding against).
    let add = run(
        state.path(),
        &["domains", "add", "shop.example.com", "--site", "blog"],
    );
    assert!(
        add.contains("shop.example.com"),
        "wallet+root can bind domains: {add}"
    );
    assert!(
        add.contains("pending"),
        "binding is pending a DNS proof: {add}"
    );
}

/// A wallet-bound login WITHOUT a root is honestly refused at domains (not a silent
/// dead-end) and the error names how to fix it.
#[test]
fn wallet_login_without_root_is_refused_at_domains_with_guidance() {
    let minted = tempfile::tempdir().unwrap();
    let out = run(minted.path(), &["login", "--new", "--show-credential"]);
    let cred = out
        .lines()
        .find_map(|l| l.trim().strip_prefix("account "))
        .expect("the shown credential")
        .trim()
        .to_string();

    let state = tempfile::tempdir().unwrap();
    run(state.path(), &["login", "--credential", &cred]);
    let (_o, err) = run_fail(
        state.path(),
        &["domains", "add", "shop.example.com", "--site", "blog"],
    );
    assert!(
        err.contains("--root"),
        "the refusal explains the --root fix: {err}"
    );
}
