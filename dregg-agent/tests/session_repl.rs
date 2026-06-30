//! End-to-end tests for the **hosted agent session** + the **SSH attach** — the
//! distribution model proven against the real `dregg-agent` binary, std-only
//! (recorded brain; no key, no network LLM, no real sshd).
//!
//! The proof the task asks for, locally simulated:
//!
//! 1. a user "ssh"es into a hosted session (we drive the same `attach` REPL the
//!    SSH forced-command drops into, over a piped stdin) → types a goal → it runs
//!    bounded + proven (cap-gated · metered · receipted);
//! 2. the budget draws down **across goals** (one ceiling for the whole session,
//!    no per-goal reset a runaway could exploit);
//! 3. a cap outside the bundle is **refused**;
//! 4. `verify` re-witnesses the whole session (host untrusted);
//! 5. a second account's session is **isolated** (its own budget + agent identity).

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU32, Ordering};

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_dregg-agent")
}

/// A fresh unique temp dir (no `tempfile` dev-dep needed). Best-effort cleanup is
/// the OS temp sweep; tests do not collide (pid + a process-unique counter).
fn tmpdir() -> PathBuf {
    static N: AtomicU32 = AtomicU32::new(0);
    let p = std::env::temp_dir().join(format!(
        "dregg-session-e2e-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
}

/// Two recorded chat-completions responses: a `shell` tool-call, then `finish`.
/// `RecordedOpenAICaller::repeating` repeats `finish` once exhausted, so a fresh
/// brain per goal does exactly one admitted shell op then ends — deterministic.
const RECORDED_RESPONSES: &str = r#"[
  {"choices":[{"message":{"role":"assistant","tool_calls":[
    {"id":"c1","type":"function","function":{"name":"shell","arguments":"{\"cmd\":\"echo hello-from-agent\"}"}}
  ]}}]},
  {"choices":[{"message":{"role":"assistant","tool_calls":[
    {"id":"c2","type":"function","function":{"name":"finish","arguments":"{\"summary\":\"done\"}"}}
  ]}}]}
]"#;

/// Write the recorded responses to `dir/resp.json` and return its path string.
fn write_resp(dir: &std::path::Path) -> String {
    let p = dir.join("resp.json");
    std::fs::write(&p, RECORDED_RESPONSES).unwrap();
    p.to_string_lossy().into_owned()
}

/// Run `dregg-agent <args...>` with `stdin_text` piped + `env` extras; return
/// (success, stdout).
fn run(args: &[&str], stdin_text: &str, env: &[(&str, &str)]) -> (bool, String) {
    let mut cmd = Command::new(bin());
    cmd.args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (k, v) in env {
        cmd.env(k, v);
    }
    let mut child = cmd.spawn().expect("spawn dregg-agent");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin_text.as_bytes())
        .unwrap();
    let out = child.wait_with_output().expect("wait dregg-agent");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
    )
}

// ── (1)+(2)+(4) the interactive session: budget draws down across goals; verify ──

#[test]
fn a_session_runs_goals_draws_budget_down_across_them_and_verifies() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());
    let out_file = dir.as_path().join("session.json");

    // Drive the REPL: two goals, then :verify, then :quit.
    let stdin = "clone and inspect a repo\nnow summarize what you found\n:verify\n:quit\n";
    let (ok, out) = run(
        &[
            "session",
            "--account",
            "dga1_demo",
            "--budget",
            "10",
            "--caps",
            "shell",
            "--replay",
            &resp,
            "--out",
            out_file.to_str().unwrap(),
        ],
        stdin,
        &[],
    );
    assert!(ok, "session exited non-zero:\n{out}");

    // Each goal ran one admitted shell op, narrated as a receipted step.
    assert!(out.contains("step  1"), "no narrated step:\n{out}");
    assert!(out.contains("admitted"), "no admitted action:\n{out}");

    // THE BUDGET DRAWS DOWN ACROSS GOALS: goal 1 → 1¢, goal 2 → 2¢ (no reset).
    assert!(
        out.contains("consumed 1¢ / 10¢"),
        "goal 1 should consume 1¢:\n{out}"
    );
    assert!(
        out.contains("consumed 2¢ / 10¢"),
        "goal 2 should consume 2¢ cumulatively:\n{out}"
    );

    // :verify re-witnessed the WHOLE session (both goals in one chain).
    assert!(
        out.contains("the WHOLE session re-witnesses: 2 signed action(s)"),
        "session verify missing/ wrong count:\n{out}"
    );

    // The artifact was written and re-witnesses offline via the existing verifier.
    assert!(out_file.exists(), "no session.json written:\n{out}");
    let (vok, vout) = run(&["verify", out_file.to_str().unwrap()], "", &[]);
    assert!(vok, "verify of the session artifact failed:\n{vout}");
    assert!(
        vout.contains("re-verifies"),
        "verify verdict missing:\n{vout}"
    );
}

// ── (1) the SSH attach: a forced-command drop-in, scoped to ONE account ──────────

#[test]
fn ssh_attach_one_shot_runs_the_goal_scoped_to_the_account() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // `ssh dga1_alice@host "do a thing"` → the forced command runs `attach`, the
    // goal arrives as SSH_ORIGINAL_COMMAND, runs once, prints the proof, exits.
    let (ok, out) = run(
        &[
            "attach",
            "--account",
            "dga1_alice",
            "--budget",
            "5",
            "--caps",
            "shell",
            "--replay",
            &resp,
        ],
        "", // no interactive stdin — the one-shot path
        &[("SSH_ORIGINAL_COMMAND", "do a single thing")],
    );
    assert!(ok, "attach exited non-zero:\n{out}");
    assert!(out.contains("ATTACHED"), "no attach banner:\n{out}");
    assert!(
        out.contains("dga1_alice") && out.contains("agent:session:dga1_alice"),
        "session not scoped to the account:\n{out}"
    );
    assert!(out.contains("admitted"), "the goal did not run:\n{out}");
    assert!(
        out.contains("the WHOLE session re-witnesses: 1 signed action(s)"),
        "attach session did not verify:\n{out}"
    );
}

// ── (3) the cap-scoping tooth: an out-of-bundle tool is refused in the REPL ──────

#[test]
fn an_out_of_bundle_tool_is_refused_in_the_session() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // The bundle grants `fs` but NOT `shell`; the recorded brain calls `shell`.
    let stdin = "try to run a shell command\n:quit\n";
    let (ok, out) = run(
        &[
            "session",
            "--account",
            "dga1_locked",
            "--budget",
            "10",
            "--caps",
            "fs",
            "--replay",
            &resp,
        ],
        stdin,
        &[],
    );
    assert!(ok, "session exited non-zero:\n{out}");
    assert!(
        out.contains("cap-refused") && out.contains("outside the cap bundle"),
        "the out-of-bundle shell was not refused:\n{out}"
    );
    // No money/effect, but the session still re-witnesses (a refusal leaves no receipt).
    assert!(
        out.contains("0 signed action(s)") || out.contains("re-witnesses"),
        "session should still verify after a refusal:\n{out}"
    );
}

// ── (5) multi-user isolation: each account its own budget + identity ─────────────

#[test]
fn two_accounts_are_isolated_by_their_own_budget_and_identity() {
    let dir = tmpdir();
    let resp = write_resp(dir.as_path());

    // Alice has a 1¢ ceiling → one op exhausts her.
    let (aok, aout) = run(
        &[
            "attach",
            "--account",
            "dga1_alice",
            "--budget",
            "1",
            "--caps",
            "shell",
            "--replay",
            &resp,
        ],
        "",
        &[("SSH_ORIGINAL_COMMAND", "work")],
    );
    assert!(aok);
    assert!(
        aout.contains("consumed 1¢ / 1¢") && aout.contains("headroom 0¢"),
        "alice not bounded by her own ceiling:\n{aout}"
    );
    assert!(aout.contains("agent:session:dga1_alice"));

    // Bob has a 100¢ ceiling → the same op leaves him almost full. His budget and
    // identity are entirely his own — alice's exhaustion does not touch him.
    let (bok, bout) = run(
        &[
            "attach",
            "--account",
            "dga1_bob",
            "--budget",
            "100",
            "--caps",
            "shell",
            "--replay",
            &resp,
        ],
        "",
        &[("SSH_ORIGINAL_COMMAND", "work")],
    );
    assert!(bok);
    assert!(
        bout.contains("consumed 1¢ / 100¢") && bout.contains("headroom 99¢"),
        "bob's budget is not his own:\n{bout}"
    );
    assert!(bout.contains("agent:session:dga1_bob"));
}
