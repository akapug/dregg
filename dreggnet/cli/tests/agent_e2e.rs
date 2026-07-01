//! End-to-end test for the `dregg-cloud agent` verbs against the `dregg-cloud` binary —
//! the Verifiable Agent Cloud, runnable in one command.
//!
//! `dregg-cloud agent deploy` an agent with a small budget + a 2-service cap bundle,
//! plus an attenuated sub-agent; assert the run is cap-gated (an out-of-bundle
//! invoke REFUSED), budget-bounded (the runaway contained at the ceiling), and
//! receipted; then `dregg-cloud agent verify` re-witnesses the chain + the bound.

use std::process::Command;

/// Run `dregg-cloud --state-dir <dir> agent <args...>` and return (success, stdout).
fn agent(dir: &std::path::Path, args: &[&str]) -> (bool, String) {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let out = Command::new(bin)
        .arg("--state-dir")
        .arg(dir)
        .arg("agent")
        .args(args)
        .output()
        .expect("run dregg-cloud agent");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
    )
}

#[test]
fn agent_deploy_runs_capped_metered_receipted_then_verifies() {
    let dir = tempfile::tempdir().unwrap();

    // Deploy an agent with a 6-unit budget + the default 2-service bundle, plus an
    // attenuated sub-agent. The mock-LLM plan attempts an out-of-bundle invoke and
    // a runaway, so the cap-gate + the budget ceiling both bite.
    let (ok, out) = agent(
        dir.path(),
        &[
            "deploy",
            "--id",
            "agent:e2e",
            "--budget",
            "6",
            "--cost",
            "1",
            "--subagent",
        ],
    );
    assert!(ok, "deploy failed:\n{out}");

    // Cap-gated: the out-of-bundle `invoke:exfiltrate` is refused, never reached.
    assert!(out.contains("cap-refused"), "no cap-gate in output:\n{out}");
    // Budget-bounded: the consumed total is pinned at the ceiling, the rest contained.
    assert!(
        out.contains("consumed 6 / 6 DREGG"),
        "budget not drawn to the ceiling:\n{out}"
    );
    assert!(
        out.contains("budget-bound"),
        "no budget bound in output:\n{out}"
    );
    // Receipted: a receipt chain with a tip + signer.
    assert!(
        out.contains("receipt chain: 6 receipts"),
        "no receipt chain:\n{out}"
    );
    assert!(out.contains("tip "), "no chain tip:\n{out}");
    // The could-have bound surfaced.
    assert!(
        out.contains("headroom 0 DREGG un-drawn"),
        "no could-have bound:\n{out}"
    );
    // The attenuated sub-agent ran with half the budget, narrower caps.
    assert!(out.contains("agent:e2e/child"), "no sub-agent:\n{out}");
    assert!(
        out.contains("(≤ parent 6)"),
        "child budget not attenuated:\n{out}"
    );

    // Verify re-witnesses the parent run without trusting the host.
    let (ok, vout) = agent(dir.path(), &["verify", "agent:e2e"]);
    assert!(ok, "verify failed:\n{vout}");
    assert!(vout.contains("✓ verified"), "verify did not pass:\n{vout}");
    assert!(
        vout.contains("consumed  6 / 6 DREGG"),
        "verify bound wrong:\n{vout}"
    );

    // The sub-agent also re-witnesses (it cannot exceed the parent).
    let (ok, cout) = agent(dir.path(), &["verify", "agent:e2e/child"]);
    assert!(ok, "child verify failed:\n{cout}");
    assert!(
        cout.contains("✓ verified"),
        "child verify did not pass:\n{cout}"
    );
}
