//! `hermes` — run dregg-agent **DIRECTLY with Nous Hermes**, two ways. The actual
//! Hermes, not a lookalike.
//!
//! The hackathon stack (`docs/HACKATHON-STACK.md`) serves Hermes two ways, and
//! dregg drives BOTH behind the same cap · budget · receipt rail:
//!
//! ## (a) The Hermes **model** over the Nous Portal — [`OpenAICompatBrain`]
//!
//! Hermes is served through the **Nous Portal** proxy. The real `hermes` CLI
//! starts it with **`hermes proxy start`** ("Run a local HTTP server that forwards
//! OpenAI-compatible requests to an OAuth-authenticated provider … External apps
//! can point at the proxy with any bearer token") — it binds [`NOUS_PORTAL_BASE`]
//! (`http://127.0.0.1:8645/v1`, provider `nous` = Nous Portal) by default. The
//! existing [`crate::brain::OpenAICompatBrain`] needs no change — it takes a base
//! URL + model + key, so pointing it at the proxy makes the **actual Hermes
//! model** ([`HERMES_PORTAL_MODEL`] = `hermes-agent`) drive the reason→act→observe
//! loop over native OpenAI `tool_calls`, cap-bounded + budget-metered + receipted.
//! The CLI exposes this as `dregg-agent run --brain hermes` (or `--llm-base … …`).
//! [`nous_portal_key`] resolves the bearer from `NOUS_PORTAL_KEY` /
//! `~/.nousportalkey` (the proxy accepts any bearer and attaches the real creds).
//!
//! ## (b) The real **`hermes` CLI** as the confined harness — [`crate::harness`]
//!
//! The most-direct integration: run the **actual `hermes` harness** (the `hermes`
//! CLI, with its installed **skills** — including the real Stripe Skills
//! `stripe-projects` / `stripe-link-cli`) as the untrusted brain behind
//! [`crate::harness::HarnessBrain`]. The harness reasons + calls its own skills;
//! dregg **intercepts every skill/tool-call** through the cap · budget · receipt
//! rail. The harness holds its own subscription auth *inside its subprocess* (dregg
//! never sees a key). This uses the real Hermes skills format directly (vs
//! re-wrapping), and is `dregg-agent run --brain hermes-cli`.
//!
//! ### The wire — an ndjson tool-call protocol (the adapter built; the bridge noted)
//!
//! The confined-harness transport ([`crate::harness::SubprocessHarness`]) speaks a
//! lowest-common-denominator **ndjson** line protocol (one tool-call JSON object
//! per stdout line; one verdict JSON line back on stdin — see [`crate::harness`]).
//! The real `hermes` CLI's machine-driven confined protocol is **`hermes acp`**
//! ([`HERMES_ACP_CMD`]) — Agent Client Protocol, JSON-RPC over stdio (the
//! `request_permission` round-trip the [`crate::harness`] shim generalizes). So the
//! **production tool-bridge** (an `hermes acp` ↔ ndjson adapter) is the **reviewed
//! wiring step**: point [`HERMES_CMD_ENV`] (`DREGG_HERMES_CMD`) at a thin wrapper
//! that bridges it, and [`spawn_hermes_harness`] drives the real CLI live, each
//! skill-call intercepted through the gate. We never auto-spawn a bare `hermes`
//! (it is not an ndjson stream); absent the bridge, the offline path replays
//! [`recorded_hermes_demo_calls`] (hermes-shaped skill calls) so the confinement
//! teeth are visible today — honestly labelled, never a faked live success.

use crate::brain::{HERMES_PORTAL_MODEL, NOUS_PORTAL_BASE, ProviderKey};
use crate::harness::SubprocessHarness;

// ───────────────────────────── (a) the Nous Portal model ─────────────────────

/// The env var holding the Nous Portal bearer key (`--brain hermes`).
pub const NOUS_PORTAL_KEY_ENV: &str = "NOUS_PORTAL_KEY";

/// The real `hermes` command that serves the Hermes model at [`NOUS_PORTAL_BASE`]
/// (`--brain hermes` points there): a local OpenAI-compatible proxy onto the Nous
/// Portal, binding `127.0.0.1:8645` by default.
pub const HERMES_PROXY_CMD: &str = "hermes proxy start";

/// The conventional path of the Nous Portal key in the operator's home.
pub fn nous_portal_key_path() -> Option<std::path::PathBuf> {
    std::env::var_os("HOME").map(|h| std::path::Path::new(&h).join(".nousportalkey"))
}

/// Resolve the Nous Portal bearer key: `NOUS_PORTAL_KEY` env, then
/// `~/.nousportalkey`. Trimmed, non-empty, or `None`. Returned as a confined
/// [`ProviderKey`] (redacted `Debug`, rides only in the auth header).
pub fn nous_portal_key() -> Option<ProviderKey> {
    ProviderKey::from_env("nous-portal", NOUS_PORTAL_KEY_ENV)
        .or_else(|| ProviderKey::from_file("nous-portal", nous_portal_key_path()?))
}

/// `true` iff a Nous Portal key is resolvable (the `--brain hermes` live leg is armed).
pub fn portal_key_present() -> bool {
    nous_portal_key().is_some()
}

/// A one-line label for the Nous Portal (Hermes model) leg — armed, or what unlocks it.
pub fn portal_status_line() -> String {
    if portal_key_present() {
        format!(
            "LIVE — Nous Portal key present; Hermes model `{HERMES_PORTAL_MODEL}` @ \
             {NOUS_PORTAL_BASE} (serve it with `{HERMES_PROXY_CMD}`)"
        )
    } else {
        format!(
            "RECORDED — run `{HERMES_PROXY_CMD}` (serves {NOUS_PORTAL_BASE}) + set \
             {NOUS_PORTAL_KEY_ENV}/~/.nousportalkey (any bearer works) to drive the live Hermes \
             model `{HERMES_PORTAL_MODEL}` (or use --replay)"
        )
    }
}

// ───────────────────────────── (b) the real `hermes` CLI ─────────────────────

/// The `hermes` CLI program name (the real Hermes harness).
pub const HERMES_CLI: &str = "hermes";

/// Env override for the harness launch command — point this at a thin `hermes`
/// wrapper that speaks the ndjson tool protocol for a genuine live run (the
/// reviewed tool-bridge step). When set, [`hermes_launch`] uses it verbatim.
pub const HERMES_CMD_ENV: &str = "DREGG_HERMES_CMD";

/// Env override for the harness launch arguments (whitespace-separated). Defaults
/// to passing the goal as a single argument.
pub const HERMES_ARGS_ENV: &str = "DREGG_HERMES_ARGS";

/// The real `hermes` machine-driven confined protocol: Agent Client Protocol
/// (JSON-RPC over stdio). The bridge to the ndjson tool protocol the confined
/// harness speaks is the reviewed wiring step (set [`HERMES_CMD_ENV`]).
pub const HERMES_ACP_CMD: &str = "hermes acp";

/// `true` iff the real `hermes` CLI resolves on PATH (a `--version` probe).
pub fn hermes_cli_on_path() -> bool {
    std::process::Command::new(HERMES_CLI)
        .arg("--version")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// A one-line label for the `hermes` CLI (confined-harness) leg.
pub fn hermes_cli_status_line() -> String {
    let explicit = std::env::var(HERMES_CMD_ENV)
        .ok()
        .filter(|s| !s.trim().is_empty());
    match (explicit, hermes_cli_on_path()) {
        (Some(cmd), _) => format!(
            "LIVE — driving `{cmd}` as the confined hermes harness (ndjson tool-bridge wired)"
        ),
        (None, true) => format!(
            "RECORDED — the real `{HERMES_CLI}` CLI is on PATH; its confined protocol is \
             `{HERMES_ACP_CMD}` (JSON-RPC over stdio). Set {HERMES_CMD_ENV} to a wrapper that \
             bridges it to the ndjson tool protocol for a live confined run; replaying \
             hermes-shaped skill calls meanwhile"
        ),
        (None, false) => format!(
            "RECORDED — `{HERMES_CLI}` CLI not installed; replaying hermes-shaped skill calls. \
             Install hermes (its confined protocol is `{HERMES_ACP_CMD}`) + set {HERMES_CMD_ENV} \
             for a live run"
        ),
    }
}

/// The launch `(program, args)` for the confined hermes harness, or `None` when no
/// explicit [`HERMES_CMD_ENV`] ndjson bridge is configured (→ the offline recorded
/// demo). We deliberately do NOT auto-spawn a bare `hermes`: its confined protocol
/// is `hermes acp` (JSON-RPC), not an ndjson tool-stream, so a bare spawn would not
/// drive the harness. Point [`HERMES_CMD_ENV`] at a thin `hermes acp` ↔ ndjson
/// bridge for a genuine live run. `goal` is passed as the sole default argument
/// (the wrapper may use it however it likes) unless [`HERMES_ARGS_ENV`] overrides.
pub fn hermes_launch(goal: &str) -> Option<(String, Vec<String>)> {
    let cmd = std::env::var(HERMES_CMD_ENV).ok()?;
    let cmd = cmd.trim().to_string();
    if cmd.is_empty() {
        return None;
    }
    let args = std::env::var(HERMES_ARGS_ENV)
        .ok()
        .filter(|s| !s.trim().is_empty())
        .map(|s| s.split_whitespace().map(String::from).collect())
        .unwrap_or_else(|| vec![goal.to_string()]);
    Some((cmd, args))
}

/// Spawn the real `hermes` CLI (or the configured wrapper) as a confined
/// [`SubprocessHarness`] for `goal`. `None` when no hermes launch is available
/// (caller falls back to the recorded demo); `Some(Err)` on a spawn failure.
pub fn spawn_hermes_harness(goal: &str) -> Option<std::io::Result<SubprocessHarness>> {
    let (program, args) = hermes_launch(goal)?;
    let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
    Some(SubprocessHarness::spawn(&program, &arg_refs))
}

/// The offline **recorded demo** of hermes-shaped skill calls, in the ndjson
/// tool-call line shape the confined harness speaks. Drives a `shell` skill, the
/// two real **Stripe Skills** (`stripe_provision` then `stripe_pay`), then
/// `finish` — so the cap-gate + budget-meter + receipt teeth are visible offline.
/// Amounts are modest so a default budget admits them; the budget/cap teeth are
/// proven explicitly in the tests and the SCALE demo.
pub fn recorded_hermes_demo_calls() -> Vec<serde_json::Value> {
    use serde_json::json;
    vec![
        json!({ "tool": "shell", "cmd": "echo 'hermes operator online'" }),
        json!({
            "tool": "stripe_provision",
            "provider": "neon",
            "service": "postgres",
            "amount_cents": 190
        }),
        json!({
            "tool": "stripe_pay",
            "vendor": "openai",
            "amount_cents": 50,
            "memo": "inference"
        }),
        json!({ "tool": "finish", "summary": "provisioned neon/postgres and paid openai 50c" }),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentAction, AgentCloud, AgentSpec, ToolCall, op, verify_agent_run};
    use crate::brain::chat_completions_url;
    use crate::harness::{HarnessBrain, MockHarness};
    use crate::stripe_skills::RecordedStripeSkills;
    use crate::toolkit::Toolkit;
    use crate::tools::OperatorTools;
    use serde_json::json;

    // ── (a) the Nous Portal constants point at the actual Hermes endpoint ────────
    #[test]
    fn the_portal_constants_point_at_nous_hermes() {
        assert_eq!(NOUS_PORTAL_BASE, "http://127.0.0.1:8645/v1");
        assert_eq!(HERMES_PORTAL_MODEL, "hermes-agent");
        // The chat route is appended for the live POST.
        assert_eq!(
            chat_completions_url(NOUS_PORTAL_BASE),
            "http://127.0.0.1:8645/v1/chat/completions"
        );
    }

    // ── (b) the confined hermes harness drives the REAL Stripe Skills, gated ─────
    // A MockHarness emits the hermes skill-call shape; HarnessBrain maps each
    // through the SHARED vocabulary (the brain↔harness unification) so the
    // operator skills (shell + the two Stripe Skills) fire as cap-gated,
    // budget-drawn, receipted operator tools, and the whole run re-witnesses.
    #[test]
    fn a_confined_hermes_harness_drives_the_stripe_skills() {
        let cloud = AgentCloud::from_seed([70u8; 32]);
        let wd = std::env::temp_dir().join(format!("dregg-hermes-skills-{}", std::process::id()));
        std::fs::create_dir_all(&wd).unwrap();
        let handle = cloud
            .deploy(
                &AgentSpec::new("agent:hermes-founder", 5000)
                    .with_shell()
                    .with_stripe_provision("neon")
                    .with_stripe_pay("openai"),
            )
            .unwrap();

        // The recorded demo IS the hermes-shaped skill stream.
        let harness = MockHarness::new(recorded_hermes_demo_calls());
        let mut brain = HarnessBrain::new(harness);

        let toolkit = OperatorTools::new(Toolkit::new(), &wd)
            .with_shell(|cmd: &str, _cwd: &std::path::Path| {
                Ok(crate::tools::ShellOut {
                    exit: 0,
                    stdout: format!("ok: {cmd}"),
                    stderr: String::new(),
                    new_cwd: None,
                })
            })
            .with_stripe_skills(RecordedStripeSkills::new());
        let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);

        assert_eq!(report.admitted, 3, "shell + provision + pay all fired");
        assert_eq!(
            report.consumed,
            1 + 190 + 50,
            "the budget drew shell+provision+pay"
        );
        assert!(report.all_tools_passed(), "{:?}", report.tool_results());
        assert!(
            report
                .receipts
                .iter()
                .any(|r| r.action.starts_with("stripe_provision")),
            "the provision skill is receipted"
        );
        assert!(
            report
                .receipts
                .iter()
                .any(|r| r.action.starts_with("stripe_pay")),
            "the pay skill is receipted"
        );
        verify_agent_run(&report).expect("the confined-hermes-harness run re-witnesses");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── (b) TOOTH: a hermes skill OUTSIDE the cap bundle is REFUSED ──────────────
    #[test]
    fn an_out_of_bundle_hermes_skill_is_refused() {
        let cloud = AgentCloud::from_seed([71u8; 32]);
        let wd = std::env::temp_dir().join(format!("dregg-hermes-refuse-{}", std::process::id()));
        std::fs::create_dir_all(&wd).unwrap();
        // Granted ONLY shell — NOT pay:stripe. The harness reaching for stripe_pay
        // is refused before any money moves, no matter what the harness emits.
        let handle = cloud
            .deploy(&AgentSpec::new("agent:hermes-narrow", 5000).with_shell())
            .unwrap();
        let harness = MockHarness::new(vec![
            json!({ "tool": "stripe_pay", "vendor": "openai", "amount_cents": 50, "memo": "x" }),
            json!({ "tool": "shell", "cmd": "echo within-bundle" }),
            json!({ "tool": "finish" }),
        ]);
        let mut brain = HarnessBrain::new(harness);
        let toolkit = OperatorTools::new(Toolkit::new(), &wd)
            .with_shell(|cmd: &str, _cwd: &std::path::Path| {
                Ok(crate::tools::ShellOut {
                    exit: 0,
                    stdout: format!("ok: {cmd}"),
                    stderr: String::new(),
                    new_cwd: None,
                })
            })
            .with_stripe_skills(RecordedStripeSkills::new());
        let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);

        assert_eq!(
            report.cap_refused, 1,
            "the out-of-bundle pay skill is refused"
        );
        assert_eq!(report.admitted, 1, "only the granted shell skill ran");
        // The harness was told of the refusal in-band.
        let verdicts = brain.transport().verdicts_seen();
        assert!(
            verdicts.iter().any(|v| v.contains("\"admitted\":false")),
            "the refusal was fed back to the harness: {verdicts:?}"
        );
        verify_agent_run(&report).expect("the run re-witnesses");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── the harness vocabulary now maps the operator skills (the unification) ────
    #[test]
    fn the_harness_maps_hermes_operator_skills() {
        // shell skill → an Op action (was previously unmappable on the harness path).
        let report = {
            let cloud = AgentCloud::from_seed([72u8; 32]);
            let wd = std::env::temp_dir().join(format!("dregg-hermes-map-{}", std::process::id()));
            std::fs::create_dir_all(&wd).unwrap();
            let handle = cloud
                .deploy(&AgentSpec::new("agent:hermes-shell", 10).with_shell())
                .unwrap();
            let harness = MockHarness::new(vec![
                // an alias the canonicalizer folds to `shell`
                json!({ "tool": "bash", "cmd": "echo aliased" }),
                json!({ "tool": "finish" }),
            ]);
            let mut brain = HarnessBrain::new(harness);
            let toolkit = OperatorTools::new(Toolkit::new(), &wd).with_shell(
                |cmd: &str, _cwd: &std::path::Path| {
                    Ok(crate::tools::ShellOut {
                        exit: 0,
                        stdout: format!("ran {cmd}"),
                        stderr: String::new(),
                        new_cwd: None,
                    })
                },
            );
            let r = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);
            std::fs::remove_dir_all(&wd).ok();
            r
        };
        assert_eq!(report.admitted, 1, "the aliased shell skill mapped + ran");
        assert!(report.receipts[0].action.starts_with(op::SHELL));
    }

    // ── hermes_launch honors the explicit wrapper override ───────────────────────
    #[test]
    fn recorded_demo_calls_are_wellformed_hermes_skill_calls() {
        let calls = recorded_hermes_demo_calls();
        assert_eq!(calls.len(), 4);
        // Each carries a string "tool" field (the ndjson contract).
        for c in &calls {
            assert!(c.get("tool").and_then(|t| t.as_str()).is_some());
        }
        // The two Stripe Skills are present.
        assert!(calls.iter().any(|c| c["tool"] == "stripe_provision"));
        assert!(calls.iter().any(|c| c["tool"] == "stripe_pay"));

        // The first call maps to a shell Op via the shared brain↔harness vocabulary.
        let first = &calls[0];
        let canon = crate::brain::canonical_tool(first.get("tool").unwrap().as_str().unwrap());
        let action = crate::brain::map_tool_call(canon, first);
        assert!(
            matches!(action, Some(AgentAction::Op(ToolCall { ref tool, .. })) if tool == op::SHELL)
        );
    }
}
