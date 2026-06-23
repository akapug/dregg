//! THE HANDS, PROVEN BY RUNNING — a confined Hermes agent runs JavaScript to
//! crawl + act on deos, bounded by its `held`, over-reach refused.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent`
//! (the default `cargo test` is mozjs-free — this file only compiles under the
//! `js-agent` feature, which pulls deos-js / real SpiderMonkey.)
//!
//! Three things proven:
//!   (a) CRAWL — the agent's JS reads the image (`deos.world.cells()` /
//!       `cell.reflect()`): a read, NO turn, NO receipt.
//!   (b) ACT — the agent's JS fires an affordance whose `required` its `held`
//!       satisfies → a REAL verified turn → a receipt, accounted as the AGENT'S
//!       OWN cell (the confused-deputy property).
//!   (c) OVER-REACH REFUSED — JS that fires past the agent's `held` (a
//!       Proof-gated affordance held only at Signature) is refused in-band (a
//!       JS-observable `-1`), NO turn, NO receipt.
//!
//! The `run_js` tool-call ITSELF is admitted by the proven `HermesGateway` as a
//! normal scoped, rate-limited `ToolGrant` (the accountability turn), and the
//! deos-js runtime is mounted under the AGENT'S `held` — never root (the
//! `docs/deos/AGENT-CONFINEMENT-REDTEAM.md` invariant).

#![cfg(feature = "js-agent")]

use std::sync::{Arc, RwLock};

use deos_hermes::run_js::RunJsTool;
use deos_hermes::{GrantRegistry, HermesGateway, ToolCallRequest};
use deos_js::applet::pack_u64;
use deos_js::JsRuntime;
use dregg_cell::AuthRequired;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

/// deos the grantor: the runtime that admits the agent's `run_js` worker and runs
/// its accountability turns.
fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// The agent's `run_js` tool over ITS OWN world: a Signature-held agent (broad —
/// it can drive its `assist` affordance — but NOT root: it cannot reach a
/// Proof-only `escalate`). The applet cell is the agent's own cell.
fn agent_tool() -> RunJsTool {
    RunJsTool::new(
        // The agent's mandate authority — broad over its own world, NOT root.
        AuthRequired::Signature,
        [0x42; 32], // the agent's public key (its cell == the agent)
        [0x01; 32], // the agent's token id
        // Seed the counter slot at 0.
        vec![(0, pack_u64(0))],
        // The agent's affordance surface:
        //   * `assist` — gated Signature: the agent's `held` satisfies it → fires.
        //   * `escalate` — gated Proof: the agent's `held` does NOT satisfy it →
        //     the over-reach the cap tooth refuses in-band.
        vec![
            ("assist".to_string(), AuthRequired::Signature),
            ("escalate".to_string(), AuthRequired::Proof),
        ],
    )
}

/// A scoped, rate-limited `run_js` grant for the agent (the accountability
/// mandate the gateway meters the tool-call on).
fn session_registry() -> GrantRegistry {
    GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000)
}

// ──────── (a) CRAWL + (b) ACT + (c) OVER-REACH, on ONE shared engine ─────────
//
// SpiderMonkey's `JSEngine::init()` is PROCESS-GLOBAL and one-shot, so the two
// JS-running scenarios share ONE `JsRuntime` (the host owns engine lifecycle and
// threads it through `RunJsTool::run_on`). Each `eval` runs on a fresh global, so
// the runtime is reused soundly. Both scenarios live in one `#[test]` so the
// engine is initialised exactly once even under cargo's parallel test threads.

#[test]
fn agent_runs_js_to_crawl_act_and_is_bounded_by_its_held() {
    let (rt, root) = grantor();
    let mut gw = HermesGateway::new(&rt, root, session_registry());
    let tool = agent_tool();

    // ONE process-global SpiderMonkey engine, shared across both scenarios.
    let mut js = JsRuntime::new().expect("boot SpiderMonkey once");

    // ── (a) CRAWL + (b) ACT ──────────────────────────────────────────────────
    // The agent's JS: CRAWL (read the image — `deos.world.cells()` enumerates the
    // agent's own ledger; a `reflect()` reads a cell's substances — NO turn), then
    // ACT (fire `assist`, gated Signature, which the agent's Signature `held`
    // satisfies — a REAL verified turn). The script returns the counter after.
    let crawl_act = r#"
        var app = deos.applet({ affordances: ["assist", "escalate"] });
        // (a) CRAWL — a read, confers no authority, leaves no receipt.
        var cells = deos.world.cells();          // every cell on the agent's ledger
        var n = cells.length;                    // the agent crawled its world
        var reflected = deos.cell(cells[0]).reflect();  // the four substances
        // (b) ACT — fire `assist` (+5). A real cap-gated verified turn.
        var after = app.assist(5);
        after;                                   // the counter after the fire
    "#;
    let call1 = ToolCallRequest::new(
        "s",
        "tc-runjs-1",
        "run_js",
        serde_json::json!({ "script": "assist+crawl" }),
    );
    let o1 = tool
        .run_on(&mut js, &mut gw, &call1, 50, crawl_act)
        .expect("run_js boots");

    // The `run_js` tool-call itself was admitted accountably (a metered, receipted
    // ToolGrant turn) — the agent is granted its hands this turn.
    assert!(
        o1.tool_admitted(),
        "the run_js tool-call is admitted by the gateway (the accountability turn): {:?}",
        o1.tool_outcome
    );
    assert_eq!(
        gw.calls_made_for_tool("run_js"),
        1,
        "the run_js call is metered — every agent action is receipted, never free"
    );
    assert!(
        o1.js_error.is_none(),
        "the agent's JS ran cleanly: {:?}",
        o1.js_error
    );
    // (b) ACT — exactly one affordance fire committed a REAL verified turn, leaving
    // a receipt (the rewindable audit tape). The counter moved 0 → 5.
    assert_eq!(
        o1.fires_committed, 1,
        "the agent's JS fired one affordance = one verified turn, accounted as the agent"
    );
    assert_eq!(
        o1.receipts.len(),
        1,
        "the committed fire left a real receipt (audit + rewind anchor)"
    );
    assert_eq!(
        o1.result,
        Some(5),
        "the substance moved: the counter the agent drove is 5 after a +5 fire"
    );

    // ── (c) OVER-REACH REFUSED ───────────────────────────────────────────────
    // The agent's JS reaches for `escalate` — a Proof-gated affordance. The agent
    // only HOLDS Signature, so the cap tooth refuses the fire IN-BAND: deos-js's
    // `__deos_fire` returns -1 (an expected, JS-observable refusal), NO turn, NO
    // receipt. (A fresh applet per call → the over-reach starts from a clean tape.)
    let over_reach = r#"
        var app = deos.applet({ affordances: ["assist", "escalate"] });
        var r = app.escalate(99);   // OVER-REACH: Proof required, only Signature held
        r;                          // -1 (refused), not a committed counter
    "#;
    let call2 = ToolCallRequest::new(
        "s",
        "tc-runjs-2",
        "run_js",
        serde_json::json!({ "script": "escalate" }),
    );
    let o2 = tool
        .run_on(&mut js, &mut gw, &call2, 51, over_reach)
        .expect("run_js boots");

    // The tool-call itself is still admitted (the agent IS granted run_js — the
    // membrane bound is on what the JS can FIRE, not on running JS at all).
    assert!(
        o2.tool_admitted(),
        "run_js is granted (the bound is on the fire, not on running JS)"
    );
    // THE BOUND: the over-reach committed NOTHING. No turn, no receipt — the cap
    // tooth refused in-band. The JS saw the refusal as -1.
    assert_eq!(
        o2.fires_committed, 0,
        "OVER-REACH HOLE — a Proof-gated fire committed under a Signature-held agent"
    );
    assert!(
        o2.receipts.is_empty(),
        "an over-reach leaves NO receipt — it never happened"
    );
    assert_eq!(
        o2.result,
        Some(-1),
        "the JS saw the cap-gate refusal in-band (-1), not a committed turn"
    );
    assert!(
        o2.js_error.is_none(),
        "a cap-gate refusal is an EXPECTED outcome (a -1), not a fatal eval error: {:?}",
        o2.js_error
    );
}

// ──────────────── the cap tooth in isolation (no JS round-trip) ──────────────

#[test]
fn the_cap_tooth_refuses_the_over_reach_directly_too() {
    let tool = agent_tool();
    // The Signature-held agent CAN fire `assist` (Signature-gated) ...
    assert!(
        tool.fire_direct("assist", 1).is_ok(),
        "the agent is empowered over its own world: a Signature-gated fire commits"
    );
    // ... but CANNOT fire `escalate` (Proof-gated) — the cap tooth refuses.
    match tool.fire_direct("escalate", 1) {
        Err(deos_js::FireError::Unauthorized { affordance }) => {
            assert_eq!(affordance, "escalate", "the over-reach is named + refused");
        }
        other => panic!("the Proof over-reach must be refused by the cap tooth, got {other:?}"),
    }
}
