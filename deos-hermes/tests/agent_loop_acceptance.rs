//! THE CONSOLIDATED AGENT-LOOP ACCEPTANCE TEST — one running multi-turn session
//! proving, together, that the confined Hermes genuinely operates UNDER the
//! capability, metered.
//!
//! The other test files each exercise one facet (the seam polarity, the wire
//! shape, the streaming dock, the confined PD launch). THIS test is the single
//! DONE bar: a real [`AcpClient`] drives a sequence of prompts over ONE
//! persistent [`HermesGateway`] (the same confinement the cockpit dock reclaims
//! between turns), and asserts in one running session that —
//!
//!   (a) N in-mandate tool-calls are ADMITTED and each leaves a real receipt
//!       (a hex-encoded 32-byte turn hash from a committed turn on the verified
//!       executor);
//!   (b) the budget DEPLETES MONOTONICALLY turn-over-turn (the per-tool counter
//!       only ever climbs, and `remaining` only ever falls, across prompts);
//!   (c) a call past the rate budget is REFUSED in-band, FAIL-CLOSED (no turn,
//!       the counter does not advance), and the refusal NAMES the rate leg;
//!   (d) a call past the session DEADLINE is refused in-band (the deadline leg);
//!   (e) an OUT-OF-MANDATE call — a tool deos denied entirely (rate-0 grant, the
//!       whole-class deny) — is refused in-band on its FIRST attempt, fail-closed.
//!
//! Every step is a real turn-or-refusal through the proven `ToolGateway` over the
//! REAL verified executor (this crate embeds `libdregg_lean.a`). The agent body is
//! the faithful [`MockHermesPeer`] replaying `acp_adapter`'s ACP wire shapes — the
//! confined brain is stood-in, the gate + executor + ACP wire are real.

use std::sync::{Arc, RwLock};

use deos_hermes::{
    AcpClient, GrantRegistry, HermesGateway, PermissionOutcome, ToolKind, MockHermesPeer,
    ScriptedCall,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGrant};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// Assert an outcome is an ALLOW with a genuine hex turn receipt; return the
/// remaining budget it reported.
fn expect_receipt(label: &str, outcome: &PermissionOutcome) -> i64 {
    match outcome {
        PermissionOutcome::Allow {
            receipt, remaining, ..
        } => {
            assert_eq!(receipt.len(), 64, "{label}: receipt is a hex 32-byte turn hash");
            assert!(
                receipt.chars().all(|c| c.is_ascii_hexdigit()),
                "{label}: receipt id is hex ({receipt})"
            );
            *remaining
        }
        other => panic!("{label}: expected an ALLOW with a receipt, got {other:?}"),
    }
}

/// Drive ONE prompt over the mock peer through a moved-in gateway, returning the
/// (spent) gateway and the run. The gateway persists across prompts — the live
/// dock reclaims it between turns so budgets carry over, which is exactly what
/// makes the depletion MONOTONIC across the whole session.
fn drive(
    gateway: HermesGateway<'static>,
    session_id: &str,
    prompt: &str,
    script: Vec<ScriptedCall>,
    clock: i64,
) -> (HermesGateway<'static>, deos_hermes::PromptRun) {
    let peer = MockHermesPeer::new(session_id, script);
    let mut client = AcpClient::new(peer, gateway, clock);
    let run = client
        .run_prompt("/deos/confined", prompt)
        .expect("the ACP loop runs end-to-end over the mock peer");
    (client.into_gateway(), run)
}

#[test]
fn confined_agent_runs_a_metered_receipted_multi_turn_session() {
    let (rt, root) = grantor();
    // Leak the runtime so the persistent gateway is `'static` across the session's
    // prompts (the dock holds it the same way live).
    let rt: &'static AgentRuntime = Box::leak(Box::new(rt));

    // deos's confinement for this session:
    //   * `terminal` tightened to rate 3 (so the session can EXHAUST it and we
    //     witness a fail-closed rate refusal turn-over-turn);
    //   * `image_generate` DENIED ENTIRELY (rate 0 — an out-of-mandate tool);
    //   * the session mandate expires at height 1000 (so a late call is refused).
    // Apply the curated standard tightenings FIRST, then OUR session-specific
    // overrides on top (with_tool_grant is last-wins), so `terminal` ends at the
    // rate-3 we want to exhaust (not the standard rate-5 floor).
    let registry = GrantRegistry::default_for_session(1000)
        .with_standard_tool_grants(1000)
        .with_tool_grant("terminal", 3, 1000)
        // A whole-tool deny: deos grants `image_generate` a rate of 0 — the agent
        // is NOT mandated to use it at all. The first attempt fails closed.
        .with_grant_for_tool_deny("image_generate");
    let mut gateway = HermesGateway::new(rt, root, registry);

    // ════ TURN 1 — three in-mandate calls: a search + two builds ════
    // (web_search rides the Fetch floor; the two terminals deplete the rate-3
    // terminal mandate to 2 used / 1 remaining.)
    let (gw, run1) = drive(
        gateway,
        "sess-acc",
        "search for dregg, then build and test it",
        vec![
            ScriptedCall::new("web_search", serde_json::json!({"query": "dregg ocap"})),
            ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
            ScriptedCall::new("terminal", serde_json::json!({"command": "cargo test"})),
        ],
        100,
    );
    gateway = gw;

    // (a) All three were ADMITTED, each with a real receipt.
    assert_eq!(run1.verdicts.len(), 3, "three gated tool-calls in turn 1");
    let term_rem_1 = {
        let mut last_term_remaining = None;
        for (call, outcome) in &run1.verdicts {
            let remaining = expect_receipt(&format!("turn1 {}", call.name), outcome);
            if call.name == "terminal" {
                last_term_remaining = Some(remaining);
            }
        }
        last_term_remaining.expect("two terminal calls in turn 1")
    };
    // The terminal mandate (rate 3) shows 2 spent, 1 remaining after turn 1.
    assert_eq!(gateway.calls_made_for_tool("terminal"), 2, "two terminal calls spent");
    assert_eq!(term_rem_1, 1, "rate-3 terminal: one call left after turn 1");
    // web_search rode the Fetch floor and metered there.
    assert_eq!(gateway.calls_made(ToolKind::Fetch), 1);

    // ════ TURN 2 — same persistent gateway: ONE more build (the LAST allowed),
    // then a SECOND build that EXHAUSTS the terminal rate and is refused. ════
    let spent_before = gateway.calls_made_for_tool("terminal");
    let (gw, run2) = drive(
        gateway,
        "sess-acc",
        "build once more, then try again",
        vec![
            ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
            ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build --release"})),
        ],
        200,
    );
    gateway = gw;

    assert_eq!(run2.verdicts.len(), 2, "two gated tool-calls in turn 2");
    // The first build is the 3rd (and last) allowed terminal call — receipt, 0 left.
    let last_remaining = expect_receipt("turn2 terminal (last allowed)", &run2.verdicts[0].1);
    assert_eq!(last_remaining, 0, "rate-3 terminal fully spent after this call");

    // (c) The SECOND build is over rate — REFUSED in-band, fail-closed, naming the
    //     rate leg. No turn, no spend.
    match &run2.verdicts[1].1 {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(
                reason.contains("rate exhausted"),
                "the over-budget terminal names the rate leg: {reason}"
            );
        }
        other => panic!("the over-budget terminal must be refused in-band, got {other:?}"),
    }

    // (b) MONOTONIC depletion: the counter only climbed (2 → 3) and the refusal did
    //     NOT advance it past the ceiling.
    assert!(
        gateway.calls_made_for_tool("terminal") > spent_before,
        "the counter advanced across the turn"
    );
    assert_eq!(
        gateway.calls_made_for_tool("terminal"),
        3,
        "exactly the rate-3 ceiling reached; the refused call did NOT advance it"
    );

    // ════ TURN 3 — the OUT-OF-MANDATE tool: `image_generate` is denied entirely
    // (rate 0). Its FIRST attempt fails closed. ════
    let (gw, run3) = drive(
        gateway,
        "sess-acc",
        "generate an image",
        vec![ScriptedCall::new(
            "image_generate",
            serde_json::json!({"prompt": "a goose"}),
        )],
        300,
    );
    gateway = gw;

    assert_eq!(run3.verdicts.len(), 1);
    // (e) Out-of-mandate: refused in-band on the FIRST attempt, fail-closed.
    match &run3.verdicts[0].1 {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(
                reason.contains("rate exhausted"),
                "the denied-class tool is refused (rate-0 mandate): {reason}"
            );
        }
        other => panic!("an out-of-mandate tool must be refused in-band, got {other:?}"),
    }
    // It never ran — the denied class's counter stays at 0.
    assert_eq!(
        gateway.calls_made_for_tool("image_generate"),
        0,
        "the denied tool never advanced its counter (fail-closed)"
    );

    // ════ TURN 4 — PAST DEADLINE: a perfectly in-scope, in-budget read_file
    // presented after the session mandate expires (clock 2000 > deadline 1000) is
    // refused in-band, naming the deadline leg. ════
    let peer = MockHermesPeer::new(
        "sess-acc",
        vec![ScriptedCall::new("read_file", serde_json::json!({"path": "README.md"}))],
    );
    // Start this prompt's clock ABOVE the mandate deadline (1000). The driver bumps
    // the clock per permission, so the read lands at > 1000.
    let mut client = AcpClient::new(peer, gateway, 2000);
    let run4 = client
        .run_prompt("/deos/confined", "read the readme")
        .expect("the ACP loop runs end-to-end even when the gate refuses");
    gateway = client.into_gateway();

    assert_eq!(run4.verdicts.len(), 1);
    // (d) Past the deadline: refused in-band, naming the deadline leg.
    match &run4.verdicts[0].1 {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(
                reason.contains("past deadline"),
                "the late read names the deadline leg: {reason}"
            );
        }
        other => panic!("a past-deadline call must be refused in-band, got {other:?}"),
    }
    assert_eq!(
        gateway.calls_made(ToolKind::Read),
        0,
        "the late read never committed a turn (fail-closed)"
    );

    // ════ THE WHOLE-SESSION INVARIANT — over every turn driven on this ONE
    // persistent gateway, the only counters that advanced are the mandated ones,
    // and the terminal mandate sits exactly at its ceiling (depleted, not over). ══
    assert_eq!(gateway.calls_made_for_tool("terminal"), 3, "terminal at its rate-3 ceiling");
    assert_eq!(gateway.calls_made(ToolKind::Fetch), 1, "one web_search rode the Fetch floor");
    // A further terminal call now — still refused: the ceiling persists across the
    // whole session (the confinement is a session-wide mandate, not per-prompt).
    let peer = MockHermesPeer::new(
        "sess-acc",
        vec![ScriptedCall::new("terminal", serde_json::json!({"command": "echo still denied"}))],
    );
    let mut client = AcpClient::new(peer, gateway, 400);
    let run5 = client.run_prompt("/deos/confined", "one more build").unwrap();
    assert!(
        matches!(run5.verdicts[0].1, PermissionOutcome::Reject { .. }),
        "the terminal mandate stays exhausted for the rest of the session"
    );
}

/// A direct (no-ACP) restatement of the SCOPE leg: present a grant whose id the
/// worker is NOT scoped to, and the gate refuses with `OutOfScope`. This exercises
/// the `describe_refusal` OutOfScope arm the ACP seam can't reach (the bridge only
/// ever presents the grant's own id). It proves the third mandate leg — scope —
/// is live, fail-closed, in the same gateway.
#[test]
fn out_of_scope_tool_id_is_refused_by_the_gate() {
    use dregg_sdk::{ToolCallError, ToolGateway};
    let (rt, root) = grantor();
    let grant = ToolGrant {
        tool_id: 77,
        rate_limit: 5,
        deadline: 1000,
        tool_method: "tool.execute".to_string(),
    };
    let mut gw = ToolGateway::admit(&rt, &root, grant).expect("admit a scoped worker");
    // Present a DIFFERENT tool id than the one granted (88 != 77): out of scope.
    match gw.invoke(88, 10, vec![]) {
        Err(ToolCallError::Refused(refusal)) => {
            assert_eq!(
                refusal,
                dregg_sdk::GatewayRefusal::OutOfScope {
                    presented: 88,
                    granted: 77,
                },
                "the gate refuses an out-of-scope tool id in-band"
            );
        }
        other => panic!("expected an in-band OutOfScope refusal, got {other:?}"),
    }
    assert_eq!(gw.calls_made(), 0, "the out-of-scope call advanced no counter");
}
