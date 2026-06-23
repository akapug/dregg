//! THE INTERACTIVE STREAMING DOCK TEST — a typed prompt drives a live, streamed,
//! multi-turn confined-agent conversation, gated + receipted, budget depleting.
//!
//! This exercises the SAME pipeline the gpui [`AgentDockView`] drives, at the
//! model level (no gpui, so it runs hermetically in the default suite):
//!
//!   1. a typed prompt → [`AcpClient::run_prompt_streaming`] over the mock peer,
//!      emitting [`StreamEvent`]s as they arrive;
//!   2. each event applied to a live [`AgentDockModel`] via `apply_event` —
//!      agent text streams into the transcript, each tool-call appears with its
//!      gate verdict the instant the gateway decides;
//!   3. a SECOND prompt on the SAME gateway — multi-turn, budgets persisting;
//!   4. the mandate budget visibly DEPLETES per allowed tool-call.

use std::sync::{Arc, RwLock};

use deos_hermes::surface::{AgentDockModel, ChatEntry};
use deos_hermes::{
    AcpClient, GrantRegistry, HermesGateway, Mandate, MockHermesPeer, ScriptedCall, StreamEvent,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// Drive one prompt streaming, applying every delta to the model as it arrives,
/// and return the ordered event log so the test can assert the streaming shape.
fn drive_turn(
    model: &mut AgentDockModel,
    gateway: HermesGateway<'static>,
    session_id: &str,
    prompt: &str,
    script: Vec<ScriptedCall>,
    reply: &str,
    clock: i64,
) -> (HermesGateway<'static>, Vec<String>) {
    model.push_user_prompt(prompt);
    let peer = MockHermesPeer::with_reply(session_id, script, reply);
    let mut client = AcpClient::new(peer, gateway, clock);

    // Collect events, applying each to the model (with a running mandate snapshot
    // on verdicts so the budget depletes), exactly as the gpui dock does.
    let mut seen = Vec::new();
    let mut log = Vec::new();
    let mut events = Vec::new();
    client
        .run_prompt_streaming("/deos/confined", prompt, None, &mut |ev| {
            events.push(ev);
        })
        .expect("the streaming prompt completes over the mock peer");

    let gateway = client.into_gateway();
    for ev in events {
        match &ev {
            StreamEvent::SessionStarted { .. } => log.push("session".into()),
            StreamEvent::AgentChunk { .. } => log.push("chunk".into()),
            StreamEvent::ToolCall { call } => log.push(format!("toolcall:{}", call.name)),
            StreamEvent::Verdict { call, outcome } => {
                seen.push((call.clone(), outcome.clone()));
                log.push(format!(
                    "verdict:{}:{}",
                    call.name,
                    if outcome.allowed() { "allow" } else { "reject" }
                ));
            }
            StreamEvent::Stopped { .. } => log.push("stop".into()),
        }
        let mandate = match &ev {
            StreamEvent::Verdict { .. } | StreamEvent::Stopped { .. } => {
                Some(Mandate::from_session(session_id, &gateway, &seen))
            }
            _ => None,
        };
        model.apply_event(&ev, mandate.as_ref());
    }
    (gateway, log)
}

#[test]
fn typed_prompt_streams_a_gated_multi_turn_conversation() {
    let (rt, root) = grantor();
    let rt: &'static AgentRuntime = Box::leak(Box::new(rt));
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let mut gateway = HermesGateway::new(rt, root, registry);

    let mut model = AgentDockModel::new_live("sess-live");
    assert!(model.transcript.is_empty());
    assert!(!model.running);

    // ── TURN 1 — a search + a build (two terminal calls) ──
    let (gw, log) = drive_turn(
        &mut model,
        gateway,
        "sess-live",
        "search for dregg and build it",
        vec![
            ScriptedCall::new("web_search", serde_json::json!({"query": "dregg"})),
            ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
            ScriptedCall::new("terminal", serde_json::json!({"command": "cargo test"})),
        ],
        "On it — searching, then building.",
        10,
    );
    gateway = gw;

    // The stream had the right SHAPE: session → chunk(s) → toolcall+verdict ×3 → stop.
    assert!(log.iter().any(|e| e == "session"));
    assert!(log.iter().any(|e| e.starts_with("chunk")));
    assert_eq!(
        log.iter().filter(|e| e.starts_with("verdict:")).count(),
        3,
        "three gated tool-calls: {log:?}"
    );
    assert_eq!(log.last().unwrap(), "stop");

    // The model is a real multi-turn transcript: a User entry, an Agent reply, and
    // three inline Tool entries — accumulated in order.
    assert!(matches!(model.transcript.first(), Some(ChatEntry::User { .. })));
    assert!(
        model.transcript.iter().any(|e| matches!(e, ChatEntry::Agent { .. })),
        "the agent reply streamed into the transcript"
    );
    let tool_entries = model
        .transcript
        .iter()
        .filter(|e| matches!(e, ChatEntry::Tool { .. }))
        .count();
    assert_eq!(tool_entries, 3, "three gated tool-calls inline in the chat");

    // The agent reply text actually streamed in.
    assert!(model.agent_text.contains("searching"), "{:?}", model.agent_text);

    // The permission moment is surfaced: the last gated call (an allowed terminal)
    // with its mandate + remaining budget.
    let perm = model.last_permission.as_ref().expect("a permission moment");
    assert!(perm.allowed);
    assert_eq!(perm.tool, "terminal");
    assert_eq!(perm.mandate, "tool:terminal");

    // The mandate budget DEPLETED: terminal (rate-5) shows 2 spent after two calls.
    let term = model
        .mandate_rows
        .iter()
        .find(|r| r.label == "tool:terminal")
        .expect("the terminal budget row");
    assert_eq!(term.rate_limit, 5);
    assert_eq!(term.spent, 2, "two terminal calls spent");
    assert_eq!(term.remaining(), 3);
    assert!(term.fraction_spent() > 0.0 && term.fraction_spent() < 1.0);

    assert!(!model.running, "turn 1 finished");

    // ── TURN 2 — another build on the SAME gateway: budgets PERSIST ──
    let (_gw, log2) = drive_turn(
        &mut model,
        gateway,
        "sess-live",
        "build it again",
        vec![ScriptedCall::new(
            "terminal",
            serde_json::json!({"command": "cargo build"}),
        )],
        "Rebuilding.",
        20,
    );
    assert_eq!(log2.iter().filter(|e| e.starts_with("verdict:")).count(), 1);

    // The conversation accumulated: two User entries now.
    let user_turns = model
        .transcript
        .iter()
        .filter(|e| matches!(e, ChatEntry::User { .. }))
        .count();
    assert_eq!(user_turns, 2, "multi-turn: two user prompts in the history");

    // The terminal budget kept depleting across turns: 3 spent total (2 + 1).
    let term2 = model
        .mandate_rows
        .iter()
        .find(|r| r.label == "tool:terminal")
        .expect("the terminal budget row");
    assert_eq!(term2.spent, 3, "budget persisted + depleted across turns");
    assert_eq!(term2.remaining(), 2);
}

#[test]
fn rate_exhaustion_surfaces_the_leg_live() {
    // Tighten terminal to rate 1; the 2nd terminal call is REFUSED in-band, and
    // the live permission moment names the leg (rate) the instant the gate bit.
    let (rt, root) = grantor();
    let rt: &'static AgentRuntime = Box::leak(Box::new(rt));
    let registry = GrantRegistry::default_for_session(1000).with_tool_grant("terminal", 1, 1000);
    let gateway = HermesGateway::new(rt, root, registry);

    let mut model = AgentDockModel::new_live("sess-rate");
    let (_gw, log) = drive_turn(
        &mut model,
        gateway,
        "sess-rate",
        "run two commands",
        vec![
            ScriptedCall::new("terminal", serde_json::json!({"command": "ls"})),
            ScriptedCall::new("terminal", serde_json::json!({"command": "rm -rf /"})),
        ],
        "Running both.",
        10,
    );

    assert_eq!(
        log.iter().filter(|e| *e == "verdict:terminal:reject").count(),
        1,
        "the 2nd terminal was refused in-band: {log:?}"
    );

    // The live permission moment shows the refusal + the rate leg.
    let perm = model.last_permission.as_ref().expect("a permission moment");
    assert!(!perm.allowed);
    assert_eq!(
        perm.leg,
        Some(deos_hermes::surface::RefusalLeg::Rate),
        "the rate leg is named live"
    );
}
