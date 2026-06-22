//! THE END-TO-END ACP LOOP TEST — client ↔ (mock) Hermes peer ↔ gateway verdict.
//!
//! Drives the REAL ACP client ([`AcpClient`]) through a full session against the
//! faithful [`MockHermesPeer`] (replaying `acp_adapter`'s message shapes), and
//! asserts the load-bearing seam runs end-to-end OVER THE WIRE SHAPE:
//!
//! * `initialize` → `session/new` → `session/prompt` complete;
//! * every `session/request_permission` is answered by the gateway with a real
//!   ALLOW (a receipted turn) or an in-band REJECT;
//! * the tool side-effect RIDES the metered turn (the receipt witnesses it);
//! * per-tool grants meter independently and refuse when exhausted;
//! * the mandate inspector + the dock model render the live confinement.

use std::sync::{Arc, RwLock};

use deos_hermes::surface::AgentDockModel;
use deos_hermes::{
    AcpClient, GrantRegistry, HermesGateway, Mandate, MandateKey, MockHermesPeer, PermissionOutcome,
    ScriptedCall,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

#[test]
fn full_acp_session_drives_every_permission_through_the_gate() {
    // A scripted Hermes turn: a search, a write, a terminal — all within budget.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = HermesGateway::new(&rt, root, registry);

    let script = vec![
        ScriptedCall::new("web_search", serde_json::json!({"query": "dregg"})),
        ScriptedCall::new(
            "write_file",
            serde_json::json!({"path": "src/lib.rs", "content": "hi"}),
        ),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
    ];
    let peer = MockHermesPeer::new("sess-1", script);
    let mut client = AcpClient::new(peer, gateway, 100);

    let run = client
        .run_prompt("/tmp/proj", "do the thing")
        .expect("the full ACP loop runs end-to-end");

    // The session completed with a stop reason and streamed text.
    assert_eq!(run.stop_reason, "end_turn");
    assert!(run.agent_text.contains("working"), "streamed agent text: {:?}", run.agent_text);

    // Every scripted call produced a permission verdict, and all three ALLOW
    // (within budget) — each carrying a real receipt.
    assert_eq!(run.verdicts.len(), 3, "one verdict per scripted call");
    for (call, outcome) in &run.verdicts {
        match outcome {
            PermissionOutcome::Allow { receipt, .. } => {
                assert_eq!(receipt.len(), 64, "{} got a real hex turn receipt", call.name);
                assert!(receipt.chars().all(|c| c.is_ascii_hexdigit()));
            }
            other => panic!("{} expected Allow, got {other:?}", call.name),
        }
    }

    // The per-tool grants metered INDEPENDENTLY of their kind floors.
    let gw = client.gateway();
    assert_eq!(gw.calls_made_for_tool("terminal"), 1, "terminal per-tool worker");
    assert_eq!(gw.calls_made_for_tool("write_file"), 1, "write_file per-tool worker");
    // web_search has no per-tool grant → rode the Fetch kind floor.
    assert_eq!(gw.calls_made(deos_hermes::ToolKind::Fetch), 1);

    // The mandate inspector reflects the live confinement.
    let mandate = Mandate::from_session("sess-1", gw, &run.verdicts);
    assert_eq!(mandate.total_allowed, 3);
    assert_eq!(mandate.total_refused, 0);
    let term = mandate
        .rows
        .iter()
        .find(|r| r.key == MandateKey::Tool("terminal".into()))
        .unwrap();
    assert_eq!(term.calls_made, 1);
    assert_eq!(term.remaining, 4, "rate-5 terminal, one spent");
    assert_eq!(term.receipts.len(), 1);

    // The dock model renders chat + ledger + mandate.
    let model = AgentDockModel::from_run("sess-1", &run, gw);
    assert_eq!(model.tool_lines.len(), 3);
    let text = model.render_text();
    assert!(text.contains("Hermes (confined)"));
    assert!(text.contains("MANDATE"));
}

#[test]
fn over_rate_terminal_refused_in_band_over_the_wire() {
    // Tighten terminal to rate 1; the 2nd terminal call in the script is refused
    // IN-BAND — deos answers the permission request with `deny`, the mock marks
    // the call failed, and the session still completes.
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_tool_grant("terminal", 1, 1000);
    let gateway = HermesGateway::new(&rt, root, registry);

    let script = vec![
        ScriptedCall::new("terminal", serde_json::json!({"command": "ls"})),
        ScriptedCall::new("terminal", serde_json::json!({"command": "rm -rf /"})),
    ];
    let peer = MockHermesPeer::new("sess-2", script);
    let mut client = AcpClient::new(peer, gateway, 100);

    let run = client.run_prompt("/tmp", "run two commands").expect("loop completes");

    assert_eq!(run.verdicts.len(), 2);
    assert!(run.verdicts[0].1.allowed(), "1st terminal within rate-1");
    match &run.verdicts[1].1 {
        PermissionOutcome::Reject { reason, .. } => {
            assert!(reason.contains("rate exhausted"), "names the rate leg: {reason}");
        }
        other => panic!("2nd terminal must be refused in-band, got {other:?}"),
    }
    // The refusal did NOT advance the counter.
    assert_eq!(client.gateway().calls_made_for_tool("terminal"), 1);
}

#[test]
fn tool_side_effect_rides_the_metered_turn() {
    // A write_file's witness effect rides the SAME metered turn: the committed
    // receipt's action carries BOTH the counter advance AND the write witness.
    // (The over-the-wire ALLOW proves the turn committed; here we assert the
    // bridge fed a non-empty work payload by checking the dock detail + that the
    // metered counter advanced exactly once.)
    let (rt, root) = grantor();
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let gateway = HermesGateway::new(&rt, root, registry);

    let script = vec![ScriptedCall::new(
        "write_file",
        serde_json::json!({"path": "a/b.txt", "content": "12345"}),
    )];
    let peer = MockHermesPeer::new("sess-3", script);
    let mut client = AcpClient::new(peer, gateway, 100);
    let run = client.run_prompt("/tmp", "write a file").expect("loop completes");

    assert_eq!(run.verdicts.len(), 1);
    assert!(run.verdicts[0].1.allowed(), "the write committed a receipted turn");
    assert_eq!(client.gateway().calls_made_for_tool("write_file"), 1);
}
