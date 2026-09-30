//! THE DREGG MCP SERVER, PROVEN BY RUNNING — a confined Hermes's ONLY tools are
//! dregg's, and every `tools/call` routes through the dregg sandbox.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent` (run_js drives a real
//! deos-js verified World; the default `cargo test` is mozjs-free and exercises
//! the `confinement_probe` PD + the tool surface only).
//!
//! What this proves (over a STANDARD MCP stdio session, the exact wire Hermes's
//! `mcp` Python SDK `ClientSession` speaks):
//!   (a) `initialize` → the server advertises the `tools` capability + echoes the
//!       client's protocol version;
//!   (b) `tools/list` → the model's ONLY tools are `run_js` + `confinement_probe`
//!       (no unconfined tool path, and no shell);
//!   (c) `tools/call confinement_probe` → a fresh confined firmament PD runs the
//!       four sandbox probes and reports EVERY confinement tooth held (file open
//!       denied, inet socket denied, only the Endpoint fd, IPC works). The call
//!       is a cap-gated, receipted dregg turn, and its text says no command ran.
//!   (c') D9 — the server never says it ran a command: a probe call that brings
//!       a `command` is refused unmetered and says nothing ran; a call to the old
//!       `terminal` name is an unknown tool.
//!   (d) `tools/call run_js` (js-agent) → the model's chosen script runs on the
//!       dregg verified World: a cap-gated, receipted verified turn.
//!   (e) a rate-0 `confinement_probe` grant REFUSES the call in-band (no PD) —
//!       the cap gate bites before any PD launches.

use std::io::BufReader;
use std::sync::{Arc, RwLock};

use deos_hermes::mcp_server::{DREGG_TOOL_NAMES, McpServer, McpToolHost};
use deos_hermes::{GrantRegistry, HermesGateway};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};
use serde_json::{Value, json};

/// deos the grantor: the runtime that admits the confined tool workers + runs
/// their cap-gated receipted turns.
fn grantor() -> (AgentRuntime, dregg_sdk::HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// Build a BARE tool host over a confinement (the per-kind/per-tool floors) — NO
/// `run_js` hands (no deos-js engine booted). SpiderMonkey's `JSEngine::init()`
/// is process-global + one-shot, so ONLY the dedicated `run_js` test may boot it;
/// every other test (probe/tools-list/unknown/rate-0 — none need run_js)
/// builds a bare host so the engine is initialised AT MOST once per process.
fn host(
    runtime: &AgentRuntime,
    root: dregg_sdk::HeldToken,
    registry: GrantRegistry,
) -> McpToolHost<'_> {
    let gateway = HermesGateway::new(runtime, root, registry);
    McpToolHost::new(gateway, 0)
}

/// Frame one MCP request line.
fn req(id: i64, method: &str, params: Value) -> String {
    serde_json::to_string(&json!({
        "jsonrpc": "2.0", "id": id, "method": method, "params": params
    }))
    .unwrap()
        + "\n"
}

/// Frame one MCP notification line (no id, no reply expected).
fn note(method: &str) -> String {
    serde_json::to_string(&json!({ "jsonrpc": "2.0", "method": method })).unwrap() + "\n"
}

/// Drive a scripted MCP session over the server and collect the response frames.
fn drive(server: &mut McpServer<'_>, requests: &str) -> Vec<Value> {
    let reader = BufReader::new(requests.as_bytes());
    let mut out: Vec<u8> = Vec::new();
    server
        .serve(reader, &mut out)
        .expect("serve the MCP session to EOF");
    String::from_utf8(out)
        .unwrap()
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("each reply is a JSON-RPC frame"))
        .collect()
}

/// (a) initialize + (b) tools/list — the model's ONLY tools are the dregg surface.
#[test]
fn the_confined_model_has_only_dregg_tools() {
    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let mut server = McpServer::new(host(&runtime, root, registry));

    let session = format!(
        "{}{}{}",
        req(
            1,
            "initialize",
            json!({ "protocolVersion": "2025-06-18", "capabilities": {} })
        ),
        note("notifications/initialized"),
        req(2, "tools/list", json!({})),
    );
    let replies = drive(&mut server, &session);

    // (a) initialize echoed our protocol version + advertised `tools`.
    let init = replies
        .iter()
        .find(|r| r["id"] == json!(1))
        .expect("initialize reply");
    assert_eq!(init["result"]["protocolVersion"], json!("2025-06-18"));
    assert!(
        init["result"]["capabilities"]["tools"].is_object(),
        "the server advertises the tools capability"
    );

    // (b) tools/list = EXACTLY the dregg confined surface — no unconfined tool path.
    let list = replies
        .iter()
        .find(|r| r["id"] == json!(2))
        .expect("tools/list reply");
    let names: Vec<String> = list["result"]["tools"]
        .as_array()
        .expect("tools is an array")
        .iter()
        .map(|t| t["name"].as_str().unwrap().to_string())
        .collect();
    assert_eq!(
        names,
        DREGG_TOOL_NAMES
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>(),
        "the model's ONLY tools are dregg's run_js + confinement_probe"
    );
}

/// The text of a `tools/call` reply's first content block.
fn text_of(result: &Value) -> &str {
    result["content"][0]["text"]
        .as_str()
        .expect("a text content block")
}

/// Drive one `tools/call` after the MCP handshake; return the call's `result`.
fn call_once(server: &mut McpServer<'_>, name: &str, arguments: Value) -> Value {
    let session = format!(
        "{}{}{}",
        req(1, "initialize", json!({ "protocolVersion": "2025-06-18" })),
        note("notifications/initialized"),
        req(
            2,
            "tools/call",
            json!({ "name": name, "arguments": arguments })
        ),
    );
    let replies = drive(server, &session);
    replies
        .iter()
        .find(|r| r["id"] == json!(2))
        .expect("tools/call reply")["result"]
        .clone()
}

/// (c) tools/call confinement_probe — a fresh confined PD reports every
/// confinement tooth held; the call is cap-gated + receipted, and the text says
/// no command ran.
#[cfg(unix)]
#[test]
fn confinement_probe_reports_every_tooth_and_runs_nothing() {
    use deos_hermes::confined::probe;

    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let mut server = McpServer::new(host(&runtime, root, registry));
    let result = call_once(&mut server, "confinement_probe", json!({}));

    assert_eq!(result["isError"], json!(false), "probe admitted: {result}");
    assert!(
        result["_deos"]["receipt"].is_string(),
        "the probe turn left a dregg receipt: {result}"
    );
    let verdict = result["_deos"]["sandboxVerdict"]
        .as_i64()
        .expect("a probe verdict") as i32;
    assert_eq!(
        verdict & probe::OPEN_DENIED,
        probe::OPEN_DENIED,
        "0x{verdict:x}"
    );
    assert_eq!(
        verdict & probe::NET_DENIED,
        probe::NET_DENIED,
        "0x{verdict:x}"
    );
    assert_eq!(
        verdict & probe::ONLY_ENDPOINT_FD,
        probe::ONLY_ENDPOINT_FD,
        "0x{verdict:x}"
    );
    assert_eq!(verdict, probe::ALL, "every confinement tooth held");

    let text = text_of(&result);
    assert!(text.contains("No command was run"), "{text}");

    let host = server.into_host();
    let tape = host.tape();
    assert_eq!(tape.len(), 1, "exactly one tool-call ran");
    assert_eq!(tape[0].tool, "confinement_probe");
    assert_eq!(tape[0].sandbox_verdict, Some(probe::ALL));
}

/// Phrases that would claim a command executed. None may appear in any reply.
const EXECUTION_CLAIMS: &[&str] = &["ran `", "shell ran", "executed", "execs "];

fn assert_claims_no_execution(text: &str, command: &str) {
    for claim in EXECUTION_CLAIMS {
        assert!(
            !text.to_lowercase().contains(claim),
            "the reply claims execution ({claim:?}): {text}"
        );
    }
    assert!(
        !text.contains(command),
        "the reply echoes the command as if it were acted on: {text}"
    );
}

/// (c') D9 — the server never tells the model a command ran. A probe call that
/// brings a `command` is refused in-band and unmetered (no receipt, no PD) and
/// says nothing ran; the old `terminal` name is an unknown tool. The admitted
/// probe's own text is checked for execution claims too.
#[test]
fn no_reply_claims_a_command_ran() {
    let command = "echo D9_MARKER_4711 && cat /etc/passwd";

    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let mut server = McpServer::new(host(&runtime, root, registry));
    let with_command = call_once(
        &mut server,
        "confinement_probe",
        json!({ "command": command }),
    );
    assert_eq!(with_command["isError"], json!(true), "{with_command}");
    assert!(with_command["_deos"]["receipt"].is_null(), "not metered");
    assert!(
        with_command["_deos"]["sandboxVerdict"].is_null(),
        "no PD launched"
    );
    let text = text_of(&with_command);
    assert!(text.contains("nothing was run"), "{text}");
    assert_claims_no_execution(text, command);

    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let mut server = McpServer::new(host(&runtime, root, registry));
    let old_name = call_once(&mut server, "terminal", json!({ "command": command }));
    assert_eq!(old_name["isError"], json!(true), "{old_name}");
    assert!(old_name["_deos"]["receipt"].is_null());
    assert_claims_no_execution(text_of(&old_name), command);

    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let mut server = McpServer::new(host(&runtime, root, registry));
    let admitted = call_once(&mut server, "confinement_probe", json!({}));
    assert_claims_no_execution(text_of(&admitted), command);
}

/// (e) a rate-0 `confinement_probe` grant REFUSES the call in-band — the gate
/// bites BEFORE any PD is launched.
#[cfg(unix)]
#[test]
fn a_rate_zero_probe_grant_refuses_before_any_pd_launches() {
    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1_000_000)
        .with_standard_tool_grants(1_000_000)
        .with_grant_for_tool_deny("confinement_probe");
    let mut server = McpServer::new(host(&runtime, root, registry));
    let result = call_once(&mut server, "confinement_probe", json!({}));

    assert_eq!(
        result["isError"],
        json!(true),
        "the rate-0 probe call is refused"
    );
    assert!(
        result["_deos"]["receipt"].is_null(),
        "no receipt — no turn committed"
    );
    assert!(
        result["_deos"]["sandboxVerdict"].is_null(),
        "no PD launched — the gate bit first"
    );
    let text = text_of(&result);
    assert!(
        text.contains("refused"),
        "the model sees the in-band refusal: {text}"
    );
}

/// (d) tools/call run_js — the model's chosen script runs on the dregg verified
/// World: a cap-gated, receipted verified turn (js-agent only).
#[cfg(feature = "js-agent")]
#[test]
fn run_js_routes_through_dregg_to_a_receipted_verified_turn() {
    use deos_hermes::RunJsTool;
    use dregg_cell::{AuthRequired, Credential, Requirement};

    let (runtime, root) = grantor();
    let registry = GrantRegistry::default_for_session(1_000_000)
        .with_standard_tool_grants(1_000_000)
        .with_tool_grant("run_js", 10_000, 1_000_000);
    // THE ONLY place that boots SpiderMonkey (process-global, one-shot) — the
    // dedicated run_js test. Every other test uses a bare host (no engine).
    let tool = RunJsTool::new(
        AuthRequired::Signature,
        [0x42; 32],
        [0x01; 32],
        vec![(0, deos_js::applet::pack_u64(0))],
        vec![
            (
                "bump".to_string(),
                Requirement::AtLeast(Credential::Signature),
            ),
            (
                "escalate".to_string(),
                Requirement::AtLeast(Credential::Proof),
            ),
        ],
    );
    let host = McpToolHost::new(HermesGateway::new(&runtime, root, registry), 0)
        .with_run_js(tool)
        .expect("boot deos-js for run_js");
    let mut server = McpServer::new(host);

    // The model's chosen JS: bind affordances, fire `bump` (+5) — a real verified
    // turn — and return the new counter.
    let script = "var app = deos.applet({ affordances: [\"bump\", \"escalate\"] }); \
                  app.fire(\"bump\", 5);";
    let session = format!(
        "{}{}{}",
        req(1, "initialize", json!({ "protocolVersion": "2025-06-18" })),
        note("notifications/initialized"),
        req(
            2,
            "tools/call",
            json!({ "name": "run_js", "arguments": { "script": script } })
        ),
    );
    let replies = drive(&mut server, &session);
    let call = replies
        .iter()
        .find(|r| r["id"] == json!(2))
        .expect("run_js reply");
    let result = &call["result"];

    assert_eq!(result["isError"], json!(false), "run_js admitted: {result}");
    assert!(
        result["_deos"]["receipt"].is_string(),
        "the run_js fire left a dregg receipt (a verified turn): {result}"
    );
    assert_eq!(
        result["_deos"]["firesCommitted"],
        json!(1),
        "exactly one affordance fire committed a verified turn"
    );
    let text = result["content"][0]["text"].as_str().unwrap();
    assert!(
        text.contains("verified turn"),
        "the model sees the receipted turn: {text}"
    );
}

/// THE WIRE — deos registers the dregg confined MCP server as the model's tool
/// source on `session/new`'s `mcpServers`. Over the faithful mock peer (replaying
/// the real `acp_adapter` shapes), assert the client sent EXACTLY the dregg
/// server (and only it) — so the live Hermes's tools would be exactly dregg's.
#[test]
fn session_new_registers_only_the_dregg_mcp_server() {
    use deos_hermes::{AcpClient, MockHermesPeer};

    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let gateway = HermesGateway::new(&runtime, root, registry);

    // No scripted tool-calls — we only need the handshake + session/new to land.
    let peer = MockHermesPeer::new("sess-mcp", vec![]);
    let mut client = AcpClient::new(peer, gateway, 10).with_dregg_mcp_server(
        "dregg",
        "deos-hermes",
        &["mcp-server"],
        &[],
    );

    let _run = client
        .run_prompt("/tmp", "drive the cockpit")
        .expect("the ACP loop runs over the mock peer");

    // The client registered EXACTLY the dregg server on session/new — the model's
    // ONLY tool source. (The McpServerStdio shape: {name, command, args, env}.)
    let registered = client.peer().registered_mcp_servers();
    let arr = registered
        .as_array()
        .expect("mcpServers is an array on session/new");
    assert_eq!(arr.len(), 1, "exactly ONE tool source — the dregg server");
    assert_eq!(arr[0]["name"], json!("dregg"));
    assert_eq!(arr[0]["command"], json!("deos-hermes"));
    assert_eq!(arr[0]["args"], json!(["mcp-server"]));
    // And the client exposes the same registration for inspection.
    assert_eq!(client.mcp_servers().len(), 1);
}

/// An UNKNOWN tool is refused — the model has no tool path outside the dregg
/// surface (even if it fabricates a name, there is no confined executor for it).
#[test]
fn an_unknown_tool_has_no_path() {
    let (runtime, root) = grantor();
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    let mut server = McpServer::new(host(&runtime, root, registry));

    let session = format!(
        "{}{}{}",
        req(1, "initialize", json!({ "protocolVersion": "2025-06-18" })),
        note("notifications/initialized"),
        req(
            2,
            "tools/call",
            json!({ "name": "exec_unconfined_shell", "arguments": { "command": "sh" } })
        ),
    );
    let replies = drive(&mut server, &session);
    let call = replies.iter().find(|r| r["id"] == json!(2)).expect("reply");
    assert_eq!(
        call["result"]["isError"],
        json!(true),
        "an unknown tool is refused"
    );
    let text = call["result"]["content"][0]["text"].as_str().unwrap();
    assert!(
        text.contains("not a") && text.contains("confined"),
        "names the no-path: {text}"
    );
}
