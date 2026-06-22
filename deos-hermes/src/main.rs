//! `deos-hermes` — drive the confined Hermes agent loop, two ways.
//!
//! 1. THE LIVE-SHAPED ACP LOOP (default, or `cargo run -- mock`): the real ACP
//!    client drives a session against the faithful [`MockHermesPeer`] (replaying
//!    `acp_adapter`'s message shapes), answering every `session/request_permission`
//!    with the [`HermesGateway`] verdict — a cap-gated, metered, receipted dregg
//!    turn (with the tool's side-effect riding it) or an in-band refusal. Then it
//!    prints the agent dock view (chat + tool-call ledger + the mandate inspector).
//!
//! 2. THE LIVE SUBPROCESS (`cargo run -- live`): spawns `hermes-acp` and drives
//!    the SAME client over its stdio. (In this environment the install is broken —
//!    missing the `acp` Python module — so this exits early with the honest error;
//!    the wiring is real for when the install is fixed.)
//!
//! Run: `cd deos-hermes && cargo run` (mock) or `cargo run -- live`.

use std::sync::{Arc, RwLock};

use deos_hermes::surface::AgentDockModel;
use deos_hermes::{
    AcpClient, AcpTransport, GrantRegistry, HermesGateway, MockHermesPeer, ScriptedCall,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "mock".to_string());
    match mode.as_str() {
        "live" => run_live(),
        _ => run_mock(),
    }
}

/// Build the grantor runtime + root token + the standard confinement (per-kind
/// floors + the curated per-tool tightenings, deadline/clock 1000).
fn confinement() -> (AgentRuntime, dregg_sdk::HeldToken, GrantRegistry) {
    let mut cclerk = AgentCipherclerk::new();
    let root_token = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    // The per-tool grants tighten `terminal` (rate 5), `web_extract` (15), etc.
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    (runtime, root_token, registry)
}

/// The live-shaped ACP loop over the faithful mock peer.
fn run_mock() {
    println!("deos-hermes — the confined Hermes ACP loop (mock peer)\n");
    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    // A scripted Hermes turn: a search, a file write, three terminal calls (the
    // 3rd over a tightened rate, in a tighter demo registry below), a fetch.
    let script = vec![
        ScriptedCall::new("web_search", serde_json::json!({"query": "dregg ocap"})),
        ScriptedCall::new(
            "write_file",
            serde_json::json!({"path": "notes/plan.md", "content": "the plan"}),
        ),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo build"})),
        ScriptedCall::new("terminal", serde_json::json!({"command": "cargo test"})),
        ScriptedCall::new("read_file", serde_json::json!({"path": "src/lib.rs"})),
    ];

    let peer = MockHermesPeer::new("sess-demo", script);
    let mut client = AcpClient::new(peer, gateway, 10);

    let run = client
        .run_prompt("/Users/ember/dev/breadstuffs", "help me confine hermes")
        .expect("the ACP loop runs end-to-end over the mock peer");

    let model = AgentDockModel::from_run("sess-demo", &run, client.gateway());
    print!("{}", model.render_text());
}

/// The live subprocess path: spawn `hermes-acp` and drive the same client.
fn run_live() {
    println!("deos-hermes — the confined Hermes ACP loop (LIVE subprocess)\n");
    let (runtime, root_token, registry) = confinement();
    let gateway = HermesGateway::new(&runtime, root_token, registry);

    match AcpTransport::spawn_hermes("hermes-acp", &[]) {
        Ok(transport) => {
            let mut client = AcpClient::new(transport, gateway, 10);
            match client.run_prompt(
                "/Users/ember/dev/breadstuffs",
                "list the files in this directory",
            ) {
                Ok(run) => {
                    let model = AgentDockModel::from_run("live", &run, client.gateway());
                    print!("{}", model.render_text());
                }
                Err(e) => {
                    eprintln!(
                        "live hermes-acp loop ended: {e}\n(the install in this env is broken — \
                         missing the `acp` python module; use `cargo run` for the mock loop)"
                    );
                }
            }
        }
        Err(e) => eprintln!("could not spawn hermes-acp: {e}"),
    }
}
