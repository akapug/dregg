//! PILLAR-4a FULL ROUND-TRIP — a confined brain's `run_js` commits a turn THROUGH
//! a REAL node's executor and reads the receipt + mutated cell back.
//!
//! Run: `cd deos-hermes && cargo test --features node-brain --test node_backed_round_trip`
//!
//! This closes the seam `tests/node_backed_hands.rs` NAMED and deferred (its node
//! is a stub that REFUSES `/turns/submit`, proving the transport + fail-closed pole
//! only). Here the node is the REAL-executor `dregg_sdk_net::test_support::TestNode`
//! — a live `dregg_cell::Ledger` driven by the genuine `dregg_turn::TurnExecutor`.
//! So a `NodeWorldSink`-backed `run_js` fire is a REAL verified turn:
//!
//!   * the `run_js` tool-call is admitted + receipted by the gateway (the
//!     accountability turn);
//!   * the `inc(1)` affordance fire RIDES the jail's sole granted egress door,
//!     POSTs a signed turn to the node's `/turns/submit`, and the node's executor
//!     EXECUTES it — committing a real receipt on the node's ledger;
//!   * the fire's receipt hash (the value `NodeWorldSink::fire_effects` returns) IS
//!     the receipt the node recorded; and
//!   * a fresh crawl of the node reads the MUTATED agent cell back (the counter slot
//!     the fire bumped, the nonce the turn bumped).
//!
//! The agent cell every committed turn binds is the cipherclerk's DEFAULT cell — so
//! the node genesis-funds EXACTLY that cell (open perms, funded), and the fire
//! commits AS the agent's own held cell (no cross-vessel reach).

#![cfg(all(unix, feature = "node-brain"))]

use std::sync::{Arc, RwLock};

use deos_hermes::egress::EgressNetGrant;
use deos_hermes::{
    DreggHost, GrantRegistry, HermesGateway, NodeJsHands, ToolCallRequest, agent_cell_of,
};
use dregg_cell::AuthRequired;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};
use dregg_sdk_net::NodeHttpClient;
use dregg_sdk_net::test_support::TestNode;

// ───────────────────────────── the grantor ──────────────────────────────────

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// A gateway whose `run_js` grant has ample rate head-room (so the accountability
/// turn is admitted — the binding limit is not the gate here).
fn run_js_gateway(rt: &AgentRuntime, root: HeldToken) -> HermesGateway<'_> {
    let registry = GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000);
    HermesGateway::new(rt, root, registry)
}

// The JS the brain fires: declare the `inc` affordance surface and fire it once —
// the fire is a real cap-gated verified turn that COMMITS on the REMOTE node.
const FIRE_JS: &str = r#"
    var app = deos.applet({ affordances: ["inc"] });
    app.inc(1);
"#;

/// Split `http://host:port` into `(host, port)`.
fn split_base_url(base_url: &str) -> (String, u16) {
    let hostport = base_url.strip_prefix("http://").expect("http base url");
    let (host, port_s) = hostport.rsplit_once(':').expect("host:port");
    (host.to_string(), port_s.parse().expect("port"))
}

/// THE FULL ROUND-TRIP: a `NodeWorldSink`-backed `run_js` fire commits a real turn
/// THROUGH the node's executor, and the node's own ledger carries the receipt + the
/// mutated cell.
#[test]
fn node_backed_run_js_commits_through_node_execution_and_reads_receipt_back() {
    // A multi-thread tokio runtime hosts the node's accept loop; the sink itself
    // runs on a PLAIN OS thread (it owns a blocking current-thread runtime and
    // must not be driven off a tokio worker).
    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .expect("tokio runtime");

    // The agent identity (the cell every committed turn binds on the node).
    let cipherclerk = AgentCipherclerk::new();
    let agent_pk = cipherclerk.public_key().0;
    let expected_agent = agent_cell_of(&cipherclerk);

    // Genesis-fund the cipherclerk's DEFAULT cell on the node (open perms, funded),
    // so an own-cell `inc` fire authorizes + pays its fee.
    let node_public_key = *blake3::hash(b"pillar4a-round-trip-node").as_bytes();
    let (node, agent_cell) = TestNode::genesis(node_public_key, agent_pk, 1_000_000);
    assert_eq!(
        agent_cell, expected_agent,
        "genesis funds the cipherclerk default cell — the cell the hands' turns bind"
    );
    let fed_id = node.fed_id();

    let spawned = rt.block_on(node.spawn());
    let base_url = spawned.base_url().to_string();
    let (host, port) = split_base_url(&base_url);

    // The host opens the provider-only egress door to EXACTLY the node.
    let dhost = DreggHost::new().with_egress_provider(host.clone(), port);
    assert!(dhost.egress.admits_connect(&host, port));
    let node_grant = EgressNetGrant::new(host, port);

    // Drive the hands on a plain OS thread; return the outcome to the test.
    let handle = std::thread::spawn(move || {
        let (agent_rt, root) = grantor();
        let gateway = run_js_gateway(&agent_rt, root);
        let mut hands = NodeJsHands::new(
            &dhost.egress,
            node_grant,
            cipherclerk,
            fed_id,
            AuthRequired::Signature, // held satisfies the `inc` affordance's required
            vec![],                  // no seed fields (counter starts at 0)
            vec![("inc".to_string(), AuthRequired::Signature)],
            gateway,
        )
        .expect("hands to a GRANTED node build");

        let call = ToolCallRequest::new(
            "sess-rt",
            "tc-rt-1",
            "run_js",
            serde_json::json!({ "script": "fire inc(+1) on the remote node's World" }),
        );
        hands
            .run_script_call(&call, 50, FIRE_JS)
            .expect("run_js boots + evals")
    });
    let outcome = handle.join().expect("sink thread");

    // THE ACCOUNTABILITY TURN committed (the run_js tool-call itself was receipted).
    assert!(
        outcome.tool_admitted(),
        "the run_js accountability turn is admitted + receipted"
    );

    // THROUGH NODE EXECUTION — the fire COMMITTED a real verified turn on the node
    // (not a stub refusal): exactly one committed fire, one receipt, no fault.
    assert!(
        outcome.js_error.is_none(),
        "no fault — the fire committed through the node executor, got: {:?}",
        outcome.js_error
    );
    assert_eq!(
        outcome.fires_committed, 1,
        "the inc(1) fire committed one real turn on the remote node"
    );
    assert_eq!(
        outcome.receipts.len(),
        1,
        "one committed fire ⇒ one receipt"
    );
    let fire_receipt = outcome.receipts[0];
    assert_ne!(
        fire_receipt, [0u8; 32],
        "a committed fire carries a real receipt"
    );

    // THE RECEIPT LANDED ON THE NODE'S LEDGER — the node executed exactly one turn,
    // and the receipt the node recorded IS the receipt the fire returned.
    rt.block_on(async {
        let node = spawned.lock().await;
        assert_eq!(
            node.receipts().len(),
            1,
            "the node's executor committed exactly one turn"
        );
        assert_eq!(
            node.receipts()[0].receipt_hash(),
            fire_receipt,
            "the node's recorded receipt IS the fire's receipt (the full round-trip)"
        );
    });

    // THE CRAWL READS THE MUTATED CELL BACK — a fresh crawl of the node (the SAME
    // read path `NodeWorldSink::with_ledger` uses) sees the counter the fire bumped
    // and the nonce the turn bumped.
    let (counter, nonce) = rt.block_on(async move {
        let client = NodeHttpClient::new(base_url);
        let ledger = client
            .fetch_ledger_snapshot()
            .await
            .expect("crawl the node's ledger");
        let cell = ledger.get(&agent_cell).expect("agent cell on the node");
        (
            deos_js::applet::unpack_u64(&cell.state.fields[0]),
            cell.state.nonce(),
        )
    });
    assert_eq!(
        counter, 1,
        "the crawl reads the mutated counter slot (inc(1)) back off the node"
    );
    // The affordance fire emits an explicit `IncrementNonce` (attach.rs) ON TOP of
    // the executor's automatic per-turn bump, so one committed fire lands nonce = 2.
    assert_eq!(
        nonce, 2,
        "the crawl reads the fire's nonce bump back off the node (explicit + per-turn)"
    );

    spawned.shutdown();
}
