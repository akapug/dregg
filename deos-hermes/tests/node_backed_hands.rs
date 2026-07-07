//! NODE-BACKED HANDS (Pillar 4) — a confined brain's `run_js` drives a REMOTE
//! node's World over a `NodeWorldSink` reached ONLY through its granted egress door.
//!
//! Run: `cd deos-hermes && cargo test --features node-brain --test node_backed_hands`
//!
//! The two poles this exercises:
//!
//!   (A) THE COMMIT LEG + FAIL-CLOSED — a `NodeWorldSink`-backed `run_js` binds the
//!       agent's hands to a node whose `host:port` is the jail's SOLE granted egress
//!       door, the `run_js` tool-call is admitted + receipted by the gateway (the
//!       accountability turn), and a fire actually RIDES the granted door to the
//!       remote node (the node sees the signed-turn POST). When the node refuses the
//!       turn, the fire FAIL-CLOSES (no receipt, the refusal surfaced) — never a
//!       silent success.
//!
//!       HONEST SCOPE (a named seam, see the module-level report): the node here is a
//!       minimal in-process STUB that serves the client's reads and REFUSES
//!       `/turns/submit`. The full round-trip — a real turn EXECUTED on the node and
//!       its receipt read back off the node's ledger — needs the executor-backed
//!       `TestNode` harness that `dregg-sdk-net`'s own `node_world_sink` tests use.
//!       That harness is a PRIVATE `#[cfg(test)]` module (not a test-support export),
//!       and re-creating its shape here requires decoding the `/turns/submit` body,
//!       which is a POSTCARD-encoded `dregg_sdk::SignedTurn` — and `postcard` is not
//!       a dev-dependency of `deos-hermes`. So this file proves the wiring +
//!       fail-closed transport up to (not through) the node-side execution.
//!
//!   (B) THE CONFINEMENT POLE — a `NodeWorldSink` pointed at a `host:port` OUTSIDE
//!       the granted egress door is REFUSED before a socket is opened
//!       (`NodeJsHands::check_endpoint` / `NodeJsHands::new` return
//!       `EndpointNotGranted`). This models the pole at the `EgressPolicy::admits`
//!       layer EXACTLY as `tests/provider_egress.rs` models the granted/sibling
//!       socket doors; that test proves the physical OS-jail backstop (an ungranted
//!       connect is EPERM'd inside the PD).

#![cfg(all(unix, feature = "node-brain"))]

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, RwLock};

use deos_hermes::egress::EgressNetGrant;
use deos_hermes::{
    DreggHost, EgressPolicy, GrantRegistry, HermesGateway, NodeHandsError, NodeJsHands,
    ToolCallRequest, agent_cell_of, check_endpoint,
};
use dregg_cell::AuthRequired;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

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

// ────────────────────── a minimal in-process STUB node ───────────────────────
//
// A blocking HTTP/1.1 server (std::net — no tokio, no postcard) that serves EXACTLY
// the reads the client makes before a submit, and REFUSES `/turns/submit`. It is NOT
// an executor: it proves the fire reached the node over the granted door and that a
// node refusal fail-closes. It records every `/turns/submit` POST it saw.

struct StubHits {
    submits: AtomicUsize,
}

/// Spawn the stub node on loopback; returns `(port, hits)`. The accept loop runs on a
/// detached thread (abandoned at process exit).
fn spawn_stub_node() -> (u16, Arc<StubHits>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind stub node");
    let port = listener.local_addr().unwrap().port();
    let hits = Arc::new(StubHits {
        submits: AtomicUsize::new(0),
    });
    let hits_srv = hits.clone();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut sock) = stream else { continue };
            serve_one(&mut sock, &hits_srv);
        }
    });
    (port, hits)
}

fn serve_one(sock: &mut std::net::TcpStream, hits: &StubHits) {
    // Read the head (until CRLFCRLF), then the Content-Length body.
    let mut buf = Vec::new();
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        match sock.read(&mut tmp) {
            Ok(0) => return,
            Ok(n) => {
                buf.extend_from_slice(&tmp[..n]);
                if let Some(p) = find_sub(&buf, b"\r\n\r\n") {
                    break p;
                }
            }
            Err(_) => return,
        }
    };
    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = head.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let path = parts.next().unwrap_or("");
    let content_length = lines
        .find_map(|l| {
            l.to_ascii_lowercase()
                .strip_prefix("content-length:")
                .map(|v| v.trim().parse::<usize>().unwrap_or(0))
        })
        .unwrap_or(0);
    let mut body = buf[header_end + 4..].to_vec();
    while body.len() < content_length {
        match sock.read(&mut tmp) {
            Ok(0) => break,
            Ok(n) => body.extend_from_slice(&tmp[..n]),
            Err(_) => break,
        }
    }

    let json = route(method, path, hits);
    let payload = serde_json::to_vec(&json).unwrap();
    let resp = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        payload.len()
    );
    let _ = sock.write_all(resp.as_bytes());
    let _ = sock.write_all(&payload);
    let _ = sock.flush();
}

fn route(method: &str, path: &str, hits: &StubHits) -> serde_json::Value {
    match (method, path) {
        // The submit-prep reads (fresh nonce + chain head + solo federation id).
        ("GET", "/api/cells") => serde_json::Value::Array(vec![]),
        ("GET", "/api/receipts") => serde_json::Value::Array(vec![]),
        ("GET", "/status") => serde_json::json!({
            "federation_mode": "solo",
            "public_key": dregg_hex(&[0u8; 32]),
        }),
        ("GET", p) if p.starts_with("/api/cell/") => {
            // The agent cell exists (found + nonce), so `submit_turn` proceeds to POST.
            serde_json::json!({ "found": true, "nonce": 0 })
        }
        // THE SUBMIT — refuse it (this stub is not an executor). Fail-closed: the
        // client turns this into an `Err`, never a silent success.
        ("POST", "/turns/submit") => {
            hits.submits.fetch_add(1, Ordering::SeqCst);
            serde_json::json!({
                "accepted": false,
                "error": "stub node: turn execution not modeled (postcard-decode seam)",
            })
        }
        _ => serde_json::json!({ "error": "not found" }),
    }
}

fn find_sub(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn dregg_hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// ───────────────────────────── the JS the brain fires ────────────────────────
//
// Declare the `inc` affordance surface and fire it once — the fire is the work that
// commits (a real cap-gated verified turn) on the REMOTE node.
const FIRE_JS: &str = r#"
    var app = deos.applet({ affordances: ["inc"] });
    app.inc(1);
"#;

// ══════════════════════════════════ POLE A ═══════════════════════════════════

/// (A) The `NodeWorldSink`-backed hands bind `run_js` to the node at the SOLE
/// granted door; the `run_js` accountability turn is admitted + receipted; a fire
/// RIDES the granted door to the node (the node sees the signed-turn POST); and the
/// node's refusal FAIL-CLOSES (no committed fire, the refusal surfaced).
///
/// This is the ONLY test in this binary that boots SpiderMonkey (process-global,
/// one-shot); POLE B never boots it (its refusals return before any runtime).
#[test]
fn node_backed_run_js_rides_the_granted_door_and_fails_closed_on_refusal() {
    let (node_port, hits) = spawn_stub_node();

    // dregg the host opens the provider-only socket door to EXACTLY the node.
    let host = DreggHost::new().with_egress_provider("127.0.0.1", node_port);
    assert!(host.egress.admits_connect("127.0.0.1", node_port));

    let node = EgressNetGrant::new("127.0.0.1", node_port);

    // The agent identity (the cell every committed turn binds on the node).
    let cipherclerk = AgentCipherclerk::new();
    let expected_agent = agent_cell_of(&cipherclerk);

    // A solo-node federation id derived the way the client would (blake3 of the
    // node public key); the stub's /status carries the matching all-zero key.
    let federation_id = *blake3::hash(&[0u8; 32]).as_bytes();

    let (rt, root) = grantor();
    let gateway = run_js_gateway(&rt, root);

    // Build the distributed hands — the sink points at http://127.0.0.1:node_port
    // (the granted door), committing AS the agent's default cell.
    let mut hands = NodeJsHands::new(
        &host.egress,
        node,
        cipherclerk,
        federation_id,
        AuthRequired::Signature, // held satisfies the `inc` affordance's required
        vec![],                  // no seed fields
        vec![("inc".to_string(), AuthRequired::Signature)],
        gateway,
    )
    .expect("hands to a GRANTED node build");

    // The hands commit AS the cipherclerk's default cell — the SAME cell the sink
    // signs as (so a turn binds the agent's own held cell, not a cross-vessel reach).
    assert_eq!(
        hands.agent(),
        expected_agent,
        "the committing cell is the agent's default cell"
    );
    assert_eq!(hands.node_endpoint().port, node_port);

    // Fire one `run_js` call against the remote node.
    let call = ToolCallRequest::new(
        "sess-node",
        "tc-node-1",
        "run_js",
        serde_json::json!({ "script": "fire inc(+1) on the remote node's World" }),
    );
    let outcome = hands
        .run_script_call(&call, 50, FIRE_JS)
        .expect("run_js boots + evals");

    // THE ACCOUNTABILITY TURN committed — the `run_js` tool-call itself was admitted
    // + receipted by the gateway (independent of what happened at the node).
    assert!(
        outcome.tool_admitted(),
        "the run_js accountability turn is admitted + receipted"
    );

    // THE FIRE RODE THE GRANTED DOOR — the node actually received the signed-turn
    // POST (the fire reached the REMOTE node over the sole granted socket).
    assert!(
        hits.submits.load(Ordering::SeqCst) >= 1,
        "the fire rode the granted door: the node saw the /turns/submit POST"
    );

    // FAIL-CLOSED — the node refused, so NOTHING committed and the refusal is
    // surfaced (never a silent success).
    assert_eq!(
        outcome.fires_committed, 0,
        "a node refusal commits nothing on the remote ledger"
    );
    assert!(outcome.receipts.is_empty(), "no receipt for a refused turn");
    let err = outcome
        .js_error
        .as_deref()
        .expect("the node refusal surfaces as an error, not a silent success");
    assert!(
        err.contains("refused by node") || err.contains("stub node"),
        "the fail-closed error names the node refusal, got: {err}"
    );
}

// ══════════════════════════════════ POLE B ═══════════════════════════════════

/// (B) THE CONFINEMENT POLE at the `admits` layer — a node endpoint OUTSIDE the
/// granted egress door is refused before any socket opens; the granted one is
/// admitted. Mirrors `tests/provider_egress.rs`'s granted/sibling socket doors (which
/// prove the physical OS-jail EPERM backstop). This test NEVER boots SpiderMonkey (an
/// ungranted `new` returns before the runtime boots).
#[test]
fn node_outside_the_granted_door_is_refused() {
    // A policy granting EXACTLY one node door.
    let mut egress = EgressPolicy::sealed();
    egress.grant_provider("127.0.0.1", 8899);

    let granted = EgressNetGrant::new("127.0.0.1", 8899);
    let sibling_port = EgressNetGrant::new("127.0.0.1", 9999); // a DIFFERENT port
    let sibling_host = EgressNetGrant::new("10.0.0.1", 8899); // a DIFFERENT host

    // The granted node door is admitted…
    check_endpoint(&egress, &granted).expect("the granted node door is admitted");
    // …a sibling port / host is NOT (the door is to ONE endpoint, not "the network").
    assert!(matches!(
        check_endpoint(&egress, &sibling_port),
        Err(NodeHandsError::EndpointNotGranted { .. })
    ));
    assert!(matches!(
        check_endpoint(&egress, &sibling_host),
        Err(NodeHandsError::EndpointNotGranted { .. })
    ));

    // Building the hands to an UNGRANTED node is refused BEFORE any sink/runtime —
    // never a silent success. (No SpiderMonkey boots: the check precedes the runtime.)
    let (rt, root) = grantor();
    let gateway = run_js_gateway(&rt, root);
    let built = NodeJsHands::new(
        &egress,
        sibling_port.clone(),
        AgentCipherclerk::new(),
        [0u8; 32],
        AuthRequired::Signature,
        vec![],
        vec![("inc".to_string(), AuthRequired::Signature)],
        gateway,
    );
    match built {
        Err(NodeHandsError::EndpointNotGranted { host, port }) => {
            assert_eq!((host.as_str(), port), ("127.0.0.1", 9999));
        }
        Err(other) => panic!("expected EndpointNotGranted, got a different error: {other}"),
        Ok(_) => panic!("hands to an UNGRANTED node must be refused"),
    }

    // A SEALED policy admits no node at all.
    let sealed = EgressPolicy::sealed();
    assert!(matches!(
        check_endpoint(&sealed, &granted),
        Err(NodeHandsError::EndpointNotGranted { .. })
    ));
}
