//! THE WORLD BRIDGE, PROVEN BY RUNNING — the socket that lands the MCP server's
//! `run_js` on the COCKPIT'S live World (`docs/deos/LOG-A-HERMES-IN.md` called it
//! "the EXACT remaining wire").
//!
//! Default features (mozjs-free) exercise the whole cross-process protocol:
//!   (a) a SERVED world (a real embedded verified executor — the same
//!       `dregg-sdk` Lean executor the cockpit embeds) answers the bridge on a
//!       Unix socket, on the thread that OWNS it (the non-`Send` reality);
//!   (b) a [`SocketWorldSink`] client crawls the served cells and commits a fire
//!       whose verified turn LANDS ON THE SERVED WORLD'S LEDGER, with the REAL
//!       receipt hash coming back over the wire;
//!   (c) FAIL-CLOSED: no socket ⇒ connect REFUSES; a bridge dying mid-session ⇒
//!       the next fire ERRS (never a silent fallback world).
//!
//! `--features js-agent` adds the full weld: `McpToolHost::with_world_bridge`
//! routes an MCP `tools/call run_js` (real SpiderMonkey) over the socket — the
//! model's script fires a turn that lands on the SERVED world's ledger, and an
//! absent socket refuses the tool call in-band.

#![cfg(unix)]

use std::path::PathBuf;
use std::time::{Duration, Instant};

use deos_hermes::world_bridge::{BridgeWorld, SocketWorldSink, serve_world_bridge};
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::action::Effect;
use dregg_turn::builder::{ActionBuilder, TurnBuilder};

/// Pack a u64 into a field element (LE low 8 bytes) — the counter shape.
fn pack_u64(v: u64) -> FieldElement {
    dregg_cell::field_from_u64(v)
}

fn unpack_u64(fe: &FieldElement) -> u64 {
    dregg_cell::field_to_u64(fe)
}

/// Fully-open permissions (the single-custody served-world shape, as
/// `deos_js::Applet::mint` seeds).
fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// The agent's identity, shared by both ends: the bridge client fires AS this
/// cell; the served world hosts it.
const AGENT_PK: [u8; 32] = [0x42; 32];
const AGENT_TOKEN: [u8; 32] = [0x01; 32];
const COUNTER_SLOT: usize = 0;

/// THE SERVED WORLD — a real embedded verified executor (the same `dregg-sdk`
/// Lean executor the cockpit embeds) presenting the `WorldSink` surface, exactly
/// as `starbridge_v2::agent_attach::WorldSinkAdapter` does over the cockpit's
/// `Rc<RefCell<World>>` (nonce + fee + chain head threaded host-side).
struct ServedWorld {
    engine: DreggEngine,
    prev_receipt: Option<[u8; 32]>,
    receipts: Vec<[u8; 32]>,
}

impl ServedWorld {
    /// Stand up the world with the agent's cell seeded (funded, open perms,
    /// counter slot zeroed) — the vessel a bridged fire binds.
    fn with_agent_cell() -> Self {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        // Local turns run Symbolic (the cheap witness end) — every gate
        // (authority/conservation/freshness) still runs identically.
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        let mut world = ServedWorld {
            engine,
            prev_receipt: None,
            receipts: Vec::new(),
        };
        let mut cell = Cell::with_balance(AGENT_PK, AGENT_TOKEN, 1_000_000);
        cell.permissions = open_permissions();
        cell.state.set_field(COUNTER_SLOT, pack_u64(0));
        world
            .engine
            .ledger_mut()
            .insert_cell(cell)
            .expect("seed the agent cell onto the served ledger");
        world
    }

    fn agent() -> CellId {
        CellId::derive_raw(&AGENT_PK, &AGENT_TOKEN)
    }

    fn counter(&self) -> u64 {
        self.engine
            .ledger()
            .get(&Self::agent())
            .and_then(|c| c.state.get_field(COUNTER_SLOT))
            .map(unpack_u64)
            .unwrap_or(0)
    }
}

impl BridgeWorld for ServedWorld {
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        f(self.engine.ledger());
    }

    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        let started = Instant::now();
        let fire = self.receipts.len() + 1;
        eprintln!("[world-bridge server fire {fire} +0.000s] request received: {method}");
        // The host's own turn shape: the agent's live nonce, a covering fee,
        // the chain head threaded — then the REAL verified executor.
        let nonce = self
            .engine
            .ledger()
            .get(&agent)
            .map(|c| c.state.nonce())
            .ok_or_else(|| format!("agent cell {agent} not on the served ledger"))?;
        let mut action = ActionBuilder::new_unchecked_for_tests(agent, method, agent);
        for effect in effects {
            action = action.effect(effect);
        }
        let mut tb = TurnBuilder::new(agent, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.prev_receipt {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action.build());
        eprintln!(
            "[world-bridge server fire {fire} +{:.3}s] execute_turn begin",
            started.elapsed().as_secs_f64()
        );
        let receipt = self
            .engine
            .execute_turn(&tb.build())
            .map_err(|e| e.to_string())?;
        eprintln!(
            "[world-bridge server fire {fire} +{:.3}s] execute_turn returned",
            started.elapsed().as_secs_f64()
        );
        let rh = receipt.receipt_hash();
        self.prev_receipt = Some(rh);
        self.receipts.push(rh);
        eprintln!(
            "[world-bridge server fire {fire} +{:.3}s] receipt ready",
            started.elapsed().as_secs_f64()
        );
        Ok(rh)
    }
}

/// A fresh per-test socket path (the OS 104-byte sun_path cap wants it short).
fn socket_path(tag: &str) -> PathBuf {
    std::env::temp_dir().join(format!("dregg-wb-{tag}-{}.sock", std::process::id()))
}

/// Serve a [`ServedWorld`] at `path` on its OWN thread (the world is built on,
/// owned by, and never leaves the serving thread — the non-`Send` design), and
/// hand the world back when the client hangs up.
fn spawn_served_world(path: PathBuf) -> std::thread::JoinHandle<(ServedWorld, usize)> {
    std::thread::spawn(move || {
        let started = Instant::now();
        eprintln!("[world-bridge server +0.000s] served-world construction begin");
        let mut world = ServedWorld::with_agent_cell();
        eprintln!(
            "[world-bridge server +{:.3}s] served-world ready; bind/accept/serve begin",
            started.elapsed().as_secs_f64()
        );
        let served = serve_world_bridge(&path, &mut world).expect("serve the world bridge");
        eprintln!(
            "[world-bridge server +{:.3}s] serve returned after {served} requests (client EOF)",
            started.elapsed().as_secs_f64()
        );
        (world, served)
    })
}

/// Dial until the serving thread has bound the socket (bounded wait).
fn connect_when_up(path: &std::path::Path) -> SocketWorldSink {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        match SocketWorldSink::connect(path) {
            Ok(sink) => return sink,
            Err(_) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(10)),
            Err(e) => panic!("world bridge never came up at {}: {e}", path.display()),
        }
    }
}

/// (a)+(b) THE PROTOCOL END-TO-END: crawl the served cells over the socket,
/// commit a fire, and prove the verified turn LANDED ON THE SERVED WORLD'S
/// ledger with the REAL receipt returned over the wire.
#[test]
fn bridged_fire_lands_on_the_served_worlds_ledger() {
    let path = socket_path("e2e");
    let server = spawn_served_world(path.clone());
    let mut sink = connect_when_up(&path);
    let agent = ServedWorld::agent();

    // CRAWL: the client sees the SERVED world's real cells (the agent's vessel,
    // counter zeroed) — a witnessed read across the process boundary shape.
    let (mut crawled_cells, mut crawled_counter) = (0usize, u64::MAX);
    sink.crawl_ledger(&mut |l| {
        crawled_cells = l.len();
        crawled_counter = l
            .get(&agent)
            .and_then(|c| c.state.get_field(COUNTER_SLOT))
            .map(unpack_u64)
            .unwrap_or(u64::MAX);
    });
    assert_eq!(crawled_cells, 1, "the crawl saw the served world's cell");
    assert_eq!(crawled_counter, 0, "the served counter starts at 0");

    // FIRE: one verified turn over the socket (the counter-bump shape
    // `AttachedApplet::fire` sends), landing on the SERVED ledger.
    let receipt = sink
        .commit_fire(
            agent,
            "bump",
            vec![
                Effect::SetField {
                    cell: agent,
                    index: COUNTER_SLOT as u64,
                    value: pack_u64(7),
                },
                Effect::IncrementNonce { cell: agent },
            ],
        )
        .expect("the bridged fire commits a real verified turn");
    assert_ne!(receipt, [0u8; 32], "a real receipt hash came back");

    // RE-CRAWL: the committed state is visible back through the bridge.
    let mut after = u64::MAX;
    sink.crawl_ledger(&mut |l| {
        after = l
            .get(&agent)
            .and_then(|c| c.state.get_field(COUNTER_SLOT))
            .map(unpack_u64)
            .unwrap_or(u64::MAX);
    });
    assert_eq!(after, 7, "the fire is visible through a bridged crawl");

    // Hang up ⇒ the serving loop returns ⇒ assert ON THE SERVED WORLD ITSELF.
    drop(sink);
    let (world, served) = server.join().expect("serving thread");
    assert_eq!(served, 3, "crawl + fire + crawl = three requests served");
    assert_eq!(
        world.counter(),
        7,
        "THE TURN LANDED: the served world's OWN ledger carries the write"
    );
    assert_eq!(
        world.receipts,
        vec![receipt],
        "the receipt on the wire IS the receipt on the served world's tape"
    );
    let _ = std::fs::remove_file(&path);
}

/// (c) FAIL-CLOSED, three faces: an ABSENT socket refuses at connect (so a
/// bridged `run_js` refuses the tool call — there is no fallback world inside
/// the sink, by construction); a STALE socket file with no listener behind it
/// refuses at connect; and a bridge DYING mid-session errs the next fire and
/// LATCHES the sink dead (every later call refuses; a dead crawl runs its
/// closure over NOTHING — never a substitute world).
#[test]
fn absent_or_dead_socket_refuses_fail_closed() {
    // (1) ABSENT socket ⇒ connect refuses.
    let absent = socket_path("absent");
    let _ = std::fs::remove_file(&absent);
    assert!(
        SocketWorldSink::connect(&absent).is_err(),
        "an absent world-bridge socket must refuse the connection"
    );

    // (2) STALE socket file (the server came and went) ⇒ connect refuses.
    let stale = socket_path("stale");
    let server = spawn_served_world(stale.clone());
    let sink = connect_when_up(&stale);
    drop(sink); // EOF ⇒ the serving loop returns ⇒ nothing listens behind the file
    let (_world, served) = server.join().expect("serving thread");
    assert_eq!(served, 0, "the session closed without a request");
    assert!(stale.exists(), "the socket FILE outlives the server");
    assert!(
        SocketWorldSink::connect(&stale).is_err(),
        "a dead world-bridge socket (stale file, no listener) must refuse"
    );
    let _ = std::fs::remove_file(&stale);

    // (3) MID-SESSION DEATH: the peer accepts, then hangs up. The next fire
    // ERRS and latches the sink dead; every later call refuses in-band.
    let dying = socket_path("dying");
    {
        let path = dying.clone();
        std::thread::spawn(move || {
            let _ = std::fs::remove_file(&path);
            let listener =
                std::os::unix::net::UnixListener::bind(&path).expect("bind the dying bridge");
            let (stream, _addr) = listener.accept().expect("accept the client");
            drop(stream); // hang up immediately — the mid-session death
        });
    }
    let mut sink = connect_when_up(&dying);
    let agent = ServedWorld::agent();
    let err = sink
        .commit_fire(agent, "bump", vec![Effect::IncrementNonce { cell: agent }])
        .expect_err("a fire across a dead bridge must err");
    assert!(
        err.contains("world bridge"),
        "the refusal names the bridge: {err}"
    );
    assert!(sink.is_dead(), "the transport fault latched the sink dead");
    let err2 = sink
        .commit_fire(agent, "bump", vec![])
        .expect_err("a latched-dead sink refuses every fire");
    assert!(err2.contains("dead"), "the latch is named: {err2}");
    let mut crawl_ran = false;
    sink.crawl_ledger(&mut |_| crawl_ran = true);
    assert!(
        !crawl_ran,
        "a dead bridge crawls NOTHING — never a substitute world"
    );
    let _ = std::fs::remove_file(&dying);
}

// ─────────────── the full run_js weld (real SpiderMonkey, js-agent) ──────────
//
// `cargo test --features js-agent` adds the headline path: an MCP
// `tools/call run_js` on a `McpToolHost::with_world_bridge` host runs the
// model's script ATTACHED to the served World over the socket — the fire lands
// on the SERVED ledger, and an absent socket REFUSES the tool call in-band
// first (fail-closed, proven on the SAME host before the server comes up).
#[cfg(feature = "js-agent")]
mod js_agent_weld {
    use super::*;
    use std::sync::{Arc, RwLock};

    use deos_hermes::mcp_server::McpToolHost;
    use deos_hermes::{GrantRegistry, HermesGateway, RunJsTool};
    use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    use serde_json::json;

    #[test]
    fn run_js_over_the_world_bridge_lands_on_the_served_world() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(run_js_bridge_body)
            .expect("spawn SpiderMonkey thread")
            .join()
            .expect("run_js bridge thread");
    }

    fn run_js_bridge_body() {
        let started = Instant::now();
        let phase = |name: &str| {
            eprintln!(
                "[world-bridge MCP +{:.3}s] {name}",
                started.elapsed().as_secs_f64()
            );
        };
        phase("test body entered");
        let path = socket_path("mcp");
        let _ = std::fs::remove_file(&path);

        // deos the grantor + the agent's run_js hands (the ONE SpiderMonkey
        // boot in this process — engine init is process-global, one-shot).
        phase("AgentCipherclerk::new begin");
        let mut cclerk = AgentCipherclerk::new();
        phase("AgentCipherclerk::new returned; mint_token begin");
        let root = cclerk.mint_token(&[7u8; 32], "deos");
        phase("mint_token returned; AgentRuntime::new begin");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
        phase("AgentRuntime::new returned; registry/tool setup begin");
        let registry = GrantRegistry::default_for_session(1_000_000)
            .with_standard_tool_grants(1_000_000)
            .with_tool_grant("run_js", 10_000, 1_000_000);
        let tool = RunJsTool::new(
            AuthRequired::Signature,
            AGENT_PK,
            AGENT_TOKEN,
            vec![(COUNTER_SLOT, pack_u64(0))],
            vec![(
                "bump".to_string(),
                dregg_cell::Requirement::AtLeast(dregg_cell::Credential::Signature),
            )],
        );
        phase("registry/tool ready; gateway/host construction begin");
        let host = McpToolHost::new(HermesGateway::new(&runtime, root, registry), 0);
        phase("gateway/host ready; JsRuntime boot begin");
        let mut host = host
            .with_run_js(tool)
            .expect("boot deos-js")
            .with_world_bridge(&path);
        phase("JsRuntime boot returned; bridge configured");

        let script = "var app = deos.applet({ affordances: [\"bump\"] }); \
                      app.fire(\"bump\", 7);";
        let args = json!({ "script": script });

        // FAIL-CLOSED FIRST: no server behind the socket ⇒ the tool call
        // REFUSES in-band — it does NOT run on the embedded World.
        phase("absent-socket call begin (must refuse before admission)");
        let refused = host.call_tool("run_js", &args);
        phase("absent-socket call returned");
        assert_eq!(
            refused["isError"],
            json!(true),
            "an absent bridge refuses run_js: {refused}"
        );
        let text = refused["content"][0]["text"].as_str().unwrap();
        assert!(
            text.contains("world-bridge") && text.contains("REFUSED"),
            "the refusal names the bridge + fail-closed: {text}"
        );
        assert_eq!(
            refused["_deos"]["firesCommitted"],
            json!(0),
            "NOTHING ran anywhere (no embedded fallback)"
        );

        // Serve the world, retry the SAME host (lazy dial per call).
        phase("spawn served-world thread");
        let server = spawn_served_world(path.clone());
        let deadline = Instant::now() + Duration::from_secs(10);
        while !path.exists() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        phase(if path.exists() {
            "socket path ready; first connected admission/fire begin"
        } else {
            "socket path wait expired; first connected call begin"
        });
        // The socket file appearing races the accept; the connect itself
        // blocks in the OS backlog, so one call is enough once the file is up.
        let landed = host.call_tool("run_js", &args);
        phase("first connected admission/fire returned");
        assert_eq!(
            landed["isError"],
            json!(false),
            "the bridged run_js was admitted: {landed}"
        );
        assert_eq!(
            landed["_deos"]["firesCommitted"],
            json!(1),
            "exactly ONE verified turn committed over the bridge"
        );
        assert!(
            landed["_deos"]["receipt"].is_string(),
            "the live receipt came back over the wire: {landed}"
        );
        let text = landed["content"][0]["text"].as_str().unwrap();
        assert!(
            text.contains("COCKPIT'S live World over the world bridge"),
            "the model sees WHERE it ran: {text}"
        );
        assert_eq!(landed["_deos"]["admitted"], json!(true));
        assert_eq!(landed["_deos"]["scriptError"], json!(null));
        assert_eq!(
            landed["_deos"]["receipts"],
            json!([landed["_deos"]["receipt"]]),
            "the new list retains the legacy first receipt"
        );

        // Both fires reach the real served executor before the exception. The
        // MCP result must be unsuccessful without pretending those turns rolled
        // back or dropping all but the first receipt.
        phase("two-fire-then-throw call begin");
        let partial = host.call_tool(
            "run_js",
            &json!({ "script": r#"
                var app = deos.applet({ affordances: ["bump"] });
                app.fire("bump", 3);
                app.fire("bump", 5);
                throw new Error("after two committed fires");
            "# }),
        );
        phase("two-fire-then-throw call returned");
        assert_eq!(partial["isError"], json!(true), "{partial}");
        assert_eq!(partial["_deos"]["admitted"], json!(true));
        assert!(partial["_deos"]["scriptError"].is_string());
        assert_eq!(partial["_deos"]["firesCommitted"], json!(2));
        let partial_receipts = partial["_deos"]["receipts"]
            .as_array()
            .expect("all committed receipts retained");
        assert_eq!(partial_receipts.len(), 2);
        assert_ne!(partial_receipts[0], partial_receipts[1]);
        assert_eq!(partial["_deos"]["receipt"], partial_receipts[0]);
        assert!(
            partial["content"][0]["text"]
                .as_str()
                .expect("error text")
                .contains("2 turn(s) already committed"),
            "a text-only MCP consumer must also see partial progress: {partial}"
        );

        // Neither a runtime error before a fire nor a syntax error can acquire
        // a receipt from a preceding call on the same host/runtime.
        for (name, script) in [
            (
                "no-fire runtime error",
                "throw new Error('before any fire');",
            ),
            ("no-fire syntax error", "var = ;"),
        ] {
            phase(&format!("{name} call begin"));
            let no_fire = host.call_tool("run_js", &json!({ "script": script }));
            phase(&format!("{name} call returned"));
            assert_eq!(no_fire["isError"], json!(true), "{no_fire}");
            assert_eq!(no_fire["_deos"]["admitted"], json!(true));
            assert!(no_fire["_deos"]["scriptError"].is_string());
            assert_eq!(no_fire["_deos"]["firesCommitted"], json!(0));
            assert_eq!(no_fire["_deos"]["receipts"], json!([]));
            assert_eq!(no_fire["_deos"]["receipt"], json!(null));
        }

        // A fresh read proves the shared runtime remains usable after throws;
        // the server-owned ledger below independently checks the actual value.
        phase("post-error readback call begin");
        let readback = host.call_tool(
            "run_js",
            &json!({ "script": "var app = deos.applet({ affordances: [\"bump\"] }); app.get(0);" }),
        );
        phase("post-error readback call returned");
        assert_eq!(readback["isError"], json!(false), "{readback}");
        assert_eq!(readback["_deos"]["scriptError"], json!(null));
        assert_eq!(readback["_deos"]["firesCommitted"], json!(0));
        assert!(
            readback["content"][0]["text"]
                .as_str()
                .expect("readback text")
                .contains("Some(15)")
        );

        // Hang up (drop the host's session connection) ⇒ the serving loop
        // returns ⇒ assert ON THE SERVED WORLD: the model's fire LANDED.
        phase("drop host begin (JsRuntime and final session socket)");
        drop(host);
        phase("drop host returned; server join begin");
        let (world, _served) = server.join().expect("serving thread");
        phase("server join returned; final ledger/receipt assertions begin");
        assert_eq!(
            world.counter(),
            15,
            "the successful fire and the two pre-exception fires all remain on the served ledger"
        );
        assert_eq!(
            world.receipts.len(),
            3,
            "no-fire errors and readback add no resource turn"
        );
        let expected_receipts: Vec<_> = world
            .receipts
            .iter()
            .map(|receipt| {
                json!(
                    receipt
                        .iter()
                        .map(|byte| format!("{byte:02x}"))
                        .collect::<String>()
                )
            })
            .collect();
        assert_eq!(landed["_deos"]["receipt"], expected_receipts[0]);
        assert_eq!(partial_receipts.as_slice(), &expected_receipts[1..]);
        let _ = std::fs::remove_file(&path);
        phase("all assertions passed; test body returning");
    }
}
