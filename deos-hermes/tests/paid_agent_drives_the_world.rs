//! THE METERED ECONOMY BITES REAL WORLD-WORK — a confined agent does genuine,
//! ACCUMULATING work on ONE shared live World across SEVERAL `run_js` tool-calls,
//! each a cap-gated, metered, AND CHARGED dregg turn, until its spend allowance is
//! exhausted and the next live-World step is refused IN-BAND with the World untouched.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent --test paid_agent_drives_the_world`
//! (the default `cargo test` is mozjs-free — the live-World `run_js` path pulls
//! deos-js / real SpiderMonkey via the `js-agent` feature.)
//!
//! ## What gap this closes
//!
//! The PAID seam (`tests/tool_market_seam.rs`) proved a charge + an over-budget
//! refusal — but only over a GENERIC tool (`web_search`) admitted as a PURE METERED
//! turn (`Some(vec![])`), never reaching a live World. Conversely the live-World
//! `run_js` proofs (`hermes_runs_js`, `hermes_authors_card_via_run_js`,
//! `hermes_composes_multi_cell`) drive REAL work on a real ledger — but every one
//! runs on a FREE gateway (no `ToolMarket`). The UNION was unproven: does the metered
//! ECONOMY actually BOUND an agent doing real, accumulating work in the World?
//!
//! This file is that union. The agent's task is genuinely stateful: bump a counter on
//! the live World by `+1`, one `run_js` call at a time. Each call is a separately
//! CHARGED tool-call (the provider is paid per step) AND lands a real verified turn on
//! the live ledger (the counter climbs). When the session spend allowance is spent,
//! the next step is refused at the membrane — no charge, no JS, the live World frozen
//! exactly where the budget ran out. "Empowered, accountable, bounded" — now with the
//! bound being the ECONOMY, across a multi-step real task.
//!
//! ## What is proven
//!
//!   (a) PAID REAL WORK — three `run_js` calls each commit a real verified turn on the
//!       live World (the counter climbs 1 → 2 → 3, re-read off the live ledger) AND
//!       each charges the provider the per-call price (conserved consumer → provider).
//!   (b) BUDGET BITES MID-TASK — the FOURTH step would exceed the spend allowance, so
//!       it is refused IN-BAND naming the budget leg: NO charge, NO JS, and the live
//!       World counter stays at 3 (the work the budget did not buy never happened).
//!   (c) END-TO-END OVER ACP — the SAME paid bound drives the live-decide loop: a real
//!       `AcpClient` session dispatches four `run_js` calls through `LiveJsHands` over a
//!       PAID gateway; the first three commit + charge, the fourth is rejected
//!       over-budget over the ACP wire, the live World again frozen at 3.

#![cfg(feature = "js-agent")]

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use deos_hermes::acp_client::AcpClient;
use deos_hermes::run_js::RunJsTool;
use deos_hermes::{
    GrantRegistry, HermesGateway, LiveJsHands, MockHermesPeer, PermissionOutcome, ScriptedCall,
    ToolCallRequest, ToolMarket,
};
use deos_js::{JsRuntime, WorldSink};
use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Attenuation, HeldToken};
use dregg_turn::action::Effect;
use dregg_turn::builder::{ActionBuilder, TurnBuilder};

// ───────────────────────── a self-contained live World ──────────────────────
//
// A `WorldSink` over an embedded `DreggEngine` (the SAME verified executor a real
// cockpit World drives). It commits each affordance fire as a real verified turn —
// the live ledger the receipts land on, and that the test re-reads to prove the
// counter genuinely climbed. (The harness mirrors `hermes_composes_multi_cell`'s
// `EmbeddedWorld`, specialised to the single-cell counter-fire path: the
// `AttachedApplet::fire` counter bump already carries its own `IncrementNonce`, so
// this sink commits the fire's effects AS-GIVEN — it does NOT add a second one.)

struct EmbeddedWorld {
    engine: DreggEngine,
    prev: Option<[u8; 32]>,
}

impl EmbeddedWorld {
    fn new() -> Self {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        EmbeddedWorld { engine, prev: None }
    }

    /// Seed an OPEN, funded agent cell with its counter slot at 0 (open perms so the
    /// counter-bump `SetField` turn authorizes — the agent drives its OWN cell).
    fn seed_agent(&mut self, pk: [u8; 32], tok: [u8; 32]) -> CellId {
        let mut agent_cell = Cell::with_balance(pk, tok, 1_000_000);
        agent_cell.permissions = open_permissions();
        let id = agent_cell.id();
        self.engine
            .ledger_mut()
            .insert_cell(agent_cell)
            .expect("seed the agent cell");
        id
    }

    fn field_u64(&self, cell: &CellId, slot: usize) -> u64 {
        self.engine
            .ledger()
            .get(cell)
            .and_then(|c| c.state.get_field(slot))
            .map(|fe| {
                let mut b = [0u8; 8];
                b.copy_from_slice(&fe[..8]);
                u64::from_le_bytes(b)
            })
            .unwrap_or(0)
    }
}

/// A `WorldSink` over a shared `Rc<RefCell<EmbeddedWorld>>` — the live ledger the
/// agent's affordance fires commit onto.
struct EmbeddedSink {
    world: Rc<RefCell<EmbeddedWorld>>,
}

impl WorldSink for EmbeddedSink {
    fn with_ledger(&self, f: &mut dyn FnMut(&dregg_cell::Ledger)) {
        f(self.world.borrow().engine.ledger());
    }

    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        let mut w = self.world.borrow_mut();
        let nonce = w
            .engine
            .ledger()
            .get(&agent)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        // Commit the fire's effects AS-GIVEN (the counter-bump fire already carries its
        // own `IncrementNonce` — adding a second would double-bump). The turn's actor is
        // the agent's own cell; the chain head threads each fire onto the last.
        let mut action = ActionBuilder::new_unchecked_for_tests(agent, method, agent);
        for e in effects {
            action = action.effect(e);
        }
        let action = action.build();
        let mut tb = TurnBuilder::new(agent, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = w.prev {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();
        let receipt = w.engine.execute_turn(&turn).map_err(|e| e.to_string())?;
        let rh = receipt.receipt_hash();
        w.prev = Some(rh);
        Ok(rh)
    }
}

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

// ───────────────────────────── the grantor + market ──────────────────────────

/// deos the grantor: the runtime that admits the agent's `run_js` worker, runs its
/// metered+charged accountability turns, and holds the provider cell that is paid.
fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// deos's tool/model provider cell — the agent pays it per `run_js` tool-call.
fn spawn_provider(runtime: &AgentRuntime, root: &HeldToken) -> CellId {
    runtime
        .spawn_sub_agent_scoped(&Attenuation::default(), root, &["provide"])
        .expect("spawn provider")
        .cell_id()
}

fn balance(runtime: &AgentRuntime, cell: CellId) -> i64 {
    let l = runtime.ledger().lock().unwrap();
    l.get(&cell).map(|c| c.state.balance()).unwrap_or(0)
}

/// A scoped `run_js` grant with ample RATE head-room — so the binding limit in this
/// test is the SPEND budget (the economy), not the rate ceiling.
fn session_registry() -> GrantRegistry {
    GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000)
}

/// The price per `run_js` tool-call and the spend allowance: three paid calls
/// (3 × 1_000 = 3_000), then over-budget on the fourth (3_000 + 1_000 > 3_500).
const PRICE: u64 = 1_000;
const BUDGET: u64 = 3_500;

/// The agent's affordance surface: `inc` (gated Signature, which the agent's
/// Signature `held` satisfies → fires). A fire bumps the counter slot by its arg.
fn agent_tool(pk: [u8; 32], tok: [u8; 32]) -> RunJsTool {
    RunJsTool::new(
        AuthRequired::Signature,
        pk,
        tok,
        vec![(0, deos_js::applet::pack_u64(0))],
        vec![("inc".to_string(), AuthRequired::Signature)],
    )
}

/// The agent's chosen JS for one step: fire `inc(+1)` on the live World — a real
/// cap-gated verified turn. (The crawl read confers no authority; the fire is the
/// work that costs.)
const STEP_JS: &str = r#"
    var app = deos.applet({ affordances: ["inc"] });
    app.inc(1);
"#;

#[test]
fn paid_agent_does_real_multi_step_world_work_then_is_cut_off_over_budget() {
    // ONE process-global SpiderMonkey engine, shared across both scenarios (its init
    // is one-shot). The ACP scenario (c) runs LAST because it consumes the runtime.
    let mut js = JsRuntime::new().expect("boot SpiderMonkey once");

    // ── (a) PAID REAL WORK + (b) BUDGET BITES — direct `run_attached_on` ──────────
    {
        let (runtime, root) = grantor();
        let provider = spawn_provider(&runtime, &root);
        let market = ToolMarket::flat(provider, PRICE, BUDGET);
        let mut gw = HermesGateway::new_paid(&runtime, root, session_registry(), market);

        let world = Rc::new(RefCell::new(EmbeddedWorld::new()));
        let agent = world.borrow_mut().seed_agent([0x42; 32], [0x01; 32]);
        let tool = agent_tool([0x42; 32], [0x01; 32]);

        let p0 = balance(&runtime, provider);

        // THREE steps of real, accumulating work on the live World — each a separately
        // charged tool-call AND a real verified turn (the counter climbs 1 → 2 → 3).
        for step in 1..=3i64 {
            let sink = Box::new(EmbeddedSink {
                world: world.clone(),
            });
            let call = ToolCallRequest::new(
                "sess",
                &format!("tc-step-{step}"),
                "run_js",
                serde_json::json!({ "script": "fire inc(+1) on the live world" }),
            );
            let o = tool
                .run_attached_on(&mut js, sink, agent, &mut gw, &call, 50, STEP_JS)
                .expect("run_js boots");

            // The tool-call was admitted (a metered, CHARGED accountability turn) and the
            // verdict records the price paid this step.
            match &o.tool_outcome {
                PermissionOutcome::Allow { paid, receipt, .. } => {
                    assert_eq!(
                        *paid, PRICE,
                        "step {step}: the verdict records the per-call charge"
                    );
                    assert_eq!(
                        receipt.len(),
                        64,
                        "step {step}: a real hex turn-hash receipt"
                    );
                }
                other => panic!("step {step} must be allowed + charged, got {other:?}"),
            }
            assert!(
                o.js_error.is_none(),
                "step {step} JS ran cleanly: {:?}",
                o.js_error
            );

            // THE WORK LANDED — exactly one verified turn on the live World this step.
            assert_eq!(
                o.fires_committed, 1,
                "step {step}: the agent's JS fired one affordance = one verified turn on the live World"
            );
            // THE CHARGE LANDED, conserved consumer → provider: the provider is paid
            // exactly `step × PRICE` so far.
            assert_eq!(
                balance(&runtime, provider),
                p0 + (step as u64 * PRICE) as i64,
                "step {step}: the provider is credited the per-call price (conserved)"
            );
            assert_eq!(
                gw.total_spent(),
                step as u64 * PRICE,
                "step {step}: session spend tracks the cumulative charge"
            );
            // A RE-READ OFF THE LIVE LEDGER proves the counter genuinely climbed.
            assert_eq!(
                world.borrow().field_u64(&agent, 0),
                step as u64,
                "step {step}: the live World counter climbed to {step}"
            );
        }

        // ── (b) THE FOURTH STEP — over budget (3_000 spent + 1_000 > 3_500). ─────────
        let sink = Box::new(EmbeddedSink {
            world: world.clone(),
        });
        let call4 = ToolCallRequest::new(
            "sess",
            "tc-step-4",
            "run_js",
            serde_json::json!({ "script": "fire inc(+1) on the live world" }),
        );
        let o4 = tool
            .run_attached_on(&mut js, sink, agent, &mut gw, &call4, 50, STEP_JS)
            .expect("run_js boots");

        // REFUSED IN-BAND naming the budget leg — no JS ran, no fire committed.
        match &o4.tool_outcome {
            PermissionOutcome::Reject { reason, .. } => {
                assert!(
                    reason.contains("budget exhausted"),
                    "the fourth step is refused naming the budget leg: {reason}"
                );
            }
            other => panic!("the fourth step must be refused over-budget, got {other:?}"),
        }
        assert_eq!(o4.fires_committed, 0, "the over-budget step fired nothing");
        // THE WORLD IS FROZEN where the budget ran out: the counter stays at 3.
        assert_eq!(
            world.borrow().field_u64(&agent, 0),
            3,
            "the live World is untouched by the refused step — frozen at 3"
        );
        // The refusal paid the provider nothing and advanced no spend.
        assert_eq!(
            balance(&runtime, provider),
            p0 + 3 * PRICE as i64,
            "an over-budget refusal pays the provider nothing"
        );
        assert_eq!(
            gw.total_spent(),
            3 * PRICE,
            "an over-budget refusal does not spend"
        );
    }

    // ── (c) THE SAME PAID BOUND, END-TO-END OVER ACP via `LiveJsHands` ────────────
    // A real `AcpClient` session dispatches four `run_js` calls (the brain's decided
    // `inc(+1)` script) through `LiveJsHands` over a PAID gateway. The first three
    // commit + charge; the fourth is rejected over-budget over the ACP wire. The
    // MockHermesPeer is the faithful scripted-brain stand-in (it frames each call
    // exactly as the real `acp_adapter` would). Runs LAST — it consumes `js`.
    {
        let (runtime, root) = grantor();
        let provider = spawn_provider(&runtime, &root);
        let market = ToolMarket::flat(provider, PRICE, BUDGET);
        let gw = HermesGateway::new_paid(&runtime, root, session_registry(), market);

        let world = Rc::new(RefCell::new(EmbeddedWorld::new()));
        let agent = world.borrow_mut().seed_agent([0x77; 32], [0x02; 32]);
        let tool = agent_tool([0x77; 32], [0x02; 32]);

        let p0 = balance(&runtime, provider);

        // The sink factory hands a fresh sink over the SAME live World each call.
        let world_for_factory = world.clone();
        let sink_factory = move || -> Box<dyn WorldSink> {
            Box::new(EmbeddedSink {
                world: world_for_factory.clone(),
            })
        };

        // SpiderMonkey is already booted; thread the test's runtime in via `with_runtime`
        // rather than booting another (which would error `AlreadyInitialized`).
        let hands = LiveJsHands::with_runtime(tool, agent, gw, sink_factory, js);

        // Four `run_js` calls — the brain's decided `inc(+1)` script each time.
        let calls: Vec<ScriptedCall> = (1..=4)
            .map(|_| ScriptedCall::new("run_js", serde_json::json!({ "script": STEP_JS })))
            .collect();
        let peer = MockHermesPeer::new("sess-paid", calls);

        let (rt_s, root_s) = grantor();
        let session_gw = HermesGateway::new(&rt_s, root_s, session_registry());
        let mut client = AcpClient::new(peer, session_gw, 10).with_run_js_hook(hands.into_hook());

        let run = client
            .run_prompt("/tmp", "Bump the counter by one, four times.")
            .expect("the ACP session drives the four run_js calls");

        // Four permission round-trips: the first three admitted, the fourth rejected.
        assert_eq!(run.verdicts.len(), 4, "four run_js permission round-trips");
        for (i, (_, verdict)) in run.verdicts.iter().enumerate() {
            if i < 3 {
                assert!(
                    verdict.allowed(),
                    "ACP step {} admitted + charged: {verdict:?}",
                    i + 1
                );
            } else {
                match verdict {
                    PermissionOutcome::Reject { reason, .. } => assert!(
                        reason.contains("budget exhausted"),
                        "the fourth ACP step is rejected over-budget: {reason}"
                    ),
                    other => panic!("the fourth ACP step must be rejected, got {other:?}"),
                }
            }
        }

        // The hook recorded four runs; the first three each landed a real receipt on the
        // live World, the fourth landed none (rejected before any JS ran).
        let js_runs = client.js_runs();
        assert_eq!(js_runs.len(), 4, "four run_js runs recorded");
        for (i, rec) in js_runs.iter().enumerate() {
            if i < 3 {
                assert_eq!(
                    rec.fires_committed,
                    1,
                    "ACP step {} fired one verified turn",
                    i + 1
                );
                assert!(
                    rec.receipts.len() == 1 && rec.receipts[0] != [0u8; 32],
                    "ACP step {} left a real receipt on the live World",
                    i + 1
                );
            } else {
                assert_eq!(
                    rec.fires_committed, 0,
                    "the rejected fourth ACP step fired nothing"
                );
            }
        }

        // The provider was paid for exactly the three admitted steps, and the live World
        // is frozen at 3 — the economy bounded the live-decide loop end-to-end over ACP.
        assert_eq!(
            balance(&runtime, provider),
            p0 + 3 * PRICE as i64,
            "the provider is paid for the three admitted ACP steps only"
        );
        assert_eq!(
            world.borrow().field_u64(&agent, 0),
            3,
            "the live World is frozen at 3 — the fourth step never bought its work"
        );
    }
}
