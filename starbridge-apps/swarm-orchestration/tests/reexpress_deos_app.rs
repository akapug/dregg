//! RE-EXPRESSION proof: the `swarm-orchestration` starbridge-app, on the composed
//! deos framework — **the same app, smaller + more capable.**
//!
//! `docs/deos/DEOS-APPS.md` (the plan §4): "Re-express 1-2 existing apps on the new
//! framework to prove the composition (the supply-chain / orchestration apps become
//! *integrated* deos apps)." This is that proof for `swarm-orchestration` (a
//! COORDINATOR dispatch-board cell holds a conserved budget + a mandate and
//! dispatches sub-tasks to WORKER cells via cap-attenuated grants; workers ack on the
//! async notify edge; an over-grant is REFUSED by the verified executor — see
//! `src/lib.rs`, ~564 lines). DEOS-APPS.md §5 names this app directly: "The
//! swarm-orchestration app gestures at [agent-as-first-class-user]." The composition
//! makes the gesture real: the affordance set IS an agent's attenuated action space,
//! and a per-viewer projection means a worker LITERALLY sees only the affordances its
//! tier authorizes.
//!
//! Its USER-FACING surface is a small set of cap-gated operations on the dispatch
//! board, on THREE rights tiers that ARE the swarm's own roles:
//!
//!   - an OBSERVER (an operator auditing a swarm she did not write — the doc's
//!     "narration-vs-truth" reader) holds `Signature` — the narrow tier: it can
//!     `view_board` (read the lead / budget / spend meters / epoch) and nothing else;
//!   - a WORKER (a dispatched agent cell) holds `Either` — it can `ack_dispatch`
//!     (the async drain: write a content-addressed ack in its own receipted turn) AND
//!     view;
//!   - the LEAD / OPERATOR holds `None`/root — it can `open_board` (pin the lead +
//!     mandate) and `dispatch` (advance a worker's spend meter + wake the worker) on
//!     top of everything a worker can do.
//!
//! So `Signature ⊂ Either ⊂ None` IS the swarm's observer ⊂ worker ⊂ lead ladder.
//! The constraint discipline the floor crate proves (`swarm_constraints()`: the
//! `AffineLe` two-meter budget gate `spent_a + spent_b <= budget`, `WriteOnce`
//! lead/budget, `Monotonic` meters, `StrictMonotonic` epoch) is PRESERVED — it is the
//! board cell's `CellProgram`, re-checked by the executor on every dispatch. This file
//! proves the SAME app gains the deos composition's capabilities; the floor crate's
//! `src` tests + `factory_birth.rs` prove the caveats bite, and
//! [`the_budget_gate_still_refuses_an_overrun`] checks the budget tooth is the same one.
//!
//! ## On the OLD bones vs the COMPOSED bones
//!
//! On the OLD bones (`src/lib.rs::register`), the app wired: a hand-rolled
//! `FactoryDescriptor` + an `InspectorDescriptor` + per-method turn-builders
//! (`build_open_board_action` / `build_dispatch_action` / `build_drain_action`) + a
//! hand-copied `web_constants()` JS module + (no per-viewer projection, no
//! web-of-cells publish of the board cell as a sturdyref, no rehydration, no generated
//! web component, no manifest).
//!
//! On the COMPOSED bones, the same operations are ONE [`DeosApp`] builder
//! ([`board_app`] below) — and the framework wires the rest:
//!
//!   - **smaller**: the whole interaction surface is one `AppSpec` / `DeosApp::builder`
//!     (~25 lines) vs. the hand-wired factory + inspector + webgen the floor needed;
//!   - **more capable**: it gains the per-viewer projection (an observer sees only
//!     `view_board`; a worker sees `ack_dispatch` too; the lead sees all of it — the
//!     attenuated action space made VISIBLE), the web-of-cells publish (the board cell
//!     IS a distributed sturdyref a federated peer reacquires), the rehydratable
//!     frustum-snapshot (a peer re-expands a fog-respecting view of the board), the
//!     generated `<dregg-affordance-surface>` web component, and the manifest — NONE of
//!     which the floor had.
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn
//! through the embedded executor; the gate is the genuine [`is_attenuation`]. No
//! parallel model. **Honest seam:** mapping a fired affordance onto a live
//! `dregg_turn::TurnExecutor` running the FULL dispatch `CellProgram` (so the
//! `AffineLe` budget gate bites IN the fire path) is the inherited seam
//! `affordance.rs` names — today the fire executes a real turn against the agent's
//! seeded cell, and the floor crate's `src` tests prove the budget gate on the executor.

use dregg_app_framework::{
    AppSpec, AffordanceSpec, AuthRequired, CapTpServer, CellAffordance, CapabilityRef, DeosApp,
    DeosCell, Effect, EffectSummary, EmbeddedExecutor, Event, FederationId, Interaction,
    InteractionLog, Rehydration, RehydrateError, AgentCipherclerk, AppCipherclerk, CellId,
};

use starbridge_swarm_orchestration::{
    BUDGET_SLOT, EPOCH_SLOT, SPENT_A_SLOT, Worker, dispatch_within_budget,
};

// =============================================================================
// The swarm dispatch board, re-expressed as a composed deos app
// =============================================================================

// The swarm rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles the
// floor crate's cap-graph enforces (a worker holds only its attenuated slice):
//   - an OBSERVER (operator auditing the swarm) holds `Signature` (the narrow read tier);
//   - a WORKER (dispatched agent) holds `Either` (sig-or-proof — ack + view);
//   - the LEAD / OPERATOR holds `None`/root (open the board, dispatch, +all).
// So `Signature ⊂ Either ⊂ None`: observer ⊂ worker ⊂ lead.
const OBSERVER: &str = "signature";
const WORKER: &str = "either";
const LEAD: &str = "none";

/// The swarm dispatch board as a declarative spec — the cap-gated operations on the
/// COORDINATOR cell, published into the web-of-cells, discoverable. The builder writes
/// the affordances; the framework wires the rest.
///
/// The effects are the deos-scaffold shapes (`emit`/`edit`) standing for the real
/// dispatch turns: `dispatch` writes a worker's spend meter (the `SPENT_A` slot the
/// `AffineLe` gate sums), `open_board` pins the `BUDGET` mandate (the `WriteOnce`
/// ceiling), the reads/acks emit the events the floor crate's `web_constants()` named
/// (`swarm-board-opened`, `dispatch-acked`). The RICH dispatch turn (the multi-effect
/// dispatch that advances the meter AND the epoch AND emits the async wake) and the
/// lead's attenuated worker-cap grant drop to raw `CellAffordance`s — see
/// [`the_rich_dispatch_and_the_worker_grant_drop_to_raw_affordances`].
fn board_spec() -> AppSpec {
    AppSpec::new("swarm-orchestration")
        .cell(
            dregg_app_framework::CellSpec::new("board")
                // view_board: an OBSERVER (Signature) reads the lead/budget/meters/epoch
                // (the narration-vs-truth audit surface).
                .affordance(AffordanceSpec::emit("view_board", OBSERVER, "board-read"))
                // ack_dispatch: a WORKER (Either) drains a wake in its own receipted turn
                // (the async notify edge's ack side).
                .affordance(AffordanceSpec::emit("ack_dispatch", WORKER, "dispatch-acked"))
                // dispatch: the LEAD (root) advances a worker's spend meter (the
                // `AffineLe`-summed `SPENT_A` slot). The real turn also bumps the epoch
                // and wakes the worker; the raw-affordance test shows the full shape.
                .affordance(AffordanceSpec::edit("dispatch", LEAD, SPENT_A_SLOT as usize))
                // open_board: the LEAD (root) pins the `BUDGET` mandate (the WriteOnce ceiling).
                .affordance(AffordanceSpec::edit("open_board", LEAD, BUDGET_SLOT as usize))
                // the board cell IS a distributed cell — publish it into the web-of-cells
                // at the observer tier (a sturdyref bearer can at least audit the board).
                .publish(OBSERVER),
        )
        .discoverable(vec!["orchestration".into(), "swarm".into()])
}

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn board_app(cclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    board_spec()
        .into_app(cclerk.clone(), executor.clone())
        .expect("the swarm board spec is valid")
}

// =============================================================================
// SMALLER: the whole surface is one builder, registered in one fold
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);

    // ONE app, ONE cell, FOUR affordances — the entire interaction surface.
    assert_eq!(app.name(), "swarm-orchestration");
    assert_eq!(app.cells().len(), 1);
    let board = &app.cells()[0];
    assert_eq!(
        board.surface().all_names(),
        vec![
            "ack_dispatch".to_string(),
            "dispatch".to_string(),
            "open_board".to_string(),
            "view_board".to_string(),
        ]
    );
    // The board cell is the agent's own (so fires execute against the seeded ledger).
    assert_eq!(board.cell(), cclerk.cell_id());
    // Published into the web-of-cells at the observer tier.
    assert_eq!(board.published_authority(), Some(&AuthRequired::Signature));

    // ONE registration folds the whole surface into a shared host context — the
    // composed `register(ctx)`, where the floor needed factory + inspector + webgen
    // as separate verbs.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection — the attenuated action space, VISIBLE
// =============================================================================

#[tokio::test]
async fn the_three_swarm_roles_see_different_action_spaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/board/projected")
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone()
    }

    // An OBSERVER (Signature) sees only `view_board` — it can AUDIT the board (the
    // narration-vs-truth reader) but cannot dispatch, open, or even ack.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_board"])
    );
    // A WORKER (Either) additionally sees `ack_dispatch` — its attenuated action space:
    // it can drain a wake, but it CANNOT dispatch (it is not the lead). This IS
    // DEOS-APPS.md §5's "the affordance set is an agent's attenuated action space."
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["ack_dispatch", "view_board"])
    );
    // The LEAD (root) sees ALL FOUR (open + dispatch, too).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["ack_dispatch", "dispatch", "open_board", "view_board"])
    );
    // The floor's swarm app had NO per-viewer projection — this is new capability.
}

// =============================================================================
// MORE CAPABLE (2): fires are real verified turns; anti-ghost holds
// =============================================================================

#[tokio::test]
async fn the_lead_dispatches_a_worker_cannot() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let router = app.mount();

    // The LEAD (root) fires `dispatch` (req None): authorized → the real SetField turn
    // (advancing a worker's spend meter) executes through the embedded executor.
    let dispatched = router
        .clone()
        .oneshot(
            Request::post("/board/fire/dispatch")
                .header(dregg_app_framework::HELD_RIGHTS_HEADER, "root")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(dispatched.status(), StatusCode::OK, "the lead dispatches");
    let bytes = axum::body::to_bytes(dispatched.into_body(), usize::MAX).await.unwrap();
    let body: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(body["fired"], "dispatch");
    assert_ne!(body["turn_hash"].as_str().unwrap(), "0".repeat(64), "a real turn");

    // A WORKER (Either) firing `dispatch` is 403 — REFUSED by the real gate, nothing
    // executed (anti-ghost). A worker cannot self-dispatch budget; only the lead
    // dispatches. The cap discipline is the SAME in-band gate (the no-amplification
    // guarantee firing at the swarm layer).
    let refused = router
        .oneshot(
            Request::post("/board/fire/dispatch")
                .header(dregg_app_framework::HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(refused.status(), StatusCode::FORBIDDEN, "a worker cannot dispatch");
}

#[tokio::test]
async fn a_worker_acks_an_observer_cannot() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> axum::http::StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/board/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // A WORKER (Either) acks a dispatch (the async drain) — a real turn.
    assert_eq!(fire(&router, "ack_dispatch", "either").await, StatusCode::OK);
    // An OBSERVER (Signature) cannot ack — it only audits; the ack is a worker's own
    // receipted turn, not an observer's.
    assert_eq!(fire(&router, "ack_dispatch", "signature").await, StatusCode::FORBIDDEN);
    // Nor can an observer open the board.
    assert_eq!(fire(&router, "open_board", "signature").await, StatusCode::FORBIDDEN);
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the board cell is a distributed sturdyref
// =============================================================================

#[tokio::test]
async fn the_board_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    let doc = cclerk.cell_id();
    // The same surface, but with a captp server attached (the web-of-cells minter).
    let captp = CapTpServer::new(FederationId([0x5a; 32]));
    let app = DeosApp::builder("swarm-orchestration", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(
            DeosCell::new(doc, "board")
                .affordance(CellAffordance::new(
                    "view_board",
                    AuthRequired::Signature,
                    Effect::EmitEvent {
                        cell: doc,
                        event: Event { topic: [1u8; 32], data: vec![] },
                    },
                ))
                .publish(AuthRequired::Signature),
        )
        .build();

    // The board cell is exported as a real `dregg://` sturdyref — a federated peer
    // reacquires the dispatch board across the membrane. The floor's swarm app never
    // published its board cell into the web-of-cells (DEOS-APPS.md §4's
    // distributed-app gap).
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(uris[0].starts_with("dregg://"), "a real sturdyref: {}", uris[0]);
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the board, per-viewer
// =============================================================================

#[test]
fn a_board_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let board = &app.cells()[0];

    // Snapshot the board. It witnessed a dispatch turn (a real, non-zero turn hash),
    // and the sources are gone (a cold snapshot handed to a downstream auditor) ⇒ the
    // liveness-type is REPLAYED-DETERMINISTIC (the confined fragment), DERIVED from the
    // witness-log.
    let log =
        InteractionLog::new().record(Interaction::witnessed_turn(board.cell(), [9u8; 32]));
    let snap = board.snapshot(log, false);
    assert_eq!(snap.lineage, AuthRequired::Signature, "snapshot at the published lineage");
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // An OBSERVER (Signature) rehydrating the snapshot reacquires only `view_board` —
    // the board snapshot respects the lattice; it cannot leak the lead's dispatch /
    // open affordances to a downstream auditor.
    let observer = board.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(observer.visible_names(), vec!["view_board".to_string()]);

    // A viewer holding an INCOMPARABLE authority (a distinct Custom identity — e.g. a
    // member of a different federation's incomparable role) cannot rehydrate at all —
    // the membrane mints NO projection.
    let blocked = board.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
    assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
}

// =============================================================================
// MORE CAPABLE (5): the generated web component + the manifest
// =============================================================================

#[tokio::test]
async fn the_app_ships_a_web_component_surface_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component — generated
    // from the Rust source of truth. The floor's swarm app hand-wrote its JS
    // (`web_constants()`).
    let surface = router
        .clone()
        .oneshot(Request::get("/surface.js").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(surface.status(), StatusCode::OK);
    let ct = surface
        .headers()
        .get(axum::http::header::CONTENT_TYPE)
        .unwrap()
        .to_str()
        .unwrap()
        .to_string();
    assert!(ct.contains("javascript"), "served as a JS module: {ct}");
    let bytes = axum::body::to_bytes(surface.into_body(), usize::MAX).await.unwrap();
    let js = String::from_utf8(bytes.to_vec()).unwrap();
    assert!(js.contains("customElements.define(\"dregg-affordance-surface\""));
    // The anti-drift affordance map names the board's fire endpoints.
    assert!(js.contains("fireEndpoint: \"/board/fire/dispatch\","));
    assert!(js.contains("fireEndpoint: \"/board/fire/view_board\","));

    // GET /manifest serves the whole composed surface.
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX).await.unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "swarm-orchestration");
    assert_eq!(m["discoverable"], serde_json::json!(["orchestration", "swarm"]));
    // The persistence seam is VISIBLE (honest) — embedded ledger today; pg-dregg plugs in.
    assert!(m["persistence"].as_str().unwrap().contains("embedded-ledger"));
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
}

// =============================================================================
// PRESERVED: the conserved two-meter budget gate is the SAME one the floor proves
// =============================================================================

#[test]
fn the_budget_gate_still_refuses_an_overrun() {
    // The deos re-expression does NOT replace the floor crate's budget discipline — it
    // composes a richer surface ON it. The two-meter affine bound `spent_a + spent_b
    // <= budget` is the floor crate's REAL gate (the executor's `AffineLe` clause), and
    // a dispatch that would breach it is refused BEFORE it runs (fail-closed). A
    // dispatch fired through an affordance is summed against this same ceiling.
    //
    // budget 1000; A at 600, a 300-to-B fits (900 <= 1000); a 500-to-B breaches.
    assert!(dispatch_within_budget(0, 300, 600, 1000), "900 <= 1000 admitted");
    assert!(!dispatch_within_budget(0, 500, 600, 1000), "1100 > 1000 REFUSED — the budget tooth");
    // The two meters are distinct columns the gate sums (no single-field counter sees it).
    assert_ne!(Worker::A.spend_slot(), Worker::B.spend_slot());
    assert_eq!(Worker::A.spend_slot(), SPENT_A_SLOT);
}

// =============================================================================
// The escape hatch: the RICH dispatch + the worker grant still compose as raw
// =============================================================================

#[test]
fn the_rich_dispatch_and_the_worker_grant_drop_to_raw_affordances() {
    // The spec scaffold covers the common shapes (emit/edit). The REAL dispatch is
    // richer — it advances a worker's meter AND the epoch AND emits the async wake on
    // the WORKER cell in ONE turn — and the lead handing a worker an ATTENUATED slice is
    // a real `Effect::GrantCapability` (the `derive_no_amplify` worker delegation). Both
    // drop to a raw `CellAffordance` — still composed, still cap-gated, still through
    // the same mount. The scaffold is a convenience, not a ceiling.
    let (cclerk, executor) = agent();
    let board = cclerk.cell_id();
    let worker_cell = CellId::from_bytes([0x9a; 32]);

    // The lead's real worker delegation: GrantCapability of an ATTENUATED slice to the
    // worker cell (Signature — narrower than the lead's authority; no amplification).
    let grant_worker = Effect::GrantCapability {
        from: board,
        to: worker_cell,
        cap: CapabilityRef {
            target: board,
            slot: SPENT_A_SLOT as u32,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    };
    // The real async wake: an EmitEvent targeting the WORKER cell (not the board) — the
    // notify edge the worker drains in its own turn.
    let wake = Effect::EmitEvent {
        cell: worker_cell,
        event: Event { topic: [2u8; 32], data: vec![] },
    };

    let app = DeosApp::builder("swarm-orchestration", cclerk.clone(), executor)
        .cell(
            DeosCell::new(board, "board")
                .affordance(CellAffordance::new("grant_worker", AuthRequired::None, grant_worker))
                .affordance(CellAffordance::new("wake_worker", AuthRequired::None, wake)),
        )
        .build();
    let cell = &app.cells()[0];
    // The lead's worker-cap grant is the real GrantCapability (board -> worker).
    assert_eq!(
        cell.surface().get("grant_worker").unwrap().effect_summary(),
        EffectSummary::GrantCapability { from: board, to: worker_cell }
    );
    // The async wake targets the WORKER cell (the notify edge), not the board.
    assert_eq!(
        cell.surface().get("wake_worker").unwrap().effect_summary(),
        EffectSummary::EmitEvent { cell: worker_cell }
    );
}
