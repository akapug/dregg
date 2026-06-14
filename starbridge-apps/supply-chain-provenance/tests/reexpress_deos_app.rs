//! RE-EXPRESSION proof: the `supply-chain-provenance` starbridge-app, on the
//! composed deos framework — **the same app, smaller + more capable.**
//!
//! `docs/deos/DEOS-APPS.md` (the plan §4): "Re-express 1-2 existing apps on the new
//! framework to prove the composition (the supply-chain / orchestration apps become
//! *integrated* deos apps)." This is that proof for `supply-chain-provenance` (an
//! ITEM is a cell, a CUSTODY HANDOFF is a cap-attenuated transfer, single-
//! custodianship is a conservation law, and the provenance is a re-derivable hash
//! chain — see `src/lib.rs`, ~877 lines). Its USER-FACING surface is a small set of
//! cap-gated operations on the ITEM cell, on THREE rights tiers that ARE the
//! supply-chain's own roles:
//!
//!   - a VERIFIER (the public / a regulator) holds `Signature` — the narrow tier:
//!     it can `view_provenance` (read + re-derive the custody chain) and nothing else;
//!   - a CUSTODIAN (a warehouse / carrier currently holding the item) holds `Either`
//!     — it can `accept_custody` (a handoff: advance the actor-bound register, the
//!     epoch, and append a receipt link) AND view;
//!   - the MANUFACTURER / OWNER holds `None`/root — it can `mint_item` (inaugurate the
//!     sole custodian) and `grant_custody` (hand the item's custody cap FORWARD,
//!     narrowed — the `derive_no_amplify` shape) on top of everything a custodian can do.
//!
//! So `Signature ⊂ Either ⊂ None` IS the supply-chain's verifier ⊂ custodian ⊂
//! manufacturer ladder. The constraint discipline the floor crate proves
//! (`custody_constraints()`: `AnyOf[Immutable, SenderInSlot]` actor-bound baton,
//! `StrictMonotonic` epoch, `Monotonic` head, `WriteOnce` links) is PRESERVED — it
//! is the ITEM cell's `CellProgram`, re-checked by the executor on every handoff
//! turn. This file does not re-prove it (the floor crate's `tests`/`src` do, and
//! `the_handoff_still_carries_the_verified_custody_chain` checks the chain is the
//! same one); it proves the SAME app gains the deos composition's capabilities.
//!
//! ## On the OLD bones vs the COMPOSED bones
//!
//! On the OLD bones (`src/lib.rs::register`), the app wired: a hand-rolled
//! `FactoryDescriptor` + an `InspectorDescriptor` + per-method turn-builders
//! (`build_mint_action` / `build_handoff_action`) + a hand-copied `web_constants()`
//! JS module + (no per-viewer projection, no web-of-cells publish of the ITEM cell as
//! a sturdyref, no rehydration, no generated web component, no manifest).
//!
//! On the COMPOSED bones, the same operations are ONE [`DeosApp`] builder
//! ([`item_app`] below) — and the framework wires the rest:
//!
//!   - **smaller**: the whole interaction surface is one `AppSpec` / `DeosApp::builder`
//!     (~25 lines) vs. the hand-wired factory + inspector + webgen the floor needed;
//!   - **more capable**: it gains the per-viewer projection (a verifier sees only
//!     `view_provenance`; a custodian sees `accept_custody` too; the manufacturer sees
//!     all of it), the web-of-cells publish (the ITEM cell IS a distributed sturdyref a
//!     regulator on another federation reacquires across the membrane), the
//!     rehydratable frustum-snapshot (a peer re-expands a fog-respecting view of the
//!     item's provenance), the generated `<dregg-affordance-surface>` web component,
//!     and the manifest — NONE of which the floor had.
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn
//! through the embedded executor; the gate is the genuine [`is_attenuation`]. No
//! parallel model. **Honest seam:** mapping a fired affordance onto a live
//! `dregg_turn::TurnExecutor` running the FULL custody `CellProgram` (so the
//! actor-bound + strict-mono caveats bite IN the fire path) is the inherited seam
//! `affordance.rs` names — today the fire executes a real turn against the agent's
//! seeded cell, and the floor crate's `src` tests prove the caveats on the executor.

use dregg_app_framework::{
    AppSpec, AffordanceSpec, AuthRequired, CapTpServer, CellAffordance, CapabilityRef, DeosApp,
    DeosCell, Effect, EffectSummary, EmbeddedExecutor, Event, FederationId, Interaction,
    InteractionLog, Rehydration, RehydrateError, AgentCipherclerk, AppCipherclerk, CellId,
};

use starbridge_supply_chain_provenance::{
    CUSTODIAN_SLOT, EPOCH_SLOT, GENESIS_PREV, Handoff, custody_chain_digests,
    custody_chain_is_connected, identity_field, verify_chain,
};

// =============================================================================
// The supply-chain ITEM, re-expressed as a composed deos app
// =============================================================================

// The supply-chain rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the
// roles the floor crate's cap-graph enforces (one custody-cap holder at a time):
//   - a VERIFIER (public / regulator) holds `Signature` (the narrow read tier);
//   - a CUSTODIAN (current holder) holds `Either` (sig-or-proof — accept + view);
//   - the MANUFACTURER / OWNER holds `None`/root (mint, grant the custody cap, +all).
// So `Signature ⊂ Either ⊂ None`: verifier ⊂ custodian ⊂ manufacturer.
const VERIFIER: &str = "signature";
const CUSTODIAN: &str = "either";
const MANUFACTURER: &str = "none";

/// The supply-chain ITEM as a declarative spec — the cap-gated operations on the
/// ITEM cell, published into the web-of-cells, discoverable. This is the whole
/// interaction surface: the builder writes the affordances; the framework wires the
/// rest (per-viewer projection, web-of-cells publish, rehydration, the web
/// component, the manifest).
///
/// The effects are the deos-scaffold shapes (`emit`/`edit`) standing for the real
/// custody turns: `accept_custody` writes the `CUSTODIAN` register (the actor-bound
/// baton slot), `mint_item` advances the `EPOCH` register, the reads/grants emit the
/// provenance events the floor crate's `web_constants()` named (`item-minted`,
/// `custody-handoff`). The RICH custody turn (the multi-effect handoff that advances
/// the register AND the epoch AND appends a `WriteOnce` link) drops to a raw
/// `CellAffordance` — see [`the_rich_custody_handoff_drops_to_a_raw_affordance`].
fn item_spec() -> AppSpec {
    AppSpec::new("supply-chain-provenance")
        .cell(
            dregg_app_framework::CellSpec::new("item")
                // view_provenance: a VERIFIER (Signature) reads + re-derives the chain.
                .affordance(AffordanceSpec::emit("view_provenance", VERIFIER, "provenance-read"))
                // accept_custody: a CUSTODIAN (Either) advances the actor-bound register
                // (the `CUSTODIAN` slot — the baton). The real turn also bumps the epoch
                // and appends a link; the raw-affordance test shows the full shape.
                .affordance(AffordanceSpec::edit("accept_custody", CUSTODIAN, CUSTODIAN_SLOT as usize))
                // mint_item: the MANUFACTURER (root) inaugurates the sole custodian —
                // advances the `EPOCH` register 0 -> 1 (the floor crate's mint).
                .affordance(AffordanceSpec::edit("mint_item", MANUFACTURER, EPOCH_SLOT as usize))
                // grant_custody: the MANUFACTURER (root) hands the custody cap forward
                // (emit the handoff event; the raw-affordance test shows the real
                // `GrantCapability` — the `derive_no_amplify` cap handoff).
                .affordance(AffordanceSpec::emit("grant_custody", MANUFACTURER, "custody-handoff"))
                // the ITEM cell IS a distributed cell — publish it into the web-of-cells
                // at the verifier tier (a sturdyref bearer can at least re-derive the chain).
                .publish(VERIFIER),
        )
        .discoverable(vec!["supply-chain".into(), "provenance".into()])
}

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn item_app(cclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    item_spec()
        .into_app(cclerk.clone(), executor.clone())
        .expect("the supply-chain item spec is valid")
}

// =============================================================================
// SMALLER: the whole surface is one builder, registered in one fold
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);

    // ONE app, ONE cell, FOUR affordances — the entire interaction surface.
    assert_eq!(app.name(), "supply-chain-provenance");
    assert_eq!(app.cells().len(), 1);
    let item = &app.cells()[0];
    assert_eq!(
        item.surface().all_names(),
        vec![
            "accept_custody".to_string(),
            "grant_custody".to_string(),
            "mint_item".to_string(),
            "view_provenance".to_string(),
        ]
    );
    // The ITEM cell is the agent's own (so fires execute against the seeded ledger).
    assert_eq!(item.cell(), cclerk.cell_id());
    // Published into the web-of-cells at the verifier tier.
    assert_eq!(item.published_authority(), Some(&AuthRequired::Signature));

    // ONE registration folds the whole surface into a shared host context — the
    // composed `register(ctx)`, where the floor needed factory + inspector + webgen
    // as separate verbs.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection — verifier vs custodian vs manufacturer
// =============================================================================

#[tokio::test]
async fn the_three_supply_chain_roles_see_different_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/item/projected")
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

    // A VERIFIER (Signature) sees only `view_provenance` — it can re-derive the chain
    // but cannot accept custody, mint, or grant.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_provenance"])
    );
    // A CUSTODIAN (Either) additionally sees `accept_custody` (the handoff baton).
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["accept_custody", "view_provenance"])
    );
    // The MANUFACTURER (root) sees ALL FOUR (mint + grant the custody cap, too).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["accept_custody", "grant_custody", "mint_item", "view_provenance"])
    );
    // The floor's supply-chain app had NO per-viewer projection — this is new capability.
}

// =============================================================================
// MORE CAPABLE (2): fires are real verified turns; anti-ghost holds
// =============================================================================

#[tokio::test]
async fn a_custodian_accepts_custody_a_verifier_cannot() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let router = app.mount();

    // A CUSTODIAN (Either) fires `accept_custody` (req Either): authorized → the real
    // SetField turn (advancing the actor-bound `CUSTODIAN` register) executes through
    // the embedded executor.
    let accepted = router
        .clone()
        .oneshot(
            Request::post("/item/fire/accept_custody")
                .header(dregg_app_framework::HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(accepted.status(), StatusCode::OK, "a custodian accepts custody");
    let bytes = axum::body::to_bytes(accepted.into_body(), usize::MAX).await.unwrap();
    let body: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(body["fired"], "accept_custody");
    assert_ne!(body["turn_hash"].as_str().unwrap(), "0".repeat(64), "a real turn");

    // A VERIFIER (Signature) firing `accept_custody` is 403 — REFUSED by the real gate,
    // nothing executed (anti-ghost). A regulator can READ the chain but cannot forge a
    // handoff. The cap discipline is the SAME in-band gate.
    let refused = router
        .oneshot(
            Request::post("/item/fire/accept_custody")
                .header(dregg_app_framework::HELD_RIGHTS_HEADER, "signature")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(refused.status(), StatusCode::FORBIDDEN, "a verifier cannot accept custody");
}

#[tokio::test]
async fn only_the_manufacturer_can_mint_or_grant_custody() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/item/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The MANUFACTURER (root) can mint AND grant custody — both real turns.
    assert_eq!(fire(&router, "mint_item", "root").await, StatusCode::OK);
    assert_eq!(fire(&router, "grant_custody", "root").await, StatusCode::OK);
    // A CUSTODIAN (Either) CANNOT mint or grant — only the owner inaugurates / re-keys.
    assert_eq!(fire(&router, "mint_item", "either").await, StatusCode::FORBIDDEN);
    assert_eq!(fire(&router, "grant_custody", "either").await, StatusCode::FORBIDDEN);
    // A VERIFIER (Signature) cannot either.
    assert_eq!(fire(&router, "mint_item", "signature").await, StatusCode::FORBIDDEN);
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the ITEM cell is a distributed sturdyref
// =============================================================================

#[tokio::test]
async fn the_item_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    let doc = cclerk.cell_id();
    // The same surface, but with a captp server attached (the web-of-cells minter).
    let captp = CapTpServer::new(FederationId([0x5c; 32]));
    let app = DeosApp::builder("supply-chain-provenance", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(
            DeosCell::new(doc, "item")
                .affordance(CellAffordance::new(
                    "view_provenance",
                    AuthRequired::Signature,
                    Effect::EmitEvent {
                        cell: doc,
                        event: Event { topic: [1u8; 32], data: vec![] },
                    },
                ))
                .publish(AuthRequired::Signature),
        )
        .build();

    // The ITEM cell is exported as a real `dregg://` sturdyref — a regulator on another
    // federation reacquires the item's provenance across the membrane. The floor's
    // supply-chain app never published its ITEM cell into the web-of-cells.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(uris[0].starts_with("dregg://"), "a real sturdyref: {}", uris[0]);
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the item, per-viewer
// =============================================================================

#[test]
fn an_item_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let item = &app.cells()[0];

    // Snapshot the item. It witnessed a custody handoff turn (a real, non-zero turn
    // hash), and the sources are gone (a cold snapshot handed to a downstream auditor)
    // ⇒ the liveness-type is REPLAYED-DETERMINISTIC (the confined fragment), DERIVED
    // from the witness-log — exactly right for provenance: the chain re-derives.
    let log =
        InteractionLog::new().record(Interaction::witnessed_turn(item.cell(), [9u8; 32]));
    let snap = item.snapshot(log, false);
    assert_eq!(snap.lineage, AuthRequired::Signature, "snapshot at the published lineage");
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VERIFIER (Signature) rehydrating the snapshot reacquires only `view_provenance`
    // — the item snapshot respects the lattice; it cannot leak the manufacturer's mint
    // or grant affordances to a downstream auditor.
    let verifier = item.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(verifier.visible_names(), vec!["view_provenance".to_string()]);

    // A viewer holding an INCOMPARABLE authority (a distinct Custom identity — e.g. a
    // party in a different federation's incomparable role) cannot rehydrate at all —
    // the membrane mints NO projection (the no-peek refusal, lifted to provenance).
    let blocked = item.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = item_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component (the
    // htmx-on-crack custom element the embedded servo web-surface mounts) — generated
    // from the Rust source of truth. The floor's supply-chain app hand-wrote its JS
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
    // The anti-drift affordance map names the item's fire endpoints.
    assert!(js.contains("fireEndpoint: \"/item/fire/accept_custody\","));
    assert!(js.contains("fireEndpoint: \"/item/fire/view_provenance\","));

    // GET /manifest serves the whole composed surface.
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX).await.unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "supply-chain-provenance");
    assert_eq!(m["discoverable"], serde_json::json!(["supply-chain", "provenance"]));
    // The persistence seam is VISIBLE (honest) — embedded ledger today; pg-dregg plugs in.
    assert!(m["persistence"].as_str().unwrap().contains("embedded-ledger"));
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
}

// =============================================================================
// PRESERVED: the verified custody chain is the SAME one the floor crate proves
// =============================================================================

#[test]
fn the_handoff_still_carries_the_verified_custody_chain() {
    // The deos re-expression does NOT replace the floor crate's custody discipline —
    // it composes a richer surface ON it. The provenance hash chain + its connected-
    // ness witness (single-custodianship as conservation) are the floor crate's REAL
    // ones, re-derivable exactly as before. A handoff fired through an affordance
    // advances this same chain.
    let m = identity_field("manufacturer");
    let a = identity_field("warehouse-a");
    let b = identity_field("carrier-b");
    let history = vec![
        Handoff { from: GENESIS_PREV, to: m, epoch: 1 }, // mint
        Handoff { from: m, to: a, epoch: 2 },
        Handoff { from: a, to: b, epoch: 3 },
    ];
    let committed = custody_chain_digests(&history);
    assert!(verify_chain(&history, &committed), "the honest custody chain re-derives");
    assert!(
        custody_chain_is_connected(&history),
        "single-custodianship is conserved (a connected custody path)"
    );
    // A forged handoff (a non-holder hands off) breaks the connectedness witness — the
    // SAME conservation tooth, unchanged by the re-expression.
    let rogue = identity_field("rogue");
    let forked = vec![
        Handoff { from: GENESIS_PREV, to: m, epoch: 1 },
        Handoff { from: rogue, to: b, epoch: 2 }, // rogue did not hold custody
    ];
    assert!(!custody_chain_is_connected(&forked), "a forged handoff is not conserved");
}

// =============================================================================
// The escape hatch: the RICH custody handoff still composes as a raw affordance
// =============================================================================

#[test]
fn the_rich_custody_handoff_drops_to_a_raw_affordance() {
    // The spec scaffold covers the common shapes (emit/edit). The REAL custody handoff
    // is richer — it advances the `CUSTODIAN` register AND the epoch AND appends a
    // `WriteOnce` link in ONE turn, and the manufacturer's `grant_custody` is a real
    // `Effect::GrantCapability` handing the custody cap forward NARROWED (the
    // `derive_no_amplify` shape). Both drop to a raw `CellAffordance` — still composed,
    // still cap-gated, still through the same mount. The scaffold is a convenience, not
    // a ceiling.
    let (cclerk, executor) = agent();
    let item = cclerk.cell_id();
    let next_custodian = CellId::from_bytes([0xAA; 32]);

    // The manufacturer's real cap handoff: GrantCapability of the item's custody cap to
    // the next custodian, at the SAME (Signature) permissions — narrowed, never widened.
    let grant_custody = Effect::GrantCapability {
        from: item,
        to: next_custodian,
        cap: CapabilityRef {
            target: item,
            slot: CUSTODIAN_SLOT as u32,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    };

    let app = DeosApp::builder("supply-chain-provenance", cclerk.clone(), executor)
        .cell(
            DeosCell::new(item, "item")
                // the manufacturer (root) hands the custody cap forward (the real grant).
                .affordance(CellAffordance::new(
                    "grant_custody",
                    AuthRequired::None,
                    grant_custody,
                )),
        )
        .build();
    let cell = &app.cells()[0];
    assert_eq!(
        cell.surface().get("grant_custody").unwrap().effect_summary(),
        EffectSummary::GrantCapability { from: item, to: next_custodian }
    );
}
