//! RE-EXPRESSION proof: the `subscription` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable.**
//!
//! `docs/deos/DEOS-APPS.md` (the plan §4): "Re-express 1-2 existing apps on the new
//! framework to prove the composition." This is that proof, for `subscription` (a
//! pub/sub feed: publishers publish, consumers consume, the owner grants — see
//! `starbridge-apps/subscription/src/lib.rs`, ~1516 lines). Its USER-FACING surface
//! is FOUR cap-gated operations on a queue cell:
//!
//!   - `publish`         — append a message (a publisher right);
//!   - `consume`         — read/advance the head (a consumer right);
//!   - `grant_publisher` — admit a publisher (the owner's right);
//!   - `grant_consumer`  — admit a consumer (the owner's right).
//!
//! On the OLD bones, an app wired these as: a hand-rolled factory + inspectors + a
//! per-method turn-builder + a hand-copied JS constants file + (no per-viewer
//! projection, no web-of-cells publish of the feed cell, no rehydration, no generated
//! web component). On the COMPOSED bones, the same four operations are ONE
//! [`DeosApp`] builder — and the framework wires the rest:
//!
//!   - **smaller**: the whole surface is one `DeosApp::builder(...).cell(...)` (this
//!     file's `subscription_app()` — ~20 lines) vs. the hand-wired endpoint + registry
//!     + webgen the floor needed;
//!   - **more capable**: it gains the per-viewer projection (a consumer sees only
//!     `consume`; the owner sees all four), the web-of-cells publish (the feed cell IS
//!     a distributed sturdyref), the rehydratable frustum-snapshot (a peer re-expands
//!     a fog-respecting view of the feed), and the generated `<dregg-affordance-surface>`
//!     web component — NONE of which the floor had.
//!
//! Every affordance carries a REAL [`dregg_turn::action::Effect`]; every fire is a
//! real verified turn through the embedded executor; the gate is the genuine
//! [`dregg_cell::is_attenuation`]. No parallel model.

use dregg_app_framework::{
    AffordanceSpec, AppSpec, AuthRequired, CellSpec, DeosApp, EmbeddedExecutor, Interaction,
    InteractionLog, Rehydration, RehydrateError, AgentCipherclerk, AppCipherclerk, CellId,
    CellAffordance, DeosCell, Effect, Event, FederationId, CapTpServer,
};

// =============================================================================
// The subscription feed, re-expressed as a composed deos app
// =============================================================================

// The pub/sub rights tiers, on the real attenuation lattice:
//   - a CONSUMER holds `Signature` (the narrow reader tier);
//   - a PUBLISHER holds `Either` (sig-or-proof — can publish AND consume);
//   - the OWNER holds `None`/root (can publish, consume, AND grant).
// So `Signature ⊂ Either ⊂ None`: the same three-tier chain the floor's doc-app used,
// but here it IS the subscription's publisher/consumer/owner model.
const CONSUMER: &str = "signature";
const PUBLISHER: &str = "either";
const OWNER: &str = "none";

/// The subscription feed as a declarative spec — the FOUR cap-gated operations on the
/// feed cell, published into the web-of-cells, discoverable. This is the whole app:
/// the builder writes the affordances; the framework wires the rest.
fn subscription_spec() -> AppSpec {
    AppSpec::new("subscription")
        .cell(
            CellSpec::new("feed")
                // consume: a consumer (Signature) reads/advances the head.
                .affordance(AffordanceSpec::emit("consume", CONSUMER, "consumed"))
                // publish: a publisher (Either) appends a message (writes the tail slot).
                .affordance(AffordanceSpec::edit("publish", PUBLISHER, 1))
                // grant_publisher / grant_consumer: the owner (root) admits members.
                .affordance(AffordanceSpec::emit("grant_publisher", OWNER, "publisher-granted"))
                .affordance(AffordanceSpec::emit("grant_consumer", OWNER, "consumer-granted"))
                // the feed cell IS a distributed cell — publish it into the web-of-cells
                // at the consumer tier (a sturdyref bearer can at least consume).
                .publish(CONSUMER),
        )
        .discoverable(vec!["pubsub".into(), "feed".into()])
}

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5B; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn subscription_app(cclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    subscription_spec()
        .into_app(cclerk.clone(), executor.clone())
        .expect("the subscription spec is valid")
}

// =============================================================================
// SMALLER: the whole surface is one builder, registered in one fold
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = subscription_app(&cclerk, &executor);

    // ONE app, ONE cell, FOUR affordances — the entire pub/sub surface.
    assert_eq!(app.name(), "subscription");
    assert_eq!(app.cells().len(), 1);
    let feed = &app.cells()[0];
    assert_eq!(
        feed.surface().all_names(),
        vec![
            "consume".to_string(),
            "grant_consumer".to_string(),
            "grant_publisher".to_string(),
            "publish".to_string(),
        ]
    );
    // The feed cell is the agent's own (so fires execute against the seeded ledger).
    assert_eq!(feed.cell(), cclerk.cell_id());
    // Published into the web-of-cells at the consumer tier.
    assert_eq!(feed.published_authority(), Some(&AuthRequired::Signature));

    // ONE registration folds the whole surface into a shared host context — the
    // composed `register(ctx)`, where the floor needed factory + inspector + webgen
    // as separate verbs.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection — consumer vs publisher vs owner diverge
// =============================================================================

#[tokio::test]
async fn the_three_tiers_see_different_feeds() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = subscription_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/feed/projected")
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

    // A CONSUMER (Signature) sees only `consume`.
    assert_eq!(visible(&router, "signature").await, serde_json::json!(["consume"]));
    // A PUBLISHER (Either) sees `consume` + `publish`.
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["consume", "publish"])
    );
    // The OWNER (root) sees ALL FOUR.
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["consume", "grant_consumer", "grant_publisher", "publish"])
    );
    // The floor's subscription had NO per-viewer projection — this is new capability.
}

// =============================================================================
// MORE CAPABLE (2): fires are real verified turns; anti-ghost holds
// =============================================================================

#[tokio::test]
async fn a_publisher_publishes_a_real_verified_turn_a_consumer_cannot() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = subscription_app(&cclerk, &executor);
    let router = app.mount();

    // A PUBLISHER (Either) fires `publish` (req Either): authorized → the real
    // SetField turn executes through the embedded executor.
    let published = router
        .clone()
        .oneshot(
            Request::post("/feed/fire/publish")
                .header(dregg_app_framework::HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(published.status(), StatusCode::OK, "publisher publishes");
    let bytes = axum::body::to_bytes(published.into_body(), usize::MAX).await.unwrap();
    let body: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(body["fired"], "publish");
    assert_ne!(body["turn_hash"].as_str().unwrap(), "0".repeat(64), "a real turn");

    // A CONSUMER (Signature) firing `publish` is 403 — REFUSED by the real gate,
    // nothing executed (anti-ghost). The cap discipline is the SAME in-band gate.
    let refused = router
        .oneshot(
            Request::post("/feed/fire/publish")
                .header(dregg_app_framework::HELD_RIGHTS_HEADER, "signature")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(refused.status(), StatusCode::FORBIDDEN, "consumer cannot publish");
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the feed cell is a distributed sturdyref
// =============================================================================

#[tokio::test]
async fn the_feed_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    let doc = cclerk.cell_id();
    // The same spec, but with a captp server attached (the web-of-cells minter).
    let captp = CapTpServer::new(FederationId([0x5B; 32]));
    let app = DeosApp::builder("subscription", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(
            DeosCell::new(doc, "feed")
                .affordance(CellAffordance::new(
                    "consume",
                    AuthRequired::Signature,
                    Effect::EmitEvent { cell: doc, event: Event { topic: [1u8; 32], data: vec![] } },
                ))
                .publish(AuthRequired::Signature),
        )
        .build();

    // The feed cell is exported as a real `dregg://` sturdyref — agents on other cells
    // reacquire the feed across the membrane. The floor's subscription never published
    // its feed cell into the web-of-cells.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(uris[0].starts_with("dregg://"), "a real sturdyref: {}", uris[0]);
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the feed, per-viewer
// =============================================================================

#[test]
fn a_feed_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = subscription_app(&cclerk, &executor);
    let feed = &app.cells()[0];

    // Snapshot the feed. It witnessed a publish turn (a real, non-zero turn hash), and
    // the sources are gone (a cold snapshot handed to a peer) ⇒ the liveness-type is
    // REPLAYED-DETERMINISTIC (the confined fragment), DERIVED from the witness-log.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(feed.cell(), [9u8; 32]));
    let snap = feed.snapshot(log, false);
    assert_eq!(snap.lineage, AuthRequired::Signature, "snapshot at the published lineage");
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A CONSUMER (Signature) rehydrating the snapshot reacquires only `consume` — the
    // feed snapshot respects the lattice; it cannot leak the owner's grant affordances.
    let consumer = feed.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(consumer.visible_names(), vec!["consume".to_string()]);

    // A viewer holding an INCOMPARABLE authority (a distinct Custom identity — e.g. a
    // member of a different federation's incomparable role) cannot rehydrate at all.
    let blocked = feed.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = subscription_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component (the
    // htmx-on-crack custom element the embedded servo web-surface mounts) — generated
    // from the Rust source of truth. The floor's subscription hand-wrote its JS.
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
    // The anti-drift affordance map names the feed's fire endpoints.
    assert!(js.contains("fireEndpoint: \"/feed/fire/publish\","));
    assert!(js.contains("fireEndpoint: \"/feed/fire/consume\","));

    // GET /manifest serves the whole composed surface (cells, affordances,
    // persistence seam, distribution posture) — the anti-drift readout.
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX).await.unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "subscription");
    assert_eq!(m["discoverable"], serde_json::json!(["pubsub", "feed"]));
    // The persistence seam is VISIBLE (honest) — embedded ledger today; pg-dregg plugs in.
    assert!(m["persistence"].as_str().unwrap().contains("embedded-ledger"));
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
}

// =============================================================================
// The reduction, stated: a custom CellAffordance still composes (the escape hatch)
// =============================================================================

#[test]
fn an_app_needing_a_richer_effect_drops_to_a_raw_affordance() {
    // The spec covers the common shapes (emit/edit). An app that needs a richer effect
    // (e.g. the subscription's GrantCapability for a real publisher grant) drops to a
    // raw `DeosCell::affordance` — still composed, still cap-gated, still through the
    // same mount. The scaffold is a convenience, not a ceiling.
    let (cclerk, executor) = agent();
    let doc = cclerk.cell_id();
    let recipient = CellId::from_bytes([0xAA; 32]);
    let grant = Effect::GrantCapability {
        from: doc,
        to: recipient,
        cap: dregg_app_framework::CapabilityRef {
            target: doc,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    };
    let app = DeosApp::builder("subscription", cclerk.clone(), executor)
        .cell(
            DeosCell::new(doc, "feed")
                .affordance(CellAffordance::new("grant_publisher", AuthRequired::None, grant)),
        )
        .build();
    let feed = &app.cells()[0];
    assert_eq!(
        feed.surface().get("grant_publisher").unwrap().effect_summary(),
        dregg_app_framework::EffectSummary::GrantCapability { from: doc, to: recipient }
    );
}
