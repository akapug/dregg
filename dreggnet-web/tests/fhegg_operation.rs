//! One owning fhEgg operation through the real web host, plus cross-surface
//! descriptor parity and transport/auth/session refusal gates.

#![cfg(feature = "fhegg-settlement")]

use std::sync::Arc;
use std::time::Duration;

use axum::{Router, body::Body, http::Request};
use dreggnet_market::fhegg_transport::{
    FHEGG_SETTLEMENT_DISCLOSURE, FHEGG_SETTLEMENT_MEDIA_TYPE, FHEGG_SETTLEMENT_OPERATION,
    FheggSettlementBundle, MAX_FHEGG_BUNDLE_BYTES,
};
use dreggnet_market::{DarkBazaarOffering, TURN_LIST};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, Outcome, SessionConfig, SessionId,
};
use dreggnet_web::discord_activity::{DiscordActivityState, discord_activity_router};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{CatalogState, fhegg_operation};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{PartyMpcSession, simulate_public_transcript};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderEncryptionOpening, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use fhegg_fhe::{Order, Side};
use rand::{SeedableRng, rngs::StdRng};
use tower::ServiceExt;

const SESSION_A: &str = "shielded-a";
const SESSION_B: &str = "shielded-b";
const SEED_A: u64 = 0xF4_E6_70;
const SEED_B: u64 = 0xF4_E6_71;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut dreggnet_market::DarkBazaarSession,
    turn: &str,
    value: i64,
    who: &str,
) {
    assert!(matches!(
        offering.advance(session, Action::new(turn, turn, value, true), actor(who),),
        Outcome::Landed { .. }
    ));
}

fn collective_key(params: &BfvParams) -> (KeygenSession, CollectivePublicKey) {
    let keygen = KeygenSession::from_seed(2, [0x21; 32]).unwrap();
    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    for party in 0..2 {
        let (state, contribution) = ThresholdParty::join(&keygen, party, params).unwrap();
        coordinator.accept(contribution).unwrap();
        drop(state);
    }
    (keygen, coordinator.finish().unwrap())
}

struct WireFixture {
    wire: Vec<u8>,
    source_bound_actions: Vec<(Action, DreggIdentity)>,
}

fn wire_for(seed: u64, committee: &[SigningKey; 2]) -> WireFixture {
    let source_verifier = SigningKey::from_bytes(&[0x29; 32]);
    let offering = DarkBazaarOffering::new()
        .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
        .unwrap();
    let mut market = offering
        .open(SessionConfig::with_seed(seed))
        .expect("fixture market opens");
    land(&offering, &mut market, TURN_LIST, 1, "seller");

    let params = BfvParams::fold_set();
    let (keygen, collective) = collective_key(&params);
    let ingress = OrderIngressSession::new(
        market.fhegg_order_ingress_nonce().unwrap(),
        4,
        &params,
        &collective,
    )
    .unwrap();
    let trader_keys = [
        SigningKey::from_bytes(&[0x40; 32]),
        SigningKey::from_bytes(&[0x41; 32]),
        SigningKey::from_bytes(&[0x42; 32]),
    ];
    let mut book = AuthenticatedOrderBook::new(
        ingress.clone(),
        trader_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .unwrap();
    let mut source_bound_actions = Vec::new();
    for (trader, (who, side, limit)) in [
        ("seller", Side::Ask, 1usize),
        ("alice", Side::Bid, 2),
        ("bob", Side::Bid, 3),
    ]
    .into_iter()
    .enumerate()
    {
        let order = Order {
            side,
            limit,
            qty: 1,
        };
        let opening = OrderEncryptionOpening::from_seed([0x51 + trader as u8; 32]);
        let (submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &ingress,
            trader,
            0,
            &order,
            &params,
            &collective,
            &trader_keys[trader],
            opening,
        )
        .unwrap();
        let binding = book
            .accept_opened(submission, &order, opening, &params, &collective)
            .unwrap();
        let action = if matches!(side, Side::Ask) {
            let certificate =
                binding.certify_listing_for_market(who.as_bytes(), [0xA5; 32], &source_verifier);
            DarkBazaarOffering::fhegg_listing_source_action(&certificate)
        } else {
            let certificate = binding.certify_for_market(who.as_bytes(), &source_verifier);
            DarkBazaarOffering::fhegg_source_bound_bid_action(limit as i64, &certificate)
        };
        let identity = actor(who);
        assert!(
            offering
                .advance(&mut market, action.clone(), identity.clone())
                .landed()
        );
        source_bound_actions.push((action, identity));
    }

    let verifier = AuthenticatedQuorumVerifier::new(
        committee
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("test verifier");
    let session = PartyMpcSession::new(
        market
            .fhegg_settlement_session_nonce()
            .expect("board-bound nonce"),
        2,
        4,
        8,
        params.plaintext_modulus(),
        Duration::from_secs(1),
    )
    .expect("public MPC session");
    let bfv = BfvPublicIdentity::from_public(&params, &keygen, &collective);
    let (_, mut inputs) = book.finish().into_parts();
    inputs.push(market.fhegg_source_input().expect("live source input"));
    let crossing = Crossing {
        p_star: Some(3),
        v_star: 1,
    };
    let transcript =
        simulate_public_transcript(&crossing, &session, &mut StdRng::seed_from_u64(seed))
            .expect("reveal-only transcript");
    let expected = ExpectedClearingContext {
        session: &session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &transcript,
        crossing: &crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical claim");
    let digest = receipt.claim_digest();
    let signatures = committee
        .iter()
        .enumerate()
        .map(|(index, key)| verifier.sign_claim(&digest, index, key).unwrap())
        .collect::<Vec<_>>();
    receipt.computation_integrity = verifier
        .assemble_evidence(&digest, &signatures)
        .expect("quorum evidence");
    WireFixture {
        wire: FheggSettlementBundle::new(&expected, &receipt)
            .expect("owning bundle")
            .to_wire_bytes(),
        source_bound_actions,
    }
}

fn configured_catalog(
    committee: &[SigningKey; 2],
    session_actions: Vec<(&'static str, u64, Vec<(Action, DreggIdentity)>)>,
) -> Arc<CatalogState> {
    let public_keys = committee
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect::<Vec<_>>();
    let source_verifier = SigningKey::from_bytes(&[0x29; 32]);
    Arc::new(CatalogState::with_host(move || {
        let offering = DarkBazaarOffering::with_fhegg_quorum(public_keys, 2)
            .expect("configured host verifier")
            .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
            .expect("configured source verifier");
        let mut host = OfferingHost::new();
        host.register(DarkBazaarOffering::KEY, "Dark Bazaar", offering);
        for (id, seed, actions) in &session_actions {
            let sid = SessionId::new(*id);
            host.open_session(
                DarkBazaarOffering::KEY,
                sid.clone(),
                SessionConfig::with_seed(*seed),
            )
            .expect("host session opens");
            assert!(matches!(
                host.advance(
                    DarkBazaarOffering::KEY,
                    &sid,
                    Action::new(TURN_LIST, TURN_LIST, 1, true),
                    actor("seller"),
                ),
                Some(Outcome::Landed { .. })
            ));
            for (action, who) in actions {
                assert!(matches!(
                    host.advance(DarkBazaarOffering::KEY, &sid, action.clone(), who.clone()),
                    Some(Outcome::Landed { .. })
                ));
            }
        }
        host
    }))
}

async fn response(app: &Router, request: Request<Body>) -> (u16, Vec<u8>) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status().as_u16();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body")
        .to_vec();
    (status, body)
}

fn upload(path: &str, body: impl Into<Body>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", FHEGG_SETTLEMENT_MEDIA_TYPE)
        .header("cookie", "dregg_user=settlement-worker")
        .body(body.into())
        .unwrap()
}

#[tokio::test]
async fn one_operation_is_discoverable_everywhere_and_settles_only_its_live_session() {
    let committee = [
        SigningKey::from_bytes(&[0x31; 32]),
        SigningKey::from_bytes(&[0x32; 32]),
    ];
    let fixture_a = wire_for(SEED_A, &committee);
    let fixture_b = wire_for(SEED_B, &committee);
    let wire = fixture_a.wire;
    let catalog = configured_catalog(
        &committee,
        vec![
            (SESSION_A, SEED_A, fixture_a.source_bound_actions),
            (SESSION_B, SEED_B, fixture_b.source_bound_actions),
        ],
    );
    let tg = tg_miniapp_router(Arc::new(TgMiniAppState::new(
        Arc::clone(&catalog),
        "test-bot-token",
        [0x71; 32],
        86_400,
    )));
    let da = discord_activity_router(Arc::new(DiscordActivityState::new(
        Arc::clone(&catalog),
        "client",
        "secret",
        [0x72; 32],
        86_400,
    )));
    let app = Router::new()
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg)
        .merge(da);

    // All surface adapters discover the exact same descriptor bytes; no copied
    // disclosure or media-type string can drift.
    let mut descriptors = Vec::new();
    for prefix in ["", "/tg", "/da"] {
        let path = format!("{prefix}/operations/{FHEGG_SETTLEMENT_OPERATION}");
        let (status, body) = response(
            &app,
            Request::builder().uri(path).body(Body::empty()).unwrap(),
        )
        .await;
        assert_eq!(status, 200);
        descriptors.push(body);
    }
    assert_eq!(descriptors[0], descriptors[1]);
    assert_eq!(descriptors[1], descriptors[2]);
    let descriptor = String::from_utf8(descriptors.remove(0)).unwrap();
    assert!(descriptor.contains(FHEGG_SETTLEMENT_DISCLOSURE));
    assert!(descriptor.contains(FHEGG_SETTLEMENT_MEDIA_TYPE));
    assert!(descriptor.contains("offering-selected safe replay material"));
    assert!(descriptor.contains("restore in timeline order"));

    // Platform-specific upload wrappers are real and fail closed at their own
    // authentication gate before the shared implementation reads the body.
    for prefix in ["/tg", "/da"] {
        let path = format!(
            "{prefix}/offerings/{}/session/{SESSION_A}/operations/{FHEGG_SETTLEMENT_OPERATION}",
            DarkBazaarOffering::KEY
        );
        let request = Request::builder()
            .method("POST")
            .uri(path)
            .header("content-type", FHEGG_SETTLEMENT_MEDIA_TYPE)
            .body(Body::from(wire.clone()))
            .unwrap();
        assert_eq!(response(&app, request).await.0, 401);
    }

    let route_a = format!(
        "/offerings/{}/session/{SESSION_A}/operations/{FHEGG_SETTLEMENT_OPERATION}",
        DarkBazaarOffering::KEY
    );
    let route_b = format!(
        "/offerings/{}/session/{SESSION_B}/operations/{FHEGG_SETTLEMENT_OPERATION}",
        DarkBazaarOffering::KEY
    );

    // Session discovery is driven by the configured live offering, not the
    // static route table.
    let (status, body) = response(
        &app,
        Request::builder()
            .uri(format!(
                "/offerings/{}/session/{SESSION_A}/operations",
                DarkBazaarOffering::KEY
            ))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    assert!(
        String::from_utf8(body)
            .unwrap()
            .contains(FHEGG_SETTLEMENT_DISCLOSURE)
    );

    // Authentication is checked before body decode.
    let anonymous = Request::builder()
        .method("POST")
        .uri(&route_a)
        .header("content-type", FHEGG_SETTLEMENT_MEDIA_TYPE)
        .body(Body::from(wire.clone()))
        .unwrap();
    assert_eq!(response(&app, anonymous).await.0, 401);

    let wrong_media = Request::builder()
        .method("POST")
        .uri(&route_a)
        .header("content-type", "application/octet-stream")
        .header("cookie", "dregg_user=settlement-worker")
        .body(Body::from(wire.clone()))
        .unwrap();
    assert_eq!(response(&app, wrong_media).await.0, 415);

    let oversized = Request::builder()
        .method("POST")
        .uri(&route_a)
        .header("content-type", FHEGG_SETTLEMENT_MEDIA_TYPE)
        .header("content-length", MAX_FHEGG_BUNDLE_BYTES + 1)
        .header("cookie", "dregg_user=settlement-worker")
        .body(Body::empty())
        .unwrap();
    assert_eq!(response(&app, oversized).await.0, 413);

    assert_eq!(
        response(&app, upload(&route_a, b"not-a-bundle".to_vec()))
            .await
            .0,
        400
    );

    // A canonical bundle for session A cannot settle session B. The board-bound
    // nonce/source join refuses before mutation.
    let (status, body) = response(&app, upload(&route_b, wire.clone())).await;
    assert_eq!(status, 409);
    assert!(
        String::from_utf8(body)
            .unwrap()
            .contains("exact live sealed board")
    );

    let (status, body) = response(&app, upload(&route_a, wire.clone())).await;
    assert_eq!(status, 200);
    let body = String::from_utf8(body).unwrap();
    assert!(body.contains("\"status\":\"applied\""));
    assert!(body.contains("\"price\":\"3\""));
    assert!(body.contains("bob"));

    // The same accepted bundle cannot be applied twice; the already-settled
    // live state refuses without a second executor mutation.
    assert_eq!(response(&app, upload(&route_a, wire)).await.0, 409);
}
