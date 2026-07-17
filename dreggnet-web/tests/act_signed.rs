//! **The SIGNED-turn route, driven through the real catalog router** — the end-to-end closure of
//! the G1 signed-identity ladder: a real Ed25519 key signs the canonical turn message (the SAME
//! [`TurnSigner`] primitive `signed.rs` verifies against — what the extension's wasm signer
//! reproduces byte-for-byte), the JSON wire POSTs to `/offerings/{key}/session/{id}/act-signed`,
//! and the session advances with the actor as the VERIFIED pubkey. Both polarities, non-vacuous:
//! - a genuine signature lands a real turn (200; the verified pubkey named; `verify` counts it);
//! - a FORGED signature (wrong key claiming the signer's pubkey) is 403 and the session is
//!   provably UNMOVED (anti-ghost read-back via `verify`);
//! - a REPLAYED counter is 403 (the consumed-counter ledger), session unmoved;
//! - a malformed body (bad hex / missing field / garbage counter) is 400, before any crypto.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

use dreggnet_offerings::{Action, SessionId, SignedAction, TurnSigner};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};

fn app() -> axum::Router {
    catalog_router(Arc::new(CatalogState::new()))
}

/// Lowercase hex of the 64-byte signature (the wire encoding; `hex` is not a dep here).
fn sig_hex(sig: &[u8; 64]) -> String {
    let mut s = String::with_capacity(128);
    for b in sig {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// The JSON wire the extension README's step-4 fetch assembles from a [`SignedAction`], with the
/// counter as a JSON number or a decimal string (both legs of the wire contract).
fn wire_json(sa: &SignedAction, counter: serde_json::Value) -> String {
    serde_json::json!({
        "action": {
            "label": sa.action.label,
            "turn": sa.action.turn,
            "arg": sa.action.arg,
            "enabled": sa.action.enabled,
            "text": sa.action.text,
        },
        "actor_pubkey_hex": sa.actor_pubkey_hex,
        "counter": counter,
        "signature_hex": sig_hex(&sa.signature),
    })
    .to_string()
}

async fn post_json(app: &axum::Router, uri: &str, body: String) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/json")
                .body(Body::from(body))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

async fn get(app: &axum::Router, uri: &str) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// The committed-turn count of a session, read back over the REAL `verify` route (replay proof) —
/// the anti-ghost ground truth every polarity below asserts against.
async fn verified_turns(app: &axum::Router, key: &str, id: &str) -> u64 {
    let (status, body) = get(app, &format!("/offerings/{key}/session/{id}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    let v: serde_json::Value = serde_json::from_str(&body).expect("verify returns JSON");
    assert_eq!(
        v["verified"], true,
        "the committed chain re-verifies: {body}"
    );
    v["turns"].as_u64().expect("turns is a count")
}

/// A signed dungeon move for `(session, counter, arg)` under `signer` — the canonical message the
/// extension builds, signed by the SAME primitive the server verifies.
fn sign_choose(signer: &TurnSigner, session: &str, counter: u64, arg: i64) -> SignedAction {
    signer.sign(
        "dungeon",
        &SessionId::new(session),
        counter,
        Action::new("choose", "choose", arg, true),
    )
}

/// GENUINE: a real key signs a turn → 200, the turn commits (verify counts it), and the actor
/// named in the response IS the verified pubkey. Then the number-or-STRING counter leg: the next
/// turn's counter rides as a decimal string (the >2^53 JSON-safety wire) and also lands.
#[tokio::test]
async fn a_signed_turn_lands_with_the_verified_pubkey_as_actor() {
    let app = app();
    let signer = TurnSigner::from_seed([7u8; 32]);
    let act = "/offerings/dungeon/session/sg-1/act-signed";

    // Open the session (a GET, as a browser would) — fresh: genesis only.
    let (status, _) = get(&app, "/offerings/dungeon/session/sg-1").await;
    assert_eq!(status, StatusCode::OK);
    assert_eq!(verified_turns(&app, "dungeon", "sg-1").await, 1);

    // Counter 0 as a JSON NUMBER.
    let sa = sign_choose(&signer, "sg-1", 0, KP_PRESS_ON as i64);
    let (status, body) = post_json(&app, act, wire_json(&sa, serde_json::json!(0))).await;
    assert_eq!(status, StatusCode::OK, "genuine signed turn lands: {body}");
    assert!(
        body.contains("Turn committed"),
        "a real receipt landed: {body}"
    );
    assert!(
        body.contains(signer.pubkey_hex()),
        "the actor is the VERIFIED pubkey, named in the response: {body}"
    );
    assert_eq!(verified_turns(&app, "dungeon", "sg-1").await, 2);

    // Counter 1 as a decimal STRING (the extension's counterWire form beyond 2^53 − 1).
    let sa = sign_choose(&signer, "sg-1", 1, KP_CLAIM_RED as i64);
    let (status, body) = post_json(&app, act, wire_json(&sa, serde_json::json!("1"))).await;
    assert_eq!(status, StatusCode::OK, "string-counter wire lands: {body}");
    assert!(body.contains("Turn committed"), "{body}");
    assert_eq!(verified_turns(&app, "dungeon", "sg-1").await, 3);
}

/// FORGED: an imposter key signs but claims the signer's pubkey → 403, and the session is
/// provably UNMOVED (verify still counts only genesis — the anti-ghost read-back).
#[tokio::test]
async fn a_forged_signature_is_403_and_the_session_is_unmoved() {
    let app = app();
    let signer = TurnSigner::from_seed([7u8; 32]);
    let imposter = TurnSigner::from_seed([8u8; 32]);
    let act = "/offerings/dungeon/session/sg-forge/act-signed";

    let mut forged = sign_choose(&imposter, "sg-forge", 0, KP_PRESS_ON as i64);
    forged.actor_pubkey_hex = signer.pubkey_hex().to_string();

    let (status, body) = post_json(&app, act, wire_json(&forged, serde_json::json!(0))).await;
    assert_eq!(
        status,
        StatusCode::FORBIDDEN,
        "a forged signature is refused: {body}"
    );
    assert!(
        body.contains("signature did not verify"),
        "the refusal names the gate that bit: {body}"
    );
    // Anti-ghost: NOTHING committed — the (lazily opened) session still holds genesis alone.
    assert_eq!(verified_turns(&app, "dungeon", "sg-forge").await, 1);
}

/// REPLAYED: the identical genuine envelope presented twice — the first lands (200), the second
/// hits the consumed-counter ledger (403, StaleCounter) and the session does not move again.
#[tokio::test]
async fn a_replayed_counter_is_403_and_commits_nothing_twice() {
    let app = app();
    let signer = TurnSigner::from_seed([7u8; 32]);
    let act = "/offerings/dungeon/session/sg-replay/act-signed";

    let sa = sign_choose(&signer, "sg-replay", 0, KP_PRESS_ON as i64);
    let wire = wire_json(&sa, serde_json::json!(0));

    let (status, body) = post_json(&app, act, wire.clone()).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the first presentation lands: {body}"
    );
    assert_eq!(verified_turns(&app, "dungeon", "sg-replay").await, 2);

    // The captured envelope, replayed verbatim.
    let (status, body) = post_json(&app, act, wire).await;
    assert_eq!(
        status,
        StatusCode::FORBIDDEN,
        "the replay is refused: {body}"
    );
    assert!(
        body.contains("stale replay counter"),
        "the refusal names the ledger gate: {body}"
    );
    assert_eq!(
        verified_turns(&app, "dungeon", "sg-replay").await,
        2,
        "the replay committed nothing (anti-ghost)"
    );
}

/// MALFORMED: each decode gate answers 400 with a named reason, before any crypto — bad/short
/// signature hex, a missing field, a garbage counter, a non-hex pubkey shape, and non-JSON.
#[tokio::test]
async fn a_malformed_body_is_400_before_any_crypto() {
    let app = app();
    let signer = TurnSigner::from_seed([7u8; 32]);
    let act = "/offerings/dungeon/session/sg-bad/act-signed";
    let sa = sign_choose(&signer, "sg-bad", 0, KP_PRESS_ON as i64);

    // Bad signature hex: right length, non-hex chars.
    let mut v: serde_json::Value =
        serde_json::from_str(&wire_json(&sa, serde_json::json!(0))).unwrap();
    v["signature_hex"] = serde_json::json!("zz".repeat(64));
    let (status, body) = post_json(&app, act, v.to_string()).await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{body}");
    assert!(body.contains("signature_hex"), "{body}");

    // Short signature hex.
    let mut v: serde_json::Value =
        serde_json::from_str(&wire_json(&sa, serde_json::json!(0))).unwrap();
    v["signature_hex"] = serde_json::json!("ab");
    let (status, _) = post_json(&app, act, v.to_string()).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);

    // Missing field: no actor_pubkey_hex.
    let mut v: serde_json::Value =
        serde_json::from_str(&wire_json(&sa, serde_json::json!(0))).unwrap();
    v.as_object_mut().unwrap().remove("actor_pubkey_hex");
    let (status, body) = post_json(&app, act, v.to_string()).await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{body}");

    // Garbage counter (neither number nor decimal string).
    let (status, body) = post_json(
        &app,
        act,
        wire_json(&sa, serde_json::json!("not-a-counter")),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{body}");
    assert!(body.contains("counter"), "{body}");

    // Negative counter (a u64 wire).
    let (status, _) = post_json(&app, act, wire_json(&sa, serde_json::json!(-1))).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);

    // A pubkey that is not 32 bytes of hex — well-formed JSON, malformed KEY (400, not 403).
    let mut short_key = sa.clone();
    short_key.actor_pubkey_hex = "abcd".to_string();
    let (status, body) = post_json(&app, act, wire_json(&short_key, serde_json::json!(0))).await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{body}");

    // Non-JSON body.
    let (status, _) = post_json(&app, act, "turn=choose&arg=0".to_string()).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);

    // NOTHING above moved the session: genesis alone.
    assert_eq!(verified_turns(&app, "dungeon", "sg-bad").await, 1);

    // And the genuine envelope still lands afterwards — the 400s consumed no counter.
    let (status, body) = post_json(&app, act, wire_json(&sa, serde_json::json!(0))).await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert_eq!(verified_turns(&app, "dungeon", "sg-bad").await, 2);
}

/// ROUTING: an unknown offering is an honest 404 (not a rendered catalog page, not a 500).
#[tokio::test]
async fn an_unknown_offering_is_404() {
    let app = app();
    let signer = TurnSigner::from_seed([7u8; 32]);
    let sa = signer.sign(
        "no-such-offering",
        &SessionId::new("s-1"),
        0,
        Action::new("choose", "choose", 0, true),
    );
    let (status, body) = post_json(
        &app,
        "/offerings/no-such-offering/session/s-1/act-signed",
        wire_json(&sa, serde_json::json!(0)),
    )
    .await;
    assert_eq!(status, StatusCode::NOT_FOUND, "{body}");
}
