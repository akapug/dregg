//! THE PUBLIC-DEMO SERVER APP — the merged [`make_app`] Router, driven end to end with NO real
//! network (axum `ServiceExt::oneshot`). This is the smoke test for the deploy scout's Phase-0
//! unblocker: the ONE app the `dreggnet-web-server` bin binds + serves must
//! - answer `GET /health` 200 (the liveness probe the fronting proxy hits);
//! - list the five games AND the eight do-once feature surfaces at `GET /offerings`;
//! - play a real turn on a game through the merged router (a POST lands a committed receipt);
//! - render the seeded no-cheat Descent leaderboard (the honest winner ranks, the forgery is
//!   excluded) and the run-cards (an honest run PASSes, the forgery FAILs) — all by replay.
//!
//! Green here = a stranger can open the demo URL and play + independently verify, node-free.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::make_app;
use dungeon_on_dregg::KP_PRESS_ON;
use tower::ServiceExt; // oneshot

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

async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::from(format!("turn={turn}&arg={arg}")))
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

/// `GET /health` answers 200 with an ok status — the liveness probe the fronting proxy checks.
#[tokio::test]
async fn health_is_200() {
    let app = make_app();
    let (status, body) = get(&app, "/health").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("ok"), "health reports ok: {body}");
}

/// `GET /` renders the landing page linking the catalog + the no-cheat board.
#[tokio::test]
async fn the_landing_page_renders() {
    let app = make_app();
    let (status, body) = get(&app, "/").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("/offerings"),
        "landing links the catalog: {body}"
    );
    assert!(
        body.contains("/descent/leaderboard"),
        "landing links the no-cheat board: {body}"
    );
}

/// `GET /offerings` lists BOTH the five games AND the eight do-once feature surfaces — the merged
/// demo host wires `register_surfaces` beside the games.
#[tokio::test]
async fn offerings_lists_the_games_and_the_do_once_surfaces() {
    let app = make_app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);

    // The five games.
    for key in ["dungeon", "council", "market", "tug", "automatafl"] {
        assert!(
            body.contains(&format!("/offerings/{key}/session/")),
            "the catalog lists the {key} game: {body}"
        );
    }
    // The eight do-once feature surfaces (register_surfaces).
    for key in [
        "trade",
        "inventory",
        "cheevos",
        "guild",
        "craft",
        "companion",
        "tavern",
        "party",
    ] {
        assert!(
            body.contains(&format!("/offerings/{key}/session/")),
            "the catalog lists the {key} feature surface: {body}"
        );
    }
}

/// A game plays a real turn through the merged router: open the dungeon, POST a legal move, and a
/// committed verified receipt lands.
#[tokio::test]
async fn a_game_plays_a_turn_through_the_merged_router() {
    let app = make_app();
    let base = "/offerings/dungeon/session/smoke1";
    let act = format!("{base}/act");

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Warden"), "the Keep opens: {body}");

    let (status, body) = post(&app, &act, "choose", KP_PRESS_ON as i64, "ember").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Turn committed"), "a real turn lands: {body}");
}

/// The single-offering session surface (`/session/{id}`) is also mounted + plays through the merged
/// app (offering #0), and re-verifies over HTTP.
#[tokio::test]
async fn the_single_offering_session_surface_is_mounted() {
    let app = make_app();
    let (status, body) = get(&app, "/session/s0").await;
    assert_eq!(status, StatusCode::OK);
    assert!(!body.is_empty(), "the session #0 surface renders");

    let (status, verify) = get(&app, "/session/s0/verify").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify.contains("\"verified\":true"),
        "the fresh session re-verifies: {verify}"
    );
}

/// The seeded no-cheat leaderboard renders: the honest winner ranks, the forgery is excluded — the
/// re-verification is on render, by replay.
#[tokio::test]
async fn the_no_cheat_leaderboard_renders_the_verified_winner() {
    let app = make_app();
    let (status, body) = get(&app, "/descent/leaderboard").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("ember"), "the verified winner ranks: {body}");
    assert!(
        body.contains("/descent/run/demo-ember"),
        "the winning row links to its run-card: {body}"
    );
    assert!(
        !body.contains("a-forger"),
        "the forged run is excluded from the no-cheat board: {body}"
    );
    assert!(body.contains("no-cheat"), "the board states its property");
}

/// The run-cards prove by re-execution: the honest run PASSes, the seeded forgery FAILs.
#[tokio::test]
async fn a_run_card_proves_honest_and_fails_the_forgery() {
    let app = make_app();

    let (status, won) = get(&app, "/descent/run/demo-ember").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        won.contains("Independent verification — PASS"),
        "the honest run re-executes to PASS: {won}"
    );

    let (status, forged) = get(&app, "/descent/run/demo-forgery").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        forged.contains("Independent verification — FAIL"),
        "the forged run shows FAIL: {forged}"
    );
    assert!(
        !forged.contains("Independent verification — PASS"),
        "the forged run is NOT a fake pass: {forged}"
    );
}
