//! **The full-portfolio catalog — the five NON-GAME offerings mounted beside the games.**
//!
//! The catalog used to be a subset (games + do-once feature surfaces). This drives the demo app
//! (`make_app`, real merged router, axum `oneshot`) and proves the WHOLE portfolio is now mounted:
//! the five `impl Offering` non-game crates — doc, names, compute, grain, hermes — are listed in
//! `GET /offerings` and each OPENS + RENDERS as a live session through the one generic host path.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{demo_host, make_app};
use tower::ServiceExt;

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
    (status, String::from_utf8_lossy(&bytes).to_string())
}

const NON_GAME: &[(&str, &str)] = &[
    ("doc", "DreggNet Doc"),
    ("names", "DreggNet Names"),
    ("compute", "DreggNet Compute"),
    ("grain", "DreggNet Grain"),
    ("hermes", "DreggNet Hermes"),
];

/// The demo host registers the whole portfolio: the games + the eight feature surfaces + the five
/// non-game offerings. Assert the count and the non-game keys directly on the host.
#[test]
fn demo_host_mounts_the_whole_portfolio() {
    let host = demo_host();
    let keys: Vec<String> = host
        .list_offerings()
        .iter()
        .map(|o| o.key.clone())
        .collect();
    for (key, _) in NON_GAME {
        assert!(keys.contains(&key.to_string()), "missing offering: {key}");
    }
    // The five games + eight feature surfaces + five non-game = at least 18 offerings.
    assert!(
        host.list_offerings().len() >= 18,
        "the catalog is the full portfolio, got {} offerings",
        host.list_offerings().len()
    );
}

/// `GET /offerings` lists every non-game offering with its title.
#[tokio::test]
async fn catalog_lists_the_non_game_offerings() {
    let app = make_app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);
    for (key, title) in NON_GAME {
        assert!(body.contains(title), "catalog missing {key} ({title})");
    }
}

/// Each non-game offering OPENS + RENDERS a live session (not the "no such session" page) — proving
/// the offering is really mounted and drivable, not merely listed.
#[tokio::test]
async fn each_non_game_offering_opens_and_renders() {
    let app = make_app();
    for (key, title) in NON_GAME {
        let uri = format!("/offerings/{key}/session/{key}-portfolio-test");
        let (status, body) = get(&app, &uri).await;
        assert_eq!(status, StatusCode::OK, "{key} did not render");
        assert!(
            !body.contains("No such session"),
            "{key} failed to open (rendered the missing-session page)"
        );
        assert!(
            !body.contains("No offering registered"),
            "{key} is not registered"
        );
        // The rendered page carries the offering's own title in the breadcrumb.
        assert!(body.contains(title), "{key} page missing its title {title}");
    }
}
