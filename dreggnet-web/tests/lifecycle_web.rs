//! **The session-lifecycle policy on the WEB surface, driven through the real router** — the G2
//! closure at the wound site (`GET /offerings/{key}/session/{id}` lazily minted a real session
//! for ANY id, unbounded, unthrottled):
//!
//! * the policy envs PARSE (via the env-shaped seam `web_policy_from` — process env is global,
//!   tests never mutate it), unset/garbage staying honestly `None`;
//! * a burst of GET-opens past the per-user quota is refused with an honest **429** (not a 500),
//!   a different user is unaffected, and re-touching an already-live session is never gated;
//! * at the capacity cap with NOTHING evictable the refusal is a 429 too;
//! * at the capacity cap on the lossy (store-less demo) host the working set stays BOUNDED — the
//!   coldest session is shed, the newest lives;
//! * the rest of the catalog (`GET /offerings`) is untouched by a policied host.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::{SessionId, SessionPolicy, SystemClock};
use dreggnet_web::{
    CatalogState, WEB_MAX_SESSIONS_ENV, WEB_MIN_OPEN_INTERVAL_ENV, WEB_OPENS_PER_USER_ENV,
    WEB_SESSION_TTL_ENV, catalog_default_host, catalog_router, demo_host_over, web_policy_from,
};
use tower::ServiceExt; // oneshot

/// GET `uri` as web user `user` (a `dregg_user` cookie), returning the status + body.
async fn get_as(app: &axum::Router, uri: &str, user: &str) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(uri)
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::empty())
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

/// The policy envs parse through the env-shaped seam: set values land in the right knobs,
/// unset stays `None` (unbounded), and garbage degrades to `None` (warn, boot anyway) — the
/// same degrade-not-refuse posture as every other env switch on this server.
#[test]
fn the_policy_envs_parse_and_unset_or_garbage_stays_unbounded() {
    let parsed = web_policy_from(|k| match k {
        k if k == WEB_MAX_SESSIONS_ENV => Some("64".to_string()),
        k if k == WEB_SESSION_TTL_ENV => Some("3600".to_string()),
        k if k == WEB_OPENS_PER_USER_ENV => Some("8".to_string()),
        k if k == WEB_MIN_OPEN_INTERVAL_ENV => Some("2".to_string()),
        _ => None,
    });
    assert_eq!(parsed.max_sessions_per_offering, Some(64));
    assert_eq!(parsed.idle_ttl_secs, Some(3600));
    assert_eq!(parsed.max_opens_per_actor, Some(8));
    assert_eq!(parsed.min_open_interval_secs, Some(2));

    let unset = web_policy_from(|_| None);
    assert!(
        unset.is_unbounded(),
        "all-unset = today's unbounded behavior"
    );

    let garbage =
        web_policy_from(|k| (k == WEB_MAX_SESSIONS_ENV).then(|| "not-a-number".to_string()));
    assert!(
        garbage.is_unbounded(),
        "an unparseable value degrades to unset, never a refused boot"
    );
}

/// **The burst refusal.** With a per-user open quota of 2, a burst of GET-opens to fresh session
/// ids from ONE cookie identity gets an honest 429 on the third — while a different user still
/// opens, a re-touch of an already-live session is never gated, and `GET /offerings` (the
/// catalog itself) is unaffected.
#[tokio::test]
async fn a_get_open_burst_past_the_user_quota_is_refused_with_a_429() {
    let policy = SessionPolicy {
        max_opens_per_actor: Some(2),
        ..SessionPolicy::default()
    };
    let app = catalog_router(Arc::new(CatalogState::with_host(move || {
        demo_host_over(None, policy)
    })));

    // Two opens by crawler-alice land.
    for sid in ["burst-1", "burst-2"] {
        let (s, _) = get_as(&app, &format!("/offerings/dungeon/session/{sid}"), "alice").await;
        assert_eq!(s, StatusCode::OK, "{sid} opens under quota");
    }
    // The third fresh mint is refused — 4xx naming the quota, not a 500, and nothing opened.
    let (s, body) = get_as(&app, "/offerings/dungeon/session/burst-3", "alice").await;
    assert_eq!(
        s,
        StatusCode::TOO_MANY_REQUESTS,
        "the over-quota open is an honest 429: {body}"
    );
    assert!(
        body.contains("open quota reached"),
        "the refusal names the tripped limit: {body}"
    );

    // Re-touching an ALREADY-LIVE session is not an open — never gated.
    let (s, _) = get_as(&app, "/offerings/dungeon/session/burst-1", "alice").await;
    assert_eq!(s, StatusCode::OK, "a live session stays reachable");

    // A different identity is on its own quota lane.
    let (s, _) = get_as(&app, "/offerings/dungeon/session/bob-1", "bob").await;
    assert_eq!(s, StatusCode::OK, "bob is not gated by alice's burst");

    // The catalog page itself is untouched by the policy.
    let (s, body) = get_as(&app, "/offerings", "alice").await;
    assert_eq!(s, StatusCode::OK);
    assert!(
        body.contains("dungeon"),
        "the catalog still lists offerings"
    );
}

/// **Capacity, both shapes.** On a host where nothing is evictable (no store, lossy eviction
/// OFF) the over-cap open is a 429; on the store-less DEMO host (which arms honest lossy
/// shedding) the over-cap open lands but the working set stays BOUNDED — the coldest session is
/// no longer live.
#[tokio::test]
async fn capacity_refuses_or_sheds_and_the_working_set_stays_bounded() {
    // ── nothing evictable → refuse (429) ──
    let strict = SessionPolicy {
        max_sessions_per_offering: Some(2),
        ..SessionPolicy::default()
    };
    let state = Arc::new(CatalogState::with_host(move || {
        // Straight onto the default catalog host: no store, and lossy eviction NOT opted into —
        // the cap must hold by refusal.
        catalog_default_host().with_policy(strict, SystemClock)
    }));
    let app = catalog_router(Arc::clone(&state));
    for sid in ["cap-1", "cap-2"] {
        let (s, _) = get_as(&app, &format!("/offerings/dungeon/session/{sid}"), "alice").await;
        assert_eq!(s, StatusCode::OK);
    }
    let (s, body) = get_as(&app, "/offerings/dungeon/session/cap-3", "alice").await;
    assert_eq!(
        s,
        StatusCode::TOO_MANY_REQUESTS,
        "at capacity with nothing evictable: an honest 429, not a 500: {body}"
    );
    assert!(!state.is_open("dungeon", &SessionId::new("cap-3")));
    assert!(state.is_open("dungeon", &SessionId::new("cap-1")));

    // ── the store-less demo host: lossy shedding keeps the set bounded ──
    let shed = SessionPolicy {
        max_sessions_per_offering: Some(2),
        ..SessionPolicy::default()
    };
    let state = Arc::new(CatalogState::with_host(move || {
        demo_host_over(None, shed) // arms evict_unpersisted (documented, named)
    }));
    let app = catalog_router(Arc::clone(&state));
    for sid in ["shed-1", "shed-2", "shed-3"] {
        let (s, _) = get_as(&app, &format!("/offerings/dungeon/session/{sid}"), "alice").await;
        assert_eq!(s, StatusCode::OK, "{sid} opens (shedding, not refusing)");
    }
    assert!(
        state.is_open("dungeon", &SessionId::new("shed-3")),
        "the newest session lives"
    );
    assert!(
        !state.is_open("dungeon", &SessionId::new("shed-1")),
        "the coldest was shed — the working set is bounded at the cap"
    );
}
