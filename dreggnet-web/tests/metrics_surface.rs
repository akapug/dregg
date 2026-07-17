//! **The web surface's Prometheus metrics, driven through the real router** — the observability
//! closure (the surface emitted ZERO metrics; the deploy/observability stack could not see it):
//!
//! * `GET /metrics` on the merged demo app answers 200 with the Prometheus exposition format,
//!   every `dregg_web_*` series present (pre-seeded at 0 from boot — a dashboard renders "0",
//!   never "No data"), and after a real session open the live-session gauge is NON-ZERO;
//! * a burst of opens past a tiny armed [`SessionPolicy`] is refused with the honest 429 AND
//!   the refusal lands on `dregg_web_opens_refused_total{limit="quota"}` — the counter moves
//!   exactly when the policy gate fires, so the `WebSessionEvictionStorm`-style alerting has a
//!   real series to rate over.
//!
//! One test binary = one process = one process-global recorder, so these assertions cannot be
//! polluted by the other suites (each `tests/*.rs` is its own process).

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::{SessionPolicy, SystemClock};
use dreggnet_web::{
    CatalogState, catalog_default_host, catalog_router, make_app, metrics, metrics_app,
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

/// Read a series' value out of a rendered Prometheus exposition: the line starting with
/// `series` (an exact name, or name+`{labels}` prefix), parsed from its trailing number.
fn series_value(rendered: &str, series: &str) -> Option<f64> {
    rendered
        .lines()
        .find(|l| l.starts_with(series) && !l.starts_with('#'))
        .and_then(|l| l.rsplit(' ').next())
        .and_then(|v| v.parse::<f64>().ok())
}

/// The SEPARATE metrics app serves `GET /metrics` (200, exposition format), every `dregg_web_*`
/// series is present from boot (pre-seeded — "0", never "No data"), and after a REAL catalog
/// session open the live-session gauge reads non-zero. Non-vacuous: the gauge value is driven
/// by the open, not by the pre-seed. The open drives the process-global recorder that BOTH apps
/// share, so the split (metrics off the main funnel'd app, onto its own loopback listener) is
/// transparent to the counts — proven here by opening on `make_app()` and reading on `metrics_app()`.
#[tokio::test]
async fn metrics_endpoint_serves_the_web_series_and_counts_a_real_open() {
    let app = make_app();
    let metrics = metrics_app();

    // A real catalog open (lazily minted, a real DungeonSession behind it), on the MAIN app.
    let (st, _) = get_as(&app, "/offerings/dungeon/session/metrics-probe", "prober").await;
    assert_eq!(st, StatusCode::OK, "the catalog session opens");

    // `/metrics` is NOT on the main app (the split) — it 404s there, proving it can't ride a funnel.
    let (st, _) = get_as(&app, "/metrics", "prober").await;
    assert_eq!(
        st,
        StatusCode::NOT_FOUND,
        "/metrics must NOT be on the public/funnel'd app"
    );

    // ...it lives on the separate loopback metrics app, reading the same global recorder.
    let (st, body) = get_as(&metrics, "/metrics", "prober").await;
    assert_eq!(
        st,
        StatusCode::OK,
        "GET /metrics answers 200 on the metrics app"
    );

    // Every series this surface emits is present (pre-seeded at install, moved by the sites).
    for name in [
        "dregg_web_sessions_open",
        "dregg_web_sessions_evicted_total",
        "dregg_web_opens_refused_total",
        "dregg_web_anchor_failures_total",
        "dregg_web_turns_refused_total",
        "dregg_web_session_resume_failures_total",
    ] {
        assert!(
            body.contains(name),
            "/metrics is missing the {name} series:\n{body}"
        );
    }

    // The open above really drove the gauge: at least the probed session is live.
    let open = series_value(&body, "dregg_web_sessions_open")
        .expect("the sessions-open gauge renders a value");
    assert!(
        open >= 1.0,
        "dregg_web_sessions_open should count the opened session, got {open}"
    );
}

/// A burst past a tiny armed policy (per-actor open quota = 1) is refused with the honest 429
/// AND increments `dregg_web_opens_refused_total{{limit="quota"}}` — the refusal counter moves
/// exactly when the gate fires (and the admitted first open does NOT count).
#[tokio::test]
async fn a_policy_refused_open_increments_the_refusal_counter() {
    // The recorder is process-global and idempotent; the router below is served bare (no
    // make_app), so install explicitly — the same handle `/metrics` renders from.
    let handle = metrics::install_recorder();

    let policy = SessionPolicy {
        max_opens_per_actor: Some(1),
        ..SessionPolicy::default()
    };
    let state = Arc::new(CatalogState::with_host(move || {
        catalog_default_host().with_policy(policy, SystemClock)
    }));
    let app = catalog_router(state);

    let before = series_value(
        &handle.render(),
        "dregg_web_opens_refused_total{limit=\"quota\"}",
    )
    .unwrap_or(0.0);

    // The first open is admitted...
    let (st, _) = get_as(&app, "/offerings/dungeon/session/q-one", "mallory").await;
    assert_eq!(st, StatusCode::OK, "the first open is within quota");
    // ...the second fresh mint by the SAME identity trips the quota gate: an honest 429.
    let (st, body) = get_as(&app, "/offerings/dungeon/session/q-two", "mallory").await;
    assert_eq!(
        st,
        StatusCode::TOO_MANY_REQUESTS,
        "the quota refuses: {body}"
    );

    let after = series_value(
        &handle.render(),
        "dregg_web_opens_refused_total{limit=\"quota\"}",
    )
    .expect("the quota-labelled refusal counter renders");
    assert!(
        after >= before + 1.0,
        "the refused open must land on the quota counter: before={before}, after={after}"
    );

    // Re-touching the ALREADY-LIVE session is never gated — and never counted as a refusal.
    let (st, _) = get_as(&app, "/offerings/dungeon/session/q-one", "mallory").await;
    assert_eq!(
        st,
        StatusCode::OK,
        "a touch of a live session is not an open"
    );
    let touched = series_value(
        &handle.render(),
        "dregg_web_opens_refused_total{limit=\"quota\"}",
    )
    .expect("the quota-labelled refusal counter renders");
    assert_eq!(
        touched, after,
        "a live-session touch must not increment the refusal counter"
    );
}
