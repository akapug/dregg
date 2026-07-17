//! Prometheus metrics for the web surface's operational observability.
//!
//! The web analogue of `node/src/metrics.rs` (the ONE pattern in this repo): install the
//! process-global Prometheus recorder once (idempotent), expose a `GET /metrics` axum handler
//! rendering the exposition format, and provide the small named emit helpers the surface's
//! call sites bump. The `metrics` macros are no-ops until a recorder is installed, so the
//! library stays zero-cost for embedders that never mount `/metrics`.
//!
//! ## The series (all emitted by this crate)
//! - `dregg_web_sessions_open` (gauge) — the catalog host's TOTAL live-session count (the sum
//!   over every registered offering), set at each catalog open touch + each lifecycle sweep;
//! - `dregg_web_sessions_evicted_total` — sessions evicted by the lifecycle sweep
//!   ([`CatalogState::sweep`](crate::CatalogState::sweep): the interval task + the tests'
//!   explicit sweeps). Honest scope: the host ALSO sweeps/LRU-evicts internally on a fresh
//!   open past capacity; those shed sessions are visible as the `sessions_open` gauge dropping,
//!   not on this counter (the host does not report them across its API);
//! - `dregg_web_opens_refused_total{limit="quota"|"rate"|"capacity"}` — session opens refused
//!   by an armed [`SessionPolicy`](dreggnet_offerings::SessionPolicy) gate (the honest-429
//!   paths), labelled by WHICH limit tripped ([`PolicyRefusal`](dreggnet_offerings::PolicyRefusal));
//! - `dregg_web_anchor_failures_total` — a verified, ranked Descent run whose devnet-node
//!   anchor (`DescentState::settle_run`) failed (the `settled=false` fail-closed branch of
//!   `POST /descent/submit`);
//! - `dregg_web_turns_refused_total` — offering advances the EXECUTOR refused
//!   (`Outcome::Refused` — the anti-ghost tooth firing), on the catalog and the
//!   single-offering surface alike;
//! - `dregg_web_session_resume_failures_total` — persisted session move-logs that REFUSED to
//!   reopen by replay (tampered / undeployable, fail-closed): the boot `resume_all` refusals
//!   and the lazy-resume `409 Conflict` path.

use std::sync::OnceLock;

use metrics::{counter, gauge};
use metrics_exporter_prometheus::{PrometheusBuilder, PrometheusHandle};

/// The process-global Prometheus handle. The recorder may only be installed ONCE per process
/// (a second `install_recorder()` errors — the global recorder is already set), so we install
/// on first call and hand back a clone of the same handle thereafter. This makes
/// `install_recorder()` idempotent, which matters when several in-process tests (or a
/// re-entrant `make_app`) each ask for the recorder. Same shape as `node/src/metrics.rs`.
static RECORDER: OnceLock<PrometheusHandle> = OnceLock::new();

/// Install the Prometheus metrics recorder (idempotent). Returns the handle used to render
/// the exposition-format output from the `/metrics` endpoint.
pub fn install_recorder() -> PrometheusHandle {
    RECORDER
        .get_or_init(|| {
            let handle = PrometheusBuilder::new()
                .install_recorder()
                .expect("failed to install Prometheus metrics recorder");
            // Pre-register every series at 0 so a dashboard renders "0" (a live, healthy
            // surface) from boot rather than "No data" until the first event — the Prometheus
            // recorder only creates a series on first touch, so an `increment(0)` / `set(0.0)`
            // here materializes it. The `limit` label values below are exactly the ones the
            // real emit site (`inc_open_refused`) uses.
            gauge!("dregg_web_sessions_open").set(0.0);
            counter!("dregg_web_sessions_evicted_total").increment(0);
            counter!("dregg_web_opens_refused_total", "limit" => "quota").increment(0);
            counter!("dregg_web_opens_refused_total", "limit" => "rate").increment(0);
            counter!("dregg_web_opens_refused_total", "limit" => "capacity").increment(0);
            counter!("dregg_web_anchor_failures_total").increment(0);
            counter!("dregg_web_turns_refused_total").increment(0);
            counter!("dregg_web_session_resume_failures_total").increment(0);
            handle
        })
        .clone()
}

/// Axum handler for `GET /metrics` — renders the Prometheus exposition format.
pub async fn metrics_handler(
    axum::extract::State(handle): axum::extract::State<PrometheusHandle>,
) -> String {
    handle.render()
}

// ─── Gauges ──────────────────────────────────────────────────────────────────

/// Set the catalog host's total live-session count (summed over every registered offering).
pub fn set_sessions_open(count: f64) {
    gauge!("dregg_web_sessions_open").set(count);
}

// ─── Counters ────────────────────────────────────────────────────────────────

/// `n` sessions were evicted by a lifecycle sweep (idle-past-TTL shed by the interval task /
/// an explicit [`CatalogState::sweep`](crate::CatalogState::sweep)).
pub fn inc_sessions_evicted(n: u64) {
    counter!("dregg_web_sessions_evicted_total").increment(n);
}

/// A session open was refused by an armed policy gate. `limit` names WHICH gate tripped —
/// `"quota"` (per-actor open quota), `"rate"` (min open interval), `"capacity"` (per-offering
/// live-session cap with nothing evictable) — matching the [`PolicyRefusal`] variants.
///
/// [`PolicyRefusal`]: dreggnet_offerings::PolicyRefusal
pub fn inc_open_refused(limit: &'static str) {
    counter!("dregg_web_opens_refused_total", "limit" => limit).increment(1);
}

/// A ranked Descent run's devnet-node anchor failed (`settle_run` returned `Err` — the run
/// still ranks in-process; the on-chain anchor is fail-closed, never a silent success).
pub fn inc_anchor_failure() {
    counter!("dregg_web_anchor_failures_total").increment(1);
}

/// The executor refused an offering advance (`Outcome::Refused` — a crafted / ineligible turn
/// landed as a REAL refusal, nothing committed). The anti-ghost tooth, made countable.
pub fn inc_turn_refused() {
    counter!("dregg_web_turns_refused_total").increment(1);
}

/// A persisted session move-log refused to reopen by replay (tampered / undeployable —
/// fail-closed, the durable file kept): a boot `resume_all` refusal or the lazy-resume
/// `409 Conflict` path.
pub fn inc_resume_failure() {
    counter!("dregg_web_session_resume_failures_total").increment(1);
}
