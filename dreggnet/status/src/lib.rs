//! `dreggnet-status` — the **public status page**: a no-auth "is the cloud up?"
//! page anyone can check.
//!
//! The cloud-provider readiness audit (`docs/CLOUD-PROVIDER-READINESS.md`) named
//! the gap plainly: *"Public status page (customer uptime/incidents) — LACK."*
//! This crate is that surface. Where [`dreggnet-ops`](../../ops) is the
//! admin-gated operator view of the whole cloud (logs, meters, per-machine
//! detail), this is the **public subset**: one overall banner, a per-service row,
//! the n=5 federation panel, recent incidents, and an uptime number — plus a
//! `/status.json` for external monitoring/embedding.
//!
//! ```text
//!   node /status · /api/federations · /metrics ─┐
//!   gateway /status · control · bridge relayer  ├─▶ StatusSource ─▶ RawHealth
//!   economy conservation (Σδ=0)                 ┘        │
//!                                                        ▼
//!                                              aggregate::build (honest rollup)
//!                                                        │
//!                                          ┌─────────────┴─────────────┐
//!                                          ▼                           ▼
//!                                   render::page_html              /status.json
//! ```
//!
//! ## The honesty law
//! A surface the page cannot reach renders [`model::ServiceState::Unknown`] —
//! never a false [`model::ServiceState::Operational`]. "We don't know" and "it's
//! down" are distinct, and neither is green.
//!
//! ## Honest scope
//! The **safe-autonomous** half is the crate + the render + the
//! health-aggregation + tests, green-standalone over deterministic
//! [`source::FixtureSource`] fixtures. The **reviewed-go** half is the live-edge
//! deploy — wiring [`live::LiveSource`] at `status.example.com` behind the real
//! health surfaces.

pub mod aggregate;
pub mod client;
pub mod config;
pub mod fixtures;
pub mod incidents;
pub mod live;
pub mod model;
pub mod render;
pub mod source;

pub use config::StatusConfig;
pub use model::StatusPage;
pub use source::{FixtureSource, StatusSource};

/// The current time as RFC3339 (the page's `generated_at`), or a fallback.
pub fn now_rfc3339() -> String {
    time::OffsetDateTime::now_utc()
        .format(&time::format_description::well_known::Rfc3339)
        .unwrap_or_else(|_| "unknown".to_string())
}

/// The current Unix time in seconds (for uptime windows).
pub fn now_epoch() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Assemble the public status page from a source (the one entry point both the
/// server and the tests use).
pub fn status_page(source: &dyn StatusSource) -> StatusPage {
    let raw = source.health();
    let windows = source.uptime_windows();
    aggregate::build(&raw, now_rfc3339(), now_epoch(), &windows)
}
