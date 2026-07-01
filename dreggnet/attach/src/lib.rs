//! `dreggnet-attach` — the **portal web attach**: the web twin of the SSH attach.
//!
//! ember's distribution model is that a user attaches to a hosted, cap+budget+
//! receipt-bounded Hermes agent **via SSH _or the portal_**. A sibling lane
//! builds the hosted session + the SSH face; this crate is the **web face**,
//! built against the *same* session contract so the two are twins, not forks.
//!
//! ```text
//!   webauth dga1_ forward-auth ──▶ X-Dregg-Subject (the cap holder = the OWNER)
//!                                          │
//!   a natural-language goal + budget +     ▼
//!   a cap bundle  ───────────────▶  dreggnet-attach  ──drive──▶  a hosted agent
//!                                   (cap-SCOPE to the subject)    session (LiveRun)
//!                                          │
//!         live reason→act→observe transcript (SSE) · budget meter · receipt chain
//!                                          │
//!                                          ▼
//!                       verify-in-browser: re-witness the chain + the bound
//!                       ("✓ the agent stayed in its box, here's the proof")
//! ```
//!
//! ## The session contract (no duplication)
//!
//! The hosted-agent-session record IS [`dreggnet_exec::live::LiveRun`] — the goal,
//! the model, the funded budget, the granted cap bundle, the workdir, the
//! re-witnessable [`AgentRunReport`](dreggnet_exec::agent::AgentRunReport) receipt
//! chain, and the narrated reason→act→observe [`transcript`](session). The web
//! attach drives + streams + re-witnesses that record; it does not re-implement
//! the loop. Re-witness is the SSH attach's own [`verify_live`](dreggnet_exec::live::verify_live).
//!
//! - [`session`] — the [`session::AgentSession`] wrapper (the `LiveRun` + its
//!   owner subject + id), the [`session::GoalRequest`] the goal box submits, and
//!   the [`session::Owned`] trait the cap-scoping rides.
//! - [`transcript`] — the enriched, streamable reason→act→observe step + the
//!   running [`transcript::BudgetMeter`], derived from the signed log + receipts.
//! - [`driver`] — drive a goal into a session: the deterministic demo planner
//!   (the safe-autonomous path) behind a [`driver::SessionDriver`] seam the live
//!   Hermes brain (reviewed-go) swaps into.
//! - [`store`] — the per-subject session store + **the cap-scoping teeth**: a user
//!   sees + drives ONLY their own sessions (another subject's is isolated).
//! - [`stream`] — the SSE wire: the transcript as `text/event-stream` frames.
//! - [`verify`] — verify-in-browser: re-witness a session's chain + budget bound.
//! - [`render`] — server-render the attach page (goal box + the live transcript +
//!   budget meter + receipts + the verify button).
//! - [`config`] — runtime config (bind, the cap gate, the login base).
//!
//! ## Honest scope
//! This is the **safe-autonomous** half: the web attach + the drive/stream/verify
//! + the cap-scoping + tests, green-standalone over a deterministic demo planner.
//! The **reviewed-go** half is the live edge — the Caddy route for
//! `portal.example.com` + a [`driver::SessionDriver`] backed by the live hosted
//! session backend (the sibling lane's Hermes/Kimi brain over a real workdir),
//! named in [`driver`] and [`config`], not faked here.

pub mod config;
pub mod driver;
pub mod render;
pub mod session;
pub mod store;
pub mod stream;
pub mod transcript;
pub mod verify;

pub use config::AttachConfig;
pub use session::{AgentSession, GoalRequest};
pub use store::SessionStore;

/// The current time as RFC3339 (a session's `created_at`), or a fallback.
pub fn now_rfc3339() -> String {
    time::OffsetDateTime::now_utc()
        .format(&time::format_description::well_known::Rfc3339)
        .unwrap_or_else(|_| "unknown".to_string())
}
