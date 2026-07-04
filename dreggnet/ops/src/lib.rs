//! `dreggnet-ops` — the DreggNet Cloud OPS/ADMIN dashboard.
//!
//! This is the operator's single pane of glass over the whole DreggNet cloud. It
//! does **not** duplicate or re-implement any service; it **aggregates** the live
//! read surfaces that already exist:
//!
//! ```text
//!   dregg node (:8420)        ──HTTP──┐
//!   gateway   (:8080)         ──HTTP──┤
//!   discord bot (:8080, read) ──HTTP──┼──▶  dreggnet-ops  ──▶  one admin-gated
//!   durable meter outbox (pg) ──SQL───┤        (aggregate)        HTML dashboard
//!   docker engine (logs)      ──sock──┘                          + JSON snapshot
//! ```
//!
//! What it shows (the four asks):
//! 1. **All-activity** — the node's live turn/receipt log + committed events, the
//!    gateway's machines, the durable jobs (from the meter outbox), and the bot's
//!    app/hermes activity, unified into one feed and per-category tables.
//! 2. **Status of all tracked things** — leases/durable-jobs (meter outbox),
//!    machines (gateway), federation nodes + consensus (node), compute backend
//!    (gateway dispatch config).
//! 3. **Logs + dashboards** — tails each service's container logs (Docker Engine
//!    API over the mounted socket) + summary tiles (turns, block height, peers,
//!    machines, jobs in flight, units spent).
//! 4. **Whole-cloud health** — a top-level rollup: node / gateway / bot / postgres
//!    up?, federation N members, consensus live?, the at-a-glance verdict.
//! 5. **Coin-bridge observability** — the Solana/Stripe mirror bridge: the
//!    lock→mint / redeem activity (node-derived), the conservation invariant
//!    (`live ≤ locked`) + double-mint signals (relayer-derived), and the relayer /
//!    Solana-cluster / Stripe-receiver reachability. See [`bridge`].
//! 6. **Historical-log viewers** — a browsable, filterable "what happened" ledger
//!    over the receipt chain / turn log, the leases & machines, the compute runs,
//!    the $DREGG economy, and the bridge — sliceable by category / who / effect /
//!    text / time window. This is the human "understand what's going on" surface;
//!    Grafana (cross-linked from the header) is the deep time-series. See [`history`].
//!
//! Every upstream is fetched **defensively**: an unreachable source degrades to a
//! recorded `SourceStatus` (reachable=false + the error) rather than failing the
//! page, so the dashboard renders the true partial state of a cloud mid-deploy.
//!
//! Auth: the dashboard is gated by a **separate admin password** at the Caddy edge
//! (a dedicated basic-auth block, distinct from the public operator credential).
//! An optional app-level [`config::OpsConfig::admin_token`] adds defence-in-depth
//! underneath it.

pub mod aggregate;
pub mod bridge;
pub mod client;
pub mod config;
pub mod docker;
pub mod history;
pub mod pg;
pub mod render;

pub use aggregate::CloudSnapshot;
pub use config::OpsConfig;
