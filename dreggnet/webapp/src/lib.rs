//! `dreggnet-webapp` — the agent-served-web-API capability.
//!
//! DreggNet's headline vision is *fully agentic web-facing apps*: an agent
//! autonomously assembles a web API and DreggNet runs + serves it. This crate is
//! the capability that makes a request to a served route turn into a real run of
//! the agent's handler **on the owned sandbox**, metered against a dregg execution-lease.
//!
//! ```text
//!   agent assembles                 DreggNet runs + serves
//!   ───────────────                 ──────────────────────
//!   WebApp { routes: [              inbound HTTP ─▶ Router::serve
//!     Route { GET /add ─▶ handler },                 │ match the route
//!     Route { GET /hello ─▶ handler },               │ Handler::build_source
//!   ] }                                              ▼
//!                                    dreggnet_exec::run_workload  (owned wasm sandbox)
//!                                                    │ Output { values }
//!                                                    ▼
//!                                    ResponseSpec::render ─▶ WebResponse
//! ```
//!
//! ## The slice that is real today
//!
//! - An agent declares a [`WebApp`] (plain `serde` data — a JSON document, or the
//!   [`assemble`] builders): routes binding a method + path to a the owned sandbox
//!   [`Handler`] and a [`ResponseSpec`].
//! - [`Router::serve`] matches a request to a route, builds the handler's
//!   concrete workload (filling [`HandlerBody::Templated`] placeholders from the
//!   request query, integer-validated), **runs it on the owned sandbox** via
//!   [`dreggnet_exec::run_workload`], and renders the result.
//! - [`LeasedRouter`] runs each served request as a **durable, exactly-once-metered
//!   workflow** against a funded dregg [`Lease`](dreggnet_bridge::Lease) — validated
//!   through the bridge's real gate. It refuses an over-budget request with `402`
//!   before the handler runs, and a request that clears the gate runs THROUGH
//!   [`dreggnet_durable`]: the handler executes on the owned sandbox, its result is durably
//!   checkpointed, and the meter charges the step exactly-once (so a crash mid-request
//!   resumes exactly-once — the same guarantee the durable bridge gives per step).
//! - The bundled `dreggnet-serve` binary serves an assembled app over real TCP
//!   (std sockets, cross-platform), so `curl localhost:PORT/add?a=40&b=2` returns
//!   `{"result":42}` computed in the wasm sandbox.
//!
//! ## What is stubbed / a later rung (honest)
//!
//! - **Path patterns** — routes match an *exact* path; `/users/{id}` params are a
//!   later rung. Per-request inputs reach a handler through the query string.
//! - **Request body → handler** — the handler entrypoint is the sandbox's zero-arg
//!   `run`; request data reaches the handler via templated query params, not the
//!   request body. A richer handler ABI (request bytes in, response bytes out)
//!   waits on a sandbox host-import shape for it.
//! - **Per-request durable store** — [`LeasedRouter`] runs each request through a
//!   full durable `dreggnet_durable` workflow over an **on-disk** SQLite store
//!   (`run_workflow_on_disk_blocking` under `std::env::temp_dir()/dreggnet-webapp/<app>`,
//!   `router.rs`). That proves the request→durable→exactly-once-metered weld AND gives
//!   cross-process crash-resume (a request that crashes mid-workflow resumes from the
//!   on-disk cursor; proved by the crash-resume integration test). Postgres is the
//!   later production-store rung. The plain [`Router`] still runs the direct exec path
//!   (no metering, no durability).
//! - **Gateway mount** — the Linux-only `httpe` gateway adopts [`Router`] in
//!   `gateway/src/webapp.rs`; this crate's portable `dreggnet-serve` is the
//!   any-host serving path.
//!
//! ## The static sibling: [`hosting`]
//!
//! Alongside the dynamic API capability above, [`hosting`] serves *static*
//! minisites on the verified rail: **a site is a dregg cell** ([`SiteCell`]). An
//! agent/user publishes content (HTML/CSS/JS) under a name via a cap-gated,
//! receipted [`SiteRegistry::publish`], and the gateway resolves
//! `<name>.dregg.works` → the site cell → its content. Because the cell carries a
//! content commitment, the same content can be served *trustlessly* (the
//! `deos-view` projection). See the [`hosting`] module docs.
//!
//! [`WebApp`]: spec::WebApp
//! [`Handler`]: spec::Handler
//! [`ResponseSpec`]: spec::ResponseSpec
//! [`HandlerBody::Templated`]: spec::HandlerBody::Templated
//! [`SiteCell`]: hosting::SiteCell
//! [`SiteRegistry::publish`]: hosting::SiteRegistry::publish

pub mod assemble;
pub mod hosting;
pub mod http;
pub mod router;
pub mod serve;
pub mod spec;
pub mod verify;

pub use serve::{
    ServeRequest, dispatch, fetch_site_bundle, serve_connection, serve_http, serve_http_connection,
    serve_registry,
};
pub use verify::{
    SITE_RECEIPT_PATH, SiteReceiptBundle, SiteVerifyError, VerifiedSite, hex32, parse_hex32,
    verify_site_bundle,
};

/// The ONE product-wide receipt contract (re-exported): `PublishReceipt`,
/// `BindReceipt`, and the deploy's view all speak this. A product receipt is
/// prev-hash-chained + ed25519-signed + re-witnessable, the kernel
/// TurnReceipt/BridgeReceipt discipline. See `docs/RECEIPT-CONTRACT.md`.
pub use dreggnet_receipt as receipt;
pub use hosting::{
    Asset, BandwidthMeter, PublishCap, PublishError, PublishReceipt, SiteCell, SiteContent,
    SiteRegistry, content_root, content_type_for, is_valid_name, site_name_from_host,
};
pub use http::{HttpMethod, WebRequest, WebResponse};
pub use router::{LeasedRouter, MeterSnapshot, Router, handler_workload_spec};
pub use spec::{Handler, HandlerBody, HandlerError, ResponseSpec, Route, WebApp};
