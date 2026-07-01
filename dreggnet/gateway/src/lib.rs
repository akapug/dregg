//! DreggNet gateway — the fly.io-compatible machines API (ladder rung 5).
//!
//! This is the public control surface: an HTTP API shaped like the
//! [Fly Machines API](https://fly.io/docs/machines/api/) so an existing fly
//! client can create, inspect, and reap durable workloads on DreggNet. Each
//! create maps onto a dregg execution-lease and is fulfilled through the bridge
//! ([`dreggnet_bridge`]).
//!
//! ```text
//!   fly client  ──HTTP──▶  MachinesHandler        (this crate, a dreggnet_http::Handler)
//!                            │  route::parse        (fly path → Route)
//!                            │  lease::lease_for_create   (CreateMachineRequest → dregg Lease)
//!                            ▼
//!                          MachineGateway          (records the machine + its lease)
//!                            │  workflow_input_for_lease   (the bridge's REAL lease gate)
//!                            ▼
//!                          dreggnet_bridge::fulfill (the durable polyana workload, metered)
//! ```
//!
//! ## The fly-compatible surface
//!
//! | Method + path | Route | Status |
//! |---|---|---|
//! | `POST /v1/apps/{app}/machines` | create + admit a lease | real routing/lease-gate; body decode at the [`http`] seam |
//! | `GET  /v1/apps/{app}/machines` | list | real |
//! | `GET  /v1/apps/{app}/machines/{id}` | status | real |
//! | `POST /v1/apps/{app}/machines/{id}/stop` | reap | real |
//! | `POST /v1/apps/{app}/machines/{id}/start` | (re)launch | real |
//! | `DELETE /v1/apps/{app}/machines/{id}` | destroy | real |
//!
//! The durable launch ([`MachineGateway::fulfill`]) either **dispatches the lease
//! over the overlay to a compute node** (a [`ComputeBackend`], the live
//! edge→node-a path via [`dreggnet_control::dispatch_lease_over_mesh`]) or, with
//! no backend configured, fulfills it **in-process** ([`dreggnet_bridge::fulfill`],
//! the single-box / dev default). The serving binary blocks on it from the create
//! request path (the connection loop is synchronous thread-per-connection), so a
//! dispatch-configured `POST .../machines` runs the workload on the node and returns
//! the machine already reflecting the real metered outcome.
//!
//! ### Divergences from fly (noted honestly)
//! - fly runs every machine as a firecracker microVM; DreggNet grades the
//!   requested guest onto the dregg cap-lattice ([`lease::cap_grade_for_guest`])
//!   so a small workload can use the cheaper sandbox tier the bridge wires today.
//! - The lease budget is currently *derived from the guest size*; a real funded
//!   lease is read from a dregg lease cell (the bridge's `dregg-verify` lane).
//! - `image` is a polyana workload reference, not an OCL image pull.
//!
//! Built on the gateway's own clean-room HTTP value vocabulary
//! ([`dreggnet_http`]) over a hand-rolled `std::net` serving loop — pure-`std`,
//! no third-party HTTP engine, so it builds and tests natively on macOS as well
//! as Linux. For a Linux deploy artifact from macOS:
//! `cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-gateway`.

pub mod api;
pub mod funding;
pub mod gateway;
pub mod hosting;
pub mod http;
pub mod lease;
pub mod metrics;
pub mod route;
pub mod sitepublish;
pub mod status;
pub mod storage;
pub mod types;
pub mod webapp;
pub mod webresp;

pub use api::{ApiHandler, BillingSource, ServerSource, ServerView, SpendLine};
pub use funding::{AttestedFunding, FundingError, FundingSource, NodeFunding};
pub use gateway::{ComputeBackend, GatewayError, MachineGateway};
pub use hosting::SiteHostHandler;
pub use http::{MachinesHandler, parse_create_request};
pub use metrics::{Metrics, Surface};
pub use route::Route;
pub use sitepublish::SitePublishHandler;
pub use status::{ComputeStatus, FederationStatus, GatewayInfo, GatewayStatus};
pub use storage::StorageHandler;
pub use types::{
    ApiError, CreateMachineRequest, DispatchReport, GuestConfig, Machine, MachineConfig,
    MachineState, OkBody,
};
pub use webapp::WebAppHandler;
