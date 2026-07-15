//! # host-gateway — a fly-compat Machines-API host gateway + cap-scoped reads.
//!
//! One serving block ([`Gateway`]) is the public control + hosting surface for agents
//! and their launches — a verified hosting edge. It classifies every inbound request:
//!
//! ```text
//!   fly client ─HTTP─▶  Gateway::handle
//!                         │  Host <name>.<apex> / verified custom domain ─▶ microsite  (static, content-addressed)
//!                         │  /ask?domain=<host>                          ─▶ on-demand-TLS ask (starbridge_domains::is_verified)
//!                         │  /api/{sites,domains,machines,servers,…}     ─▶ cap-scoped reads (subject VERIFIED by the gateway)
//!                         │  /v1/apps/{app}/machines...                  ─▶ fly machines API (create owner-scoped)
//!                         │  / , /status , /healthz                      ─▶ friendly surfaces
//! ```
//!
//! ## Assembled on the resident substrate (no forks)
//!
//! * [`http_serve`] — the hardened HTTP/1.1 serve loop the gateway serves on.
//! * [`starbridge_domains`] — the verified custom-domain resolver + the
//!   `is_verified` read the on-demand-TLS `ask` consults.
//! * [`webauth_core`] — the gateway VERIFIES a presented `dga1_` credential itself and
//!   derives the cap-scope subject from it (it trusts no upstream header; see
//!   [`auth::SubjectAuth`]).
//! * [`dregg_ipfs`] — a dregg content commitment IS an IPFS CID, so a launch's landing
//!   page, token metadata, and image are content-addressed ([`content`], [`launchpad`]).
//!
//! ## The launch composition (the offering)
//!
//! The gateway is not just a router: [`launchpad::Launchpad`] composes a [`launchpad::Launch`]
//! into a **live landing microsite** whose metadata + image are content-addressed — so
//! the instant a launch lands it is served at `<slug>.<apex>` and re-witnessable by CID.
//!
//! ## Parameterized apex, no product branding
//!
//! The hosting apex is configuration ([`SiteRegistry::new`] / [`starbridge_domains`]'s
//! `apex_from_env`), never a hardcoded host. The crate is substrate-general.
//!
//! ## Assembling + serving
//!
//! ```no_run
//! use std::sync::Arc;
//! use host_gateway::{Gateway, SiteRegistry, MachinesHandler, SubjectAuth};
//! use starbridge_domains::DomainRegistry;
//!
//! let sites = Arc::new(SiteRegistry::new("dregg.net"));
//! let domains = Arc::new(DomainRegistry::new());
//! let gateway = Gateway::new(
//!     sites,
//!     domains,
//!     MachinesHandler::new(),
//!     SubjectAuth::trusted_header("x-dregg-subject"),
//! );
//! http_serve::serve_http("127.0.0.1:8080", gateway.into_service()).unwrap();
//! ```

pub mod api;
pub mod auth;
pub mod content;
pub mod gateway;
pub mod launchpad;
pub mod machines;
pub mod microsite;
pub mod route;

pub use api::{
    AgentSource, AgentView, ApiHandler, BillingSource, ServerSource, ServerView, SpendLine,
};
pub use auth::SubjectAuth;
pub use content::{ContentStore, address};
pub use gateway::Gateway;
pub use launchpad::{Launch, LaunchError, LaunchReceipt, Launchpad};
pub use machines::{
    CreateMachineRequest, GuestConfig, Machine, MachineConfig, MachineLauncher, MachineState,
    MachineStore, MachinesHandler, NullLauncher,
};
pub use microsite::{Asset, Microsite, SiteError, SiteRegistry};
pub use route::Route;

// Re-export the resident custom-domain control plane the gateway aggregates, so a
// caller wires bindings without a second dependency line.
pub use starbridge_domains::{DomainBinding, DomainRegistry};
