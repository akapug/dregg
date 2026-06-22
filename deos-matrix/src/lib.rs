//! `deos-matrix` — the protocol foundation of the native deos Matrix client.
//!
//! This crate stands on the official [`matrix_sdk`] (matrix-rust-sdk). It owns
//! its own tokio runtime and exposes a small, deos-shaped API:
//!
//! - [`MatrixClient`] — configure a homeserver, log in (password), restore a
//!   session, run an encrypted sync, list joined rooms, read a room's recent
//!   timeline.
//!
//! The async/sync boundary is the load-bearing design point. `matrix-rust-sdk`
//! is tokio-async; dregg's embedded executor is sync. So we keep ALL async I/O
//! inside this crate and expose a deos-friendly surface. The UI (gpui) and the
//! deos confinement seams (identity-cell binding, device-keys-as-caps, the
//! comms-PD) are layered ABOVE this crate later — see `README.md`.
//!
//! # Design lineage
//!
//! The worker/request-response bridge mirrors `iamb`'s `worker.rs`: a synchronous
//! caller sends a typed request over a channel; the async worker (running on the
//! tokio runtime) executes the matrix-sdk call and replies over a oneshot. That
//! is the SAME shape we will use to bridge into the sync dregg executor. The
//! headless library here is `async fn` directly (so it composes with any tokio
//! caller, including the CLI); [`worker`] sketches the sync-facing bridge that the
//! confined comms-PD will use.

pub mod client;
pub mod membrane;
pub mod session;
pub mod source;
pub mod worker;

#[cfg(feature = "gui")]
pub mod chat;

#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;

pub use client::{MatrixClient, RoomSummary, TimelineMessage};
pub use session::StoredSession;
pub use source::{ChatSource, MockSource};

/// Crate-wide error type.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("matrix sdk error: {0}")]
    Sdk(#[from] matrix_sdk::Error),
    #[error("client build error: {0}")]
    ClientBuild(#[from] matrix_sdk::ClientBuildError),
    #[error("matrix id parse error: {0}")]
    IdParse(#[from] matrix_sdk::IdParseError),
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("session (de)serialization error: {0}")]
    Session(#[from] serde_json::Error),
    #[error("{0}")]
    Other(String),
}

pub type Result<T> = std::result::Result<T, Error>;
