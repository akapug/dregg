//! **The REACTOR proof for polis (the council auto-certifier), end-to-end.**
//!
//! The fifth axis (AX5): the council's approve→certify threshold step made
//! reactive. A committed quorum-crossing `approve` drives the
//! [`CouncilCertifyReactor`] to emit its own `certify` turn — the on-chain
//! governance loop, the reactive twin of [`crate::service::CouncilService::certify`].
//!
//! The reactor + service faces are compiled INTO THIS TEST BINARY via `#[path]` —
//! they are NOT library modules, because `dregg-sdk` depends on `starbridge-polis`
//! and `dregg-app-framework` depends on `dregg-sdk`, so a normal `polis →
//! app-framework` edge would close an illegal package cycle. Cargo permits it only
//! across the dev-dependency edge this binary uses. See `Cargo.toml`'s
//! `[features].deos` comment.
//!
//! The end-to-end reaction assertions live in `src/reactor.rs`'s `#[cfg(test)]`
//! module (it owns the `react_build` → executor flow); this binary is the glue
//! that compiles the cycle-bound faces into a runnable test target.

#![cfg(feature = "deos")]
#![allow(dead_code)] // each included module has pub items this binary uses a subset of

#[path = "../src/service.rs"]
mod service;

#[path = "../src/reactor.rs"]
mod reactor;
