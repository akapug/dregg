//! `dregg-persist-hosttest` — the persist-PD spine as a runnable host library:
//! the `no_std` chain-gate discipline, the REAL `redb` durable backend over a
//! block-device `StorageBackend`, and the app-hosting economy on top.
//!
//! THREE ORGANS, ONE SPINE (`.docs-history-noclaude/PG-DREGG-ON-SEL4-DEOS-SPINE.md`):
//!
//!  * [`commit_store`] — the persist-PD's chain-gate discipline, `no_std`+`alloc`
//!    over a `BTreeMap` stand-in. This is the module that rides INSIDE the persist
//!    PD verbatim (via `#[path]` include); the gate SEMANTICS, transport-free.
//!  * [`redb_store`] — the REAL durable store: the SAME `CommitRecord` + the SAME
//!    chain gate, but committed into real `redb` ACID tables over a
//!    [`redb::StorageBackend`] (a block device's five ops). On the host the backend
//!    is a file-backed region (REAL cross-process durability); on-device the SAME
//!    trait rides the seL4 block cap (the named rung). This makes "durable" real.
//!  * [`hosting`] — the app-hosting economy: pay-to-host as a VERIFIED VALUE TURN
//!    (a conserving Transfer through the durable spine), fee-lapse → eviction
//!    (a verified turn dropping the durable hosting), fail-closed, conserving.
//!
//! The `commit_store` module is written `#![no_std]`-shaped (`extern crate
//! alloc`); compiled here as part of a `std` crate, `extern crate alloc` aliases
//! std's own allocator (one allocator, no duplication — the same trick
//! `../crypto-floor-hosttest` uses for its carried `stark_core`). So the byte-for-
//! byte module the persist PD carries is exercised here against real `redb` + the
//! economy, on a box with no user-mode qemu-aarch64.

// `commit_store.rs` is `#![no_std]`; aliasing alloc to std's keeps it one
// allocator when compiled into this std lib.
extern crate alloc;

pub mod commit_store;
pub mod hosting;
pub mod redb_store;
