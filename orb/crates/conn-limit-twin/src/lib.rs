//! Twin (executable model) of the blocking reactor's SHARED per-source
//! **connection-limit gate** — `SharedStanding::admit` / `on_close` in
//! `crates/dataplane/src/standing.rs`.
//!
//! The io_uring / kqueue shards use the lock-free [`Standing`] because each
//! shard's per-source counters are touched by ONE thread only (the shard event
//! loop) — there is no cross-thread race there to model, which is exactly why it
//! needs no lock. The `SharedStanding` variant is the genuinely concurrent one:
//! the thread-per-connection *blocking* reactor runs its accept loop and its
//! per-connection worker threads at the same time, so `admit` (the `ConnLimit`
//! gate's check-and-increment) and `on_close` (the worker's decrement on return)
//! race across threads for one source's counter.
//!
//! The safety claim (`standing.rs:225-237`, doc-comment, machine-checked nowhere
//! before this model): the check-and-increment is a SINGLE critical section, so
//! two concurrent accepts from one source cannot both read `active == cap-1` and
//! both admit — there is no TOCTOU window that over-admits past the cap. Split
//! that check and increment into two critical sections and the window reopens:
//! both accepts read under the cap, both increment, and the source ends with
//! `cap+1` live connections — the `ConnLimit` decision (`Reactor.Stage.ConnLimit`,
//! `Reactor/StandingCounters.lean`) is violated at run time. This is the same
//! structural invariant `SharedStanding::rate_note` relies on for the `429`
//! rate gate (one stripe held across age-and-count).
//!
//! The model itself lives in `tests/loom.rs`, exercised under `--cfg loom` for
//! exhaustive schedule exploration. This crate is deliberately zero-dependency
//! and separate from `dataplane`: the dataplane package's `build.rs` links the
//! Lean runtime (`libleanshared`) into every target, and that runtime breaks
//! loom's unwind-based panic capture inside its stackful coroutines — the same
//! reason `ring-twin`, `wake-twin`, `borrow-recycle-twin`, and `splitsend-twin`
//! are their own crates.
//!
//! See `tests/loom.rs` for the model, the real-gate correspondence, and the
//! explicit statement of what it covers versus the deployed `standing.rs`.
#![deny(unsafe_op_in_unsafe_fn)]
