//! spec_audit.rs — THE SPECULATIVE-AUDIT execution model.
//!
//! # The idea (measurement-validated)
//!
//! The verified Lean executor floors at ~15µs/turn (gate Poseidon2 ~9.2µs + function-backed state
//! eval ~5.9µs — both inherent, NOT marshalling; the FFI copy is already minimal). The fast Rust
//! [`TurnExecutor`] runs at ~0.5µs. So instead of paying the verified floor on the interaction hot
//! path, we run the FAST Rust executor LIVE and have the verified Lean executor REPLAY the same turn
//! OFF the hot path to AUDIT for divergence.
//!
//! This is SPECULATIVE EXECUTION at the turn granularity:
//!   * **Rust speculates** — [`SpeculativeAudit::execute_live`] runs the Rust executor and returns
//!     IMMEDIATELY (the fast path the desktop already takes). It also captures the pre-state and the
//!     Rust post-root and enqueues an [`AuditEntry`].
//!   * **Lean verifies / retires** — the audit worker drains the queue and, for each entry, replays
//!     the turn through the verified Lean executor (`lean_apply::execute_via_lean`) against the SAME
//!     pre-state, then asserts the Lean post-root equals the Rust post-root (the differential, here
//!     promoted from `lean_state_producer_differential.rs`'s test assertion into a runtime audit).
//!
//! The user gets the fast experience; the verified executor is the authority that catches any Rust
//! bug. The Lean result is AUTHORITATIVE — a mismatch means the Rust executor has a bug (Rust is the
//! artifact dregg2 exists to REPLACE because it is buggy). On divergence we do NOT panic the live
//! path: we record + signal a [`DivergenceReport`] (callback + `tracing::error!`).
//!
//! # What this prototype does NOT decide (flagged for ember — trust-model layer)
//!
//! This harness is deliberately generic over *when* the audit runs (eager background thread vs.
//! batched caller pump) and does NOT hardcode a RETIREMENT/SETTLEMENT policy. The open trust-model
//! questions — does the user see speculative (Rust) or audited (Lean) state? what does
//! "retirement" mean (a settlement barrier? a checkpoint the audit must clear before export)? what
//! happens to turns that built on a diverged turn? — are a later design layer, NOT decided here. See
//! the module-level note in the demo test.
//!
//! # Coverage boundary (fail-closed, surfaced)
//!
//! The audit can only compare a turn the verified producer can run: marshallable AND root-agreeing
//! (`lean_apply::execute_via_lean` returns the verified post-state). A turn outside that COVERED set
//! is recorded as [`AuditOutcome::Skipped`] with the precise reason (an `ExtractError`), NEVER
//! silently treated as agreement — the coverage gap is surfaced, exactly as the producer path fences
//! its uncovered partition.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use dregg_cell::Ledger;
use dregg_turn::executor::TurnExecutor;
use dregg_turn::shadow::ShadowHostCtx;
use dregg_turn::turn::{Turn, TurnResult};

use crate::lean_apply::{self, ExtractError};

/// A speculative turn awaiting verified audit: the turn, its captured pre-state, and the Rust
/// executor's post-root (the SPECULATED root the verified replay is checked against).
///
/// The pre-state is captured as a full [`Ledger`] clone so the verified replay can run against
/// EXACTLY the state the Rust executor saw — independent of any later live turns that mutated the
/// working ledger. (A production retirement layer would snapshot a root + a delta journal instead of
/// a full clone; this prototype keeps the clone for fidelity and clarity.)
pub struct AuditEntry {
    /// The monotonic index of this turn in the live stream (for the divergence report).
    pub turn_index: u64,
    /// The turn the Rust executor speculatively executed.
    pub turn: Turn,
    /// The pre-state the Rust executor ran against (a full clone — the verified replay's template).
    pub pre_ledger: Ledger,
    /// The host admission context the Rust executor used — the verified replay MUST see the same
    /// clock / freeze-set / chain-head / budget, or the differential is meaningless.
    pub host: ShadowHostCtx,
    /// Whether the Rust executor COMMITTED the turn (the speculated commit bit).
    pub rust_committed: bool,
    /// The speculated post-state the verified replay is checked against. Either the genuine Rust
    /// post-ledger (root computed lazily IN the audit, OFF the hot path — the canonical Poseidon
    /// commitment is NOT part of the desktop's interaction path), or a caller-FORCED root (fault
    /// injection). Keeping root computation in the audit is what keeps the live path at Rust speed.
    pub rust_post: SpeculatedPost,
}

/// The speculated post-state an [`AuditEntry`] carries — resolved to a root IN the audit worker.
pub enum SpeculatedPost {
    /// The genuine Rust post-ledger (a clone). Its `.root()` is computed lazily during the audit, so
    /// the expensive canonical commitment never lands on the live hot path.
    Ledger(Box<Ledger>),
    /// A caller-FORCED root (fault injection) — what a BUGGY Rust executor would have claimed.
    ForcedRoot([u8; 32]),
}

impl SpeculatedPost {
    /// Resolve to the speculated root (computing the Rust post-ledger's canonical commitment here,
    /// OFF the live path). For a forced root this is a no-op return.
    fn root(self) -> [u8; 32] {
        match self {
            SpeculatedPost::Ledger(mut l) => l.root(),
            SpeculatedPost::ForcedRoot(r) => r,
        }
    }
}

/// A surfaced verified-vs-speculated divergence: the verified Lean executor's replay did NOT
/// reproduce the Rust executor's speculated outcome. The Lean result is AUTHORITATIVE — this means
/// the RUST executor has a bug on this turn. (Live state is not rolled back here; retirement is a
/// later layer — see the module note.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DivergenceReport {
    /// The index of the diverging turn in the live stream.
    pub turn_index: u64,
    /// The speculated (Rust) commit bit.
    pub rust_committed: bool,
    /// The authoritative (verified Lean) commit bit.
    pub lean_committed: bool,
    /// The speculated (Rust) post-state root.
    pub rust_root: [u8; 32],
    /// The authoritative (verified Lean) post-state root.
    pub lean_root: [u8; 32],
    /// Which axis diverged.
    pub kind: DivergenceKind,
}

/// The axis on which the verified replay disagreed with the Rust speculation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivergenceKind {
    /// The commit bits disagreed (e.g. Rust committed, the verified kernel rejected) — possibly
    /// also a root difference, but the commit bit is the headline.
    CommitBit,
    /// Both committed (or both rejected) but the post-state roots differ.
    Root,
}

/// The per-turn audit verdict the worker produces when it drains an [`AuditEntry`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuditOutcome {
    /// The verified replay AGREED with the Rust speculation (commit bit AND root). The turn retires
    /// clean.
    Agreed { turn_index: u64 },
    /// The verified replay DIVERGED — a surfaced Rust bug (see [`DivergenceReport`]).
    Diverged(DivergenceReport),
    /// The turn was OUTSIDE the covered set (not marshallable, or a characterized root-gap effect):
    /// the verified producer could not run, so there is nothing to compare. Surfaced with the
    /// precise reason — NEVER silently counted as agreement.
    Skipped {
        turn_index: u64,
        reason: ExtractError,
    },
}

/// A callback invoked for every divergence the audit catches (in addition to the `tracing::error!`).
/// `Send + Sync` so it can fire from the background audit thread.
pub type DivergenceSink = Arc<dyn Fn(&DivergenceReport) + Send + Sync>;

/// THE SPECULATIVE-AUDIT HARNESS.
///
/// Holds the live (fast) Rust [`TurnExecutor`] and an audit queue. [`execute_live`](Self::execute_live)
/// runs the Rust executor and returns immediately (enqueuing the turn for audit); the audit drains
/// OFF the live path — either pumped by the caller ([`drain_audit`](Self::drain_audit) /
/// [`drain_all`](Self::drain_all)) or by a spawned background thread
/// ([`spawn_worker`](Self::spawn_worker)).
///
/// The queue is an `Arc<Mutex<VecDeque<…>>>` so the harness can hand a clone to a background worker
/// and keep enqueuing from the live thread concurrently.
pub struct SpeculativeAudit {
    /// The fast Rust executor — the LIVE (speculative) path the desktop already takes.
    executor: TurnExecutor,
    /// The audit queue (shared with any spawned worker).
    queue: Arc<Mutex<VecDeque<AuditEntry>>>,
    /// Monotonic live-turn counter (the `turn_index` stamped on each entry / report).
    next_index: u64,
    /// Optional divergence sink — fired (in addition to `tracing::error!`) on every caught
    /// divergence, from whichever thread runs the audit.
    sink: Option<DivergenceSink>,
}

impl SpeculativeAudit {
    /// Build a harness around a fast Rust [`TurnExecutor`].
    pub fn new(executor: TurnExecutor) -> Self {
        Self {
            executor,
            queue: Arc::new(Mutex::new(VecDeque::new())),
            next_index: 0,
            sink: None,
        }
    }

    /// Install a divergence sink (a callback fired on every caught divergence). Use this to surface
    /// the report to the UI / a settlement layer / a test latch.
    pub fn with_divergence_sink(mut self, sink: DivergenceSink) -> Self {
        self.sink = Some(sink);
        self
    }

    /// THE FAST PATH. Run the Rust executor LIVE against `ledger` (mutating it in place to the Rust
    /// post-state) and return its [`TurnResult`] IMMEDIATELY — the ~0.5µs path the desktop takes.
    ///
    /// As a side effect it captures the pre-state (a clone, taken BEFORE the Rust mutation), the host
    /// admission ctx, and the Rust post-root, and enqueues an [`AuditEntry`] for the verified replay
    /// to audit OFF this path. The audit does NOT run here.
    ///
    /// Returns the live `TurnResult`. The user sees the (speculative) Rust outcome.
    pub fn execute_live(&mut self, turn: &Turn, ledger: &mut Ledger) -> TurnResult {
        // Capture the pre-state + host ctx BEFORE the Rust executor mutates the ledger — the verified
        // replay must run against EXACTLY this pre-state with the SAME admission context.
        let pre_ledger = ledger.clone();
        let host = self.executor.build_shadow_host_ctx(turn, ledger);

        // THE SPECULATION: run the fast Rust executor in place. This is the ~0.5µs hot-path cost.
        let result = self.executor.execute(turn, ledger);
        let rust_committed = result.is_committed();

        // Snapshot the Rust POST-state for the audit. We clone the post-ledger but DEFER its
        // `.root()` (the expensive canonical Poseidon commitment) to the audit worker — the desktop
        // hot path does not compute the root per interaction, so neither do we.
        let rust_post = SpeculatedPost::Ledger(Box::new(ledger.clone()));

        // Enqueue for the OFF-PATH verified audit.
        let turn_index = self.next_index;
        self.next_index += 1;
        let entry = AuditEntry {
            turn_index,
            turn: turn.clone(),
            pre_ledger,
            host,
            rust_committed,
            rust_post,
        };
        if let Ok(mut q) = self.queue.lock() {
            q.push_back(entry);
        }

        result
    }

    /// FAULT-INJECTION (test/demo only). Like [`execute_live`](Self::execute_live) but records a
    /// CALLER-SUPPLIED `forced_rust_root` as the speculated root instead of the genuine Rust root.
    /// This simulates a buggy Rust executor that produced the wrong post-state, so the audit MUST
    /// catch the divergence. The live `ledger` is still mutated by the genuine Rust executor (we only
    /// poison the RECORDED root the audit compares against).
    pub fn execute_live_with_forced_root(
        &mut self,
        turn: &Turn,
        ledger: &mut Ledger,
        forced_rust_root: [u8; 32],
    ) -> TurnResult {
        let pre_ledger = ledger.clone();
        let host = self.executor.build_shadow_host_ctx(turn, ledger);
        let result = self.executor.execute(turn, ledger);
        let rust_committed = result.is_committed();

        let turn_index = self.next_index;
        self.next_index += 1;
        let entry = AuditEntry {
            turn_index,
            turn: turn.clone(),
            pre_ledger,
            host,
            rust_committed,
            // The POISONED root — what a buggy Rust executor would have claimed.
            rust_post: SpeculatedPost::ForcedRoot(forced_rust_root),
        };
        if let Ok(mut q) = self.queue.lock() {
            q.push_back(entry);
        }
        result
    }

    /// How many turns are queued awaiting audit.
    pub fn pending(&self) -> usize {
        self.queue.lock().map(|q| q.len()).unwrap_or(0)
    }

    /// A clonable handle to the audit queue + sink — hand it to a background worker thread.
    pub fn worker_handle(&self) -> AuditWorker {
        AuditWorker {
            queue: Arc::clone(&self.queue),
            sink: self.sink.clone(),
        }
    }

    /// PUMP ONE: drain a single queued entry and audit it (verified replay + differential). Returns
    /// `None` when the queue is empty. OFF the live path — call it from a batched pump or a worker
    /// loop. Does NOT hardcode a retirement policy — it just produces the verdict.
    pub fn drain_audit(&self) -> Option<AuditOutcome> {
        self.worker_handle().drain_one()
    }

    /// PUMP ALL: drain and audit every queued entry, returning the verdicts in order. OFF the live
    /// path. Returns immediately if the queue is empty.
    pub fn drain_all(&self) -> Vec<AuditOutcome> {
        self.worker_handle().drain_all()
    }

    /// Spawn an EAGER BACKGROUND WORKER thread that drains + audits the queue until told to stop.
    /// Returns a [`WorkerStop`] handle; drop it or call [`WorkerStop::stop`] to halt the thread (it
    /// finishes draining the queue first). The retirement-policy layer would wire the verdicts this
    /// produces into settlement; here the worker just runs the audit and fires the divergence sink.
    pub fn spawn_worker(&self) -> WorkerStop {
        let worker = self.worker_handle();
        let stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let stop_thread = Arc::clone(&stop);
        let handle = std::thread::spawn(move || {
            loop {
                // Drain everything available, then back off briefly. When stop is signalled, do a
                // final drain and exit (don't leave audited turns unverified).
                let _ = worker.drain_all();
                if stop_thread.load(std::sync::atomic::Ordering::Relaxed) {
                    let _ = worker.drain_all();
                    break;
                }
                std::thread::sleep(std::time::Duration::from_micros(200));
            }
        });
        WorkerStop {
            stop,
            handle: Some(handle),
        }
    }
}

/// A clonable audit worker: the queue + the divergence sink. The actual verified-replay differential
/// lives here so it can run on either the calling thread (a pump) or a spawned background thread.
#[derive(Clone)]
pub struct AuditWorker {
    queue: Arc<Mutex<VecDeque<AuditEntry>>>,
    sink: Option<DivergenceSink>,
}

impl AuditWorker {
    /// Drain + audit one entry. `None` when empty.
    pub fn drain_one(&self) -> Option<AuditOutcome> {
        let entry = self.queue.lock().ok()?.pop_front()?;
        Some(self.audit(entry))
    }

    /// Drain + audit every queued entry (in FIFO order).
    pub fn drain_all(&self) -> Vec<AuditOutcome> {
        let mut out = Vec::new();
        while let Some(o) = self.drain_one() {
            out.push(o);
        }
        out
    }

    /// THE DIFFERENTIAL (promoted to a runtime audit). Replay one speculated turn through the
    /// verified Lean executor against its captured pre-state, then compare the verified outcome to
    /// the speculated (Rust) one. The verified result is AUTHORITATIVE — a mismatch is a surfaced
    /// Rust bug.
    fn audit(&self, entry: AuditEntry) -> AuditOutcome {
        let AuditEntry {
            turn_index,
            turn,
            pre_ledger,
            host,
            rust_committed,
            rust_post,
        } = entry;

        // Resolve the speculated Rust post-root HERE (off the live path): the canonical Poseidon
        // commitment of the Rust post-ledger, or the caller-forced root (fault injection).
        let rust_root = rust_post.root();

        // Drive the verified Lean executor against the SAME pre-state + host ctx the Rust executor
        // used, reconstituting its authoritative post-state.
        let (mut lean_ledger, lean_committed) =
            match lean_apply::execute_via_lean(&turn, &pre_ledger, &host) {
                Ok(pair) => pair,
                // OUTSIDE the covered set (not marshallable, or a characterized root-gap effect): the
                // verified producer cannot run, so there is nothing to compare. Surface the precise
                // reason — never silently call it agreement.
                Err(reason) => {
                    return AuditOutcome::Skipped { turn_index, reason };
                }
            };
        let lean_root = lean_ledger.root();

        // THE COMPARISON: commit bit first (the headline), then the post-state root.
        if lean_committed != rust_committed {
            let report = DivergenceReport {
                turn_index,
                rust_committed,
                lean_committed,
                rust_root,
                lean_root,
                kind: DivergenceKind::CommitBit,
            };
            self.signal(&report);
            return AuditOutcome::Diverged(report);
        }
        if lean_root != rust_root {
            let report = DivergenceReport {
                turn_index,
                rust_committed,
                lean_committed,
                rust_root,
                lean_root,
                kind: DivergenceKind::Root,
            };
            self.signal(&report);
            return AuditOutcome::Diverged(report);
        }

        AuditOutcome::Agreed { turn_index }
    }

    /// Surface a divergence — `tracing::error!` plus the optional sink. The Lean result is
    /// authoritative; this report means the Rust executor has a bug. Does NOT panic the live path.
    fn signal(&self, report: &DivergenceReport) {
        tracing::error!(
            target: "dregg::spec_audit::divergence",
            turn_index = report.turn_index,
            kind = ?report.kind,
            rust_committed = report.rust_committed,
            lean_committed = report.lean_committed,
            rust_root = ?report.rust_root,
            lean_root = ?report.lean_root,
            "SPECULATIVE-AUDIT DIVERGENCE: the verified Lean executor did not reproduce the Rust \
             speculation — the verified result is AUTHORITATIVE, so the Rust executor has a bug on \
             this turn",
        );
        if let Some(sink) = &self.sink {
            sink(report);
        }
    }
}

/// A handle to a spawned background audit worker. Dropping it (or calling [`stop`](Self::stop))
/// signals the thread to finish draining and exit, then joins it.
pub struct WorkerStop {
    stop: Arc<std::sync::atomic::AtomicBool>,
    handle: Option<std::thread::JoinHandle<()>>,
}

impl WorkerStop {
    /// Signal the worker to stop (after a final drain) and join it.
    pub fn stop(mut self) {
        self.stop_and_join();
    }

    fn stop_and_join(&mut self) {
        self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(h) = self.handle.take() {
            let _ = h.join();
        }
    }
}

impl Drop for WorkerStop {
    fn drop(&mut self) {
        self.stop_and_join();
    }
}
