//! speculative_audit.rs — THE SPECULATIVE-AUDIT execution-model demo + measurement.
//!
//! This proves the model `spec_audit::SpeculativeAudit` implements: the FAST Rust `TurnExecutor`
//! runs LIVE on the hot path (~Rust speed) and the VERIFIED Lean executor REPLAYS the turn history
//! OFF the hot path to AUDIT for divergence. The user gets fast; the verified executor catches any
//! Rust bug.
//!
//! Three things are demonstrated + measured:
//!   (a) the live path returns at ~Rust speed (NOT the ~15µs verified floor),
//!   (b) the audit drains and CONFIRMS agreement on all N turns (zero divergence),
//!   (c) FAULT INJECTION: feed the audit a deliberately-WRONG Rust post-root for one turn and show
//!       the audit CATCHES it (a `DivergenceReport` fires).
//!
//! Requires the linked Lean archive (`lean_available()`); when absent the test self-skips (it cannot
//! run the verified replay to compare).
//!
//! # Trust-model layer NOT decided here (flagged for ember)
//!
//! This harness is generic over WHEN the audit runs (here a caller-pumped `drain_all`; the harness
//! also offers `spawn_worker` for an eager background thread) and does NOT hardcode a
//! retirement/settlement policy. Open questions for ember, surfaced rather than guessed:
//!   * Does the user see SPECULATIVE (Rust) or AUDITED (Lean) state? (This demo shows the user the
//!     Rust state live; the audit confirms it later.)
//!   * What does "retirement" / "settlement" mean — a barrier the audit must clear before export /
//!     federation / a checkpoint? Right now the audit just produces a verdict.
//!   * On a caught divergence, what happens to turns that BUILT ON the diverged turn? (The verified
//!     replay here runs each turn against its OWN captured pre-state, so the audit is per-turn sound;
//!     but a real chain would need to re-derive the suffix from the authoritative state.)

use std::collections::HashMap;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
};
use std::time::Instant;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::spec_audit::{
    AuditOutcome, DivergenceKind, DivergenceReport, SpeculativeAudit,
};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A distinct-identity open cell keyed by a 16-bit index (so a stream of many senders never
/// collides). The whole pk is set from `idx`, since `Cell::public_key` is not test-writable.
fn make_indexed_cell(idx: u16, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = (idx & 0xff) as u8;
    pk[1] = (idx >> 8) as u8;
    pk[31] = 0xC0; // disjoint from `make_open_cell`'s pk[31] family
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// A ledger with N distinct sender cells (each nonce 0) plus one shared recipient B. Using a fresh
/// agent per turn keeps every turn a genesis turn (nonce 0, `previous_receipt_hash: None`) so the
/// receipt-chain gate admits the whole stream against ONE evolving ledger — exactly the streaming
/// shape the harness audits, without threading a per-agent receipt chain (a separate concern).
fn n_sender_ledger(n: u64) -> (Ledger, Vec<CellId>, CellId) {
    let mut ledger = Ledger::new();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    ledger.insert_cell(b).unwrap();
    let mut senders = Vec::with_capacity(n as usize);
    for i in 0..n {
        let cell = make_indexed_cell(i as u16, 1_000);
        let id = cell.id();
        ledger.insert_cell(cell).unwrap();
        senders.push(id);
    }
    (ledger, senders, b_id)
}

/// Build a deterministic stream of N covered (transfer / setfield) turns — one per distinct sender
/// (each a genesis turn, nonce 0). Even turns transfer 1 to B; odd turns set the sender's own slot 6.
fn turn_stream(senders: &[CellId], b_id: CellId) -> Vec<Turn> {
    senders
        .iter()
        .enumerate()
        .map(|(i, &s)| {
            if i % 2 == 0 {
                single_effect_turn(
                    s,
                    s,
                    0,
                    Effect::Transfer {
                        from: s,
                        to: b_id,
                        amount: 1,
                    },
                )
            } else {
                single_effect_turn(
                    s,
                    s,
                    0,
                    Effect::SetField {
                        cell: s,
                        index: 6,
                        value: field_from_u64(i as u64 + 1),
                    },
                )
            }
        })
        .collect()
}

/// (a) live path is fast + (b) audit drains and CONFIRMS agreement on all N (zero divergence).
#[test]
fn speculative_audit_confirms_agreement_and_measures() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }

    const N: u64 = 64;
    let (mut ledger, senders, b_id) = n_sender_ledger(N);
    let turns = turn_stream(&senders, b_id);

    // The divergence sink — a latch that MUST stay empty on the clean run.
    let divergences: Arc<Mutex<Vec<DivergenceReport>>> = Arc::new(Mutex::new(Vec::new()));
    let sink_div = Arc::clone(&divergences);
    let audit = SpeculativeAudit::new(TurnExecutor::new(ComputronCosts::zero()))
        .with_divergence_sink(Arc::new(move |r: &DivergenceReport| {
            sink_div.lock().unwrap().push(r.clone());
        }));
    let mut audit = audit;

    // BASELINE: the bare Rust `execute` cost (the SPECULATION proper) — what the desktop hot path
    // pays. Run on a throwaway ledger clone so the measured `audit` run below starts clean.
    {
        let mut bare = ledger.clone();
        let bare_exec = TurnExecutor::new(ComputronCosts::zero());
        let t = Instant::now();
        for turn in &turns {
            let _ = bare_exec.execute(turn, &mut bare);
        }
        let per = t.elapsed().as_secs_f64() * 1e6 / N as f64;
        eprintln!("BASELINE bare Rust execute (the speculation): {per:.3} µs/turn");
    }

    // (a) THE LIVE PATH — measure its latency. This must be ~Rust speed (~sub-µs), NOT the verified
    // ~15µs floor: the verified replay does not run here. The expensive canonical root commitment is
    // DEFERRED to the audit (off this path); the live cost is `execute` + the pre/post snapshot.
    let mut committed = 0u64;
    let t_live = Instant::now();
    for turn in &turns {
        let result = audit.execute_live(turn, &mut ledger);
        if result.is_committed() {
            committed += 1;
        }
    }
    let live_elapsed = t_live.elapsed();
    let live_per_turn_us = live_elapsed.as_secs_f64() * 1e6 / N as f64;

    assert_eq!(
        committed, N,
        "all {N} covered turns should commit on the live Rust path"
    );
    assert_eq!(
        audit.pending() as u64,
        N,
        "all {N} turns should be queued for audit"
    );

    // (b) THE AUDIT — drain OFF the live path, measure throughput. Every turn must AGREE.
    let t_audit = Instant::now();
    let outcomes = audit.drain_all();
    let audit_elapsed = t_audit.elapsed();
    let audit_per_turn_us = audit_elapsed.as_secs_f64() * 1e6 / N as f64;
    let audit_tps = N as f64 / audit_elapsed.as_secs_f64();

    assert_eq!(
        outcomes.len() as u64,
        N,
        "audit should produce one verdict per turn"
    );
    let mut agreed = 0u64;
    let mut skipped = 0u64;
    for o in &outcomes {
        match o {
            AuditOutcome::Agreed { .. } => agreed += 1,
            AuditOutcome::Skipped { turn_index, reason } => {
                skipped += 1;
                eprintln!("turn {turn_index} skipped (uncovered): {reason}");
            }
            AuditOutcome::Diverged(r) => {
                panic!("UNEXPECTED divergence on the clean run: {r:?}");
            }
        }
    }
    assert_eq!(
        agreed, N,
        "the verified audit must CONFIRM agreement on all {N} covered turns (skipped={skipped})"
    );
    assert!(
        divergences.lock().unwrap().is_empty(),
        "the divergence sink must stay empty on the clean run"
    );
    assert_eq!(audit.pending(), 0, "queue should be fully drained");

    eprintln!("=== SPECULATIVE-AUDIT measurement (N={N}) ===");
    eprintln!(
        "(a) LIVE path:  {live_per_turn_us:.3} µs/turn  (Rust speculate — the user's hot path: execute + a ~10µs pre/post snapshot clone; the canonical root() is DEFERRED off this path)"
    );
    eprintln!(
        "(b) AUDIT path: {audit_per_turn_us:.3} µs/turn  ({audit_tps:.0} turns/sec — verified Lean replay + root resolution, OFF the hot path)"
    );
    eprintln!("    confirmed agreement on {agreed}/{N} turns, zero divergence");
    // NOTE: on this synthetic 65-cell stream BOTH paths are dominated by `Ledger::root()` (the
    // canonical sorted-Poseidon2 cap-root over every cell — see spec_audit_microbench), NOT by the
    // executor logic or the Lean FFI. The harness's own live overhead is the ~10µs snapshot clone;
    // the expensive commitment is deferred to the audit. The relative numbers are workload-bound;
    // see the microbench for the decomposition.
    eprintln!(
        "    audit/live ratio on this workload: {:.2}x (both root()-bound; see spec_audit_microbench)",
        audit_per_turn_us / live_per_turn_us.max(1e-9)
    );
}

/// (c) FAULT INJECTION: a buggy Rust executor claims the WRONG post-root for one turn; the verified
/// audit MUST catch it (a `DivergenceReport` fires).
#[test]
fn speculative_audit_catches_injected_fault() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }

    // Three distinct senders (each a genesis turn, nonce 0) + recipient B.
    let (mut ledger, senders, b_id) = n_sender_ledger(3);
    let (s0, s1, s2) = (senders[0], senders[1], senders[2]);

    // Count divergences via the sink (it fires from the audit, exactly as a settlement layer would
    // observe it).
    let caught = Arc::new(AtomicUsize::new(0));
    let caught_sink = Arc::clone(&caught);
    let last_report: Arc<Mutex<Option<DivergenceReport>>> = Arc::new(Mutex::new(None));
    let last_sink = Arc::clone(&last_report);
    let mut audit = SpeculativeAudit::new(TurnExecutor::new(ComputronCosts::zero()))
        .with_divergence_sink(Arc::new(move |r: &DivergenceReport| {
            caught_sink.fetch_add(1, Ordering::Relaxed);
            *last_sink.lock().unwrap() = Some(r.clone());
        }));

    // Turn 0: a HONEST transfer (the audit should agree).
    let t0 = single_effect_turn(
        s0,
        s0,
        0,
        Effect::Transfer {
            from: s0,
            to: b_id,
            amount: 7,
        },
    );
    let r0 = audit.execute_live(&t0, &mut ledger);
    assert!(r0.is_committed(), "turn 0 should commit on the live path");

    // Turn 1: the SAME ledger evolves, but we POISON the recorded Rust post-root — simulating a buggy
    // Rust executor that produced the wrong state. The live ledger is still mutated honestly; only
    // the root the audit compares against is wrong.
    let t1 = single_effect_turn(
        s1,
        s1,
        0,
        Effect::Transfer {
            from: s1,
            to: b_id,
            amount: 3,
        },
    );
    let poisoned_root = [0xABu8; 32];
    let r1 = audit.execute_live_with_forced_root(&t1, &mut ledger, poisoned_root);
    assert!(
        r1.is_committed(),
        "turn 1 should commit on the live path (only the recorded root is poisoned)"
    );

    // Turn 2: another HONEST transfer (the audit should agree again — proving the catch is targeted,
    // not a blanket failure).
    let t2 = single_effect_turn(
        s2,
        s2,
        0,
        Effect::Transfer {
            from: s2,
            to: b_id,
            amount: 2,
        },
    );
    let r2 = audit.execute_live(&t2, &mut ledger);
    assert!(r2.is_committed(), "turn 2 should commit on the live path");

    // Drain + audit all three.
    let outcomes = audit.drain_all();
    assert_eq!(outcomes.len(), 3, "three turns audited");

    // Turn 0 and turn 2 agree; turn 1 DIVERGES on the root.
    assert!(
        matches!(outcomes[0], AuditOutcome::Agreed { turn_index: 0 }),
        "turn 0 (honest) should agree, got {:?}",
        outcomes[0]
    );
    match &outcomes[1] {
        AuditOutcome::Diverged(r) => {
            assert_eq!(r.turn_index, 1);
            assert_eq!(
                r.kind,
                DivergenceKind::Root,
                "the injected fault is a root mismatch"
            );
            assert_eq!(
                r.rust_root, poisoned_root,
                "the report carries the (poisoned) speculated root"
            );
            assert_ne!(
                r.lean_root, poisoned_root,
                "the verified root differs from the poison"
            );
        }
        other => panic!("turn 1 (poisoned) should DIVERGE, got {other:?}"),
    }
    assert!(
        matches!(outcomes[2], AuditOutcome::Agreed { turn_index: 2 }),
        "turn 2 (honest) should agree, got {:?}",
        outcomes[2]
    );

    // The sink fired exactly once (the one injected fault).
    assert_eq!(
        caught.load(Ordering::Relaxed),
        1,
        "the divergence sink should fire exactly once (the single injected fault)"
    );
    let report = last_report
        .lock()
        .unwrap()
        .clone()
        .expect("a report was captured");
    eprintln!("=== FAULT-INJECTION caught ===");
    eprintln!("{report:?}");
}

/// The background-worker variant: prove the eager `spawn_worker` thread drains + audits the queue
/// while the live thread keeps executing, with zero divergence on a clean stream.
#[test]
fn speculative_audit_background_worker_drains() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }

    const N: u64 = 32;
    let (mut ledger, senders, b_id) = n_sender_ledger(N);
    let turns = turn_stream(&senders, b_id);

    let divergences: Arc<Mutex<Vec<DivergenceReport>>> = Arc::new(Mutex::new(Vec::new()));
    let sink_div = Arc::clone(&divergences);
    let mut audit = SpeculativeAudit::new(TurnExecutor::new(ComputronCosts::zero()))
        .with_divergence_sink(Arc::new(move |r: &DivergenceReport| {
            sink_div.lock().unwrap().push(r.clone());
        }));

    // Spawn the eager background audit worker BEFORE the live stream — it drains concurrently.
    let worker = audit.spawn_worker();

    for turn in &turns {
        let result = audit.execute_live(turn, &mut ledger);
        assert!(result.is_committed());
    }

    // Stop the worker (final drain + join), then assert everything was audited clean.
    worker.stop();
    assert_eq!(
        audit.pending(),
        0,
        "the background worker should have drained the queue"
    );
    assert!(
        divergences.lock().unwrap().is_empty(),
        "zero divergence on the clean background-audited stream"
    );
}
