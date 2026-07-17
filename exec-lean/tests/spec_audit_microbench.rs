//! spec_audit_microbench.rs — isolate WHERE the per-turn cost lives (no Lean needed).
//!
//! The speculative-audit demo measured ~700ms/turn for BOTH the bare Rust `execute` and the verified
//! audit on a 64-sender stream. This pins whether that is the Rust executor proper, its internal
//! `ledger.root()` (the canonical commitment), or the per-turn ledger clone — so the report is honest
//! about what the "live path" actually costs on this workload.
//!
//! Run with `--nocapture` to see the breakdown. This is a measurement aid, not a correctness gate.

use std::collections::HashMap;
use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
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

fn cell(seed0: u8, seed1: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed0;
    pk[1] = seed1;
    pk[31] = 0xC0;
    let mut c = Cell::with_balance(pk, [0u8; 32], balance);
    c.permissions = open_permissions();
    c
}

fn transfer_turn(from: CellId, to: CellId) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: from,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from,
            to,
            amount: 1,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent: from,
        nonce: 0,
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

#[test]
fn microbench_where_the_cost_lives() {
    const N: u64 = 64;
    // N distinct senders + recipient.
    let mut ledger = Ledger::new();
    let recip = cell(0xFF, 0xFF, 5);
    let recip_id = recip.id();
    ledger.insert_cell(recip).unwrap();
    let mut senders = Vec::new();
    for i in 0..N {
        let c = cell((i & 0xff) as u8, (i >> 8) as u8, 1_000);
        senders.push(c.id());
        ledger.insert_cell(c).unwrap();
    }
    let turns: Vec<Turn> = senders
        .iter()
        .map(|&s| transfer_turn(s, recip_id))
        .collect();

    let exec = TurnExecutor::new(ComputronCosts::zero());

    // (1) full execute stream (matches the demo's bare baseline).
    let mut l1 = ledger.clone();
    let t = Instant::now();
    for turn in &turns {
        let _ = exec.execute(turn, &mut l1);
    }
    let full_us = t.elapsed().as_secs_f64() * 1e6 / N as f64;

    // (2) just `ledger.root()` repeated N times on the growing ledger (no execute) — isolates the
    // canonical-commitment materialization cost.
    let mut l2 = ledger.clone();
    // WARM the ledger once outside the timed loop: the first `root()` is a
    // STRUCTURAL rebuild that cold-folds every cell's cap sub-root (filling the
    // per-cell sub-root cache, `.docs-history-noclaude/INCREMENTAL-COMMITMENT.md` step 2). Timing
    // it would amortize that one-time cold rebuild across the loop and hide the
    // STEADY-STATE per-turn cost (a single incremental dirty-leaf re-hash that
    // reuses the cached cap-root). The steady-state number is the one the doc's
    // "O(changed) per turn" claim is about.
    let _ = l2.root();
    let t = Instant::now();
    for _ in 0..N {
        // dirty one leaf so materialize actually recomputes (root caches when clean).
        let any = senders[0];
        if let Some(c) = l2.get_mut(&any) {
            c.state.set_nonce(c.state.nonce() + 1);
        }
        let _ = l2.root();
    }
    let root_us = t.elapsed().as_secs_f64() * 1e6 / N as f64;

    // (3) just the per-turn ledger clone (the audit snapshot cost).
    let t = Instant::now();
    let mut sink = 0usize;
    for _ in 0..N {
        let c = ledger.clone();
        sink = sink.wrapping_add(c.len());
    }
    let clone_us = t.elapsed().as_secs_f64() * 1e6 / N as f64;
    std::hint::black_box(sink);

    eprintln!(
        "=== spec-audit microbench (N={N}, ledger={} cells) ===",
        ledger.len()
    );
    eprintln!("(1) full Rust execute (incl. internal root()): {full_us:.3} µs/turn");
    eprintln!("(2) ledger.root() materialize alone:           {root_us:.3} µs/turn");
    eprintln!("(3) ledger.clone() (the audit snapshot):       {clone_us:.3} µs/turn");
    eprintln!(
        "    => execute-minus-root (the turn proper):   {:.3} µs/turn",
        (full_us - root_us).max(0.0)
    );
}

/// SUB-COMPONENT split of `post_root` (the dominant ~6µs steady-state phase): how much of a
/// touched-cell re-commit is the per-cell BLAKE3 canonical-commitment absorption (`hash_cell`)
/// vs the in-`CellState` `system_roots_digest()` recompute vs the rest. Measurement-only.
#[test]
fn microbench_hash_cell_subcomponents() {
    use dregg_cell::commitment::compute_canonical_state_commitment;
    const N: u64 = 200_000;
    let c = cell(0x01, 0x02, 1_000);

    // (a) full canonical commitment (what `Ledger::hash_cell` calls per touched leaf).
    let t = Instant::now();
    let mut acc = [0u8; 32];
    for _ in 0..N {
        acc = compute_canonical_state_commitment(&c);
        std::hint::black_box(&acc);
    }
    let full_ns = t.elapsed().as_nanos() as f64 / N as f64;

    // (b) just the system_roots_digest recompute (a BLAKE3 derive-key sponge over 8 roots),
    // which `hash_cell_state_into` calls on EVERY commitment.
    let t = Instant::now();
    let mut d = [0u8; 32];
    for _ in 0..N {
        d = c.state.system_roots_digest();
        std::hint::black_box(&d);
    }
    let srd_ns = t.elapsed().as_nanos() as f64 / N as f64;

    // (c) just one BLAKE3 64-byte parent hash (the Merkle-path inner-node cost per level).
    let t = Instant::now();
    let mut p = [0u8; 32];
    for _ in 0..N {
        let mut h = blake3::Hasher::new();
        h.update(&[0u8; 32]);
        h.update(&[1u8; 32]);
        p = *h.finalize().as_bytes();
        std::hint::black_box(&p);
    }
    let parent_ns = t.elapsed().as_nanos() as f64 / N as f64;

    // (d) BLAKE3 new_derive_key context-derivation overhead alone (the per-hash fixed cost
    // both the canonical commitment and system_roots_digest pay).
    let t = Instant::now();
    let mut k = [0u8; 32];
    for _ in 0..N {
        let h =
            blake3::Hasher::new_derive_key(dregg_cell::commitment::CANONICAL_COMMITMENT_CONTEXT);
        k = *h.finalize().as_bytes();
        std::hint::black_box(&k);
    }
    let dk_ns = t.elapsed().as_nanos() as f64 / N as f64;

    // (e) the SAME context but with a precomputed keyed hasher (clone the keyed state) —
    // models caching the derived key once and cloning per call.
    static KEYED: std::sync::OnceLock<blake3::Hasher> = std::sync::OnceLock::new();
    let base = KEYED.get_or_init(|| {
        blake3::Hasher::new_derive_key(dregg_cell::commitment::CANONICAL_COMMITMENT_CONTEXT)
    });
    let t = Instant::now();
    let mut k2 = [0u8; 32];
    for _ in 0..N {
        let h = base.clone();
        k2 = *h.finalize().as_bytes();
        std::hint::black_box(&k2);
    }
    let dkclone_ns = t.elapsed().as_nanos() as f64 / N as f64;

    eprintln!("=== hash_cell sub-components (ns/call) ===");
    eprintln!("(a) compute_canonical_state_commitment (full leaf): {full_ns:.1} ns");
    eprintln!("(b)   of which system_roots_digest() recompute:     {srd_ns:.1} ns");
    eprintln!("(c) one Merkle-path parent BLAKE3 (64B):            {parent_ns:.1} ns");
    eprintln!("(d) new_derive_key + finalize (empty) overhead:     {dk_ns:.1} ns");
    eprintln!("(e) clone(precomputed keyed) + finalize (empty):    {dkclone_ns:.1} ns");
}

/// PROFILE the ~89µs turn-proper across phases (env-gated `DREGG_TURN_PROFILE` fences in
/// `executor/{execute,execute_tree}.rs`). Same workload as the microbench: a populated 65-cell
/// ledger, one-Transfer turns. Reports µs/turn per phase + the forest inner breakdown. Off the
/// hot path; the env var is set only for this test's window.
#[test]
fn microbench_turn_proper_phase_profile() {
    // EXACTLY the microbench (1) workload: N distinct senders, each runs ONE transfer (nonce 0)
    // against the SAME growing ledger — so the per-turn dirty-leaf set + root() behaviour matches.
    const N: u64 = 64;
    let mut ledger = Ledger::new();
    let recip = cell(0xFF, 0xFF, 5);
    let recip_id = recip.id();
    ledger.insert_cell(recip).unwrap();
    let mut senders = Vec::new();
    for i in 0..N {
        let c = cell((i & 0xff) as u8, (i >> 8) as u8, 1_000);
        senders.push(c.id());
        ledger.insert_cell(c).unwrap();
    }
    let turns: Vec<Turn> = senders
        .iter()
        .map(|&s| transfer_turn(s, recip_id))
        .collect();
    let exec = TurnExecutor::new(ComputronCosts::zero());

    // SAFETY: single-threaded test; set the gate around this window only. The cached `enabled()`
    // latch reads the env on its FIRST call, which is the first `execute` below — so set it first.
    unsafe {
        std::env::set_var("DREGG_TURN_PROFILE", "1");
    }
    let mut l1 = ledger.clone();
    let mut last_receipt: std::collections::HashMap<CellId, [u8; 32]> =
        std::collections::HashMap::new();
    let t = Instant::now();
    for (turn, &s) in turns.iter().zip(senders.iter()) {
        if let dregg_turn::TurnResult::Committed { receipt, .. } = exec.execute(turn, &mut l1) {
            last_receipt.insert(s, receipt.receipt_hash());
        }
    }
    let full_us = t.elapsed().as_secs_f64() * 1e6 / N as f64;
    unsafe {
        std::env::remove_var("DREGG_TURN_PROFILE");
    }
    eprintln!(
        "\n=== turn-proper phase profile (mirrors microbench (1): N={N}, growing ledger) ==="
    );
    eprintln!("full execute (timed, incl both root() calls): {full_us:.3} µs/turn");
    dregg_turn::executor::turn_profile_dump("cold-first-root");

    // STEADY STATE: the tree is now materialized (round 1 paid the cold full rebuild). Run a SECOND
    // round of N turns on the SAME ledger (nonces now 1) — each touches only 2-3 leaves, so pre_root
    // is the cheap incremental `update_leaf` (O(log N)), NOT the cold fold. This isolates the genuine
    // per-turn floor. (`enabled()` is a process-latched OnceLock — already true from round 1.)
    let round2: Vec<Turn> = senders
        .iter()
        .map(|&s| {
            let mut t = transfer_turn(s, recip_id);
            t.nonce = 1;
            t.previous_receipt_hash = last_receipt.get(&s).copied();
            t
        })
        .collect();
    let t = Instant::now();
    for turn in &round2 {
        let r = exec.execute(turn, &mut l1);
        assert!(r.is_committed(), "round 2 turn must commit (steady-state)");
    }
    let r2_us = t.elapsed().as_secs_f64() * 1e6 / N as f64;
    eprintln!("\n=== STEADY-STATE round 2 (cold fold already paid): {r2_us:.3} µs/turn ===");
    dregg_turn::executor::turn_profile_dump("steady-state");
}
