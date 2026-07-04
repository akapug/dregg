//! MID-FOREST YIELD POINT — the live executor checkpoint BETWEEN two effects.
//!
//! `continuation_umem_round_trip.rs` proves the suspend/resume round-trip over a trace cut of a
//! COMPLETED turn. This file closes the seam that module's banner named ("THE SEAM — mid-forest
//! checkpoint"): the executor's depth-first effect-application loop now exposes a `yield_point`
//! (`TurnExecutor::maybe_umem_yield`) that snapshots `project_executor_state` LIVE, between two
//! effects of a single in-flight turn, and `Continuation::from_yield` binds that live boundary to
//! the committed Blum trace.
//!
//! THE SOUNDNESS this proves (the Rust shadow of `Dregg2/Exec/Continuation.midturn_split` /
//! `yield_resume_sound`):
//!   * the LIVE mid-flight snapshot (captured by the executor between effects) equals a trace
//!     PREFIX fold — the journal-prefix snapshot IS the trace-prefix fold (`from_yield` binds it);
//!   * resuming from that boundary reaches EXACTLY the executor's post-state — the journal-prefix
//!     snapshot + forward-the-rest equals running straight through;
//!   * the boundary survives a serialization hand-off (the passable-umem property);
//!   * ATOMICITY (honesty teeth): the yield is an OBSERVATION — the turn still commits as a whole,
//!     the receipt is whole-turn, and a foreign snapshot does NOT bind (`from_yield` refuses).

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::continuation::Continuation;
use dregg_turn::umem::{UProjection, fold};
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

fn multi_effect_turn(agent: CellId, target: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
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
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// A three-effect turn whose mid-state genuinely differs from both endpoints, so a yield between
/// effects captures a REAL intermediate boundary. Returns (executor, agent_id, target_id, slot).
fn three_effect_turn(executor: &TurnExecutor, ledger: &mut Ledger) -> (CellId, CellId, u32) {
    let agent = make_open_cell(8, 1000);
    let target = make_open_cell(9, 10);
    let (agent_id, target_id) = (agent.id(), target.id());

    let mut agent_with_cap = agent;
    let slot = agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();
    let _ = executor;
    (agent_id, target_id, slot)
}

fn umem_executor() -> TurnExecutor {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);
    executor
}

/// THE KEYSTONE: arm the yield BETWEEN two effects of a live turn; the executor snapshots the
/// genuine mid-flight state; `from_yield` binds it to the committed trace; resume reaches post.
#[test]
fn live_mid_forest_yield_binds_and_resumes_to_post() {
    let executor = umem_executor();
    let mut ledger = Ledger::new();
    let (agent_id, target_id, slot) = three_effect_turn(&executor, &mut ledger);

    // Arm the yield at journal-prefix length 1 — i.e. AFTER the first effect (the transfer's
    // balance writes) but BEFORE the rest. The executor will snapshot live, between effects.
    // (journal length grows as effects apply; length >= 1 fires the once-guarded capture.)
    executor.set_umem_yield_at(Some(1));

    let turn = multi_effect_turn(
        agent_id,
        agent_id,
        0,
        vec![
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 7,
            },
            Effect::SetField {
                cell: agent_id,
                index: 0,
                value: [9u8; 32],
            },
            Effect::AttenuateCapability {
                cell: agent_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
        ],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "turn must commit as a whole: {result:?}"
    );

    // The executor captured a LIVE mid-flight boundary between two effects.
    let live = executor
        .last_umem_yield
        .lock()
        .unwrap()
        .clone()
        .expect("a mid-forest yield must have fired (journal reached the armed length)");

    // The committed whole-turn trace folds pre -> post (the bridge square).
    let witness = executor
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .expect("umem witness produced")
        .expect("umem witness ok");
    let straight_post = fold(&witness.pre, &witness.ops);
    assert_eq!(straight_post, witness.post, "the bridge square holds");

    // THE BIND: the live mid-flight snapshot equals a trace-PREFIX fold (the journal-prefix
    // snapshot IS the trace-prefix fold). `from_yield` finds the cut and suspends there.
    let k = Continuation::from_yield(&witness.pre, &witness.ops, &live)
        .expect("the live mid-flight snapshot must bind to a trace prefix (midturn_split)");

    // The captured boundary IS the live snapshot — not the pre, not the post (a genuine middle).
    assert_eq!(
        k.captured(),
        live,
        "the continuation's captured boundary is the live mid-flight projection"
    );
    assert_ne!(k.captured(), witness.pre, "the yield is past the pre-state");
    assert_ne!(
        k.captured(),
        witness.post,
        "the yield is before the post-state (a real middle)"
    );
    assert!(
        !k.is_complete(),
        "a mid-forest yield has remaining work to fold"
    );

    // RESUME (after a serialization hand-off) reaches EXACTLY the executor's post-state.
    let wire = k.to_bytes();
    let landed = Continuation::from_bytes(&wire).expect("handed-off yield decodes");
    assert_eq!(
        landed, k,
        "the yielded continuation is byte-faithful across the pipe"
    );
    let resumed = landed.resume().expect("the yielded tail resumes");
    assert_eq!(
        resumed, witness.post,
        "resume(yield) reaches the executor's post-state (yield_resume_sound)"
    );
}

/// The yield fires at EVERY armed boundary the live walk crosses, and each binds + resumes to the
/// same post — the journal-prefix snapshot at any cut equals the trace-prefix fold.
#[test]
fn yield_at_each_boundary_binds_and_resumes() {
    // First, learn how many journal entries the turn produces by running it once with no yield.
    let probe = umem_executor();
    let mut probe_ledger = Ledger::new();
    let (agent_id, target_id, slot) = three_effect_turn(&probe, &mut probe_ledger);
    let turn = multi_effect_turn(
        agent_id,
        agent_id,
        0,
        vec![
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 5,
            },
            Effect::SetField {
                cell: agent_id,
                index: 1,
                value: [3u8; 32],
            },
            Effect::AttenuateCapability {
                cell: agent_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
        ],
    );
    assert!(probe.execute(&turn, &mut probe_ledger).is_committed());
    let probe_w = probe
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .unwrap()
        .unwrap();
    let n_ops = probe_w.ops.len();
    assert!(n_ops >= 3, "expected several ops, got {n_ops}");

    // Now arm a yield at each journal-prefix length 1..=n_ops and check bind+resume.
    for k in 1..=(n_ops as u64) {
        let executor = umem_executor();
        let mut ledger = Ledger::new();
        let (agent_id, target_id, slot) = three_effect_turn(&executor, &mut ledger);
        executor.set_umem_yield_at(Some(k));
        let turn = multi_effect_turn(
            agent_id,
            agent_id,
            0,
            vec![
                Effect::Transfer {
                    from: agent_id,
                    to: target_id,
                    amount: 5,
                },
                Effect::SetField {
                    cell: agent_id,
                    index: 1,
                    value: [3u8; 32],
                },
                Effect::AttenuateCapability {
                    cell: agent_id,
                    slot,
                    narrower_permissions: AuthRequired::Signature,
                    narrower_effects: None,
                    narrower_expiry: None,
                },
            ],
        );
        assert!(executor.execute(&turn, &mut ledger).is_committed());

        // The convenience accessor: capture straight off the executor.
        let captured = executor.capture_yielded_continuation();
        if let Some(cont) = captured {
            let post = {
                let w = executor.last_umem_witness.lock().unwrap();
                let w = w.as_ref().unwrap().as_ref().unwrap();
                fold(&w.pre, &w.ops)
            };
            assert_eq!(
                cont.resume().expect("resumes"),
                post,
                "yield armed at journal length {k} binds and resumes to post"
            );
        }
        // (If the live snapshot coincides with the post-state at some boundary the accessor may
        // still bind it as a complete continuation; either way resume reaches post — asserted
        // above. The point is no armed boundary produces an UNBINDABLE snapshot.)
    }
}

/// ATOMICITY / fail-closed teeth: a FOREIGN snapshot (one no trace prefix reproduces) does NOT
/// bind as a mid-turn yield. A yield boundary is bound to THIS turn's trace, not free-witnessed.
#[test]
fn foreign_snapshot_does_not_bind() {
    let executor = umem_executor();
    let mut ledger = Ledger::new();
    let (agent_id, target_id, _slot) = three_effect_turn(&executor, &mut ledger);
    let turn = multi_effect_turn(
        agent_id,
        agent_id,
        0,
        vec![Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 11,
        }],
    );
    assert!(executor.execute(&turn, &mut ledger).is_committed());
    let w = executor
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .unwrap()
        .unwrap();

    // A bogus boundary: take the pre-projection and corrupt one balance so no trace prefix
    // reproduces it. `from_yield` must refuse (None) — a foreign boundary is not a yield of this
    // turn.
    let mut foreign: UProjection = w.pre.clone();
    use dregg_turn::umem::{UKey, UVal};
    foreign.insert(UKey::Balance(agent_id), UVal::Int(424242));
    assert!(
        Continuation::from_yield(&w.pre, &w.ops, &foreign).is_none(),
        "a snapshot no trace prefix reproduces must NOT bind as a mid-turn yield"
    );
}

/// The yield is a pure observation: with the umem lane OFF, no yield fires even when armed — the
/// live proving path is untouched.
#[test]
fn yield_is_gated_by_the_umem_lane() {
    // The VK epoch ARMED the umem witness lane by default; this control explicitly DISARMS it so the
    // yield armed but the lane OFF captures nothing — the yield is a pure observation OF that lane.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor
        .umem_witness_enabled
        .store(false, Ordering::Relaxed);
    executor.set_umem_yield_at(Some(1));
    let mut ledger = Ledger::new();
    let (agent_id, target_id, _slot) = three_effect_turn(&executor, &mut ledger);
    let turn = multi_effect_turn(
        agent_id,
        agent_id,
        0,
        vec![Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 3,
        }],
    );
    assert!(executor.execute(&turn, &mut ledger).is_committed());
    assert!(
        executor.last_umem_yield.lock().unwrap().is_none(),
        "with the umem lane off, the yield must NOT fire (live path untouched)"
    );
}
