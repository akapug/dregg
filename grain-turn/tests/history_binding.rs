//! # The per-grain CommitBindsMMR weld — committed state PINS witnessed history.
//!
//! Before this weld the grain's receipt chain was tamper-evident-given-a-trusted-root:
//! the chain hashes linked, but NOTHING the substrate commits bound WHICH chain is the
//! grain's history — "a claim, not a proof". These tests drive REAL committed kernel
//! turns through the R2 minter and check the three teeth of the binding:
//!
//! 1. **Honest path** — every committed post-state carries, at
//!    [`HISTORY_ROOT_SLOT`], exactly the MMR root over the grain's receipt chain
//!    strictly before that turn, [`verify_grain_history`] answers `Bound`, and the
//!    binding RIDES the canonical state commitment (the very bytes
//!    `Ledger::hash_cell` folds into the ledger root that `post_state_hash`,
//!    finalization votes, and owner checkpoints sign).
//! 2. **Equivocation tooth** — a DIVERGENT receipt chain presented for the same
//!    committed state is refused (`Divergent`, carrying both roots as evidence);
//!    a wrong-length chain is refused (`LengthMismatch`).
//! 3. **Absent-root compat** — a cell that predates the binding answers the TYPED
//!    lower rung (`Unbound`), never a fake "bound empty history" (the empty-log
//!    root is the nonzero domain-tagged constant, distinct from the zero slot).

use dregg_agent::agent::GrainTurnMinter;
use grain_turn::{
    GrainHistoryVerdict, HISTORY_ROOT_SLOT, ToolGatewayMinter, grain_history_root,
    verify_grain_history,
};

/// Drive `n` REAL committed grain turns (each a genuine executor turn on the
/// worker cell — over-rate turns would be refused host-side).
fn mint_n(minter: &mut ToolGatewayMinter, n: usize) {
    for i in 0..n {
        minter
            .mint_turn(&format!("act-{i}"), 1, (i + 1) as i64, [i as u8 + 1; 32])
            .expect("in-budget grain turn lands");
    }
}

#[test]
fn committed_state_binds_the_prior_receipt_chain() {
    let mut m = ToolGatewayMinter::open("history-binding-honest", 8).expect("admit grain");
    mint_n(&mut m, 3);

    let log = m.receipt_log().to_vec();
    assert_eq!(log.len(), 3, "one receipt digest per committed turn");

    // Every committed post-state binds EXACTLY the prefix of the chain before its
    // turn: turn k's after-cell carries root(receipts 0..k).
    for (k, rec) in m.records().iter().enumerate() {
        assert_eq!(
            rec.after_cell.state.fields[HISTORY_ROOT_SLOT],
            grain_history_root(&log[..k]),
            "turn {k}'s committed post-state binds the receipt chain strictly before it"
        );
    }

    // Even the FIRST turn binds a NONZERO value (the domain-tagged empty root) —
    // "bound empty history" is distinguishable from "no binding" (zero default).
    let first = &m.records()[0].after_cell;
    assert_eq!(
        first.state.fields[HISTORY_ROOT_SLOT],
        grain_history_root(&[])
    );
    assert_ne!(
        first.state.fields[HISTORY_ROOT_SLOT], [0u8; 32],
        "the empty-log root must be nonzero, or Unbound and bound-empty collapse"
    );

    // The light-client check over the REAL committed cell (straight off the ledger).
    let cell = m.committed_worker_cell().expect("worker cell committed");
    assert_eq!(
        verify_grain_history(&cell, &log),
        GrainHistoryVerdict::Bound,
        "the genuine history verifies against the committed state"
    );

    // THE CONSENSUS RIDE: the slot is folded by the canonical state commitment —
    // the same bytes `Ledger::hash_cell` Merkle-folds into the ledger root that
    // post_state_hash / finalization votes / owner checkpoints sign. Moving the
    // bound root MUST move the commitment.
    let honest = dregg_cell::commitment::compute_canonical_state_commitment(&cell);
    let mut tampered = cell.clone();
    tampered.state.fields[HISTORY_ROOT_SLOT] = [0xEE; 32];
    assert_ne!(
        honest,
        dregg_cell::commitment::compute_canonical_state_commitment(&tampered),
        "the history binding must ride the canonical state commitment"
    );
}

#[test]
fn a_divergent_receipt_chain_for_the_same_committed_state_is_refused() {
    let mut m = ToolGatewayMinter::open("history-binding-equivocation", 8).expect("admit grain");
    mint_n(&mut m, 3);
    let cell = m.committed_worker_cell().expect("worker cell committed");
    let log = m.receipt_log().to_vec();

    // The operator presents a DIVERGENT chain: same length, different interior
    // receipt. The committed state binds ONE root; the divergent prefix's root
    // disagrees — refused, with both roots as evidence.
    let mut forged = log.clone();
    forged[1] = [0xAB; 32];
    match verify_grain_history(&cell, &forged) {
        GrainHistoryVerdict::Divergent {
            committed,
            recomputed,
        } => {
            assert_eq!(committed, cell.state.fields[HISTORY_ROOT_SLOT]);
            assert_eq!(recomputed, grain_history_root(&forged[..2]));
            assert_ne!(committed, recomputed);
        }
        v => panic!("a divergent interior receipt must be refused, got {v:?}"),
    }

    // Substituting the FIRST receipt (a wholesale different history) is refused too.
    let mut other_history = log.clone();
    other_history[0] = [0xCD; 32];
    assert!(
        matches!(
            verify_grain_history(&cell, &other_history),
            GrainHistoryVerdict::Divergent { .. }
        ),
        "a wholesale different history for the same committed state must be refused"
    );

    // A truncated chain (operator hides a turn) is refused by the committed
    // `calls_made` counter before any hashing.
    assert_eq!(
        verify_grain_history(&cell, &log[..2]),
        GrainHistoryVerdict::LengthMismatch {
            calls_made: 3,
            presented: 2
        },
        "a truncated chain disagrees with the committed turn counter"
    );

    // HONEST BOUNDARY — the FRONTIER receipt (the latest turn's own) is NOT yet
    // pinned by this committed state (it absorbs post_state_hash, so binding it
    // here would be circular). It is pinned by its own post_state_hash binding +
    // the executor signature, and by the NEXT turn's state once one lands. A
    // frontier substitution therefore still verifies `Bound` here — document the
    // rung honestly rather than pretend otherwise.
    let mut frontier_forged = log.clone();
    frontier_forged[2] = [0xEF; 32];
    assert_eq!(
        verify_grain_history(&cell, &frontier_forged),
        GrainHistoryVerdict::Bound,
        "the frontier receipt is the R2 signature's territory, not this binding's"
    );

    // ...and one more committed turn moves the frontier INTO the binding: the same
    // forged receipt-2 is now refused.
    mint_n(&mut m, 1);
    let cell4 = m.committed_worker_cell().expect("worker cell committed");
    let mut frontier_forged4 = m.receipt_log().to_vec();
    frontier_forged4[2] = [0xEF; 32];
    assert!(
        matches!(
            verify_grain_history(&cell4, &frontier_forged4),
            GrainHistoryVerdict::Divergent { .. }
        ),
        "the next committed turn pins the previous frontier receipt"
    );
}

#[test]
fn a_pre_binding_cell_answers_the_typed_lower_rung() {
    // A freshly admitted worker with NO committed turn carries the slot's zero
    // default — exactly what every grain cell minted before this weld looks like.
    let m = ToolGatewayMinter::open("history-binding-legacy", 4).expect("admit grain");
    let cell = m.committed_worker_cell().expect("worker cell admitted");
    assert_eq!(
        cell.state.fields[HISTORY_ROOT_SLOT], [0u8; 32],
        "no turn committed yet ⇒ the slot is at its zero default"
    );
    assert_eq!(
        verify_grain_history(&cell, &[]),
        GrainHistoryVerdict::Unbound,
        "absent root ⇒ the EXPLICIT lower rung, never a fake bound-empty claim"
    );
    // Presenting any nonempty chain against an unbound cell is still Unbound —
    // the verdict names the missing binding, it does not guess.
    assert_eq!(
        verify_grain_history(&cell, &[[7u8; 32]]),
        GrainHistoryVerdict::Unbound
    );
}
