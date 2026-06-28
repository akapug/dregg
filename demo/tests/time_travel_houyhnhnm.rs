//! TIME-TRAVEL / undo — the Houyhnhnm pillar #3, made tangible on the REAL substrate.
//!
//! Branch-and-stitch (`starbridge-v2/src/branch_stitch_session.rs`) is the
//! *spatial* axis of dregg's event-structure config lattice: a turn forks a
//! confined world you drive and later stitch back. This demo exercises the
//! *temporal* axis of the SAME object — REWIND a live verified history to a past
//! state, BRANCH at that past point, and replay a DIFFERENT verified future.
//! Distributed/reversible computing made concrete, every step gated by the real
//! `TurnExecutor` and checked against the recorded root tooth.
//!
//! Everything here rides the production machinery in `turn/src/reversible.rs`:
//!
//!   * REWIND    — [`ReversibleHistory::replay_to`] (forward-from-genesis) AND
//!                 [`ReversibleHistory::undo_to`] (backward-from-head via the
//!                 `Turn::invert` un-turn). The demo shows the two roads land on
//!                 the SAME verified past state (modulo the monotone nonce).
//!   * BRANCH    — fork the past with the first-class
//!                 [`ReversibleHistory::fork_at`]: a new history whose committed
//!                 prefix `[0,k]` SHARES the parent's config-lattice down-set
//!                 (each prefix step is an `Arc`-handle clone — NOT re-executed),
//!                 landing on the original's `roots[k]` byte-identically. Then a
//!                 divergent turn writes a different future. This is the temporal
//!                 dual of branch-and-stitch's spatial `World::fork`.
//!   * GENUINE   — receipts are real (`record_commit` returns `Some(receipt)`),
//!                 conservation/authority hold (the real executor rejects
//!                 otherwise), the un-turn is an exact inverse on value/state
//!                 ([`ledgers_agree_modulo_nonce`]), and the irreversible
//!                 boundary fails closed (you cannot rewind past a settled commit).
//!
//! HONEST CHARACTER OF THE REVERSIBILITY (reported in the run, not papered over):
//!   * `undo_to` is an EXACT inverse on VALUE/STATE (balances, fields, caps) —
//!     `undo(do(s)) == s` — modulo the per-turn monotone nonce ratchet, the one
//!     deliberate island of irreversibility every committed turn carries
//!     (`FIRST-CLASS-REVERSIBILITY.md` §4.2). It is not replay-to-N approximation;
//!     it walks history backward applying real inverse turns through the executor.
//!   * BRANCHING is now first-class: [`ReversibleHistory::fork_at`] SHARES the
//!     recorded prefix as the event-structure config-lattice down-set (each
//!     prefix step is an `Arc`-handle clone of the parent's — no re-execution, no
//!     deep copy), landing on `roots[k]` byte-identically. The earlier demo
//!     SYNTHESIZED this by replaying the `steps()` prefix through the executor
//!     (faithful but re-executing); `fork_at` is the sound optimization that
//!     synthesis pointed at. See `fork_at_shares_the_downset_not_replay` at the
//!     bottom (the structural-sharing witness, `Arc::ptr_eq`).

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::TurnExecutor;
use dregg_turn::action::Effect;
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::reversible::{ReversibleHistory, ledgers_agree_modulo_nonce};
use dregg_turn::turn::Turn;

// ── fixtures (mirror turn/src/reversible.rs tests; the demo/test substrate) ──

/// An open cell (no auth required), so the `Unchecked` authorization an un-turn
/// and a bare demo turn carry is gated only by the open permissions.
fn open_cell(seed: u8, balance: i64) -> Cell {
    let pk = [seed; 32];
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

/// A bare unchecked turn authored by `agent` carrying `effects`.
fn turn_with(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut ab = ActionBuilder::new_unchecked_for_tests(agent, "act", agent);
    for e in effects {
        ab = ab.effect(e);
    }
    let mut tb = TurnBuilder::new(agent, nonce);
    tb.add_action(ab.build());
    tb.fee(0).build()
}

fn nonce_of(l: &Ledger, id: &CellId) -> u64 {
    l.get(id).map(|c| c.state.nonce()).unwrap_or(0)
}

fn balance_of(l: &Ledger, id: &CellId) -> i64 {
    l.get(id).map(|c| c.state.balance()).unwrap_or(0)
}

/// Build the flagship history: a tiny two-party ledger world that accrues a
/// chain of verified turns. Returns `(history, ledger, executor, alice, bob)`.
///
/// Steps (0-based `ReversibleStep` index):
///   idx 0,1 = genesis(alice=1000), genesis(bob=0)
///   idx 2   = t1: alice → bob 100   (clean transfer)
///   idx 3   = t2: alice → bob  50   (clean transfer)
///   idx 4   = t3: bob SetField[0]   (clean, a "memo" write)
///   idx 5   = t4: bob → alice 30    (clean transfer)
/// head = 6.
fn build_history() -> (ReversibleHistory, Ledger, TurnExecutor, CellId, CellId) {
    let mut h = ReversibleHistory::new(1_700_000_000);
    let mut l = Ledger::new();
    let ex = h.fresh_executor();

    let alice = h.record_genesis(&mut l, open_cell(0xA1, 1_000));
    let bob = h.record_genesis(&mut l, open_cell(0xB0, 0));

    let n = nonce_of(&l, &alice);
    assert!(
        h.record_commit(
            &ex,
            &mut l,
            turn_with(
                alice,
                n,
                vec![Effect::Transfer {
                    from: alice,
                    to: bob,
                    amount: 100
                }]
            ),
        )
        .is_some(),
        "t1 must commit"
    );
    let n = nonce_of(&l, &alice);
    assert!(
        h.record_commit(
            &ex,
            &mut l,
            turn_with(
                alice,
                n,
                vec![Effect::Transfer {
                    from: alice,
                    to: bob,
                    amount: 50
                }]
            ),
        )
        .is_some(),
        "t2 must commit"
    );
    let n = nonce_of(&l, &bob);
    assert!(
        h.record_commit(
            &ex,
            &mut l,
            turn_with(
                bob,
                n,
                vec![Effect::SetField {
                    cell: bob,
                    index: 0,
                    value: [7u8; 32]
                }]
            ),
        )
        .is_some(),
        "t3 must commit"
    );
    let n = nonce_of(&l, &bob);
    assert!(
        h.record_commit(
            &ex,
            &mut l,
            turn_with(
                bob,
                n,
                vec![Effect::Transfer {
                    from: bob,
                    to: alice,
                    amount: 30
                }]
            ),
        )
        .is_some(),
        "t4 must commit"
    );

    assert_eq!(h.len(), 6, "2 genesis + 4 turns");
    (h, l, ex, alice, bob)
}

// ════════════════════════════════════════════════════════════════════════════
// THE FLAGSHIP: rewind → branch-the-past → replay a divergent verified future.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn time_travel_rewind_branch_and_replay_a_divergent_verified_future() {
    let (h, live, _ex, alice, bob) = build_history();

    // The live (head) world after the full history.
    //   alice = 1000 - 100 - 50 + 30 = 880 ; bob = 0 + 100 + 50 - 30 = 120
    assert_eq!(balance_of(&live, &alice), 880, "live alice");
    assert_eq!(balance_of(&live, &bob), 120, "live bob");

    // ── (a) REWIND — reconstruct the state as-of a past receipt, two ways. ───
    //
    // The fork cursor we care about is k=4: AFTER t1+t2 (idx 2,3) but BEFORE
    // t3's memo and t4's reverse transfer. As-of step 4:
    //   alice = 1000 - 100 - 50 = 850 ; bob = 100 + 50 = 150.
    const K: usize = 4;

    // Road 1: replay forward from genesis (verified against roots[K]).
    let mut rewound_fwd = h
        .replay_to(K)
        .expect("forward replay to the past must verify");
    // Road 2: undo backward from head via the real un-turn (Turn::invert),
    // gated by the executor, verified "same root tooth, run backward" modulo the
    // monotone nonce. This is the EXACT inverse — not a replay approximation.
    let rewound_bwd = h.undo_to(K).expect("backward undo to the past must verify");

    // Both roads land on the SAME verified past VALUE/STATE.
    assert!(
        ledgers_agree_modulo_nonce(&rewound_bwd, &rewound_fwd),
        "replay-forward and undo-backward must reconstruct the same past (modulo nonce)"
    );
    // The value observables are EXACT — the rewind genuinely restored the past.
    assert_eq!(
        balance_of(&rewound_fwd, &alice),
        850,
        "rewound alice (forward)"
    );
    assert_eq!(balance_of(&rewound_fwd, &bob), 150, "rewound bob (forward)");
    assert_eq!(
        balance_of(&rewound_bwd, &alice),
        850,
        "rewound alice (backward un-turn)"
    );
    assert_eq!(
        balance_of(&rewound_bwd, &bob),
        150,
        "rewound bob (backward un-turn)"
    );
    // t3's memo field was NOT yet written at the past cursor.
    assert_eq!(
        rewound_fwd.get(&bob).unwrap().state.fields[0],
        [0u8; 32],
        "the memo (t3) is in the FUTURE of the rewound cursor — absent in the past"
    );
    // The rewind agrees with the recorded root tooth at K (anti-substitution).
    assert_eq!(
        rewound_fwd.root(),
        h.root_at(K),
        "the rewound forward state matches the recorded root tooth at K"
    );

    // ── (b) BRANCH at the past point and replay a DIFFERENT future. ──────────
    //
    // Fork at K=4 with the first-class `fork_at`. The branch SHARES the verified
    // past as the config-lattice down-set (the prefix is NOT re-executed — see
    // `fork_at_shares_the_downset_not_replay`), then we author a divergent turn:
    // instead of t3's memo + t4's bob→alice 30, alice sends bob a big 500
    // transfer. A genuinely different future from the same shared past. The
    // working ledger is the rewind result (`rewound_fwd`) — `fork_at` itself
    // neither produces nor re-executes a ledger.
    let mut branch = h.fork_at(K);
    let mut bl = rewound_fwd;
    let bex = branch.fresh_executor();

    // PROOF the past is shared: the fork's root at K equals the original's.
    assert_eq!(
        branch.root_at(K),
        h.root_at(K),
        "the branch shares the original's verified past at the fork point EXACTLY"
    );
    assert_eq!(
        balance_of(&bl, &alice),
        850,
        "branch starts from the rewound past"
    );

    // The divergent verified turn (a REAL receipt through the real executor).
    let n = nonce_of(&bl, &alice);
    let divergent_receipt = branch
        .record_commit(
            &bex,
            &mut bl,
            turn_with(
                alice,
                n,
                vec![Effect::Transfer {
                    from: alice,
                    to: bob,
                    amount: 500,
                }],
            ),
        )
        .expect("the divergent branch turn must commit as a genuine verified turn");

    // The branch now diverges: alice = 850 - 500 = 350 ; bob = 150 + 500 = 650.
    assert_eq!(balance_of(&bl, &alice), 350, "divergent branch alice");
    assert_eq!(balance_of(&bl, &bob), 650, "divergent branch bob");

    // PROOF the future diverged: the branch head root differs from BOTH the
    // original head root AND the original's root at the same height (K+1=5).
    let branch_head = branch.len();
    assert_eq!(
        branch_head,
        K + 1,
        "branch = shared prefix + one divergent turn"
    );
    assert_ne!(
        branch.root_at(branch_head),
        h.root_at(h.len()),
        "the branched future differs from the original head"
    );
    assert_ne!(
        branch.root_at(branch_head),
        h.root_at(K + 1),
        "the branched future differs from the original's step at the same height"
    );

    // ── (c) GENUINE — the divergent turn is a real verified turn. ────────────
    // It carries a real receipt hash and a real signed agent record.
    assert_eq!(
        divergent_receipt.agent, alice,
        "the receipt names the real author"
    );
    let _hash = divergent_receipt.receipt_hash(); // a real, bound receipt commitment
    // The original history is UNTOUCHED by the branch — time-travel forks, it
    // does not rewrite the settled past.
    assert_eq!(
        balance_of(&live, &alice),
        880,
        "original head unchanged by the branch"
    );
    assert_eq!(h.len(), 6, "original history length unchanged");

    // ── (d) The original future is still fully recoverable AND reversible. ───
    // Replay the original all the way back to head — the branch did not corrupt
    // the recorded history.
    let replayed_head = h.replay_to(h.len()).expect("original head still replays");
    assert_eq!(balance_of(&replayed_head, &alice), 880);
    // The whole clean window above genesis is reversible (no settled commit).
    assert!(
        h.window_reversible(2),
        "the clean window above genesis is reversible"
    );
}

// ── undo is an EXACT inverse on value/state — undo(do(s)) == s (mod nonce). ──

#[test]
fn undo_is_an_exact_inverse_on_value_state() {
    let (h, _live, _ex, alice, bob) = build_history();

    // For EVERY reversible cursor k (k >= 2 so we never undo a genesis cell),
    // undo-backward and replay-forward agree on every observable except the
    // monotone nonce — `undo(do(s)) == s` on value/state, the reversibility
    // headline. `undo_to` fail-closes internally on mismatch, so a returned Ok
    // already proves it; we re-assert for the demo's explicitness.
    for k in 2..=h.len() {
        let fwd = h.replay_to(k).expect("forward replay verifies");
        let bwd = h
            .undo_to(k)
            .expect("backward undo verifies (state modulo nonce)");
        assert!(
            ledgers_agree_modulo_nonce(&bwd, &fwd),
            "undo_to({k}) value/state must equal replay_to({k}) (the exact inverse)"
        );
        assert_eq!(
            balance_of(&bwd, &alice),
            balance_of(&fwd, &alice),
            "alice exact at k={k}"
        );
        assert_eq!(
            balance_of(&bwd, &bob),
            balance_of(&fwd, &bob),
            "bob exact at k={k}"
        );
    }
}

// ── the irreversible boundary fails closed — a settled commit is a wall. ─────

#[test]
fn rewind_fails_closed_past_a_settled_commit() {
    // History: genesis ×2, then a SETTLED nonce bump on alice (the island of
    // irreversibility — a freshness ratchet, committed by design), then a clean
    // transfer on top. Rewinding the clean tail succeeds; rewinding PAST the
    // settled commit must refuse — time-travel honors the committed boundary.
    let mut h = ReversibleHistory::new(1_700_000_000);
    let mut l = Ledger::new();
    let ex = h.fresh_executor();
    let alice = h.record_genesis(&mut l, open_cell(0xA1, 1_000)); // idx 0
    let bob = h.record_genesis(&mut l, open_cell(0xB0, 0)); // idx 1

    let n = nonce_of(&l, &alice);
    assert!(
        h.record_commit(
            &ex,
            &mut l,
            turn_with(alice, n, vec![Effect::IncrementNonce { cell: alice }])
        )
        .is_some(),
        "the settled commit (idx 2)"
    );
    let n = nonce_of(&l, &alice);
    assert!(
        h.record_commit(
            &ex,
            &mut l,
            turn_with(
                alice,
                n,
                vec![Effect::Transfer {
                    from: alice,
                    to: bob,
                    amount: 40
                }]
            ),
        )
        .is_some(),
        "the clean tail (idx 3)"
    );

    // The clean tail above the commit rewinds fine.
    assert!(
        h.undo_to(3).is_ok(),
        "rewinding the clean tail above the commit works"
    );
    // Rewinding PAST the settled nonce bump fails closed — you cannot un-settle.
    assert!(
        matches!(
            h.undo_to(2),
            Err(dregg_turn::reversible::ReversibleError::IrreversibleStep { .. })
        ),
        "rewinding past the settled commit must fail closed"
    );
    assert!(
        !h.window_reversible(2),
        "the window crossing the commit is not reversible"
    );
}

// ── fork_at SHARES the down-set — no re-execution, structurally the parent's. ─

#[test]
fn fork_at_shares_the_downset_not_replay() {
    // The first-class `ReversibleHistory::fork_at` SHARES the recorded prefix as
    // the event-structure config-lattice down-set: it lands on the original's
    // root tooth at every shared step BYTE-IDENTICALLY, and — the proof that the
    // prefix is NOT re-executed — each fork prefix step IS the parent's step
    // (same `Arc` allocation, `Arc::ptr_eq`), not a freshly recomputed object.
    // This is the named reversibility rung the earlier replay-synthesis pointed
    // at, now built.
    let (h, _live, _ex, _alice, _bob) = build_history();
    for k in 2..=h.len() {
        let branch = h.fork_at(k);
        assert_eq!(
            branch.len(),
            k,
            "the fork carries exactly the prefix length"
        );
        for step in 0..=k {
            assert_eq!(
                branch.root_at(step),
                h.root_at(step),
                "fork_at({k}) shares the original root tooth at step {step} byte-identically"
            );
        }
        // STRUCTURAL SHARING (not re-execution): the fork's prefix steps ARE the
        // parent's, witnessed by pointer-equality of the shared `Arc` handles.
        for i in 0..k {
            assert!(
                std::sync::Arc::ptr_eq(&branch.steps()[i], &h.steps()[i]),
                "fork_at({k}) step {i} is the parent's step (Arc::ptr_eq) — shared, not re-executed"
            );
        }
    }
}
