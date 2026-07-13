//! DRIVEN — the [`ComputeOffering`] over the REAL compute-exchange substrate: post a job
//! (budget escrowed), a worker claims + the requester settles conserving the escrow to the worker
//! (Σδ = 0, a real `TurnReceipt`), and every refusal a compute market must enforce — a double-claim,
//! a settle without a valid claim / result, a below-floor job, an over-budget claim, a settle fired
//! by a non-requester. Each is executor-refereed: a legal move Lands a real receipt; an illegal one
//! is a real Refusal that commits nothing (anti-ghost).

use dreggnet_compute::{ComputeOffering, TURN_CLAIM, TURN_POST, TURN_SETTLE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

fn requester() -> DreggIdentity {
    DreggIdentity("requester-corp".into())
}
fn worker() -> DreggIdentity {
    DreggIdentity("worker-gpu-node-a".into())
}
fn other_worker() -> DreggIdentity {
    DreggIdentity("worker-gpu-node-b".into())
}

fn post(arg: i64) -> Action {
    Action::new("post", TURN_POST, arg, true)
}
fn claim(arg: i64) -> Action {
    Action::new("claim", TURN_CLAIM, arg, true)
}
fn settle_with_result() -> Action {
    Action::new("settle", TURN_SETTLE, 0, true).with_text("blake3:rendered-frame-batch-ok")
}
fn settle_no_result() -> Action {
    Action::new("settle", TURN_SETTLE, 0, true)
}

// =============================================================================
// (1) THE HONEST LIFECYCLE — post → claim → settle, each a real verified turn, the escrow
//     conserved to the worker (Σδ = 0).
// =============================================================================

#[test]
fn honest_lifecycle_posts_claims_and_settles_conserved() {
    let off = ComputeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(7)).expect("open");

    // POST — the requester escrows a 1000 budget. A real verified post turn.
    let r = off.advance(&mut s, post(1000), requester());
    assert!(r.landed(), "post landed a real turn, got {r:?}");
    if let Outcome::Landed { receipt, ended } = &r {
        assert_ne!(receipt.turn_hash, [0u8; 32], "a real post turn hash");
        assert!(!ended);
    }
    assert!(s.is_posted());
    assert_eq!(s.budget(), 1000);
    assert_eq!(s.onledger_state(), Some(1), "STATE POSTED on-ledger");

    // CLAIM — a worker claims at 800 (≤ budget). Cap-gated `bid` → STATE POSTED→BID.
    let r = off.advance(&mut s, claim(800), worker());
    assert!(r.landed(), "claim landed a real turn, got {r:?}");
    assert!(s.is_claimed());
    assert_eq!(s.claim_price(), 800);
    assert_eq!(s.onledger_state(), Some(2), "STATE BID on-ledger");
    assert!(
        s.onledger_claimant_matches(),
        "PROVIDER_HASH is the real worker"
    );

    // SETTLE — the requester releases the escrow with the worker's result. PAID=800, REFUNDED=200.
    let r = off.advance(&mut s, settle_with_result(), requester());
    assert!(r.landed(), "settle landed a real turn, got {r:?}");
    if let Outcome::Landed { ended, .. } = &r {
        assert!(*ended, "settle ends the session");
    }
    assert!(s.is_settled());
    assert_eq!(s.onledger_state(), Some(3), "STATE SETTLED on-ledger");

    // Conservation Σδ = 0, and the budget moved to the worker (PAID == claim).
    assert_eq!(
        s.onledger_settlement(),
        Some((800, 200, 1000)),
        "paid 800 to the worker, refunded 200, budget 1000"
    );
    assert_eq!(
        s.settlement_delta(),
        Some(0),
        "Σδ = PAID + REFUNDED − BUDGET = 0"
    );

    // Three real verified turns; verify() holds over the committed chain.
    assert_eq!(s.receipts_len(), 3, "post + claim + settle");
    let v = off.verify(&s);
    assert!(v.verified, "verify holds: {}", v.detail);
    assert_eq!(v.turns, 3);
}

// =============================================================================
// (2) DOUBLE-CLAIM — a second claim on an already-claimed job is a real refusal (nothing commits).
// =============================================================================

#[test]
fn a_double_claim_is_refused_nothing_commits() {
    let off = ComputeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(11)).expect("open");
    assert!(off.advance(&mut s, post(1000), requester()).landed());
    assert!(off.advance(&mut s, claim(800), worker()).landed());

    // A second worker tries to claim the same job — the POSTED precondition now fails.
    let r = off.advance(&mut s, claim(700), other_worker());
    assert!(!r.landed(), "the double-claim must be refused, got {r:?}");
    // Nothing committed: still the first worker's claim, still STATE BID, still 2 receipts.
    assert_eq!(s.claim_price(), 800, "the first claim stands");
    assert_eq!(
        s.onledger_state(),
        Some(2),
        "still BID — the double-claim committed nothing"
    );
    assert_eq!(s.receipts_len(), 2, "no receipt for the refused claim");
    assert!(
        s.onledger_claimant_matches(),
        "the on-ledger claimant is still the first worker"
    );
}

// =============================================================================
// (3) SETTLE WITHOUT A VALID CLAIM — a settle on an unclaimed job does not settle.
// =============================================================================

#[test]
fn a_settle_without_a_claim_is_refused() {
    let off = ComputeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(13)).expect("open");
    assert!(off.advance(&mut s, post(1000), requester()).landed());

    let r = off.advance(&mut s, settle_with_result(), requester());
    assert!(
        !r.landed(),
        "a settle with no claim must be refused, got {r:?}"
    );
    assert!(!s.is_settled());
    assert_eq!(
        s.onledger_state(),
        Some(1),
        "still POSTED — nothing settled"
    );
    assert_eq!(s.receipts_len(), 1, "only the post turn");
}

// =============================================================================
// (4) SETTLE WITHOUT A RESULT — the worker must submit a result before the escrow releases.
// =============================================================================

#[test]
fn a_settle_without_a_result_is_refused() {
    let off = ComputeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(17)).expect("open");
    assert!(off.advance(&mut s, post(1000), requester()).landed());
    assert!(off.advance(&mut s, claim(800), worker()).landed());

    // Settle with NO result text — the SUBMIT gate refuses.
    let r = off.advance(&mut s, settle_no_result(), requester());
    assert!(
        !r.landed(),
        "a settle with no result must be refused, got {r:?}"
    );
    assert!(!s.is_settled());
    assert_eq!(s.onledger_state(), Some(2), "still BID — nothing settled");

    // With the result submitted, the SAME settle now lands (non-vacuous: the gate really gated).
    let r = off.advance(&mut s, settle_with_result(), requester());
    assert!(r.landed(), "with a result, the settle lands, got {r:?}");
    assert!(s.is_settled());
}

// =============================================================================
// (5) BELOW-FLOOR JOB — a job whose budget is below the market floor does not settle.
// =============================================================================

#[test]
fn a_below_floor_job_does_not_settle() {
    let off = ComputeOffering::new().with_floor(5000);
    let mut s = off.open(SessionConfig::with_seed(19)).expect("open");
    // Budget 1000 < floor 5000: it posts and can be claimed, but never settles.
    assert!(off.advance(&mut s, post(1000), requester()).landed());
    assert!(off.advance(&mut s, claim(800), worker()).landed());

    let r = off.advance(&mut s, settle_with_result(), requester());
    assert!(!r.landed(), "a below-floor job must not settle, got {r:?}");
    assert!(!s.is_settled());
    assert_eq!(
        s.onledger_state(),
        Some(2),
        "still BID — the below-floor job did not settle"
    );

    // A job AT/above the floor settles fine (non-vacuous floor).
    let off2 = ComputeOffering::new().with_floor(5000);
    let mut s2 = off2.open(SessionConfig::with_seed(20)).expect("open");
    assert!(off2.advance(&mut s2, post(6000), requester()).landed());
    assert!(off2.advance(&mut s2, claim(4000), worker()).landed());
    assert!(
        off2.advance(&mut s2, settle_with_result(), requester())
            .landed(),
        "an at-floor job settles"
    );
    assert_eq!(s2.settlement_delta(), Some(0), "conserved");
}

// =============================================================================
// (6) OVER-BUDGET CLAIM — a claim above the budget is a real executor refusal (FieldLteField).
// =============================================================================

#[test]
fn an_over_budget_claim_is_refused_by_the_executor() {
    let off = ComputeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(23)).expect("open");
    assert!(off.advance(&mut s, post(1000), requester()).landed());

    // Claim 1500 against a 1000 budget — the substrate's FieldLteField(BID <= BUDGET) bites.
    let r = off.advance(&mut s, claim(1500), worker());
    assert!(
        !r.landed(),
        "an over-budget claim must be refused, got {r:?}"
    );
    assert!(!s.is_claimed(), "the over-budget claim bound no worker");
    assert_eq!(
        s.onledger_state(),
        Some(1),
        "still POSTED — the claim committed nothing"
    );
    assert_eq!(s.receipts_len(), 1, "no receipt for the refused claim");

    // A within-budget claim by the same worker then lands (non-vacuous: the budget gate really gated).
    assert!(
        off.advance(&mut s, claim(900), worker()).landed(),
        "a within-budget claim lands"
    );
    assert_eq!(s.claim_price(), 900);
}

// =============================================================================
// (7) THE CAP TOOTH — a settle fired by a non-requester (the worker) is a real cap refusal.
// =============================================================================

#[test]
fn a_settle_by_a_non_requester_is_refused_at_the_cap() {
    let off = ComputeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(29)).expect("open");
    assert!(off.advance(&mut s, post(1000), requester()).landed());
    assert!(off.advance(&mut s, claim(800), worker()).landed());

    // The WORKER (provider rights) tries to settle (needs requester/root rights) — cap refusal.
    let r = off.advance(&mut s, settle_with_result(), worker());
    assert!(
        !r.landed(),
        "a worker's settle must be refused at the cap, got {r:?}"
    );
    assert!(!s.is_settled());
    assert_eq!(
        s.onledger_state(),
        Some(2),
        "still BID — the worker's settle committed nothing"
    );

    // The REQUESTER settles fine (non-vacuous cap: the right actor lands it).
    assert!(
        off.advance(&mut s, settle_with_result(), requester())
            .landed(),
        "the requester settles"
    );
    assert!(s.is_settled());
}

// =============================================================================
// (8) VERIFY IS NON-VACUOUS — it fails on an empty (unposted) chain, holds on a real one.
// =============================================================================

#[test]
fn verify_fails_on_an_unposted_session_and_holds_on_a_real_chain() {
    let off = ComputeOffering::new();
    let empty = off.open(SessionConfig::with_seed(31)).expect("open");
    let v = off.verify(&empty);
    assert!(!v.verified, "an unposted session has no chain to verify");

    let mut s = off.open(SessionConfig::with_seed(33)).expect("open");
    assert!(off.advance(&mut s, post(1000), requester()).landed());
    assert!(off.verify(&s).verified, "a posted job verifies");
    assert!(off.advance(&mut s, claim(800), worker()).landed());
    assert!(off.verify(&s).verified, "a claimed job verifies");
    assert!(
        off.advance(&mut s, settle_with_result(), requester())
            .landed()
    );
    let v = off.verify(&s);
    assert!(v.verified, "a settled job verifies: {}", v.detail);
    assert_eq!(v.turns, 3);
}
