//! # The flagship Houyhnhnm demo: a REAL SealedEscrow atomic fair-exchange.
//!
//! Two mutually-distrustful parties — Alice and Bob — exchange value with **no
//! trusted intermediary**, driving the PROVEN `dregg_cell::escrow_sealed`
//! capacity end to end. This is the canonical object-capability / agoric pattern
//! (Miller's *escrow exchange agent*) and the bedrock of trustless distributed
//! agent commerce — exactly the Houyhnhnm picture of mutually-suspicious agents
//! exchanging value safely.
//!
//! The census in `docs/deos/PROTOCOL-FRONTIER-FOR-APPS.md` found that the proven
//! `SealedEscrow` capacity has ZERO app users — `starbridge-apps/escrow-market`
//! *fakes* escrow with hand-rolled slot caveats. This demo uses the REAL API.
//!
//! ## The model
//!
//! Value in dregg is per-asset (a wallet for asset X is a `Cell` whose `token_id`
//! is X and whose signed `balance` carries the value). Alice trades 100 of
//! asset-10 for Bob's 250 of asset-20:
//!
//! ```text
//!   alice_a10 (100) ──deposit leg A──┐                 ┌── bob_b10  (→100)
//!                                     ▼  escrow cell    │
//!                              [witnessed custody]──settle──atomic──┤
//!                                     ▲                 │
//!   bob_b20   (250) ──deposit leg B──┘                 └── alice_a20 (→250)
//! ```
//!
//! The escrow MODULE is the witness/gate: it decides *when* (both conforming legs
//! present, unconsumed) and *how much* (`settle()` returns the authorized
//! `(amount_a, amount_b)`) value may move. This test plays the executor role
//! honestly — performing the wallet moves the gate authorizes, and asserting the
//! system conserves value at every step.
//!
//! What the demo demonstrates (each asserted):
//!   1. **Witnessed deposit** — locking a leg moves the escrow cell's canonical
//!      commitment (a light client SEES value enter the escrow).
//!   2. **Atomic settlement** — both legs move to their counterparties in one
//!      step; there is no half-open trade.
//!   3. **Conservation** — total asset-10 and total asset-20 are invariant across
//!      the whole run (open · deposit · settle), value-conserving by construction.
//!   4. **The half-open-trade attack defeated** — if a counterparty never
//!      reciprocates, the depositor RECLAIMS and is made whole; no party can ever
//!      walk away holding the other's leg without a genuine own deposit.

use dregg_cell::Cell;
use dregg_cell::escrow_sealed::{
    EscrowError, EscrowState, EscrowTerms, Leg, LegRequirement, LegStatus, Side, deposit_leg,
    is_escrow, open_escrow, reclaim_leg, settle,
};
use dregg_types::CellId;

const ASSET_10: [u8; 32] = [10u8; 32];
const ASSET_20: [u8; 32] = [20u8; 32];
const ALICE_PK: [u8; 32] = [1u8; 32];
const BOB_PK: [u8; 32] = [2u8; 32];

/// A wallet = a sovereign cell holding a signed balance in one asset.
fn wallet(pk: [u8; 32], asset: [u8; 32], balance: i64) -> Cell {
    Cell::with_balance(pk, asset, balance)
}

/// The id the escrow's terms name a party by — its asset-source wallet id. (Both
/// parties are identified by the cell that locks their leg.)
fn party_id(pk: [u8; 32], asset: [u8; 32]) -> CellId {
    Cell::with_balance(pk, asset, 0).id()
}

/// The honest executor move: debit `amount` (>0) from `from`, credit it to `to`.
/// Returns false if `from` cannot cover it (no value is created or destroyed).
fn move_value(from: &mut Cell, to: &mut Cell, amount: i64) -> bool {
    assert!(amount > 0);
    let amt = amount as u64;
    if !from.state.debit_balance(amt) {
        return false;
    }
    assert!(to.state.credit_balance(amt));
    true
}

/// THE FLAGSHIP HAPPY PATH: a complete atomic fair-exchange with no trusted
/// intermediary, value conserved throughout.
#[test]
fn atomic_fair_exchange_completes_and_conserves_value() {
    // ── The two parties' wallets. Alice has 100 of asset-10 and an (empty)
    //    receiving wallet for asset-20; Bob symmetric. ──────────────────────────
    let mut alice_a10 = wallet(ALICE_PK, ASSET_10, 100);
    let mut alice_a20 = wallet(ALICE_PK, ASSET_20, 0);
    let mut bob_b20 = wallet(BOB_PK, ASSET_20, 250);
    let mut bob_b10 = wallet(BOB_PK, ASSET_10, 0);

    // The escrow's custody wallets (value in transit lives here while locked).
    let mut escrow_a10 = wallet([0xE5; 32], ASSET_10, 0);
    let mut escrow_b20 = wallet([0xE5; 32], ASSET_20, 0);

    // Invariant we will check after every step: value is conserved per asset.
    let total_10 =
        |a: &Cell, b: &Cell, e: &Cell| a.state.balance() + b.state.balance() + e.state.balance();
    let total_20 =
        |a: &Cell, b: &Cell, e: &Cell| a.state.balance() + b.state.balance() + e.state.balance();
    let sum10_0 = total_10(&alice_a10, &bob_b10, &escrow_a10);
    let sum20_0 = total_20(&alice_a20, &bob_b20, &escrow_b20);
    assert_eq!(sum10_0, 100);
    assert_eq!(sum20_0, 250);

    // ── Open the escrow with the swap terms. The terms digest is sealed into the
    //    escrow cell's commitment so the two parties cannot disagree on the trade. ─
    let alice = party_id(ALICE_PK, ASSET_10);
    let bob = party_id(BOB_PK, ASSET_20);
    let terms = EscrowTerms::swap(
        LegRequirement::new(alice, CellId::from_bytes(ASSET_10), 100),
        LegRequirement::new(bob, CellId::from_bytes(ASSET_20), 250),
    );
    let mut escrow = wallet([0xE5; 32], [0xE5; 32], 0);
    open_escrow(&mut escrow, &terms);
    assert!(is_escrow(&escrow));

    // ── Alice deposits leg A: value LEAVES her wallet into escrow custody, and
    //    the escrow commitment MOVES (witnessed — a light client sees it). ───────
    let commit_before = escrow.state_commitment();
    deposit_leg(
        &mut escrow,
        &terms,
        Side::A,
        &Leg::new(alice, CellId::from_bytes(ASSET_10), 100),
    )
    .expect("Alice's conforming leg deposits");
    assert!(move_value(&mut alice_a10, &mut escrow_a10, 100));
    let commit_after = escrow.state_commitment();
    assert_ne!(
        commit_before, commit_after,
        "depositing a leg re-seals the escrow commitment — value is witnessed"
    );
    assert_eq!(alice_a10.state.balance(), 0, "Alice's leg is locked away");
    // Conservation still holds with value in transit.
    assert_eq!(total_10(&alice_a10, &bob_b10, &escrow_a10), 100);

    // At this point only A is in. Settlement MUST refuse (no half-open trade).
    assert_eq!(
        settle(&mut escrow, &terms),
        Err(EscrowError::LegNotDeposited(Side::B)),
        "atomic: cannot settle with only one leg present"
    );

    // ── Bob deposits leg B. ───────────────────────────────────────────────────
    deposit_leg(
        &mut escrow,
        &terms,
        Side::B,
        &Leg::new(bob, CellId::from_bytes(ASSET_20), 250),
    )
    .expect("Bob's conforming leg deposits");
    assert!(move_value(&mut bob_b20, &mut escrow_b20, 250));
    assert_eq!(bob_b20.state.balance(), 0);

    // ── Settle atomically. The gate authorizes the EXACT amounts that move; we
    //    (the executor) move each leg to its counterparty in one step. ──────────
    let view = EscrowState::read(&escrow).unwrap();
    assert_eq!(view.status(Side::A), LegStatus::Deposited);
    assert_eq!(view.status(Side::B), LegStatus::Deposited);
    let (moved_a, moved_b) =
        settle(&mut escrow, &terms).expect("both legs present: settles atomically");
    assert_eq!((moved_a, moved_b), (100, 250));

    // Leg A (asset-10) → Bob; leg B (asset-20) → Alice. Atomic crossing.
    assert!(move_value(&mut escrow_a10, &mut bob_b10, moved_a));
    assert!(move_value(&mut escrow_b20, &mut alice_a20, moved_b));

    // ── The exchange happened: Alice holds Bob's 250 of asset-20, Bob holds
    //    Alice's 100 of asset-10, and value is conserved system-wide. ───────────
    assert_eq!(
        alice_a20.state.balance(),
        250,
        "Alice received Bob's asset-20"
    );
    assert_eq!(
        bob_b10.state.balance(),
        100,
        "Bob received Alice's asset-10"
    );
    assert_eq!(escrow_a10.state.balance(), 0, "escrow custody drained");
    assert_eq!(escrow_b20.state.balance(), 0, "escrow custody drained");
    assert_eq!(
        total_10(&alice_a10, &bob_b10, &escrow_a10),
        sum10_0,
        "asset-10 conserved"
    );
    assert_eq!(
        total_20(&alice_a20, &bob_b20, &escrow_b20),
        sum20_0,
        "asset-20 conserved"
    );

    // ── One-shot: the settled legs cannot be replayed to double-spend. ─────────
    assert_eq!(
        settle(&mut escrow, &terms),
        Err(EscrowError::LegAlreadyConsumed(Side::A)),
        "a settled escrow cannot be re-settled (one-shot)"
    );
}

/// THE HALF-OPEN-TRADE ATTACK, DEFEATED. Alice deposits; Bob never reciprocates.
/// Alice reclaims her leg and is made whole. No party can walk away holding the
/// other's leg without a genuine own deposit — and a settled-or-reclaimed leg is
/// one-shot.
#[test]
fn half_open_trade_is_defeated_by_reclaim() {
    let mut alice_a10 = wallet(ALICE_PK, ASSET_10, 100);
    let mut escrow_a10 = wallet([0xE5; 32], ASSET_10, 0);

    let alice = party_id(ALICE_PK, ASSET_10);
    let bob = party_id(BOB_PK, ASSET_20);
    let terms = EscrowTerms::swap(
        LegRequirement::new(alice, CellId::from_bytes(ASSET_10), 100),
        LegRequirement::new(bob, CellId::from_bytes(ASSET_20), 250),
    );
    let mut escrow = wallet([0xE5; 32], [0xE5; 32], 0);
    open_escrow(&mut escrow, &terms);

    // Alice locks her leg; Bob ghosts (never deposits).
    deposit_leg(
        &mut escrow,
        &terms,
        Side::A,
        &Leg::new(alice, CellId::from_bytes(ASSET_10), 100),
    )
    .unwrap();
    assert!(move_value(&mut alice_a10, &mut escrow_a10, 100));
    assert_eq!(alice_a10.state.balance(), 0);

    // Bob cannot claim Alice's leg without depositing his own conforming leg.
    let view = EscrowState::read(&escrow).unwrap();
    let bob_grab = dregg_cell::escrow_sealed::Claim {
        claimant: bob,
        take: Side::A,
        own_leg: Leg::new(bob, CellId::from_bytes(ASSET_20), 250), // asserted, never deposited
        claimed_value: 100,
    };
    assert_eq!(
        view.check_claim(&terms, &bob_grab),
        Err(EscrowError::LegNotDeposited(Side::B)),
        "no claim without a conforming own deposit — the half-open trade is refused"
    );

    // Alice reclaims her own leg and is made whole.
    let reclaimed =
        reclaim_leg(&mut escrow, &terms, Side::A, alice).expect("Alice reclaims her leg");
    assert_eq!(reclaimed, 100);
    assert!(move_value(&mut escrow_a10, &mut alice_a10, reclaimed));
    assert_eq!(
        alice_a10.state.balance(),
        100,
        "Alice is made whole — no value lost"
    );
    assert_eq!(escrow_a10.state.balance(), 0);

    // One-shot: a reclaimed leg can never then be settled (no double-spend).
    assert_eq!(
        settle(&mut escrow, &terms),
        Err(EscrowError::LegAlreadyConsumed(Side::A)),
        "a reclaimed leg cannot be settled — one-shot consumption"
    );
    // And reclaim by a non-owner is refused (you can only reclaim YOUR leg).
    assert_eq!(
        reclaim_leg(&mut escrow, &terms, Side::A, bob),
        Err(EscrowError::NotYourLeg(Side::A)),
    );
}
