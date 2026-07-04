//! # The flagship: escrow-market drives the REAL `SealedEscrow` capacity.
//!
//! Two mutually-distrustful parties — Alice and Bob — exchange value with **no
//! trusted intermediary**, through the app's [`SealedEscrowMarket`], which drives
//! the protocol-proven `dregg_cell::escrow_sealed` capacity end to end. This is
//! the canonical object-capability / agoric escrow-exchange pattern, and the proof
//! that escrow-market's escrow is a real witnessed movable asset, not decorative
//! slot arithmetic.
//!
//! Each asserted property:
//!   1. **Witnessed deposit** — locking a leg moves the escrow cell's canonical
//!      commitment (a light client SEES value enter).
//!   2. **Atomic settlement** — both legs cross to their counterparties in one
//!      step; settling with one leg present is refused (no half-open trade).
//!   3. **Conservation** — total asset-10 and total asset-20 are invariant across
//!      the whole run (open · deposit · settle).
//!   4. **The half-open-trade attack defeated** — a ghosting counterparty cannot
//!      claim; the depositor reclaims and is made whole; one-shot consumption.

use dregg_cell::Cell;
use dregg_types::CellId;
use starbridge_escrow_market::{
    Claim, EscrowError, EscrowState, EscrowTerms, Leg, LegRequirement, LegStatus, MarketError,
    SealedEscrowMarket, Side,
};

const ASSET_10: [u8; 32] = [10u8; 32];
const ASSET_20: [u8; 32] = [20u8; 32];
const ALICE_PK: [u8; 32] = [1u8; 32];
const BOB_PK: [u8; 32] = [2u8; 32];

fn wallet(pk: [u8; 32], asset: [u8; 32], balance: i64) -> Cell {
    Cell::with_balance(pk, asset, balance)
}
fn party(pk: [u8; 32], asset: [u8; 32]) -> CellId {
    Cell::with_balance(pk, asset, 0).id()
}
fn swap_terms() -> (EscrowTerms, CellId, CellId) {
    let alice = party(ALICE_PK, ASSET_10);
    let bob = party(BOB_PK, ASSET_20);
    let terms = EscrowTerms::swap(
        LegRequirement::new(alice, CellId::from_bytes(ASSET_10), 100),
        LegRequirement::new(bob, CellId::from_bytes(ASSET_20), 250),
    );
    (terms, alice, bob)
}

/// THE FLAGSHIP HAPPY PATH: a complete atomic fair-exchange with no trusted
/// intermediary, value conserved throughout.
#[test]
fn atomic_fair_exchange_completes_and_conserves_value() {
    let (terms, alice, bob) = swap_terms();
    let mut alice_a10 = wallet(ALICE_PK, ASSET_10, 100);
    let mut alice_a20 = wallet(ALICE_PK, ASSET_20, 0);
    let mut bob_b20 = wallet(BOB_PK, ASSET_20, 250);
    let mut bob_b10 = wallet(BOB_PK, ASSET_10, 0);

    let mut market = SealedEscrowMarket::open(terms.clone());

    // Conservation baselines (wallets + the market's custody).
    let total10 = |a: &Cell, b: &Cell, m: &SealedEscrowMarket| {
        a.state.balance() + b.state.balance() + m.escrow_custody_a()
    };
    let total20 = |a: &Cell, b: &Cell, m: &SealedEscrowMarket| {
        a.state.balance() + b.state.balance() + m.escrow_custody_b()
    };
    assert_eq!(total10(&alice_a10, &bob_b10, &market), 100);
    assert_eq!(total20(&alice_a20, &bob_b20, &market), 250);

    // (1) Witnessed deposit: Alice locks leg A; the commitment moves.
    let before = market.commitment();
    market
        .deposit(
            Side::A,
            &Leg::new(alice, CellId::from_bytes(ASSET_10), 100),
            &mut alice_a10,
        )
        .expect("Alice's conforming leg deposits");
    assert_ne!(
        before,
        market.commitment(),
        "deposit re-seals the commitment"
    );
    assert_eq!(alice_a10.state.balance(), 0, "Alice's leg is locked away");
    assert_eq!(
        total10(&alice_a10, &bob_b10, &market),
        100,
        "asset-10 conserved"
    );

    // (2) Atomic: settle with only one leg present is refused.
    assert_eq!(
        market.settle(&mut alice_a20, &mut bob_b10),
        Err(MarketError::Escrow(EscrowError::LegNotDeposited(Side::B))),
        "cannot settle a half-open trade"
    );

    // Bob locks leg B.
    market
        .deposit(
            Side::B,
            &Leg::new(bob, CellId::from_bytes(ASSET_20), 250),
            &mut bob_b20,
        )
        .expect("Bob's conforming leg deposits");
    assert_eq!(bob_b20.state.balance(), 0);

    let view = market.state().unwrap();
    assert_eq!(view.status(Side::A), LegStatus::Deposited);
    assert_eq!(view.status(Side::B), LegStatus::Deposited);

    // Settle atomically.
    let (moved_a, moved_b) = market
        .settle(&mut alice_a20, &mut bob_b10)
        .expect("both legs present: settles atomically");
    assert_eq!((moved_a, moved_b), (100, 250));

    // The exchange happened, value conserved system-wide.
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
    assert_eq!(market.escrow_custody_a(), 0, "custody drained");
    assert_eq!(market.escrow_custody_b(), 0, "custody drained");
    assert_eq!(
        total10(&alice_a10, &bob_b10, &market),
        100,
        "asset-10 conserved"
    );
    assert_eq!(
        total20(&alice_a20, &bob_b20, &market),
        250,
        "asset-20 conserved"
    );

    // One-shot: a settled escrow cannot be re-settled (no double-spend).
    assert_eq!(
        market.settle(&mut alice_a20, &mut bob_b10),
        Err(MarketError::Escrow(EscrowError::LegAlreadyConsumed(
            Side::A
        )))
    );
}

/// THE HALF-OPEN-TRADE ATTACK, DEFEATED. Alice deposits; Bob never reciprocates.
/// Bob cannot claim without a genuine own deposit; Alice reclaims and is made
/// whole; the reclaimed leg is one-shot.
#[test]
fn half_open_trade_is_defeated_by_reclaim() {
    let (terms, alice, bob) = swap_terms();
    let mut alice_a10 = wallet(ALICE_PK, ASSET_10, 100);
    let mut market = SealedEscrowMarket::open(terms.clone());

    market
        .deposit(
            Side::A,
            &Leg::new(alice, CellId::from_bytes(ASSET_10), 100),
            &mut alice_a10,
        )
        .unwrap();
    assert_eq!(alice_a10.state.balance(), 0);

    // Bob cannot claim Alice's leg without depositing his own conforming leg.
    let view: EscrowState = market.state().unwrap();
    let bob_grab = Claim {
        claimant: bob,
        take: Side::A,
        own_leg: Leg::new(bob, CellId::from_bytes(ASSET_20), 250), // asserted, never deposited
        claimed_value: 100,
    };
    assert_eq!(
        view.check_claim(&terms, &bob_grab),
        Err(EscrowError::LegNotDeposited(Side::B)),
        "no claim without a conforming own deposit"
    );

    // Alice reclaims her own leg and is made whole.
    let reclaimed = market
        .reclaim(Side::A, alice, &mut alice_a10)
        .expect("Alice reclaims her leg");
    assert_eq!(reclaimed, 100);
    assert_eq!(
        alice_a10.state.balance(),
        100,
        "Alice is made whole — no value lost"
    );

    // One-shot: a reclaimed leg can never then be settled.
    let mut sink_a = wallet(ALICE_PK, ASSET_20, 0);
    let mut sink_b = wallet(BOB_PK, ASSET_10, 0);
    assert_eq!(
        market.settle(&mut sink_a, &mut sink_b),
        Err(MarketError::Escrow(EscrowError::LegAlreadyConsumed(
            Side::A
        )))
    );
    // And reclaim by a non-owner is refused (you can only reclaim YOUR leg).
    assert_eq!(
        market.reclaim(Side::A, bob, &mut sink_b),
        Err(MarketError::Escrow(EscrowError::NotYourLeg(Side::A)))
    );
}

/// An over-claim is bounded by the committed leg amount (the forge-rejecting
/// `check_claim` core).
#[test]
fn over_claim_is_rejected() {
    let (terms, alice, bob) = swap_terms();
    let mut alice_a10 = wallet(ALICE_PK, ASSET_10, 100);
    let mut bob_b20 = wallet(BOB_PK, ASSET_20, 250);
    let mut market = SealedEscrowMarket::open(terms.clone());
    market
        .deposit(
            Side::A,
            &Leg::new(alice, CellId::from_bytes(ASSET_10), 100),
            &mut alice_a10,
        )
        .unwrap();
    market
        .deposit(
            Side::B,
            &Leg::new(bob, CellId::from_bytes(ASSET_20), 250),
            &mut bob_b20,
        )
        .unwrap();

    let view = market.state().unwrap();
    let forged = Claim {
        claimant: bob,
        take: Side::A,
        own_leg: Leg::new(bob, CellId::from_bytes(ASSET_20), 250),
        claimed_value: 9_999, // A only locked 100
    };
    assert_eq!(
        view.check_claim(&terms, &forged),
        Err(EscrowError::OverClaim {
            claimed: 9_999,
            locked: 100
        })
    );
}
