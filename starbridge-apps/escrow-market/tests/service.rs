//! **The CELLS-AS-SERVICE-OBJECTS proof for the sealed escrow-market.**
//!
//! Publishes the escrow's typed interface (`open`/`deposit`/`settle`/`reclaim` +
//! `view` with their auth + replayable-vs-serviced semantics), and drives the
//! swap lifecycle through the PROVEN `SealedEscrow` capacity via [`EscrowService`].
//! Properties pinned:
//!
//! 1. **The escrow publishes a resolvable typed interface** — richer than
//!    derive-from-program (the four mutators are `Signature`-gated, `view` is
//!    `Serviced`), resolvable through an [`InterfaceRegistry`].
//! 2. **The whole lifecycle drives the real capacity** — deposit both legs →
//!    settle atomically, value conserved; a non-conforming deposit and a one-shot
//!    replay are the capacity's forge-rejections.
//! 3. **`view` is the named serviced seam** — the committed leg state IS the
//!    answer (a pure read, not a turn).
//! 4. **The interface is witnessably inspectable** — a route-membership witness
//!    proves `settle` is a member of the committed interface.

use dregg_app_framework::InterfaceRegistry;
use dregg_cell::Cell;
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use starbridge_escrow_market::service::{
    EscrowService, METHOD_DEPOSIT, METHOD_OPEN, METHOD_RECLAIM, METHOD_SETTLE, METHOD_VIEW,
    interface_descriptor, register_interface,
};
use starbridge_escrow_market::{
    EscrowError, EscrowTerms, Leg, LegRequirement, LegStatus, MarketError, SealedEscrowMarket, Side,
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

#[test]
fn the_escrow_publishes_a_resolvable_typed_interface() {
    let cell = party(ALICE_PK, ASSET_10);
    let svc = EscrowService::new(cell);

    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, svc.cell);
    let resolved = registry
        .get(&svc.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    for m in [METHOD_OPEN, METHOD_DEPOSIT, METHOD_SETTLE, METHOD_RECLAIM] {
        assert_eq!(
            resolved.method(&method_symbol(m)).unwrap().auth_required,
            AuthRequired::Signature,
            "{m} is Signature-gated",
        );
    }
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_VIEW))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );

    // The published descriptor carries richer semantics than derive-from-program.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &dregg_cell::program::CellProgram::Predicate(vec![]),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn the_whole_lifecycle_drives_the_real_capacity() {
    let (terms, alice, bob) = swap_terms();
    let mut market = SealedEscrowMarket::open(terms);
    let svc = EscrowService::new(market.escrow.id());

    let mut alice_a10 = wallet(ALICE_PK, ASSET_10, 100);
    let mut alice_a20 = wallet(ALICE_PK, ASSET_20, 0);
    let mut bob_b20 = wallet(BOB_PK, ASSET_20, 250);
    let mut bob_b10 = wallet(BOB_PK, ASSET_10, 0);

    // view() — the serviced read: both legs empty at open.
    let state = svc.view(&market).unwrap();
    assert_eq!(state.status(Side::A), LegStatus::Empty);

    // deposit(A), deposit(B) — through the service handle.
    svc.deposit(
        &mut market,
        Side::A,
        &Leg::new(alice, CellId::from_bytes(ASSET_10), 100),
        &mut alice_a10,
    )
    .expect("Alice deposits her leg");
    svc.deposit(
        &mut market,
        Side::B,
        &Leg::new(bob, CellId::from_bytes(ASSET_20), 250),
        &mut bob_b20,
    )
    .expect("Bob deposits his leg");

    // settle() — atomic, value conserved across the crossing.
    let (a, b) = svc
        .settle(&mut market, &mut alice_a20, &mut bob_b10)
        .expect("the atomic swap settles");
    assert_eq!((a, b), (100, 250));
    assert_eq!(alice_a20.state.balance(), 250);
    assert_eq!(bob_b10.state.balance(), 100);

    // One-shot: a replayed settle is the capacity's forge-rejection.
    assert_eq!(
        svc.settle(&mut market, &mut alice_a20, &mut bob_b10),
        Err(MarketError::Escrow(EscrowError::LegAlreadyConsumed(
            Side::A
        )))
    );
}

#[test]
fn a_nonconforming_deposit_is_refused_through_the_service() {
    let (terms, _alice, bob) = swap_terms();
    let mut market = SealedEscrowMarket::open(terms);
    let svc = EscrowService::new(market.escrow.id());
    let mut bob_b20 = wallet(BOB_PK, ASSET_20, 250);

    // Bob under-pays (1 < 250): the capacity refuses; nothing moves.
    assert_eq!(
        svc.deposit(
            &mut market,
            Side::B,
            &Leg::new(bob, CellId::from_bytes(ASSET_20), 1),
            &mut bob_b20,
        ),
        Err(MarketError::Escrow(EscrowError::LegNonConforming(Side::B)))
    );
    assert_eq!(bob_b20.state.balance(), 250);
}

#[test]
fn the_interface_is_witnessably_inspectable() {
    let svc = EscrowService::new(party(ALICE_PK, ASSET_10));
    let iface = &svc.descriptor;

    for m in [
        METHOD_OPEN,
        METHOD_DEPOSIT,
        METHOD_SETTLE,
        METHOD_RECLAIM,
        METHOD_VIEW,
    ] {
        assert!(
            iface.route_method(&method_symbol(m)).is_some(),
            "{m} routes"
        );
    }

    // A route-membership witness PROVES `settle` is a member of the committed
    // interface (via the existing dfa AIR) — and does not verify for a method it
    // was not minted for.
    let settle = method_symbol(METHOD_SETTLE);
    let (proof, root) = iface
        .route_membership_witness(&settle)
        .expect("a declared method has a membership witness");
    assert_eq!(root, iface.to_route_table().commitment);
    assert!(iface.verify_route_membership(&settle, &proof));
    assert!(!iface.verify_route_membership(&method_symbol(METHOD_OPEN), &proof));
}

/// The published interface matches what the standalone descriptor builds.
#[test]
fn the_service_descriptor_is_the_published_interface() {
    let svc = EscrowService::new(party(BOB_PK, ASSET_20));
    assert_eq!(
        svc.descriptor.interface_id,
        interface_descriptor().interface_id
    );
}
