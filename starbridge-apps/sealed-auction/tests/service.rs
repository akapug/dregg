//! **The CELLS-AS-SERVICE-OBJECTS proof for sealed-auction, end-to-end.**
//!
//! The commit-reveal auction lifecycle, driven through the `invoke()` front door
//! against the real [`EmbeddedExecutor`]. The same guarantees the
//! `kvstore`/`bounty-board` service exemplars pin, on the auction's
//! `StrictMonotonic(PHASE)` + `WriteOnce(COMMIT_BASE+i)` lifecycle program:
//!
//! 1. **The auction publishes a typed interface** (commit_bid/close_commit/reveal_bid/
//!    resolve/view with their auth + replayable-vs-serviced semantics), resolvable as a
//!    Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `commit_bid` commits a real verified turn** — the desugared
//!    `SetField` lands the seal on the ledger's commit board.
//! 3. **The anti-front-running tooth bites at the executor** — a second `commit_bid` to
//!    the SAME committed slot is refused on the commit path by `WriteOnce`, not by a
//!    userspace check.
//! 4. **The cap-gate bites at the front door** — an unauthorized `commit_bid`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any turn
//!    is built; nothing is submitted (anti-ghost).
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its answer
//!    rides the OFE cross-cell-read).
//! 6. **The phase ratchet advances** — `close_commit` then `resolve` commit and
//!    advance `PHASE` one-way (`StrictMonotonic`).

use dregg_app_framework::CellId;
use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_sealed_auction::service::{
    AuctionService, AuctionServiceError, METHOD_COMMIT_BID, METHOD_VIEW, interface_descriptor,
    register_interface,
};
use starbridge_sealed_auction::{PHASE_RESOLVED, PHASE_SLOT, commit_slot, seed_auction};

/// A cipherclerk + an embedded executor whose agent cell IS the auction cell, with the
/// canonical auction program installed and a COMMIT-phase genesis state (seller bound).
fn deploy_auction(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, AuctionService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let auction_cell: CellId = cclerk.cell_id();
    // Installs `auction_cell_program()` (WriteOnce commit board / result registers +
    // StrictMonotonic(PHASE)) and sets PHASE = COMMIT + binds SELLER — the same program
    // the factory bakes, so the invoke()-desugared turns are re-enforced identically.
    seed_auction(&executor, "auctioneer");
    let service = AuctionService::new(auction_cell);
    (cclerk, executor, service)
}

#[test]
fn the_auction_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_auction(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an app
    // populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_COMMIT_BID))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_VIEW))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );

    // The published descriptor carries richer semantics than derive-from-program would
    // (all-Replayable / all-None): the ids differ.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &starbridge_sealed_auction::auction_cell_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_commit_commits_a_real_turn_and_lands_the_seal() {
    let (cclerk, executor, service) = deploy_auction(0x02);

    let seal = [0x9au8; 32];
    let turn = service
        .commit_bid(&cclerk, commit_slot(0), seal, InvokeAuthority::Signature)
        .expect("a Signature holder may build a commit_bid invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared commit turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetField landed — the sealed bid is on the board.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[commit_slot(0)],
        seal,
        "the sealed bid landed on the commit board"
    );
}

#[test]
fn a_competing_overwrite_of_a_committed_slot_is_refused_by_the_executor() {
    let (cclerk, executor, service) = deploy_auction(0x03);

    // First commit: a seal binds commit_slot(0) (WriteOnce admits-from-zero).
    let t1 = service
        .commit_bid(
            &cclerk,
            commit_slot(0),
            [0x11u8; 32],
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor.submit_turn(&t1).expect("the first commit commits");

    // A Signature-authorized competing commit to the SAME slot: the front door passes
    // (auth + routing OK), but the EXECUTOR refuses on the verified WriteOnce invariant
    // — the protocol layer, not a userspace check (the anti-front-running tooth).
    let steal = service
        .commit_bid(
            &cclerk,
            commit_slot(0),
            [0x22u8; 32],
            InvokeAuthority::Signature,
        )
        .expect("the competing commit invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&steal);
    assert!(
        rejected.is_err(),
        "the executor must refuse an overwrite of a committed bid"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once")
            || msg.contains("writeonce")
            || msg.contains("monotonic")
            || msg.contains("program"),
        "refused on the WriteOnce(COMMIT_BASE+i) caveat, got: {msg}"
    );

    // Anti-ghost: the original sealed bid is untouched; the overwrite committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[commit_slot(0)],
        [0x11u8; 32],
        "the original sealed bid is still the committed value"
    );
}

#[test]
fn an_unauthorized_commit_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_auction(0x04);

    // The caller holds NO authority; `commit_bid` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .commit_bid(&cclerk, commit_slot(0), [0x33u8; 32], InvokeAuthority::None)
        .expect_err("an unauthorized commit must be refused");
    assert!(matches!(
        refused,
        AuctionServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the commit board is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[commit_slot(0)], [0u8; 32]);
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_auction(0x05);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(AuctionServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("rig_auction")).is_none(),
        "an unknown method is not a member of the interface"
    );
}

#[test]
fn the_phase_ratchet_advances_through_invoke() {
    let (cclerk, executor, service) = deploy_auction(0x06);

    // close_commit advances COMMIT → REVEAL (StrictMonotonic).
    executor
        .submit_turn(
            &service
                .close_commit(&cclerk, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("close_commit commits");

    // resolve advances REVEAL → RESOLVED and writes WINNER / HIGH_BID (StrictMonotonic +
    // WriteOnce). The winner scalar is an opaque identity field.
    let winner = field_from_u64(7);
    executor
        .submit_turn(
            &service
                .resolve(&cclerk, winner, 50, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("resolve commits");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[PHASE_SLOT],
        field_from_u64(PHASE_RESOLVED),
        "the lifecycle reached RESOLVED"
    );

    // A re-resolve is a no-advance RESOLVED → RESOLVED the executor's StrictMonotonic refuses.
    let re = executor.submit_turn(
        &service
            .resolve(&cclerk, winner, 50, InvokeAuthority::Signature)
            .unwrap(),
    );
    assert!(re.is_err(), "a re-resolve is refused (StrictMonotonic)");
}
