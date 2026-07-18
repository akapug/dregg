//! **The CELLS-AS-SERVICE-OBJECTS proof for privacy-voting, end-to-end.**
//!
//! The propose/vote/tally lifecycle, driven through the `invoke()` front door against
//! the real [`EmbeddedExecutor`]. The same guarantees the `bounty-board`/`kvstore`
//! service exemplars pin, on the voting floor's two-cell program (the ballot's
//! `WriteOnce(VOTE)` + the poll's `Monotonic(TALLY_*)` / `WriteOnce(CLOSED)`):
//!
//! 1. **The service publishes a typed interface** (open_poll/cast_vote/record_tally/
//!    close_poll/view with their auth + replayable-vs-serviced semantics), resolvable
//!    as a Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `cast_vote` commits a real verified turn** — the desugared
//!    `SetField`s land on the BALLOT and the `VOTE` slot binds.
//! 3. **The one-vote-per-ballot tooth bites at the executor** — a SECOND `cast_vote`
//!    is refused on the commit path by `WriteOnce(VOTE)`, not by a userspace check.
//! 4. **The cap-gate bites at the front door** — an unauthorized `cast_vote`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any turn
//!    is built; nothing is submitted (anti-ghost).
//! 5. **The monotone-tally tooth bites at the executor** — a `record_tally` advance
//!    commits, but a shrink is refused by `Monotonic(TALLY_*)`.
//! 6. **The one-way close bites** — `close_poll` sets `CLOSED`.
//! 7. **A serviced method is the named seam** — `view` refuses to desugar (its answer
//!    rides the OFE cross-cell-read).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_privacy_voting::service::{
    METHOD_CAST_VOTE, METHOD_VIEW, VotingService, VotingServiceError, interface_descriptor,
    register_interface,
};
use starbridge_privacy_voting::{
    CLOSED_SLOT, TALLY_YES_SLOT, VOTE_NO, VOTE_SLOT, VOTE_YES, seed_ballot, seed_poll,
};

/// A cipherclerk + an embedded executor with BOTH voting cells seeded: the agent's
/// own cell IS the poll (the public tally board, opened on "ship it?"), and a distinct
/// companion cell is the ballot (bound to the poll, `VOTE` unset). Returns the service
/// handle over both.
fn deploy_voting(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, VotingService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    // Install the poll program + genesis state (question hash, tallies 0, open).
    seed_poll(&executor, "ship it?");
    let poll = cclerk.cell_id();
    // Birth the ballot companion cell (its program + POLL_REF, VOTE unset) and grant
    // the operator a cap reaching it so it can author the cast_vote turn.
    let ballot = seed_ballot(&executor, &cclerk, poll);
    let service = VotingService::new(poll, ballot);
    (cclerk, executor, service)
}

#[test]
fn the_service_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_voting(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.poll);
    let resolved = registry
        .get(&service.poll)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_CAST_VOTE))
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
        &starbridge_privacy_voting::poll_cell_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_cast_vote_commits_a_real_turn_and_binds_the_ballot() {
    let (cclerk, executor, service) = deploy_voting(0x02);

    let turn = service
        .cast_vote(&cclerk, VOTE_YES, InvokeAuthority::Signature)
        .expect("a Signature holder may build a cast_vote invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared cast_vote turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetField landed — the ballot's VOTE slot is bound.
    let state = executor.cell_state(service.ballot).unwrap();
    assert_eq!(
        state.fields[VOTE_SLOT],
        field_from_u64(VOTE_YES),
        "the ballot recorded the YES choice"
    );
}

#[test]
fn a_second_cast_vote_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_voting(0x03);

    // First vote: YES binds the ballot's VOTE slot.
    let t1 = service
        .cast_vote(&cclerk, VOTE_YES, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("the first vote commits");

    // A Signature-authorized SECOND vote (a different choice): the front door passes
    // (auth + routing OK), but the EXECUTOR refuses on the verified WriteOnce(VOTE)
    // invariant — the protocol layer, not a userspace check (one vote per ballot).
    let second = service
        .cast_vote(&cclerk, VOTE_NO, InvokeAuthority::Signature)
        .expect("the second vote invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&second);
    assert!(
        rejected.is_err(),
        "the executor must refuse a second vote on the same ballot"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once") || msg.contains("writeonce") || msg.contains("program"),
        "refused on the WriteOnce(VOTE) caveat, got: {msg}"
    );

    // Anti-ghost: the ballot still records the FIRST (YES) vote.
    let state = executor.cell_state(service.ballot).unwrap();
    assert_eq!(
        state.fields[VOTE_SLOT],
        field_from_u64(VOTE_YES),
        "the first vote stands"
    );
}

#[test]
fn an_unauthorized_cast_vote_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_voting(0x04);

    // The caller holds NO authority; `cast_vote` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .cast_vote(&cclerk, VOTE_YES, InvokeAuthority::None)
        .expect_err("an unauthorized cast_vote must be refused");
    assert!(matches!(
        refused,
        VotingServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the ballot is untouched (anti-ghost).
    let state = executor.cell_state(service.ballot).unwrap();
    assert_eq!(state.fields[VOTE_SLOT], [0u8; 32]);
}

#[test]
fn record_tally_advances_but_a_shrink_is_refused_by_monotonic() {
    let (cclerk, executor, service) = deploy_voting(0x05);

    // Advance the YES tally 0 -> 1, backed by the counted ballot's id (the
    // ballot-binding CountGe gate demands the exhibit): accepted.
    let counted: std::collections::BTreeSet<[u8; 32]> =
        [service.ballot.as_bytes().to_owned()].into_iter().collect();
    let bump = service
        .record_tally(&cclerk, VOTE_YES, 1, &counted, InvokeAuthority::Signature)
        .expect("a Signature holder may build a record_tally invocation");
    executor.submit_turn(&bump).expect("the tally bump commits");
    let state = executor.cell_state(service.poll).unwrap();
    assert_eq!(
        state.fields[TALLY_YES_SLOT],
        field_from_u64(1),
        "the YES tally advanced to 1"
    );

    // Attempt to shrink the YES tally 1 -> 0 (witness present, so MONOTONIC is
    // what refuses): refused by Monotonic(TALLY_YES).
    let shrink = service
        .record_tally(&cclerk, VOTE_YES, 0, &counted, InvokeAuthority::Signature)
        .expect("the shrink invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&shrink);
    assert!(rejected.is_err(), "a tally shrink must be refused");
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refused on the Monotonic(TALLY_*) caveat, got: {msg}"
    );
}

#[test]
fn close_poll_commits_and_sets_the_closed_flag() {
    let (cclerk, executor, service) = deploy_voting(0x06);

    let turn = service
        .close_poll(&cclerk, InvokeAuthority::Signature)
        .expect("a Signature holder may build a close_poll invocation");
    executor
        .submit_turn(&turn)
        .expect("the close_poll turn commits");

    let state = executor.cell_state(service.poll).unwrap();
    assert_ne!(
        state.fields[CLOSED_SLOT], [0u8; 32],
        "the poll is closed (CLOSED set non-zero, one-way)"
    );
}

#[test]
fn view_is_a_serviced_seam() {
    let (cclerk, _executor, service) = deploy_voting(0x07);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(VotingServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );
}
