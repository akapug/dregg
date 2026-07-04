//! **The CELLS-AS-SERVICE-OBJECTS proof for supply-chain-provenance, end-to-end.**
//!
//! The custody lifecycle (mint → handoff) driven through the `invoke()` front
//! door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board`/`kvstore`/`escrow-market` service exemplars pin, on the item's
//! actor-bound + `StrictMonotonic(EPOCH)` custody program:
//!
//! 1. **The item publishes a typed interface** (mint/handoff/view with their auth
//!    + replayable-vs-serviced semantics), resolvable as a Service-Explorer would
//!    resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `mint` commits a real verified turn** — the desugared
//!    `SetField`s land on the ledger and inaugurate the sole custodian (`EPOCH`
//!    advances 0 → 1, `CUSTODIAN` is the signer).
//! 3. **The cap-gate bites at the front door** — an unauthorized `mint`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — a replayed `mint` (a
//!    second `EPOCH 1 → 1`) is refused on the commit path by
//!    `StrictMonotonic(EPOCH)`, not by a userspace check.
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_supply_chain_provenance::service::{
    METHOD_HANDOFF, METHOD_VIEW, ProvenanceService, ProvenanceServiceError, interface_descriptor,
    register_interface,
};
use starbridge_supply_chain_provenance::{
    CUSTODIAN_SLOT, EPOCH_SLOT, HEAD_SLOT, TIP_SLOT, item_program, signer_identity,
};

/// A cipherclerk + an embedded executor whose agent cell IS the item cell, with
/// the canonical custody program installed but NOT yet minted (`EPOCH == 0`), so
/// the `mint` invocation inaugurates the genesis state through the executor.
fn deploy_item(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, ProvenanceService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let item_cell = cclerk.cell_id();
    // Install the SAME program the factory bakes (actor-bound register +
    // StrictMonotonic(EPOCH) + Monotonic(HEAD) + WriteOnce links), so the
    // invoke()-desugared turns are re-enforced identically. Do NOT seed genesis —
    // `mint` binds it.
    executor.install_program(item_cell, item_program());
    let service = ProvenanceService::new(item_cell);
    (cclerk, executor, service)
}

#[test]
fn the_item_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_item(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 3);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_HANDOFF))
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

    // The published descriptor carries richer semantics than derive-from-program
    // would (all-Replayable / all-None): the ids differ.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(&item_program());
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_mint_commits_a_real_turn_and_inaugurates_custody() {
    let (cclerk, executor, service) = deploy_item(0x02);

    let turn = service
        .mint(&cclerk, InvokeAuthority::Signature)
        .expect("a Signature holder may build a mint invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared mint turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed — EPOCH advanced 0 → 1 and
    // the signer holds the baton (the actor-bound register's inception).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[EPOCH_SLOT as usize],
        field_from_u64(1),
        "the provenance epoch advanced to 1"
    );
    assert_eq!(
        state.fields[CUSTODIAN_SLOT as usize],
        signer_identity(&cclerk),
        "the signer is the sole custodian"
    );
}

#[test]
fn an_unauthorized_mint_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_item(0x03);

    // The caller holds NO authority; `mint` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .mint(&cclerk, InvokeAuthority::None)
        .expect_err("an unauthorized mint must be refused");
    assert!(matches!(
        refused,
        ProvenanceServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the item is untouched (anti-ghost): still unminted.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[EPOCH_SLOT as usize], [0u8; 32]);
}

#[test]
fn a_replayed_mint_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_item(0x04);

    // First mint: inaugurates the genesis state (EPOCH 0 → 1).
    let t1 = service.mint(&cclerk, InvokeAuthority::Signature).unwrap();
    executor.submit_turn(&t1).expect("the first mint commits");

    // A Signature-authorized SECOND mint: the front door passes (auth + routing
    // OK), but the EXECUTOR refuses on the verified StrictMonotonic(EPOCH)
    // invariant (a no-advance EPOCH 1 → 1) — the protocol layer, not a userspace
    // check.
    let replay = service
        .mint(&cclerk, InvokeAuthority::Signature)
        .expect("the replayed mint invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&replay);
    assert!(
        rejected.is_err(),
        "the executor must refuse a replayed mint"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("strictly increase") || msg.contains("program"),
        "refused on the StrictMonotonic(EPOCH) caveat, got: {msg}"
    );
}

#[test]
fn the_full_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_item(0x05);

    // mint → handoff, each an invoke()-desugared verified turn the executor
    // re-enforces the custody program on.
    executor
        .submit_turn(&service.mint(&cclerk, InvokeAuthority::Signature).unwrap())
        .expect("mint commits");

    // Read the live chain cursor and accept custody (the signer takes the baton).
    let state = executor.cell_state(service.cell).unwrap();
    let from = state.fields[CUSTODIAN_SLOT as usize];
    let prev = state.fields[TIP_SLOT as usize];
    let head = {
        let mut b = [0u8; 8];
        b.copy_from_slice(&state.fields[HEAD_SLOT as usize][24..32]);
        u64::from_be_bytes(b) as usize
    };
    let handoff = service
        .handoff(&cclerk, &from, &prev, 2, head, InvokeAuthority::Signature)
        .expect("a Signature holder builds a handoff");
    executor
        .submit_turn(&handoff)
        .expect("the handoff commits and advances the chain");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[EPOCH_SLOT as usize],
        field_from_u64(2),
        "the provenance epoch advanced to 2"
    );

    // A stale handoff (re-using epoch 2) is a no-advance the executor's
    // StrictMonotonic(EPOCH) refuses.
    let stale = service
        .handoff(
            &cclerk,
            &from,
            &prev,
            2,
            head + 1,
            InvokeAuthority::Signature,
        )
        .unwrap();
    assert!(
        executor.submit_turn(&stale).is_err(),
        "a stale-epoch handoff is refused (StrictMonotonic)"
    );
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_item(0x06);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(ProvenanceServiceError::Refused(
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
