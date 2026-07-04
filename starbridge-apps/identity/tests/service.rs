//! **The CELLS-AS-SERVICE-OBJECTS proof for identity, end-to-end.**
//!
//! The per-issuer credential lifecycle, driven through the `invoke()` front door
//! against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board`/`kvstore` service exemplars pin, on the issuer's
//! `MonotonicSequence(ISSUANCE_COUNTER)` + `Monotonic(REVOCATION_ROOT)` +
//! `SenderAuthorized(PublicRoot)` program — the IDENTICAL [`issuer_program`] the
//! [`issuer_factory_descriptor`] bakes (installed via [`seed_issuer`]):
//!
//! 1. **The issuer publishes a typed interface** (issue/revoke mutators +
//!    present/verify serviced reads, with their auth + replayable-vs-serviced
//!    semantics), resolvable as a Service-Explorer would resolve it (via an
//!    [`InterfaceRegistry`]).
//! 2. **An authorized `issue` commits a real verified turn** — the desugared
//!    `SetField` lands on the ledger and `ISSUANCE_COUNTER` advances 0 → 1; the
//!    turn carries the issuer's membership witness so the real `MerkleMembership`
//!    STARK admits the signer.
//! 3. **The cap-gate bites at the front door** — an unauthorized `issue`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — a replayed second `issue`
//!    (same counter value) is refused on the commit path by
//!    `MonotonicSequence(ISSUANCE_COUNTER)`, not by a userspace check.
//! 5. **A serviced method is the named seam** — `present` / `verify` refuse to
//!    desugar (their answers ride the holder/verifier-side read paths), and an
//!    unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_identity::service::{
    IdentityService, IdentityServiceError, METHOD_ISSUE, METHOD_PRESENT, METHOD_VERIFY,
    interface_descriptor, register_interface,
};
use starbridge_identity::{ISSUANCE_COUNTER_SLOT, kyc_schema, seed_issuer};

/// A cipherclerk + an embedded executor whose agent cell IS the issuer cell, with
/// the canonical issuer program installed and a configured (schema-bound, counter
/// 0) genesis state — and `ISSUER_AUTH_ROOT` committing the firing signer.
fn deploy_issuer(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, IdentityService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let issuer_cell = cclerk.cell_id();
    // Installs `issuer_program()` (WriteOnce(SCHEMA) + MonotonicSequence(COUNTER) +
    // Monotonic(REVOCATION_ROOT) + SenderAuthorized(PublicRoot(ISSUER_AUTH_ROOT))) and binds
    // the configured genesis state — the same program the factory bakes, so the
    // invoke()-desugared turns are re-enforced identically. Also seeds ISSUER_AUTH_ROOT =
    // single_member_authorized_root(signer_pk), so the firing signer is the sole authorized
    // issuer the SenderAuthorized tooth reads.
    seed_issuer(&executor, &cclerk, &kyc_schema());
    let service = IdentityService::new(issuer_cell);
    (cclerk, executor, service)
}

#[test]
fn the_issuer_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_issuer(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an app
    // populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 4);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_ISSUE))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_PRESENT))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );

    // The published descriptor carries richer semantics than derive-from-program would
    // (all-Replayable / all-None): the ids differ.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &starbridge_identity::issuer_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_issue_commits_a_real_turn_and_advances_the_lifecycle() {
    let (cclerk, executor, service) = deploy_issuer(0x02);

    let turn = service
        .issue(&cclerk, 1, InvokeAuthority::Signature)
        .expect("a Signature holder may build an issue invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared issue turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetField landed — ISSUANCE_COUNTER advanced 0 → 1.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(1),
        "the issuance sequence advanced to 1"
    );
}

#[test]
fn an_unauthorized_issue_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_issuer(0x03);

    // The caller holds NO authority; `issue` requires Signature. Refused before any turn is
    // built (fail-closed at the userspace front door).
    let refused = service
        .issue(&cclerk, 1, InvokeAuthority::None)
        .expect_err("an unauthorized issue must be refused");
    assert!(matches!(
        refused,
        IdentityServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the issuer is untouched (anti-ghost): counter still 0.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[ISSUANCE_COUNTER_SLOT], field_from_u64(0));
}

#[test]
fn a_replayed_second_issue_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_issuer(0x04);

    // First issue: ISSUANCE_COUNTER 0 → 1.
    let t1 = service
        .issue(&cclerk, 1, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("the first issue commits");

    // A Signature-authorized second issue that re-writes the SAME counter value (1): the
    // front door passes (auth + routing OK), but the EXECUTOR refuses on the verified
    // MonotonicSequence(ISSUANCE_COUNTER) invariant (it requires new == old + 1, i.e. 2) —
    // the protocol layer, not a userspace check.
    let replay = service
        .issue(&cclerk, 1, InvokeAuthority::Signature)
        .expect("the replayed issue invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&replay);
    assert!(
        rejected.is_err(),
        "the executor must refuse a non-+1 issuance"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("sequence") || msg.contains("program"),
        "refused on the MonotonicSequence(ISSUANCE_COUNTER) caveat, got: {msg}"
    );

    // Anti-ghost: the counter is still 1; the replay committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(1),
        "the counter is still 1"
    );
}

#[test]
fn the_full_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_issuer(0x05);

    // issue → revoke, each an invoke()-desugared verified turn the executor re-enforces the
    // issuer program on (carrying the membership witness for the SenderAuthorized tooth).
    executor
        .submit_turn(
            &service
                .issue(&cclerk, 1, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("issue commits (counter 0 → 1)");
    // revoke: advance REVOCATION_ROOT (1 > 0) and — under the every-turn MonotonicSequence —
    // the counter 1 → 2.
    executor
        .submit_turn(
            &service
                .revoke(&cclerk, 1, 2, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("revoke commits (root 0 → 1, counter 1 → 2)");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[ISSUANCE_COUNTER_SLOT],
        field_from_u64(2),
        "the issuance sequence reached 2"
    );

    // A revoke that REWINDS the revocation root (back to 0) is refused by Monotonic.
    let rewind = executor.submit_turn(
        &service
            .revoke(&cclerk, 0, 3, InvokeAuthority::Signature)
            .unwrap(),
    );
    assert!(
        rewind.is_err(),
        "a revocation-root rewind is refused (Monotonic)"
    );
}

#[test]
fn present_and_verify_are_serviced_seams_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_issuer(0x06);

    // `present` / `verify` are Serviced — their answers ride the holder/verifier-side read
    // paths, never a replay.
    assert!(matches!(
        service.present(&cclerk),
        Err(IdentityServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));
    assert!(matches!(
        service.verify(&cclerk),
        Err(IdentityServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );
    let _ = METHOD_VERIFY;
}
