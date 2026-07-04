//! **The CELLS-AS-SERVICE-OBJECTS proof for storage-gateway-mandate, end-to-end.**
//!
//! The three storage operations driven through the `invoke()` front door against
//! the real [`EmbeddedExecutor`], on the gateway's volume-budget + clearance
//! program. The same guarantees the `bounty-board`/`kvstore` service exemplars
//! pin, on the gateway's `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` budget
//! tooth + root-bound `ClearanceDominates` GET tooth:
//!
//! 1. **The gateway publishes a typed interface** (put/get/list with their auth +
//!    replayable-vs-serviced semantics), resolvable as a Service-Explorer would
//!    resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized in-budget `put` commits a real verified turn** — the
//!    desugared `SetField`s land and `VOLUME_SPENT` advances.
//! 3. **The budget invariant bites at the executor** — an over-budget `put`
//!    (`new_spent > ceiling`) is refused on the commit path by
//!    `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)`, not a userspace check.
//! 4. **The clearance tooth bites at the executor** — a `get` presenting the
//!    `writer` label (which dominates `storage-read`) commits, while a `get`
//!    presenting the `guest` label is refused by the root-bound
//!    `ClearanceDominates`.
//! 5. **The cap-gate bites at the front door** — an unauthorized `put`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 6. **A serviced method is the named seam** — `list` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, FieldElement, InterfaceRegistry,
    InvokeAuthority, InvokeRefused,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_storage_gateway_mandate::service::{
    GatewayService, GatewayServiceError, METHOD_GET, METHOD_LIST, METHOD_PUT, interface_descriptor,
    register_interface,
};
use starbridge_storage_gateway_mandate::{
    DEFAULT_COMMITMENT_ANCHOR, DEFAULT_KEY_PREFIX, DEFAULT_READ_COMPARTMENT,
    DEFAULT_VOLUME_CEILING, VOLUME_CEILING_SLOT, VOLUME_SPENT_SLOT, guest_label, seed_gateway,
    writer_label,
};

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse
/// of `field_from_u64` for the volume meter the gateway stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A cipherclerk + an embedded executor whose agent cell IS the gateway cell,
/// with the gateway program installed and the configured genesis state (anchor,
/// ceiling, prefix, read-compartment, clearance root, `VOLUME_SPENT = 0`).
fn deploy_gateway(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, GatewayService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let gateway = cclerk.cell_id();
    seed_gateway(
        &executor,
        DEFAULT_COMMITMENT_ANCHOR,
        DEFAULT_VOLUME_CEILING,
        DEFAULT_KEY_PREFIX,
        DEFAULT_READ_COMPARTMENT,
    );
    let service = GatewayService::new(gateway);
    (cclerk, executor, service)
}

#[test]
fn the_gateway_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_gateway(0x01);

    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 3);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_PUT))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_LIST))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );
}

#[test]
fn an_authorized_in_budget_put_commits_and_advances_the_meter() {
    let (cclerk, executor, service) = deploy_gateway(0x02);

    let state = executor.cell_state(service.cell).unwrap();
    let spent = field_to_u64(&state.fields[VOLUME_SPENT_SLOT as usize]);
    let ceiling = field_to_u64(&state.fields[VOLUME_CEILING_SLOT as usize]);
    assert_eq!(spent, 0, "the seed starts the meter at zero");
    assert!(ceiling >= 5, "the demo ceiling has headroom");
    let new_spent = spent + 5; // within the ceiling

    let turn = service
        .put(
            &cclerk,
            "uploads/doc.txt",
            new_spent,
            FieldElement::default(),
            InvokeAuthority::Signature,
        )
        .expect("a Signature holder may build a put invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared in-budget put commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    let after = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        field_to_u64(&after.fields[VOLUME_SPENT_SLOT as usize]),
        new_spent,
        "VOLUME_SPENT advanced to the new debit"
    );
}

#[test]
fn an_over_budget_put_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_gateway(0x03);

    let state = executor.cell_state(service.cell).unwrap();
    let ceiling = field_to_u64(&state.fields[VOLUME_CEILING_SLOT as usize]);
    let over = ceiling + 1; // pushes VOLUME_SPENT past the ceiling

    // The front door passes (auth + routing OK), but the EXECUTOR refuses on the
    // verified FieldLteField(VOLUME_SPENT <= VOLUME_CEILING) invariant.
    let turn = service
        .put(
            &cclerk,
            "uploads/big.bin",
            over,
            FieldElement::default(),
            InvokeAuthority::Signature,
        )
        .expect("the over-budget put invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&turn);
    assert!(
        rejected.is_err(),
        "the executor must refuse an over-budget put"
    );

    // Anti-ghost: the meter is untouched.
    let after = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        field_to_u64(&after.fields[VOLUME_SPENT_SLOT as usize]),
        0,
        "the over-budget write committed nothing"
    );
}

#[test]
fn a_writer_get_commits_while_a_guest_get_is_refused_by_the_executor() {
    let (cclerk, executor, service) = deploy_gateway(0x04);

    // A writer's clearance dominates `storage-read` — the root-bound
    // ClearanceDominates tooth admits the GET.
    let writer_turn = service
        .get(
            &cclerk,
            "uploads/doc.txt",
            writer_label(),
            InvokeAuthority::Signature,
        )
        .expect("a Signature holder may build a get invocation");
    executor
        .submit_turn(&writer_turn)
        .expect("a writer's GET dominates the read compartment and commits");

    // A guest does NOT dominate `storage-read` — the EXECUTOR refuses on the
    // root-bound ClearanceDominates tooth (not a userspace check).
    let guest_turn = service
        .get(
            &cclerk,
            "uploads/doc.txt",
            guest_label(),
            InvokeAuthority::Signature,
        )
        .expect("the guest GET invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&guest_turn);
    assert!(
        rejected.is_err(),
        "the executor must refuse a guest's GET (clearance does not dominate)"
    );
}

#[test]
fn an_unauthorized_put_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_gateway(0x05);

    // The caller holds NO authority; `put` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .put(
            &cclerk,
            "uploads/doc.txt",
            5,
            FieldElement::default(),
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized put must be refused");
    assert!(matches!(
        refused,
        GatewayServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the meter is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(field_to_u64(&state.fields[VOLUME_SPENT_SLOT as usize]), 0);
}

#[test]
fn list_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_gateway(0x06);

    // `list` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.list(&cclerk),
        Err(GatewayServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );
    assert!(iface.method(&method_symbol(METHOD_GET)).is_some());
}
