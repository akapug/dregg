//! **The CELLS-AS-SERVICE-OBJECTS proof for subscription, end-to-end (AX3).**
//!
//! The pub/sub queue lifecycle driven through the `invoke()` front door against the
//! real [`EmbeddedExecutor`]. The same guarantees the `bounty-board` / `kvstore`
//! service exemplars pin, on the feed's installed [`feed_invariants_program`] (the
//! flat `Monotonic` head/tail + `WriteOnce` capacity/owner + `FieldLteField(tail <=
//! head)` invariants — the SAME shared program the deos surface (AX2) installs via
//! [`seed_feed`]):
//!
//! 1. **The feed publishes a typed interface** (publish/consume/grant_*/view with
//!    their auth + replayable-vs-serviced semantics), resolvable via an
//!    [`InterfaceRegistry`].
//! 2. **An authorized `consume` / `publish` commits a real verified turn** — the
//!    desugared effects land on the ledger and the cursors advance.
//! 3. **The cap-gate bites at the front door** — an unauthorized `consume` is
//!    refused before any turn is built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — a head ROLLBACK is refused
//!    on the commit path by `Monotonic(SEQ_HEAD)`, not by a userspace check.
//! 5. **A serviced method is the named seam** — `view` refuses to desugar, and an
//!    unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_subscription::service::{
    METHOD_CONSUME, METHOD_VIEW, SubscriptionService, SubscriptionServiceError,
    interface_descriptor, register_interface, subscription_service_program,
};
use starbridge_subscription::{
    SEQ_HEAD_SLOT, SEQ_TAIL_SLOT, field_from_bytes, fold_message_root, seed_feed,
};

/// A cipherclerk + an embedded executor whose agent cell IS the feed cell, with the
/// flat queue invariants installed and a configured genesis state (head=1, tail=0).
fn deploy_feed(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, SubscriptionService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let feed_cell = cclerk.cell_id();
    // Installs `feed_invariants_program()` and seeds capacity/owner + head=1, tail=0
    // — the SAME shared program the deos surface assumes, re-enforced on every turn.
    seed_feed(&executor, 16, "owner");
    let service = SubscriptionService::new(feed_cell);
    (cclerk, executor, service)
}

#[test]
fn the_feed_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_feed(0x01);

    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_CONSUME))
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
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &subscription_service_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_consume_commits_and_advances_the_tail() {
    let (cclerk, executor, service) = deploy_feed(0x02);

    // seed leaves head=1, tail=0 — a consume to new_tail=1 is valid (tail <= head).
    let payload = field_from_bytes(b"delivered");
    let turn = service
        .consume(&cclerk, 1, payload, InvokeAuthority::Signature)
        .expect("a Signature holder may build a consume invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared consume turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[SEQ_TAIL_SLOT as usize],
        field_from_u64(1),
        "the consumer cursor advanced to 1"
    );
}

#[test]
fn an_authorized_publish_commits_and_advances_the_head() {
    let (cclerk, executor, service) = deploy_feed(0x03);

    // seed leaves head=1 — a publish to new_head=2 advances under Monotonic.
    let payload = field_from_bytes(b"item-2");
    let root = fold_message_root(&[0u8; 32], 2, &payload);
    let turn = service
        .publish(&cclerk, 2, root, payload, InvokeAuthority::Signature)
        .expect("a Signature holder may build a publish invocation");
    executor
        .submit_turn(&turn)
        .expect("the desugared publish turn commits");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[SEQ_HEAD_SLOT as usize],
        field_from_u64(2),
        "the producer cursor advanced to 2"
    );
}

#[test]
fn an_unauthorized_consume_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_feed(0x04);

    let payload = field_from_bytes(b"delivered");
    let refused = service
        .consume(&cclerk, 1, payload, InvokeAuthority::None)
        .expect_err("an unauthorized consume must be refused");
    assert!(matches!(
        refused,
        SubscriptionServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the tail is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[SEQ_TAIL_SLOT as usize], field_from_u64(0));
}

#[test]
fn a_head_rollback_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_feed(0x05);

    // The front door passes (auth + routing OK), but a publish whose head ROLLS BACK
    // below the current head (seed head=1 → new_head=0) is an EXECUTOR refusal on the
    // verified `Monotonic(SEQ_HEAD)` invariant — the protocol layer, not userspace.
    let payload = field_from_bytes(b"rollback");
    let root = fold_message_root(&[0u8; 32], 0, &payload);
    let rollback = service
        .publish(&cclerk, 0, root, payload, InvokeAuthority::Signature)
        .expect("the rollback invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&rollback);
    assert!(
        rejected.is_err(),
        "the executor must refuse a head rollback (Monotonic)"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field"),
        "refused on the Monotonic(SEQ_HEAD) caveat, got: {msg}"
    );

    // Anti-ghost: the head is still 1; the rollback committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[SEQ_HEAD_SLOT as usize], field_from_u64(1));
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_feed(0x06);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(SubscriptionServiceError::Refused(
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
