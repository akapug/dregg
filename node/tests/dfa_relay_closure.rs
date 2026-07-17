//! The DFA route-commitment relay wire, closed AT THE NODE.
//!
//! The `dregg-dfa-routing-v1` route-commitment-binding AIR
//! (`circuit/src/dsl/dfa_routing.rs`, faithful to the Lean model
//! `Dregg2.Crypto.DfaAcceptanceAir`) and its live verifier
//! (`turn::executor::membership_verifier::DslCircuitDfaVerifier`) both shipped —
//! but the node never MINTED the routing vk and never REGISTERED the verifier, so
//! a relay's `Witnessed { Dfa }` caveat was rejected before the verifier's own
//! logic could run (fail-closed / SAFE, but the built machinery was dead).
//!
//! `executor_setup` now mints [`route_circuit_vk`] (content-derived — no ceremony)
//! and `configure_turn_executor` deploys the routing program + registers the real
//! [`DslCircuitDfaVerifier`], so the same executor EVERY node ingress configures
//! (the thin-HTTP submit, the signed-envelope submit, the blocklace-finalized
//! path) dispatches a relay's Dfa caveat to the real STARK verifier.
//!
//! These teeth pin the WIRING closure through the `WitnessedPredicateRegistry`
//! entry a relay's caveat dispatches to:
//!
//! - the routing vk is minted, non-placeholder, and deployed in the node's Dfa
//!   registry;
//! - the node executor's `Dfa` kind now dispatches to the real `dsl-circuit-dfa`
//!   verifier (was a fail-closed stub / `KindNotRegistered`);
//! - a caveat whose commitment is not the deployed routing vk — including the
//!   relay-operator template's `[0u8; 32]` placeholder — FAILS CLOSED;
//! - malformed proof bytes under the deployed vk are REJECTED.
//!
//! The end-to-end honest-proof discharge (a valid route verifying through the
//! registered verifier) is `#[ignore]`d: it needs an honest STARK proof from the
//! routing prover, which is RED at HEAD independently of this wiring —
//! `dregg_circuit::dsl::dfa_routing::build_routing_witness`'s honest witness fails
//! the descriptor's own lowered constraints (`[#0, #11]` on row 0), panicking the
//! debug prover. The turn crate's own `live_routing_*` teeth are red with the
//! identical panic, and the circuit's prove/verify teeth were removed (only
//! `descriptor_is_deployable` remains) — a `circuit/src/dsl/dfa_routing.rs`
//! regression, not a node wiring gap. When that is repaired, drop the `#[ignore]`.

use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
};
use dregg_circuit::dsl::dfa_routing::build_routing_witness;
use dregg_node::executor_setup::{
    BlockHeightMode, canonical_router_transitions, configure_turn_executor,
    program_registry_with_route_circuit, route_circuit_vk,
};
use dregg_node::state::NodeState;
use dregg_turn::executor::prove_dfa_transition;
use dregg_turn::{ComputronCosts, TurnExecutor};

/// A node with its real on-disk state, and an executor configured exactly as
/// every node ingress configures it.
async fn configured_executor() -> (NodeState, TurnExecutor, tempfile::TempDir) {
    let dir = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(dir.path(), Vec::new()).expect("node state");
    let mut executor = TurnExecutor::new(ComputronCosts::default());
    {
        let s = state.read().await;
        configure_turn_executor(&mut executor, &s, BlockHeightMode::Current);
    }
    (state, executor, dir)
}

/// The vk is minted at all, it is content-derived (so every node agrees without a
/// ceremony or epoch decision), it is not the template's placeholder, and it is
/// deployed in the registry the node's Dfa verifier resolves against.
#[tokio::test]
async fn route_circuit_vk_is_deterministic_and_deployed() {
    let (state, _executor, _dir) = configured_executor().await;
    let s = state.read().await;
    assert_eq!(
        route_circuit_vk(),
        route_circuit_vk(),
        "the routing vk is content-derived, so it must be stable"
    );
    assert_ne!(
        route_circuit_vk(),
        [0u8; 32],
        "the routing vk must not be the relay-operator template's placeholder"
    );
    assert!(
        program_registry_with_route_circuit(&s).contains(&route_circuit_vk()),
        "the node's Dfa registry must carry the routing program at its vk"
    );
}

/// THE WIRING CLOSURE: the node-configured executor's `Dfa` kind now dispatches to
/// the real `dsl-circuit-dfa` verifier over a registry that carries the routing
/// program — no longer a fail-closed stub / `KindNotRegistered`. (The verifier
/// resolving the vk to the deployed program and running its STARK is exercised
/// end-to-end by `discharges_honest_route_end_to_end`, gated on the routing
/// prover; here we pin that the dispatch target is the real verifier, not a stub.)
#[tokio::test]
async fn node_executor_dispatches_dfa_to_the_real_verifier() {
    let (_state, executor, _dir) = configured_executor().await;
    let registry = executor
        .witnessed_registry
        .as_ref()
        .expect("the node executor carries a witnessed registry");
    let dfa = registry
        .get(WitnessedPredicateKind::Dfa)
        .expect("Dfa must be registered on the node executor (was KindNotRegistered)");
    assert_eq!(
        dfa.name(),
        "dsl-circuit-dfa",
        "Dfa must dispatch to the real DSL-circuit verifier, not a fail-closed stub"
    );
}

/// FAIL-CLOSED (undeployed commitment): a Dfa caveat whose commitment is NOT a
/// deployed vk is rejected — registering the verifier opened the routing circuit,
/// not the kind. The `[0u8; 32]` case is the relay-operator template's placeholder
/// commitment, which stays fail-closed until the template threads the vk through
/// (`dregg-storage-templates`). Uses synthetic proof bytes: the reject fires on
/// the missing-program lookup, before any STARK runs.
#[tokio::test]
async fn node_executor_fails_closed_on_undeployed_route_commitment() {
    let (_state, executor, _dir) = configured_executor().await;
    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let sender = [7u8; 32];

    for (commitment, label) in [
        ([0u8; 32], "the relay-operator template's placeholder"),
        ([0xABu8; 32], "an attacker's self-declared circuit"),
    ] {
        let wp = WitnessedPredicate::dfa(commitment, InputRef::Sender, 0);
        let err = registry
            .verify(&wp, &PredicateInput::Sender(&sender), b"any-proof-bytes")
            .expect_err(&format!("{label} must fail closed"));
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "{label} must be REJECTED (an un-deployed circuit is never host-trusted); got {err:?}"
        );
    }
}

/// FAIL-CLOSED (malformed bytes at the deployed vk): garbage / empty proof bytes
/// under the real routing vk are rejected (the wire never decodes), not waved
/// through by the registration.
#[tokio::test]
async fn node_executor_rejects_malformed_route_proof() {
    let (_state, executor, _dir) = configured_executor().await;
    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let sender = [7u8; 32];
    let wp = WitnessedPredicate::dfa(route_circuit_vk(), InputRef::Sender, 0);

    for bytes in [b"not-a-valid-dfa-wire".as_slice(), b"".as_slice()] {
        let err = registry
            .verify(&wp, &PredicateInput::Sender(&sender), bytes)
            .expect_err("a malformed routing proof must be rejected");
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "a malformed routing proof must be REJECTED; got {err:?}"
        );
    }
}

/// END-TO-END DISCHARGE (blocked on the routing prover, see module docs): an
/// honest route verifies through the registered verifier at the deployed vk. This
/// needs an honest STARK proof, and `build_routing_witness` fails the descriptor's
/// own lowered constraints at HEAD (`circuit/src/dsl/dfa_routing.rs` regression),
/// panicking the debug prover. Drop the `#[ignore]` once that is repaired.
#[ignore = "blocked on circuit/src/dsl/dfa_routing.rs: honest witness fails its own \
            lowered constraints [#0,#11] on row 0 (turn's live_routing_* red identically)"]
#[tokio::test]
async fn discharges_honest_route_end_to_end() {
    let (state, executor, _dir) = configured_executor().await;
    let transitions = canonical_router_transitions();
    let wire = {
        let s = state.read().await;
        let programs = program_registry_with_route_circuit(&s);
        let (witness, public_inputs) = build_routing_witness(&transitions, 0, &[0, 1, 0])
            .expect("the canonical router accepts internal,external,internal");
        let num_rows = witness.get("current_state").map(|v| v.len()).unwrap();
        prove_dfa_transition(
            &programs,
            &route_circuit_vk(),
            &witness,
            num_rows,
            &public_inputs,
        )
        .expect("the routing proof wire builds against the node-deployed program")
    };

    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let wp = WitnessedPredicate::dfa(route_circuit_vk(), InputRef::Sender, 0);
    let sender = [7u8; 32];
    registry
        .verify(&wp, &PredicateInput::Sender(&sender), &wire)
        .expect("an honest route must discharge the relay's Dfa caveat at the deployed vk");
}
