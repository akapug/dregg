//! **The CELLS-AS-SERVICE-OBJECTS proof for polis (the council), end-to-end.**
//!
//! The council propose → approve → certify → execute governance lifecycle, driven
//! through the `invoke()` front door against the real [`EmbeddedExecutor`]. The
//! same guarantees the `bounty-board` / `governed-namespace` service exemplars
//! pin, on the council's verified M-of-N program (`AllowedTransitions` machine +
//! `AffineLe` threshold gate + `Monotonic` approval bits):
//!
//! 1. **The council publishes a typed interface** (propose/approve/certify/reject/
//!    execute/view with their auth + replayable-vs-serviced semantics), resolvable
//!    as a Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **The whole lifecycle commits through invoke()** — propose → approve(×2) →
//!    certify → execute, each an invoke()-desugared verified turn the executor
//!    re-enforces the council program on; the proposal advances to EXECUTED.
//! 3. **The cap-gate bites at the front door** — an unauthorized `certify`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — a `certify` with too few
//!    approvals is refused on the commit path by `AffineLe { M·flag − Σ ≤ 0 }`,
//!    not by a userspace check.
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.
//!
//! The service face is compiled INTO THIS TEST BINARY via `#[path]` — it is NOT a
//! library module, because `dregg-sdk` depends on `starbridge-polis` and
//! `dregg-app-framework` depends on `dregg-sdk`, so a normal `polis →
//! app-framework` edge would close an illegal package cycle. Cargo permits it only
//! across the dev-dependency edge this binary uses. See `Cargo.toml`'s
//! `[features].deos` comment.

#![cfg(feature = "deos")]
#![allow(dead_code)] // the included `src/service.rs` has pub items this binary uses a subset of

#[path = "../src/service.rs"]
mod service;

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;

use service::{
    CouncilService, CouncilServiceError, interface_descriptor, register_interface, seed_council,
};
use starbridge_polis::STATE_SLOT;
use starbridge_polis::council::{
    APPROVED_FLAG_SLOT, CouncilCharter, METHOD_CERTIFY, METHOD_VIEW, STATE_APPROVED,
    STATE_EXECUTED, STATE_PROPOSED,
};

const THRESHOLD: u64 = 2;

fn charter_2of3() -> CouncilCharter {
    CouncilCharter::new(
        vec![
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x22; 32]),
            CellId::from_bytes([0x33; 32]),
        ],
        THRESHOLD,
    )
}

/// A cipherclerk + an embedded executor whose agent cell IS the council proposal
/// cell, with the canonical council program installed (DRAFT genesis).
fn deploy_council(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CouncilService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let charter = charter_2of3();
    seed_council(&executor, &charter);
    let service = CouncilService::new(cclerk.cell_id(), charter);
    (cclerk, executor, service)
}

#[test]
fn the_council_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_council(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 6);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_CERTIFY))
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
}

#[test]
fn the_full_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_council(0x02);
    let council = service.cell;

    // propose → approve(0) → approve(1) → certify → execute, each an
    // invoke()-desugared verified turn the executor re-enforces the council
    // program on.
    executor
        .submit_turn(
            &service
                .propose(&cclerk, [0xAC; 32], InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("propose commits");
    let state = executor.cell_state(council).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        field_from_u64(STATE_PROPOSED),
        "the council advanced to PROPOSED"
    );

    executor
        .submit_turn(
            &service
                .approve(&cclerk, 0, 1, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("member 0 approves");
    executor
        .submit_turn(
            &service
                .approve(&cclerk, 1, 2, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("member 1 approves (quorum reached)");

    executor
        .submit_turn(
            &service
                .certify(&cclerk, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("certify commits (Σ approvals == M, AffineLe holds)");
    let state = executor.cell_state(council).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        field_from_u64(STATE_APPROVED)
    );
    assert_eq!(state.fields[APPROVED_FLAG_SLOT as usize], field_from_u64(1));

    executor
        .submit_turn(
            &service
                .execute(&cclerk, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("execute commits");
    let state = executor.cell_state(council).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        field_from_u64(STATE_EXECUTED),
        "the lifecycle reached EXECUTED"
    );

    // A re-execute is a no-row AllowedTransitions refusal (terminal/inert).
    let re = executor.submit_turn(
        &service
            .execute(&cclerk, InvokeAuthority::Signature)
            .unwrap(),
    );
    assert!(
        re.is_err(),
        "EXECUTED is terminal — a re-execute is refused"
    );
}

#[test]
fn an_unauthorized_certify_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_council(0x03);
    let council = service.cell;

    // Bring it to PROPOSED + two approvals so only auth gates the certify.
    executor
        .submit_turn(
            &service
                .propose(&cclerk, [0xAC; 32], InvokeAuthority::Signature)
                .unwrap(),
        )
        .unwrap();

    // The caller holds NO authority; `certify` requires Signature. Refused before
    // any turn is built (fail-closed at the userspace front door).
    let refused = service
        .certify(&cclerk, InvokeAuthority::None)
        .expect_err("an unauthorized certify must be refused");
    assert!(matches!(
        refused,
        CouncilServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the flag is untouched (anti-ghost).
    let state = executor.cell_state(council).unwrap();
    assert_eq!(state.fields[APPROVED_FLAG_SLOT as usize], [0u8; 32]);
}

#[test]
fn a_premature_certify_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_council(0x04);
    let council = service.cell;

    // PROPOSED + only ONE approval (M = 2).
    executor
        .submit_turn(
            &service
                .propose(&cclerk, [0xAC; 32], InvokeAuthority::Signature)
                .unwrap(),
        )
        .unwrap();
    executor
        .submit_turn(
            &service
                .approve(&cclerk, 0, 1, InvokeAuthority::Signature)
                .unwrap(),
        )
        .unwrap();

    // A Signature-authorized certify: the front door passes (auth + routing OK),
    // but the EXECUTOR refuses on the verified `AffineLe { 2·flag − Σ ≤ 0 }` gate
    // (Σ = 1 < M = 2) — the protocol layer, not a userspace check.
    let early = service
        .certify(&cclerk, InvokeAuthority::Signature)
        .expect("the certify invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&early);
    assert!(
        rejected.is_err(),
        "the executor must refuse arming the flag with too few approvals"
    );

    // Anti-ghost: the proposal is still PROPOSED, the flag still 0.
    let state = executor.cell_state(council).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        field_from_u64(STATE_PROPOSED)
    );
    assert_eq!(state.fields[APPROVED_FLAG_SLOT as usize], [0u8; 32]);
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_council(0x05);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(CouncilServiceError::Refused(
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
