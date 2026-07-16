//! **IT PLUGS IN.** A real turn carrying `Effect::Custom` whose sub-proof is THIS AIR's
//! public inputs reaches the executor, passes the registry dispatch, and passes the STATE
//! WELD — driven through `TurnExecutor::execute`, not by calling a helper.
//!
//! This is the gate that separates "a self-consistent circuit" from "a Custom VK the
//! substrate can actually run". It follows the driven pattern of
//! `turn/tests/custom_vk_door.rs`.
//!
//! # Why these are FAST (no STARK is minted)
//!
//! The executor's custom gauntlet runs the state weld BEFORE the expensive leg verify:
//!
//! ```text
//!   verify_and_commit_proof
//!     1. enforce_custom_effect_proofs          (registry dispatch)
//!     2. verify_and_commit_proof_rotated
//!          b. convert_turn_effects_to_vm        <- THE DOOR
//!          c. enforce_custom_proof_state_binding <- THE WELD (before any proof parse)
//!          d. parse + verify the rotated leg    (the minutes-slow part)
//! ```
//!
//! So a turn with a deliberately-unparseable `execution_proof` still drives 1, 2b and 2c
//! for real. The AIR's PI layout getting PAST 2c is exactly the claim under test: its
//! public inputs open with `[old8 ‖ new8]` in the door's ABI, so a real turn can carry it.
//! `tests/prove_fold.rs` mints the actual leaf.

#![allow(non_snake_case)]

use std::sync::Arc;

use dregg_cell::{
    Cell, CellId, CellMode, CustomEffectError, CustomEffectRegistry, CustomEffectVerifier, Ledger,
    Permissions, ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2,
};
use dregg_circuit::field::BabyBear;
use dregg_turn::action::Effect;
use dregg_turn::turn::CustomProgramProof;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Turn, TurnError,
    TurnExecutor, TurnResult,
};

use dregg_param_compose::air::build;
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;

const ROLE_P: u64 = 101;
const ROLE_Q: u64 = 202;

fn shape() -> ComposeShape {
    ComposeShape::new(3, 4, 3, 2)
}

fn composition() -> Composition {
    Composition {
        subjects: vec![
            Subject {
                identity: 7,
                role: ROLE_P,
                params: vec![2, 5, 0, 0],
            },
            Subject {
                identity: 9,
                role: ROLE_Q,
                params: vec![3, 4, 0, 0],
            },
        ],
        ruleset: Ruleset {
            id: 0xAB,
            version: 1,
            linear: vec![LinearTerm {
                role: ROLE_P,
                param: 0,
                coeff: 10,
            }],
            knots: vec![Knot {
                role_a: ROLE_P,
                param_a: 1,
                role_b: ROLE_Q,
                param_b: 1,
                coeff: -2,
            }],
        },
        param_count: 4,
    }
}

// --------------------------------------------------------------------------
// Fixtures (mirroring turn/tests/custom_vk_door.rs)
// --------------------------------------------------------------------------

fn open_permissions() -> Permissions {
    Permissions {
        send: dregg_cell::AuthRequired::None,
        receive: dregg_cell::AuthRequired::None,
        set_state: dregg_cell::AuthRequired::None,
        set_permissions: dregg_cell::AuthRequired::None,
        set_verification_key: dregg_cell::AuthRequired::None,
        increment_nonce: dregg_cell::AuthRequired::None,
        delegate: dregg_cell::AuthRequired::None,
        access: dregg_cell::AuthRequired::None,
    }
}

/// Accepts any non-empty proof. Deliberate, and it does NOT launder the test: the object
/// under test is the PI LAYOUT reaching the weld, not the sub-proof's algebra (which
/// `tests/prove_fold.rs` proves for real). A rejecting verifier would short-circuit at
/// step 1 and prove nothing about the door.
struct AcceptVerifier {
    vk_hash: [u8; 32],
}

impl CustomEffectVerifier for AcceptVerifier {
    fn name(&self) -> &'static str {
        "param-compose-door-test-accept"
    }
    fn vk_hash(&self) -> [u8; 32] {
        self.vk_hash
    }
    fn verify(&self, _public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        if proof_bytes.is_empty() {
            return Err(CustomEffectError::Rejected {
                vk_hash: self.vk_hash,
                name: "param-compose-door-test-accept",
                reason: "empty proof".to_string(),
            });
        }
        Ok(())
    }
}

/// Register an accepting verifier under a genuine v2 vk_hash derived from THIS AIR's real
/// descriptor — so the registry's layered binding is satisfied honestly, and the vk the
/// turn names is the composition program's own.
fn registry_for(program_bytes: Vec<u8>) -> (CustomEffectRegistry, [u8; 32]) {
    let air_fingerprint = *blake3::hash(b"param-compose-air").as_bytes();
    let verifier_fingerprint =
        VerifierFingerprint::SourceHash(*blake3::hash(b"param-compose-verifier").as_bytes());
    let proving_system_id = ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: "param-compose-door-test",
    };
    let vk_hash = canonical_vk_v2(&VkComponents {
        program_bytes: &program_bytes,
        air_fingerprint,
        verifier_fingerprint: verifier_fingerprint.clone(),
        proving_system_id: proving_system_id.clone(),
    });
    let mut registry = CustomEffectRegistry::empty();
    registry
        .register(
            program_bytes,
            air_fingerprint,
            verifier_fingerprint,
            proving_system_id,
            Arc::new(AcceptVerifier { vk_hash }),
        )
        .expect("registers under its own v2 vk_hash");
    (registry, vk_hash)
}

fn felt8(bytes: &[u8; 32]) -> [BabyBear; 8] {
    dregg_cell::commitment::bytes32_to_felt8(bytes)
}

fn setup_sovereign(commitment: [u8; 32]) -> (CellId, Ledger) {
    let mut pk = [0u8; 32];
    pk[0] = 1;
    pk[31] = 37;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 1_000);
    cell.permissions = open_permissions();
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger
        .register_sovereign_cell(cell_id, commitment)
        .expect("sovereign registration");
    let _ = ledger.insert_cell(cell);
    (cell_id, ledger)
}

fn turn_with(
    agent: CellId,
    effects: Vec<Effect>,
    execution_proof: Option<Vec<u8>>,
    execution_proof_cell: Option<CellId>,
    new_commitment: Option<[u8; 32]>,
    custom_program_proofs: Option<Vec<CustomProgramProof>>,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof,
        execution_proof_cell,
        execution_proof_new_commitment: new_commitment,
        custom_program_proofs,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Build the composition AIR bound to `(old, new)` and package its REAL public inputs as
/// the turn's custom sub-proof.
fn compose_proof_for(
    vk_hash: [u8; 32],
    old: &[u8; 32],
    new: &[u8; 32],
) -> (CustomProgramProof, usize) {
    let air = build(&shape(), &composition(), &felt8(old), &felt8(new)).expect("builds");
    assert!(
        air.builder.air_accepts(),
        "the carried composition is honest"
    );
    let pis: Vec<u32> = air.builder.pis.iter().map(|f| f.0).collect();
    let n = pis.len();
    (
        CustomProgramProof {
            vk_hash,
            // Non-empty so the registry's ProofMissing guard passes. Deliberately NOT a
            // real STARK — see the module doc; prove_fold.rs mints the real leaf.
            proof_bytes: vec![0xAB; 32],
            public_inputs: pis,
        },
        n,
    )
}

fn program_bytes() -> Vec<u8> {
    let air = build(
        &shape(),
        &composition(),
        &[BabyBear::ZERO; 8],
        &[BabyBear::ZERO; 8],
    )
    .expect("builds");
    postcard::to_allocvec(&air.builder.descriptor()).expect("descriptor serializes")
}

// ===========================================================================
// THE GATE
// ===========================================================================

/// **IT PLUGS IN.** A turn carrying `Effect::Custom` + this AIR's public inputs, with the
/// HONEST state prefix (the cell's genuine stored OLD and this turn's claimed NEW), gets
/// PAST the door's count gate and PAST the state weld, dying only later at the
/// rotated-leg parse (the deliberately-unparseable bytes).
///
/// That terminus is the claim: the composition AIR's PI layout is one a real turn can
/// carry. Nothing about the layout refuses it.
#[test]
fn the_composition_proof_passes_the_door_and_the_weld_via_a_real_turn() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, vk_hash) = registry_for(program_bytes());

    let (proof, n_pis) = compose_proof_for(vk_hash, &stored_old, &claimed_new);
    eprintln!("composition sub-proof carries {n_pis} public inputs (cap 64)");

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            assert!(
                !matches!(reason, TurnError::CustomProofStateBindingMismatch { .. }),
                "the composition AIR's PIs must PASS the state weld — its layout opens with \
                 [old8 ‖ new8] per the door's ABI; got {reason:?}"
            );
            assert!(
                !matches!(reason, TurnError::CustomProofCountMismatch { .. }),
                "THE DOOR: the composition turn must pass the count gate; got {reason:?}"
            );
            assert!(
                !matches!(reason, TurnError::ProofVerificationFailed(_)),
                "the registry dispatch must ACCEPT the composition sub-proof (a rejected or \
                 unregistered one would die here, before the weld); got {reason:?}"
            );
            // It reached the leg verify and died there — the expected terminus for a fast
            // test with unparseable proof bytes.
            assert!(
                matches!(reason, TurnError::InvalidExecutionProof(_)),
                "expected to reach the rotated-leg parse (i.e. everything the composition \
                 AIR is responsible for passed); got {reason:?}"
            );
        }
        other => panic!(
            "with unparseable proof bytes the turn cannot commit; expected the leg-parse \
             refusal, got {other:?}"
        ),
    }
}

/// **THE WELD STILL BITES.** The SAME composition proof, but built about a DIFFERENT
/// transition, is refused by the state weld — a host cannot staple a valid composition
/// proof of some other cell's state onto this turn.
///
/// This is what makes the test above meaningful rather than vacuous: the weld is not
/// waving everything through, it is refusing exactly the wrong-transition proof.
#[test]
fn a_composition_proof_about_another_transition_is_refused_by_the_weld() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, vk_hash) = registry_for(program_bytes());

    // An honest composition — about the WRONG transition.
    let (proof, _) = compose_proof_for(vk_hash, &[0xEEu8; 32], &[0xFFu8; 32]);

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                TurnError::CustomProofStateBindingMismatch { index: 0, .. }
            ),
            "a composition proof about another transition must be refused BY THE WELD; \
             got {reason:?}"
        ),
        other => panic!("the wrong-transition composition turn must be REFUSED: {other:?}"),
    }

    assert_eq!(
        ledger.get_sovereign_commitment(&cell_id),
        Some(&stored_old),
        "a refused custom turn must not advance the sovereign commitment"
    );
}
