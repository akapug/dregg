//! Multi-step derivation chaining AIR -- backward-compatible shim.
//!
//! The production implementation uses [`crate::dsl::derivation`] for the DSL-native
//! multi-step circuit. This module provides the types and prove/verify functions
//! expected by existing callers.

use crate::derivation_air::{
    CircuitRule, DERIVATION_AIR_WIDTH, DerivationWitness, compute_policy_root,
};
use crate::dsl::derivation::MULTI_STEP_DSL_WIDTH;
use crate::field::BabyBear;
use crate::poseidon2::hash_2_to_1;

/// Multi-step AIR width.
pub const MULTI_STEP_AIR_WIDTH: usize = DERIVATION_AIR_WIDTH + 5;

/// Maximum derivation steps per proof (single-proof AIR constraint).
pub const MAX_STEPS: usize = 32;

/// Maximum delegation chain depth across all composed proofs.
///
/// Bounds the total proving time for a delegation chain: at an assumed ~500ms per
/// step (an order-of-magnitude estimate, not benchmarked) this caps it near ~50
/// seconds. Chains deeper than this are rejected at proof generation time
/// to prevent DoS via unbounded recursive proving.
///
/// This limit applies to the total chain from root issuer to final delegate. A single
/// proof covers up to MAX_STEPS steps; chains longer than MAX_STEPS use chunked
/// derivation (multiple proofs composed). This cap limits the TOTAL depth.
pub const MAX_DELEGATION_DEPTH: usize = 100;

/// The "allow" predicate marker value.
pub const ALLOW_PREDICATE: u32 = 0xA110;

/// Multi-step column indices (appended after derivation columns).
pub mod col {
    use super::DERIVATION_AIR_WIDTH;

    pub const STEP_INDEX: usize = DERIVATION_AIR_WIDTH;
    pub const ACCUMULATED_HASH: usize = DERIVATION_AIR_WIDTH + 1;
    pub const PREV_ACCUMULATED: usize = DERIVATION_AIR_WIDTH + 2;
    pub const IS_FINAL_STEP: usize = DERIVATION_AIR_WIDTH + 3;
    pub const IS_ACTIVE: usize = DERIVATION_AIR_WIDTH + 4;
}

/// Public input layout.
pub mod pi {
    pub const INITIAL_STATE_ROOT: usize = 0;
    pub const REQUEST_HASH: usize = 1;
    pub const CONCLUSION: usize = 2;
    pub const NUM_STEPS: usize = 3;
    pub const FINAL_ACCUMULATED_HASH: usize = 4;
    pub const POLICY_ROOT: usize = 5;
}

/// One body Merkle proof: `(leaf, sibling path, position bits)`.
type BodyMerkleProof = (BabyBear, Vec<[BabyBear; 3]>, Vec<u8>);

/// Witness for a multi-step derivation.
#[derive(Clone, Debug)]
pub struct MultiStepWitness {
    pub initial_state_root: BabyBear,
    pub request_hash: BabyBear,
    pub steps: Vec<DerivationWitness>,
    pub allow_predicate: BabyBear,
    pub policy_root: BabyBear,
    pub body_merkle_proofs: Option<Vec<BodyMerkleProof>>,
}

impl MultiStepWitness {
    pub fn conclusion(&self) -> BabyBear {
        if let Some(last) = self.steps.last() {
            if last.derived_predicate == self.allow_predicate {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        } else {
            BabyBear::ZERO
        }
    }

    pub fn compute_accumulated_hashes(&self) -> Vec<BabyBear> {
        let mut acc = Vec::with_capacity(self.steps.len());
        let mut prev = self.initial_state_root;
        for step in &self.steps {
            let derived_hash = step.derived_hash();
            let next = hash_2_to_1(prev, derived_hash);
            acc.push(next);
            prev = next;
        }
        acc
    }

    pub fn final_accumulated_hash(&self) -> BabyBear {
        self.compute_accumulated_hashes()
            .last()
            .copied()
            .unwrap_or(self.initial_state_root)
    }
}

/// Build a multi-step witness from components.
pub fn build_multi_step_witness(
    initial_state_root: BabyBear,
    request_hash: BabyBear,
    steps: Vec<DerivationWitness>,
) -> MultiStepWitness {
    let rules: Vec<&CircuitRule> = steps.iter().map(|s| &s.rule).collect();
    let policy_root = compute_policy_root(&rules);

    MultiStepWitness {
        initial_state_root,
        request_hash,
        steps,
        allow_predicate: BabyBear::new(ALLOW_PREDICATE),
        policy_root,
        body_merkle_proofs: None,
    }
}

/// **The multi-step accumulator-chain constraints** — the prerequisite named by
/// `docs/DESIGN-parse-as-derivation.md` §2 ("the multi-step *derivation* accumulator
/// chain is columns-present/constraints-absent today") and its status ledger (the
/// GAP row `multi_step_witness.rs:146`).
///
/// The 384-column multi-step trace (`dsl::derivation::generate_multi_step_trace_dsl`)
/// LAYS OUT `STEP_INDEX / ACCUMULATED_HASH / PREV_ACCUMULATED` but no deployed
/// descriptor CONSTRAINS them. These are the descriptor-level (`ConstraintExpr`)
/// constraints that bind the linear fold `acc_i = hash_2_to_1(acc_{i-1},
/// derived_hash_i)` (`compute_accumulated_hashes`, above), authored line-for-line on
/// the `dsl::dfa_routing` running-hash template:
///
/// - **accumulation** — `next.ACCUMULATED_HASH == hash_2_to_1(this.ACCUMULATED_HASH,
///   next.DERIVED_HASH)` — the exact `ChainedHash2to1` form `dfa_routing.rs:178`
///   ships for its route commitment, over the derivation step's `DERIVED_HASH`
///   (`derivation_air::col::DERIVED_HASH`).
/// - **prev threading** — `next.PREV_ACCUMULATED == this.ACCUMULATED_HASH`, a degree-1
///   `Transition` (`dfa_routing.rs:173`) so each row's `PREV_ACCUMULATED` witnesses
///   the previous accumulator (the fold's seed of that step).
///
/// The chain's boundary pins (row-0 seed against `pi[INITIAL_STATE_ROOT]`, last-row
/// `ACCUMULATED_HASH == pi[FINAL_ACCUMULATED_HASH]`, `STEP_INDEX` monotonicity, and
/// the `IS_FINAL_STEP`/`IS_ACTIVE` selector discipline) are the descriptor's
/// `BoundaryDef`s / per-row selector constraints — assembled when this list is wired
/// into a standalone multi-step `CircuitDescriptor`. That descriptor assembly, and
/// the STEP_INDEX `+1` increment (needs an `INPUT_POS_P1`-style helper column, cf.
/// `dsl::dyck_stack`), are the remainder of the prerequisite; these two are its
/// load-bearing chain binds.
pub fn multi_step_chaining_constraints() -> Vec<crate::dsl::circuit::ConstraintExpr> {
    use crate::derivation_air::col as dcol;
    use crate::dsl::circuit::ConstraintExpr;
    use crate::dsl::derivation::multi_col;
    vec![
        // acc_i = hash_2_to_1(acc_{i-1}, derived_hash_i).
        ConstraintExpr::ChainedHash2to1 {
            output_next_col: multi_col::ACCUMULATED_HASH,
            seed_local_col: multi_col::ACCUMULATED_HASH,
            input_next_col: dcol::DERIVED_HASH,
        },
        // next.prev_accumulated == this.accumulated_hash.
        ConstraintExpr::Transition {
            next_col: multi_col::PREV_ACCUMULATED,
            local_col: multi_col::ACCUMULATED_HASH,
        },
    ]
}

/// The multi-step derivation AIR (constraint-prover interface).
pub struct MultiStepDerivationAir {
    pub witness: MultiStepWitness,
    pub max_steps: usize,
}

impl MultiStepDerivationAir {
    pub fn new(witness: MultiStepWitness) -> Self {
        let max_steps = witness.steps.len().max(1);
        Self { witness, max_steps }
    }

    pub fn with_max_steps(witness: MultiStepWitness, max_steps: usize) -> Self {
        Self { witness, max_steps }
    }
}

impl crate::constraint_prover::Air for MultiStepDerivationAir {
    fn trace_width(&self) -> usize {
        MULTI_STEP_DSL_WIDTH
    }
    fn num_public_inputs(&self) -> usize {
        6
    }
    fn constraints(&self) -> Vec<crate::constraint_prover::Constraint> {
        // The retired `constraint_prover::Constraint` interface (a trace-digest mock,
        // purged 2026-07-16) is not the real constraint path. The descriptor-level
        // (`ConstraintExpr`) accumulator-chain constraints — the ones the design's
        // status ledger flags as the GAP here — are authored in
        // [`multi_step_chaining_constraints`]; per-row derivation checking runs through
        // the DSL evaluator.
        vec![]
    }
    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        crate::dsl::derivation::generate_multi_step_trace_dsl(&self.witness)
    }
}

// RETIRED 2026-07-16 (mock-proof purge): `prove_authorization` (a trace-digest
// proof over `MultiStepDerivationAir`, not a cryptographic one) had a single caller —
// the equally retired `presentation::prove_authorization`. The real derivation
// proof is the IR-v2 descriptor path (`prove_vm_descriptor2`).

/// Generate the multi-step trace.
pub fn generate_multi_step_trace(
    witness: &MultiStepWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    crate::dsl::derivation::generate_multi_step_trace_dsl(witness)
}
