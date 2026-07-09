//! The genuine `proof_bind` engine for the `custom` effect — a REAL recursive
//! sub-proof verification, not a bounds check.
//!
//! ## What this closes
//!
//! The deployed `customVmDescriptor2R24` carries one `DescriptorIR2.ProofBind`
//! op binding the Custom row's `custom_proof_commitment` column (var 72) and
//! `custom_program_vk_hash` column (var 68). At the descriptor-IR level the op
//! only *declares* the binding; the in-AIR check is a bounds check
//! (`descriptor_ir2.rs`, `VmConstraint2::ProofBind`), and the EffectVM AIR's
//! Custom leg (`effect_vm/air.rs`) explicitly does NOT verify the external
//! proof — it only records its hash commitment and warns:
//!
//! > "Verifiers MUST independently verify the external proof against the
//! >  committed program VK hash. Without this check, a malicious prover can
//! >  claim any custom_proof_commitment without having a valid external proof."
//!
//! That independent verification is what this module makes a deployed,
//! SDK-reachable, light-client-runnable check. It is the REAL engine the
//! descriptor-semantic toy (`descriptor_ir2.rs::ToyEngine`) modeled: the proof
//! carrier is a genuine [`dregg_circuit::dsl::circuit::CellProgram`] STARK, the verifier
//! accepts exactly the proofs that the program's AIR accepts, and a verifying
//! proof's exposed `(commit, vk)` are the canonical PI-commitment and the
//! program's VK hash.
//!
//! ## The soundness property
//!
//! [`verify_proof_bind`] turns the descriptor's `proof_bind` gate from "the
//! columns are in range" into "the bound proof VERIFIED, its public-input
//! commitment EQUALS the bound `commit` column, and its program VK EQUALS the
//! bound `vk` column." A custom effect carrying a FORGED sub-proof — a
//! non-verifying STARK, a commitment that does not match the proof's public
//! inputs, or a VK that does not match the program — is REJECTED.
//!
//! ## How the sub-proof binds (the two columns)
//!
//! * `custom_program_vk_hash` (8 felts, EffectVM PI `CUSTOM_PROOFS_BASE + i*12 +
//!   0..8`; column 68 in the rotated descriptor) — the program identity, the
//!   32-byte [`CellProgram::vk_hash`] mapped through
//!   [`dregg_circuit::effect_vm::bytes32_to_8_limbs`]. The verifier looks the
//!   program up by this hash; an unknown program fails closed.
//! * `custom_proof_commitment` (4 felts, EffectVM PI `... + 8..12`; column 72)
//!   — [`custom_proof_pi_commitment`] of the sub-proof's public inputs. The
//!   verifier recomputes it from the verified sub-proof's PI and requires
//!   equality; a swapped or fabricated commitment fails closed.
//!
//! Both are bound into the turn hash (`turn::Turn::hash`) via
//! `custom_program_proofs`, so the sub-proof bytes + PI cannot be swapped after
//! the fact without changing the turn identity.

use dregg_circuit::binding::WideHash;
use dregg_circuit::dsl::circuit::{CellProgram, ProgramRegistry};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::BabyBear;

/// Domain separator for the custom sub-proof's public-input commitment. Distinct
/// from every other `WideHash` domain so a commitment minted here cannot be
/// confused with (or replayed as) any other binding hash.
pub const CUSTOM_PROOF_PI_DOMAIN: &str = "dregg-custom-proof-bind-pi-v1";

/// The EffectVM `custom_proof_commitment` column is a DEPLOYED 4-felt descriptor
/// column (`customVmDescriptor2R24`, vars 68..72). It is its OWN binding surface,
/// distinct from the action/presentation binding, and is NOT widened to 8 here:
/// doing so is VK-affecting in the effect-VM AIR (re-emit the descriptor, shift
/// the column layout, re-pin the FP, touch the Lean descriptor). At 4 felts it
/// carries ~62-bit birthday collision resistance — the SAME class of exposure the
/// action binding had, and a forged sub-proof's public inputs are adversary-
/// chosen, so it IS collision-relevant. This 4-felt column is the precise
/// remaining surface to rotate in a dedicated effect-VM descriptor pass.
pub type ProofBindCommitment = [BabyBear; 4];

/// The canonical commitment to a custom sub-proof's public inputs — the value
/// that lands in the Custom row's `custom_proof_commitment` column.
///
/// Prover and verifier MUST agree on this derivation: the prover writes it into
/// the EffectVM Custom row + PI, and [`verify_proof_bind`] recomputes it from the
/// verified sub-proof's public inputs and requires equality.
///
/// Derived as the first 4 felts of the canonical [`WideHash::from_poseidon2`]
/// squeeze under [`CUSTOM_PROOF_PI_DOMAIN`]. Because the first squeeze block of
/// `from_poseidon2` is independent of the (newer) second block, these 4 felts are
/// byte-identical to the pre-8-felt-`WideHash` value — the deployed descriptor FP
/// is unchanged. See [`ProofBindCommitment`] for why this stays at 4 felts.
pub fn custom_proof_pi_commitment(public_inputs: &[BabyBear]) -> ProofBindCommitment {
    let wide = WideHash::from_poseidon2(CUSTOM_PROOF_PI_DOMAIN, public_inputs);
    let felts = wide.to_felts();
    [felts[0], felts[1], felts[2], felts[3]]
}

/// A custom effect's external program proof, fully witnessed: the program it
/// runs under (its descriptor IS the VK), the verifying STARK, and the public
/// inputs the proof attests.
///
/// This is the in-memory form the prover produces and the verifier consumes.
/// On the wire it is carried as `turn::CustomProgramProof { proof_bytes,
/// public_inputs }` plus the program (resolved from the host
/// [`ProgramRegistry`] by the bound VK hash) — exactly the
/// `verify_transition` contract.
#[derive(Clone, Debug)]
pub struct BoundCustomProof {
    /// The program (its descriptor is the VK; `vk_hash` is its identity).
    pub program: CellProgram,
    /// The serialized STARK proof bytes for one transition under `program`.
    pub proof_bytes: Vec<u8>,
    /// The public inputs the sub-proof attests.
    pub public_inputs: Vec<BabyBear>,
    /// **PROVER-SIDE-ONLY re-provable trace witness** (the named trace-column witness the
    /// `CellProgram` proves over). Retained so the deployed chain prover can RE-PROVE the sub-proof
    /// as a recursion-foldable leaf ([`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`])
    /// and FOLD it under the custom-binding node — making the commitment binding witnessable by a
    /// PURE LIGHT CLIENT, not just a re-executing validator. `None` for a `BoundCustomProof`
    /// reconstructed from the on-wire [`dregg_turn::CustomProgramProof`] (the wire keeps only the
    /// finished bytes + PIs; the re-provable witness is NEVER serialized). A `None`-witness bound
    /// proof carries the off-AIR verify but cannot be folded — exactly the re-exec-only rung.
    pub witness_values: Option<std::collections::HashMap<String, Vec<BabyBear>>>,
    /// The number of trace rows for [`Self::witness_values`] (prover-side only; `None` off the wire).
    pub num_rows: Option<usize>,
}

impl BoundCustomProof {
    /// The 8-felt `custom_program_vk_hash` column value this proof binds.
    pub fn vk_hash_felts(&self) -> [BabyBear; 8] {
        bytes32_to_8_limbs(&self.program.vk_hash)
    }

    /// The 4-felt `custom_proof_commitment` column value this proof binds.
    pub fn proof_commitment(&self) -> ProofBindCommitment {
        custom_proof_pi_commitment(&self.public_inputs)
    }
}

/// The claimed binding read off the EffectVM Custom row / PI: the columns the
/// descriptor's `proof_bind` op pins. The verifier checks the sub-proof against
/// exactly THESE claimed values, so a row that lies about either column is
/// rejected even when the sub-proof itself verifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClaimedProofBind {
    /// The Custom row's `custom_program_vk_hash` column (8 felts, var 68).
    pub vk_hash: [BabyBear; 8],
    /// The Custom row's `custom_proof_commitment` column (4 felts, var 72).
    pub commitment: ProofBindCommitment,
}

/// Why a `proof_bind` verification failed — every variant is a forged or
/// malformed binding the genuine engine REJECTS (where the old bounds-check
/// would have accepted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofBindError {
    /// The bound VK hash names no program in the host registry — fail closed.
    UnknownProgram { vk_hash: [BabyBear; 8] },
    /// The resolved program's VK does not match the Custom row's bound VK column.
    VkMismatch {
        claimed: [BabyBear; 8],
        program: [BabyBear; 8],
    },
    /// The sub-proof's public-input commitment does not match the bound
    /// `custom_proof_commitment` column.
    CommitmentMismatch {
        claimed: ProofBindCommitment,
        recomputed: ProofBindCommitment,
    },
    /// The external STARK sub-proof did not verify under the program's AIR.
    SubProofVerifyFailed(String),
    /// The sub-proof could not be proven (prove side only).
    SubProofProveFailed(String),
}

impl std::fmt::Display for ProofBindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofBindError::UnknownProgram { .. } => {
                write!(
                    f,
                    "proof_bind: bound VK names no registered program (fail closed)"
                )
            }
            ProofBindError::VkMismatch { .. } => {
                write!(
                    f,
                    "proof_bind: program VK does not match the bound vk column"
                )
            }
            ProofBindError::CommitmentMismatch { .. } => write!(
                f,
                "proof_bind: sub-proof PI commitment does not match the bound commit column"
            ),
            ProofBindError::SubProofVerifyFailed(e) => {
                write!(f, "proof_bind: external sub-proof failed verification: {e}")
            }
            ProofBindError::SubProofProveFailed(e) => {
                write!(f, "proof_bind: external sub-proof could not be proven: {e}")
            }
        }
    }
}

impl std::error::Error for ProofBindError {}
