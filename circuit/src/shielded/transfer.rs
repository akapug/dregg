//! The shielded transfer STARK side: hidden membership + nullifier per input,
//! over the commitment tree, bound to the published value-commitment transcript.
//!
//! This is the part of the M2-a shielded transfer that is a genuine ZK *circuit*
//! and lives in `dregg-circuit` (no dependency on `dregg-cell`'s curve stack —
//! `circuit` is *upstream* of `cell`, so the Pedersen value-balance half is
//! composed at the `cell`/test layer; see this module's `mod.rs` and the
//! integration tests). What lives here:
//!
//! - [`ShieldedInputProof`] — one hidden note-spend proof: it proves, with the
//!   note **owner** and **spending key** in the (hidden) witness, that the input
//!   note is a member of the commitment tree at `merkle_root` and that
//!   `nullifier` is its correct derivation, all through `HidingFriPcs`.
//! - [`ShieldedTransfer`] — the published shielded action: the per-input hidden
//!   proofs + the revealed `(nullifiers, merkle_root)` + the opaque
//!   value-commitment transcript bytes the Pedersen side conserves.
//!
//! The value commitments are carried here as opaque 32-byte blobs
//! (`ShieldedValueLeg`), exactly the compressed-Ristretto encoding
//! `dregg_cell::value_commitment::ValueCommitment::to_bytes` produces. This
//! lets the circuit-side transfer *bind* the value transcript (so the two halves
//! cannot be mixed-and-matched across actions) without `circuit` depending on
//! the curve crate. The conservation/range verification over those bytes is the
//! Pedersen half (`dregg_cell::value_commitment::verify_full_conservation_bytes`),
//! composed downstream.

use crate::dsl::dsl_p3_air::{DslZkProof, prove_dsl_zk, verify_dsl_zk};
use crate::field::BabyBear;
use crate::shielded::spend_circuit::{
    ShieldedSpendWitness, generate_shielded_spend_trace, pi, shielded_spend_circuit,
};

/// One value-commitment leg of a shielded transfer: the asset type (still public
/// in the single-asset M2-a toehold) and the opaque 32-byte compressed Pedersen
/// value commitment (`v·V + r·R`, hiding `v`). The Pedersen conservation proof
/// (downstream, over these bytes) certifies `Σ in = Σ out` without revealing any
/// `v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedValueLeg {
    /// Asset type (public in M2-a; hidden into a scalar in M2-b's ZSA pool).
    pub asset_type: u64,
    /// Compressed Ristretto encoding of the Pedersen value commitment.
    pub commitment_bytes: [u8; 32],
}

/// One spent input's **hidden** note-spend proof.
///
/// `proof` is produced through the hiding uni-STARK path, so its openings reveal
/// nothing about the witness (owner, spending key, randomness, the full note
/// preimage, the Merkle path) beyond the public inputs. The public inputs that
/// the verifier checks are carried alongside so a [`ShieldedTransfer`] can pin
/// every input to the *same* `merkle_root` and collect the revealed nullifier.
///
/// (Not `Clone`/`Debug`: the inner `DslZkProof` (a `p3_uni_stark::Proof` over the
/// hiding config) implements neither; it is `Serialize` for transport.)
pub struct ShieldedInputProof {
    /// The revealed nullifier (the chain's double-spend tag for this input).
    pub nullifier: BabyBear,
    /// The hiding (zero-knowledge) shielded-spend proof (membership + nullifier,
    /// owner/leaf/key/path all blind). The note's value/asset are NOT bound here
    /// — they live in the Pedersen value commitment (the transfer's other half).
    pub proof: DslZkProof,
}

impl ShieldedInputProof {
    /// The public-input vector this input's proof is checked against, pinned to
    /// the shared `merkle_root`. Layout matches the shielded-spend circuit's PI:
    /// `[nullifier, merkle_root]`.
    fn public_inputs(&self, merkle_root: BabyBear) -> Vec<BabyBear> {
        let mut pis = vec![BabyBear::ZERO; 2];
        pis[pi::NULLIFIER] = self.nullifier;
        pis[pi::MERKLE_ROOT] = merkle_root;
        pis
    }
}

/// A published shielded transfer (the M2-a object, circuit side).
///
/// What a verifier sees: the commitment-tree `merkle_root`, one hidden note-spend
/// proof per input (each revealing only its nullifier + the bound value/asset
/// felts), and the input/output value-commitment legs the Pedersen side
/// conserves. What stays hidden: every input note's owner and spending key, the
/// full note preimage, and every Merkle path — all inside the `HidingFriPcs`
/// proofs. What the Pedersen layer additionally hides: the actual amounts.
///
/// (Not `Clone`/`Debug`: holds `ShieldedInputProof`s whose inner `DslZkProof`
/// implements neither.)
pub struct ShieldedTransfer {
    /// The commitment-tree root all input notes are proven members of.
    pub merkle_root: BabyBear,
    /// One hidden note-spend proof per spent input.
    pub inputs: Vec<ShieldedInputProof>,
    /// Input value-commitment legs (the spent notes' Pedersen commitments).
    pub input_legs: Vec<ShieldedValueLeg>,
    /// Output value-commitment legs (the minted notes' Pedersen commitments).
    pub output_legs: Vec<ShieldedValueLeg>,
}

impl ShieldedTransfer {
    /// Verify the **STARK side** of the shielded transfer: every input's hidden
    /// membership+nullifier proof verifies against the shared `merkle_root`, and
    /// the nullifiers are pairwise distinct (no in-transfer double-spend).
    ///
    /// This does NOT check value balance — that is the Pedersen conservation
    /// proof over `input_legs`/`output_legs` (downstream, in `dregg_cell`). A
    /// complete shielded-transfer acceptance is `verify_stark_side()` AND the
    /// Pedersen `verify_full_conservation_bytes`. See [`transfer_message`] for
    /// the transcript that binds the two halves together.
    pub fn verify_stark_side(&self) -> Result<(), ShieldedError> {
        if self.inputs.is_empty() {
            return Err(ShieldedError::NoInputs);
        }
        let circuit = shielded_spend_circuit();
        // Each input's hidden proof must verify against the shared root.
        for (i, input) in self.inputs.iter().enumerate() {
            let pis = input.public_inputs(self.merkle_root);
            verify_dsl_zk(&circuit, &input.proof, &pis).map_err(|e| {
                ShieldedError::InputProofRejected {
                    input_index: i,
                    reason: format!("{e}"),
                }
            })?;
        }
        // No two inputs may carry the same nullifier (in-transfer double-spend).
        for i in 0..self.inputs.len() {
            for j in (i + 1)..self.inputs.len() {
                if self.inputs[i].nullifier == self.inputs[j].nullifier {
                    return Err(ShieldedError::DuplicateNullifier {
                        a: i,
                        b: j,
                    });
                }
            }
        }
        Ok(())
    }

    /// The set of nullifiers this transfer spends (what the chain's nullifier set
    /// must reject if any are already present — the cross-transfer double-spend
    /// gate, enforced by the existing nullifier-set grow-gate).
    pub fn nullifiers(&self) -> Vec<BabyBear> {
        self.inputs.iter().map(|i| i.nullifier).collect()
    }

    /// The transcript that binds the STARK side to the Pedersen side: the
    /// `merkle_root`, every nullifier, and every value-commitment leg, in order.
    /// Both halves' proofs are Fiat-Shamir-bound to this message so an adversary
    /// cannot splice the membership proofs of one transfer onto the value
    /// commitments of another. The Pedersen conservation/range proofs take this
    /// as their `message`.
    pub fn transfer_message(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(b"dregg-shielded-transfer-v1");
        m.extend_from_slice(&self.merkle_root.as_u32().to_le_bytes());
        m.extend_from_slice(&(self.inputs.len() as u64).to_le_bytes());
        for input in &self.inputs {
            m.extend_from_slice(&input.nullifier.as_u32().to_le_bytes());
        }
        m.extend_from_slice(&(self.input_legs.len() as u64).to_le_bytes());
        for leg in &self.input_legs {
            m.extend_from_slice(&leg.asset_type.to_le_bytes());
            m.extend_from_slice(&leg.commitment_bytes);
        }
        m.extend_from_slice(&(self.output_legs.len() as u64).to_le_bytes());
        for leg in &self.output_legs {
            m.extend_from_slice(&leg.asset_type.to_le_bytes());
            m.extend_from_slice(&leg.commitment_bytes);
        }
        m
    }
}

/// Witness for building one input's hidden note-spend proof: the full note
/// preimage + spending key + Merkle path (all hidden), plus the published value
/// commitment leg for it.
#[derive(Clone, Debug)]
pub struct ShieldedTransferWitness {
    /// The hidden shielded-spend witness (leaf commitment, key, Merkle path).
    pub spend: ShieldedSpendWitness,
    /// This input's published value-commitment leg.
    pub leg: ShieldedValueLeg,
}

/// Prove one shielded input: generate the shielded-spend trace and prove it
/// through the **hiding** uni-STARK path, yielding a [`ShieldedInputProof`]
/// whose openings reveal nothing about the leaf / key / path.
pub fn prove_shielded_input(
    witness: &ShieldedTransferWitness,
) -> Result<ShieldedInputProof, ShieldedError> {
    let circuit = shielded_spend_circuit();
    let (trace, pis) = generate_shielded_spend_trace(&witness.spend);
    let proof = prove_dsl_zk(&circuit, &trace, &pis)
        .map_err(|e| ShieldedError::ProveFailed { reason: format!("{e}") })?;
    Ok(ShieldedInputProof {
        nullifier: pis[pi::NULLIFIER],
        proof,
    })
}

/// Build a complete shielded transfer's STARK side from per-input witnesses and
/// the output legs. All inputs are pinned to `merkle_root` (the tree they are
/// proven members of). The caller composes the Pedersen conservation proof over
/// `input_legs`/`output_legs` (downstream) to complete value balance.
pub fn prove_shielded_transfer(
    merkle_root: BabyBear,
    witnesses: &[ShieldedTransferWitness],
    output_legs: Vec<ShieldedValueLeg>,
) -> Result<ShieldedTransfer, ShieldedError> {
    if witnesses.is_empty() {
        return Err(ShieldedError::NoInputs);
    }
    let mut inputs = Vec::with_capacity(witnesses.len());
    let mut input_legs = Vec::with_capacity(witnesses.len());
    for w in witnesses {
        // Pin every input's witnessed root to the shared root (the proof binds
        // `merkle_root` as a public input, so a mismatched witness produces a
        // proof that fails `verify_stark_side` against the shared root).
        inputs.push(prove_shielded_input(w)?);
        input_legs.push(w.leg.clone());
    }
    Ok(ShieldedTransfer {
        merkle_root,
        inputs,
        input_legs,
        output_legs,
    })
}

/// Errors from shielded-transfer construction / verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedError {
    /// A shielded transfer must spend at least one input.
    NoInputs,
    /// Proving one input's hidden note-spend proof failed.
    ProveFailed { reason: String },
    /// An input's hidden proof did not verify against the shared root.
    InputProofRejected { input_index: usize, reason: String },
    /// Two inputs carry the same nullifier (in-transfer double-spend).
    DuplicateNullifier { a: usize, b: usize },
}

impl core::fmt::Display for ShieldedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoInputs => write!(f, "shielded transfer has no inputs"),
            Self::ProveFailed { reason } => {
                write!(f, "shielded input proving failed: {reason}")
            }
            Self::InputProofRejected {
                input_index,
                reason,
            } => write!(
                f,
                "shielded input {input_index} proof rejected: {reason}"
            ),
            Self::DuplicateNullifier { a, b } => write!(
                f,
                "shielded inputs {a} and {b} share a nullifier (double-spend)"
            ),
        }
    }
}

impl std::error::Error for ShieldedError {}
