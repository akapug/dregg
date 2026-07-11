//! Proof wrapping: dregg STARK proof -> Groth16 proof for EVM verification.
//!
//! The real wrap prover is the **native gnark FRI-verifier circuit**
//! (`chain/gnark/`, design + milestones in `docs/deos/ETH-NATIVE-WRAP.md`): a
//! BN254 circuit whose constraints ARE `verify_turn_chain_recursive_from_parts`
//! (VK pin + `verify_all_tables` + segment tooth), emitting a ~256-byte
//! Groth16 proof for the Solidity settlement seam. It is not yet wired; until
//! it is, this seam is fail-closed (`ChainError::WrapProverMissing`) unless the
//! `mock` feature explicitly opts into simulated proofs.
//!
//! (The previous SP1 RISC-V-zkVM wrap path was deleted: it verified the
//! pre-Plonky3 `GuestStarkProof` format — an artifact dregg no longer
//! produces — and paid a 1–2 order-of-magnitude interpreter tax. See
//! `docs/deos/ETH-NATIVE-WRAP.md` §1.)

use crate::error::ChainError;
use serde::{Deserialize, Serialize};

/// A Groth16 proof ready for EVM on-chain verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EvmProof {
    /// The Groth16 proof bytes (formatted for the on-chain verifier contract).
    pub proof_bytes: Vec<u8>,
    /// The public values the wrap circuit commits.
    /// Contains: verification_result (bool) + original public inputs.
    pub public_values: Vec<u8>,
    /// Identifier of the wrap circuit's verifying key (binds which circuit was proven).
    pub vkey: String,
    /// The address of the verifier contract to call.
    pub verifier_address: String,
}

/// Generate a Groth16 proof wrapping a dregg STARK proof for EVM verification.
///
/// # Arguments
/// * `stark_proof_bytes` - Serialized STARK proof
/// * `public_inputs` - The public inputs as u32 field limbs
///
/// # Behavior by feature
/// * `mock`: produces a deterministic SIMULATED proof for integration testing.
/// * otherwise: returns [`ChainError::WrapProverMissing`] (fail-closed) — the
///   native gnark wrap prover is not yet wired.
pub async fn wrap_for_evm(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    #[cfg(feature = "mock")]
    {
        return mock_wrap(stark_proof_bytes, public_inputs).await;
    }

    #[cfg(not(feature = "mock"))]
    {
        let _ = (stark_proof_bytes, public_inputs);
        Err(ChainError::WrapProverMissing)
    }
}

/// Mock implementation for development without a wrap prover.
#[cfg(feature = "mock")]
async fn mock_wrap(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    use blake3::Hasher;

    // Validate that the proof bytes look reasonable
    if stark_proof_bytes.len() < 5 || &stark_proof_bytes[0..4] != b"DREG" {
        return Err(ChainError::InvalidProof(
            "invalid proof header (expected DREG magic)".to_string(),
        ));
    }

    // Generate a deterministic mock proof (hash of inputs)
    let mut hasher = Hasher::new();
    hasher.update(b"mock-groth16-proof:");
    hasher.update(stark_proof_bytes);
    for pi in public_inputs {
        hasher.update(&pi.to_le_bytes());
    }
    let mock_proof = hasher.finalize().as_bytes().to_vec();

    // Serialize public values as the wrap circuit would commit them
    let public_values = bincode::serialize(&(true, public_inputs.to_vec()))
        .map_err(|e| ChainError::InvalidProof(e.to_string()))?;

    Ok(EvmProof {
        proof_bytes: mock_proof,
        public_values,
        vkey: crate::MOCK_PROGRAM_VKEY.to_string(),
        verifier_address: crate::MOCK_VERIFIER_ADDRESS.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(feature = "mock"))]
    #[tokio::test]
    async fn test_wrap_fails_closed_without_prover() {
        let result = wrap_for_evm(b"garbage", &[1, 2]).await;
        assert!(matches!(result.unwrap_err(), ChainError::WrapProverMissing));
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_wrap_rejects_invalid_proof() {
        let result = wrap_for_evm(b"garbage", &[1, 2]).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ChainError::InvalidProof(_)));
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_mock_wrap_accepts_valid_header() {
        // Minimal valid-looking proof: DREG magic + version byte + some data
        let mut fake_proof = b"DREG".to_vec();
        fake_proof.push(1);
        fake_proof.extend_from_slice(&[0u8; 100]);

        let result = wrap_for_evm(&fake_proof, &[12345, 67890]).await;
        assert!(result.is_ok());

        let evm_proof = result.unwrap();
        assert!(!evm_proof.proof_bytes.is_empty());
        assert!(!evm_proof.public_values.is_empty());
        assert!(!evm_proof.verifier_address.is_empty());
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_mock_wrap_deterministic() {
        let mut proof = b"DREG".to_vec();
        proof.push(1);
        proof.extend_from_slice(&[42u8; 64]);

        let r1 = wrap_for_evm(&proof, &[1, 2]).await.unwrap();
        let r2 = wrap_for_evm(&proof, &[1, 2]).await.unwrap();
        assert_eq!(r1.proof_bytes, r2.proof_bytes);
    }
}
