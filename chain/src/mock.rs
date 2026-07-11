//! Mock utilities for testing the chain integration without a wrap prover.
//!
//! This module provides helpers that simulate the full proving pipeline:
//! STARK proof -> Groth16 wrapping -> EVM verification, all without external dependencies.

use crate::error::ChainError;
use crate::prove::EvmProof;

/// Simulate the full end-to-end flow: generate a STARK proof, wrap it, verify it.
///
/// This is useful for integration testing the API surface without a wrap prover.
pub async fn mock_end_to_end(leaf_hash: u32, merkle_root: u32) -> Result<EvmProof, ChainError> {
    // Build a fake STARK proof with valid header
    let mut stark_proof = b"DREG".to_vec();
    stark_proof.push(1); // version
    // Minimal proof body (not a real proof, but has the right structure for mock)
    stark_proof.extend_from_slice(&[0u8; 64]); // trace commitment
    stark_proof.extend_from_slice(&[0u8; 64]); // constraint commitment
    stark_proof.extend_from_slice(&0u32.to_le_bytes()); // 0 fri commitments
    stark_proof.extend_from_slice(&0u32.to_le_bytes()); // 0 fri final poly
    stark_proof.extend_from_slice(&2u32.to_le_bytes()); // 2 public inputs
    stark_proof.extend_from_slice(&leaf_hash.to_le_bytes());
    stark_proof.extend_from_slice(&merkle_root.to_le_bytes());

    let public_inputs = vec![leaf_hash, merkle_root];

    crate::wrap_for_evm(&stark_proof, &public_inputs).await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_mock_end_to_end() {
        let proof = mock_end_to_end(12345, 67890).await.unwrap();
        assert!(!proof.proof_bytes.is_empty());
        assert!(!proof.public_values.is_empty());

        // Verify the mock proof
        let verified =
            crate::verify_on_chain(&proof, "http://localhost:8545", &proof.verifier_address)
                .await
                .unwrap();
        assert!(verified);
    }
}
