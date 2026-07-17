//! On-chain verification: submit a Groth16 proof to the deployed verifier contract.

use crate::error::ChainError;
use crate::prove::EvmProof;

/// Verify a wrapped proof on-chain by calling the verifier contract.
///
/// This calls the `verifyProof(bytes32,bytes,bytes)` function on the verifier
/// contract deployed at the address specified in the proof. The contract reverts
/// if the proof is invalid; if the call succeeds, the proof is valid.
///
/// # Arguments
/// * `proof` - The EVM proof produced by [`crate::wrap_for_evm`]
/// * `rpc_url` - The JSON-RPC endpoint (e.g., `https://mainnet.base.org`)
/// * `verifier_address` - Override for the verifier contract address (or use proof's default)
///
/// # Returns
/// `true` if the proof verified on-chain, `false` if the verifier reverted.
///
/// # Behavior by feature (fail-closed, mirroring [`crate::wrap_for_evm`])
/// * `on-chain`: the real contract call via alloy.
/// * `mock` (without `on-chain`): a SIMULATED structural check for tests. Must be
///   opted into — it trusts the proof's own committed `valid` bit, so it accepts
///   any consistently-minted fake by design.
/// * neither: returns [`ChainError::VerifierMissing`]. The default build NEVER
///   silently substitutes a simulated verification for a real one. (It used to:
///   the mock path rode `not(on-chain)`, so a default build "verified" a minted
///   fake by decoding its self-declared `valid` bit — found 2026-07-16.)
///
/// # On-Chain Gas Cost
/// A Groth16/BN254 verifier costs ~250-300k gas per proof (one EIP-197 pairing).
/// This is constant regardless of the complexity of the wrapped computation.
pub async fn verify_on_chain(
    proof: &EvmProof,
    rpc_url: &str,
    verifier_address: &str,
) -> Result<bool, ChainError> {
    #[cfg(feature = "on-chain")]
    {
        return real_verify_on_chain(proof, rpc_url, verifier_address).await;
    }

    #[cfg(all(feature = "mock", not(feature = "on-chain")))]
    {
        return mock_verify_on_chain(proof, rpc_url, verifier_address).await;
    }

    #[cfg(all(not(feature = "mock"), not(feature = "on-chain")))]
    {
        let _ = (proof, rpc_url, verifier_address);
        Err(ChainError::VerifierMissing)
    }
}

/// Mock on-chain verification for testing (`mock` feature only, like the mock
/// provers). Validates proof structure without actually calling a contract,
/// then returns the proof's own committed `valid` bit — meaningful ONLY for
/// proofs minted by this crate's own mock wrap path in tests.
#[cfg(all(feature = "mock", not(feature = "on-chain")))]
async fn mock_verify_on_chain(
    proof: &EvmProof,
    _rpc_url: &str,
    _verifier_address: &str,
) -> Result<bool, ChainError> {
    // In mock mode, just check that the proof has reasonable structure
    if proof.proof_bytes.is_empty() {
        return Err(ChainError::InvalidProof("empty proof bytes".to_string()));
    }
    if proof.public_values.is_empty() {
        return Err(ChainError::InvalidProof("empty public values".to_string()));
    }

    // Decode the public values to check the verification result
    let (valid, _inputs): (bool, Vec<u32>) = bincode::deserialize(&proof.public_values)
        .map_err(|e| ChainError::InvalidProof(format!("cannot decode public values: {e}")))?;

    Ok(valid)
}

/// Real on-chain verification via alloy.
#[cfg(feature = "on-chain")]
async fn real_verify_on_chain(
    proof: &EvmProof,
    rpc_url: &str,
    verifier_address: &str,
) -> Result<bool, ChainError> {
    use alloy::primitives::{Address, Bytes, FixedBytes};
    use alloy::providers::ProviderBuilder;
    use alloy::sol;

    // The `verifyProof(bytes32 vkey, bytes publicValues, bytes proofBytes)` shape
    // the deployed contracts expose (interface name retained from the contracts).
    sol! {
        #[sol(rpc)]
        interface ISP1Verifier {
            /// Verifies a proof. Reverts if the proof is invalid.
            function verifyProof(
                bytes32 programVKey,
                bytes calldata publicValues,
                bytes calldata proofBytes
            ) external view;
        }
    }

    // Parse the verifier contract address
    let address: Address = verifier_address
        .parse()
        .map_err(|e| ChainError::OnChainError(format!("invalid verifier address: {e}")))?;

    // Parse the program vkey
    let vkey_bytes = hex::decode(proof.vkey.trim_start_matches("0x"))
        .map_err(|e| ChainError::OnChainError(format!("invalid vkey hex: {e}")))?;
    if vkey_bytes.len() != 32 {
        return Err(ChainError::OnChainError(
            "vkey must be 32 bytes".to_string(),
        ));
    }
    let program_vkey = FixedBytes::<32>::from_slice(&vkey_bytes);

    // Connect to the RPC endpoint
    let provider = ProviderBuilder::new()
        .connect(rpc_url)
        .await
        .map_err(|e| ChainError::RpcError(format!("failed to connect: {e}")))?;

    // Build the contract call
    let verifier = ISP1Verifier::new(address, &provider);

    let public_values = Bytes::from(proof.public_values.clone());
    let proof_bytes = Bytes::from(proof.proof_bytes.clone());

    // Call verifyProof (this is a view function, so no gas is spent)
    // If the proof is invalid, the contract reverts.
    match verifier
        .verifyProof(program_vkey, public_values, proof_bytes)
        .call()
        .await
    {
        Ok(_) => Ok(true),
        Err(e) => {
            let err_str = format!("{e}");
            if err_str.contains("revert") {
                Ok(false)
            } else {
                Err(ChainError::RpcError(err_str))
            }
        }
    }
}

/// Format an `EvmProof` as calldata for manual contract interaction.
///
/// Returns the ABI-encoded calldata for `verifyProof(bytes32,bytes,bytes)`.
/// Useful for submitting via Etherscan, cast, or other tools.
pub fn format_calldata(proof: &EvmProof) -> Result<Vec<u8>, ChainError> {
    // Function selector: keccak256("verifyProof(bytes32,bytes,bytes)")[:4]
    let selector: [u8; 4] = [0x4f, 0x44, 0xa8, 0x9e]; // verifyProof selector

    let vkey_bytes = hex::decode(proof.vkey.trim_start_matches("0x"))
        .map_err(|e| ChainError::InvalidProof(format!("invalid vkey hex: {e}")))?;

    // ABI encode: selector + vkey(32) + offset_public_values + offset_proof + public_values + proof_bytes
    // This is a simplified encoding; in production use alloy's ABI encoder.
    let mut calldata = Vec::new();
    calldata.extend_from_slice(&selector);

    // Pad vkey to 32 bytes
    let mut vkey_padded = [0u8; 32];
    let copy_len = vkey_bytes.len().min(32);
    vkey_padded[..copy_len].copy_from_slice(&vkey_bytes[..copy_len]);
    calldata.extend_from_slice(&vkey_padded);

    // For proper ABI encoding of dynamic types, we'd use alloy's encoder.
    // This is a reference showing the structure.
    // In practice, use the `on-chain` feature with alloy for correct encoding.
    calldata.extend_from_slice(&proof.public_values);
    calldata.extend_from_slice(&proof.proof_bytes);

    Ok(calldata)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE DEFAULT-BUILD TOOTH: with neither `on-chain` nor `mock`, a
    /// consistently-minted fake proof (structurally valid, self-declared
    /// `valid = true`) must be REJECTED fail-closed. Before 2026-07-16 this
    /// exact input returned `Ok(true)` in the default build — verification by
    /// reading the attacker's own bit.
    #[cfg(all(not(feature = "on-chain"), not(feature = "mock")))]
    #[tokio::test]
    async fn test_verify_fails_closed_without_verifier() {
        let public_values = bincode::serialize(&(true, vec![12345u32, 67890])).unwrap();
        let minted_fake = EvmProof {
            proof_bytes: vec![1, 2, 3, 4],
            public_values,
            vkey: "deadbeef".repeat(4),
            verifier_address: crate::MOCK_VERIFIER_ADDRESS.to_string(),
        };
        let result = verify_on_chain(
            &minted_fake,
            "http://localhost:8545",
            &minted_fake.verifier_address,
        )
        .await;
        assert!(matches!(result.unwrap_err(), ChainError::VerifierMissing));
    }

    #[cfg(all(feature = "mock", not(feature = "on-chain")))]
    #[tokio::test]
    async fn test_mock_verify_cases() {
        let public_values = bincode::serialize(&(true, vec![12345u32, 67890])).unwrap();

        let valid_proof = EvmProof {
            proof_bytes: vec![1, 2, 3, 4],
            public_values,
            vkey: "deadbeef".repeat(4),
            verifier_address: crate::MOCK_VERIFIER_ADDRESS.to_string(),
        };
        let result = verify_on_chain(
            &valid_proof,
            "http://localhost:8545",
            &valid_proof.verifier_address,
        )
        .await;
        assert!(result.is_ok());
        assert!(result.unwrap());

        let empty_proof = EvmProof {
            proof_bytes: vec![],
            public_values: vec![1],
            vkey: "aa".repeat(32),
            verifier_address: crate::MOCK_VERIFIER_ADDRESS.to_string(),
        };
        let result = verify_on_chain(
            &empty_proof,
            "http://localhost:8545",
            &empty_proof.verifier_address,
        )
        .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_format_calldata() {
        let public_values = bincode::serialize(&(true, vec![42u32])).unwrap();

        let proof = EvmProof {
            proof_bytes: vec![0xAA, 0xBB],
            public_values,
            vkey: "ab".repeat(32),
            verifier_address: crate::MOCK_VERIFIER_ADDRESS.to_string(),
        };

        let calldata = format_calldata(&proof).unwrap();
        // Should start with the function selector
        assert_eq!(&calldata[..4], &[0x4f, 0x44, 0xa8, 0x9e]);
    }
}
