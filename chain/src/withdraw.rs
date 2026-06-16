//! Withdrawal proof generation: produces SP1-wrapped proofs for on-chain vault withdrawals.
//!
//! When a user wants to withdraw tokens from the DreggVault, they need to prove:
//! 1. They own a valid note in the dregg note tree (Merkle membership)
//! 2. The nullifier is correctly derived from the note (prevents double-spend)
//! 3. The withdrawal amount matches the note's value
//! 4. The recipient address is bound into the proof (prevents front-running)
//!
//! This module generates the STARK proof of these properties, then wraps it in SP1
//! to produce a Groth16 proof suitable for the `DreggVault.withdraw()` call.
//!
//! # Flow
//!
//! ```text
//! User's note (secret: nullifier_key, blinding)
//!     │
//!     v
//! generate_withdrawal_proof()
//!     │
//!     ├─ 1. Compute nullifier = hash(nullifier_key, note_commitment)
//!     ├─ 2. Build STARK proof of note membership + ownership
//!     ├─ 3. Wrap STARK in SP1 (produces Groth16)
//!     │
//!     v
//! EvmProof (ready for vault.withdraw() calldata)
//! ```

use crate::error::ChainError;
use crate::listener::Address;
use crate::prove::EvmProof;
use serde::{Deserialize, Serialize};

/// Parameters for generating a withdrawal proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WithdrawalRequest {
    /// The nullifier for this note (derived from nullifier_key + note_commitment).
    /// Once revealed on-chain, the note is considered spent.
    pub nullifier: [u8; 32],

    /// The note's value in the token's smallest unit.
    pub note_value: u64,

    /// Asset identifier (encoded token address or asset ID).
    pub note_asset: [u8; 20],

    /// Merkle proof of the note's membership in the attested note tree.
    /// Each element is a sibling hash at the corresponding tree level.
    pub merkle_proof: Vec<[u8; 32]>,

    /// The leaf index of the note in the note tree.
    pub leaf_index: u64,

    /// The current attested root of the note tree (the proof is verified against this).
    pub note_tree_root: [u8; 32],

    /// The recipient Ethereum address for the withdrawal.
    pub recipient: Address,

    /// The note commitment (Poseidon2 hash of note contents).
    pub note_commitment: [u8; 32],

    /// Secret values needed to prove ownership (not revealed on-chain):
    /// `nullifier_key` (32 bytes) and `blinding` (32 bytes). These are used by the
    /// STARK prover but NOT included in public outputs.
    pub secrets: WithdrawalSecrets,

    /// The serialized note-membership STARK proof (the `DREG`-format bytes the
    /// circuit crate's prover emits for this note: membership in `note_tree_root`,
    /// correct nullifier derivation, value/recipient binding). The real
    /// (`prove`-feature) path re-verifies this inside the SP1 guest and wraps the
    /// execution in Groth16; the `mock` path ignores it. Empty in mock requests.
    #[serde(default)]
    pub stark_proof_bytes: Vec<u8>,
}

/// Secret witness values for the withdrawal proof (never revealed on-chain).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WithdrawalSecrets {
    /// The nullifier derivation key (private to the note owner).
    pub nullifier_key: [u8; 32],
    /// The blinding factor used in the note commitment.
    pub blinding: [u8; 32],
}

/// The output of withdrawal proof generation, ready for on-chain submission.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WithdrawalProof {
    /// The EVM proof (Groth16 via SP1) ready for vault.withdraw().
    pub evm_proof: EvmProof,
    /// The nullifier that will be revealed on-chain (marks the note as spent).
    pub nullifier: [u8; 32],
    /// The token address for the withdrawal.
    pub token: Address,
    /// The amount to withdraw.
    pub amount: u64,
    /// The recipient address.
    pub recipient: Address,
    /// ABI-encoded calldata for vault.withdraw() (ready to submit).
    pub calldata: Vec<u8>,
}

/// Public values committed by the SP1 guest for withdrawal verification.
///
/// These are checked by the DreggVault contract after proof verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct WithdrawalPublicValues {
    /// Whether the STARK proof verified successfully.
    valid: bool,
    /// The nullifier (derived from nullifier_key + note_commitment).
    nullifier: [u8; 32],
    /// The token address.
    token: [u8; 20],
    /// The withdrawal amount.
    amount: u64,
    /// The recipient address.
    recipient: [u8; 20],
    /// The note tree root the proof was verified against.
    note_tree_root: [u8; 32],
}

/// Generate an SP1-wrapped proof suitable for on-chain withdrawal from the vault.
///
/// This function:
/// 1. Validates the withdrawal request parameters
/// 2. Constructs the STARK proof of note membership + ownership
/// 3. Wraps the STARK in SP1 to produce a Groth16 proof
/// 4. Formats the result as calldata for `vault.withdraw()`
///
/// # Arguments
/// * `request` - The withdrawal parameters including secrets, Merkle proof, and recipient
///
/// # Returns
/// A `WithdrawalProof` containing the EVM proof and formatted calldata.
///
/// # Mock Mode
/// Without the `prove` feature, produces a simulated proof for testing the flow.
pub async fn generate_withdrawal_proof(
    request: &WithdrawalRequest,
) -> Result<WithdrawalProof, ChainError> {
    // Validate request parameters.
    if request.note_value == 0 {
        return Err(ChainError::InvalidProof(
            "withdrawal amount cannot be zero".to_string(),
        ));
    }
    if request.merkle_proof.is_empty() {
        return Err(ChainError::InvalidProof(
            "merkle proof cannot be empty".to_string(),
        ));
    }
    if request.note_tree_root == [0u8; 32] {
        return Err(ChainError::InvalidProof(
            "note tree root cannot be zero".to_string(),
        ));
    }

    // Verify the nullifier derivation locally before generating the expensive proof.
    let expected_nullifier = derive_nullifier(
        &request.secrets.nullifier_key,
        &request.note_commitment,
    );
    if expected_nullifier != request.nullifier {
        return Err(ChainError::InvalidProof(
            "nullifier does not match derivation from secrets".to_string(),
        ));
    }

    #[cfg(feature = "mock")]
    {
        return mock_generate_withdrawal_proof(request).await;
    }

    #[cfg(all(feature = "prove", not(feature = "mock")))]
    {
        return real_generate_withdrawal_proof(request).await;
    }

    #[cfg(not(any(feature = "mock", feature = "prove")))]
    {
        let _ = request;
        Err(ChainError::ToolchainMissing)
    }
}

/// Derive a withdrawal nullifier from the nullifier key and note commitment.
///
/// `nullifier = blake3("dregg-withdrawal-nullifier-v1", nullifier_key || note_commitment)`
///
/// # Why this is a separate domain from `dregg_cell::note::Note::nullifier`
///
/// The protocol-internal nullifier (`cell/src/note.rs`) is a **Poseidon2** hash
/// over the STARK-native field:
///
/// ```text
/// nullifier = poseidon2(commitment_felt || spending_key[8 limbs] || creation_nonce[8 limbs])
/// ```
///
/// (the structure the note-spending AIR's `NoteSpendingWitness::nullifier`
/// verifies). It includes `creation_nonce` so two notes that happen to share an
/// owner + fields + randomness collision-resistantly resolve to distinct
/// nullifiers inside the in-protocol AIR.
///
/// This crate (`dregg-chain`) is the **SP1 / EVM withdrawal** boundary. Its
/// nullifier matches what the SP1 guest commits as a public output for the
/// `DreggVault` contract on EVM — a different circuit with a different
/// public-input layout, hashed with BLAKE3 because that is what the EVM-side
/// guest and contract verify. The two are doubly separated: a different hash
/// family (BLAKE3 vs Poseidon2) AND a different domain string. Reconciling them
/// into a single derivation would require:
///
///   1. Changing the SP1 guest's PI layout (touches the SP1 circuit, which
///      lives outside this workspace) and re-deploying the EVM verifier.
///   2. Routing `creation_nonce` through `WithdrawalRequest` (currently it
///      only carries the post-hashed `note_commitment` because that's what
///      the EVM contract sees).
///
/// AUDIT-nullifiers.md §6: this is the **intentionally distinct** EVM-side
/// nullifier domain. The domain separator string `"dregg-withdrawal-nullifier-v1"`
/// makes the separation explicit at the hash-domain level so no proof from one
/// scheme can be replayed as the other. Callers operating on
/// `dregg_cell::Note` values MUST use `Note::nullifier`, not this function.
pub fn derive_nullifier(nullifier_key: &[u8; 32], note_commitment: &[u8; 32]) -> [u8; 32] {
    let mut input = Vec::with_capacity(64);
    input.extend_from_slice(nullifier_key);
    input.extend_from_slice(note_commitment);
    // Domain-separated from `dregg-note nullifier v1` (see doc-comment above).
    blake3::derive_key("dregg-withdrawal-nullifier-v1", &input)
}

/// Mock implementation of withdrawal proof generation.
#[cfg(feature = "mock")]
async fn mock_generate_withdrawal_proof(
    request: &WithdrawalRequest,
) -> Result<WithdrawalProof, ChainError> {
    use blake3::Hasher;

    // Build the public values that the SP1 guest would commit.
    let public_values = WithdrawalPublicValues {
        valid: true,
        nullifier: request.nullifier,
        token: request.note_asset,
        amount: request.note_value,
        recipient: request.recipient,
        note_tree_root: request.note_tree_root,
    };
    let public_values_bytes = bincode::serialize(&public_values)
        .map_err(|e| ChainError::InvalidProof(format!("serialization error: {e}")))?;

    // Generate a deterministic mock Groth16 proof.
    let mut hasher = Hasher::new();
    hasher.update(b"mock-withdrawal-groth16:");
    hasher.update(&request.nullifier);
    hasher.update(&request.note_commitment);
    hasher.update(&request.recipient);
    hasher.update(&request.note_value.to_le_bytes());
    let mock_proof_bytes = hasher.finalize().as_bytes().to_vec();

    let evm_proof = EvmProof {
        proof_bytes: mock_proof_bytes,
        public_values: public_values_bytes,
        vkey: crate::SP1_PROGRAM_VKEY.to_string(),
        verifier_address: crate::contracts::BASE_MAINNET.to_string(),
    };

    // Build the ABI-encoded calldata for vault.withdraw().
    // In production, use alloy's ABI encoder. Here we build a simplified version.
    let calldata = encode_withdraw_calldata(
        &request.note_asset,
        request.note_value,
        &request.recipient,
        &evm_proof,
    );

    Ok(WithdrawalProof {
        evm_proof,
        nullifier: request.nullifier,
        token: request.note_asset,
        amount: request.note_value,
        recipient: request.recipient,
        calldata,
    })
}

/// Real withdrawal-proof generation (requires the `prove` feature + SP1 toolchain).
///
/// The structured note-membership STARK proof in `request.stark_proof_bytes` is
/// re-verified inside the SP1 guest and wrapped to a Groth16/BN254 receipt by the
/// shared [`crate::prove::wrap_for_evm`] path (the same real wrapper `wrap_for_evm`
/// uses for the trust bridge — there is exactly one SP1 wrap in this crate). The
/// withdrawal's public inputs (nullifier · token · amount · recipient · note-tree
/// root, as field-limb `u32`s) are bound as the guest's public values, so the
/// `DreggVault.withdraw()` call verifies the same claim on-chain.
///
/// Returns [`ChainError::InvalidProof`] if the request carries no STARK proof to
/// wrap (the real path cannot fabricate one — that is the `mock` path's job).
#[cfg(all(feature = "prove", not(feature = "mock")))]
async fn real_generate_withdrawal_proof(
    request: &WithdrawalRequest,
) -> Result<WithdrawalProof, ChainError> {
    if request.stark_proof_bytes.is_empty() {
        return Err(ChainError::InvalidProof(
            "real withdrawal proving requires request.stark_proof_bytes (the \
             note-membership STARK proof from the circuit crate); none supplied"
                .to_string(),
        ));
    }

    // The public inputs the on-chain vault binds, as u32 field limbs. Order is
    // fixed and mirrored by `WithdrawalPublicValues` / the contract decode.
    let public_inputs = withdrawal_public_inputs(request);

    // The single real SP1 wrap: guest re-verifies the STARK, Groth16-wraps it.
    let evm_proof = crate::prove::wrap_for_evm(&request.stark_proof_bytes, &public_inputs).await?;

    let calldata = encode_withdraw_calldata(
        &request.note_asset,
        request.note_value,
        &request.recipient,
        &evm_proof,
    );

    Ok(WithdrawalProof {
        evm_proof,
        nullifier: request.nullifier,
        token: request.note_asset,
        amount: request.note_value,
        recipient: request.recipient,
        calldata,
    })
}

/// The withdrawal public inputs as `u32` field limbs, in the canonical order the
/// guest commits and the `DreggVault` contract decodes: nullifier (8) · token (5)
/// · amount (2) · recipient (5) · note-tree root (8). Each 32-byte hash is read as
/// 8 big-endian `u32` limbs; each 20-byte address as 5; the `u64` amount as 2.
#[cfg(all(feature = "prove", not(feature = "mock")))]
fn withdrawal_public_inputs(request: &WithdrawalRequest) -> Vec<u32> {
    let mut pis = Vec::with_capacity(8 + 5 + 2 + 5 + 8);
    push_be_u32_limbs(&mut pis, &request.nullifier);
    push_be_u32_limbs(&mut pis, &request.note_asset);
    pis.push((request.note_value >> 32) as u32);
    pis.push(request.note_value as u32);
    push_be_u32_limbs(&mut pis, &request.recipient);
    push_be_u32_limbs(&mut pis, &request.note_tree_root);
    pis
}

/// Append `bytes` as big-endian `u32` limbs (4 bytes each). `bytes.len()` need not
/// be a multiple of 4; a trailing partial limb is right-padded with zeros.
#[cfg(all(feature = "prove", not(feature = "mock")))]
fn push_be_u32_limbs(out: &mut Vec<u32>, bytes: &[u8]) {
    for chunk in bytes.chunks(4) {
        let mut limb = [0u8; 4];
        limb[..chunk.len()].copy_from_slice(chunk);
        out.push(u32::from_be_bytes(limb));
    }
}

/// Encode the calldata for `vault.withdraw(address token, uint256 amount, address recipient, bytes sp1Proof)`.
///
/// This produces the raw bytes that can be sent as transaction data to the vault contract.
fn encode_withdraw_calldata(
    token: &Address,
    amount: u64,
    recipient: &Address,
    proof: &EvmProof,
) -> Vec<u8> {
    // Function selector: keccak256("withdraw(address,uint256,address,bytes)")[:4]
    // In mock mode we use a placeholder; in production alloy computes this.
    let selector: [u8; 4] = [0x9a, 0x03, 0x14, 0x2c]; // placeholder

    let mut calldata = Vec::new();
    calldata.extend_from_slice(&selector);

    // ABI-encode token address (left-padded to 32 bytes)
    let mut token_padded = [0u8; 32];
    token_padded[12..32].copy_from_slice(token);
    calldata.extend_from_slice(&token_padded);

    // ABI-encode amount (uint256, big-endian)
    let mut amount_bytes = [0u8; 32];
    amount_bytes[24..32].copy_from_slice(&amount.to_be_bytes());
    calldata.extend_from_slice(&amount_bytes);

    // ABI-encode recipient (left-padded to 32 bytes)
    let mut recipient_padded = [0u8; 32];
    recipient_padded[12..32].copy_from_slice(recipient);
    calldata.extend_from_slice(&recipient_padded);

    // ABI-encode sp1Proof as bytes (offset + length + data)
    // Simplified: just append the proof bytes. Full ABI encoding uses offsets.
    let sp1_proof_inner = encode_sp1_proof_bytes(proof);
    let offset: u64 = 128; // 4 slots * 32 bytes
    let mut offset_bytes = [0u8; 32];
    offset_bytes[24..32].copy_from_slice(&offset.to_be_bytes());
    calldata.extend_from_slice(&offset_bytes);

    // Length of sp1Proof bytes
    let proof_len = sp1_proof_inner.len() as u64;
    let mut len_bytes = [0u8; 32];
    len_bytes[24..32].copy_from_slice(&proof_len.to_be_bytes());
    calldata.extend_from_slice(&len_bytes);

    // The proof data itself
    calldata.extend_from_slice(&sp1_proof_inner);

    calldata
}

/// Encode the SP1 proof as the vault contract expects: abi.encode(proofBytes, publicValues).
fn encode_sp1_proof_bytes(proof: &EvmProof) -> Vec<u8> {
    // Simplified ABI encoding of (bytes, bytes).
    // In production, use alloy's encoder for correctness.
    let mut encoded = Vec::new();
    encoded.extend_from_slice(&proof.proof_bytes);
    encoded.extend_from_slice(&proof.public_values);
    encoded
}

/// Verify a withdrawal proof locally (for testing before on-chain submission).
///
/// Checks that the proof structure is well-formed and the public values are consistent.
pub fn verify_withdrawal_proof_locally(proof: &WithdrawalProof) -> Result<bool, ChainError> {
    if proof.evm_proof.proof_bytes.is_empty() {
        return Err(ChainError::InvalidProof("empty proof bytes".to_string()));
    }
    if proof.evm_proof.public_values.is_empty() {
        return Err(ChainError::InvalidProof(
            "empty public values".to_string(),
        ));
    }

    // Decode the public values.
    let values: WithdrawalPublicValues =
        bincode::deserialize(&proof.evm_proof.public_values)
            .map_err(|e| ChainError::InvalidProof(format!("cannot decode public values: {e}")))?;

    // Check consistency.
    if values.nullifier != proof.nullifier {
        return Err(ChainError::InvalidProof(
            "nullifier mismatch".to_string(),
        ));
    }
    if values.amount != proof.amount {
        return Err(ChainError::InvalidProof("amount mismatch".to_string()));
    }
    if values.recipient != proof.recipient {
        return Err(ChainError::InvalidProof(
            "recipient mismatch".to_string(),
        ));
    }
    if values.token != proof.token {
        return Err(ChainError::InvalidProof("token mismatch".to_string()));
    }

    Ok(values.valid)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mock_request() -> WithdrawalRequest {
        let nullifier_key = [0x11; 32];
        let blinding = [0x22; 32];
        let note_commitment = [0x33; 32];
        let nullifier = derive_nullifier(&nullifier_key, &note_commitment);

        WithdrawalRequest {
            nullifier,
            note_value: 1_000_000,
            note_asset: [0x44; 20],
            merkle_proof: vec![[0x55; 32], [0x66; 32], [0x77; 32]],
            leaf_index: 42,
            note_tree_root: [0x88; 32],
            recipient: [0x99; 20],
            note_commitment,
            secrets: WithdrawalSecrets {
                nullifier_key,
                blinding,
            },
            // Mock requests carry no real STARK proof; the mock path ignores it.
            stark_proof_bytes: Vec::new(),
        }
    }

    #[test]
    fn test_derive_nullifier_properties() {
        let key = [0x42; 32];
        let commitment = [0xAA; 32];

        // Deterministic
        let n1 = derive_nullifier(&key, &commitment);
        let n2 = derive_nullifier(&key, &commitment);
        assert_eq!(n1, n2);

        // Different inputs -> different outputs
        let c2 = [0xBB; 32];
        let n3 = derive_nullifier(&key, &c2);
        assert_ne!(n1, n3);
    }

    /// Adversarial: the EVM-side withdrawal nullifier MUST be in a different
    /// hash domain than the in-protocol `Note::nullifier`. The in-protocol
    /// nullifier is a Poseidon2 hash over BabyBear (see
    /// `dregg_cell::note::Note::nullifier`), so it is already in an entirely
    /// different hash family from this BLAKE3-based EVM nullifier — the
    /// strongest possible separation. As a belt-and-suspenders check we ALSO
    /// confirm the EVM nullifier does not collide with the *legacy* BLAKE3
    /// `"dregg-note nullifier v1"` domain string (the chain crate is standalone
    /// and cannot depend on `dregg-cell`, so that string is reproduced here),
    /// guarding the domain-separator layer independently of the hash family.
    ///
    /// This guards against an attacker reusing a withdrawal proof's revealed
    /// nullifier to fake an in-protocol spend (or vice-versa).
    /// See `dregg_cell::note::Note::nullifier` for the canonical scheme.
    #[test]
    fn test_withdrawal_nullifier_domain_separated_from_in_protocol() {
        let key = [0x42; 32];
        let commitment = [0xAA; 32];
        let creation_nonce = [0xBB; 32];

        // EVM-side withdrawal nullifier (this module).
        let evm_nullifier = derive_nullifier(&key, &commitment);

        // The legacy in-protocol BLAKE3 nullifier domain string, reproduced
        // locally for the domain-separator cross-check (NOT the live scheme,
        // which is now Poseidon2):
        //   blake3::derive_key("dregg-note nullifier v1",
        //                      commitment || spending_key || creation_nonce)
        let mut input = Vec::with_capacity(96);
        input.extend_from_slice(&commitment);
        input.extend_from_slice(&key);
        input.extend_from_slice(&creation_nonce);
        let in_protocol_nullifier = blake3::derive_key("dregg-note nullifier v1", &input);

        assert_ne!(
            evm_nullifier, in_protocol_nullifier,
            "EVM withdrawal nullifier must NOT collide with in-protocol Note::nullifier — \
             cross-domain replay protection"
        );

        // Even with zero creation_nonce (i.e. the input order-difference being
        // the only distinguisher), the domain separator string differs, so the
        // outputs must still differ.
        let mut input_zero_nonce = Vec::with_capacity(96);
        input_zero_nonce.extend_from_slice(&commitment);
        input_zero_nonce.extend_from_slice(&key);
        input_zero_nonce.extend_from_slice(&[0u8; 32]);
        let in_protocol_zero =
            blake3::derive_key("dregg-note nullifier v1", &input_zero_nonce);
        assert_ne!(
            evm_nullifier, in_protocol_zero,
            "domain separator alone must prevent cross-domain collision"
        );
    }

    #[tokio::test]
    async fn test_generate_withdrawal_proof_rejects_invalid() {
        let mut req = mock_request();
        req.note_value = 0;
        assert!(generate_withdrawal_proof(&req).await.is_err());

        let mut req = mock_request();
        req.merkle_proof = vec![];
        assert!(generate_withdrawal_proof(&req).await.is_err());

        let mut req = mock_request();
        req.nullifier = [0xFF; 32]; // Doesn't match derivation
        assert!(generate_withdrawal_proof(&req).await.is_err());
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_mock_generate_withdrawal_proof_succeeds() {
        let req = mock_request();
        let result = generate_withdrawal_proof(&req).await;
        assert!(result.is_ok());

        let proof = result.unwrap();
        assert_eq!(proof.nullifier, req.nullifier);
        assert_eq!(proof.amount, 1_000_000);
        assert_eq!(proof.recipient, [0x99; 20]);
        assert!(!proof.evm_proof.proof_bytes.is_empty());
        assert!(!proof.calldata.is_empty());
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_verify_withdrawal_proof_locally() {
        let req = mock_request();
        let proof = generate_withdrawal_proof(&req).await.unwrap();
        let verified = verify_withdrawal_proof_locally(&proof).unwrap();
        assert!(verified);
    }

    // ── teeth on the REAL (`--features prove`) path — fast + deterministic,
    //    exercising the reachable logic without an actual (minutes-long) SP1 prove.

    /// REJECT polarity on the real path: with no `stark_proof_bytes`, real
    /// withdrawal proving fails closed (it cannot fabricate a membership proof) —
    /// it must NOT silently succeed or fall through to a mock.
    #[cfg(all(feature = "prove", not(feature = "mock")))]
    #[tokio::test]
    async fn test_real_generate_rejects_missing_stark_proof() {
        let req = mock_request(); // stark_proof_bytes is empty
        assert!(req.stark_proof_bytes.is_empty());
        let err = real_generate_withdrawal_proof(&req).await.unwrap_err();
        assert!(
            matches!(err, ChainError::InvalidProof(_)),
            "missing STARK proof must be InvalidProof, got {err:?}"
        );
    }

    /// The public-input limb layout the on-chain `DreggVault` decodes: exactly
    /// 8(nullifier)+5(token)+2(amount)+5(recipient)+8(root) = 28 `u32`s, with the
    /// `u64` amount split into its two big-endian halves at the fixed offset. A
    /// changed nullifier MUST change the bound public inputs (they are load-bearing).
    #[cfg(all(feature = "prove", not(feature = "mock")))]
    #[test]
    fn test_withdrawal_public_inputs_layout_and_binding() {
        let req = mock_request();
        let pis = withdrawal_public_inputs(&req);
        assert_eq!(pis.len(), 8 + 5 + 2 + 5 + 8, "fixed PI limb count");

        // nullifier = [0x..;32] occupies limbs 0..8 as BE u32s.
        let n0 = u32::from_be_bytes(req.nullifier[0..4].try_into().unwrap());
        assert_eq!(pis[0], n0, "first nullifier limb is BE");

        // amount = 1_000_000 (< 2^32): high half 0, low half = amount, at offset 13.
        let amt_off = 8 + 5;
        assert_eq!(pis[amt_off], 0, "amount high u32 limb");
        assert_eq!(pis[amt_off + 1], 1_000_000u32, "amount low u32 limb");

        // A 64-bit amount with high bits set splits correctly.
        let mut big = mock_request();
        big.note_value = 0x1234_5678_9ABC_DEF0;
        let pb = withdrawal_public_inputs(&big);
        assert_eq!(pb[amt_off], 0x1234_5678, "high half of u64 amount");
        assert_eq!(pb[amt_off + 1], 0x9ABC_DEF0, "low half of u64 amount");

        // Binding: flipping the nullifier changes the bound public inputs.
        let mut tampered = mock_request();
        tampered.nullifier[0] ^= 0x01;
        assert_ne!(
            withdrawal_public_inputs(&tampered),
            pis,
            "a different nullifier MUST yield different on-chain public inputs"
        );
    }
}
