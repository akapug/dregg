//! Proof round-trip integration test: prove → serialize → transmit → deserialize → verify.
//!
//! Tests that proofs survive serialization boundaries — this catches wire protocol
//! binding mismatches and format disagreements between prover and verifier.
//!
//! stark-kill (f04b2dd1e) deleted the hand-STARK engine and with it the legacy
//! `PredicateProof` (+ `prove_predicate`/`verify_predicate`) and
//! `stark::{proof_to_bytes, proof_from_bytes, verify}` these round-trips used to
//! ride. Dispositions:
//! - the predicate-proof postcard round-trips (GTE/LTE/GT/LT/NEQ) and the
//!   predicate proof-size bound died with the `PredicateProof` type — the
//!   descriptor-world predicate proofs live behind `dregg-circuit-prove`
//!   (not a dep of this crate) and their wire shape is exercised by the
//!   presentation-wire round-trip below plus the circuit-prove emit gates;
//! - the raw STARK bytes round-trip is ported onto the surviving Plonky3
//!   Merkle prover (same tooth: a serialized proof must deserialize and the
//!   DESERIALIZED proof must verify);
//! - the presentation-proof wire round-trip survives unchanged (its inner
//!   membership proof now rides the descriptor `DescriptorProofWire` path).

use dregg_circuit::BabyBear;
use dregg_sdk::AuthRequest;
use dregg_teasting::agent::{SimAgent, shared_root_key};

/// STARK proof bytes: prove → postcard bytes → deserialize → verify.
///
/// Builds a Poseidon2-compatible Merkle witness (real hashing), generates a real
/// Plonky3 STARK proof, serializes/deserializes it, then verifies the
/// deserialized proof (and that it still rejects wrong public inputs).
#[test]
fn test_stark_proof_bytes_round_trip() {
    use dregg_circuit::plonky3_prover::{
        DreggProof, generate_sound_merkle_trace, prove_plonky3, verify_plonky3,
    };

    // Build a Poseidon2-compatible Merkle path (depth 4).
    let leaf_hash = BabyBear::new(12345);
    let depth = 4;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        positions.push((i % 4) as u8);
        siblings.push([
            BabyBear::new((i * 7 + 100) as u32),
            BabyBear::new((i * 7 + 200) as u32),
            BabyBear::new((i * 7 + 300) as u32),
        ]);
    }

    // Generate the trace; public inputs are [leaf, root].
    let (trace, public_inputs) = generate_sound_merkle_trace(leaf_hash, &siblings, &positions);
    assert_eq!(public_inputs[0], leaf_hash);

    // Generate a real STARK proof.
    let proof = prove_plonky3(&trace, &public_inputs);

    // Serialize to bytes (simulates wire transmission).
    let bytes = postcard::to_allocvec(&proof).expect("STARK proof should serialize");
    assert!(!bytes.is_empty(), "Serialized proof should be non-empty");

    // Deserialize from bytes.
    let recovered: DreggProof =
        postcard::from_bytes(&bytes).expect("STARK proof should deserialize");

    // Verify the recovered proof using the same public inputs.
    let result = verify_plonky3(&recovered, &public_inputs);
    assert!(
        result.is_ok(),
        "Deserialized STARK proof should verify: {:?}",
        result.err()
    );

    // The deserialized proof must still bind its public inputs: wrong root fails.
    let wrong_pis = vec![public_inputs[0], BabyBear::new(0xBAD)];
    assert!(
        verify_plonky3(&recovered, &wrong_pis).is_err(),
        "Deserialized proof must reject wrong public inputs"
    );
}

/// Presentation proof: full bridge proof survives postcard serialization.
///
/// NOTE: This test documents a known serialization gap: the WirePresentationProof
/// may fail to round-trip via postcard due to nested proof field layout.
/// If this test fails with DeserializeUnexpectedEnd, that's a real wire protocol bug
/// that needs fixing (the prover and verifier disagree on the binary format).
#[test]
fn test_presentation_proof_round_trip() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("roundtrip-svc");
    let root_token = alice.mint_token_with_key(&root_key, "roundtrip");

    let request = AuthRequest {
        service: Some("roundtrip".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    // Generate a full presentation proof.
    let proof = alice.prove_authorization(&root_token, &request).unwrap();
    assert!(proof.is_valid());

    // Convert to wire format (this is what gets transmitted over the network).
    let wire_proof = proof.into_wire_proof();

    // Serialize the wire proof.
    let bytes = postcard::to_allocvec(&wire_proof).expect("wire proof serializes");

    // Deserialize the wire proof.
    let recovered: dregg_bridge::WirePresentationProof =
        postcard::from_bytes(&bytes).expect("wire proof deserializes");

    // Verify the recovered proof's STARK issuer membership proof.
    let real_stark = recovered
        .real_stark_proof
        .as_ref()
        .expect("recovered proof should have real STARK proof");
    assert_eq!(
        real_stark.verify(),
        dregg_circuit::PresentationVerification::Valid,
        "Recovered STARK proof should verify after round-trip"
    );
}
