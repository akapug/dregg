//! Privacy unlinkability integration test: multiple presentations of the same token
//! must not be correlatable by a colluding set of verifiers.
//!
//! The privacy model requires:
//! 1. presentation_tag differs per presentation (fresh randomness each time).
//! 2. fact_commitments differ when blinding is used.
//! 3. The issuer membership proof uses blinded ring mode (different blinded_leaf each time).
//! 4. No fixed identifier leaks through public inputs.

use dregg_circuit::BabyBear;
use dregg_circuit::dsl::predicates::{compute_blinded_fact_commitment, compute_fact_commitment};
use dregg_circuit::poseidon2::hash_fact;
use dregg_sdk::AuthRequest;
use dregg_teasting::agent::{SimAgent, shared_root_key};

/// Same token, same request, two presentations: presentation tags must differ.
#[test]
fn test_presentation_tags_differ_across_presentations() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("privacy-svc");
    let root_token = alice.mint_token_with_key(&root_key, "privacy");

    let request = AuthRequest {
        service: Some("privacy".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    let proof1 = alice.prove_authorization(&root_token, &request).unwrap();
    let proof2 = alice.prove_authorization(&root_token, &request).unwrap();

    // Both proofs should be valid.
    assert!(proof1.is_valid());
    assert!(proof2.is_valid());

    // The presentation tags (public output) MUST differ between presentations.
    // This is what prevents verifiers from correlating "same token presented twice."
    let tag1 = proof1.circuit_proof.public_inputs.presentation_tag;
    let tag2 = proof2.circuit_proof.public_inputs.presentation_tag;
    assert_ne!(
        tag1, tag2,
        "Presentation tags must differ between independent presentations of the same token"
    );
}

/// Blinded fact commitments: same fact, different blinding → different (unlinkable) commitments.
///
/// 2026-07-16: this test previously ended with a "…and both blinded proofs still verify" coda
/// built on `dsl::predicates::{PredicateWitness, prove_predicate, verify_predicate}`, which
/// 8cc7ef821 (the `*_air` shim cleanup) DELETED. The live successor,
/// `dregg_bridge::present::prove_predicate_for_fact`, hardcodes an UNBLINDED
/// `compute_fact_commitment` and exposes no blinding parameter — so a blinded predicate PROOF
/// is currently unprovable and that coda has no live implementation to assert against. The
/// commitment-unlinkability property below is the half that does, and it is now asserted
/// against the real `compute_blinded_fact_commitment` rather than a hand-rolled hash.
/// (Blinded predicate PROVING is dead code — see HORIZONLOG.)
#[test]
fn test_blinded_fact_commitments_unlinkable() {
    let value = 100u32;

    // The raw fact_hash and state_root for one fact.
    let fh = hash_fact(
        BabyBear::new(42),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    let sr = BabyBear::new(99999);

    // Without blinding: a deterministic commitment (correlatable across presentations).
    let fc_unblinded = compute_fact_commitment(fh, sr);

    // The SAME fact, committed under two different blinding factors.
    let fc_blinded1 = compute_blinded_fact_commitment(fh, sr, BabyBear::new(12345));
    let fc_blinded2 = compute_blinded_fact_commitment(fh, sr, BabyBear::new(67890));

    // Unlinkability: blinded commitments of the same fact must differ from each other, and
    // from the unblinded one — otherwise colluding verifiers can correlate presentations.
    assert_ne!(
        fc_blinded1, fc_blinded2,
        "Different blinding → different commitments"
    );
    assert_ne!(
        fc_blinded1, fc_unblinded,
        "Blinded must differ from unblinded"
    );
    assert_ne!(
        fc_blinded2, fc_unblinded,
        "Blinded must differ from unblinded"
    );
}

// NOTE: removed 2 empty #[ignore] placeholder tests (delegation unlinkability,
// timing side-channel) that provided zero runtime value.
