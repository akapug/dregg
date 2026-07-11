//! The payoff: a REAL AWS Nitro attestation flows through the dregg
//! `WitnessedPredicate` rail and is accepted as a first-class fact — the same rail
//! the zkTLS/DECO oracle facts ride. Uses the real captured doc, so this proves the
//! whole confidential-execution path against genuine hardware attestation.

use std::sync::Arc;

use dregg_cell::predicate::{PredicateInput, WitnessedPredicateVerifier};
use dregg_cell::tee_attest::{encode_tee_proof, TeeQuoteKind, TeeWitnessedPredicateVerifier};
use dregg_tee_verify::{verify_nitro_core, NitroVerifier};

const REAL_DOC: &[u8] = include_bytes!("data/nitro_att.bin");

#[test]
fn real_nitro_fact_is_accepted_through_the_dregg_rail() {
    // What the verifier will extract from this genuine doc.
    let (claims, _) = verify_nitro_core(REAL_DOC).expect("core verify");
    let pinned_measurement = claims.measurement; // the enclave's code identity
    let bound_commitment = [0xABu8; 32]; // what the enclave bound into user_data

    // Install the REAL Nitro verifier into dregg-cell's fail-closed seam (no freshness
    // bound so the captured fixture verifies forever).
    let rail =
        TeeWitnessedPredicateVerifier::with_verifier(Arc::new(NitroVerifier::without_freshness()));

    let proof = encode_tee_proof(TeeQuoteKind::AwsNitro, REAL_DOC);

    // Accept: pinned measurement matches + report_data is bound to the committed input.
    rail.verify(
        &pinned_measurement,
        &PredicateInput::Slot(&bound_commitment),
        &proof,
    )
    .expect("a genuine Nitro fact for the pinned binary+commitment must be accepted");

    // Reject: wrong pinned binary.
    assert!(
        rail.verify(&[0u8; 32], &PredicateInput::Slot(&bound_commitment), &proof)
            .is_err(),
        "a quote for a different measured binary must be rejected"
    );

    // Reject: report_data not bound to the committed input (replayed / unbound).
    assert!(
        rail.verify(
            &pinned_measurement,
            &PredicateInput::Slot(&[7u8; 32]),
            &proof
        )
        .is_err(),
        "an unbound/replayed report_data must be rejected"
    );
}

#[test]
fn the_rail_fails_closed_without_a_verifier_installed() {
    let rail = TeeWitnessedPredicateVerifier::new();
    let proof = encode_tee_proof(TeeQuoteKind::AwsNitro, REAL_DOC);
    assert!(
        rail.verify(&[0u8; 32], &PredicateInput::Slot(&[0xABu8; 32]), &proof)
            .is_err(),
        "with no vendor verifier installed the rail must fail closed even on a genuine doc"
    );
}
