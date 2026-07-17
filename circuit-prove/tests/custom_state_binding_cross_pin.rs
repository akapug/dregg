//! **THE DRIFT GUARD** for the custom-proof PI commitment's two homes.
//!
//! `dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment` is what the
//! FOLD's custom leaf computes in-circuit and the binding node `connect`s. The verify
//! floor (`dregg-turn`'s executor) must recompute the SAME value from a wire sub-proof's
//! public inputs to enforce the state-binding weld — but `dregg-circuit` cannot depend on
//! `dregg-circuit-prove` (the verify floor must not pull the prover), so
//! `dregg_circuit::effect_vm::custom_state_binding::custom_proof_pi_commitment_8` is a
//! byte-identical twin.
//!
//! If the two ever drift, the executor would compute a commitment the fold never binds:
//! every honest custom turn would be refused (fail-closed, not a soundness hole — but a
//! silent liveness break). This test fails loudly instead. Same posture as the existing
//! `dfa_route_commitment` cross-pin.

use dregg_circuit::effect_vm::custom_state_binding as verify_side;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_proof_bind as prove_side;

#[test]
fn the_domain_separators_are_identical() {
    assert_eq!(
        verify_side::CUSTOM_PROOF_PI_DOMAIN,
        prove_side::CUSTOM_PROOF_PI_DOMAIN,
        "the verify-floor twin's domain drifted from the fold's — the executor would \
         recompute a commitment the fold never binds"
    );
}

#[test]
fn the_commitment_derivations_are_byte_identical() {
    // Cover the shapes that matter: empty, sub-rate, exactly the state prefix, and a
    // multi-chunk vector (the sponge's absorb loop must agree, not just one block).
    for len in [0usize, 1, 4, 8, 16, 17, 32, 64] {
        let pis: Vec<BabyBear> = (0..len).map(|j| BabyBear::new(1_234 + j as u32)).collect();
        assert_eq!(
            verify_side::custom_proof_pi_commitment_8(&pis),
            prove_side::custom_proof_pi_commitment(&pis),
            "custom PI commitment drifted between the verify floor and the fold at \
             len={len}"
        );
    }
}

/// The width the verify floor assumes IS the width the fold's binding node connects.
#[test]
fn the_commitment_widths_agree() {
    assert_eq!(
        prove_side::PROOF_BIND_COMMIT_WIDTH,
        8,
        "the fold binds an 8-felt commitment"
    );
    let pis = vec![BabyBear::new(1); 20];
    assert_eq!(
        verify_side::custom_proof_pi_commitment_8(&pis).len(),
        prove_side::PROOF_BIND_COMMIT_WIDTH,
        "the verify floor's commitment width must equal the fold's connected claim width"
    );
}

/// The state-binding prefix fits inside a real custom PI vector without colliding with
/// the commitment machinery: the commitment covers the WHOLE vector, prefix included.
#[test]
fn the_state_prefix_rides_the_folds_commitment() {
    let old: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(100 + j as u32));
    let new: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(200 + j as u32));
    let mut pis = verify_side::custom_pi_state_prefix(&old, &new).to_vec();
    pis.extend_from_slice(&[BabyBear::new(5), BabyBear::new(6)]);

    // The value the fold's leaf computes in-circuit already covers the state roots.
    let folded = prove_side::custom_proof_pi_commitment(&pis);
    assert_eq!(
        folded,
        verify_side::custom_proof_pi_commitment_8(&pis),
        "the fold's in-circuit commitment must cover the state-binding prefix"
    );

    // And it MOVES when the post-root is forged — so the prefix is genuinely under the
    // commitment the fold connects, not appended beside it.
    let mut forged = pis.clone();
    forged[verify_side::CUSTOM_PI_NEW_COMMIT_BASE] = BabyBear::new(999);
    assert_ne!(
        prove_side::custom_proof_pi_commitment(&forged),
        folded,
        "a forged post-state root must move the commitment the fold binds"
    );
}
