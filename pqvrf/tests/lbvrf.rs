use pqvrf::{
    CHALLENGE_WEIGHT, EvalError, MAX_EVALUATIONS, MODULUS_P, RESPONSE_BOUND, eval, keygen, verify,
};

const SEED: [u8; 32] = [0x42; 32];
const INPUT: &[u8] = b"dregg leader sortition / epoch 7 / round 19";

#[test]
fn honest_evaluation_verifies() {
    let (public_key, mut secret_key) = keygen(&SEED);
    let (output, proof) = eval(&mut secret_key, INPUT).expect("one-time evaluation");
    assert!(verify(&public_key, INPUT, &output, &proof));
}

#[test]
fn uniqueness_no_second_output_verifies() {
    let (public_key, mut secret_key) = keygen(&SEED);
    let (output, proof) = eval(&mut secret_key, INPUT).expect("one-time evaluation");
    assert!(verify(&public_key, INPUT, &output, &proof));

    // Exercise every output coordinate in both directions. None of these 64
    // distinct values may be admitted for the same (pk,input) and proof.
    for coordinate in 0..output.coefficients.len() {
        for delta in [1_u32, MODULUS_P - 1] {
            let mut second = output.clone();
            second.coefficients[coordinate] = (second.coefficients[coordinate] + delta) % MODULUS_P;
            assert_ne!(second, output);
            assert!(!verify(&public_key, INPUT, &second, &proof));
        }
    }
}

#[test]
fn forged_proof_and_wrong_output_are_rejected() {
    let (public_key, mut secret_key) = keygen(&SEED);
    let (output, proof) = eval(&mut secret_key, INPUT).expect("one-time evaluation");

    let mut forged = proof.clone();
    let nonzero = forged
        .challenge
        .coefficients
        .iter()
        .position(|&coefficient| coefficient != 0)
        .expect("challenge has nonzero coefficients");
    forged.challenge.coefficients[nonzero] *= -1;
    assert_eq!(
        forged
            .challenge
            .coefficients
            .iter()
            .filter(|&&coefficient| coefficient != 0)
            .count(),
        CHALLENGE_WEIGHT
    );
    assert!(!verify(&public_key, INPUT, &output, &forged));

    let mut wrong_output = output.clone();
    wrong_output.coefficients[0] = (wrong_output.coefficients[0] + 1) % MODULUS_P;
    assert!(!verify(&public_key, INPUT, &wrong_output, &proof));
    assert!(!verify(&public_key, b"wrong input", &output, &proof));
}

#[test]
fn norm_bound_violations_are_rejected() {
    let (public_key, mut secret_key) = keygen(&SEED);
    let (output, mut proof) = eval(&mut secret_key, INPUT).expect("one-time evaluation");
    proof.response[0].coefficients[0] = RESPONSE_BOUND + 1;
    assert!(!verify(&public_key, INPUT, &output, &proof));
}

#[test]
fn malformed_challenge_is_rejected() {
    let (public_key, mut secret_key) = keygen(&SEED);
    let (output, mut proof) = eval(&mut secret_key, INPUT).expect("one-time evaluation");
    proof.challenge.coefficients[0] = 2;
    assert!(!verify(&public_key, INPUT, &output, &proof));
}

#[test]
fn evaluation_is_deterministic() {
    let (public_key_a, mut secret_key_a) = keygen(&SEED);
    let (public_key_b, mut secret_key_b) = keygen(&SEED);
    let evaluation_a = eval(&mut secret_key_a, INPUT).expect("first evaluation");
    let evaluation_b = eval(&mut secret_key_b, INPUT).expect("second derivation");
    assert_eq!(public_key_a, public_key_b);
    assert_eq!(evaluation_a, evaluation_b);
}

#[test]
fn few_time_bound_is_enforced() {
    let (_public_key, mut secret_key) = keygen(&SEED);
    assert_eq!(secret_key.evaluations_remaining(), MAX_EVALUATIONS);
    eval(&mut secret_key, INPUT).expect("the one permitted evaluation");
    assert_eq!(secret_key.evaluations_used(), MAX_EVALUATIONS);
    assert_eq!(secret_key.evaluations_remaining(), 0);
    assert_eq!(
        eval(&mut secret_key, b"a second input"),
        Err(EvalError::EvaluationLimitExceeded)
    );
}

#[test]
fn project_known_answer_fingerprint() {
    // The paper does not publish a byte-level KAT. This project-local vector
    // locks the complete BLAKE3 instantiation (matrix, key, value, and proof).
    let (public_key, mut secret_key) = keygen(&SEED);
    let (output, proof) = eval(&mut secret_key, INPUT).expect("known-answer evaluation");
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pqvrf.project-kat.v1");
    for polynomial in &public_key.t {
        for coefficient in polynomial.coefficients {
            hasher.update(&coefficient.to_le_bytes());
        }
    }
    for coefficient in output.coefficients {
        hasher.update(&coefficient.to_le_bytes());
    }
    for polynomial in &proof.response {
        for coefficient in polynomial.coefficients {
            hasher.update(&coefficient.to_le_bytes());
        }
    }
    for coefficient in proof.challenge.coefficients {
        hasher.update(&coefficient.to_le_bytes());
    }
    assert_eq!(
        hasher.finalize().to_hex().as_str(),
        "8aae76a04df9ce54c93512fd7debef153c368b6aaa5808df1594ab21b37b9b3e"
    );
}
