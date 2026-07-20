//! Executable teeth for the first active fhIR prox product.
//!
//! Inputs and outputs remain mod-`t` shared.  The test driver checks correctness
//! only through the module's equality-bit boundary; it has no output-share
//! accessor and never reconstructs a projected value.

use std::time::Duration;

use fhegg_fhe::fhir::private_box::{
    project_private_box, BoxBranch, PartyBoxInput, PrivateBoxError, PrivateBoxSession,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

const N: usize = 3;
const BITS: usize = 16;
const T: u64 = 1 << BITS;

fn session(candidate: u8, input_bound: u64) -> PrivateBoxSession {
    PrivateBoxSession::new(
        [0xf1; 32],
        [candidate; 32],
        N,
        BITS,
        T,
        input_bound,
        100,
        1_000,
        Duration::from_secs(3),
    )
    .expect("valid private box session")
}

fn share_mod_t(value: u64, seed: u64) -> Vec<u64> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut shares = (0..N - 1).map(|_| rng.gen_range(0..T)).collect::<Vec<_>>();
    let partial = shares.iter().fold(0u64, |sum, &share| (sum + share) % T);
    shares.push((value + T - partial) % T);
    shares
}

fn project(value: u64, candidate: u8) -> (BoxBranch, bool, bool) {
    let session = session(candidate, 60_000);
    let inputs = share_mod_t(value, u64::from(candidate) ^ value)
        .into_iter()
        .enumerate()
        .map(|(party, share)| PartyBoxInput::new(&session, party, share).unwrap())
        .collect();
    let run = project_private_box(&session, inputs).expect("active private projection");
    let expected = value.clamp(100, 1_000);
    let correct = run
        .verify_public_output(expected)
        .expect("output-only equality check");
    let wrong = run
        .verify_public_output(expected ^ 1)
        .expect("wrong output-only equality check");
    (run.branch(), correct.is_equal(), wrong.is_equal())
}

#[test]
fn active_lower_interior_and_upper_projection_are_exact_without_opening_output() {
    for (value, branch) in [
        (42, BoxBranch::Lower),
        (100, BoxBranch::Interior),
        (500, BoxBranch::Interior),
        (1_000, BoxBranch::Interior),
        (1_200, BoxBranch::Upper),
    ] {
        let (got_branch, correct, wrong) = project(value, value as u8);
        assert_eq!(got_branch, branch, "wrong branch for input {value}");
        assert!(correct, "projected output differs for input {value}");
        assert!(!wrong, "wrong public candidate accepted for input {value}");
    }
}

#[test]
fn projected_shares_chain_into_a_candidate_bound_second_box_without_opening() {
    let first = session(0x51, 60_000);
    let inputs = share_mod_t(1_200, 0x5151)
        .into_iter()
        .enumerate()
        .map(|(party, share)| PartyBoxInput::new(&first, party, share).unwrap())
        .collect();
    let first_run = project_private_box(&first, inputs).expect("first active box");
    assert_eq!(first_run.branch(), BoxBranch::Upper);
    let binding = first_run.output_binding_digest();
    let second = PrivateBoxSession::new(
        first.program_digest(),
        binding,
        N,
        BITS,
        T,
        1_000,
        200,
        800,
        Duration::from_secs(3),
    )
    .expect("candidate-bound second box");
    let second_run = first_run
        .project_again(&second)
        .expect("private output chains without share access");
    assert_eq!(second_run.branch(), BoxBranch::Upper);
    assert!(second_run
        .verify_public_output(800)
        .expect("second output equality")
        .is_equal());

    let first = session(0x52, 60_000);
    let inputs = share_mod_t(500, 0x5252)
        .into_iter()
        .enumerate()
        .map(|(party, share)| PartyBoxInput::new(&first, party, share).unwrap())
        .collect();
    let first_run = project_private_box(&first, inputs).unwrap();
    let unbound_next = PrivateBoxSession::new(
        first.program_digest(),
        [0xff; 32],
        N,
        BITS,
        T,
        1_000,
        200,
        800,
        Duration::from_secs(3),
    )
    .unwrap();
    assert!(matches!(
        first_run.project_again(&unbound_next),
        Err(PrivateBoxError::CandidateChainMismatch)
    ));
}

#[test]
fn range_roster_session_and_canonical_domain_fail_closed() {
    let valid = session(0x71, 10_000);

    let out_of_range = share_mod_t(10_001, 0x7101)
        .into_iter()
        .enumerate()
        .map(|(party, share)| PartyBoxInput::new(&valid, party, share).unwrap())
        .collect();
    assert!(matches!(
        project_private_box(&valid, out_of_range),
        Err(PrivateBoxError::InputOutOfRange)
    ));

    let missing = share_mod_t(500, 0x7102)
        .into_iter()
        .take(N - 1)
        .enumerate()
        .map(|(party, share)| PartyBoxInput::new(&valid, party, share).unwrap())
        .collect();
    assert!(matches!(
        project_private_box(&valid, missing),
        Err(PrivateBoxError::MissingParties { have: 2, need: N })
    ));

    let duplicate = vec![
        PartyBoxInput::new(&valid, 0, 7).unwrap(),
        PartyBoxInput::new(&valid, 0, 11).unwrap(),
        PartyBoxInput::new(&valid, 2, 13).unwrap(),
    ];
    assert!(matches!(
        project_private_box(&valid, duplicate),
        Err(PrivateBoxError::DuplicateParty { party: 0 })
    ));

    let other = session(0x72, 10_000);
    assert_ne!(valid.session_id(), other.session_id());
    let wrong_session = share_mod_t(500, 0x7103)
        .into_iter()
        .enumerate()
        .map(|(party, share)| PartyBoxInput::new(&valid, party, share).unwrap())
        .collect();
    assert!(matches!(
        project_private_box(&other, wrong_session),
        Err(PrivateBoxError::SessionMismatch)
    ));

    assert!(matches!(
        PartyBoxInput::new(&valid, 0, T),
        Err(PrivateBoxError::NonCanonicalShare { .. })
    ));
    assert!(matches!(
        PrivateBoxSession::new(
            [0xf1; 32],
            [0x73; 32],
            N,
            BITS,
            T + 1,
            10_000,
            100,
            1_000,
            Duration::from_secs(1),
        ),
        Err(PrivateBoxError::PlaintextModulusMustEqualCanonicalDomain { .. })
    ));
    assert!(matches!(
        PrivateBoxSession::new(
            [0xf1; 32],
            [0x74; 32],
            N,
            BITS,
            T,
            999,
            100,
            1_000,
            Duration::from_secs(1),
        ),
        Err(PrivateBoxError::InvalidBounds)
    ));
}
