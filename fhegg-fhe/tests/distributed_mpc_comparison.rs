//! Party-owned strict comparison: mod-t shares in, one ordering bit out.
//!
//! This is the reusable decision organ for private allocation, preference,
//! matchmaking, range windows, and floor-swap predicates. Neither operand nor
//! their difference is reconstructed or retained in the public transcript.

use std::thread;
use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
    InMemoryReplayGuard,
};
use fhegg_fhe::decision_attestation::{
    AttestedComparisonReceipt, AttestedDecisionReceipt, DecisionAttestationError,
    ExpectedComparisonContext,
};
use fhegg_fhe::mpc_party::{
    local_channels, run_party_comparison, simulate_comparison_transcript, trusted_dealer_triples,
    DistributedComparisonRun, PartyComparisonInput, PartyEqualityInput, PartyMpcError,
    PartyMpcSession,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

const N: usize = 3;
const T: u64 = 65_537;
const BITS: usize = 16;

fn share_mod_t(value: u64, rng: &mut StdRng) -> Vec<u64> {
    let mut shares = (0..N - 1).map(|_| rng.gen_range(0..T)).collect::<Vec<_>>();
    let partial = shares.iter().fold(0u64, |acc, &share| (acc + share) % T);
    shares.push((value + T - partial) % T);
    shares
}

fn compare(left: u64, right: u64, seed: u64) -> DistributedComparisonRun {
    assert!(left < 1 << BITS && right < 1 << BITS);
    let session = PartyMpcSession::less_than([seed as u8; 32], N, BITS, T, Duration::from_secs(2))
        .expect("valid strict-comparison session");
    let mut rng = StdRng::seed_from_u64(seed);
    let left_shares = share_mod_t(left, &mut rng);
    let right_shares = share_mod_t(right, &mut rng);
    let inputs = (0..N)
        .map(|party| {
            let mut party_rng = StdRng::seed_from_u64(seed ^ 0x7000_0000 ^ party as u64);
            PartyComparisonInput::new(
                &session,
                party,
                left_shares[party],
                right_shares[party],
                &mut party_rng,
            )
            .expect("party owns only its two local residue shares")
        })
        .collect::<Vec<_>>();
    let preprocessing = trusted_dealer_triples(&session, &mut rng)
        .expect("trusted preprocessing sees public shape only");
    let (coordinator, endpoints) = local_channels(&session);
    let parties = inputs
        .into_iter()
        .zip(preprocessing)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party_comparison(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let run = coordinator
        .coordinate_comparison(&session)
        .expect("full comparison quorum");
    assert!(run.transcript.is_reveal_only(&session));
    for party in parties {
        party
            .join()
            .expect("party thread exits")
            .expect("party circuit completes");
    }
    run
}

#[test]
fn strict_comparison_reveals_only_the_expected_order_bit() {
    for (index, (left, right, expected)) in [
        (0, 0, false),
        (0, 1, true),
        (1, 0, false),
        (42_423, 42_424, true),
        (42_424, 42_424, false),
        (65_534, 65_535, true),
        (65_535, 0, false),
    ]
    .into_iter()
    .enumerate()
    {
        let run = compare(left, right, 0xc011_a000 + index as u64);
        assert_eq!(run.is_less_than(), expected, "{left} < {right}");
        assert_eq!(run.transcript.revealed_less_than, u8::from(expected));
    }

    let session =
        PartyMpcSession::less_than([0x61; 32], N, BITS, T, Duration::from_secs(1)).unwrap();
    let mut rng = StdRng::seed_from_u64(0x6161);
    let simulated =
        simulate_comparison_transcript(true, &session, &mut rng).expect("comparison simulator");
    assert!(simulated.is_reveal_only(&session));
}

#[test]
fn equality_and_comparison_material_cannot_cross_sessions() {
    let comparison =
        PartyMpcSession::less_than([0x62; 32], N, BITS, T, Duration::from_secs(1)).unwrap();
    let equality =
        PartyMpcSession::equality([0x63; 32], N, BITS, T, Duration::from_secs(1)).unwrap();
    let mut rng = StdRng::seed_from_u64(0x6263);
    assert!(matches!(
        PartyEqualityInput::new(&comparison, 0, 1, 2, &mut rng),
        Err(PartyMpcError::SessionMismatch)
    ));
    assert!(matches!(
        PartyComparisonInput::new(&equality, 0, 1, 2, &mut rng),
        Err(PartyMpcError::SessionMismatch)
    ));
}

#[test]
fn comparison_bit_has_a_strict_quorum_receipt_and_replay_domain() {
    let seed = 0xc011_a777;
    let run = compare(7, 9, seed);
    let session =
        PartyMpcSession::less_than([seed as u8; 32], N, BITS, T, Duration::from_secs(2)).unwrap();
    let keys = [
        SigningKey::from_bytes(&[31; 32]),
        SigningKey::from_bytes(&[37; 32]),
        SigningKey::from_bytes(&[41; 32]),
    ];
    let verifier = AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap();
    let context = ExpectedComparisonContext {
        session: &session,
        roster_digest: verifier.roster_digest(),
        transcript: &run.transcript,
        less_than: run.is_less_than(),
    };
    let draft = AttestedComparisonReceipt::issue(
        &context,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    let signatures = [0usize, 2]
        .into_iter()
        .map(|party| {
            verifier
                .sign_claim(&draft.claim_digest(), party, &keys[party])
                .unwrap()
        })
        .collect::<Vec<_>>();
    let evidence = verifier
        .assemble_evidence(&draft.claim_digest(), &signatures)
        .unwrap();
    let receipt = AttestedComparisonReceipt::issue(&context, evidence).unwrap();
    let wire = receipt.to_wire_bytes().unwrap();
    let decoded = AttestedComparisonReceipt::from_wire_bytes(&wire).unwrap();
    assert_eq!(decoded, receipt);
    assert_eq!(
        AttestedDecisionReceipt::from_wire_bytes(&wire),
        Err(DecisionAttestationError::InvalidWire),
        "comparison and equality receipts are wire-domain separated"
    );

    let mut replay = InMemoryReplayGuard::default();
    decoded
        .verify_full(&context, &verifier, &mut replay)
        .unwrap();
    assert_eq!(
        decoded.verify_full(&context, &verifier, &mut replay),
        Err(DecisionAttestationError::ReplayDetected)
    );
}
