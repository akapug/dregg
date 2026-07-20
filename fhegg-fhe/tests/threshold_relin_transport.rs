//! Authenticated/recoverable public control plane for multiparty relin.
//!
//! These tests intentionally exercise manifests, not a fictional codec for
//! fhe.rs's opaque `RelinKeyShare<R1/R2>` values.  The existing
//! `threshold_relin` and `threshold_relin_dark_amm_decision` integration tests
//! exercise the real algebraic shares and the resulting Dark AMM key.

use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhegg_fhe::threshold::relin::transport::{
    CoordinatorPhase, RelinCoordinator, RelinPhase, RelinRoster, RelinTransportError,
    SignedRelinEnvelope, RELIN_ENVELOPE_WIRE_LEN,
};
use fhegg_fhe::threshold::relin::RelinKeySession;
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};

struct Fixture {
    session: RelinKeySession,
    keys: Vec<SigningKey>,
}

fn make_fixture(entropy: u8) -> Fixture {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let keygen = KeygenSession::from_seed(N, [0x31; 32]).expect("keygen session");
    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    for party in 0..N {
        let (_, contribution) = ThresholdParty::join(&keygen, party, &params).expect("party joins");
        coordinator
            .accept(contribution)
            .expect("public contribution accepted");
    }
    let collective: CollectivePublicKey = coordinator.finish().expect("collective public key");
    let session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [entropy; 32],
        Duration::from_secs(30),
    )
    .expect("relin session");
    let keys = [0x91u8, 0x92, 0x93]
        .into_iter()
        .map(|seed| SigningKey::from_bytes(&[seed; 32]))
        .collect();
    Fixture { session, keys }
}

fn public_keys(keys: &[SigningKey]) -> Vec<[u8; 32]> {
    keys.iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect()
}

fn envelope(
    fixture: &Fixture,
    roster: &RelinRoster,
    phase: RelinPhase,
    party: usize,
    predecessor: [u8; 32],
    tag: u8,
) -> SignedRelinEnvelope {
    SignedRelinEnvelope::sign(
        &fixture.session,
        roster,
        phase,
        party,
        predecessor,
        [tag; 32],
        &fixture.keys[party],
    )
    .expect("signed relin envelope")
}

#[test]
fn serialize_restart_resend_and_continue_both_rounds() {
    let fixture = make_fixture(0x61);
    let keys = public_keys(&fixture.keys);
    let mut coordinator = RelinCoordinator::new(&fixture.session, keys.clone()).expect("start");
    let roster = coordinator.roster().clone();

    let r1_0 = envelope(&fixture, &roster, RelinPhase::Round1, 0, [0; 32], 0x10);
    let r1_1 = envelope(&fixture, &roster, RelinPhase::Round1, 1, [0; 32], 0x11);
    let r1_2 = envelope(&fixture, &roster, RelinPhase::Round1, 2, [0; 32], 0x12);
    coordinator.accept(r1_1.clone()).expect("out-of-order R1");
    coordinator.accept(r1_0.clone()).expect("R1 party 0");

    let snapshot = coordinator.to_snapshot_bytes();
    let mut coordinator =
        RelinCoordinator::from_snapshot_bytes(&snapshot, &fixture.session).expect("restore R1");
    assert_eq!(coordinator.phase(), CoordinatorPhase::CollectingRound1);
    coordinator
        .verify_recorded_resend(&r1_0)
        .expect("exact authenticated R1 resend");
    coordinator.accept(r1_2).expect("finish R1");
    assert_eq!(coordinator.phase(), CoordinatorPhase::CollectingRound2);
    let r1_digest = coordinator
        .round1_transcript_digest()
        .expect("complete R1 digest");

    let r2 = (0..3)
        .map(|party| {
            envelope(
                &fixture,
                &roster,
                RelinPhase::Round2,
                party,
                r1_digest,
                0x20 + party as u8,
            )
        })
        .collect::<Vec<_>>();
    coordinator.accept(r2[2].clone()).expect("R2 party 2");
    let snapshot = coordinator.to_snapshot_bytes();
    let mut coordinator =
        RelinCoordinator::from_snapshot_bytes(&snapshot, &fixture.session).expect("restore R2");
    coordinator
        .verify_recorded_resend(&r2[2])
        .expect("exact authenticated R2 resend");
    coordinator.accept(r2[0].clone()).expect("R2 party 0");
    coordinator.accept(r2[1].clone()).expect("finish R2");
    assert_eq!(coordinator.phase(), CoordinatorPhase::Complete);
    assert!(coordinator.round2_transcript_digest().is_some());

    let complete = coordinator.to_snapshot_bytes();
    let recovered = RelinCoordinator::from_snapshot_bytes(&complete, &fixture.session)
        .expect("restore complete");
    assert_eq!(recovered, coordinator);
}

#[test]
fn canonical_wires_refuse_every_truncation_trailing_bytes_and_corruption() {
    let fixture = make_fixture(0x62);
    let keys = public_keys(&fixture.keys);
    let coordinator = RelinCoordinator::new(&fixture.session, keys).expect("start");
    let signed = envelope(
        &fixture,
        coordinator.roster(),
        RelinPhase::Round1,
        0,
        [0; 32],
        0x31,
    );
    let wire = signed.to_wire_bytes();
    assert_eq!(wire.len(), RELIN_ENVELOPE_WIRE_LEN);
    assert_eq!(
        SignedRelinEnvelope::from_wire_bytes(&wire).expect("round trip"),
        signed
    );
    for end in 0..wire.len() {
        assert!(
            SignedRelinEnvelope::from_wire_bytes(&wire[..end]).is_err(),
            "truncated envelope length {end}"
        );
    }
    let mut trailing = wire.clone();
    trailing.push(0);
    assert_eq!(
        SignedRelinEnvelope::from_wire_bytes(&trailing),
        Err(RelinTransportError::MalformedWire)
    );

    let snapshot = coordinator.to_snapshot_bytes();
    for end in 0..snapshot.len() {
        assert!(
            RelinCoordinator::from_snapshot_bytes(&snapshot[..end], &fixture.session).is_err(),
            "truncated snapshot length {end}"
        );
    }
    let mut trailing = snapshot.clone();
    trailing.push(0);
    assert!(RelinCoordinator::from_snapshot_bytes(&trailing, &fixture.session).is_err());
    let mut corrupted = snapshot;
    corrupted[40] ^= 1;
    assert_eq!(
        RelinCoordinator::from_snapshot_bytes(&corrupted, &fixture.session),
        Err(RelinTransportError::SnapshotChecksumMismatch)
    );
}

#[test]
fn forgery_cross_context_duplicate_replay_and_substitution_are_atomic() {
    let fixture = make_fixture(0x63);
    let keys = public_keys(&fixture.keys);
    let mut coordinator = RelinCoordinator::new(&fixture.session, keys.clone()).expect("start");
    let roster = coordinator.roster().clone();

    let assert_atomic = |before: &[u8], coordinator: &RelinCoordinator| {
        assert_eq!(coordinator.to_snapshot_bytes(), before);
    };

    let before = coordinator.to_snapshot_bytes();
    let wrong_phase = envelope(&fixture, &roster, RelinPhase::Round2, 0, [0; 32], 0x40);
    assert_eq!(
        coordinator.accept(wrong_phase),
        Err(RelinTransportError::PhaseMismatch)
    );
    assert_atomic(&before, &coordinator);

    let wrong_predecessor = envelope(&fixture, &roster, RelinPhase::Round1, 0, [7; 32], 0x41);
    assert_eq!(
        coordinator.accept(wrong_predecessor),
        Err(RelinTransportError::PredecessorMismatch)
    );
    assert_atomic(&before, &coordinator);

    let legitimate = envelope(&fixture, &roster, RelinPhase::Round1, 0, [0; 32], 0x42);
    let mut wrong_pk_wire = legitimate.to_wire_bytes();
    const COLLECTIVE_PK_OFFSET: usize = 8 + 1 + 4 + 32;
    wrong_pk_wire[COLLECTIVE_PK_OFFSET] ^= 1;
    let wrong_pk =
        SignedRelinEnvelope::from_wire_bytes(&wrong_pk_wire).expect("structural wrong-PK wire");
    assert_eq!(
        coordinator.accept(wrong_pk),
        Err(RelinTransportError::PublicKeyMismatch)
    );
    assert_atomic(&before, &coordinator);

    let mut forged_wire = legitimate.to_wire_bytes();
    *forged_wire.last_mut().expect("signature byte") ^= 1;
    assert_eq!(
        coordinator.accept_wire(&forged_wire),
        Err(RelinTransportError::InvalidSignature { party: 0 })
    );
    assert_atomic(&before, &coordinator);

    let other_fixture = make_fixture(0x64);
    let other_roster =
        RelinRoster::new(&other_fixture.session, keys.clone()).expect("other roster");
    let cross_session = envelope(
        &other_fixture,
        &other_roster,
        RelinPhase::Round1,
        0,
        [0; 32],
        0x43,
    );
    assert_eq!(
        coordinator.accept(cross_session),
        Err(RelinTransportError::SessionMismatch)
    );
    assert_atomic(&before, &coordinator);

    let mut reversed_keys = keys;
    reversed_keys.reverse();
    let reversed_roster =
        RelinRoster::new(&fixture.session, reversed_keys).expect("substituted roster");
    let roster_substitution = SignedRelinEnvelope::sign(
        &fixture.session,
        &reversed_roster,
        RelinPhase::Round1,
        0,
        [0; 32],
        [0x44; 32],
        &fixture.keys[2],
    )
    .expect("valid signature under wrong roster");
    assert_eq!(
        coordinator.accept(roster_substitution),
        Err(RelinTransportError::RosterMismatch)
    );
    assert_atomic(&before, &coordinator);

    coordinator
        .accept(legitimate.clone())
        .expect("first message accepted");
    let after_accept = coordinator.to_snapshot_bytes();
    assert_eq!(
        coordinator.accept(legitimate.clone()),
        Err(RelinTransportError::DuplicateMessage {
            phase: RelinPhase::Round1,
            party: 0,
        })
    );
    assert_atomic(&after_accept, &coordinator);

    let substituted = envelope(&fixture, &roster, RelinPhase::Round1, 0, [0; 32], 0x45);
    assert_eq!(
        coordinator.verify_recorded_resend(&substituted),
        Err(RelinTransportError::SubstitutedMessage {
            phase: RelinPhase::Round1,
            party: 0,
        })
    );
    assert_atomic(&after_accept, &coordinator);
}
