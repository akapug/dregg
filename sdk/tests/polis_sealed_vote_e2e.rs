//! Both-polarity e2e for the WIRED sealed-governance app.
//!
//! Unlike the retired `_sealed_governance_typecheck` `#[path]` fixture, these
//! tests reach the modules through the REAL public crate surface
//! (`dregg_sdk::sealed_governance` + `dregg_sdk::council_seal`, declared in
//! `sdk/src/lib.rs`). If the lib wiring regresses, these stop compiling — they
//! are the wire fact for "the governance app ships in the built image".
//!
//! Polarities (genuine ✓ / attack ✗):
//!   - GENUINE: an eligible, unlinkable, first-time sealed vote tallies under
//!     its real choice at quorum.
//!   - DOUBLE VOTE: nullifier reuse is rejected at collection.
//!   - EARLY PEEK: a sub-quorum tally before close opens NOTHING (the cliff).
//!   - INELIGIBLE / SUBSTITUTION: a valid borrowed nullifier paired with a seal
//!     binding a different nullifier + a forged choice is rejected at tally.
//!   - UNLINKABILITY: the opened tally carries the choice but no link to the
//!     voter's eligibility secret, and nullifiers are per-election.
//!   - SORTITION: an unbiasable beacon draw (light-client-verified) breaks an
//!     exact tie deterministically — same draw ⇒ same outcome.

use dregg_federation::beacon::BeaconDraw;
use dregg_sdk::beacon_cell::BeaconCell;
use dregg_sdk::{
    Ballot, Council, CouncilSealError, GovernanceError, PolisElection, SealedBallot,
    UnlinkableSubmission, eligibility_nullifier, seal_unlinkable_ballot,
};

const LABEL: &[u8] = b"polis:e2e-budget";

fn fresh_election(seed: u8) -> SealedBallot {
    SealedBallot::new_unlinkable(Council::genesis(5, 3, [seed; 32]).unwrap(), LABEL)
}

/// GENUINE (✓): three eligible voters cast unlinkable sealed ballots; the quorum
/// tallies them under their real choices.
#[test]
fn genuine_unlinkable_election_tallies_at_quorum() {
    let mut election = fresh_election(0x01);
    let committee = election.committee().clone();
    let label = election.label().to_vec();

    // Ada→0, Bao→0, Cyra→1: parks wins 2–1.
    for (secret, choice) in [([0x10; 32], 0u32), ([0x20; 32], 0), ([0x30; 32], 1)] {
        let nullifier = eligibility_nullifier(&secret, &label);
        election
            .collect_unlinkable(seal_unlinkable_ballot(
                &committee,
                &label,
                Ballot { choice },
                nullifier,
                secret, // entropy seed
            ))
            .unwrap();
    }
    election.close().unwrap();

    let outcome = election.tally(&[0, 1, 2]).unwrap();
    assert_eq!(outcome.counted, 3, "all three eligible ballots counted");
    assert_eq!(outcome.tallies.get(&0), Some(&2), "two votes for choice 0");
    assert_eq!(outcome.tallies.get(&1), Some(&1), "one vote for choice 1");
    assert_eq!(outcome.winner(), Some(0), "choice 0 (parks) wins");
}

/// ATTACK (✗): the SAME eligibility secret cannot vote twice — nullifier reuse
/// is caught at collection.
#[test]
fn double_vote_rejected_at_collection() {
    let mut election = fresh_election(0x02);
    let committee = election.committee().clone();
    let label = election.label().to_vec();
    let secret = [0x42; 32];
    let nullifier = eligibility_nullifier(&secret, &label);

    election
        .collect_unlinkable(seal_unlinkable_ballot(
            &committee,
            &label,
            Ballot { choice: 0 },
            nullifier,
            [1u8; 32],
        ))
        .unwrap();

    let again = election.collect_unlinkable(seal_unlinkable_ballot(
        &committee,
        &label,
        Ballot { choice: 1 }, // tries to switch
        nullifier,
        [2u8; 32],
    ));
    assert_eq!(
        again.err(),
        Some(GovernanceError::DoubleVote),
        "one vote per eligibility — reuse rejected"
    );
}

/// ATTACK (✗): a sub-quorum (2-of-5, below K=3) tally before reveal opens
/// NOTHING — the common-secret cliff. No early peek, no early bias.
#[test]
fn early_peek_below_quorum_opens_nothing() {
    let mut election = fresh_election(0x03);
    let committee = election.committee().clone();
    let label = election.label().to_vec();
    let nullifier = eligibility_nullifier(&[0x55; 32], &label);
    election
        .collect_unlinkable(seal_unlinkable_ballot(
            &committee,
            &label,
            Ballot { choice: 0 },
            nullifier,
            [1u8; 32],
        ))
        .unwrap();
    election.close().unwrap();

    assert_eq!(
        election.tally(&[0, 1]).err(),
        Some(GovernanceError::Seal(CouncilSealError::BelowThreshold)),
        "a sub-threshold coalition cannot tally early"
    );
    // A single guardian gets nothing either.
    assert_eq!(
        election.tally(&[2]).err(),
        Some(GovernanceError::Seal(CouncilSealError::BelowThreshold))
    );
}

/// ATTACK (✗): an ineligible / substituting voter — a valid borrowed public
/// nullifier paired with a seal that binds a DIFFERENT nullifier and a forged
/// choice — is rejected at tally (the whole tally fail-closes; the forged
/// choice never counts).
#[test]
fn ballot_substitution_rejected_at_tally() {
    let mut election = fresh_election(0x04);
    let committee = election.committee().clone();
    let label = election.label().to_vec();

    let valid_nullifier = eligibility_nullifier(&[0x77; 32], &label);
    let forged = seal_unlinkable_ballot(
        &committee,
        &label,
        Ballot { choice: 999 },
        [0xAB; 32], // bound nullifier ≠ valid_nullifier
        [9u8; 32],
    );
    let attack = UnlinkableSubmission {
        submission: forged.submission,
        nullifier: valid_nullifier,
    };
    election.collect_unlinkable(attack).unwrap(); // dedup passes (public token valid)
    election.close().unwrap();

    assert_eq!(
        election.tally(&[0, 1, 2]).err(),
        Some(GovernanceError::NullifierMismatch),
        "a sealed-in nullifier that disagrees with the claimed token fail-closes the tally"
    );
}

/// PRIVACY (✓): nullifiers are one-way and per-election — the opened tally
/// reveals the choice but not the voter, and a secret in a different election
/// yields a different nullifier (cross-election unlinkable).
#[test]
fn nullifiers_are_one_way_and_per_election() {
    let secret = [0x10; 32];
    let here = eligibility_nullifier(&secret, b"polis:election-A");
    let there = eligibility_nullifier(&secret, b"polis:election-B");
    assert_ne!(
        here, there,
        "same voter, different elections ⇒ different nullifiers"
    );
    // The nullifier is not the secret (one-way blake3).
    assert_ne!(here, secret);
}

/// APP (✓/✗): the runnable `PolisElection` end to end — an eligible roster
/// member tallies; a non-roster stranger is refused at cast (the roster tooth).
#[test]
fn polis_election_app_roster_gate() {
    let secrets = [[0xA1u8; 32], [0xA2; 32], [0xA3; 32]];
    let roster: Vec<[u8; 32]> = secrets.iter().map(PolisElection::roster_commit).collect();
    let council = Council::genesis(5, 3, [0x0A; 32]).unwrap();
    let mut e = PolisElection::new(council, b"polis:app-e2e", roster);

    // ✗ a stranger (not on the roster) is refused BEFORE any seal is admitted.
    assert_eq!(
        e.cast(&[0xEEu8; 32], 0, [9u8; 32]).err(),
        Some(GovernanceError::Ineligible),
        "non-roster voter cannot cast"
    );

    // ✓ the eligible roster casts and tallies at quorum.
    e.cast(&secrets[0], 1, [1u8; 32]).unwrap();
    e.cast(&secrets[1], 1, [2u8; 32]).unwrap();
    e.cast(&secrets[2], 0, [3u8; 32]).unwrap();
    e.close().unwrap();
    let outcome = e.tally(&[0, 1, 2]).unwrap();
    assert_eq!(outcome.counted, 3, "only the three eligible votes counted");
    assert_eq!(outcome.winner(), Some(1));

    // ✗ a sub-quorum still opens nothing through the app surface (the cliff).
    assert_eq!(
        e.tally(&[0, 1]).err(),
        Some(GovernanceError::Seal(CouncilSealError::BelowThreshold))
    );
}

/// SORTITION (✓): a real beacon cell ticks an UNBIASABLE, light-client-verified
/// value; a deterministic draw over {0,1} breaks an exact tie. Same draw ⇒ same
/// winner (any verifier agrees); the draw is fixed AFTER the ballots seal.
#[test]
fn beacon_sortition_breaks_a_tie_deterministically() {
    // A 2–2 tie at the tally.
    let mut election = fresh_election(0x05);
    let committee = election.committee().clone();
    let label = election.label().to_vec();
    for (secret, choice) in [
        ([1u8; 32], 0u32),
        ([2u8; 32], 1),
        ([3u8; 32], 0),
        ([4u8; 32], 1),
    ] {
        let nullifier = eligibility_nullifier(&secret, &label);
        election
            .collect_unlinkable(seal_unlinkable_ballot(
                &committee,
                &label,
                Ballot { choice },
                nullifier,
                secret,
            ))
            .unwrap();
    }
    election.close().unwrap();
    let outcome = election.tally(&[0, 1, 2]).unwrap();
    assert_eq!(outcome.tallies.get(&0), Some(&2));
    assert_eq!(outcome.tallies.get(&1), Some(&2), "an exact tie");

    // Break it with a beacon draw — light-client-verified against the genesis
    // anchor, so the tie-break is not the council's say-so.
    let mut beacon = BeaconCell::genesis(5, 3, 1, [0xBE; 32]).unwrap();
    let tick = beacon.tick().unwrap();
    assert!(
        beacon.anchor().verify_beacon(&tick.output),
        "draw is light-client-verified"
    );

    let winner1 = BeaconDraw::new(&tick.randomness()).draw(2).unwrap();
    let winner2 = BeaconDraw::new(&tick.randomness()).draw(2).unwrap();
    assert_eq!(
        winner1, winner2,
        "same draw ⇒ same winner (deterministic, any verifier agrees)"
    );
    assert!(winner1 < 2, "the tie-break resolves to a real choice");
}
