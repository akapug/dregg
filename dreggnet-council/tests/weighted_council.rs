//! The WEIGHTED council driven end-to-end — every claim of
//! [`CouncilOffering::new_weighted`] exercised against the real engine:
//!
//! * a weighted APPROVE bumps the tally by the member's GRANTED weight (not 1),
//!   and the board still light-client re-verifies (the recompute is weight-aware);
//! * one member whose weight alone clears the WEIGHT quorum is a legitimate
//!   quorum — ENACT lands with a single ballot;
//! * a below-weight-quorum ENACT is a REAL refusal and nothing is applied;
//! * a zero-weight member's cast is refused fail-closed WITHOUT consuming the
//!   single-use ballot (no committed turn);
//! * a second weighted cast — at any weight — is the same nullifier refusal as
//!   the classic council (weight changes what a ballot is WORTH, never how many
//!   ballots a member has).

use dreggnet_council::{
    APPROVE_OPTION, CandidateProposal, CouncilOffering, REJECT_OPTION, TURN_APPROVE, TURN_ENACT,
    TURN_PROPOSE, TURN_REJECT,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

/// A whale (weight 5), a holder (weight 2), and a dust account (weight 0).
fn weighted_electorate() -> (Vec<([u8; 32], u64)>, Vec<DreggIdentity>) {
    let grants: Vec<([u8; 32], u64)> = vec![([11u8; 32], 5), ([22u8; 32], 2), ([33u8; 32], 0)];
    let ids = grants
        .iter()
        .map(|(pk, _)| CouncilOffering::member_identity(pk))
        .collect();
    (grants, ids)
}

fn catalog() -> Vec<CandidateProposal> {
    vec![CandidateProposal::new("Fund the commons treasury", 7)]
}

fn press(
    offering: &CouncilOffering,
    session: &mut dreggnet_council::CouncilSession,
    turn: &str,
    arg: i64,
    who: &DreggIdentity,
) -> Outcome {
    offering.advance(session, Action::new("", turn, arg, true), who.clone())
}

#[test]
fn a_weighted_cast_lands_its_granted_weight_and_light_client_reverifies() {
    let (grants, ids) = weighted_electorate();
    // Weight quorum 6: whale (5) alone is short; whale + holder (7) clears it.
    let offering = CouncilOffering::new_weighted(grants, catalog(), 6);
    let mut session = offering
        .open(SessionConfig::with_seed(70_001))
        .expect("the weighted council deploys");
    assert!(session.is_weighted());

    assert!(matches!(
        press(&offering, &mut session, TURN_PROPOSE, 0, &ids[0]),
        Outcome::Landed { .. }
    ));

    // The whale's ONE ballot is worth its whole grant — tally jumps by 5, not 1.
    match press(&offering, &mut session, TURN_APPROVE, 0, &ids[0]) {
        Outcome::Landed { receipt, .. } => assert_ne!(receipt.turn_hash, [0u8; 32]),
        other => panic!("the whale's weighted APPROVE must land, got {other:?}"),
    }
    assert_eq!(
        session.tally_of(0),
        Some((0, 5)),
        "one cast, weight five: the tally is the WEIGHT sum"
    );

    // Below the weight quorum (5 < 6) ENACT is a real refusal; nothing applied.
    match press(&offering, &mut session, TURN_ENACT, 0, &ids[0]) {
        Outcome::Refused(why) => assert!(
            why.contains("quorum") || why.contains("approved"),
            "the engine's own reason: {why}"
        ),
        other => panic!("a below-weight-quorum ENACT must be refused, got {other:?}"),
    }
    assert_eq!(session.policy_value(0), 0, "no phantom effect below quorum");

    // The holder's weight-2 approve clears the quorum (5 + 2 = 7 ≥ 6) → ENACT lands.
    assert!(matches!(
        press(&offering, &mut session, TURN_APPROVE, 0, &ids[1]),
        Outcome::Landed { .. }
    ));
    assert_eq!(session.tally_of(0), Some((0, 7)));
    match press(&offering, &mut session, TURN_ENACT, 0, &ids[0]) {
        Outcome::Landed { receipt, .. } => assert_ne!(receipt.turn_hash, [0u8; 32]),
        other => panic!("an at-weight-quorum ENACT must land, got {other:?}"),
    }
    assert!(session.is_enacted(0));
    assert_eq!(session.policy_value(0), 7, "the enacted effect committed");

    // The whole weighted chain re-verifies: the stored weighted tally equals the
    // light-client recompute, and the enactment has a passing weighted decision.
    let report = offering.verify(&session);
    assert!(report.verified, "{}", report.detail);
}

#[test]
fn one_whale_clearing_the_weight_quorum_alone_is_a_legitimate_quorum() {
    let (grants, ids) = weighted_electorate();
    // Weight quorum 5: the whale's single ballot resolves the poll by itself.
    let offering = CouncilOffering::new_weighted(grants, catalog(), 5);
    let mut session = offering
        .open(SessionConfig::with_seed(70_002))
        .expect("deploys");
    press(&offering, &mut session, TURN_PROPOSE, 0, &ids[0]);
    assert!(matches!(
        press(&offering, &mut session, TURN_APPROVE, 0, &ids[0]),
        Outcome::Landed { .. }
    ));
    match press(&offering, &mut session, TURN_ENACT, 0, &ids[1]) {
        Outcome::Landed { .. } => {}
        other => panic!("a single whale at the weight quorum enacts, got {other:?}"),
    }
    assert!(offering.verify(&session).verified);
}

#[test]
fn a_zero_weight_member_is_refused_fail_closed_without_burning_the_ballot() {
    let (grants, ids) = weighted_electorate();
    let offering = CouncilOffering::new_weighted(grants, catalog(), 5);
    let mut session = offering
        .open(SessionConfig::with_seed(70_003))
        .expect("deploys");
    press(&offering, &mut session, TURN_PROPOSE, 0, &ids[0]);
    let before = session.committed_turns();

    // The dust account (weight 0) is IN the electorate, but its cast is refused
    // BEFORE the ballot turn — the engine's ZeroWeight floor.
    match press(&offering, &mut session, TURN_APPROVE, 0, &ids[2]) {
        Outcome::Refused(why) => assert!(
            why.contains("weight") && why.contains("NOT consumed"),
            "the honest fail-closed reason: {why}"
        ),
        other => panic!("a zero-weight cast must be refused, got {other:?}"),
    }
    assert_eq!(
        session.committed_turns(),
        before,
        "a refused zero-weight cast commits NOTHING"
    );
    assert_eq!(session.tally_of(0), Some((0, 0)));
    assert!(offering.verify(&session).verified);
}

#[test]
fn a_second_weighted_cast_is_the_same_nullifier_refusal() {
    let (grants, ids) = weighted_electorate();
    let offering = CouncilOffering::new_weighted(grants, catalog(), 6);
    let mut session = offering
        .open(SessionConfig::with_seed(70_004))
        .expect("deploys");
    press(&offering, &mut session, TURN_PROPOSE, 0, &ids[0]);
    assert!(matches!(
        press(&offering, &mut session, TURN_APPROVE, 0, &ids[0]),
        Outcome::Landed { .. }
    ));
    let before = session.committed_turns();
    // Flipping to REJECT (or re-approving) does not grant a second ballot.
    match press(&offering, &mut session, TURN_REJECT, 0, &ids[0]) {
        Outcome::Refused(why) => {
            assert!(why.to_lowercase().contains("voted"), "{why}")
        }
        other => panic!("a double weighted vote must be refused, got {other:?}"),
    }
    assert_eq!(session.committed_turns(), before);
    assert_eq!(
        session.tally_of(0),
        Some((0, 5)),
        "the tally never double-counts a member's weight"
    );
}

#[test]
fn member_weight_reads_the_grant_and_the_unweighted_council_is_unchanged() {
    let (grants, _) = weighted_electorate();
    let weighted = CouncilOffering::new_weighted(grants.clone(), catalog(), 3);
    let ws = weighted
        .open(SessionConfig::with_seed(70_005))
        .expect("deploys");
    assert_eq!(ws.member_weight(&[11u8; 32]), 5);
    assert_eq!(ws.member_weight(&[33u8; 32]), 0);
    assert_eq!(
        ws.member_weight(&[99u8; 32]),
        0,
        "a stranger weighs nothing"
    );

    let plain = CouncilOffering::new(grants.iter().map(|(pk, _)| *pk).collect(), catalog(), 2);
    let ps = plain
        .open(SessionConfig::with_seed(70_006))
        .expect("deploys");
    assert!(!ps.is_weighted());
    assert_eq!(
        ps.member_weight(&[11u8; 32]),
        1,
        "one member, one vote — weight is uniformly 1"
    );
    let _ = (REJECT_OPTION, APPROVE_OPTION); // the option layout is part of the public contract
}
