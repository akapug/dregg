//! **The council offering, DRIVEN end to end.** Every refusal below is a real
//! executor gate (a `collective-choice` `WriteOnce`/nullifier/AffineLe, or the
//! council cell's `WriteOnce`), not a flag. The flow: open a council over a real
//! cell → members propose → members vote → quorum enacts a REAL committed effect;
//! a below-quorum proposal does NOT enact; a double vote is refused; a non-member
//! is refused; and `verify` re-checks the whole decision chain.

use dreggnet_council::{
    CandidateProposal, CouncilOffering, TURN_APPROVE, TURN_ENACT, TURN_PROPOSE, TURN_REJECT,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

const ALICE: [u8; 32] = [1u8; 32];
const BOB: [u8; 32] = [2u8; 32];
const CAROL: [u8; 32] = [3u8; 32];
const MALLORY: [u8; 32] = [9u8; 32]; // NOT a council member

fn council() -> CouncilOffering {
    CouncilOffering::new(
        vec![ALICE, BOB, CAROL],
        vec![
            CandidateProposal::new("Set treasury policy flag", 7),
            CandidateProposal::new("Raise the spend ceiling", 42),
        ],
        2, // quorum M = 2 of 3
    )
}

fn id(pk: &[u8; 32]) -> DreggIdentity {
    CouncilOffering::member_identity(pk)
}

fn propose(
    off: &CouncilOffering,
    s: &mut dreggnet_council::CouncilSession,
    catalog: i64,
    who: &[u8; 32],
) -> Outcome {
    off.advance(
        s,
        Action::new("propose", TURN_PROPOSE, catalog, true),
        id(who),
    )
}
fn vote_approve(
    off: &CouncilOffering,
    s: &mut dreggnet_council::CouncilSession,
    prop: i64,
    who: &[u8; 32],
) -> Outcome {
    off.advance(s, Action::new("approve", TURN_APPROVE, prop, true), id(who))
}
fn vote_reject(
    off: &CouncilOffering,
    s: &mut dreggnet_council::CouncilSession,
    prop: i64,
    who: &[u8; 32],
) -> Outcome {
    off.advance(s, Action::new("reject", TURN_REJECT, prop, true), id(who))
}
fn enact(
    off: &CouncilOffering,
    s: &mut dreggnet_council::CouncilSession,
    prop: i64,
    who: &[u8; 32],
) -> Outcome {
    off.advance(s, Action::new("enact", TURN_ENACT, prop, true), id(who))
}

/// THE HEADLINE: propose → 2 of 3 members vote approve → quorum reached → the
/// proposal ENACTS a REAL committed turn (a real TurnReceipt; the policy effect is
/// applied to the council cell). And `verify` re-checks the chain.
#[test]
fn quorum_reached_enacts_a_real_committed_effect() {
    let off = council();
    let mut s = off
        .open(SessionConfig::with_seed(1))
        .expect("council opens");

    // Alice opens proposal 0 (catalog item 0). A real committed council-cell turn.
    let out = propose(&off, &mut s, 0, &ALICE);
    assert!(out.landed(), "proposing must land a real turn, got {out:?}");
    assert_eq!(s.proposal_count(), 1);
    // The effect is NOT yet applied — the policy slot is still 0.
    assert_eq!(s.policy_value(0), 0, "no effect before enactment");

    // Below quorum: one approve vote. ENACT must be refused (the AffineLe gate).
    assert!(vote_approve(&off, &mut s, 0, &ALICE).landed());
    assert_eq!(s.tally_of(0), Some((0, 1)));
    match enact(&off, &mut s, 0, &ALICE) {
        Outcome::Refused(why) => assert!(why.contains("below quorum"), "got: {why}"),
        other => panic!("one vote is below quorum — enact must refuse, got {other:?}"),
    }
    assert!(!s.is_enacted(0));
    assert_eq!(
        s.policy_value(0),
        0,
        "a refused enact applies nothing (anti-ghost)"
    );

    // A second approve vote reaches quorum (2 of 3).
    assert!(vote_approve(&off, &mut s, 0, &BOB).landed());
    assert_eq!(s.tally_of(0), Some((0, 2)));

    // ENACT now commits: a REAL TurnReceipt, and the policy effect is applied.
    match enact(&off, &mut s, 0, &CAROL) {
        Outcome::Landed { receipt, .. } => {
            assert_ne!(receipt.turn_hash, [0u8; 32], "a real committed receipt");
        }
        other => panic!("at quorum the proposal must enact, got {other:?}"),
    }
    assert!(s.is_enacted(0));
    assert_eq!(
        s.policy_value(0),
        7,
        "the enacted effect is committed to the council cell"
    );

    // A second enact is refused (already enacted / the council cell's WriteOnce).
    match enact(&off, &mut s, 0, &ALICE) {
        Outcome::Refused(_) => {}
        other => panic!("a double-enact must refuse, got {other:?}"),
    }

    // verify() re-checks the whole decision chain.
    let report = off.verify(&s);
    assert!(
        report.verified,
        "the decision chain re-verifies: {}",
        report.detail
    );
    assert!(
        report.turns >= 4,
        "propose + 2 votes + enact all committed, got {}",
        report.turns
    );
}

/// A below-quorum proposal does NOT enact: only one member votes approve, so the
/// engine's quorum gate refuses the decision-turn and the effect is never applied.
#[test]
fn below_quorum_does_not_enact() {
    let off = council();
    let mut s = off
        .open(SessionConfig::with_seed(2))
        .expect("council opens");
    assert!(propose(&off, &mut s, 1, &ALICE).landed());
    assert!(vote_approve(&off, &mut s, 0, &ALICE).landed());

    // Even a reject vote from another member does not help APPROVE reach quorum.
    assert!(vote_reject(&off, &mut s, 0, &BOB).landed());
    assert_eq!(s.tally_of(0), Some((1, 1)));

    match enact(&off, &mut s, 0, &ALICE) {
        Outcome::Refused(_) => {}
        other => panic!("APPROVE below quorum must not enact, got {other:?}"),
    }
    assert!(!s.is_enacted(0));
    assert_eq!(
        s.policy_value(1),
        0,
        "catalog item 1's policy slot stays unset"
    );
    assert!(
        off.verify(&s).verified,
        "an unenacted proposal still re-verifies"
    );
}

/// A member's SECOND vote on the same proposal is refused — the write-once ballot
/// (the engine nullifier + `WriteOnce(VOTE)`). The board does not move.
#[test]
fn double_vote_is_refused_write_once() {
    let off = council();
    let mut s = off
        .open(SessionConfig::with_seed(3))
        .expect("council opens");
    assert!(propose(&off, &mut s, 0, &ALICE).landed());
    assert!(vote_approve(&off, &mut s, 0, &ALICE).landed());
    assert_eq!(s.tally_of(0), Some((0, 1)));

    // Alice tries to vote again (even switching to reject): refused, board unchanged.
    match vote_reject(&off, &mut s, 0, &ALICE) {
        Outcome::Refused(why) => assert!(why.contains("already voted"), "got: {why}"),
        other => panic!("a second vote must be refused, got {other:?}"),
    }
    assert_eq!(
        s.tally_of(0),
        Some((0, 1)),
        "the board did not move on the refused double vote"
    );
}

/// A non-member's vote is refused — they hold no ballot cap in the electorate.
#[test]
fn non_member_vote_is_refused() {
    let off = council();
    let mut s = off
        .open(SessionConfig::with_seed(4))
        .expect("council opens");
    assert!(propose(&off, &mut s, 0, &ALICE).landed());

    // Mallory is not on the council: refused before any ballot is issued.
    match vote_approve(&off, &mut s, 0, &MALLORY) {
        Outcome::Refused(why) => assert!(why.contains("not a council member"), "got: {why}"),
        other => panic!("a non-member vote must be refused, got {other:?}"),
    }
    // A non-member also cannot propose or enact.
    assert!(matches!(
        propose(&off, &mut s, 1, &MALLORY),
        Outcome::Refused(_)
    ));
    assert_eq!(
        s.tally_of(0),
        Some((0, 0)),
        "no vote was recorded for the non-member"
    );
}

/// The full flow round-trips through the offering surface: actions() / render()
/// present the proposals + votes as cap-gated affordances.
#[test]
fn surface_reflects_proposals_and_votes() {
    let off = council();
    let mut s = off
        .open(SessionConfig::with_seed(5))
        .expect("council opens");

    // Before any proposal: two PROPOSE affordances (one per catalog item).
    let acts = off.actions(&s);
    assert_eq!(acts.iter().filter(|a| a.turn == TURN_PROPOSE).count(), 2);

    assert!(propose(&off, &mut s, 0, &ALICE).landed());
    assert!(vote_approve(&off, &mut s, 0, &ALICE).landed());
    assert!(vote_approve(&off, &mut s, 0, &BOB).landed());

    // Now the ENACT affordance for proposal 0 is enabled (approve reached quorum).
    let acts = off.actions(&s);
    let enact_aff = acts
        .iter()
        .find(|a| a.turn == TURN_ENACT && a.arg == 0)
        .expect("an enact affordance is present");
    assert!(
        enact_aff.enabled,
        "at quorum the enact affordance is enabled"
    );

    // render() produces a non-empty deos surface.
    let surface = off.render(&s);
    match surface.view() {
        deos_view::ViewNode::Section { children, .. } => assert!(!children.is_empty()),
        other => panic!("expected a Section surface, got {other:?}"),
    }
}

/// Two independent proposals resolve independently: one enacts, the other does not.
#[test]
fn two_proposals_enact_independently() {
    let off = council();
    let mut s = off
        .open(SessionConfig::with_seed(6))
        .expect("council opens");

    assert!(propose(&off, &mut s, 0, &ALICE).landed());
    assert!(propose(&off, &mut s, 1, &BOB).landed());

    // Proposal 0 reaches quorum; proposal 1 gets only one vote.
    assert!(vote_approve(&off, &mut s, 0, &ALICE).landed());
    assert!(vote_approve(&off, &mut s, 0, &BOB).landed());
    assert!(vote_approve(&off, &mut s, 1, &CAROL).landed());

    assert!(enact(&off, &mut s, 0, &ALICE).landed());
    assert!(matches!(
        enact(&off, &mut s, 1, &ALICE),
        Outcome::Refused(_)
    ));

    assert_eq!(s.policy_value(0), 7, "proposal 0 enacted its effect");
    assert_eq!(s.policy_value(1), 0, "proposal 1 did not enact");
    assert!(
        off.verify(&s).verified,
        "the mixed chain re-verifies: {}",
        off.verify(&s).detail
    );
}
