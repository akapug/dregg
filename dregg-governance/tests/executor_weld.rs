//! The weld — the constitution face running over the CANONICAL executor-backed
//! `collective-choice` engine (the reconciliation of the two `VoteEngine`s,
//! `docs/FINDING-chain-participation-census.md` §5 weld #2).
//!
//! Every vote below is a REAL ballot-cap turn on the embedded verified
//! executor; every refusal is an executor/engine gate, not a mock:
//! - the full spine: proposal → committee ballot-cap turns → the in-cell
//!   per-option `AffineLe` reaches the constitutional threshold → the
//!   `ConstitutionManager` auto-enacts (the participant set actually changes);
//! - REJECT: a non-electorate voter gets no ballot cap; a double ballot dies
//!   at the nullifier; `required` REJECT ballots never arm the decision-turn.

use dregg_blocklace::constitution::MembershipProposal;
use dregg_blocklace::finality::BlockId;

use collective_choice::VoteError;
use dregg_governance::VoterId;
use dregg_governance::reactor::EnactOutcome;
use dregg_governance::substrate::{ExecutorEnactReactor, ExecutorGovernance};

fn key(b: u8) -> VoterId {
    [b; 32]
}

// ─── The spine: proposal → ballot-cap turns → quorum → auto-enact ────────────

#[test]
fn constitution_proposal_runs_the_full_spine_on_the_executor_engine() {
    // A 3-validator federation (constitutional threshold = ⌊2*3/3⌋+1 = 3).
    let mut gov = ExecutorGovernance::new(vec![key(1), key(2), key(3)]);
    assert_eq!(gov.constitution.threshold(), 3);
    assert_eq!(gov.constitution.current.participant_count(), 3);

    // Propose admitting validator #4 — opens a {reject, approve} poll on the
    // EXECUTOR engine, gated at the constitutional threshold on APPROVE.
    let proposal_block = BlockId([0xE1; 32]);
    let poll = gov
        .propose(
            proposal_block,
            MembershipProposal::Join {
                node_key: key(4),
                justification: b"stake proof".to_vec(),
            },
            "admit validator #4?",
        )
        .expect("proposal opens an executor poll");

    // Two approvals, cast as real ballot-cap turns.
    gov.vote(poll, key(1), true).expect("real turn commits");
    gov.vote(poll, key(2), true).expect("real turn commits");
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 2]);

    // Below quorum: the decision-turn is REFUSED by the in-cell AffineLe, the
    // reactor produces no reaction, and nothing is enacted.
    let reactor = ExecutorEnactReactor;
    assert!(
        gov.resolve(poll).unwrap().is_none(),
        "below the constitutional threshold the decision-turn must be refused"
    );
    assert_eq!(reactor.react(&mut gov, poll), EnactOutcome::NoReaction);
    assert_eq!(
        gov.constitution.current.participant_count(),
        3,
        "below quorum must NOT enact"
    );

    // The third approval crosses the constitutional threshold.
    gov.vote(poll, key(3), true).expect("real turn commits");
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 3]);

    // Two gates provably agree: the executor's decision-turn commits AND the
    // real constitution reports the proposal passed.
    assert!(gov.constitution_has_passed(poll));
    assert_eq!(
        reactor.react(&mut gov, poll),
        EnactOutcome::Enacted { new_version: 1 }
    );

    // The ConstitutionManager ACTUALLY enacted: #4 is a validator now.
    assert_eq!(gov.constitution.current.participant_count(), 4);
    assert!(gov.constitution.current.is_participant(&key(4)));
    // Threshold recomputed for 4 participants: ⌊2*4/3⌋+1 = 3.
    assert_eq!(gov.constitution.threshold(), 3);

    // And the executor's light-client replay agrees with the stored tally.
    assert_eq!(
        gov.engine.light_client_tally(poll).unwrap(),
        gov.tally(poll).unwrap(),
    );
}

// ─── REJECT: non-electorate + double ballot, THROUGH the adapter ─────────────

#[test]
fn non_electorate_voter_and_double_ballot_are_refused_through_the_adapter() {
    let mut gov = ExecutorGovernance::new(vec![key(1), key(2), key(3)]);
    let proposal_block = BlockId([0xE2; 32]);
    let poll = gov
        .propose(
            proposal_block,
            MembershipProposal::Join {
                node_key: key(4),
                justification: vec![],
            },
            "admit #4?",
        )
        .unwrap();

    // A stranger (not a participant) is refused: no ballot cap exists for them.
    match gov.vote(poll, key(99), true) {
        Err(VoteError::Ineligible) => {}
        other => panic!("a non-electorate voter must be refused, got {other:?}"),
    }
    // The refusal never reached the real constitution's tally.
    assert_eq!(
        gov.constitution.votes.approval_count(&proposal_block),
        0,
        "a refused ballot must not reach the real VoteTracker"
    );

    // A committee member votes once (accepted) ...
    gov.vote(poll, key(1), true).expect("first ballot commits");
    // ... and a second ballot from the same voter dies at the nullifier.
    match gov.vote(poll, key(1), false) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a double ballot must be refused, got {other:?}"),
    }
    // Exactly ONE vote is mirrored into the constitution; the board holds.
    assert_eq!(gov.constitution.votes.approval_count(&proposal_block), 1);
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 1]);
    assert!(gov.resolve(poll).unwrap().is_none());
    assert_eq!(gov.constitution.current.participant_count(), 3);
}

// ─── REJECT: `required` REJECT ballots never enact ───────────────────────────

#[test]
fn reject_ballots_never_arm_the_decision_turn_or_enact() {
    // All three validators vote REJECT: the total (3) equals the constitutional
    // threshold, but the gate watches the APPROVE tally (0) — under the old
    // Σ-TALLY quorum this WOULD have armed RESOLVED. Fail-closed, twice over:
    // the executor refuses the decision-turn AND the constitution never passed.
    let mut gov = ExecutorGovernance::new(vec![key(1), key(2), key(3)]);
    let poll = gov
        .propose(
            BlockId([0xE3; 32]),
            MembershipProposal::Join {
                node_key: key(4),
                justification: vec![],
            },
            "admit #4?",
        )
        .unwrap();

    for v in [1u8, 2, 3] {
        gov.vote(poll, key(v), false)
            .expect("reject ballot commits");
    }
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![3, 0]);

    assert!(
        gov.resolve(poll).unwrap().is_none(),
        "3 REJECT ballots must not arm the APPROVE-gated decision-turn"
    );
    assert!(!gov.constitution_has_passed(poll));
    let reactor = ExecutorEnactReactor;
    assert_eq!(reactor.react(&mut gov, poll), EnactOutcome::NoReaction);
    assert_eq!(
        gov.constitution.current.participant_count(),
        3,
        "a rejected proposal must never enact"
    );
    assert!(!gov.constitution.current.is_participant(&key(4)));
}
