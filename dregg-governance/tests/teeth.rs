//! Teeth — the adversarial gates that must bite (green, non-vacuous, standalone).
//!
//! Governance and stories, one primitive, on ONE verified engine — proven by
//! driving it:
//! - a governance proposal → committee ballot-cap turns → resolves + **auto-enacts**
//!   at the constitutional threshold (below threshold → the executor refuses the
//!   decision-turn and NOTHING is enacted);
//! - a non-committee vote is refused because no ballot cap exists for a stranger;
//! - a community poll runs verifiable (the executor's stored monotone tally and the
//!   light-client replay agree) and an ineligible/double ballot is refused;
//! - liquid-democracy delegation is non-amplifying via the **verified**
//!   `Mandate::sub_delegate` lattice;
//! - the SAME `collective_choice::VoteEngine` object drives a governance proposal,
//!   a community poll, AND a CYOA branch-vote.
//!
//! Every refusal below is an executor/engine gate. The one test that still drives
//! the demoted `HostBallotBox` is named for what it is: a light-client derivation
//! aid, making no claim about executor enforcement.

use dregg_blocklace::constitution::MembershipProposal;
use dregg_blocklace::finality::BlockId;

use collective_choice::{
    CollectiveChoice as ExecutorEngine, PollSpec as ExecutorPollSpec,
    VoteEngine as ExecutorVoteEngine, VoteError,
};

use dregg_governance::community::CommunityPolls;
use dregg_governance::governance::FederationGovernance;
use dregg_governance::reactor::{EnactOutcome, GovernanceEnactReactor};
use dregg_governance::substrate::{EXEC_APPROVE, EXEC_REJECT};
use dregg_governance::{
    APPROVE, BallotLog, Electorate, HostBallotBox, HostVoteEngine, OptionId, PollSpec, Resolution,
    VoterId,
};
use dregg_governance::{CastOutcome, DecisionRule};

fn key(b: u8) -> VoterId {
    [b; 32]
}

// ─── Face 1 — federation self-governance, ON THE EXECUTOR ───────────────────

#[test]
fn governance_proposal_reaches_quorum_and_auto_enacts() {
    // A 3-validator federation (constitutional threshold = ⌊2*3/3⌋+1 = 3).
    let mut gov = FederationGovernance::new(vec![key(1), key(2), key(3)]);
    assert_eq!(gov.constitution.threshold(), 3);
    assert_eq!(gov.constitution.current.participant_count(), 3);

    // Propose admitting validator #4. The constitutional `required_votes_for` is
    // baked into the poll cell as the per-option AffineLe gate on APPROVE.
    let proposal_block = BlockId([0xAA; 32]);
    let poll = gov
        .propose(
            proposal_block,
            MembershipProposal::Join {
                node_key: key(4),
                justification: b"stake proof".to_vec(),
            },
            "admit validator #4?",
        )
        .expect("the proposal opens an executor poll");

    // Two approvals — real ballot-cap turns. Below the threshold: the executor
    // REFUSES the decision-turn, the reactor enacts nothing.
    gov.vote(poll, key(1), true).expect("real turn commits");
    gov.vote(poll, key(2), true).expect("real turn commits");
    assert!(
        gov.resolve(poll).unwrap().is_none(),
        "below the constitutional threshold the decision-turn must be refused"
    );
    let reactor = GovernanceEnactReactor;
    assert_eq!(reactor.react(&mut gov, poll), EnactOutcome::NoReaction);
    assert_eq!(
        gov.constitution.current.participant_count(),
        3,
        "below quorum must NOT enact"
    );

    // The third approval crosses the constitutional threshold.
    gov.vote(poll, key(3), true).expect("real turn commits");
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 3]);
    // Two gates provably agree: the executor's decision-turn commits AND the REAL
    // constitution reports the proposal passed.
    assert!(gov.resolve(poll).unwrap().is_some());
    assert!(gov.constitution_has_passed(poll));

    // The reactor auto-enacts on the REAL constitution: #4 is now a validator.
    assert_eq!(
        reactor.react(&mut gov, poll),
        EnactOutcome::Enacted { new_version: 1 }
    );
    assert_eq!(gov.constitution.current.participant_count(), 4);
    assert!(gov.constitution.current.is_participant(&key(4)));
    // Threshold recomputed for 4 participants: ⌊2*4/3⌋+1 = 3.
    assert_eq!(gov.constitution.threshold(), 3);
}

#[test]
fn non_committee_vote_is_refused_and_leaves_the_constitution_untouched() {
    let mut gov = FederationGovernance::new(vec![key(1), key(2), key(3)]);
    let proposal_block = BlockId([0xBB; 32]);
    let poll = gov
        .propose(
            proposal_block,
            MembershipProposal::AmendThreshold { new_threshold: 2 },
            "lower threshold to 2?",
        )
        .unwrap();

    // A stranger tries to vote → refused: there is no ballot cap to mint them.
    match gov.vote(poll, key(99), true) {
        Err(VoteError::Ineligible) => {}
        other => panic!("a non-committee voter must be refused, got {other:?}"),
    }
    // The real constitution's distinct-voter tally never recorded it.
    assert_eq!(
        gov.constitution.votes.approval_count(&proposal_block),
        0,
        "a non-committee ballot must not reach the real VoteTracker"
    );
    // Nor did the executor's board move.
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 0]);
    assert!(gov.resolve(poll).unwrap().is_none());
}

// ─── Face 2 — community polls, ON THE EXECUTOR ──────────────────────────────

#[test]
fn community_poll_runs_verifiable_light_client_tally() {
    let mut polls = CommunityPolls::new([0xC0; 32]);
    let poll = polls
        .open(
            "best snack?",
            &["ramen", "tacos"],
            vec![key(1), key(2), key(3)],
            3,
        )
        .unwrap();

    for (v, choice) in [(1u8, 0usize), (2, 1), (3, 1)] {
        let cap = polls.ballot(poll, key(v)).expect("electorate member");
        polls.cast(poll, &cap, choice).expect("real turn commits");
    }

    // The executor's stored monotone tally and the light-client replay AGREE —
    // nobody stuffed the board.
    let stored = polls.tally(poll).unwrap();
    assert_eq!(stored, polls.light_client_tally(poll).unwrap());
    assert_eq!(stored.per_option, vec![1, 2]);
    assert_eq!(stored.total, 3);

    // Quorum of 3 distinct voters: the decision-turn commits.
    let decision = polls.resolve(poll).unwrap().expect("quorum reached");
    assert_eq!(decision.winner, 1);
    assert_eq!(decision.winner_tally, 2);
}

#[test]
fn an_ineligible_or_double_community_ballot_is_refused() {
    let mut polls = CommunityPolls::new([0xC1; 32]);
    let poll = polls
        .open("ratify?", &["no", "yes"], vec![key(1), key(2), key(3)], 3)
        .unwrap();

    let cap1 = polls.ballot(poll, key(1)).unwrap();
    polls.cast(poll, &cap1, 1).expect("first ballot commits");
    let cap2 = polls.ballot(poll, key(2)).unwrap();
    polls.cast(poll, &cap2, 1).expect("second ballot commits");

    // (a) an ineligible voter gets no ballot cap at all.
    match polls.ballot(poll, key(50)) {
        Err(VoteError::Ineligible) => {}
        other => panic!("an ineligible voter must be refused, got {other:?}"),
    }
    // (b) a second cast on the same ballot dies at the nullifier.
    match polls.cast(poll, &cap1, 0) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a double vote must be refused, got {other:?}"),
    }

    // The board holds at exactly the two honest ballots, and 2 < 3 does not resolve.
    assert_eq!(polls.tally(poll).unwrap().per_option, vec![0, 2]);
    assert!(polls.resolve(poll).unwrap().is_none());
}

#[test]
fn liquid_democracy_delegation_is_non_amplifying() {
    let mut polls = CommunityPolls::new([0xC2; 32]);
    let poll = polls
        .open("direction?", &["left", "right"], vec![key(1), key(2)], 2)
        .unwrap();

    // #1 delegates their ballot to #2 — through the VERIFIED Mandate lattice.
    let cap1 = polls.ballot(poll, key(1)).unwrap();
    let delegated = polls.delegate(&cap1, key(2));

    // The delegated mandate is provably ⊆ the delegator's: the delegation tree's
    // own tooth says so. This is `Mandate::sub_delegate`, mirrored in Lean — not
    // a host-side `if new_weight > self.weight`.
    let tree = CommunityPolls::delegation_tree(&cap1, &delegated);
    assert!(tree.no_amplify(), "a delegated mandate can never amplify");
    assert!(tree.well_attenuated(&[1, 2, 3]));
    assert!(
        delegated.mandate.budget <= cap1.mandate.budget,
        "budget only narrows"
    );
    assert!(
        delegated.mandate.keep.is_subset(&cap1.mandate.keep),
        "rights only narrow"
    );

    // The delegate votes the delegator's ballot — it counts exactly ONCE.
    polls
        .cast(poll, &delegated, 1)
        .expect("the delegate may exercise the attenuated mandate");
    assert_eq!(polls.tally(poll).unwrap().per_option, vec![0, 1]);

    // And the delegator can no longer vote that ballot themselves: same ballot,
    // same nullifier. The authority moved; it did not multiply.
    match polls.cast(poll, &cap1, 0) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a delegated-away ballot must not vote twice, got {other:?}"),
    }
    assert_eq!(polls.tally(poll).unwrap().per_option, vec![0, 1]);
}

// ─── Face 3 — the unifying demonstration, on the VERIFIED engine ────────────

#[test]
fn same_vote_engine_drives_all_three_faces() {
    // ONE executor-backed engine object. THREE polls: a governance proposal, a
    // community poll, and a CYOA story branch-vote — driven through the identical
    // open_poll / cast / tally / resolve methods, every ballot a real turn.
    let mut engine = ExecutorEngine::new([0xEE; 32]);

    // (a) a GOVERNANCE-shaped poll: closed committee, the threshold gated on
    // APPROVE (the constitutional shape — `required` REJECTs never arm it).
    let governance = engine
        .open_poll_gated(
            ExecutorPollSpec {
                question: "admit a validator?".into(),
                options: vec!["reject".into(), "approve".into()],
                electorate: vec![key(1), key(2), key(3)],
                quorum_m: 3,
            },
            EXEC_APPROVE,
        )
        .unwrap();

    // (b) a COMMUNITY-shaped poll: plurality over the enrolled voters.
    let community = engine
        .open_poll(ExecutorPollSpec {
            question: "which mascot?".into(),
            options: vec!["goose".into(), "dragon".into()],
            electorate: vec![key(4), key(5)],
            quorum_m: 2,
        })
        .unwrap();

    // (c) a CYOA branch-vote: the audience decides the story's next passage. The
    // options are the story's available branches — the EXACT same shape
    // (SPWEEN-ON-DREGG.md §4.2: "the collective choice IS a governance vote over
    // the shared story-state").
    let story = engine
        .open_poll(ExecutorPollSpec {
            question: "the door creaks open. you...".into(),
            options: vec!["step through".into(), "flee".into(), "listen".into()],
            electorate: vec![key(6), key(7)],
            quorum_m: 2,
        })
        .unwrap();

    // Drive all three through the SAME trait methods.
    let cast = |engine: &mut ExecutorEngine, poll, v: u8, opt: usize| {
        let cap = engine
            .issue_ballot(poll, key(v))
            .expect("electorate member");
        engine.cast(poll, &cap, opt).expect("real turn commits");
    };

    // Governance: 3 committee approvals → the gated decision-turn commits.
    for v in [1u8, 2, 3] {
        cast(&mut engine, governance, v, EXEC_APPROVE);
    }
    let d = engine.resolve(governance).unwrap().expect("quorum reached");
    assert_eq!(d.winner, EXEC_APPROVE);

    // Community: dragon (option 1) wins 2–0.
    for v in [4u8, 5] {
        cast(&mut engine, community, v, 1);
    }
    assert_eq!(engine.resolve(community).unwrap().unwrap().winner, 1);

    // Story: "step through" (branch 0) wins — applied as the next passage.
    for v in [6u8, 7] {
        cast(&mut engine, story, v, 0);
    }
    assert_eq!(engine.resolve(story).unwrap().unwrap().winner, 0);

    // All three are the same `Tally` shape over the same engine, and every
    // stored board matches its light-client replay.
    for poll in [governance, community, story] {
        assert_eq!(
            engine.tally(poll).unwrap(),
            engine.light_client_tally(poll).unwrap()
        );
    }
    // And REJECT is a real option on the governance poll — the shape is two-sided.
    assert_eq!(engine.tally(governance).unwrap().per_option[EXEC_REJECT], 0);
}

// ─── The demoted host ballot box — a derivation aid, NOT a gate ─────────────

#[test]
fn host_ballot_box_derivation_aid_catches_a_dropped_ballot() {
    // This drives `HostBallotBox`, which is NOT a governance substrate and which
    // no marquee path runs on. It claims exactly one thing, and that thing is
    // true: a from-scratch re-derivation over a causal ballot log detects a
    // censoring operator, because dropping a block changes the committed root.
    let mut box_ = HostBallotBox::new();
    let spec = PollSpec {
        question: "admit #4?".into(),
        options: vec!["reject".into(), "approve".into()],
        electorate: Electorate::Closed([key(1), key(2), key(3)].into_iter().collect()),
        rule: DecisionRule::Threshold {
            option: APPROVE,
            min: 3,
        },
        enact_on_pass: true,
        nonce: 0xCC,
    };
    let poll = box_.open_poll(spec);
    for v in [1u8, 2, 3] {
        let b = box_.next_block(poll, key(v), APPROVE, 1).unwrap();
        assert_eq!(box_.cast(poll, b), CastOutcome::Accepted);
    }

    let st = box_.poll_state(poll).unwrap();
    let full_log = &st.log;
    let committed_root = full_log.causal_root(); // what consensus commits to
    let honest = HostBallotBox::derive_tally(poll, &st.spec, full_log);
    assert!(HostBallotBox::verify_tally(
        &st.spec,
        full_log,
        &honest,
        committed_root
    ));
    assert_eq!(honest.distinct_voters, 3);

    // An operator DROPS one ballot: a truncated 2-block log, and a tally that is
    // internally self-consistent over that shrunken log.
    let mut dropped_log = BallotLog::new();
    for b in full_log.blocks().iter().take(2) {
        dropped_log.append(b.clone());
    }
    let operator_claim = HostBallotBox::derive_tally(poll, &st.spec, &dropped_log);

    // Against the COMMITTED root (which any peer holding the dropped block knows),
    // the censored tally is caught — its causal root does not match.
    assert!(
        !HostBallotBox::verify_tally(&st.spec, &dropped_log, &operator_claim, committed_root),
        "a dropped ballot must be detectable: the committed causal root changed"
    );
    assert_eq!(
        HostBallotBox::derive_tally(poll, &st.spec, full_log).distinct_voters,
        3
    );

    // And a stuffed/inflated claim is caught by the same re-derivation.
    let mut forged = honest.clone();
    forged.per_option.insert(OptionId(1), 99);
    forged.distinct_voters = 99;
    assert!(!HostBallotBox::verify_tally(
        &st.spec,
        full_log,
        &forged,
        committed_root
    ));
    // Resolution here is a host-side `>=`, not a gate — asserted only to pin the
    // aid's own behaviour.
    assert!(matches!(
        box_.resolve(poll),
        Resolution::Decided {
            winner: APPROVE,
            enact: true
        }
    ));
}
