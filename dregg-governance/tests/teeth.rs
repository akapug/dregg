//! Teeth — the adversarial gates that must bite (green, non-vacuous, standalone).
//!
//! Governance and stories, one primitive — proven:
//! - a governance proposal → committee votes → resolves + **auto-enacts** at quorum
//!   (below quorum → NOT enacted);
//! - a non-committee vote is refused (the real `is_participant` gate);
//! - a dropped ballot fails because votes-are-blocks (the committed causal root
//!   changes);
//! - a community poll runs verifiable (light-client tally) and a forged/stuffed
//!   tally is refused;
//! - the SAME `VoteEngine` object drives a governance proposal, a community poll,
//!   AND a CYOA branch-vote (the shared-shape demonstration).

use dregg_blocklace::constitution::MembershipProposal;
use dregg_blocklace::finality::BlockId;

use dregg_governance::community::{CommunityPolls, VoteCap};
use dregg_governance::governance::FederationGovernance;
use dregg_governance::reactor::{EnactOutcome, GovernanceEnactReactor};
use dregg_governance::{
    APPROVE, BallotLog, CastOutcome, CollectiveChoice, DecisionRule, Electorate, OptionId,
    PollSpec, Resolution, Tally, VoteEngine, VoterId,
};

fn key(b: u8) -> VoterId {
    [b; 32]
}

// ─── Face 1 — federation self-governance ────────────────────────────────────

#[test]
fn governance_proposal_reaches_quorum_and_auto_enacts() {
    // A 3-validator federation (constitutional threshold = ⌊2*3/3⌋+1 = 3).
    let mut gov = FederationGovernance::new(vec![key(1), key(2), key(3)]);
    assert_eq!(gov.constitution.threshold(), 3);
    assert_eq!(gov.constitution.current.participant_count(), 3);

    // Propose admitting validator #4.
    let proposal_block = BlockId([0xAA; 32]);
    let poll = gov.propose(
        proposal_block,
        MembershipProposal::Join {
            node_key: key(4),
            justification: b"stake proof".to_vec(),
        },
        "admit validator #4?",
    );

    // Two approvals: below quorum — resolve stays Pending, reactor enacts nothing.
    assert_eq!(gov.vote(poll, key(1), true), CastOutcome::Accepted);
    assert_eq!(gov.vote(poll, key(2), true), CastOutcome::Accepted);
    assert_eq!(gov.resolve(poll), Resolution::Pending);
    let reactor = GovernanceEnactReactor;
    assert_eq!(reactor.react(&mut gov, poll), EnactOutcome::NoReaction);
    assert_eq!(
        gov.constitution.current.participant_count(),
        3,
        "below quorum must NOT enact"
    );

    // The third approval crosses the constitutional threshold.
    assert_eq!(gov.vote(poll, key(3), true), CastOutcome::Accepted);
    assert_eq!(
        gov.resolve(poll),
        Resolution::Decided {
            winner: APPROVE,
            enact: true
        }
    );
    // Two gates provably agree: the engine and the REAL constitution both pass.
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
    let poll = gov.propose(
        proposal_block,
        MembershipProposal::AmendThreshold { new_threshold: 2 },
        "lower threshold to 2?",
    );

    // A stranger (not a participant) tries to vote → refused by the electorate.
    assert_eq!(
        gov.vote(poll, key(99), true),
        CastOutcome::RefusedNotEligible
    );
    // The real constitution's distinct-voter tally never recorded it.
    assert_eq!(
        gov.constitution.votes.approval_count(&proposal_block),
        0,
        "a non-committee ballot must not reach the real VoteTracker"
    );
    assert!(matches!(gov.resolve(poll), Resolution::Pending));
}

#[test]
fn a_dropped_ballot_fails_because_votes_are_blocks() {
    // Three committee members approve; the ballots are causal blocks.
    let mut gov = FederationGovernance::new(vec![key(1), key(2), key(3)]);
    let poll = gov.propose(
        BlockId([0xCC; 32]),
        MembershipProposal::Join {
            node_key: key(4),
            justification: vec![],
        },
        "admit #4?",
    );
    gov.vote(poll, key(1), true);
    gov.vote(poll, key(2), true);
    gov.vote(poll, key(3), true);

    let st = gov.engine.poll_state(poll).unwrap();
    let full_log = &st.log;
    let committed_root = full_log.causal_root(); // what consensus commits to
    let honest = CollectiveChoice::derive_tally(poll, &st.spec, full_log);
    // Honest tally over ALL three blocks passes verification.
    assert!(CollectiveChoice::verify_tally(
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
    let operator_claim = CollectiveChoice::derive_tally(poll, &st.spec, &dropped_log);

    // Against the COMMITTED root (which any peer holding the dropped block knows),
    // the censored tally is caught — its causal root does not match.
    assert!(
        !CollectiveChoice::verify_tally(&st.spec, &dropped_log, &operator_claim, committed_root),
        "a dropped ballot must be detectable: the committed causal root changed"
    );
    // And a peer re-deriving over the full (uncensored) block set still counts 3.
    assert_eq!(
        CollectiveChoice::derive_tally(poll, &st.spec, full_log).distinct_voters,
        3
    );
}

// ─── Face 2 — community polls ───────────────────────────────────────────────

#[test]
fn community_poll_runs_verifiable_light_client_tally() {
    let mut polls = CommunityPolls::new();
    let poll = polls.open("best snack?", &["ramen", "tacos"], Electorate::Open, 3, 1);
    assert_eq!(polls.cast(poll, key(1), OptionId(0)), CastOutcome::Accepted);
    assert_eq!(polls.cast(poll, key(2), OptionId(1)), CastOutcome::Accepted);
    assert_eq!(polls.cast(poll, key(3), OptionId(1)), CastOutcome::Accepted);

    let st = polls.engine.poll_state(poll).unwrap();
    let log = &st.log;
    let committed_root = log.causal_root();
    let tally = polls.tally(poll).unwrap();

    // Anyone light-client-recomputes the tally from the ballot log and matches.
    assert!(polls.verify_tally(poll, log, &tally, committed_root));
    assert_eq!(tally.per_option.get(&OptionId(1)).copied(), Some(2));
    assert_eq!(
        polls.resolve(poll),
        Resolution::Decided {
            winner: OptionId(1),
            enact: false
        }
    );
}

#[test]
fn a_forged_or_stuffed_community_tally_is_refused() {
    let mut polls = CommunityPolls::new();
    // A closed electorate {1,2,3}.
    let electorate = Electorate::Closed([key(1), key(2), key(3)].into_iter().collect());
    let poll = polls.open("ratify?", &["no", "yes"], electorate, 3, 7);
    polls.cast(poll, key(1), OptionId(1));
    polls.cast(poll, key(2), OptionId(1));

    // (a) an ineligible voter is refused outright.
    assert_eq!(
        polls.cast(poll, key(50), OptionId(1)),
        CastOutcome::RefusedNotEligible
    );
    // (b) a double vote is refused.
    assert_eq!(
        polls.cast(poll, key(1), OptionId(0)),
        CastOutcome::RefusedDoubleVote
    );

    // (c) a forged tally that inflates the count is caught by re-derivation.
    let st = polls.engine.poll_state(poll).unwrap();
    let log = &st.log;
    let committed_root = log.causal_root();
    let mut forged: Tally = polls.tally(poll).unwrap();
    forged.per_option.insert(OptionId(1), 99); // claim 99 "yes" votes
    forged.distinct_voters = 99;
    assert!(
        !polls.verify_tally(poll, log, &forged, committed_root),
        "an inflated/stuffed tally must fail light-client verification"
    );
}

#[test]
fn liquid_democracy_delegation_is_non_amplifying() {
    let mut polls = CommunityPolls::new();
    let poll = polls.open("direction?", &["left", "right"], Electorate::Open, 2, 3);

    // #1 delegates their vote to #2 (a narrowed cap — cannot exceed weight 1).
    let cap = VoteCap::base(key(1));
    assert!(cap.attenuate(2).is_err(), "a cap cannot be widened");
    let narrowed = cap.attenuate(1).unwrap();
    assert!(polls.delegate(poll, narrowed, key(2)));

    // A delegator can no longer vote directly (authority moved to the delegate).
    assert_eq!(
        polls.cast(poll, key(1), OptionId(0)),
        CastOutcome::RefusedNotEligible
    );
    // The delegate votes with effective weight 2 (own 1 + delegated 1).
    assert_eq!(polls.cast(poll, key(2), OptionId(1)), CastOutcome::Accepted);

    let tally = polls.tally(poll).unwrap();
    assert_eq!(
        tally.per_option.get(&OptionId(1)).copied(),
        Some(2),
        "the delegate carries the delegated weight — but never MORE than delegated"
    );
    // Double-delegation refused (a cap is single-use).
    assert!(!polls.delegate(poll, VoteCap::base(key(1)), key(3)));
}

// ─── Face 3 — the unifying demonstration ────────────────────────────────────

#[test]
fn same_vote_engine_drives_all_three_faces() {
    // ONE engine object. THREE polls: a governance proposal, a community poll, and
    // a CYOA story branch-vote — driven through the identical open_poll / cast /
    // tally / resolve methods. Governance, community, and story are one primitive.
    let mut engine = CollectiveChoice::new();

    // (a) a GOVERNANCE-shaped poll: closed committee, threshold on APPROVE.
    let governance = engine.open_poll(PollSpec {
        question: "admit a validator?".into(),
        options: vec!["reject".into(), "approve".into()],
        electorate: Electorate::Closed([key(1), key(2), key(3)].into_iter().collect()),
        rule: DecisionRule::Threshold {
            option: APPROVE,
            min: 3,
        },
        enact_on_pass: true,
        nonce: 1,
    });

    // (b) a COMMUNITY-shaped poll: open, plurality.
    let community = engine.open_poll(PollSpec {
        question: "which mascot?".into(),
        options: vec!["goose".into(), "dragon".into()],
        electorate: Electorate::Open,
        rule: DecisionRule::Plurality { quorum: 2 },
        enact_on_pass: false,
        nonce: 2,
    });

    // (c) a CYOA branch-vote: the audience decides the story's next passage. The
    // options are the story's available branches — the EXACT same shape
    // (SPWEEN-ON-DREGG.md §4.2: "the collective choice IS a governance vote over
    // the shared story-state").
    let story = engine.open_poll(PollSpec {
        question: "the door creaks open. you...".into(),
        options: vec!["step through".into(), "flee".into(), "listen".into()],
        electorate: Electorate::Open,
        rule: DecisionRule::Plurality { quorum: 2 },
        enact_on_pass: true, // the winning branch is applied as a turn
        nonce: 3,
    });

    // Drive all three through the SAME trait methods.
    let cast = |engine: &mut CollectiveChoice, poll, v: u8, opt: u64| {
        let b = engine
            .next_block(poll, key(v), OptionId(opt), 1)
            .expect("open poll");
        assert_eq!(engine.cast(poll, b), CastOutcome::Accepted);
    };

    // Governance: 3 committee approvals → decided.
    cast(&mut engine, governance, 1, 1);
    cast(&mut engine, governance, 2, 1);
    cast(&mut engine, governance, 3, 1);
    assert_eq!(
        engine.resolve(governance),
        Resolution::Decided {
            winner: APPROVE,
            enact: true
        }
    );

    // Community: dragon (option 1) wins 2–0.
    cast(&mut engine, community, 4, 1);
    cast(&mut engine, community, 5, 1);
    assert_eq!(
        engine.resolve(community),
        Resolution::Decided {
            winner: OptionId(1),
            enact: false
        }
    );

    // Story: "step through" (branch 0) wins — applied as the next passage.
    cast(&mut engine, story, 6, 0);
    cast(&mut engine, story, 7, 0);
    assert_eq!(
        engine.resolve(story),
        Resolution::Decided {
            winner: OptionId(0),
            enact: true
        }
    );

    // All three are the same `Tally` shape over the same engine.
    for poll in [governance, community, story] {
        assert!(engine.tally(poll).is_some());
    }
}
