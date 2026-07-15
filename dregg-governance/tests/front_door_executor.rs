//! **The front door bites AT THE EXECUTOR.**
//!
//! `dregg-governance` used to be dual-faced: a real verified weld
//! (`substrate.rs`) reachable only through a side door, while the marquee names —
//! `FederationGovernance`, `CommunityPolls`, `GovernanceEnactReactor` — fronted a
//! parallel in-memory `CollectiveChoice` whose gates were host-side Rust (a
//! `voted: HashSet` for double-vote, a `>=` for the threshold). These drives pin
//! that the marquee names now resolve to the verified object, and that the
//! refusals come from the engine/executor rather than from bookkeeping.
//!
//! Each test states exactly WHICH tooth bit, and the honest-scope notes say where
//! a tooth is a construction/model tooth rather than an in-circuit one.

use dregg_blocklace::constitution::{MembershipProposal, MembershipVote};
use dregg_blocklace::finality::BlockId;

use collective_choice::VoteError;
use dregg_intent::agent_mandate::{Auth, Caveat, Rights};

use dregg_governance::VoterId;
use dregg_governance::community::CommunityPolls;
use dregg_governance::governance::FederationGovernance;
use dregg_governance::reactor::{EnactOutcome, GovernanceEnactReactor};

fn key(b: u8) -> VoterId {
    [b; 32]
}

fn admit_4() -> MembershipProposal {
    MembershipProposal::Join {
        node_key: key(4),
        justification: b"stake proof".to_vec(),
    }
}

/// A 3-validator federation with an open proposal to admit #4 (threshold 3).
fn federation(block: u8) -> (FederationGovernance, BlockId, collective_choice::PollId) {
    let mut gov = FederationGovernance::new(vec![key(1), key(2), key(3)]);
    let pb = BlockId([block; 32]);
    let poll = gov
        .propose(pb, admit_4(), "admit validator #4?")
        .expect("the proposal opens an executor poll");
    (gov, pb, poll)
}

// ─── 1. A double vote through the FRONT DOOR dies in the engine ─────────────

#[test]
fn front_door_double_vote_is_refused_by_the_engine_not_a_host_hashset() {
    let (mut gov, pb, poll) = federation(0xD1);

    // First ballot: a real ballot-cap turn on the embedded verified executor.
    gov.vote(poll, key(1), true).expect("first ballot commits");
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 1]);

    // Second ballot from the same voter — through `FederationGovernance::vote`,
    // the marquee front door. REFUSED. The refusal is `collective_choice`'s
    // ballot-nullifier (the node `used_proof_hashes` mirror), which is depth
    // (iii) of one-vote inside the verified engine; behind it sit depth (i), the
    // ballot cell's in-circuit `WriteOnce(VOTE)` caveat, and depth (ii), the
    // single per-voter factory-born ballot cell (a voter has exactly ONE ballot
    // per poll, at a deterministic blinding token). What it is NOT any more:
    // `dregg-governance`'s own `PollState::voted: HashSet` — that set is off the
    // governance path entirely.
    match gov.vote(poll, key(1), false) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a double vote must be refused at the engine, got {other:?}"),
    }

    // Neither board moved: not the executor's, not the real constitution's.
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 1]);
    assert_eq!(gov.constitution.votes.approval_count(&pb), 1);

    // Flipping sides does not buy a second vote either.
    assert!(matches!(
        gov.vote(poll, key(1), true),
        Err(VoteError::DoubleVote)
    ));
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 1]);

    // And one vote is not three: the decision-turn stays refused, nothing enacts.
    assert!(gov.resolve(poll).unwrap().is_none());
    assert_eq!(
        GovernanceEnactReactor.react(&mut gov, poll),
        EnactOutcome::NoReaction
    );
    assert_eq!(gov.constitution.current.participant_count(), 3);
}

// ─── 2. A below-quorum enact refuses ────────────────────────────────────────

#[test]
fn front_door_below_quorum_enact_refuses() {
    let (mut gov, _pb, poll) = federation(0xD2);
    assert_eq!(gov.constitution.threshold(), 3);

    // Two of three approve. The APPROVE tally is 2; the constitutional
    // `required_votes_for` is 3, baked into the poll cell as the per-option
    // AffineLe `3·RESOLVED − TALLY_APPROVE ≤ 0` and re-checked by the `CountGe`
    // gate over the DISTINCT approver set.
    gov.vote(poll, key(1), true).unwrap();
    gov.vote(poll, key(2), true).unwrap();
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 2]);

    // The executor REFUSES the decision-turn — this is the gate, not a host `>=`.
    assert!(
        gov.resolve(poll).unwrap().is_none(),
        "2 < 3: the in-cell gates must refuse the decision-turn"
    );
    assert_eq!(
        GovernanceEnactReactor.react(&mut gov, poll),
        EnactOutcome::NoReaction
    );
    assert_eq!(
        gov.constitution.current.participant_count(),
        3,
        "below quorum must NOT enact"
    );
    assert!(!gov.constitution.current.is_participant(&key(4)));

    // The third approval crosses it, and the SAME reactor now enacts for real —
    // so the refusal above was the threshold biting, not the reactor being inert.
    gov.vote(poll, key(3), true).unwrap();
    assert_eq!(
        GovernanceEnactReactor.react(&mut gov, poll),
        EnactOutcome::Enacted { new_version: 1 }
    );
    assert_eq!(gov.constitution.current.participant_count(), 4);
    assert!(gov.constitution.current.is_participant(&key(4)));
}

// ─── 3. Tally forgery ───────────────────────────────────────────────────────

#[test]
fn a_forged_constitutional_tally_alone_never_enacts_the_executor_gate_still_refuses() {
    // THE FORGE: `ConstitutionManager` is a public field, so an operator can
    // inflate the AUTHORITY-side tally directly — submitting votes that never
    // passed through the engine. Under the pre-weld front door both "gates" were
    // fed by the same host-side bookkeeping, so a forged tally that satisfied one
    // satisfied the other. Now they are independent, and the executor is the one
    // that cannot be talked to.
    let (mut gov, pb, poll) = federation(0xD3);

    // Zero ballot-cap turns cast. Forge a full 3-of-3 constitutional approval.
    for v in [1u8, 2, 3] {
        gov.constitution.submit_vote(
            &MembershipVote {
                proposal_block: pb,
                approve: true,
            },
            key(v),
        );
    }
    // The forge WORKED on the authority side — this is a real inflated tally.
    assert_eq!(gov.constitution.votes.approval_count(&pb), 3);
    assert!(
        gov.constitution_has_passed(poll),
        "the forged authority-side tally reports PASSED"
    );

    // But the executor's board is empty: no ballot was ever cast, so the CountGe
    // gate has ZERO distinct approvers to exhibit and the AffineLe has nothing to
    // clear. The decision-turn is REFUSED.
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 0]);
    assert!(
        gov.resolve(poll).unwrap().is_none(),
        "a forged authority tally must not arm the executor's decision-turn"
    );

    // And so the reactor — which requires BOTH gates — enacts nothing. The
    // participant set is untouched despite a "passed" constitution.
    assert_eq!(
        GovernanceEnactReactor.react(&mut gov, poll),
        EnactOutcome::NoReaction
    );
    assert_eq!(gov.constitution.current.participant_count(), 3);
    assert!(!gov.constitution.current.is_participant(&key(4)));
}

#[test]
fn a_quorum_shaped_reject_total_never_arms_the_approve_gate() {
    // The tally-inflation shape that is reachable through the front door: fill the
    // board to the threshold with the WRONG option. All three validators vote
    // REJECT, so the TOTAL (3) equals the constitutional threshold — under a
    // Σ-TALLY quorum this would have armed RESOLVED. The gate is per-option on
    // APPROVE (which sits at 0), so it is refused, twice over.
    let (mut gov, _pb, poll) = federation(0xD4);
    for v in [1u8, 2, 3] {
        gov.vote(poll, key(v), false)
            .expect("reject ballot commits");
    }
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![3, 0]);
    assert_eq!(gov.tally(poll).unwrap().total, 3);

    assert!(
        gov.resolve(poll).unwrap().is_none(),
        "3 REJECT ballots must not arm the APPROVE-gated decision-turn"
    );
    assert!(!gov.constitution_has_passed(poll));
    assert_eq!(
        GovernanceEnactReactor.react(&mut gov, poll),
        EnactOutcome::NoReaction
    );
    assert_eq!(gov.constitution.current.participant_count(), 3);
}

#[test]
fn a_stranger_cannot_stuff_the_executor_board() {
    // The other tally-inflation shape reachable at the front door: stuff the board
    // with ballots from outside the electorate. Eligibility IS holding a ballot
    // cap, and a cap is minted only to a constitutional participant.
    let (mut gov, pb, poll) = federation(0xD5);
    for stranger in [50u8, 51, 52, 53] {
        match gov.vote(poll, key(stranger), true) {
            Err(VoteError::Ineligible) => {}
            other => panic!("a stranger must get no ballot cap, got {other:?}"),
        }
    }
    // Nothing reached either board.
    assert_eq!(gov.tally(poll).unwrap().per_option, vec![0, 0]);
    assert_eq!(gov.constitution.votes.approval_count(&pb), 0);
    assert!(gov.resolve(poll).unwrap().is_none());
    assert_eq!(gov.constitution.current.participant_count(), 3);
}

// ─── 4. Delegation amplification, via the VERIFIED Mandate lattice ──────────

#[test]
fn delegation_amplification_is_unrepresentable_in_the_verified_mandate_lattice() {
    let mut polls = CommunityPolls::new([0xD6; 32]);
    let poll = polls
        .open("direction?", &["left", "right"], vec![key(1), key(2)], 2)
        .unwrap();
    let cap1 = polls.ballot(poll, key(1)).unwrap();

    // The root ballot mandate is deliberately narrow: the Read facet only, budget
    // 1, and a caveat admitting ONLY the cast method-code.
    assert_eq!(cap1.mandate.keep, Rights::from([Auth::Read]));
    assert_eq!(cap1.mandate.budget, 1);
    assert!(cap1.mandate.caveat.admits(1), "the cast method is admitted");
    assert!(!cap1.mandate.caveat.admits(2), "nothing else is");

    // THE ATTACK: a delegate asks for EVERYTHING — every right in the Auth
    // lattice, an unbounded budget, and a wide-open caveat. `sub_delegate` is the
    // ONLY constructor of a child mandate, and it intersects rights, takes min of
    // budgets, and conjoins caveats. Asking for more yields less. This is
    // `dregg_intent::agent_mandate`, mirrored in Lean (`Mandate.subDelegate`) —
    // the SAME lattice `collective-choice` uses, not a second one.
    let greedy: Rights = Rights::from([
        Auth::Read,
        Auth::Write,
        Auth::Grant,
        Auth::Call,
        Auth::Reply,
        Auth::Reset,
        Auth::Control,
    ]);
    let child = cap1
        .mandate
        .sub_delegate(cap1.mandate.holder, &greedy, u64::MAX, &Caveat::any());

    assert_eq!(
        child.keep,
        Rights::from([Auth::Read]),
        "asking for Grant/Control yields only what the parent held"
    );
    assert!(!child.keep.contains(&Auth::Grant));
    assert_eq!(
        child.budget, 1,
        "min(1, u64::MAX) = 1 — the budget never widens"
    );
    assert!(
        !child.caveat.admits(2),
        "the parent's method window is conjoined, never relaxed"
    );

    // The lattice's own tooth agrees, and it is NOT vacuous: a HAND-FORGED wide
    // mandate (built by `Mandate::root`, bypassing `sub_delegate`) makes the same
    // predicate FALSE. So `no_amplify` is checking something.
    let honest = polls.delegate(&cap1, key(2));
    let honest_tree = CommunityPolls::delegation_tree(&cap1, &honest);
    assert!(honest_tree.no_amplify());
    assert!(honest_tree.well_attenuated(&[1, 2]));
    assert!(honest_tree.budget_bounded());

    let forged = dregg_intent::agent_mandate::Mandate::root(
        cap1.mandate.holder,
        honest.holder,
        cap1.mandate.target,
        greedy.clone(),
        u64::MAX,
        Caveat::any(),
    );
    let forged_tree = dregg_intent::agent_mandate::DelegTree::leaf(cap1.mandate.clone())
        .with_child(dregg_intent::agent_mandate::DelegTree::leaf(forged));
    assert!(
        !forged_tree.no_amplify(),
        "the no_amplify tooth must REFUSE an amplified child — else it proves nothing"
    );
    assert!(!forged_tree.well_attenuated(&[1, 2]));
    assert!(!forged_tree.budget_bounded());
}

#[test]
fn a_delegated_vote_counts_exactly_once_at_the_executor() {
    // The other half of non-amplification, and this half IS an executor gate: a
    // delegate votes the delegator's SAME ballot cell, so the delegated vote
    // cannot become two votes. Delegating moves authority; it never mints any.
    let mut polls = CommunityPolls::new([0xD7; 32]);
    let poll = polls
        .open("direction?", &["left", "right"], vec![key(1), key(2)], 2)
        .unwrap();

    let cap1 = polls.ballot(poll, key(1)).unwrap();
    let delegated = polls.delegate(&cap1, key(2));
    // Same ballot cell — that is why the count cannot double.
    assert_eq!(delegated.ballot, cap1.ballot);
    assert_ne!(delegated.holder, cap1.holder, "the holder did change");

    polls.cast(poll, &delegated, 1).expect("the delegate votes");
    assert_eq!(polls.tally(poll).unwrap().per_option, vec![0, 1]);

    // Re-delegating the delegate's cap onward and voting AGAIN: still one ballot,
    // still one nullifier. A delegation chain cannot manufacture weight.
    let onward = polls.delegate(&delegated, key(3));
    assert_eq!(onward.ballot, cap1.ballot);
    match polls.cast(poll, &onward, 1) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a re-delegated ballot must not vote twice, got {other:?}"),
    }
    // And the delegator cannot vote the ballot they gave away.
    match polls.cast(poll, &cap1, 0) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a delegated-away ballot must not vote again, got {other:?}"),
    }
    assert_eq!(polls.tally(poll).unwrap().per_option, vec![0, 1]);

    // One ballot is below the quorum of 2 — nothing resolves off a delegation.
    assert!(polls.resolve(poll).unwrap().is_none());

    // #2's OWN ballot is separate and still available: delegation consumed #1's
    // ballot, not #2's franchise.
    let cap2 = polls.ballot(poll, key(2)).unwrap();
    assert_ne!(cap2.ballot, cap1.ballot);
    polls
        .cast(poll, &cap2, 1)
        .expect("#2 still has their own vote");
    assert_eq!(polls.tally(poll).unwrap().per_option, vec![0, 2]);
    assert!(
        polls.resolve(poll).unwrap().is_some(),
        "2 distinct voters = quorum"
    );
}
