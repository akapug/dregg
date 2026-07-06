//! # Federation self-governance — the committee votes, and the federation enacts
//!
//! This is the census's face (a): a federation *already governing itself*, surfaced
//! as an app. It ties the [`crate::VoteEngine`] directly to the REAL
//! [`dregg_blocklace::constitution`] — the Constitutional Consensus protocol
//! (arXiv:2505.19216): membership *is* voted, at the `2n/3+1` threshold, by
//! distinct voters, with votes carried as blocklace blocks (uncensorable), and
//! equivocators auto-evicted.
//!
//! A proposal (admit/evict a validator, amend the threshold, amend routes) opens a
//! poll over `{reject, approve}` whose:
//! - **electorate** is the constitution's current participant set;
//! - **threshold** is the constitutional [`required_votes_for`] — the 2n/3+1
//!   supermajority, honoring the H-rule (amending `T→T'` needs `max(T, T')`);
//! - every accepted cast **mirrors into the real distinct-voter `VoteTracker`** via
//!   [`ConstitutionManager::submit_vote`], so the engine's tally and the
//!   constitution's tally are the same count (they provably agree);
//! - once quorum is met, [`crate::reactor::GovernanceEnactReactor`] **auto-enacts**
//!   on the real `ConstitutionManager` — the participant set actually changes.
//!
//! [`required_votes_for`]: dregg_blocklace::constitution::Constitution::required_votes_for
//! [`ConstitutionManager::submit_vote`]: dregg_blocklace::constitution::ConstitutionManager::submit_vote

use std::collections::{BTreeMap, BTreeSet};

use dregg_blocklace::constitution::{ConstitutionManager, MembershipProposal, MembershipVote};
use dregg_blocklace::finality::BlockId;

use crate::{
    APPROVE, CastOutcome, CollectiveChoice, DecisionRule, Electorate, PollId, PollSpec, REJECT,
    Resolution, VoteEngine, VoterId,
};

/// The default timeout (in waves) for a governance federation's constitution.
pub const DEFAULT_TIMEOUT_WAVES: u64 = 10;

/// A federation governing itself: the real [`ConstitutionManager`] plus the shared
/// [`CollectiveChoice`] engine, wired so a proposal → committee vote → auto-enact
/// flows through both.
pub struct FederationGovernance {
    /// The REAL constitutional consensus state — the authority for who is a
    /// member, the threshold, and the enacted outcome.
    pub constitution: ConstitutionManager,
    /// The shared vote engine — the SAME object the community-poll face uses.
    pub engine: CollectiveChoice,
    /// Open governance polls → the constitution proposal block they enact.
    proposals: BTreeMap<PollId, (BlockId, MembershipProposal)>,
}

impl FederationGovernance {
    /// Stand up a federation of `participants` under a fresh constitution.
    pub fn new(participants: Vec<VoterId>) -> Self {
        FederationGovernance {
            constitution: ConstitutionManager::from_participants(
                participants,
                DEFAULT_TIMEOUT_WAVES,
            ),
            engine: CollectiveChoice::new(),
            proposals: BTreeMap::new(),
        }
    }

    /// The current committee (the constitution's participant set).
    pub fn committee(&self) -> BTreeSet<VoterId> {
        self.constitution.participants().iter().copied().collect()
    }

    /// Open a governance proposal: register it with the real constitution and open
    /// the matching `{reject, approve}` poll over the current committee, gated by
    /// the constitutional threshold (the 2n/3+1 supermajority / H-rule).
    ///
    /// `proposal_block` is the id of the blocklace block that carried the proposal
    /// (the same id the votes reference in their causal past).
    pub fn propose(
        &mut self,
        proposal_block: BlockId,
        proposal: MembershipProposal,
        question: &str,
    ) -> PollId {
        self.constitution
            .submit_proposal(proposal_block, proposal.clone());

        // The constitutional threshold for THIS proposal (encodes 2n/3+1 and the
        // H-rule for a threshold amendment).
        let required = self.constitution.current.required_votes_for(&proposal) as u64;

        let spec = PollSpec {
            question: question.into(),
            options: vec!["reject".into(), "approve".into()],
            electorate: Electorate::Closed(self.committee()),
            rule: DecisionRule::Threshold {
                option: APPROVE,
                min: required,
            },
            enact_on_pass: true,
            nonce: block_nonce(&proposal_block),
        };
        let poll = self.engine.open_poll(spec);
        self.proposals.insert(poll, (proposal_block, proposal));
        poll
    }

    /// A committee member casts an approve/reject ballot. The cast goes through the
    /// SAME [`VoteEngine`] the community face uses AND mirrors into the real
    /// distinct-voter `VoteTracker`, so the two tallies agree.
    ///
    /// A non-committee voter is refused ([`CastOutcome::RefusedNotEligible`]) and
    /// the constitution's tally is left untouched (the real `is_participant` gate).
    pub fn vote(&mut self, poll: PollId, voter: VoterId, approve: bool) -> CastOutcome {
        let choice = if approve { APPROVE } else { REJECT };
        let block = match self.engine.next_block(poll, voter, choice, 1) {
            Some(b) => b,
            None => return CastOutcome::RefusedUnknownPoll,
        };
        let outcome = self.engine.cast(poll, block);
        if outcome == CastOutcome::Accepted
            && let Some((proposal_block, _)) = self.proposals.get(&poll)
        {
            let mv = MembershipVote {
                proposal_block: *proposal_block,
                approve,
            };
            self.constitution.submit_vote(&mv, voter);
        }
        outcome
    }

    /// The engine's resolution for a governance poll.
    pub fn resolve(&self, poll: PollId) -> Resolution {
        self.engine.resolve(poll)
    }

    /// The constitution proposal block a poll enacts (if any).
    pub fn proposal_block(&self, poll: PollId) -> Option<BlockId> {
        self.proposals.get(&poll).map(|(b, _)| *b)
    }

    /// Whether the REAL constitution reports this poll's proposal as passed — the
    /// authority-side gate. By construction this agrees with the engine's
    /// [`Resolution::Decided`] (every accepted engine cast mirrored a
    /// `submit_vote`), which the tests assert.
    pub fn constitution_has_passed(&self, poll: PollId) -> bool {
        match self.proposals.get(&poll) {
            Some((pb, _)) => self
                .constitution
                .votes
                .has_passed(pb, &self.constitution.current),
            None => false,
        }
    }
}

/// Derive a poll nonce from a proposal block id (so two proposals never collide,
/// even with identical text).
fn block_nonce(block: &BlockId) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&block.0[0..8]);
    u64::from_be_bytes(b)
}
