//! # The quorum auto-enact reactor
//!
//! The reactive twin of a governance vote, modelled on
//! `starbridge-apps/governed-namespace/src/reactor.rs` (the `GovernanceCommitReactor`
//! that auto-fires the route-table swap at quorum). Where a member *drives* a
//! proposal/vote *in*, this WATCHES a governance poll and, the instant the running
//! tally crosses the constitutional threshold, REACTS by enacting the proposal on
//! the real [`dregg_blocklace::constitution::ConstitutionManager`] — vote-and-enact
//! bound as one step.
//!
//! Fail-closed below quorum: a poll that has not [`crate::Resolution::Decided`]
//! produces no reaction, so nothing is enacted.

use crate::governance::FederationGovernance;
use crate::{PollId, Resolution, VoteEngine};

/// The result of a reactor step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnactOutcome {
    /// The poll is below quorum (or not `enact_on_pass`) — nothing enacted.
    NoReaction,
    /// The proposal was enacted on the real constitution; carries the new
    /// constitution version.
    Enacted { new_version: u64 },
    /// The poll crossed quorum but the constitution declined to apply it (e.g.
    /// already applied, or a no-op change).
    NotApplied,
}

/// Watches a [`FederationGovernance`]'s poll and auto-enacts the proposal at quorum.
///
/// The reactive analogue of `governed-namespace`'s `GovernanceCommitReactor`:
/// it declares WHAT it enacts (the poll's registered proposal block) and reacts
/// only when the engine resolves the poll as decided-and-enact.
#[derive(Clone, Copy, Debug, Default)]
pub struct GovernanceEnactReactor;

impl GovernanceEnactReactor {
    /// Attempt one reactor step against `poll`.
    ///
    /// - Below quorum (or a poll that does not enact-on-pass) → [`EnactOutcome::NoReaction`].
    /// - At/above quorum → enact on the real constitution via `apply_if_passed`
    ///   and report the outcome. The enactment is the REAL membership change: a
    ///   validator is admitted/evicted, the threshold amended, etc.
    pub fn react(&self, gov: &mut FederationGovernance, poll: PollId) -> EnactOutcome {
        match gov.engine.resolve(poll) {
            Resolution::Decided { enact: true, .. } => {
                let proposal_block = match gov.proposal_block(poll) {
                    Some(b) => b,
                    None => return EnactOutcome::NoReaction,
                };
                if gov.constitution.apply_if_passed(&proposal_block) {
                    EnactOutcome::Enacted {
                        new_version: gov.constitution.version(),
                    }
                } else {
                    EnactOutcome::NotApplied
                }
            }
            // Decided-but-not-enact, or Pending: no reaction, nothing enacted.
            _ => EnactOutcome::NoReaction,
        }
    }
}
