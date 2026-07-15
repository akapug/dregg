//! # The quorum auto-enact reactor
//!
//! The reactive twin of a governance vote, modelled on
//! `starbridge-apps/governed-namespace/src/reactor.rs` (the `GovernanceCommitReactor`
//! that auto-fires the route-table swap at quorum). Where a member *drives* a
//! proposal/vote *in*, this WATCHES a governance poll and, the instant the vote
//! crosses the constitutional threshold, REACTS by enacting the proposal on the
//! real [`dregg_blocklace::constitution::ConstitutionManager`] — vote-and-enact
//! bound as one step.
//!
//! [`GovernanceEnactReactor`] *is* [`crate::substrate::ExecutorEnactReactor`]:
//! the name that used to front a reactor reading a host-side `Resolution` now
//! names the one that fires on a real executor decision-turn.
//!
//! **Fail-closed at every step.** Below the constitutional threshold the
//! executor's in-cell `AffineLe` + `CountGe` gates refuse the decision-turn, so
//! the reactor produces [`EnactOutcome::NoReaction`] and nothing is enacted. A
//! decided poll whose winner is not APPROVE never enacts. And the real
//! constitution's own distinct-voter `has_passed` must independently agree before
//! `apply_if_passed` fires — so forging one side alone enacts nothing.

/// The result of a reactor step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnactOutcome {
    /// The executor refused the decision-turn (below the constitutional
    /// threshold), the winner was not APPROVE, or the real constitution did not
    /// independently agree — nothing enacted.
    NoReaction,
    /// The proposal was enacted on the real constitution; carries the new
    /// constitution version.
    Enacted { new_version: u64 },
    /// Both gates passed but the constitution declined to apply it (e.g. already
    /// applied, or a no-op change).
    NotApplied,
}

/// **The governance auto-enact reactor**, on the verified executor.
///
/// Watches a [`crate::governance::FederationGovernance`] poll and auto-enacts the
/// proposal at quorum. See [`crate::substrate::ExecutorEnactReactor::react`] for
/// the two gates it requires.
pub use crate::substrate::ExecutorEnactReactor as GovernanceEnactReactor;
