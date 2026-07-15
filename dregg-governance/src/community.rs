//! # Community polls — verifiable, delegatable, on the verified executor
//!
//! The census's community-tools face (§2, face b/d + the design in §2.3): a
//! general poll anyone can run, on the SAME engine the federation face uses —
//! which is now [`collective_choice::CollectiveChoice`], the executor-backed one.
//!
//! - **verifiable** — the executor's stored `Monotonic` tally and the
//!   light-client replay of the cast log ([`CommunityPolls::light_client_tally`])
//!   agree; nobody can shrink the board (the `Monotonic` caveat refuses it), and
//!   an inflated tally slot cannot arm a decision, because `RESOLVED` is guarded
//!   by the `CountGe` gate over the DISTINCT approver set;
//! - **one-vote** — the ballot cell's `WriteOnce(VOTE)`, the single per-voter
//!   factory-born ballot, and the engine's nullifier set;
//! - **delegatable** — liquid democracy through the **Lean-mirrored**
//!   [`Mandate::sub_delegate`] (AND-only macaroon attenuation: rights ⊆, budget
//!   ≤, caveat ⇒). This is the ONE non-amplifying lattice, *reused*.
//!
//! ## The delegation lattice is reused, not re-implemented
//!
//! This module used to carry its own `VoteCap` / `DelegationLedger`: a
//! `weight: u64` with an `attenuate` that refused `new_weight > self.weight`, and
//! a `HashMap<VoterId, u64>` of received weight. That was a host-side re-do of a
//! lattice that already ships *and is already proven*
//! ([`dregg_intent::agent_mandate`], mirrored in Lean, with
//! [`DelegTree::no_amplify`] as its tooth). Two lattices meant two chances to be
//! wrong; there is now one.
//!
//! Delegation here is [`CommunityPolls::delegate`]: the delegate receives a
//! strictly-attenuated [`Mandate`] over the SAME ballot cell. Amplification is
//! not "refused by an `if`" — it is *unrepresentable*: `sub_delegate` intersects
//! rights, takes `min` of budgets, and conjoins caveats, so asking for more
//! yields less. And because the delegate votes the delegator's one ballot, the
//! vote still counts exactly ONCE — the nullifier sees the same ballot.
//!
//! ## Named residual — `Electorate::Open`
//!
//! An executor-backed poll's electorate is the cap-mint set: eligibility IS
//! holding a ballot cap. A truly open poll ([`crate::Electorate::Open`], where
//! anyone may cast) therefore has no executor expression — there is no set to
//! mint from. [`CommunityPolls::open`] takes an explicit enrolled electorate.
//! An open-enrollment cap mint would have to live in `collective-choice`.

use collective_choice::{
    BallotCap, CollectiveChoice as ExecutorEngine, Decision, PollId, PollSpec, Tally, TurnReceipt,
    VoteEngine, VoteError,
};
use dregg_intent::agent_mandate::{DelegTree, Mandate};

use crate::VoterId;

/// The community-poll face over the CANONICAL executor-backed engine.
///
/// The same object type [`crate::governance::FederationGovernance`] votes on —
/// governance and community really are one primitive, and now they are one
/// *substrate* too.
pub struct CommunityPolls {
    /// The executor-backed engine every ballot here is a verified turn on.
    pub engine: ExecutorEngine,
}

impl CommunityPolls {
    /// A fresh community-poll host with its own embedded verified executor.
    /// `community_id` seeds the executor's operator identity.
    pub fn new(community_id: [u8; 32]) -> Self {
        CommunityPolls {
            engine: ExecutorEngine::new(community_id),
        }
    }

    /// Open a plurality poll over `options`, deciding once `quorum` distinct
    /// voters have cast. `electorate` is the enrolled voter set — the ONLY keys a
    /// ballot cap will be minted to (see the `Electorate::Open` residual in the
    /// module docs).
    ///
    /// The quorum lands in the poll cell as the in-cell `AffineLe`
    /// `quorum·RESOLVED − Σ TALLY ≤ 0`, with `CountGe` over the distinct voter
    /// set guarding `RESOLVED`.
    pub fn open(
        &mut self,
        question: &str,
        options: &[&str],
        electorate: Vec<VoterId>,
        quorum: u64,
    ) -> Result<PollId, VoteError> {
        self.engine.open_poll(PollSpec {
            question: question.into(),
            options: options.iter().map(|s| s.to_string()).collect(),
            electorate,
            quorum_m: quorum,
        })
    }

    /// Mint (or return) `voter`'s ballot cap for `poll` — **the eligibility
    /// gate**. A voter outside the enrolled electorate is
    /// [`VoteError::Ineligible`]: there is no cap to hold. Idempotent — a voter
    /// has exactly one ballot cell per poll.
    pub fn ballot(&mut self, poll: PollId, voter: VoterId) -> Result<BallotCap, VoteError> {
        self.engine.issue_ballot(poll, voter)
    }

    /// **Liquid democracy** — delegate `cap` to `to`, through the verified,
    /// Lean-mirrored [`Mandate::sub_delegate`].
    ///
    /// The delegate gets a strictly-attenuated mandate over the delegator's SAME
    /// ballot cell: rights ⊆, budget ≤, caveat ⇒. So the delegate can never
    /// out-authorize the delegator ([`DelegTree::no_amplify`]), and the
    /// delegated vote still counts exactly once (same ballot ⇒ same nullifier).
    /// A re-delegation attenuates again.
    pub fn delegate(&self, cap: &BallotCap, to: VoterId) -> BallotCap {
        self.engine.delegate(cap, to)
    }

    /// The delegation tree `root → delegate` — the object whose
    /// [`DelegTree::no_amplify`] / [`DelegTree::well_attenuated`] teeth witness
    /// that a delegated vote can never exceed what was delegated.
    pub fn delegation_tree(root: &BallotCap, delegate: &BallotCap) -> DelegTree {
        ExecutorEngine::delegation_tree(root, delegate)
    }

    /// Cast a ballot as a real turn on the embedded executor. A second cast on
    /// the same ballot — by the voter OR by a delegate holding an attenuated copy
    /// — is [`VoteError::DoubleVote`].
    pub fn cast(
        &mut self,
        poll: PollId,
        cap: &BallotCap,
        choice: usize,
    ) -> Result<TurnReceipt, VoteError> {
        self.engine.cast(poll, cap, choice)
    }

    /// The executor's stored monotone tally.
    pub fn tally(&self, poll: PollId) -> Result<Tally, VoteError> {
        self.engine.tally(poll)
    }

    /// The light-client recompute: replay the append-only cast log and sum. When
    /// this agrees with [`Self::tally`] (the executor's stored slots), the board
    /// is unforged.
    pub fn light_client_tally(&self, poll: PollId) -> Result<Tally, VoteError> {
        self.engine.light_client_tally(poll)
    }

    /// Attempt the decision-turn. `Ok(None)` below quorum — the in-cell gates
    /// refused the turn.
    pub fn resolve(&mut self, poll: PollId) -> Result<Option<Decision>, VoteError> {
        self.engine.resolve(poll)
    }
}

/// A voter's mandate over their ballot — re-exported so a caller can name the
/// verified delegation object without depending on `dregg-intent` directly.
pub type VoteMandate = Mandate;
