//! # Federation self-governance — the committee votes, and the federation enacts
//!
//! The census's face (a): a federation *already governing itself*, surfaced as an
//! app — and it runs on the **verified executor**, not on a host-side twin.
//!
//! [`FederationGovernance`] *is* [`crate::substrate::ExecutorGovernance`]. There
//! is no second object and no second engine: the name that used to front a
//! parallel in-memory `CollectiveChoice` (whose double-vote gate was a
//! `HashSet::contains` and whose threshold was a Rust `>=`) now names the real
//! weld. Every ballot is a real turn on the embedded verified executor, so:
//!
//! - **eligibility** is holding a ballot cap, minted only to a current
//!   constitutional participant — a stranger is `VoteError::Ineligible` because
//!   there is no cap to hold, not because a `BTreeSet` said so;
//! - **one-vote** is the ballot cell's `WriteOnce(VOTE)` caveat, the single
//!   per-voter factory-born ballot, and the engine's ballot-nullifier set (the
//!   node's `used_proof_hashes` mirror) — three independent depths;
//! - **the threshold** is the constitutional
//!   [`required_votes_for`] (2n/3+1, honoring the H-rule for a threshold
//!   amendment) baked into the poll cell as the per-option `AffineLe` gate
//!   `required·RESOLVED − TALLY_APPROVE ≤ 0`, so `required` REJECT ballots never
//!   arm the decision-turn — plus the `CountGe` gate, which makes arming
//!   `RESOLVED` EXHIBIT `required` DISTINCT approvers, so an inflated tally slot
//!   cannot forge a quorum;
//! - **enactment** is real: every accepted cast mirrors into the REAL
//!   distinct-voter `VoteTracker` via [`ConstitutionManager::submit_vote`], and
//!   [`crate::reactor::GovernanceEnactReactor`] applies the proposal on the real
//!   `ConstitutionManager` only when the executor's decision-turn commits AND
//!   the constitution independently reports the proposal passed. The participant
//!   set actually changes.
//!
//! Two gates that provably agree, and neither one is host bookkeeping.
//!
//! [`required_votes_for`]: dregg_blocklace::constitution::Constitution::required_votes_for
//! [`ConstitutionManager::submit_vote`]: dregg_blocklace::constitution::ConstitutionManager::submit_vote

/// The default timeout (in waves) for a governance federation's constitution.
pub const DEFAULT_TIMEOUT_WAVES: u64 = 10;

/// **A federation governing itself, on the verified executor.**
///
/// The marquee governance front door. This is not a wrapper, an adapter, or a
/// mirror of [`crate::substrate::ExecutorGovernance`] — it *is* that type. The
/// pre-weld `FederationGovernance` was a full parallel reimplementation over an
/// in-memory ballot box; it is gone, and the name resolves to the verified
/// object.
///
/// See [`crate::substrate::ExecutorGovernance`] for the API (propose / vote /
/// resolve / tally / `constitution_has_passed`) and
/// [`crate::reactor::GovernanceEnactReactor`] for auto-enact.
pub use crate::substrate::ExecutorGovernance as FederationGovernance;
