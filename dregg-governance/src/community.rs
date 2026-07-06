//! # Community polls — verifiable, delegatable, uncensorable
//!
//! The census's community-tools face (§2, face b/d + the design in §2.3). A general
//! poll anyone can run, on the SAME [`CollectiveChoice`] engine the federation face
//! uses:
//!
//! - **verifiable** — the tally is a light-client-recomputable derivation over the
//!   ballot log ([`CollectiveChoice::verify_tally`]); a forged/stuffed/censored
//!   tally is caught;
//! - **delegatable** — liquid democracy via non-amplifying [`VoteCap`] attenuation:
//!   a voter hands their weight to a delegate, and the AND-only attenuation lattice
//!   guarantees the delegate's authority never *exceeds* what was delegated;
//! - **uncensorable** — ballots are content-addressed blocks in a causal log, so a
//!   dropped ballot changes the committed [`crate::BallotLog::causal_root`] and any
//!   peer holding the block re-derives the same count.

use std::collections::{HashMap, HashSet};

use crate::{
    BallotLog, CastOutcome, CollectiveChoice, DecisionRule, Electorate, OptionId, PollId, PollSpec,
    Resolution, Tally, VoteEngine, VoterId,
};

/// A voting capability carrying a weight. Attenuation may only *narrow* the weight
/// — the non-amplification tooth (the object-capability / macaroon AND-only law the
/// census points at: `Mandate::attenuate` / macaroon caveats).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VoteCap {
    /// The holder this cap authorizes to vote.
    pub holder: VoterId,
    /// The voting weight the cap carries.
    pub weight: u64,
}

/// A cap cannot be widened — attenuation to a larger weight is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AmplifyRefused;

impl VoteCap {
    /// A base one-vote cap for `holder`.
    pub fn base(holder: VoterId) -> Self {
        VoteCap { holder, weight: 1 }
    }

    /// Attenuate this cap to a *narrower* weight. Widening is refused
    /// ([`AmplifyRefused`]) — a delegated vote can never exceed the delegator's.
    pub fn attenuate(&self, new_weight: u64) -> Result<VoteCap, AmplifyRefused> {
        if new_weight > self.weight {
            return Err(AmplifyRefused);
        }
        Ok(VoteCap {
            holder: self.holder,
            weight: new_weight,
        })
    }
}

/// A liquid-democracy delegation ledger over one poll: who has delegated their
/// vote away, and how much weight each delegate has received.
#[derive(Clone, Debug, Default)]
pub struct DelegationLedger {
    delegated_away: HashSet<VoterId>,
    received: HashMap<VoterId, u64>,
}

impl DelegationLedger {
    /// A fresh ledger.
    pub fn new() -> Self {
        DelegationLedger::default()
    }

    /// Delegate `from`'s cap to `to`. The delegator's own vote is consumed (they
    /// may no longer cast directly), and the delegate's effective weight grows by
    /// the (already-attenuated) cap weight. Returns `false` if `from` already
    /// delegated (a cap is single-use — no double-delegation).
    pub fn delegate(&mut self, from: VoteCap, to: VoterId) -> bool {
        if self.delegated_away.contains(&from.holder) {
            return false;
        }
        self.delegated_away.insert(from.holder);
        *self.received.entry(to).or_insert(0) += from.weight;
        true
    }

    /// The effective weight `voter` casts with: their base `1` (unless they
    /// delegated it away, in which case `0`) plus any weight delegated to them.
    pub fn effective_weight(&self, voter: &VoterId) -> u64 {
        let base = if self.delegated_away.contains(voter) {
            0
        } else {
            1
        };
        base + self.received.get(voter).copied().unwrap_or(0)
    }
}

/// The community-poll face over the shared [`CollectiveChoice`] engine, with a
/// per-poll delegation ledger for liquid democracy.
#[derive(Clone, Debug, Default)]
pub struct CommunityPolls {
    /// The shared engine — the SAME type the federation face drives.
    pub engine: CollectiveChoice,
    ledgers: HashMap<PollId, DelegationLedger>,
}

impl CommunityPolls {
    /// A fresh community-poll host.
    pub fn new() -> Self {
        CommunityPolls::default()
    }

    /// Open a plurality poll over `options`, deciding once `quorum` total ballots
    /// are in. `electorate` is [`Electorate::Open`] for a fully public poll or
    /// [`Electorate::Closed`] for a named eligible set.
    pub fn open(
        &mut self,
        question: &str,
        options: &[&str],
        electorate: Electorate,
        quorum: u64,
        nonce: u64,
    ) -> PollId {
        let poll = self.engine.open_poll(PollSpec {
            question: question.into(),
            options: options.iter().map(|s| s.to_string()).collect(),
            electorate,
            rule: DecisionRule::Plurality { quorum },
            enact_on_pass: false,
            nonce,
        });
        self.ledgers.entry(poll).or_default();
        poll
    }

    /// Delegate `cap` to `to` on `poll` (liquid democracy). Returns `false` for an
    /// unknown poll or a double-delegation.
    pub fn delegate(&mut self, poll: PollId, cap: VoteCap, to: VoterId) -> bool {
        match self.ledgers.get_mut(&poll) {
            Some(l) => l.delegate(cap, to),
            None => false,
        }
    }

    /// Cast a ballot, using the voter's *effective* delegated weight. A voter who
    /// delegated their vote away casts with weight 0 — refused as
    /// [`CastOutcome::RefusedNotEligible`] (their authority now lives with the
    /// delegate).
    pub fn cast(&mut self, poll: PollId, voter: VoterId, choice: OptionId) -> CastOutcome {
        let weight = self
            .ledgers
            .get(&poll)
            .map(|l| l.effective_weight(&voter))
            .unwrap_or(1);
        if weight == 0 {
            return CastOutcome::RefusedNotEligible;
        }
        let block = match self.engine.next_block(poll, voter, choice, weight) {
            Some(b) => b,
            None => return CastOutcome::RefusedUnknownPoll,
        };
        self.engine.cast(poll, block)
    }

    /// The current tally.
    pub fn tally(&self, poll: PollId) -> Option<Tally> {
        self.engine.tally(poll)
    }

    /// The current resolution.
    pub fn resolve(&self, poll: PollId) -> Resolution {
        self.engine.resolve(poll)
    }

    /// Light-client verification of a claimed tally against a ballot log and the
    /// independently-known committed root. Returns `false` for a censored
    /// (dropped-ballot) or stuffed tally. Delegates to
    /// [`CollectiveChoice::verify_tally`].
    pub fn verify_tally(
        &self,
        poll: PollId,
        log: &BallotLog,
        claimed: &Tally,
        committed_root: [u8; 32],
    ) -> bool {
        match self.engine.poll_state(poll) {
            Some(st) => CollectiveChoice::verify_tally(&st.spec, log, claimed, committed_root),
            None => false,
        }
    }
}
