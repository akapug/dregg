//! [`LiquidityGovernance`] — the collective-governed **liquidity vote** that authorizes a
//! pile→fuel swap. The vote is the authorization; a passed vote (and ONLY a passed vote)
//! yields the [`SwapAuthorization`] that [`crate::swap::JupiterSwap::execute`] requires.
//!
//! # The flow: vote → authorize → sign → execute
//!
//! 1. **Propose.** The operator opens a liquidity-event proposal over
//!    [`collective_choice`] — a per-option-gated poll ([`CollectiveChoice::open_poll_gated`])
//!    whose gated option is `APPROVE`, with a holder electorate and a quorum `M`. This is
//!    the SAME quorum engine the bot's `/party` uses (poll → write-once ballots → monotone
//!    tally → the quorum `AffineLe` gate).
//! 2. **Vote.** Each holder casts a single-use ballot (`WriteOnce(VOTE)` + a nullifier —
//!    a double vote is a real executor refusal).
//! 3. **Authorize.** [`LiquidityGovernance::finalize`] resolves the poll. A passed vote
//!    (APPROVE reached quorum) mints a [`SwapAuthorization`] stamped by the operator's
//!    [`GovernanceAuthority`]; a below-quorum vote yields `None` — NO authorization.
//! 4. **Sign + execute.** The operator signs the swap tx and [`crate::swap::JupiterSwap`]
//!    executes against the authorization (see [`crate::swap`]).
//!
//! An unauthorized swap (no authorization) or a failed-quorum vote therefore cannot move
//! the treasury — the refusal is a real quorum gate, not a flag.

use collective_choice::{
    BallotCap, CollectiveChoice, Decision, PollId, PollSpec, Tally, VoteEngine, VoteError,
};

use crate::swap::{GovernanceAuthority, SwapAuthorization};

/// The `REJECT` ballot option (index 0).
pub const REJECT_OPTION: usize = 0;
/// The `APPROVE` ballot option (index 1) — the poll is per-option-gated on THIS option,
/// so the decision-turn commits only once APPROVE itself reaches quorum.
pub const APPROVE_OPTION: usize = 1;

/// A liquidity-event proposal: swap `amount` atomic `$DREGG` out of the pile with a
/// `min_out` atomic USDC slippage floor, pending a holder vote at quorum `quorum_m`.
#[derive(Clone, Debug)]
pub struct LiquidityProposal {
    /// The poll the holders vote in.
    pub poll: PollId,
    /// Atomic `$DREGG` the proposal would swap out of the pile.
    pub amount: u64,
    /// The minimum atomic USDC the swap must realize (the authorized slippage floor).
    pub min_out: u64,
    /// The quorum threshold `M` — APPROVE must reach this for the proposal to pass.
    pub quorum_m: u64,
}

/// Why a governance action was refused.
#[derive(Clone, Debug)]
pub enum GovernanceError {
    /// The underlying vote engine refused (bad spec, ineligible voter, double vote, an
    /// executor caveat, …).
    Vote(VoteError),
}

impl std::fmt::Display for GovernanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GovernanceError::Vote(e) => write!(f, "liquidity vote refused: {e}"),
        }
    }
}

impl std::error::Error for GovernanceError {}

impl From<VoteError> for GovernanceError {
    fn from(e: VoteError) -> Self {
        GovernanceError::Vote(e)
    }
}

/// The collective-governed liquidity-vote authority. Wraps the [`CollectiveChoice`]
/// quorum engine (the vote) and the operator's [`GovernanceAuthority`] (the attestation
/// that turns a passed vote into a swap-executable [`SwapAuthorization`]). Holds the mint
/// pair so the minted authorization binds them.
pub struct LiquidityGovernance {
    engine: CollectiveChoice,
    authority: GovernanceAuthority,
    dregg_mint: [u8; 32],
    usdc_mint: [u8; 32],
}

impl LiquidityGovernance {
    /// Stand up a liquidity-vote authority: a fresh collective-choice engine under
    /// `federation_id`, the operator's certification `authority`, and the `$DREGG`/USDC
    /// mint pair (from [`PayConfig`](crate::config::PayConfig)) the authorization binds.
    pub fn new(
        federation_id: [u8; 32],
        authority: GovernanceAuthority,
        dregg_mint: [u8; 32],
        usdc_mint: [u8; 32],
    ) -> Self {
        LiquidityGovernance {
            engine: CollectiveChoice::new(federation_id),
            authority,
            dregg_mint,
            usdc_mint,
        }
    }

    /// The governance authority public key — what a [`crate::swap::JupiterSwap`] is
    /// configured with to verify authorizations minted here.
    pub fn authority_public_key(&self) -> [u8; 32] {
        self.authority.public_key()
    }

    /// Open a liquidity-event proposal: a REJECT/APPROVE poll gated on APPROVE, over the
    /// holder `electorate`, at quorum `quorum_m`. Returns the proposal handle voters and
    /// [`LiquidityGovernance::finalize`] operate on.
    pub fn propose(
        &mut self,
        question: impl Into<String>,
        amount: u64,
        min_out: u64,
        electorate: Vec<[u8; 32]>,
        quorum_m: u64,
    ) -> Result<LiquidityProposal, GovernanceError> {
        let spec = PollSpec {
            question: question.into(),
            options: vec!["reject".to_string(), "approve".to_string()],
            electorate,
            quorum_m,
        };
        let poll = self.engine.open_poll_gated(spec, APPROVE_OPTION)?;
        Ok(LiquidityProposal {
            poll,
            amount,
            min_out,
            quorum_m,
        })
    }

    /// Mint (or return) a holder's single-use ballot cap. A voter not in the proposal's
    /// electorate is refused ([`VoteError::Ineligible`]) — holding a cap IS eligibility.
    pub fn issue_ballot(
        &mut self,
        proposal: &LiquidityProposal,
        voter_pk: [u8; 32],
    ) -> Result<BallotCap, GovernanceError> {
        Ok(self.engine.issue_ballot(proposal.poll, voter_pk)?)
    }

    /// Cast one holder's vote — `approve = true` votes APPROVE, `false` votes REJECT. A
    /// double vote on the same ballot is a real refusal (the nullifier / `WriteOnce`).
    pub fn vote(
        &mut self,
        proposal: &LiquidityProposal,
        ballot: &BallotCap,
        approve: bool,
    ) -> Result<(), GovernanceError> {
        let option = if approve {
            APPROVE_OPTION
        } else {
            REJECT_OPTION
        };
        self.engine.cast(proposal.poll, ballot, option)?;
        Ok(())
    }

    /// The live monotone tally (`[reject, approve]`) a light client can recompute.
    pub fn tally(&self, proposal: &LiquidityProposal) -> Result<Tally, GovernanceError> {
        Ok(self.engine.tally(proposal.poll)?)
    }

    /// Read the certified decision, if the proposal has resolved (APPROVE at quorum).
    /// `Ok(None)` below quorum — the quorum `AffineLe` refused the decision-turn.
    pub fn decision(
        &mut self,
        proposal: &LiquidityProposal,
    ) -> Result<Option<Decision>, GovernanceError> {
        Ok(self.engine.resolve(proposal.poll)?)
    }

    /// **The authorization gate.** Resolve the proposal and, ONLY if APPROVE reached
    /// quorum (a passed vote), mint the [`SwapAuthorization`] stamped by the governance
    /// authority. A below-quorum vote — or one where APPROVE did not win — yields `None`:
    /// no authorization, so no swap can execute.
    pub fn finalize(
        &mut self,
        proposal: &LiquidityProposal,
    ) -> Result<Option<SwapAuthorization>, GovernanceError> {
        // The quorum `AffineLe` is the REAL gate: `resolve` returns `Some` only once the
        // gated APPROVE option reaches `M`. Below quorum → `None` → no authorization.
        let Some(decision) = self.engine.resolve(proposal.poll)? else {
            return Ok(None);
        };
        // Defensive: the gated poll commits on APPROVE≥M, but a contested board (REJECT
        // strictly higher) is not a mandate to move the treasury — require APPROVE to be
        // the winner at quorum.
        if decision.winner != APPROVE_OPTION || decision.winner_tally < proposal.quorum_m {
            return Ok(None);
        }
        let poll_id = *blake3::hash(proposal.poll.0.as_bytes().as_slice()).as_bytes();
        Ok(Some(self.authority.authorize(
            proposal.amount,
            proposal.min_out,
            self.dregg_mint,
            self.usdc_mint,
            poll_id,
        )))
    }
}
