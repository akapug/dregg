//! Ring trade participation trait for dregg apps.
//!
//! Wraps `dregg_intent::solver` types. Apps that want to contribute liquidity
//! to multi-party ring trades implement [`RingTradeParticipant`] and register
//! with a solver coordinator. The solver calls `exchange_offers` to enumerate
//! what the app currently offers, then calls `settle_leg` / `rollback_leg` for
//! the legs it assigns to this app in an atomic settlement round.
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::ring_trade::{RingTradeParticipant, ExchangeSpec, Settlement};
//!
//! impl RingTradeParticipant for MyAMM {
//!     type Error = MyError;
//!     fn exchange_offers(&self) -> Vec<ExchangeSpec> { self.pool_offers() }
//!     fn settle_leg(&mut self, s: &Settlement) -> Result<(), MyError> { self.execute(s) }
//!     fn rollback_leg(&mut self, s: &Settlement) -> Result<(), MyError> { self.undo(s) }
//! }
//! ```

pub use dregg_intent::solver::{
    ExchangeSpec, IntentNode, RingSolver, RingTrade, Settlement, SolverError,
};
pub use dregg_intent::verified_settle::{
    VerifiedLedger, VerifiedLeg, VerifiedSettleError, funded_ledger, settle_ring_verified,
};
pub use dregg_intent::{CommitmentId, IntentId};

/// An opaque identifier for a single leg in a ring trade.
///
/// Derived from the settlement's `from`/`to` commitments and asset. Apps can
/// use this to correlate `settle_leg` and `rollback_leg` calls.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LegId(pub [u8; 32]);

impl LegId {
    /// Derive a `LegId` from a `Settlement`'s fields.
    pub fn from_settlement(s: &Settlement) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&s.from.0);
        hasher.update(&s.to.0);
        hasher.update(&s.asset);
        hasher.update(&s.amount.to_le_bytes());
        LegId(*hasher.finalize().as_bytes())
    }
}

/// Apps implement this trait to register as a participant in ring trades.
///
/// The framework calls these methods during atomic settlement. All legs in a
/// ring must succeed; if any `settle_leg` fails the coordinator calls
/// `rollback_leg` on each previously-settled app in reverse order.
pub trait RingTradeParticipant {
    /// Error type returned by settle/rollback operations.
    type Error: std::fmt::Debug;

    /// Return the exchange offers this app currently has available.
    ///
    /// Called by the solver coordinator before each solve round to populate the
    /// intent graph. The returned specs should reflect the app's current state
    /// (pool depths, order book, etc.).
    fn exchange_offers(&self) -> Vec<ExchangeSpec>;

    /// Settle a single leg of a ring trade involving this app.
    ///
    /// Called atomically as part of multi-app settlement. If this returns `Ok`,
    /// the leg is committed. If it returns `Err`, the coordinator calls
    /// `rollback_leg` on all previously settled apps.
    fn settle_leg(&mut self, settlement: &Settlement) -> Result<(), Self::Error>;

    /// Roll back a previously settled leg if a peer in the ring fails.
    ///
    /// Must be idempotent — it may be called even if the original `settle_leg`
    /// did not fully succeed (e.g., partial state change before error).
    fn rollback_leg(&mut self, settlement: &Settlement) -> Result<(), Self::Error>;
}

// ===========================================================================
// The coordinator — the missing integration that lets APPS COMMUNICATE VIA
// DECLARATIVE INTENTS rather than bespoke point-to-point Transfer wiring.
// ===========================================================================
//
// An app (or a user via an app) does not call another app. It POSTS what it
// offers and what it wants — a declarative [`ExchangeSpec`]. The coordinator
// collects every participant's posted offers, asks the verified [`RingSolver`]
// to MATCH them into an atomic ring (A→B→…→A), proves Σδ=0 across the whole
// ring through the verified executor ([`settle_ring_verified`]) BEFORE any app
// mutates state, and only then drives each touched app's [`RingTradeParticipant`]
// to settle its leg. Any failure — no match, a non-conserving ring, or an app
// that cannot honor its leg — refuses ATOMICALLY: all-or-none, no partial.

/// An OBJECT-SAFE view of a [`RingTradeParticipant`] so one coordinator can drive
/// a ring across HETEROGENEOUS apps that each have their own concrete `Error`
/// type. The blanket impl adapts any [`RingTradeParticipant`] by rendering its
/// error via `Debug` at the dyn boundary (the coordinator only needs success vs.
/// failure to drive atomicity; the rich error stays in the app).
pub trait RingParticipant {
    /// The offers this app currently posts (its declarative intents).
    fn exchange_offers(&self) -> Vec<ExchangeSpec>;
    /// Settle one leg that touches this app (it is the leg's sender or receiver).
    fn settle_leg(&mut self, settlement: &Settlement) -> Result<(), String>;
    /// Roll back a previously-settled leg (idempotent — may be called after a
    /// partial settle).
    fn rollback_leg(&mut self, settlement: &Settlement) -> Result<(), String>;
}

impl<T: RingTradeParticipant> RingParticipant for T {
    fn exchange_offers(&self) -> Vec<ExchangeSpec> {
        RingTradeParticipant::exchange_offers(self)
    }
    fn settle_leg(&mut self, settlement: &Settlement) -> Result<(), String> {
        RingTradeParticipant::settle_leg(self, settlement).map_err(|e| format!("{e:?}"))
    }
    fn rollback_leg(&mut self, settlement: &Settlement) -> Result<(), String> {
        RingTradeParticipant::rollback_leg(self, settlement).map_err(|e| format!("{e:?}"))
    }
}

/// A participant entry the coordinator drives: the app's anonymous ring identity
/// (its [`CommitmentId`], whose low byte is the verified-ledger cell index) and a
/// mutable handle to the app itself.
pub type CoordinatedParticipant<'a> = (CommitmentId, &'a mut dyn RingParticipant);

/// The receipt of a successful atomic coordination round.
#[derive(Clone, Debug)]
pub struct CoordinationReceipt {
    /// The ring the solver matched out of the posted intents.
    pub ring: RingTrade,
    /// The verified post-state ledger — the result of folding every leg through
    /// the verified executor with Σδ=0 asserted per touched asset.
    pub verified_post: VerifiedLedger,
}

/// Why a coordination round refused. Every variant is ATOMIC: on `NoMatch` and
/// `NotConserving` ZERO app state changed (the refusal is before any
/// [`RingParticipant::settle_leg`]); on `ParticipantFailed` every leg already
/// applied was rolled back, restoring the pre-round state.
#[derive(Clone, Debug)]
pub enum CoordinationError {
    /// The posted intents do not compose into any atomic ring (no cycle whose
    /// offers cover the next party's want). Nothing settled.
    NoMatch,
    /// The matched ring did not conserve value through the verified executor
    /// (a leg was rejected, or some asset's supply changed). Nothing settled —
    /// the verified gate runs BEFORE any app is touched.
    NotConserving(VerifiedSettleError),
    /// An app could not honor a leg the solver assigned it. Every leg already
    /// applied in this round was rolled back; no partial settlement remains.
    ParticipantFailed {
        /// Index of the failing leg within the ring's settlements.
        leg_index: usize,
        /// The settlement the app refused.
        settlement: Settlement,
        /// The app's rendered error.
        detail: String,
    },
}

impl std::fmt::Display for CoordinationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoMatch => write!(f, "no atomic ring matched the posted intents"),
            Self::NotConserving(e) => write!(f, "matched ring did not conserve: {e}"),
            Self::ParticipantFailed {
                leg_index, detail, ..
            } => write!(f, "app refused leg {leg_index}: {detail}"),
        }
    }
}

impl std::error::Error for CoordinationError {}

/// **The intent-coordination engine for apps.**
///
/// Holds only the solver bound (max ring size) and the wall-clock `now` against
/// which intent expiries are judged. It owns no value — value lives in the apps'
/// cells; the coordinator only MATCHES posted intents and drives the verified
/// atomic settlement across them.
#[derive(Clone, Copy, Debug)]
pub struct RingCoordinator {
    /// Largest cycle the solver will search for (clamped to ≥ 2 by the solver).
    pub max_ring_size: usize,
    /// The wall-clock time intents are judged fresh against.
    pub now: u64,
}

impl RingCoordinator {
    /// A coordinator that matches rings up to `max_ring_size` participants.
    pub fn new(max_ring_size: usize, now: u64) -> Self {
        Self { max_ring_size, now }
    }

    /// **Run one atomic coordination round.**
    ///
    /// 1. Collect every participant's posted [`ExchangeSpec`]s into the solver's
    ///    intent graph (each offer becomes an [`IntentNode`] anchored to the
    ///    app's [`CommitmentId`]).
    /// 2. Ask the [`RingSolver`] to MATCH a best ring. No ring → [`CoordinationError::NoMatch`]
    ///    (nothing settled).
    /// 3. Prove the matched ring conserves through the verified executor
    ///    ([`settle_ring_verified`], Σδ=0 per touched asset). A non-conserving
    ///    ring → [`CoordinationError::NotConserving`] (nothing settled — this gate
    ///    runs BEFORE any app is touched).
    /// 4. Drive each touched app's [`RingParticipant::settle_leg`]. If any app
    ///    refuses, roll back every leg already applied this round (reverse order)
    ///    and return [`CoordinationError::ParticipantFailed`] — all-or-none.
    ///
    /// On success returns a [`CoordinationReceipt`] carrying the matched ring and
    /// the verified post-ledger.
    pub fn coordinate(
        &self,
        participants: &mut [CoordinatedParticipant<'_>],
    ) -> Result<CoordinationReceipt, CoordinationError> {
        // (1) Gather posted intents → solver nodes.
        let expiry = self.now.saturating_add(3600);
        let mut nodes: Vec<IntentNode> = Vec::new();
        for (commitment, app) in participants.iter() {
            for spec in app.exchange_offers() {
                let intent_id = intent_id_for(commitment, &spec);
                nodes.push(IntentNode {
                    intent_id,
                    exchange: spec,
                    creator: *commitment,
                    expiry,
                });
            }
        }

        // (2) Match a ring.
        let solver = RingSolver::new(self.max_ring_size);
        let ring = solver
            .solve_best(&nodes, self.now)
            .ok_or(CoordinationError::NoMatch)?;

        // (3) Verified Σδ=0 gate — BEFORE any app mutation. The same per-asset
        //     projection the verified settlement path uses (settlement.from/to low
        //     byte = ledger cell), folded all-or-nothing with conservation
        //     asserted per touched asset.
        let legs: Vec<VerifiedLeg> = ring.settlements.iter().map(settlement_to_leg).collect();
        let k0 = funded_ledger(&legs);
        let verified_post =
            settle_ring_verified(&k0, &legs).map_err(CoordinationError::NotConserving)?;

        // (4) Atomically drive the apps. A leg touches its sender AND receiver;
        //     both apps settle it. Track applied (leg, participant) pairs so a
        //     failure can be rolled back in reverse.
        let mut applied: Vec<(usize, usize)> = Vec::new();
        for (li, settlement) in ring.settlements.iter().enumerate() {
            for pi in 0..participants.len() {
                let touches =
                    participants[pi].0 == settlement.from || participants[pi].0 == settlement.to;
                if !touches {
                    continue;
                }
                match participants[pi].1.settle_leg(settlement) {
                    Ok(()) => applied.push((li, pi)),
                    Err(detail) => {
                        // Roll back everything applied this round, newest first.
                        for &(lj, pj) in applied.iter().rev() {
                            let _ = participants[pj].1.rollback_leg(&ring.settlements[lj]);
                        }
                        return Err(CoordinationError::ParticipantFailed {
                            leg_index: li,
                            settlement: settlement.clone(),
                            detail,
                        });
                    }
                }
            }
        }

        Ok(CoordinationReceipt {
            ring,
            verified_post,
        })
    }
}

/// Project a [`Settlement`] onto the verified-ledger leg the verified executor
/// settles — the SAME projection `verified_settle::extract_legs` performs (sender
/// = `from.0[0]`, receiver = `to.0[0]`, the settlement's asset + amount).
fn settlement_to_leg(s: &Settlement) -> VerifiedLeg {
    VerifiedLeg {
        from: s.from.0[0],
        to: s.to.0[0],
        asset: s.asset,
        amount: s.amount as i128,
    }
}

/// A content-addressed intent id for a posted offer (binds the app's commitment
/// and the exchange terms). Distinct offers from the same app get distinct ids.
fn intent_id_for(commitment: &CommitmentId, spec: &ExchangeSpec) -> IntentId {
    let mut h = blake3::Hasher::new_derive_key("dregg-app-intent-id-v1");
    h.update(&commitment.0);
    h.update(&spec.offer_asset);
    h.update(&spec.offer_amount.to_le_bytes());
    h.update(&spec.want_asset);
    h.update(&spec.want_min_amount.to_le_bytes());
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_intent::CommitmentId;

    #[test]
    fn leg_id_is_deterministic() {
        let s = Settlement {
            from: CommitmentId([1u8; 32]),
            to: CommitmentId([2u8; 32]),
            asset: [3u8; 32],
            amount: 42,
        };
        let id1 = LegId::from_settlement(&s);
        let id2 = LegId::from_settlement(&s);
        assert_eq!(id1, id2);
    }
}
