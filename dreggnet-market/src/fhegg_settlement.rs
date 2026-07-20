//! Authenticated fhEgg output authorization for real Dark Bazaar settlement.
//!
//! This adapter begins at fhEgg's public output boundary: an independently
//! reconstructed [`ExpectedClearingContext`] and an [`AttestedClearingReceipt`]
//! whose computation-integrity evidence passes the relying party's verifier.
//! Before that receipt can mutate market state, this module additionally binds
//! it to the exact live Dark Bazaar session:
//!
//! * the MPC nonce must equal a domain-separated digest of the live sealed board;
//! * the board commitment must occur exactly once among the ordered fhEgg inputs;
//! * `(p*, V*)` must equal the live one-unit first-price result; and
//! * the executor-backed auction cell must still contain every recorded seal and
//!   remain in the untouched commit phase.
//!
//! Only after all cheap joins and the full authenticated receipt verification
//! succeed is the existing executor `SETTLE` path called. This module retains
//! that clearing-only API for hosts that intentionally settle another domain
//! later. A Descent or other provenance-carrying asset should normally cross via
//! [`crate::DarkBazaarOffering::settle_fhegg_asset_atomic`], which composes the
//! authenticated clear, replay guard, exact source-bound asset, `$DREGG` leg,
//! provenance verification, and audit receipt into one process-local transaction.
//!
//! # Exact security boundary
//!
//! Acceptance proves that the configured computation-integrity policy endorsed
//! the exact fhEgg ciphertext/source inputs, reveal-only transcript, public
//! rule, and `(p*, V*)`, and that the seller's exact encrypted ask/asset plus
//! every bid's exact signed-message/ciphertext pair are inside their
//! corresponding on-ledger source-bound seals under the same BFV
//! parameter/public-key domain named by the clearing claim. Each source
//! certificate is issued only after the configured ingress verifier reproduces
//! the exact BFV encryption of the operator-visible one-unit order. This closes
//! same-opening for today's Tier-1 CRAWL, under that verifier's honesty and key
//! custody; it is explicitly **not** a house-blind lattice ZK proof. With today's
//! unanimous/quorum Ed25519 verifier, computation correctness additionally assumes the accepted
//! quorum contains an honest computation verifier. The underlying fhEgg demo is
//! semi-honest, uses trusted Beaver preprocessing, and supports a Shamir `t < n`
//! opening roster (the game integration exercises 3-of-4 custody with one party
//! absent after DKG). Its DKG transcript binds bivariate row commitments, checks
//! pairwise algebraic VSS consistency, and publishes `C_ab = -a*s_ab + e_ab`
//! images whose `C_00` is required to byte-equal the actual RLWE public-key
//! share, alongside DKG-bound Ed25519 share envelopes. Thus a consistent,
//! recommitted row family off the public-key relation is rejected. Setup still
//! requires every dealer. The exact remaining lattice seams are proofs that the
//! hidden key/error witnesses occupy their required ternary/CBD ranges and that
//! each decryption share is `c1*s +` an in-range smudge; this adapter does not
//! upgrade those residual assumptions.

use std::fmt;

use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, BfvPublicIdentity, ComputationIntegrityVerifier,
    Digest32, ExpectedClearingContext, InputDigest, InputDigestKind, ReplayGuard,
};
use fhegg_fhe::order_ingress::OrderIngressSession;
use starbridge_sealed_auction::Phase;

use crate::{DarkBazaarOffering, DarkBazaarSession, FHEGG_LISTING_SOURCE_SLOT};
use dreggnet_offerings::{DreggIdentity, Outcome};

const BOARD_DOMAIN: &str = "dreggnet-market/fhegg/live-sealed-board/v1";
const SESSION_DOMAIN: &str = "dreggnet-market/fhegg/settlement-session/v1";

#[derive(Clone, Debug)]
pub struct FheggSettlementReceipt {
    /// Exact digest authenticated by fhEgg's computation-integrity evidence.
    pub claim_digest: Digest32,
    /// Canonical commitment to the live sealed-auction source board.
    pub source_commitment: Digest32,
    /// Public uniform-price bucket authorized by fhEgg and consumed as the
    /// first-price value of this one-unit Dark Bazaar listing.
    pub price: u64,
    /// Public cleared volume. The current asset-backed listing requires one.
    pub volume: u64,
    /// Winner selected by the existing seal-ordered live tie policy.
    pub winner: DreggIdentity,
    /// Existing executor resolve turn, not a synthetic adapter receipt.
    pub settlement_turn: dregg_app_framework::TurnReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FheggSettlementError {
    NotListed,
    AlreadySettled,
    PhaseNotCommit(Option<Phase>),
    NoBids,
    BelowReserve {
        high: i128,
        reserve: i128,
    },
    PriceOutOfRange(i128),
    MissingAuctionCell,
    SourceBoardMismatch {
        slot: usize,
    },
    UnboundListingSource,
    ListingSourceBoardMismatch,
    ListingSourceInputPairCount {
        found: usize,
    },
    ListingSourceBfvDomainMismatch,
    UnboundSource {
        slot: usize,
    },
    SourceInputPairCount {
        bid: usize,
        found: usize,
    },
    SourceBfvDomainMismatch {
        bid: usize,
    },
    SessionMismatch,
    SourceCommitmentCount {
        found: usize,
    },
    ResultMismatch {
        expected_price: u64,
        claimed_price: Option<usize>,
        claimed_volume: u64,
    },
    Attestation(AttestationError),
    SettlementRefused(String),
    PostSettlementMismatch(&'static str),
}

impl fmt::Display for FheggSettlementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotListed => write!(f, "nothing is listed yet"),
            Self::AlreadySettled => write!(f, "the Dark Bazaar session is already settled"),
            Self::PhaseNotCommit(phase) => write!(
                f,
                "fhEgg settlement requires an untouched COMMIT phase, found {phase:?}"
            ),
            Self::NoBids => write!(f, "no sealed bids were placed"),
            Self::BelowReserve { high, reserve } => {
                write!(f, "top bid {high} is below reserve {reserve}")
            }
            Self::PriceOutOfRange(price) => {
                write!(f, "top bid {price} cannot be represented as a fhEgg bucket")
            }
            Self::MissingAuctionCell => write!(f, "the listed auction cell is absent"),
            Self::SourceBoardMismatch { slot } => write!(
                f,
                "recorded sealed bid does not match on-ledger commit slot {slot}"
            ),
            Self::UnboundListingSource => write!(
                f,
                "the seller listing has no exact encrypted ask/asset source binding"
            ),
            Self::ListingSourceBoardMismatch => write!(
                f,
                "the seller listing source does not match its reserved on-ledger WriteOnce slot"
            ),
            Self::ListingSourceInputPairCount { found } => write!(
                f,
                "the seller listing source has {found} exact signed-message/ciphertext input pairs; expected one"
            ),
            Self::ListingSourceBfvDomainMismatch => write!(
                f,
                "the seller listing source was opened under a different BFV parameter/public-key domain"
            ),
            Self::UnboundSource { slot } => write!(
                f,
                "commit slot {slot} is a legacy bid without an exact fhEgg source binding"
            ),
            Self::SourceInputPairCount { bid, found } => write!(
                f,
                "source-bound bid {bid} has {found} exact signed-message/ciphertext input pairs; expected one"
            ),
            Self::SourceBfvDomainMismatch { bid } => write!(
                f,
                "source-bound bid {bid} was opened under a different BFV parameter/public-key domain"
            ),
            Self::SessionMismatch => write!(
                f,
                "fhEgg MPC nonce is not bound to this exact live sealed board"
            ),
            Self::SourceCommitmentCount { found } => write!(
                f,
                "expected the live board commitment exactly once among fhEgg inputs, found {found}"
            ),
            Self::ResultMismatch {
                expected_price,
                claimed_price,
                claimed_volume,
            } => write!(
                f,
                "fhEgg result ({claimed_price:?}, {claimed_volume}) does not authorize live one-unit price {expected_price}"
            ),
            Self::Attestation(error) => write!(f, "fhEgg receipt refused: {error}"),
            Self::SettlementRefused(why) => {
                write!(f, "authorized executor settlement refused: {why}")
            }
            Self::PostSettlementMismatch(why) => {
                write!(f, "authorized settlement diverged after landing: {why}")
            }
        }
    }
}

impl std::error::Error for FheggSettlementError {}

impl From<AttestationError> for FheggSettlementError {
    fn from(error: AttestationError) -> Self {
        Self::Attestation(error)
    }
}

pub(crate) struct LiveClear {
    pub(crate) price: u64,
    pub(crate) winner: DreggIdentity,
}

impl DarkBazaarSession {
    /// Canonical commitment to the exact public sealed-order source currently
    /// frozen into this session's executor cell. It contains no bid opening.
    pub fn fhegg_source_commitment(&self) -> Result<Digest32, FheggSettlementError> {
        preflight_board(self)?;

        let mut hasher = blake3::Hasher::new_derive_key(BOARD_DOMAIN);
        hasher.update(&self.market.seed.to_be_bytes());
        hasher.update(&self.market.reserve.to_be_bytes());
        let seller = self
            .market
            .seller
            .as_ref()
            .ok_or(FheggSettlementError::NotListed)?;
        hasher.update(&(seller.0.len() as u64).to_be_bytes());
        hasher.update(seller.0.as_bytes());
        let listing = self
            .market
            .fhegg_listing_source
            .ok_or(FheggSettlementError::UnboundListingSource)?;
        hasher.update(&listing.asset);
        hasher.update(
            &self
                .market
                .fhegg_listing_source_seal()
                .ok_or(FheggSettlementError::UnboundListingSource)?,
        );
        hasher.update(&listing.session_digest);
        hasher.update(&listing.binding_digest);
        hasher.update(&listing.message_digest);
        hasher.update(&listing.ciphertext_digest);
        hasher.update(&(self.market.bids.len() as u64).to_be_bytes());
        for placed in &self.market.bids {
            let source = placed
                .fhegg_source
                .ok_or(FheggSettlementError::UnboundSource { slot: placed.slot })?;
            hasher.update(&(placed.who.0.len() as u64).to_be_bytes());
            hasher.update(placed.who.0.as_bytes());
            hasher.update(&[placed.handle]);
            hasher.update(&(placed.slot as u64).to_be_bytes());
            hasher.update(&placed.seal());
            hasher.update(&source.session_digest);
            hasher.update(&source.binding_digest);
            hasher.update(&source.message_digest);
            hasher.update(&source.ciphertext_digest);
        }
        Ok(*hasher.finalize().as_bytes())
    }

    /// Exact ordered-input pairs independently frozen into the seller's listing
    /// source slot and every source-bound bid seal. A producer includes these
    /// pairs in its canonical order batch; settlement requires each adjacent
    /// pair exactly once.
    pub fn fhegg_bound_order_inputs(&self) -> Result<Vec<InputDigest>, FheggSettlementError> {
        let listing = self
            .market
            .fhegg_listing_source
            .ok_or(FheggSettlementError::UnboundListingSource)?;
        let mut inputs = Vec::with_capacity((self.market.bids.len() + 1) * 2);
        inputs.push(InputDigest::commitment(listing.message_digest));
        inputs.push(InputDigest {
            kind: InputDigestKind::Ciphertext,
            digest: listing.ciphertext_digest,
        });
        for placed in &self.market.bids {
            let source = placed
                .fhegg_source
                .ok_or(FheggSettlementError::UnboundSource { slot: placed.slot })?;
            inputs.push(InputDigest::commitment(source.message_digest));
            inputs.push(InputDigest {
                kind: InputDigestKind::Ciphertext,
                digest: source.ciphertext_digest,
            });
        }
        Ok(inputs)
    }

    /// Verify that every source-bound bid's signed-message/ciphertext pair
    /// occurs exactly once and adjacently in a proposed canonical fhEgg input
    /// list. This is exposed separately so ingress and transport boundaries can
    /// fail before any computation evidence or replay state is consumed.
    pub fn verify_fhegg_bound_order_inputs(
        &self,
        ordered_inputs: &[InputDigest],
    ) -> Result<(), FheggSettlementError> {
        let pairs = self.fhegg_bound_order_inputs()?;
        let listing_pair = &pairs[..2];
        let found = ordered_inputs
            .windows(2)
            .filter(|window| *window == listing_pair)
            .count();
        if found != 1 {
            return Err(FheggSettlementError::ListingSourceInputPairCount { found });
        }
        for (bid, pair) in pairs[2..].chunks_exact(2).enumerate() {
            let found = ordered_inputs
                .windows(2)
                .filter(|window| *window == pair)
                .count();
            if found != 1 {
                return Err(FheggSettlementError::SourceInputPairCount { bid, found });
            }
        }
        Ok(())
    }

    /// Require every exact-opening certificate to name the same BFV
    /// parameter/public-key domain independently retained by the settlement
    /// verifier. Ciphertext byte equality alone is not accepted as this join.
    pub fn verify_fhegg_source_bfv_identity(
        &self,
        bfv: &BfvPublicIdentity,
        buckets: usize,
    ) -> Result<(), FheggSettlementError> {
        let nonce = self
            .fhegg_order_ingress_nonce()
            .map_err(|_| FheggSettlementError::NotListed)?;
        let expected = OrderIngressSession::digest_for_bfv_identity(nonce, buckets, bfv)
            .map_err(|_| FheggSettlementError::ListingSourceBfvDomainMismatch)?;
        let listing = self
            .market
            .fhegg_listing_source
            .ok_or(FheggSettlementError::UnboundListingSource)?;
        if listing.session_digest != expected {
            return Err(FheggSettlementError::ListingSourceBfvDomainMismatch);
        }
        for (bid, placed) in self.market.bids.iter().enumerate() {
            let source = placed
                .fhegg_source
                .ok_or(FheggSettlementError::UnboundSource { slot: placed.slot })?;
            if source.session_digest != expected {
                return Err(FheggSettlementError::SourceBfvDomainMismatch { bid });
            }
        }
        Ok(())
    }

    /// Canonical ordered-input item a fhEgg producer must append exactly once
    /// when constructing the independently retained clearing context.
    pub fn fhegg_source_input(&self) -> Result<InputDigest, FheggSettlementError> {
        Ok(InputDigest::commitment(self.fhegg_source_commitment()?))
    }

    /// MPC session nonce required by the settlement gate. Deriving it from the
    /// exact live-board commitment makes cross-session and altered-board replay
    /// fail before computation evidence or market state is consumed.
    pub fn fhegg_settlement_session_nonce(&self) -> Result<Digest32, FheggSettlementError> {
        let source = self.fhegg_source_commitment()?;
        Ok(*blake3::Hasher::new_derive_key(SESSION_DOMAIN)
            .update(&source)
            .finalize()
            .as_bytes())
    }
}

impl DarkBazaarOffering {
    /// Fully verify an authenticated fhEgg clearing against independently
    /// supplied public objects and the live sealed board, then drive the real
    /// executor SETTLE. Every represented mismatch is rejected before mutation.
    pub fn settle_fhegg_verified<V: ComputationIntegrityVerifier, R: ReplayGuard>(
        &self,
        session: &mut DarkBazaarSession,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
    ) -> Result<FheggSettlementReceipt, FheggSettlementError> {
        let live = live_clear(session)?;
        let source_commitment = session.fhegg_source_commitment()?;
        let expected_nonce = session.fhegg_settlement_session_nonce()?;

        if expected.session.nonce() != expected_nonce {
            return Err(FheggSettlementError::SessionMismatch);
        }
        let found = expected
            .ordered_inputs
            .iter()
            .filter(|input| {
                input.kind == InputDigestKind::Commitment && input.digest == source_commitment
            })
            .count();
        if found != 1 {
            return Err(FheggSettlementError::SourceCommitmentCount { found });
        }
        session.verify_fhegg_source_bfv_identity(expected.bfv, expected.session.buckets())?;
        session.verify_fhegg_bound_order_inputs(expected.ordered_inputs)?;
        if expected.crossing.p_star != Some(live.price as usize) || expected.crossing.v_star != 1 {
            return Err(FheggSettlementError::ResultMismatch {
                expected_price: live.price,
                claimed_price: expected.crossing.p_star,
                claimed_volume: expected.crossing.v_star,
            });
        }

        // Binding is checked explicitly before the evidence verifier/replay gate,
        // keeping failed context substitutions side-effect-free.
        receipt.verify_binding(expected)?;
        receipt.verify_full(expected, verifier, replay_guard)?;

        let settlement_turn = match self.market.do_settle(&mut session.market) {
            Outcome::Landed {
                receipt,
                ended: true,
            } => receipt,
            Outcome::Landed { ended: false, .. } => {
                return Err(FheggSettlementError::PostSettlementMismatch(
                    "SETTLE landed without ending the auction",
                ));
            }
            Outcome::Refused(why) => return Err(FheggSettlementError::SettlementRefused(why)),
        };

        let clearing = session.market.clearing.as_ref().ok_or(
            FheggSettlementError::PostSettlementMismatch("no clearing was recorded"),
        )?;
        if clearing.winner.value != i128::from(live.price) {
            return Err(FheggSettlementError::PostSettlementMismatch(
                "recorded winning price differs from authenticated p*",
            ));
        }
        let winner = session.winning_actor().cloned().ok_or(
            FheggSettlementError::PostSettlementMismatch("recorded winning handle has no actor"),
        )?;
        if winner != live.winner {
            return Err(FheggSettlementError::PostSettlementMismatch(
                "winner differs from sealed-board preflight",
            ));
        }

        Ok(FheggSettlementReceipt {
            claim_digest: receipt.claim_digest(),
            source_commitment,
            price: live.price,
            volume: 1,
            winner,
            settlement_turn,
        })
    }
}

fn preflight_board(session: &DarkBazaarSession) -> Result<(), FheggSettlementError> {
    if !session.market.is_listed() {
        return Err(FheggSettlementError::NotListed);
    }
    if session.market.is_settled() {
        return Err(FheggSettlementError::AlreadySettled);
    }
    let phase = session.market.phase();
    if phase != Some(Phase::Commit) || session.market.onledger_phase() != Some(0) {
        return Err(FheggSettlementError::PhaseNotCommit(phase));
    }
    if session.market.bids.is_empty() {
        return Err(FheggSettlementError::NoBids);
    }
    let cell = session
        .market
        .auction_cell
        .ok_or(FheggSettlementError::MissingAuctionCell)?;
    let state = session
        .market
        .executor
        .cell_state(cell)
        .ok_or(FheggSettlementError::MissingAuctionCell)?;
    let listing_seal = session
        .market
        .fhegg_listing_source_seal()
        .ok_or(FheggSettlementError::UnboundListingSource)?;
    if state.fields[FHEGG_LISTING_SOURCE_SLOT] != listing_seal {
        return Err(FheggSettlementError::ListingSourceBoardMismatch);
    }
    for placed in &session.market.bids {
        if state.fields[placed.slot] != placed.seal() {
            return Err(FheggSettlementError::SourceBoardMismatch { slot: placed.slot });
        }
    }
    Ok(())
}

pub(crate) fn live_clear(session: &DarkBazaarSession) -> Result<LiveClear, FheggSettlementError> {
    preflight_board(session)?;
    let placed = session
        .market
        .bids
        .iter()
        .max_by_key(|placed| (placed.bid.value, placed.seal()))
        .expect("preflight requires a nonempty book");
    let high = placed.bid.value;
    if high < session.market.reserve {
        return Err(FheggSettlementError::BelowReserve {
            high,
            reserve: session.market.reserve,
        });
    }
    let price = u64::try_from(high).map_err(|_| FheggSettlementError::PriceOutOfRange(high))?;
    Ok(LiveClear {
        price,
        winner: placed.who.clone(),
    })
}
