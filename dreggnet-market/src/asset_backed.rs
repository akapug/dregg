//! A real owned-asset settlement weld for the sealed auction.
//!
//! The auction cell and verified ring decide the winner and price. This module then
//! consumes that exact result to settle an existing [`AssetId`] through
//! [`dreggnet_trade`]'s owner-gated, sealed-escrow atomic swap. It is the narrow
//! engine seam needed by The Descent: a fair-drawn loot note can cross to the Bazaar
//! winner without being re-minted into a synthetic market universe.
//!
//! Honest boundary: this is an additive post-clear weld. The current `Offering`
//! crawl first commits its auction resolve turn and then a caller invokes
//! [`MarketSession::settle_winning_asset`]. The asset/value cross itself is atomic,
//! but auction resolution and the cross are not yet one indivisible multi-cell turn.

use dreggnet_offerings::DreggIdentity;
use dreggnet_trade::{AssetId, ProvenanceReport, Settlement, TradeError, TradeWorld};

use crate::MarketSession;

/// A real asset/value crossing derived from a verified sealed-auction clear.
#[derive(Clone, Debug)]
pub struct AssetBackedClearing {
    /// The stable asset id that crossed; its lineage is extended, not restarted.
    pub asset: AssetId,
    /// The seller identity already bound by the auction's LIST action.
    pub seller: DreggIdentity,
    /// The actor whose sealed bid won the verified clear.
    pub winner: DreggIdentity,
    /// The exact winning price paid in `$DREGG`.
    pub price: u64,
    /// The sealed-escrow settlement receipt for the asset/value legs.
    pub settlement: Settlement,
    /// Re-verification of the asset lineage after it crossed to the winner.
    pub provenance: ProvenanceReport,
}

/// Why a verified auction result could not be welded to an owned-asset cross.
#[derive(Debug)]
pub enum AssetBackedError {
    /// The auction has not landed a verified clear yet.
    AuctionNotSettled,
    /// The recorded winner handle does not map back to a committed bidder actor.
    WinnerActorMissing,
    /// The clear lacks the seller identity bound by LIST.
    SellerMissing,
    /// The winning price cannot be represented by the `$DREGG` value leg.
    PriceOutOfRange(i128),
    /// The owner gate, value balance, or sealed escrow refused the cross.
    Trade(TradeError),
    /// The asset crossed but its committed lineage did not re-verify.
    ProvenanceBroken(Vec<String>),
}

impl std::fmt::Display for AssetBackedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AuctionNotSettled => write!(f, "the sealed auction has not settled"),
            Self::WinnerActorMissing => {
                write!(f, "the winning bidder handle has no recorded actor")
            }
            Self::SellerMissing => write!(f, "the auction has no recorded seller"),
            Self::PriceOutOfRange(price) => {
                write!(f, "winning price {price} is outside the $DREGG value range")
            }
            Self::Trade(e) => write!(f, "owned-asset settlement refused: {e}"),
            Self::ProvenanceBroken(reasons) => {
                write!(
                    f,
                    "the crossed asset's provenance broke: {}",
                    reasons.join("; ")
                )
            }
        }
    }
}

impl std::error::Error for AssetBackedError {}

impl From<TradeError> for AssetBackedError {
    fn from(value: TradeError) -> Self {
        Self::Trade(value)
    }
}

impl MarketSession {
    /// The actor whose sealed bid won the verified clear.
    pub fn winning_actor(&self) -> Option<&DreggIdentity> {
        let winner = self.clearing.as_ref()?.winner.bidder;
        self.bids
            .iter()
            .find(|placed| placed.handle == winner)
            .map(|placed| &placed.who)
    }

    /// Settle an existing owned asset to the verified winner at the verified price.
    ///
    /// `world` must be the world that already contains `asset`; for Descent loot,
    /// obtain it from `LootVault::into_assets()` and adopt it with
    /// `TradeWorld::with_assets`. The seller and buyer labels are the exact opaque
    /// `DreggIdentity` strings used by LIST/BID, so the asset signature gate and the
    /// auction attribution name the same parties.
    pub fn settle_winning_asset(
        &self,
        world: &mut TradeWorld,
        asset: AssetId,
    ) -> Result<AssetBackedClearing, AssetBackedError> {
        let clearing = self
            .clearing
            .as_ref()
            .ok_or(AssetBackedError::AuctionNotSettled)?;
        let seller = self.seller.clone().ok_or(AssetBackedError::SellerMissing)?;
        let winner = self
            .winning_actor()
            .cloned()
            .ok_or(AssetBackedError::WinnerActorMissing)?;
        let price = u64::try_from(clearing.winner.value)
            .map_err(|_| AssetBackedError::PriceOutOfRange(clearing.winner.value))?;

        // `list` checks that the LIST actor still owns this exact AssetId. `buy`
        // opens the asset<->$DREGG escrow, deposits both legs, and either crosses
        // both or returns the asset to the seller on buyer shortfall.
        let mut listing = world.list(seller.as_str(), asset, price)?;
        let settlement = world.buy(&mut listing, winner.as_str())?;
        let provenance = world.verify_provenance(asset);
        if !provenance.verified {
            return Err(AssetBackedError::ProvenanceBroken(provenance.reasons));
        }

        Ok(AssetBackedClearing {
            asset,
            seller,
            winner,
            price,
            settlement,
            provenance,
        })
    }
}
