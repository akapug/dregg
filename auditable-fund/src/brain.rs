//! The **decision brain** — what the fund decides, each turn attested.
//!
//! A [`Brain`] reasons from a [`MarketView`] (attested prices for the mandate's assets) to a
//! [`Decision`]. In the fund's default path the decision is turned into an ATTESTED turn
//! (`deos-hermes::AttestationCarrier::attest_turn`): the model's own words this turn are bound
//! authentic ∧ well-formed ∧ injection-free. By default the brain is a RECORDED / modeled one
//! ([`RecordedBrain`], [`ThresholdBrain`]) — no live model provider, fully deterministic — so
//! the whole produce→attest→land→audit chain runs hermetically and green.

use crate::oracle::AttestedPrice;

/// The side of a decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    /// Buy `qty` units of the asset (draws cash).
    Buy,
    /// Sell `qty` units of the asset (releases cash).
    Sell,
    /// Take no position this turn (still an attested, on-ledger turn).
    Hold,
}

impl Side {
    /// A stable tag byte, folded into the trade commitment.
    pub fn tag(self) -> u8 {
        match self {
            Side::Buy => 1,
            Side::Sell => 2,
            Side::Hold => 0,
        }
    }

    /// A short label for the on-ledger action.
    pub fn label(self) -> &'static str {
        match self {
            Side::Buy => "buy",
            Side::Sell => "sell",
            Side::Hold => "hold",
        }
    }
}

/// A brain's decision for one turn. Its [`Decision::text`] is what the attestation binds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decision {
    /// Buy / sell / hold.
    pub side: Side,
    /// The asset (empty for a hold).
    pub asset: String,
    /// Units to trade (0 for a hold).
    pub qty: i64,
    /// The model's free-text rationale (bound, injection-free, by the attestation).
    pub rationale: String,
}

impl Decision {
    /// A buy decision.
    pub fn buy(asset: &str, qty: i64, rationale: &str) -> Decision {
        Decision {
            side: Side::Buy,
            asset: asset.to_string(),
            qty,
            rationale: rationale.to_string(),
        }
    }

    /// A sell decision.
    pub fn sell(asset: &str, qty: i64, rationale: &str) -> Decision {
        Decision {
            side: Side::Sell,
            asset: asset.to_string(),
            qty,
            rationale: rationale.to_string(),
        }
    }

    /// A hold decision.
    pub fn hold(rationale: &str) -> Decision {
        Decision {
            side: Side::Hold,
            asset: String::new(),
            qty: 0,
            rationale: rationale.to_string(),
        }
    }

    /// The exact text the attestation binds this turn — the model's reasoning, rendered
    /// injection-free-friendly (no `{{`, JSON-safe once the carrier cleans it).
    pub fn text(&self) -> String {
        format!(
            "DECISION side={} asset={} qty={} because {}",
            self.side.label(),
            if self.asset.is_empty() {
                "-"
            } else {
                &self.asset
            },
            self.qty,
            self.rationale,
        )
    }

    /// The short on-ledger action label for this decision.
    pub fn label(&self) -> String {
        match self.side {
            Side::Hold => "hold".to_string(),
            _ => format!("{}:{}:{}", self.side.label(), self.asset, self.qty),
        }
    }
}

/// The attested market the brain reasons over: the mandate's assets, each at an attested
/// price. The brain sees prices it (and later, an auditor) can prove.
#[derive(Clone, Debug)]
pub struct MarketView {
    /// Attested price per asset, keyed by asset.
    pub prices: std::collections::BTreeMap<String, AttestedPrice>,
}

impl MarketView {
    /// The attested amount for `asset` in cents, if quoted this round (parsed from the
    /// notarized decimal-USD amount).
    pub fn amount(&self, asset: &str) -> Option<i64> {
        self.prices
            .get(asset)
            .and_then(|p| crate::oracle::amount_to_cents(&p.amount).ok())
    }
}

/// A decision brain. The fund calls [`Brain::decide`] once per turn.
pub trait Brain {
    /// Decide this turn from the attested market view.
    fn decide(&mut self, view: &MarketView) -> Decision;
}

/// A RECORDED brain — replays a fixed script of decisions (the default, deterministic,
/// no-live-model path). Once the script is exhausted it holds.
pub struct RecordedBrain {
    script: std::collections::VecDeque<Decision>,
}

impl RecordedBrain {
    /// A recorded brain from an ordered script of decisions.
    pub fn new(script: Vec<Decision>) -> RecordedBrain {
        RecordedBrain {
            script: script.into(),
        }
    }
}

impl Brain for RecordedBrain {
    fn decide(&mut self, _view: &MarketView) -> Decision {
        self.script
            .pop_front()
            .unwrap_or_else(|| Decision::hold("script exhausted"))
    }
}

/// A simple modeled momentum brain: buy `qty` of `asset` when its attested price is at or
/// below `buy_below`, sell when at or above `sell_above`, else hold. Deterministic — a stand
/// in for a live model, useful in examples.
pub struct ThresholdBrain {
    /// The asset this brain watches.
    pub asset: String,
    /// Buy when the attested price is at or below this.
    pub buy_below: i64,
    /// Sell when the attested price is at or above this.
    pub sell_above: i64,
    /// Units per trade.
    pub qty: i64,
}

impl Brain for ThresholdBrain {
    fn decide(&mut self, view: &MarketView) -> Decision {
        match view.amount(&self.asset) {
            Some(p) if p <= self.buy_below => {
                Decision::buy(&self.asset, self.qty, "price at/below the buy threshold")
            }
            Some(p) if p >= self.sell_above => {
                Decision::sell(&self.asset, self.qty, "price at/above the sell threshold")
            }
            _ => Decision::hold("price inside the no-trade band"),
        }
    }
}
