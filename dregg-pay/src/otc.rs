//! [`otc_quote`] — the friendly over-the-counter desk: a user brings USDC and buys
//! `$DREGG` out of the treasury's pile at a discount.
//!
//! # The economics
//!
//! The pile ([`Treasury::dregg_balance`](crate::treasury::Treasury::dregg_balance))
//! accumulates from `$DREGG`-paid runs and is otherwise illiquid. The OTC desk turns
//! it into a service: a user brings `usdc_in` USDC and receives `$DREGG` priced at the
//! live oracle rate MINUS [`PayConfig::otc_discount_bps`] (default 10%) — i.e. the
//! user buys `$DREGG` cheaper than market, a friendly fill that also refuels the
//! treasury with the incoming USDC.
//!
//! `dregg_out = usd_in / (oracle_price × (1 − otc_discount))`
//!
//! # Scope — quote + accounting only
//!
//! [`otc_quote`] computes the fill and checks the pile can cover it (a precise refusal
//! otherwise). It does **not** move funds. The actual `$DREGG` transfer to the buyer
//! executes behind the operator's signer — the deferred [`crate::sweeper::SolanaSweeper`]
//! /operator-signed settlement (`otc_settle`, a follow-up). Custody is the seed/signer.

use crate::config::{DepositAddress, PayConfig};
use crate::pricing::{PriceError, PriceOracle, discount_factor};
use crate::swap::{Signer, SignerError};
use crate::treasury::{Treasury, TreasuryStore};
use ed25519_dalek::{Signature, Verifier as _, VerifyingKey};

/// A computed OTC fill: bring `usdc_in`, receive `dregg_out`, at the discounted rate.
#[derive(Clone, Debug, PartialEq)]
pub struct OtcQuote {
    /// Atomic USDC the user brings in (fuels the treasury).
    pub usdc_in: u64,
    /// Atomic `$DREGG` the user receives out of the pile.
    pub dregg_out: u64,
    /// The oracle mid price (USD per whole `$DREGG`) the quote was fed from.
    pub oracle_price_usd: f64,
    /// The OTC discount applied, in basis points.
    pub discount_bps: u32,
    /// The effective price per whole `$DREGG` the user pays (`oracle × (1 − disc)`).
    pub effective_price_usd: f64,
    /// The pile balance (atomic `$DREGG`) the quote was checked against.
    pub pile_balance: u64,
}

/// Why an OTC quote could not be filled.
#[derive(Clone, Debug, PartialEq)]
pub enum OtcError {
    /// The price oracle was unavailable / invalid — no fill can be priced.
    PriceUnavailable(PriceError),
    /// The pile cannot cover the fill — a precise refusal (need vs have).
    InsufficientPile {
        /// Atomic `$DREGG` the fill requires.
        needed: u64,
        /// Atomic `$DREGG` currently in the pile.
        available: u64,
    },
}

impl std::fmt::Display for OtcError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OtcError::PriceUnavailable(e) => write!(f, "OTC price unavailable: {e}"),
            OtcError::InsufficientPile { needed, available } => write!(
                f,
                "OTC pile short: need {needed} atomic $DREGG, pile has {available}"
            ),
        }
    }
}

impl std::error::Error for OtcError {}

impl From<PriceError> for OtcError {
    fn from(e: PriceError) -> Self {
        OtcError::PriceUnavailable(e)
    }
}

/// The `$DREGG`-out (atomic) a `usdc_in` (atomic) fill yields at the discounted rate —
/// the pure pricing, without the pile check. Floors to whole atomic units.
pub fn otc_dregg_out(
    usdc_in: u64,
    oracle_price: f64,
    config: &PayConfig,
) -> Result<u64, PriceError> {
    if config.otc_discount_bps >= 10_000 {
        return Err(PriceError::InvalidDiscount(config.otc_discount_bps));
    }
    let (oracle_num, oracle_den) = crate::pricing::decimal_ratio(oracle_price)?;
    crate::pricing::mul_div_floor(
        vec![
            usdc_in as u128,
            oracle_den,
            10_000,
            crate::pricing::pow10(config.dregg_decimals)?,
        ],
        vec![
            crate::pricing::pow10(config.usdc_decimals)?,
            oracle_num,
            (10_000 - config.otc_discount_bps) as u128,
        ],
    )
}

/// Quote an OTC fill: a user brings `usdc_in` atomic USDC and buys `$DREGG` out of the
/// pile (`pile_balance` atomic `$DREGG`) at the oracle price minus the OTC discount.
///
/// Fails closed: an unavailable price → [`OtcError::PriceUnavailable`]; a pile that
/// cannot cover the fill → [`OtcError::InsufficientPile`] with the exact shortfall.
/// This is QUOTE + ACCOUNTING only — the `$DREGG` transfer executes behind the
/// operator's signer (the deferred `otc_settle`).
pub fn otc_quote(
    usdc_in: u64,
    pile_balance: u64,
    oracle: &dyn PriceOracle,
    config: &PayConfig,
) -> Result<OtcQuote, OtcError> {
    let oracle_price = oracle.dregg_usd_price()?;
    let effective_price_usd = oracle_price * discount_factor(config.otc_discount_bps);
    let dregg_out = otc_dregg_out(usdc_in, oracle_price, config)?;
    if dregg_out > pile_balance {
        return Err(OtcError::InsufficientPile {
            needed: dregg_out,
            available: pile_balance,
        });
    }
    Ok(OtcQuote {
        usdc_in,
        dregg_out,
        oracle_price_usd: oracle_price,
        discount_bps: config.otc_discount_bps,
        effective_price_usd,
        pile_balance,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// otc_settle — the deferred, signer-gated OTC settlement
// ─────────────────────────────────────────────────────────────────────────────

/// A completed OTC settlement: the `$DREGG` moved to the buyer + the USDC-in recorded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OtcSettlement {
    /// The buyer the `$DREGG` was transferred to.
    pub buyer: DepositAddress,
    /// Atomic `$DREGG` moved out of the pile to the buyer.
    pub dregg_out: u64,
    /// Atomic USDC recorded in from the buyer (fuels the treasury).
    pub usdc_in: u64,
    /// The pile balance (atomic `$DREGG`) after the settlement.
    pub pile_after: u64,
    /// The fuel balance (atomic USDC) after the settlement.
    pub fuel_after: u64,
    /// The settlement transaction reference (the operator-signed transfer's signature on
    /// the real path; a synthetic id on the mock path).
    pub reference: String,
}

/// Why an OTC settlement was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtcSettleError {
    /// The pile can no longer cover the quoted fill — fail closed (need vs have). Reuses
    /// [`otc_quote`]'s pile check at settle time (the pile may have shrunk since quoting).
    InsufficientPile {
        /// Atomic `$DREGG` the settlement needs.
        needed: u64,
        /// Atomic `$DREGG` currently in the pile.
        available: u64,
    },
    /// The operator signer failed.
    Signer(SignerError),
}

impl std::fmt::Display for OtcSettleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OtcSettleError::InsufficientPile { needed, available } => write!(
                f,
                "OTC settle refused: pile short — need {needed} atomic $DREGG, have {available}"
            ),
            OtcSettleError::Signer(e) => write!(f, "OTC settle refused: {e}"),
        }
    }
}

impl std::error::Error for OtcSettleError {}

impl From<SignerError> for OtcSettleError {
    fn from(e: SignerError) -> Self {
        OtcSettleError::Signer(e)
    }
}

/// The canonical bytes an OTC settlement SIGNS — binds `buyer ‖ usdc_in ‖ dregg_out` so an
/// operator signature can't be replayed onto a different fill.
pub fn otc_settle_message(buyer: &DepositAddress, usdc_in: u64, dregg_out: u64) -> Vec<u8> {
    let mut m = Vec::with_capacity(22 + 32 + 8 + 8);
    m.extend_from_slice(b"dregg-pay/otc-settle/v1");
    m.extend_from_slice(&buyer.to_bytes());
    m.extend_from_slice(&usdc_in.to_le_bytes());
    m.extend_from_slice(&dregg_out.to_le_bytes());
    m
}

/// Settle a previously-computed [`OtcQuote`], **behind the operator's signer**: move the
/// quoted `$DREGG` out of the pile to `buyer` and record the USDC-in as fuel.
///
/// Fail closed: RE-checks the pile can still cover the fill ([`OtcSettleError::InsufficientPile`]
/// — reusing [`otc_quote`]'s check shape, since the pile may have shrunk since the quote)
/// BEFORE anything moves; a signer failure refuses with no move. The operator [`Signer`]
/// signs the `$DREGG` transfer ([`otc_settle_message`]); the real on-chain transfer
/// executes behind that signature — `dregg-pay` holds no key.
pub fn otc_settle<S: TreasuryStore>(
    quote: &OtcQuote,
    buyer: &DepositAddress,
    signer: &dyn Signer,
    treasury: &Treasury<S>,
) -> Result<OtcSettlement, OtcSettleError> {
    // Fail closed FIRST: the pile must still cover the fill (the quote may be stale).
    let pile = treasury.dregg_balance();
    if quote.dregg_out > pile {
        return Err(OtcSettleError::InsufficientPile {
            needed: quote.dregg_out,
            available: pile,
        });
    }

    // The operator signs the $DREGG transfer to the buyer (no key in dregg-pay).
    let message = otc_settle_message(buyer, quote.usdc_in, quote.dregg_out);
    let signature = signer.sign(&message)?;
    // Verify the operator signature (a custody sanity tooth — real ed25519, no network).
    if let Ok(vk) = VerifyingKey::from_bytes(&signer.public_key()) {
        if let Ok(sig) = Signature::from_slice(&signature) {
            if vk.verify(&message, &sig).is_err() {
                return Err(OtcSettleError::Signer(SignerError::Backend(
                    "operator signature failed to verify".into(),
                )));
            }
        }
    }

    // Move: pile DOWN to the buyer, USDC-in recorded as fuel.
    let pile_after =
        treasury
            .withdraw_dregg(quote.dregg_out)
            .map_err(|_| OtcSettleError::InsufficientPile {
                needed: quote.dregg_out,
                available: treasury.dregg_balance(),
            })?;
    let fuel_after = treasury.deposit_usdc(quote.usdc_in);

    Ok(OtcSettlement {
        buyer: *buyer,
        dregg_out: quote.dregg_out,
        usdc_in: quote.usdc_in,
        pile_after,
        fuel_after,
        reference: format!("mock-otc-settle:{}:{}", buyer.to_base58(), quote.dregg_out),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::DepositAddress;
    use crate::pricing::MockOracle;
    use crate::swap::MockSigner;
    use crate::treasury::{InMemoryTreasuryStore, Treasury};

    fn cfg() -> PayConfig {
        PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            [0x11u8; 32],
            DepositAddress([0xEEu8; 32]),
            1_000_000,
        )
    }

    #[test]
    fn quote_gives_dregg_out_at_ten_percent_off() {
        let c = cfg(); // otc_discount_bps = 1000 (10%)
        let oracle = MockOracle::new(0.005); // $0.005 per whole $DREGG
        // Bring $1.00 = 1_000_000 atomic USDC. Effective price = 0.005 * 0.9 = 0.0045.
        // dregg_out_whole = 1.00 / 0.0045 = 222.222…  → 222_222_222 atomic (6 dp).
        let pile = 1_000_000_000u64; // plenty
        let q = otc_quote(1_000_000, pile, &oracle, &c).unwrap();
        assert!((q.effective_price_usd - 0.0045).abs() < 1e-9);
        assert_eq!(q.dregg_out, 222_222_222);
        // Sanity: without the discount it would be 200_000_000 — the buyer gets MORE.
        let at_market = (1.0 / 0.005 * 1_000_000.0) as u64;
        assert_eq!(at_market, 200_000_000);
        assert!(
            q.dregg_out > at_market,
            "discount gives the buyer more $DREGG"
        );
    }

    #[test]
    fn quote_refused_precisely_when_pile_short() {
        let c = cfg();
        let oracle = MockOracle::new(0.005);
        // Same $1.00 wants 222_222_222 atomic; pile has only 100_000_000.
        let err = otc_quote(1_000_000, 100_000_000, &oracle, &c).unwrap_err();
        assert_eq!(
            err,
            OtcError::InsufficientPile {
                needed: 222_222_222,
                available: 100_000_000
            }
        );
    }

    #[test]
    fn quote_fails_closed_on_bad_price() {
        let c = cfg();
        let bad = MockOracle::new(0.0);
        assert!(matches!(
            otc_quote(1_000_000, u64::MAX, &bad, &c),
            Err(OtcError::PriceUnavailable(_))
        ));
    }

    #[test]
    fn quote_refuses_a_free_fill_discount() {
        let mut c = cfg();
        c.otc_discount_bps = 10_000;
        let err = otc_quote(1, u64::MAX, &MockOracle::new(0.005), &c).unwrap_err();
        assert_eq!(
            err,
            OtcError::PriceUnavailable(PriceError::InvalidDiscount(10_000))
        );
    }

    fn seeded_treasury(pile: u64) -> Treasury<InMemoryTreasuryStore> {
        let t = Treasury::new(InMemoryTreasuryStore::new(), 6);
        t.deposit_dregg(pile);
        t
    }

    #[test]
    fn otc_settle_moves_pile_to_buyer_and_records_usdc_mock_signed() {
        let c = cfg();
        let oracle = MockOracle::new(0.005);
        // Bring $1.00 → 222_222_222 atomic $DREGG. Pile has plenty.
        let pile = 1_000_000_000u64;
        let t = seeded_treasury(pile);
        let quote = otc_quote(1_000_000, t.dregg_balance(), &oracle, &c).unwrap();

        let buyer = DepositAddress([0xAB; 32]);
        let signer = MockSigner::from_seed([5u8; 32]);
        let settled = otc_settle(&quote, &buyer, &signer, &t).unwrap();

        assert_eq!(settled.dregg_out, 222_222_222);
        assert_eq!(settled.usdc_in, 1_000_000);
        assert_eq!(settled.buyer, buyer);
        // Pile DOWN by the fill; USDC-in recorded as fuel.
        assert_eq!(t.dregg_balance(), pile - 222_222_222);
        assert_eq!(settled.pile_after, pile - 222_222_222);
        assert_eq!(t.usdc_balance(), 1_000_000, "USDC-in recorded as fuel");
        assert_eq!(settled.fuel_after, 1_000_000);
    }

    #[test]
    fn otc_settle_refuses_when_pile_short_no_move() {
        let c = cfg();
        let oracle = MockOracle::new(0.005);
        // Quote against a fat pile, then settle against a treasury that only has a little.
        let quote = otc_quote(1_000_000, 1_000_000_000, &oracle, &c).unwrap();
        assert_eq!(quote.dregg_out, 222_222_222);

        let t = seeded_treasury(100_000_000); // pile shrank below the quote
        let buyer = DepositAddress([0xAB; 32]);
        let signer = MockSigner::from_seed([5u8; 32]);
        let err = otc_settle(&quote, &buyer, &signer, &t).unwrap_err();
        assert_eq!(
            err,
            OtcSettleError::InsufficientPile {
                needed: 222_222_222,
                available: 100_000_000
            }
        );
        // Nothing moved on the refusal.
        assert_eq!(t.dregg_balance(), 100_000_000);
        assert_eq!(t.usdc_balance(), 0);
    }
}
