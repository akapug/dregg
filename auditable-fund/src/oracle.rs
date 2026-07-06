//! The **price oracle** — every price the fund trades on is a REAL zkOracle attestation.
//!
//! The fund NEVER fills at a bare number. A price is a [`dregg_zkoracle_prove::AttestedPrice`]:
//! a Coinbase spot quote bound to a [`dregg_zkoracle_prove::ZkOracleAttestation`] — authentic
//! (a genuine `api.coinbase.com` TLS session, notary-signed) ∧ well-formed (the response body
//! lies in the JSON CFG) ∧ injection-free (a read-only quote has no user field). This is the
//! REAL price lane [`dregg_zkoracle_prove::endpoints::price`] exposes; the fund composes it
//! directly through the [`PriceOracle`] interface. There is no modeled price stub any more —
//! every simulated fill is at a price a third party re-verifies with [`verify_coinbase_spot`].
//!
//! [`CoinbaseSpotOracle`] is the real (fixture-backed) implementation. A LIVE implementation
//! swaps the fixture for the `tlsn-live` MPC-TLS roundtrip against `api.coinbase.com` — the
//! SAME [`PriceOracle`] interface, so the fund composes it unchanged. That live wire is the
//! named operational remainder; everything here runs green, at real attested prices.
//!
//! ## Denomination — attested decimal USD → integer cents
//!
//! Coinbase returns a decimal USD string (`"64250.37"`, no float rounding). The fund's book is
//! integer **cents**; [`amount_to_cents`] converts the *attested* amount into cents. Both the
//! fill and the audit run the conversion over the SAME notarized amount, so the fund can never
//! book a cent it cannot prove.

use dregg_zkoracle_prove::verify_coinbase_spot;

pub use dregg_zkoracle_prove::PriceError as ZkPriceError;
pub use dregg_zkoracle_prove::{
    AttestedPrice, CoinbaseSpotOracle, EndpointConfig, FixtureNotary, PriceOracle,
    coinbase_spot_spec,
};

/// **Parse an attested Coinbase decimal-USD amount into integer cents.** `"64250.37"` →
/// `6_425_037`, `"1000"` → `100_000`. Truncates beyond two fractional digits (cents are the
/// book's unit). A non-numeric amount is a [`PriceError::Unparseable`] — the fund refuses a
/// price it cannot denominate, rather than guess.
pub fn amount_to_cents(amount: &str) -> Result<i64, PriceError> {
    let amount = amount.trim();
    let neg = amount.starts_with('-');
    let body = amount.strip_prefix('-').unwrap_or(amount);
    let (int_part, frac_part) = match body.split_once('.') {
        Some((i, f)) => (i, f),
        None => (body, ""),
    };
    if int_part.is_empty() && frac_part.is_empty() {
        return Err(PriceError::Unparseable(amount.to_string()));
    }
    if !int_part.chars().all(|c| c.is_ascii_digit())
        || !frac_part.chars().all(|c| c.is_ascii_digit())
    {
        return Err(PriceError::Unparseable(amount.to_string()));
    }
    let dollars: i64 = if int_part.is_empty() {
        0
    } else {
        int_part
            .parse::<i64>()
            .map_err(|_| PriceError::Unparseable(amount.to_string()))?
    };
    // Two-digit cents: pad or truncate the fractional part.
    let mut cents_str = frac_part.to_string();
    while cents_str.len() < 2 {
        cents_str.push('0');
    }
    cents_str.truncate(2);
    let cents: i64 = cents_str
        .parse::<i64>()
        .map_err(|_| PriceError::Unparseable(amount.to_string()))?;
    let total = dollars
        .checked_mul(100)
        .and_then(|d| d.checked_add(cents))
        .ok_or_else(|| PriceError::Unparseable(amount.to_string()))?;
    Ok(if neg { -total } else { total })
}

/// **Verify an attested price and return its fill amount in cents** — the check every fill and
/// every audit runs. It (1) re-verifies the zkOracle attestation against the pinned oracle
/// config with [`verify_coinbase_spot`] (authentic ∧ well-formed ∧ the response asset matches
/// the requested one), then (2) BINDS the caller's claimed `(asset, amount)` to the notarized
/// quote: the re-derived asset and amount must be EXACTLY the ones this price claims. A price
/// whose attestation is forged/tampered, whose notary is not the pinned one, or whose claimed
/// amount is not the notarized one, is REFUSED — the fund can never fill at a price it cannot
/// prove. Returns the notarized amount in cents.
pub fn verify_attested_price(
    price: &AttestedPrice,
    oracle_config: &EndpointConfig,
) -> Result<i64, PriceError> {
    let reverified =
        verify_coinbase_spot(&price.attestation, oracle_config).map_err(PriceError::NotAttested)?;
    // The claim the fund carries must be exactly what the notarized quote says.
    if reverified.asset != price.asset || reverified.amount != price.amount {
        return Err(PriceError::AmountNotBound);
    }
    amount_to_cents(&reverified.amount)
}

/// Why an [`AttestedPrice`] failed verification at fill/audit time — the "unattested price"
/// refusal.
#[derive(Clone, Debug)]
pub enum PriceError {
    /// The zkOracle attestation itself failed (forged / tampered / wrong-notary / bad schema /
    /// wrong asset).
    NotAttested(ZkPriceError),
    /// The attestation is valid but does NOT notarize the claimed amount/asset (a price the
    /// fund cannot prove: the claim and the notarized quote disagree).
    AmountNotBound,
    /// The notarized amount is not a parseable decimal-USD quantity (cannot denominate).
    Unparseable(String),
}

impl core::fmt::Display for PriceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PriceError::NotAttested(e) => write!(f, "price attestation refused: {e}"),
            PriceError::AmountNotBound => {
                write!(f, "the attestation does not notarize the claimed amount")
            }
            PriceError::Unparseable(a) => write!(f, "notarized amount `{a}` is not a decimal USD"),
        }
    }
}

impl std::error::Error for PriceError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cents_conversion_is_exact() {
        assert_eq!(amount_to_cents("64250.37").unwrap(), 6_425_037);
        assert_eq!(amount_to_cents("1000.00").unwrap(), 100_000);
        assert_eq!(amount_to_cents("1000").unwrap(), 100_000);
        assert_eq!(amount_to_cents("0.5").unwrap(), 50);
        assert_eq!(amount_to_cents("900.00").unwrap(), 90_000);
        // Beyond two fractional digits truncates to cents.
        assert_eq!(amount_to_cents("12.349").unwrap(), 1_234);
        assert!(amount_to_cents("not-a-price").is_err());
    }
}
