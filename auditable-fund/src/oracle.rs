//! The **price oracle** — every price the fund trades on is a zkOracle attestation.
//!
//! The fund NEVER fills at a bare number. A price is an [`AttestedPrice`]: a quantity bound
//! to a [`ZkOracleAttestation`] — the same authentic ∧ well-formed ∧ injection-free object
//! `deos-hermes` attests a brain turn under. [`verify_attested_price`] re-checks that
//! attestation AND binds the claimed amount to the notarized response body, so a fund cannot
//! claim a fill at a price it cannot prove.
//!
//! [`PriceOracle`] is the interface the parallel zkoracle-prove price lane realizes —
//! `price(asset) -> AttestedPrice { amount, time, attestation }`. This crate builds against
//! the interface; [`ModeledOracle`] is a stub that produces a genuine attestation over a
//! modeled quote (its notary is a deterministic fixture), so when the live price endpoint
//! lands the fund composes it unchanged.

use deos_hermes::{
    AnthropicConfig, AttestationCarrier, ProveError, ZkOracleAttestation, ZkOracleError,
    attestation_commitment, messages_body, verify_zkoracle,
};

/// A price the fund is allowed to fill at: a quantity bound to a zkOracle attestation over a
/// notarized quote. Every simulated fill uses one of these — the fund can prove the price.
#[derive(Clone, Debug)]
pub struct AttestedPrice {
    /// The asset the quote is for.
    pub asset: String,
    /// The quoted amount (price denomination, e.g. cents).
    pub amount: i64,
    /// The quote time (unix-ish; the modeled oracle's logical clock).
    pub time: i64,
    /// The exact injection-free field the attestation binds — the canonical quote string
    /// (see [`canonical_quote`]). Stored so a verifier can re-derive and compare.
    pub field: String,
    /// **The zkOracle attestation** over the quote body: authentic (notary-signed session) ∧
    /// well-formed (JSON CFG cert) ∧ injection-free. Its committed field decodes to `amount`.
    pub attestation: ZkOracleAttestation,
}

impl AttestedPrice {
    /// The canonical 32-byte commitment to this attested price (the hash the on-ledger trade
    /// receipt folds in) — [`deos_hermes::attestation_commitment`] of the underlying zkOracle
    /// attestation.
    pub fn commitment(&self) -> [u8; 32] {
        attestation_commitment(&self.attestation)
    }
}

/// **The price-oracle interface** — `price(asset) -> AttestedPrice`. The fund composes any
/// implementation; the live zkoracle-prove price endpoint and the [`ModeledOracle`] stub both
/// satisfy it. Every returned price carries its own zkOracle attestation.
pub trait PriceOracle {
    /// Quote `asset` as an attested price, or an error if the oracle cannot quote it.
    fn price(&self, asset: &str) -> Result<AttestedPrice, OracleError>;
}

/// The canonical quote field bound by a price attestation — a JSON-string-safe,
/// injection-free (`{{`-free) string that encodes the whole quote, so the attestation's
/// committed field IS the price claim. Any change to asset/amount/time changes this string,
/// hence the attestation, hence its commitment.
pub fn canonical_quote(asset: &str, amount: i64, time: i64) -> String {
    format!("QUOTE asset={asset} amount={amount} time={time}")
}

/// A modeled zkOracle price endpoint: a deterministic fixture notary + a quote table + a
/// logical clock. `price()` produces a GENUINE [`ZkOracleAttestation`] over the canonical
/// quote body (real CFG cert + real injection matcher + fixture-notary authentic leg) — the
/// same machinery the live endpoint uses; only the transport is modeled.
pub struct ModeledOracle {
    carrier: AttestationCarrier,
    quotes: std::collections::BTreeMap<String, i64>,
    clock: i64,
}

impl ModeledOracle {
    /// A modeled oracle whose notary is derived from `seed` (so its [`Self::config`] pin is
    /// reproducible — a verifier pins the same anchor).
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        ModeledOracle {
            carrier: AttestationCarrier::from_seed(seed),
            quotes: std::collections::BTreeMap::new(),
            clock: 0,
        }
    }

    /// Set the current quote for `asset`.
    pub fn set_price(&mut self, asset: &str, amount: i64) {
        self.quotes.insert(asset.to_string(), amount);
    }

    /// Advance the oracle's logical clock (a new quote round).
    pub fn tick(&mut self) {
        self.clock += 1;
    }

    /// The current logical time.
    pub fn now(&self) -> i64 {
        self.clock
    }

    /// The pinned notary anchor a verifier checks this oracle's attestations against — the
    /// public key the fund and the auditor pin as "the oracle we trust."
    pub fn config(&self) -> &AnthropicConfig {
        self.carrier.config()
    }
}

impl PriceOracle for ModeledOracle {
    fn price(&self, asset: &str) -> Result<AttestedPrice, OracleError> {
        let amount = *self
            .quotes
            .get(asset)
            .ok_or(OracleError::NoQuote(asset.to_string()))?;
        let field = canonical_quote(asset, amount, self.clock);
        let body = messages_body(&field);
        let attestation = self
            .carrier
            .attest_body(&body, field.as_bytes())
            .map_err(OracleError::Prove)?;
        Ok(AttestedPrice {
            asset: asset.to_string(),
            amount,
            time: self.clock,
            field,
            attestation,
        })
    }
}

/// **Verify an attested price** — the check every fill and every audit runs. It (1) verifies
/// the zkOracle attestation against the pinned oracle notary (`authentic ∧ well-formed ∧
/// injection-free`), then (2) BINDS the claimed `(asset, amount, time)` to the notarized
/// response body: the attestation's authenticated body must be EXACTLY the canonical quote
/// for that claim. A price whose attestation is forged/tampered, or whose claimed amount is
/// not the notarized one, is REFUSED — so the fund can never fill at a price it cannot prove.
pub fn verify_attested_price(
    price: &AttestedPrice,
    oracle_config: &AnthropicConfig,
) -> Result<(), PriceError> {
    let verified =
        verify_zkoracle(&price.attestation, oracle_config).map_err(PriceError::NotAttested)?;
    let expected = messages_body(&canonical_quote(&price.asset, price.amount, price.time));
    if verified.session.response_body != expected.as_bytes() {
        return Err(PriceError::AmountNotBound);
    }
    if price.field != canonical_quote(&price.asset, price.amount, price.time) {
        return Err(PriceError::AmountNotBound);
    }
    Ok(())
}

/// Why an oracle could not produce a quote.
#[derive(Clone, Debug)]
pub enum OracleError {
    /// The oracle has no quote for the asset.
    NoQuote(String),
    /// The attestation prover refused (should not happen for a well-formed quote).
    Prove(ProveError),
}

/// Why an [`AttestedPrice`] failed verification — the "unattested price" refusal.
#[derive(Clone, Debug)]
pub enum PriceError {
    /// The zkOracle attestation itself failed (forged / tampered / wrong-notary / injecting).
    NotAttested(ZkOracleError),
    /// The attestation is valid but does NOT notarize the claimed amount (a price the fund
    /// cannot prove: the claim and the notarized body disagree).
    AmountNotBound,
}

impl core::fmt::Display for OracleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            OracleError::NoQuote(a) => write!(f, "no quote for `{a}`"),
            OracleError::Prove(e) => write!(f, "prover refused: {e:?}"),
        }
    }
}

impl core::fmt::Display for PriceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PriceError::NotAttested(e) => write!(f, "price attestation refused: {e:?}"),
            PriceError::AmountNotBound => {
                write!(f, "the attestation does not notarize the claimed amount")
            }
        }
    }
}
