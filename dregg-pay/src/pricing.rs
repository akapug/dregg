//! [`PriceOracle`] — the live `$DREGG`/USDC price, and [`runs_for_payment`] — how a
//! payment in either asset converts to run-credits under ember's dual-asset
//! economics.
//!
//! # The economics
//!
//! * **USDC is the FUEL, priced flat.** A run costs [`PayConfig::price_usd_per_run`]
//!   (default `$0.10`). A USDC payment credits `usd_value / price_usd_per_run` runs,
//!   floored. No oracle needed — USDC *is* the unit of account.
//! * **`$DREGG` is the PILE, priced-fed at a holder discount.** A `$DREGG` run costs
//!   `price_usd_per_run × (1 − dregg_discount_bps/10000)`-worth of `$DREGG` (≈ `$0.08`
//!   at the defaults). We ask the oracle for the live `$DREGG`/USDC price, value the
//!   paid `$DREGG` in USD, and divide by that discounted per-run price. Stable in
//!   real terms; the 20% discount rewards paying in the illiquid pile asset.
//!
//! # Two oracle impls behind one trait
//!
//! * [`MockOracle`] — a fixed price, for driven tests (NO network).
//! * [`JupiterPriceOracle`] — the REAL path, wrapping the public Jupiter price API
//!   (`price.jup.ag` / `api.jup.ag/price`) behind an injected [`HttpGet`] seam (the
//!   same "inject the transport, keep the core pure" shape the watcher uses for its
//!   RPC). The JSON parse ([`parse_jupiter_price`]) is real and unit-tested against a
//!   sample response — no network in tests.

use crate::config::{Asset, PayConfig};

/// The live price of one whole `$DREGG` in USD (i.e. `$DREGG`/USDC). This is the one
/// number the discounted pricing and the OTC fill are fed from.
pub trait PriceOracle {
    /// The current `$DREGG`/USDC price (USD per one whole `$DREGG`). Fails closed:
    /// a stale/unavailable/invalid price returns `Err`, never a silent default —
    /// pricing a run off a bad price would mis-charge.
    fn dregg_usd_price(&self) -> Result<f64, PriceError>;
}

/// Why a price read or a run computation failed.
#[derive(Clone, Debug, PartialEq)]
pub enum PriceError {
    /// The oracle transport (HTTP) failed.
    Transport(String),
    /// The response could not be parsed into a price for the requested mint.
    Parse(String),
    /// The price was non-finite or ≤ 0 (a division-by-zero / nonsense guard).
    InvalidPrice(f64),
    /// A discount must leave a positive price; 10,000 bps would make runs/free
    /// tokens unbounded and anything larger applies the discount backwards.
    InvalidDiscount(u32),
    /// The configured decimal exponent cannot be represented safely.
    InvalidDecimals(u8),
    /// The exact integer pricing calculation exceeded its checked `u128` budget.
    ArithmeticOverflow,
}

impl std::fmt::Display for PriceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PriceError::Transport(e) => write!(f, "price transport error: {e}"),
            PriceError::Parse(e) => write!(f, "price parse error: {e}"),
            PriceError::InvalidPrice(p) => write!(f, "invalid $DREGG price: {p}"),
            PriceError::InvalidDiscount(bps) => {
                write!(f, "invalid discount: {bps} bps must be below 10000")
            }
            PriceError::InvalidDecimals(d) => write!(f, "invalid token decimals: {d}"),
            PriceError::ArithmeticOverflow => write!(f, "pricing arithmetic overflow"),
        }
    }
}

impl std::error::Error for PriceError {}

// ─────────────────────────────────────────────────────────────────────────────
// MOCK oracle — driven tests, no network
// ─────────────────────────────────────────────────────────────────────────────

/// A fixed-price oracle for driven tests. `price` is USD per one whole `$DREGG`.
#[derive(Clone, Copy, Debug)]
pub struct MockOracle {
    price: f64,
}

impl MockOracle {
    /// An oracle that always returns `price` USD per whole `$DREGG`.
    pub fn new(price: f64) -> Self {
        MockOracle { price }
    }
}

impl PriceOracle for MockOracle {
    fn dregg_usd_price(&self) -> Result<f64, PriceError> {
        check_price(self.price)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// REAL Jupiter oracle — public price API behind an injected HTTP seam
// ─────────────────────────────────────────────────────────────────────────────

/// The HTTP seam. A production impl issues a GET against the Jupiter price endpoint
/// and returns the response body. Injected (not baked-in reqwest/tokio) exactly like
/// the watcher's [`AccountFetcher`](crate::watcher::AccountFetcher), so the pure
/// pricing core — and its JSON parse — is exercised in tests with no network.
pub trait HttpGet {
    /// GET `url`, returning the response body as a string.
    fn get(&self, url: &str) -> Result<String, PriceError>;
}

/// The real `$DREGG`/USDC oracle over the public Jupiter price API. It queries
/// `{api_base}?ids={dregg_mint}` (default `api_base` is the public price endpoint;
/// the mint comes from [`PayConfig`], never hardcoded) and parses the price string
/// out of the JSON with [`parse_jupiter_price`].
///
/// The endpoint returns a `$DREGG` price already denominated in USDC, so no separate
/// SOL leg is needed for *pricing*. (The `$DREGG`→SOL→USDC *swap execution* that
/// realizes the pile as fuel is the deferred, signer-gated follow-up — see the crate
/// docs.)
pub struct JupiterPriceOracle<H: HttpGet> {
    http: H,
    dregg_mint_base58: String,
    api_base: String,
}

impl<H: HttpGet> JupiterPriceOracle<H> {
    /// The public Jupiter price endpoint (v2). Public network constant, not a secret
    /// and not a mint — the mint is supplied from config.
    pub const DEFAULT_API_BASE: &'static str = "https://api.jup.ag/price/v2";

    /// Build from a [`PayConfig`] (for the `$DREGG` mint) + an HTTP client, using the
    /// default public endpoint.
    pub fn new(config: &PayConfig, http: H) -> Self {
        Self::with_api_base(config, http, Self::DEFAULT_API_BASE.to_string())
    }

    /// Build with an explicit `api_base` (an operator override / a devnet proxy).
    pub fn with_api_base(config: &PayConfig, http: H, api_base: String) -> Self {
        JupiterPriceOracle {
            http,
            dregg_mint_base58: bs58::encode(config.mint).into_string(),
            api_base,
        }
    }

    /// The exact URL this oracle would GET (exposed so tests can assert it without a
    /// network call).
    pub fn price_url(&self) -> String {
        format!("{}?ids={}", self.api_base, self.dregg_mint_base58)
    }
}

impl<H: HttpGet> PriceOracle for JupiterPriceOracle<H> {
    fn dregg_usd_price(&self) -> Result<f64, PriceError> {
        let body = self.http.get(&self.price_url())?;
        let price = parse_jupiter_price(&body, &self.dregg_mint_base58).ok_or_else(|| {
            PriceError::Parse(format!("no price for mint {}", self.dregg_mint_base58))
        })?;
        check_price(price)
    }
}

/// Parse the price of `mint` out of a Jupiter price-API JSON body. The v2 shape is:
///
/// ```json
/// {"data":{"<mint>":{"id":"<mint>","type":"derivedPrice","price":"0.00512"}},"timeTaken":0.1}
/// ```
///
/// The `price` is a JSON string. This finds the mint's object then the first `price`
/// field within it. Returns `None` if the mint is absent or the price is unparseable.
pub fn parse_jupiter_price(json: &str, mint: &str) -> Option<f64> {
    let value: serde_json::Value = serde_json::from_str(json).ok()?;
    let price = value.get("data")?.get(mint)?.get("price")?;
    match price {
        serde_json::Value::String(s) => s.parse::<f64>().ok(),
        serde_json::Value::Number(n) => n.as_f64(),
        _ => None,
    }
}

/// Guard: a price must be finite and strictly positive.
fn check_price(p: f64) -> Result<f64, PriceError> {
    if p.is_finite() && p > 0.0 {
        Ok(p)
    } else {
        Err(PriceError::InvalidPrice(p))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The pricing function
// ─────────────────────────────────────────────────────────────────────────────

/// One whole token, in atomic units, for `decimals`.
pub(crate) fn pow10(decimals: u8) -> Result<u128, PriceError> {
    10u128
        .checked_pow(decimals as u32)
        .ok_or(PriceError::InvalidDecimals(decimals))
}

/// Convert the operator/oracle decimal to the exact ratio represented by its
/// shortest decimal rendering. This avoids binary-float boundary errors such as
/// `0.30 / 0.10` flooring to two runs.
pub(crate) fn decimal_ratio(value: f64) -> Result<(u128, u128), PriceError> {
    check_price(value)?;
    let rendered = value.to_string();
    let (mantissa, exp) = match rendered.split_once(['e', 'E']) {
        Some((m, e)) => (
            m,
            e.parse::<i32>()
                .map_err(|_| PriceError::InvalidPrice(value))?,
        ),
        None => (rendered.as_str(), 0),
    };
    let (whole, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = format!("{whole}{frac}");
    let mut numerator = digits
        .parse::<u128>()
        .map_err(|_| PriceError::ArithmeticOverflow)?;
    let scale = frac.len() as i32 - exp;
    let denominator = if scale >= 0 {
        10u128
            .checked_pow(scale as u32)
            .ok_or(PriceError::ArithmeticOverflow)?
    } else {
        numerator = numerator
            .checked_mul(
                10u128
                    .checked_pow((-scale) as u32)
                    .ok_or(PriceError::ArithmeticOverflow)?,
            )
            .ok_or(PriceError::ArithmeticOverflow)?;
        1
    };
    Ok((numerator, denominator))
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// Exact checked `floor(product(numerators) / product(denominators))`, cancelling
/// cross factors before multiplication to retain the full useful `u128` range.
pub(crate) fn mul_div_floor(
    mut numerators: Vec<u128>,
    mut denominators: Vec<u128>,
) -> Result<u64, PriceError> {
    if denominators.contains(&0) {
        return Err(PriceError::ArithmeticOverflow);
    }
    for n in &mut numerators {
        for d in &mut denominators {
            let g = gcd(*n, *d);
            *n /= g;
            *d /= g;
        }
    }
    let num = numerators.into_iter().try_fold(1u128, |a, b| {
        a.checked_mul(b).ok_or(PriceError::ArithmeticOverflow)
    })?;
    let den = denominators.into_iter().try_fold(1u128, |a, b| {
        a.checked_mul(b).ok_or(PriceError::ArithmeticOverflow)
    })?;
    u64::try_from(num / den).map_err(|_| PriceError::ArithmeticOverflow)
}

/// How many run-credits a `payment` of `amount` atomic units in `asset` buys.
///
/// * [`Asset::Usdc`] → flat: `floor((amount / 10^usdc_decimals) / price_usd_per_run)`.
///   The oracle is not consulted.
/// * [`Asset::Dregg`] → price-fed with the holder discount: value the `$DREGG` in USD
///   via the oracle, then `floor(usd_value / (price_usd_per_run × (1 − discount)))`.
///
/// Floors to whole runs (sub-run value is not credited — the ledger's dust rule).
pub fn runs_for_payment(
    asset: Asset,
    amount: u64,
    oracle: &dyn PriceOracle,
    config: &PayConfig,
) -> Result<u64, PriceError> {
    let price_per_run = config.price_usd_per_run;
    if !(price_per_run.is_finite() && price_per_run > 0.0) {
        return Err(PriceError::InvalidPrice(price_per_run));
    }
    match asset {
        Asset::Usdc => {
            let (price_num, price_den) = decimal_ratio(price_per_run)?;
            mul_div_floor(
                vec![amount as u128, price_den],
                vec![pow10(config.usdc_decimals)?, price_num],
            )
        }
        Asset::Dregg => {
            let dregg_price = oracle.dregg_usd_price()?;
            if config.dregg_discount_bps >= 10_000 {
                return Err(PriceError::InvalidDiscount(config.dregg_discount_bps));
            }
            let (oracle_num, oracle_den) = decimal_ratio(dregg_price)?;
            let (price_num, price_den) = decimal_ratio(price_per_run)?;
            mul_div_floor(
                vec![amount as u128, oracle_num, price_den, 10_000],
                vec![
                    pow10(config.dregg_decimals)?,
                    oracle_den,
                    price_num,
                    (10_000 - config.dregg_discount_bps) as u128,
                ],
            )
        }
    }
}

/// `(1 − bps/10000)` — the multiplier a discount applies to a price. Clamped to
/// `[0, 1]` so a mis-set bps can never invert the sign.
pub fn discount_factor(bps: u32) -> f64 {
    let f = 1.0 - (bps as f64) / 10_000.0;
    f.clamp(0.0, 1.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::DepositAddress;

    fn cfg() -> PayConfig {
        PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            [0x11u8; 32],
            DepositAddress([0xEEu8; 32]),
            1_000_000,
        )
    }

    #[test]
    fn usdc_priced_flat_at_ten_cents() {
        let c = cfg(); // price_usd_per_run = 0.10, usdc_decimals = 6
        let oracle = MockOracle::new(999.0); // must be ignored for USDC
        // $1.00 = 1_000_000 atomic USDC → 10 runs at $0.10.
        assert_eq!(
            runs_for_payment(Asset::Usdc, 1_000_000, &oracle, &c).unwrap(),
            10
        );
        // $0.05 → below one run.
        assert_eq!(
            runs_for_payment(Asset::Usdc, 50_000, &oracle, &c).unwrap(),
            0
        );
        // Binary f64 computes 0.3 / 0.1 just below 3 on common platforms. Money
        // math must use the configured decimal values exactly at this boundary.
        assert_eq!(
            runs_for_payment(Asset::Usdc, 300_000, &oracle, &c).unwrap(),
            3
        );
    }

    #[test]
    fn dregg_priced_fed_at_twenty_percent_discount() {
        let c = cfg(); // discount 2000 bps → effective $0.08/run
        let oracle = MockOracle::new(0.005); // $0.005 per whole $DREGG
        // 100 whole $DREGG = 100_000_000 atomic → usd_value $0.50.
        // $0.50 / $0.08 = 6.25 → 6 runs (vs 5 at the flat USDC price — holder reward).
        assert_eq!(
            runs_for_payment(Asset::Dregg, 100_000_000, &oracle, &c).unwrap(),
            6
        );
        // Same USD value in USDC gives only 5 runs — the discount is real.
        assert_eq!(
            runs_for_payment(Asset::Usdc, 500_000, &oracle, &c).unwrap(),
            5
        );
    }

    #[test]
    fn dregg_pricing_fails_closed_on_bad_price() {
        let c = cfg();
        let bad = MockOracle::new(0.0);
        assert!(matches!(
            runs_for_payment(Asset::Dregg, 100_000_000, &bad, &c),
            Err(PriceError::InvalidPrice(_))
        ));
    }

    #[test]
    fn free_or_inverted_discount_is_refused_not_saturated_to_max_runs() {
        let mut c = cfg();
        c.dregg_discount_bps = 10_000;
        let oracle = MockOracle::new(0.005);
        assert_eq!(
            runs_for_payment(Asset::Dregg, 1, &oracle, &c),
            Err(PriceError::InvalidDiscount(10_000))
        );
    }

    #[test]
    fn parses_jupiter_v2_price_json() {
        let mint = "So11111111111111111111111111111111111111112";
        let body = format!(
            "{{\"data\":{{\"{mint}\":{{\"id\":\"{mint}\",\"type\":\"derivedPrice\",\"price\":\"0.00512\"}}}},\"timeTaken\":0.12}}"
        );
        assert_eq!(parse_jupiter_price(&body, mint), Some(0.00512));
        assert_eq!(parse_jupiter_price(&body, "NotAMint"), None);

        let smuggled =
            format!("{{\"data\":{{\"attacker\":{{\"id\":\"{mint}\",\"price\":\"999\"}}}}}}");
        assert_eq!(
            parse_jupiter_price(&smuggled, mint),
            None,
            "the mint must be a key under data, not an unrelated string value"
        );
    }

    #[test]
    fn jupiter_oracle_drives_over_mock_http() {
        struct MockHttp {
            body: String,
        }
        impl HttpGet for MockHttp {
            fn get(&self, _url: &str) -> Result<String, PriceError> {
                Ok(self.body.clone())
            }
        }
        let c = cfg();
        let mint_b58 = bs58::encode(c.mint).into_string();
        let body = format!(
            "{{\"data\":{{\"{mint_b58}\":{{\"id\":\"{mint_b58}\",\"price\":\"0.007\"}}}}}}"
        );
        let oracle = JupiterPriceOracle::new(&c, MockHttp { body });
        assert!(oracle.price_url().contains(&mint_b58));
        assert_eq!(oracle.dregg_usd_price().unwrap(), 0.007);
    }
}
