//! # The auditable fund — an AI fund you audit instead of trust
//!
//! An agent that trades a bounded budget on a mandate and **cannot lie about what it did**.
//! Every decision is a jailed+attested turn; every trade lands as an on-ledger, light-client
//! verifiable receipt; every price is proven via a zkOracle attestation. A third party
//! [`audit_fund`]s the track record and confirms — trusting no operator — that the fund
//! followed its mandate and did not lie about a single fill.
//!
//! ## ⚑ PAPER TRADING ONLY
//!
//! This agent does **not** touch real money, real exchange orders, or real custody. Fills are
//! SIMULATED against attested prices ([`Fund::step`] → `simulate_fill`). There is **no** code
//! path in this crate or the paths it reaches that places a real order or moves real funds. A
//! live-trading path is a deliberately UN-BUILT change that would be an explicit,
//! REVIEWED-GO-gated integration (ember + a real broker) — it is not wired, not stubbed, not
//! present.
//!
//! ## What composes into it (the real dregg primitives)
//!
//! | Guarantee | Primitive |
//! |---|---|
//! | each decision an attested turn | `deos-hermes` `AttestationCarrier` / `attest_turn` / `verify_zkoracle` |
//! | each trade an on-ledger receipt | `agent-platform` `LocalNode` / `NodeMinter` (R2 kernel turn), `grain-turn::ATTESTATION_SLOT` |
//! | each price a zkOracle attestation | `dregg-zkoracle-prove` `ZkOracleAttestation` behind the [`PriceOracle`] interface |
//! | the mandate as caps | [`Mandate`] enforced as refusals + the minter's rate-limited `ToolGrant` |
//!
//! ## The loop and the audit
//!
//! ```text
//!   gather attested prices → brain decides → attest the decision → enforce the mandate caps
//!     → verify the price + simulate the fill (draw the bounded budget)
//!     → land an on-ledger R2 turn binding {decision att, price att, fill}
//!   audit_fund: verify the chain (light client) + every decision & price attestation
//!     + the mandate held every turn + recompute the on-ledger commitment  ⇒  P&L
//! ```
//!
//! ## The teeth (all bite; see the crate tests)
//!
//! - an over-mandate trade (disallowed asset / over-position) is REFUSED by the cap gate;
//! - an over-budget buy is REFUSED by the bounded budget;
//! - a fill claimed at an unattested / unprovable price is REFUSED;
//! - a forged, altered, dropped, reordered, or backdated track record FAILS the audit.

pub mod audit;
pub mod brain;
pub mod fund;
pub mod mandate;
pub mod oracle;

/// Re-exported so downstream code (and this crate's tests / example) can name the pinned
/// notary anchor type without a direct `deos-hermes` dependency.
pub use deos_hermes::AnthropicConfig;

pub use audit::{AuditError, AuditReport, audit_fund};
pub use brain::{Brain, Decision, MarketView, RecordedBrain, Side, ThresholdBrain};
pub use fund::{Fund, FundError, StepOutcome, TrackRecord, TradeRecord};
pub use mandate::{Mandate, MandateViolation};
pub use oracle::{
    AttestedPrice, CoinbaseSpotOracle, EndpointConfig, FixtureNotary, PriceError, PriceOracle,
    ZkPriceError, amount_to_cents, coinbase_spot_spec, verify_attested_price,
};
