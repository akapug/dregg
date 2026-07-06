//! The **mandate as caps** — the bounded contract the fund agent trades under.
//!
//! A [`Mandate`] is not advisory prose; it is a set of hard bounds the fund enforces as
//! REFUSALS (see [`crate::fund::Fund::step`]). An over-mandate decision — a disallowed
//! asset, or a fill that would push a position past [`Mandate::max_position`] — never
//! reaches a simulated fill or an on-ledger turn: the step returns an error and the fund's
//! state is unchanged. The capital bound ([`Mandate::budget`]) is drawn down per fill and a
//! draw that cannot be covered is likewise refused. The on-ledger turn budget
//! ([`Mandate::max_turns`]) is a genuine executor cap: it becomes the `NodeMinter`'s
//! rate-limited `ToolGrant`, so an over-budget mint is refused host-side by the kernel, not
//! by a soft check in this crate.

/// The bounded trading mandate the fund operates under. Every field is a hard cap the fund
/// enforces as a refusal; none is advisory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mandate {
    /// The assets the fund is permitted to trade. A buy/sell of any other asset is REFUSED
    /// ([`crate::fund::FundError::Mandate`] / [`MandateViolation::AssetNotAllowed`]).
    pub allowed_assets: Vec<String>,
    /// The maximum absolute position (in units) the fund may hold in ANY single asset. A
    /// fill whose resulting position would exceed this in magnitude is REFUSED
    /// ([`MandateViolation::PositionExceeded`]).
    pub max_position: i64,
    /// The initial capital (in the price denomination, e.g. cents) the fund starts with.
    /// The fund's cash is drawn down by each buy and released by each sell; a buy whose cost
    /// exceeds available cash is REFUSED ([`crate::fund::FundError::OverBudget`]). Cash never
    /// goes negative.
    pub budget: i64,
    /// The maximum number of on-ledger turns (decisions committed) the fund may mint. This
    /// is wired into the `NodeMinter`'s rate-limited `ToolGrant`, so the (N+1)-th mint is
    /// refused by the executor host-side — a real cap gate, not a soft check.
    pub max_turns: i64,
}

impl Mandate {
    /// Whether `asset` is inside the mandate's allowed set.
    pub fn allows(&self, asset: &str) -> bool {
        self.allowed_assets.iter().any(|a| a == asset)
    }
}

/// Which mandate cap a decision breached. Surfaced inside [`crate::fund::FundError::Mandate`]
/// (at the fund) and [`crate::audit::AuditError::MandateBreached`] (at the audit).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MandateViolation {
    /// The decision trades an asset outside [`Mandate::allowed_assets`].
    AssetNotAllowed(String),
    /// The fill would push the position in `asset` past [`Mandate::max_position`] in
    /// magnitude (`would` is the prospective post-fill position).
    PositionExceeded { asset: String, would: i64, max: i64 },
    /// A sell exceeds the held position (no shorting in paper mode).
    InsufficientPosition { asset: String, have: i64, sell: i64 },
}

impl core::fmt::Display for MandateViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MandateViolation::AssetNotAllowed(a) => write!(f, "asset `{a}` is outside the mandate"),
            MandateViolation::PositionExceeded { asset, would, max } => {
                write!(
                    f,
                    "position in `{asset}` would be {would}, past the max {max}"
                )
            }
            MandateViolation::InsufficientPosition { asset, have, sell } => {
                write!(
                    f,
                    "cannot sell {sell} of `{asset}` holding only {have} (no shorting)"
                )
            }
        }
    }
}
