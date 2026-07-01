//! **Spending limits + budget alerts**: a per-account DEC spend cap with alert
//! thresholds (50% / 80% / 100% by default), enforced through the proven exec budget
//! cell.
//!
//! ## What it does
//!
//! A [`BudgetGuard`] tracks an account's accrued spend against a hard cap. Each charge
//! goes through [`charge`](BudgetGuard::charge):
//! - **under cap:** admitted, drawn down the underlying
//!   [`ReplenishingBudget`](dreggnet_exec::budget::ReplenishingBudget) (the same
//!   rate-bounded-ceiling cell the leases + the abuse guard use), and any alert
//!   threshold newly crossed by this charge fires a [`BudgetAlert`] (a record the
//!   console / a notification surfaces — not a side effect here);
//! - **at/over the hard cap:** refused ([`SpendDecision::Refused`]) — nothing is drawn,
//!   so new spend is genuinely stopped, the same way a lapsed lease stops serving.
//!
//! The cap is the budget cell's ceiling, so the hard stop is enforced by the audited
//! cell (`would_admit` / `draw`), not a bespoke counter. The guard only adds the
//! threshold-alert bookkeeping on top.

use dreggnet_exec::budget::{BudgetError, BudgetTerms, ReplenishingBudget};

/// An alert raised when an account's accrued spend crosses a budget threshold. A record
/// for the console / a notification to surface — emitting it is the caller's job.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetAlert {
    /// The account whose spend crossed the threshold.
    pub account: String,
    /// The threshold crossed, in percent of the cap (e.g. `80`).
    pub threshold_pct: u8,
    /// The accrued spend at the moment the threshold fired (DEC).
    pub spent_units: i64,
    /// The hard spend cap (DEC).
    pub cap_units: i64,
}

/// A per-account spend cap + the alert thresholds to fire on the way up.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpendLimit {
    /// The hard cap in DEC: spend beyond this is refused.
    pub cap_units: i64,
    /// The thresholds (percent of the cap) that fire an alert when first crossed,
    /// e.g. `[50, 80, 100]`. Order-independent; each fires at most once.
    pub alert_thresholds_pct: Vec<u8>,
}

impl SpendLimit {
    /// A spend cap of `cap_units` DEC with the default `[50, 80, 100]` alert thresholds.
    pub fn new(cap_units: i64) -> SpendLimit {
        SpendLimit {
            cap_units,
            alert_thresholds_pct: vec![50, 80, 100],
        }
    }

    /// A spend cap with explicit alert thresholds.
    pub fn with_thresholds(cap_units: i64, alert_thresholds_pct: Vec<u8>) -> SpendLimit {
        SpendLimit {
            cap_units,
            alert_thresholds_pct,
        }
    }
}

/// The outcome of one charge against a [`BudgetGuard`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpendDecision {
    /// The charge fit under the cap and was drawn. Carries the new accrued spend and
    /// any alert thresholds newly crossed by this charge (possibly several at once,
    /// e.g. a big charge jumping from 40% to 85% fires both 50% and 80%).
    Admitted {
        spent_units: i64,
        alerts: Vec<BudgetAlert>,
    },
    /// The charge would exceed the hard cap — refused, nothing drawn.
    Refused {
        account: String,
        cap_units: i64,
        spent_units: i64,
        attempted: i64,
    },
}

impl SpendDecision {
    /// Whether the charge was admitted.
    pub fn is_admitted(&self) -> bool {
        matches!(self, SpendDecision::Admitted { .. })
    }
}

/// A per-account spend cap enforced through the exec budget cell, plus the alert-
/// threshold bookkeeping.
pub struct BudgetGuard {
    account: String,
    limit: SpendLimit,
    /// The underlying ceiling cell — the cap is its budget; admission is its `would_admit`.
    cell: ReplenishingBudget,
    /// A monotonic block cursor the ceiling cell needs; the spend cap never replenishes
    /// within a period, so this only advances the clock, it never refills.
    clock: i64,
    /// Thresholds already alerted (each fires at most once on the way up).
    fired: Vec<u8>,
}

impl BudgetGuard {
    /// Open a guard for `account` over `asset`, enforcing `limit`. The cap becomes the
    /// budget cell's ceiling; the refill window is set to the whole horizon so the cap
    /// is a flat ceiling within a billing period (no mid-period replenishment).
    pub fn open(
        account: impl Into<String>,
        asset: impl Into<String>,
        limit: SpendLimit,
    ) -> Result<BudgetGuard, BudgetError> {
        // A ceiling over the whole horizon: refill_amount == budget, a single window so
        // nothing replenishes back within the period. `BudgetTerms::ceiling` is exactly
        // this prepaid-ceiling shape.
        let cell = ReplenishingBudget::open(BudgetTerms::ceiling(
            asset.into(),
            limit.cap_units.max(0),
            i64::MAX / 4,
            0,
        ))?;
        Ok(BudgetGuard {
            account: account.into(),
            limit,
            cell,
            clock: 0,
            fired: Vec::new(),
        })
    }

    /// The account this guard bills.
    pub fn account(&self) -> &str {
        &self.account
    }

    /// The accrued spend so far (DEC).
    pub fn spent(&self) -> i64 {
        self.cell.outstanding_at(self.clock)
    }

    /// The remaining headroom under the cap (DEC).
    pub fn remaining(&self) -> i64 {
        self.cell.headroom_at(self.clock)
    }

    /// The hard cap (DEC).
    pub fn cap(&self) -> i64 {
        self.limit.cap_units
    }

    /// Charge `amount` DEC against the account. Admitted under the cap (drawing the
    /// ceiling cell and firing any newly-crossed alert thresholds); refused at/over the
    /// cap (nothing drawn). A non-positive charge is a no-op admit.
    pub fn charge(&mut self, amount: i64) -> SpendDecision {
        self.clock += 1;
        if amount <= 0 {
            return SpendDecision::Admitted {
                spent_units: self.spent(),
                alerts: Vec::new(),
            };
        }
        if !self.cell.would_admit(amount, self.clock) {
            return SpendDecision::Refused {
                account: self.account.clone(),
                cap_units: self.limit.cap_units,
                spent_units: self.spent(),
                attempted: amount,
            };
        }
        // Admitted: draw the ceiling cell (the audited hard-cap enforcement).
        let _ = self
            .cell
            .draw(amount, self.clock)
            .expect("would_admit just passed, so draw cannot fail");
        let spent = self.spent();
        let alerts = self.fire_thresholds(spent);
        SpendDecision::Admitted {
            spent_units: spent,
            alerts,
        }
    }

    /// Fire (once) every alert threshold whose percent-of-cap the accrued `spent` now
    /// meets or exceeds, in ascending threshold order.
    fn fire_thresholds(&mut self, spent: i64) -> Vec<BudgetAlert> {
        let cap = self.limit.cap_units;
        if cap <= 0 {
            return Vec::new();
        }
        let pct = (spent.saturating_mul(100) / cap).clamp(0, i64::from(u8::MAX));
        let mut thresholds = self.limit.alert_thresholds_pct.clone();
        thresholds.sort_unstable();
        let mut out = Vec::new();
        for t in thresholds {
            if i64::from(t) <= pct && !self.fired.contains(&t) {
                self.fired.push(t);
                out.push(BudgetAlert {
                    account: self.account.clone(),
                    threshold_pct: t,
                    spent_units: spent,
                    cap_units: cap,
                });
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DREGG: &str = "DREGG";

    fn guard(cap: i64) -> BudgetGuard {
        BudgetGuard::open("alice", DREGG, SpendLimit::new(cap)).unwrap()
    }

    // ── TOOTH: crossing 80% fires the 50% + 80% alerts; under that, none ──
    #[test]
    fn crossing_eighty_percent_fires_an_alert() {
        let mut g = guard(100);

        // 40 DEC → 40%: below every threshold, no alert.
        match g.charge(40) {
            SpendDecision::Admitted {
                alerts,
                spent_units,
            } => {
                assert_eq!(spent_units, 40);
                assert!(alerts.is_empty(), "40% crosses no threshold");
            }
            other => panic!("expected admit, got {other:?}"),
        }

        // +45 → 85%: crosses 50% AND 80% in one charge — both fire, once each.
        match g.charge(45) {
            SpendDecision::Admitted {
                alerts,
                spent_units,
            } => {
                assert_eq!(spent_units, 85);
                let pcts: Vec<u8> = alerts.iter().map(|a| a.threshold_pct).collect();
                assert_eq!(pcts, vec![50, 80]);
                assert!(
                    alerts
                        .iter()
                        .all(|a| a.account == "alice" && a.cap_units == 100)
                );
            }
            other => panic!("expected admit with alerts, got {other:?}"),
        }

        // +5 → 90%: 50/80 already fired, 100 not yet → no new alert.
        match g.charge(5) {
            SpendDecision::Admitted { alerts, .. } => assert!(alerts.is_empty()),
            other => panic!("expected admit, got {other:?}"),
        }
    }

    // ── TOOTH: a charge that would exceed the hard cap is refused, nothing drawn ──
    #[test]
    fn the_hard_cap_refuses_new_spend() {
        let mut g = guard(100);
        assert!(g.charge(90).is_admitted());
        assert_eq!(g.spent(), 90);
        assert_eq!(g.remaining(), 10);

        // 20 more would exceed the 100 cap → refused, spend unchanged.
        match g.charge(20) {
            SpendDecision::Refused {
                cap_units,
                spent_units,
                attempted,
                ..
            } => {
                assert_eq!(cap_units, 100);
                assert_eq!(spent_units, 90, "nothing drawn on a refusal");
                assert_eq!(attempted, 20);
            }
            other => panic!("expected a refusal, got {other:?}"),
        }
        assert_eq!(g.spent(), 90, "the refused charge left spend untouched");

        // Exactly filling the cap is admitted and fires the 100% alert.
        match g.charge(10) {
            SpendDecision::Admitted {
                spent_units,
                alerts,
            } => {
                assert_eq!(spent_units, 100);
                assert!(alerts.iter().any(|a| a.threshold_pct == 100));
            }
            other => panic!("expected the cap-filling admit, got {other:?}"),
        }
        // And the very next DEC is refused.
        assert!(matches!(g.charge(1), SpendDecision::Refused { .. }));
        assert_eq!(g.remaining(), 0);
    }

    #[test]
    fn a_nonpositive_charge_is_a_noop_admit() {
        let mut g = guard(100);
        assert!(g.charge(0).is_admitted());
        assert_eq!(g.spent(), 0);
    }
}
