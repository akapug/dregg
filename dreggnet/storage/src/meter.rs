//! `meter` — pay-per-operation + pay-per-byte metering for bucket operations.
//!
//! Storage is a **paid** service: every mutating operation is charged against a
//! funded account before it commits, and an operation that would exceed the
//! account budget is refused (`PaymentRequired`) *before* any state is written —
//! the object-store counterpart of the webapp router's pre-handler `402`.
//!
//! This in-process [`Account`] + [`Pricing`] is the stand-in for the real
//! verified rail. On a dregg node the budget is a funded `execution-lease` /
//! `StandingObligation` and each charge is a metered `Payable` tick — exactly the
//! lease⟷meter weld `dreggnet-bridge` already drives for compute. Here the meter
//! enforces the same honest invariant locally: **no operation runs beyond what
//! the account budget proves was paid for.**

use std::sync::Mutex;

use serde::{Deserialize, Serialize};

/// The price list for bucket operations, in abstract meter units (the dregg
/// `Payable` unit on the real rail). A `put` is charged a flat op cost plus a
/// per-KiB storage cost over the stored bytes; reads/list are charged a flat op
/// cost; a delete is charged a flat op cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pricing {
    /// Flat cost charged per `put`.
    pub put_op_units: i64,
    /// Cost charged per KiB (rounded up) of object bytes on a `put`.
    pub put_units_per_kib: i64,
    /// Flat cost charged per `get` / `verified_get`.
    pub get_op_units: i64,
    /// Flat cost charged per `list`.
    pub list_op_units: i64,
    /// Flat cost charged per `delete`.
    pub delete_op_units: i64,
}

impl Default for Pricing {
    /// A sensible default: writes cost more than reads; storage is billed per KiB.
    fn default() -> Pricing {
        Pricing {
            put_op_units: 10,
            put_units_per_kib: 1,
            get_op_units: 1,
            list_op_units: 2,
            delete_op_units: 5,
        }
    }
}

impl Pricing {
    /// A free price list (every operation costs zero) — for unmetered local use.
    pub fn free() -> Pricing {
        Pricing {
            put_op_units: 0,
            put_units_per_kib: 0,
            get_op_units: 0,
            list_op_units: 0,
            delete_op_units: 0,
        }
    }

    /// The cost of a `put` storing `bytes` bytes: the flat op cost plus the
    /// per-KiB storage cost (KiB rounded up, so any non-empty object pays for at
    /// least 1 KiB of storage).
    pub fn put_cost(&self, bytes: usize) -> i64 {
        let kib = bytes.div_ceil(1024) as i64;
        self.put_op_units + kib * self.put_units_per_kib
    }
}

/// A funded account a holder's operations are metered against. The stand-in for a
/// funded dregg `execution-lease` budget; charges are atomic and the remaining
/// balance never goes negative (an over-budget charge is rejected, not clamped).
pub struct Account {
    /// The account holder (for receipts/audit).
    pub holder: String,
    /// Remaining budget, in meter units. Decremented on each successful charge.
    remaining: Mutex<i64>,
    /// Total charged so far (for receipts/audit).
    spent: Mutex<i64>,
}

impl Account {
    /// A funded account for `holder` with `budget_units` of budget.
    pub fn funded(holder: impl Into<String>, budget_units: i64) -> Account {
        Account {
            holder: holder.into(),
            remaining: Mutex::new(budget_units.max(0)),
            spent: Mutex::new(0),
        }
    }

    /// The remaining budget.
    pub fn remaining(&self) -> i64 {
        *self.remaining.lock().expect("account poisoned")
    }

    /// The total charged so far.
    pub fn spent(&self) -> i64 {
        *self.spent.lock().expect("account poisoned")
    }

    /// Charge `units` against the account. Succeeds (returning the new remaining
    /// balance) only if the account can cover the full charge; otherwise the
    /// account is untouched and [`OverBudget`] is returned — the caller must
    /// refuse the operation before committing any state.
    pub fn charge(&self, units: i64) -> Result<i64, OverBudget> {
        let units = units.max(0);
        let mut remaining = self.remaining.lock().expect("account poisoned");
        if *remaining < units {
            return Err(OverBudget {
                requested: units,
                remaining: *remaining,
            });
        }
        *remaining -= units;
        *self.spent.lock().expect("account poisoned") += units;
        Ok(*remaining)
    }
}

/// An operation was refused because the account could not cover its metered cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OverBudget {
    /// The units the operation required.
    pub requested: i64,
    /// The units the account had remaining.
    pub remaining: i64,
}

impl std::fmt::Display for OverBudget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "operation requires {} units but only {} remain",
            self.requested, self.remaining
        )
    }
}

impl std::error::Error for OverBudget {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn put_cost_rounds_kib_up() {
        let p = Pricing::default();
        assert_eq!(p.put_cost(0), 10); // empty object: just the op cost
        assert_eq!(p.put_cost(1), 11); // 1 byte → 1 KiB billed
        assert_eq!(p.put_cost(1024), 11); // exactly 1 KiB
        assert_eq!(p.put_cost(1025), 12); // spills into a 2nd KiB
    }

    #[test]
    fn account_charges_and_refuses_over_budget() {
        let acct = Account::funded("agent:ember", 25);
        assert_eq!(acct.charge(10).unwrap(), 15);
        assert_eq!(acct.charge(10).unwrap(), 5);
        // The next 10 won't fit: refused, account untouched.
        assert_eq!(
            acct.charge(10),
            Err(OverBudget {
                requested: 10,
                remaining: 5
            })
        );
        assert_eq!(acct.remaining(), 5);
        assert_eq!(acct.spent(), 20);
        // A charge that fits still works.
        assert_eq!(acct.charge(5).unwrap(), 0);
    }
}
