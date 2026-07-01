//! `rate` — per-account **rate limiting** over the replenishing-budget cell.
//!
//! Two application-layer rates a permissionless cloud must bound (the transport
//! slow-loris / connection cap already lives below this — this is the per-ACCOUNT
//! half):
//!
//! - **deploy rate** — `N` deploys per hour per account, so one subject cannot
//!   hammer the build/publish path (the spam-deploy magnet);
//! - **request rate** — the gateway serving path, per-site and per-account, so a
//!   tenant cannot hammer (or be hammered into a runaway bill) on the data plane.
//!
//! Both are the **replenishing budget** in its rate-limiter shape: a ceiling of
//! `N` over a sliding `window`, where each consumed unit becomes eligible again
//! exactly one `window` later (`refill_amount = 1`, `refill_max = N`). Over the
//! ceiling is refused FAIL-CLOSED — the `429` signal. The block clock is unix
//! seconds, so `window = 3600` is "per hour".

use std::collections::HashMap;

use dreggnet_exec::budget::{BudgetError, BudgetTerms, ReplenishingBudget};

/// Which rate class a draw is against. The key namespaces the per-account and
/// per-site sliding windows so they don't contend.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RateClass {
    /// Deploys (site publish / server create / agent run launch) by an account.
    Deploy { subject: String },
    /// Inbound requests served on behalf of an account (all its sites).
    AccountRequests { subject: String },
    /// Inbound requests to one specific site (stops a single hot site / a single
    /// tenant being hammered into a bill).
    SiteRequests { site_id: String },
}

impl RateClass {
    fn key(&self) -> String {
        match self {
            RateClass::Deploy { subject } => format!("deploy:{subject}"),
            RateClass::AccountRequests { subject } => format!("acct-req:{subject}"),
            RateClass::SiteRequests { site_id } => format!("site-req:{site_id}"),
        }
    }

    /// The label for the `429` reason / logs.
    pub fn label(&self) -> &'static str {
        match self {
            RateClass::Deploy { .. } => "deploy-rate",
            RateClass::AccountRequests { .. } => "account-request-rate",
            RateClass::SiteRequests { .. } => "site-request-rate",
        }
    }
}

/// The ceiling for a rate class: at most `limit` events per `window_secs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RateLimit {
    /// The number of events admitted in a sliding window.
    pub limit: u32,
    /// The window length in seconds (the replenishment period).
    pub window_secs: i64,
}

impl RateLimit {
    /// `limit` events per `window_secs`.
    pub fn new(limit: u32, window_secs: i64) -> RateLimit {
        RateLimit { limit, window_secs }
    }

    /// `limit` events per hour.
    pub fn per_hour(limit: u32) -> RateLimit {
        RateLimit::new(limit, 3600)
    }

    /// `limit` events per minute.
    pub fn per_minute(limit: u32) -> RateLimit {
        RateLimit::new(limit, 60)
    }

    /// The replenishing-budget terms that realize this rate as a sliding-window
    /// ceiling: budget `limit`, period `window_secs`, each unit refilling 1, the
    /// live queue bounded by `limit`. Schedule rooted at block 0 (unix epoch).
    fn terms(&self, key: &str) -> BudgetTerms {
        BudgetTerms::new(
            key,
            self.limit.max(1) as i64,
            self.window_secs.max(1),
            1,
            self.limit.max(1) as u16,
            0,
        )
    }
}

/// Why a rate draw was refused — the `429` signal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RateExceeded {
    /// Which class hit its ceiling.
    pub class: &'static str,
    /// The ceiling (events per window).
    pub limit: u32,
    /// The window length in seconds.
    pub window_secs: i64,
    /// A `Retry-After` hint in seconds: how long until a slot frees up (≈ one
    /// window from the oldest pending refill).
    pub retry_after_secs: i64,
}

impl std::fmt::Display for RateExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} limit exceeded ({} per {}s): retry after {}s",
            self.class, self.limit, self.window_secs, self.retry_after_secs
        )
    }
}

impl std::error::Error for RateExceeded {}

/// The per-account / per-site rate limiter. Holds one replenishing-budget cell
/// per live rate-class key, draining lazily (no timer): a class that goes quiet
/// for a window naturally returns to full headroom.
#[derive(Default)]
pub struct RateLimiter {
    cells: HashMap<String, ReplenishingBudget>,
}

impl RateLimiter {
    /// A fresh limiter (no windows yet).
    pub fn new() -> RateLimiter {
        RateLimiter::default()
    }

    /// Charge one event against `class` at time `now_secs` (unix seconds) under
    /// `limit`. Admits + records when the sliding window has headroom; refuses
    /// fail-closed (the `429`) when the ceiling is hit. The cell matures lazily,
    /// so a window that has elapsed since the last event returns headroom.
    pub fn charge(
        &mut self,
        class: &RateClass,
        limit: RateLimit,
        now_secs: i64,
    ) -> Result<(), RateExceeded> {
        let key = class.key();
        let terms = limit.terms(&key);
        let cell = self.cells.entry(key).or_insert_with(|| {
            ReplenishingBudget::open(terms.clone()).expect("rate terms well-formed")
        });
        // Mature elapsed windows up to now, then draw one event.
        cell.mature(now_secs);
        match cell.draw(1, now_secs) {
            Ok(_) => Ok(()),
            Err(BudgetError::ExceedsCeiling { .. }) => Err(RateExceeded {
                class: class.label(),
                limit: limit.limit,
                window_secs: limit.window_secs,
                retry_after_secs: limit.window_secs,
            }),
            // A backdated draw (clock skew going backwards) is treated as a refusal
            // rather than a panic — fail closed.
            Err(_) => Err(RateExceeded {
                class: class.label(),
                limit: limit.limit,
                window_secs: limit.window_secs,
                retry_after_secs: limit.window_secs,
            }),
        }
    }

    /// Read-only: how many events `class` has outstanding in the current window
    /// at `now_secs` (for o11y / a console meter).
    pub fn outstanding(&self, class: &RateClass, now_secs: i64) -> i64 {
        self.cells
            .get(&class.key())
            .map(|c| c.outstanding_at(now_secs))
            .unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deploy_rate_429s_over_the_hourly_ceiling() {
        let mut rl = RateLimiter::new();
        let class = RateClass::Deploy {
            subject: "dregg:a".into(),
        };
        let limit = RateLimit::per_hour(3);
        let t0 = 1_000_000;
        // three deploys in the hour admit.
        for i in 0..3 {
            assert!(rl.charge(&class, limit, t0 + i).is_ok(), "deploy {i}");
        }
        // the fourth in the same window is refused (429).
        let refusal = rl.charge(&class, limit, t0 + 4).unwrap_err();
        assert_eq!(refusal.class, "deploy-rate");
        assert_eq!(refusal.limit, 3);
        assert_eq!(refusal.retry_after_secs, 3600);
    }

    #[test]
    fn the_window_slides_so_headroom_returns() {
        let mut rl = RateLimiter::new();
        let class = RateClass::Deploy {
            subject: "dregg:a".into(),
        };
        let limit = RateLimit::per_hour(2);
        let t0 = 1_000_000;
        rl.charge(&class, limit, t0).unwrap();
        rl.charge(&class, limit, t0 + 10).unwrap();
        // exhausted within the hour.
        assert!(rl.charge(&class, limit, t0 + 20).is_err());
        // one hour after the first draw, its slot has refilled → admits again.
        assert!(rl.charge(&class, limit, t0 + 3600).is_ok());
    }

    #[test]
    fn request_rate_is_per_site_and_per_account_independently() {
        let mut rl = RateLimiter::new();
        let site = RateClass::SiteRequests {
            site_id: "site_x".into(),
        };
        let acct = RateClass::AccountRequests {
            subject: "dregg:a".into(),
        };
        let limit = RateLimit::per_minute(2);
        let t0 = 5_000;
        // the site window and the account window are independent keys.
        assert!(rl.charge(&site, limit, t0).is_ok());
        assert!(rl.charge(&site, limit, t0).is_ok());
        assert!(rl.charge(&site, limit, t0).is_err()); // site hammered → 429
        // the account window (a different key) still has its own headroom.
        assert!(rl.charge(&acct, limit, t0).is_ok());
        assert!(rl.charge(&acct, limit, t0).is_ok());
        assert!(rl.charge(&acct, limit, t0).is_err());
    }
}
