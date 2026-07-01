//! `quota` — per-account ceilings on what an anonymous cap-account may hold.
//!
//! A permissionless cloud cannot let one `dga1_` subject deploy an unbounded
//! number of sites/servers/agents or consume unbounded compute/bandwidth/storage
//! — that is the spam/abuse magnet. A quota is a **ceiling**: a new resource that
//! would push an account past its ceiling is refused IN-BAND (the budget-`402`
//! shape), before any record or backend is created.
//!
//! Two families of bound:
//! - **counts** ([`Countable`]): how many live sites/servers/agents/buckets/domains
//!   an account holds at once — a slot is taken on create, returned on destroy.
//! - **totals** ([`Metered`]): cumulative compute units / bandwidth bytes / storage
//!   bytes against a ceiling — the same arithmetic the replenishing-budget cell
//!   decides (`dreggnet_exec::budget::prepaid_ceiling_admits`), so a quota is
//!   literally the budget's ceiling decision reused.
//!
//! The ceiling an account gets depends on its [`AccountStanding`]: `Good` gets the
//! conservative default tier, `Flagged` a tighter tier, `Suspended` zero.

use std::collections::HashMap;

use dreggnet_exec::budget::prepaid_ceiling_admits;
use serde::{Deserialize, Serialize};

use crate::governance::AccountStanding;

/// A counted resource — bounded by how many an account holds live at once.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Countable {
    /// A published static site (`webapp` `SiteCell`).
    Site,
    /// A persistent server (`control` `ServerFleet`) / a gateway machine.
    Server,
    /// A long-running agent (`exec` agent run).
    Agent,
    /// An object-store bucket (`storage` `BucketRegistry`).
    Bucket,
    /// A bound custom domain (`dregg-domains` `DomainBinding`).
    Domain,
}

impl Countable {
    /// The log/error label.
    pub fn as_str(self) -> &'static str {
        match self {
            Countable::Site => "site",
            Countable::Server => "server",
            Countable::Agent => "agent",
            Countable::Bucket => "bucket",
            Countable::Domain => "domain",
        }
    }
}

/// A metered consumable — bounded by a cumulative ceiling.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Metered {
    /// Cumulative compute units billed to the account.
    ComputeUnits,
    /// Cumulative bandwidth bytes served on the account's behalf.
    BandwidthBytes,
    /// Cumulative stored bytes the account holds.
    StorageBytes,
}

impl Metered {
    /// The log/error label.
    pub fn as_str(self) -> &'static str {
        match self {
            Metered::ComputeUnits => "compute-units",
            Metered::BandwidthBytes => "bandwidth-bytes",
            Metered::StorageBytes => "storage-bytes",
        }
    }
}

/// The full ceiling set for one standing tier. `0` means "none allowed".
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuotaLimits {
    /// Max live sites.
    pub sites: u64,
    /// Max live servers/machines.
    pub servers: u64,
    /// Max live agents.
    pub agents: u64,
    /// Max live buckets.
    pub buckets: u64,
    /// Max bound domains.
    pub domains: u64,
    /// Cumulative compute-units ceiling.
    pub compute_units: u64,
    /// Cumulative bandwidth-bytes ceiling.
    pub bandwidth_bytes: u64,
    /// Cumulative storage-bytes ceiling.
    pub storage_bytes: u64,
}

impl QuotaLimits {
    /// The all-zero limits — what a `Suspended` account gets (create nothing).
    pub const ZERO: QuotaLimits = QuotaLimits {
        sites: 0,
        servers: 0,
        agents: 0,
        buckets: 0,
        domains: 0,
        compute_units: 0,
        bandwidth_bytes: 0,
        storage_bytes: 0,
    };

    /// The ceiling for a counted resource.
    pub fn count_limit(&self, kind: Countable) -> u64 {
        match kind {
            Countable::Site => self.sites,
            Countable::Server => self.servers,
            Countable::Agent => self.agents,
            Countable::Bucket => self.buckets,
            Countable::Domain => self.domains,
        }
    }

    /// The ceiling for a metered resource.
    pub fn metered_limit(&self, kind: Metered) -> u64 {
        match kind {
            Metered::ComputeUnits => self.compute_units,
            Metered::BandwidthBytes => self.bandwidth_bytes,
            Metered::StorageBytes => self.storage_bytes,
        }
    }
}

/// The per-standing quota tiers: the ceiling an account gets is a function of its
/// standing. `Suspended` is always [`QuotaLimits::ZERO`] (not stored).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuotaPolicy {
    /// The conservative default tier for a `Good` (new, anonymous) account.
    pub good: QuotaLimits,
    /// The tighter tier a `Flagged` (under-review) account is throttled to.
    pub flagged: QuotaLimits,
}

impl QuotaPolicy {
    /// The ceiling set an account in `standing` is held to.
    pub fn limits_for(&self, standing: AccountStanding) -> QuotaLimits {
        match standing {
            AccountStanding::Good => self.good,
            AccountStanding::Flagged => self.flagged,
            AccountStanding::Suspended => QuotaLimits::ZERO,
        }
    }
}

impl Default for QuotaPolicy {
    /// A deliberately CONSERVATIVE default for a KYC-free account — enough to try
    /// the platform out, not enough to be a useful spam/malware host. Raising it
    /// is an operator/payment action (a standing/tier change), never automatic.
    fn default() -> Self {
        QuotaPolicy {
            good: QuotaLimits {
                sites: 3,
                servers: 2,
                agents: 2,
                buckets: 2,
                domains: 1,
                // ~ a small free trial of metered resources.
                compute_units: 100_000,
                bandwidth_bytes: 5 * 1024 * 1024 * 1024, // 5 GiB
                storage_bytes: 1024 * 1024 * 1024,       // 1 GiB
            },
            flagged: QuotaLimits {
                sites: 1,
                servers: 0,
                agents: 0,
                buckets: 1,
                domains: 0,
                compute_units: 10_000,
                bandwidth_bytes: 512 * 1024 * 1024, // 512 MiB
                storage_bytes: 256 * 1024 * 1024,   // 256 MiB
            },
        }
    }
}

/// Why a quota admission was refused — the in-band `402`-shape signal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuotaError {
    /// A counted resource would exceed the account's live-count ceiling.
    CountExceeded {
        /// Which counted resource.
        kind: Countable,
        /// The ceiling for the account's standing.
        limit: u64,
        /// How many the account already holds live.
        used: u64,
    },
    /// A metered draw would exceed the account's cumulative ceiling.
    MeteredExceeded {
        /// Which metered resource.
        kind: Metered,
        /// The ceiling for the account's standing.
        limit: u64,
        /// How much the account has already consumed.
        used: u64,
        /// The amount the draw requested.
        requested: u64,
    },
}

impl std::fmt::Display for QuotaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuotaError::CountExceeded { kind, limit, used } => write!(
                f,
                "{} quota exhausted ({used}/{limit}): refused",
                kind.as_str()
            ),
            QuotaError::MeteredExceeded {
                kind,
                limit,
                used,
                requested,
            } => write!(
                f,
                "{} quota exhausted ({used} + {requested} > {limit}): refused",
                kind.as_str()
            ),
        }
    }
}

impl std::error::Error for QuotaError {}

/// Per-account usage: live counts + cumulative metered totals. The single source
/// of truth a quota admission consults. Keyed by subject (`dga1_`-derived id).
#[derive(Clone, Debug, Default)]
struct Usage {
    counts: HashMap<Countable, u64>,
    metered: HashMap<Metered, u64>,
}

/// The quota ledger: tracks every account's live counts + metered totals and
/// decides admission against the standing-tiered [`QuotaPolicy`].
#[derive(Default)]
pub struct QuotaLedger {
    by_subject: HashMap<String, Usage>,
}

impl QuotaLedger {
    /// A fresh ledger (no usage recorded).
    pub fn new() -> QuotaLedger {
        QuotaLedger::default()
    }

    /// The live count an account holds of `kind`.
    pub fn count(&self, subject: &str, kind: Countable) -> u64 {
        self.by_subject
            .get(subject)
            .and_then(|u| u.counts.get(&kind).copied())
            .unwrap_or(0)
    }

    /// The cumulative metered total an account has consumed of `kind`.
    pub fn metered(&self, subject: &str, kind: Metered) -> u64 {
        self.by_subject
            .get(subject)
            .and_then(|u| u.metered.get(&kind).copied())
            .unwrap_or(0)
    }

    /// Whether creating one more `kind` would be admitted for an account in
    /// `standing` (read-only; no mutation). The ceiling is the standing tier's.
    pub fn would_admit_count(
        &self,
        subject: &str,
        kind: Countable,
        standing: AccountStanding,
        policy: &QuotaPolicy,
    ) -> Result<(), QuotaError> {
        let limit = policy.limits_for(standing).count_limit(kind);
        let used = self.count(subject, kind);
        // Decide through the SAME ceiling primitive the budget cell uses: a draw
        // of 1 against the `limit` ceiling with `used` already consumed.
        if prepaid_ceiling_admits(limit as i64, used as i64, 1) {
            Ok(())
        } else {
            Err(QuotaError::CountExceeded { kind, limit, used })
        }
    }

    /// Admit + record one new `kind` for an account in `standing`. Refuses
    /// in-band over the ceiling (no slot taken on refusal).
    pub fn create(
        &mut self,
        subject: &str,
        kind: Countable,
        standing: AccountStanding,
        policy: &QuotaPolicy,
    ) -> Result<(), QuotaError> {
        self.would_admit_count(subject, kind, standing, policy)?;
        *self
            .by_subject
            .entry(subject.to_string())
            .or_default()
            .counts
            .entry(kind)
            .or_insert(0) += 1;
        Ok(())
    }

    /// Return a counted slot (a resource was destroyed). Saturates at zero.
    pub fn release(&mut self, subject: &str, kind: Countable) {
        if let Some(u) = self.by_subject.get_mut(subject) {
            let c = u.counts.entry(kind).or_insert(0);
            *c = c.saturating_sub(1);
        }
    }

    /// Whether drawing `amount` more of a metered `kind` stays under the
    /// account's cumulative ceiling for `standing` (read-only).
    pub fn would_admit_metered(
        &self,
        subject: &str,
        kind: Metered,
        amount: u64,
        standing: AccountStanding,
        policy: &QuotaPolicy,
    ) -> Result<(), QuotaError> {
        let limit = policy.limits_for(standing).metered_limit(kind);
        let used = self.metered(subject, kind);
        if prepaid_ceiling_admits(limit as i64, used as i64, amount as i64) {
            Ok(())
        } else {
            Err(QuotaError::MeteredExceeded {
                kind,
                limit,
                used,
                requested: amount,
            })
        }
    }

    /// Admit + record a metered draw of `amount` for an account in `standing`.
    /// Refuses in-band over the cumulative ceiling (nothing charged on refusal).
    pub fn charge(
        &mut self,
        subject: &str,
        kind: Metered,
        amount: u64,
        standing: AccountStanding,
        policy: &QuotaPolicy,
    ) -> Result<(), QuotaError> {
        self.would_admit_metered(subject, kind, amount, standing, policy)?;
        *self
            .by_subject
            .entry(subject.to_string())
            .or_default()
            .metered
            .entry(kind)
            .or_insert(0) += amount;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn policy() -> QuotaPolicy {
        QuotaPolicy::default()
    }

    #[test]
    fn count_quota_refuses_in_band_over_the_ceiling() {
        let mut q = QuotaLedger::new();
        let p = policy();
        // good tier allows 3 sites.
        for i in 0..3 {
            assert!(
                q.create("dregg:a", Countable::Site, AccountStanding::Good, &p)
                    .is_ok(),
                "site {i} should admit"
            );
        }
        // the 4th is refused in-band.
        assert_eq!(
            q.create("dregg:a", Countable::Site, AccountStanding::Good, &p),
            Err(QuotaError::CountExceeded {
                kind: Countable::Site,
                limit: 3,
                used: 3
            })
        );
        // a refusal takes no slot — still 3.
        assert_eq!(q.count("dregg:a", Countable::Site), 3);
    }

    #[test]
    fn releasing_a_slot_lets_a_new_create_through() {
        let mut q = QuotaLedger::new();
        let p = policy();
        for _ in 0..3 {
            q.create("dregg:a", Countable::Site, AccountStanding::Good, &p)
                .unwrap();
        }
        assert!(
            q.create("dregg:a", Countable::Site, AccountStanding::Good, &p)
                .is_err()
        );
        // destroy one → a slot opens.
        q.release("dregg:a", Countable::Site);
        assert_eq!(q.count("dregg:a", Countable::Site), 2);
        assert!(
            q.create("dregg:a", Countable::Site, AccountStanding::Good, &p)
                .is_ok()
        );
    }

    #[test]
    fn flagged_tier_is_tighter() {
        let mut q = QuotaLedger::new();
        let p = policy();
        // flagged allows 1 site, 0 servers.
        assert!(
            q.create("dregg:f", Countable::Site, AccountStanding::Flagged, &p)
                .is_ok()
        );
        assert!(
            q.create("dregg:f", Countable::Site, AccountStanding::Flagged, &p)
                .is_err()
        );
        assert_eq!(
            q.create("dregg:f", Countable::Server, AccountStanding::Flagged, &p),
            Err(QuotaError::CountExceeded {
                kind: Countable::Server,
                limit: 0,
                used: 0
            })
        );
    }

    #[test]
    fn suspended_tier_creates_nothing() {
        let mut q = QuotaLedger::new();
        let p = policy();
        for kind in [
            Countable::Site,
            Countable::Server,
            Countable::Agent,
            Countable::Bucket,
            Countable::Domain,
        ] {
            assert!(
                q.create("dregg:s", kind, AccountStanding::Suspended, &p)
                    .is_err(),
                "{} must be refused for a suspended account",
                kind.as_str()
            );
        }
    }

    #[test]
    fn metered_ceiling_refuses_over_the_cumulative_total() {
        let mut q = QuotaLedger::new();
        let p = policy();
        let limit = p.good.compute_units;
        // draw up to the ceiling.
        assert!(
            q.charge(
                "dregg:m",
                Metered::ComputeUnits,
                limit,
                AccountStanding::Good,
                &p
            )
            .is_ok()
        );
        // one more unit is refused.
        assert_eq!(
            q.charge(
                "dregg:m",
                Metered::ComputeUnits,
                1,
                AccountStanding::Good,
                &p
            ),
            Err(QuotaError::MeteredExceeded {
                kind: Metered::ComputeUnits,
                limit,
                used: limit,
                requested: 1,
            })
        );
        assert_eq!(q.metered("dregg:m", Metered::ComputeUnits), limit);
    }
}
