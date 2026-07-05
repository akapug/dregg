//! `hosting_meter` — the unified metered-`$DREGG` **hosting billing** rail
//! (`docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.5).
//!
//! Liftoff bills hosting in its token; this is the parity-plus-verifiability move:
//! every hosting resource is a metered, receipted, `$DREGG`-settled charge that
//! rides the **same exactly-once conserving ledger** compute-leases settle through
//! ([`dreggnet_durable::Settlement`] / [`crate::settle_ledger`] /
//! [`crate::node_api::NodeApiSettlement`]). One meter shape over five resources:
//!
//! ```text
//!   resource    meter                              settles as
//!   ─────────   ────────────────────────────────   ───────────────────────────────
//!   publish     per publish op + per-KiB stored     one charge on the publish turn
//!   bandwidth   per-MiB served (the NEW counter)    a per-period roll-up charge
//!   uptime      per wall-clock period               a per-period tick (the §3.3 shape)
//!   cert        per issued/renewed cert             a per-issuance charge
//!   build       per deploy build-minute             a charge on the build workflow
//! ```
//!
//! ## One ledger, exactly-once, Σδ = 0
//!
//! Each charge is a [`LeaseCharge`] moving `units` of the hosting asset from the
//! **site owner's spend account** (the payer) to the **provider** (the beneficiary),
//! settled through a [`Settlement`]. Because that sink is the same conserving,
//! exactly-once rail the compute orchestrator uses, a hosting charge is:
//! - **conserving** — the owner is debited exactly what the provider is credited
//!   (per-asset Σδ = 0);
//! - **exactly-once** — keyed `(lease_id, period)`, so a re-run (a roll-up retried,
//!   a settler restart over a [`DurableSettleLedger`](crate::settle_ledger)) settles
//!   nothing new. The hosting `lease_id` is `host:<resource>:<key>` and the `period`
//!   is the resource's ordinal (publish seq, cert issuance, build seq, uptime
//!   period, or the bandwidth roll-up counter).
//!
//! ## Charge before the operation commits; lapse stops serving
//!
//! A discrete charge (publish/cert/build/uptime) that the owner cannot cover comes
//! back [`HostingError::OverBudget`] — the caller refuses the operation before it
//! commits (the `storage/src/meter.rs` pre-`402` shape). A **bandwidth** roll-up the
//! owner cannot cover **lapses** the site in the shared
//! [`BandwidthMeter`](dreggnet_webapp::BandwidthMeter): the serving path then refuses
//! it with `402` — a site with an exhausted hosting budget stops being served,
//! exactly as a lapsed compute lease is reaped.
//!
//! ## Real vs the named on-chain wire (honest)
//!
//! - **Real (this module, in-process, tested):** the per-resource pricing, the
//!   bandwidth byte roll-up over the live serving counter, the charge-before-commit
//!   gate, the lapse→stop-serving, and the fold through the conserving exactly-once
//!   [`Settlement`] — proven end to end over [`ConservingLedger`](dreggnet_durable::ConservingLedger).
//! - **Reviewed-go / S3-gated:** pointing the [`Settlement`] at the real
//!   [`NodeApiSettlement`](crate::node_api::NodeApiSettlement) so each hosting charge
//!   is a real on-chain conserving `Transfer` against real `$DREGG` accounts on the
//!   live edge. The seam is identical — the orchestrator constructs the meter over
//!   either sink — so the billing proven here carries over unchanged.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use dreggnet_durable::{LeaseCharge, SettleError, SettleReceipt, Settlement};
use dreggnet_webapp::{BandwidthMeter, SiteRegistry};

const KIB: u64 = 1024;
const MIB: u64 = 1024 * 1024;

/// The per-resource price list, in abstract meter units (the `$DREGG` `Payable` unit
/// on the real rail). The single pricing shape the five hosting resources bill on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostingPricing {
    /// Flat cost charged per publish operation.
    pub publish_op_units: i64,
    /// Cost per KiB (rounded up) of stored site bytes on a publish.
    pub publish_units_per_kib: i64,
    /// Cost per MiB (rounded up) of bytes served — the bandwidth roll-up rate.
    pub bandwidth_units_per_mib: i64,
    /// Cost charged per wall-clock uptime period (served sites / servers).
    pub uptime_units_per_period: i64,
    /// Flat cost charged per issued / renewed cert.
    pub cert_units_per_issue: i64,
    /// Cost charged per deploy build-minute in the sandbox.
    pub build_units_per_minute: i64,
}

impl Default for HostingPricing {
    /// A sensible default: a publish has an op + per-KiB storage cost; bandwidth
    /// bills per served MiB; uptime/cert/build each carry a flat per-unit cost.
    fn default() -> HostingPricing {
        HostingPricing {
            publish_op_units: 10,
            publish_units_per_kib: 1,
            bandwidth_units_per_mib: 5,
            uptime_units_per_period: 2,
            cert_units_per_issue: 4,
            build_units_per_minute: 3,
        }
    }
}

impl HostingPricing {
    /// A free price list (every hosting resource costs zero) — the subsidized early
    /// era, where the meter accrues but settles nothing.
    pub fn free() -> HostingPricing {
        HostingPricing {
            publish_op_units: 0,
            publish_units_per_kib: 0,
            bandwidth_units_per_mib: 0,
            uptime_units_per_period: 0,
            cert_units_per_issue: 0,
            build_units_per_minute: 0,
        }
    }

    /// The cost of publishing a site of `stored_bytes`: the flat op cost plus the
    /// per-KiB storage cost (KiB rounded up).
    pub fn publish_cost(&self, stored_bytes: u64) -> i64 {
        self.publish_op_units + ceil_div(stored_bytes, KIB) as i64 * self.publish_units_per_kib
    }

    /// The cost of serving `served_bytes` of bandwidth: per-MiB (rounded up), so any
    /// non-empty roll-up pays for at least 1 MiB.
    pub fn bandwidth_cost(&self, served_bytes: u64) -> i64 {
        ceil_div(served_bytes, MIB) as i64 * self.bandwidth_units_per_mib
    }

    /// The cost of a `minutes`-minute deploy build (negative minutes clamp to 0).
    pub fn build_cost(&self, minutes: i64) -> i64 {
        self.build_units_per_minute * minutes.max(0)
    }
}

/// Which hosting resource a charge bills — the receipt's label + the `lease_id` tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostingResource {
    Publish,
    Bandwidth,
    Uptime,
    Cert,
    Build,
}

impl HostingResource {
    /// The lowercase tag this resource carries in its `host:<tag>:<key>` lease id.
    pub fn tag(self) -> &'static str {
        match self {
            HostingResource::Publish => "publish",
            HostingResource::Bandwidth => "bandwidth",
            HostingResource::Uptime => "uptime",
            HostingResource::Cert => "cert",
            HostingResource::Build => "build",
        }
    }
}

/// Why a hosting charge was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostingError {
    /// The owner's spend account could not cover the charge — the operation is
    /// refused before it commits (the pre-`402` charge-before-commit gate). For a
    /// discrete resource this aborts the op; for bandwidth the site is lapsed instead.
    OverBudget {
        resource: HostingResource,
        account: String,
        amount: i64,
    },
    /// The settlement backend refused for a reason other than budget (a conflict,
    /// a node fault on the real rail).
    Settle(SettleError),
}

impl std::fmt::Display for HostingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HostingError::OverBudget {
                resource,
                account,
                amount,
            } => write!(
                f,
                "hosting {} charge of {amount} refused: account `{account}` over budget",
                resource.tag()
            ),
            HostingError::Settle(e) => write!(f, "hosting settlement failed: {e}"),
        }
    }
}

impl std::error::Error for HostingError {}

/// The receipt of one settled hosting charge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostingReceipt {
    /// Which resource was billed.
    pub resource: HostingResource,
    /// The site / domain / deploy the charge is for.
    pub subject: String,
    /// The units billed.
    pub units: i64,
    /// The underlying conserving settlement receipt (the exactly-once / Σδ witness).
    pub settle: SettleReceipt,
}

/// The outcome of one bandwidth roll-up for a site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BandwidthOutcome {
    /// The unbilled bytes were rolled up + settled. Carries the roll-up period, the
    /// bytes billed, and the units charged.
    Charged { period: i64, bytes: u64, units: i64 },
    /// No unbilled bytes — nothing to settle this roll-up.
    NoTraffic,
    /// The owner's spend account is exhausted: the site was **lapsed** (serving
    /// stops) — the hosting analog of a compute lease reaping.
    Lapsed { reason: String },
}

/// The unified hosting-billing meter: one [`Settlement`]-backed rail over the five
/// hosting resources, plus the shared bandwidth byte-counter it rolls up.
pub struct HostingMeter {
    pricing: HostingPricing,
    settlement: Arc<dyn Settlement>,
    /// The asset hosting is billed in (the `$DREGG` token id / cell).
    asset: String,
    /// The provider account every hosting charge is paid to.
    beneficiary: String,
    /// The live per-site bandwidth byte-counter (shared with the serving path).
    bandwidth: Arc<BandwidthMeter>,
    /// The authoritative published-site set, when wired (HB-3). The bandwidth roll-up
    /// bills EVERY site with recorded traffic, resolving the payer from the published
    /// [`SiteCell::owner`](dreggnet_webapp::SiteCell) — so a served-but-never-manually-
    /// registered site is no longer free hosting. `None` falls back to `accounts`-only
    /// (the pre-HB-3 behaviour, e.g. tests with no registry).
    registry: Option<Arc<SiteRegistry>>,
    /// site → owner spend account: an **explicit override** of the registry-derived
    /// owner (e.g. a beneficiary distinct from the publishing cell). With no registry
    /// wired this is the only owner source; with one, it takes precedence per site.
    accounts: Mutex<HashMap<String, String>>,
    /// site → last settled bandwidth roll-up period (the next is `+ 1`).
    bw_periods: Mutex<HashMap<String, i64>>,
}

impl HostingMeter {
    /// A hosting meter pricing at `pricing`, settling each charge through
    /// `settlement` (the conserving exactly-once ledger) in `asset` to the provider
    /// `beneficiary`, rolling up the live `bandwidth` byte-counter.
    pub fn new(
        pricing: HostingPricing,
        settlement: Arc<dyn Settlement>,
        asset: impl Into<String>,
        beneficiary: impl Into<String>,
        bandwidth: Arc<BandwidthMeter>,
    ) -> HostingMeter {
        HostingMeter {
            pricing,
            settlement,
            asset: asset.into(),
            beneficiary: beneficiary.into(),
            bandwidth,
            registry: None,
            accounts: Mutex::new(HashMap::new()),
            bw_periods: Mutex::new(HashMap::new()),
        }
    }

    /// Wire the authoritative published-site [`SiteRegistry`] (HB-3): the bandwidth
    /// roll-up then bills every served site off the published set, taking the payer
    /// from each [`SiteCell::owner`](dreggnet_webapp::SiteCell) — no `register_site`
    /// call required, so a published-and-served site cannot accrue free egress that
    /// the roll-up skips forever.
    pub fn with_site_registry(mut self, registry: Arc<SiteRegistry>) -> HostingMeter {
        self.registry = Some(registry);
        self
    }

    /// Resolve the owner spend account a served `site`'s bandwidth bills to: the
    /// explicit `accounts` override first, else the published cell's owner (HB-3).
    fn owner_of(&self, site: &str) -> Option<String> {
        if let Some(owner) = self
            .accounts
            .lock()
            .expect("hosting meter poisoned")
            .get(site)
        {
            return Some(owner.clone());
        }
        self.registry
            .as_ref()
            .and_then(|r| r.get(site))
            .map(|cell| cell.owner)
    }

    /// The price list this meter bills on.
    pub fn pricing(&self) -> &HostingPricing {
        &self.pricing
    }

    /// The shared bandwidth byte-counter (the serving path records into this).
    pub fn bandwidth(&self) -> &Arc<BandwidthMeter> {
        &self.bandwidth
    }

    /// Register `site`'s owner spend account, so [`tick_all_bandwidth`](Self::tick_all_bandwidth)
    /// can bill its served bytes to the right payer.
    pub fn register_site(&self, site: impl Into<String>, owner: impl Into<String>) {
        self.accounts
            .lock()
            .expect("hosting meter poisoned")
            .insert(site.into(), owner.into());
    }

    /// **Fund a site's in-band bandwidth budget** (HB-1): authorize `budget_bytes` of
    /// served egress, set on the shared [`BandwidthMeter`] the serving path enforces.
    /// Once a site's served bytes would exceed this, the serving path refuses `402`
    /// IN-BAND — so free egress is bounded by funded coverage, not by roll-up latency.
    /// The control plane sets this from the owner's funded hosting balance (converting
    /// the funded `units` to covered bytes at the bandwidth rate via
    /// [`covered_bytes_for`](Self::covered_bytes_for)).
    pub fn fund_bandwidth_budget(&self, site: &str, budget_bytes: u64) {
        self.bandwidth.set_budget(site, budget_bytes);
    }

    /// Top up a site's in-band bandwidth budget by `bytes` (a coverage top-up that
    /// resumes serving once an exhausted site is re-funded).
    pub fn top_up_bandwidth_budget(&self, site: &str, bytes: u64) {
        self.bandwidth.add_budget(site, bytes);
    }

    /// How many served bytes `funded_units` of the hosting asset covers at this
    /// meter's bandwidth rate — the conversion the control plane uses to turn an
    /// owner's funded balance into the in-band serving ceiling. A zero/absent rate
    /// (the free era) covers unbounded bytes (`u64::MAX`).
    pub fn covered_bytes_for(&self, funded_units: i64) -> u64 {
        let rate = self.pricing.bandwidth_units_per_mib;
        if rate <= 0 || funded_units <= 0 {
            return u64::MAX;
        }
        // funded_units / rate MiB of coverage (floor — never authorize more than funded).
        ((funded_units as u64) / (rate as u64)).saturating_mul(MIB)
    }

    /// Settle one charge of `amount` of the hosting asset, `owner → provider`, keyed
    /// `(host:<resource>:<key>, period)`. A zero charge settles trivially (the free
    /// era); an over-budget charge surfaces as [`HostingError::OverBudget`].
    fn charge(
        &self,
        resource: HostingResource,
        subject: &str,
        owner: &str,
        key: &str,
        period: i64,
        amount: i64,
    ) -> Result<HostingReceipt, HostingError> {
        let lease_id = format!("host:{}:{}", resource.tag(), key);
        if amount <= 0 {
            // Nothing to move (free tier): a trivial, conserving no-op receipt.
            return Ok(HostingReceipt {
                resource,
                subject: subject.to_string(),
                units: 0,
                settle: SettleReceipt {
                    lease_id,
                    period,
                    asset: self.asset.clone(),
                    amount: 0,
                    payer_balance: 0,
                    beneficiary_balance: 0,
                    replayed: false,
                },
            });
        }
        let charge = LeaseCharge::new(
            owner,
            &self.beneficiary,
            &self.asset,
            lease_id,
            period,
            amount,
        );
        match self.settlement.settle(&charge) {
            Ok(settle) => Ok(HostingReceipt {
                resource,
                subject: subject.to_string(),
                units: amount,
                settle,
            }),
            Err(SettleError::InsufficientFunds { .. }) => Err(HostingError::OverBudget {
                resource,
                account: owner.to_string(),
                amount,
            }),
            Err(e) => Err(HostingError::Settle(e)),
        }
    }

    /// Meter a **publish**: the flat op cost + the per-KiB storage cost over
    /// `stored_bytes`, billed to `owner`, keyed by the publish `seq` (the
    /// registry-monotonic publish ordinal — re-metering the same publish replays).
    pub fn meter_publish(
        &self,
        site: &str,
        owner: &str,
        stored_bytes: u64,
        seq: u64,
    ) -> Result<HostingReceipt, HostingError> {
        let amount = self.pricing.publish_cost(stored_bytes);
        self.charge(
            HostingResource::Publish,
            site,
            owner,
            site,
            seq as i64,
            amount,
        )
    }

    /// Meter an **uptime** period for a served site/server, billed to `owner`, keyed
    /// by the period ordinal (the §3.3 per-wall-clock-period shape).
    pub fn meter_uptime(
        &self,
        site: &str,
        owner: &str,
        period: i64,
    ) -> Result<HostingReceipt, HostingError> {
        self.charge(
            HostingResource::Uptime,
            site,
            owner,
            site,
            period,
            self.pricing.uptime_units_per_period,
        )
    }

    /// Meter a **cert** issuance/renewal for `domain`, billed to `owner`, keyed by
    /// the issuance `seq`.
    pub fn meter_cert(
        &self,
        domain: &str,
        owner: &str,
        seq: u64,
    ) -> Result<HostingReceipt, HostingError> {
        self.charge(
            HostingResource::Cert,
            domain,
            owner,
            domain,
            seq as i64,
            self.pricing.cert_units_per_issue,
        )
    }

    /// Meter a deploy **build** of `minutes` build-minutes for `deploy`, billed to
    /// `owner`, keyed by the build `seq`.
    pub fn meter_build(
        &self,
        deploy: &str,
        owner: &str,
        minutes: i64,
        seq: u64,
    ) -> Result<HostingReceipt, HostingError> {
        let amount = self.pricing.build_cost(minutes);
        self.charge(
            HostingResource::Build,
            deploy,
            owner,
            deploy,
            seq as i64,
            amount,
        )
    }

    /// Roll up + settle the **bandwidth** a site has served since its last roll-up.
    ///
    /// Reads the site's unbilled bytes from the shared [`BandwidthMeter`], settles
    /// one per-MiB charge `owner → provider`, and advances the billing cursor by
    /// exactly what was settled (no double-count). No unbilled bytes →
    /// [`BandwidthOutcome::NoTraffic`]; an owner that cannot pay → the site is
    /// **lapsed** ([`BandwidthOutcome::Lapsed`]) so the serving path stops serving it.
    #[tracing::instrument(skip(self), fields(site = %site, owner = %owner))]
    pub fn tick_bandwidth(
        &self,
        site: &str,
        owner: &str,
    ) -> Result<BandwidthOutcome, HostingError> {
        let bytes = self.bandwidth.unbilled(site);
        if bytes == 0 {
            return Ok(BandwidthOutcome::NoTraffic);
        }
        let amount = self.pricing.bandwidth_cost(bytes);
        let period = self.next_bw_period(site);

        // A free-tier roll-up (zero rate) bills nothing but still advances the cursor.
        if amount <= 0 {
            self.bandwidth.mark_billed(site, bytes);
            self.commit_bw_period(site, period);
            return Ok(BandwidthOutcome::Charged {
                period,
                bytes,
                units: 0,
            });
        }

        let lease_id = format!("host:{}:{}", HostingResource::Bandwidth.tag(), site);
        let charge = LeaseCharge::new(
            owner,
            &self.beneficiary,
            &self.asset,
            lease_id,
            period,
            amount,
        );
        match self.settlement.settle(&charge) {
            Ok(_) => {
                // Advance the cursor only by what settled — the exactly-once guard.
                self.bandwidth.mark_billed(site, bytes);
                self.commit_bw_period(site, period);
                tracing::info!(period, bytes, units = amount, "billed bandwidth roll-up");
                Ok(BandwidthOutcome::Charged {
                    period,
                    bytes,
                    units: amount,
                })
            }
            Err(SettleError::InsufficientFunds { .. }) => {
                self.bandwidth.lapse(site);
                tracing::warn!(
                    period,
                    bytes,
                    "owner exhausted — site lapsed, serving stops"
                );
                Ok(BandwidthOutcome::Lapsed {
                    reason: format!("owner `{owner}` spend account exhausted"),
                })
            }
            Err(e) => Err(HostingError::Settle(e)),
        }
    }

    /// Roll up bandwidth for **every** site with recorded traffic whose owner is
    /// resolvable — the control loop's per-period bandwidth sweep. Returns each site's
    /// outcome.
    ///
    /// **HB-3:** the payer is resolved per site via [`owner_of`](Self::owner_of) — the
    /// explicit `accounts` override, else the published [`SiteCell::owner`] from the
    /// wired registry. A served-but-never-manually-registered site is therefore billed
    /// (no free hosting), as long as a registry is wired; a site with no resolvable
    /// owner at all is skipped (nothing to bill it to).
    #[tracing::instrument(skip(self))]
    pub fn tick_all_bandwidth(&self) -> Result<Vec<(String, BandwidthOutcome)>, HostingError> {
        let mut out = Vec::new();
        for site in self.bandwidth.sites() {
            if let Some(owner) = self.owner_of(&site) {
                let outcome = self.tick_bandwidth(&site, &owner)?;
                out.push((site, outcome));
            }
        }
        tracing::info!(sites = out.len(), "bandwidth sweep complete");
        Ok(out)
    }

    /// The next (un-settled) bandwidth roll-up period for `site`.
    fn next_bw_period(&self, site: &str) -> i64 {
        self.bw_periods
            .lock()
            .expect("hosting meter poisoned")
            .get(site)
            .copied()
            .unwrap_or(0)
            + 1
    }

    /// Record that `period` is the last settled bandwidth roll-up for `site`.
    fn commit_bw_period(&self, site: &str, period: i64) {
        self.bw_periods
            .lock()
            .expect("hosting meter poisoned")
            .insert(site.to_string(), period);
    }
}

/// Ceil-divide (`0` denominator → `0`).
fn ceil_div(n: u64, d: u64) -> u64 {
    if d == 0 { 0 } else { n.div_ceil(d) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_durable::ConservingLedger;

    const DREGG: &str = "DREGG";

    fn meter(
        pricing: HostingPricing,
        bandwidth: Arc<BandwidthMeter>,
    ) -> (HostingMeter, Arc<ConservingLedger>) {
        let ledger = Arc::new(ConservingLedger::new());
        let m = HostingMeter::new(
            pricing,
            ledger.clone(),
            DREGG,
            "dreggnet-provider",
            bandwidth,
        );
        (m, ledger)
    }

    #[test]
    fn publish_cert_build_uptime_each_meter_and_settle_conserving() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, ledger) = meter(HostingPricing::default(), bw);
        ledger.fund(DREGG, "owner", 1_000);

        // publish: op 10 + ceil(2000/1024)=2 KiB × 1 = 12.
        let pr = m.meter_publish("blog", "owner", 2_000, 0).unwrap();
        assert_eq!(pr.units, 12);
        assert!(!pr.settle.replayed);
        // cert: 4.
        assert_eq!(
            m.meter_cert("blog.example.com", "owner", 0).unwrap().units,
            4
        );
        // build: 3/min × 5 = 15.
        assert_eq!(m.meter_build("deploy-1", "owner", 5, 0).unwrap().units, 15);
        // uptime: 2/period.
        assert_eq!(m.meter_uptime("blog", "owner", 1).unwrap().units, 2);

        // Every charge moved owner → provider, conserving (Σδ = 0).
        let total = 12 + 4 + 15 + 2;
        assert_eq!(ledger.balance(DREGG, "owner"), 1_000 - total);
        assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), total);
        assert_eq!(ledger.total_supply(DREGG), 1_000, "Σδ = 0");
    }

    #[test]
    fn re_metering_a_charge_is_exactly_once() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, ledger) = meter(HostingPricing::default(), bw);
        ledger.fund(DREGG, "owner", 1_000);

        let first = m.meter_publish("blog", "owner", 1, 7).unwrap();
        assert!(!first.settle.replayed);
        // Same (site, seq) → same (lease_id, period): replays, no second move.
        let again = m.meter_publish("blog", "owner", 1, 7).unwrap();
        assert!(again.settle.replayed);
        assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), first.units);
    }

    #[test]
    fn bandwidth_rolls_up_served_bytes_and_advances_the_cursor() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, ledger) = meter(HostingPricing::default(), bw.clone());
        ledger.fund(DREGG, "owner", 1_000);
        m.register_site("blog", "owner");

        // Serving recorded ~1.5 MiB of bandwidth.
        bw.record("blog", MIB + MIB / 2);
        match m.tick_bandwidth("blog", "owner").unwrap() {
            BandwidthOutcome::Charged {
                period,
                bytes,
                units,
            } => {
                assert_eq!(period, 1);
                assert_eq!(bytes, MIB + MIB / 2);
                assert_eq!(units, 2 * 5, "ceil(1.5 MiB) = 2 MiB × 5");
            }
            other => panic!("expected a charge, got {other:?}"),
        }
        // Cursor advanced: a second roll-up with no new bytes is NoTraffic.
        assert_eq!(
            m.tick_bandwidth("blog", "owner").unwrap(),
            BandwidthOutcome::NoTraffic
        );
        // More traffic → the next period.
        bw.record("blog", 100);
        match m.tick_bandwidth("blog", "owner").unwrap() {
            BandwidthOutcome::Charged { period, .. } => assert_eq!(period, 2),
            other => panic!("expected period 2, got {other:?}"),
        }
        assert_eq!(ledger.total_supply(DREGG), 1_000, "Σδ = 0 across roll-ups");
    }

    #[test]
    fn an_exhausted_owner_lapses_the_site() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, _ledger) = meter(HostingPricing::default(), bw.clone());
        // owner funded with nothing → cannot pay the bandwidth roll-up.
        m.register_site("blog", "owner");
        bw.record("blog", MIB);

        match m.tick_bandwidth("blog", "owner").unwrap() {
            BandwidthOutcome::Lapsed { .. } => {}
            other => panic!("expected a lapse, got {other:?}"),
        }
        assert!(bw.is_lapsed("blog"), "the site is lapsed → serving stops");
    }

    #[test]
    fn over_budget_publish_is_refused_before_commit() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, ledger) = meter(HostingPricing::default(), bw);
        ledger.fund(DREGG, "owner", 3); // < the 10-unit op cost.
        match m.meter_publish("blog", "owner", 0, 0) {
            Err(HostingError::OverBudget {
                resource: HostingResource::Publish,
                ..
            }) => {}
            other => panic!("expected an over-budget refusal, got {other:?}"),
        }
        // Nothing moved.
        assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), 0);
    }

    #[test]
    fn free_pricing_accrues_but_settles_nothing() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, ledger) = meter(HostingPricing::free(), bw.clone());
        m.register_site("blog", "owner");
        bw.record("blog", MIB);

        // A free publish + bandwidth roll-up: zero units, no settlement move.
        assert_eq!(m.meter_publish("blog", "owner", 9_999, 0).unwrap().units, 0);
        match m.tick_bandwidth("blog", "owner").unwrap() {
            BandwidthOutcome::Charged { units, .. } => assert_eq!(units, 0),
            other => panic!("expected a zero charge, got {other:?}"),
        }
        // The cursor still advanced (the bytes are billed at rate 0).
        assert_eq!(bw.unbilled("blog"), 0);
        assert_eq!(ledger.total_supply(DREGG), 0);
    }

    #[test]
    fn funding_an_in_band_bandwidth_budget_bounds_egress() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, _ledger) = meter(HostingPricing::default(), bw.clone());
        // 5 units/MiB; funding 15 units covers 3 MiB.
        assert_eq!(m.covered_bytes_for(15), 3 * MIB);
        m.fund_bandwidth_budget("blog", m.covered_bytes_for(15));
        assert_eq!(bw.budget("blog"), Some(3 * MIB));

        // The in-band gate is live on the shared meter: serving 3 MiB fits, the 4th
        // would exceed and is refused in-band (the serving path checks would_exceed).
        assert!(!bw.would_exceed_budget("blog", 3 * MIB));
        bw.record("blog", 3 * MIB);
        assert!(
            bw.would_exceed_budget("blog", 1),
            "served == budget ⇒ next byte refused"
        );

        // A top-up lifts the ceiling.
        m.top_up_bandwidth_budget("blog", MIB);
        assert!(!bw.would_exceed_budget("blog", MIB));
    }

    #[test]
    fn the_bandwidth_sweep_bills_every_registered_site() {
        let bw = Arc::new(BandwidthMeter::new());
        let (m, ledger) = meter(HostingPricing::default(), bw.clone());
        ledger.fund(DREGG, "alice", 100);
        ledger.fund(DREGG, "bob", 100);
        m.register_site("a", "alice");
        m.register_site("b", "bob");
        bw.record("a", MIB);
        bw.record("b", 2 * MIB);

        let outcomes = m.tick_all_bandwidth().unwrap();
        assert_eq!(outcomes.len(), 2);
        assert_eq!(ledger.balance(DREGG, "alice"), 100 - 5); // 1 MiB × 5
        assert_eq!(ledger.balance(DREGG, "bob"), 100 - 10); // 2 MiB × 5
        assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), 15);
    }

    // ---- HB-3 ----

    /// HB-3: a site that was published + served but NEVER manually `register_site`'d is
    /// billed off the wired published-site registry (payer = the published cell's
    /// owner), so served-but-unregistered is no longer free hosting.
    #[test]
    fn hb3_published_but_unregistered_site_is_billed_via_the_registry() {
        use dreggnet_webapp::{PublishCap, SiteContent};

        let bw = Arc::new(BandwidthMeter::new());
        let registry = Arc::new(SiteRegistry::new());
        // The owner publishes a site — but never calls `register_site` on the meter.
        registry
            .publish(
                &PublishCap::for_site("alice", "blog"),
                "blog",
                SiteContent::new().with("/index.html", "hi"),
            )
            .unwrap();

        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund(DREGG, "alice", 100);
        let m = HostingMeter::new(
            HostingPricing::default(),
            ledger.clone(),
            DREGG,
            "dreggnet-provider",
            bw.clone(),
        )
        .with_site_registry(registry.clone());

        // Traffic accrues on the published-but-unregistered site.
        bw.record("blog", MIB);

        // Pre-HB-3 this site was skipped (absent from `accounts`) → free. Now the
        // roll-up bills it, resolving the payer from the published `SiteCell.owner`.
        let outcomes = m.tick_all_bandwidth().unwrap();
        assert_eq!(
            outcomes.len(),
            1,
            "the unregistered-but-published site is billed"
        );
        assert_eq!(outcomes[0].0, "blog");
        assert_eq!(ledger.balance(DREGG, "alice"), 100 - 5); // 1 MiB × 5
        assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), 5);
    }

    /// HB-3: an explicit `accounts` entry OVERRIDES the registry-derived owner (e.g. a
    /// distinct beneficiary), and a served site with no resolvable owner at all (no
    /// registry entry, no override) is skipped — nothing to bill it to.
    #[test]
    fn hb3_accounts_override_wins_and_an_unowned_site_is_skipped() {
        use dreggnet_webapp::{PublishCap, SiteContent};

        let bw = Arc::new(BandwidthMeter::new());
        let registry = Arc::new(SiteRegistry::new());
        registry
            .publish(
                &PublishCap::for_site("alice", "blog"),
                "blog",
                SiteContent::new().with("/index.html", "hi"),
            )
            .unwrap();

        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund(DREGG, "carol", 100);
        let m = HostingMeter::new(
            HostingPricing::default(),
            ledger.clone(),
            DREGG,
            "dreggnet-provider",
            bw.clone(),
        )
        .with_site_registry(registry.clone());
        // Override the published owner with an explicit beneficiary.
        m.register_site("blog", "carol");

        // A second site has traffic but neither a registry entry nor an override.
        bw.record("blog", MIB);
        bw.record("ghost", MIB);

        let outcomes = m.tick_all_bandwidth().unwrap();
        assert_eq!(
            outcomes.len(),
            1,
            "only the owner-resolvable site is billed"
        );
        assert_eq!(outcomes[0].0, "blog");
        assert_eq!(
            ledger.balance(DREGG, "carol"),
            100 - 5,
            "the override payer is billed"
        );
        assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), 5);
    }
}
