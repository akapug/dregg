//! The billing **source layer**: the per-resource rate card, the billable-resource
//! taxonomy, and the normalized [`UsageEvent`] (one metered, settled charge with the
//! [`UsageReceipt`] it traces back to).
//!
//! ## Where the usage comes from (the meter, not a new counter)
//!
//! Billing does not meter. Every [`UsageEvent`] is a VIEW of a charge the meter
//! already settled: a `dreggnet_control::HostingReceipt` (publish / bandwidth /
//! uptime / cert / build) or a `dreggnet_control::SettleRecord` read back from the
//! durable settle ledger / the `dreggnet_meter` outbox. The mapping is field-for-field
//! (see [`UsageReceipt`]); the named control adapter (lib.rs) performs it, and the
//! dev-dep test in `invoice.rs` exercises it against the real `HostingMeter`.

use serde::{Deserialize, Serialize};

/// A billable cloud resource — the line-item taxonomy an invoice groups usage by.
///
/// The first five mirror the meter's `dreggnet_control::HostingResource`
/// (publish→[`Site`](BillableResource::Site), uptime→[`Server`](BillableResource::Server),
/// bandwidth/cert/build); the rest extend it to the fuller invoice surface the console
/// shows (agents / durable compute / object storage / deploys). Declaration order is
/// the canonical line-item sort order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BillableResource {
    /// A published static site: the publish op + per-KiB stored bytes.
    Site,
    /// A persistent server's per-wall-clock-period uptime.
    Server,
    /// An agent run's metered calls/steps.
    Agent,
    /// Bytes served out, billed per MiB.
    Bandwidth,
    /// A durable execution-lease's metered compute steps.
    Compute,
    /// Object-storage bytes held, billed per GiB-period.
    Storage,
    /// A TLS certificate issuance/renewal.
    Cert,
    /// A deploy build, billed per build-minute.
    Build,
    /// A deploy operation (flat).
    Deploy,
}

impl BillableResource {
    /// The canonical billing tag (the line-item label + the invoice field key).
    pub fn tag(self) -> &'static str {
        match self {
            BillableResource::Site => "site",
            BillableResource::Server => "server",
            BillableResource::Agent => "agent",
            BillableResource::Bandwidth => "bandwidth",
            BillableResource::Compute => "compute",
            BillableResource::Storage => "storage",
            BillableResource::Cert => "cert",
            BillableResource::Build => "build",
            BillableResource::Deploy => "deploy",
        }
    }

    /// Decode a resource from a tag, accepting BOTH billing's canonical tags and the
    /// meter's `HostingResource` tags (`publish`→[`Site`](BillableResource::Site),
    /// `uptime`→[`Server`](BillableResource::Server)). An unknown tag is `None`.
    pub fn from_tag(tag: &str) -> Option<BillableResource> {
        Some(match tag {
            "site" | "publish" => BillableResource::Site,
            "server" | "uptime" => BillableResource::Server,
            "agent" => BillableResource::Agent,
            "bandwidth" => BillableResource::Bandwidth,
            "compute" => BillableResource::Compute,
            "storage" => BillableResource::Storage,
            "cert" => BillableResource::Cert,
            "build" => BillableResource::Build,
            "deploy" => BillableResource::Deploy,
            _ => return None,
        })
    }

    /// Decode the resource from a meter lease id. The hosting meter keys every charge
    /// `host:<tag>:<key>` (`dreggnet_control::hosting_meter`); a bare `<tag>` or
    /// `<tag>:<key>` is also accepted. Returns `None` for an unrecognized tag.
    pub fn from_lease_id(lease_id: &str) -> Option<BillableResource> {
        let (tag, _key) = split_lease_id(lease_id);
        BillableResource::from_tag(tag)
    }
}

/// Split a meter lease id into `(tag, key)`. `host:bandwidth:blog` → `("bandwidth",
/// "blog")`; `bandwidth:blog` → `("bandwidth", "blog")`; `bandwidth` → `("bandwidth",
/// "")`.
pub fn split_lease_id(lease_id: &str) -> (&str, &str) {
    let mut parts = lease_id.splitn(3, ':');
    let first = parts.next().unwrap_or("");
    if first == "host" {
        let tag = parts.next().unwrap_or("");
        let key = parts.next().unwrap_or("");
        (tag, key)
    } else {
        let key = parts.next().unwrap_or("");
        (first, key)
    }
}

/// The per-resource price list, in `$DREGG` meter units (DEC). The single rate card
/// estimation costs against and an invoice line item's `unit_rate_units` is read from.
///
/// Mirrors `dreggnet_control::HostingPricing` for the overlapping resources
/// (`publish_op_units`, `publish_units_per_kib`→[`site_units_per_kib`](RateCard::site_units_per_kib),
/// `bandwidth_units_per_mib`, `uptime_units_per_period`→[`server_units_per_period`](RateCard::server_units_per_period),
/// `cert_units_per_issue`, `build_units_per_minute`) and extends it with the
/// agent/compute/storage/deploy rates the fuller invoice taxonomy needs. The
/// alignment is asserted in the dev-dep test (`estimate.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct RateCard {
    /// Flat cost per publish op (the [`Site`](BillableResource::Site) flat).
    pub publish_op_units: i64,
    /// Cost per KiB (rounded up) of stored site bytes.
    pub site_units_per_kib: i64,
    /// Cost per server uptime period.
    pub server_units_per_period: i64,
    /// Cost per agent call/step.
    pub agent_units_per_call: i64,
    /// Cost per MiB (rounded up) of bytes served.
    pub bandwidth_units_per_mib: i64,
    /// Cost per durable-compute step.
    pub compute_units_per_step: i64,
    /// Cost per GiB-period of object storage held.
    pub storage_units_per_gib: i64,
    /// Cost per issued/renewed cert.
    pub cert_units_per_issue: i64,
    /// Cost per deploy build-minute.
    pub build_units_per_minute: i64,
    /// Flat cost per deploy op (the [`Deploy`](BillableResource::Deploy) flat).
    pub deploy_op_units: i64,
}

impl Default for RateCard {
    /// A sensible default. The overlapping rates match
    /// `dreggnet_control::HostingPricing::default()` exactly.
    fn default() -> RateCard {
        RateCard {
            publish_op_units: 10,
            site_units_per_kib: 1,
            server_units_per_period: 2,
            agent_units_per_call: 1,
            bandwidth_units_per_mib: 5,
            compute_units_per_step: 1,
            storage_units_per_gib: 3,
            cert_units_per_issue: 4,
            build_units_per_minute: 3,
            deploy_op_units: 6,
        }
    }
}

impl RateCard {
    /// A free price list (every resource costs zero) — the subsidized early era.
    pub fn free() -> RateCard {
        RateCard {
            publish_op_units: 0,
            site_units_per_kib: 0,
            server_units_per_period: 0,
            agent_units_per_call: 0,
            bandwidth_units_per_mib: 0,
            compute_units_per_step: 0,
            storage_units_per_gib: 0,
            cert_units_per_issue: 0,
            build_units_per_minute: 0,
            deploy_op_units: 0,
        }
    }

    /// The per-unit (per-quantity) rate for `resource`. For a [`Site`](BillableResource::Site)
    /// this is the per-KiB storage rate (the op cost is the [`flat_for`](RateCard::flat_for)).
    pub fn unit_rate_for(&self, resource: BillableResource) -> i64 {
        match resource {
            BillableResource::Site => self.site_units_per_kib,
            BillableResource::Server => self.server_units_per_period,
            BillableResource::Agent => self.agent_units_per_call,
            BillableResource::Bandwidth => self.bandwidth_units_per_mib,
            BillableResource::Compute => self.compute_units_per_step,
            BillableResource::Storage => self.storage_units_per_gib,
            BillableResource::Cert => self.cert_units_per_issue,
            BillableResource::Build => self.build_units_per_minute,
            BillableResource::Deploy => 0,
        }
    }

    /// The flat (per-op, quantity-independent) cost for `resource`: the publish op for
    /// a [`Site`](BillableResource::Site), the deploy op for a [`Deploy`](BillableResource::Deploy),
    /// else `0`.
    pub fn flat_for(&self, resource: BillableResource) -> i64 {
        match resource {
            BillableResource::Site => self.publish_op_units,
            BillableResource::Deploy => self.deploy_op_units,
            _ => 0,
        }
    }

    /// The DEC cost of `quantity` of `resource` at this rate card: `quantity ×
    /// unit_rate + flat`. The exact arithmetic estimation and a line item both use.
    pub fn cost(&self, resource: BillableResource, quantity: u64) -> i64 {
        (quantity as i64)
            .saturating_mul(self.unit_rate_for(resource))
            .saturating_add(self.flat_for(resource))
    }
}

/// The metered, settled charge a [`UsageEvent`] traces back to — the receipt anchor
/// that makes the invoice verifiable.
///
/// Structurally mirrors `dreggnet_control::SettleRecord` / `dreggnet_durable::SettleReceipt`:
/// the `(lease_id, period)` exactly-once key, the `asset` + `amount` moved owner →
/// provider, and the on-chain settling `turn_hash` once the durable ledger confirmed
/// it (`None` for an in-process conserving-ledger settlement that carries no on-chain
/// hash). "Every invoice line traces to one of these" is the verifiable-bill tooth.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UsageReceipt {
    /// The meter lease id, `host:<resource>:<key>` (the resource + the billed subject).
    pub lease_id: String,
    /// The period ordinal within the lease (the other half of the exactly-once key).
    pub period: i64,
    /// The asset the charge was denominated in (the `$DREGG` token id).
    pub asset: String,
    /// The DEC moved owner → provider for this charge.
    pub amount: i64,
    /// The on-chain settling turn hash, once the durable ledger confirmed it.
    #[serde(default)]
    pub turn_hash: Option<String>,
}

impl UsageReceipt {
    /// A receipt anchor.
    pub fn new(
        lease_id: impl Into<String>,
        period: i64,
        asset: impl Into<String>,
        amount: i64,
        turn_hash: Option<String>,
    ) -> UsageReceipt {
        UsageReceipt {
            lease_id: lease_id.into(),
            period,
            asset: asset.into(),
            amount,
            turn_hash,
        }
    }
}

/// One normalized usage event: a metered, settled charge attributed to a cap-account,
/// carrying the [`UsageReceipt`] it traces back to and the quantity × rate breakdown.
///
/// `amount_units == quantity × unit_rate_units + flat_units` and (for a well-formed
/// event sourced from a real charge) `amount_units == receipt.amount`. The settle-ledger
/// recovery path ([`from_settle`](UsageEvent::from_settle)) carries the amount without
/// the quantity breakdown (the durable record stores only the amount), so it sets
/// `quantity = 0`, `unit_rate = 0`, `flat = amount` — the line still traces to the
/// receipt and totals exactly, it just lacks the human-readable unit breakdown.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UsageEvent {
    /// The cap-account subject the charge is billed to (the payer / owner).
    pub account: String,
    /// Which resource was billed.
    pub resource: BillableResource,
    /// The specific resource billed (site / server / domain / deploy id).
    pub subject: String,
    /// The metered quantity, in the resource's natural unit (KiB / MiB / periods / …).
    pub quantity: u64,
    /// The per-unit DEC rate applied.
    pub unit_rate_units: i64,
    /// A flat per-op DEC cost (e.g. the publish op cost); `0` for most resources.
    pub flat_units: i64,
    /// The DEC charged: `quantity × unit_rate + flat`.
    pub amount_units: i64,
    /// The metered settle receipt this event traces back to.
    pub receipt: UsageReceipt,
}

impl UsageEvent {
    /// A metered usage event with the full quantity × rate breakdown. `amount_units`
    /// is computed `quantity × unit_rate + flat`; a well-formed `receipt.amount` equals
    /// it (asserted by [`is_consistent`](UsageEvent::is_consistent) and the invoice
    /// receipt-trace check).
    pub fn metered(
        account: impl Into<String>,
        resource: BillableResource,
        subject: impl Into<String>,
        quantity: u64,
        unit_rate_units: i64,
        flat_units: i64,
        receipt: UsageReceipt,
    ) -> UsageEvent {
        let amount_units = (quantity as i64)
            .saturating_mul(unit_rate_units)
            .saturating_add(flat_units);
        UsageEvent {
            account: account.into(),
            resource,
            subject: subject.into(),
            quantity,
            unit_rate_units,
            flat_units,
            amount_units,
            receipt,
        }
    }

    /// A usage event recovered from a settle receipt alone (the durable-ledger / meter-
    /// outbox path): the resource is decoded from `receipt.lease_id`, the amount is the
    /// receipt's, and the whole amount is carried as a flat (no quantity breakdown).
    /// Returns `None` if the lease id's tag is not a recognized resource.
    pub fn from_settle(account: impl Into<String>, receipt: UsageReceipt) -> Option<UsageEvent> {
        let (tag, key) = split_lease_id(&receipt.lease_id);
        let resource = BillableResource::from_tag(tag)?;
        let subject = if key.is_empty() {
            receipt.lease_id.clone()
        } else {
            key.to_string()
        };
        let amount_units = receipt.amount;
        Some(UsageEvent {
            account: account.into(),
            resource,
            subject,
            quantity: 0,
            unit_rate_units: 0,
            flat_units: amount_units,
            amount_units,
            receipt,
        })
    }

    /// Whether the event's breakdown is internally consistent: the computed
    /// `quantity × unit_rate + flat` equals both `amount_units` and the anchored
    /// `receipt.amount`. A forged event (an amount that does not match its receipt or
    /// its own breakdown) fails this and the invoice receipt-trace check.
    pub fn is_consistent(&self) -> bool {
        let computed = (self.quantity as i64)
            .saturating_mul(self.unit_rate_units)
            .saturating_add(self.flat_units);
        computed == self.amount_units && self.amount_units == self.receipt.amount
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lease_id_decodes_resource_and_key() {
        assert_eq!(split_lease_id("host:bandwidth:blog"), ("bandwidth", "blog"));
        assert_eq!(split_lease_id("publish:site"), ("publish", "site"));
        assert_eq!(split_lease_id("cert"), ("cert", ""));
        assert_eq!(
            BillableResource::from_lease_id("host:publish:blog"),
            Some(BillableResource::Site)
        );
        assert_eq!(
            BillableResource::from_lease_id("host:uptime:srv"),
            Some(BillableResource::Server)
        );
        assert_eq!(BillableResource::from_lease_id("host:nonsense:x"), None);
    }

    #[test]
    fn rate_card_cost_is_quantity_times_rate_plus_flat() {
        let card = RateCard::default();
        // a site of 4 KiB: op 10 + 4 × 1 = 14.
        assert_eq!(card.cost(BillableResource::Site, 4), 14);
        // bandwidth of 3 MiB: 3 × 5 = 15.
        assert_eq!(card.cost(BillableResource::Bandwidth, 3), 15);
        // a deploy: flat 6, quantity-independent.
        assert_eq!(card.cost(BillableResource::Deploy, 0), 6);
        // free card: everything 0.
        assert_eq!(RateCard::free().cost(BillableResource::Site, 9_999), 0);
    }

    #[test]
    fn a_metered_event_is_consistent_with_its_receipt() {
        let r = UsageReceipt::new("host:bandwidth:blog", 1, "DREGG", 15, None);
        let e = UsageEvent::metered("acct", BillableResource::Bandwidth, "blog", 3, 5, 0, r);
        assert_eq!(e.amount_units, 15);
        assert!(e.is_consistent());
    }

    #[test]
    fn a_tampered_receipt_amount_breaks_consistency() {
        // The receipt says 99 but the breakdown computes 15 — a forged line.
        let r = UsageReceipt::new("host:bandwidth:blog", 1, "DREGG", 99, None);
        let e = UsageEvent::metered("acct", BillableResource::Bandwidth, "blog", 3, 5, 0, r);
        assert!(!e.is_consistent());
    }

    #[test]
    fn settle_recovery_decodes_resource_and_totals() {
        let r = UsageReceipt::new("host:cert:blog.example", 0, "DREGG", 4, Some("h1".into()));
        let e = UsageEvent::from_settle("acct", r).unwrap();
        assert_eq!(e.resource, BillableResource::Cert);
        assert_eq!(e.subject, "blog.example");
        assert_eq!(e.amount_units, 4);
        assert!(e.is_consistent(), "flat == amount == receipt.amount");
        // an unrecognized tag yields no event.
        let bad = UsageReceipt::new("host:mystery:x", 0, "DREGG", 4, None);
        assert!(UsageEvent::from_settle("acct", bad).is_none());
    }
}
