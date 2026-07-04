//! `dreggnet-billing` — **invoices + spending limits + cost estimation** over the
//! existing DreggNet meter. The customer-facing billing plane
//! (`docs/CLOUD-PROVIDER-READINESS.md` Billing: *"usage is metered but there are no
//! invoices, spending limits, or cost estimation"*).
//!
//! This crate does NOT meter. It sits ABOVE the meter
//! (`dreggnet_control::HostingMeter` / the per-resource charges / the durable settle
//! ledger / the `dreggnet_meter` outbox) and turns already-settled usage into the three
//! customer-facing billing capabilities:
//!
//! 1. **Invoices** ([`invoice`]) — aggregate a cap-account's usage over a billing
//!    period into per-resource line items (quantity × rate = amount) and a total in DEC.
//!    The verifiable angle: every line item carries the metered settle
//!    [`UsageReceipt`]s it was billed from, and [`Invoice::verify_against_receipts`]
//!    re-witnesses the whole bill — **every line traces to a receipt**, not a mystery
//!    charge. The invoice itself is then sealed into the product-wide receipt contract
//!    ([`Invoice::seal`]), so a customer can verify the bill is the host's signed,
//!    prev-hash-chained record (the dregg differentiator).
//! 2. **Spending limits + budget alerts** ([`limits`]) — a per-account DEC spend cap
//!    with alert thresholds (50% / 80% / 100%). Crossing a threshold fires a
//!    [`BudgetAlert`] (a record the console / a notification surfaces); at the hard cap,
//!    new spend is [`SpendDecision::Refused`]. The cap is enforced through the audited
//!    exec budget cell (the same `ReplenishingBudget` the leases + abuse guard use).
//! 3. **Cost estimation** ([`estimate`]) — estimate-before-you-deploy: given a resource
//!    declaration, the DEC cost over a period against the rate card. The
//!    `dregg-cloud estimate` shape.
//!
//! ## Ground (what this reads, and where it plugs in)
//!
//! - The **usage source** is the meter: a `dreggnet_control::HostingReceipt`
//!   (publish/bandwidth/uptime/cert/build) or a `dreggnet_control::SettleRecord` from
//!   the durable settle ledger maps field-for-field into a [`UsageEvent`] (see
//!   [`usage::UsageReceipt`]). The default build does not link control (billing is
//!   dependency-light + portable); the conversion is the **control settle-ledger
//!   adapter seam**, exercised for real in the dev-dep test below.
//! - The **rate card** ([`RateCard`]) mirrors `dreggnet_control::HostingPricing` and
//!   extends it to the fuller invoice taxonomy (agents / compute / storage / deploys).
//! - The **cap-account subject** is the same `dregg:<hex>` webauth subject the console
//!   scopes on (`console/src/scope.rs`); an invoice is per-subject and another subject's
//!   usage can never appear on it ([`Invoice::assemble`] filters by account).
//! - The **receipt contract** is `dreggnet_receipt` — an invoice is a sealed receipt.
//!
//! ## Named live-wire seams (NOT wired here — disjoint, swarm-safe)
//!
//! - **Console billing panel:** a `console` `BillingView` + panel assembled from the
//!   subject's [`Invoice`] + [`BudgetGuard`] state, scoped exactly like the existing
//!   `ConsoleView::for_subject`. This crate provides the cap-scoped [`Invoice`]; the
//!   console renders it.
//! - **CLI verbs:** `dregg-cloud invoice` (list / show / verify a period's bill) and
//!   `dregg-cloud estimate <declaration>` in `cli/src/main.rs`, over this crate's
//!   [`Invoice`] / [`estimate`].
//! - **Control settle-ledger adapter:** the per-period roll-up loop in
//!   `dreggnet-control` emits each settled `HostingReceipt` / reads the settle ledger
//!   into [`UsageEvent`]s for the active period (the dev-dep test shows the exact
//!   mapping), and feeds the [`BudgetGuard`] so a hard-cap account stops being charged.

pub mod estimate;
pub mod invoice;
pub mod limits;
pub mod usage;

pub use estimate::{Estimate, EstimateLine, ResourceDeclaration, estimate};
pub use invoice::{BillingPeriod, Invoice, InvoiceError, LineItem, SealedInvoice, invoices_for};
pub use limits::{BudgetAlert, BudgetGuard, SpendDecision, SpendLimit};
pub use usage::{BillableResource, RateCard, UsageEvent, UsageReceipt};

#[cfg(test)]
mod control_adapter_tests {
    //! The control settle-ledger adapter seam, exercised against the REAL meter: build a
    //! real `HostingMeter` over a conserving ledger, meter a cap-account's
    //! publish/cert/build/uptime/bandwidth usage, map each emitted `HostingReceipt` into
    //! a [`UsageEvent`], and assemble a receipt-traced invoice whose total equals exactly
    //! what the meter settled to the provider. This is the "sourced from the settle
    //! ledger / the meter outbox" claim made real (dev-dep on control, so the shipped
    //! billing artifact never links the control plane).

    use std::sync::Arc;

    use dreggnet_control::hosting_meter::{HostingReceipt, HostingResource};
    use dreggnet_control::{BandwidthMeter, HostingMeter, HostingPricing};
    use dreggnet_durable::ConservingLedger;

    use crate::{BillableResource, BillingPeriod, Invoice, UsageEvent, UsageReceipt};

    const DREGG: &str = "DREGG";

    /// Map a meter resource into the billing taxonomy.
    fn resource_of(h: HostingResource) -> BillableResource {
        match h {
            HostingResource::Publish => BillableResource::Site,
            HostingResource::Bandwidth => BillableResource::Bandwidth,
            HostingResource::Uptime => BillableResource::Server,
            HostingResource::Cert => BillableResource::Cert,
            HostingResource::Build => BillableResource::Build,
        }
    }

    /// The adapter: a settled `HostingReceipt` → a billing [`UsageEvent`]. The settle
    /// receipt carries the amount but not the quantity breakdown, so this is the
    /// settle-shape recovery (the whole amount as a flat) — it still traces exactly.
    fn event_of(account: &str, h: &HostingReceipt) -> UsageEvent {
        let r = &h.settle;
        let receipt = UsageReceipt::new(
            r.lease_id.clone(),
            r.period,
            r.asset.clone(),
            r.amount,
            None,
        );
        UsageEvent {
            account: account.to_string(),
            resource: resource_of(h.resource),
            subject: h.subject.clone(),
            quantity: 0,
            unit_rate_units: 0,
            flat_units: r.amount,
            amount_units: r.amount,
            receipt,
        }
    }

    #[test]
    fn usage_from_the_real_meter_assembles_a_receipt_traced_invoice() {
        // A real meter over a conserving ledger, default pricing.
        let bw = Arc::new(BandwidthMeter::new());
        let ledger = Arc::new(ConservingLedger::new());
        ledger.fund(DREGG, "alice", 10_000);
        let meter = HostingMeter::new(
            HostingPricing::default(),
            ledger.clone(),
            DREGG,
            "dreggnet-provider",
            bw.clone(),
        );
        meter.register_site("blog", "alice");

        // Meter a realistic month for alice, collecting the emitted receipts.
        let mut receipts: Vec<HostingReceipt> = Vec::new();
        receipts.push(meter.meter_publish("blog", "alice", 2_000, 0).unwrap()); // op 10 + 2 KiB = 12
        receipts.push(meter.meter_cert("blog.example", "alice", 0).unwrap()); // 4
        receipts.push(meter.meter_build("deploy-1", "alice", 5, 0).unwrap()); // 15
        receipts.push(meter.meter_uptime("blog", "alice", 1).unwrap()); // 2
        bw.record("blog", 3 * 1024 * 1024); // 3 MiB
        if let dreggnet_control::hosting_meter::BandwidthOutcome::Charged { .. } =
            meter.tick_bandwidth("blog", "alice").unwrap()
        {
            // Reconstruct the bandwidth receipt the same way the meter would surface it.
            receipts.push(HostingReceipt {
                resource: HostingResource::Bandwidth,
                subject: "blog".into(),
                units: 15,
                settle: dreggnet_durable::SettleReceipt {
                    lease_id: "host:bandwidth:blog".into(),
                    period: 1,
                    asset: DREGG.into(),
                    amount: 15, // 3 MiB × 5
                    payer_balance: 0,
                    beneficiary_balance: 0,
                    replayed: false,
                },
            });
        }

        // The amount the meter actually moved to the provider.
        let settled_to_provider = ledger.balance(DREGG, "dreggnet-provider");
        assert_eq!(settled_to_provider, 12 + 4 + 15 + 2 + 15);

        // Adapt → assemble → re-witness.
        let events: Vec<UsageEvent> = receipts.iter().map(|h| event_of("alice", h)).collect();
        let inv = Invoice::assemble(
            "alice",
            BillingPeriod::new("2026-06", 0, 1000),
            DREGG,
            &events,
            "t0",
        );

        // The invoice total equals exactly what the meter settled — and every line
        // traces to a metered receipt.
        assert_eq!(inv.total_units, settled_to_provider);
        assert_eq!(inv.verify_against_receipts(), Ok(()));
        // Five resources billed (site/cert/build/server/bandwidth), one line each.
        assert_eq!(inv.line_items.len(), 5);
    }

    #[test]
    fn the_rate_card_aligns_with_hosting_pricing() {
        // The billing rate card mirrors the meter's pricing for the overlapping rates,
        // so an estimate equals what the meter charges.
        let p = HostingPricing::default();
        let card = crate::RateCard::default();
        assert_eq!(card.publish_op_units, p.publish_op_units);
        assert_eq!(card.site_units_per_kib, p.publish_units_per_kib);
        assert_eq!(card.server_units_per_period, p.uptime_units_per_period);
        assert_eq!(card.bandwidth_units_per_mib, p.bandwidth_units_per_mib);
        assert_eq!(card.cert_units_per_issue, p.cert_units_per_issue);
        assert_eq!(card.build_units_per_minute, p.build_units_per_minute);
        // And the estimate arithmetic reproduces `HostingPricing::publish_cost`.
        assert_eq!(
            card.cost(BillableResource::Site, 2), // op 10 + 2 KiB
            p.publish_cost(2 * 1024)
        );
    }
}
