//! **Cost estimation**: estimate-before-you-deploy. Given a resource declaration (a
//! site / server / agent + its expected usage over a period), compute the DEC cost
//! against the rate card — the `dregg-cloud estimate` shape, so a user sees the bill
//! before committing the spend.
//!
//! The estimate uses the SAME arithmetic the meter bills on
//! ([`RateCard::cost`](crate::RateCard::cost) = `quantity × unit_rate + flat`), so an
//! estimate of N KiB of site storage equals exactly what a publish of N KiB is charged
//! — the estimate matches the rate card (and, asserted in the dev-dep test, the real
//! `dreggnet_control::HostingPricing`).

use crate::usage::{BillableResource, RateCard};

/// A declared resource + its expected usage over the estimate's period — the input a
/// user supplies before deploying.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceDeclaration {
    /// Which resource is being declared.
    pub resource: BillableResource,
    /// The expected quantity over the period, in the resource's natural unit (KiB of
    /// stored bytes for a site, MiB for bandwidth, uptime periods for a server, …).
    pub quantity: u64,
}

impl ResourceDeclaration {
    /// Declare `quantity` of `resource`.
    pub fn new(resource: BillableResource, quantity: u64) -> ResourceDeclaration {
        ResourceDeclaration { resource, quantity }
    }
}

/// One estimated line: the resource, the declared quantity, the rate applied, and the
/// DEC it would cost. The estimate twin of an invoice [`LineItem`](crate::LineItem) —
/// same arithmetic, no receipts (nothing has been metered yet).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EstimateLine {
    pub resource: BillableResource,
    pub quantity: u64,
    pub unit_rate_units: i64,
    pub flat_units: i64,
    pub amount_units: i64,
}

/// A cost estimate over a set of declared resources.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Estimate {
    /// The period label the estimate is for (e.g. `"per month"`).
    pub period_label: String,
    /// The per-resource estimated lines.
    pub lines: Vec<EstimateLine>,
    /// The estimated total in DEC: `Σ` of every line.
    pub total_units: i64,
}

/// Estimate the DEC cost of `declarations` over `period_label` against `card`. Each
/// declaration is costed `quantity × unit_rate + flat` — the exact meter arithmetic —
/// and the total is the sum.
pub fn estimate(
    declarations: &[ResourceDeclaration],
    card: &RateCard,
    period_label: impl Into<String>,
) -> Estimate {
    let lines: Vec<EstimateLine> = declarations
        .iter()
        .map(|d| EstimateLine {
            resource: d.resource,
            quantity: d.quantity,
            unit_rate_units: card.unit_rate_for(d.resource),
            flat_units: card.flat_for(d.resource),
            amount_units: card.cost(d.resource, d.quantity),
        })
        .collect();
    let total_units = lines.iter().map(|l| l.amount_units).sum();
    Estimate {
        period_label: period_label.into(),
        lines,
        total_units,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── TOOTH: an estimate matches the rate card, line by line + total ──
    #[test]
    fn an_estimate_matches_the_rate_card() {
        let card = RateCard::default();
        let decls = vec![
            // a 100-KiB site: op 10 + 100 × 1 = 110.
            ResourceDeclaration::new(BillableResource::Site, 100),
            // 50 MiB bandwidth: 50 × 5 = 250.
            ResourceDeclaration::new(BillableResource::Bandwidth, 50),
            // 30 uptime periods: 30 × 2 = 60.
            ResourceDeclaration::new(BillableResource::Server, 30),
            // 10 agent calls: 10 × 1 = 10.
            ResourceDeclaration::new(BillableResource::Agent, 10),
        ];
        let est = estimate(&decls, &card, "per month");

        assert_eq!(est.lines.len(), 4);
        assert_eq!(est.lines[0].amount_units, 110);
        assert_eq!(
            est.lines[0].flat_units, 10,
            "the publish op is the site flat"
        );
        assert_eq!(est.lines[1].amount_units, 250);
        assert_eq!(est.lines[2].amount_units, 60);
        assert_eq!(est.lines[3].amount_units, 10);

        // The total is the sum, and each line equals `card.cost` exactly.
        assert_eq!(est.total_units, 110 + 250 + 60 + 10);
        for l in &est.lines {
            assert_eq!(l.amount_units, card.cost(l.resource, l.quantity));
        }
    }

    #[test]
    fn the_free_card_estimates_zero() {
        let est = estimate(
            &[ResourceDeclaration::new(BillableResource::Site, 9_999)],
            &RateCard::free(),
            "free era",
        );
        assert_eq!(est.total_units, 0);
    }
}
