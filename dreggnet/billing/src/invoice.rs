//! The **invoice**: a cap-account's metered usage over a billing period, aggregated
//! into per-resource line items (quantity × rate = amount) — and made VERIFIABLE.
//!
//! ## The verifiable bill (the differentiator)
//!
//! A DreggNet invoice is not a mystery charge. It is verifiable at two layers:
//!
//! 1. **Line-level receipt trace.** Every line item carries the
//!    [`UsageReceipt`](crate::UsageReceipt)s it was aggregated from, and
//!    [`Invoice::verify_against_receipts`] re-witnesses the bill: each line's amount is
//!    exactly the sum of its receipts' settled amounts, each line's `quantity × rate +
//!    flat` reproduces that amount, and the invoice total is exactly the sum of every
//!    receipt. A single padded line or inflated total fails the check. "Every line
//!    traces to a receipt."
//! 2. **Document-level seal.** [`Invoice::seal`] lifts the whole invoice into the
//!    product-wide receipt contract (`dreggnet_receipt`): a prev-hash-chained,
//!    ed25519-signed record the customer can re-witness without trusting the host, and
//!    a producer's monthly invoice stream is tamper-evident end to end
//!    ([`dreggnet_receipt::verify_chain`]).
//!
//! ## Cap-scoping (per-account)
//!
//! [`Invoice::assemble`] keeps only the events whose `account` matches the invoice
//! subject — another account's usage can never appear on this bill, the same one-rule
//! cap-scoping the console enforces (`console/src/scope.rs`). [`invoices_for`] fans a
//! pooled event set out into one disjoint invoice per account.

use std::collections::BTreeMap;

use dreggnet_receipt::{BodyHasher, ReceiptAttestation, ReceiptBody, ReceiptChain};
use serde::{Deserialize, Serialize};

use crate::usage::{BillableResource, UsageEvent, UsageReceipt};

/// The window an invoice bills. `label` is the human period (e.g. `"2026-06"`); `start`
/// (inclusive) and `end` (exclusive) bound it on whatever clock the meter periods ride
/// (a block height / epoch / unix second).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BillingPeriod {
    pub label: String,
    pub start: i64,
    pub end: i64,
}

impl BillingPeriod {
    /// A billing period `[start, end)` labelled `label`.
    pub fn new(label: impl Into<String>, start: i64, end: i64) -> BillingPeriod {
        BillingPeriod {
            label: label.into(),
            start,
            end,
        }
    }
}

/// One per-resource line on an invoice: the aggregated quantity, the rate applied, the
/// DEC amount, and the metered receipts the amount traces back to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineItem {
    /// Which resource this line bills.
    pub resource: BillableResource,
    /// The total metered quantity across the line's charges (the resource's natural unit).
    pub quantity: u64,
    /// The per-unit DEC rate applied (the rate-card rate; `0` if the line was recovered
    /// from settle receipts without a quantity breakdown).
    pub unit_rate_units: i64,
    /// The total flat DEC component across the line's charges (publish/deploy ops).
    pub flat_units: i64,
    /// The DEC subtotal for this resource: `Σ` of the line's receipts.
    pub amount_units: i64,
    /// Every metered settle receipt aggregated into this line — the trace anchors.
    pub receipts: Vec<UsageReceipt>,
}

/// A per-account invoice over a billing period.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Invoice {
    /// The cap-account subject this invoice bills.
    pub account: String,
    /// The period billed.
    pub period: BillingPeriod,
    /// The asset the invoice is denominated in (the `$DREGG` token id / DEC).
    pub asset: String,
    /// The per-resource line items, sorted by resource.
    pub line_items: Vec<LineItem>,
    /// The invoice total in DEC: `Σ` of every line.
    pub total_units: i64,
    /// When the invoice was assembled (RFC3339; the caller's clock).
    pub generated_at: String,
}

/// Why an invoice failed to verify against its receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvoiceError {
    /// A line's `amount_units` did not equal the sum of its receipts' amounts — the
    /// line does not trace to its receipts (a padded or unbacked charge).
    LineDoesNotTrace {
        resource: BillableResource,
        line_amount: i64,
        receipts_sum: i64,
    },
    /// A line's `quantity × unit_rate + flat` did not reproduce its `amount_units` —
    /// the quantity breakdown is inconsistent with the charged amount.
    LineMathMismatch {
        resource: BillableResource,
        computed: i64,
        line_amount: i64,
    },
    /// The invoice `total_units` did not equal the sum of its line amounts.
    TotalMismatch { total: i64, lines_sum: i64 },
    /// A line carried a receipt billed to a different asset than the invoice.
    AssetMismatch {
        resource: BillableResource,
        expected: String,
        found: String,
    },
}

impl std::fmt::Display for InvoiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvoiceError::LineDoesNotTrace {
                resource,
                line_amount,
                receipts_sum,
            } => write!(
                f,
                "line `{}` amount {line_amount} != Σ receipts {receipts_sum} (does not trace)",
                resource.tag()
            ),
            InvoiceError::LineMathMismatch {
                resource,
                computed,
                line_amount,
            } => write!(
                f,
                "line `{}` quantity×rate+flat = {computed} != amount {line_amount}",
                resource.tag()
            ),
            InvoiceError::TotalMismatch { total, lines_sum } => {
                write!(f, "invoice total {total} != Σ lines {lines_sum}")
            }
            InvoiceError::AssetMismatch {
                resource,
                expected,
                found,
            } => write!(
                f,
                "line `{}` receipt asset `{found}` != invoice asset `{expected}`",
                resource.tag()
            ),
        }
    }
}

impl std::error::Error for InvoiceError {}

impl Invoice {
    /// Assemble the invoice for `account` over `period` from a pool of usage events,
    /// in `asset`. Only the events billed to `account` are aggregated (the cap-scoping
    /// tooth — another account's usage cannot appear); within the account, events are
    /// grouped by resource into line items sorted by resource, and the total is the sum
    /// of every line.
    pub fn assemble(
        account: &str,
        period: BillingPeriod,
        asset: impl Into<String>,
        events: &[UsageEvent],
        generated_at: impl Into<String>,
    ) -> Invoice {
        let mut by_resource: BTreeMap<BillableResource, LineItem> = BTreeMap::new();
        for e in events.iter().filter(|e| e.account == account) {
            let line = by_resource.entry(e.resource).or_insert_with(|| LineItem {
                resource: e.resource,
                quantity: 0,
                unit_rate_units: e.unit_rate_units,
                flat_units: 0,
                amount_units: 0,
                receipts: Vec::new(),
            });
            line.quantity = line.quantity.saturating_add(e.quantity);
            line.flat_units = line.flat_units.saturating_add(e.flat_units);
            line.amount_units = line.amount_units.saturating_add(e.amount_units);
            // Keep the first non-zero unit rate seen for the line's display rate.
            if line.unit_rate_units == 0 && e.unit_rate_units != 0 {
                line.unit_rate_units = e.unit_rate_units;
            }
            line.receipts.push(e.receipt.clone());
        }
        let line_items: Vec<LineItem> = by_resource.into_values().collect();
        let total_units = line_items.iter().map(|l| l.amount_units).sum();
        Invoice {
            account: account.to_string(),
            period,
            asset: asset.into(),
            line_items,
            total_units,
            generated_at: generated_at.into(),
        }
    }

    /// **Re-witness the bill against its receipts** (the verifiable-invoice tooth).
    ///
    /// Checks, for every line: each receipt is billed in the invoice's asset; the
    /// line's `amount_units` equals the sum of its receipts' amounts (every line traces
    /// to a receipt); and `quantity × unit_rate + flat` reproduces the amount whenever a
    /// unit rate is present. Finally the invoice `total_units` equals the sum of every
    /// line. A padded line, an inflated total, or a tampered receipt amount all fail.
    pub fn verify_against_receipts(&self) -> Result<(), InvoiceError> {
        let mut lines_sum: i64 = 0;
        for line in &self.line_items {
            let mut receipts_sum: i64 = 0;
            for r in &line.receipts {
                if r.asset != self.asset {
                    return Err(InvoiceError::AssetMismatch {
                        resource: line.resource,
                        expected: self.asset.clone(),
                        found: r.asset.clone(),
                    });
                }
                receipts_sum = receipts_sum.saturating_add(r.amount);
            }
            if receipts_sum != line.amount_units {
                return Err(InvoiceError::LineDoesNotTrace {
                    resource: line.resource,
                    line_amount: line.amount_units,
                    receipts_sum,
                });
            }
            // The quantity breakdown must reproduce the amount when a unit rate applies.
            if line.unit_rate_units != 0 {
                let computed = (line.quantity as i64)
                    .saturating_mul(line.unit_rate_units)
                    .saturating_add(line.flat_units);
                if computed != line.amount_units {
                    return Err(InvoiceError::LineMathMismatch {
                        resource: line.resource,
                        computed,
                        line_amount: line.amount_units,
                    });
                }
            }
            lines_sum = lines_sum.saturating_add(line.amount_units);
        }
        if lines_sum != self.total_units {
            return Err(InvoiceError::TotalMismatch {
                total: self.total_units,
                lines_sum,
            });
        }
        Ok(())
    }

    /// The canonical, domain-separated body hash of the invoice — what the seal signs
    /// and the next invoice in the producer's chain links back to. Binds the account,
    /// period, asset, every line (resource, quantity, rate, flat, amount, and each
    /// anchored receipt's `(lease_id, period, amount)`), and the total. The line items
    /// are already sorted by resource, so the hash is canonical.
    pub fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"dreggnet-invoice-v1");
        h.field(self.account.as_bytes());
        h.field(self.period.label.as_bytes());
        h.u64(self.period.start as u64);
        h.u64(self.period.end as u64);
        h.field(self.asset.as_bytes());
        h.u64(self.line_items.len() as u64);
        for line in &self.line_items {
            h.field(line.resource.tag().as_bytes());
            h.u64(line.quantity);
            h.field(&line.unit_rate_units.to_le_bytes());
            h.field(&line.flat_units.to_le_bytes());
            h.field(&line.amount_units.to_le_bytes());
            h.u64(line.receipts.len() as u64);
            for r in &line.receipts {
                h.field(r.lease_id.as_bytes());
                h.field(&r.period.to_le_bytes());
                h.field(&r.amount.to_le_bytes());
            }
        }
        h.field(&self.total_units.to_le_bytes());
        h.finalize()
    }

    /// **Seal the invoice into the receipt contract** at chain position `seq`: link it
    /// to the producer chain's head, ed25519-sign it, and advance the head. The result
    /// is a [`SealedInvoice`] a customer re-witnesses without trusting the host, and a
    /// run of sealed invoices verifies as one tamper-evident stream
    /// ([`dreggnet_receipt::verify_chain`]).
    pub fn seal(self, chain: &ReceiptChain, seq: u64) -> SealedInvoice {
        let att = chain.seal(self.body_hash(), seq, None);
        SealedInvoice {
            invoice: self,
            seq,
            attestation: Some(att),
        }
    }
}

/// An invoice sealed into the product-wide receipt contract: the bill plus its chain
/// position and signed attestation. Implements [`ReceiptBody`] so it re-witnesses with
/// the same [`dreggnet_receipt::verify_chain`] every product receipt does.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SealedInvoice {
    /// The billed invoice.
    pub invoice: Invoice,
    /// The producer-monotonic chain position.
    pub seq: u64,
    /// The signed attestation (prev-hash link + ed25519 signature); `Some` once sealed.
    pub attestation: Option<ReceiptAttestation>,
}

impl ReceiptBody for SealedInvoice {
    fn body_hash(&self) -> [u8; 32] {
        self.invoice.body_hash()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attestation.as_ref()
    }
}

/// Fan a pooled set of usage events out into one **disjoint invoice per account**: each
/// invoice sees only its own account's usage (the cap-scoping tooth applied across the
/// whole pool). Returns invoices keyed by account, period + asset shared.
pub fn invoices_for(
    period: BillingPeriod,
    asset: &str,
    events: &[UsageEvent],
    generated_at: &str,
) -> BTreeMap<String, Invoice> {
    let mut accounts: BTreeMap<String, ()> = BTreeMap::new();
    for e in events {
        accounts.insert(e.account.clone(), ());
    }
    accounts
        .into_keys()
        .map(|acct| {
            let inv = Invoice::assemble(&acct, period.clone(), asset, events, generated_at);
            (acct, inv)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::usage::UsageReceipt;
    use dreggnet_receipt::verify_chain;

    const DREGG: &str = "DREGG";

    fn period() -> BillingPeriod {
        BillingPeriod::new("2026-06", 0, 1000)
    }

    /// A small realistic usage pool for `acct`: a site publish (op + storage), a
    /// bandwidth roll-up, a cert, and a build — each carrying a real receipt anchor.
    fn acct_events(acct: &str) -> Vec<UsageEvent> {
        vec![
            // publish: op 10 + 2 KiB × 1 = 12.
            UsageEvent::metered(
                acct,
                BillableResource::Site,
                "blog",
                2,
                1,
                10,
                UsageReceipt::new("host:publish:blog", 0, DREGG, 12, Some("t-pub".into())),
            ),
            // bandwidth: 3 MiB × 5 = 15.
            UsageEvent::metered(
                acct,
                BillableResource::Bandwidth,
                "blog",
                3,
                5,
                0,
                UsageReceipt::new("host:bandwidth:blog", 1, DREGG, 15, Some("t-bw".into())),
            ),
            // cert: 4.
            UsageEvent::metered(
                acct,
                BillableResource::Cert,
                "blog.example",
                1,
                4,
                0,
                UsageReceipt::new("host:cert:blog.example", 0, DREGG, 4, None),
            ),
            // build: 5 min × 3 = 15.
            UsageEvent::metered(
                acct,
                BillableResource::Build,
                "deploy-1",
                5,
                3,
                0,
                UsageReceipt::new("host:build:deploy-1", 0, DREGG, 15, None),
            ),
        ]
    }

    // ── TOOTH: usage → an invoice with correct line items + total, all receipt-traced ──
    #[test]
    fn usage_aggregates_into_a_receipt_traced_invoice() {
        let events = acct_events("alice");
        let inv = Invoice::assemble("alice", period(), DREGG, &events, "t0");

        // One line per resource, sorted by the resource order (Site < Bandwidth < Cert < Build).
        assert_eq!(inv.line_items.len(), 4);
        assert_eq!(inv.line_items[0].resource, BillableResource::Site);
        assert_eq!(inv.line_items[0].amount_units, 12);
        assert_eq!(inv.line_items[0].quantity, 2);
        assert_eq!(inv.line_items[0].flat_units, 10);

        // The total is the sum of the lines: 12 + 15 + 4 + 15 = 46.
        assert_eq!(inv.total_units, 46);

        // And the whole bill re-witnesses against its receipts: every line traces.
        assert_eq!(inv.verify_against_receipts(), Ok(()));
    }

    // ── TOOTH: an inflated total / padded line is caught by the receipt trace ──
    #[test]
    fn a_padded_invoice_fails_the_receipt_trace() {
        let events = acct_events("alice");
        let mut inv = Invoice::assemble("alice", period(), DREGG, &events, "t0");

        // Pad the total without a backing receipt → caught.
        inv.total_units += 100;
        assert!(matches!(
            inv.verify_against_receipts(),
            Err(InvoiceError::TotalMismatch { .. })
        ));

        // Pad a line's amount (a charge with no receipt behind it) → caught.
        let mut inv2 = Invoice::assemble("alice", period(), DREGG, &events, "t0");
        inv2.line_items[1].amount_units += 50;
        inv2.total_units += 50; // keep the total consistent so the LINE check is what bites.
        assert!(matches!(
            inv2.verify_against_receipts(),
            Err(InvoiceError::LineDoesNotTrace { .. })
        ));
    }

    // ── TOOTH: a tampered receipt amount breaks the trace ──
    #[test]
    fn tampering_a_receipt_amount_breaks_the_trace() {
        let events = acct_events("alice");
        let mut inv = Invoice::assemble("alice", period(), DREGG, &events, "t0");
        // Forge a receipt to claim a smaller settled amount than the line bills.
        inv.line_items[0].receipts[0].amount = 1;
        assert!(matches!(
            inv.verify_against_receipts(),
            Err(InvoiceError::LineDoesNotTrace { .. })
        ));
    }

    // ── TOOTH: another account cannot see this account's invoice (cap-scoped) ──
    #[test]
    fn invoices_are_cap_scoped_per_account() {
        let mut pool = acct_events("alice");
        pool.extend(acct_events("bob"));
        // Bob also has an extra server-uptime line, to make the pools differ.
        pool.push(UsageEvent::metered(
            "bob",
            BillableResource::Server,
            "srv-1",
            3,
            2,
            0,
            UsageReceipt::new("host:uptime:srv-1", 7, DREGG, 6, None),
        ));

        let alice = Invoice::assemble("alice", period(), DREGG, &pool, "t0");
        let bob = Invoice::assemble("bob", period(), DREGG, &pool, "t0");

        // Alice's invoice never carries a receipt billed to bob's resources.
        assert!(
            alice
                .line_items
                .iter()
                .flat_map(|l| &l.receipts)
                .all(|r| !r.lease_id.contains("srv-1"))
        );
        assert_eq!(alice.total_units, 46);
        // Bob's has the extra uptime line.
        assert_eq!(bob.total_units, 46 + 6);
        assert!(
            bob.line_items
                .iter()
                .any(|l| l.resource == BillableResource::Server)
        );

        // The fan-out yields exactly two disjoint invoices, each verifying.
        let all = invoices_for(period(), DREGG, &pool, "t0");
        assert_eq!(all.len(), 2);
        for inv in all.values() {
            assert_eq!(inv.verify_against_receipts(), Ok(()));
        }
        // A stranger account that owns nothing in the pool gets an empty, zero invoice.
        let stranger = Invoice::assemble("carol", period(), DREGG, &pool, "t0");
        assert!(stranger.line_items.is_empty());
        assert_eq!(stranger.total_units, 0);
        assert_eq!(stranger.verify_against_receipts(), Ok(()));
    }

    // ── TOOTH: the sealed invoice is a re-witnessable, tamper-evident receipt ──
    #[test]
    fn a_sealed_invoice_chain_is_tamper_evident() {
        let chain = ReceiptChain::from_seed([7u8; 32]);
        // Two billing periods → a two-invoice producer chain.
        let inv0 = Invoice::assemble(
            "alice",
            BillingPeriod::new("2026-05", 0, 100),
            DREGG,
            &acct_events("alice"),
            "t0",
        )
        .seal(&chain, 0);
        let inv1 = Invoice::assemble(
            "alice",
            BillingPeriod::new("2026-06", 100, 200),
            DREGG,
            &acct_events("alice"),
            "t1",
        )
        .seal(&chain, 1);
        let stream = vec![inv0, inv1];

        // The customer re-witnesses the whole stream with just the receipts + the signer key.
        assert_eq!(verify_chain(&stream), Ok(()));

        // Altering a sealed invoice's billed amount invalidates its signature.
        let mut forged = stream.clone();
        forged[1].invoice.total_units += 1;
        assert!(
            verify_chain(&forged).is_err(),
            "a tampered bill fails re-witness"
        );
    }
}
