//! # supply-chain-provenance — the DERIVED-CELL + ATTESTED-QUERY showcase.
//!
//! A provenance SUMMARY is a derived view: `summary = f(events)`. The custody
//! history of an item ([`Handoff`](crate::Handoff)s) determines, by a pure
//! function, the item's current custodian, how many handoffs it has been
//! through, its provenance epoch, and its chain tip. That is a natural
//! **derived cell** — a cell whose committed value is a verifiable function of
//! other state. This module wires the TWO grounded dregg capabilities that make
//! such a summary unforgeable to a light client:
//!
//! 1. **The derived-cell primitive** ([`dregg_cell::derived`]) — a derived
//!    cell carries a [`DerivationSpec`] and the CLAIMED result of evaluating it
//!    over its source cells, BOUND into its committed state. A forged summary
//!    (claim ≠ `f(sources)`) or a stale one (sources moved, summary did not
//!    re-derive) is rejected by the SAME [`verify_derivation`] check. The
//!    invariant is the executor image of the proven Lean rung
//!    `metatheory/Dregg2/Deos/DerivedCell.lean` (`bind_verifies`,
//!    `forged_value_rejected`, `stale_rejected`, `claim_bound_in_root`). Here a
//!    **shipment-manifest** cell is derived over a roster of item source cells:
//!    its committed value IS the total quantity in the shipment — the sum of the
//!    item cells' balances ([`dregg_cell::derived::Aggregate::SumBalance`], the materialized-aggregate
//!    seed). A manifest that over-states the total (forge) or that is not
//!    re-derived after an item's quantity changes (stale) does not verify.
//!
//! 2. **The attested-query primitive** ([`dregg_query`]) — the item's custody
//!    handoffs are receipt rows; a query over them carries a NON-OMISSION
//!    certificate (a range opening against the receipt-log MMR root, the Rust
//!    embodiment of `Dregg2/Lightclient/MMR.lean`'s `server_cannot_omit_position`).
//!    A verifier checks the certificate against a trusted root and re-derives the
//!    rows, so a verifying answer is provably computed from EXACTLY the committed
//!    handoff range — nothing hidden, nothing forged, nothing reordered. This is
//!    the COMPLETENESS certificate over a cell's provenance events: "these are
//!    ALL the custody handoffs, and I can prove none were omitted".
//!
//! ## What is grounded vs. projected
//!
//! [`summarize`] is the **projection-function form** of the derived view — the
//! pure `f(events)` shape, documented as the model the grounded primitives bind.
//! [`bind_shipment_manifest`] / [`verify_shipment_manifest`] are the **grounded
//! derived-cell** wiring over the real [`dregg_cell::derived`] primitive.
//! [`attested_custody_log`] / [`verify_attested_custody_log`] are the **grounded
//! attested-query** wiring over the real [`dregg_query`] MMR certificate. All
//! three are exercised in this module's tests.

use dregg_app_framework::hex_encode_32;
use dregg_cell::cell::Cell;
use dregg_cell::derived::{
    DerivationError, DerivationSpec, bind_derivation, resolver_from_pairs, verify_derivation,
};
use dregg_cell::id::CellId as CellCellId;
use dregg_query::receipt::EffectSummary;
use dregg_query::{
    AttestError, AttestedAnswer, AttestedSlice, Blake3Mmr, Mmr, Pred, Query, RangeCertificate,
    ReceiptRecord, Term, answer_whole_log,
};

use dregg_types::CellId;

use crate::{CUSTODIAN_SLOT, Handoff, custody_chain_digests, custody_chain_is_connected};

// =============================================================================
// (1) The projection-function form — `summary = f(events)`.
// =============================================================================

/// **A provenance summary** — the pure derived view of an item's custody
/// history. Every field is a deterministic function of the
/// [`Handoff`](crate::Handoff) sequence, so a verifier holding the events
/// recomputes it exactly. This is the derived-view SHAPE the grounded primitives
/// below bind into a commitment / certify against a root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProvenanceSummary {
    /// The CURRENT sole custodian's identity scalar (the latest handoff's `to`),
    /// or the genesis-zero scalar for an empty history.
    pub current_custodian: [u8; 32],
    /// How many custody handoffs the item has been through (the chain length).
    pub handoff_count: usize,
    /// The provenance epoch reached (the last handoff's epoch, `0` if empty).
    pub epoch: u64,
    /// The chain tip — the latest committed custody-link digest (the genesis-zero
    /// digest for an empty history).
    pub chain_tip: [u8; 32],
    /// Whether the history is a single CONNECTED, conserved custody path (no fork,
    /// no gap, strictly-monotone epochs from 1) — the conservation witness.
    pub conserved: bool,
}

/// **`summarize`** — fold a custody history into its [`ProvenanceSummary`]. The
/// projection `f(events)`: the current custodian is the latest `to`, the chain
/// tip is the last link digest, and `conserved` is the single-custodianship
/// conservation check ([`custody_chain_is_connected`](crate::custody_chain_is_connected)).
pub fn summarize(handoffs: &[Handoff]) -> ProvenanceSummary {
    let digests = custody_chain_digests(handoffs);
    ProvenanceSummary {
        current_custodian: handoffs.last().map(|h| h.to).unwrap_or([0u8; 32]),
        handoff_count: handoffs.len(),
        epoch: handoffs.last().map(|h| h.epoch).unwrap_or(0),
        chain_tip: digests.last().copied().unwrap_or([0u8; 32]),
        conserved: custody_chain_is_connected(handoffs),
    }
}

// =============================================================================
// (2) The grounded derived-cell — a shipment manifest over item source cells.
// =============================================================================

/// The [`DerivationSpec`] for a **shipment manifest** over `items`: its committed
/// value is the total quantity the shipment carries — the sum of the item cells'
/// balances ([`dregg_cell::derived::Aggregate::SumBalance`], the materialized-aggregate seed). A
/// manifest that over-states the total (forge) or that is not re-derived after an
/// item's quantity changes (stale) fails [`verify_shipment_manifest`].
pub fn shipment_manifest_spec(items: impl IntoIterator<Item = CellCellId>) -> DerivationSpec {
    DerivationSpec::sum_balance(items)
}

/// **Re-derive a shipment manifest** — evaluate [`shipment_manifest_spec`] over
/// the `items` roster and bind the (spec-digest, claimed-total) pair into the
/// `manifest` cell's committed heap (the grounded `dregg_cell::derived`
/// `bind_derivation`). Returns the freshly derived total quantity. After this, the
/// manifest's commitment binds the shipment total; a re-derive on every item
/// quantity change keeps it honest.
pub fn bind_shipment_manifest(
    manifest: &mut Cell,
    items: &[(CellCellId, &Cell)],
) -> Result<i64, DerivationError> {
    let spec = shipment_manifest_spec(items.iter().map(|(id, _)| *id));
    bind_derivation(manifest, &spec, resolver_from_pairs(items))
}

/// **Verify a shipment manifest** — the grounded `dregg_cell::derived`
/// `verify_derivation` forge/stale detector: recompute the shipment total over the
/// `items` roster and reject a `manifest` whose bound claim disagrees
/// ([`DerivationError::ValueMismatch`]). Returns the verified total on success.
pub fn verify_shipment_manifest(
    manifest: &Cell,
    items: &[(CellCellId, &Cell)],
) -> Result<i64, DerivationError> {
    let spec = shipment_manifest_spec(items.iter().map(|(id, _)| *id));
    verify_derivation(manifest, &spec, resolver_from_pairs(items))
}

// =============================================================================
// (3) The grounded attested-query — a completeness certificate over the events.
// =============================================================================

/// The per-handoff receipt commitment (the MMR leaf value): a domain-separated
/// digest of the item, the link digest, and the epoch. Deterministic, so a
/// verifier recomputes the same leaf.
fn handoff_receipt_hash(item: &CellId, link: &[u8; 32], epoch: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-supplychain-receipt\x01");
    h.update(item.as_bytes());
    h.update(link);
    h.update(&epoch.to_be_bytes());
    *h.finalize().as_bytes()
}

/// Build the receipt rows for an item's custody history — one
/// [`ReceiptRecord`] per handoff, carrying an [`EffectSummary::Field`] for the
/// `CUSTODIAN` slot write (the disclosed provenance event the fact extractor
/// reads). The dense `chain_index` is the handoff position; the height is the
/// provenance epoch.
pub fn custody_receipts(item: &CellId, handoffs: &[Handoff]) -> Vec<ReceiptRecord> {
    let digests = custody_chain_digests(handoffs);
    let item_hex = hex_encode_32(item.as_bytes());
    handoffs
        .iter()
        .enumerate()
        .map(|(i, h)| ReceiptRecord {
            chain_index: i as u64,
            receipt_hash: hex_encode_32(&handoff_receipt_hash(item, &digests[i], h.epoch)),
            height: h.epoch,
            agent: item_hex.clone(),
            effects: vec![EffectSummary::Field {
                cell: item_hex.clone(),
                index: CUSTODIAN_SLOT as u64,
                value: hex_encode_32(&h.to),
            }],
        })
        .collect()
}

/// A query for every recorded custodian of an item: `field(item, CUSTODIAN_SLOT,
/// ?custodian, ?height)`. A pure conjunctive scan (no aggregate, no negation), so
/// the CALM classifier grades it MONOTONE — a verifying whole-log answer is the
/// unqualified "these are ALL the custodians, none omitted".
pub fn custody_log_query(item: &CellId) -> Query {
    Query::new().atom(
        Pred::Field,
        vec![
            Term::sym(hex_encode_32(item.as_bytes())),
            Term::nat(CUSTODIAN_SLOT as u64),
            Term::var("custodian"),
            Term::var("height"),
        ],
    )
}

/// **Produce an attested custody log** — the grounded `dregg_query` non-omission
/// certificate over an item's provenance events. Builds the receipt-log MMR over
/// the custody receipts, opens the WHOLE prefix, and evaluates
/// [`custody_log_query`] over the certified slice
/// ([`answer_whole_log`]). Returns the committed MMR `root` (the trusted root a
/// light client pins) and the certificate-carrying [`AttestedAnswer`].
///
/// The answer, once it [`verify`](AttestedAnswer::verify)s against the returned
/// root, is provably computed from EXACTLY the committed handoff range — a
/// completeness certificate over the item's custody history.
pub fn attested_custody_log(item: &CellId, handoffs: &[Handoff]) -> ([u8; 32], AttestedAnswer) {
    let receipts = custody_receipts(item, handoffs);

    // The receipt-log MMR over the per-handoff commitments.
    let mut mmr = Mmr::new(Blake3Mmr);
    for r in &receipts {
        mmr.push(r.receipt_hash_bytes().expect("our own 32-byte hex leaf"));
    }
    let root = mmr.root();
    let len = mmr.len();
    let hi = len.saturating_sub(1);
    let (_values, opening) = mmr.open_range(0, hi);

    let slice = AttestedSlice {
        receipts,
        cert: RangeCertificate {
            root,
            lo: 0,
            hi,
            opening,
        },
    };
    let answer =
        answer_whole_log(slice, custody_log_query(item)).expect("the custody-log query evaluates");
    (root, answer)
}

/// **Verify an attested custody log** against a trusted `root` — the grounded
/// `dregg_query` verifier: the slice's non-omission certificate verifies (the
/// input was the EXACT receipt range), the whole-log coverage matches the
/// certificate, and the rows equal a local re-evaluation. A tampered, omitted,
/// or reordered receipt makes this fail ([`AttestError`]).
pub fn verify_attested_custody_log(
    answer: &AttestedAnswer,
    root: &[u8; 32],
) -> Result<(), AttestError> {
    answer.verify(&Blake3Mmr, root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{GENESIS_PREV, identity_field};

    fn demo_history() -> Vec<Handoff> {
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let b = identity_field("carrier-b");
        vec![
            Handoff {
                from: GENESIS_PREV,
                to: m,
                epoch: 1,
            },
            Handoff {
                from: m,
                to: a,
                epoch: 2,
            },
            Handoff {
                from: a,
                to: b,
                epoch: 3,
            },
        ]
    }

    // ── (1) the projection-function derived view ─────────────────────────────

    #[test]
    fn summary_is_a_faithful_projection_of_the_history() {
        let h = demo_history();
        let s = summarize(&h);
        assert_eq!(s.handoff_count, 3);
        assert_eq!(s.epoch, 3);
        assert_eq!(s.current_custodian, identity_field("carrier-b"));
        assert_eq!(s.chain_tip, *custody_chain_digests(&h).last().unwrap());
        assert!(
            s.conserved,
            "the honest history is a connected custody path"
        );
    }

    #[test]
    fn an_empty_history_summarizes_to_genesis() {
        let s = summarize(&[]);
        assert_eq!(s.handoff_count, 0);
        assert_eq!(s.epoch, 0);
        assert_eq!(s.current_custodian, [0u8; 32]);
        assert_eq!(s.chain_tip, [0u8; 32]);
    }

    // ── (2) the grounded derived-cell (dregg_cell::derived) ──────────────────

    /// An item cell carrying a quantity (its balance) — the unit of the shipment
    /// total the manifest derives.
    fn item_cell(seed: u8, quantity: i64) -> Cell {
        Cell::with_balance([seed; 32], [seed; 32], quantity)
    }

    #[test]
    fn an_honest_shipment_manifest_verifies() {
        let i1 = item_cell(1, 100);
        let i2 = item_cell(2, 250);
        let i3 = item_cell(3, 50);
        let roster = [(i1.id(), &i1), (i2.id(), &i2), (i3.id(), &i3)];

        let mut manifest = item_cell(9, 0);
        let total = bind_shipment_manifest(&mut manifest, &roster).unwrap();
        assert_eq!(total, 400, "100 + 250 + 50 units in the shipment");
        assert_eq!(verify_shipment_manifest(&manifest, &roster), Ok(400));
    }

    #[test]
    fn a_forged_shipment_manifest_is_rejected() {
        let i1 = item_cell(1, 100);
        let i2 = item_cell(2, 250);
        let roster = [(i1.id(), &i1), (i2.id(), &i2)];

        // A manifest that lies about its shipment total (claims 999, truly 350).
        let mut forged = item_cell(9, 0);
        let spec = shipment_manifest_spec(roster.iter().map(|(id, _)| *id));
        dregg_cell::derived::write_binding(&mut forged.state, &spec, 999);

        assert!(matches!(
            verify_shipment_manifest(&forged, &roster),
            Err(DerivationError::ValueMismatch {
                claimed: 999,
                actual: 350
            })
        ));
    }

    #[test]
    fn a_stale_shipment_manifest_is_rejected() {
        let mut i1 = item_cell(1, 100);
        let i2 = item_cell(2, 250);

        // Honestly derive over the roster (total 350).
        let mut manifest = item_cell(9, 0);
        {
            let roster = [(i1.id(), &i1), (i2.id(), &i2)];
            assert_eq!(bind_shipment_manifest(&mut manifest, &roster).unwrap(), 350);
        }

        // An item's quantity changes (100 -> 600) without re-deriving the manifest —
        // the SAME source set, so the spec digest is unchanged and the value tooth
        // (not the spec tooth) bites.
        i1.state.apply_balance_change(500);
        let roster = [(i1.id(), &i1), (i2.id(), &i2)];
        assert!(matches!(
            verify_shipment_manifest(&manifest, &roster),
            Err(DerivationError::ValueMismatch {
                claimed: 350,
                actual: 850
            })
        ));
    }

    // ── (3) the grounded attested-query (dregg_query) ────────────────────────

    fn item_id() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    #[test]
    fn the_attested_custody_log_verifies_whole_log_completeness() {
        let item = item_id();
        let h = demo_history();
        let (root, answer) = attested_custody_log(&item, &h);

        // The certificate verifies against the committed root — the answer is
        // provably computed from EXACTLY the genuine handoff range (non-omission).
        assert!(verify_attested_custody_log(&answer, &root).is_ok());
        // One row per recorded custodian (3 distinct custodians).
        assert_eq!(
            answer.rows.len(),
            3,
            "every custodian is in the certified answer"
        );
        assert_eq!(answer.coverage, dregg_query::Coverage::WholeLog);
    }

    #[test]
    fn a_tampered_receipt_breaks_the_certificate() {
        let item = item_id();
        let h = demo_history();
        let (root, mut answer) = attested_custody_log(&item, &h);
        assert!(verify_attested_custody_log(&answer, &root).is_ok());

        // Tamper a receipt leaf in the certified slice — the MMR opening no longer
        // bags to the trusted root (the server cannot substitute a receipt).
        answer.slice.receipts[1].receipt_hash = hex_encode_32(&[0xAB; 32]);
        assert!(
            verify_attested_custody_log(&answer, &root).is_err(),
            "a tampered receipt must break the non-omission certificate"
        );
    }

    #[test]
    fn an_omitted_handoff_breaks_the_certificate() {
        let item = item_id();
        let h = demo_history();
        let (root, mut answer) = attested_custody_log(&item, &h);
        assert!(verify_attested_custody_log(&answer, &root).is_ok());

        // Drop a handoff from the certified slice — the dense count no longer
        // matches the root-pinned length (the omission tooth).
        answer.slice.receipts.pop();
        assert!(
            verify_attested_custody_log(&answer, &root).is_err(),
            "an omitted handoff must break the completeness certificate"
        );
    }
}
