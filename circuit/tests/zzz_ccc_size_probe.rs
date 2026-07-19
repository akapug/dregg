//! # E15 MEASUREMENT — what does ONE cross-cell-conservation (CCC v2) proof COST on the wire?
//!
//! The circuit-minimality census (E15, `docs/EFFICIENCY-BACKLOG-circuit-minimality.md`) found the
//! Lean-proved CCC AIR has ZERO production callers (`BlockConservation::prove_and_verify` is
//! test-only; `verify_with_proofs` has no caller at all) while the live per-asset Σδ=0 gate is
//! scalar Rust arithmetic (`BlockConservation::check`, i64 sums). The route-vs-retire decision
//! needs the PRICE of routing: if the verifier wiring its own docs describe ever lands, every
//! turn bundle carries one of THESE proofs per touched asset. This test measures that unit —
//! the postcard-serialized wire size of a real, verifying CCC v2 proof at the minimal honest
//! trace (one matched transfer, 4 padded rows) and at a 2×-active trace (8 padded rows) — so the
//! v2 (172-col, 154 bit-decomposition range columns) baseline is MEASURED, not estimated, before
//! any byte-bus re-emit (172 → ~30 committed cols via the width-tagged range table,
//! `rangeTidW 15`) is priced against it.
//!
//! A measurement, in the house style of `effect_vm_ir2_size_measure.rs`: it asserts the proofs
//! are REAL (prove + verify through the pinned Lean descriptor) and reports sizes; it asserts
//! nothing about which number should win.
//!
//! Run: `CARGO_TARGET_DIR=/tmp/adv-E15 cargo test -p dregg-circuit --test zzz_ccc_size_probe -- --nocapture`

use dregg_circuit::cross_cell_conservation_air::{
    CrossCellDelta, build_cross_cell_conservation_trace, prove_cross_cell_conservation,
    verify_cross_cell_conservation,
};
use dregg_circuit::field::BabyBear;

fn kib(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

fn delta(asset: u32, mag: u32, credit: bool) -> CrossCellDelta {
    CrossCellDelta {
        asset: BabyBear::new(asset),
        magnitude: mag,
        credit,
    }
}

/// Prove + verify the delta list through the pinned Lean v2 descriptor, then measure the
/// postcard wire size (total + component breakdown), mirroring
/// `effect_vm_ir2_size_measure::breakdown`.
fn prove_verify_measure(label: &str, deltas: &[CrossCellDelta]) -> usize {
    let (trace, pi) = build_cross_cell_conservation_trace(deltas);
    let proof = prove_cross_cell_conservation(&trace, &pi)
        .unwrap_or_else(|e| panic!("[{label}] honest CCC trace must prove: {e}"));
    verify_cross_cell_conservation(&proof, &pi)
        .unwrap_or_else(|e| panic!("[{label}] CCC proof must verify: {e}"));

    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    let commitments = postcard::to_allocvec(&proof.commitments).unwrap().len();
    let opened = postcard::to_allocvec(&proof.opened_values).unwrap().len();
    let opening = postcard::to_allocvec(&proof.opening_proof).unwrap().len();
    println!(
        "[{label}] rows: {} × cols: {} | total: {} B ({:.1} KiB) | commitments: {} B | \
         opened_values: {} B ({:.1} KiB) | opening_proof: {} B ({:.1} KiB) | degree_bits: {:?}",
        trace.len(),
        trace[0].len(),
        total,
        kib(total),
        commitments,
        opened,
        kib(opened),
        opening,
        kib(opening),
        proof.degree_bits,
    );
    total
}

/// THE E15 UNIT PRICE: one CCC v2 proof at the minimal honest trace (a matched A −10 / B +10
/// transfer, 2 active + padding = 4 rows) and at 4 active deltas (8 rows). This is the per-asset
/// per-turn wire cost the route branch would add under the CURRENT 172-col descriptor.
#[test]
fn ccc_v2_unit_proof_size() {
    let two = vec![delta(7, 10, false), delta(7, 10, true)];
    let four = vec![
        delta(7, 10, false),
        delta(7, 10, true),
        delta(7, 25, false),
        delta(7, 25, true),
    ];
    let small = prove_verify_measure("ccc-v2 2-delta (4 rows)", &two);
    let bigger = prove_verify_measure("ccc-v2 4-delta (8 rows)", &four);
    // Both are real proofs of the same 172-col descriptor; the delta between them isolates the
    // row-doubling share from the fixed FRI floor.
    println!(
        "[ccc-v2] row-doubling delta: {} B ({:.1} KiB)",
        bigger as i64 - small as i64,
        kib(bigger.saturating_sub(small)),
    );
}
