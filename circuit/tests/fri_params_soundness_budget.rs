//! # THE FRI PARAMS→BITS BUDGET GATE — the knob-drift floor, computed and enforced.
//!
//! The deployed FRI configs carry a soundness budget that lived ONLY in comments
//! (`plonky3_prover::create_config`, `descriptor_ir2::ir2_config`) — a knob edit could silently
//! drop it with no red anywhere. This file computes the budget FROM the exported production knobs
//! and enforces a conservative engineering floor against knob drift.
//!
//! ## The ledger — and what the numbers actually mean (post-audit, 2026-07-13)
//!
//!   * **capacity ledger (REFUTED as a security claim)**: `num_queries × log_blowup +
//!     query_pow_bits`. This is the FRI capacity / up-to-capacity (`1−ρ`) per-query figure every
//!     production STARK historically quoted. **The capacity conjecture is REFUTED** for coset
//!     Reed–Solomon at rates covering our `ρ = 1/64` (Kambiré, arXiv 2604.09724 / eprint
//!     2025/2046). So this column is NOT a proven, nor even conjecturally-safe, security number —
//!     it is retained ONLY as the historical arithmetic and as a stable knob-drift baseline.
//!   * **proven (Johnson bound)**: `num_queries × log_blowup / 2 + query_pow_bits` — the
//!     list-decoding-to-√rate figure that IS proven for any code (`73` at deployed). Reported.
//!   * **the number we actually stand behind (~112.6)**: for the deployed dim-2 constant-fold
//!     recursion code, the FIELD-INDEPENDENT counting bound `|Good| ≤ C(64,2) = 2016` over the
//!     quartic-extension challenge field (`|F| ≈ 2^123.6`) proves `2016/|F| < 2⁻¹¹²`, i.e.
//!     **~112.6 proven bits** (`wrap_perFold_soundness_capacity`,
//!     `metatheory/Dregg2/Circuit/FriCorrelatedAgreementSharp.lean` §8). This — not the refuted
//!     capacity 130 — is the accepted standing security posture (ember, 2026-07-13). Sound against
//!     Kambiré: his blow-up needs `n → ∞`, `r > 2`; at our fixed `r = 2`, `n = 64` his own
//!     construction caps at `C(64,2)`.
//!   * **caps**: all figures are additionally capped by the degree-4 BabyBear extension (~2^124
//!     challenge space) and the Poseidon2 commitment hash. The ~112.6 already sits under this cap.
//!
//! ## What this gate is (and is NOT)
//!
//! The `≥ 128` check below is a CONSERVATIVE ENGINEERING MARGIN on the capacity arithmetic — a
//! knob-drift tooth that reddens when a config edit lowers the (refuted) capacity number. **It is
//! NOT a claim that 128 is proven or conjecturally-safe.** The proven security floor is ~112.6
//! (structure-specific) / 73 (general Johnson), carried in the Lean tree, not here. Retargeting the
//! numeric gate to the proven ~112 would read cleaner but is an ember decision, not this test's to
//! make; the margin is left at 128 (which the deployed capacity 130 clears) purely as drift
//! detection.
//!
//! ## Teeth
//!
//!   1. Both deployed configs (v1 `create_config`, IR-v2 `ir2_config`) satisfy
//!      `capacity ≥ 128` — and their two ledgers agree (security parity, the invariant the
//!      `(6, 19)` pin was measured against).
//!   2. NON-VACUITY: the same formula REDs a degraded knob set — the gate discriminates, it is
//!      not a `≥ 0` tautology.
//!
//! Run: `cargo test -p dregg-circuit --test fri_params_soundness_budget -- --nocapture`.

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_BLOWUP, IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS,
};
use dregg_circuit::plonky3_prover::{
    PROD_FRI_LOG_BLOWUP, PROD_FRI_NUM_QUERIES, PROD_FRI_QUERY_POW_BITS,
};

/// The conservative knob-drift MARGIN the deployed knobs must clear on the capacity arithmetic.
/// NOTE: 128 here is an engineering drift-detection margin, NOT a proven or conjecturally-safe
/// security level — the capacity conjecture is refuted (Kambiré). The proven floor is ~112.6
/// (structure-specific) / 73 (general Johnson), carried in the Lean tree. See the module header.
const CONJECTURED_FLOOR_BITS: usize = 128;

/// Capacity-ledger FRI arithmetic: `~log_blowup` bits per query, plus query-PoW. The capacity
/// conjecture this rests on is REFUTED (Kambiré) — this is a knob-drift baseline, not a security
/// claim; the proven number is `wrap_perFold_soundness_capacity`'s ~112.6.
fn conjectured_bits(log_blowup: usize, num_queries: usize, pow_bits: usize) -> usize {
    num_queries * log_blowup + pow_bits
}

/// Proven (Johnson / list-decoding-to-√rate) FRI soundness: `~log_blowup/2` bits per query,
/// plus query-PoW (integer floor — the reported figure rounds down, never up).
fn proven_bits(log_blowup: usize, num_queries: usize, pow_bits: usize) -> usize {
    num_queries * log_blowup / 2 + pow_bits
}

#[test]
fn deployed_fri_configs_clear_the_conjectured_floor() {
    let configs = [
        (
            "v1 create_config",
            PROD_FRI_LOG_BLOWUP,
            PROD_FRI_NUM_QUERIES,
            PROD_FRI_QUERY_POW_BITS,
        ),
        (
            "ir2_config",
            IR2_FRI_LOG_BLOWUP,
            IR2_FRI_NUM_QUERIES,
            IR2_FRI_QUERY_POW_BITS,
        ),
    ];

    let mut ledgers = Vec::new();
    for (name, lb, q, pow) in configs {
        let conj = conjectured_bits(lb, q, pow);
        let prov = proven_bits(lb, q, pow);
        eprintln!(
            "[{name}] log_blowup={lb} queries={q} query_pow={pow} → conjectured {conj} bits, \
             proven (Johnson) {prov} bits (both capped by the ~124-bit degree-4 extension)"
        );
        assert!(
            conj >= CONJECTURED_FLOOR_BITS,
            "[{name}] DEPLOYED FRI KNOB DRIFT: conjectured budget {conj} < {CONJECTURED_FLOOR_BITS} \
             bits. A knob change dropped the deployed soundness floor — this must land as a \
             deliberate, named decision, never a silent downgrade."
        );
        ledgers.push((conj, prov));
    }

    // Security parity across the two deployed configs — the invariant the ir2 (6, 19) pin was
    // measured against (`effect_vm_ir2_size_measure::ir2_fri_grid`, PROOF-ECONOMICS §2c).
    assert_eq!(
        ledgers[0], ledgers[1],
        "the v1 and IR-v2 configs drifted off security parity (conjectured, proven); \
         re-run the FRI grid before accepting a parity break"
    );
}

/// PROOF THE GATE BITES: the same formula REDs a degraded knob set (a rate-1/2, 20-query,
/// no-PoW config is ~20 conjectured bits — far below the floor). If this ever passes the
/// floor, the gate arithmetic itself is broken.
#[test]
fn budget_gate_reds_a_degraded_config() {
    let degraded = conjectured_bits(1, 20, 0);
    assert!(
        degraded < CONJECTURED_FLOOR_BITS,
        "the budget formula must RED a degraded (lb=1, q=20, pow=0) config; it computed {degraded}"
    );
}
