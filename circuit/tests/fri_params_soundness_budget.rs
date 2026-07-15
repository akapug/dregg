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
//!   2. NON-VACUITY: `budget_gate_reds_each_degraded_knob` PERTURBS THE DEPLOYED CONSTS — it halves
//!      each of the 3 gated knobs on each config in turn — and requires `check_budget`, the same
//!      function tooth 1 calls, to refuse with a typed `BelowFloor` naming that config and that
//!      number. It measures the gate's real margin: if a deployed knob could be halved without a
//!      red, this says so.
//!
//! ## ⚠ The gate covers 3 of the 5 deployed knobs
//!
//! `IR2_FRI_MAX_LOG_ARITY` and `IR2_FRI_LOG_FINAL_POLY_LEN` are gated by NOTHING and can drift
//! silently. That is the sharper half of the gap, because the surviving ~112.6-bit bound is
//! explicitly STRUCTURE-SPECIFIC (the deployed dim-2 constant-fold recursion code, at fixed `r = 2`,
//! `n = 64`) — so the only numeric gate here enforces a margin on the arithmetic this same file calls
//! REFUTED, and enforces nothing on the structural parameters the surviving bound actually depends
//! on. Closing it is CRATE-EXCELLENCE-PLAN Move 5 ("extend the FRI gate to all 5 knobs" + a
//! `proven_bits` floor at ~112); retargeting the margin off the refuted capacity metric is an ember
//! call, not this file's to make.
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

/// Why a knob set was refused — the typed reason, so a caller (and the non-vacuity gate below) can
/// assert WHICH tooth fired rather than that something went wrong.
#[derive(Debug, PartialEq, Eq)]
enum BudgetRefusal {
    /// The capacity ledger fell under the drift margin.
    BelowFloor {
        name: &'static str,
        got: usize,
        floor: usize,
    },
    /// The two deployed configs disagree on `(conjectured, proven)` — a security-parity break.
    ParityBreak {
        left: (usize, usize),
        right: (usize, usize),
    },
}

/// **THE GATE ITSELF**, over the knobs it is handed rather than over the consts it closes on.
///
/// This is a plain function, not a `#[test]` body, for one reason: a `const` cannot be perturbed, so
/// a gate that reads `PROD_FRI_*` inline is unfalsifiable by any test — which is exactly how
/// `budget_gate_reds_a_degraded_config` came to assert `20 < 128` and never invoke the gate at all
/// (CRATE-EXCELLENCE-PLAN S8). With the knobs as parameters, `budget_gate_reds_each_degraded_knob`
/// can hand it PERTURBED DEPLOYED values and require the real gate to red.
fn check_budget(configs: [(&'static str, usize, usize, usize); 2]) -> Result<(), BudgetRefusal> {
    let mut ledgers = Vec::new();
    for (name, lb, q, pow) in configs {
        let conj = conjectured_bits(lb, q, pow);
        let prov = proven_bits(lb, q, pow);
        if conj < CONJECTURED_FLOOR_BITS {
            return Err(BudgetRefusal::BelowFloor {
                name,
                got: conj,
                floor: CONJECTURED_FLOOR_BITS,
            });
        }
        ledgers.push((conj, prov));
    }
    if ledgers[0] != ledgers[1] {
        return Err(BudgetRefusal::ParityBreak {
            left: ledgers[0],
            right: ledgers[1],
        });
    }
    Ok(())
}

/// The DEPLOYED knob set, read from the production exports — the only input the live gate judges.
fn deployed() -> [(&'static str, usize, usize, usize); 2] {
    [
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
    ]
}

#[test]
fn deployed_fri_configs_clear_the_conjectured_floor() {
    for (name, lb, q, pow) in deployed() {
        eprintln!(
            "[{name}] log_blowup={lb} queries={q} query_pow={pow} → conjectured {} bits, \
             proven (Johnson) {} bits (both capped by the ~124-bit degree-4 extension)",
            conjectured_bits(lb, q, pow),
            proven_bits(lb, q, pow)
        );
    }
    if let Err(e) = check_budget(deployed()) {
        panic!(
            "DEPLOYED FRI KNOB DRIFT: {e:?}. A knob change dropped the deployed soundness floor (or \
             broke security parity between the two configs) — this must land as a deliberate, named \
             decision, never a silent downgrade. Re-run the FRI grid \
             (`effect_vm_ir2_size_measure::ir2_fri_grid`) before accepting it."
        );
    }
}

/// **PROOF THE GATE BITES — perturb the DEPLOYED consts and require the REAL gate to red.**
///
/// The predecessor (`budget_gate_reds_a_degraded_config`) asserted `conjectured_bits(1, 20, 0) < 128`
/// — i.e. that `20 < 128`. It evaluated the formula on a synthetic point it invented, never called
/// the gate it was named for, and would have passed unchanged if the gate's `assert!` had been
/// DELETED OUTRIGHT. It could not distinguish an armed gate from an absent one.
///
/// This walks each of the 3 gated knobs on each of the 2 deployed configs, degrades that ONE knob
/// from its real deployed value, and requires `check_budget` — the same function the live gate calls
/// — to refuse with the typed `BelowFloor`. So it measures the gate's margin against reality: if the
/// deployed knobs ever sit so far above the floor that a knob can be halved without reddening, this
/// test says so.
#[test]
fn budget_gate_reds_each_degraded_knob() {
    // ── HONEST POLE FIRST. The unperturbed deployed knobs must PASS. Without this every "the
    //    degraded config reds" assertion below is satisfied by a gate that refuses everything.
    assert_eq!(
        check_budget(deployed()),
        Ok(()),
        "the DEPLOYED knobs must clear the gate — otherwise the degradation assertions below are \
         vacuous (a gate that reds on everything reds on a degraded config too)"
    );

    // ── Degrade one knob at a time, from the DEPLOYED value, and require the real gate to red.
    for ci in 0..2 {
        for knob in 0..3 {
            let name = deployed()[ci].0;
            let mut cfgs = deployed();
            let (_, lb, q, pow) = cfgs[ci];
            let knob_name = match knob {
                0 => "log_blowup",
                1 => "num_queries",
                _ => "query_pow_bits",
            };
            // Halve the knob (pow → 0): a plausible "small" config edit, not a strawman. If the gate
            // cannot see a HALVED deployed knob, it is not protecting the floor.
            match knob {
                0 => cfgs[ci] = (name, lb / 2, q, pow),
                1 => cfgs[ci] = (name, lb, q / 2, pow),
                _ => cfgs[ci] = (name, lb, q, 0),
            }
            let (_, dlb, dq, dpow) = cfgs[ci];
            let got = conjectured_bits(dlb, dq, dpow);

            match check_budget(cfgs) {
                Ok(()) => panic!(
                    "the gate ACCEPTED [{name}] with {knob_name} degraded {}→{} (capacity \
                     {}→{got} bits). The gate does not red on a halved deployed knob — it is not \
                     protecting the floor it names.",
                    match knob {
                        0 => lb,
                        1 => q,
                        _ => pow,
                    },
                    match knob {
                        0 => dlb,
                        1 => dq,
                        _ => dpow,
                    },
                    conjectured_bits(lb, q, pow)
                ),
                Err(BudgetRefusal::BelowFloor {
                    name: n,
                    got: g,
                    floor,
                }) => {
                    // Assert WHICH config and WHICH number — not merely that it refused. A refusal
                    // naming the other config, or a parity break, would mean the perturbation fired
                    // the wrong tooth and the knob under test is still ungated.
                    assert_eq!(n, name, "the floor tooth fired on the wrong config");
                    assert_eq!(
                        g, got,
                        "the floor tooth reported a capacity it did not compute"
                    );
                    assert_eq!(floor, CONJECTURED_FLOOR_BITS);
                }
                Err(BudgetRefusal::ParityBreak { .. }) => {
                    // Reachable only if a degraded knob still clears the floor and merely breaks
                    // parity — i.e. the FLOOR tooth did not see the degradation. That is the exact
                    // hole this test exists to find, so it is a failure, not a pass.
                    panic!(
                        "degrading [{name}]'s {knob_name} to capacity {got} bits broke PARITY but \
                         did NOT trip the floor tooth ({CONJECTURED_FLOOR_BITS} bits). The floor is \
                         blind to this knob; only the two-config parity check caught it, and parity \
                         would not catch the same edit applied to BOTH configs."
                    );
                }
            }
        }
    }
}
