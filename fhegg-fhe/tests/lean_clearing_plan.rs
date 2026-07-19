//! The real Lean → artifact → Rust decoder → current convex-engine authority edge.

use fhegg_fhe::bfv_lean::{LeanCiphertext, RnsPoly};
use fhegg_fhe::convex_engine::convex_solve;
use fhegg_fhe::convex_step::SignedCt;
use fhegg_fhe::fhir::{
    decode_canonical_clearing_plan, lean_rebalance_plan_v1, LEAN_REBALANCE_V1_JSON,
};

fn zero_signed(lo: i64, hi: i64, t: u64) -> SignedCt {
    let zero_poly = RnsPoly {
        rows: vec![vec![0]],
    };
    let ct = LeanCiphertext {
        moduli: vec![97],
        degree: 1,
        level: 0,
        variable_time: false,
        polys: vec![zero_poly.clone(), zero_poly],
        plain_bound: 0,
    };
    SignedCt::new(ct, lo, hi, t).expect("the Lean-certified interval is inside the window")
}

#[test]
fn lean_plan_decodes_dispatches_and_malformed_or_drifted_wires_refuse() {
    let plan = lean_rebalance_plan_v1().expect("the checked-in Lean plan must decode canonically");
    assert_eq!(plan.version, 1);
    assert_eq!(plan.kernel_id, "fhir-exact-linear-v1");
    assert_eq!(plan.spec.a, vec![vec![2, 1], vec![1, 2]]);
    assert_eq!(plan.spec.leakage_manifest.dims, 2);
    assert_eq!(plan.spec.leakage_manifest.nnz_a, 4);
    assert_eq!(plan.spec.leakage_manifest.precision_bits, 19);
    assert!(plan.spec.leakage_manifest.public_facts.is_empty());
    assert_eq!(plan.no_wrap.max_abs_intermediate, 1600);
    assert_eq!(plan.no_wrap.final_scale, 81);
    assert_eq!(plan.no_wrap.growth_factor, 2);
    assert_eq!(plan.no_wrap.noise_ceiling, 68);

    // Dispatch the decoded fields—without rebuilding a Rust fhIR Program—through the actual
    // exact-integer FHE consumer. Structurally-valid zero ciphertexts keep this KAT fast while
    // exercising convex_solve's real window/noise/prox gates and interval propagation.
    let t = plan.spec.plaintext_modulus;
    let state = vec![zero_signed(-100, 100, t), zero_signed(-100, 100, t)];
    let out = convex_solve(
        &state,
        &plan.engine_step(),
        plan.spec.prox_lo,
        plan.spec.prox_hi,
        plan.spec.iterations,
        t,
    )
    .expect("the Lean-admitted plan must pass the current consumer's gates");
    assert_eq!(out[0].interval(), (-1600, 1600));
    assert_eq!(out[1].interval(), (-1600, 1600));

    let noncanonical = LEAN_REBALANCE_V1_JSON.replacen(",\"tier\"", ", \"tier\"", 1);
    assert!(decode_canonical_clearing_plan(&noncanonical).is_err());

    let false_certificate = LEAN_REBALANCE_V1_JSON.replacen(
        "\"max_abs_intermediate\":1600",
        "\"max_abs_intermediate\":1599",
        1,
    );
    let err = decode_canonical_clearing_plan(&false_certificate).unwrap_err();
    assert!(err.0.contains("max-absolute-intermediate"), "{err}");

    let wrong_matrix = LEAN_REBALANCE_V1_JSON.replacen("[[2,1],[1,2]]", "[[2,1],[1,3]]", 1);
    assert!(decode_canonical_clearing_plan(&wrong_matrix).is_err());
}
