//! Smoke driver for the v2 multi-limb cross-cell conservation AIR (wrap-class fix #3).
//! Exercises the public API end-to-end (the crate's lib test target is pre-existing-broken by
//! unrelated modules, so this example is the empirical witness). Run:
//!   cargo run -p dregg-circuit --example ccc_smoke

use dregg_circuit::cross_cell_conservation_air::*;
use dregg_circuit::field::BabyBear;

fn delta(asset: u32, mag: u32, credit: bool) -> CrossCellDelta {
    CrossCellDelta {
        asset: BabyBear::new(asset),
        magnitude: mag,
        credit,
    }
}

fn is_unsat(trace: &[Vec<BabyBear>], pi: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_cross_cell_conservation(trace, pi)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(proof)) => verify_cross_cell_conservation(&proof, pi).is_err(),
    }
}

fn main() {
    std::panic::set_hook(Box::new(|_| {})); // quiet the expected unsat panic

    // shape
    let d = cross_cell_conservation_descriptor();
    assert_eq!(d.name, "dregg-cross-cell-conservation-v2");
    assert_eq!(d.trace_width, 172);
    assert_eq!(d.constraints.len(), 201);
    println!(
        "shape OK: width={} constraints={} name={}",
        d.trace_width,
        d.constraints.len(),
        d.name
    );

    // LIVENESS: honest matched transfer proves
    let honest = vec![delta(7, 10, false), delta(7, 10, true)];
    let (t, pi) = build_cross_cell_conservation_trace(&honest);
    let proof = prove_cross_cell_conservation(&t, &pi).expect("honest must prove");
    verify_cross_cell_conservation(&proof, &pi).expect("honest must verify");
    let mut bad = pi.clone();
    bad[0] = bad[0] + BabyBear::ONE;
    assert!(verify_cross_cell_conservation(&proof, &bad).is_err());
    println!("LIVENESS OK: honest A-10,B+10 proves+verifies; wrong-asset PI rejects");

    // LIVENESS beyond p: balanced total 2^31 > p proves (v1 would have wrapped)
    let big = 1_073_741_823u32;
    let turn = vec![
        delta(7, big, true),
        delta(7, big, true),
        delta(7, big, false),
        delta(7, big, false),
    ];
    let (t2, pi2) = build_cross_cell_conservation_trace(&turn);
    let p2 = prove_cross_cell_conservation(&t2, &pi2).expect("balanced >p must prove");
    verify_cross_cell_conservation(&p2, &pi2).expect("must verify");
    println!("LIVENESS>p OK: balanced per-asset total ~2^31 (>p) proves under multi-limb");

    // SOUNDNESS: the p-sum forgery is UNSAT
    let (m1, m2) = (1_006_632_961u32, 1_006_632_960u32);
    assert_eq!(m1 as u64 + m2 as u64, 2_013_265_921);
    let forged = vec![delta(7, m1, true), delta(7, m2, true)];
    assert_eq!(cross_cell_balance(&forged), 2_013_265_921);
    let (ft, fpi) = build_cross_cell_conservation_trace(&forged);
    let last = ft.last().unwrap();
    assert_eq!(last[CCC_C0], BabyBear::new(1));
    assert_eq!(last[CCC_C1], BabyBear::new(28672));
    assert_eq!(last[CCC_C2], BabyBear::new(1));
    assert_eq!(last[CCC_D0], BabyBear::ZERO);
    assert!(is_unsat(&ft, &fpi), "p-sum forgery MUST be unsat");
    println!(
        "SOUNDNESS OK: p-sum forgery (1006632961+1006632960=p) credit limbs=(1,28672,1)!=(0,0,0)=debit => UNSAT"
    );

    // unbalanced unsat + disclosed-mint proves
    let (ut, upi) =
        build_cross_cell_conservation_trace(&vec![delta(7, 10, false), delta(7, 999, true)]);
    assert!(is_unsat(&ut, &upi));
    let (dt, dpi) = build_cross_cell_conservation_trace(&vec![
        delta(7, 10, false),
        delta(7, 999, true),
        delta(7, 989, false),
    ]);
    let dp = prove_cross_cell_conservation(&dt, &dpi).expect("disclosed-mint must prove");
    verify_cross_cell_conservation(&dp, &dpi).expect("verify");
    println!("SOUNDNESS OK: unbalanced UNSAT; disclosed-supply row conserves+proves");

    println!("ALL CCC v2 CHECKS PASSED");
}
