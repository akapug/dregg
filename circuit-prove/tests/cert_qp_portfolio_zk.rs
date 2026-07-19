use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::cert_qp_air::{
    A, CertQpWitness, EPSILON, L, MC, N, P, Q, SCALE_DIGITS, U, prove_cert_qp_zk,
    try_cert_qp_descriptor, verify_cert_qp_zk,
};
use fhegg_solver::qp::{CertQp, solve_admm};
use fhegg_solver::qp_exact::lift_cert;
use fhir::{ConvexProgram, compile, products};

fn solved_registered_portfolio() -> CertQpWitness {
    let compiled = compile(&products::portfolio_qp_public()).expect("real fhIR product compiles");
    let ConvexProgram::Qp(prob) = compiled.program else {
        panic!("portfolio_qp_public must lower to QP");
    };
    let result = solve_admm(&prob, 6000, 1.0, 1e-6, 1.6);
    let f64_cert = CertQp::from_solution(&prob, &result, 1e-3);
    let exact = lift_cert(&f64_cert, SCALE_DIGITS).expect("rounded fixed-point lift");
    assert!(
        exact.check().valid,
        "the actual fhIR solve must certify at the registered rounded scale: {:?}",
        exact.check()
    );
    let witness = CertQpWitness {
        n: exact.n,
        mc: exact.mc,
        scale: exact.scale,
        p: exact.p,
        q: exact.q,
        a: exact.a,
        l: exact.l,
        u: exact.u,
        x: exact.x,
        y: exact.y,
        epsilon: exact.epsilon,
    };
    assert_eq!(witness.n, N);
    assert_eq!(witness.mc, MC);
    assert_eq!(witness.p, P);
    assert_eq!(witness.q, Q);
    assert_eq!(witness.a, A);
    assert_eq!(witness.l, L);
    assert_eq!(witness.u, U);
    assert_eq!(witness.epsilon, EPSILON);
    witness
}

#[test]
fn real_portfolio_all_three_clauses_prove_hiding_and_bind_public_return() {
    let cert = solved_registered_portfolio();
    let check = cert.check().expect("registered");
    assert!(check.primal && check.stationarity && check.normal_cone && check.valid);

    let (desc, proof, pis) =
        prove_cert_qp_zk(&cert).expect("valid exact KKT witness proves through HidingFriPcs");
    assert_eq!(desc.name, "cert-qp-portfolio6-s3");
    assert_eq!(desc.trace_width, 123);
    assert_eq!(pis, cert.public_inputs().unwrap());
    assert!(
        proof.commitments.random.is_some(),
        "HidingFriPcs proof carries its random-polynomial commitment"
    );
    verify_cert_qp_zk(&desc, &proof, &pis).expect("hiding proof verifies without x,y");

    let mut drifted_desc = desc.clone();
    drifted_desc.name.push_str("-forged");
    assert!(
        verify_cert_qp_zk(&drifted_desc, &proof, &pis).is_err(),
        "verification refuses descriptor/program drift as well as proving"
    );

    let mut forged_pis = pis.clone();
    forged_pis[0] += BabyBear::ONE;
    assert!(
        verify_cert_qp_zk(&desc, &proof, &forged_pis).is_err(),
        "the public expected-return result is proof-bound"
    );
}

#[test]
fn program_drift_and_each_load_bearing_clause_refuse() {
    let cert = solved_registered_portfolio();

    let mut drift = cert.clone();
    drift.p[0] += 1;
    assert!(try_cert_qp_descriptor(&drift).is_err());

    let mut primal_bad = cert.clone();
    primal_bad.x[0] += 10;
    let p = primal_bad.check().unwrap();
    assert!(!p.primal && !p.valid);
    assert!(prove_cert_qp_zk(&primal_bad).is_err());

    // Budget-row dual is free in the projection clause (l=u), so changing only
    // y0 isolates stationarity while leaving primal + normal cone untouched.
    let mut stationarity_bad = cert.clone();
    stationarity_bad.y[0] += 2;
    let s = stationarity_bad.check().unwrap();
    assert!(
        s.primal && !s.stationarity && s.normal_cone && !s.valid,
        "{s:?}"
    );
    assert!(prove_cert_qp_zk(&stationarity_bad).is_err());

    // A null direction of A^T: y0 += d and every box dual -= d.  Stationarity
    // is unchanged exactly, while the box projection/normal-cone signs break.
    let mut normal_bad = cert.clone();
    normal_bad.y[0] += 100;
    for y in &mut normal_bad.y[1..] {
        *y -= 100;
    }
    let n = normal_bad.check().unwrap();
    assert!(
        n.primal && n.stationarity && !n.normal_cone && !n.valid,
        "{n:?}"
    );
    assert!(prove_cert_qp_zk(&normal_bad).is_err());
}
