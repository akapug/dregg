//! Criterion bench: PROOF VERIFY.
//!
//! Times `verify_effect_vm_p3` — the audited Plonky3 verifier — on a pre-built
//! honest proof. Verify is the light side of the system and the dominant cost a
//! LIGHT CLIENT pays, so it is benchmarked separately from prove.
//!
//! SMOKE (default): verify the `transfer_1effect` proof.
//! FULL (`PERF_FULL=1`): verify across the 1/4/16-effect ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench verify`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm_p3_full_air::{prove_effect_vm_p3, verify_effect_vm_p3};
use dregg_perf::{build_trace, regime, workloads};

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("verify/{}", regime()));
    for w in workloads() {
        let (trace, pis) = build_trace(&w);
        let proof = prove_effect_vm_p3(&trace, &pis).expect("honest turn must prove");
        group.bench_function(w.name, |b| {
            b.iter(|| {
                verify_effect_vm_p3(black_box(&proof), black_box(&pis))
                    .expect("honest proof must verify");
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_verify);
criterion_main!(benches);
