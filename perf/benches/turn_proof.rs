//! Criterion bench for the PRODUCTION turn-proof path.
//!
//! Times `prove_effect_vm_p3` and `verify_effect_vm_p3` — the audited Plonky3
//! prover/verifier the SDK routes a turn's Effect-VM state transition through —
//! over honest Effect-VM traces. This is the "how long does a real turn take to
//! prove?" number the product assessment needs, measured (not estimated).
//!
//! Run: `cargo bench -p dregg-perf --bench turn_proof`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm_p3_full_air::{prove_effect_vm_p3, verify_effect_vm_p3};
use dregg_perf::{build_trace, workloads};

fn bench_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group("turn_prove");
    // Proving is seconds-scale; keep the sample count modest so the wall-clock
    // budget stays reasonable.
    group.sample_size(10);
    for w in workloads() {
        let (trace, pis) = build_trace(&w);
        group.bench_function(w.name, |b| {
            b.iter(|| {
                let proof = prove_effect_vm_p3(black_box(&trace), black_box(&pis))
                    .expect("honest turn must prove");
                black_box(proof);
            });
        });
    }
    group.finish();
}

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("turn_verify");
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

criterion_group!(benches, bench_prove, bench_verify);
criterion_main!(benches);
