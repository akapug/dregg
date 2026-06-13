//! Criterion bench: TRANSFER PROVE.
//!
//! Times the two production EffectVM provers over the same Transfer transition:
//!   * `prove_effect_vm_p3` — the hand-AIR prover the live commit path uses.
//!   * `prove_vm_descriptor` — the verified-by-construction descriptor-interpreter
//!     prover (the Lean-emitted descriptor cutover path).
//!
//! SMOKE (default): the single smallest real turn (`transfer_1effect`).
//! FULL (`PERF_FULL=1`): the 1/4/16-effect ladder for the hand-AIR prover.
//!
//! Run: `cargo bench -p dregg-perf --bench prove`
//! Persvati capture: `PERF_FULL=1 cargo bench -p dregg-perf --bench prove`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::effect_vm_p3_full_air::prove_effect_vm_p3;
use dregg_circuit::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};
use dregg_perf::{build_trace, regime, single_transfer, workloads};

/// The hand-AIR prover — the live default path.
fn bench_prove_hand_air(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("prove_hand_air/{}", regime()));
    // Proving is seconds-scale; keep the sample count modest.
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

/// The verified descriptor-interpreter prover for the canonical Transfer.
/// selector 1 = TRANSFER (the validated cutover-ready descriptor).
fn bench_prove_descriptor(c: &mut Criterion) {
    let Some(json) = descriptor_for_selector(1) else {
        eprintln!("prove_descriptor: no transfer descriptor registered — skipped");
        return;
    };
    let desc = parse_vm_descriptor(json).expect("parse transfer descriptor");
    let (st, effs) = single_transfer();
    let (trace, full_pis) = build_trace(&dregg_perf::Workload {
        name: "transfer_1effect",
        initial: st,
        effects: effs,
    });
    let dpis = full_pis[..desc.public_input_count].to_vec();

    let mut group = c.benchmark_group(format!("prove_descriptor/{}", regime()));
    group.sample_size(10);
    group.bench_function("transfer_1effect", |b| {
        b.iter(|| {
            let proof = prove_vm_descriptor(black_box(&desc), black_box(&trace), black_box(&dpis))
                .expect("descriptor prove");
            black_box(proof);
        });
    });
    group.finish();
}

criterion_group!(benches, bench_prove_hand_air, bench_prove_descriptor);
criterion_main!(benches);
