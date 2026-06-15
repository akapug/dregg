//! Criterion bench: TRANSFER PROVE.
//!
//! Times the LIVE EffectVM proving paths over the canonical Transfer transition:
//!   * `prove_vm_descriptor` — the verified-by-construction descriptor-interpreter
//!     prover (the Lean-emitted descriptor the rotated IR-v2 commit tower descends
//!     from). This is the EffectVM sub-proof number.
//!   * `prove_turn_self_sovereign` — the real self-sovereign commit-path entry the
//!     node drives (EffectVM leg + PI-binding main proof). This is the full real
//!     turn number, over the workload ladder.
//!
//! (The v1 hand-AIR `prove_effect_vm_p3` is the `not(recursion)` wasm floor and is
//! retired here — under the `recursion` default it is absent.)
//!
//! SMOKE (default): the single smallest real turn (`transfer_1effect`).
//! FULL (`PERF_FULL=1`): the 1/4/16-effect ladder for the full-turn prover.
//!
//! Run: `cargo bench -p dregg-perf --bench prove`
//! Persvati capture: `PERF_FULL=1 cargo bench -p dregg-perf --bench prove`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};
use dregg_perf::{build_trace, regime, single_transfer, workloads};
use dregg_sdk::prove_turn_self_sovereign;

const TURN_HASH: [u8; 32] = [7u8; 32];

/// The full self-sovereign turn prover — the real commit path the node drives.
fn bench_prove_full_turn(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("prove_full_turn/{}", regime()));
    // Proving is seconds-scale; keep the sample count modest.
    group.sample_size(10);
    for w in workloads() {
        group.bench_function(w.name, |b| {
            b.iter(|| {
                let proof = prove_turn_self_sovereign(
                    black_box(&w.initial),
                    black_box(&w.effects),
                    TURN_HASH,
                )
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

criterion_group!(benches, bench_prove_full_turn, bench_prove_descriptor);
criterion_main!(benches);
