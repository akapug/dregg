//! Criterion bench for the PRODUCTION turn-proof path.
//!
//! Times `prove_turn_self_sovereign` and `verify_full_turn` — the real
//! self-sovereign commit-path entry the node drives (under the `recursion`
//! default the Effect-VM leg proves through the rotated IR-v2 descriptor tower,
//! NOT the v1 hand-AIR) — over honest transfer turns. This is the "how long does
//! a real turn take to prove?" number the product assessment needs, measured
//! (not estimated).
//!
//! Run: `cargo bench -p dregg-perf --bench turn_proof`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm::pi;
use dregg_perf::{build_trace, workloads};
use dregg_sdk::{prove_turn_self_sovereign, verify_full_turn};

const TURN_HASH: [u8; 32] = [7u8; 32];

fn bench_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group("turn_prove");
    // Proving is seconds-scale; keep the sample count modest so the wall-clock
    // budget stays reasonable.
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

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("turn_verify");
    for w in workloads() {
        let (_trace, pis) = build_trace(&w);
        let old_commit = pis[pi::OLD_COMMIT];
        let new_commit = pis[pi::NEW_COMMIT];
        let proof = prove_turn_self_sovereign(&w.initial, &w.effects, TURN_HASH)
            .expect("honest turn must prove");
        group.bench_function(w.name, |b| {
            b.iter(|| {
                verify_full_turn(black_box(&proof), old_commit, new_commit)
                    .expect("honest proof must verify");
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_prove, bench_verify);
criterion_main!(benches);
