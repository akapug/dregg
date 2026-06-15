//! Criterion bench: PROOF VERIFY.
//!
//! Times `verify_full_turn` — the self-sovereign turn verifier the light client
//! runs — on a pre-built honest proof. Verify is the light side of the system
//! and the dominant cost a LIGHT CLIENT pays, so it is benchmarked separately
//! from prove. Under the `recursion` default the verified leg is the rotated
//! IR-v2 descriptor chain (not the v1 hand-AIR).
//!
//! SMOKE (default): verify the `transfer_1effect` proof.
//! FULL (`PERF_FULL=1`): verify across the 1/4/16-effect ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench verify`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm::pi;
use dregg_perf::{build_trace, regime, workloads};
use dregg_sdk::{prove_turn_self_sovereign, verify_full_turn};

const TURN_HASH: [u8; 32] = [7u8; 32];

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("verify/{}", regime()));
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

criterion_group!(benches, bench_verify);
criterion_main!(benches);
