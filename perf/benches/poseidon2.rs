//! Criterion bench: POSEIDON2 PERMUTATION.
//!
//! Times the SNARK-friendly hash primitive that dominates the EffectVM aux
//! witness-gen and every cell commitment:
//!   * one width-16 BabyBear permutation (`Poseidon2State::permute`).
//!   * the `hash_2_to_1` compression (Merkle node) and the `hash_many` sponge.
//!
//! The permutation is fixed-cost (nanoseconds), so SMOKE == FULL input; FULL
//! only changes the larger sponge length to show absorb scaling.
//!
//! Run: `cargo bench -p dregg-perf --bench poseidon2`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{Poseidon2State, WIDTH, hash_2_to_1, hash_many};
use dregg_perf::{perf_full, regime};

fn bench_permute(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("poseidon2/{}", regime()));

    // One full width-16 permutation.
    let elems: Vec<BabyBear> = (0..WIDTH as u32).map(BabyBear::new).collect();
    group.bench_function("permute_width16", |b| {
        b.iter(|| {
            let mut state = Poseidon2State::from_elements(black_box(&elems));
            state.permute();
            black_box(state);
        });
    });

    // 2->1 compression (the Merkle-node hash).
    let l = BabyBear::new(0xABCDE);
    let r = BabyBear::new(0x12345);
    group.bench_function("hash_2_to_1", |b| {
        b.iter(|| black_box(hash_2_to_1(black_box(l), black_box(r))));
    });

    // Sponge over a vector — SMOKE: 8 elems, FULL: 64 elems (absorb scaling).
    let n = if perf_full() { 64 } else { 8 };
    let inputs: Vec<BabyBear> = (0..n as u32).map(BabyBear::new).collect();
    group.bench_function(format!("hash_many_{n}"), |b| {
        b.iter(|| black_box(hash_many(black_box(&inputs))));
    });

    group.finish();
}

criterion_group!(benches, bench_permute);
criterion_main!(benches);
