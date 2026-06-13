//! Criterion bench: TRACE GENERATION (witness gen).
//!
//! Times the two witness-gen stages every EffectVM proof consumes BEFORE the
//! STARK runs:
//!   * `generate_effect_vm_trace` — build the base trace from state + effects.
//!   * `extend_trace_with_hashes` — fill the Poseidon2-aux blocks (the hash
//!     witness). This is the part the perf-report flags as the witness-gen cost,
//!     and a candidate for parallelization.
//!
//! Both are fast (sub-millisecond), so the same input is used SMOKE and FULL;
//! FULL adds the larger effect bundles via the shared `workloads()` ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench trace_gen`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm_p3_full_air::extend_trace_with_hashes;
use dregg_circuit::generate_effect_vm_trace;
use dregg_perf::{regime, workloads};

fn bench_base_trace(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("trace_gen_base/{}", regime()));
    for w in workloads() {
        group.bench_function(w.name, |b| {
            b.iter(|| {
                let (trace, pis) =
                    generate_effect_vm_trace(black_box(&w.initial), black_box(&w.effects));
                black_box((trace, pis));
            });
        });
    }
    group.finish();
}

fn bench_hash_extension(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("trace_gen_hashext/{}", regime()));
    for w in workloads() {
        let (base_trace, _pis) = generate_effect_vm_trace(&w.initial, &w.effects);
        group.bench_function(w.name, |b| {
            b.iter(|| {
                let full = extend_trace_with_hashes(black_box(&base_trace));
                black_box(full);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_base_trace, bench_hash_extension);
criterion_main!(benches);
