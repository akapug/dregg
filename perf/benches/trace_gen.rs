//! Criterion bench: TRACE GENERATION (witness gen).
//!
//! Times the two witness-gen stages every EffectVM proof consumes BEFORE the
//! STARK runs:
//!   * `generate_effect_vm_trace` — build the base trace from state + effects.
//!   * `descriptor_recursion_matrix` — extend the base trace into the FULL
//!     descriptor-AIR-width matrix (base wires + Poseidon2 site-aux blocks +
//!     range bits), exactly as `prove_vm_descriptor` does before proving. This is
//!     the witness surface the LIVE rotated/descriptor proof consumes (the v1
//!     `extend_trace_with_hashes` hand-AIR extension is the `not(recursion)`
//!     floor, retired here).
//!
//! Both are fast (sub-millisecond), so the same input is used SMOKE and FULL;
//! FULL adds the larger effect bundles via the shared `workloads()` ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench trace_gen`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::generate_effect_vm_trace;
use dregg_circuit::lean_descriptor_air::{descriptor_recursion_matrix, parse_vm_descriptor};
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

fn bench_witness_extension(c: &mut Criterion) {
    // selector 1 = TRANSFER — the validated descriptor; every workload here is a
    // transfer ladder, so the same descriptor extends each base trace.
    let Some(json) = descriptor_for_selector(1) else {
        eprintln!("trace_gen witness-ext: no transfer descriptor registered — skipped");
        return;
    };
    let desc = parse_vm_descriptor(json).expect("parse transfer descriptor");

    let mut group = c.benchmark_group(format!("trace_gen_witness_ext/{}", regime()));
    for w in workloads() {
        let (base_trace, _pis) = generate_effect_vm_trace(&w.initial, &w.effects);
        group.bench_function(w.name, |b| {
            b.iter(|| {
                let full = descriptor_recursion_matrix(black_box(&desc), black_box(&base_trace))
                    .expect("descriptor witness extension");
                black_box(full);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_base_trace, bench_witness_extension);
criterion_main!(benches);
