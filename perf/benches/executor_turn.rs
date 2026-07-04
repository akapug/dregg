//! Criterion bench: EXECUTOR TURN.
//!
//! Times the live Rust `TurnExecutor::execute` — the executor entry the node
//! drives — over a real single-Transfer turn against a `Ledger` with two open
//! cells. This is the NON-proof hot path: state lookup, authorization gating,
//! effect application, receipt + commitment. It is cheap (microseconds-scale),
//! so the same input is used for SMOKE and FULL.
//!
//! NOTE: a fresh `Ledger` + `Turn` is rebuilt per iteration so each `execute`
//! runs against an unmutated state (the executor mutates the ledger in place).
//!
//! Run: `cargo bench -p dregg-perf --bench executor_turn`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::{executor_transfer_turn, fresh_executor, regime};

fn bench_executor_turn(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("executor_turn/{}", regime()));
    let executor = fresh_executor();
    group.bench_function("transfer_open_cells", |b| {
        b.iter_batched(
            // setup: fresh ledger + turn each iter (execute mutates the ledger).
            executor_transfer_turn,
            |(mut ledger, turn)| {
                let result = executor.execute(black_box(&turn), black_box(&mut ledger));
                debug_assert!(result.is_committed(), "honest open-cell turn must commit");
                black_box(result);
            },
            criterion::BatchSize::SmallInput,
        );
    });
    group.finish();
}

criterion_group!(benches, bench_executor_turn);
criterion_main!(benches);
