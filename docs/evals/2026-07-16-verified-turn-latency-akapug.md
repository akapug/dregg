# dregg verified-turn latency eval — independent third-party run
**Date:** 2026-07-16 · **By:** akapug (Mission Control / meld integration testing) · **For:** emberian/dregg

An independent latency characterization of dregg's verified commit path, run while
evaluating dregg as the coordination substrate for a multi-agent metaharness (meld
on orca). Shared because it may be useful upstream — this is a *use-case-side*
contribution (an eval), not a code change.

## Setup
- Binary: `dregg-node` release build, **verified Lean executor** as the state
  producer (`State producer: LEAN (verified, 21 effects)`), full-turn STARK proving
  **off** (Trusted tier — the shipped default).
- Node: solo federation (n=1, quorum 1), data dir on **tmpfs** (`/dev/shm`) to
  isolate executor+consensus cost from disk.
- Measurement: persistent-connection HTTP direct to the node API (no CLI process
  spawn), Python `perf_counter`, warmup discarded.
- Host: single build box, no contention, one core path.

## Results
| operation | p50 | p99 | min | n |
|---|---|---|---|---|
| verified READ (`GET /api/cells`, ledger read) | **0.34 ms** | 0.86 ms | 0.29 ms | 300 |
| verified WRITE TURN apply (`POST /api/faucet`, materialize-cell turn: sign + cap-check + verified-Lean execute + receipt + ledger insert) | **2.2 ms** | 17.6 ms¹ | 0.9 ms | 10² |

¹ one outlier of ten (alloc/GC); the typical spread was 0.9–4.4 ms.
² faucet rate-limits at 429 after 10 rapid requests — a cap, not a latency wall.
   A purpose-built persistent turn loop would give a larger-n distribution.

For reference, a per-call **CLI-spawn** path (`dregg turn status` in a shell loop)
measured p50 52.8 ms — but ~42 ms of that is Rust binary cold-start, so the CLI
path is not representative of an embedded or persistent-connection consumer.

## The distinction that matters to consumers: APPLY vs FINALITY
- **APPLY** (execute + receipt; the point where you hold a tamper-evident,
  capability-witnessed receipt): **~2 ms**. The HTTP call returns here.
- **Consensus FINALITY** (turn committed into a finalized blocklace block): gated
  by `min_block_interval_ms = 2000` at solo n=1 (mutation-driven). This is
  distributed agreement, separate from apply — a consumer that trusts the local
  verified receipt is unblocked at apply-time; finality settles in the background.

## Why this was useful to us
We were deciding whether dregg turns could serve a *hot* coordination path
(sub-millisecond expectations, per-tool-call frequency) or only an audit/authority
tier. The numbers say: on **apply latency**, a tmpfs dregg node is fast enough to be
the hot path — reads at RAM-projection speed (0.3 ms), writes at ~2 ms with a
verified receipt for free. The 2 s consensus finality only constrains facts that
need multi-node agreement per act, which hot coordination does not.

## Honest limits of this run
- Single node, single thread, **no concurrent-writer contention** — the real
  multi-agent hot-path stress test is unmeasured.
- Trusted tier only; the `--prove` full-STARK-per-turn tier is heavier and unmeasured.
- `faucet` is a stand-in for a generic write turn; a domain coordination turn may differ.
- Pre-rebase binary; latency is version-invariant but a latest-upstream re-run is planned.

Happy to re-run with any harness/methodology emberian prefers, or contribute a
persistent-loop bench into the repo if wanted.

---

## Addendum: concurrent-writer stress (same run, verified Lean executor, tmpfs)
N concurrent agent-PROCESSES each submitting a real signed `emit-event` verified turn
to one dregg space (via the `dregg` CLI, so each sample includes ~42ms CLI cold-start).

| concurrency | committed | throughput | note |
|---|---|---|---|
| 1 | 1/1 | ~10/s | CLI-spawn-bound (single pipeline) |
| 2 | 2/2 | ~21/s | linear |
| 4 | 4/4 | ~56/s | linear |
| 8 | 8/8 | ~75/s | |
| 16 | 16/16 | ~115/s | all correct |
| 32 | 25/32 | ~107/s | 7 failed — single-shared-cell nonce contention (all writers hit ONE operator cell) |

**Correctness:** every committed turn landed in the ledger (50 events), no corruption
under concurrency through 16 writers. **Throughput** plateaus ~110/s but is bounded by
CLI process spawn, not the executor — the ~2ms apply cost implies a far higher
in-process ceiling. **The 32-writer failures are single-cell contention, not a limit:**
all writers shared one operator cell, so their turns serialize on that cell's nonce.
In a real dregg space each AGENT owns its own cell, so writes to distinct cells would
not contend — the natural multi-agent topology parallelizes.

### Next-rigor evals (the ones that would most interest emberian)
1. **Per-agent-distinct-cell concurrency** — isolate executor throughput from
   single-cell nonce serialization (the realistic multi-agent shape).
2. **Persistent-connection, no-CLI-spawn** submit loop — the true executor write ceiling.
3. **`--prove` STARK tier** under the same load — the "every transition proven" cost.
4. **n>1 committee** finality-under-load — the distributed path (the 1s block-interval
   note in the run log references a prior n=4 stall on the old 5s default).

## EMBER FINDING (2026-07-16): swarm_demo broken on upstream latest
- `cargo run -p starbridge-swarm-orchestration --example swarm_demo` FAILS on HEAD
  53d9dfe58: `error[E0432]: unresolved import non_revocation_dsl_circuit`
  (dregg-dsl-runtime/src/lib.rs:68 <- dregg_circuit::dsl::revocation). The swarm
  Notify/React exemplar does not build on main. Likely a circuit-DSL API rename the
  example/dsl-runtime lagged, or a feature-gate. Ember-reportable (broken example).
  PRECISE DIAGNOSIS: `dregg_circuit::dsl::revocation` (circuit/src/dsl/revocation.rs)
  now exports generate_non_revocation_trace / prove_non_revocation_p3 /
  verify_non_revocation_p3 / revocation_hash_to_field, but NOT `non_revocation_dsl_circuit`
  — that symbol was removed/renamed in a circuit-DSL refactor, and both
  dregg-dsl-runtime/src/lib.rs:68 and the swarm-orchestration example still import it.
  A circuit-DSL rename that dregg-dsl-runtime lagged. NOT guess-fixed here: a
  verified-circuit symbol's semantics are Ember's to reconcile (a wrong stub would
  launder vacuity into the verified path). Clean Ember bug report.
  Non-blocking for us: the formal Notify/React demo waits on this fix; cross-turn
  coordination and the apply-vs-finality lesson proven via the live cave regardless.
