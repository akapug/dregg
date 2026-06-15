# pg-dregg benchmarks — what a verified turn costs

This is the authoritative, **measured** performance record for `pg-dregg` — the
numbers behind the "DBOS, but every step is a verified turn" pitch. Every figure
here is produced by `cargo bench` (criterion) or the `loadgen` binary over the
**postgres-free cores**, i.e. the *algorithmic* cost of the verification itself,
isolated from any pg / SPI / IPC overhead. That is the honest thing to quote for
"what does the verification cost", and it is the number a deployment's per-row
latency and per-turn throughput actually ride on. The live-pg path adds the
SPI round-trip and the `MERGE` applicator on top (exercised by
`cargo pgrx test pg18` + `scripts/e2e-live.sh`); those are explicitly NOT in
these figures and are called out where relevant.

> **Reproduce:** `cd pg-dregg && cargo bench` (the criterion groups) and
> `cargo run --release --bin loadgen -- --secs 3 --agents 8 --latency` (the
> sustained-spine rate). Both build the default (empty) feature set — no pgrx, no
> executor — so they run anywhere with a Rust toolchain, no postgres required.

## Measurement environment

| | |
|---|---|
| machine | Apple M2 Max (12 cores), single-threaded benches |
| toolchain | `rustc 1.94.0-nightly`, release profile (`opt-level=3`, `lto="thin"`) |
| date | 2026-06-15 |
| crate | `pg-dregg` 0.1.0, default features (postgres-free cores) |
| harness | criterion 0.5 (100 samples/group, 3 s warmup) + `bin/loadgen` |

Criterion reports a `[lo  median  hi]` confidence interval per measurement; the
tables below quote the **median**. Run-to-run variation on this machine is a few
percent (visible in the raw `cargo bench` output); the figures are stable to the
significant digits shown.

---

## 1. The headline numbers

| path | what it is | latency (median) | throughput |
|---|---|---|---|
| **`submit_decision/hot_lru_reeval`** | the verified-WRITE gate, **per row, LRU warm** (the steady state) | **1.63 µs** | **614 K admissions/s** |
| `submit_decision/cold_full_chain_verify` | the verified-write gate, cold (full ed25519 chain verify) | 55.1 µs | 18.1 K/s |
| **`read_projection/rls_filter_rows`** | the cap-gated RLS **read**, per candidate row, hot | **1.70 µs/row** | **590 K rows/s** |
| `chain_gate/verify_chain_step` | the anti-substitution tooth (the Tier-C trigger gate) | **3.94 ns** | 254 M ops/s |
| `chain_gate/rootchain_extend` | the full chain-gate a `MirrorBatch` apply pays | 4.64 ns | 215 M ops/s |
| `mirror_apply/from_parts_assemble` | assemble + well-formedness gate one verified turn | 631 ns | 1.59 M/s |
| `mirror_apply/ingest_story_chain` | ingest a 4-turn mirror from genesis (per turn) | 26.7 ns | 150 M turns/s |
| `mirror_serde/encode_batch` | the node↔pg wire codec (encode) | 3.26 µs | 830 MiB/s |
| `mirror_serde/decode_batch` | the node↔pg wire codec (decode) | 9.29 µs | 291 MiB/s |
| `mirror_serde/cells_json` | the Tier-C trigger payload per batch | 11.4 µs | 87.6 K/s |
| **`workflow/run_durable_steps/128`** | a full durable-workflow run, **every step checkpointed** | **6.73 µs/step** | **149 K turns/s** |
| `workflow/crash_recover_resume` | crash → recover (re-validate whole chain) → resume tail, exactly-once (64-step) | 517 µs | 124 K turns/s |
| **`drain_spine/drain_intents/128`** | the **write-outbox drain**: N intents through SUBMIT→PRODUCE→CHAIN | **3.64 µs/turn** | **275 K turns/s** |

The hot per-row write gate is **~1.6 µs** because a warm verified-credential LRU
pays the ed25519 chain verify **once per token**, then each row re-evaluates only
the first-party caveats off the *cached, decoded* credential — the per-row cost is
a revocation-set lookup + a caveat eval, not a fresh decode or a signature check.
The cold path (a cache miss / first row of a new token) is **~34× more** because
it pays the full signature-chain verify.

The chain tooth is **effectively free** (~4 ns): it is a 32-byte equality + an
ordinal compare. The expensive, marketable work is the **capability decision**;
the anti-substitution discipline that makes the writes unforgeable adds almost
nothing on top.

---

## 2. THE marketable comparison — `dregg_admits` vs a hand-rolled SQL policy

The single most-asked question when pitching dregg capabilities as RLS: *what
does the verified gate cost versus the owner/expiry/revoked predicate I'd write
by hand?* The `gate_vs_handrolled` group answers it on the per-row decision axis.

The hand-rolled baseline is the Rust equivalent of the policy a developer writes
*without* dregg:

```sql
-- the naive hand-rolled RLS USING clause:
USING (owner_of(resource) = current_user        -- an ACL membership check
       AND expires_at > now()                     -- an expiry compare
       AND id NOT IN (SELECT id FROM revoked))    -- a revocation lookup
```

modeled as a string-prefix extract + a `HashSet` membership + an integer compare
+ a `HashSet` revocation lookup — a fair model of the *work* a hand-coded RLS
predicate does per candidate row (the planner inlines it; the cost is the
comparisons, not IPC). The dregg side is `authz::decide(token, "read", resource,
now)` with a **warm LRU** — the realistic large-scan steady state. Both policies
admit the **same rows** (so neither short-circuits on a denial — a fair cost
comparison).

| policy | per-row (n=1000) | throughput | what it guarantees |
|---|---|---|---|
| **`handrolled_acl`** | **~15 ns/row** | ~65 M rows/s | a plaintext owner/expiry/revoked compare |
| **`dregg_admits`** | **~1.80 µs/row** | ~556 K rows/s | an unforgeable, attenuable, instantly-revocable **capability** decision |

(At n=100 the figures are the same per-row: `handrolled_acl` ~14 ns/row, ~71 M/s;
`dregg_admits` ~1.80 µs/row, ~554 K/s — the per-row cost is flat in the scan size,
as it should be.)

So the verified gate costs **~120× more per row** than a naive ACL string-compare.
**That ratio is the whole point of the benchmark, and the framing matters:** this
is *not* apples-to-apples on **guarantees**. The hand-rolled ACL is a plaintext
comparison a bug, a stale cache, or an SQL-injection can bypass; it has no
attenuation (no "this delegate can do strictly less than I can", proven) and no
cryptographic unforgeability (a row owner is just a string the app trusts). The
dregg gate is a verified capability decision: a forged token is refused
(`forged_token_is_denied_fail_closed`), an attenuated child's authority is a
provable subset of its parent's (`attenuation_narrows_through_the_core` + the
`proptest_authz` no-amplify fuzz), and a revocation lands on the **very next row**
(`instant_revocation_denies_on_the_next_check`). The ~1.8 µs buys those
properties. At 556 K cap-gated rows/sec on one core, that is a price almost every
read-path can pay — and the comparison exists so the overhead is *legible*, not
hidden.

> The `cold_full_chain_verify` row (55 µs) is what the per-row cost would be
> *without* the LRU — i.e. if you re-verified the ed25519 chain on every row. The
> mandatory verified-credential LRU is exactly what collapses that to the 1.6 µs
> hot path; this is why the LRU is not optional in M1.

---

## 3. The DBOS-shaped path — durable workflow + crash recovery

`workflow/*` measures the end-to-end path a DBOS user actually rides: a multi-step
durable workflow driven through the **whole verified-write spine** (the API
`examples/supply_chain` and `examples/subscription_billing` are built on), and the
crash → recover → resume cycle that is DBOS's headline feature.

| measurement | cost | per-turn |
|---|---|---|
| `run_durable_steps/16` | ~416 µs (16 steps) | ~26 µs/step |
| `run_durable_steps/128` | ~862 µs (128 steps) | **~6.7 µs/step** |
| `crash_recover_resume` | ~517 µs (64-step: recover all + resume tail) | ~8 µs/turn re-validated |

A **verified, durable, checkpointed** workflow step costs **~6.7 µs** at depth 128
(the per-step cost falls with depth as the warm LRU amortizes). That is the number
to put next to DBOS's per-step checkpoint: pg-dregg's step is *also* a verified
turn (unforgeable + conserving + attenuated + receipted), and it still runs at
**~149 K steps/sec** on one core.

Crash recovery re-validates the *entire* persisted chain on the way up (a restored
store is self-checking — `recovery_of_a_tampered_log_fails_closed` proves a
substituted root is caught), then resumes the uncommitted tail exactly-once. The
64-step recover-and-resume is **~517 µs total** — the cost of surviving a crash,
which is the thing DBOS sells, here with the chain re-validation included.

---

## 4. The two write surfaces — engine-driven vs outbox-drained

pg-dregg has two realizable verified-write paths, and both are benched:

* **`workflow/*`** — the in-process `WorkflowEngine` drives steps directly (the
  embedded / library shape, `examples/*`). ~6.7 µs/step.
* **`drain_spine/*`** — the node-side `Drainer` pulls intents off the submit
  outbox (`dregg.submit_queue`) and runs each through the four-gate spine
  (SUBMIT re-check → PRODUCE → CHAIN → advance) — the queue-drain deployment shape
  `dregg_drain_once` exercises against live pg.

| measurement | cost | per-turn | throughput |
|---|---|---|---|
| `drain_spine/drain_intents/16` | ~108 µs (16 intents) | ~6.75 µs/turn | ~148 K turns/s |
| `drain_spine/drain_intents/128` | ~465 µs (128 intents) | **~3.64 µs/turn** | **~275 K turns/s** |

Both surfaces land in the same few-µs-per-turn regime, dominated by the capability
decision (amortized by the LRU). The drainer's PRODUCE gate here is the
deterministic, value-conserving `FoldProducer` stand-in (the postgres-free core
ships it so every *other* gate — the submit re-check, the chain admission, the
mirror — is proven without the executor in the build); a real deployment supplies
the verified Lean executor at that seam (`docs/PG-DREGG-TIER-D-SPIKE.md`). The
PRODUCE-gate cost in production is the executor's turn cost, which is a separate
measurement (the executor lane); the spine plumbing this group measures is the
realizable per-turn overhead the drain adds around it.

---

## 5. End-to-end sustained rate (the loadgen number)

`cargo run --release --bin loadgen -- --secs 3 --agents 8 --latency` drives
sustained load through the **full verified-write spine** (authz submit-gate +
`RootChain` chain-gate + apply), conserving value every step, and reports the
sustained rate + the per-turn latency distribution. Measured run:

```
committed verified turns: 791,552  (in 3.000 s)
refused (gate):           0
sustained rate:           263,836 verified turns/sec   (single core)
conservation:             Σ balances = 1,000,000,000  (== float)  ✓

per-turn latency (full spine):
  mean:   3.61 µs    p50: 3.08 µs    p90: 3.33 µs
  p99:    7.38 µs    p99.9: 52.1 µs  max: ~34 ms (one cold-start outlier)
```

So a single core sustains **~264 K verified turns/sec** end-to-end, with a hot-path
**p50 ≈ 3.1 µs / p99 ≈ 7.4 µs**. The p99.9 and max reflect the cold-LRU starts (a
token's first turn pays the full ed25519 verify, the 55 µs cold path) and
allocator/scheduling jitter, not the steady state. Value is conserved on every one
of the ~792 K turns (Σ balances never drifts from the genesis float) — the
conservation property is not a sampled check, it is exact across the whole run.

---

## 6. How to read these against DBOS / a hand-rolled system

* **vs DBOS** (`docs/PG-DREGG-VS-DBOS.md`): a DBOS step is ordinary code issuing an
  ordinary `UPDATE` — its per-step cost is a postgres write + the checkpoint.
  pg-dregg's per-step cost (~6.7 µs core, + the live-pg `MERGE`/SPI on top) buys
  the step being a *verified turn*: the bare-`UPDATE` money-printing bug DBOS
  executes exactly-once is refused here by construction. The benchmark isolates
  what that verification costs (a few µs/turn); the durability/crash-recovery cost
  is comparable to DBOS's (both re-validate from a durable log).
* **vs a hand-rolled RLS policy** (§2): the verified capability decision is ~120×
  a naive ACL string-compare per row, and that overhead is the price of
  unforgeability + attenuation + instant revocation — properties a hand-rolled
  plaintext predicate does not have and a bug in it silently loses.

The honest one-liner: **the verified-write *chain* discipline is effectively free
(~4 ns/turn); the verified *capability* decision is a few µs/row hot (amortized by
the LRU from a 55 µs cold verify); and that few-µs is what makes pg-dregg's reads
cap-secure and its writes unforgeable** — at hundreds of thousands of verified
turns/sec on a single core.

---

## 7. What is NOT measured here (named, not hidden)

* **The live-pg round-trip.** Every number above is the postgres-free core. The
  SPI call overhead, the `MERGE` applicator, the trigger dispatch, and the WAL
  write are additive and are exercised separately (`cargo pgrx test pg18`,
  `scripts/e2e-live.sh`). A live `dregg_admits` RLS decision is the 1.6 µs core
  *plus* the per-call SPI to read the `dregg.token` GUC + `now()` — the SPI
  dominates, which is a postgres cost, not a dregg cost. (A deployment that binds
  the token once per statement rather than re-reading the GUC per row amortizes
  it; that is a pg-side tuning, out of scope for the core benchmark.)
* **The real executor's PRODUCE cost.** The `drain_spine` and `workflow` groups use
  the deterministic `FoldProducer` / `FoldProjector` stand-in at the executor seam
  (the postgres-free core does not link the verified Lean executor). The
  production PRODUCE cost is the executor's per-turn cost, measured in the executor
  lane, not here. What these groups measure is the spine *plumbing* around it.
* **The Tier-C proof verify.** The whole-chain IVC proof verification
  (`dregg_attest_*`) is the expensive complete soundness half; its cost is the
  circuit verifier's, not the structural chain tooth's (~4 ns) measured here.
  These benches cover the realizable, shipped, circuit-free write path.
