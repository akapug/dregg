# dregg HOT-PATH BENCHMARKS

The unified hot-path benchmark suite — the numbers that quantify what this epoch
built. Every bench is a criterion bench in `perf/benches/` over the PUBLIC API of
the code that actually runs (the embedded verified `World`, the real
`TurnExecutor`, the canonical commitment, the audited Plonky3 prover). No
estimates; we time the live paths.

Run the whole suite (smoke):

```
cargo bench -p dregg-perf
```

A single bench:

```
cargo bench -p dregg-perf --bench symbolic_collapse
cargo bench -p dregg-perf --bench membrane
```

FULL (realistic-input) capture, for the persvati baseline run:

```
PERF_FULL=1 perf/scripts/capture-baseline.sh main-YYYYMMDD
```

Every bench is SMOKE-vs-FULL aware (`PERF_FULL=1` selects the realistic inputs);
the SMOKE default keeps `cargo bench` seconds-to-minutes-scale on a laptop.

---

## Machine stamp

These numbers are stamped by the host they were captured on — NOT recomputed at
read time. Re-capture on your own machine before trusting absolute figures; the
RATIOS (symbolic speedup, the commitment cost removed) are the portable result.

| field   | value                              |
|---------|------------------------------------|
| host    | Darwin 25.5.0 arm64                |
| cpu     | Apple M2 Max (12 cores)            |
| regime  | SMOKE (`PERF_FULL` unset)          |
| git     | `fb0c01e2`                         |
| profile | criterion release                  |
| harness | criterion, default sampling        |

Capture metadata for a saved baseline lands in `perf/baselines/<name>/META.txt`
(host / git / UTC timestamp), written by `perf/scripts/capture-baseline.sh`.

---

## THE HEADLINE — symbolic vs full + collapse (interactivity)

`perf/benches/symbolic_collapse.rs`. A batch of N real transfer turns through the
embedded `World` (the same verified executor the node and the seL4 `executor` PD
drive), committed three ways. SMOKE batch N=8 (FULL sweeps N ∈ {8, 64, 256}).

| leg               | N | time (median) | per-turn  | what it pays |
|-------------------|---|---------------|-----------|--------------|
| `full_batch`      | 8 | ~6.8 s        | ~850 ms   | the publishable default: every committed turn materializes its per-turn Merkle witness (`Ledger::root()` pre+post) AND the replay-tape double-execution (`History::record_commit` re-runs the turn + root on the recorder) |
| `symbolic_batch`  | 8 | ~0.9 ms       | ~110 µs   | the local interactive fast path: the FULL state transition + every legality gate fire, but `Ledger::root()` and the replay double-execution are SKIPPED — the turn is buffered for collapse |
| `collapse_8`      | 8 | ~2.9 s        | (one-time)| `World::collapse`: re-run the buffered batch under Full to materialize the real witnesses ON DEMAND — paid once, at publish, instead of per turn |

**The symbolic speedup is ~3 orders of magnitude per turn** (`full ÷ symbolic` ≈
6.8 s / 0.9 ms ≈ **7,000×** in this smoke run). That is THE interactivity number:
the witness/commitment work — `Ledger::root()` materialization plus the replay
double-execution — is exactly what symbolic mode removes from the live loop, and
exactly what `collapse` pays back ONCE when the work is published.

The cost that symbolic removes is the per-turn WITNESS, not the per-turn
DECISION: every admission gate (authority, conservation, the NoteSpend STARK,
sovereign-witness, nonce/fee) runs identically in both modes. A turn rejected in
Full is rejected in Symbolic, at the same action, for the same reason
(`turn/src/collapse.rs`). A symbolic receipt carries the deferred sentinel
state-hash and is local/unpublishable until collapsed.

> Smoke caveat: the smoke run uses only 20 samples and rebuilds a fresh
> `demo_world` per iteration, so the criterion confidence intervals are WIDE
> (`full_batch_8`: 5.6–8.5 s; `symbolic_batch_8`: 0.1–2.5 ms). The ORDER OF
> MAGNITUDE is unambiguous; for tight intervals capture with `PERF_FULL=1` on the
> persvati run (`capture-baseline.sh`), which sweeps N and lets criterion settle.

### What symbolic SAVES, decomposed — the commitment cost

`perf/benches/commitment.rs` isolates the per-touched-cell witness cost symbolic
defers — the canonical state commitment a Full turn computes per cell:

| commitment                              | time      |
|-----------------------------------------|-----------|
| `compute_canonical_state_commitment` (v8) | _(filled at capture — see baselines)_ |
| `compute_canonical_state_commitment_v9` (rotated) | _(filled at capture — see baselines)_ |

The per-cell commitment is the Poseidon2-sponge a Full turn pays for every
touched cell; the ledger-level `Ledger::root()` folds these into the Merkle
witness the receipt's `pre_state_hash` / `post_state_hash` carry. Symbolic mode
skips the `root()` materialization wholesale (deferred sentinel), and `collapse`
re-derives it on demand — so the headline saving is the ledger-root cost times
the batch length, deferred to a single collapse.

---

## Executor turn — the baseline everything compares against

`perf/benches/executor_turn.rs`. The live Rust `TurnExecutor::execute` — the
executor entry the node drives — over one real Transfer turn against a `Ledger`
with two open cells. The non-proof admit hot path: state lookup, authorization
gating, effect application, receipt + commitment.

| bench                | time      |
|----------------------|-----------|
| `transfer_open_cells`| _(filled at capture — see baselines)_ |

This is the floor: the bare classical state transition with witness. The
`symbolic_batch` per-turn cost sits near this floor (it is the same transition
minus the ledger-root); the `full_batch` per-turn cost is this PLUS the
replay-tape double-execution + root materialization.

---

## Membrane — "invite someone to my computer"

`perf/benches/membrane.rs`. The four legs of the confined shared-fork membrane
(`starbridge-v2/src/shared_fork.rs`, gpui-free over the embedded `World`).

| leg              | time (median) | what it is |
|------------------|---------------|------------|
| `fork`           | ~3.3 µs       | `World::fork`: deep-clone my live ledger + the genuine executor into a confined sub-world (the snapshot/rehydrate substrate; committing on the fork mutates ONLY the fork) |
| `mint`           | ~1.43 s       | `SharedFork::construct`: birth the guest's view by GRANTING an attenuated embedded cap into its fork c-list via a real verified powerbox turn (`Powerbox::grant` — the held + non-amplifying gates + executor backstop). This IS a Full commit, so it pays the per-turn witness cost above. |
| `drive_embedded` | ~938 ms       | `SharedFork::commit_turn_gated`: the guest drives an EMBEDDED turn through the fail-closed boundary gate (classify over `touched_cells`, then commit locally — an embedded exercise needs no consent). Also a Full commit. |
| `stitch_settle`  | ~72 ns        | `Stitch::settle`: reconcile the branch doc-graph into main under the Settlement-Soundness gate (a conferred cap must be held at the settlement tip), then take the pushout |
| `roundtrip`      | ~4.2 s        | fork → mint → drive → stitch end-to-end (the whole membrane lifecycle) |

Reading: the membrane's STRUCTURAL operations are cheap — forking a world is
microseconds (a clone), and stitching the doc-graph back is nanoseconds (a lattice
join under the settlement gate). The COST of a membrane is the verified turns
inside it: `mint` and `drive_embedded` are dominated by the underlying Full
`commit_turn` (a real powerbox grant / a real transfer), each paying the same
per-turn witness the headline measures. The membrane adds essentially nothing over
the turns it carries — the gate classification is a `touched_cells` scan, not a
second execution.

> The `drive` consent-gated BOUNDARY path (the `ConditionalTurn` consent
> round-trip) is the rarer, slower leg and is not timed here — the common membrane
> exercise is the embedded turn. The consent path is exercised by `shared_fork`'s
> own tests.

---

## Circuit prove / verify

The circuit prove/verify hot path is already covered by the existing benches in
`perf/benches/` (NOT added by this suite; referenced here for completeness):

- `turn_witness_vs_proving.rs` — the witness-only admit path vs the full
  self-sovereign turn prover, side by side (the proving multiplier reads off
  directly).
- `prove.rs` / `verify.rs` — the audited Plonky3 EffectVM prove + the light-client
  verify.
- `cohort_circuit.rs` — the rotated IR-v2 multi-table batch STARK per effect-cohort.
- `recursion_fold.rs` — the bundle-tree aggregation fold.
- `embedded_commit.rs` — the verified Lean kernel `commit_turn` throughput.

Run `cargo bench -p dregg-perf --bench turn_witness_vs_proving` (FULL is
minutes-scale — capture on persvati). The proving leg is the cost symbolic mode
NEVER pays on the interactive loop: a proof is minted only when a turn crosses the
publish boundary, after `collapse`.

---

## Data plane (DP-2) — the cap-gated message bus

`perf/benches/data_plane.rs`. DP-2 has landed (`captp::data_plane::Bus` — the
userspace message bus a deos app uses to move work, cap-gated by `SendCap` and
receipted by a signed `CustodyReceipt`). The bench times its throughput:

| leg                | what it pays |
|--------------------|--------------|
| `enqueue`          | the `SendCap` admission gate + relay enqueue + monotone inbox-root advance + the Ed25519 custody-receipt SIGNATURE (the price of a convictable delivery) |
| `drain`            | deliver the recipient's queued boxes + append their content hashes to the authenticated delivered-log (the "handled" witness) |
| `enqueue_drain`    | the unit of data-plane work: send + deliver one message |
| `publish_fanout_S` | `Bus::publish`: fan one payload out to S subscribers (each a real cap-gated, receipted enqueue) — SMOKE S=4, FULL S ∈ {4, 32, 128} |

Run `cargo bench -p dregg-perf --bench data_plane`. The send cost is dominated by
the Ed25519 receipt signature — the bus mints accountability (a drop is provable),
not a fire-and-forget queue. Numbers land in the saved baseline.

## Pending benches

- All six requested hot-path families are now benched: executor turn, canonical
  commitment, symbolic-vs-full+collapse, membrane, circuit prove/verify (the
  existing `turn_witness_vs_proving` / `prove` / `verify` / `cohort_circuit` /
  `recursion_fold`), and the DP-2 data plane. No pending bench remains.

---

## Baselines

Saved baselines live in `perf/baselines/<name>/`:

- criterion estimates under `target/criterion/*/<name>/` (compare with
  `--baseline <name>`),
- `proof-sizes.json` (wire-byte regression tracker),
- `perf-report.txt` (the human-readable map),
- `META.txt` (host / git / UTC capture stamp).

Capture: `perf/scripts/capture-baseline.sh [name]` (the FULL suite; persvati, not
laptops). Compare a later run: `PERF_FULL=1 cargo bench -p dregg-perf -- --baseline <name>`.
