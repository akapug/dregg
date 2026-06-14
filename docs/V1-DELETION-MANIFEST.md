# V1-DELETION-MANIFEST — the isolated-component catalog (C7 grep-zero plan)

*(2026-06-14, during THE FLIP. This is the precise inventory of the legacy v1
effect-VM proof component — what gets DELETED at C7, what must be MIGRATED first,
what is test-only, and the grep-zero checklist. Built so C7 is a mechanical
Workflow fan-out the instant the VK epoch lands green. Cross-ref:
`docs/ROTATION-CUTOVER.md` §EXEC.3 (the C7 deletion list) + `HORIZONLOG.md` ⚑⚑
PRE-FLIP GATE. Symbol counts are file-counts from the 2026-06-14 grep baseline.)*

## The boundary, in one line

v1 = the IR-v1 / 186-column hand-AIR effect-VM proof (`EffectVmAir` /
`EffectVmP3Air` / `EffectVmP3Proof` / `generate_effect_vm_trace` / the v1
`bilateral_aggregation_air` / `CutoverFallback`). Rotated = the IR-v2 R=24
multi-table `Ir2BatchProof` via the Lean-emitted descriptor interpreter
(`descriptor_ir2` + `trace_rotated` + the v3 registry). The flip makes rotated
the default; C7 deletes v1. The two share `circuit/src/lean_descriptor_air.rs`
infra (`LeanExpr`/`JsonCursor`/`parse_expr`/…) — those STAY (bucket D).

## Bucket A — PURE v1, DELETE at C7 (no rotated-path role)

| target | where | refs | note |
|---|---|---|---|
| `EffectVmP3Air` | `circuit/src/effect_vm_p3_full_air.rs` | 6 files | the full 186-col AIR; 30 self-refs in-file |
| `EffectVmP3Air` shape-mirror | `circuit/src/effect_vm_p3_air.rs` | — | 5 `ACTIVE_BASE_COUNT` refs |
| `EffectVmAir` + `EFFECT_VM_WIDTH=186` | `circuit/src/effect_vm/air.rs` | 36 files | the bulk is `effect_vm/tests.rs` (bucket C) |
| `EffectVmP3Proof` + `prove_effect_vm_p3` | `circuit/src/…` (+1 sdk) | 7 / 8 files | the v1 SDK effect-vm leg type |
| `generate_effect_vm_trace` (186-col) | `circuit/src/effect_vm/trace.rs` | 43 files | 33 in circuit; live consumers in bucket B |
| `BilateralAggregationAir` block | `circuit/src/bilateral_aggregation_air.rs` | 4 files | KEEP the FILE for `CrossSideExistenceAir`/`BundleTreeFoldAir` (bucket D) — delete only the `BilateralAggregationAir` + `AggregationInnerRow`/`AGG_WIDTH`/`build_aggregation_trace` block |
| `CutoverFallback` | `sdk/src/full_turn_proof.rs` | 2 files | 8 in-file refs + 1 test; retired by Wall A |

## Bucket B — MIGRATE first, then the v1 ref dies (live consumers)

| consumer | where | status |
|---|---|---|
| full-turn prove (vk_hash / conservation / unconditional trace) | `sdk/src/full_turn_proof.rs` | **Wall A — LANE LIVE** (`a744069d`) |
| bilateral verify reads v1 PI slice | `turn/src/aggregate_bilateral_prover.rs` + `witnessed_receipt.rs` | **Wall B — LANE LIVE** (`a744069d`) |
| FLOW-B freshness arm | `node/src/blocklace_sync.rs` + `turn_proving.rs` | **Wall C — LANE LIVE** (`a9fe8d40`) |
| node WR producer populates `bilateral_schedule` | `node/src/blocklace_sync.rs` `materialize_blocklace_artifacts` | **MAIN LOOP, deferred til Wall C lands** (node/ collision) |
| **#103 executor verify** `verify_and_commit_proof` off bespoke `EffectVmAir` → rotated `Ir2BatchProof` (+ retire `air.rs:1365-1374` legacy cap arm) | `turn/src/executor/proof_verify.rs` (16 refs) | **MAIN LOOP, rides the VK epoch — do AFTER walls land** (must match the finalized rotated leg) |
| sovereign prove path | `sdk/src/cipherclerk.rs` (8) | confirm rotation-threaded or rotation:None-clean |
| MCP / API / atomic produce-verify surfaces | `node/src/{mcp.rs(18),api.rs(4),prove_pool.rs}`, `turn/src/executor/{atomic.rs(6),mod.rs,execute.rs,authorize.rs}`, `turn/src/turn.rs` | mostly rotation:None-clean per §EXEC.3 "(a) most need no edit" — confirm each at C7 prep, thread only the load-bearing ones |

## Bucket C — TEST harnesses (delete WITH their targets at C7)

`circuit/src/effect_vm/tests.rs` (65 `EffectVmAir` refs) · the ~40 v1 harnesses
named in §EXEC.3: `circuit/tests/effect_vm_descriptor_cutover_harness.rs`,
`effect_vm_{grant,attenuate,revoke}_non_amp.rs`, the v1 call-sites in
`effect_vm_p3_descriptor_differential.rs` / `turn_revalidation_vs_prove.rs`. The
differential harnesses (v1-vs-rotated) lose their reason to exist once v1 is gone.

## Bucket D — KEEP (shared infra / rotated-path deps in the same files)

`circuit/src/lean_descriptor_air.rs` — DELETE only `EffectVmDescriptorAir::eval`
+ `prove_vm_descriptor`/`verify_vm_descriptor` (v1 surface); KEEP
`LeanExpr`/`VmConstraint`/`RangeSpec`/`EffectVmDescriptor`/`i64_to_babybear`/
`const_to_expr`/`JsonCursor`/`parse_expr` (imported by `descriptor_ir2.rs`).
`bilateral_aggregation_air.rs` `CrossSideExistenceAir` + `BundleTreeFoldAir` (the
CG-5 / proof-of-proofs; they do NOT read `effect_vm::pi`; retire in a later Lean lane).
The wasm path keeps v1 UNTIL the Option-A wasm-rotated prover lands (then it joins bucket A).

## The grep-zero checklist (run after C7; each must reach 0 in recursion-enabled builds)

```
generate_effect_vm_trace · EffectVmAir · EffectVmP3Air · EffectVmP3Proof
prove_effect_vm_p3 · CutoverFallback · EFFECT_VM_WIDTH · ACTIVE_BASE_COUNT (v1 PI)
BilateralAggregationAir · AggregationInnerRow (v1)
```
Caveat (the Option-A decision): until the wasm-rotated prover lands, the
`#[cfg(not(feature="recursion"))]` wasm path keeps `generate_effect_vm_trace`
(3 wasm files) — so the FULL grep-zero is gated on that frontier build; native
(recursion-enabled) builds reach zero at C7.

## Execution shape

C7 is a Workflow fan-out: one agent per bucket-A file (delete + fix the
compile-fallout in its bucket-B/C dependents, which are already migrated by then),
a synthesizer that runs the grep-zero checklist + the persvati gauntlet. Gated on:
the VK epoch landed green (v3Registry default + re-pin + #103 + notify + reseed).
