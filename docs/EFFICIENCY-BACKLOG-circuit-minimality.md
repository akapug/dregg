# EFFICIENCY BACKLOG — circuit minimality beyond the Epoch-2 bundle

2026-07-18. Ranked backlog of circuit efficiency / minimality work OUTSIDE the committed Epoch-2
bundle (rate-8 absorb bundle, chip one-hot flag/tag retype + per-shape tuples, H4+caveat,
separate-absorb floor shape, narrow-bus retirement, TURN_HASH limb widening, bare-V3 stratum
retirement, heap-open closure, D5 PI-map regen). Provenance: five hunt lenses (aux-tables,
registry-vestiges, other-AIRs, recursion-wrap, semantic-minimum) over HEAD, with the largest and
shakiest claims independently re-derived by two adversarial verifier passes (verifier 2 pinned
HEAD = `2e5fcd2b4`). One claim was refuted — see the graveyard; it is not silently dropped.

## Vocabulary

Evidence classes (arch-review vocabulary):

- **[M]** — measured on a real prove/verify at HEAD.
- **[P]** — parsed/read from code or descriptors at HEAD; a structural fact.
- **[A]** — analytic: calibrated-model extrapolation, not measured on this exact path.
- **[U]** — unknown: needs a probe before the number can be trusted.

Verification tags: **CONFIRMED** = independently re-derived by a verifier pass; **hunt-only** =
single-lens parse, no second derivation; **REFUTED** = graveyard.

Wire pricing used throughout: composite ~188 B/col on the main batch, [M]-calibrated by the S2
deletion itself (−960 cols → −181,757 B; post-S2 transfer proof = 375,053 B, cells 394,400;
`docs/MEASURE-legacy-1felt-chain-drop.md`). Aux-instance pricing: 28.5 B/col opened + 19q ×
2.48 B/col ≈ 75.6 B/col **[A]** (calibrated at h=64/256; h=8 paths are shorter).

Effort unit = **lane**, calibrated: the S2 deletion = 1 heavy lane; the narrow-bus campaign = 6 lanes.

Risk classes: **byte-safe** (no VK/FP/FS change) · **regen** (VK/FP re-pin, no statement or value
change) · **semantic-change** (statement, soundness posture, or published-value change).

## Decisions that expire at the Epoch-2 freeze

Four items get an epoch cheaper if decided before the Epoch-2 flag day; deferral costs a second
VK/FS epoch later:

1. **E3 — mutable-last limb schedule.** The v10 absorption order is being frozen in the bundle;
   reordering later is another flag day.
2. **E4 prep — run the FRI re-grid measurement now** at post-S2 and mocked-floor widths so the
   (lb,q) point can land inside the same FS epoch.
3. **R11 fold-side costing.** D7 priced the floor-shape branches on the wire only (+9,043 B for
   the preprocessed round); each extra instance/round also adds per-query input-round Merkle paths
   + opened-value Horner chains to EVERY leaf-wrap circuit. Uncosted **[U]**; belongs in the
   Stage-3 B-vs-F decision before it is made, not after.
4. **E12 — pin children on the wide tree** before the staged wide-tree flip ships, or the seam
   ships with it.

## Ranked backlog — summary

| # | Item | Verified cost today | Yield | Effort | Risk | vs Epoch-2 |
|---|------|--------------------|-------|--------|------|------------|
| 1 | E1 v1-face dead-band compaction | ~28 KB/proof (7.5%), 8,847 dead col-instances | ~29 KB/proof mean, ~9.5K cells/member | 1–2 lanes | regen | independent; ride the regen |
| 2 | E2 double-prove retirement + fold-arity 8 | 1 extra full prove/turn + ~3.8× commit-phase hashing in every wrap | seconds/turn off the recursion stack | 2–3 lanes | semantic-change | independent |
| 3 | E3 mutable-last limb schedule | chip h=64 where 32 suffices (34 members) | ~12.7K cells (~15% of floor); kills the h-64 cliff | hours + rider | semantic-change | BEFORE freeze |
| 4 | E4 FRI re-grid (8,14–15,16) | (6,19) chosen at a 3.0×-smaller member | projected 151→115–125 KB [A] | 1 lane | regen | with/after bundle |
| 5 | E5 map-ops instance split | 476 all-zero cols ≈ 36 KB on heapWrite/refusal | 36–68 KB on 10 map members | 1 lane | regen | independent |
| 6 | E6 absent-op deletion | MapAbsent instance ≈ 18–27 KB + 1 witness chip path × 7 members | strongest single lever on the chip-64 cliff | 1–2 lanes | regen + Lean lemma | independent |
| 7 | E7 by-name zoo re-emit | 39–88% of width per predicate/payment proof | dominant share of every private-payment sub-proof | ~2 lanes | regen | does NOT inherit Epoch-2 |
| 8 | E8 bilateral-v2 expected-block deletion | 35 duplicated cols+gates, live per multi-cell turn | width 87→52 + closes middle-row identity gap | 1 lane | semantic-change | independent |
| 9 | E9 joint-turn binding leaf | free-witness digest + 1 uni-STARK + 1 wrap per joint turn | delete a layer or make it real | 0.5–1 lane | semantic-change | rides tag retype if (b) |
| 10 | E10 frozen-authority falsifier + 83-col dedup | 83 duplicate cols ≈ 15.6 KB (16 members); 41 members unprobed | falsifier answer + 15.6 KB + 5.3K cells | hours + 1 lane | byte-safe then regen | dedup rides regen |
| 11 | E11 Golden-v1 stratum deletion | ~900 dead lines; pow-14 config sets the gate's weakest column | ledger floor rises to the pow-16 set | 1 lane | byte-safe + gate re-pin | independent |
| 12 | E12 pinned children on wide/joint trees | 2 of 3 tree folds fold unpinned children | closes the foreign-child seam pre-flip | 0.5–1 lane | semantic-change | BEFORE wide flip |
| 13 | E13 Memory-table retirement + degree-8 kill | 2 AIRs + 3 buses for one member's 2 ops; lone deg-8 gate | main degree uniformly ≤2; whole subsystem deleted | 1–2 lanes | regen | ride the regen |
| 14 | E14 umem cohort boundary flip | 29 extra cols + byte sends × 57 welded proofs | ~2–3 KB × 57 | 0.5 lane | regen | independent |
| 15 | E15 CCC route-or-retire | Lean-proved AIR unrouted; live gate = Rust sums; 154/172 range cols | decision + 172→~30 cols if routed | 0–2 lanes | semantic-change if routed | independent |
| 16 | E16 ops-layer routing | O(K)×minutes per fold request; ~100 KB envelope freight | amortized folds; smaller envelopes | ~1 lane + hours | mixed | independent |
| 17 | E17 hygiene riders | fossils, false parity claim, placeholder members, PI ballast | audit-surface shrink | ≤0.5 lane each | mostly regen riders | ride the regen |

---

## Ranked backlog — detail

### E1 — v1-face dead-band compaction (rank 1)

- **What/where:** On every wide member, the L0 v1 executor face is largely unread: on post-S2
  transfer (W=1704), **149 committed columns are referenced by zero constraints** — cols 14–53
  (40 retired-verb selectors; `RETIRED_SELECTORS`, `circuit/src/effect_vm/columns.rs:186-188`),
  70–75 (6 params), 90–97 + 101–185 + 187 (94 of 98 v1 aux, including the entire 60-col v1
  balance **bit**-decomposition band `NEW_BAL_LO/HI_BIT_BASE`, `columns.rs:310-313`, superseded by
  the 15-bit-limb avail weld), plus 9 gentian-tail cols. Registry-wide: min 141 (transferFee),
  mean 155.2, max 207 (heapWrite), **8,847 dead col-instances = 8.5% of total registry width**
  (`circuit/descriptors/rotation-wide-registry-staged.tsv`).
- **Verified cost today:** 149 × 188 B ≈ **28.0 KB/proof = 7.47% of the 375,053 B post-S2 proof**;
  registry mean ≈ 29.2 KB; ~9.5K committed cells/member. [P] census, [A] pricing ([M]-calibrated
  via the S2 drop). **CONFIRMED by both verifiers** (semantic-minimum variant exact; the
  registry-vestiges variant's transfer detail refuted — see graveyard).
- **Fold-ins (same compactor pass):** 21 members still carry the 4 transitively-dead H4 chip sites
  the uniform S2 kill-set missed (~2,176 main cells + 1,024 aux cells + ~6.4 KB each; hunt-only
  [P]); heapWrite has 1 further dead arity-2 site + 8 orphan cols [P]; gentian-refuse aux is
  9–12 cols dead where carried [P]; the 34–39-col dead bands on note/refusal/heap members are
  included in the totals but their stratum identity is **[U]** — read the note-region emit and
  name the band before the compactor eats it.
- **Fix sketch:** a `compactS2`-style value-preserving face compaction at the Lean emit
  (`RotWideCompactS2.compactS2` machinery + `compactOk` gate already exist), with a **per-member**
  kill-set instead of the uniform one. Pure column deletion; producer fill + width pins follow.
- **Effort:** 1–2 lanes (S2-class). **Risk:** regen. **Dependencies:** independent of the A/B/F
  floor-shape choice; ride the Epoch-2 regen window (Design A explicitly keeps the v1 face, so
  nothing in the bundle deletes this band on its own).

### E2 — retire the per-turn double-prove; escalate fold arity (rank 2)

- **What/where:** Every IVC-bound turn is proven twice: the production artifact mints under
  `ir2_config` (lb 6, 19q, fold-by-8; `circuit/src/descriptor_ir2.rs:5452-5456`), then
  `turn/src/rotation_witness.rs:749-762` re-proves the identical descriptor/trace/PI vector under
  `ir2_leaf_wrap_config` (fold-by-2; `circuit-prove/src/ivc_turn_chain.rs:951`,
  `plonky3_recursion_impl.rs:116-119`), plus a mint self-verify (`rotation_witness.rs:685-687`).
  The arity-2 choice is a still-unresolved PROBE (`plonky3_recursion_impl.rs:401-411` — "isolate
  whether higher-arity folding is the obstruction"); the in-circuit verifier reads count/arity
  from the proof, so direct consumption of the arity-8 proof is plausible but unexercised **[U]**.
  Downstream, arity-2 is baked into every recursion layer AND the gnark wrap
  (`friFoldRowArity2`, `chain/gnark/fri_verify_native.go`; `dregg_outer_config.rs:139-142`).
- **Verified cost today:** one full extra descriptor prove per finalized turn (~425–440 ms post-S2
  [A]; the hunt's 638 ms was the pre-S2 [M] figure) + ~18 commit rounds instead of ~6 in every
  in-circuit verifier: **~3.8× on the commit-phase Merkle-path term** (whole hashing table drops
  by less than 3× — the input-round paths are arity-independent). The 2^15-row poseidon2-W16
  shrink table (~11,000 perms) is precisely this term. [P] structure, [A] arithmetic.
  **CONFIRMED by both verifiers** (with the quantitative hedge above).
- **Fix sketch:** exercise the recompose path at arity >1 against a real `ir2_config` proof; if
  green, consume the production proof directly, delete the re-mint, collapse the
  `DreggStarkConfig`/`DreggRecursionConfig` split (the "SIDESTEP option a" fossil,
  `ivc_turn_chain.rs:927-935`; 15 leaf adapters affected); add an arity-8 `fold_row` to gnark.
- **Effort:** 1–2 lanes dregg-side + 1 gnark lane. **Risk:** semantic-change — arity-8 at lb 6
  costs ~3 per-fold soundness bits (112→109); the decision goes through `dregg_fri_ledger`, not a
  comment. **Dependencies:** independent of Epoch-2; compounds with apex lever B; this is where
  the latency lives once the bundle lands (post-Epoch-2 the recursion stack is >99% of settlement
  latency — R11).

### E3 — pre-freeze decision: mutable-last limb schedule (rank 3)

- **What/where:** The Lean-pinned absorption order puts every transfer-mutated limb first
  (`pre[1]=balance_lo, pre[2]=nonce, pre[3]=balance_hi`; mirrored at
  `cell/src/commitment.rs:1075-1083`), so D1's rate-8 simulation found zero BEFORE/AFTER chip
  dedup — the streams diverge at step 1 (`docs/DECIDERS-rotated-arch-D1-D7.md:87-89`).
- **Verified cost today:** chip height 64 where ~32 would suffice on the 34-member transfer class;
  the capOpen/noteSpend family misses the 64 cliff by 1–2 permutations. [P] order, [A] dedup
  projection (D1's simulator, needs one re-run under the reordered schedule). Hunt-only.
- **Expected yield:** BEFORE/AFTER chains share ~21 of 23 rate-8 steps as identical chip tuples →
  chip height 64→**32** for the 34-member class (~12.7K cells ≈ ~15% of the 82.7K-cell floor);
  subsumes D6 follow-up #2 with margin; de-risks the witness-node8 axis on map-op members.
- **Fix sketch:** re-run the D1 simulator mutable-last (hours); pin the v10 schedule accordingly.
  Seed choice couples: a per-object seed (design B) kills this dedup — decide the two together.
  BEFORE/AFTER need no in-hash domain separation (each digest has its own PI slot).
- **Effort:** hours + free rider on the Epoch-2 emit. **Risk:** semantic-change (published anchor
  values change — the flag day already planned). **Dependencies:** MUST be decided before the
  Epoch-2 freeze; retrofit = another epoch.

### E4 — FRI re-grid at post-bundle scale (rank 4)

- **What/where:** `ir2_config` = (lb 6, 19q, pow 16) was chosen from a grid measured when the
  member proof was 120.4 KiB (`.docs-history-noclaude/PROOF-ECONOMICS.md`) — **3.0× smaller than
  today's post-S2 375 KB** (4.5× vs pre-S2), and ~4.8× smaller than nothing: the Epoch-2 floor
  moves the knee again. At floor scale, LDE volume at lb 8 ≈ today's at lb 6 (21.2M vs 25.2M
  cell-evals).
- **Verified cost today:** the gate floors admit (8,15,16) → 136/76 and (8,14,16) → 128/72
  against floors 128/71 (`circuit-prove/tests/fri_params_soundness_budget.rs:185,196`), and the
  gate's own doc records that lb 6→8 improves every numeric floor. Unused knobs:
  `commit_proof_of_work_bits` hardwired 0 (`circuit/src/plonky3_prover.rs:176`) and
  `log_final_poly_len = 0`, never in any grid. [P]/[M-dated]. **CONFIRMED** on every checkable
  fact; the payoff endpoint is a model number.
- **Expected yield:** projected ~151 KB → ~115–125 KB at the floor shape **[A]**; the measured
  old-era (8,15)-vs-(6,19) delta was −11.5%, so treat 115–125 as the optimistic end until the
  measurement lane runs. Also the only lever that shrinks every query-proportional term the
  recursion wrap re-verifies.
- **Fix sketch:** re-run `ir2_fri_grid` at post-S2 and mocked-floor widths; push candidates
  through the Lean `dregg_fri_ledger` — ε_C (commit-phase, height-dependent) already binds BELOW
  the Johnson column, so the two closed-form columns are not sufficient. Carry the gate's own
  label: capacity-128 is a refuted-conjecture drift canary, not security headroom.
- **Effort:** 1 measurement lane + ledger pin update. **Risk:** regen (FS change).
  **Dependencies:** measure now; land the flip with/after the Epoch-2 FS epoch. Related [U]: the
  recursion wrap re-verifies 38q at (3,38,pow14) — the same up-blowup logic would shrink the gnark
  wrap circuit; scope unknown.

### E5 — split the 897-col map-ops monolith (rank 5)

- **What/where:** `Ir2Air::MapOps` is always MAP_WIDTH=897 (`descriptor_ir2.rs:1913,2132`); the
  op≤3 layout ends at col 421 and everything in [421,897) is structurally zero on op≠4 rows
  (`:1874-1876`). `heapWriteVmDescriptor2R24` and `refusalVmDescriptor2R24` carry only
  `map_op write`, so their committed map instance is 53% all-zero columns on every row.
- **Verified cost today:** 476 dead cols × 75.6 B/col ≈ **36.0 KB** wire on heapWrite/refusal
  proofs; the full 897-col instance ≈ 67.8 KB on each of the 10 map-carrying members — a line
  item the transfer-calibrated review never priced. [P] structure **CONFIRMED**, [A] pricing
  (model not measured on an h=8 aux instance).
- **Fix sketch:** split into op≤3 (width 421) and AAFI (897) arms selected off the constraint
  list exactly like `map_absent` already is (presence flag + width fn + Lean twin).
- **Effort:** 1 lane. **Risk:** regen. **Dependencies:** independent; rides any regen.

### E6 — delete the `absent` map op (subsumed by `aafi_insert`) (rank 6)

- **What/where:** On all 7 absent-carrying members the `absent` op and the `aafi_insert` have the
  same guard, same key (var 68), same 8-felt root group, and absent's new_root == root [P,
  TSV parse]. The AAFI arm already carries the pointer-bracket non-membership proof
  (`low_addr < key < low_next` against the same root, `descriptor_ir2.rs:1906-1913`;
  `imtAbsent_excludes`), and `noteCreateVmDescriptor2R24` already inserts with no absent op —
  the in-registry existence proof.
- **Verified cost today:** the entire MapAbsent instance (MA_WIDTH=358) ≈ 18–27 KB [A] + one
  BUS_MAP_LOG interaction + **one full 16-deep witness node8 chip path (~16–17 unique perms)** per
  carrier. noteSpend/createCell miss the chip-64 cliff by ONE permutation — deleting a whole
  witness path is strictly stronger than the D6 one-terminator consolidation. Hunt-only.
- **Fix sketch:** Lean lemma that the emitted `aafi_insert` discharges the `opensTo none`
  conjunct the kernel refinement consumes (mirror of `imtAbsent_excludes` inside `imtInsert`);
  then stop emitting absent ops; MapAbsent AIR + MA_* layout (~200 lines Rust + Lean twin) go dead
  registry-wide.
- **Effort:** 1–2 lanes. **Risk:** regen, gated on the Lean lemma (the lemma is what keeps this
  out of semantic-change territory). **Dependencies:** independent; combines with E3 on the cliff.

### E7 — by-name predicate/membership zoo re-emit (rank 7)

- **What/where:** The graduated-lane idiom (7 unused permutation lanes per single-output chip
  site) is endemic in the non-rotated Lean-emitted descriptors: `by-name/note-spend-leaf.json`
  **125 of 149 cols are lookup-only + 8 fully unreferenced (89% plumbing/dead), per private
  payment**; blinded-membership 29/33; attested-fact 29/34; merkle-membership-depth2 21/24;
  predicate-arith 20 of 25–27 each; 4ary-general 7/18; non-revocation 15/27;
  cross-side-existence-v2 17/24; bundle-tree-fold-v2 8/10. The 4-ary layout documents the lanes
  explicitly (`circuit/src/membership_descriptor_4ary.rs:27,72`). [P] census, hunt-only.
- **Verified cost today:** 39–88% of each proof's committed width, at per-predicate /
  per-payment / per-bilateral-turn frequency. These descriptors are separate Lean emit modules —
  **the Epoch-2 chip changes do not re-emit them**; without a pass of their own they keep the old
  shape forever.
- **Fix sketch:** one shared Lean combinator (`chipLookup` with per-shape tuple, out0-only) + a
  re-emit sweep of `by-name/` through `scripts/emit-descriptors.sh` (the drift gate already
  recurses into by-name); delete note-spend-leaf's 8 unreferenced cols in the same pass. Fold in
  the 1-felt waist fix (SenderAuthorized authorized-set root is a single ~31-bit felt,
  `turn/src/executor/membership_verifier.rs:1076-1101` → 8-felt root + wide-tag chain) — that
  component is semantic-change.
- **Effort:** ~2 lanes + regen. **Risk:** regen (waist fix: semantic-change). **Dependencies:**
  sequence AFTER the Epoch-2 chip retype so the sweep happens once.

### E8 — bilateral aggregation v2: delete the self-checked expected block (rank 8)

- **What/where:** `dregg-bilateral-aggregation-v2.json` (width 87, 70 constraints): **35 of 38
  gates are exactly `sched[13+i] == expected[49+i]`, and both blocks are filled by the prover from
  the same `AggregationInnerRowV2`** (`circuit/src/bilateral_aggregation_air.rs:332-408`); no PI,
  boundary, or lookup pins the expected block externally. Identity PIs bind first/last rows only —
  middle rows' turn-identity columns are unconstrained. Live per multi-cell turn via
  `node/src/api.rs:3989-3997` + wasm. **CONFIRMED** (verifier 2, full constraint-by-constraint
  parse).
- **Verified cost today:** 35 duplicated cols + 35 gates per bilateral-turn proof (height small,
  so cells minor — the cost is a whole extra per-turn instance, a claims gap, and dual maintenance
  of the legacy 112-col and v2 87-col layouts in one file).
- **Fix sketch:** drop the expected block (width 87→52) and pin the schedule per-row via a window
  gate on the identity slots; re-emit from `EffectVmEmitBilateralAgg.lean`. Also fix the doc-level
  claims: per-row PI equality is overstated today, and the `edge_fp` "~124-bit" collision claim
  (`bilateral_aggregation_air.rs:563-585`) is wrong for a 1-felt output (~31-bit; the off-AIR
  multiset check is what closes it).
- **Effort:** 1 lane + regen. **Risk:** semantic-change (middle-row strengthening — in the
  strengthening direction). **Dependencies:** independent; can fold into E9(b)'s rebuild.

### E9 — joint-turn binding leaf: delete it or make it real (rank 9)

- **What/where:** `JointTurnAggregationAir` (`circuit-prove/src/joint_turn_aggregation.rs:
  1360-1411`) has exactly 4 constraints; the `hash_4_to_1` accumulator fold is computed host-side
  only, so `bundle_digest` is a free witness in-AIR and col 1 (`cell_commit`) is read by zero
  constraints. It is a hand-written Rust AIR (Lean-authored-AIR law violation), its anchors are
  1-felt (tid = TURN_HASH[0]; digest content = PI 43, the bare-V3 ~31-bit stratum — zeroed on wide
  members), it gets its own recursion wrap (`joint_turn_recursive.rs:293-334`), and the joint tree
  passes no expose hook, so nothing ties binding rows to the leaves in-circuit. The recursive fold
  has zero production callers (own test + perf only). [P], both hunt lenses agree; verifier-read
  adjacent facts confirmed.
- **Verified cost today:** per joint turn on that path: 1 uni-STARK + 1 recursion wrap
  (~tens of seconds at the ~80 s/layer scale) + 1 extra agg leaf, attesting what the host gate
  already checks; plus the standing in-circuit/host soundness asymmetry.
- **Fix sketch:** (a) delete the binding proof and have the verifier recompute the
  1-hash-per-cell chain over the leaf PIs it already checks; or (b) port the segment pattern —
  expose each leaf's tid via `prove_descriptor_leaf_with_pi_slice_expose`
  (`ivc_turn_chain.rs:1028`) and `connect` at the combine, wide 8-felt tail as content. All
  machinery exists.
- **Effort:** (a) <1 lane; (b) ~1 lane. **Risk:** semantic-change (posture change either way, in
  the honest direction). **Dependencies:** (b) rides the Epoch-2 tag retype; neither inherits the
  bundle otherwise (this AIR does not use the chip).

### E10 — frozen-authority: falsifier on the 41, dedup on the 16 (rank 10)

- **What/where:** Only 16/57 members carry the 83 freeze-shaped colEq gates (AFTER limb k =
  BEFORE limb k at delta 179); **41 members have zero freeze-shaped colEq at any delta** [P].
  Whether each such member's semantic gates + verifier-side PI reconstruction
  (`trace_rotated.rs:665-686`) fully compensate is **[U]** — this is the witness-gen-perimeter
  axis made member-precise. Separately, on the 16 carriers the 83 AFTER columns are pure
  duplicates by constraint.
- **Verified cost today:** 83 cols ≈ 15.6 KB wire + 5.3K cells per proof on the 16-member class,
  plus 83 gates. [P] parse; hunt-only (two lenses agree on the 16-member list).
- **Fix sketch:** falsifier first (hours, byte-safe): forge a changed owner-limb on
  `cellSealVmDescriptor2R24` and observe what rejects it — AIR, executor, or nothing. Then emit
  the AFTER absorb tuples referencing the BEFORE columns directly for frozen limbs (absorb tuples
  are arbitrary `LeanExpr::Var` refs; the weld-tower layering is the only thing forbidding it) —
  deletes the 83 cols AND the 83 gates. The anchor stays a function of the state snapshot alone
  (`cell/src/commitment.rs:1320-1377`); column sharing changes no published value. Note: sharing
  kills width, not absorb count — both chains still absorb all 178 limbs.
- **Effort:** falsifier hours; dedup ~1 lane. **Risk:** falsifier byte-safe; dedup regen.
  **Dependencies:** dedup rides the Epoch-2 emit; falsifier independent, run early.

### E11 — delete the Golden-v1 shape stratum; re-pin the gate floor (rank 11)

- **What/where:** `recursive_witness_bundle.rs` (590 lines) proves `EffectVmShapeAir`
  (`effect_vm_p3_air.rs`, 296 lines), a self-described non-soundness-equivalent structural subset,
  routed by zero production callers (the `recursive_compress: bool` surface; no caller passes
  `true`). It is the main user of `create_recursion_config()` (lb 3/38q/**pow 14**) — the config
  that pins the FRI ledger's weakest Johnson column at 71 and sits at exactly 128 capacity.
- **Verified cost today:** ~900 lines + verifier plumbing of misleading surface; the soundness
  gate's weakest-link floor is set by a config no production proof uses. [P], hunt-only.
- **Fix sketch:** delete the stratum + `WitnessedReceipt` variant plumbing; re-pin the ledger gate
  over the surviving configs (floor rises to the pow-16 set).
- **Effort:** 1 lane. **Risk:** byte-safe deletion + gate re-pin. **Dependencies:** independent.

### E12 — pin children on the wide and joint tree folds (rank 12)

- **What/where:** The module doc claims every child folds through
  `into_recursion_input_pinned` (`ivc_turn_chain.rs:171-183`); true for the scalar tree
  (`:3708-3732`), false for the wide tree (`:2467-2468`, bare `into_recursion_input`) and the
  joint tree (`joint_turn_recursive.rs:371-372`). The wide tree is the staged flip-precursor.
  [P], hunt-only.
- **Verified cost today:** the foreign-child seam the pin was built to close, re-opened on 2 of 3
  paths; plus doc-vs-code drift; plus FOUR near-duplicate tree folds at three soundness levels.
- **Fix sketch:** route wide + joint through the pinned farmable primitive (needs an 8-felt twin
  of `merge_two_segment_proofs`); consolidate the folds while there.
- **Effort:** 0.5–1 lane. **Risk:** semantic-change (closes a seam). **Dependencies:** land
  BEFORE the wide-tree flip ships.

### E13 — retire the legacy Memory table; kill the lone degree-8 gate (rank 13)

- **What/where:** `setFieldDynVmDescriptor2R24` is the sole carrier of `mem_op` in either
  registry; it alone keeps `Ir2Air::Memory` (18 cols, `descriptor_ir2.rs:1713`) + `MemBoundary`
  (28 cols, `:1726`) + BUS_MEM_LOG/CHECK/ADDRS (`:354-356`) + their Lean surface deployed — the
  flat-address regime the universal memory table superseded. The same member holds the registry's
  only main gate above degree 2: `∏k=0..7 (col69 − k)` — **CONFIRMED** (56 members deg ≤2, this
  one deg 8), forcing an 8-chunk main quotient where siblings sit at 2.
- **Verified cost today:** ~46 committed cols + byte-table pull + 2 instances on setFieldDyn
  proofs (~3–4 KB) — plus two AIR arms, three buses, and a boundary discipline maintained for one
  member's dynamic access to an 8-slot bank the static setField siblings already cover.
- **Fix sketch:** re-emit the dynamic slot as an 8-way one-hot mux in main (~8–16 cols, all
  deg ≤2) or as a umem op; delete Memory + MemBoundary + BUS_MEM_* wholesale; main-side degree
  becomes uniformly ≤2 registry-wide. Check the odd `value == addr` (both var 69) on the wire
  **[U]** before migrating.
- **Effort:** 1–2 lanes. **Risk:** regen. **Dependencies:** VK regen rides Epoch-2.

### E14 — flip the umem boundary to the cohort form (rank 14)

- **What/where:** All 57 welded members carry exactly one `umem_op` write — precisely the cohort
  eligibility — but the Lean emitter hard-codes `cohort := false`
  (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitUMemWeldWide.lean:83-86`, no justification stated),
  so every welded proof commits the width-38 GENERAL boundary (UB_WIDTH=38) instead of the
  width-9 cohort AIR (UBC_WIDTH=9) that is built, proven, and routed by zero registries — a second
  narrow-bus-pattern instance. **CONFIRMED, every link** (including that even the
  `umem-cohort-*-staged` TSVs declare the general sem).
- **Verified cost today:** 29 extra cols + the general form's key canonical-decomp +
  lex-comparator byte sends per welded proof ≈ 2–3 KB × 57 members [A]; plus the built-dead UBC
  code.
- **Fix sketch:** flip `cohort := true` in `weldUMemIntoWide` AND swap the hard-coded general
  `umemBoundaryTableDef` (the verifier's nit: it is not one word) + Rust byte-parity pin + regen.
- **Effort:** 0.5 lane. **Risk:** regen. **Dependencies:** independent.

### E15 — cross-cell conservation: route or retire (rank 15)

- **What/where:** The live per-asset Σδ=0 gate is Rust arithmetic
  (`turn/src/executor/proof_verify.rs:1712-1767`); the Lean-proved CCC AIR is self-documented
  "ADDITIVE — NOT wired" (`cross_cell_conservation_air.rs:37-41`). The v2 descriptor spends
  **154 of 172 columns on bit-decomposition range checks** while the batch's byte table exists.
  [P], hunt-only.
- **Verified cost today:** ~0 prover cycles (unrouted), full maintenance (Lean twin, 201 pinned
  constraints, tests) + the good-one-dead/weak-one-deployed pattern.
- **Fix sketch:** decide. Retire = trivial. Route = re-emit with byte-bus range lookups
  (172 → ~30 cols) + the verifier wiring its own docs describe.
- **Effort:** 0–2 lanes by branch. **Risk:** retire byte-safe; route semantic-change (posture
  improvement). **Dependencies:** independent.

### E16 — ops-layer routing: accumulator, envelope freight, anchor decider, shrink packing (rank 16)

- **(a)** The node re-wraps ALL retained turns from scratch per fold request
  (`node/src/mcp/handlers_verify.rs:151-160`); the O(1) online accumulator is built and unrouted.
  Cost: O(K) × ~80–130 s/node re-paid per request [M-scale from the apex measurements]. Fix:
  route the accumulator or cache leaf wraps by turn hash. ~1 lane.
- **(b)** Every whole-chain envelope carries and verifies the binding-descriptor proof declared
  non-load-bearing (`ivc_turn_chain.rs:1585-1588`, `:3839`; `accumulator.rs:58-60`) — ~100 KB
  [A-rough, unmeasured [U]] + O(n) `seam_pairs` accumulator state. Fix: optional/drop at the
  Epoch-2 FS re-pin (envelope v5); coordinate lightclient/wasm. Small.
- **(c)** Root-VK anchor identity: K-dependence is documented; member-MIX dependence is
  plausible and untested **[U]**. Decider: fold two 2-turn chains of different verbs, compare
  root VK fingerprints. Hours; if mix-dependent, make the wrap-normalized accumulator the sole
  anchor-bearing path (~1 lane).
- **(d)** Lever A shrink packing landed opt-in and the settlement path still proves at the
  default (`apex_shrink_gnark_export.rs:457-459`). One timed prove + flip the default. Hours.
- **Risk:** (a)(d) byte-safe; (b) regen; (c) decider byte-safe. **Dependencies:** independent.

### E17 — hygiene riders on the Epoch-2 regen (rank 17, each ≤0.5 lane)

- Tables-decl sync: declared-tables list is a facade (memory/map_ops declared by all 57, lookups
  grammar-forbidden; tid-84 used undeclared; decorative arities) and the D3 Δ47 arity fossil has
  now survived TWO regens — the fix is emit-side (sync `TableDef.arity` in the Lean weld layers,
  as the Rust welds already do), or it survives Epoch-2 as well. [P] regen.
- Welded placeholder members: noteSpend/noteCreate welded twins are producer-unexercisable
  placeholders inside an accepted-form registry the wire verifiers iterate
  (`EffectVmEmitUMemWeldWide.lean:71-72`; `effect_vm_descriptors.rs:1233-1237`) — filter them out.
  Adversarial-surface removal, not bytes. [P] regen.
- Fossil test registry: `rotation-wide-transfer-staged.tsv` (91 KB, one weaker shadow member)
  carries a byte-identity claim that is false at HEAD (`effect_vm_descriptors.rs:1203-1204`);
  demote to a test fixture or delete. [P] byte-safe.
- PI layout normalization: 36 of 68 PI slots bound by zero members (adds 1–7, 42–43 to D5's
  known set); wide-anchor start offset varies across 9 values (52/50/51/46/58/62/67/70/4) — the
  stale-index bug class. Fold fixed-position layout into the Epoch-2 PI-map regen. [P] regen.
- Duplicate gates + arity-3: seven capOpen members carry one literally duplicated gate; chip
  arity 3 has zero uses registry-wide — drop it from the admissible set at the one-hot retype.
  [P] regen.
- Strata freight: ~45 retired effect-VM JSONs (v1 + ir2-216 generations) still shipped/pinned/
  tested; `cap_delegation_nonamp` twin; hand `CrossSideExistenceAir`/`BundleTreeFoldAir` impls
  (with a width-8-vs-24 doc drift); binary membership twin. Quarantine or delete with the regen.
  [P] byte-safe.
- automatafl: hand-Rust AIR (813+773 lines, self-labeled "translation validation") still in-tree
  while the Lean-emitted step/resolve descriptors have zero in-tree consumers **[U]** — route or
  retire; the descriptors themselves are dense (no width wound). [P]/[U] semantic-change if routed.
- Byte-bus nibble pair-batching: 32 → ~20 interactions on transfer (−48 aux base cols ≈ −3K
  cells / 4–9 KB [A]) via paired lookups against a 256-row table — measure first: the dated
  PROOF-ECONOMICS measurement found the 2^8 table's LDE dominant at a different grid. [A] regen.
- Stale FRI-config docs at three load-bearing sites (`plonky3_recursion_impl.rs:380-391`,
  `ivc_turn_chain.rs:55,876-877`, `dregg_outer_config.rs:56-63`) — a lane retuning from the docs
  would mis-mint. Doc sweep, hours. [P] byte-safe.
- `edge_fp` claims fix (see E8). [P] byte-safe.

---

## Already tracked elsewhere (cross-references only)

- **Narrow-bus retirement** — Epoch-2 bundle (chip one-hot/tag retype, per-shape tuples); E7
  sequences after it; E14 is a second instance of the same built-but-unrouted pattern.
- **TURN_HASH limb widening** — Epoch-2 bundle; E9(b) rides the same tag retype.
- **Bare-V3 stratum retirement** — Epoch-2 bundle; E9's digest anchor is pinned to it today.
- **Heap-open wound** — tracked in the excellence backlog; E5/E6 touch the same map machinery but
  neither closes it. Related uncosted knob: HEAP_TREE_DEPTH=16 drives ~500 of MapOps' 897 cols
  (2^16 leaves per cell heap) **[U]**.
- **D5 PI-map regen / D6 chip-64 consolidation** — Epoch-2 scope; E17's PI item extends D5;
  E3+E6 subsume D6 follow-up #2 if taken.

## Graveyard — refuted, with corrections

- **REFUTED — registry-vestiges F1, transfer-level detail.** Claimed: 161 dead cols on transfer,
  including "cols 2..53 = 52 of 54 v1 selectors". Independent re-parse (verifier 2): **149** dead;
  cols 2–13 are referenced (transition hi/lo self-copies), the dead selector band is 14–53 (40 of
  54); registry total 8,847 not 8,851; share 8.5% not ~9%. Where registry-vestiges F1 and
  semantic-minimum F1 conflicted, semantic-minimum is correct; E1 carries the corrected numbers.
  The aggregate thesis (the dead-band class and its ~28–29 KB/proof cost) survives.

Corrections absorbed into confirmed items (adjusted, not refuted):

- E2: "638 ms at HEAD" was the pre-S2 [M] figure; post-S2 ≈ 425–440 ms [A]. "~17 leaf adapters"
  → 15. Flat "~3×" hashing → ~3.8× on the commit-phase term only; whole table < 3×.
- E4: "measured on a member ~4.6× smaller than today's" → 3.0× vs today's post-S2 proof (4.5× vs
  pre-S2). The 115–125 KB endpoint is [A] model projection; measured old-era delta was −11.5%.
  Capacity-128 is a drift canary, not headroom.
- E14: "one-word Lean change" understated — the weld also hard-codes the general boundary
  TableDef; still ~0.5 lane.
- E8: the finding's own doc-critique stands — "per-row PI slots equal the outer PI's" in the v2
  doc overstates; bindings are first/last row only.

## Open unknowns worth one probe each

- E1: identity of the 34–39-col dead bands on note/refusal/heap members (read the note-region
  emit before compaction).
- E10: what rejects a forged owner-limb on the 41-member no-freeze class (the falsifier).
- E13: setFieldDyn's `value == addr` mem-op oddity.
- E16(c): member-mix invariance of the K-fold root VK.
- Pre-freeze item 3: fold-side cost of the Epoch-2 floor-shape branches (absorb instance /
  preprocessed round) in every leaf-wrap circuit.
- AT-F8: whether the two 30-bit after-balance range teeth (wires 76/77, on 41/57 members) remain
  necessary once the wide chain + avail weld carry the balance limbs — needs the Lean weld
  semantics, not the wire.
- Descent's prove entry (assumed to ride the custom wide member; untraced).

## Top-3 recommended next moves after the Epoch-2 bundle

**1. Run the dead-band compactor (E1, folding E5).** This is the same shape as the S2 lane that
already landed and measured −181,757 B, so both the method (`compactS2` + `compactOk` gate) and
the pricing (188 B/col, [M]-calibrated) are proven; the delta is a per-member kill-set instead of
a uniform one, plus the map-ops arm split. Expected return is ~29 KB/proof mean across all 57
members and ~36–68 KB on the map-op members, all pure deletion at regen risk class. If the
Epoch-2 regen window is still open it rides for free; if not, this lane justifies its own regen
day and becomes the natural vehicle for the E6, E13, E14, and E17 riders — and for E3 if the
mutable-last schedule missed the freeze. One prerequisite probe: name the 34–39-col unidentified
bands (RV-F8) before the compactor eats the evidence.

**2. Resolve the arity probe and delete the double-prove (E2).** Once the bundle lands, the main
proof stops being the settlement bottleneck — the recursion stack is >99% of latency, and its
dominant term is commit-phase Merkle hashing inflated ~3.8× by a fold-by-2 choice that was
explicitly a diagnostic probe, never a decision. One lane exercises the recompose path at
arity >1 against a real `ir2_config` proof; if green, the per-turn re-mint deletes, the
config-type wall falls, and every leaf-wrap/agg/shrink circuit shrinks its hashing table — with
the −3-bit-per-fold soundness trade made explicitly through `dregg_fri_ledger` rather than
inherited from a comment. The gnark arity-8 `fold_row` is the long pole; bundle it with apex
lever B so the ETH wrap re-lands once.

**3. Run the FRI re-grid measurement lane (E4).** The deployed (6,19) point was tuned on a member
3× smaller than today's and ~4.8× smaller than the Epoch-2 floor; the gate's own floors already
admit (8,15,16) and (8,14,16), and the arithmetic says lb-8 at floor scale costs the prover what
lb-6 costs today. The lane is: re-run `ir2_fri_grid` at post-S2 and mocked-floor widths, push the
candidates through the Lean ledger (ε_C binds below the Johnson column, so the closed-form check
is not sufficient), and re-pin inside the same FS epoch the bundle already spends. Projected
return is ~151 → 115–125 KB [A] — and even the pessimistic measured-era −11.5% would make it the
cheapest large wire lever left, since below ~120 KB the only remaining levers are query count,
instance/round count, and Poseidon2 itself.
