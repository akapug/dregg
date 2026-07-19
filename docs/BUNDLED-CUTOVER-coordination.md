# BUNDLED-CUTOVER coordination — the ordered, minimal-window landing plan

2026-07-19. **STATUS: PLAN, NOT EXECUTION.** This document designs the coordinated landing of
every staged deploy-affecting circuit-minimality change plus the live lanes it collides with. It
was produced by a read-only lane against a tree that is **drifting hard** (HEAD advanced from
`189536ca3` to `8b7d26ace` during the grounding read; 191 dirty/untracked paths at read time).
**It MUST be adversarially reviewed, and every prerequisite in §8 must be settled/committed,
before any window opens.** Where a staged recipe is incomplete or a dependency unverified, it is
marked **[U]** — those are work items, not footnotes.

Grounding sources (all at-HEAD reads, cited inline throughout):
`docs/EFFICIENCY-BACKLOG-circuit-minimality.md` (the backlog + its BUNDLED-CUTOVER section, `1cfbdf657`),
`docs/E2-double-prove-deletion-design.md` (`5218759e3`), `HORIZONLOG.md` (entries 2026-07-18/19,
partly uncommitted), `docs/VK-REGEN-LOG.md` + `docs/VK-REGEN-CONTROLS.md`,
`docs/DECIDERS-rotated-arch-D1-D7.md`, `docs/ROADMAP-assurance-perimeter.md`, `git status`/`git diff`
of the working tree, and `git log` through `8b7d26ace`.

---

## §0 The problem, restated precisely

Multiple wins are individually proven/staged byte-safe but each requires an ACK-gated descriptor
regen (new member VK/FP bytes) and/or a recursion FS epoch (root-VK rotation). Regens cannot run
in parallel: `scripts/emit_descriptors.py` re-runs the whole emitter list and re-pins the whole
`GUARDED` FP set in one stamped event (`docs/VK-REGEN-CONTROLS.md` §1) — a second concurrent regen
clobbers the first, and the ACK (`DREGG_VK_REGEN_ACK` = the exact `HEAD:metatheory/Dregg2` tree
hash) names ONE reviewed tree. Meanwhile two live lanes are mid-flight in the SAME files: the IMT
arity-2→3 heap/fields leaf migration (regen already run, sitting **uncommitted** in the working
tree) and the E9/E12 joint-turn recursion surgery (−797 net lines across `joint_turn_*.rs`,
uncommitted). Nobody had designed the coordinated landing; this is that design.

**One structural fact shapes everything** (why the backlog's "ONE window" instinct is right):
a descriptor-bytes regen is not only a member-VK event. Per `docs/VK-REGEN-CONTROLS.md` (header +
§1), the deployed descriptor's AIR fingerprint feeds the recursive VK hash, and the leaf-wrap
circuits' shapes depend on member geometry (width/PI count), so the rotated-tree root-VK
fingerprint — the light client's trust anchor (`lightclient/src/lib.rs::verify_history`,
`expected_vk`) — is expected to rotate on ANY descriptor regen, not just on E2's arity flip.
**[U-verify in lane: confirm with `recursion_vk_determinism` before/after a descriptor-only regen;
if confirmed, splitting descriptor work and FS work into two windows costs light clients a second
anchor re-issue for nothing.]** This plan therefore lands everything epoch-bearing in ONE announced
window with serialized internal regen steps, after a settle phase that clears the live lanes.

---

## §1 Inventory — every in-flight/staged deploy-affecting change at HEAD

Epoch-class legend:
- **DESC** — descriptor-bytes epoch: registry TSV/JSON bytes move, member VK/FP re-pin
  (`*_FP` constants in `circuit/src/effect_vm_descriptors.rs` etc.), ACK-gated regen.
- **FS** — recursion FS epoch: recursion circuit shape / FRI transcript changes; proofs not
  interchangeable across the flip; root-VK rotation; light-client anchor re-issue.
- **VALUE** — published commitment values change (v9→v10 anchor flip); stored commitments strand.
- **NONE** — no epoch (byte-safe, dead-code deletion, or accept-surface-only).

| # | Change | State at HEAD | Epoch class | Registries / pins touched | Depends on | Staged recipe |
|---|--------|---------------|-------------|---------------------------|------------|---------------|
| B0 | **Epoch-2 bundle proper** (rate-8 absorb + chip one-hot/tag retype + per-shape tuples + H4+caveat + separate-absorb floor shape + narrow-bus retirement + TURN_HASH limb widening + D5 PI-map regen; the v9→v10 value flip) | DECIDED (`ARCH-REVIEW-rotated-commitment-chip.md`, `DECIDERS-rotated-arch-D1-D7.md`); emit-lane readiness **[U — not verified by this read; the backlog calls it "committed" as in decided, not built]** | DESC + FS + **VALUE** | both wide TSVs, `effect_vm_descriptors.rs`, `layout_generated.rs`, PI map | E3 decided BEFORE freeze (backlog "Decisions that expire" #1); D4 external sweeps BEFORE value flip (DECIDERS D4); E12 BEFORE the wide-tree flip (backlog #4) | backlog §BUNDLED-CUTOVER step 1 |
| IMT | **IMT arity-2→3 heap/fields leaf migration** ("heap8" co-tenant; the heap-open leaf wound fix) | **UNCOMMITTED IN WORKING TREE, regen ALREADY RUN** — Lean (`DeployedHeapTree`, `DeployedFieldsTree`, `MapMerkleRoot::linkHeap`, `EffectVmEmitRotationV3.{heap,fields}WritesTo8`, `HeapOpenEmit`/`FieldsOpenEmit`/`AccumulatorOpenEmit`/`AccumulatorInsertEmit`/`CarrierOctetGates`) + producer (`trace_rotated.rs` leaf col 2 = `next_addr`) + both wide TSVs + FP re-pins + `PROVENANCE.json` + the uncommitted `VK-REGEN-LOG` row `2026-07-19T01:12:18Z` (ACK+ALLOW_DIRTY, `source_dirty=YES`) | DESC (already spent, not yet published) | both wide TSVs, `effect_vm_descriptors.rs`, `PROVENANCE.json` | nothing — it un-reds honest heap-open paths that are RED at HEAD (HORIZONLOG "CLOSED 2026-07-19" bullet, uncommitted) | HORIZONLOG 07-18 S2 entry, heap-open sub-bullet |
| E9 | **Joint-turn binding-leaf + recursive-fold deletion** (option (a): `JointTurnAggregationAir`, `prove_joint_turn_recursive*`, `RecursiveJointTurnProof` deleted; test `joint_turn_recursive_rotated.rs` deleted; module re-doc'd to binding nodes) | **UNCOMMITTED IN WORKING TREE** (−797 net lines, `joint_turn_aggregation.rs` + `joint_turn_recursive.rs`) | NONE (dead scaffolding; the fold had zero production callers — backlog §E9; module-header HISTORY note in the working diff) | none | nothing; but E2 edits the SAME files — E9 must land before E2's step | working-tree diff; backlog §E9(a) |
| E12 | **Pin children on wide + joint tree folds** | Joint side RESOLVED by the E9 deletion (the unpinned joint fold is gone). Wide-tree side (`ivc_turn_chain.rs:2467-2468` bare `into_recursion_input`) **NOT visibly done** — `ivc_turn_chain.rs` is clean at HEAD **[U]** | FS if the wide tree is deployed-load-bearing; NONE if it is still the staged flip-precursor **[U — deployment status unverified]** | none (recursion circuits only) | must land BEFORE the wide-tree flip ships (backlog §E12) | backlog §E12 |
| E1 | **Per-member v1-face dead-band compaction** | Proof half LANDED committed (`58bbf7c09`; crown corollary + overdebit tooth); deployment staged in 5 steps; HELD-REGEN; its two files dirty from the IMT lane | DESC | both wide TSVs, `effect_vm_descriptors.rs` FPs, new `e1_compact_generated.rs`, `emit_descriptors.py` | IMT lands first (same files; kill-set/e1compact table must be emitted against post-IMT bytes); RV-F8 band naming DONE (HORIZONLOG ⑤); the PI-equality differential **does not exist yet** (HORIZONLOG ④) — build before window | HORIZONLOG E1 entry ①–⑥ |
| E7 | **By-name narrow-bus swap** (24 members, 387 cols) | Census + narrowing bridge LANDED committed (`9959af6cc`, `ChipNarrowLookup.lean`); regen staged, mechanical | DESC (by-name family) | `circuit/descriptors/by-name/*`, `layout_generated.rs`, `membership_descriptor_4ary.rs`, by-name goldens/`#guard`s | AFTER the Epoch-2 chip retype (backlog §E7 "does NOT inherit"); by-name lanes quiescent (automatafl churn, §5); the 3 NEW by-name members post-date the census **[U]** (§9) | backlog §E7 recipe (1)–(6) |
| E4 | **FRI re-grid flip** (lb 6→8, 19q→15/14, optional lfpl 4) | Measurement LANDED committed (`daa0a16`); flip staged | FS (member + recursion transcript; rides E2's epoch — a lone flip is a second flag day) | `descriptor_ir2.rs` IR2_FRI_* knobs; `fri_params_soundness_budget.rs` floors; `FriArityFiberDischarge.lean` | E2 first (E4's ledger verdicts are stated at arity 2^3 — E2 design §3.4); the (k3,b8) `friSetupK` instance is the ONE new Lean proof; floor re-pin documented | backlog §E4 recipe 1–5 |
| E2 | **Fold-arity 8 + double-prove retirement** | Probe GO committed (`1df4bc4cc`); execution-ready design committed (`5218759e3`) | FS (DEFINES the epoch: root VK rotates, retention envelope `RETAINED_FINALIZED_TURN_V1`→2, light-client anchors re-issue) | `plonky3_recursion_impl.rs:116`, `rotation_witness.rs`, `ivc_turn_chain.rs`, `turn_proving.rs`, ~15 leaf adapters | E9/E12 land FIRST (file collision — E2 design §4.1 ⚠ and §7.5); C2 corrupt-and-reject canaries in the SAME commit (§5 "the deletion without C2 is not a lane this document endorses") | E2 design §4.2 D1–D4 |
| E11 | **Golden-v1 accept-surface retirement + gate re-pin** | Prodread RESOLVED committed (`bd247bbaf`); recipe staged | NONE (accept-surface cutover; `compute_recursive_vk_hash` is its own VK universe and dies with the stratum) | none (no descriptor/member-VK/TSV bytes) | independent of the window; surface removal and gate re-pin NEVER split (backlog §E11) | HORIZONLOG E11 entry steps 1–5 |
| E8 | **Bilateral-v2 expected-block delete** (87→52) | Soundness core **IN WORKING TREE UNTRACKED** (`metatheory/Dregg2/Circuit/Emit/BilateralAggregationCompact.lean` — `expand_satisfies` + `contract_preserves` + the `gapTrace` middle-row-forgery exhibit) | DESC (bilateral descriptor re-emit) + semantic-change in the strengthening direction | `dregg-bilateral-aggregation-v2.json` successor, `bilateral_aggregation_air.rs` | its Lean file committed + whole-tree green first | file header (working tree); backlog §E8 |
| E5 | Map-ops instance split (897→421 arm) | Backlog-staged only; **no emit twin written [U]** | DESC | wide TSVs (map-carrying members) | CONTENDED with IMT cluster — after IMT lands | backlog §E5 |
| E6 | Absent-op deletion | Backlog-staged; **the gating Lean lemma (aafi discharges `opensTo none`) not written [U]** | DESC + Lean lemma | wide TSVs (7 absent carriers), MapAbsent AIR | the lemma is what keeps it out of semantic-change; after IMT | backlog §E6 |
| E13 | Memory-table retirement + degree-8 kill | Backlog-staged; `value == addr` oddity **[U]** unprobed | DESC | wide TSVs (setFieldDyn), Memory/MemBoundary AIRs, BUS_MEM_* | probe the oddity first | backlog §E13 |
| E14 | umem cohort-boundary flip | Backlog-staged (0.5 lane) | DESC | umem-welded TSV, `EffectVmEmitUMemWeldWide.lean:83-86`, byte-parity pin | none | backlog §E14 |
| E16(b) | Whole-chain envelope binding-descriptor drop (envelope v5) | Backlog-staged | FS re-pin (envelope shape) | envelope codec, lightclient/wasm | ride the window's FS epoch; coordinate lightclient/wasm | backlog §E16(b) |
| E17 | Hygiene riders (tables-decl sync, welded-placeholder filter, PI normalization, dup-gate/arity-3 drop, strata quarantine, transfer-probe fossil demotion) | Backlog-staged | DESC riders (some byte-safe) | wide TSVs, `rotation-wide-transfer-staged.tsv` (fossil), retired JSONs | ride the regen | backlog §E17 |
| E3 | Mutable-last limb schedule | **DECISION not made [U]** — hours (D1 simulator re-run) | (folds into B0's VALUE flip) | v10 absorption order (`cell/src/commitment.rs:1075-1083` mirror) | MUST be decided BEFORE the Epoch-2 freeze; couples with seed choice | backlog §E3 |
| E10 | Frozen-authority falsifier (+83-col dedup rider) | Falsifier **IN WORKING TREE UNTRACKED** (`circuit/tests/zzz_e10_freeze_owner_falsifier.rs`, owner-limb-precise on cellSeal) | falsifier NONE; dedup DESC rider | (dedup: wide TSVs, absorb tuples) | falsifier result decides whether dedup is safe | backlog §E10 |
| E15 | CCC route-or-retire | Size probe **IN WORKING TREE UNTRACKED** (`circuit/tests/zzz_ccc_size_probe.rs`); decision open **[U]** | NONE (retire) / semantic (route) | — | independent | backlog §E15 |
| — | **Non-campaign lanes sharing the files** (must settle for the clean window): zk HidingFriPcs byte-table degree fix (`descriptor_ir2.rs:5825`, dirty); gnark verifier-emit lane (`fri_verify_native.go` betas-return diff + untracked `emitted_*.go`); Dark-Bazaar / private-preference / private-shuffle by-name additions (3 new by-name JSONs + `emit_descriptors.py` newline-set entries, untracked/dirty); automatafl step/resolve by-name churn (3 regen events 07-18, `AutomataflStepRefine.lean` dirty WIP, Leg R deliberately unregistered); cert-f/cert-qp market descriptors (dirty/new) | working tree | mostly NONE (by-name additions already regen-stamped) | by-name/, `emit_descriptors.py`, gnark | — | §8 checklist |

**Explicitly NOT in any window:** bare-V3 stratum retirement. The backlog's Epoch-2 preamble lists
it in the bundle, but the 2026-07-18 grounding (HORIZONLOG "bare-V3 1-felt stratum: GROUNDED
consumer map") found live consumers (rotated-replay CLI floor, the 3 gentian Sat members with no
wide twins, the un-taken setfield-value8 epoch, ~30 tests) — the registry cannot retire yet. Its
retirement path is its own 5-step sequence ending in a LATER ACK-gated regen. Do not let the
window's scope silently re-absorb it.

---

## §2 The dependency graph

```
SETTLE (Phase 0)                          WINDOW 1 (the Epoch-2 flag day)
────────────────                          ──────────────────────────────────────────
IMT commit + clean re-stamp ──┬─────────► Step 1: B0 chip-retype bundle regen
  (unblocks E1's files,       │             (needs: E3 decided, D4 swept for VALUE,
   cycle-3 CI wiring,         │              D5 PI-map, E17 riders ready)
   un-reds heap-open paths)   │                       │
                              │                       ▼
E9 commit (joint_turn_*) ─────┼─────────► Step 2: E2 flip + retention-v2 + C2–C4
E12 wide pin land-or-classify─┘             (defines the FS epoch; E12 residual
  [U: FS-bearing?]                           rides here if FS-bearing)
                                                      │
E3 decision (hours) ────────► Step 1                  ▼
D4 external sweeps ─────────► Step 1 (VALUE) Step 3: E4 re-grid + (k3,b8) discharge
E11 cutover (independent,                     + documented floor re-pin
  no regen — before window,                           │
  own canary + gate re-pin)                           ▼
E8 Lean commit ─────────────► Step 5 rider  Step 4: E7 by-name regen (24 members;
E10 falsifier run ──────────► E10 dedup       after chip retype; by-name quiescent;
  rider go/no-go                              new-member census decision [U])
PI-equality differential                              │
  BUILT (does not exist) ───► Steps 1,4,5             ▼
E6 Lean lemma / E5,E13,E14   Step 5: E1 compaction + READY riders
  emit twins (each [U]) ────►   (E5,E6,E13,E14,E8,E10-dedup,E16(b),E17)
                                — unready riders DROP to a later epoch,
                                  never hold the window
                                                      │
                                                      ▼
                              CLOSE: apex re-verify → ETH re-land (apex lever B)
                              → anchor distribution → strict-clean PROVENANCE
                              → dregg-epoch registry_fp → VK-REGEN-LOG rows
```

Conflict pairs (same bytes, cannot bundle blindly):
- **E1 ↔ IMT**: same two TSVs + `EffectVmEmitRotationV3.lean` + `trace_rotated.rs`. E1's
  `deadColsE1` derivation is per-member-recomputed so it survives the IMT re-shape, but the
  emitted `e1compact` table and the width gates must be generated against POST-IMT bytes. IMT
  first, strictly.
- **E5/E6 ↔ IMT**: the map-ops/absent machinery is exactly what IMT re-shaped (backlog marks both
  CONTENDED, IMT-migration cluster). Their emit twins must be authored against the post-IMT
  emitters.
- **E2 ↔ E9/E12**: `joint_turn_aggregation.rs`/`joint_turn_recursive.rs` carry
  `ir2_leaf_wrap_config` mint sites that ride E2's knob flip; both files are owned by the live
  surgery. E9 lands first; E2's design says exactly this (§4.1 ⚠, §7.5).
- **E2 ↔ gnark-emit lane**: `chain/gnark/fri_verify_native.go` is dirty from the verifier-emit
  lane (betas-return signature change) and E2's optional arity-8 `fold_row` targets the same file.
  E2-alone does NOT require the gnark change (E2 design §3.3 — the OUTER config may stay arity-2);
  the handshake is only "gnark lane commits before the window closes" so the ETH re-land
  (bundled with apex lever B) lands on a settled file.
- **E7 ↔ automatafl / new-by-name lanes**: the drift gate recurses into `by-name/`, and E7's regen
  re-emits the whole family. The automatafl Leg-R descriptor is deliberately NOT registered until
  complete (HORIZONLOG 07-18) — E7's regen must not accidentally register or clobber WIP; quiesce
  the by-name lanes for step 4.
- **E4 ↔ E11**: both move `fri_params_soundness_budget.rs` floors. Not a conflict if sequenced
  (E11 pre-window: shipped() 7→6, Johnson 71→73; E4 in-window: the lb-8 re-pin) — two clean
  documented motions instead of one entangled one.
- **E1 ↔ E4 (soft)**: E1 changes member widths → wrap trace heights can move → the
  height-dependent `commitBits` column should be RE-READ from the ledger at window close, after
  step 5, not assumed from step 3 (E2 design §3.4.4).

---

## §3 The minimal window partition

**Answer: ONE ACK-gated window (the Epoch-2 flag day) with five serialized regen/flip steps,
preceded by a settle phase, plus one independent non-regen cutover (E11).** The already-spent IMT
regen is committed in the settle phase — it is not a second "window" by choice but a sunk epoch
that must publish before anything else can (its bytes sit uncommitted in the exact files every
other change needs, its stamp is `source_dirty=YES` and therefore `--strict`-refused for
deployment, and the honest heap-open producer paths are red at HEAD without it).

Rationale against two windows (descriptor-window + FS-window): if the root-VK-rotates-on-any-regen
inference of §0 holds **[U]**, two windows mean two light-client anchor re-issues and two
mutually-unverifiable epoch boundaries for zero isolation benefit — the canary gauntlets overlap
almost entirely. If the inference FAILS (descriptor regens leave the root VK stable), the
partition below still works; only the anchor-distribution step at close becomes E2/E4-only.

### Phase 0 — SETTLE (no ACK, no new epoch decisions; ordered but parallelizable where disjoint)

P0.1 **Land the IMT migration** (§4 has the full handshake). Commit the Lean + producer + TSVs +
FP pins + `PROVENANCE.json` + the `VK-REGEN-LOG` row as ONE named-file commit series; then re-run
`scripts/emit-descriptors.sh` on the now-clean tree — byte-identical output is an ungated no-op,
and a `stamp-existing`/re-emit replaces the dirty stamp with a strict-clean one
(`VK-REGEN-CONTROLS.md` §2, bootstrap note). Gate: heap-open honest canaries green
(wide roundtrips noteSpend/noteCreate/createCell, heapWrite honest verify), `check-descriptor-drift.sh`
PASS, whole `Dregg2` green including `MapMerkleRoot` (un-blocks cycle-3 CI wiring —
`ROADMAP-assurance-perimeter.md` "pending the co-tenant heap8/S2 landing").

P0.2 **Land the E9 surgery** (commit the joint_turn_* deletions + module re-doc + test deletion).
Gate: whole-tree build; `*_binding_deployed_tooth.rs` suite green; no epoch artifacts.

P0.3 **Resolve E12's residual**: read `ivc_turn_chain.rs:2467-2468` at the then-HEAD; if the wide
tree is production-load-bearing, schedule the pin inside Window step 2 (it shares E2's FS epoch);
if it is still the staged flip-precursor, land the pin now as a plain commit. **[U — this
classification is the lane's first task.]**

P0.4 **Commit the stray co-tenant lanes** touching window files: the zk HidingFriPcs fix
(`descriptor_ir2.rs`), the gnark verifier-emit lane, the E8 Lean proof file, the E10/E15 probes,
the by-name additions + `emit_descriptors.py` entries, the automatafl WIP to a stable point
(Leg R stays unregistered), HORIZONLOG/VK-REGEN-LOG doc rows. Nothing here mints an epoch; all of
it must stop being dirty (§8).

P0.5 **Make the expiring decisions**: E3 (re-run the D1 simulator mutable-last, pin the v10
schedule — couples with the seed choice, decide together; backlog §E3); the E4 query-count choice
(15 vs 14 — capacity sits EXACTLY at the 128 drift margin, zero headroom; choose eyes-open) and
the lfpl-4 rider; E7's optional SenderAuthorized waist-fix rider (semantic-change — in or out).

P0.6 **Run the D4 external-holder pre-flight** (DECIDERS D4 verdict): (1) sweep hbox + dev
laptops for `dregg_persist` redb stores / starbridge-v2 World images carrying
`LedgerCheckpoint.sovereign_commitments` (`persist/src/ledger_store.rs:39-48`) — the ONE artifact
class the VALUE flip strands; (2) Base-Sepolia fixture `DreggSettlement` (`0x6c87…Bd87`):
redeploy-or-declare-dead; (3) note the standing UNKNOWN — third parties running the standalone
verifier binary cannot be enumerated from the repo.

P0.7 **E11 cutover** (independent lane, before the window so the budget-gate floors settle):
delete the Golden-v1 stratum + accept surfaces + gate re-pin IN ONE COMMIT (HORIZONLOG E11 recipe
1–5); canary = a pre-deletion-minted Golden-v1 fixture chain flips VERIFIED→REJECTED; `cv`-audit
that no new caller of the deleted names appeared since the census.

P0.8 **Build the missing gauntlet tooling**: the value-level PI-equality differential
(old-vs-new registry, per-member — named as NOT EXISTING in HORIZONLOG E1 ④); decide whether
Control 4 (covered-relation non-regression, `VK-REGEN-CONTROLS.md` §2 — design-only) is built for
this window or explicitly waived in the review. Waiving it silently is exactly the "name-only
diff" laundering the controls doc warns about — say it out loud either way.

P0.9 **E10 falsifier run** (byte-safe, already in-tree): its result decides whether the 83-col
dedup rider is admissible in step 5 or the 41-member class needs a semantic fix first.

**Phase-0 exit gate (the clean-window requirement, §8 in checklist form): `git status` clean;
whole-workspace build green; full `Dregg2` green; `check-descriptor-drift.sh` PASS;
`--verify-provenance --strict` PASS.**

### Window 1 — the Epoch-2 flag day (one announced epoch; ONE operator owns the regen lock; each step's gauntlet passes before the next step starts)

Every regen step uses the same mechanics: commit the Lean/Rust source first, then
`DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)" scripts/emit-descriptors.sh` on the
CLEAN tree (never `ALLOW_DIRTY` inside the window — a dirty mint is `--strict`-refused and
unreviewable), review the printed change set, commit descriptors + FP files + `PROVENANCE.json` +
the `VK-REGEN-LOG` row together (`VK-REGEN-CONTROLS.md` §3). The ACK re-derives per step because
each step advances `HEAD:metatheory/Dregg2`.

**Step 1 — B0 chip-retype bundle regen (DESC + VALUE).**
Scope: chip one-hot/tag retype + per-shape tuples, rate-8 absorb at the E3-decided schedule,
H4+caveat, separate-absorb floor shape, narrow-bus retirement, TURN_HASH limb widening, D5 PI-map
regen + E17 PI-layout normalization + tables-decl sync + dup-gate/arity-3 drop. The VALUE flip
(published v10 anchors) happens here, gated on P0.6.
Files: the Epoch-2 emit lanes under `metatheory/Dregg2/Circuit/Emit/` **[U — build state
unverified; this step CANNOT be scheduled until its emit lanes exist and are green]**, both wide
TSVs, `effect_vm_descriptors.rs`, `layout_generated.rs`.
GO/NO-GO: full §6 gauntlet; the D6 per-member chip-height table re-measured (34/57 → 64 as
specced); NO-GO reverts the step's commits (§7).

**Step 2 — E2 flip + double-prove deletion (defines the FS epoch).**
Ordered per the E2 design §4.2: D1 knob flip (`INNER_FRI_MAX_LOG_ARITY` 1→3) + doc retirements →
D2 leg extraction (+ the §7.1 PI-completeness check; fall back to bare-leg retention) → D4
retention envelope v1→2 (fail-closed on arity-2 blobs) → D3 type collapse (~15 adapters) →
posture re-pin (112→109 via `dregg_fri_ledger`, stated in the commit). E12's wide-tree pin rides
here if P0.3 classified it FS-bearing. E16(b)'s envelope-v5 binding-descriptor drop rides this
epoch too (coordinate lightclient/wasm in the same step).
HARD GATE: C2 (arity-8 corrupt-and-reject: commit-phase sibling, folded eval, schedule byte,
final-poly coefficient — the WRAP must reject each) lands IN THE SAME COMMIT as the deletion; plus
C1/C3/C4/C6 (E2 design §4.4). No regen of descriptor bytes in this step (`ir2_config` unchanged).

**Step 3 — E4 re-grid (rides step 2's epoch).**
Flip `IR2_FRI_LOG_BLOWUP` 6→8 + `IR2_FRI_NUM_QUERIES` per P0.5 (+lfpl if chosen) → land the
(k3,b8) `FriArityFiberDischarge.friSetupK` instance (the ONE new Lean proof — without it the new
perFold rides an undischarged hypothesis) → documented floor re-pin in
`fri_params_soundness_budget.rs` via the exported ledger → price ε_C (commit 67→60) and NAME the
chosen posture in the cutover commit; state the cumulative 112→105 spend in one sentence (E2
design §3.4.5).
GO/NO-GO: budget gate green at the new pins; the `fri_regrid_post_s2_measure` baseline tripwire
goes red BY DESIGN — re-ground its candidate table in the same commit; measured prover-time budget
(~4×) explicitly accepted for the recursion wrap path.

**Step 4 — E7 by-name regen (DESC, 24 members).**
The backlog §E7 recipe verbatim: per-module wide→narrow lookup swap + lane-col deletion + dense
renumber (+ note-spend-leaf's 8 unref cols + derivation col 0) → re-point Refine/Rung2 proofs at
`chip_lookup_narrow_sound_of_wide_table`/`narrow_lookup_holdsAt_sound` → GOLDEN regen via
`emitVmJson2` + by-name re-emit (drift gate recurses) → Rust layout twins
(`MEMBERSHIP_4ARY_WIDTH` 18→11, `LANE_BASE` deleted; prover side already live) → per-member honest
prove+verify + each module's forge teeth. Include the P0.5-decided waist-fix rider or not.
Pre-step handshake: by-name lanes quiescent; DECIDE the three new N4K4/shuffle members
(census-extend or explicitly out-of-scope — they post-date the 26-member census **[U]**);
automatafl Leg R stays unregistered.

**Step 5 — E1 compaction + ready riders (DESC).**
E1 per the HORIZONLOG recipe ①–④: emit-driver `compactE1` after `compactForEmit`, the
`e1compact` companion lines → `e1_compact_generated.rs` + `compact_e1_columns` sequenced AFTER
`compact_s2_columns` at every producer site (both registries) → `emit_descriptors.py` parse +
ACK regen → width gates adjusted + the PI-equality differential run + prove/verify + executor +
proof-size re-baseline. Riders that are READY ride the same regen: E5/E6 (if their emit twins +
E6's lemma landed), E13, E14, E8 (its Lean core is proven; the regen re-emits bilateral v3),
E10-dedup (if the falsifier cleared it), E17 strata quarantine + transfer-probe fossil demotion.
**Any rider whose prerequisite is not green at step-open DROPS to a later epoch — riders never
hold the window.**
Watch: `check-drift-taxonomy.sh` — E1 SHRINKS; verify the shrink is not mis-flagged as a widen
(`DREGG_ALLOW_REGENESIS` stays unset).

**Window close.**
(1) apex re-verify over the final shape (C5: apex shrink over an arity-8 apex — the layer the
probe did not exercise) + re-read the height-dependent commit-ledger column post-E1;
(2) ETH wrap re-land bundled with apex lever B (gnark `fold_row` only if the OUTER config
escalated — E2 design §3.3); (3) whole-history demo + light-client verify path
(`verify_history` three teeth, wasm bindings, `grain-verify/src/r3.rs`); (4) distribute the new
root-VK anchor (the flag-day `git push` + client rebuild, `HANDOFF-v13-VK-EPOCH.md` §1c);
(5) `--verify-provenance --strict` on the final stamp; (6) `dregg-epoch` `registry_fp`
re-derives (wide+weld FPs — the epoch handshake must SEE this flag day; it was blind to S2-class
flips until the 07-18 fix); (7) the VK-REGEN-LOG rows and a HORIZONLOG close-out entry.

---

## §4 The IMT-migration handshake (question 3, answered precisely)

**Does the optimizer cutover collide with the IMT migration? YES — maximally.** The IMT lane's
uncommitted change set IS the window's substrate: both wide TSVs, `effect_vm_descriptors.rs`,
`PROVENANCE.json`, `trace_rotated.rs`, `EffectVmEmitRotationV3.lean`, and the map/heap Lean
(`MapMerkleRoot` et al.) that E1/E5/E6 build on. E1's staged recipe names its own two files as
"DIRTY from a live lane — settle before flipping" (backlog §E1); the cycle-3 roadmap is blocked on
the same landing.

**Must it bundle with Window 1, or land first? LAND FIRST — it cannot honestly bundle.** Three
reasons: (a) its regen ALREADY RAN (the uncommitted `2026-07-19T01:12:18Z` log row) — the epoch is
spent; bundling would mean carrying a dirty tree for the entire pre-window period, which the ACK
gate is designed to refuse; (b) its stamp is `source_dirty=YES`, which `--verify-provenance
--strict` refuses — the deployable path REQUIRES a clean re-stamp, which requires committing;
(c) it is a red-to-green fix (honest heap-open producer paths fail at HEAD by the arity mismatch)
— holding a correctness fix hostage to an efficiency flag day is backwards.

**The required handshake, stated as an interface:**
1. The IMT lane commits its full set (Lean + producer + TSVs + FPs + PROVENANCE + log row) as
   named files — no `git add -A` (live siblings) — and posts the landing in HORIZONLOG.
2. The window operator re-runs the emitter on the clean tree: byte-identical ⇒ ungated no-op,
   then replaces the dirty stamp (strict-clean). If NOT byte-identical, the lane and the tree have
   diverged since 01:12Z — STOP; the diff is reviewed before anything else happens.
3. Only then do E1/E5/E6 author their emit halves (against post-IMT emitters) and only then does
   the Phase-0 exit gate run.
4. The named IMT residue stays OUT of the window: the SCALAR §2–§5 `MapMerkleRoot`
   `opensTo`/`writesTo` still fold arity-2 `leafOf` (banner'd, 1-felt lane-0 denotation — part of
   the bare-V3 retirement arc, not this window).

---

## §5 By-name / automatafl / gnark lane handshakes (the smaller collisions)

- **automatafl**: three by-name regen events on 07-18 alone; `AutomataflStepRefine.lean` dirty at
  read time; Leg R byte-pinned in-file but deliberately unregistered. Handshake: the lane declares
  quiescence before step 4; E7's re-emit must reproduce automatafl-step/resolve byte-identically
  (they are zero-killable per the census) — any diff there is a red flag, not a rider.
- **New by-name members** (dark-bazaar-private-n4k4, private-preference-n4k4, private-shuffle-n8):
  landed after the E7 census; all use full-arity-16 permutations with all output lanes public, so
  the graduated-lane kill likely does not apply — but "likely" is not a census. Step-4 pre-task:
  extend the per-column parse to the three (hours) or name them out-of-scope in the regen commit.
- **gnark verifier-emit lane** (`fri_verify_native.go` + untracked `emitted_*.go`): commits in
  Phase 0. E2-alone needs nothing from gnark; the ETH re-land at window close is the single
  coordination point (bundled with apex lever B so the wrap re-lands exactly once).

---

## §6 The canary gauntlet (per step; GO = all green, NO-GO = §7)

Before EVERY step (baseline) and after (verdict):

| Tooth | What it proves | Source |
|---|---|---|
| `check-descriptor-drift.sh` PASS | JSON↔Lean agreement; no unreviewed bytes | VK-REGEN-CONTROLS §1 |
| `--verify-provenance --strict` | stamp matches bytes, clean source, right tree | VK-REGEN-CONTROLS Control 1 |
| Per-member honest prove+verify (`effect_vm_wide_roundtrip`, `wide_new_members_cover`, executor `sdk/tests/executor_welded_commit.rs`) | completeness: no honest witness lost | HORIZONLOG E1 ④ |
| **PI-equality differential old-vs-new** (built in P0.8) | value preservation member-for-member | HORIZONLOG E1 ④ (named missing) |
| Forge/overdebit teeth: `deployedCompact_rejects_overdebit` / `deployedE1_rejects_overdebit` (kernel `decide`), per-module by-name forge teeth, the stapleable-slot canaries | soundness did not narrow | E1/S2 crown entries; backlog §E7(5) |
| E2 C1–C6, C2 MANDATORY in-commit (arity-8 corrupt-and-reject at the WRAP) | the surviving in-circuit path binds everything | E2 design §4.4–§5 |
| `fri_params_soundness_budget` at re-pinned expectations (incl. the arity-drift recovery tooth keeping the 2016/112 arity-2 row as counterfactual) | soundness spend priced through the ledger | E2 design §2.2 |
| `recursion_vk_determinism` (in-process + cross-process) | the new root VK is deterministic | E2 design §4.1 |
| Light-client path: `verify_history` three teeth + wasm `bindings_lightclient` + `grain-verify/src/r3.rs`; cross-epoch replay (C4): pre-flip root FAILS the post-flip anchor, v1 retained blob REFUSED at decode | anchor rotation is fail-closed both ways | E2 design §4.3–4.4 |
| `check-drift-taxonomy.sh` on shrink steps | a shrink is not laundered as regenesis | HORIZONLOG E1 ③ |
| Proof-size re-baseline (`MEASURE-legacy-1felt-chain-drop.md` lineage) + `fri_regrid_post_s2_measure` re-grounded | the claimed bytes are the measured bytes | backlog §E4(5) |
| Whole-tree build + full `Dregg2` + `#assert_axioms` prints | no red umbrella behind per-file green | swarm doctrine |

GO/NO-GO decision rule: a step is GO only when its full row-set is green ON THE STEP'S FINAL
COMMIT (not on intermediate states), and the NEXT step may not open before the verdict is logged
in HORIZONLOG. Any red that traces to a crate the step did not touch = "blocked on churn" —
back off and re-verify, do not force (the tree is shared).

---

## §7 Rollback + blast radius

**Mid-step failure recovery.** Every regen is deterministic from committed Lean, so rollback =
`git revert` the step's commit series, then re-run the emitter with a fresh ACK at the reverted
`HEAD:metatheory/Dregg2` — the tree returns to the prior step's bytes exactly, and the
byte-identical re-emit is an ungated no-op confirming it. `docs/VK-REGEN-LOG.md` is append-only:
a rollback APPENDS a new row (the revert regen), never edits — the log shows the failed attempt,
which is the point. NEVER `git stash`, never `git checkout` across others' WIP; the revert is
commit-scoped to the step's named files.

**What breaks at each epoch boundary (the blast table):**
- **DESC steps (1, 4, 5):** every verifier pinned to the old FPs refuses new proofs after
  rebuild; old proofs refuse against new binaries. Deployment reality check: flip = push +
  rebuild; the devnet game ledger is non-durable (hand-run `:8420`, lost on reboot — standing
  record), and D4 found no live external v9 holder — the blast is currently small AND that is a
  fact about today, re-verify at window time (P0.6).
- **VALUE flip (step 1):** stored `sovereign_commitments` in any redb `LedgerCheckpoint` /
  starbridge World image strand (the D4 artifact class); `commit_log` roots are recomputable.
  The P0.6 sweep is the pre-flight; a hit = migrate-or-declare-dead BEFORE the step.
- **FS steps (2, 3):** retained pre-flip `FinalizedTurn` blobs are arity-2/old-grid — refused
  fail-closed by the retention envelope v1→2 bump (E2 design D4/C4), by deliberate decision
  rather than mixed-schedule folding. Light clients: the old anchor verifies nothing new; the new
  anchor verifies nothing old — the re-issue at window close is the ONE distribution event.
  Whole-chain envelopes: v5 (E16(b)) refuses v4 if taken.
- **E11 (Phase 0):** `dregg-verifier scope-recursive` disappears (user-visible CLI change); any
  holder of a Golden-v1 recursive artifact loses verification — the census says that producer
  path has zero callers, and the canary proves the flip.

**If the window must abort entirely** (e.g., step 1's gauntlet fails structurally): the tree
reverts to the Phase-0 exit state, which is itself a coherent deployable epoch (post-IMT,
post-E9/E11). The window re-opens after the fix with fresh ACKs. Nothing in this plan leaves the
tree between epochs.

---

## §8 Pre-cutover settle checklist (the clean-window requirement, enumerated)

The ACK gate needs a reviewable clean `metatheory/Dregg2` and the stamp needs a clean SOURCE tree.
At read time the following are dirty/untracked and must be committed, landed elsewhere, or
deliberately reverted before Window 1 (owner in parentheses where known):

1. **IMT migration set** (P0.1): `DeployedHeapTree.lean`, `DeployedFieldsTree.lean`,
   `MapMerkleRoot.lean`, `EffectVmEmitRotationV3.lean`, `HeapOpenEmit.lean`, `FieldsOpenEmit.lean`,
   `AccumulatorOpenEmit.lean`, `AccumulatorInsertEmit.lean`, `CarrierOctetGates.lean`,
   `trace_rotated.rs`, both wide TSVs, `effect_vm_descriptors.rs`, `PROVENANCE.json`,
   `VK-REGEN-LOG.md` row, HORIZONLOG bullets. (heap8 co-tenant lane)
2. **E9/E12 surgery** (P0.2): `joint_turn_aggregation.rs`, `joint_turn_recursive.rs`, deleted
   `joint_turn_recursive_rotated.rs`, `circuit-prove/src/lib.rs`. (E9 lane)
3. **E8 soundness core**: untracked `BilateralAggregationCompact.lean` + its `Dregg2.lean`/
   `EmitByName.lean` import wiring.
4. **zk fix**: `descriptor_ir2.rs:5825` HidingFriPcs byte-table degree pin. (dark-bazaar lane)
5. **gnark verifier-emit lane**: `fri_verify_native.go` + untracked `emitted_*.go` + tests.
6. **By-name additions**: 3 new N4K4/shuffle JSONs + `emit_descriptors.py` newline-set +
   `Market/*.lean` + `Games/Private*.lean` dirt.
7. **automatafl WIP**: `AutomataflStepRefine.lean` + related — to a declared-stable point;
   Leg R unregistered.
8. **Probes**: `zzz_e10_freeze_owner_falsifier.rs`, `zzz_ccc_size_probe.rs`,
   `zzz_apply_delta_bench.rs`.
9. **Everything else in `git status`** — 191 paths at read time, including large non-circuit
   fronts (fhegg, dreggnet-web, discord-bot, app-framework, sdk-py/ts, deploy units). None of it
   mints circuit epochs, but ALL of it must stop being dirty for the strict stamp; the realistic
   path is that those fronts keep landing on their own cadence and the window opens in a lull —
   the operator checks `git status` clean AT WINDOW OPEN, not days before.
10. **Decisions closed**: E3 schedule (P0.5), E4 q/lfpl choice, E7 waist-rider in/out, E12
    classification (P0.3), E15 route-or-retire (or explicitly deferred), the three new by-name
    members' E7 scope, Control-4 built-or-waived (P0.8).
11. **Sweeps done**: D4 external holders (P0.6); `cv`-audit for new callers of E11-deleted names.
12. **Tooling built**: the PI-equality differential (P0.8).

Recommended sequencing of the settle itself: **the live lanes land first, then the cutover** —
IMT (P0.1) and E9 (P0.2) are the critical path; everything else in Phase 0 is parallel to them.

---

## §9 Honest UNKNOWNs and incomplete recipes (each blocks or bounds a step)

1. **Does a descriptor-only regen rotate the deployed rotated-tree root VK?** Inferred yes from
   VK-REGEN-CONTROLS + leaf-shape dependence; not directly measured. Decides whether steps 1/4/5
   share step 2's anchor re-issue or are anchor-neutral. Cheap check: `recursion_vk_determinism`
   fingerprint before/after step 1. (§0)
2. **B0's emit-lane readiness.** The Epoch-2 bundle is DECIDED (arch-review/DECIDERS) but this
   read did not verify that its Lean emit changes exist/build. If they are unbuilt, step 1 has a
   multi-lane construction phase in front of it and the window date moves — the partition is
   unaffected, the schedule is. (§1 B0)
3. **E12 wide-tree deployment status** — FS-bearing or precursor-only. (P0.3)
4. **E7 × the three new by-name members** — census not extended. (§5)
5. **E5/E6/E13 emit twins + E6's Lean lemma** — not written; they are step-5 riders ONLY if
   green by step-open. E13's `value == addr` oddity unprobed. (§1)
6. **E2 §7 unknowns** carry over verbatim: served-leg PI completeness (D2 fallback exists);
   outer-shrink trace-shape stability at arity-8 apex (decides gnark byte-stability); the
   at-height ~18→~6 rounds confirmation; whether plonky3 native verify enforces schedule ≤ max
   (the envelope refusal is designed as the wall regardless).
7. **Step 1+5 merge option**: if ALL of E1's and the riders' emit halves are green before the
   window opens, steps 1 and 5 can collapse into one regen event (fewer stamps, one gauntlet).
   Kept separate here because the backlog sequences them apart and the canary isolation is worth
   more than a saved stamp; the merge is an operator call at window open, not a plan change.
8. **Control 4** (covered-relation non-regression) remains design-only; this window runs on the
   PI-differential + forge teeth + crown corollaries unless P0.8 builds it. Named, not hidden.

---

## §10 Compact critical path (the one-line version)

IMT commit+re-stamp → E9 commit → [E11 cutover ∥ E3/E4/E7 decisions ∥ D4 sweeps ∥ PI-differential
build ∥ E12 classify] → clean-tree gate → **Window:** B0 chip-retype regen (+VALUE, gated on D4)
→ E2 flip (+retention v2, C2 in-commit; FS epoch defined) → E4 re-grid (+k3,b8 discharge, floor
re-pin) → E7 by-name regen → E1 + ready riders regen → apex re-verify + ETH re-land (lever B) +
anchor distribution + strict-clean stamp. Riders drop rather than hold; bare-V3 retirement stays
out; every step's gauntlet gates the next.
