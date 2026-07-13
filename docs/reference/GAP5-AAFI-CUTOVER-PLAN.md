# GAP #5 AAFI-IMT Cutover — Complete Executable Scope

**Status:** execution plan (read-only analysis; no code changed by this doc). The lane ember (or a
follow-up swarm) runs from. **Date:** 2026-07-13.
**Grounds:** `docs/reference/CARRIER-CENSUS.md` GAP #5 (closure obstruction), `docs/reference/
LIGHTCLIENT-AAFI-IMPACT.md` (AAFI low-pain, sync=replay), `metatheory/Dregg2/Circuit/
IndexedMerkleTree.lean` (Lean IMT closure PROVEN), `circuit/src/heap_root.rs` (deployed arity-3 leaf
+ `AafiInsertWitness8` storage half, ADDITIVE).

**What is already landed (verified against HEAD):**
- Lean IMT closure PROVEN — `IndexedMerkleTree.lean`: `imtInsert_preserves`,
  `canonicalHeapExtract_of_imt`, `imt_double_spend_unsat` (531f2a009), all `#assert_axioms`-clean.
- Deployed arity-3 IMT leaf `HeapLeaf { addr, value, next_addr }` + arity-3 `digest()`/`digest8()`
  (`heap_root.rs:106-141,584`) + MapAbsent pointer-bracket (the `.absent` arm is CLOSED,
  `descriptor_ir2.rs:2875-2917`, 919b2b0b8).
- AAFI storage half: `insert_witness_aafi` + `AafiInsertWitness8` + `next_free_index` on
  `CanonicalHeapTree8` (`heap_root.rs:912-1024,1129-1161`), ADDITIVE, differential-checked vs the
  proven Lean `imtInsert` (d42188fd3). This produces the two-path witness the AIR cutover consumes.

**What remains (this plan):** the INSERT arm is still OPEN. The deployed per-turn insert (op=3,
`descriptor_ir2.rs:2727-2857`) opens ONE leaf against `new_root` over the SHARED sibling path —
sound for value-updates (stable position) but NOT for insert (the compacted-array suffix shifts;
no shared pre-image binds the shifted region). The committed root's sortedness is therefore a
PRODUCER-TRUST assumption. This plan routes the three append-only accumulators to the AAFI
two-path insert (stable positions), consuming `AafiInsertWitness8`, closing the double-spend.

---

## PART 1 — THE ROUTING SPLIT

### 1.1 The effect → accumulator → tree → op map (ground truth)

Insert map-ops are `MapOp` records defined in `metatheory/Dregg2/Circuit/Emit/
EffectVmEmitRotationV3.lean`, appended to the rotated V3 descriptors; the authoritative per-effect
partition is `AlgoStarkSoundFanoutMemory.lean:261-316`. All ride ONE `Ir2Air::MapOps` table
(`descriptor_ir2.rs:2727`), partitioned by the `op` code column (`MAP_OP`).

| Effect | Accumulator | Rotated limb | Fresh/absent op | Insert op (`op=3` today) | Def @ EffectVmEmitRotationV3.lean |
|---|---|---|---|---|---|
| NoteSpend | **nullifier set** | limb 26 | `nullifierFreshOp` `.absent` | `nullifierInsertOp` | :2271 / :2282 |
| NoteCreate | **commitment set** | limb 27 | (none — grow-only) | `commitmentsInsertOp` | :2477 |
| Revoke | **revoked set** | revocation root | (hole — see §1.4) | (insert gate NOT deployed) | — (`cell/src/revoked_set.rs`) |
| CreateCell/factory/spawn | cells/accounts set | limb 0 | `cellsFreshOp` `.absent` | `cellsInsertOp` | :2590 / :2601 |
| Attenuate/grant/introduce | cap graph (`cap_root`) | limb 25 | (cap-open appendix) | `insertWriteOpRot` | :1820 |
| HeapWrite | mutable cell heap | in-cell heap_root | (n/a — update) | `.write` (op=1) | — |

**Switches to the AAFI path (this cutover):** `nullifierInsertOp` (26), `commitmentsInsertOp` (27),
and the **revoked** insert (§1.4). These are the grow-only sets whose canonical insertion order =
the tau-finalized spend/create/revoke sequence (INV-6), and GAP #5's double-spend lives precisely
in their absence proofs.

**Stays on the current scheme (decided separately):** `cellsInsertOp` (cells existence set) and
`insertWriteOpRot` (cap graph) keep `op=3` for now — the cells set is grouped with the mutable cell
heap in the impact analysis (needs the `addr→slot` persistence decision); `.read`/`.write` (op 0/1)
for the mutable cell heap are untouched.

### 1.2 Recommendation: option (b) — a new `MapKind::AafiInsert` (code 4) op-mode, NOT a distinct tree/AIR

Reasons:
1. The producer already landed — `AafiInsertWitness8` on `CanonicalHeapTree8` is ADDITIVE. No new
   `AafiTree8` type is needed; the same tree carries both the sorted-compacted `root8` and the
   append-order lineage (`next_free_index`, `fold_append_order_8`, `heap_root.rs:1106`).
2. The map-log bus (`BUS_MAP_LOG`) and the descriptor grammar already partition by op code; adding
   code 4 is one enum arm + one gated leg. A distinct AIR duplicates the whole table, the log bus,
   and the fill.
3. The mutable-heap legs (op 0/1/3) are literally untouched — the new columns are zero on op≠4
   rows, and the two-path leg is gated by an `is_aafi` selector.

A distinct `AafiTree8` type + AIR (option a) is the wrong trade: it forces a second tree object in
the cell, a second producer, a second fill, and a second log bus, to save nothing (the append-order
fold is already a method on the existing tree).

### 1.3 The exact type/enum/routing changes

- **`circuit/src/descriptor_ir2.rs:478-503`** — extend `enum MapKind` with `AafiInsert`, and
  `code(self)`: `MapKind::AafiInsert => 4`. Extend the grammar parser (`:962-966`) with
  `"aafi_insert" => MapKind::AafiInsert`.
- **`metatheory/Dregg2/Circuit/...` `MapOpKind`** — add the mirror `.aafiInsert` constructor
  (the Lean `MapOp.op` field; wire code 4).
- **`EffectVmEmitRotationV3.lean:2288,2483`** and the revoked op (§1.4) — flip `op := .insert` →
  `op := .aafiInsert` for `nullifierInsertOp`, `commitmentsInsertOp`, revoked insert. This is the
  ATOMIC routing switch (Part 4, F1). The Rust descriptor mirror follows.

### 1.4 The revoked set (a hole, not just a re-route)

`cell/src/revoked_set.rs:16-30` documents that the deployed revocation root is currently
producer-supplied ("a node can supply an empty root and the commitment faithfully records the lie —
a light client cannot detect it", Lean hole #3/#139); the Lean models `revokedRoot` on the same
`Heap8Scheme` as `nullifierRoot`. So there is **no deployed insert gate to flip** — land the revoked
insert gate DIRECTLY as AAFI (a `revokedInsertOp` `.aafiInsert` + `revokedFreshOp` `.absent`,
guarded by the revoke selector), closing the hole and the GAP #5 shape in one step.

---

## PART 2 — THE AIR TWO-PATH CUTOVER

Files: `descriptor_ir2.rs` (MapOps AIR eval `:2727-2857`, fill `:4386-4501`), `effect_vm/
trace_rotated.rs` (rotated fill `:1415/1516`), `metatheory/Dregg2/Circuit/MapOpsColumnLayout.lean`
(width/law mirror). Constants: `HEAP_TREE_DEPTH = 16` (`heap_root.rs:54`), `CHIP_OUT_LANES = 8`,
`MA_DECOMP_COLS = 13`, `MA_CMP_COLS = 13`, `decomp_cols(27) = 10`.

### 2.1 The current MAP_WIDTH layout (`descriptor_ir2.rs:1799-1816`)

The inline comments (…149 / 165 / 421) are STALE by one — they predate the `MAP_NEXT` felt (the
arity-3 pointer) inserted at 21. Computing from the code arithmetic (authoritative):

```
MAP_ROOT       = 0        (8)   old_root8
MAP_KEY        = 8        (1)
MAP_VALUE      = 9        (1)
MAP_OP         = 10       (1)
MAP_NEW_ROOT   = 11       (8)   new_root8
MAP_IS_REAL    = 19       (1)
MAP_OLD_VALUE  = 20       (1)
MAP_NEXT       = 21       (1)   the arity-3 pointer (next_addr)
MAP_SIB0       = 22       (8·16=128)  the ONE shared path siblings
MAP_DIR0       = 150      (16)         its direction bits
MAP_OLD_LEAF   = 166      (8)
MAP_NEW_LEAF   = 174      (8)
MAP_OLD_CHAIN0 = 182      (8·15=120)  old_leaf → old_root intermediate nodes
MAP_NEW_CHAIN0 = 302      (8·15=120)  new_leaf → new_root intermediate nodes
MAP_WIDTH      = 422
```

(Fix the stale `// 421` comment to `// 422` while here.)

### 2.2 The exact new columns (append after `MAP_NEW_CHAIN0`; zero on op≠4 rows)

The AAFI insert needs TWO INDEPENDENT openings (low update, and append at a distinct free slot) plus
the pointer-bracket range gate. The existing `MAP_SIB0/MAP_DIR0` path is repurposed as PATH1 (the
low-leaf path); PATH2 (the free-slot path) is new. New groups:

| New const | Width | Consumes (`AafiInsertWitness8`) | Purpose |
|---|---|---|---|
| `MAP_R1` | 8 | (derived) | intermediate root after the low update |
| `MAP_LOW_ADDR` | 1 | `low_leaf_old.addr` | range gate lo bound |
| `MAP_LOW_VALUE` | 1 | `low_leaf_old.value` | reconstruct low digests |
| `MAP_LOW_NEW` | 8 | `low_leaf_new` digest | low leaf after `next_addr:=k` |
| `MAP_LOW_NEW_CHAIN0` | 8·15=120 | (derived) | low_new → R1 over PATH1 |
| `MAP_SIB2_0` | 8·16=128 | `free_index` path sibs | PATH2 siblings (free slot) |
| `MAP_DIR2_0` | 16 | `free_index` bits | PATH2 direction bits |
| `MAP_FREE_EMPTY` | 8 | `heap_empty_subtree_root_8(0)` (const) | the empty slot digest, pre-append |
| `MAP_FREE_EMPTY_CHAIN0` | 8·15=120 | (derived) | free_empty → R1 over PATH2 |
| **range block** | 3·13 + 2·13 = 65 | `low.addr,k,low.next` decomp + 2 cmp | pointer-bracket gate (portable from MapAbsent `MA_A_DEC0..MA_CMP_HI0`) |

Reuse (no new column): `MAP_OLD_LEAF` = `low_leaf_old` digest; `MAP_NEW_LEAF` = appended-leaf digest;
`MAP_NEXT` = `low_leaf_old.next_addr` (= the appended leaf's `next_addr`); `MAP_NEW_CHAIN0` =
append_leaf → new_root over PATH2; `MAP_SIB0/DIR0` + `MAP_OLD_CHAIN0` = PATH1 (low_old → old_root).

**New columns total: 8+1+1+8+120+128+16+8+120+65 = 475.**
**MAP_WIDTH before = 422 → after ≈ 897.** (≈ doubling — the two paths + the range block. Tighter
reuse of the two `*_CHAIN0` groups can trim ~120; keep them distinct for a clean per-path law.)

### 2.3 The gates ↔ imtInsert step ↔ `AafiInsertWitness8` field

Guard everything below by `is_aafi = (op == 4)` (a degree-1 selector; the existing `not_insert`
selector at `:2755-2758` extends to also zero these on op∈{0,1,3}). The `MAP_OP` boolean-set
constraint (`:2733`) extends to `op·(op-1)·(op-3)·(op-4) = 0`.

- **Gate (a) — low-leaf open at stable position vs old_root.** `MAP_OLD_LEAF` (arity-3 IMT digest
  `hash[MAP_LOW_ADDR, MAP_LOW_VALUE, MAP_NEXT]`) folds up PATH1 (`MAP_SIB0/DIR0`,
  `MAP_OLD_CHAIN0`) to `MAP_ROOT`. → imtInsert "find the unique low leaf"; Lean:
  membership leg of `imtInsert_preserves`. Fields: `low_leaf_old`, `low_siblings`, `low_directions`,
  `old_root`.
- **Gate (b) — pointer-bracket range `low.addr < k < low.next_addr`.** Reuse `eval_canon_decomp` +
  `eval_lex_lt` VERBATIM from the MapAbsent arm (`descriptor_ir2.rs:2880-2917`) on the new range
  block (`MAP_LOW_ADDR`, `MAP_KEY`, `MAP_NEXT`). → imtInsert's `if l.addr < k ∧ k < l.nextAddr`;
  Lean: `ImtAbsent` premise of `imtInsert_preserves` (`imtAbsent_excludes` refutes present-k). This
  is the double-spend tooth: a present/out-of-gap k has no bracket → UNSAT.
- **Gate (c) — PATH1 low update → R1.** `MAP_LOW_NEW` = `hash[MAP_LOW_ADDR, MAP_LOW_VALUE, MAP_KEY]`
  (the SAME low leaf with `next_addr:=k`), folded up the SAME PATH1 siblings
  (`MAP_LOW_NEW_CHAIN0`) to `MAP_R1`. Sub-gates: `low_new.addr==low_old.addr`,
  `low_new.value==low_old.value`, `low_new.next==MAP_KEY`. → imtInsert step (i) "update
  `nextAddr → k`"; Lean: `imtLowUpdate_binds` (`IndexedMerkleTree.lean:429`). Field: `low_leaf_new`.
- **Gate (d) — PATH2 append at free_index.** (d1) `MAP_FREE_EMPTY` is pinned to the constant
  `heap_empty_subtree_root_8(0)` and folds up PATH2 (`MAP_SIB2_0/MAP_DIR2_0`,
  `MAP_FREE_EMPTY_CHAIN0`) to `MAP_R1` — proves the slot at `free_index` was EMPTY under R1 (no
  overwrite). (d2) `MAP_NEW_LEAF` = `hash[MAP_KEY, MAP_VALUE, MAP_NEXT]` (the appended leaf,
  inheriting `low_oldNext = MAP_NEXT`) folds up the SAME PATH2 (`MAP_NEW_CHAIN0`) to `MAP_NEW_ROOT`.
  Sub-gate: `append_leaf.next == MAP_NEXT == low_old.next`. → imtInsert step (ii) "splice
  `(k, v, low_oldNext)` at a free slot, no shift"; Lean: `pathRecompute_binds_updates` on the second
  path. Fields: `free_index`, `new_leaf` (appended), `new_root`.

Soundness: (a)+(c) bind "only `low_position` changed, `old_root → R1`"; (d1)+(d2) bind "only
`free_index` changed empty→append, `R1 → new_root`"; (b) binds k into low's real pointer gap. Since
`low_position ≠ free_index` and the free slot was empty, the composition is exactly
`imtInsert_preserves`'s "only the low leaf and the new slot changed, nothing else" — the compacted-
array shift obstruction is gone because positions are STABLE (append-at-free-index).

### 2.4 The producer fill

- **`descriptor_ir2.rs:4386-4501`** — add a `MapKind::AafiInsert` arm calling
  `tree.insert_witness_aafi(HeapLeaf::entry(key, value))` (`heap_root.rs:945`) and laying its fields
  into the new columns: `w.old_root→MAP_ROOT`, `w.new_root→MAP_NEW_ROOT`,
  `w.low_leaf_old.{addr,value}→MAP_LOW_ADDR/VALUE`, `w.low_leaf_old.next_addr→MAP_NEXT`,
  digests via `digest8()` into `MAP_OLD_LEAF/MAP_LOW_NEW/MAP_NEW_LEAF/MAP_FREE_EMPTY`, the two paths
  from `w.low_siblings/w.low_directions` (PATH1) and the `free_index` membership path (PATH2, derive
  from `append_order_after`), and the four `fold_chain`s (low_old→root, low_new→R1, free_empty→R1,
  append→new_root) with their `chip_hist` node8 registrations. Advance the working tree via the
  AAFI layout (`append_order_after`), NOT `CanonicalHeapTree8::new` re-sort.
- **`effect_vm/trace_rotated.rs:1415/1516`** — `generate_rotated_note_spend_trace_with_nullifier_tree`
  and `generate_rotated_create_cell_trace_with_accounts_tree` (and a new revoked variant) thread
  the AAFI witness for the append-only sets instead of `insert_witness`. The `before_*` leaf slices
  they already carry feed `insert_witness_aafi`.
- **`MapOpsColumnLayout.lean`** — the width/law mirror: add the `aafiInsert` gate law modelling the
  two-path opening + range bracket, and prove it discharges to the proven `imtInsert` (import
  `IndexedMerkleTree.imtInsert_preserves`). Update the `toyInsertOp`/`toy_insert_gates` teeth
  (`:836,889`) with an `aafiInsert` twin, and the width mirror to 897.

---

## PART 3 — THE FULL REGEN SURFACE (what the atomic flip invalidates)

1. **VK regen** — the rotated V3 AFTER roots for NoteSpend (limb 26), NoteCreate (limb 27), Revoke
   (revocation root) change from the sorted-compacted fold to the AAFI append-order fold
   (`fold_append_order_8`). All ride the ONE rotation V3 registry + wrap → **one VK epoch** covers
   all three. Effects: `noteSpendV3`, `noteCreateV3`, the revoke descriptor.
2. **Staged fixtures** (`circuit/descriptors/`): `rotation-v3-staged-registry.tsv`,
   `rotation-wide-registry-staged.tsv`, `rotation-wide-transfer-staged.tsv`,
   `rotation-wide-umem-welded-registry-staged.tsv`, `umem-cohort-v1-staged-registry.tsv`,
   `umem-cohort-multidomain-v1-staged-registry.tsv`, `rotation-layout-v3-staged.json`,
   `rotation-caveat-layout-v3-staged.json`, `PROVENANCE.json`.
3. **GENTIAN executor↔cell differential** — `circuit/tests/heap_root_cell_circuit_differential.rs`
   (currently arity-2 `HeapLeaf { addr, value }` + arity-2 `hash_many[addr,value]` + an
   order-independence assertion). Migrate to arity-3 leaf + AAFI append-order reference; **DELETE the
   order-independence assertion** (`family_separation_and_order_independence`, :190-204) for the
   append-only sets. Also `heap_root_gentian_weld.rs`, `fields_root_gentian_weld.rs`.
4. **`root_is_input_order_independent`** — `heap_root.rs:1242`, `cap_root.rs:1129`: RETIRES for the
   append-only sets (the AAFI fold IS insertion-order-dependent, by design — this is the whole point;
   sync is REPLAY, order is canonical, per LIGHTCLIENT-AAFI-IMPACT §1). Keep/scope it to the
   sorted-compacted layer for the still-sorted mutable heap.
5. **Store append-log / seq persistence** — `cell/src/nullifier_set.rs`, `commitment_set.rs`,
   `revoked_set.rs`: reconstruct-from-store currently rebuilds sorted via `CanonicalHeapTree8::new`.
   Persist `next_free_index` + the append order (a `seq` column) OR replay the tau-finalized
   sequence, so the reconstructed AAFI root matches. `node/src/blocklace_sync.rs:4455`
   (`load_all_nullifiers`).
6. **Cell slot persistence** — **N/A this flip** (the mutable cell heap is NOT flipping;
   `cell/src/state.rs` untouched by the append-only cutover). Owed only when the cell heap flips.
7. **Downstream `HeapLeaf` migration** — ~201 occurrences across 9 crates (circuit, cell, sdk, node,
   perf, sandstorm-bridge, wasm, turn, circuit-prove). The struct already has `next_addr`; the
   mechanical migration replaces remaining arity-2 `HeapLeaf { addr, value }` literals with
   `HeapLeaf::entry(addr, value)` (which seeds `next_addr = SENTINEL_MAX`, relinked on tree build).
   Heaviest: `sdk/src/full_turn_proof.rs`, `effect_vm/trace_rotated.rs`, test files
   (`effect_vm_rotation_flip.rs`, the `vk_epoch_*_light_client_binding.rs` set), `cell/src/*_set.rs`.
8. **Descriptor TSV registries** — the 6 `.tsv` + `PROVENANCE.json` (also in §2 above).
9. **`MapOpsColumnLayout.lean` width mirror** — 422 → 897 + the new gate law (also §2.4).

### Batching the wrap-class VK epoch — YES

The 4 staged wrap-class fixes (vault / cap-open / cross-cell / core-transfer;
`docs/reference/WRAP-CLASS-AUDIT.md`) are already "STAGED like the wrap-class fixes (rides the VK
epoch flip)" per the census. VK regen is the dominant cost and both touch the rotation V3 apex →
**batch all into ONE VK epoch flip.** Do not spend two separate expensive regens.

---

## PART 4 — THE ORDERED GREEN-CUTOVER SEQUENCE

### Stage A — ADDITIVE (land green incrementally; the tree stays green — nothing emits op=4 yet)

- **A1 [DONE, d42188fd3]** `AafiInsertWitness8` + `insert_witness_aafi` + `next_free_index`.
- **A2** Add `MapKind::AafiInsert` (code 4) + grammar `"aafi_insert"` + the Lean `MapOpKind.aafiInsert`
  mirror. Extend the `MAP_OP` boolean-set gate to allow 4. *(single-owned: `descriptor_ir2.rs`)*
- **A3** Add the 475 new columns to the MAP_WIDTH layout (§2.2), fix the stale `//421`→`//422`.
  Zero on op≠4 rows. *(single-owned: `descriptor_ir2.rs`)*
- **A4** Add the `is_aafi`-gated two-path leg to the MapOps AIR eval (§2.3). Green — no descriptor
  emits op=4. *(single-owned: `descriptor_ir2.rs`)*
- **A5** Add the `MapKind::AafiInsert` producer fill (§2.4) + `trace_rotated.rs` AAFI variants. Fires
  only when a descriptor emits aafiInsert (none yet). *(single-owned: circuit)*
- **A6** `MapOpsColumnLayout.lean` mirror: aafiInsert gate law ⟹ `imtInsert_preserves`; width 897;
  toy teeth. *(PARALLEL — Lean lane, disjoint from Rust)*
- **A7** `HeapLeaf::entry` migration of the remaining arity-2 literals (§3.7). *(PARALLEL — per-file /
  per-crate, disjoint)*
- **A8** Store append-order/seq persistence in `nullifier_set` / `commitment_set` / `revoked_set` +
  the replay path. *(PARALLEL — per-set, disjoint files)*

### Stage F — THE ATOMIC FLIP (single-owned, one coordinated commit)

- **F1** Switch `nullifierInsertOp` / `commitmentsInsertOp` `.insert → .aafiInsert`
  (`EffectVmEmitRotationV3.lean:2288,2483`) + land the AAFI-native **revoked** insert/fresh ops
  (§1.4) + the Rust descriptor mirror.
- **F2** Regen the committed root lineage: rotation V3 AFTER roots now = AAFI fold; regen VK + ALL
  staged fixtures (§3.2) in the SAME commit.
- **F3** Batch the 4 wrap-class staged fixes into this VK epoch (§3 batching).

This trio is interlocked (routing switch ↔ committed roots ↔ VK/fixtures) — it MUST be one agent,
one commit. A parallel agent touching the same registry mid-flip clobbers (see
`feedback-swarm-shared-tree-clobber-hazard.md`).

### Stage P — POST-FLIP TAIL

- **P1** Regenerate light-client binding + rotation-flip fixtures (`vk_epoch_*_light_client_binding.rs`,
  `effect_vm_rotation_flip.rs`). *(PARALLEL)*
- **P2** Rebuild the GENTIAN differential (§3.3): arity-3 + AAFI append-order reference; DELETE the
  order-independence assertions (§3.3, §3.4). *(PARALLEL)*
- **P3** Cut reconstruct-from-store to the append-order/replay path (`blocklace_sync.rs:4455`).
  *(PARALLEL)*
- **P4** Run the FULL gauntlet on hbox — whole-tree Lean archive build + circuit-prove IVC gauntlets
  — to catch the red-umbrella downstream: the shared `MAP_WIDTH` growth touches EVERY MapOps consumer
  (per `feedback-swarm-shared-tree-clobber-hazard.md` "per-file green hides a red umbrella"). *(runs
  LAST, after P1-P3)*

### Swarm-safety summary

| Stage | Owner |
|---|---|
| A2-A5 (shared `descriptor_ir2.rs`) | single-owned OR strictly sequenced by the main loop |
| A6 (Lean), A7 (HeapLeaf per-file), A8 (per-set store) | PARALLEL, disjoint |
| F1-F3 (the flip) | SINGLE-OWNED, one commit |
| P1-P3 | PARALLEL |
| P4 (umbrella build) | LAST |
