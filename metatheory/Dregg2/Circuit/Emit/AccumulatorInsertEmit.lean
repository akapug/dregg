/-
# Dregg2.Circuit.Emit.AccumulatorInsertEmit — the INSERT-shaped accumulator keystone, the CORRECT-shaped
genuine close for the FOURTH/FIFTH/SIXTH faithful-root (nullifier · commitments · cells — the three
DEDICATED accumulator roots), over the ACTUAL deployed sorted INSERT.

## Why this file exists (the update-shape obstruction, and the honest fix)

`AccumulatorOpenEmit.lean` built `effAccumWriteV3` / `accumOpen_writesTo8` — the UPDATE-AT-KEY shaped
after-spine (two `HeapMembershipCore` witnesses SHARING a sibling path, before = old leaf, after =
in-place-updated leaf at the SAME key). That shape is the exact twin of heap/fields, whose deployed
writes ARE update-at-key. But the three accumulators are NOT update-at-key: each accumulator write
(`noteSpend` nullifier-insert / `noteCreate` commitments-insert / `createCell` cells-insert) is a
SORTED-TREE FRESH-KEY INSERT (`heap_root.rs::CanonicalHeapTree8::insert_witness`) — the key is ABSENT
in BEFORE, splices at the sorted position, and the tree REBUILDS. There is NO shared before/after
path (a prior agent proved this a genuine obstruction). The update-shaped after-spine therefore does
NOT fit the accumulators.

This file builds the CORRECT insert-shaped keystone. The honest model of the sorted insert:
  (a) NON-MEMBERSHIP of the fresh key in BEFORE — the predecessor/successor bracket (`GapOpen8.inner`:
      `pred < key < succ`, both present + adjacent in the sorted tree) ⟹ `key ∉ keysOf8 beforeRoot`
      (`SortedTreeNonMembershipHeap8.nonMembership_sound8`);
  (b) MEMBERSHIP of the spliced `(key, value)` leaf in AFTER — `MembersAt8 afterRoot (key, value)`
      (the `insert_witness` membership path in the REBUILT tree reaching the AFTER root);
  (c) the ROOT RECOMPUTE tying BEFORE→AFTER — the set grows by EXACTLY the fresh key, in sorted order
      (`SortedTreeNonMembershipHeap8.update_sound8`: `keysOf8 afterRoot = insert key (keysOf8 beforeRoot)`).

## The deliverables
  * `accumInserts8` (§A) — the faithful insert relation (the insert twin of `heapWritesTo8`): fresh in
    BEFORE, present in AFTER, set-grows-by-exactly-key; its faithful consequences.
  * `accumInsert_writesTo8` (§B) — THE KEYSTONE: the non-membership witness + the AFTER membership +
    the two spine bindings FORCE `accumInserts8` over the FULL committed 8-felt BEFORE/AFTER root
    groups — NEVER the lane-0 squeeze. Parametric over the 3 families (like `accumOpen_writesTo8`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR floor enters only through
the `Heap8Scheme` node8 carrier already in play, and the realizable spine↔root binding `SpineCommits8`
is a HYPOTHESIS, never an axiom.
-/
import Dregg2.Circuit.SortedTreeNonMembershipHeap8

namespace Dregg2.Circuit.Emit.AccumulatorInsertEmit

open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (MembersAt8)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8
  (SpineCommits8 keysOf8 GapOpen8 keyOfH nonMembership_sound8 update_sound8)
open Dregg2.Circuit.SortedTreeNonMembership (sortedInsert)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §A — the faithful INSERT relation `accumInserts8` (the insert twin of `heapWritesTo8`).

`heapWritesTo8 S8 oldRoot k v newRoot` says a SHARED path recomposes `oldRoot` from `(k, oldVal)` and
`newRoot` from `(k, v)` — the update-at-key shape. The accumulator insert has NO shared path; the
faithful insert claim is instead: `key` was ABSENT in BEFORE, `(key, value)` is PRESENT in AFTER, and
the committed key set grows by EXACTLY `key`. We package it existentially over the (realizable) sorted
key spine the BEFORE root commits to. -/

/-- **`accumInserts8 S8 beforeRoot key value afterRoot`** — the faithful 8-felt accumulator INSERT: the
BEFORE root commits some sorted spine, `key` is ABSENT from the BEFORE tree, the spliced `(key, value)`
leaf is a MEMBER of the AFTER tree, and the AFTER root commits the INSERTED spine (`sortedInsert key
spine`). Over the FULL committed BEFORE/AFTER 8-felt root groups (~124-bit), NEVER lane-0. -/
def accumInserts8 (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ) (afterRoot : Digest8) :
    Prop :=
  ∃ spine : List ℤ,
    SpineCommits8 S8 beforeRoot spine ∧
    key ∉ keysOf8 S8 beforeRoot ∧
    MembersAt8 S8 afterRoot (key, value) ∧
    SpineCommits8 S8 afterRoot (sortedInsert key spine)

/-- **`accumInserts8_setGrows` — the faithful set-grow consequence.** The AFTER committed key set is
EXACTLY the BEFORE set plus the fresh `key` (`update_sound8`): the insert adds precisely `key`, nothing
else. The insert twin of `heapWritesTo8_forces_postleaf` at the set level. -/
theorem accumInserts8_setGrows (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ)
    (afterRoot : Digest8) (h : accumInserts8 S8 beforeRoot key value afterRoot) :
    ∀ y, y ∈ keysOf8 S8 afterRoot ↔ (y = key ∨ y ∈ keysOf8 S8 beforeRoot) := by
  obtain ⟨spine, hbefore, hfresh, _hmem, hafter⟩ := h
  exact update_sound8 S8 beforeRoot afterRoot key spine hbefore hfresh hafter

/-- **`accumInserts8_value_present`** — the written `(key, value)` leaf is a genuine MEMBER of the AFTER
tree at the FULL 8-felt root: the value is stored at `key` in AFTER, not merely lane-0-projected. -/
theorem accumInserts8_value_present (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ)
    (afterRoot : Digest8) (h : accumInserts8 S8 beforeRoot key value afterRoot) :
    MembersAt8 S8 afterRoot (key, value) := by
  obtain ⟨_spine, _hbefore, _hfresh, hmem, _hafter⟩ := h
  exact hmem

/-- **`accumInserts8_fresh`** — the inserted `key` was genuinely ABSENT from BEFORE (no overwrite): the
insert is a FRESH-key insert, not a silent update. Anti-ghost: distinguishes a genuine insert from an
update-at-key masquerade. -/
theorem accumInserts8_fresh (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ)
    (afterRoot : Digest8) (h : accumInserts8 S8 beforeRoot key value afterRoot) :
    key ∉ keysOf8 S8 beforeRoot := by
  obtain ⟨_spine, _hbefore, hfresh, _hmem, _hafter⟩ := h
  exact hfresh

/-! ## §B — THE KEYSTONE: `accumInsert_writesTo8` (the non-membership + after-membership + recompute
FORCE the faithful insert). Parametric over the 3 accumulator families (via the abstract roots/leaves).

Given: the BEFORE root commits a sorted spine; a `GapOpen8` covering `key` valid against that spine
(the pred/succ bracket, whose neighbor openings ride the proven `Heap8Scheme` recompose soundness); the
spliced `(key, value)` leaf opens against the AFTER root (`MembersAt8`); and the AFTER root commits the
inserted spine — then the faithful insert `accumInserts8` holds. This is the insert twin of
`accumOpen_writesTo8` — the STEP-A keystone the assurance case's per-family §J trio consumes. -/
theorem accumInsert_writesTo8 (S8 : Heap8Scheme)
    (beforeRoot afterRoot : Digest8) (key value : ℤ) (spine : List ℤ)
    (hbefore : SpineCommits8 S8 beforeRoot spine)
    (g : GapOpen8 S8 beforeRoot key) (hcov : g.coversSpine spine)
    (hafterMem : MembersAt8 S8 afterRoot (key, value))
    (hafter : SpineCommits8 S8 afterRoot (sortedInsert key spine)) :
    accumInserts8 S8 beforeRoot key value afterRoot := by
  -- (a) the fresh-key non-membership in BEFORE, from the covering gap over the committed spine.
  have hfresh : key ∉ keysOf8 S8 beforeRoot :=
    nonMembership_sound8 S8 beforeRoot key spine hbefore g hcov
  -- (b)+(c) assemble the faithful insert relation.
  exact ⟨spine, hbefore, hfresh, hafterMem, hafter⟩

/-- **`accumInsert_writesTo8_setGrows` — the KEYSTONE's headline consequence, in one shot.** From the
non-membership bracket + the AFTER membership + the two spine bindings, the AFTER committed key set is
EXACTLY the BEFORE set plus the fresh `key`. The genuine faithful 8-felt insert the apex proves per
accumulator family, over the ACTUAL sorted insert (NOT the update-at-key shared-spine). -/
theorem accumInsert_writesTo8_setGrows (S8 : Heap8Scheme)
    (beforeRoot afterRoot : Digest8) (key value : ℤ) (spine : List ℤ)
    (hbefore : SpineCommits8 S8 beforeRoot spine)
    (g : GapOpen8 S8 beforeRoot key) (hcov : g.coversSpine spine)
    (hafterMem : MembersAt8 S8 afterRoot (key, value))
    (hafter : SpineCommits8 S8 afterRoot (sortedInsert key spine)) :
    ∀ y, y ∈ keysOf8 S8 afterRoot ↔ (y = key ∨ y ∈ keysOf8 S8 beforeRoot) :=
  accumInserts8_setGrows S8 beforeRoot key value afterRoot
    (accumInsert_writesTo8 S8 beforeRoot afterRoot key value spine
      hbefore g hcov hafterMem hafter)

#assert_axioms accumInserts8_setGrows
#assert_axioms accumInserts8_value_present
#assert_axioms accumInserts8_fresh
#assert_axioms accumInsert_writesTo8
#assert_axioms accumInsert_writesTo8_setGrows

end Dregg2.Circuit.Emit.AccumulatorInsertEmit
