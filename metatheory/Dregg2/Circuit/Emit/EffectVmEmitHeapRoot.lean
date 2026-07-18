/-
# Dregg2.Circuit.Emit.EffectVmEmitHeapRoot — the GENUINE sorted-Merkle heap-write descriptor
(REFINEMENT-DESIGN Decision 1; THE ROTATION's heap-write descriptor gadget).

THE HEAP generalizes the proven `cap_root` openable sorted-Poseidon2 machinery with a GENERIC leaf
(`Substrate.Heap`: `addr = hash[coll,key]`, `leaf = hash[addr,value]`, root = the depth-16 binary-Merkle
fold of the sorted leaf list, `MapMerkleRoot.mapRoot` — the deployed `heap_root.rs::CanonicalHeapTree`).
This module supplies the heap write's in-ROW address + leaf recompute and the SPLICE base descriptor.
The new `heap_root` is FORCED — not by a prepend accumulator — but by a genuine `.write` `MapOp` whose
`Ir2Air::MapOps` AIR opens the addressed OLD leaf against the committed root and recomputes the sorted-tree
update (see `RotatedKernelRefinementExercise.heapWriteV3` + `DescriptorIR2.writesTo`).

Two in-row recompute sites (the cap-root gate family reused, `EffectVmEmitCapRoot`; the SAME `VmHashSite`
shape, the cap-edge leaf `hash[holder,target,rights,op]` replaced by the heap two-site shape):

  1. **`siteHeapAddr`** — recompute the heap ADDRESS in-row: `addr = hash[ coll, key ]`. The prover
     cannot choose the address freely; it is `hash` of the bound `(collection_id, key)` (the design's
     "sorted-by-key-hash", `Substrate.Heap.addrOf`). This binds the splice `MapOp`'s KEY column.
  2. **`siteHeapLeaf`** — recompute the heap LEAF in-row: `leaf = hash[ addr, value ]` (the
     generic-leaf generalization of the cap-edge leaf, `Substrate.Heap.leafOf`). Tampering the
     address OR the value moves the leaf.

## Where the new root is FORCED (the SPLICE, NOT a prepend digest)

The new `heap_root` is NOT advanced by a prepend accumulator `hash[leaf, old_root]` — that digest is a
function of `(leaf, old_root)` a prover can pick without performing the real sorted-tree insert. Instead
`heapWriteSpliceVmDescriptor` (§2.E) carries ONLY the address+leaf sites and delegates the new-root
forcing to a `.write` `MapOp` (`RotatedKernelRefinementExercise.heapSpliceWriteOp`), appended when the
descriptor is rotated + graduated into `heapWriteV3`. The deployed `Ir2Air::MapOps` AIR
(`DescriptorIR2.MapOp.holdsAt .write`, denotation `DescriptorIR2.writesTo`) forces
`new_heap_root = mapRoot (Heap.set h addr value)` for the sorted heap `h` committed by the old root — the
genuine binary-Merkle sorted insert-or-update over the WHOLE leaf list, functional under CR
(`writesTo_functional`). The `SAT ⟹ mapRoot (Heap.set …)` theorem is
`RotatedKernelRefinementExercise.heapWrite_realizes_heapSet`; the forged-root rejection is
`heapWrite_sat_rejects_forged_root` / `heapWrite_sat_rejects_wrong_splice_root`. No free digest survives.

The new-root carrier is the `heap_root` register column (a non-`balance` state field absorbed into
`state_commit` by the same GROUP-4 mechanism `cap_root` uses); the splice reads/writes it via the
ROTATED limbs (`HEAP_ROOT_BEFORE_ROT` / `HEAP_ROOT_AFTER_ROT` in `RotatedKernelRefinementExercise`).

## cell≡circuit differential

The recomputed address/leaf read the SAME `Substrate.Heap` functions the cell stores and the executor
recomputes, so cell≡circuit is BY DEFINITION at this value layer (the cap Phase-A discipline). The Rust
differential is `circuit/tests/heap_root_cell_circuit_differential.rs` /
`circuit/tests/heap_write_deployed_root_forced.rs` (the deployed-level splice-present + root-forced tripwire).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis where used downstream. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCapRoot

namespace Dregg2.Circuit.Emit.EffectVmEmitHeapRoot

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (cN)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the param columns carrying the heap-write content `(collection_id, key, value)`.

Reuse the cap-edge param block (`EffectVmEmitCapRoot.cp`): the heap write's `(coll, key, value)`
ride the same param columns the cap edge `(holder, target, rights)` use — distinct effects, distinct
selectors, the SAME free param columns. -/
namespace hp
/-- The `collection_id` param column (cap-family `HOLDER` slot, reused). -/
def COLL  : Nat := EffectVmEmitCapRoot.cp.HOLDER
/-- The `key` param column (cap-family `TARGET` slot, reused). -/
def KEY   : Nat := EffectVmEmitCapRoot.cp.TARGET
/-- The written `value` param column (cap-family `RIGHTS` slot, reused). -/
def VALUE : Nat := EffectVmEmitCapRoot.cp.RIGHTS
end hp

/-! ## §1 — the in-row carriers for the recomputed address + leaf, and the old/new heap roots. -/

/-- The recomputed heap-ADDRESS carrier (`hash[coll,key]`). An aux column — the cap-edge-leaf
carrier slot, reused (this descriptor's selector ≠ a cap selector, so the slot never collides).
This is the column the splice `.write` `MapOp` reads as its KEY. -/
def HEAP_ADDR : Nat := EffectVmEmitCapRoot.CAP_EDGE_LEAF

/-- The recomputed heap-LEAF carrier (`hash[addr,value]`). The next aux slot past the address. -/
def HEAP_LEAF : Nat := EffectVmEmitCapRoot.CAP_EDGE_LEAF + 1

/-- The OLD `heap_root` carrier: the `state_before` `heap_root` register (the absorbed cap-root
before column `CAP_ROOT_BEFORE`). The deployed layout carries the `heap_root` register at this
absorbed column for a heap-write row. The splice `MapOp` reads the committed root off the ROTATED
limb (`HEAP_ROOT_BEFORE_ROT`); this constant pins the v1-state carrier. -/
def HEAP_ROOT_BEFORE : Nat := EffectVmEmitCapRoot.CAP_ROOT_BEFORE

/-- The NEW `heap_root` carrier: the `state_after` register column GROUP-4 absorbs into
`state_commit` (the same absorbed carrier `cap_root` advances into). The splice `MapOp` forces the
new root off the ROTATED limb (`HEAP_ROOT_AFTER_ROT`); this constant pins the v1-state carrier. -/
def HEAP_ROOT_AFTER : Nat := EffectVmEmitCapRoot.CAP_ROOT_AFTER

/-! ## §2 — the TWO in-row recompute hash-sites (address + leaf; the new root is splice-forced). -/

/-- **`siteHeapAddr`** — `addr = hash[ coll, key ]` (the sorted address; `Substrate.Heap.addrOf`). -/
def siteHeapAddr : VmHashSite :=
  { digestCol := HEAP_ADDR
  , inputs := [ .col (prmCol hp.COLL), .col (prmCol hp.KEY) ]
  , arity := 2 }

/-- **`siteHeapLeaf`** — `leaf = hash[ addr, value ]` (the generic leaf; `Substrate.Heap.leafOf`). -/
def siteHeapLeaf : VmHashSite :=
  { digestCol := HEAP_LEAF
  , inputs := [ .col HEAP_ADDR, .col (prmCol hp.VALUE) ]
  , arity := 2 }

/-! ## §2.E — THE heapWrite VM descriptor (PHASE-E: the genuine sorted-Merkle splice, MapOp-forced).

The new `heap_root` is FORCED by the genuine sorted-Merkle SPLICE root `mapRoot (Heap.set h addr v)`
(the binary-Merkle update over the WHOLE sorted leaf list), NOT a prepend accumulator advance. The
`.write` `MapOp` on the heap root (`RotatedKernelRefinementExercise.heapSpliceWriteOp`) is realized by
the deployed `Ir2Air::MapOps` AIR: it opens the addressed OLD leaf against the committed `heap_root`
(the rotated limb) and FORCES the new `heap_root` to the genuine sorted-tree update
(`DescriptorIR2.writesTo`, denotation of `MapOp.holdsAt .write`).

The base descriptor therefore carries ONLY the address+leaf sites: `siteHeapAddr` binds the MapOp's
KEY column (`HEAP_ADDR = hash[coll, key]`) to the genuine sorted address; `siteHeapLeaf` binds the leaf
carrier (informational — the MapOps AIR recomputes the leaf internally along the opened path). The new
root is FORCED by the splice alone — the content-binding a prepend digest could not give. -/

/-- The heapWrite recompute sites: address + leaf only (the new-root advance is the splice `MapOp`).
`siteHeapAddr` binds the MapOp KEY (`HEAP_ADDR = hash[coll, key]`); `siteHeapLeaf` binds the leaf
carrier. -/
def heapSpliceSites : List VmHashSite := [ siteHeapAddr, siteHeapLeaf ]

/-- **`heapWriteSpliceVmDescriptor`** — THE base heapWrite circuit: its `hashSites` are the address+leaf
sites only (NO prepend advance). Rotated + graduated + appended with the splice `.write` `MapOp` it is
`RotatedKernelRefinementExercise.heapWriteV3` — the new root FORCED to the genuine sorted-Merkle splice
(`DescriptorIR2.writesTo` = `mapRoot (Heap.set h addr v)`), not a prepend accumulator. The trace width is
`EFFECT_VM_WIDTH` (the deployed effect-VM width; every recompute column the sites read lands `< width`). -/
def heapWriteSpliceVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-heapWrite-splice-v1"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 0
  , constraints := []
  , hashSites   := heapSpliceSites
  , ranges      := [] }

/-- The heapWrite base descriptor's `hashSites` ARE exactly the address+leaf sites. -/
theorem heapWriteSpliceVmDescriptor_hashSites :
    heapWriteSpliceVmDescriptor.hashSites = heapSpliceSites := rfl

/-! ## §3 — the recomputed values as pure functions (what the address/leaf sites FORCE). -/

/-- The address as a function of `(coll, key)` (the unique `hash` image the address site forces). -/
def addrOf (hash : List ℤ → ℤ) (coll key : ℤ) : ℤ := hash [ coll, key ]

/-- The leaf as a function of `(addr, value)` (the unique `hash` image the leaf site forces). -/
def leafOf (hash : List ℤ → ℤ) (addr value : ℤ) : ℤ := hash [ addr, value ]

/-! ## §4 — the address + leaf carriers are FORCED by a satisfying splice row. -/

/-- **`heapSplice_addr_forced`** — the address carrier IS `hash[coll,key]` from the splice sites (the
MapOp KEY binding): a satisfying splice row binds `HEAP_ADDR` to the genuine sorted address, so the
`.write` MapOp's key is the real `hash[coll,key]`, not a free column. -/
theorem heapSplice_addr_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSites) :
    env.loc HEAP_ADDR = addrOf hash (env.loc (prmCol hp.COLL)) (env.loc (prmCol hp.KEY)) := by
  unfold heapSpliceSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-- **`heapSplice_leaf_forced`** — the leaf carrier IS `hash[addr,value]` from the splice sites, where
`addr` is the recomputed address carrier `HEAP_ADDR`. Tampering the address OR the value moves the leaf. -/
theorem heapSplice_leaf_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env heapSpliceSites) :
    env.loc HEAP_LEAF = leafOf hash (env.loc HEAP_ADDR) (env.loc (prmCol hp.VALUE)) := by
  unfold heapSpliceSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨_, h1, _⟩ := h
  rw [h1]; rfl

/-! ## §5 — THE ANTI-GHOST lives with the splice.

The genuine new-root anti-ghost is `DescriptorIR2.writesTo_functional` (under `Poseidon2SpongeCR`, via
`MapMerkleRoot.mapRoot_injective`): a satisfying `heapWriteV3` row's new `heap_root` is the UNIQUE
sorted-Merkle splice of the committed heap content — a prover cannot keep the published root while
tampering the address or value. The address/leaf carriers are additionally in-row bound
(`heapSplice_addr_forced` / `heapSplice_leaf_forced`), so the splice is keyed by the real
`hash[coll,key]`. The end-to-end `SAT ⟹ mapRoot (Heap.set …)` realization + the forged-root rejection
are `RotatedKernelRefinementExercise.heapWrite_realizes_heapSet` /
`heapWrite_sat_rejects_forged_root`. -/

/-! ## §6 — NON-VACUITY: a concrete splice row fires; a tampered write moves the leaf. -/

/-- A concrete heap-write splice row: coll=3 (col 70), key=4 (col 71), value=42 (col 72). The
address/leaf carriers (cols 102/103) hold the genuine recomputed values under the toy sponge `cN`, so
the splice recompute holds. -/
def goodSpliceRow : VmRowEnv where
  loc := fun v =>
    if v = 70 then 3
    else if v = 71 then 4
    else if v = 72 then 42
    else if v = 102 then cN [3, 4]
    else if v = 103 then cN [cN [3, 4], 42]
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic carrier columns (anti-drift).
#guard prmCol hp.COLL == 70
#guard prmCol hp.KEY == 71
#guard prmCol hp.VALUE == 72
#guard HEAP_ADDR == 102
#guard HEAP_LEAF == 103

/-- **NON-VACUITY (witness TRUE).** `goodSpliceRow` satisfies the address+leaf recompute under the
concrete sponge — the two sites carry their genuine digests. The recompute predicate is INHABITED. -/
theorem goodSpliceRow_recomputes : siteHoldsAll cN goodSpliceRow heapSpliceSites := by
  have hC : prmCol hp.COLL = 70 := by decide
  have hK : prmCol hp.KEY = 71 := by decide
  have hV : prmCol hp.VALUE = 72 := by decide
  have hA : HEAP_ADDR = 102 := by decide
  have hL : HEAP_LEAF = 103 := by decide
  unfold heapSpliceSites siteHoldsAll
  simp only [siteHoldsAll.go, siteHeapAddr, siteHeapLeaf,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil,
    hC, hK, hV, hA, hL]
  refine ⟨?_, ?_, trivial⟩
  · show goodSpliceRow.loc 102 = cN [goodSpliceRow.loc 70, goodSpliceRow.loc 71]; decide
  · show goodSpliceRow.loc 103 = cN [goodSpliceRow.loc 102, goodSpliceRow.loc 72]; decide

/-- **NON-VACUITY (anti-ghost on value).** Writing a DIFFERENT value (42 → 99) at the same `(coll, key)`
yields a DIFFERENT leaf — the value is bound (and the leaf feeds the sorted-Merkle splice). -/
theorem tampered_value_moves_leaf :
    leafOf cN (addrOf cN 3 4) 42 ≠ leafOf cN (addrOf cN 3 4) 99 := by
  unfold leafOf addrOf cN
  norm_num

/-- **NON-VACUITY (anti-ghost on address).** Writing the same value at a DIFFERENT `(coll, key)`
(3,4 → 5,6) yields a DIFFERENT leaf — the address is bound. -/
theorem tampered_addr_moves_leaf :
    leafOf cN (addrOf cN 3 4) 42 ≠ leafOf cN (addrOf cN 5 6) 42 := by
  unfold leafOf addrOf cN
  norm_num

/-! ## §7 — Axiom-hygiene + layout pins. -/

-- The new/old-root carriers ARE the absorbed `heap_root` (= cap-root) state columns.
#guard HEAP_ROOT_AFTER == EffectVmEmitCapRoot.CAP_ROOT_AFTER
#guard HEAP_ROOT_BEFORE == EffectVmEmitCapRoot.CAP_ROOT_BEFORE
-- The address / leaf / before / after carriers are DISTINCT.
#guard [HEAP_ADDR, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER].dedup.length == 4
-- The write param columns are distinct + in-range.
#guard [hp.COLL, hp.KEY, hp.VALUE].dedup.length == 3
#guard [hp.COLL, hp.KEY, hp.VALUE].all (· < NUM_PARAMS)
-- The recompute is two ordered sites (address, leaf); the new root is the splice `MapOp`.
#guard heapSpliceSites.length == 2

#assert_axioms heapSplice_addr_forced
#assert_axioms heapSplice_leaf_forced
#assert_axioms goodSpliceRow_recomputes
#assert_axioms tampered_value_moves_leaf
#assert_axioms tampered_addr_moves_leaf

end Dregg2.Circuit.Emit.EffectVmEmitHeapRoot
