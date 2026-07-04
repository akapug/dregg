/-
# Dregg2.Crypto.PerCellUmem — STAGE A of `docs/deos/UMEM-PRIMITIVE.md`: per-cell umem soundness.

THE OBLIGATION (Codex-flagged): *verify the `UKey::cell()` filter preserves soundness.*

A per-cell umem is the GLOBAL umem (`Crypto/UniversalMemory.lean`, the ONE Blum trace over the
`Domain × κ` address space) restricted to the keys that belong to ONE cell — exactly the Rust
`UKey::cell()` filter (`turn/src/umem.rs:215`). Stage A projects a cell's `heap_map` as a
`Heap{cell, collection, key}` collection whose boundary root is the cell's committed `heap_root`
(`cell/src/state.rs:210,409` `compute_heap_root`). The question THIS module answers: does
filtering the ONE trace down to a single cell's heap leave a SOUND standalone memory whose
boundary root still EQUALS the committed `heap_root`?

THE VERDICT (proved below): YES — the `UKey::cell()` filter is just an ADDRESS-CLASS filter, so
the existing tag-isolation keystones discharge it with no new soundness machinery:

  * `percell_consistentFrom_filter` — restricting a consistent global trace to cell `c`'s heap
    address class is consistent (instance of `consistentFrom_filter`: dropped ops only write
    OUTSIDE the class, so the class's cells evolve identically). THE FILTER PRESERVES SOUNDNESS.

  * `percell_consistent_strip` — that filtered slice, stripped of its `(Domain.heap, ·)` tag and
    re-keyed by its in-cell heap key, is a consistent STANDALONE κ-addressed memory from the
    cell's heap slice of the initial state (riding `consistentFrom_strip` after the cell filter).
    A per-cell umem is sound IN ISOLATION — other cells' (and other domains') ops cannot touch it.

  * `percell_boundary_root_derived` — the boundary root over the cell's PRESENT heap cells equals
    the cell's committed `heap_root` whenever the committed heap map and the per-cell final memory
    agree as lookups (`boundary_root_derived`: pure canonicity, NO crypto). The per-cell boundary
    IS the committed `heap_root`.

  * `percell_umem_sound` — the welded Stage-A statement: from the ONE balance, cell `c`'s heap
    projection is (a) a consistent standalone memory and (b) carries the committed `heap_root` as
    its derived boundary. Per-cell umem soundness, end to end.

The cell filter `inCellHeap c` is `consistentFrom_filter`'s predicate `p` taken at the address
class «heap-domain AND `cellOf · = some c`». It composes with `consistentFrom_strip` because that
class is, by construction, a SINGLE domain (heap) — the same two lemmas the global keystone uses,
now nested. No new theorem: the keystone applied at the per-cell seam.

Non-vacuity (both polarities): a two-cell heap trace whose per-cell filter recovers exactly cell
`c`'s ops (a write to cell `d` is DROPPED), and the boundary-root derivation firing on a concrete
one-cell heap. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every result; crypto
enters ONLY as the named `Poseidon2SpongeCR` floor at the injective anti-forgery tooth, never as
an axiom. Lean/design only — no circuit Rust here.
-/
import Dregg2.Crypto.UniversalMemory

namespace Dregg2.Crypto.PerCellUmem

open Dregg2.Crypto.MemoryChecking
open Dregg2.Crypto.UniversalMemory
open Dregg2.Substrate
open Dregg2.Substrate.Heap (FeltHeap)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

universe u v

/-! ## §1 — the per-cell address class: the `UKey::cell()` filter.

A heap-plane key belongs to a cell (`UKey::cell()` returns `Some c`); the index/factory/nullifier
keys belong to none (`UKey::cell()` returns `None`). The per-cell umem of cell `c` is the global
umem restricted to the address class «heap domain AND this key's owning cell is `c`». `cellOf` is
the abstract content of the Rust `UKey::cell()` method; `inCellHeap c` is the `consistentFrom_filter`
predicate `p`. -/

variable {κ : Type u} {ν : Type v}

/-- The owning cell of a key (`None` = a cell-independent plane: index / factory / nullifier) —
the abstract content of the Rust `UKey::cell()` (`turn/src/umem.rs:215`). -/
abbrev CellOf (κ : Type u) := κ → Option Nat

/-- The per-cell HEAP address class: a unified address `(d, a)` is in cell `c`'s heap iff its
domain is `heap` AND its key's owning cell is `c`. This is exactly the `UKey::cell()` filter
restricted to the heap plane (Stage A's `Heap{cell, collection, key}` collection). -/
def inCellHeap [DecidableEq κ] (cellOf : CellOf κ) (c : Nat) (a : UAddr κ) : Bool :=
  decide (a.1 = Domain.heap) && decide (cellOf a.2 = some c)

/-- The per-cell heap projection of a unified trace: the ops touching cell `c`'s heap cells, in
trace order. The Rust `project_cell` (`turn/src/umem.rs:276`) filtered to one cell. -/
def cellTrace [DecidableEq κ] (cellOf : CellOf κ) (c : Nat)
    (tr : List (Op (UAddr κ) ν)) : List (Op (UAddr κ) ν) :=
  tr.filter fun op => inCellHeap cellOf c op.addr

/-! ## §2 — THE FILTER PRESERVES SOUNDNESS (the Codex obligation).

`consistentFrom_filter` says consistency restricts to ANY address class. The `UKey::cell()` filter
IS such a class (`inCellHeap c`). So the per-cell projection of a consistent global trace is
consistent — dropped ops (other cells, other domains) only write OUTSIDE cell `c`'s heap, so cell
`c`'s cells evolve identically. NO new soundness argument: the keystone, at the per-cell seam. -/

section Filter

variable [DecidableEq κ]

/-- **`percell_consistentFrom_filter` — THE `UKey::cell()` FILTER PRESERVES SOUNDNESS.** If the
global trace is consistent from `m`, cell `c`'s heap sub-trace is consistent from any memory
agreeing with `m` on cell `c`'s heap cells. (A direct instance of `consistentFrom_filter` at the
per-cell address class — the proof IS the keystone.) -/
theorem percell_consistentFrom_filter (cellOf : CellOf κ) (c : Nat)
    {tr : List (Op (UAddr κ) ν)} {m m' : UAddr κ → ν}
    (hagree : ∀ a, inCellHeap cellOf c a = true → m' a = m a) :
    ConsistentFrom m tr →
      ConsistentFrom m' (cellTrace cellOf c tr) :=
  consistentFrom_filter (inCellHeap cellOf c) hagree

/-- Every address in the per-cell projection lives in the heap domain — the precondition
`consistentFrom_strip` needs to peel the tag (the per-cell class is a SINGLE domain). -/
theorem cellTrace_heap_domain (cellOf : CellOf κ) (c : Nat)
    {tr : List (Op (UAddr κ) ν)} :
    ∀ op ∈ cellTrace cellOf c tr, op.addr.1 = Domain.heap := by
  intro op hop
  have hp : inCellHeap cellOf c op.addr = true := (List.mem_filter.mp hop).2
  unfold inCellHeap at hp
  exact of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hp).1

/-- **`percell_consistent_strip` — a per-cell umem is sound IN ISOLATION.** Cell `c`'s heap
projection, stripped of its constant `heap`-domain tag, is a consistent STANDALONE κ-addressed
memory from the cell's heap slice of the initial state. Riding `consistentFrom_strip` after the
cell filter: the per-cell umem is exactly a standalone memory, no aliasing from any other cell or
domain (the tag-isolation guarantee, nested one level in for the cell key). -/
theorem percell_consistent_strip (cellOf : CellOf κ) (c : Nat)
    {tr : List (Op (UAddr κ) ν)} {m : UAddr κ → ν} {m' : κ → ν}
    (hagreeStrip : ∀ a, m' a = m (Domain.heap, a))
    (hcons : ConsistentFrom m tr) :
    ConsistentFrom m' ((cellTrace cellOf c tr).map stripOp) := by
  -- the cell filter preserves consistency (agreeing with itself on the class)…
  have hfil : ConsistentFrom m (cellTrace cellOf c tr) :=
    percell_consistentFrom_filter cellOf c (fun _ _ => rfl) hcons
  -- …and the heap tag peels off the single-domain slice.
  exact consistentFrom_strip Domain.heap
    (cellTrace_heap_domain cellOf c) hagreeStrip hfil

end Filter

/-! ## §3 — the per-cell BOUNDARY ROOT = the committed `heap_root`.

After the filter+strip, cell `c`'s heap is a standalone κ-addressed memory. Re-keyed by its
in-cell heap key (the `(collection_id, key)` hash the `heap_root` tree sorts by, `Substrate/Heap`'s
`ℤ` address), its final present cells are exactly the leaf list `compute_heap_root` sponges. So the
boundary root over them EQUALS the committed `heap_root` — `boundary_root_derived`, pure canonicity,
NO crypto. The per-cell boundary IS the committed `heap_root`. -/

/-- **`percell_boundary_root_derived` — THE PER-CELL BOUNDARY = THE COMMITTED `heap_root`.** Cell
`c`'s committed heap map `h` (the `heap_map` whose sorted-Poseidon2 digest is `heap_root`) and the
per-cell final memory view agree as lookups ⟹ the committed `heap_root` EQUALS the boundary root
derived from the per-cell final cells. Pure `boundary_root_derived` (canonicity, `Heap.root_deterministic`
riding `ext_get`): the per-cell boundary is a refactor of WHERE `heap_root` is read, not WHAT it
commits to. NO crypto hypothesis. -/
theorem percell_boundary_root_derived (hash : List ℤ → ℤ) {h : FeltHeap}
    {fin' : ℤ → Option ℤ} {as : List ℤ}
    (hs : Heap.SortedKeys h) (has : as.Pairwise (· < ·))
    (hsem : ∀ a, Heap.get h a = if a ∈ as then fin' a else none) :
    Heap.root hash h = Heap.root hash (boundaryCells fin' as) :=
  boundary_root_derived hash hs has hsem

/-! ## §4 — THE WELDED STAGE-A STATEMENT.

`percell_umem_sound`: from the ONE Blum balance over the global trace, a single cell's heap
projection is BOTH a consistent standalone memory (the filter preserves soundness) AND carries the
committed `heap_root` as its derived boundary root. The two halves of Stage A — soundness under the
`UKey::cell()` filter, and boundary = `heap_root` — in one theorem. -/

/-- **`percell_umem_sound` — PER-CELL UMEM SOUNDNESS (Stage A).** Given the global trace consistent
from `init` (the ONE Blum balance, via `universal_memory_sound`/`memcheck_sound`), cell `c`'s heap
projection is:
  (1) a consistent STANDALONE κ-addressed memory from the cell's heap slice of `init` — the
      `UKey::cell()` filter preserves soundness; and
  (2) its committed `heap_root` (= `Heap.root` of the heap map `h`) equals the boundary root derived
      from its present cells — the per-cell boundary is the committed root.
NO new soundness machinery: (1) is `consistentFrom_filter`/`consistentFrom_strip` (tag isolation at
the per-cell seam), (2) is `boundary_root_derived` (canonicity). -/
theorem percell_umem_sound [DecidableEq κ]
    (cellOf : CellOf κ) (c : Nat) (hash : List ℤ → ℤ)
    {tr : List (Op (UAddr κ) (Option ℤ))} {init : UAddr κ → Option ℤ}
    {initCell : κ → Option ℤ}
    (hcons : Consistent init tr)
    (hinitCell : ∀ a, initCell a = init (Domain.heap, a))
    {h : FeltHeap} {fin' : ℤ → Option ℤ} {as : List ℤ}
    (hs : Heap.SortedKeys h) (has : as.Pairwise (· < ·))
    (hsem : ∀ a, Heap.get h a = if a ∈ as then fin' a else none) :
    Consistent initCell ((cellTrace cellOf c tr).map stripOp) ∧
      Heap.root hash h = Heap.root hash (boundaryCells fin' as) :=
  ⟨percell_consistent_strip cellOf c hinitCell hcons,
   percell_boundary_root_derived hash hs has hsem⟩

/-! ## §5 — NON-VACUITY: both polarities, concrete traces, `#guard`-witnessed. -/

section NonVacuity

/-- `cellOf` for the witness: heap keys `0,1` belong to cell `100`, heap key `2` to cell `200`. -/
private def cellOfW : CellOf Nat := fun k =>
  if k = 0 ∨ k = 1 then some 100 else if k = 2 then some 200 else none

private def A0 : UAddr Nat := (Domain.heap, 0)   -- cell 100
private def A1 : UAddr Nat := (Domain.heap, 1)   -- cell 100
private def A2 : UAddr Nat := (Domain.heap, 2)   -- cell 200 — must be DROPPED by the cell-100 filter
private def R0 : UAddr Nat := (Domain.registers, 0) -- wrong domain — must be DROPPED too

private def winit : UAddr Nat → Option ℤ := fun _ => none

/-- A four-op global trace: write cell-100 key 0, write cell-200 key 2 (other cell), write
register 0 (other domain), read-back cell-100 key 0. -/
private def trW : List (Op (UAddr Nat) (Option ℤ)) :=
  [⟨.write, A0, some 11, none, 0⟩,
   ⟨.write, A2, some 22, none, 0⟩,         -- other cell — dropped
   ⟨.write, R0, some 33, none, 0⟩,         -- other domain — dropped
   ⟨.read, A0, some 11, some 11, 1⟩]

-- The global trace is consistent.
#guard decide (Consistent winit trW)

-- The cell-100 filter keeps EXACTLY cell 100's heap ops (op 0 and op 3) — the other-cell write
-- and the other-domain write are DROPPED. (The filter is a real function of the cell, not a
-- constant — the teeth.)
#guard (cellTrace cellOfW 100 trW).length == 2
#guard decide (∀ op ∈ cellTrace cellOfW 100 trW, op.addr = A0)

-- The filtered per-cell trace, stripped, is a consistent standalone memory from cell 100's slice.
#guard decide (Consistent (fun a => winit (Domain.heap, a))
  ((cellTrace cellOfW 100 trW).map stripOp))

-- THE FILTER PRESERVES SOUNDNESS fires end-to-end on the honest instance (every hypothesis by
-- `rfl`/`decide` — nothing vacuous in the pipeline).
example : Consistent (fun a => winit (Domain.heap, a))
    ((cellTrace cellOfW 100 trW).map stripOp) :=
  percell_consistent_strip cellOfW 100 (fun _ => rfl) (by decide)

-- A DIFFERENT cell's filter recovers a DIFFERENT slice (cell 200 keeps only op 1) — the cell
-- argument is load-bearing, the per-cell umem is genuinely per-cell.
#guard (cellTrace cellOfW 200 trW).length == 1
#guard decide (∀ op ∈ cellTrace cellOfW 200 trW, op.addr = A2)

/-- The boundary-root derivation fires on a concrete one-cell heap: cell `c`'s committed map
`[(0, 11)]` has the same root as the boundary view derived from its final column. -/
private def finCellW : ℤ → Option ℤ := fun a => if a = 0 then some 11 else none

example :
    Heap.root Heap.refSponge [((0 : ℤ), (11 : ℤ))]
      = Heap.root Heap.refSponge (boundaryCells finCellW [0]) := by
  refine percell_boundary_root_derived Heap.refSponge ?_ ?_ ?_
  · simp [Heap.SortedKeys, Heap.keys]
  · simp
  · intro a
    by_cases ha : a = (0 : ℤ)
    · subst ha; decide
    · rw [if_neg (fun hmem => ha (List.mem_singleton.mp hmem)),
        Heap.get_cons_ne _ _ ha, Heap.get_nil]

-- The boundary view of the per-cell heap is exactly the one-cell map (executably).
#guard boundaryCells finCellW [0] == [(0, 11)]
#guard Heap.root Heap.refSponge (boundaryCells finCellW [0]) == Heap.root Heap.refSponge [((0 : ℤ), (11 : ℤ))]

/-- THE WELDED STAGE-A theorem fires: cell 100's heap projection is a consistent standalone
memory AND carries the committed `heap_root` as its boundary. -/
example :
    Consistent (fun a => winit (Domain.heap, a)) ((cellTrace cellOfW 100 trW).map stripOp) ∧
      Heap.root Heap.refSponge [((0 : ℤ), (11 : ℤ))]
        = Heap.root Heap.refSponge (boundaryCells finCellW [0]) :=
  percell_umem_sound cellOfW 100 Heap.refSponge (by decide) (fun _ => rfl)
    (h := [((0 : ℤ), (11 : ℤ))]) (fin' := finCellW) (as := [0])
    (by simp [Heap.SortedKeys, Heap.keys]) (by simp)
    (fun a => by
      by_cases ha : a = (0 : ℤ)
      · subst ha; decide
      · rw [if_neg (fun hmem => ha (List.mem_singleton.mp hmem)),
          Heap.get_cons_ne _ _ ha, Heap.get_nil])

end NonVacuity

/-! ## Axiom-hygiene pins -/

#assert_axioms percell_consistentFrom_filter
#assert_axioms cellTrace_heap_domain
#assert_axioms percell_consistent_strip
#assert_axioms percell_boundary_root_derived
#assert_axioms percell_umem_sound
#assert_namespace_axioms Dregg2.Crypto.PerCellUmem

end Dregg2.Crypto.PerCellUmem
