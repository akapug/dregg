/-
# Dregg2.Substrate.HeapKernel — THE HEAP's kernel face: the guarded heap-update step
(REFINEMENT-DESIGN Decision 1, wave R2 — the `write`-verb completion, standalone).

`Dregg2.Substrate.Heap` is the openable sorted-map semantics. THIS module is how the heap sits
beside `RecordKernelState`: the design says "the kernel does not grow" — the `write` verb's spec
has read "guarded **heap**/program/permission update" since the VerbRegistry was written
(`Substrate/VerbRegistry.lean §2`, `Verb.write`), so a heap operation is a `write`-verb INSTANCE
under the existing frame discipline. Concretely:

  * ONE register (`heap_root`, a named non-`balance` field of the cell record) carries the
    committed root; the heap LEAVES live in the per-cell side-map `HeapExt` (the component that
    will be spliced into `RecordKernelState` at rotation time — like `nullifiers`/`commitments`/
    `slotCaveats` were added, an additive extension defaulting empty).
  * the guarded heap step `heapStepGuarded` is built ON `EffectsState.stateStepGuarded` (the
    caveat-gated field write — the `write` verb's proven gate stack: authority + membership +
    lifecycle-liveness + per-slot caveats), EXACTLY the `RelationalCaveat.relStateStepGuarded`
    extension pattern: run the existing guarded write of the RECOMPUTED root into `heap_root`,
    ADD the heap-atom gate, fail closed on either. The post-state is the underlying write's
    post-state — so every existing keystone lifts VERBATIM (`heapStepGuarded_factors`).
  * the GUARD ATOMS `heap_contains` / `heap_get` (`HeapAtom`) have the `RelCaveat` shape (an
    inductive with a decidable, fail-closed `eval`) — the guard-algebra additions the design
    names, with coordination cost classified like the existing relational atoms (they read ONE
    cell's committed heap; no cross-cell read).

## What is PROVED here (the design's "the theorems extend trivially", made actual)

  * **BALANCE-NEUTRALITY** — the heap step moves NO asset: the scalar `balance` total is unchanged
    (`heapStep_conserves`), the per-asset `bal` ledger is LITERALLY untouched
    (`heapStep_moves_no_asset`), and the W1 exact value law is preserved
    (`heapStep_preserves_exact`). Conservation lifts untouched, by construction.
  * **FRAME DISCIPLINE** — other cells' heaps and records are untouched
    (`heapStep_heap_frame_cells` / `heapStep_cell_frame`); on the written cell, every field other
    than `heap_root` is untouched (`heapStep_field_frame`) and every heap key other than the
    written `(collection, key)` keeps its opening (`heapStep_key_frame`, under the ONE named CR
    floor); caps/authority untouched (`heapStep_caps_unchanged`/`heapStep_authGraph_unchanged`).
  * **THE REGISTER BINDS THE HEAP** — the committed `heap_root` field reads back EXACTLY the
    recomputed root of the post-heap (`heapStep_root_written`): the register and the side-map are
    one object (the cell≡circuit identity seed: cell, executor, and circuit all read
    `Heap.root` of the same leaf list).
  * **GATES** — authority still required (`heapStep_authorized`), atoms fail closed
    (`heapStep_atom_violation_fails`), the metadata clock advances (`heapStep_obsadvance`),
    sortedness is an invariant (`heapStep_sorted`).

## The splice (deliberately NOT done here)

`RecordKernelState` itself is NOT edited (the splice rides THE ONE ROTATION with the registers
8→16 + PI v3 bundle): at rotation time, `HeapExt.heap` becomes a `RecordKernelState` field
(defaulting `fun _ => []`, the additive-extension pattern), `heapStepGuarded` loses its explicit
`ext` parameter, and the executor's `write`-verb dispatch gains the heap arm. Every theorem below
is stated so that substitution is name-stable.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto enters ONLY as the named
`Poseidon2SpongeCR` hypothesis (the cap-root floor) and ONLY where an opening is compared across
distinct addresses. No `sorry`, no `:= True`, no `native_decide`. NEW file; imports read-only.
-/
import Dregg2.Substrate.Heap
import Dregg2.Exec.EffectsState

namespace Dregg2.Substrate.HeapKernel

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §0 — the `heap_root` register (the ONE named field the heap step writes). -/

/-- **The `heap_root` register** — the named cell-record field carrying the committed heap root
(REFINEMENT-DESIGN Decision 1: "one register holds `heap_root`"). A non-`balance` metadata field,
so the `write`-verb regime invariants apply verbatim. -/
def heapRootField : FieldName := "heap_root"

/-- `heap_root` is NOT the conserved `balance` field — the side condition every balance-neutrality
lift consumes. -/
theorem heapRootField_ne_balance : heapRootField ≠ balanceField := by decide

/-- Reading a field OTHER than the one `setField` wrote is unchanged (the record-level frame; the
same induction the factory modules carry — restated here so this NEW file edits nothing). -/
theorem fieldOf_setField_ne (f g : FieldName) (cell : Value) (v : Int) (hfg : g ≠ f) :
    fieldOf g (setField f cell (.int v)) = fieldOf g cell := by
  have hfg' : (f == g) = false := by
    rw [beq_eq_false_iff_ne]; exact fun h => hfg h.symm
  have hlist : ∀ fs : List (FieldName × Value),
      ((setField.setFieldList f fs (.int v)).find? (fun p => p.1 == g))
        = fs.find? (fun p => p.1 == g) := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, List.find?, hfg']
    | cons hd tl ih =>
        obtain ⟨kk, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (kk == f) = true
        · have hkk : kk = f := by simpa using hk
          rw [if_pos hk]
          simp only [List.find?_cons, hfg', hkk]
        · rw [if_neg hk]
          by_cases hg : (kk == g) = true
          · simp only [List.find?_cons, hg]
          · rw [List.find?_cons_of_neg (by simpa using hg),
                List.find?_cons_of_neg (by simpa using hg)]
            exact ih
  unfold fieldOf Value.scalar Value.field
  cases cell with
  | record fs => simp only [setField]; rw [hlist fs]
  | int n => simp [setField, List.find?, hfg']
  | dig d => simp [setField, List.find?, hfg']
  | sym s => simp [setField, List.find?, hfg']

/-! ## §1 — `HeapExt`: the heap component as it will sit in `RecordKernelState`.

A per-cell heap, DEFAULTING EMPTY — the exact additive-extension shape `nullifiers`/`commitments`/
`slotCaveats` rode in on (`RecordKernel.lean`: "DEFAULTS EMPTY (the additive extension)"). Defined
standalone; the rotation splices this field into `RecordKernelState` verbatim. -/

/-- **The heap component** (the future `RecordKernelState.heaps` field): each cell's openable
sorted map. Defaults to the empty heap everywhere — a cell that never writes its heap has
`root hash [] ` as its `heap_root` and is unaffected (the additive extension). -/
structure HeapExt where
  /-- The per-cell heap leaf list (`(addr, value)` sorted by address = key-hash). -/
  heap : CellId → Heap.FeltHeap := fun _ => []

/-! ## §2 — the GUARD ATOMS: `heap_contains` / `heap_get` (the design's guard-algebra additions).

The `RelCaveat` shape (`Exec/RelationalCaveat.lean §1`): an inductive atom with a decidable,
computable, FAIL-CLOSED `eval`. Both atoms read ONE cell's committed heap — the coordination cost
class of the existing relational atoms (no cross-cell read, no ordering forced). -/

/-- **The heap guard atoms.** `heapContains coll key` — the addressed slot is PRESENT;
`heapGetEq coll key val` — the addressed slot holds EXACTLY `val`. The two atoms the design names
(`heap_contains` / `heap_get`), in the relational-atom shape. -/
inductive HeapAtom where
  /-- the membership atom: `(coll, key)` is present in the heap. -/
  | heapContains (coll key : ℤ)
  /-- the read atom: `(coll, key)` is present AND holds `val`. -/
  | heapGetEq (coll key val : ℤ)
  deriving Repr, DecidableEq

/-- Evaluate one atom against a committed heap (decidable, fail-closed). -/
def HeapAtom.eval (hash : List ℤ → ℤ) : HeapAtom → Heap.FeltHeap → Bool
  | .heapContains coll key, h => (Heap.hget hash h coll key).isSome
  | .heapGetEq coll key val, h => Heap.hget hash h coll key == some val

/-- Do ALL heap atoms admit the committed heap? FAIL-CLOSED (the `relCaveatsAdmit` shape). -/
def heapAtomsAdmit (hash : List ℤ → ℤ) (atoms : List HeapAtom) (h : Heap.FeltHeap) : Bool :=
  atoms.all (fun a => a.eval hash h)

/-- `heapContains` is EXACTLY heap membership (the atom's semantic characterization). -/
theorem heapContains_eval_iff (hash : List ℤ → ℤ) (coll key : ℤ) (h : Heap.FeltHeap) :
    (HeapAtom.heapContains coll key).eval hash h = true
      ↔ ∃ v, Heap.hget hash h coll key = some v := by
  simp [HeapAtom.eval, Option.isSome_iff_exists]

/-- `heapGetEq` is EXACTLY the addressed read (the atom's semantic characterization). -/
theorem heapGetEq_eval_iff (hash : List ℤ → ℤ) (coll key val : ℤ) (h : Heap.FeltHeap) :
    (HeapAtom.heapGetEq coll key val).eval hash h = true
      ↔ Heap.hget hash h coll key = some val := by
  simp [HeapAtom.eval]

/-! ## §3 — `heapStepGuarded`: the guarded heap update (a `write`-verb instance).

The `relStateStepGuarded` extension pattern: gate on the heap atoms (against the PRE-state heap —
guards are preconditions, like every caveat), then run THE EXISTING guarded field write
(`stateStepGuarded`: authority + membership + lifecycle-liveness + per-slot caveats on `heap_root`)
writing the RECOMPUTED root of the post-heap. Commits iff every gate passes; fail-closed. -/

/-- The post-heap of a heap write on `target` (the sorted insert-or-update at the address). -/
def heapAfter (hash : List ℤ → ℤ) (ext : HeapExt) (target : CellId) (coll key v : ℤ) :
    Heap.FeltHeap :=
  Heap.hset hash (ext.heap target) coll key v

/-- **`heapStepGuarded` — the guarded heap-update step (computable).** Atom gate on the pre-state
heap, then the EXISTING caveat-gated `write` of the recomputed root into `heap_root`. On commit:
the kernel state is EXACTLY `stateStepGuarded`'s post-state (so every `write`-verb keystone lifts
verbatim) and the target's heap is the sorted-updated leaf list. Fail-closed on EVERY gate
(atoms / authority / membership / lifecycle / slot caveats). -/
def heapStepGuarded (hash : List ℤ → ℤ) (s : RecChainedState) (ext : HeapExt)
    (atoms : List HeapAtom) (actor target : CellId) (coll key v : ℤ) :
    Option (RecChainedState × HeapExt) :=
  if heapAtomsAdmit hash atoms (ext.heap target) = true then
    match stateStepGuarded s heapRootField actor target
        (Heap.root hash (heapAfter hash ext target coll key v)) with
    | some s' => some (s', { heap := fun c =>
        if c = target then heapAfter hash ext target coll key v else ext.heap c })
    | none => none
  else none

/-- **`heapStepGuarded_factors` — the bridge every keystone lifts through.** A committed heap step
factors as: (a) the heap atoms admitted the pre-heap; (b) the UNDERLYING guarded `write` of the
recomputed root committed with post-state `s'`; (c) the post-heap is the sorted update on `target`
and untouched elsewhere. The `stateStepGuarded_eq`/`stateStep_factors` shape, one level up. -/
theorem heapStepGuarded_factors {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    heapAtomsAdmit hash atoms (ext.heap target) = true ∧
    stateStepGuarded s heapRootField actor target
        (Heap.root hash (heapAfter hash ext target coll key v)) = some s' ∧
    (∀ c, ext'.heap c =
        if c = target then heapAfter hash ext target coll key v else ext.heap c) := by
  unfold heapStepGuarded at h
  by_cases hg : heapAtomsAdmit hash atoms (ext.heap target) = true
  · rw [if_pos hg] at h
    cases hw : stateStepGuarded s heapRootField actor target
        (Heap.root hash (heapAfter hash ext target coll key v)) with
    | none => rw [hw] at h; exact absurd h (by simp)
    | some s'' =>
        rw [hw] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, hext⟩ := h
        subst hs
        refine ⟨hg, rfl, ?_⟩
        intro c
        rw [← hext]
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **FAIL-CLOSED on the atom gate.** A violated heap atom (`heapAtomsAdmit = false`) means the
step does NOT commit — the guard-algebra teeth, exactly `stateStepGuarded_caveat_violation_fails`'s
shape. -/
theorem heapStep_atom_violation_fails (hash : List ℤ → ℤ) (s : RecChainedState) (ext : HeapExt)
    (atoms : List HeapAtom) (actor target : CellId) (coll key v : ℤ)
    (hviol : heapAtomsAdmit hash atoms (ext.heap target) = false) :
    heapStepGuarded hash s ext atoms actor target coll key v = none := by
  unfold heapStepGuarded
  rw [if_neg (by rw [hviol]; simp)]

/-! ## §4 — BALANCE-NEUTRALITY: the heap step moves NO asset (conservation lifts untouched). -/

/-- **`heapStep_conserves` — the scalar `balance` total is UNCHANGED.** The heap step is a `write`
of the non-`balance` `heap_root` field, so `guarded_state_conserves` applies verbatim — the heap is
balance-neutral BY CONSTRUCTION (the design's "conservation lifts untouched"). -/
theorem heapStep_conserves {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    recTotal s'.kernel = recTotal s.kernel :=
  guarded_state_conserves heapRootField_ne_balance (heapStepGuarded_factors h).2.1

/-- **`heapStep_moves_no_asset` — the per-asset ledger is LITERALLY untouched.** The underlying
field write edits only the `cell` record map; the `bal : CellId → AssetId → ℤ` ledger and the
`accounts` carrier are the SAME functions, so every per-asset total is unchanged. The strongest
balance-neutrality statement: not conserved-by-cancellation, UNTOUCHED. -/
theorem heapStep_moves_no_asset {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    s'.kernel.bal = s.kernel.bal ∧
    s'.kernel.accounts = s.kernel.accounts ∧
    (∀ a : AssetId, recTotalAsset s'.kernel a = recTotalAsset s.kernel a) := by
  have hw := stateStepGuarded_eq (heapStepGuarded_factors h).2.1
  obtain ⟨_, hs'⟩ := stateStep_factors hw
  subst hs'
  exact ⟨rfl, rfl, fun a => rfl⟩

/-- **`heapStep_preserves_exact` — the W1 exact value law survives the heap step.** If every
asset's total was exactly `0` before, it is after — `stateStep_preserves_exact` lifted. -/
theorem heapStep_preserves_exact {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext'))
    (hex : ExactConservation s.kernel) : ExactConservation s'.kernel :=
  stateStep_preserves_exact (stateStepGuarded_eq (heapStepGuarded_factors h).2.1) hex

/-! ## §5 — the gate stack: authority required, caps untouched, metadata clock advances. -/

/-- **`heapStep_authorized`.** A committed heap step means the actor held authority over the
target — the `write` verb's authority gate fires under the heap gates too. -/
theorem heapStep_authorized {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    stateAuthB s.kernel.caps actor target = true :=
  guarded_state_authorized (heapStepGuarded_factors h).2.1

/-- **`heapStep_caps_unchanged`.** The heap step edits NO capability — the cap table is the same
function (authority-neutrality of the `state` substance's verb). -/
theorem heapStep_caps_unchanged {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    s'.kernel.caps = s.kernel.caps := by
  have hw := stateStepGuarded_eq (heapStepGuarded_factors h).2.1
  obtain ⟨_, hs'⟩ := stateStep_factors hw
  subst hs'
  rfl

/-- **`heapStep_authGraph_unchanged`.** The reconstructed authority graph is unchanged — the
abstract-Spec face of cap-neutrality. -/
theorem heapStep_authGraph_unchanged {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    Dregg2.Spec.execGraph s'.kernel.caps = Dregg2.Spec.execGraph s.kernel.caps :=
  guarded_state_authGraph_unchanged (heapStepGuarded_factors h).2.1

/-- **`heapStep_obsadvance`.** The receipt chain grows by exactly one row — the monotone metadata
clock every committed action carries. -/
theorem heapStep_obsadvance {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    s'.log.length = s.log.length + 1 :=
  state_obsadvance (stateStepGuarded_eq (heapStepGuarded_factors h).2.1)

/-! ## §6 — FRAME DISCIPLINE: everything not written is untouched. -/

/-- **FRAME (other cells' heaps).** A heap write to `target` leaves every other cell's heap the
SAME leaf list (hence the same root, the same openings — everything). -/
theorem heapStep_heap_frame_cells {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext'))
    (c : CellId) (hc : c ≠ target) : ext'.heap c = ext.heap c := by
  rw [(heapStepGuarded_factors h).2.2 c, if_neg hc]

/-- **FRAME (other cells' records).** Every other cell's record is untouched. -/
theorem heapStep_cell_frame {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext'))
    (c : CellId) (hc : c ≠ target) : s'.kernel.cell c = s.kernel.cell c := by
  have hw := stateStepGuarded_eq (heapStepGuarded_factors h).2.1
  obtain ⟨_, hs'⟩ := stateStep_factors hw
  subst hs'
  simp [writeField, hc]

/-- **FRAME (the written cell's OTHER registers).** On `target`, every field other than
`heap_root` reads the same — the heap step touches exactly ONE register. -/
theorem heapStep_field_frame {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext'))
    (g : FieldName) (hg : g ≠ heapRootField) :
    fieldOf g (s'.kernel.cell target) = fieldOf g (s.kernel.cell target) := by
  have hw := stateStepGuarded_eq (heapStepGuarded_factors h).2.1
  obtain ⟨_, hs'⟩ := stateStep_factors hw
  subst hs'
  simp only [writeField]
  exact fieldOf_setField_ne heapRootField g (s.kernel.cell target) _ hg

/-- **FRAME (untouched keys keep their openings).** On the written cell's heap, every address
other than the written `(coll, key)` reads the same — under the ONE named CR floor (distinct pairs
occupy distinct key-hash addresses). The design's "pay-per-touch: untouched data costs nothing". -/
theorem heapStep_key_frame {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext'))
    (coll' key' : ℤ) (hne : ¬(coll' = coll ∧ key' = key)) :
    Heap.hget hash (ext'.heap target) coll' key' = Heap.hget hash (ext.heap target) coll' key' := by
  rw [(heapStepGuarded_factors h).2.2 target, if_pos rfl]
  exact Heap.hget_hset_frame hash hCR (ext.heap target) coll key coll' key' v hne

/-- **READ-AFTER-WRITE through the step.** The written `(coll, key)` reads back exactly `v` on the
committed post-heap. -/
theorem heapStep_get_written {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    Heap.hget hash (ext'.heap target) coll key = some v := by
  rw [(heapStepGuarded_factors h).2.2 target, if_pos rfl]
  exact Heap.hget_hset_self hash (ext.heap target) coll key v

/-- **THE REGISTER BINDS THE HEAP (`heapStep_root_written`).** The committed `heap_root` register
reads back EXACTLY `Heap.root` of the committed post-heap — register and side-map are one object.
This is the cell≡circuit identity seed: the cell's stored root, the executor's recompute, and the
circuit's seeded column all read THIS function of THIS leaf list (the cap Phase-A discipline,
`EffectVmEmitCapRoot §"cap Phase A VALUE model"`, with the generic leaf). -/
theorem heapStep_root_written {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext')) :
    fieldOf heapRootField (s'.kernel.cell target) = Heap.root hash (ext'.heap target) := by
  have hroot := guarded_state_field_written (heapStepGuarded_factors h).2.1
  rw [(heapStepGuarded_factors h).2.2 target, if_pos rfl]
  exact hroot

/-- **SORTEDNESS IS AN INVARIANT.** A sorted pre-heap commits to a sorted post-heap (the
sorted-insert gate's preservation, lifted through the step). -/
theorem heapStep_sorted {hash : List ℤ → ℤ} {s : RecChainedState} {ext : HeapExt}
    {atoms : List HeapAtom} {actor target : CellId} {coll key v : ℤ}
    {s' : RecChainedState} {ext' : HeapExt}
    (h : heapStepGuarded hash s ext atoms actor target coll key v = some (s', ext'))
    (hs : Heap.SortedKeys (ext.heap target)) : Heap.SortedKeys (ext'.heap target) := by
  rw [(heapStepGuarded_factors h).2.2 target, if_pos rfl]
  exact Heap.set_sorted (ext.heap target) _ v hs

-- §3–§6 tripwires: every keystone kernel-clean; CR enters only `heapStep_key_frame` (named hyp).
#assert_axioms fieldOf_setField_ne
#assert_axioms heapContains_eval_iff
#assert_axioms heapGetEq_eval_iff
#assert_axioms heapStepGuarded_factors
#assert_axioms heapStep_atom_violation_fails
#assert_axioms heapStep_conserves
#assert_axioms heapStep_moves_no_asset
#assert_axioms heapStep_preserves_exact
#assert_axioms heapStep_authorized
#assert_axioms heapStep_caps_unchanged
#assert_axioms heapStep_authGraph_unchanged
#assert_axioms heapStep_obsadvance
#assert_axioms heapStep_heap_frame_cells
#assert_axioms heapStep_cell_frame
#assert_axioms heapStep_field_frame
#assert_axioms heapStep_key_frame
#assert_axioms heapStep_get_written
#assert_axioms heapStep_root_written
#assert_axioms heapStep_sorted

/-! ## §7 — NON-VACUITY: concrete commits, concrete refusals (witness TRUE and FALSE per gate).

The `EffectsState §10` concrete-state pattern: cells 0,1 with balances 100,5; actor 0 owns cell 0
(authority by ownership — empty cap table); the reference sponge from `Substrate/Heap §3`. -/

open Dregg2.Substrate.Heap (refSponge)

/-- The §10-shaped concrete chained state: cells 0,1; balances 100,5; empty caps; empty log. -/
def hs0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else .record [("balance", .int 5)]
        caps := fun _ => [] }
    log := [] }

/-- The empty heap extension (every cell's heap empty — the additive-extension default). -/
def hext0 : HeapExt := {}

/-- A heap extension whose cell 0 already holds `(1, 2) := 7` (for the satisfied-atom witness). -/
def hext1 : HeapExt :=
  { heap := fun c => if c = 0 then Heap.hset refSponge [] 1 2 7 else [] }

-- An authorized, atom-free heap write COMMITS (witness TRUE for the whole gate stack):
#guard (heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).isSome
-- ...reads back the written value at the written address:
#guard ((heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).map
        (fun p => Heap.hget refSponge (p.2.heap 0) 1 2)) == some (some 42)
-- ...writes the RECOMPUTED root into the `heap_root` register (the register binds the heap):
#guard ((heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).map
        (fun p => fieldOf heapRootField (p.1.kernel.cell 0)))
       == some (Heap.root refSponge (Heap.hset refSponge [] 1 2 42))
-- ...conserves the balance total (105 unchanged — balance-neutral):
#guard ((heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).map
        (fun p => recTotal p.1.kernel)) == some 105
-- ...does not perturb the target's balance field:
#guard ((heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).map
        (fun p => balOf (p.1.kernel.cell 0))) == some 100
-- ...advances the metadata clock by one:
#guard ((heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).map
        (fun p => p.1.log.length)) == some 1
-- ...and leaves the OTHER cell's heap untouched (the cell frame):
#guard ((heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42).map
        (fun p => p.2.heap 1)) == some []

-- An UNAUTHORIZED actor (9 owns nothing) cannot heap-write (fail-closed; witness FALSE):
#guard (heapStepGuarded refSponge hs0 hext0 [] 9 0 1 2 42).isSome == false

-- ATOM TEETH — `heap_contains`: satisfied admits, violated refuses (TRUE and FALSE):
#guard (heapStepGuarded refSponge hs0 hext1 [.heapContains 1 2] 0 0 1 2 99).isSome
#guard (heapStepGuarded refSponge hs0 hext0 [.heapContains 1 2] 0 0 1 2 99).isSome == false
-- ATOM TEETH — `heap_get`: the exact stored value admits, a wrong expectation refuses:
#guard (heapStepGuarded refSponge hs0 hext1 [.heapGetEq 1 2 7] 0 0 3 4 99).isSome
#guard (heapStepGuarded refSponge hs0 hext1 [.heapGetEq 1 2 8] 0 0 3 4 99).isSome == false

-- The atoms in isolation (TRUE and FALSE instances of each guard atom):
#guard (HeapAtom.heapContains 1 2).eval refSponge (hext1.heap 0)
#guard (HeapAtom.heapContains 3 4).eval refSponge (hext1.heap 0) == false
#guard (HeapAtom.heapGetEq 1 2 7).eval refSponge (hext1.heap 0)
#guard (HeapAtom.heapGetEq 1 2 8).eval refSponge (hext1.heap 0) == false

/-- Non-vacuity of the FAIL-CLOSED theorem at a concrete violated atom: the step provably refuses
(`heapStep_atom_violation_fails` firing, not just the `#guard`). -/
theorem hext0_violation_refuses :
    heapStepGuarded refSponge hs0 hext0 [.heapContains 1 2] 0 0 1 2 99 = none :=
  heapStep_atom_violation_fails refSponge hs0 hext0 [.heapContains 1 2] 0 0 1 2 99 (by decide)

/-- Non-vacuity of the conservation lift at a concrete committed step: balance-neutral, by the
THEOREM (not just the guard). -/
example (s' : RecChainedState) (ext' : HeapExt)
    (h : heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42 = some (s', ext')) :
    recTotal s'.kernel = recTotal hs0.kernel :=
  heapStep_conserves h

/-- Non-vacuity of the authority gate at a concrete committed step. -/
example (s' : RecChainedState) (ext' : HeapExt)
    (h : heapStepGuarded refSponge hs0 hext0 [] 0 0 1 2 42 = some (s', ext')) :
    stateAuthB hs0.kernel.caps 0 0 = true :=
  heapStep_authorized h

#assert_axioms hext0_violation_refuses

end Dregg2.Substrate.HeapKernel
