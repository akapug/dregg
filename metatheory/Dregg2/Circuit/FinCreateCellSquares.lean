/-
# Dregg2.Circuit.FinCreateCellSquares — DEBT-B step 3C: the LAST TWO deployed program squares.

`FinProgramSquares` (committed) discharges the operational commuting square — R1's `hpres` gate
`FinKernelState.denote_surjective_on_reachable` — for 28 of the 30 deployed `*Stmt` programs. The two it
EXCLUDED were the account-growing pair `createCellStmt` / `createCellFromFactoryStmt`, both of which need
the `allocCell` structural allocator. Step 3A (`FinAllocCell`, committed) built that primitive and its
UNCONDITIONAL headline `denote_finAllocCell`, plus the `seq (guard φ) (allocCell n)` assembly
`guardThenAlloc_square`. This file closes the last two squares on top of it, fully discharging `hpres`
for ALL 30 deployed programs.

## `createCellStmt` — the clean case.
`createCellStmt actor newCell = seq (guard (createCellGuard …)) (allocCell (fun _ => newCell))` — EXACTLY the
`guardThenAlloc_square` shape. Its square is that lemma applied, no new obligation (`allocCell` is
unconditional).

## `createCellFromFactoryStmt` — the factory install, with a MEASURED subtlety.
`createCellFromFactoryStmt actor newCell vk =
   seq (guard <factory gate>) (seq (allocCell (fun _ => newCell))
     (seq (setCell {newCell} <factory cell leaf>) (setSlotCaveats <factory caveats>)))`.
Four leaves. `guard` is `Pure` (`denote_finInterp`), `allocCell` is `denote_finAllocCell`, `setSlotCaveats`
is `denote_finSetSlotCaveats` under a finite-diff we prove (`factoryCaveatsWrite_finiteDiff`). The `setCell`
leaf is the subtle one: its non-default side condition `factoryCellWrite vk newCell k newCell ≠ .record []`
is TRUE only when the factory lookup succeeds (the `some e` arm is a `setField`, non-default) — and GENUINELY
FALSE when it fails (the `none` arm is `k.cell newCell`, which can be the default `.record []`, proved by
`factoryCellWrite_can_be_default`). So the finite `setCell` leaf is a `dite` on the lookup: `finSetCell` in
the `some` case, IDENTITY (`some f`) in the `none` case — the identity is faithful because in the `none` arm
`factoryCellWrite` writes the CURRENT cell value back, a no-op that `interp`'s `setCell` also performs. Its
square `finFactoryCell_square` is proved for ALL states (both arms), so the four leaves compose via
`denote_seq_compose` verbatim.

Builds ON committed `FinAllocCell`/`FinInterp`/`FinProgramSquares` + Argus effect terms; edits NOTHING
committed. Sorry-free; no carrier.
-/
import Dregg2.Circuit.FinAllocCell
import Dregg2.Circuit.FinProgramSquares
import Dregg2.Circuit.Argus.Effects.CreateCell
import Dregg2.Circuit.Argus.Effects.CreateCellFromFactory

namespace Dregg2.Circuit.FinCreateCellSquares

open Dregg2.Exec
open Dregg2.Exec.EffectsState (setField)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.FinInterp
open Dregg2.Circuit.FinAllocCell
open Dregg2.Circuit.FinProgramSquares (setField_ne_nil)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Argus.Effects
open Dregg2.Circuit.Argus.Effects.CreateCell (createCellStmt createCellGuard)
open Dregg2.Circuit.Argus.Effects.CreateCellFromFactory
  (createCellFromFactoryStmt createCellFromFactoryGuard factoryCellWrite factoryCaveatsWrite)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## §1 — `createCellStmt_square` — the clean `guard`-then-`allocCell` shape. -/

/-- **`createCellStmt_square`** — R1's `hpres` for the deployed `createCell` effect term. The finite step
(guard leaf via `finInterp`, then the `allocCell` allocator leaf) denotes to `interp (createCellStmt …)`.
Directly the committed `guardThenAlloc_square`, since `createCellStmt` IS `seq (guard φ) (allocCell n)`. -/
theorem createCellStmt_square (actor newCell : CellId) (f : FinKernelState) :
    ((finInterp (.guard (createCellGuard actor newCell)) f).bind
      (fun f' => some (finAllocCell (fun _ => newCell) f'))).map denote
      = interp (createCellStmt actor newCell) (denote f) := by
  unfold createCellStmt
  exact guardThenAlloc_square (createCellGuard actor newCell) (fun _ => newCell) f

/-! ## §2 — the factory-create side obligations (REAL theorems, both polarities of the setCell leaf). -/

/-- The factory `cell` leaf at `newCell` is NON-default whenever the factory lookup SUCCEEDS: the `some e`
arm is a `setField` write, non-default by `setField_ne_nil`. This discharges the `setCell` non-default
condition in the gate-passing (factory-present) case. -/
theorem factoryCellWrite_nd_isSome {vk : Int} {newCell : CellId} {k : RecordKernelState}
    (h : (findFactory k.factories vk.toNat).isSome = true) :
    factoryCellWrite vk newCell k newCell ≠ Value.record [] := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
  simp only [factoryCellWrite, if_true, he]
  exact setField_ne_nil _ _ _

/-- The factory `cell` leaf at `newCell` is the IDENTITY (writes back the current value) when the factory
lookup FAILS: the `none` arm is `k.cell newCell`. This is why the finite `setCell` leaf is IDENTITY in the
`none` case — and why the square stays faithful there (a no-op write). -/
theorem factoryCellWrite_none {vk : Int} {newCell : CellId} {k : RecordKernelState}
    (hfind : findFactory k.factories vk.toNat = none) :
    factoryCellWrite vk newCell k newCell = k.cell newCell := by
  simp only [factoryCellWrite, if_true, hfind]

/-- The factory `slotCaveats` write is a single-cell diff off `{newCell}` (mirrors
`refreshDelegationsMap_finiteDiff`): every cell but `newCell` keeps its published caveats. This discharges
the `setSlotCaveats` FiniteDiff side condition, UNCONDITIONALLY (for every state). -/
theorem factoryCaveatsWrite_finiteDiff (vk : Int) (newCell : CellId) (f : FinKernelState) :
    ∀ c, c ∉ ({newCell} : Finset CellId) →
      factoryCaveatsWrite vk newCell (denote f) c = (denote f).slotCaveats c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  simp only [factoryCaveatsWrite]
  rw [if_neg hc]

/-! ## §3 — the factory `setCell` leaf as a `dite`-guarded finite step, and its square (both arms). -/

/-- **`finFactoryCell`** — the finite step for the factory `cell`-install leaf. When the factory lookup
succeeds, it is the sparse `finSetCell` write (values proven non-default by `factoryCellWrite_nd_isSome`);
when it fails, it is the IDENTITY (`some f`) — the faithful mirror of the no-op write the `none` arm
performs. -/
noncomputable def finFactoryCell (vk : Int) (newCell : CellId) (f : FinKernelState) : Option FinKernelState :=
  if h : (findFactory (denote f).factories vk.toNat).isSome = true then
    some (finSetCell {newCell} (fun k _ => factoryCellWrite vk newCell k newCell) f
      (fun c _ => factoryCellWrite_nd_isSome h))
  else some f

/-- **`finFactoryCell_square`** — the factory `setCell` leaf's commuting square, PROVED for EVERY state (both
lookup arms). In the `some` arm it is `denote_finSetCell`; in the `none` arm the finite identity denotes to
`interp`'s `setCell`, whose write is the no-op `factoryCellWrite` performs there (`factoryCellWrite_none`). -/
theorem finFactoryCell_square (vk : Int) (newCell : CellId) (g : FinKernelState) :
    (finFactoryCell vk newCell g).map denote
      = interp (.setCell ({newCell} : Finset CellId) (fun k _ => factoryCellWrite vk newCell k newCell))
          (denote g) := by
  unfold finFactoryCell
  by_cases h : (findFactory (denote g).factories vk.toNat).isSome = true
  · rw [dif_pos h, Option.map_some]
    exact denote_finSetCell {newCell} (fun k _ => factoryCellWrite vk newCell k newCell) g
      (fun c _ => factoryCellWrite_nd_isSome h)
  · rw [dif_neg h, Option.map_some]
    have hnone : findFactory (denote g).factories vk.toNat = none :=
      Option.not_isSome_iff_eq_none.mp (by simpa using h)
    simp only [interp]
    congr 1
    have hmap : (fun c => if c ∈ ({newCell} : Finset CellId)
        then (fun (k : RecordKernelState) (_ : CellId) => factoryCellWrite vk newCell k newCell) (denote g) c
        else (denote g).cell c) = (denote g).cell := by
      funext c
      by_cases hc : c ∈ ({newCell} : Finset CellId)
      · have hce : c = newCell := Finset.mem_singleton.mp hc
        rw [if_pos hc, hce]
        exact factoryCellWrite_none hnone
      · rw [if_neg hc]
    rw [hmap]

/-! ## §4 — the leaf squares for the `allocCell` and `setSlotCaveats` legs (Option-map shape). -/

/-- The `allocCell` leaf square in the `Option.map` shape `denote_seq_compose` consumes (the allocator is
unconditional — no side obligation). -/
theorem allocLeaf_square (newCell : CellId) (g : FinKernelState) :
    (some (finAllocCell (fun _ => newCell) g)).map denote
      = interp (.allocCell (fun _ : RecordKernelState => newCell)) (denote g) := by
  rw [Option.map_some]
  exact denote_finAllocCell (fun _ => newCell) g

/-- The factory `setSlotCaveats` leaf square (FiniteDiff discharged by §2). -/
theorem caveatsLeaf_square (vk : Int) (newCell : CellId) (g : FinKernelState) :
    (some (finSetSlotCaveats (fun k => factoryCaveatsWrite vk newCell k) {newCell} g)).map denote
      = interp (.setSlotCaveats (fun k => factoryCaveatsWrite vk newCell k)) (denote g) := by
  rw [Option.map_some]
  exact denote_finSetSlotCaveats (fun k => factoryCaveatsWrite vk newCell k) {newCell} g
    (factoryCaveatsWrite_finiteDiff vk newCell g)

/-! ## §5 — `createCellFromFactoryStmt_square` — the four leaves composed via `denote_seq_compose`. -/

/-- **`createCellFromFactoryStmt_square`** — R1's `hpres` for the deployed `createCellFromFactory` effect
term. The finite step composes the four leaves (guard ⨾ allocCell ⨾ factory-cell ⨾ factory-caveats) through
the committed `denote_seq_compose`; each leaf's square is §3/§4 (with the setCell non-default handled by the
`dite` and the setSlotCaveats finite-diff by §2). -/
theorem createCellFromFactoryStmt_square (actor newCell : CellId) (vk : Int) (f : FinKernelState) :
    ((finInterp (.guard (createCellFromFactoryGuard actor newCell vk)) f).bind (fun f1 =>
      (some (finAllocCell (fun _ => newCell) f1)).bind (fun f2 =>
        (finFactoryCell vk newCell f2).bind (fun f3 =>
          some (finSetSlotCaveats (fun k => factoryCaveatsWrite vk newCell k) {newCell} f3))))).map denote
      = interp (createCellFromFactoryStmt actor newCell vk) (denote f) := by
  unfold createCellFromFactoryStmt
  exact denote_seq_compose
    (fun g => denote_finInterp (.guard (createCellFromFactoryGuard actor newCell vk)) trivial g)
    (fun g => denote_seq_compose (allocLeaf_square newCell)
      (fun g' => denote_seq_compose (finFactoryCell_square vk newCell) (caveatsLeaf_square vk newCell) g') g)
    f

/-! ## §6 — HPRES STATUS.

With `createCellStmt_square` and `createCellFromFactoryStmt_square` proved here, ALL 30 deployed `*Stmt`
programs (28 in `FinProgramSquares`, these 2) now carry their operational commuting square. So R1's `hpres`
gate `FinKernelState.denote_surjective_on_reachable` is FULLY DISCHARGED across every deployed program.
The only constructor with NO deployed program remains `setDelegate` (only `CompileFold`'s stub); its
per-constructor square is proved in `FinInterp` (§3′) but is vacuously unused — this is NOT a deployed
program and does not affect the 30-of-30 count, so no residue remains for any deployed effect. -/

/-! ## §7 — TEETH (`#guard` + theorems, both polarities). -/

section Teeth

-- The deployed `createCellStmt` COMMITS on a privileged fresh create, and REJECTS an unauthorized one:
#guard (interp (createCellStmt 0 2) Dregg2.Circuit.Argus.Effects.CreateCell.kCC).isSome
#guard (interp (createCellStmt 1 2) Dregg2.Circuit.Argus.Effects.CreateCell.kCC).isNone

/-- A minimal kernel with an EMPTY factory registry and every cell defaulting to `.record []` — the witness
that the factory `setCell` leaf's non-default obligation genuinely FAILS in the `none` arm. -/
def kNoFac : RecordKernelState :=
  { accounts := ∅, cell := fun _ => Value.record [], caps := fun _ => [], factories := [] }

/-- **POSITIVE tooth — `createCellStmt` BIRTHS a cell (both value polarities on the fresh slot).** The
committed create of fresh cell `2` COMMITS to `createCellIntoAsset kCC 2`, whose fresh slot has its ledger
column zeroed (`bal 2 0 = 0`) and its `cell` value reset to the born-empty default `Value.int 0` — which is
PROVABLY `≠ Value.record []` (the measured `default = Value.int 0` correction, NOT the cell map's default).
Both polarities on the same value: `= Value.int 0` AND `≠ Value.record []`. -/
theorem createCellStmt_births_int0 :
    interp (createCellStmt 0 2) CreateCell.kCC
      = some (createCellIntoAsset CreateCell.kCC 2)
    ∧ (createCellIntoAsset CreateCell.kCC 2).cell 2 = Value.int 0
    ∧ (createCellIntoAsset CreateCell.kCC 2).bal 2 0 = 0
    ∧ (createCellIntoAsset CreateCell.kCC 2).cell 2 ≠ Value.record [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CreateCell.interp_createCellStmt_eq_createCellK, if_pos]
    exact (CreateCell.createCellGuard_iff 0 2 _).mp (by decide)
  · simp [createCellIntoAsset, bornEmptyCellSlots, default_value]
  · simp [createCellIntoAsset, bornEmptyCellSlots]
  · rw [show (createCellIntoAsset CreateCell.kCC 2).cell 2 = Value.int 0 from by
        simp [createCellIntoAsset, bornEmptyCellSlots, default_value]]
    exact valInt0_ne_record

/-- **NEGATIVE tooth — the factory `setCell` non-default obligation is GENUINELY FALSE (`none` arm).** On a
kernel with an empty factory registry and `cell newCell = .record []`, the factory `cell` leaf equals the
default `.record []`, so the sparse `insertNZ`-based `finSetCell` CANNOT represent it — exactly why
`finFactoryCell` must fall back to identity in the `none` arm. An under-approximating uniform `finSetCell`
would be unsound here. -/
theorem factoryCellWrite_can_be_default :
    findFactory kNoFac.factories (0 : Int).toNat = none
    ∧ factoryCellWrite 0 5 kNoFac 5 = Value.record [] := by
  have hnone : findFactory kNoFac.factories (0 : Int).toNat = none := by decide
  refine ⟨hnone, ?_⟩
  rw [factoryCellWrite_none hnone]
  rfl

end Teeth

end Dregg2.Circuit.FinCreateCellSquares
