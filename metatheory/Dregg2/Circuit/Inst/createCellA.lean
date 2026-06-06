/-
# Dregg2.Circuit.Inst.createCellA — the v2-dual (`EffectCommit2Dual`) VALIDATION for `createCellA`.

`createCellA` grows `accounts` by `newCell` AND resets `bal` at `newCell` to `0` ∀ asset, prepends
the creation receipt, and freezes the other 15 kernel fields. Guard: `createCellAdmit` (privileged
creation authority ∧ freshness).

ADDITIVE: imports `AccountsCommit`, `EffectCommit2Dual`, `Spec/accountgrowth`; edits none.
-/
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.Inst.CreateCellA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.AccountsCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoAccountsBal` portal (the v1 `RestHashIffFrame` minus `accounts` + `bal`). -/

/-- **`RestIffNoAccountsBal RH`** — the rest hash binds the 15 non-`accounts`-non-`bal` components
(BIDIRECTIONAL), omitting `accounts` and `bal` (the touched fields of `createCellA`). Frame order
matches `CreateCellSpec`. -/
def RestIffNoAccountsBal (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.cell = k.cell ∧ k'.caps = k.caps ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats
      ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `createCellE` dual instance (`accounts` + `bal`). -/

structure CreateCellArgs where
  actor   : CellId
  newCell : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def createCellGuardProp (s : RecChainedState) (args : CreateCellArgs) : Prop :=
  createCellAdmit s.kernel args.actor args.newCell

instance (s : RecChainedState) (args : CreateCellArgs) : Decidable (createCellGuardProp s args) := by
  unfold createCellGuardProp createCellAdmit; exact inferInstanceAs (Decidable (_ ∧ _))

def createCellGuardEncode (s : RecChainedState) (args : CreateCellArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (createCellGuardProp s args) else 0

def createCellGuardGates : ConstraintSystem := [cBitGuard]

theorem createCellGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied createCellGuardGates a ↔ satisfied createCellGuardGates b := by
  unfold satisfied createCellGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def expectedAccounts (s : RecChainedState) (args : CreateCellArgs) : Finset CellId :=
  insert args.newCell s.kernel.accounts

def expectedBal (s : RecChainedState) (args : CreateCellArgs) : CellId → AssetId → ℤ :=
  fun c a => if c = args.newCell then 0 else s.kernel.bal c a

def accountsComp (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState CreateCellArgs :=
  accountsComponent LE cN hN hLE expectedAccounts

def balComp (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateCellArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD expectedBal

def createCellE (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2Dual RecChainedState CreateCellArgs where
  view         := chainView
  active1      := accountsComp LE cN hN hLE
  active2      := balComp D hD
  logUpdate    := some (fun s args => createReceipt args.actor args.newCell :: s.log)
  restFrame    := fun k k' =>
    (k'.cell = k.cell ∧ k'.caps = k.caps ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats
      ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := createCellGuardGates
  guardProp    := createCellGuardProp
  guardWidth   := 1
  guardEncode  := createCellGuardEncode
  guardLocal   := createCellGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem createCellGuardDecodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2Dual (createCellE LE cN hN hLE D hD) := by
  intro s args s' hsat
  change satisfied createCellGuardGates (createCellGuardEncode s args s') at hsat
  show createCellGuardProp s args
  have hg := hsat cBitGuard (by simp [createCellGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createCellGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem createCellGuardEncodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2Dual (createCellE LE cN hN hLE D hD) := by
  intro s args s' hg
  show satisfied createCellGuardGates (createCellGuardEncode s args s')
  intro c hc
  simp only [createCellGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createCellGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem createCellRestFrameDecodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoAccountsBal S.RH) :
    RestFrameDecodes2Dual S (createCellE LE cN hN hLE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `CreateCellSpec` (direct identity). -/

theorem apex_iff_createCellSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) :
    (createCellE LE cN hN hLE D hD).apex s args s' ↔
      CreateCellSpec s args.actor args.newCell s' := by
  show (createCellGuardProp s args
        ∧ s'.kernel.accounts = expectedAccounts s args
        ∧ s'.kernel.bal = expectedBal s args
        ∧ s'.log = createReceipt args.actor args.newCell :: s.log
        ∧ ((createCellE LE cN hN hLE D hD).restFrame s.kernel s'.kernel))
       ↔ CreateCellSpec s args.actor args.newCell s'
  unfold CreateCellSpec createCellGuardProp createCellE expectedAccounts expectedBal
  constructor
  · rintro ⟨hg, hacc, hbal, hlog, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hacc, hbal, hlog, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hacc, hbal, hlog, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hacc, hbal, hlog, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `createCellA_full_sound ⇒ CreateCellSpec`. -/

/-- **`createCellA_full_sound` — the VALIDATION.** A satisfying dual-component full-state witness for
`createCellE` proves the complete declarative `CreateCellSpec`. Portals: `RestIffNoAccountsBal RH`,
`logHashInjective LH`, `compressNInjective cN` + `listLeafInjective LE` (accounts sorted-list digest),
`Function.Injective D` (bal whole-function digest). -/
theorem createCellA_full_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoAccountsBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (createCellE LE cN hN hLE D hD)
        (encodeE2Dual S (createCellE LE cN hN hLE D hD) s args s')) :
    CreateCellSpec s args.actor args.newCell s' := by
  have hapex : (createCellE LE cN hN hLE D hD).apex s args s' :=
    effect2dual_circuit_full_sound S (createCellE LE cN hN hLE D hD)
      (createCellRestFrameDecodes S LE cN hN hLE D hD hRest) hLog
      (createCellGuardDecodes LE cN hN hLE D hD) s args s' h
  exact (apex_iff_createCellSpec LE cN hN hLE D hD s args s').mp hapex

#assert_axioms createCellGuardLocal
#assert_axioms createCellGuardDecodes
#assert_axioms createCellGuardEncodes
#assert_axioms apex_iff_createCellSpec
#assert_axioms createCellA_full_sound

end Dregg2.Circuit.Inst.CreateCellA