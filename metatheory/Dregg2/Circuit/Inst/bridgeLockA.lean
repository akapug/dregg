/-
# Dregg2.Circuit.Inst.bridgeLockA — the v2-dual (`EffectCommit2Dual`) VALIDATION for `bridgeLockA`.

`bridgeLockA` is the canonical dual-component bridge-outbound-lock effect: it DEBITS the per-asset
ledger `bal` at `(originator, asset)` by `amount` AND PREPENDS an unresolved bridge-tagged
`EscrowRecord` onto `escrows`, advances the log by `escrowReceiptA actor ::`, and freezes the other
15 kernel fields. This is Gate 1's validator: `bridgeLockA_full_sound ⇒ BridgeOutboundLockSpec`
THROUGH the generic dual-component framework.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/bridgeoutboundlock`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.Spec.bridgeoutboundlock

namespace Dregg2.Circuit.Inst.BridgeLockA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.BridgeOutboundLock
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `bridgeLockE` dual instance (`bal` + `escrows`). -/

structure BridgeLockArgs where
  id            : Nat
  actor         : CellId
  originator    : CellId
  destination   : CellId
  asset         : AssetId
  amount        : ℤ

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def bridgeLockGuardProp (s : RecChainedState) (args : BridgeLockArgs) : Prop :=
  lockGuard s.kernel args.id args.actor args.originator args.destination args.asset args.amount

instance (s : RecChainedState) (args : BridgeLockArgs) : Decidable (bridgeLockGuardProp s args) := by
  unfold bridgeLockGuardProp lockGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def bridgeLockGuardEncode (s : RecChainedState) (args : BridgeLockArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (bridgeLockGuardProp s args) else 0

def bridgeLockGuardGates : ConstraintSystem := [cBitGuard]

theorem bridgeLockGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied bridgeLockGuardGates a ↔ satisfied bridgeLockGuardGates b := by
  unfold satisfied bridgeLockGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState BridgeLockArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recBalCreditCell s.kernel.bal args.originator args.asset (-args.amount))

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState BridgeLockArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => parkedBridgeRecord args.id args.originator args.destination args.asset args.amount
      :: s.kernel.escrows)

def bridgeLockE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2Dual RecChainedState BridgeLockArgs where
  view         := chainView
  active1      := balComponent D hD
  active2      := escrowsComponent LE cN hN hLE
  logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats
      ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := bridgeLockGuardGates
  guardProp    := bridgeLockGuardProp
  guardWidth   := 1
  guardEncode  := bridgeLockGuardEncode
  guardLocal   := bridgeLockGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem bridgeLockGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2Dual (bridgeLockE D hD LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied bridgeLockGuardGates (bridgeLockGuardEncode s args s') at hsat
  show bridgeLockGuardProp s args
  have hg := hsat cBitGuard (by simp [bridgeLockGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeLockGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem bridgeLockGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2Dual (bridgeLockE D hD LE cN hN hLE) := by
  intro s args s' hg
  show satisfied bridgeLockGuardGates (bridgeLockGuardEncode s args s')
  intro c hc
  simp only [bridgeLockGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeLockGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem bridgeLockRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameDecodes2Dual S (bridgeLockE D hD LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `BridgeOutboundLockSpec` (direct identity). -/

theorem apex_iff_bridgeOutboundLockSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState) :
    (bridgeLockE D hD LE cN hN hLE).apex s args s' ↔
      BridgeOutboundLockSpec s args.id args.actor args.originator args.destination args.asset
        args.amount s' := by
  show (bridgeLockGuardProp s args
        ∧ s'.kernel.bal = recBalCreditCell s.kernel.bal args.originator args.asset (-args.amount)
        ∧ s'.kernel.escrows = parkedBridgeRecord args.id args.originator args.destination args.asset
            args.amount :: s.kernel.escrows
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((bridgeLockE D hD LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ BridgeOutboundLockSpec s args.id args.actor args.originator args.destination args.asset
            args.amount s'
  unfold BridgeOutboundLockSpec bridgeLockGuardProp bridgeLockE parkedBridgeRecord
  constructor
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `bridgeLockA_full_sound ⇒ BridgeOutboundLockSpec`. -/

/-- **`bridgeLockA_full_sound` — Gate 1 VALIDATION.** A satisfying dual-component full-state witness
for `bridgeLockE` proves the complete declarative `BridgeOutboundLockSpec`. Portals:
`RestIffNoBalEscrows RH`, `logHashInjective LH`, `Function.Injective D` (bal whole-function digest),
`compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem bridgeLockA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (bridgeLockE D hD LE cN hN hLE)
        (encodeE2Dual S (bridgeLockE D hD LE cN hN hLE) s args s')) :
    BridgeOutboundLockSpec s args.id args.actor args.originator args.destination args.asset
      args.amount s' := by
  have hapex : (bridgeLockE D hD LE cN hN hLE).apex s args s' :=
    effect2dual_circuit_full_sound S (bridgeLockE D hD LE cN hN hLE)
      (bridgeLockRestFrameDecodes S D hD LE cN hN hLE hRest) hLog
      (bridgeLockGuardDecodes D hD LE cN hN hLE) s args s' h
  exact (apex_iff_bridgeOutboundLockSpec D hD LE cN hN hLE s args s').mp hapex

#assert_axioms bridgeLockGuardLocal
#assert_axioms bridgeLockGuardDecodes
#assert_axioms bridgeLockGuardEncodes
#assert_axioms apex_iff_bridgeOutboundLockSpec
#assert_axioms bridgeLockA_full_sound

end Dregg2.Circuit.Inst.BridgeLockA