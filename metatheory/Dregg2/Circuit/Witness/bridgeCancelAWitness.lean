/-
# Dregg2.Circuit.Witness.bridgeCancelAWitness — `execute → satisfying assignment` for `bridgeCancelA`
(the bridge-OUTBOUND CANCEL / timeout-refund; v2-DUAL family, touched components = `bal` (credit creator
back) AND `escrows` (markResolved)).

The DUAL bal+escrows analog of `bridgeLockAWitness`: `bridgeCancelWitnessVec` RUNS the REAL executor
`bridgeCancelChainA` and lays the satisfying 74-wire `encodeE2Dual` assignment out as a flat `List Int`
over a concrete surface. FIVE gates: guard (`var 0 = 1`), rest (`66=67`), `bal` (`68=69`), `escrows`
(`70=71`), log (`72=73`). The honest witness satisfies `effectCircuit2Dual`; a forged post-state that
ALSO mints a bystander cell's `bal` (component-1 tamper) is REJECTED by the `bal` bind gate `68 ≠ 69`.
`Inst.bridgeCancelA.bridgeCancelA_full_sound` proved the crown jewel (`⇒ BridgeOutboundCancelSpec`).
-/
import Dregg2.Circuit.Inst.bridgeCancelA

namespace Dregg2.Circuit.Witness.BridgeCancelAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Inst.BridgeCancelA
open Dregg2.Circuit.Spec.BridgeOutboundCancel
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (bal probe digest + escrows list digest). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := fun l => (l.length : ℤ)

/-- `bal` probe digest (asset-`asset` column at creator + a bystander cell 2). -/
def balProbes (creator : CellId) (asset : AssetId) : List (CellId × AssetId) :=
  [(creator, asset), (2, asset)]
def balDigestC (creator : CellId) (asset : AssetId) (bal : CellId → AssetId → ℤ) : ℤ :=
  (balProbes creator asset).foldl (fun acc p => acc * 1000000 + bal p.1 p.2) 0

def leConcrete : EscrowRecord → ℤ :=
  fun r => (r.id : ℤ) * 100000 + r.amount * 1000 + (if r.resolved then 1 else 0) * 100 + (r.asset : ℤ)
def cnConcrete : List ℤ → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000000 + x) (xs.length : ℤ)
def escrowsDigestC (escrows : List EscrowRecord) : ℤ := cnConcrete (escrows.map leConcrete)

def bridgeCancelSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete dual `ActiveComponent`s + the concrete `bridgeCancelEC`. -/

def balComponentC (creator : CellId) (asset : AssetId) :
    ActiveComponent RecChainedState BridgeCancelArgs where
  digest    := fun k => balDigestC creator asset k.bal
  expected  := fun s args => balDigestC creator asset (balExpected s args)
  postClause := fun s args post =>
    balDigestC creator asset post.bal = balDigestC creator asset (balExpected s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def escrowsComponentC : ActiveComponent RecChainedState BridgeCancelArgs where
  digest    := fun k => escrowsDigestC k.escrows
  expected  := fun s args => escrowsDigestC (markResolved s.kernel.escrows args.id)
  postClause := fun s args post =>
    escrowsDigestC post.escrows = escrowsDigestC (markResolved s.kernel.escrows args.id)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def bridgeCancelEC (creator : CellId) (asset : AssetId) :
    EffectSpec2Dual RecChainedState BridgeCancelArgs where
  view         := chainView
  active1      := balComponentC creator asset
  active2      := escrowsComponentC
  logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  restFrame    := fun k k' => True
  guardGates   := bridgeCancelGuardGates
  guardProp    := bridgeCancelGuardProp
  guardWidth   := 1
  guardEncode  := bridgeCancelGuardEncode
  guardLocal   := bridgeCancelGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (creator : CellId) (asset : AssetId) (s : RecChainedState) (args : BridgeCancelArgs)
    (s' : RecChainedState) : List Int :=
  (List.range (bridgeCancelEC creator asset).traceWidth).map
    (fun v => encodeE2Dual bridgeCancelSurfaceC (bridgeCancelEC creator asset) s args s' v)

def bridgeCancelWitnessVec (creator : CellId) (asset : AssetId) (s : RecChainedState)
    (args : BridgeCancelArgs) : List Int :=
  match bridgeCancelChainA s args.id args.actor with
  | some s' => witnessOf creator asset s args s'
  | none    => witnessOf creator asset s args s

theorem bridgeCancelWitnessVec_commit {creator : CellId} {asset : AssetId}
    {s s' : RecChainedState} {args : BridgeCancelArgs}
    (h : bridgeCancelChainA s args.id args.actor = some s') :
    bridgeCancelWitnessVec creator asset s args = witnessOf creator asset s args s' := by
  unfold bridgeCancelWitnessVec; rw [h]

theorem witnessOf_get (creator : CellId) (asset : AssetId) (s : RecChainedState)
    (args : BridgeCancelArgs) (s' : RecChainedState) (v : Nat)
    (hv : v < (bridgeCancelEC creator asset).traceWidth) :
    (witnessOf creator asset s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2Dual bridgeCancelSurfaceC (bridgeCancelEC creator asset) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A pre-state with an unresolved BRIDGE escrow record (id 7, creator 0, asset 1, amount 5) plus a
bystander resolved record (id 8). Creator 0 = actor; cell 0 live; bal asset-1 column 95 (the 5 was
locked away). Cancel credits creator 0 back +5 (to 100) and marks id 7 resolved; bystander cell 2 = 50. -/

def recA : EscrowRecord :=
  { id := 7, creator := 0, recipient := 1, amount := 5, resolved := false, asset := 1, bridge := true }
def recB : EscrowRecord :=
  { id := 8, creator := 1, recipient := 1, amount := 9, resolved := true, asset := 1, bridge := true }

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => default
        caps := fun _ => []
        escrows := [recA, recB]
        bal := fun c a => if a = 1 then (if c = 0 then 95 else if c = 1 then 5 else if c = 2 then 50 else 0) else 0 }
    log := [] }

def goodArgsC : BridgeCancelArgs := { id := 7, actor := 0 }

def goodPostC : RecChainedState := (bridgeCancelChainA sC0 7 0).getD sC0

/-- THE FORGERY: creator 0 honestly credited back (100), BUT bystander cell 2's asset-1 balance is ALSO
minted 50 → 999. The escrows/frame/log stay honest, so a projection circuit would have passed it; the
`bal` component digest differs (component-1 gate `68 = 69`). -/
def forgedBalC : CellId → AssetId → ℤ :=
  fun c a => if a = 1 then (if c = 0 then 100 else if c = 1 then 5 else if c = 2 then 999 else 0) else 0

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalC }, log := goodPostC.log }

def honestWitness : List Int := bridgeCancelWitnessVec 0 1 sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 1 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 74
#guard forgedWitness.length == 74

#guard decide (satisfied (effectCircuit2Dual (bridgeCancelEC 0 1))
  (encodeE2Dual bridgeCancelSurfaceC (bridgeCancelEC 0 1) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- comp1 bal
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- comp2 escrows
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log

#guard decide (satisfied (effectCircuit2Dual (bridgeCancelEC 0 1))
  (encodeE2Dual bridgeCancelSurfaceC (bridgeCancelEC 0 1) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- bal component REJECTED

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def bridgeCancelHonestWitnessJson : String := witnessJson honestWitness
def bridgeCancelForgedWitnessJson : String := witnessJson forgedWitness

-- The EXACT bytes the Rust `lean_executor_derived_bridge_cancel_a` test pastes (goldens).
#guard bridgeCancelHonestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2000705001095809154,2000705101100809155,3,3,100000050,100000050,2000705101000809101,2000705101000809101,1,1]"
#guard bridgeCancelForgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2000705001095809154,2000705101100810104,3,3,100000999,100000050,2000705101000809101,2000705101000809101,1,1]"

#assert_axioms bridgeCancelWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.BridgeCancelAWitness
