/-
# Dregg2.Circuit.Witness.cellDestroyAWitness — `execute → satisfying assignment` for `cellDestroyA` (the
non-terminal → Destroyed lifecycle effect; v2-DUAL family, touched components = `lifecycle` AND
`deathCert`, both `funcComponent`s).

The DUAL-component analog of `attenuateAWitness`: `cellDestroyWitnessVec` RUNS the REAL executor
`cellDestroyChainA` (the arm `execFullA` dispatches `.cellDestroyA` to) and lays the satisfying 74-wire
`encodeE2Dual` assignment out as a flat `List Int` over the concrete commitment surface. The dual circuit
has FIVE gates: guard (`var 0 = 1`), rest (`66=67`), component-1 `lifecycle` (`68=69`), component-2
`deathCert` (`70=71`), log (`72=73`). The honest witness satisfies `effectCircuit2Dual`; a forged
post-state that ALSO destroys a BYSTANDER cell (lifecycle-component tamper) is REJECTED by the
component-1 bind gate `68 ≠ 69`. `Inst.cellDestroyA.cellDestroyA_full_sound` proved the crown jewel
(`⇒ CellDestroySpec`).
-/
import Dregg2.Circuit.Inst.cellDestroyA

namespace Dregg2.Circuit.Witness.CellDestroyAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Inst.CellDestroyA
open Dregg2.Circuit.Spec.CellLifecycle
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (two `CellId → Nat` function components). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := fun l => (l.length : ℤ)

/-- The probe cells the concrete `CellId → Nat` digests sample: the destroyed `cell`, plus a bystander
cell `1` (so a bystander destroy / cert bind shows up). -/
def natProbes (cell : CellId) : List CellId := [cell, 1]

/-- Concrete injective `CellId → Nat` digest: an injective positional Horner fold over the probe values. -/
def natFnDigestC (cell : CellId) (f : CellId → Nat) : ℤ :=
  (natProbes cell).foldl (fun acc c => acc * 1000000 + (f c : ℤ)) 0

def cellDestroySurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete dual `ActiveComponent`s + the concrete `cellDestroyEC`. -/

def lifecycleComponentC (cell : CellId) : ActiveComponent RecChainedState CellDestroyArgs where
  digest    := fun k => natFnDigestC cell k.lifecycle
  expected  := fun s args => natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).lifecycle
  postClause := fun s args post =>
    natFnDigestC cell post.lifecycle = natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).lifecycle
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def deathCertComponentC (cell : CellId) : ActiveComponent RecChainedState CellDestroyArgs where
  digest    := fun k => natFnDigestC cell k.deathCert
  expected  := fun s args => natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).deathCert
  postClause := fun s args post =>
    natFnDigestC cell post.deathCert = natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).deathCert
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def cellDestroyEC (cell : CellId) : EffectSpec2Dual RecChainedState CellDestroyArgs where
  view         := chainView
  active1      := lifecycleComponentC cell
  active2      := deathCertComponentC cell
  logUpdate    := some (fun s args => cellLifecycleReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' => True
  guardGates   := cellDestroyGuardGates
  guardProp    := cellDestroyGuardProp
  guardWidth   := 1
  guardEncode  := cellDestroyGuardEncode
  guardLocal   := cellDestroyGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (cell : CellId) (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState) :
    List Int :=
  (List.range (cellDestroyEC cell).traceWidth).map
    (fun v => encodeE2Dual cellDestroySurfaceC (cellDestroyEC cell) s args s' v)

def cellDestroyWitnessVec (s : RecChainedState) (args : CellDestroyArgs) : List Int :=
  match cellDestroyChainA s args.actor args.cell args.certHash with
  | some s' => witnessOf args.cell s args s'
  | none    => witnessOf args.cell s args s

theorem cellDestroyWitnessVec_commit {s s' : RecChainedState} {args : CellDestroyArgs}
    (h : cellDestroyChainA s args.actor args.cell args.certHash = some s') :
    cellDestroyWitnessVec s args = witnessOf args.cell s args s' := by
  unfold cellDestroyWitnessVec; rw [h]

theorem witnessOf_get (cell : CellId) (s : RecChainedState) (args : CellDestroyArgs)
    (s' : RecChainedState) (v : Nat) (hv : v < (cellDestroyEC cell).traceWidth) :
    (witnessOf cell s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2Dual cellDestroySurfaceC (cellDestroyEC cell) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A pre-state with cells {0,1} both LIVE (`lifecycle = 0`); actor 0 self-authorized over cell 0
(`stateAuthB` true since `actor = target`). `cellDestroyA` flips cell 0 to Destroyed (3) and binds
`certHash = 77` at cell 0; the bystander cell 1 must stay LIVE. -/

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => default
        caps := fun _ => [] }
    log := [] }

/-- Destroy cell 0 (actor 0), binding death-cert hash 77. -/
def goodArgsC : CellDestroyArgs := { actor := 0, cell := 0, certHash := 77 }

def goodPostC : RecChainedState := (cellDestroyChainA sC0 0 0 77).getD sC0

/-- THE FORGERY: cell 0 honestly destroyed, BUT bystander cell 1 is ALSO destroyed (lifecycle → 3) — a
collateral kill the destroy never authorized. The deathCert/frame/log stay honest, so a projection
circuit would have passed it; the LIFECYCLE component digest differs (component-1 gate `68 = 69`). -/
def forgedLifecycleC : CellId → Nat :=
  fun c => if c = 0 then 3 else if c = 1 then 3 else goodPostC.kernel.lifecycle c

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with lifecycle := forgedLifecycleC }, log := goodPostC.log }

def honestWitness : List Int := cellDestroyWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 74
#guard forgedWitness.length == 74

#guard decide (satisfied (effectCircuit2Dual (cellDestroyEC 0))
  (encodeE2Dual cellDestroySurfaceC (cellDestroyEC 0) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- comp1 lifecycle
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- comp2 deathCert
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log

#guard decide (satisfied (effectCircuit2Dual (cellDestroyEC 0))
  (encodeE2Dual cellDestroySurfaceC (cellDestroyEC 0) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- lifecycle component REJECTED

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def cellDestroyHonestWitnessJson : String := witnessJson honestWitness
def cellDestroyForgedWitnessJson : String := witnessJson forgedWitness

-- The EXACT bytes the Rust `lean_executor_derived_cell_destroy_a` test pastes (goldens).
#guard cellDestroyHonestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,80000003,2,2,3000000,3000000,77000000,77000000,1,1]"
#guard cellDestroyForgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,80000006,2,2,3000003,3000000,77000000,77000000,1,1]"

#assert_axioms cellDestroyWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.CellDestroyAWitness
