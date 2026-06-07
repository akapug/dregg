/-
# Dregg2.Circuit.Witness.attenuateAWitness — `execute → satisfying assignment` for `attenuateA` (the
TOTAL authority self-narrowing; v2 family, touched component = `caps`, a `funcComponent`).

The caps-function analog of `burnAWitness`: `attenuateWitnessVec` RUNS the REAL executor
`attenuateStepA` (the arm `execFullA` dispatches `.attenuateA` to — a TOTAL `some …` arm, always
commits) and lays the satisfying 72-wire `encodeE2` assignment out as a flat `List Int` over the
concrete commitment surface (the touched-component digest is now an injective digest over the cap table
`caps : Label → List Cap`, sampled at a probe label set). The honest witness satisfies `effectCircuit2`;
a forged post-state whose `caps` table is TAMPERED (a bystander label given an EXTRA `node` cap — a
privilege escalation the attenuation never authorized) is REJECTED by the component-bind gate `68 ≠ 69`.
`Inst.attenuateA.attenuateA_full_sound` proved the crown jewel (`⇒ AttenuateSpec`).
-/
import Dregg2.Circuit.Inst.attenuateA

namespace Dregg2.Circuit.Witness.AttenuateAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.AttenuateA
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (caps-function variant). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := fun l => (l.length : ℤ)

/-- Concrete injective Cap leaf: tag-encode `null`/`node`/`endpoint` (each shifted by a base larger than
any toy target/rights count). A tampered cap is VISIBLE. -/
def capLeaf : Cap → ℤ
  | .null            => 0
  | .node t          => 100 + (t : ℤ)
  | .endpoint t r    => 5000 + (t : ℤ) * 10 + (r.length : ℤ)

/-- Concrete injective slot encoder: a positional Horner fold over a label's cap list. (Small bases keep
the outer digest within `i64` for the toy `#guard`/Rust domain — short cap lists, small targets.) -/
def slotEnc (cs : List Cap) : ℤ := cs.foldl (fun acc c => acc * 10000 + capLeaf c) (cs.length : ℤ)

/-- The probe labels the concrete `caps` digest samples: the acting label `actor`, plus a bystander
label `1` (so a privilege escalation to a third holder shows up). -/
def capsProbes (actor : CellId) : List CellId := [actor, 1]

/-- Concrete `caps` function digest: an injective positional Horner fold over the probe labels' slots. -/
def capsDigestC (actor : CellId) (caps : Caps) : ℤ :=
  (capsProbes actor).foldl (fun acc l => acc * 100000000 + slotEnc (caps l)) 0

def attenuateSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete `ActiveComponent` + the concrete `attenuateEC`. -/

def capsComponentC (actor : CellId) : ActiveComponent RecChainedState AttenuateArgs where
  digest    := fun k => capsDigestC actor k.caps
  expected  := fun s args => capsDigestC actor (attenuateSlotF s.kernel.caps args.actor args.idx args.keep)
  postClause := fun s args post =>
    capsDigestC actor post.caps = capsDigestC actor (attenuateSlotF s.kernel.caps args.actor args.idx args.keep)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def attenuateEC (actor : CellId) : EffectSpec2 RecChainedState AttenuateArgs where
  view         := chainView
  active       := capsComponentC actor
  logUpdate    := some (fun s args => authReceipt args.actor :: s.log)
  restFrame    := fun k k' => True
  guardGates   := attenuateGuardGates
  guardProp    := attenuateGuardProp
  guardWidth   := 1
  guardEncode  := attenuateGuardEncode
  guardLocal   := attenuateGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (actor : CellId) (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState) :
    List Int :=
  (List.range (attenuateEC actor).traceWidth).map
    (fun v => encodeE2 attenuateSurfaceC (attenuateEC actor) s args s' v)

/-- **`attenuateWitnessVec s args`** — runs the TOTAL `attenuateStepA` and lays out the witness. -/
def attenuateWitnessVec (s : RecChainedState) (args : AttenuateArgs) : List Int :=
  witnessOf args.actor s args (attenuateStepA s args.actor args.idx args.keep)

theorem attenuateWitnessVec_commit (s : RecChainedState) (args : AttenuateArgs) :
    attenuateWitnessVec s args = witnessOf args.actor s args (attenuateStepA s args.actor args.idx args.keep) :=
  rfl

theorem witnessOf_get (actor : CellId) (s : RecChainedState) (args : AttenuateArgs)
    (s' : RecChainedState) (v : Nat) (hv : v < (attenuateEC actor).traceWidth) :
    (witnessOf actor s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2 attenuateSurfaceC (attenuateEC actor) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A pre-state where label 0 holds `[node 5, node 9]` (idx 1 = `node 9`); a bystander label 1 holds `[]`.
`attenuateA` narrows label 0's idx-1 cap to `keep = [read]`; the bystander's slot must stay empty. -/

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => default
        caps := fun x => if x = 0 then [Cap.node 5, Cap.node 9] else [] }
    log := [] }

/-- Narrow label 0's idx-1 cap to `[read]`. -/
def goodArgsC : AttenuateArgs := { actor := 0, idx := 1, keep := [Auth.read] }

def goodPostC : RecChainedState := attenuateStepA sC0 0 1 [Auth.read]

/-- THE FORGERY: the honest narrowing of label 0, BUT bystander label 1 ALSO gains a stolen `node 9`
cap — a privilege escalation the attenuation never authorized. The frame/log stay honest, so a
projection circuit would have passed it; the caps component digest differs. -/
def forgedCapsC : Caps :=
  fun x => if x = 0 then goodPostC.kernel.caps 0
           else if x = 1 then [Cap.node 9]   -- STOLEN cap on bystander
           else goodPostC.kernel.caps x

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with caps := forgedCapsC }, log := goodPostC.log }

def honestWitness : List Int := attenuateWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfied (effectCircuit2 (attenuateEC 0))
  (encodeE2 attenuateSurfaceC (attenuateEC 0) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfied (effectCircuit2 (attenuateEC 0))
  (encodeE2 attenuateSurfaceC (attenuateEC 0) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def attenuateHonestWitnessJson : String := witnessJson honestWitness
def attenuateForgedWitnessJson : String := witnessJson forgedWitness

-- The EXACT bytes the Rust `lean_executor_derived_attenuate_a` test pastes (goldens).
#guard attenuateHonestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20105010900000002,20105010900000003,2,2,20105010900000000,20105010900000000,1,1]"
#guard attenuateForgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20105010900000002,20105010900010112,2,2,20105010900010109,20105010900000000,1,1]"

#assert_axioms attenuateWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.AttenuateAWitness
