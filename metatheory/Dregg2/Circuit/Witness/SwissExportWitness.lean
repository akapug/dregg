/-
# Dregg2.Circuit.Witness.SwissExportWitness — the v2 WITNESS GENERATOR for `swissExportA`.

Closes the verifiable-execution beachhead for `exportSturdyRefA` (mint a CapTP sturdy ref: insert a
fresh `SwissRecord` into the swiss-table), over the v2 framework (`EffectCommit2`), touched component
`kernel.swiss` (a `listComponent` — FULL list equality, so a drop/reorder of an existing sturdy ref is
REJECTED). Reused: `Exec.swissExportChainA`, `Inst.SwissExportA.swissExportA_full_sound` (⇒
`ExportSpec`), `effect2_circuit_full_complete`, `emittedEffect2`/`emitDescriptorJson`.

§3 abstract execute→prove + verify→accept; §4 the concrete `swissExportWitnessVec` running the real
executor; §5 the descriptor + witness JSON. The anti-ghost forgery: the post swiss-list inserts the
record with a FORGED `refcount` (2 not the spec's 1 — a double-counted ref) — the component-bind gate
68≠69 = a real UNSAT.

CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.swissExportA

namespace Dregg2.Circuit.Witness.SwissExportWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.SwissExportA
open Dregg2.Circuit.Spec.SwissExport
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Auth)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoSwiss S.RH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (hspec : ExportSpec s args.sw args.actor args.exporter args.target args.rights s') :
    satisfiedE2 S (swissExportE LE cN hN hLE) (encodeE2 S (swissExportE LE cN hN hLE) s args s') :=
  effect2_circuit_full_complete S (swissExportE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (exportGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_exportSpec LE cN hN hLE s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissExportE LE cN hN hLE) (encodeE2 S (swissExportE LE cN hN hLE) s args s')) :
    ExportSpec s args.sw args.actor args.exporter args.target args.rights s' :=
  swissExportA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Concrete computable per-`Auth` code. -/
def authCode : Auth → ℤ
  | .read => 1 | .write => 2 | .grant => 3 | .call => 4 | .reply => 5 | .reset => 6 | .control => 7

/-- Concrete computable per-`SwissRecord` leaf code (all six fields folded, mod a small prime). -/
def swissCode (r : SwissRecord) : ℤ :=
  ((r.swiss : ℤ) * 101 + (r.exporter : ℤ) * 103 + (r.target : ℤ) * 107
    + r.rights.foldl (fun acc a => (acc * 11 + authCode a) % 2000003) 1 * 109
    + (r.refcount : ℤ) * 113 + (match r.cert with | none => 0 | some h => (h : ℤ) + 1) * 127) % 2000003

/-- Concrete computable swiss-list digest: a small modular Horner fold (length-tagged), so a
drop/reorder/tamper of any entry shows up. -/
def swissDigConcrete : List SwissRecord → ℤ :=
  fun rs => rs.foldl (fun acc r => (acc * 7919 + swissCode r) % 2000003) ((rs.length : ℤ) + 1)

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.caps 0).length * 17

def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `swiss` component (computable digest), spec-expected being the export prepend. -/
def swissCompC : ActiveComponent RecChainedState ExportArgs :=
  { digest    := fun k => swissDigConcrete k.swiss
  , expected  := fun s args =>
      swissDigConcrete (exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)
  , postClause := fun s args post =>
      swissDigConcrete post.swiss
        = swissDigConcrete (exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def swissExportEC : EffectSpec2 RecChainedState ExportArgs :=
  { view         := chainView
  , active       := swissCompC
  , logUpdate    := some (fun s args => exportReceipt args.actor args.exporter :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := exportGuardGates
  , guardProp    := exportGuardProp
  , guardWidth   := 1
  , guardEncode  := exportGuardEncode
  , guardLocal   := exportGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: actor 0 self-exports sw 7 → target 1 (empty rights, empty swiss). -/

def kPre : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => default, caps := fun _ => [], swiss := [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The export args: actor 0 = exporter 0 (self-authority) exports sw 7 → target 1, no rights. -/
def argsRef : ExportArgs := { sw := 7, actor := 0, exporter := 0, target := 1, rights := [] }

def sPost : RecChainedState :=
  (swissExportChainA sPre argsRef.sw argsRef.actor argsRef.exporter argsRef.target argsRef.rights).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the inserted swiss record carries a FORGED
`refcount := 2` (a double-counted live ref) instead of the spec's `refcount := 1`. The component-bind
gate must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      swiss := { exportRecord argsRef.sw argsRef.exporter argsRef.target argsRef.rights
                  with refcount := 2 } :: kPre.swiss } }

def witnessOf (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState) : List Int :=
  (List.range (swissExportEC.traceWidth)).map (fun w => encodeE2 SC swissExportEC s args s' w)

def swissExportWitnessVec (s : RecChainedState) (args : ExportArgs) : List Int :=
  match swissExportChainA s args.sw args.actor args.exporter args.target args.rights with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem swissExportWitnessVec_commit {s s' : RecChainedState} {args : ExportArgs}
    (h : swissExportChainA s args.sw args.actor args.exporter args.target args.rights = some s') :
    swissExportWitnessVec s args = witnessOf s args s' := by
  unfold swissExportWitnessVec; rw [h]

def honestWitness : List Int := swissExportWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72
#guard decide (satisfied (effectCircuit2 swissExportEC) (encodeE2 SC swissExportEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 swissExportEC) (encodeE2 SC swissExportEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def swissExportAirName : String := "dregg-swissExportA-v2"
def emittedSwissExport : EmittedDescriptor := emittedEffect2 swissExportAirName swissExportEC
def descriptorJson : String := emitDescriptorJson emittedSwissExport
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedSwissExport.constraints.length == 4
#guard emittedSwissExport.traceWidth == 72
#guard descriptorJson ==
  "{\"name\":\"dregg-swissExportA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitness.getD 68 0 == 16874   -- component digest binds (honest export, refcount 1)
#guard forgedWitness.getD 68 0 == 16987    -- forged component digest differs (refcount 2)
#guard forgedWitness.getD 69 0 == 16874    -- expected stays the spec prepend
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,17139,2,2,16874,16874,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,17252,2,2,16987,16874,263,263]"

#assert_axioms swissExportWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SwissExportWitness
