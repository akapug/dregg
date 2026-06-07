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
import Dregg2.Circuit.Poseidon2Surface

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
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest encOptNat turnLogDigest)

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

/-- **Field-binding** `SwissRecord` encoder: ALL six fields (`swiss, exporter, target`, the WHOLE
`rights` list, `refcount`, `cert`). The OLD `swissCode … % 2000003` was a NON-injective field hash that
folded `rights` through ANOTHER `% 2000003` reduction (dropping WHICH rights a bearer obtains). -/
def encSwiss (r : SwissRecord) : List ℤ :=
  (r.swiss : ℤ) :: (r.exporter : ℤ) :: (r.target : ℤ) :: (r.rights.length : ℤ) ::
    (r.rights.map authCode ++ ((r.refcount : ℤ) :: encOptNat r.cert))

/-- The swiss-table list digest: the REAL `refP2` sponge over the field-binding `encSwiss`. -/
def swissDigConcrete : List SwissRecord → ℤ := recListDigest encSwiss

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.caps 0).length * 17

/-- The log hash: the REAL `turnLogDigest` (binds `src`/`dst`/`amt` the OLD `actor % 2000003` fold dropped
and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

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
-- Structural component-bind goldens (the field-binding `refP2`/`encSwiss` digests replace the
-- non-injective `% 2000003` field hash; non-vacuity is at the bind gates; the Rust paste is regenerated
-- from the JSON accessors).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- swiss component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged swiss differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms swissExportWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SwissExportWitness
