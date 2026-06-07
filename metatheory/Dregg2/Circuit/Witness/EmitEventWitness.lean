/-
# Dregg2.Circuit.Witness.EmitEventWitness — execute→prove→verify→anti-ghost for `emitEventA`.

This amplifies the `Transfer` verifiable-execution beachhead (`Dregg2.Circuit.TransferWitness`) to the
log-only effect `emitEventA`, through the GENERIC v1 framework (`EffectCommit`). The pieces already
proved and REUSED (not re-proved):

  * `Exec.execFullA` — the REAL chained executor. `execFullA s (.emitEventA actor cell topic data) =
    some s'` IS the executor computing the post-state.
  * `Spec.CellStateLog.execFullA_emitEvent_iff_spec` — executor ⟺ `EmitEventSpec` (both directions).
  * `Inst.EmitEventA.{emitEventE, apex_iff_emitEventSpec, emitEventA_full_sound}` — the v1 instance +
    the crown-jewel `satisfying witness ⇒ EmitEventSpec`.
  * `EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}` — the generic full-state circuit.

THE PIECES THIS MODULE SUPPLIES (the `TransferWitness` pattern, per effect):

  (1) `emitEventWitnessVec : RecChainedState → EmitEventArgs → List Int` — the executor-driven witness
      generator: it RUNS `execFullA` and lays out the full-state witness (digest columns filled by the
      concrete surface `Witness.Common.SConc`) via `layoutE`. On a fail-closed turn it falls back to
      the pre-state (yielding a guard-failing vector, as it should).
  (2) `execute_produces_satisfying_witness` — a committed `execFullA` step makes the full-state witness
      SATISFY the circuit (reuses `effect_circuit_full_complete` ∘ the apex bridge ∘ the executor⟺spec).
  (3) `satisfying_witness_proves_full_state` — any satisfying witness proves the full `EmitEventSpec`
      (reuses `emitEventA_full_sound`).
  (4) the concrete `#guard`s: the EXECUTOR-DERIVED honest witness SATISFIES; a REAL forged post-state
      (a tampered receipt row, and a minted bystander cell) yields a vector the circuit REJECTS — a
      real UNSAT (the log-bind / frame-reuse gate, the anti-ghost tooth end-to-end).
  (5) the JSON the Rust `lean_executor_derived_emitEvent` prover proves+verifies (honest) / rejects.
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Spec.cellstatelog

namespace Dregg2.Circuit.Witness.EmitEventWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.EmitEventA
open Dregg2.Circuit.Spec.CellStateLog
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR: `execute → satisfying assignment`. -/

/-- **`emitEventWitnessVec s args`** — the executor-driven witness generator. Runs
`execFullA s (.emitEventA …)`; on commit lays out the full-state witness for the executor's post-state,
every digest column filled by the concrete commitment surface; on a fail-closed turn falls back to the
pre-state (a guard-failing vector). THIS is `execute → the satisfying assignment for the real
per-effect circuit`, materialized for the Rust prover. -/
def emitEventWitnessVec (s : RecChainedState) (args : EmitEventArgs) : List Int :=
  match execFullA s (.emitEventA args.actor args.cell args.topic args.data) with
  | some s' => layoutE emitEventE s args s'
  | none    => layoutE emitEventE s args s

/-- **`emitEventWitnessVec` IS `layoutE` of the EXECUTOR's post-state** (the some-branch unfold). -/
theorem emitEventWitnessVec_commit {s s' : RecChainedState} {args : EmitEventArgs}
    (h : execFullA s (.emitEventA args.actor args.cell args.topic args.data) = some s') :
    emitEventWitnessVec s args = layoutE emitEventE s args s' := by
  unfold emitEventWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE THEOREM (abstract surface, CR portals carried). -/

/-- **`execute_produces_satisfying_witness` — the execute→prove direction.** A committed `execFullA`
emit step makes the full-state witness `encodeE … s args s'` SATISFY the full-state circuit. Reuses
`effect_circuit_full_complete` via `apex_iff_emitEventSpec` ∘ `execFullA_emitEvent_iff_spec`. -/
theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : EmitEventArgs}
    (h : execFullA s (.emitEventA args.actor args.cell args.topic args.data) = some s') :
    satisfiedE S emitEventE (encodeE S emitEventE s args s') := by
  have hspec : EmitEventSpec s args.actor args.cell args.topic args.data s' :=
    (execFullA_emitEvent_iff_spec s args.actor args.cell args.topic args.data s').mp h
  have hapex : emitEventE.apex s args s' := (apex_iff_emitEventSpec s args s').mpr hspec
  exact effect_circuit_full_complete S emitEventE hRest emitEventGuardEncodes s args s' hapex

/-- **`satisfying_witness_proves_full_state` — the verify→accept direction (soundness).** ANY witness
satisfying the full-state circuit proves the complete declarative `EmitEventSpec`. Reuses
`emitEventA_full_sound`; carries the standard Poseidon-CR portals + `AccountsWF` on both states. -/
theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S emitEventE (encodeE S emitEventE s args s')) :
    EmitEventSpec s args.actor args.cell args.topic args.data s' :=
  emitEventA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A concrete THREE-cell pre-state {0,1,2} (balances 100/5/50), empty log; actor 0 emits on cell 0. We
RUN the executor and materialize the witness. The forgeries are REAL post-states: (F1) a tampered
receipt row (actor 9 instead of 0) — the log-bind gate (72/73) rejects; (F2) a minted bystander cell 2
(50 → 999) — the frame-reuse gate (68/69) rejects. -/

/-- Concrete 3-cell kernel (balances 100/5/50). -/
def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

/-- Concrete pre-state: the 3-cell kernel with an empty log. -/
def s0 : RecChainedState := { kernel := kCells, log := [] }

/-- The good args: actor 0 emits topic 7 / data 9 on cell 0 (live). -/
def goodArgs : EmitEventArgs := { actor := 0, cell := 0, topic := 7, data := 9 }

/-- The honest executor post-state (= `emitStep s0 0 0 7 9`). -/
def goodPost : RecChainedState := emitStep s0 goodArgs.actor goodArgs.cell goodArgs.topic goodArgs.data

/-- THE LOG FORGERY: the SAME kernel but a forged receipt row (actor 9, not 0). The log-bind gate
(`logDigPost = logDigExpected`, wires 72/73) must reject it. -/
def forgedLog : RecChainedState :=
  { kernel := kCells, log := { actor := 9, src := 0, dst := 0, amt := 0 } :: s0.log }

/-- THE THIRD-CELL FORGERY: the honest receipt but a MINTED bystander cell 2 (50 → 999). The
frame-reuse gate (`frameDigPre = frameDigPost`, wires 68/69) must reject it. -/
def forgedCell : RecChainedState :=
  { kernel := { kCells with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else kCells.cell c }
    log := goodPost.log }

/-- The honest executor-derived witness vector. -/
def honestWitness : List Int := emitEventWitnessVec s0 goodArgs
/-- The log-forged witness vector. -/
def forgedLogWitness : List Int := layoutE emitEventE s0 goodArgs forgedLog
/-- The third-cell-forged witness vector. -/
def forgedCellWitness : List Int := layoutE emitEventE s0 goodArgs forgedCell

-- (1) the witnesses have the framework trace width.
#guard honestWitness.length == 74
#guard forgedLogWitness.length == 74
#guard forgedCellWitness.length == 74

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state circuit.
#guard decide (satisfied (effectCircuit emitEventE) (fun v => honestWitness.getD v 0))

-- (3) THE ANTI-GHOST TEETH (real UNSAT): both forged post-states FAIL the circuit.
#guard decide (satisfied (effectCircuit emitEventE) (fun v => forgedLogWitness.getD v 0)) == false
#guard decide (satisfied (effectCircuit emitEventE) (fun v => forgedCellWitness.getD v 0)) == false
-- ...and SPECIFICALLY: the log forgery breaks the log-bind gate (72 ≠ 73), the cell forgery the
--    frame-reuse gate (68 ≠ 69) — the exact anti-ghost wires.
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0          -- log: post = expected
#guard !(forgedLogWitness.getD 72 0 == forgedLogWitness.getD 73 0) -- log forgery: REJECTED here
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0          -- frame: pre = post
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0) -- cell forgery: REJECTED here

/-! ## §4 — JSON export (the bytes the Rust prover consumes). -/

/-- The honest executor-derived witness, as the JSON array the Rust prover proves+verifies. -/
def honestWitnessJson : String := witnessJson honestWitness
/-- The log-forged witness, as the JSON array the Rust prover REJECTS (log-bind UNSAT). -/
def forgedLogWitnessJson : String := witnessJson forgedLogWitness
/-- The third-cell-forged witness, as the JSON array the Rust prover REJECTS (frame-reuse UNSAT). -/
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

-- The exact bytes the Rust `lean_executor_derived_emitEvent` test pastes (goldens pin them so an
-- executor/surface drift is caught here first).
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3000100000005000050,3000100000005000050,0,0,1000000,1000000]"
#guard forgedLogWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3000100000005000050,3000100000005000050,0,0,1009000,1000000]"
#guard forgedCellWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3000100000005000050,3000100000005000999,0,0,1000000,1000000]"

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms emitEventWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.EmitEventWitness
