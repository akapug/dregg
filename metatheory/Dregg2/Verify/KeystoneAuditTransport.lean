/-
# Dregg2.Verify.KeystoneAuditTransport — the TRANSPORT-from-an-audited-sibling keystone-audit (Wave 3).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over keystones that
are SIBLINGS of an already-audited theorem, transporting the audited sibling's witness SHAPE:

  • NON-AMPLIFYING family (siblings of `EffectsAuthority.{introduce,attenuate}_non_amplifying`):
    `recKDelegateAtten_non_amplifying`, and the executor-level `execFullA_{introduceA,attenuateA,
    delegateAttenA}_non_amplifying` — each carries the SAME `IsNonAmplifyingF`/`confRights ≤` shape;
  • RECEIPT-BINDING (siblings of the audited Argus receipt weld):
    `writeCell0_receipt_binds_tail` (the lemma `writeCell0_receipt_observable` is BUILT from) reuses the
    SAME receipt companions; `stateCommit_binds_cells_and_rest` (the lemma the audited CROWN
    `stateCommit_binds_cellCommit` is built from) reuses the SAME crossbind companions;
  • MEMORY-PROGRAM (over the codec-free `bal` plane): `moveAsset_is_memory_program` — the per-asset move
    IS its emitted three-op trace, fold-checked on a concrete two-cell/two-asset ledger.

Each is a THEOREM, so the keystone-audit's two checks bite:

  [1] NON-VACUITY — a `*_satisfiable` FIRES the conclusion on a concrete instance (a real held cap
      narrowed to `[read]`; the receipt of `writeCell0 v`; the committed `recCexecAsset` move fold);
  [2] TEETH — a `*_teeth` REFUTES the dual (an amplifying grant rejected; a value-DROPPING leaf; the
      ledger really MOVED — not a vacuous frame).

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate.

STOP-REPORT (mis-classified as cheap → Wave-4 HARD, NOT audited here):
  • `Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree` — its satisfiable needs a concrete
    `interp st k = some k'` step PLUS two crypto-injectivity-conditioned root equalities
    (`hRootPI`/`hSFRootPI`) PLUS two `argusReceipt … = some q` openings, all instantiating the CR
    typeclass parameters; that is a runnable-circuit / stepped-interp witness, not a cheap `def`+`decide`.
  • `Exec.ForestMemoryProgram.{balanceA_step_memprog, eachStepMemProg_of_all_covered,
    forest_of_covered_is_memory_program}` — each non-vacuity witness requires inhabiting `NodeAuthS`
    (the section-parametrized credential carrier over 11 abstract types + `OrderTop`/`SemilatticeInf
    Rights`) and exhibiting a COMMITTED gated `execFullAGated` / `execFullForestG` run (an `AuthPortal`/
    `MacKernel` passing the gate). A gated-forest runnable witness, the Wave-4 class. Deferred.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Exec.AuthTurn
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.ForestMemoryProgram
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Circuit.CommitmentCrossBind

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditTransport

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.ForestMemoryProgram
open Dregg2.Exec.UniversalBridge (uaddr UCodec UOp uproj moveAssetTrace)
open Dregg2.Crypto.MemoryChecking (step)
open Dregg2.Authority (Cap Auth)

/-! ## §1 — the NON-AMPLIFYING family (transport of the `introduce/attenuate` non-amp shape).

The audited siblings (`EffectsAuthority.{introduce,attenuate}_non_amplifying`) carry `heldRW`/`grantAmp`
witnesses. We transport the SAME shape onto the local executable predicate `IsNonAmplifyingF` and the
rights-lattice `confRights ≤`: a real held cap `endpoint 9 [read,write]` narrowed to `[read]` (the
conclusion FIRES), and the amplifying grant `node 9` (confers `control ∉ heldRW`) REFUTED. -/

def heldRW : Cap := Cap.endpoint 9 [Auth.read, Auth.write]
def grantAmp : Cap := Cap.node 9
/-- A `caps` table where `heldCapTo capsRW 0 9` finds `heldRW` (it `confersEdgeTo 9`). -/
def capsRW : Dregg2.Authority.Caps := fun l => if l = 0 then [heldRW] else []

/-- **`recKDelegateAtten_non_amplifying_satisfiable`.** The delegated cap's real authority is `⊆` the
held cap's: `confRights (attenuate [read] (heldCapTo capsRW 0 9)) ≤ confRights (heldCapTo capsRW 0 9)`,
on a concrete `caps` where the delegator (0) genuinely holds `heldRW` toward `9`. -/
theorem recKDelegateAtten_non_amplifying_satisfiable :
    confRights (attenuate [Auth.read] (heldCapTo capsRW 0 9))
      ≤ confRights (heldCapTo capsRW 0 9) :=
  Dregg2.Exec.recKDelegateAtten_non_amplifying capsRW 0 9 [Auth.read]

/-- **`recKDelegateAtten_non_amplifying_teeth`.** A WIDENING is refused: `node 9` confers `control`,
which `heldRW` does not — so `¬ (confRights (node 9) ≤ confRights heldRW)`. The `confRights ≤` is
two-valued, not `:= True`. -/
theorem recKDelegateAtten_non_amplifying_teeth :
    ¬ (confRights grantAmp ≤ confRights heldRW) := by decide

/-- **`introduceA_non_amplifying_satisfiable`.** The introduce copy is reflexively non-amplifying on a
real cap: `IsNonAmplifyingF heldRW heldRW`. -/
theorem introduceA_non_amplifying_satisfiable : IsNonAmplifyingF heldRW heldRW := fun _ ha => ha

/-- **`attenuateA_non_amplifying_satisfiable`.** The narrowed cap confers a genuine SUBSET:
`IsNonAmplifyingF heldRW (attenuate [read] heldRW)`. -/
theorem attenuateA_non_amplifying_satisfiable :
    IsNonAmplifyingF heldRW (attenuate [Auth.read] heldRW) :=
  attenuateF_non_amplifying [Auth.read] heldRW

/-- **`nonamp_teeth`.** The shared discriminating instance: an amplifying grant (`node 9`, confers
`control ∉ heldRW`) is REFUTED — `¬ IsNonAmplifyingF heldRW grantAmp`. -/
theorem nonamp_teeth : ¬ IsNonAmplifyingF heldRW grantAmp :=
  amplifyingF_rejected heldRW grantAmp Auth.control (by decide) (by decide)

/-! ## §2 — the MEMORY-PROGRAM move keystone (`moveAsset_is_memory_program`).

A concrete little kernel (two live accounts, two assets, an authority cap); the per-asset move
`recCexecAsset smv0 tmv 0` COMMITS and IS exactly its emitted three-op trace fold. -/

def Cmv : UCodec :=
  { val := fun v => match v with | .int i => i | _ => 0
  , cap := fun _ => 0, caveat := fun _ => 0, factory := fun _ => 0
  , receipt := fun t => (t.actor : ℤ) + 2 * t.src + 3 * t.dst + 5 * t.amt }
def kmv : RecordKernelState :=
  { accounts := {1, 2}
  , cell := fun _ => .record []
  , caps := fun l => if l = 1 then [Cap.node 2] else []
  , bal := fun c a => if a = 0 then (if c = 1 then 10 else if c = 2 then 3 else 0)
                      else (if c = 1 then 7 else 0) }
def smv0 : RecChainedState := { kernel := kmv, log := [] }
def tmv : Turn := { actor := 1, src := 1, dst := 2, amt := 4 }
def smv1 : RecChainedState := (recCexecAsset smv0 tmv 0).getD smv0

/-- **`moveAsset_is_memory_program_satisfiable`.** The move COMMITS and fires the fold equation:
`uproj Cmv s' = (moveAssetTrace Cmv smv0 tmv 0).foldl step (uproj Cmv smv0)` on the committed `s'`. -/
theorem moveAsset_is_memory_program_satisfiable :
    ∃ s', recCexecAsset smv0 tmv 0 = some s'
      ∧ uproj Cmv s' = (moveAssetTrace Cmv smv0 tmv 0).foldl step (uproj Cmv smv0) := by
  have hsome : (recCexecAsset smv0 tmv 0).isSome = true := by decide
  obtain ⟨s', h⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨s', h, moveAsset_is_memory_program Cmv h⟩

/-- **`moveAsset_is_memory_program_teeth`.** The ledger REALLY MOVED: the post-projection at the
debited cell/asset differs from the pre-projection (`10 → 6` at `(1,0)`), so the memory-program
equation binds a NON-constant trace — it is not a vacuous frame agreement. -/
theorem moveAsset_is_memory_program_teeth :
    ¬ (uproj Cmv smv1 (uaddr (.balA 1 0)) = uproj Cmv smv0 (uaddr (.balA 1 0))) := by decide

/-! ## §3 — TAG the 7 transported keystones with their companions (re-pinning aliases).

The RECEIPT-BINDING pair reuse the EXISTING audited companions:
  • `writeCell0_receipt_binds_tail` ← `writeCell0_receipt_eq` (satisfiable) / `writeCell0_receipt_observable`
    (teeth) — the SAME pair the audited `argus_commits_to_one_receipt` uses (and `_observable` is BUILT
    from `_binds_tail`, so it discriminates precisely this keystone);
  • `stateCommit_binds_cells_and_rest` ← `chC_is_cellCommit` (satisfiable) / `chC_bad_not_bridge` (teeth)
    — the SAME pair the audited CROWN `stateCommit_binds_cellCommit` (built FROM this lemma) uses. -/

-- non-amplifying family:
@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTransport.recKDelegateAtten_non_amplifying_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTransport.recKDelegateAtten_non_amplifying_teeth]
def recKDelegateAtten_non_amplifying_KS := @Dregg2.Exec.recKDelegateAtten_non_amplifying

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTransport.introduceA_non_amplifying_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTransport.nonamp_teeth]
def execFullA_introduceA_non_amplifying_KS :=
  @Dregg2.Exec.TurnExecutorFull.execFullA_introduceA_non_amplifying

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTransport.attenuateA_non_amplifying_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTransport.nonamp_teeth]
def execFullA_attenuateA_non_amplifying_KS :=
  @Dregg2.Exec.TurnExecutorFull.execFullA_attenuateA_non_amplifying

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTransport.attenuateA_non_amplifying_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTransport.nonamp_teeth]
def execFullA_delegateAttenA_non_amplifying_KS :=
  @Dregg2.Exec.TurnExecutorFull.execFullA_delegateAttenA_non_amplifying

-- receipt-binding (reuse the audited siblings' companions):
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_eq
    teeth := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_observable]
def writeCell0_receipt_binds_tail_KS :=
  @Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_binds_tail

@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.CommitmentCrossBind.chC_is_cellCommit
    teeth := Dregg2.Circuit.CommitmentCrossBind.chC_bad_not_bridge]
def stateCommit_binds_cells_and_rest_KS :=
  @Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cells_and_rest

-- memory-program move:
@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTransport.moveAsset_is_memory_program_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTransport.moveAsset_is_memory_program_teeth]
def moveAsset_is_memory_program_KS :=
  @Dregg2.Exec.ForestMemoryProgram.moveAsset_is_memory_program

/-! ## §4 — RUN the audit (the CI gate over the transported family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditTransport.recKDelegateAtten_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTransport.execFullA_introduceA_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTransport.execFullA_attenuateA_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTransport.execFullA_delegateAttenA_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTransport.writeCell0_receipt_binds_tail_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTransport.stateCommit_binds_cells_and_rest_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTransport.moveAsset_is_memory_program_KS

#keystone_audit_tagged

/-! ## §5 — axiom-hygiene over the witnesses + re-pinned aliases (kernel-triple clean). -/

#assert_axioms recKDelegateAtten_non_amplifying_satisfiable
#assert_axioms introduceA_non_amplifying_satisfiable
#assert_axioms attenuateA_non_amplifying_satisfiable
#assert_axioms nonamp_teeth
#assert_axioms moveAsset_is_memory_program_satisfiable
#assert_axioms moveAsset_is_memory_program_teeth
#assert_axioms recKDelegateAtten_non_amplifying_KS
#assert_axioms writeCell0_receipt_binds_tail_KS
#assert_axioms stateCommit_binds_cells_and_rest_KS
#assert_axioms moveAsset_is_memory_program_KS

end Dregg2.Verify.KeystoneAuditTransport
