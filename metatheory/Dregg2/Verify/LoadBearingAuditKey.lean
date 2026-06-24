/-
# Dregg2.Verify.LoadBearingAuditKey — RUN the `@[load_bearing]` linter on the key supply/authority specs.

This module imports the linter (`Dregg2.Verify.LoadBearingLint`) and the audited spec leaves, then
runs `#load_bearing_audit_report` on each of the supply/authority specs codex flagged. It is the
*measurement* deliverable: which specs are genuinely independent + non-vacuous vs gate-copies/vacuous.

The linter is exercised by TWO `@[linter_calibration]` negative-calibration fixtures, each ASSERTED to
FAIL by `#load_bearing_calibration_expect_fail` (which THROWS if a fixture unexpectedly passes — so the
FAILs are asserted-intended, never a silent FAIL count):
  * `gateCopyBurnSpec` — calibrates check #1 (boundary): a "spec" that names the executor step
    `recCBurnAsset`. MUST fail #1.
  * `Dregg2.Spec.execGraph` — calibrates check #2 (defeq): the `execGraph_eq_any := rfl` offender, DEF-EQ
    to the implementation authority-edge gate (`execGraphGate` below = the exact `.any` body the `rfl`
    proof witnesses). MUST fail #2. Its GENUINE counterpart (the independent spec the C-c1 legs attest
    against) is `Spec.authConnects`.
If either fixture does NOT fail, the corresponding linter tooth is broken and the module throws.
-/
import Dregg2.Verify.LoadBearingLint
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.heapwrite
import Dregg2.Exec.AuthTurn

open Dregg2.Verify.LoadBearingLint

namespace Dregg2.Verify.LoadBearingAuditKey

/-! ## §0 — the calibration gate: the implementation authority-edge `.any` body.

`execGraphGate` is, VERBATIM, the implementation body the `execGraph_eq_any := rfl` proof shows
`execGraph` equals — i.e. the executor's per-cell authority-edge test. It plays the role of "the
implementation gate the spec is being validated against". `execGraph` (the would-be spec) is DEF-EQ to
it, so check #2 flags `execGraph` as a gate-copy. -/
def execGraphGate (caps : Dregg2.Authority.Caps) :
    Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights :=
  fun h c =>
    (caps h).any (fun cap =>
      (cap == Dregg2.Authority.Cap.node c.target) ||
      (match cap with
       | .endpoint t rights => (t == c.target) && rights.contains Dregg2.Authority.Auth.write
       | _ => false)) = true

/-! ## §0b — NEGATIVE CALIBRATION for check #1 (the boundary tooth).

`gateCopyBurnSpec` is a deliberately BAD "spec" that calls the executor step `recCBurnAsset` directly
(a `Prop` over the executor's own commit). Check #1 MUST flag it (it references a forbidden step gate).
If the linter PASSES this, check #1 is toothless — this calibrates the boundary check the way
`execGraph` calibrates the defeq check. Tagged `@[linter_calibration]` so an auditor reads it as the
DELIBERATE boundary-violator fixture (the FAIL is intended), not real spec debt. -/
@[linter_calibration]
def gateCopyBurnSpec (s : Dregg2.Exec.RecChainedState)
    (actor cell : Dregg2.Exec.CellId) (a : Dregg2.Exec.AssetId) (amt : ℤ)
    (s' : Dregg2.Exec.RecChainedState) : Prop :=
  Dregg2.Exec.TurnExecutorFull.recCBurnAsset s actor cell a amt = some s'

/-! ## §1 — the measured audits.

Each runs the three checks. `gate :=` pairs the spec to the implementation step/gate it validates (so
check #2 is genuinely exercised, not `n/a`); `nonvacuous :=` names the witness (these specs use
`_rejects_*` rejection teeth as their non-vacuity witnesses, not a `_nonvacuous` decl).
`#load_bearing_audit_report` always prints (so the calibration offenders do not abort the module). -/

-- ── NEGATIVE-CALIBRATION FIXTURE #1 (boundary tooth): a gate-copy spec — ASSERTED to FAIL check #1
-- (references recCBurnAsset). `#load_bearing_calibration_expect_fail` THROWS if it unexpectedly passes,
-- so this FAIL is asserted-intended, not a silent entry in the FAIL count.
#load_bearing_calibration_expect_fail Dregg2.Verify.LoadBearingAuditKey.gateCopyBurnSpec
  gate := Dregg2.Exec.TurnExecutorFull.recCBurnAsset
  nonvacuous := Dregg2.Circuit.Spec.SupplyDestruction.burnA_rejects_destroyed_issuer

-- ── SUPPLY-DESTRUCTION: BurnGuard / BurnSpec (gate = recCBurnAsset / recKBurnAsset) ──────────────
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyDestruction.BurnGuard
  gate := Dregg2.Exec.TurnExecutorFull.recKBurnAsset
  nonvacuous := Dregg2.Circuit.Spec.SupplyDestruction.burnA_rejects_destroyed_issuer
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyDestruction.BurnSpec
  gate := Dregg2.Exec.TurnExecutorFull.recCBurnAsset
  nonvacuous := Dregg2.Circuit.Spec.SupplyDestruction.burnA_rejects_destroyed_issuer

-- ── SUPPLY-CREATION: mintAdmit / MintASpec (gate = recKMintAsset / recCMintAsset) ───────────────
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyCreation.mintAdmit
  gate := Dregg2.Exec.TurnExecutorFull.recKMintAsset
  nonvacuous := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyCreation.MintASpec
  gate := Dregg2.Exec.TurnExecutorFull.recCMintAsset
  nonvacuous := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized

-- ── CELL-STATE-FIELD: SetFieldGuard / SetFieldSpec (gate = stateStepDev) ────────────────────────
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateField.SetFieldGuard
  gate := Dregg2.Exec.EffectsState.stateStepDev
  nonvacuous := Dregg2.Circuit.Spec.CellStateField.setFieldSpec_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateField.SetFieldSpec
  gate := Dregg2.Exec.EffectsState.stateStepDev
  nonvacuous := Dregg2.Circuit.Spec.CellStateField.setFieldSpec_rejects_unauthorized

-- ── SOVEREIGN-COMMITMENT: MakeSovereignGuard / MakeSovereignSpec (gate = makeSovereignStep) ──────
#load_bearing_audit_report Dregg2.Circuit.Spec.SovereignCommitment.MakeSovereignGuard
  gate := Dregg2.Exec.TurnExecutorFull.makeSovereignStep
  nonvacuous := Dregg2.Circuit.Spec.SovereignCommitment.makeSovereignSpec_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.SovereignCommitment.MakeSovereignSpec
  gate := Dregg2.Exec.TurnExecutorFull.makeSovereignStep
  nonvacuous := Dregg2.Circuit.Spec.SovereignCommitment.makeSovereignSpec_rejects_unauthorized

-- ── HEAP-WRITE: HeapWriteSpec (gate = heapStepGuardedW) ─────────────────────────────────────────
#load_bearing_audit_report Dregg2.Circuit.Spec.HeapWrite.HeapWriteSpec
  gate := Dregg2.Substrate.HeapKernel.heapStepGuardedW
  nonvacuous := Dregg2.Circuit.Spec.HeapWrite.heapWriteSpec_root_pinned

-- ── NEGATIVE-CALIBRATION FIXTURE #2 (defeq tooth): execGraph — the `execGraph_eq_any := rfl`
-- DEF-EQ-TO-GATE offender. ASSERTED to FAIL check #2 (defeq to `execGraphGate`): the command THROWS if
-- it unexpectedly passes. Its GENUINE counterpart (the independent spec the C-c1 legs attest against)
-- is `Spec.authConnects`. This + fixture #1 are the intended negative-calibration PAIR.
#load_bearing_calibration_expect_fail Dregg2.Spec.execGraph
  gate := Dregg2.Verify.LoadBearingAuditKey.execGraphGate
  genuine := Dregg2.Spec.authConnects

end Dregg2.Verify.LoadBearingAuditKey
