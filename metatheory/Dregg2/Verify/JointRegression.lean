/-
# Dregg2.Verify.JointRegression — regression pins for the common cross-vat charter pattern.

Tier-4 (`Verify/Catalog.lean`) covers intra-cell contract shapes. Cross-vat maneuvers are **common**
(not exotic): coordinated covenant + bilateral equalizer + per-leg credentials. This module is the
regression harness — it re-exports the proved keystones from the joint/charter spine so downstream
Apps and FFI cutover can import ONE module and get the full bilateral guarantee bundle.
-/
import Dregg2.Exec.JointCharterBridge
import Dregg2.Apps.CrossCellCovenantGated

namespace Dregg2.Verify.JointRegression

open Dregg2.Exec
open Dregg2.Exec.JointCharterBridge
open Dregg2.Exec.CrossVatCharter
open Dregg2.Exec.CoordinatedForestGate
open Dregg2.Exec.CrossCellForest
open Dregg2.Exec.CrossCaveat
open Dregg2.Exec.JointCell
open Dregg2.Apps.CrossCellCovenantGated

/-! ## §1 — The common-pattern bundle (charter ∧ bilateral ∧ cred-gated). -/

/-- **`joint_charter_commits`** — the demo cross-vat charter commits on the standard fixtures. -/
theorem joint_charter_commits :
    (charterDischarge demoCharter sA sB 0 0 noDischarges noDischarges).isSome :=
  ccov_charter_commits

/-- **`joint_charter_refines_bilateral`** — charter discharge implies bilateral coordinated commit. -/
theorem joint_charter_refines_bilateral :
    (execBilateralCoordinated sA sB (charterBilateral demoCharter)).isSome := by
  decide

/-- **`joint_cred_gated_commits`** — portal credentials + covenant commit on the bilateral path. -/
theorem joint_cred_gated_commits :
    (execBilateralCredGated sA sB honestCredStep).isSome := by decide

/-- **`joint_forged_cred_rejected`** — forged portal credential fail-closes the bilateral gate. -/
theorem joint_forged_cred_rejected :
    execBilateralCredGated sA sB forgedCredStep = none :=
  ccov_forged_cred_rejected

/-- **`joint_covenant_teeth`** — violated cross-cell covenant rejects even with good credentials. -/
theorem joint_covenant_teeth :
    execBilateralCoordinated sA sBhigh honestStep = none :=
  ccov_covenant_teeth

/-- **`joint_cg5_conserved`** — committed bilateral coordinated step preserves joint total. -/
theorem joint_cg5_conserved {A' B' : KernelState}
    (h : execBilateralCoordinated sA sB honestStep = some (A', B')) :
    jointTotal A' B' = jointTotal sA sB :=
  ccov_joint_conserves h

/-! ## §2 — `#guard` tripwires (non-vacuity). -/

#guard ((charterDischarge demoCharter sA sB 0 0 noDischarges noDischarges).isSome)  --  charter
#guard ((execBilateralCoordinated sA sB (charterBilateral demoCharter)).isSome)  --  refines
#guard ((execBilateralCredGated sA sB honestCredStep).isSome)  --  cred-gated
#guard ((execBilateralCredGated sA sB forgedCredStep).isSome) == false  --  forged rejected
#guard ((execBilateralCoordinated sA sBhigh honestStep).isSome) == false  --  covenant teeth
#guard (∑ i, (crossForestBilateral demoCharter.bt).δ i) == 0  --  forest Σ=0

/-! ## §3 — Axiom hygiene. -/

#assert_axioms joint_charter_commits
#assert_axioms joint_charter_refines_bilateral
#assert_axioms joint_cred_gated_commits
#assert_axioms joint_forged_cred_rejected
#assert_axioms joint_covenant_teeth
#assert_axioms joint_cg5_conserved

end Dregg2.Verify.JointRegression