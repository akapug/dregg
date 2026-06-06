/-
# Dregg2.Exec.CoordinatedForestGate — wiring `.coordinated` caveats to the bilateral equalizer.

`FullForestAuth.GatedCaveat.holds` correctly fail-closes `.coordinated` on a **single-cell** node.
This module supplies the **positive** production path at the **joint kernel** layer (`KernelState ×
KernelState`): optional per-leg credential portal checks, then `dischargeCoordinated` on the atomic
equalizer. Intra-cell fail-closed is unchanged; coordinated caveats become **common** via
`execBilateralCoordinated` / `execBilateralCredGated`.

The `RecordKernelState` gated forest (`execFullForestG`) and the joint `KernelState` equalizer use
different kernel carriers. The lift to `RecChainedState` pairs lives in
`CoordinatedForestGLift` (`execCoordinatedForestG` / `recordKernelView`); this module stays the
joint-layer equalizer; Apps witness on the proved joint fixtures (`sA`/`sB` from `JointCell`).
-/
import Dregg2.Exec.FullForestAuth
import Dregg2.Exec.CoordinatedCaveat
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Exec.CoordinatedForestGate

open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.CoordinatedCaveat
open Dregg2.Exec.CrossCaveat
open Dregg2.Exec.JointCell
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — Bilateral step carriers (joint-kernel layer). -/

/-- A **coordinated bilateral step** — covenant + turn + CG-2 binding (the equalizer payload). -/
structure BilateralStep where
  covenant : CoordinatedCaveat
  bt       : BiTurn
  bind     : SharedBinding bt

/-- A **credential-gated** bilateral step — adds per-leg §8 portal credentials (the common charter
shape without yet lifting into `RecChainedState`). -/
structure BilateralCredStep extends BilateralStep where
  credA : Authorization Dg Pf
  credB : Authorization Dg Pf

/-- **`.coordinated` caveats require the bilateral path** — intra-cell `holds` fail-closes. -/
def GatedCaveat.requiresBilateral (c : GatedCaveat) : Bool :=
  c.tier == .coordinated

/-- Wrap a cross-cell `φ` as a `.coordinated` caveat. -/
def coordinatedOf (φ : CrossCaveat) : CoordinatedCaveat := { φ := φ }

/-! ## §2 — Bilateral executors (joint `KernelState`). -/

/-- **`execBilateralCoordinated`** — the equalizer commit (no credential overlay). -/
def execBilateralCoordinated (A B : KernelState) (step : BilateralStep) :
    Option (KernelState × KernelState) :=
  dischargeCoordinated step.covenant A B step.bt

/-- Per-leg credential admission (portal only — the §8 WHO check at the joint layer). -/
def bilateralCredAdmits (step : BilateralCredStep) : Bool :=
  portalVerify step.credA && portalVerify step.credB

/-- Project a credential step to its equalizer payload. -/
def BilateralCredStep.bilateral (s : BilateralCredStep) : BilateralStep :=
  { covenant := s.covenant, bt := s.bt, bind := s.bind }

/-- **`execBilateralCredGated`** — credentials ∧ coordinated equalizer (the charter-shaped gate). -/
def execBilateralCredGated (A B : KernelState) (step : BilateralCredStep) :
    Option (KernelState × KernelState) :=
  if bilateralCredAdmits step then execBilateralCoordinated A B step.bilateral else none

/-! ## §3 — Keystones. -/

theorem coordinated_intra_gate_failclosed (c : GatedCaveat) (s : RecChainedState)
    (h : c.tier = .coordinated) : c.holds s = false := by
  unfold GatedCaveat.holds; rw [h]

theorem bilateral_coordinated_sound (step : BilateralStep) {A B A' B' : KernelState}
    (h : execBilateralCoordinated A B step = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧
    step.bind.sidOfA = step.bind.sidOfB ∧
    step.covenant.φ A B = true :=
  coordinated_discharge_sound step.covenant step.bind h

theorem bilateral_cred_unauthorized_fails (step : BilateralCredStep) (A B : KernelState)
    (h : bilateralCredAdmits step = false) :
    execBilateralCredGated A B step = none := by
  unfold execBilateralCredGated bilateralCredAdmits
  by_cases hc : portalVerify step.credA && portalVerify step.credB
  · have hadm : bilateralCredAdmits step = true := by simp [bilateralCredAdmits, hc]
    rw [hadm] at h
    cases h
  · simp [hc, bilateralCredAdmits]

theorem bilateral_cred_forged_fails :
    execBilateralCredGated sA sB
      { covenant := covenantCoord, bt := goodBi
        , bind := { sidOfA := 42, sidOfB := 42, agreeA := rfl, agreeB := rfl }
        , credA := forgedCred, credB := goodCred }
      = none := by
  unfold execBilateralCredGated bilateralCredAdmits portalVerify forgedCred goodCred
  decide

theorem bilateral_covenant_teeth :
    execBilateralCoordinated sA sBhigh
      { covenant := covenantCoord, bt := goodBi
        , bind := { sidOfA := 42, sidOfB := 42, agreeA := rfl, agreeB := rfl } }
      = none :=
  overbroad_discharge_rejected

/-! ## §4 — `#guard` demos. -/

def demoBind : SharedBinding goodBi :=
  { sidOfA := 42, sidOfB := 42, agreeA := rfl, agreeB := rfl }

def demoStep : BilateralStep :=
  { covenant := covenantCoord, bt := goodBi, bind := demoBind }

def demoCredStep : BilateralCredStep :=
  { covenant := covenantCoord, bt := goodBi, bind := demoBind
  , credA := goodCred, credB := goodCred }

#guard GatedCaveat.requiresBilateral { tier := .coordinated, check := fun _ => true }  --  true
#guard ((execBilateralCoordinated sA sB demoStep).isSome)  --  covenant holds ⇒ commits
#guard ((execBilateralCoordinated sA sBhigh demoStep).isSome) == false  --  covenant violated
#guard ((execBilateralCredGated sA sB demoCredStep).isSome)  --  creds + covenant ⇒ commits

/-! ## §5 — Axiom hygiene. -/

#assert_axioms coordinated_intra_gate_failclosed
#assert_axioms bilateral_coordinated_sound
#assert_axioms bilateral_cred_unauthorized_fails
#assert_axioms bilateral_cred_forged_fails
#assert_axioms bilateral_covenant_teeth

end Dregg2.Exec.CoordinatedForestGate