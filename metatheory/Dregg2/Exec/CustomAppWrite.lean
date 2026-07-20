/-
# Dregg2.Exec.CustomAppWrite — the bounded atomic Custom → app-field face

`Effect::Custom` is a proof-binding carrier, not a state-transition verb.  The deployed
outer EffectVM already proves ordinary `SetField` effects and the resulting sovereign
post-state; the custom leaf/fold already binds the custom verifier, proof, public inputs,
and the same state transition.  The missing executor seam was the equality between an
application value published by that proof and the bounded fields the turn writes.

This file proves the composition, without pretending to be a Rust refinement:

1. `CustomPublishes` says the verified custom proof publishes application vector `root`;
2. `AdmittedWriteRun` says admission paired it with the immediately following contiguous
   field-write run, whose values equal those public inputs;
3. `EffectVmApplies` says the outer proven transition put that run in the post-state.

`custom_app_write_atomic` composes the three legs: every declared post-state field equals
the custom proof's published application value.  `tampered_post_refused` is the negative
tooth.  The two-lane literal example demonstrates that the face is satisfiable.

The Rust implementation additionally restricts the values to canonical BabyBear scalar
encodings and the field range to `fields[0..8]`; the `fieldBound` premise mirrors the latter.
No axiom, no `sorry`.
-/
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Exec.CustomAppWrite

set_option autoImplicit false

/-- The bounded state surface exposed by the deployed wide custom leg. -/
abbrev FieldOctet := Fin 8 → Nat

/-- One ordinary typed `SetField` effect, projected to the data this face consumes. -/
structure FieldWrite where
  cell  : Nat
  index : Nat
  value : Nat
deriving DecidableEq, Repr

/-- Convert a declared app-field offset to its genuinely bounded `Fin 8` index. -/
def fieldIndex {L : Nat} (fieldKey : Nat) (fieldBound : fieldKey + L ≤ 8)
    (j : Fin L) : Fin 8 :=
  ⟨fieldKey + j.1, by omega⟩

/-- Leg 1: the verified custom program publishes `root` at the declared PI offset. -/
def CustomPublishes {L : Nat} (piOffset : Nat) (pis : Nat → Nat)
    (root : Fin L → Nat) : Prop :=
  ∀ j, pis (piOffset + j.1) = root j

/-- Leg 2: admission requires the `L` effects immediately after Custom to be the
contiguous field run for this cell, with values copied exactly from the declared app PIs. -/
def AdmittedWriteRun {L : Nat} (cell fieldKey piOffset : Nat) (pis : Nat → Nat)
    (writes : Fin L → FieldWrite) : Prop :=
  ∀ j, (writes j).cell = cell ∧
       (writes j).index = fieldKey + j.1 ∧
       (writes j).value = pis (piOffset + j.1)

/-- Leg 3: the outer EffectVM transition applies the admitted ordinary field writes to
the sovereign post-state. -/
def EffectVmApplies {L : Nat} (fieldKey : Nat) (fieldBound : fieldKey + L ≤ 8)
    (writes : Fin L → FieldWrite) (post : FieldOctet) : Prop :=
  ∀ j, post (fieldIndex fieldKey fieldBound j) = (writes j).value

/-- The exact three-leg admission certificate for the bounded custom app-write face. -/
structure Admitted {L : Nat} (cell fieldKey piOffset : Nat) (fieldBound : fieldKey + L ≤ 8)
    (pis : Nat → Nat) (root : Fin L → Nat) (writes : Fin L → FieldWrite)
    (post : FieldOctet) : Prop where
  customPublishes : CustomPublishes piOffset pis root
  writeRun        : AdmittedWriteRun cell fieldKey piOffset pis writes
  effectVmApplies : EffectVmApplies fieldKey fieldBound writes post

/-- **Atomic custom app write.** If the proof publishes `root`, admission equates its app
PIs to the typed write run, and the outer proven transition applies that run, then each
bounded committed post-state field is exactly the corresponding published value. -/
theorem custom_app_write_atomic {L cell fieldKey piOffset : Nat}
    (fieldBound : fieldKey + L ≤ 8) (pis : Nat → Nat) (root : Fin L → Nat)
    (writes : Fin L → FieldWrite) (post : FieldOctet)
    (h : Admitted cell fieldKey piOffset fieldBound pis root writes post) :
    ∀ j, post (fieldIndex fieldKey fieldBound j) = root j := by
  intro j
  rw [h.effectVmApplies j, (h.writeRun j).2.2, h.customPublishes j]

/-- **Negative tooth.** A post-state that differs from the custom proof's published value
on any declared lane cannot possess the three-leg admission certificate. -/
theorem tampered_post_refused {L cell fieldKey piOffset : Nat}
    (fieldBound : fieldKey + L ≤ 8) (pis : Nat → Nat) (root : Fin L → Nat)
    (writes : Fin L → FieldWrite) (post : FieldOctet)
    (hTamper : ∃ j, post (fieldIndex fieldKey fieldBound j) ≠ root j) :
    ¬ Admitted cell fieldKey piOffset fieldBound pis root writes post := by
  intro h
  obtain ⟨j, hj⟩ := hTamper
  exact hj (custom_app_write_atomic fieldBound pis root writes post h j)

/-! ## Literal non-vacuity: a two-lane result `[7, 9]` written to fields 2 and 3. -/

def demoPis : Nat → Nat
  | 16 => 7
  | 17 => 9
  | _  => 0

def demoRoot (j : Fin 2) : Nat := 2 * j.1 + 7

def demoWrites (j : Fin 2) : FieldWrite :=
  { cell := 4, index := 2 + j.1, value := 2 * j.1 + 7 }

def demoPost (j : Fin 8) : Nat :=
  match j.1 with
  | 2 => 7
  | 3 => 9
  | _ => 0

theorem demo_admitted : Admitted 4 2 16 (by omega) demoPis demoRoot demoWrites demoPost := by
  constructor
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j <;> decide
  · intro j
    fin_cases j <;> rfl

/-- The face fires on a concrete transition: the committed post-state fields 2 and 3 are
exactly the proof-published values 7 and 9. -/
theorem demo_atomic :
    ∀ j, demoPost (fieldIndex 2 (L := 2) (by omega) j) = demoRoot j :=
  custom_app_write_atomic (by omega) demoPis demoRoot demoWrites demoPost demo_admitted

#assert_axioms custom_app_write_atomic
#assert_axioms tampered_post_refused
#assert_axioms demo_admitted
#assert_axioms demo_atomic

end Dregg2.Exec.CustomAppWrite
