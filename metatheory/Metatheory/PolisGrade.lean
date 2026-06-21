/-
# Metatheory.PolisGrade — graded severity: the quantale of violation-grades.

gem3.5flash's point (and gpt5.5's "quantale when budgets/cost demand it"): grade-laundering and
hole-rent are not Boolean — they ACCUMULATE and LAUNDER numeric coercion-capital across time and
branching, so the grade must be a **quantale**: an order `≤` (severity), a monoid `⊗` (sequential
accumulation, unit = "no violation"), a join `⊔` (worst-case over branches), with `⊗` MONOTONE and
DISTRIBUTING over `⊔` (so a linear action composed with a branch is the worst-case composition).
Boolean safety is the degenerate two-point instance.

We give the (binary) `GradeAlgebra` class, the **max-plus / tropical** model on `ℕ` (`⊔ = max`,
`⊗ = +` — accumulate worst-case cost; `+` distributes over `max`), graded bars with `or`-aggregation
and graded non-regression (`GradedNoWeaken`: severity only ever increases — "no legal rewrite closes
the door, even with numeric costs / finality tiers / time-locks"), and the graded amendment-stream
theorem. The deployed `Dregg2.Finality.Tier` is the intended *finality* grade instance (its rank is
the severity order); wiring that instance is the deployment step.

Pure Lean 4 core (imports only the import-free `Metatheory.Polis`; `ℕ` + `omega`); no `sorry`.
-/
import Metatheory.Polis

namespace Metatheory.PolisGrade

universe u

/-- A (binary) **quantale of violation grades**: severity order `le`, sequential accumulation `comp`
(`⊗`, unit `unit`), worst-case branch `join` (`⊔`), with `comp` monotone and distributing over
`join`. -/
class GradeAlgebra (Q : Type u) where
  le : Q → Q → Prop
  comp : Q → Q → Q
  unit : Q
  join : Q → Q → Q
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  comp_unit : ∀ a, comp unit a = a
  comp_comm : ∀ a b, comp a b = comp b a
  comp_assoc : ∀ a b c, comp (comp a b) c = comp a (comp b c)
  comp_mono : ∀ {a a'} (b), le a a' → le (comp a b) (comp a' b)
  join_le_left : ∀ a b, le a (join a b)
  join_le_right : ∀ a b, le b (join a b)
  join_lub : ∀ {a b c}, le a c → le b c → le (join a b) c
  comp_join : ∀ a b c, comp a (join b c) = join (comp a b) (comp a c)

namespace GradeAlgebra
variable {Q : Type u} [GradeAlgebra Q]

/-- `join` is monotone in its left argument (from the lub property) — the step `or`-composition
needs to be monotone for graded non-regression. -/
theorem join_mono_left {a a' : Q} (b : Q) (h : le a a') : le (join a b) (join a' b) :=
  join_lub (le_trans h (join_le_left a' b)) (join_le_right a' b)

end GradeAlgebra

/-! The max-plus / tropical model on `ℕ`, via standalone arithmetic lemmas (concrete goals, so
`omega` applies; the instance then takes them as terms, dodging projection-opacity). -/

private theorem nat_le_max_l (a b : Nat) : a ≤ max a b := by omega
private theorem nat_le_max_r (a b : Nat) : b ≤ max a b := by omega
private theorem nat_max_lub {a b c : Nat} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := by omega
private theorem nat_add_max (a b c : Nat) : a + max b c = max (a + b) (a + c) := by omega

/-- The **max-plus / tropical** quantale on `ℕ`: `⊔ = max` (worst-case branch), `⊗ = +`
(accumulate cost), unit `0` (no violation). `+` distributes over `max` — the canonical model of
"accumulate worst-case cost over time", i.e. hole-rent (`⊗`/`+` over epochs) and grade-laundering
(`⊔`/`max` over the trace). -/
instance : GradeAlgebra Nat where
  le := Nat.le
  comp := (· + ·)
  unit := 0
  join := max
  le_refl := Nat.le_refl
  le_trans := fun h₁ h₂ => Nat.le_trans h₁ h₂
  comp_unit := Nat.zero_add
  comp_comm := Nat.add_comm
  comp_assoc := Nat.add_assoc
  comp_mono := fun b h => Nat.add_le_add_right h b
  join_le_left := nat_le_max_l
  join_le_right := nat_le_max_r
  join_lub := nat_max_lub
  comp_join := nat_add_max

/-- A **graded politician floor**: each trace carries a violation grade (`0` = clean). The Boolean
`Bar` is the two-point degenerate case. -/
structure GradedBar (Q Trace : Type u) where
  severity : Trace → Q

/-- `or`-aggregation: the combined floor's grade is the **worst-case** (`⊔`) of the components. -/
def GradedBar.or {Q Trace : Type u} [GradeAlgebra Q] (b₁ b₂ : GradedBar Q Trace) :
    GradedBar Q Trace :=
  ⟨fun τ => GradeAlgebra.join (b₁.severity τ) (b₂.severity τ)⟩

/-- **Graded non-regression**: a later floor's grade dominates the earlier's at every trace —
"no legal rewrite may close the door behind you, even when the rules are renegotiated with numeric
costs, finality tiers, and time-locks" (gem3.5flash). The grade form of
`Metatheory.Polis.amendment_stream_nonregression`. -/
def GradedNoWeaken {Q Trace : Type u} [GradeAlgebra Q] (old new : GradedBar Q Trace) : Prop :=
  ∀ τ, GradeAlgebra.le (old.severity τ) (new.severity τ)

theorem GradedNoWeaken.rfl' {Q Trace : Type u} [GradeAlgebra Q] (b : GradedBar Q Trace) :
    GradedNoWeaken b b := fun τ => GradeAlgebra.le_refl (b.severity τ)

theorem GradedNoWeaken.trans' {Q Trace : Type u} [GradeAlgebra Q] {a b c : GradedBar Q Trace}
    (h₁ : GradedNoWeaken a b) (h₂ : GradedNoWeaken b c) : GradedNoWeaken a c :=
  fun τ => GradeAlgebra.le_trans (h₁ τ) (h₂ τ)

/-- **`or` PRESERVES graded non-regression** — strengthening one graded component never lowers the
union grade. The graded politician floor is monotone-amendable. -/
theorem GradedNoWeaken.or_mono {Q Trace : Type u} [GradeAlgebra Q] {old new : GradedBar Q Trace}
    (h : GradedNoWeaken old new) (c : GradedBar Q Trace) :
    GradedNoWeaken (old.or c) (new.or c) :=
  fun τ => GradeAlgebra.join_mono_left (c.severity τ) (h τ)

/-- **`graded_amendment_nonregression`** — along ANY graded-amendment stream that never weakens,
the frozen-minimum grade is preserved forever. The quantale lift of
`amendment_stream_nonregression`: graded non-regression survives dynamic renegotiation with costs. -/
theorem graded_amendment_nonregression {Q Trace : Type u} [GradeAlgebra Q]
    (ams : Nat → GradedBar Q Trace → GradedBar Q Trace)
    (mono : ∀ n b, GradedNoWeaken b (ams n b))
    (floorMin b₀ : GradedBar Q Trace) (h₀ : GradedNoWeaken floorMin b₀) :
    ∀ n, GradedNoWeaken floorMin (Nat.rec b₀ (fun k bk => ams k bk) n) := by
  intro n
  induction n with
  | zero => exact h₀
  | succ k ih => exact ih.trans' (mono k _)

/-! ### Non-vacuity — the grade really accumulates, branches worst-case, and never weakens. -/

/-- HOLE-RENT: severity ACCUMULATES over epochs (`⊗ = +`) — a hole open 3 epochs grades `3`. -/
example : GradeAlgebra.comp (GradeAlgebra.comp (1 : Nat) 1) 1 = 3 := by decide
/-- GRADE-LAUNDERING: severity is the WORST tier reached (`⊔ = max`) — `max 2 4 = 4`. -/
example : GradeAlgebra.join (2 : Nat) 4 = 4 := by decide
/-- `or` aggregates worst-case: the union of grade-2 and grade-4 bars grades `4`. -/
example : ((⟨fun _ => 2⟩ : GradedBar Nat Unit).or ⟨fun _ => 4⟩).severity () = 4 := by decide
/-- GRADED NON-REGRESSION: a grade-3 floor dominates a grade-1 floor pointwise. -/
example : GradedNoWeaken (⟨fun _ => 1⟩ : GradedBar Nat Unit) ⟨fun _ => 3⟩ :=
  fun _ => by show (1 : Nat) ≤ 3; omega
/-- … and `+`-distributes over `max` (the quantale law): `a ⊗ (b ⊔ c) = (a⊗b) ⊔ (a⊗c)`. -/
example : GradeAlgebra.comp (3 : Nat) (GradeAlgebra.join 2 5)
        = GradeAlgebra.join (GradeAlgebra.comp 3 2) (GradeAlgebra.comp 3 5) := by decide

end Metatheory.PolisGrade
