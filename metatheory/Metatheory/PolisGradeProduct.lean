/-
# Metatheory.PolisGradeProduct — the PRODUCT quantale grade (gpt5.5's architecture §5).

gpt5.5: don't collapse everything into one `Nat` — use a PRODUCT grade. Finality tiers launder
(idempotent `⊔`/max, no accumulation); hole-rent and burden accumulate (additive max-plus). So the
politician grade is a product `tier × rent × burden`, each component its own `GradeAlgebra`. We
prove the general fact: **the product of two grade-quantales is a grade-quantale** (componentwise),
so any product of deployed grades (e.g. `Finality.Tier × ℕ`) is automatically a quantale — and the
graded non-regression theorems lift to it for free.

Pure Lean 4 core (imports `Metatheory.PolisGrade`).
-/
import Metatheory.PolisGrade

namespace Metatheory.PolisGrade

universe u v

/-- **The product of two grade-quantales is a grade-quantale** (componentwise). -/
instance instProd {Q : Type u} {R : Type v} [GradeAlgebra Q] [GradeAlgebra R] :
    GradeAlgebra (Q × R) where
  le p q := GradeAlgebra.le p.1 q.1 ∧ GradeAlgebra.le p.2 q.2
  comp p q := (GradeAlgebra.comp p.1 q.1, GradeAlgebra.comp p.2 q.2)
  unit := (GradeAlgebra.unit, GradeAlgebra.unit)
  join p q := (GradeAlgebra.join p.1 q.1, GradeAlgebra.join p.2 q.2)
  le_refl _ := ⟨GradeAlgebra.le_refl _, GradeAlgebra.le_refl _⟩
  le_trans h₁ h₂ := ⟨GradeAlgebra.le_trans h₁.1 h₂.1, GradeAlgebra.le_trans h₁.2 h₂.2⟩
  comp_unit p := Prod.ext_iff.mpr ⟨GradeAlgebra.comp_unit p.1, GradeAlgebra.comp_unit p.2⟩
  comp_comm p q := Prod.ext_iff.mpr ⟨GradeAlgebra.comp_comm p.1 q.1, GradeAlgebra.comp_comm p.2 q.2⟩
  comp_assoc p q r :=
    Prod.ext_iff.mpr ⟨GradeAlgebra.comp_assoc p.1 q.1 r.1, GradeAlgebra.comp_assoc p.2 q.2 r.2⟩
  comp_mono b h := ⟨GradeAlgebra.comp_mono b.1 h.1, GradeAlgebra.comp_mono b.2 h.2⟩
  join_le_left p q := ⟨GradeAlgebra.join_le_left p.1 q.1, GradeAlgebra.join_le_left p.2 q.2⟩
  join_le_right p q := ⟨GradeAlgebra.join_le_right p.1 q.1, GradeAlgebra.join_le_right p.2 q.2⟩
  join_lub h₁ h₂ := ⟨GradeAlgebra.join_lub h₁.1 h₂.1, GradeAlgebra.join_lub h₁.2 h₂.2⟩
  comp_join p q r :=
    Prod.ext_iff.mpr ⟨GradeAlgebra.comp_join p.1 q.1 r.1, GradeAlgebra.comp_join p.2 q.2 r.2⟩

/-- The politician product grade: a laundering grade × an additive rent grade. (Deployment: the
first component is `Dregg2.Finality.Tier` with `⊗ = max` (idempotent — finality doesn't accumulate,
it takes the worst); the second is additive max-plus rent. Here `ℕ × ℕ` is the concrete demo.) -/
abbrev PolGrade := Nat × Nat

/-- Composition is componentwise — rent (and, in deployment, the tier) accumulate independently. -/
example : GradeAlgebra.comp ((1, 2) : PolGrade) (3, 4) = (4, 6) := by decide
/-- Worst-case branch is componentwise `⊔`. -/
example : GradeAlgebra.join ((1, 5) : PolGrade) (3, 2) = (3, 5) := by decide
/-- Graded non-regression lifts to the product for free (a grade-(3,3) floor dominates a
grade-(1,1) one pointwise). -/
example : GradedNoWeaken (⟨fun _ => (1, 1)⟩ : GradedBar PolGrade Unit) ⟨fun _ => (3, 3)⟩ :=
  fun _ => ⟨by show (1 : Nat) ≤ 3; omega, by show (1 : Nat) ≤ 3; omega⟩

end Metatheory.PolisGrade
