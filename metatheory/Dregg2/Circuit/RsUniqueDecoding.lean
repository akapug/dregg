/-
# RS unique decoding — DECODING IS WELL-DEFINED (FriExtract link D).

THE BRICK: a received word in the unique-decoding regime determines AT MOST ONE low-degree
polynomial. Chain, in this one file:

  (1) **RS minimum distance** (`rs_min_distance`): the evaluation vectors of two DISTINCT
      `natDegree < k` polynomials on `n` distinct points have `hammingDist ≥ n − k + 1`
      (stated ℕ-cleanly as `n + 1 ≤ hammingDist + k`). Direct contrapositive of
      `lowDegree_agree_forces_eq` — the agreement set has < k points, so the disagreement
      set has > n − k.
  (2) **Unique nearest codeword** (`unique_nearest_codeword`): if a received word `w` is
      within the unique-decoding radius (`2·d + k ≤ n`, i.e. `d < (n−k+1)/2`) of the
      codewords of `p₁` and `p₂`, then `p₁ = p₂` — `hammingDist_triangle` squeezes
      `d(c₁,c₂) ≤ d(c₁,w) + d(w,c₂) ≤ n − k < n − k + 1` against (1).
  (3) **Decode well-defined** (`decode_wellDefined`, `decode_existsUnique`): the set of
      low-degree polynomials within the radius of `w` is a SUBSINGLETON — the decoder the
      FriExtract argument runs is a well-defined partial function, and IF a decoding
      exists it is UNIQUE.

Specialized at the DEPLOYED field (`BabyBear = ZMod 2013265921`) and at the deployed
FRI blowup (`ir2LeafWrapConfig.logBlowup = 6`, rate `2⁻⁶`): `decode_wellDefined_deployedBlowup`.

FIRE (non-vacuous, concrete BabyBear data, n = 4, k = 2, minimum distance 3):
  * `min_distance_fires` / `min_distance_exact`: the codewords of `X` and `0` on
    `{0,1,2,3}` are at distance EXACTLY 3 = n − k + 1 — the bound is met, not vacuous.
  * `decode_unique_fires`: a received word `![1,2,3,42]` — the codeword of `X + 1` with
    coordinate 3 GENUINELY corrupted (`w4_corrupted`) — still pins its polynomial:
    uniqueness forces `X + C 1 = C 1 + X` THROUGH the decoder theorem, every hypothesis
    discharged on concrete data (distance 1, radius `2·1 + 2 ≤ 4`).
  * `decode_existsUnique_fires`: on that same corrupted word, existence + uniqueness (`∃!`).

SCOPE (honest): this file is the DECODER-WELL-DEFINEDNESS half of link D. The PROXIMITY
half — that FRI acceptance certifies the committed word IS within the unique-decoding
radius of the RS code (the BBHR18-style distortion/soundness analysis) — is the SEPARATE
deep obligation (link A) and is NOT attempted here. This file supplies: GIVEN that
proximity, the decoded polynomial is unique.
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree
import Dregg2.Circuit.LowDegreeUniqueness
import Dregg2.Circuit.FriVerifier

namespace Dregg2.Circuit.RsUniqueDecoding

open Polynomial
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.LowDegreeUniqueness

variable {F : Type*} [CommRing F] {n k : ℕ}

/-! ## §0 — The RS codeword: the evaluation vector of a polynomial on `n` points. -/

/-- The RS encoding of `p` on the point family `pts`: the evaluation vector
`i ↦ p.eval (pts i)`. Distinctness of the points enters as `Function.Injective pts`. -/
def evalVec (pts : Fin n → F) (p : Polynomial F) : Fin n → F := fun i => p.eval (pts i)

variable [IsDomain F] [DecidableEq F]

/-! ## §1 — RS minimum distance `n − k + 1` (Singleton bound met, ℕ-clean form). -/

/-- **RS minimum distance.** Two DISTINCT polynomials of `natDegree < k` evaluated on `n`
distinct points disagree in MORE than `n − k` coordinates: `n + 1 ≤ hammingDist + k`
(ℕ-clean form of `hammingDist ≥ n − k + 1`). Contrapositive of
`lowDegree_agree_forces_eq`: were there ≥ k agreements, the polynomials would be equal. -/
theorem rs_min_distance (pts : Fin n → F) (hinj : Function.Injective pts)
    {p q : Polynomial F} (hne : p ≠ q) (hp : p.natDegree < k) (hq : q.natDegree < k) :
    n + 1 ≤ hammingDist (evalVec pts p) (evalVec pts q) + k := by
  -- the agreement set has fewer than k points, else `lowDegree_agree_forces_eq` forces p = q
  have hAcard :
      (Finset.univ.filter fun i : Fin n => p.eval (pts i) = q.eval (pts i)).card < k := by
    by_contra h
    push Not at h
    refine hne (lowDegree_agree_forces_eq p q
      ((Finset.univ.filter fun i : Fin n => p.eval (pts i) = q.eval (pts i)).image pts)
      hp hq ?_ ?_)
    · rwa [Finset.card_image_of_injective _ hinj]
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
  -- agreements + disagreements = n; hammingDist IS the disagreement count
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => p.eval (pts i) = q.eval (pts i))
  have hdist : hammingDist (evalVec pts p) (evalVec pts q)
      = (Finset.univ.filter fun i : Fin n => ¬ p.eval (pts i) = q.eval (pts i)).card := rfl
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-! ## §2 — Unique nearest codeword (triangle inequality vs minimum distance). -/

/-- **Unique nearest codeword.** If a received word `w` lies within the unique-decoding
radius of the codewords of BOTH `p₁` and `p₂` — `2·d(w,cᵢ) + k ≤ n`, the ℕ-clean form of
`d(w,cᵢ) < (n−k+1)/2` — then `p₁ = p₂`. Triangle inequality:
`d(c₁,c₂) ≤ d(c₁,w) + d(w,c₂) ≤ n − k`, contradicting `rs_min_distance` unless equal. -/
theorem unique_nearest_codeword (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F) {p₁ p₂ : Polynomial F}
    (hp₁ : p₁.natDegree < k) (hp₂ : p₂.natDegree < k)
    (hd₁ : 2 * hammingDist w (evalVec pts p₁) + k ≤ n)
    (hd₂ : 2 * hammingDist w (evalVec pts p₂) + k ≤ n) :
    p₁ = p₂ := by
  by_contra hne
  have hmin := rs_min_distance pts hinj hne hp₁ hp₂
  have htri := hammingDist_triangle (evalVec pts p₁) w (evalVec pts p₂)
  have hcomm : hammingDist (evalVec pts p₁) w = hammingDist w (evalVec pts p₁) :=
    hammingDist_comm _ _
  omega

/-- Radius-form variant: hypotheses stated as `2·d < n − k + 1` (with `k ≤ n` making the
ℕ subtraction honest). Same content as `unique_nearest_codeword`; `omega` converts. -/
theorem unique_nearest_codeword_radius (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F) {p₁ p₂ : Polynomial F} (hk : k ≤ n)
    (hp₁ : p₁.natDegree < k) (hp₂ : p₂.natDegree < k)
    (hd₁ : 2 * hammingDist w (evalVec pts p₁) < n - k + 1)
    (hd₂ : 2 * hammingDist w (evalVec pts p₂) < n - k + 1) :
    p₁ = p₂ :=
  unique_nearest_codeword pts hinj w hp₁ hp₂ (by omega) (by omega)

/-! ## §3 — Decoding is WELL-DEFINED. -/

/-- **Decode well-defined (subsingleton form).** For any received word `w`, the set of
`natDegree < k` polynomials whose codeword lies within the unique-decoding radius of `w`
is a SUBSINGLETON: the FriExtract decoder, wherever it is defined, is single-valued. -/
theorem decode_wellDefined (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F) :
    Set.Subsingleton {p : Polynomial F |
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) + k ≤ n} :=
  fun _ h₁ _ h₂ => unique_nearest_codeword pts hinj w h₁.1 h₂.1 h₁.2 h₂.2

/-- **Decode well-defined (`∃!` form).** IF some low-degree polynomial lies within the
unique-decoding radius of `w` (the proximity fact link A must supply), THEN exactly one
does — the decoded polynomial the extraction argument names is well-defined. -/
theorem decode_existsUnique (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F)
    (hex : ∃ p : Polynomial F,
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) + k ≤ n) :
    ∃! p : Polynomial F,
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) + k ≤ n :=
  let ⟨p, hp⟩ := hex
  ⟨p, hp, fun _ hq => unique_nearest_codeword pts hinj w hq.1 hp.1 hq.2 hp.2⟩

/-! ## §4 — Specialization at the DEPLOYED field and blowup. -/

/-- `unique_nearest_codeword` over **BabyBear** — the deployed prover's field. -/
theorem unique_nearest_codeword_babyBear {n k : ℕ} (pts : Fin n → BabyBear)
    (hinj : Function.Injective pts) (w : Fin n → BabyBear) {p₁ p₂ : Polynomial BabyBear}
    (hp₁ : p₁.natDegree < k) (hp₂ : p₂.natDegree < k)
    (hd₁ : 2 * hammingDist w (evalVec pts p₁) + k ≤ n)
    (hd₂ : 2 * hammingDist w (evalVec pts p₂) + k ≤ n) :
    p₁ = p₂ :=
  unique_nearest_codeword pts hinj w hp₁ hp₂ hd₁ hd₂

/-- **Decode well-defined at the DEPLOYED blowup**: domain size `n = 2^logBlowup · k` with
`ir2LeafWrapConfig.logBlowup = 6` (`FriVerifier.lean`, `ir2_leaf_wrap_config`) — rate `2⁻⁶`,
unique-decoding radius `2·d + k ≤ 64·k`. Pure instantiation of `decode_wellDefined`. -/
theorem decode_wellDefined_deployedBlowup (k : ℕ)
    (pts : Fin (2 ^ Dregg2.Circuit.FriVerifier.ir2LeafWrapConfig.logBlowup * k) → BabyBear)
    (hinj : Function.Injective pts)
    (w : Fin (2 ^ Dregg2.Circuit.FriVerifier.ir2LeafWrapConfig.logBlowup * k) → BabyBear) :
    Set.Subsingleton {p : Polynomial BabyBear |
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) + k
        ≤ 2 ^ Dregg2.Circuit.FriVerifier.ir2LeafWrapConfig.logBlowup * k} :=
  decode_wellDefined pts hinj w

/-! ## §5 — FIRE: concrete BabyBear instance (n = 4, k = 2, minimum distance 3). -/

/-- Four distinct BabyBear points `{0,1,2,3}` — the concrete evaluation domain. -/
noncomputable def pts4 : Fin 4 → BabyBear := ![0, 1, 2, 3]

/-- The four points are genuinely distinct in BabyBear (kernel-checked). -/
theorem pts4_injective : Function.Injective pts4 := by decide

/-- Codeword of `X` on `pts4` is `![0,1,2,3]`. -/
theorem evalVec_pts4_X : evalVec pts4 (X : Polynomial BabyBear) = ![0, 1, 2, 3] := by
  funext i
  fin_cases i <;> simp [evalVec, pts4]

/-- Codeword of `0` on `pts4` is `![0,0,0,0]`. -/
theorem evalVec_pts4_zero : evalVec pts4 (0 : Polynomial BabyBear) = ![0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [evalVec, pts4]

/-- **FIRE (minimum distance, via the theorem).** `X ≠ 0`, both `natDegree < 2`, so
`rs_min_distance` forces their codewords ≥ 3 = n − k + 1 apart. -/
theorem min_distance_fires :
    3 ≤ hammingDist (evalVec pts4 (X : Polynomial BabyBear)) (evalVec pts4 0) := by
  have h := rs_min_distance (k := 2) pts4 pts4_injective (p := X) (q := 0)
    X_ne_zero (by simp) (by simp)
  omega

/-- **FIRE (minimum distance, exhibited exactly).** The distance is EXACTLY 3 — the
`n − k + 1` bound is achieved by concrete codewords, not vacuous. -/
theorem min_distance_exact :
    hammingDist (evalVec pts4 (X : Polynomial BabyBear)) (evalVec pts4 0) = 3 := by
  rw [evalVec_pts4_X, evalVec_pts4_zero]
  decide

/-- The received word: the codeword `![1,2,3,4]` of `X + 1` with coordinate 3 corrupted
to `42` — a REAL error inside the unique-decoding radius (radius: `2·d + 2 ≤ 4`, d ≤ 1). -/
noncomputable def w4 : Fin 4 → BabyBear := ![1, 2, 3, 42]

/-- Codeword of `X + C 1` on `pts4` is `![1,2,3,4]`. -/
theorem evalVec_pts4_XaddOne :
    evalVec pts4 (X + C 1 : Polynomial BabyBear) = ![1, 2, 3, 4] := by
  funext i
  fin_cases i <;> simp [evalVec, pts4] <;> norm_num

/-- Codeword of `C 1 + X` on `pts4` is the same vector `![1,2,3,4]`. -/
theorem evalVec_pts4_OneAddX :
    evalVec pts4 (C 1 + X : Polynomial BabyBear) = ![1, 2, 3, 4] := by
  funext i
  fin_cases i <;> simp [evalVec, pts4] <;> norm_num

/-- The corruption is REAL: `w4` is NOT the codeword of `X + C 1` (coordinate 3 differs). -/
theorem w4_corrupted : w4 ≠ evalVec pts4 (X + C 1 : Polynomial BabyBear) := by
  rw [evalVec_pts4_XaddOne]
  decide

/-- `w4` is at Hamming distance exactly 1 from the codeword `![1,2,3,4]`. -/
theorem w4_dist : hammingDist w4 (![1, 2, 3, 4] : Fin 4 → BabyBear) = 1 := by decide

/-- **FIRE (unique decoding, hypotheses genuinely discharged).** The corrupted word `w4`
pins its polynomial: `unique_nearest_codeword` at (n,k) = (4,2) forces `X + C 1 = C 1 + X`
— derived THROUGH the decoder theorem (distance 1, radius `2·1 + 2 ≤ 4`), not by `ring`. -/
theorem decode_unique_fires : (X + C 1 : Polynomial BabyBear) = C 1 + X := by
  refine unique_nearest_codeword (k := 2) pts4 pts4_injective w4 ?_ ?_ ?_ ?_
  · rw [natDegree_X_add_C]
    norm_num
  · have h : (C 1 + X : Polynomial BabyBear).natDegree ≤ 1 := by compute_degree
    omega
  · rw [evalVec_pts4_XaddOne, w4_dist]
  · rw [evalVec_pts4_OneAddX, w4_dist]

/-- **FIRE (`∃!`).** On the concretely corrupted word `w4` there EXISTS a decoding
(`X + C 1`, distance 1) and it is UNIQUE — `decode_existsUnique` with every hypothesis
discharged on deployed-field data. -/
theorem decode_existsUnique_fires :
    ∃! p : Polynomial BabyBear,
      p.natDegree < 2 ∧ 2 * hammingDist w4 (evalVec pts4 p) + 2 ≤ 4 :=
  decode_existsUnique pts4 pts4_injective w4
    ⟨X + C 1, by rw [natDegree_X_add_C]; norm_num, by rw [evalVec_pts4_XaddOne, w4_dist]⟩

/-! ## §6 — Axiom hygiene: every theorem kernel-clean. -/

#assert_axioms rs_min_distance
#assert_axioms unique_nearest_codeword
#assert_axioms unique_nearest_codeword_radius
#assert_axioms decode_wellDefined
#assert_axioms decode_existsUnique
#assert_axioms unique_nearest_codeword_babyBear
#assert_axioms decode_wellDefined_deployedBlowup
#assert_axioms pts4_injective
#assert_axioms evalVec_pts4_X
#assert_axioms evalVec_pts4_zero
#assert_axioms min_distance_fires
#assert_axioms min_distance_exact
#assert_axioms evalVec_pts4_XaddOne
#assert_axioms evalVec_pts4_OneAddX
#assert_axioms w4_corrupted
#assert_axioms w4_dist
#assert_axioms decode_unique_fires
#assert_axioms decode_existsUnique_fires

end Dregg2.Circuit.RsUniqueDecoding
