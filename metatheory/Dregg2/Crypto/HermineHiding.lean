/-
# `Dregg2.Crypto.HermineHiding` — the KEY-HIDING theorem: signing does not leak the secret.

The final leg between "verified algebra" and "verified *usable* signature." `HermineMSIS` proved a
forgery breaks MSIS (unforgeability); this proves the complementary property a signature scheme MUST
have to be usable at all: **the signature transcript is (statistically) independent of the secret**, so
publishing signatures does not leak the signing key.

A Hermine/Raccoon signature is `z = y + c·s` with the mask `y` sampled uniformly over a WIDE support `S`
(the noise-flooding of `Smudging`). Its distribution is therefore `unif (S.image (· + c·s))` — the mask
distribution *shifted* by `c·s`. The key insight: a SIMULATOR that knows nothing about `s` can output
`unif S`, and by the smudging lemma the real signature is within statistical distance `‖c·s‖/M` of that.
So the signature is **ε-simulatable without the secret**, `ε = ‖c·s‖/M` — the standard key-hiding /
honest-verifier-zero-knowledge guarantee. Make the noise `M` dwarf the shift budget and `ε` is
negligible: the key does not leak, no matter how many signatures are published.

`signature_hides_secret` is that statement; `key_hiding_two_secrets` upgrades it (via the triangle
inequality) to "two different secrets produce indistinguishable signatures," the un-linkability form.
-/
import Dregg2.Crypto.Smudging
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Dregg2.Crypto.HermineHiding

open Dregg2.Crypto.Smudging

variable {α : Type*} [DecidableEq α]

/-- **The triangle inequality for statistical distance** — `statDist` is a metric. -/
theorem statDist_triangle (s : Finset α) (p q r : α → ℚ) :
    statDist s p r ≤ statDist s p q + statDist s q r := by
  have hsum : ∑ x ∈ s, |p x - r x| ≤ ∑ x ∈ s, (|p x - q x| + |q x - r x|) :=
    Finset.sum_le_sum (fun x _ => abs_sub_le (p x) (q x) (r x))
  rw [Finset.sum_add_distrib] at hsum
  unfold statDist
  linarith

/-- **Symmetry of statistical distance** — `statDist` is symmetric (`|p − q| = |q − p|`). -/
theorem statDist_comm (s : Finset α) (p q : α → ℚ) : statDist s p q = statDist s q p := by
  unfold statDist
  congr 1
  exact Finset.sum_congr rfl (fun x _ => abs_sub_comm _ _)

/-- **Telescoping (generalized) triangle inequality.** For any walk `f 0, f 1, …, f m` of mass
functions, `statDist (f 0) (f m)` is at most the sum of the adjacent-step distances. Proved by
induction on `m` from `statDist_triangle`. This is the telescope leg of the product-hybrid argument. -/
theorem statDist_telescope (s : Finset α) (f : ℕ → α → ℚ) (m : ℕ) :
    statDist s (f 0) (f m) ≤ ∑ k ∈ Finset.range m, statDist s (f k) (f (k + 1)) := by
  induction m with
  | zero => simp [statDist]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have htri := statDist_triangle s (f 0) (f m) (f (m + 1))
    linarith [ih]

/-- **Product-hybrid TV subadditivity (`statDist_pi_le_sum`).** For `n` component distributions
`P i, Q i : β → ℚ` over supports `S i` — each a genuine distribution (nonnegative on its support and
summing to `1`) — the PRODUCT distributions `⊗P = fun x => ∏ i, P i (x i)` and `⊗Q` over the product
support `Fintype.piFinset S` satisfy `statDist (⊗P) (⊗Q) ≤ ∑ᵢ statDist (P i) (Q i)`.

**The hybrid argument.** The hybrids `hyb k = P₁⊗…⊗Q_{<k}⊗P_{≥k}` interpolate `hyb 0 = ⊗P` to
`hyb n = ⊗Q`, switching one coordinate at a time. Adjacent hybrids `hyb k`, `hyb (k+1)` differ ONLY in
coordinate `k`: writing the shared tail `R = ∏_{i ≠ k} (·)`, we get `hyb k x = P k (x k)·R` and
`hyb (k+1) x = Q k (x k)·R`, so `|hyb k x − hyb (k+1) x| = R·|P k (x k) − Q k (x k)|` (`R ≥ 0`). Summing
over the product support and refactoring by `Finset.prod_univ_sum`, the other coordinates' marginals sum
to `1` and factor out, giving the SINGLE-COORDINATE EQUALITY
`statDist (hyb k) (hyb (k+1)) = statDist (S k) (P k) (Q k)`. Telescoping with `statDist_telescope`
(the triangle inequality summed) yields the bound. A standard probability lemma — no hardness carrier. -/
theorem statDist_pi_le_sum {n : ℕ} {β : Type*} [DecidableEq β]
    (S : Fin n → Finset β) (P Q : Fin n → β → ℚ)
    (hP0 : ∀ i, ∀ j ∈ S i, 0 ≤ P i j) (hQ0 : ∀ i, ∀ j ∈ S i, 0 ≤ Q i j)
    (hP1 : ∀ i, ∑ j ∈ S i, P i j = 1) (hQ1 : ∀ i, ∑ j ∈ S i, Q i j = 1) :
    statDist (Fintype.piFinset S) (fun x => ∏ i, P i (x i)) (fun x => ∏ i, Q i (x i))
      ≤ ∑ i, statDist (S i) (P i) (Q i) := by
  classical
  -- the hybrid family: leading `k` coordinates already switched to `Q`, the rest still `P`.
  set hyb : ℕ → (Fin n → β) → ℚ :=
    fun k x => ∏ i : Fin n, (if (i : ℕ) < k then Q i (x i) else P i (x i)) with hyb_def
  have hyb0 : hyb 0 = fun x => ∏ i, P i (x i) := by
    funext x; exact Finset.prod_congr rfl (fun i _ => by simp)
  have hybn : hyb n = fun x => ∏ i, Q i (x i) := by
    funext x; exact Finset.prod_congr rfl (fun i _ => by simp [i.isLt])
  -- SINGLE-COORDINATE STEP: adjacent hybrids differ only in coordinate `k`, and the distance is
  -- exactly the per-coordinate statDist (the other marginals sum to 1 and factor out).
  have hstep : ∀ (k : ℕ) (hk : k < n),
      statDist (Fintype.piFinset S) (hyb k) (hyb (k + 1))
        = statDist (S ⟨k, hk⟩) (P ⟨k, hk⟩) (Q ⟨k, hk⟩) := by
    intro k hk
    set k' : Fin n := ⟨k, hk⟩ with hk'
    -- the reassembled per-coordinate integrand: `|P k' − Q k'|` at `k'`, the hybrid factor elsewhere.
    set v : Fin n → β → ℚ :=
      fun i j => if i = k' then |P i j - Q i j| else (if (i : ℕ) < k then Q i j else P i j) with hv
    -- pointwise: `|hyb k x − hyb (k+1) x| = ∏ i, v i (x i)` on the product support.
    have key : ∀ x ∈ Fintype.piFinset S, |hyb k x - hyb (k + 1) x| = ∏ i, v i (x i) := by
      intro x hx
      have hxmem : ∀ i, x i ∈ S i := fun i => Fintype.mem_piFinset.mp hx i
      -- the shared tail product `R = ∏_{i ≠ k'} (hybrid factor)`, and it is `≥ 0`.
      set R : ℚ := ∏ i ∈ Finset.univ.erase k', (if (i : ℕ) < k then Q i (x i) else P i (x i)) with hR
      have hR0 : 0 ≤ R := by
        apply Finset.prod_nonneg
        intro i _
        by_cases hik : (i : ℕ) < k
        · simp only [hik, if_true]; exact hQ0 i (x i) (hxmem i)
        · simp only [hik, if_false]; exact hP0 i (x i) (hxmem i)
      -- hyb k x = P k' (x k') * R
      have hAk : hyb k x = P k' (x k') * R := by
        simp only [hyb_def]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k')]
        congr 1
        simp [hk']
      -- hyb (k+1) x = Q k' (x k') * R
      have hAk1 : hyb (k + 1) x = Q k' (x k') * R := by
        simp only [hyb_def]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k')]
        rw [show (if ((k' : ℕ) < k + 1) then Q k' (x k') else P k' (x k')) = Q k' (x k') by
          simp [hk']]
        congr 1
        -- the tail products agree factorwise (coordinates `≠ k'` see the same branch)
        apply Finset.prod_congr rfl
        intro i hi
        have hine : i ≠ k' := Finset.ne_of_mem_erase hi
        have hival : (i : ℕ) ≠ k := fun h => hine (Fin.ext (by simp [hk', h]))
        by_cases hik : (i : ℕ) < k
        · simp [hik, Nat.lt_succ_of_lt hik]
        · have : ¬ (i : ℕ) < k + 1 := by omega
          simp [hik, this]
      -- ∏ i, v i (x i) = |P k' (x k') − Q k' (x k')| * R
      have hV : ∏ i, v i (x i) = |P k' (x k') - Q k' (x k')| * R := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k')]
        congr 1
        · simp [hv, hk']
        · apply Finset.prod_congr rfl
          intro i hi
          have hine : i ≠ k' := Finset.ne_of_mem_erase hi
          simp [hv, hine]
      rw [hAk, hAk1, hV, ← sub_mul, abs_mul, abs_of_nonneg hR0]
    -- assemble the sum, factor via `prod_univ_sum`, collapse the unit marginals.
    unfold statDist
    congr 1
    rw [Finset.sum_congr rfl key]
    rw [← Finset.prod_univ_sum S v]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k')]
    have htail : ∏ i ∈ Finset.univ.erase k', (∑ j ∈ S i, v i j) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hine : i ≠ k' := Finset.ne_of_mem_erase hi
      have : (∑ j ∈ S i, v i j) = ∑ j ∈ S i, (if (i : ℕ) < k then Q i j else P i j) :=
        Finset.sum_congr rfl (fun j _ => by simp [hv, hine])
      rw [this]
      by_cases hik : (i : ℕ) < k
      · simp only [hik, if_true]; exact hQ1 i
      · simp only [hik, if_false]; exact hP1 i
    rw [htail, mul_one]
    exact Finset.sum_congr rfl (fun j _ => by simp [hv, hk'])
  -- telescope + reindex `range n → Fin n`.
  calc statDist (Fintype.piFinset S) (fun x => ∏ i, P i (x i)) (fun x => ∏ i, Q i (x i))
      = statDist (Fintype.piFinset S) (hyb 0) (hyb n) := by rw [hyb0, hybn]
    _ ≤ ∑ k ∈ Finset.range n, statDist (Fintype.piFinset S) (hyb k) (hyb (k + 1)) :=
        statDist_telescope _ hyb n
    _ = ∑ k ∈ Finset.range n,
          (fun m => if h : m < n then statDist (S ⟨m, h⟩) (P ⟨m, h⟩) (Q ⟨m, h⟩) else 0) k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k < n := Finset.mem_range.mp hk
        rw [hstep k hkn]; simp [hkn]
    _ = ∑ i : Fin n, statDist (S i) (P i) (Q i) := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun m => if h : m < n then statDist (S ⟨m, h⟩) (P ⟨m, h⟩) (Q ⟨m, h⟩) else 0) n]
        exact Finset.sum_congr rfl (fun i _ => by simp)

/-- **KEY-HIDING.** A signature `z = y + c·s` with mask `y ~ unif S` (noise-flooded over the wide support
`S`) and secret-shift `σ = (· + c·s)` has distribution `unif (S.image σ)`. A simulator with NO secret
outputs `unif S`; the real signature is within statistical distance `B/M` of it, where `B` bounds how far
the shift moves the support and `M = |S|` is the noise width. So the signature is `B/M`-SIMULATABLE
without the secret — it leaks at most `B/M` about `s`, negligible once `M ≫ B`. -/
theorem signature_hides_secret (S : Finset α) (σ : α → α) (hσ : Function.Injective σ)
    (hpos : 0 < S.card) (B : ℕ) (hB : (S \ S.image σ).card ≤ B) :
    statDist (S ∪ S.image σ) (unif S) (unif (S.image σ)) ≤ (B : ℚ) / (S.card : ℚ) :=
  smudge_bound B (Finset.card_image_of_injective S hσ).symm hpos hB

/-- **Concrete key-hiding (non-vacuous).** Over `ℤ` with a width-10 mask and a shift of `1` (`‖c·s‖ = 1`),
the signature leaks at most `1/10` — a real bound, decide-checked. As the noise width `M` grows the
leakage `1/M` shrinks; that is noise-flooding driving the key-hiding negligible. -/
theorem concrete_signature_hides :
    statDist ((Finset.Ico (0:ℤ) 10) ∪ ((Finset.Ico (0:ℤ) 10).image (· + 1)))
      (unif (Finset.Ico (0:ℤ) 10)) (unif ((Finset.Ico (0:ℤ) 10).image (· + 1)))
      ≤ (1 : ℚ) / 10 := by
  have hinj : Function.Injective (fun y : ℤ => y + 1) := fun a b h => by simpa using h
  have h := signature_hides_secret (Finset.Ico (0:ℤ) 10) (· + 1) hinj (by decide) 1
    (by decide)
  simpa using h

/-- **Un-linkability (key-hiding across secrets).** Two secrets, via their shifts `σ₀`, `σ₁`, produce
signature distributions each within `B/M` of the SAME secret-independent `unif S`, hence within `2B/M` of
EACH OTHER (triangle). So an adversary cannot tell which secret signed — the signatures are
indistinguishable up to `2B/M`. (Stated over the common support `s ⊇ S ∪ image σ₀ ∪ image σ₁`, with each
half's smudging bound supplied.) -/
theorem key_hiding_two_secrets (s : Finset α) (S : Finset α) (σ₀ σ₁ : α → α) (B : ℕ) (M : ℕ)
    (hM : 0 < M)
    (h0 : statDist s (unif (S.image σ₀)) (unif S) ≤ (B : ℚ) / (M : ℚ))
    (h1 : statDist s (unif S) (unif (S.image σ₁)) ≤ (B : ℚ) / (M : ℚ)) :
    statDist s (unif (S.image σ₀)) (unif (S.image σ₁)) ≤ (2 * B : ℚ) / (M : ℚ) := by
  calc statDist s (unif (S.image σ₀)) (unif (S.image σ₁))
      ≤ statDist s (unif (S.image σ₀)) (unif S) + statDist s (unif S) (unif (S.image σ₁)) :=
        statDist_triangle s _ _ _
    _ ≤ (B : ℚ) / (M : ℚ) + (B : ℚ) / (M : ℚ) := add_le_add h0 h1
    _ = (2 * B : ℚ) / (M : ℚ) := by ring

#assert_axioms statDist_triangle
#assert_axioms statDist_comm
#assert_axioms statDist_telescope
#assert_axioms statDist_pi_le_sum
#assert_axioms signature_hides_secret
#assert_axioms concrete_signature_hides
#assert_axioms key_hiding_two_secrets

end Dregg2.Crypto.HermineHiding
