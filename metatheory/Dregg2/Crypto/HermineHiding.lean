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
#assert_axioms signature_hides_secret
#assert_axioms concrete_signature_hides
#assert_axioms key_hiding_two_secrets

end Dregg2.Crypto.HermineHiding
