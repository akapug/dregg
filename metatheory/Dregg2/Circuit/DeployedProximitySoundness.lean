/-
# Dregg2.Circuit.DeployedProximitySoundness — link A: the assembled DEPLOYED
proximity-soundness statement.

**Honest scope (first sentence).** This module COMPOSES two committed results — the
query-sampling counting bound `FriQuerySoundness.accept_prob_le_of_farN` and the deployed
numeric error `FriQuerySoundness.deployed_query_error_{eq,lt}` — into the single clean
deployed statement: a word `δ = 7/16`-FAR from the deployed rate-`1/8` Reed–Solomon code
passes the deployed `k = 38`-query check on a fraction of samples STRICTLY below `2⁻³¹`
(`far_word_rarely_accepted` generically; `far_word_rarely_accepted_deployed` at the in-tree
deployed-rate BabyBear code `BabyBearFriDeployed.friSetupDeployedRate`). Nothing new is
assumed: every hypothesis of the imported bound is either discharged concretely (the FIRE,
§4: an explicit far word `x ↦ (ωˣ)²` proved `7`-far from EVERY codeword) or carried as an
explicit theorem hypothesis (`hgC`, `hfar` — the honest interface of a soundness statement,
NOT axioms).

**The conclusion shape is a CARD RATIO, faithfully.** `accept_prob_le_of_farN` bounds
`|accepting samples| / N^k` — the counting form of the uniform-independent-query probability
(`FriQuerySoundness §1` proves this model is FAITHFUL to the shipped verifier's
with-replacement sampling). No probability measure is fabricated here; the ratio IS the
probability under the uniform distribution on `Ω = (Fin 38 → L)`, stated as the ratio.

**Deployed parameters, READ not invented** (cross-pinned in §3 to `DeployedUdrRegime`):
`log_blowup = 3` ⇔ rate `ρ = 1/8`, `num_queries = 38` (`circuit/src/plonky3_prover.rs:96-100`
via `DeployedUdrRegime.plonky3ProverParams`), `δ = 7/16 = (1 − ρ)/2` the unique-decoding
radius (`DeployedUdrRegime.deployed_delta_eq_udr`). On the size-`16` deployed-rate domain the
absolute radius is exactly `δ·16 = 7` (`DeployedUdrRegime.deployed_udr_scaled_16`), so
"`δ`-far" is the integer hypothesis `farN C 7`.

**The operational reading** (`accept_soundness_deployed`): for ANY oracle `f` and any claimed
codeword `g ∈ C`, EITHER `f` is `7/16`-close to the deployed code, OR the `38`-query check
accepts `f` against `g` on `< 2⁻³¹` of the sample space — FRI acceptance certifies proximity
except with soundness error `(1 − 7/16)³⁸ < 2⁻³¹`. Both disjuncts are exercised: the far FIRE
word forces the right disjunct (`deployed_soundness_fires`), and the honest codeword is
accepted on the WHOLE sample space (`honest_accept_ratio_one` — ratio exactly `1`), so the
bound constrains far words only, as it must.
-/
import Mathlib.Tactic
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.BabyBearFriDeployed
import Dregg2.Circuit.DeployedUdrRegime
import Dregg2.Tactics

namespace Dregg2.Circuit.DeployedProximitySoundness

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriQuerySoundness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-! ## §1. The composed generic bound at the deployed `δ = 7/16`, `k = 38`.

`accept_prob_le_of_farN` (committed) gives `≤ (1 − δ)^k` for a `farN`-far word against any
claimed codeword; `deployed_query_error_eq/lt` (committed) give `(1 − 7/16)³⁸ = (9/16)³⁸ <
2⁻³¹`. The chain is `≤` then `<`, so the composed bound is STRICT. -/

/-- **Composed deployed-parameter bound (generic domain).** If `f` is `d`-FAR from the code
`C` (no codeword within Hamming distance `d`) and `d` is at least `(7/16)·|ι|` — i.e. `f` is
`δ = 7/16`-far in relative distance — then against ANY claimed codeword `g ∈ C` the deployed
`38` uniform independent queries all accept on a fraction of samples STRICTLY below `2⁻³¹`.
This is `accept_prob_le_of_farN` at `k = 38, δ = 7/16` chained through
`deployed_query_error_eq` and `deployed_query_error_lt`. The conclusion is the card ratio —
the acceptance probability under the uniform sample distribution, stated faithfully in
counting form. -/
theorem far_word_rarely_accepted {F : Type*} [Field F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Submodule F (ι → F)} {f g : ι → F} {d : ℕ}
    (hN : 0 < Fintype.card ι) (hgC : g ∈ C) (hfar : farN C d f)
    (hδd : (7 / 16 : ℝ) * (Fintype.card ι : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin 38 → ι => Accepts f g Q)).card : ℝ)
        / ((Fintype.card ι : ℝ) ^ 38)
      < 1 / 2 ^ 31 := by
  refine lt_of_le_of_lt
    (accept_prob_le_of_farN (C := C) 38 hN (by norm_num) hgC hfar hδd) ?_
  rw [deployed_query_error_eq]
  exact deployed_query_error_lt

/-- **The honest operational reading (generic domain).** For ANY oracle `f` and claimed
codeword `g ∈ C`: either `f` is `d`-CLOSE to the code (the proximity the acceptance is meant
to certify), or the `38`-query acceptance event has mass `< 2⁻³¹`. Acceptance certifies
`d`-proximity except with soundness error `(1 − 7/16)³⁸ < 2⁻³¹`. (Classical dichotomy on
`closeN`; the far branch is `far_word_rarely_accepted`.) -/
theorem accept_certifies_proximity {F : Type*} [Field F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Submodule F (ι → F)} {f g : ι → F} {d : ℕ}
    (hN : 0 < Fintype.card ι) (hgC : g ∈ C)
    (hδd : (7 / 16 : ℝ) * (Fintype.card ι : ℝ) ≤ (d : ℝ)) :
    closeN C d f ∨
      ((Finset.univ.filter (fun Q : Fin 38 → ι => Accepts f g Q)).card : ℝ)
          / ((Fintype.card ι : ℝ) ^ 38)
        < 1 / 2 ^ 31 := by
  by_cases hc : closeN C d f
  · exact Or.inl hc
  · exact Or.inr (far_word_rarely_accepted hN hgC hc hδd)

/-! ## §2. The DEPLOYED instantiation: rate-`1/8` BabyBear code, `|L| = 16`, radius `7`.

`friSetupDeployedRate.C` is the in-tree deployed-rate code: degree-`< 2` Reed–Solomon on the
size-`16` BabyBear domain `{ω₁₆^j}` — rate `2/16 = 1/8`, exactly the shipped
`log_blowup = 3`. At `N = 16` the deployed relative radius `δ = 7/16` is the integer `7`
(`DeployedUdrRegime.deployed_udr_scaled_16`), so `farN C 7` — no codeword within Hamming
distance `7` — is precisely "`7/16`-far". -/

/-- **DEPLOYED PROXIMITY SOUNDNESS (link A).** A word `7/16`-FAR from the deployed rate-`1/8`
BabyBear Reed–Solomon code (`farN friSetupDeployedRate.C 7` — beyond the deployed radius
`δ·16 = 7`) passes the deployed `38`-query check against any claimed codeword `g ∈ C` on
STRICTLY less than `2⁻³¹` of the `16³⁸` samples. -/
theorem far_word_rarely_accepted_deployed {f g : Fin (2 ^ 4) → BabyBear}
    (hgC : g ∈ friSetupDeployedRate.C) (hfar : farN friSetupDeployedRate.C 7 f) :
    ((Finset.univ.filter (fun Q : Fin 38 → Fin (2 ^ 4) => Accepts f g Q)).card : ℝ)
        / (16 : ℝ) ^ 38
      < 1 / 2 ^ 31 := by
  have h := far_word_rarely_accepted (C := friSetupDeployedRate.C) (d := 7)
    (by norm_num) hgC hfar (by norm_num)
  have hcard : ((Fintype.card (Fin (2 ^ 4)) : ℕ) : ℝ) = 16 := by norm_num
  rwa [hcard] at h

/-- **The honest operational reading, DEPLOYED.** For any oracle `f` on the deployed domain
and any claimed codeword `g ∈ C`: either `f` is within the deployed unique-decoding radius
`7 = (7/16)·16` of the code, or the deployed `38`-query check accepts on `< 2⁻³¹` of the
sample space. FRI acceptance at the shipped parameters certifies `7/16`-proximity except
with soundness error `(1 − 7/16)³⁸ < 2⁻³¹`. -/
theorem accept_soundness_deployed {f g : Fin (2 ^ 4) → BabyBear}
    (hgC : g ∈ friSetupDeployedRate.C) :
    closeN friSetupDeployedRate.C 7 f ∨
      ((Finset.univ.filter (fun Q : Fin 38 → Fin (2 ^ 4) => Accepts f g Q)).card : ℝ)
          / (16 : ℝ) ^ 38
        < 1 / 2 ^ 31 := by
  by_cases hc : closeN friSetupDeployedRate.C 7 f
  · exact Or.inl hc
  · exact Or.inr (far_word_rarely_accepted_deployed hgC hc)

/-! ## §3. Parameter provenance — the `38`, the `7/16`, and the radius `7` are READ. -/

/-- `k = 38` is the shipped `PROD_FRI_NUM_QUERIES` (`plonky3_prover.rs:99`), via the in-tree
record `DeployedUdrRegime.plonky3ProverParams`. -/
theorem deployed_k_reads_38 : DeployedUdrRegime.plonky3ProverParams.numQueries = 38 :=
  DeployedUdrRegime.prover_numQueries

/-- `δ = 7/16` is the audited deployed proximity parameter — and it EQUALS the rate-`1/8`
unique-decoding radius `(1 − ρ)/2` (committed `deployed_delta_eq_udr`). -/
theorem deployed_delta_reads_udr :
    DeployedUdrRegime.deployedDelta
      = DeployedUdrRegime.udr DeployedUdrRegime.plonky3ProverParams.logBlowup :=
  DeployedUdrRegime.deployed_delta_eq_udr

/-- The integer radius `7` used in §2 is exactly `δ·16` on the size-`16` deployed-rate
domain (committed `deployed_udr_scaled_16`). -/
theorem radius_seven_is_deltaN : DeployedUdrRegime.deployedDelta * ((16 : ℕ) : ℚ) = 7 :=
  DeployedUdrRegime.deployed_udr_scaled_16

/-! ## §4. FIRE — every hypothesis discharged on a concrete far/near pair.

The far word is `fSq : x ↦ (ω₁₆ˣ)²` — the squared point value. A codeword is affine in the
point value `t = ω₁₆ˣ`; if one agreed with `t²` at THREE points it would give the nonzero
quadratic `t² − b·t − a` three distinct roots (the sixteen point values are pairwise distinct
since `ω₁₆` has order 16). So `fSq` agrees with EVERY codeword on `≤ 2` of the 16 points —
Hamming distance `≥ 14 > 7` from all of `C`: genuinely `7/16`-far, with margin. -/

/-- The sixteen point values `ω₁₆^j` are pairwise distinct (kernel check: `ω₁₆` has order
`16`, so `j ↦ ω₁₆^j` is injective on `Fin 16`). -/
theorem omega16_pow_inj :
    ∀ x y : Fin (2 ^ 4), omega16 ^ (x : ℕ) = omega16 ^ (y : ℕ) → x = y := by decide

/-- **The concrete far word**: the squared point value `fSq x = (ω₁₆ˣ)²`. -/
noncomputable def fSq : Fin (2 ^ 4) → BabyBear := fun x => (omega16 ^ (x : ℕ)) ^ 2

/-- **`fSq` is `7`-far from the deployed code** — indeed `≥ 14`-far: any codeword
`a + b·ω₁₆ˣ` agreeing with `fSq` at even THREE of the sixteen (distinct) point values `t`
would satisfy `t² = a + b·t` thrice, forcing `t₁ + t₂ = b = t₁ + t₃` hence `t₂ = t₃` —
contradicting distinctness. So agreement `≤ 2 < 16 − 7`, i.e. disagreement `> 7`, against
EVERY codeword: the `farN` hypothesis of link A holds concretely. -/
theorem fSq_far : farN friSetupDeployedRate.C 7 fSq := by
  rintro ⟨g, hgC, hcard⟩
  obtain ⟨a, b, hg⟩ := hgC
  have h3 : 3 ≤ ((disagree fSq g)ᶜ).card := by
    have h16 : Fintype.card (Fin (2 ^ 4)) = 16 := by norm_num
    rw [Finset.card_compl, h16]
    omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨x₁, x₂, x₃, hx12, hx13, hx23, rfl⟩ := Finset.card_eq_three.mp htcard
  have hagree : ∀ x ∈ ({x₁, x₂, x₃} : Finset (Fin (2 ^ 4))),
      (omega16 ^ (x : ℕ)) ^ 2 = a + b * omega16 ^ (x : ℕ) := by
    intro x hx
    have hxc := hts hx
    rw [Finset.mem_compl, mem_disagree, not_not] at hxc
    exact hxc.trans (congrFun hg x)
  have e₁ := hagree x₁ (by simp)
  have e₂ := hagree x₂ (by simp)
  have e₃ := hagree x₃ (by simp)
  have ht12 : omega16 ^ (x₁ : ℕ) ≠ omega16 ^ (x₂ : ℕ) :=
    fun h => hx12 (omega16_pow_inj x₁ x₂ h)
  have ht13 : omega16 ^ (x₁ : ℕ) ≠ omega16 ^ (x₃ : ℕ) :=
    fun h => hx13 (omega16_pow_inj x₁ x₃ h)
  have h12 : omega16 ^ (x₁ : ℕ) + omega16 ^ (x₂ : ℕ) = b :=
    mul_left_cancel₀ (sub_ne_zero.mpr ht12) (by linear_combination e₁ - e₂)
  have h13 : omega16 ^ (x₁ : ℕ) + omega16 ^ (x₃ : ℕ) = b :=
    mul_left_cancel₀ (sub_ne_zero.mpr ht13) (by linear_combination e₁ - e₃)
  have h23 : omega16 ^ (x₂ : ℕ) = omega16 ^ (x₃ : ℕ) := add_left_cancel (h12.trans h13.symm)
  exact hx23 (omega16_pow_inj x₂ x₃ h23)

/-- **FIRE (the far side).** Link A discharged end-to-end on concrete data: the far word
`fSq` against the zero codeword passes the deployed `38`-query check on `< 2⁻³¹` of the
sample space. Derived THROUGH the operational dichotomy (`accept_soundness_deployed`), whose
close branch is refuted by `fSq_far` — every hypothesis concrete, nothing carried. -/
theorem deployed_soundness_fires :
    ((Finset.univ.filter (fun Q : Fin 38 → Fin (2 ^ 4) =>
        Accepts fSq (0 : Fin (2 ^ 4) → BabyBear) Q)).card : ℝ)
        / (16 : ℝ) ^ 38
      < 1 / 2 ^ 31 := by
  rcases accept_soundness_deployed (f := fSq) (Submodule.zero_mem _) with hc | h
  · exact absurd hc fSq_far
  · exact h

/-- **The near side (completeness contrast).** The honest deployed-rate codeword
`fHonestParam 3 ω₁₆ = 2 + 3·ω₁₆ˣ` is accepted by EVERY sample — the soundness bound
constrains far words only. -/
theorem honest_always_accepted (Q : Fin 38 → Fin (2 ^ 4)) :
    Accepts (fHonestParam 3 omega16) (fHonestParam 3 omega16) Q :=
  fun _ => rfl

/-- **The near side, quantified**: the honest codeword's accepting fraction is exactly `1`
(the whole `16³⁸`-point sample space) — against the far word's `< 2⁻³¹`. The two ends of the
dichotomy are `1` versus `< 2⁻³¹`, both computed, neither vacuous. -/
theorem honest_accept_ratio_one :
    ((Finset.univ.filter (fun Q : Fin 38 → Fin (2 ^ 4) =>
        Accepts (fHonestParam 3 omega16) (fHonestParam 3 omega16) Q)).card : ℝ)
        / (16 : ℝ) ^ 38 = 1 := by
  have huniv : (Finset.univ.filter (fun Q : Fin 38 → Fin (2 ^ 4) =>
      Accepts (fHonestParam 3 omega16) (fHonestParam 3 omega16) Q)) = Finset.univ :=
    Finset.filter_true_of_mem (fun Q _ => fun _ => rfl)
  rw [huniv, Finset.card_univ]
  have hcard : Fintype.card (Fin 38 → Fin (2 ^ 4)) = 16 ^ 38 := by
    rw [Fintype.card_fun]
    norm_num
  rw [hcard]
  norm_num

/-! ## §5. Axiom hygiene — every theorem kernel-clean (standard axioms only). -/

#assert_axioms far_word_rarely_accepted
#assert_axioms accept_certifies_proximity
#assert_axioms far_word_rarely_accepted_deployed
#assert_axioms accept_soundness_deployed
#assert_axioms deployed_k_reads_38
#assert_axioms deployed_delta_reads_udr
#assert_axioms radius_seven_is_deltaN
#assert_axioms omega16_pow_inj
#assert_axioms fSq_far
#assert_axioms deployed_soundness_fires
#assert_axioms honest_always_accepted
#assert_axioms honest_accept_ratio_one

end Dregg2.Circuit.DeployedProximitySoundness
