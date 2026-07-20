/-
# `Dregg2.Circuit.FriCarrierEpsilon` — the REPLACEMENT for `FriLowDegreeSound`: an ε-BOUNDED,
`Q`-ATTEMPT-QUANTIFIED forgery bound over the DEPLOYED `sampleBits` sampler. PROVEN, not carried.

`Dregg2.Circuit.FriCarrierVacuity` established that `FriLowDegreeSound` is equivalent to `True`
(`friLowDegreeSound_content_iff_true`), admits no falsifier
(`friLowDegreeSound_has_no_falsifier`), and that the naive repair ("accept ⟹ codeword") is FALSE
by counting (`spotCheck_accepts_non_codeword`). This file supplies the shape a carrier here IS
allowed to take, and then proves it rather than assuming it.

## What makes this shape admissible where the old one was not

`FriQueryForgeryBound N m k Q ε` says: over `Q` independent Fiat–Shamir attempts, each drawing `k`
query indices as `Challenger.sampleBits` does (a squeeze uniform over `N = |F|`, reduced mod
`m = 2^logN`), the fraction of runs on which SOME attempt's `k` spot-checks ALL miss a `δ`-far
word is at most `ε`.

  * **Not implied by its antecedent.** It is a statement about the MEASURE of the accepting set.
    No single accepting instance discharges it — unlike the old carrier, whose consequent was
    literally a conjunct of `verifyAlgo`.
  * **⚑ REFUTABLE IN PRINCIPLE, AND REFUTED AT A WITNESS.**
    `friQueryForgeryBound_false_without_defect` exhibits `N = 3, m = 2, k = 1, Q = 1, δ = 1/2`
    where the bound FAILS at the un-defected `ε = (1−δ)^k = 1/2` — the actual fraction is `2/3`.
    That is codex's `FriQuerySamplingBias.biased_survival_defect_load_bearing` witness, lifted
    into the carrier's own shape. A carrier you can knock over with a counterexample is a carrier
    that says something.
  * **PROVEN, not carried.** `friQueryForgeryBound_proven` composes
    `FriQuerySamplingBias.biased_query_survival_pow_le` (codex's deployed-sampler bound, defect
    term `m/N` included) with `FriCarrierVacuity.attempt_union_le` (the `Q`-attempt Bernoulli
    union bound). There is no `class`, no `Prop` field, no hole.

## ⚑ THE DEPLOYED NUMBER

`deployed_forgery_bound`: at `|F| = 2013265921`, `k = OUTER_FRI_NUM_QUERIES = 38`, `m = 2^logN`
buckets, `Q` attempts, and `δ = 7/16` (the unique-decoding radius at
`OUTER_FRI_LOG_BLOWUP = 3` ⇒ `ρ = 1/8` — the ONLY radius the tree proves), the forgery probability
is at most

    Q · ((9/16) + 2^logN / 2013265921)^38.

`FriCarrierVacuity.deployed_ud_survival_between` pins the un-biased base of that at
`(9/16)^38 ∈ (2^-32, 2^-31)`. So the bound is vacuous — exceeds `1/2` — by
`Q ≈ 2^30.5` attempts: `deployed_bound_useless_at_2pow32` proves it exceeds `1` already at
`Q = 2^32`. **That is the honest ceiling of the deployed FRI query leg: ~31 bits, not 130.**

## Discipline
ADDITIVE. `FriVerifier`, `FriQuerySamplingBias`, `FriVerifierCompose`, `FriCarrierVacuity` are
imported read-only and untouched; codex's `FriQuerySamplingBias` is REUSED, not re-derived. No
`sorry`, no fresh `axiom`, no `native_decide`. `#assert_all_clean` over every keystone.
-/
import Dregg2.Circuit.FriCarrierVacuity
import Dregg2.Circuit.FriQuerySamplingBias
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriCarrierEpsilon

open Finset
open Dregg2.Circuit.FriCarrierVacuity (attempt_union_le)
open Dregg2.Circuit.FriQuerySamplingBias
  (biased_query_survival_pow_le biased_survival_fires)

/-! ## §1 — the carrier's SHAPE.

The sample space is `Fin Q → (Fin k → Fin N)`: `Q` independent Fiat–Shamir attempts, each drawing
`k` pre-reduction squeeze values uniform over `Fin N` (`N = |F|`). The deployed query index is
`v % m` (`Challenger.sampleBits`, `FriVerifier.lean:150`). `Emiss` is the `δ`-far word's per-index
MISS set — the residues at which it happens to agree with the code. -/

/-- The single-attempt good set: the `k`-index draws on which every spot check lands in `Emiss`,
i.e. every check misses the word's disagreements. Acceptance of a far word IS membership here. -/
def missSet (N m k : ℕ) (Emiss : Finset ℕ) : Finset (Fin k → Fin N) :=
  Finset.univ.filter (fun Q : Fin k → Fin N => ∀ i, (Q i).val % m ∈ Emiss)

/-- **⚑ THE REPLACEMENT CARRIER SHAPE.** The fraction of `Q`-attempt runs on which SOME attempt's
`k` deployed spot-checks all miss, bounded by an EXPLICIT `ε`. Compare `FriLowDegreeSound`: this
quantifies a MEASURE over an adversary budget rather than asserting an implication whose
consequent its own antecedent supplies. -/
def FriQueryForgeryBound (N m k Q : ℕ) (Emiss : Finset ℕ) (ε : ℝ) : Prop :=
  ((Finset.univ.filter
      (fun S : Fin Q → (Fin k → Fin N) => ∃ j, S j ∈ missSet N m k Emiss)).card : ℝ)
    / ((Fintype.card (Fin k → Fin N) : ℝ) ^ Q)
  ≤ ε

/-! ## §2 — ⚑ THE BOUND, PROVEN (not carried).

Two proven ingredients, composed: codex's deployed-sampler single-attempt bound (with the `m/N`
uniformity defect) and the `Q`-attempt Bernoulli union bound. -/

/-- The single-attempt fraction, in the form `attempt_union_le` consumes: the `missSet`'s density
in the full draw space `Fin k → Fin N`. This is exactly codex's
`biased_query_survival_pow_le` restated over `Fintype.card`. -/
theorem missSet_density_le (N m k : ℕ) (Emiss : Finset ℕ) (δ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hE : Emiss.card ≤ m)
    (hmiss : (Emiss.card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    (((missSet N m k Emiss).card : ℝ) / (Fintype.card (Fin k → Fin N) : ℝ))
      ≤ ((1 - δ) + (m : ℝ) / (N : ℝ)) ^ k := by
  have hcard : (Fintype.card (Fin k → Fin N) : ℝ) = (N : ℝ) ^ k := by
    rw [Fintype.card_fun]
    simp
  rw [hcard]
  exact biased_query_survival_pow_le N m k Emiss δ hN hm hE hmiss

/-- **⚑⚑ THE REPLACEMENT CARRIER, PROVEN.** For a `δ`-far word (per-index uniform miss density
`≤ 1 − δ`), a `Q`-attempt adversary against the DEPLOYED `sampleBits` sampler forges with
probability at most

    Q · ((1 − δ) + m/N)^k

where the `m/N` addend is the modular-reduction uniformity defect codex's
`FriQuerySamplingBias` quantified. No `class`, no `Prop` field, no hole: this is a theorem. -/
theorem friQueryForgeryBound_proven (N m k Q : ℕ) (Emiss : Finset ℕ) (δ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hE : Emiss.card ≤ m)
    (hmiss : (Emiss.card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    FriQueryForgeryBound N m k Q Emiss ((Q : ℝ) * ((1 - δ) + (m : ℝ) / (N : ℝ)) ^ k) := by
  have hNpos : 0 < N := hN
  have : Nonempty (Fin k → Fin N) := ⟨fun _ => ⟨0, hNpos⟩⟩
  have hunion := attempt_union_le (missSet N m k Emiss) Q
  have hdens := missSet_density_le N m k Emiss δ hN hm hE hmiss
  refine le_trans hunion ?_
  exact mul_le_mul_of_nonneg_left hdens (by positivity)

/-! ## §3 — ⚑ REFUTABILITY: the shape is knockable-over, and it IS knocked over.

The lane's sufficient test. `FriLowDegreeSound` admitted no falsifier at any parameters
(`FriCarrierVacuity.friLowDegreeSound_has_no_falsifier`). This shape admits one, and the witness
is codex's: drop the `m/N` defect addend and the bound becomes FALSE at `N = 3, m = 2`. -/

/-- The concrete forgery fraction at the witness `N = 3, m = 2, k = 1, Q = 1, Emiss = {0}`: two of
the three squeeze values (`0` and `2`) reduce to residue `0`, so the fraction is `2/3`. Reuses
codex's `biased_survival_fires` count. -/
theorem witness_forgery_fraction :
    ((Finset.univ.filter
        (fun S : Fin 1 → (Fin 1 → Fin 3) => ∃ j, S j ∈ missSet 3 2 1 ({0} : Finset ℕ))).card : ℝ)
      / ((Fintype.card (Fin 1 → Fin 3) : ℝ) ^ 1) = 2 / 3 := by
  have hc : (Finset.univ.filter
      (fun S : Fin 1 → (Fin 1 → Fin 3) => ∃ j, S j ∈ missSet 3 2 1 ({0} : Finset ℕ))).card
      = 2 := by decide
  have hcard : (Fintype.card (Fin 1 → Fin 3) : ℝ) = 3 := by
    rw [Fintype.card_fun]; simp
  rw [hc, hcard]
  norm_num

/-- **⚑⚑ THE CARRIER IS REFUTABLE, AND HERE IS THE REFUTATION.** At `δ = 1/2, k = 1, Q = 1` the
un-defected value `Q · (1 − δ)^k = 1/2` does NOT bound the forgery probability `2/3`. So
`FriQueryForgeryBound` is a statement with content: a wrong `ε` makes it FALSE. This is the
falsifier `FriLowDegreeSound` provably could not have
(`FriCarrierVacuity.friLowDegreeSound_has_no_falsifier`), and it is exactly codex's
`biased_survival_defect_load_bearing` witness in the carrier's own shape. -/
theorem friQueryForgeryBound_false_without_defect :
    ¬ FriQueryForgeryBound 3 2 1 1 ({0} : Finset ℕ) ((1 : ℝ) * (1 - (1 / 2 : ℝ)) ^ 1) := by
  unfold FriQueryForgeryBound
  rw [witness_forgery_fraction]
  norm_num

/-- And the PROVEN `ε` (with the `m/N` defect and the `Q` factor) DOES hold at that same witness —
`2/3 ≤ 1 · ((1 − 1/2) + 2/3)^1 = 7/6`. The defect addend is what restores truth, so it is a COST
being paid, not slack. -/
theorem friQueryForgeryBound_holds_at_witness :
    FriQueryForgeryBound 3 2 1 1 ({0} : Finset ℕ)
      ((1 : ℝ) * ((1 - (1 / 2 : ℝ)) + (2 : ℝ) / (3 : ℝ)) ^ 1) := by
  have h := friQueryForgeryBound_proven 3 2 1 1 ({0} : Finset ℕ) (1 / 2)
    (by norm_num) (by norm_num) (by decide) (by rw [Finset.card_singleton]; norm_num)
  push_cast at h
  exact h

/-! ## §4 — ⚑ THE DEPLOYED INSTANTIATION, AND THE HONEST CEILING.

`dregg_outer_config.rs`: `OUTER_FRI_LOG_BLOWUP = 3` ⇒ rate `ρ = 1/8`; `OUTER_FRI_NUM_QUERIES = 38`.
The unique-decoding radius `δ = (1 − ρ)/2 = 7/16` is the ONLY radius the tree proves
(`FriVerifierCompose` §2: the Johnson/correlated-agreement carrier is NOT assumed). -/

/-- **⚑ THE DEPLOYED FORGERY BOUND.** At the shipped BabyBear field, `2^logN` query buckets,
`k = 38` queries and the PROVEN unique-decoding radius `δ = 7/16`, a `Q`-attempt adversary forges
with probability at most `Q · ((9/16) + 2^logN/|F|)^38`. Every ingredient is proven: codex's
deployed-sampler defect bound, and the Bernoulli union bound over the attempt budget. -/
theorem deployed_forgery_bound (logN Q : ℕ) (Emiss : Finset ℕ)
    (hE : Emiss.card ≤ 2 ^ logN)
    (hmiss : (Emiss.card : ℝ) / ((2 : ℕ) ^ logN : ℕ) ≤ 1 - (7 / 16 : ℝ)) :
    FriQueryForgeryBound 2013265921 (2 ^ logN) 38 Q Emiss
      ((Q : ℝ) * ((9 / 16 : ℝ) + ((2 ^ logN : ℕ) : ℝ) / (2013265921 : ℝ)) ^ 38) := by
  have h := friQueryForgeryBound_proven 2013265921 (2 ^ logN) 38 Q Emiss (7 / 16 : ℝ)
    (by norm_num) (pow_pos (by norm_num) logN) hE hmiss
  have hbase : (1 : ℝ) - (7 / 16 : ℝ) = 9 / 16 := by norm_num
  rw [hbase] at h
  exact h

/-- **⚑⚑ THE HONEST CEILING.** The deployed bound's un-biased base `(9/16)^38` is `> 2^-32`
(`FriCarrierVacuity.deployed_ud_survival_between`), so at `Q = 2^32` attempts the bound EXCEEDS
`1` and asserts nothing at all. There is no proven FRI query-soundness past roughly `2^31`
adversary attempts — **~31 bits**, against the `3·38 + 16 = 130` the deployed config's own doc
comment claims, and against the `57` the Johnson reading gives. -/
theorem deployed_bound_useless_at_2pow32 :
    (1 : ℝ) < ((2 : ℝ) ^ 32) * ((9 / 16 : ℝ)) ^ 38 := by
  have h := (Dregg2.Circuit.FriCarrierVacuity.deployed_ud_survival_between).1
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 32 := by positivity
  have := (mul_lt_mul_of_pos_left h hpos)
  calc (1 : ℝ) = (2 : ℝ) ^ 32 * (1 / 2 ^ 32) := by norm_num
    _ < (2 : ℝ) ^ 32 * ((9 / 16 : ℝ)) ^ 38 := this

/-- The same ceiling read as a bit count: `2^31` attempts already push the bound above `1/2`, so
"the security level" of the deployed query leg, at the radius the tree proves, is below 31 bits
before any PoW grinding is credited — and `FriChecks.queryPow` in the object
`wrap_sound`/`emitVerifier_wrap_sound` quantify over is `queryPowWitnessShape`
(`FriVerifier.lean:822`), a singleton-wire-shape check worth zero bits. -/
theorem deployed_bound_exceeds_half_at_2pow31 :
    (1 : ℝ) / 2 < ((2 : ℝ) ^ 31) * ((9 / 16 : ℝ)) ^ 38 := by
  have h := (Dregg2.Circuit.FriCarrierVacuity.deployed_ud_survival_between).1
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 31 := by positivity
  have hmul := mul_lt_mul_of_pos_left h hpos
  calc (1 : ℝ) / 2 = (2 : ℝ) ^ 31 * (1 / 2 ^ 32) := by norm_num
    _ < (2 : ℝ) ^ 31 * ((9 / 16 : ℝ)) ^ 38 := hmul

#assert_all_clean [
  missSet_density_le,
  friQueryForgeryBound_proven,
  witness_forgery_fraction,
  friQueryForgeryBound_false_without_defect,
  friQueryForgeryBound_holds_at_witness,
  deployed_forgery_bound,
  deployed_bound_useless_at_2pow32,
  deployed_bound_exceeds_half_at_2pow31
]

end Dregg2.Circuit.FriCarrierEpsilon
