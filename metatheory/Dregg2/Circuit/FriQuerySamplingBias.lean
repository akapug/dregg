/-
# `Dregg2.Circuit.FriQuerySamplingBias` — the QUANTITATIVE uniformity-defect term for the
deployed `Challenger.sampleBits` query indices.

This is the well-defined next sub-lemma of the FRI extraction floor: **blocker (b)** of
`FriVerifierCompose.friLdtExtractV3_rom_of_legs`
(`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5, Stages 4–5).

## The gap this closes

Stage 5 (`FriVerifierCompose`) proved the deployed query indices are QUALITATIVELY
non-uniform: `babybear_sampleBits_not_balanced` shows `toNat(squeeze) % 2^logN` cannot have
equal-sized residue buckets at any shipped `logN` — because `|F| = 2013265921` is ODD, so
`2^logN ∤ |F|` (`babybear_order_not_divisible_by_two` + pigeonhole). But it left the defect
UNQUANTIFIED. In its own words:

> "the bias is small (`≈ 2^logN / |F|` relative) but it is NONZERO and NO in-tree theorem
> accounts for it. Composing `εQuery` over the oracle therefore needs a uniformity-defect term
> that does not exist."

This file supplies exactly that term. `εQuery` (`FriVerifierQuery.epsilon_query_layer_carried`)
models the `k` query indices as UNIFORM draws `Q : Fin k → κ` and bounds a `δ`-far word's
per-index survival by `(1 − δ)`. The deployed index is `n % m` with `n` a uniform squeeze value
over `N := |F|` and `m := 2^logN = |κ|`. `residue_reduction_prob_le` below bounds, for ANY
residue event `E : Finset ℕ`,

    Pr_{n unif range N}[ n % m ∈ E ]  ≤  |E| / m  +  m / N.

The first addend is the uniform probability `εQuery` already uses; the SECOND, `m / N =
2^logN / |F|`, IS the uniformity-defect term (`babybear_query_bias_le`). Taking `E` the per-index
MISS set (`|E| = m − |D|`, uniform miss `= 1 − δ`) upgrades the deployed per-index survival to
`(1 − δ) + 2^logN/|F|`, so a bias-aware `εQuery` composes as `L/|F| + ((1−δ) + 2^logN/|F|)^k` —
the sampling defect enters as a single explicit addend, PROVEN, not papered.

## Non-vacuity / what makes it false

The defect term is LOAD-BEARING, not slack. `residue_bias_defect_load_bearing` exhibits
`N = 3, m = 2, E = {0}` where `Pr[n % 2 ∈ {0}] = 2/3` STRICTLY EXCEEDS the naive uniform value
`|E|/m = 1/2` — so the bound WITHOUT the `+ m/N` addend is FALSE, and `m/N` is exactly what a
non-dividing `m ∤ N` (the deployed regime) forces. The core counting lemma `residueClassCard_le`
would be false if a residue class held more than `⌊N/m⌋ + 1` elements of `range N` — it cannot,
by the injection `n ↦ n / m` (within one class `n = m·(n/m) + j` is recovered, and `n < N`
forces `n/m ≤ N/m`).

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`,
no `native_decide`.
-/
import Dregg2.Circuit.FriVerifierCompose

set_option autoImplicit false

namespace Dregg2.Circuit.FriQuerySamplingBias

open Finset
open Dregg2.Circuit.FriVerifierCompose (epsQuery)

/-! ## 1. The core counting fact — a residue class of `range N` has `≤ ⌊N/m⌋ + 1` elements. -/

/-- **A RESIDUE CLASS IS SMALL.** Among `{0, …, N−1}`, at most `⌊N/m⌋ + 1` numbers are
congruent to `j` mod `m`. The injection is `n ↦ n / m`: within one residue class `n` is recovered
from `n / m` (as `m·(n/m) + j`), and `n < N` forces `n / m ≤ N / m`. (No `0 < m` needed: at
`m = 0` the class is `{j}` and `N / 0 + 1 = 1`, so the bound holds a fortiori.) -/
theorem residueClassCard_le (N m j : ℕ) :
    ((Finset.range N).filter (fun n => n % m = j)).card ≤ N / m + 1 := by
  classical
  rw [← Finset.card_range (N / m + 1)]
  refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
  · intro n hn
    obtain ⟨hnN, _⟩ := Finset.mem_filter.1 hn
    have hle : n / m ≤ N / m := Nat.div_le_div_right (le_of_lt (Finset.mem_range.1 hnN))
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hle)
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hab' : a / m = b / m := hab
    calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
      _ = m * (b / m) + b % m := by rw [hab', ha.2, hb.2]
      _ = b := Nat.div_add_mod b m

/-- **A RESIDUE EVENT IS SMALL.** For any set `E` of residues, at most `|E| · (⌊N/m⌋ + 1)`
numbers in `{0, …, N−1}` reduce into `E` mod `m` — the residue-class bound summed over `E`. -/
theorem residueSetCard_le (N m : ℕ) (E : Finset ℕ) :
    ((Finset.range N).filter (fun n => n % m ∈ E)).card ≤ E.card * (N / m + 1) := by
  classical
  have hsplit : (Finset.range N).filter (fun n => n % m ∈ E)
      = E.biUnion (fun j => (Finset.range N).filter (fun n => n % m = j)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨hn, hmem⟩; exact ⟨n % m, hmem, hn, rfl⟩
    · rintro ⟨j, hj, hn, hnj⟩; exact ⟨hn, hnj ▸ hj⟩
  rw [hsplit]
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_card_nsmul E _ (N / m + 1) (fun j _ => residueClassCard_le N m j)).trans ?_
  rw [smul_eq_mul]

/-! ## 2. ⚑ THE UNIFORMITY-DEFECT TERM. -/

/-- **⚑ THE MODULAR-REDUCTION SAMPLING BIAS, BOUNDED.** For `n` uniform over `{0, …, N−1}` and
any residue event `E` (with `|E| ≤ m`), the reduced index `n % m` lands in `E` with probability
at most `|E|/m + m/N`. The first addend is the value a UNIFORM index would give; the second,
`m/N`, is the uniformity-defect term the deployed `sampleBits` reduction incurs — the term
`FriVerifierCompose` names as missing. -/
theorem residue_reduction_prob_le (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (E : Finset ℕ)
    (hE : E.card ≤ m) :
    (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) / (N : ℝ)
      ≤ (E.card : ℝ) / (m : ℝ) + (m : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  -- The Nat numerator bound, cast to `ℝ`.
  set B : ℝ := (E.card : ℝ) * (((N / m : ℕ) : ℝ) + 1) with hBdef
  have hnumR : (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) ≤ B := by
    have h := (Nat.cast_le (α := ℝ)).2 (residueSetCard_le N m E)
    rw [hBdef]; push_cast at h ⊢; linarith
  -- `⌊N/m⌋ ≤ N/m` as reals.
  have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR]; exact_mod_cast Nat.div_mul_le_self N m
  -- Bound `B` by `|E|·N/m + m`, using `|E| ≤ m` for the trailing `+ |E|`.
  have hEcardR : (E.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hE
  have hB : B ≤ (E.card : ℝ) * (N : ℝ) / (m : ℝ) + (m : ℝ) := by
    have h1 : (E.card : ℝ) * ((N / m : ℕ) : ℝ) ≤ (E.card : ℝ) * ((N : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    have hBexp : B = (E.card : ℝ) * ((N / m : ℕ) : ℝ) + (E.card : ℝ) := by rw [hBdef]; ring
    rw [hBexp]
    have hmul : (E.card : ℝ) * ((N : ℝ) / (m : ℝ)) = (E.card : ℝ) * (N : ℝ) / (m : ℝ) := by ring
    linarith [h1, hEcardR, hmul.le, hmul.ge]
  -- Assemble: numerator ≤ B ≤ (|E|·N/m + m), then divide by N.
  have hfin : ((E.card : ℝ) * (N : ℝ) / (m : ℝ) + (m : ℝ)) / (N : ℝ)
      = (E.card : ℝ) / (m : ℝ) + (m : ℝ) / (N : ℝ) := by
    field_simp
  calc (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) / (N : ℝ)
      ≤ B / (N : ℝ) := by gcongr
    _ ≤ ((E.card : ℝ) * (N : ℝ) / (m : ℝ) + (m : ℝ)) / (N : ℝ) := by gcongr
    _ = (E.card : ℝ) / (m : ℝ) + (m : ℝ) / (N : ℝ) := hfin

/-! ## 3. The deployed instantiation — `m = 2^logN` buckets, `N = |F| = 2013265921`. -/

/-- **⚑ THE DEPLOYED QUERY-INDEX BIAS, BOUNDED.** `m = 2^logN` query buckets, `N = |F| =
2013265921` squeeze values. Any residue event's biased probability exceeds its uniform value
`|E|/2^logN` by at most `2^logN / |F|`. This is the QUANTITATIVE companion to
`FriVerifierCompose.babybear_sampleBits_not_balanced`: that theorem shows the buckets are UNEQUAL;
this one bounds BY HOW MUCH any event's probability can be inflated by that inequality — the
uniformity-defect addend `εQuery` must carry over the deployed non-uniform indices. -/
theorem babybear_query_bias_le (logN : ℕ) (E : Finset ℕ) (hE : E.card ≤ 2 ^ logN) :
    (((Finset.range 2013265921).filter (fun n => n % (2 ^ logN) ∈ E)).card : ℝ) / (2013265921 : ℝ)
      ≤ (E.card : ℝ) / ((2 : ℝ) ^ logN) + ((2 : ℝ) ^ logN) / (2013265921 : ℝ) := by
  have h := residue_reduction_prob_le 2013265921 (2 ^ logN) (by norm_num)
    (pow_pos (by norm_num : (0 : ℕ) < 2) logN) E hE
  have hcast : (((2 ^ logN : ℕ)) : ℝ) = (2 : ℝ) ^ logN := by push_cast; ring
  rw [hcast] at h
  exact h

/-! ## 4. FIRE — the defect term is load-bearing (its omission makes the bound FALSE). -/

/-- The concrete biased probability at `N = 3, m = 2, E = {0}`: `Pr[n % 2 = 0] = 2/3`. -/
theorem residue_bias_fires :
    (((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / (3 : ℝ) = 2 / 3 := by
  have hc : ((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card = 2 := by decide
  rw [hc]; norm_num

/-- **⚑ THE `+ m/N` TERM IS NECESSARY.** At `N = 3, m = 2, E = {0}` the biased probability `2/3`
STRICTLY EXCEEDS the naive uniform value `|E|/m = 1/2`. So `residue_reduction_prob_le` WITHOUT its
`+ m/N` addend would be FALSE — the defect term is load-bearing exactly in the `m ∤ N` regime the
deployed `sampleBits` lives in (`babybear_sampleBits_not_balanced`). -/
theorem residue_bias_defect_load_bearing :
    (1 : ℝ) / 2 < (((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / (3 : ℝ) := by
  rw [residue_bias_fires]; norm_num

/-- Sanity: the full bound (with the defect term) DOES hold at that same witness — `2/3 ≤ 1/2 +
2/3`. The `+ m/N` is what restores truth. -/
theorem residue_bias_bound_holds :
    (((Finset.range 3).filter (fun n => n % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / ((3 : ℕ) : ℝ)
      ≤ ((({0} : Finset ℕ).card : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) :=
  residue_reduction_prob_le 3 2 (by norm_num) (by norm_num) ({0} : Finset ℕ) (by decide)

/-! ## 5. ⚑⚑ WIRING THE DEFECT INTO `εQuery` — the `k`-query composition.

⚑ THIS IS THE CLOSURE OF `FriVerifierCompose` §3 BLOCKER (b). §1–§4 QUANTIFIED the per-index
defect (`residue_reduction_prob_le`); this section COMPOSES it into the `k`-query survival exponent
`εQuery` raises `(1 − δ)` to. The uniform model (`FriQuerySoundness.accept_prob_le`,
`FriVerifierCompose.epsQuery`) counts `k`-samples over `Fin k → κ` and gets per-index survival
`(1 − δ)` because it assumes the query index is UNIFORM over `κ`. The deployed index is
`Challenger.sampleBits`: a squeeze `n` uniform over `Fin |F|`, reduced `n % 2^logN`. §1–§4 show that
reduction inflates any residue event's probability by up to `m/N = 2^logN/|F|`. So the DEPLOYED
per-index survival is not `(1 − δ)` but `(1 − δ) + 2^logN/|F|`, and the `k` INDEPENDENT squeeze
draws raise THAT to the `k`:

    biased εQuery = L/|F| + ((1 − δ) + 2^logN/|F|)^k                 (`epsQueryBias`)

The fold-density term `L/|F|` is unchanged — it is a property of the fold-challenge `α` marginal, not
of the query sampler. Only the query exponent's base carries the defect.

## Why the base is `(1 − δ) + m/N` and not `(1 − δ)`

The uniform per-index survival is `|E|/m` where `E` is the per-index MISS set (the residue values `j`
at which the folded word AGREES — a `δ`-far word has `≥ δ·m` disagreements, so `|E|/m ≤ 1 − δ`). Under
the deployed reduction `n % m` with `n` uniform over `N = |F|`, `Pr[n % m ∈ E] ≤ |E|/m + m/N`
(`residue_reduction_prob_le`), so the deployed per-index survival is `≤ (1 − δ) + m/N`.

## Non-vacuity / load-bearing (`biased_survival_defect_load_bearing`)

The `+ m/N` addend is NOT slack. At `N = 3, m = 2, E = {0}, δ = 1/2, k = 1` the biased `1`-query
survival is `2/3`, which STRICTLY EXCEEDS the un-defected value `(1 − δ)^k = 1/2` — so the composed
bound WITHOUT the defect term (`≤ (1 − δ)^k`) is FALSE, and `2 ∤ 3` is exactly the deployed
`2^logN ∤ |F|` regime (`babybear_order_not_divisible_by_two`). The defect term restores truth
(`biased_survival_bound_holds_at_witness`).
-/

/-! ### 5.1 The counting bridge — a residue filter over `Fin N` counts the same as over `range N`. -/

/-- The `Fin N` and `range N` residue-filter cardinalities agree, via the injection `a ↦ a.val`. Lets
§1–§4's `range N` bounds feed the product-space count over the sample space `Fin k → Fin N`. -/
theorem card_fin_filter_mod_eq (N m : ℕ) (E : Finset ℕ) :
    (Finset.univ.filter (fun a : Fin N => a.val % m ∈ E)).card
      = ((Finset.range N).filter (fun n => n % m ∈ E)).card := by
  apply Finset.card_bij (fun (a : Fin N) _ => a.val)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨a.isLt, ha⟩
  · intro a _ b _ hab
    exact Fin.val_injective hab
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨⟨n, hn.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hn.2

/-! ### 5.2 The product count — `k` independent biased draws all survive with count `c^k`. -/

/-- **THE `k`-FOLD COUNTING IDENTITY (biased model).** Over the deployed sample space
`Fin k → Fin N` (`k` independent squeeze values, each uniform over the `N = |F|` squeeze range), the
number of samples whose reduced indices `n % m` ALL land in the miss set `E` is `c^k`, where
`c = |{a : Fin N | a.val % m ∈ E}|` is the per-coordinate survive count. This is the biased analogue
of `FriQuerySoundness.accepting_card`, over the pre-reduction squeeze space rather than `κ`. -/
theorem biased_accepting_card (N m k : ℕ) (E : Finset ℕ) :
    (Finset.univ.filter (fun Q : Fin k → Fin N => ∀ i, (Q i).val % m ∈ E)).card
      = (Finset.univ.filter (fun a : Fin N => a.val % m ∈ E)).card ^ k := by
  have hset : (Finset.univ.filter (fun Q : Fin k → Fin N => ∀ i, (Q i).val % m ∈ E))
      = Fintype.piFinset (fun _ : Fin k => Finset.univ.filter (fun a : Fin N => a.val % m ∈ E)) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset_const]

/-! ### 5.3 ⚑ THE BIAS-AWARE `k`-QUERY SURVIVAL BOUND — the composed defect term. -/

/-- **⚑⚑ THE COMPOSED DEFECT-CARRYING SURVIVAL BOUND.** For a `δ`-far word whose per-index MISS set
`E` has uniform density `|E|/m ≤ 1 − δ`, the fraction of `k`-query DEPLOYED samples (each index
`n % m`, `n` uniform over `Fin N`) that ALL miss is

    ≤ ((1 − δ) + m/N)^k.

The per-index survival `(1 − δ)` of the uniform model is REPLACED by `(1 − δ) + m/N` — the second
addend is the `residue_reduction_prob_le` defect — and the `k` independent draws raise it to the `k`
(`biased_accepting_card` + `pow_le_pow_left₀`). This is exactly the exponent `εQuery` needs over the
deployed `sampleBits` sampler; without the `m/N` addend the bound is FALSE at `m ∤ N`
(`biased_survival_defect_load_bearing`). -/
theorem biased_query_survival_pow_le (N m k : ℕ) (E : Finset ℕ) (δ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hE : E.card ≤ m)
    (hmiss : (E.card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    ((Finset.univ.filter (fun Q : Fin k → Fin N => ∀ i, (Q i).val % m ∈ E)).card : ℝ)
        / ((N : ℝ) ^ k)
      ≤ ((1 - δ) + (m : ℝ) / (N : ℝ)) ^ k := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [biased_accepting_card]
  set c : ℕ := (Finset.univ.filter (fun a : Fin N => a.val % m ∈ E)).card with hc
  have hbridge : ((Finset.range N).filter (fun n => n % m ∈ E)).card = c := by
    rw [hc]; exact (card_fin_filter_mod_eq N m E).symm
  have hbase : (c : ℝ) / (N : ℝ) ≤ (1 - δ) + (m : ℝ) / (N : ℝ) := by
    have h := residue_reduction_prob_le N m hN hm E hE
    rw [hbridge] at h
    linarith [hmiss, h]
  have hbase0 : (0 : ℝ) ≤ (c : ℝ) / (N : ℝ) := by positivity
  push_cast
  rw [← div_pow]
  exact pow_le_pow_left₀ hbase0 hbase k

/-- **⚑ THE DEPLOYED-FIELD INSTANTIATION.** `N = |F| = 2013265921` squeeze values, `m = 2^logN`
query buckets. A `δ`-far word's `k` deployed spot-checks all miss with probability
`≤ ((1 − δ) + 2^logN/|F|)^k` — the honest bias-aware query exponent at the shipped BabyBear field.
(Holds at every `logN`; the defect addend `2^logN/|F|` is nonzero and LOAD-BEARING exactly in the
deployed `logN ≥ 1` regime where `2^logN ∤ |F|`, `babybear_order_not_divisible_by_two`.) -/
theorem babybear_biased_query_survival_pow_le (logN k : ℕ) (E : Finset ℕ) (δ : ℝ)
    (hE : E.card ≤ 2 ^ logN)
    (hmiss : (E.card : ℝ) / ((2 : ℝ) ^ logN) ≤ 1 - δ) :
    ((Finset.univ.filter (fun Q : Fin k → Fin 2013265921 =>
          ∀ i, (Q i).val % (2 ^ logN) ∈ E)).card : ℝ)
        / ((2013265921 : ℝ) ^ k)
      ≤ ((1 - δ) + ((2 : ℝ) ^ logN) / (2013265921 : ℝ)) ^ k := by
  have hcast : (((2 ^ logN : ℕ)) : ℝ) = (2 : ℝ) ^ logN := by push_cast; ring
  have hmiss' : (E.card : ℝ) / (((2 ^ logN : ℕ)) : ℝ) ≤ 1 - δ := by rw [hcast]; exact hmiss
  have h := biased_query_survival_pow_le 2013265921 (2 ^ logN) k E δ (by norm_num)
    (pow_pos (by norm_num) logN) hE hmiss'
  push_cast at h
  exact_mod_cast h

/-! ### 5.4 ⚑ `epsQueryBias` — the bias-aware `εQuery`, and its relation to the uniform one. -/

/-- **⚑ THE BIAS-AWARE `εQuery`.** `L/|F| + ((1 − δ) + 2^logN/|F|)^k`: the fold-density term
(unchanged from `FriVerifierCompose.epsQuery`, a property of the `α` marginal) plus the deployed
`k`-query survival term whose base carries the `sampleBits` defect (`biased_query_survival_pow_le`).
This is the value `εQuery` composes to over the DEPLOYED non-uniform query indices. -/
noncomputable def epsQueryBias (cardF logN k L : ℕ) (δ : ℝ) : ℝ :=
  (L : ℝ) / (cardF : ℝ) + ((1 - δ) + ((2 : ℝ) ^ logN) / (cardF : ℝ)) ^ k

/-- **The defect is a COST, not slack — `epsQueryBias` DOMINATES the uniform `epsQuery`.** At list
size `L = 1` the bias-aware bound is `≥` the uniform `FriVerifierCompose.epsQuery`, because the
survival base is raised from `(1 − δ)` to `(1 − δ) + 2^logN/|F| ≥ (1 − δ)`. So substituting the honest
deployed sampler can only WEAKEN `εQuery` — the direction a real defect must move a sound bound. -/
theorem epsQueryBias_ge_epsQuery (cardF logN k : ℕ) (δ : ℝ)
    (hδ1 : δ ≤ 1) :
    epsQuery cardF k δ ≤ epsQueryBias cardF logN k 1 δ := by
  unfold epsQuery epsQueryBias
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
  have hbias : (0 : ℝ) ≤ (2 : ℝ) ^ logN / (cardF : ℝ) := by positivity
  have hpow : (1 - δ) ^ k ≤ ((1 - δ) + (2 : ℝ) ^ logN / (cardF : ℝ)) ^ k :=
    pow_le_pow_left₀ h0 (by linarith) k
  push_cast
  linarith

/-! ### 5.5 ⚑ NON-VACUITY — the `+ m/N` addend is load-bearing (its omission makes the bound FALSE). -/

/-- The concrete biased `1`-query survival at `N = 3, m = 2, E = {0}`: `2/3` (two of the three
squeeze values, `0` and `2`, reduce to residue `0 ∈ E`). -/
theorem biased_survival_fires :
    ((Finset.univ.filter (fun Q : Fin 1 → Fin 3 =>
        ∀ i, (Q i).val % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / ((3 : ℝ) ^ 1) = 2 / 3 := by
  have hc : (Finset.univ.filter (fun Q : Fin 1 → Fin 3 =>
      ∀ i, (Q i).val % 2 ∈ ({0} : Finset ℕ))).card = 2 := by decide
  rw [hc]; norm_num

/-- **⚑⚑ THE DEFECT ADDEND IS LOAD-BEARING.** At `N = 3, m = 2, E = {0}, δ = 1/2, k = 1` the biased
survival `2/3` STRICTLY EXCEEDS the un-defected exponent `(1 − δ)^k = (1/2)^1 = 1/2`. So the composed
query bound WITHOUT the `+ m/N` term — i.e. `≤ (1 − δ)^k`, the value the UNIFORM
`FriQuerySoundness.accept_prob_le` proves — is FALSE for the deployed biased sampler. And `2 ∤ 3` is
exactly the deployed `2^logN ∤ |F|` regime (`babybear_order_not_divisible_by_two`): the defect is
real precisely where `sampleBits` lives. -/
theorem biased_survival_defect_load_bearing :
    (1 - (1 / 2 : ℝ)) ^ 1
      < ((Finset.univ.filter (fun Q : Fin 1 → Fin 3 =>
          ∀ i, (Q i).val % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / ((3 : ℝ) ^ 1) := by
  rw [biased_survival_fires]; norm_num

/-- **The `+ m/N` restores truth.** The bias-aware bound (with the defect term) DOES hold at the
witness — a specialization of the general `biased_query_survival_pow_le` at `N = 3, m = 2, E = {0},
δ = 1/2, k = 1`, whose conclusion `2/3 ≤ ((1 − 1/2) + 2/3)^1 = 7/6` is what makes the composed
`εQuery` sound over the biased sampler. -/
theorem biased_survival_bound_holds_at_witness :
    ((Finset.univ.filter (fun Q : Fin 1 → Fin 3 =>
        ∀ i, (Q i).val % 2 ∈ ({0} : Finset ℕ))).card : ℝ) / ((3 : ℝ) ^ 1)
      ≤ ((1 - (1 / 2 : ℝ)) + (2 : ℝ) / (3 : ℝ)) ^ 1 := by
  have h := biased_query_survival_pow_le 3 2 1 ({0} : Finset ℕ) (1 / 2)
    (by norm_num) (by norm_num) (by decide) (by rw [Finset.card_singleton]; norm_num)
  push_cast at h
  convert h using 2

#assert_all_clean [
  residueClassCard_le,
  residueSetCard_le,
  residue_reduction_prob_le,
  babybear_query_bias_le,
  residue_bias_fires,
  residue_bias_defect_load_bearing,
  residue_bias_bound_holds,
  card_fin_filter_mod_eq,
  biased_accepting_card,
  biased_query_survival_pow_le,
  babybear_biased_query_survival_pow_le,
  epsQueryBias_ge_epsQuery,
  biased_survival_fires,
  biased_survival_defect_load_bearing,
  biased_survival_bound_holds_at_witness
]

end Dregg2.Circuit.FriQuerySamplingBias
