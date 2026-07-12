/-
# DEPLOYED UDR REGIME — reality check: dregg's shipped FRI parameters vs the
unique-decoding radius, in exact rational arithmetic.

THE QUESTION: does the deployed FRI configuration sit inside the UNIQUE-decoding regime
(δ strictly below the half-minimum-distance radius `(1 − ρ)/2`), or does it lean on
list-decoding assumptions?

THE DEPLOYED NUMBERS (read from source, not invented):
* Prover-side (`circuit/src/plonky3_prover.rs:96-100`, as recorded in-tree at
  `BabyBearFriDeployed.lean:15-18` and `FriQuerySoundness.lean:217-226`):
  `log_blowup = 3` ⇒ rate `ρ = 1/8`, `num_queries = 38`, `query_pow_bits = 16`,
  `max_log_arity = 3`, `log_final_poly_len = 0`.
* Wrap-side (`FriVerifier.ir2LeafWrapConfig`, from `circuit-prove/src/ivc_turn_chain.rs:1137`):
  `log_blowup = 6` ⇒ rate `1/64`, `num_queries = 19`, `query_pow_bits = 16`.
* The proximity parameter the tree's query-soundness work uses
  (`FriQuerySoundness.lean:221`, `deployed_accept_prob_lt`): **δ = 7/16**.

**THE HONEST FINDING (loudly).** The tree's δ is **NOT strictly below** the unique-decoding
radius — it EQUALS it: at ρ = 1/8, `(1 − ρ)/2 = 7/16 = δ` exactly
(`deployed_delta_eq_udr`, `deployed_delta_NOT_lt_udr`). The requested strict inequality
`δ < (1 − ρ)/2` is FALSE and is not fudged here. The configuration is nonetheless
genuinely in the UNIQUE-decoding regime, because the strictness lives one layer down:
the rate-ρ Reed–Solomon code on an N-point domain is MDS with minimum distance
`N(1 − ρ) + 1`, and `2·δ·N = N(1 − ρ) < N(1 − ρ) + 1` STRICTLY for every N
(`deployed_two_delta_lt_minDist`). Concretely: two degree-`< ρN` polynomials each within
Hamming distance `δ·N` of a common word agree on `≥ N − 2δN = ρN` points, which forces
them EQUAL by interpolation uniqueness — proved below at the deployed rate over the
deployed field (`deployed_udr_unique_decoding`, via `lowDegree_agree_forces_eq_babyBear`),
FIRED on a concrete corrupted 16-point instance, and shown TIGHT: at relative radius `1/2`
(just above `7/16`) two distinct low-degree polynomials inhabit the same ball
(`beyond_udr_two_codewords`), so the uniqueness conclusion genuinely fails outside the
regime — the deployed `7/16` is the honest boundary, and the tree stands exactly ON it,
which the MDS `+1` makes sound.

SCOPE (honest): (i) the wrap config's rate/UDR (`1/64`, `63/128`) are computed, but the
tree cites no separate δ for the wrap path — its query-soundness instantiation is the
prover-side `δ = 7/16, k = 38`; no wrap-δ claim is made. (ii) `deployed_udr_unique_decoding`
is the uniqueness half at radius exactly `δN`; that FRI acceptance certifies δ-proximity is
the separate committed seam (`FriQuerySoundness`), reused here only for the numeric error
tooth `deployed_error_at_udr`.
-/
import Dregg2.Circuit.LowDegreeUniqueness
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Tactics

namespace Dregg2.Circuit.DeployedUdrRegime

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.LowDegreeUniqueness
open Dregg2.Circuit.FriVerifier (FriParams ir2LeafWrapConfig)

/-! ## §1. The deployed parameters, as in-tree values with `rfl` teeth. -/

/-- The prover-side FRI knobs (`circuit/src/plonky3_prover.rs:96-100`, recorded in-tree at
`BabyBearFriDeployed.lean` §header and `FriQuerySoundness.lean` §Deployed): `log_blowup 3`,
`38` queries, `16` PoW bits, `max_log_arity 3`, `log_final_poly_len 0`, deg-4 extension. -/
def plonky3ProverParams : FriParams :=
  { logBlowup := 3, numQueries := 38, powBits := 16, maxLogArity := 3,
    logFinalPolyLen := 0, extDeg := 4 }

theorem prover_logBlowup : plonky3ProverParams.logBlowup = 3 := rfl
theorem prover_numQueries : plonky3ProverParams.numQueries = 38 := rfl
theorem prover_powBits : plonky3ProverParams.powBits = 16 := rfl

/-- The wrap-side config is the IN-TREE `ir2LeafWrapConfig` — `log_blowup 6`, `19` queries. -/
theorem wrap_logBlowup : ir2LeafWrapConfig.logBlowup = 6 := rfl
theorem wrap_numQueries : ir2LeafWrapConfig.numQueries = 19 := rfl
theorem wrap_powBits : ir2LeafWrapConfig.powBits = 16 := rfl

/-! ## §2. Rate and unique-decoding radius, exact over ℚ. -/

/-- The Reed–Solomon rate at a given `log_blowup`: `ρ = 1/2^logBlowup`. -/
def rate (logBlowup : ℕ) : ℚ := 1 / 2 ^ logBlowup

/-- The unique-decoding radius at a given `log_blowup`: `(1 − ρ)/2` — half the relative
minimum distance `1 − ρ` of the rate-`ρ` RS code (relative form; the exact MDS minimum
distance is `N(1 − ρ) + 1`, whose `+1` is the strictness reserve — §3). -/
def udr (logBlowup : ℕ) : ℚ := (1 - rate logBlowup) / 2

/-- **The δ the tree deploys** (`FriQuerySoundness.lean:221-226`,
`deployed_accept_prob_lt`): `7/16`. -/
def deployedDelta : ℚ := 7 / 16

/-- **(a) The deployed prover rate**: `ρ = 1/2³ = 1/8`. -/
theorem deployed_rate : rate plonky3ProverParams.logBlowup = 1 / 8 := by
  norm_num [rate, plonky3ProverParams]

/-- The wrap-path rate: `1/2⁶ = 1/64` (from the in-tree `ir2LeafWrapConfig`). -/
theorem wrap_rate : rate ir2LeafWrapConfig.logBlowup = 1 / 64 := by
  norm_num [rate, ir2LeafWrapConfig]

/-- **(b) The deployed unique-decoding radius**: `(1 − 1/8)/2 = 7/16`, exactly. -/
theorem deployed_udr : udr plonky3ProverParams.logBlowup = 7 / 16 := by
  norm_num [udr, rate, plonky3ProverParams]

/-- The wrap-path unique-decoding radius: `(1 − 1/64)/2 = 63/128`, exactly. -/
theorem wrap_udr : udr ir2LeafWrapConfig.logBlowup = 63 / 128 := by
  norm_num [udr, rate, ir2LeafWrapConfig]

/-! ## §3. (c) THE HONEST FINDING: δ EQUALS the UDR — the strict `<` is FALSE. -/

/-- **The tree's δ sits EXACTLY ON the unique-decoding radius**: `7/16 = (1 − 1/8)/2`. -/
theorem deployed_delta_eq_udr : deployedDelta = udr plonky3ProverParams.logBlowup := by
  norm_num [deployedDelta, udr, rate, plonky3ProverParams]

/-- **LOUDLY: the requested strict inequality `δ < (1 − ρ)/2` is FALSE** at the deployed
parameters — δ is not below the radius, it IS the radius. Not fudged. -/
theorem deployed_delta_NOT_lt_udr : ¬ deployedDelta < udr plonky3ProverParams.logBlowup := by
  rw [deployed_delta_eq_udr]
  exact lt_irrefl _

/-- The non-strict direction that DOES hold: `δ ≤ (1 − ρ)/2`. -/
theorem deployed_delta_le_udr : deployedDelta ≤ udr plonky3ProverParams.logBlowup :=
  le_of_eq deployed_delta_eq_udr

/-- **The CORRECT strict inequality** — why `δ = (1 − ρ)/2` is still genuinely inside the
unique-decoding regime: the rate-`ρ` RS code is MDS with minimum distance `N(1 − ρ) + 1`,
and two balls of radius `δ·N` can only share a word if `2δN ≥ d_min`; here
`2·δ·N = N(1 − ρ) < N(1 − ρ) + 1` STRICTLY, for every domain size `N`. -/
theorem deployed_two_delta_lt_minDist (N : ℕ) :
    2 * deployedDelta * N < (1 - rate plonky3ProverParams.logBlowup) * N + 1 := by
  have h : 2 * deployedDelta * (N : ℚ) = (1 - rate plonky3ProverParams.logBlowup) * N := by
    norm_num [deployedDelta, rate, plonky3ProverParams]
  rw [h]
  exact lt_add_one _

/-- Integer-exact scaling tooth: at the smallest deployed-rate domain `N = 16`
(`BabyBearFriDeployed.friSetupDeployedRate`), the radius is EXACTLY the integer `7`. -/
theorem deployed_udr_scaled_16 : deployedDelta * ((16 : ℕ) : ℚ) = 7 := by
  norm_num [deployedDelta]

/-! ## §4. Unique decoding at the deployed rate, over the deployed field.

The theorem that makes "in the unique-decoding regime" MEAN something: at rate `1/8`
(`N = 8k`, degree bound `k`), any two degree-`< k` polynomials within Hamming distance
`δ·N = 7N/16` of a COMMON word on an `N`-point subset of BabyBear are EQUAL. Proof: their
disagreement sets with the word have total size `≤ 7N/8`, so they AGREE on
`≥ N − 7N/8 = N/8 = k` points — interpolation uniqueness (`lowDegree_agree_forces_eq_babyBear`)
finishes. The strictness reserve is visible: the agreement bound lands exactly ON `k`. -/

/-- **Unique decoding at the deployed rate `1/8` and deployed radius `δ = 7/16`, over
BabyBear.** The ball of radius `δ·N` around any word contains at most ONE degree-`< k`
codeword. -/
theorem deployed_udr_unique_decoding
    {N k : ℕ} (hNk : N = 8 * k)
    (pts : Finset BabyBear) (hcard : pts.card = N)
    (f : BabyBear → BabyBear) (p q : Polynomial BabyBear)
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hpf : (((pts.filter (fun x => p.eval x ≠ f x)).card : ℚ)) ≤ deployedDelta * N)
    (hqf : (((pts.filter (fun x => q.eval x ≠ f x)).card : ℚ)) ≤ deployedDelta * N) :
    p = q := by
  classical
  set Dp := pts.filter (fun x => p.eval x ≠ f x) with hDp
  set Dq := pts.filter (fun x => q.eval x ≠ f x) with hDq
  set A := pts \ (Dp ∪ Dq) with hA
  -- Counting: |A| ≥ N − |Dp| − |Dq| ≥ N − 7N/8 = k.
  have hcut : N ≤ A.card + (Dp ∪ Dq).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := pts) (t := Dp ∪ Dq)
    rwa [hcard] at h
  have hunion : (Dp ∪ Dq).card ≤ Dp.card + Dq.card := Finset.card_union_le _ _
  have hk : k ≤ A.card := by
    have hcutQ : (N : ℚ) ≤ (A.card : ℚ) + (Dp.card : ℚ) + (Dq.card : ℚ) := by
      have h : N ≤ A.card + Dp.card + Dq.card := by omega
      exact_mod_cast h
    have hNQ : (N : ℚ) = 8 * (k : ℚ) := by exact_mod_cast hNk
    have hδ : deployedDelta = 7 / 16 := rfl
    rw [hδ] at hpf hqf
    have hkQ : (k : ℚ) ≤ (A.card : ℚ) := by
      rw [hNQ] at hcutQ hpf hqf
      linarith
    exact_mod_cast hkQ
  -- Agreement: outside both disagreement sets, p and q both equal f.
  have hagree : ∀ x ∈ A, p.eval x = q.eval x := by
    intro x hx
    rw [hA, Finset.mem_sdiff, Finset.mem_union] at hx
    obtain ⟨hxp, hxn⟩ := hx
    push Not at hxn
    obtain ⟨hnp, hnq⟩ := hxn
    have hpe : p.eval x = f x := by
      by_contra hne
      exact hnp (Finset.mem_filter.mpr ⟨hxp, hne⟩)
    have hqe : q.eval x = f x := by
      by_contra hne
      exact hnq (Finset.mem_filter.mpr ⟨hxp, hne⟩)
    rw [hpe, hqe]
  exact lowDegree_agree_forces_eq_babyBear p q A hp hq hk hagree

/-! ## §5. FIRE — the hypotheses discharge on a CONCRETE corrupted instance.

`N = 16, k = 2` — the smallest deployed-rate domain (rate `2/16 = 1/8`, the same geometry
`BabyBearFriDeployed` instantiates). The word `fireWord` is the evaluation of `X + 3`
CORRUPTED at the point `0` (value `1` instead of `3`) — 1 error against the integer budget
`⌊δ·N⌋ = 7`. Both candidate decodings are within radius, and the theorem forces them equal. -/

/-- The 16-point evaluation set `{0,…,15} ⊆ BabyBear`. -/
noncomputable def firePts : Finset BabyBear :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}

theorem firePts_card : firePts.card = 16 := by decide

/-- The received word: `x + 3` corrupted at `x = 0` (reads `1`, honest value `3`). -/
noncomputable def fireWord : BabyBear → BabyBear := fun x => if x = 0 then 1 else x + 3

/-- Candidate `p = X + 3` is within the deployed radius of the corrupted word:
its disagreement set is `⊆ {0}`, so has size `≤ 1 ≤ 7 = δ·16`. -/
theorem fire_p_close :
    (((firePts.filter (fun x => (X + C 3 : Polynomial BabyBear).eval x ≠ fireWord x)).card : ℚ))
      ≤ deployedDelta * ((16 : ℕ) : ℚ) := by
  have hsub : firePts.filter (fun x => (X + C 3 : Polynomial BabyBear).eval x ≠ fireWord x)
      ⊆ {0} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hne⟩ := hx
    rw [Finset.mem_singleton]
    by_contra hx0
    exact hne (by simp [fireWord, hx0])
  have h1 : (firePts.filter
      (fun x => (X + C 3 : Polynomial BabyBear).eval x ≠ fireWord x)).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have h1Q : (((firePts.filter
      (fun x => (X + C 3 : Polynomial BabyBear).eval x ≠ fireWord x)).card : ℚ)) ≤ 1 := by
    exact_mod_cast h1
  calc (((firePts.filter
        (fun x => (X + C 3 : Polynomial BabyBear).eval x ≠ fireWord x)).card : ℚ))
      ≤ 1 := h1Q
    _ ≤ deployedDelta * ((16 : ℕ) : ℚ) := by norm_num [deployedDelta]

/-- Candidate `q = 3 + X` (the same codeword, different syntax) is within radius too. -/
theorem fire_q_close :
    (((firePts.filter (fun x => (C 3 + X : Polynomial BabyBear).eval x ≠ fireWord x)).card : ℚ))
      ≤ deployedDelta * ((16 : ℕ) : ℚ) := by
  have hsub : firePts.filter (fun x => (C 3 + X : Polynomial BabyBear).eval x ≠ fireWord x)
      ⊆ {0} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hne⟩ := hx
    rw [Finset.mem_singleton]
    by_contra hx0
    exact hne (by simp [fireWord, hx0, add_comm])
  have h1 : (firePts.filter
      (fun x => (C 3 + X : Polynomial BabyBear).eval x ≠ fireWord x)).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have h1Q : (((firePts.filter
      (fun x => (C 3 + X : Polynomial BabyBear).eval x ≠ fireWord x)).card : ℚ)) ≤ 1 := by
    exact_mod_cast h1
  calc (((firePts.filter
        (fun x => (C 3 + X : Polynomial BabyBear).eval x ≠ fireWord x)).card : ℚ))
      ≤ 1 := h1Q
    _ ≤ deployedDelta * ((16 : ℕ) : ℚ) := by norm_num [deployedDelta]

/-- **FIRE.** On the corrupted 16-point instance, both within-radius candidates are forced
EQUAL by `deployed_udr_unique_decoding` — the conclusion `X + 3 = 3 + X` is derived via the
deployed-rate unique-decoding theorem (not by `ring`), with every hypothesis discharged on
concrete data: `16 = 8·2`, `|pts| = 16`, degrees `1 < 2`, both distances `≤ 7 = δ·16`. -/
theorem deployed_udr_decoding_fires :
    (X + C 3 : Polynomial BabyBear) = C 3 + X := by
  refine deployed_udr_unique_decoding (N := 16) (k := 2) rfl firePts firePts_card fireWord
    _ _ ?_ ?_ fire_p_close fire_q_close
  · rw [natDegree_X_add_C]
    norm_num
  · rw [add_comm, natDegree_X_add_C]
    norm_num

/-! ## §6. TIGHTNESS (the bite) — just above the radius, uniqueness FAILS.

At relative radius `1/2 > 7/16`, the ball is no longer a unique-decoding ball: the word
that reads `x` on `{0,…,7}` and `20` on `{8,…,15}` has TWO distinct degree-`< 2`
polynomials within distance `8 = (1/2)·16` — `X` and the constant `20`. So the deployed
radius `7/16` cannot be relaxed toward `1/2`; the configuration is at the honest boundary
of the unique regime, not comfortably inside a slack bound. -/

/-- The low half `{0,…,7}` of the 16-point domain. -/
noncomputable def lowHalf : Finset BabyBear := {0, 1, 2, 3, 4, 5, 6, 7}

/-- The high half `{8,…,15}` of the 16-point domain. -/
noncomputable def highHalf : Finset BabyBear := {8, 9, 10, 11, 12, 13, 14, 15}

theorem lowHalf_card : lowHalf.card = 8 := by decide
theorem highHalf_card : highHalf.card = 8 := by decide

theorem firePts_eq_union : firePts = lowHalf ∪ highHalf := by decide

theorem lowHigh_inter : lowHalf ∩ highHalf = ∅ := by decide

theorem firePts_split : ∀ x ∈ firePts, x ∈ lowHalf ∨ x ∈ highHalf := by
  intro x hx
  rw [firePts_eq_union, Finset.mem_union] at hx
  exact hx

theorem highHalf_not_low : ∀ x ∈ highHalf, x ∉ lowHalf := by
  intro x hhi hlo
  have hmem : x ∈ lowHalf ∩ highHalf := Finset.mem_inter.mpr ⟨hlo, hhi⟩
  rw [lowHigh_inter] at hmem
  exact absurd hmem (Finset.notMem_empty x)

/-- The ambiguous word: `x` on the low half, `20` on the high half. -/
noncomputable def biteWord : BabyBear → BabyBear := fun x => if x ∈ lowHalf then x else 20

/-- **BITE (tightness): beyond the UDR, decoding is NOT unique.** Two DISTINCT
degree-`< 2` polynomials (`X` and `C 20`) both lie within relative distance `1/2` of
`biteWord` on the 16-point domain — so the unique-decoding conclusion genuinely fails once
the radius grows past the deployed `7/16` toward `1/2`. -/
theorem beyond_udr_two_codewords :
    ∃ p q : Polynomial BabyBear, p.natDegree < 2 ∧ q.natDegree < 2 ∧ p ≠ q ∧
      (((firePts.filter (fun x => p.eval x ≠ biteWord x)).card : ℚ))
          ≤ (1 / 2) * ((16 : ℕ) : ℚ) ∧
      (((firePts.filter (fun x => q.eval x ≠ biteWord x)).card : ℚ))
          ≤ (1 / 2) * ((16 : ℕ) : ℚ) := by
  refine ⟨X, C 20, ?_, ?_, X_ne_C 20, ?_, ?_⟩
  · rw [natDegree_X]; norm_num
  · rw [natDegree_C]; norm_num
  · -- X disagrees only on the high half (where biteWord reads 20, not x).
    have hsub : firePts.filter (fun x => (X : Polynomial BabyBear).eval x ≠ biteWord x)
        ⊆ highHalf := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxf, hne⟩ := hx
      rcases firePts_split x hxf with hlo | hhi
      · exact absurd (by simp [biteWord, hlo]) hne
      · exact hhi
    have h8 : (firePts.filter
        (fun x => (X : Polynomial BabyBear).eval x ≠ biteWord x)).card ≤ 8 := by
      simpa [highHalf_card] using Finset.card_le_card hsub
    have h8Q : (((firePts.filter
        (fun x => (X : Polynomial BabyBear).eval x ≠ biteWord x)).card : ℚ)) ≤ 8 := by
      exact_mod_cast h8
    calc (((firePts.filter
          (fun x => (X : Polynomial BabyBear).eval x ≠ biteWord x)).card : ℚ))
        ≤ 8 := h8Q
      _ ≤ (1 / 2) * ((16 : ℕ) : ℚ) := by norm_num
  · -- C 20 disagrees only on the low half (where biteWord reads x, never 20).
    have hsub : firePts.filter (fun x => (C 20 : Polynomial BabyBear).eval x ≠ biteWord x)
        ⊆ lowHalf := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxf, hne⟩ := hx
      rcases firePts_split x hxf with hlo | hhi
      · exact hlo
      · exact absurd (by simp [biteWord, highHalf_not_low x hhi]) hne
    have h8 : (firePts.filter
        (fun x => (C 20 : Polynomial BabyBear).eval x ≠ biteWord x)).card ≤ 8 := by
      simpa [lowHalf_card] using Finset.card_le_card hsub
    have h8Q : (((firePts.filter
        (fun x => (C 20 : Polynomial BabyBear).eval x ≠ biteWord x)).card : ℚ)) ≤ 8 := by
      exact_mod_cast h8
    calc (((firePts.filter
          (fun x => (C 20 : Polynomial BabyBear).eval x ≠ biteWord x)).card : ℚ))
        ≤ 8 := h8Q
      _ ≤ (1 / 2) * ((16 : ℕ) : ℚ) := by norm_num

/-! ## §7. The numeric-error tooth, reused from the committed query-soundness work.

At the deployed δ (= the UDR) and the deployed `k = 38` queries, the per-oracle query error
`(1 − δ)³⁸ < 2⁻³¹` — stated here with `1 − 7/16` so the δ THIS file audits is literally the
one whose error the tree bounds (`FriQuerySoundness.deployed_query_error_{eq,lt}` reused). -/

/-- The deployed per-oracle query error at δ = UDR = `7/16`, `k = 38`: below `2⁻³¹`. -/
theorem deployed_error_at_udr : ((1 : ℝ) - 7 / 16) ^ 38 < 1 / 2 ^ 31 := by
  rw [Dregg2.Circuit.FriQuerySoundness.deployed_query_error_eq]
  exact Dregg2.Circuit.FriQuerySoundness.deployed_query_error_lt

/-! ## §8. Axiom hygiene — every theorem kernel-clean. -/

#assert_axioms prover_logBlowup
#assert_axioms prover_numQueries
#assert_axioms prover_powBits
#assert_axioms wrap_logBlowup
#assert_axioms wrap_numQueries
#assert_axioms wrap_powBits
#assert_axioms deployed_rate
#assert_axioms wrap_rate
#assert_axioms deployed_udr
#assert_axioms wrap_udr
#assert_axioms deployed_delta_eq_udr
#assert_axioms deployed_delta_NOT_lt_udr
#assert_axioms deployed_delta_le_udr
#assert_axioms deployed_two_delta_lt_minDist
#assert_axioms deployed_udr_scaled_16
#assert_axioms deployed_udr_unique_decoding
#assert_axioms firePts_card
#assert_axioms lowHalf_card
#assert_axioms highHalf_card
#assert_axioms firePts_eq_union
#assert_axioms lowHigh_inter
#assert_axioms firePts_split
#assert_axioms highHalf_not_low
#assert_axioms fire_p_close
#assert_axioms fire_q_close
#assert_axioms deployed_udr_decoding_fires
#assert_axioms beyond_udr_two_codewords
#assert_axioms deployed_error_at_udr

end Dregg2.Circuit.DeployedUdrRegime
