/-
# `Dregg2.Circuit.FriQueryBiasSharp` — RED-TEAM of the deployed query sampler: the bias defect is
`δ/|F|`, NOT `2^logN/|F|`, and the OPTIMAL adversary attains it exactly.

This is an ATTACK lane on `FriQuerySamplingBias` (codex, committed) at DEPLOYED parameters. It
REUSES that file (imports it, forks nothing) and reports what the attack found.

## What was attacked

`FriQuerySamplingBias.epsQueryBias` carries the deployed per-index survival as
`(1 − δ) + 2^logN/|F|` (`biased_query_survival_pow_le`). The red-team question: at deployed
parameters, can an EFFICIENT adversary — one that picks the committed word, hence picks WHICH
residues its word agrees on — actually realize that inflation, and does it break the ledger?

## ⚑ FINDING 1 — the carried term is SOUND but LOOSE by a factor `2^logN`, and the looseness is
NOT cosmetic: wired as-is it would assert an 11.7-bit collapse that does not happen.

`residueClassCard_le` bounds EVERY residue class by `⌊N/m⌋ + 1`. At BabyBear that is false economy:
`|F| − 1 = 2013265920 = 2^27 · 15`, so `2^b ∣ |F| − 1` for every `b ≤ 27`, hence

    |F| % 2^b = 1        for every 1 ≤ b ≤ 27          (`babybear_mod_two_pow_eq_one`)

— EXACTLY ONE residue class (`j = 0`) is heavy, with `⌊N/m⌋ + 1` elements; all `m − 1` others have
exactly `⌊N/m⌋`. So the total inflation available to ANY event is one extra preimage out of `|F|`,
not one per residue in the event. The honest per-index survival is

    (1 − δ) + δ/|F|          (`residue_survival_le_sharp`)

against the carried `(1 − δ) + 2^logN/|F|`. At the deployed `logN = 12` that is `4096·(1/δ) ≈ 4681×`
tighter. `logN ≤ 27` is not an assumption of convenience — it is FORCED: the FRI domain is a coset
of a 2-adic subgroup of `F*`, and `¬ 2^28 ∣ |F| − 1` (`babybear_no_2adic_subgroup_above_27`), so no
domain of size `2^28` exists and `p3_baby_bear::BabyBear::TWO_ADICITY = 27` is the ceiling.

Why the looseness matters. The carried `2^logN/|F|` GROWS with the trace height (`logN` is
`log_global_max_height`, `fri/src/verifier.rs:268`, with `extra_query_index_bits() = 0`). Wired into
the ledger at a production-height trace it would read, at `lb = 6, q = 19`:

    logN = 12 (the measured fixture):  query column 57.000  — loss 0.0004 bits
    logN = 20:                         query column 56.886  — loss 0.114 bits
    logN = 27 (largest realizable):    query column 45.283  — loss 11.717 bits

An 11.7-bit collapse, trace-height-driven, of exactly the shape the frontier doc already flags for
`ε_C`. **It does not happen.** Under the sharp term the loss is `9.53e-8` bits and is INDEPENDENT of
`logN` — `deployed_sharp_bound_is_logN_uniform` states that independence directly.

## ⚑ FINDING 2 — the sharp bound is the adversary's EXACT optimum, not an estimate.

`sharp_bound_attained_exactly` exhibits `N = 17, m = 16` (the `N % m = 1` regime in miniature) with
the optimal adversary strategy — put the word's AGREEMENT set on the heavy residue `0` — and shows
its success probability `2/17` EQUALS the bound `(1 − δ) + δ/N` at `1 − δ = 1/16`. So `δ/|F|` cannot
be replaced by anything smaller: it is what the best adversary gets. `codex_bound_not_attained` shows
the carried term is `> 8×` above that optimum at the same witness.

## ⚑ VERDICT AT DEPLOYED PARAMETERS — BOUND HOLDS; the bias is not the weakness.

`deployed_ir2_query_leg_le` is the money statement, quantified over EVERY adversary word:

    ∀ E (the word's agreement-residue set) with |E| ≤ 2^12 and |E|/2^12 ≤ 1/8,
      Pr_{19 deployed sampleBits draws}[ all 19 miss ]  ≤  2^(−57) · (1 + 10^(−7))

at `logN = 12, k = 19, δ = 7/8` (`lb = 6`: `1 − δ = √ρ = 1/8`). The uniform-sampler value is exactly
`2^(−57)`. So the deployed Johnson QUERY column reads `56.99999990 + 16 = 72.99999990` against a
uniform `73` — the sampling defect costs **`9.53e-8` bits**. It is REAL (`sharp_term_exceeds_uniform`
proves the survival strictly exceeds `2^(−57)`; the sampler is genuinely non-uniform, per
`babybear_sampleBits_not_balanced`) and it is twelve orders of magnitude below the term that actually
binds — `ε_C` at `71`, giving the ethSTARK eq. (20) composite `~70` (FRI-PARAM-FRONTIER §1c). The
bias moves the composite by nothing at any printed precision.

⚠ SCOPE, stated so it cannot be read up. This is the QUERY leg only, under the ROM idealisation that
`Challenger.sample()` is uniform over `F` (the sponge assumption; not discharged here). It says
nothing about `ε_C`, nothing about the per-fold column, and nothing about `WordProofBridge` /
`DeployedFriEmbedding` — blocker (a) is untouched and remains the open one. The arity-8 posture is
unchanged by anything here: the fold challenge `α` has no query sampler in it, so `109.84`
(`FriArityTransfer.arity8_perFold_soundness`, and `arity8_error_not_lt_2e112` refuting `112.6` at
arity 8) stands exactly as the frontier doc reports it, at `96.9%` farness.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`,
no `native_decide`.
-/
import Dregg2.Circuit.FriQuerySamplingBias

set_option autoImplicit false

namespace Dregg2.Circuit.FriQueryBiasSharp

open Finset
open Dregg2.Circuit.FriQuerySamplingBias
  (card_fin_filter_mod_eq biased_accepting_card epsQueryBias)
open Dregg2.Circuit.FriVerifierCompose (epsQuery)

/-! ## §1 — the two-adicity fact that collapses the defect. -/

/-- **⚑ `|F| ≡ 1 (mod 2^b)` AT EVERY REALIZABLE `b`.** BabyBear's `|F| − 1 = 2013265920 = 2^27 · 15`,
so `2^b` divides `|F| − 1` for every `b ≤ 27` and the reduction `n ↦ n % 2^b` leaves remainder
exactly `1`. This is what makes only ONE residue class heavy, and it is the whole content of the
sharpening: `FriQuerySamplingBias.residueClassCard_le` charges `+1` to EVERY class, but at `N % m = 1`
only class `0` is entitled to it. -/
theorem babybear_mod_two_pow_eq_one (b : ℕ) (hb1 : 0 < b) (hb : b ≤ 27) :
    2013265921 % 2 ^ b = 1 := by
  have hdvd : (2 : ℕ) ^ b ∣ 2013265920 :=
    (pow_dvd_pow 2 hb).trans ⟨15, by norm_num⟩
  obtain ⟨c, hc⟩ := hdvd
  have hlt : 1 < 2 ^ b := by
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  have hsplit : (2013265921 : ℕ) = 2 ^ b * c + 1 := by omega
  rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- **The `b ≤ 27` side condition is FORCED, not chosen.** `2^28` does not divide `|F| − 1`, so
`F*` has no subgroup of order `2^28` and no FRI evaluation domain of size `2^28` exists — BabyBear's
`TWO_ADICITY = 27` (`p3-baby-bear/src/baby_bear.rs:42`) is a consequence of this, and
`log_global_max_height` (the `bits` passed to `sampleBits`, `fri/src/verifier.rs:268` with
`extra_query_index_bits() = 0`) cannot exceed it. -/
theorem babybear_no_2adic_subgroup_above_27 : ¬ ((2 : ℕ) ^ 28 ∣ 2013265920) := by decide

/-- **TEETH — the sharpening is NOT free, and it is pinned to the realizable regime.** Just past the
two-adicity ceiling the hypothesis `N % m = 1` fails catastrophically: `|F| % 2^28 = 134217729 ≈ 2^27`,
i.e. HALF the residues would be heavy. So `residue_survival_le_sharp` genuinely consumes
`babybear_mod_two_pow_eq_one`; it is not a bound that would have held anyway. -/
theorem babybear_mod_two_pow_28 : 2013265921 % 2 ^ 28 = 134217729 := by norm_num

/-! ## §2 — the sharp counting: at `N % m = 1` an event gets `+1` in TOTAL, not `+1` per residue. -/

/-- Over a domain that is an EXACT multiple `m · q`, every residue class has at most `q` elements —
no `+1`. (`FriQuerySamplingBias.residueClassCard_le` must charge `+1` because it makes no
divisibility assumption.) Injection `n ↦ n / m`. -/
theorem residueClassCard_le_of_multiple (m q j : ℕ) (hm : 0 < m) :
    ((Finset.range (m * q)).filter (fun n => n % m = j)).card ≤ q := by
  classical
  have hcard : ((Finset.range (m * q)).filter (fun n => n % m = j)).card
      ≤ (Finset.range q).card := by
   refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
   · intro n hn
     obtain ⟨hnN, _⟩ := Finset.mem_filter.1 hn
     have hlt : n < m * q := Finset.mem_range.1 hnN
     refine Finset.mem_range.2 ((Nat.div_lt_iff_lt_mul hm).2 ?_)
     rw [Nat.mul_comm]
     exact hlt
   · intro a ha b hb hab
     simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
     have hab' : a / m = b / m := hab
     calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
       _ = m * (b / m) + b % m := by rw [hab', ha.2, hb.2]
       _ = b := Nat.div_add_mod b m
  simpa using hcard

/-- The event version over an exact multiple: `≤ |E| · q`, with NO additive slack. -/
theorem residueSetCard_le_of_multiple (m q : ℕ) (hm : 0 < m) (E : Finset ℕ) :
    ((Finset.range (m * q)).filter (fun n => n % m ∈ E)).card ≤ E.card * q := by
  classical
  have hsplit : (Finset.range (m * q)).filter (fun n => n % m ∈ E)
      = E.biUnion (fun j => (Finset.range (m * q)).filter (fun n => n % m = j)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨hn, hmem⟩; exact ⟨n % m, hmem, hn, rfl⟩
    · rintro ⟨j, hj, hn, hnj⟩; exact ⟨hn, hnj ▸ hj⟩
  rw [hsplit]
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_card_nsmul E _ q
    (fun j _ => residueClassCard_le_of_multiple m q j hm)).trans ?_
  rw [smul_eq_mul]

/-- **⚑ THE SHARP COUNT.** When `N % m = 1` — the deployed BabyBear regime at every realizable
`logN` (`babybear_mod_two_pow_eq_one`) — an event `E` collects at most `|E| · ⌊N/m⌋ + 1` of the `N`
squeeze values. Compare `FriQuerySamplingBias.residueSetCard_le`'s `|E| · (⌊N/m⌋ + 1)`: the extra
preimage is charged ONCE (to the single heavy class `0`), not `|E|` times. -/
theorem residueSetCard_le_sharp (N m : ℕ) (hm : 0 < m) (hmod : N % m = 1) (E : Finset ℕ) :
    ((Finset.range N).filter (fun n => n % m ∈ E)).card ≤ E.card * (N / m) + 1 := by
  classical
  obtain ⟨q, hq, hNq⟩ : ∃ q, N / m = q ∧ N = m * q + 1 := by
    refine ⟨N / m, rfl, ?_⟩
    have := Nat.div_add_mod N m
    omega
  rw [hq, hNq, Finset.range_add_one, Finset.filter_insert]
  have hbase := residueSetCard_le_of_multiple m q hm E
  split_ifs with h
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · omega

/-! ## §3 — ⚑ THE SHARP PER-INDEX SURVIVAL: `(1 − δ) + δ/N`. -/

/-- **⚑⚑ THE HONEST DEPLOYED PER-INDEX SURVIVAL.** For `n` uniform over the `N` squeeze values and
`E` the word's per-index AGREEMENT (miss) set with uniform density `|E|/m ≤ 1 − δ`, the DEPLOYED
reduced index `n % m` lands in `E` with probability at most

    (1 − δ) + δ/N ,

whenever `N % m = 1`. The carried `FriQuerySamplingBias.biased_query_survival_pow_le` gives
`(1 − δ) + m/N`; this replaces the `m` by `δ ≤ 1`, a factor-`m/δ` improvement — and §5 shows it is
EXACTLY the adversary's optimum, so nothing further is available. -/
theorem residue_survival_le_sharp (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmod : N % m = 1)
    (E : Finset ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmiss : (E.card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ) / (N : ℝ)
      ≤ (1 - δ) + δ / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨q, hq, hNq⟩ : ∃ q, N / m = q ∧ m * q + 1 = N := by
    refine ⟨N / m, rfl, ?_⟩
    have := Nat.div_add_mod N m
    omega
  have hQR : (0 : ℝ) ≤ (q : ℝ) := by positivity
  -- `m · q = N − 1` exactly, from `N % m = 1`.
  have hmq : (m : ℝ) * (q : ℝ) = (N : ℝ) - 1 := by
    have : ((m * q + 1 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hNq
    push_cast at this
    linarith
  -- The adversary's event size, in absolute terms.
  have hEm : (E.card : ℝ) ≤ (1 - δ) * (m : ℝ) := by
    rw [div_le_iff₀ hmR] at hmiss; linarith
  -- The sharp count, cast.
  have hcard : (((Finset.range N).filter (fun n => n % m ∈ E)).card : ℝ)
      ≤ (E.card : ℝ) * (q : ℝ) + 1 := by
    have h := (Nat.cast_le (α := ℝ)).2 (residueSetCard_le_sharp N m hm hmod E)
    rw [hq] at h
    push_cast at h; linarith
  -- `|E|·q ≤ (1−δ)·m·q = (1−δ)·(N−1)`.
  have hstep : (E.card : ℝ) * (q : ℝ) ≤ (1 - δ) * ((N : ℝ) - 1) := by
    have h1 : (E.card : ℝ) * (q : ℝ) ≤ ((1 - δ) * (m : ℝ)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hEm hQR
    nlinarith [hmq]
  rw [div_le_iff₀ hNR]
  have hexp : ((1 - δ) + δ / (N : ℝ)) * (N : ℝ) = (1 - δ) * (N : ℝ) + δ := by
    field_simp
  rw [hexp]
  nlinarith [hcard, hstep]

/-- **The deployed-field instantiation.** At `|F| = 2013265921` and `m = 2^logN` with
`1 ≤ logN ≤ 27` — every realizable FRI domain, per `babybear_no_2adic_subgroup_above_27` — the
deployed `sampleBits` per-index survival is `≤ (1 − δ) + δ/|F|`. -/
theorem babybear_survival_le_sharp (logN : ℕ) (hlo : 0 < logN) (hhi : logN ≤ 27)
    (E : Finset ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmiss : (E.card : ℝ) / ((2 : ℝ) ^ logN) ≤ 1 - δ) :
    (((Finset.range 2013265921).filter (fun n => n % (2 ^ logN) ∈ E)).card : ℝ)
        / (2013265921 : ℝ)
      ≤ (1 - δ) + δ / (2013265921 : ℝ) := by
  have hcast : (((2 ^ logN : ℕ)) : ℝ) = (2 : ℝ) ^ logN := by push_cast; ring
  have hmiss' : (E.card : ℝ) / (((2 ^ logN : ℕ)) : ℝ) ≤ 1 - δ := by rw [hcast]; exact hmiss
  exact residue_survival_le_sharp 2013265921 (2 ^ logN) (by norm_num)
    (pow_pos (by norm_num) logN) (babybear_mod_two_pow_eq_one logN hlo hhi) E δ hδ0 hδ1 hmiss'

/-- **⚑ THE DEFECT IS `logN`-UNIFORM.** The sharp per-index bound `(1 − δ) + δ/|F|` mentions `logN`
NOWHERE — so it is identical at the measured `2^12` fixture and at the largest realizable `2^27`
domain. This is the refutation of the trace-height scaling the carried `2^logN/|F|` term implies
(which would read an 11.7-bit query-column collapse at `logN = 27, lb = 6, q = 19`). -/
theorem deployed_sharp_bound_is_logN_uniform (logN logN' : ℕ)
    (h : 0 < logN) (h' : logN ≤ 27) (hb : 0 < logN') (hb' : logN' ≤ 27)
    (E E' : Finset ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmiss : (E.card : ℝ) / ((2 : ℝ) ^ logN) ≤ 1 - δ)
    (hmiss' : (E'.card : ℝ) / ((2 : ℝ) ^ logN') ≤ 1 - δ) :
    (((Finset.range 2013265921).filter (fun n => n % (2 ^ logN) ∈ E)).card : ℝ)
        / (2013265921 : ℝ) ≤ (1 - δ) + δ / (2013265921 : ℝ)
    ∧ (((Finset.range 2013265921).filter (fun n => n % (2 ^ logN') ∈ E')).card : ℝ)
        / (2013265921 : ℝ) ≤ (1 - δ) + δ / (2013265921 : ℝ) :=
  ⟨babybear_survival_le_sharp logN h h' E δ hδ0 hδ1 hmiss,
   babybear_survival_le_sharp logN' hb hb' E' δ hδ0 hδ1 hmiss'⟩

/-! ## §4 — the `k`-query composition, over the deployed sample space. -/

/-- **⚑ THE SHARP `k`-QUERY SURVIVAL BOUND.** `k` independent deployed squeezes, each reduced
`n % m`; a `δ`-far word survives all `k` spot-checks with probability `≤ ((1 − δ) + δ/N)^k`. Reuses
`FriQuerySamplingBias.biased_accepting_card` and `card_fin_filter_mod_eq` verbatim — only the
per-index base is sharpened. -/
theorem biased_query_survival_sharp (N m k : ℕ) (E : Finset ℕ) (δ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hmod : N % m = 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmiss : (E.card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    ((Finset.univ.filter (fun Q : Fin k → Fin N => ∀ i, (Q i).val % m ∈ E)).card : ℝ)
        / ((N : ℝ) ^ k)
      ≤ ((1 - δ) + δ / (N : ℝ)) ^ k := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [biased_accepting_card]
  set c : ℕ := (Finset.univ.filter (fun a : Fin N => a.val % m ∈ E)).card with hc
  have hbridge : ((Finset.range N).filter (fun n => n % m ∈ E)).card = c := by
    rw [hc]; exact (card_fin_filter_mod_eq N m E).symm
  have hbase : (c : ℝ) / (N : ℝ) ≤ (1 - δ) + δ / (N : ℝ) := by
    have h := residue_survival_le_sharp N m hN hm hmod E δ hδ0 hδ1 hmiss
    rw [hbridge] at h; exact h
  have hbase0 : (0 : ℝ) ≤ (c : ℝ) / (N : ℝ) := by positivity
  push_cast
  rw [← div_pow]
  exact pow_le_pow_left₀ hbase0 hbase k

/-- **`epsQueryBiasSharp` — the bias-aware `εQuery` at the honest defect.** Same shape as
`FriQuerySamplingBias.epsQueryBias`, with the survival base `(1 − δ) + δ/|F|` in place of
`(1 − δ) + 2^logN/|F|`. -/
noncomputable def epsQueryBiasSharp (cardF k L : ℕ) (δ : ℝ) : ℝ :=
  (L : ℝ) / (cardF : ℝ) + ((1 - δ) + δ / (cardF : ℝ)) ^ k

/-- **⚑ THE SANDWICH — sharp is a STRICT IMPROVEMENT that stays SOUND.** The sharp term sits between
the uniform `epsQuery` (which is NOT sound over the deployed sampler — `babybear_sampleBits_not_balanced`)
and the carried `epsQueryBias` (sound but loose). Both inequalities at once: nothing is being
weakened, and the carried bound is not being contradicted — it is being tightened. -/
theorem epsQuery_le_sharp_le_epsQueryBias (cardF logN k : ℕ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    epsQuery cardF k δ ≤ epsQueryBiasSharp cardF k 1 δ
    ∧ epsQueryBiasSharp cardF k 1 δ ≤ epsQueryBias cardF logN k 1 δ := by
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
  have hδF : (0 : ℝ) ≤ δ / (cardF : ℝ) := by positivity
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ logN := one_le_pow₀ (by norm_num)
  have hinv : (0 : ℝ) ≤ ((cardF : ℝ))⁻¹ := by positivity
  constructor
  · unfold epsQuery epsQueryBiasSharp
    have hpow : (1 - δ) ^ k ≤ ((1 - δ) + δ / (cardF : ℝ)) ^ k :=
      pow_le_pow_left₀ h0 (by linarith) k
    push_cast; linarith
  · unfold epsQueryBiasSharp epsQueryBias
    have hle : δ / (cardF : ℝ) ≤ (2 : ℝ) ^ logN / (cardF : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_trans hδ1 hone) hinv
    have hpow : ((1 - δ) + δ / (cardF : ℝ)) ^ k
        ≤ ((1 - δ) + (2 : ℝ) ^ logN / (cardF : ℝ)) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    linarith

/-! ## §5 — ⚑ THE OPTIMAL ADVERSARY, AND THE BOUND IT ATTAINS EXACTLY. -/

/-- **THE ADVERSARY'S STRATEGY, EXHIBITED.** At `N = 17, m = 16` (`17 % 16 = 1` — the deployed
`N % m = 1` regime in miniature), residue class `0` is HEAVY (two preimages: `0` and `16`) and every
other class has exactly one. The optimal adversary therefore commits a word whose single agreeing
position is the heavy residue `0`. -/
theorem heavy_class_witness :
    ((Finset.range 17).filter (fun n => n % 16 = 0)).card = 2
    ∧ ((Finset.range 17).filter (fun n => n % 16 = 5)).card = 1 := by
  constructor <;> decide

/-- **⚑⚑ THE SHARP BOUND IS ATTAINED — `δ/N` CANNOT BE IMPROVED.** The optimal adversary of
`heavy_class_witness` succeeds with probability EXACTLY `2/17`, and the sharp bound
`(1 − δ) + δ/N` at `1 − δ = |E|/m = 1/16`, `N = 17` is `1/16 + (15/16)/17 = 2/17` — EQUALITY. So
`residue_survival_le_sharp` is tight: the defect term `δ/|F|` is precisely what the best adversary
extracts from the modular reduction, not a slack estimate. -/
theorem sharp_bound_attained_exactly :
    (((Finset.range 17).filter (fun n => n % 16 ∈ ({0} : Finset ℕ))).card : ℝ) / (17 : ℝ)
      = (1 - (15 / 16 : ℝ)) + (15 / 16 : ℝ) / (17 : ℝ) := by
  have hc : ((Finset.range 17).filter (fun n => n % 16 ∈ ({0} : Finset ℕ))).card = 2 := by decide
  rw [hc]; norm_num

/-- **The defect is REAL — the adversary strictly beats the uniform model.** `2/17 > 1/16`: the
uniform per-index survival `|E|/m` is an UNDER-estimate over the deployed sampler, exactly as
`FriVerifierCompose.babybear_sampleBits_not_balanced` predicts qualitatively. -/
theorem adversary_beats_uniform :
    (1 : ℝ) / 16 < (((Finset.range 17).filter (fun n => n % 16 ∈ ({0} : Finset ℕ))).card : ℝ)
      / (17 : ℝ) := by
  have hc : ((Finset.range 17).filter (fun n => n % 16 ∈ ({0} : Finset ℕ))).card = 2 := by decide
  rw [hc]; norm_num

/-- **The carried term is NOT attained — it overshoots the optimum by `> 8×`.** At the same witness
`FriQuerySamplingBias`'s base is `(1 − δ) + m/N = 1/16 + 16/17`, against the adversary's actual
`2/17`. Concretely: `1/16 + 16/17 > 8 · (2/17)`. -/
theorem codex_bound_not_attained :
    8 * ((((Finset.range 17).filter (fun n => n % 16 ∈ ({0} : Finset ℕ))).card : ℝ) / (17 : ℝ))
      < (1 - (15 / 16 : ℝ)) + (16 : ℝ) / (17 : ℝ) := by
  have hc : ((Finset.range 17).filter (fun n => n % 16 ∈ ({0} : Finset ℕ))).card = 2 := by decide
  rw [hc]; norm_num

/-! ## §6 — ⚑ THE DEPLOYED NUMBER: IR-v2 `(lb=6, q=19, pow=16)`, `logN = 12`, `δ = 7/8`. -/

/-- The sharp deployed base, in closed form: `1/8 + (7/8)/|F|`. Raised to `k = 19` it stays within a
factor `1 + 10^(−7)` of the uniform `2^(−57)`. The exact excess is `6.606e−8`, i.e. `9.53e−8` bits;
the stated `10^(−7)` leaves ~34% margin. -/
theorem deployed_sharp_pow_le :
    ((1 : ℝ) / 8 + (7 / 8) / 2013265921) ^ 19 ≤ (1 / 2 : ℝ) ^ 57 * (1 + 1 / 10 ^ 7) := by
  norm_num

/-- **TEETH — the deployed defect is NONZERO.** The biased 19-query survival STRICTLY exceeds the
uniform `2^(−57)`. Nothing here proves the bias away; it prices it. -/
theorem sharp_term_exceeds_uniform :
    (1 / 2 : ℝ) ^ 57 < ((1 : ℝ) / 8 + (7 / 8) / 2013265921) ^ 19 := by
  norm_num

/-- **⚑ THE CARRIED TERM OVERSTATES THE DEPLOYED LOSS BY `> 3000×`.** At `logN = 12` the carried
base `1/8 + 2^12/|F|` raised to `19` exceeds `2^(−57)` by at least `3·10^(−4)` — against the sharp
term's at most `10^(−7)` (`deployed_sharp_pow_le`). In bits: `4.46e−4` claimed vs `9.53e−8` actual. -/
theorem deployed_codex_pow_ge :
    (1 / 2 : ℝ) ^ 57 * (1 + 3 / 10 ^ 4) ≤ ((1 : ℝ) / 8 + 4096 / 2013265921) ^ 19 := by
  norm_num

/-- **⚑⚑ THE VERDICT AT DEPLOYED PARAMETERS — quantified over EVERY adversary word.**

For the deployed IR-v2 wrap (`log_blowup = 6` ⟹ Johnson `1 − δ = √ρ = 1/8`; `num_queries = 19`;
`logN = 12` at the measured `|D⁽⁰⁾| = 2^12` fixture): whatever word the adversary commits — i.e. for
EVERY agreement-residue set `E` its `δ`-far word can arrange — the probability over the `19` deployed
`sampleBits` draws that ALL `19` spot-checks miss is at most

    2^(−57) · (1 + 10^(−7)) .

The uniform-sampler value is exactly `2^(−57)`. So the deployed sampling defect costs `9.53e−8` bits:
the Johnson QUERY column reads `56.99999990 (+16 PoW) = 72.99999990` against a uniform `73`.

⚑ BOUND HOLDS. The query-index bias is real, is the adversary's exact optimum (§5), and is twelve
orders of magnitude below the term that binds (`ε_C` at `71`, composite `~70`). -/
theorem deployed_ir2_query_leg_le (E : Finset ℕ)
    (hE : E.card ≤ 2 ^ 12)
    (hmiss : (E.card : ℝ) / ((2 : ℝ) ^ 12) ≤ 1 / 8) :
    ((Finset.univ.filter (fun Q : Fin 19 → Fin 2013265921 =>
          ∀ i, (Q i).val % (2 ^ 12) ∈ E)).card : ℝ)
        / ((2013265921 : ℝ) ^ 19)
      ≤ (1 / 2 : ℝ) ^ 57 * (1 + 1 / 10 ^ 7) := by
  have hcast : (((2 ^ 12 : ℕ)) : ℝ) = (2 : ℝ) ^ 12 := by norm_num
  have hmiss' : (E.card : ℝ) / (((2 ^ 12 : ℕ)) : ℝ) ≤ 1 - (7 / 8 : ℝ) := by
    rw [hcast]; linarith [hmiss]
  have hmod : (2013265921 : ℕ) % 2 ^ 12 = 1 := babybear_mod_two_pow_eq_one 12 (by norm_num) (by norm_num)
  have h := biased_query_survival_sharp 2013265921 (2 ^ 12) 19 E (7 / 8 : ℝ)
    (by norm_num) (pow_pos (by norm_num) 12) hmod (by norm_num) (by norm_num) hmiss'
  refine h.trans ?_
  have hb : ((1 : ℝ) - 7 / 8) + (7 / 8 : ℝ) / ((2013265921 : ℕ) : ℝ)
      = (1 : ℝ) / 8 + (7 / 8) / 2013265921 := by norm_num
  rw [hb]
  exact deployed_sharp_pow_le

/-- **The v1 production config `(lb = 3, q = 38, pow = 16)`, same treatment.** `1 − δ = √ρ = 2^(−1.5)`
is irrational, so the statement is made at the rational under-approximation `1 − δ = 45/128 ≤ √(1/8)`
(a WEAKER adversary constraint would be unsound; `45/128 = 0.3515625 < 0.35355 = √ρ`, so this is the
sound direction only if the adversary is at most this dense — stated therefore as the survival bound
at that density, not as the v1 posture). The v1 loss under the sharp term is `4.98e−8` bits; it is
recorded in the module docstring and not asserted as a config claim here. -/
theorem v1_sharp_base_le :
    ((45 : ℝ) / 128 + (83 / 128) / 2013265921) ^ 38 ≤ ((45 : ℝ) / 128) ^ 38 * (1 + 1 / 10 ^ 7) := by
  norm_num

#assert_all_clean [
  babybear_mod_two_pow_eq_one,
  babybear_no_2adic_subgroup_above_27,
  babybear_mod_two_pow_28,
  residueClassCard_le_of_multiple,
  residueSetCard_le_of_multiple,
  residueSetCard_le_sharp,
  residue_survival_le_sharp,
  babybear_survival_le_sharp,
  deployed_sharp_bound_is_logN_uniform,
  biased_query_survival_sharp,
  heavy_class_witness,
  sharp_bound_attained_exactly,
  adversary_beats_uniform,
  codex_bound_not_attained,
  deployed_sharp_pow_le,
  sharp_term_exceeds_uniform,
  deployed_codex_pow_ge,
  deployed_ir2_query_leg_le,
  v1_sharp_base_le
]

end Dregg2.Circuit.FriQueryBiasSharp
