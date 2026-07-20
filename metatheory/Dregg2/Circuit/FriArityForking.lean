/-
# `Dregg2.Circuit.FriArityForking` — sub-seam (d) of `FriColumnDecode`: what a rewinding /
forking argument would have to PROVIDE to obtain the arity-8 Vandermonde's `8` distinct
challenges — and the arithmetic showing it CANNOT, at deployed parameters.

## The seam this addresses

`DeployedTraceExtract.DeployedFriEmbedding` (`§2`) carries two ASSUMED fields:

    chal     : BatchPublicInputs → BatchProof → (Fin 8 → BabyBear)
    chal_inj : ∀ pi π, Function.Injective (chal pi π)

They exist because the PROVED keystone `FriFoldArity.fold_close_of_arity_challenges`
(`comps = (fiberV)⁻¹ *ᵥ fvec`, `FriFoldArity.lean:107`) inverts a size-`n` Vandermonde in the
CHALLENGE and therefore needs `n = 8` DISTINCT challenges per layer — while one deployed
transcript carries exactly ONE `β` per layer (the arity-8 fold is three chained arity-2 folds
at `β, β², β⁴`, all derived from that single `β`; `FriColumnDecode.chain8_eval8`).
`FriColumnDecode.lean:45-63` names the gap "transcript rewind" and defers it. This file asks
what discharging it would COST, and answers with numbers.

## What is PROVED here

**§1 — the `n`-way forking bound, generalizing the tree's own 2-way one.** `HermineTSUF`
already PROVES `frk ≥ ε(ε/q_H − 1/|C|)` (Bellare–Neven, in a finite ℚ model, via
Cauchy–Schwarz). `nfork_probability_bound` is its `n`-way generalization —
`frk ≥ ε^n/q_H^{n−1} − ε·C(n,2)/|C|` — proved from Mathlib's power-mean inequality
`Finset.pow_sum_div_card_le_sum_pow` (Cauchy–Schwarz's `n`-th-power sibling). Same model,
same discipline, no new assumption. This is the honest statement of "what a forking argument
must provide", quantified over a `q_H`-bounded adversary with an explicit `ε`.

**§2 — THE FIRST REFUTATION: that bound is VACUOUS at `n = 8`, at deployed parameters.**
The `n`-way fork pays `q_H^{n−1}`, and at `n = 8` that is `q_H^7`:

  * over the `chal` field the tree actually models, `BabyBear` (`|F| = 2013265921 ≈ 2^30.9`):
    the RHS is `≤ 0` for every `ε ≤ 1` as soon as **`q_H ≥ 14`** (`babybear_8fork_vacuous`).
    Fourteen random-oracle queries. The threshold is TIGHT, not slack — at `q_H = 13, ε = 1`
    the RHS is genuinely positive (`babybear_8fork_positive_at_13`, the load-bearing tooth).
  * over the field the deployed prover actually samples from, `BinomialExtensionField<BabyBear,
    4>` (`|F| = p⁴ ≈ 2^123.6`, `circuit/src/plonky3_prover.rs:60`): still `≤ 0` for every
    `ε ≤ 1` once **`q_H ≥ 2^17`** (`extension_8fork_vacuous`).

So naive `n`-way forking is dead at arity 8 REGARDLESS of field width. Widening the challenge
does not save it; the `q_H^7` is what kills it.

**§3 — the Q-LINEAR route (Attema–Fehr–Klooß, TCC'22) and where IT lands.** The modern
Fiat–Shamir analysis of `(k₁,…,k_μ)`-special-sound protocols pays `(Q+1)·κ` — LINEAR in the
query bound, not `Q^{n−1}` — with `κ ≈ (n−1)/|C|` per folding round. `fsKnowledgeError` states
it, and the two evaluations are the whole finding:

  * `afk_babybear_vacuous`  : at `|C| = p` (the modelled base field), `Q = 2^29` ⟹ error `> 1`.
    Vacuous for `Q ≳ 2^28.1`.
  * `afk_extension_sound`   : at `|C| = p⁴` (the DEPLOYED extension field), `Q = 2^60` ⟹ error
    `< 2^-60`. Sound.

That contrast IS the actionable result: the arity-8 challenge must live in the degree-4
extension, and `DeployedFriEmbedding.chal`'s type — `Fin 8 → BabyBear`, the BASE field — is a
~93-bit understatement of the deployed challenge space. This is the felt-width narrowing class
(`docs/WOUND-felt-width-boundaries-2026-07-19.md`) appearing at a soundness parameter: it is a
MODEL defect, not a deployed vulnerability, and it is exactly the difference between a vacuous
and a sound bound.

**§4 — THE SECOND REFUTATION: `accept_folds` at `d = 0` is FALSE at deployed parameters, and
NO argument (forking, straight-line, or otherwise) can supply it.** `accept_folds` asserts
EXACT membership `Fold (chal i) oracle ∈ friSetupK8.C'` on `verifyAlgo`-accept. But
`verifyAlgo` spot-checks `PROD_FRI_NUM_QUERIES = 38` positions. `avoiding_tuples_card` counts
the query-tuples that miss a disagreement set exactly: `(m − |D|)^k`, and
`far_word_has_accepting_pattern` turns `|D| < m` into a NONEMPTY set of accepting patterns for
a word that is not in the code. At the deployed rate `1/8` the unique-decoding radius is
`δ = (1−ρ)/2 = 7/16`, and the survival probability is pinned in a band:
`2^-32 < (9/16)^38 < 2^-31` (`deployed_far_survival_gt` / `_lt`). Positive. So "accepting ⟹
codeword" is FALSE by counting — a `d = 0` carrier, not a lemma. The keystone is available at
positive `d` (`fold_close_of_arity_challenges` yields `closeN C (n²·d)`, i.e. `64·d` at `n = 8`);
`friProximityK8_discharge0` uses the `d = 0` specialization, which is the unobtainable one.

**§5 — THE KEY QUESTION, ANSWERED: straight-line extraction does not supply the 8 challenges.**
BCS16 straight-line extraction reads the committed ORACLE off the adversary's random-oracle
query record; it never reruns the adversary. Under Fiat–Shamir the layer challenge is a FUNCTION
of the transcript, and `straightline_cannot_supply_arity8` proves the consequence: no injective
`α : Fin 8 → F` can have every value equal to `fs t`.

**The honest scope of that theorem** (see its own docstring, which states this at length): it is
a one-line proof about ONE transcript. It does NOT establish "no straight-line extractor can see
8 distinct challenges" — a grinding adversary's query record contains many, and an extractor
observing that record sees them. What no straight-line extractor gets is `8` distinct challenges
carrying ACCEPTING fold data for a COMMON oracle, because `accept_folds` is conditioned on
`verifyAlgo`-accept and one proof completes one accepting transcript per layer. That step is an
ARGUMENT, in prose, not a theorem — its formal residue is `single_transcript_consistent_with_far`.
The two routes are incompatible in the sense that matters: the Vandermonde-in-`α` argument is a
SPECIAL-SOUNDNESS argument, and special soundness is rewinding-shaped by construction.

**The verdict, stated carefully: arity-8 does NOT force rewinding — the CHOSEN PROOF does.**
`fold_close_of_arity_challenges` is a deterministic algebraic lemma (invert a Vandermonde over
`8` challenges); it is not the soundness step real FRI uses. The straight-line-compatible step
is the PROXIMITY GAP (BCIKS20): for a SINGLE random `α`, `Pr_α[Fold α f close to C'] ≤ err`
when `f` is far. One challenge, quantified over the coin, extractor never rewinds. The tree
already has that machinery (`FriProximityGapListDecoding`, `FriCorrelatedAgreementSharp`).
So the repair is to route `friProximityK8_discharge0` through the proximity gap at one `α`
rather than the Vandermonde at eight — which also deletes `chal`/`chal_inj` outright.
`single_transcript_consistent_with_far` records why the current route can never fire: a single
transcript contributes a good-challenge set of card `1`, and `good_challenge_card_lt` permits a
far word up to `7`. No contradiction is derivable from one transcript. Ever.

## Discipline
Sorry-free; no `axiom`; no `native_decide`; no `def …Sound` carrier. Every probabilistic
statement is quantified over a `q_H`/`Q`-bounded adversary with an explicit `ε` at named
deployed parameters. `#assert_all_clean` ⊆ `{propext, Classical.choice, Quot.sound}`. ADDITIVE:
imports read-only, no shared module touched.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Dregg2.Circuit.FriFoldArity

set_option autoImplicit false

namespace Dregg2.Circuit.FriArityForking

open Finset

/-! ## §0 — the deployed parameters, as numerals.

`circuit/src/plonky3_prover.rs`: `PROD_FRI_MAX_LOG_ARITY = 3` (so the fold is 8-to-1),
`PROD_FRI_LOG_BLOWUP = 3` (rate `ρ = 1/8`), `PROD_FRI_NUM_QUERIES = 38`,
`PROD_EXT_DEGREE = 4` (challenges sampled from `BinomialExtensionField<BabyBear, 4>`). -/

/-- The BabyBear order `|F| = 15·2^27 + 1` — the field `DeployedFriEmbedding.chal` is TYPED in. -/
def babybearCard : ℚ := 2013265921

/-- The DEPLOYED challenge space `|F⁴|` — `BinomialExtensionField<BabyBear, 4>`, what the shipped
prover actually samples fold challenges from (`plonky3_prover.rs:60`). -/
def extensionCard : ℚ := 2013265921 ^ 4

/-- The deployed fold arity, `2 ^ PROD_FRI_MAX_LOG_ARITY = 8`. -/
def deployedArity : ℕ := 8

/-- `PROD_FRI_NUM_QUERIES`. -/
def deployedQueries : ℕ := 38

/-! ## §1 — the `n`-way forking bound, PROVED (generalizing the tree's 2-way `HermineTSUF`).

The Bellare–Neven finite model, exactly as `Dregg2.Crypto.HermineTSUF.Forking` sets it up: an
adversary's run is summarized by `x : Fin qH → ℚ`, where `x i` is the probability it produces an
accepting transcript whose fork index is `i`; its advantage is `ε = ∑ x i`. To fork `n` ways we
rerun from the fork index `n−1` more times; conditioned on index `i` the reruns are independent,
so the all-`n`-accept mass is `∑ x i ^ n`, and the `C(n,2)` pairwise challenge collisions cost
`ε · C(n,2)/|C|`. The 2-way case is the tree's existing `forkSuccess` / `forking_probability_bound`. -/

/-- The adversary's advantage: total accepting mass across fork indices. -/
def forgerAdv {qH : ℕ} (x : Fin qH → ℚ) : ℚ := ∑ i, x i

/-- **The `n`-way fork success** in the finite model, `n = m + 1`: the all-`n`-accept mass
`∑ x i ^ n` minus the pairwise-challenge-collision loss `ε · C(n,2)/|C|`. At `m = 1` this is
`HermineTSUF.forkSuccess` (`C(2,2) = 1`). -/
def nForkSuccess {qH : ℕ} (x : Fin qH → ℚ) (m : ℕ) (cardC : ℚ) : ℚ :=
  (∑ i, x i ^ (m + 1)) - (∑ i, x i) * (((m + 1).choose 2 : ℚ) / cardC)

/-- **The `n`-way forking bound** (`n = m + 1`): `frk ≥ ε^n / qH^{n−1} − ε·C(n,2)/|C|`. At `m = 1`
this is `HermineTSUF.ForkingProbabilityBound`. Stated as a Prop over an EXPLICIT query bound
`qH` and an EXPLICIT advantage `eps` — never over solutions or words. -/
def NForkBound (frk eps : ℚ) (m qH : ℕ) (cardC : ℚ) : Prop :=
  frk ≥ eps ^ (m + 1) / (qH : ℚ) ^ m - eps * (((m + 1).choose 2 : ℚ) / cardC)

/-- **The power-mean core**, `Fin qH` form: `(∑ xᵢ)^{m+1} / qH^m ≤ ∑ xᵢ^{m+1}`. Mathlib's
`Finset.pow_sum_div_card_le_sum_pow` (Jensen for sums of powers) — the `n`-th-power sibling of
the Cauchy–Schwarz step `HermineTSUF` uses at `n = 2`. -/
theorem adv_pow_div_le_sum_pow {qH : ℕ} (x : Fin qH → ℚ) (hx : ∀ i, 0 ≤ x i) (m : ℕ) :
    (∑ i, x i) ^ (m + 1) / (qH : ℚ) ^ m ≤ ∑ i, x i ^ (m + 1) := by
  have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin qH)))
    (f := x) (fun i _ => hx i) m
  simpa using h

/-- **`nfork_probability_bound` — the `n`-way forking bound, PROVED.** No hardness assumption, no
`sorry`: the all-accept mass dominates `ε^n/qH^{n−1}` by the power mean, and the collision loss is
exactly the subtracted term. This is the honest statement of what a forking argument DELIVERS. -/
theorem nfork_probability_bound {qH : ℕ} (x : Fin qH → ℚ) (hx : ∀ i, 0 ≤ x i) (m : ℕ)
    (cardC : ℚ) :
    NForkBound (nForkSuccess x m cardC) (forgerAdv x) m qH cardC := by
  unfold NForkBound nForkSuccess forgerAdv
  have hcore := adv_pow_div_le_sum_pow x hx m
  linarith

/-! ## §2 — THE FIRST REFUTATION: at `n = 8` the bound is VACUOUS at deployed parameters.

`NForkBound`'s right-hand side is a LOWER bound on the fork success. When it is `≤ 0` it says
nothing — `frk ≥ 0` is free. The `q_H^{n−1}` denominator makes that happen at absurdly small
query budgets once `n = 8`. -/

/-- **The vacuity criterion.** The `n`-way bound's RHS is `≤ 0` exactly when the collision loss
swallows the power-mean gain: `ε^m · |C| ≤ C(n,2) · qH^m`. -/
theorem nfork_rhs_nonpos {m qH : ℕ} {eps cardC : ℚ} (h0 : 0 ≤ eps) (hq : 0 < (qH : ℚ))
    (hC : 0 < cardC)
    (h : eps ^ m * cardC ≤ ((m + 1).choose 2 : ℚ) * (qH : ℚ) ^ m) :
    eps ^ (m + 1) / (qH : ℚ) ^ m - eps * (((m + 1).choose 2 : ℚ) / cardC) ≤ 0 := by
  have hqm : (0 : ℚ) < (qH : ℚ) ^ m := by positivity
  have hCne : cardC ≠ 0 := ne_of_gt hC
  have hkey : eps * (eps ^ m * cardC) ≤ eps * (((m + 1).choose 2 : ℚ) * (qH : ℚ) ^ m) :=
    mul_le_mul_of_nonneg_left h h0
  rw [sub_nonpos, div_le_iff₀ hqm]
  have hrw : eps * (((m + 1).choose 2 : ℚ) / cardC) * (qH : ℚ) ^ m
      = (eps * (((m + 1).choose 2 : ℚ) * (qH : ℚ) ^ m)) / cardC := by
    field_simp
  rw [hrw, le_div_iff₀ hC]
  calc eps ^ (m + 1) * cardC = eps * (eps ^ m * cardC) := by ring
    _ ≤ eps * (((m + 1).choose 2 : ℚ) * (qH : ℚ) ^ m) := hkey

/-- **THE HEADLINE REFUTATION (base field).** Over the field `DeployedFriEmbedding.chal` is
actually typed in — `BabyBear`, `|F| = 2013265921` — the `8`-way forking bound is VACUOUS
(RHS `≤ 0`) for EVERY advantage `ε ≤ 1` as soon as the adversary makes **`q_H ≥ 14`**
random-oracle queries. Fourteen. Arithmetic: `ε^8 ≤ ε`, `qH^7 ≥ 14^7 = 105413504`, and
`|F| = 2013265921 ≤ 28 · 14^7 = 2951578112`, so `ε/qH^7 ≤ ε · 28/|F|`. -/
theorem babybear_8fork_vacuous {qH : ℕ} (hq : 14 ≤ qH) {eps : ℚ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    eps ^ 8 / (qH : ℚ) ^ 7 - eps * (28 / babybearCard) ≤ 0 := by
  have hq' : (14 : ℚ) ≤ (qH : ℚ) := by exact_mod_cast hq
  have hnum : eps ^ 8 ≤ eps := by
    calc eps ^ 8 ≤ eps ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = eps := pow_one eps
  have hden : (14 : ℚ) ^ 7 ≤ (qH : ℚ) ^ 7 := by gcongr
  have hd0 : (0 : ℚ) < (14 : ℚ) ^ 7 := by norm_num
  have step1 : eps ^ 8 / (qH : ℚ) ^ 7 ≤ eps / (14 : ℚ) ^ 7 :=
    div_le_div₀ h0 hnum hd0 hden
  have step2 : eps / (14 : ℚ) ^ 7 ≤ eps * (28 / babybearCard) := by
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ h0
    unfold babybearCard; norm_num
  linarith

/-- **THE THRESHOLD IS TIGHT — the load-bearing tooth.** `14` is not slack: at `q_H = 13` and
`ε = 1` the `8`-way bound's RHS is STRICTLY POSITIVE (`1/13^7 − 28/|F| = 1/62748517 −
28/2013265921 > 0`). So `babybear_8fork_vacuous` is refuting exactly where refutation begins,
and the vacuity is a real property of the parameters rather than a lossy estimate. -/
theorem babybear_8fork_positive_at_13 :
    (0 : ℚ) < (1 : ℚ) ^ 8 / (13 : ℚ) ^ 7 - (1 : ℚ) * (28 / babybearCard) := by
  unfold babybearCard; norm_num

/-- **THE REFUTATION SURVIVES WIDENING THE FIELD (extension field).** Even over the challenge
space the DEPLOYED prover really samples from — `BinomialExtensionField<BabyBear, 4>`,
`|F⁴| = 2013265921⁴ ≈ 2^123.6` — the `8`-way bound is still VACUOUS for every `ε ≤ 1` once
`q_H ≥ 2^17 = 131072`. Arithmetic: `|F⁴| ≤ 28 · (2^17)^7 = 28 · 2^119`.

**This is the load-bearing half of the finding**: widening the challenge does NOT rescue naive
`n`-way forking. The `q_H^{n−1}` loss is what kills it, and `n = 8` makes that `q_H^7`. -/
theorem extension_8fork_vacuous {qH : ℕ} (hq : 131072 ≤ qH) {eps : ℚ} (h0 : 0 ≤ eps)
    (h1 : eps ≤ 1) :
    eps ^ 8 / (qH : ℚ) ^ 7 - eps * (28 / extensionCard) ≤ 0 := by
  have hq' : (131072 : ℚ) ≤ (qH : ℚ) := by exact_mod_cast hq
  have hnum : eps ^ 8 ≤ eps := by
    calc eps ^ 8 ≤ eps ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = eps := pow_one eps
  have hden : (131072 : ℚ) ^ 7 ≤ (qH : ℚ) ^ 7 := by gcongr
  have hd0 : (0 : ℚ) < (131072 : ℚ) ^ 7 := by norm_num
  have step1 : eps ^ 8 / (qH : ℚ) ^ 7 ≤ eps / (131072 : ℚ) ^ 7 :=
    div_le_div₀ h0 hnum hd0 hden
  have step2 : eps / (131072 : ℚ) ^ 7 ≤ eps * (28 / extensionCard) := by
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ h0
    unfold extensionCard; norm_num
  linarith

/-! ## §3 — the Q-LINEAR route (Attema–Fehr–Klooß TCC'22) and where IT lands.

Naive `n`-way forking is not the state of the art. For a `(k₁,…,k_μ)`-special-sound multi-round
protocol, AFK22 shows the Fiat–Shamir transform has knowledge error `≤ (Q+1)·κ` — LINEAR in the
query bound — where `κ ≈ ∑ (kᵢ−1)/|C|` is the interactive knowledge error. For one arity-`n`
FRI folding round, `k = n` and `κ = (n−1)/|C|`. THIS is the route that could work; the question
is at which `|C|`. -/

/-- **The AFK22 Fiat–Shamir knowledge error** for one `n`-special-sound folding round against a
`Q`-query adversary over challenge space `|C|`: `(Q+1)·(n−1)/|C|`. Explicitly `Q`-bounded, with
an explicit `ε`. -/
def fsKnowledgeError (n Q : ℕ) (cardC : ℚ) : ℚ := ((Q : ℚ) + 1) * ((n : ℚ) - 1) / cardC

/-- **VACUOUS over the modelled base field.** At `n = 8` and `|C| = |BabyBear| = 2013265921`, an
adversary with `Q = 2^29` random-oracle queries already drives the knowledge error ABOVE `1`
(`(2^29+1)·7/2013265921 ≈ 1.87`) — no soundness at all. The cutoff is `Q ≈ 2^28.1`, which is a
laughable budget for a Fiat–Shamir adversary. -/
theorem afk_babybear_vacuous : 1 < fsKnowledgeError 8 (2 ^ 29) babybearCard := by
  unfold fsKnowledgeError babybearCard; norm_num

/-- **SOUND over the DEPLOYED extension field.** At `n = 8` and `|C| = |BabyBear⁴| = 2013265921⁴`,
an adversary with `Q = 2^60` queries faces knowledge error `< 2^-60`. So the Q-linear route DOES
close the seam — but only because the deployed prover samples challenges from
`BinomialExtensionField<BabyBear, 4>`.

**Contrast `afk_babybear_vacuous`.** These two theorems together are the actionable result:
`DeployedFriEmbedding.chal : Fin 8 → BabyBear` types the challenges in the BASE field, ~93 bits
narrower than what `plonky3_prover.rs:60` actually samples, and that narrowing is exactly the
difference between "error > 1" and "error < 2^-60". A MODEL defect, not a deployed
vulnerability — and the felt-width narrowing class landing on a soundness parameter. -/
theorem afk_extension_sound : fsKnowledgeError 8 (2 ^ 60) extensionCard < 1 / 2 ^ 60 := by
  unfold fsKnowledgeError extensionCard; norm_num

/-! ## §4 — THE SECOND REFUTATION: `accept_folds` at `d = 0` is FALSE by counting.

`DeployedFriEmbedding.accept_folds` asserts EXACT membership `Fold (chal i) oracle ∈ C'` from a
single `verifyAlgo` accept. `verifyAlgo` spot-checks `PROD_FRI_NUM_QUERIES = 38` positions. A
word that disagrees with every codeword on a set `D` still passes every spot-check that misses
`D`, and those patterns are COUNTABLE and NONZERO. No forking or straight-line argument can ever
close a gap that is false by counting. -/

/-- **The accepting patterns are counted exactly**: the `k`-tuples of query positions that all
avoid a disagreement set `D ⊆ Fin m` number exactly `(m − |D|)^k`. -/
theorem avoiding_tuples_card (m k : ℕ) (D : Finset (Fin m)) :
    (Fintype.piFinset (fun _ : Fin k => Dᶜ)).card = (m - D.card) ^ k := by
  classical
  rw [Fintype.card_piFinset]
  simp [Finset.card_compl]

/-- **A FAR WORD HAS AN ACCEPTING SPOT-CHECK PATTERN.** If the disagreement set is not all of the
domain (`|D| < m`), the set of `k`-query patterns that entirely miss it is NONEMPTY — so there is
an accepting transcript for a word that is NOT in the code. This is the counting refutation of
any "`verifyAlgo` accepts ⟹ exact codeword membership" carrier. -/
theorem far_word_has_accepting_pattern (m k : ℕ) (D : Finset (Fin m)) (hD : D.card < m) :
    (Fintype.piFinset (fun _ : Fin k => Dᶜ)).Nonempty := by
  classical
  rw [← Finset.card_pos, avoiding_tuples_card]
  exact pow_pos (Nat.sub_pos_of_lt hD) k

/-- **AT DEPLOYED PARAMETERS, the survival probability is POSITIVE.** Rate `ρ = 1/8`
(`PROD_FRI_LOG_BLOWUP = 3`) gives unique-decoding radius `δ = (1−ρ)/2 = 7/16`; a `δ`-far word
survives one uniform spot-check with probability `1 − δ = 9/16`, and all `38`
(`PROD_FRI_NUM_QUERIES`) with `(9/16)^38 > 0`. -/
theorem deployed_far_survival_pos : (0 : ℚ) < (9 / 16) ^ deployedQueries := by
  unfold deployedQueries; positivity

/-- **Pinned in a band, upper**: `(9/16)^38 < 2^-31`. -/
theorem deployed_far_survival_lt : ((9 : ℚ) / 16) ^ deployedQueries < 1 / 2 ^ 31 := by
  unfold deployedQueries; norm_num

/-- **Pinned in a band, lower — the NON-VACUITY tooth**: `2^-32 < (9/16)^38`. Together with
`deployed_far_survival_lt` the deployed spot-check survival is `2^-31.54`, a REAL number strictly
between two powers of two, not an unbounded "small". A `d = 0` `accept_folds` asserts this
probability is `0`. It is not. -/
theorem deployed_far_survival_gt : (1 : ℚ) / 2 ^ 32 < ((9 : ℚ) / 16) ^ deployedQueries := by
  unfold deployedQueries; norm_num

/-! ## §5 — THE KEY QUESTION: straight-line extraction versus the arity-8 Vandermonde.

BCS16 straight-line extraction recovers the committed ORACLE from the adversary's random-oracle
query record, in ONE run, without rewinding. Under Fiat–Shamir the layer challenge is a FUNCTION
of the transcript. So a straight-line extractor sees exactly one challenge per layer — and the
Vandermonde needs eight DISTINCT ones. The following is that obstruction, proved. -/

/-- **THE SINGLE-TRANSCRIPT OBSTRUCTION.** For any Fiat–Shamir challenge derivation `fs : T → F`
and any single transcript `t`, no INJECTIVE `α : Fin 8 → F` has all `8` of its values FS-derived
from `t`. Proof: `α 0 = fs t = α 1`, and injectivity forces `(0 : Fin 8) = 1`.

**SCOPE — read this before citing it.** The proof is one line and the statement is deliberately
narrow: it says the `8` challenges cannot all be THE challenge of ONE transcript. It does NOT
say "no straight-line extractor can ever see 8 distinct challenges" — that would be FALSE. A
Fiat–Shamir adversary grinds, so its random-oracle query record genuinely contains many
`(prefix, challenge)` pairs, and a BCS16-style extractor observing that record sees all of them.

What the extractor does NOT get is `8` distinct challenges carrying ACCEPTING fold data for a
COMMON committed oracle: `accept_folds` is conditioned on `verifyAlgo`-accept, and one output
proof completes exactly one accepting transcript per layer. The other `7` are unqueried
counterfactuals — precisely the objects only a rerun produces, and §2 prices reruns out. The
formal residue of that argument is `single_transcript_consistent_with_far` below; the argument
itself is prose, not a theorem, and is labelled as such. -/
theorem straightline_cannot_supply_arity8 {T F : Type*} (fs : T → F) (t : T) (α : Fin 8 → F)
    (hinj : Function.Injective α) : ¬ ∀ i, α i = fs t := by
  intro h
  have h01 : α 0 = α 1 := by rw [h 0, h 1]
  exact absurd (hinj h01) (by decide)

/-- The general form: a single transcript supplies a SINGLETON challenge set, and no injective
`Fin n → F` with `1 < n` lands inside a singleton. -/
theorem no_injective_into_singleton {F : Type*} {n : ℕ} (hn : 1 < n) (c : F) (α : Fin n → F)
    (hinj : Function.Injective α) : ¬ ∀ i, α i = c := by
  intro h
  have hz : (0 : ℕ) < n := by omega
  have hne : (⟨0, hz⟩ : Fin n) ≠ ⟨1, hn⟩ := by simp [Fin.ext_iff]
  exact hne (hinj (by rw [h ⟨0, hz⟩, h ⟨1, hn⟩]))

/-! ### The consequence for the deployed keystone: it can never fire on one transcript. -/

open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-- **`single_transcript_consistent_with_far` — WHY THE CURRENT ROUTE CANNOT FIRE.**
`FriFoldArity.good_challenge_card_lt` bites a far word `f ∉ C` by bounding its good-challenge set
below `8`. A single Fiat–Shamir transcript contributes the singleton `{fs t}`, of card `1`. Since
`1 < 8`, the keystone's hypothesis is SATISFIED by a far word — no contradiction is derivable
from one transcript.

This is the precise sense in which sub-seam (d) is not a missing lemma but a missing EXECUTION:
the argument needs seven more runs, and §2 prices them out. -/
theorem single_transcript_consistent_with_far {T : Type*} (fs : T → BabyBear) (t : T) :
    ({fs t} : Finset BabyBear).card < deployedArity := by
  rw [Finset.card_singleton]; unfold deployedArity; norm_num

/-- **The same, exercising the REAL deployed far word `f₀`.** This genuinely invokes
`FriFoldArity.f0_good_card_lt` — the tooth that BITES `f₀` at `8` distinct challenges — on the
singleton good-challenge set a single transcript supplies. Its conclusion is `1 < 8`: TRUE. That
is the whole point. The tooth is SATISFIED, not violated, so no contradiction with `f₀ ∉ C` is
derivable from one accepting challenge. The tooth that bites at eight does not nick at one. -/
theorem f0_single_challenge_no_contradiction (c : BabyBear)
    (hc : Dregg2.Circuit.FriFoldArity.Fold Dregg2.Circuit.FriFoldArity.friSetupK8.geom c
            Dregg2.Circuit.FriFoldArity.f0 ∈ Dregg2.Circuit.FriFoldArity.friSetupK8.C') :
    ({c} : Finset BabyBear).card < 8 :=
  Dregg2.Circuit.FriFoldArity.f0_good_card_lt {c} (by
    intro a ha; rw [Finset.mem_singleton] at ha; rwa [ha])

/-! ## §6 — the verdict, as a single composed statement.

Putting §2 and §5 together: to discharge `chal`/`chal_inj` by rewinding you must run the
adversary `8` times from a common fork point, and the fork-success lower bound is non-positive
for any adversary making `≥ 14` (base field) or `≥ 2^17` (extension field) random-oracle
queries; to discharge them straight-line is impossible in principle. The route that DOES work is
neither: it is the single-challenge proximity gap, plus the AFK22 `Q`-linear accounting over the
DEPLOYED extension field (`afk_extension_sound`). -/

/-- **THE VERDICT.** At the deployed arity `8`, for any advantage `ε ≤ 1`:
* rewinding is priced out — the `8`-way fork bound is vacuous past `q_H ≥ 2^17` even over the
  extension field (`extension_8fork_vacuous`), and past `q_H ≥ 14` over the base field the model
  actually uses (`babybear_8fork_vacuous`);
* straight-line cannot supply the challenges at all (`straightline_cannot_supply_arity8`).

Hence `DeployedFriEmbedding.chal`/`chal_inj` are not dischargeable by EITHER standard route, and
the arity-8 Vandermonde must be replaced by a single-challenge proximity-gap step. -/
theorem arity8_forking_and_straightline_both_blocked
    {qH : ℕ} (hq : 131072 ≤ qH) {eps : ℚ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    {T F : Type*} (fs : T → F) (t : T) :
    (eps ^ 8 / (qH : ℚ) ^ 7 - eps * (28 / extensionCard) ≤ 0)
      ∧ (∀ α : Fin 8 → F, Function.Injective α → ¬ ∀ i, α i = fs t) :=
  ⟨extension_8fork_vacuous hq h0 h1, fun α hinj => straightline_cannot_supply_arity8 fs t α hinj⟩

#assert_all_clean [
  adv_pow_div_le_sum_pow,
  nfork_probability_bound,
  nfork_rhs_nonpos,
  babybear_8fork_vacuous,
  babybear_8fork_positive_at_13,
  extension_8fork_vacuous,
  afk_babybear_vacuous,
  afk_extension_sound,
  avoiding_tuples_card,
  far_word_has_accepting_pattern,
  deployed_far_survival_pos,
  deployed_far_survival_lt,
  deployed_far_survival_gt,
  straightline_cannot_supply_arity8,
  no_injective_into_singleton,
  single_transcript_consistent_with_far,
  f0_single_challenge_no_contradiction,
  arity8_forking_and_straightline_both_blocked
]

end Dregg2.Circuit.FriArityForking
