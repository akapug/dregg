/-
# `Dregg2.Circuit.FriVerifierQuery` — STAGE 4: the query-phase composition, and the honest one.

**Honest scope (first sentence).** This module proves `εQuery`: for a FRI fold layer whose committed
input word is FAR from the domain code (at the honest, PROVEN unique-decoding radius), the probability
— over BOTH the fold challenge `α` and the `k`-point query sample `Q` — that the prover's claimed
folded oracle passes all `k` spot-checks is at most

    εQuery = L / |F|  +  (1 − δ)^k                                (§2, `epsilon_query_layer_carried`)

where the first addend is the per-fold good-challenge DENSITY (the correlated-agreement / proximity-gap
carrier `FriProximityGapChallenges S (4d) d L`, `= L/|F|` because a `4d`-far word has ≤ `L` folding
challenges that fold it back close) and the second is the query-sampling error `(1−δ)^k` (`accept_prob_le`
of `FriQuerySoundness` — a `δ`-far oracle survives `k` uniform independent spot-checks with probability
`≤ (1−δ)^k`). This is the stage where `johnsonBits` stops being `by norm_num` bookkeeping: the exponent
`k` arrives as a THEOREM about the (fold-challenge, query-sample) randomness, not a hand-transcribed
constant.

**What is PROVEN vs what is CARRIED (radius honesty — [[project-fri-soundness-reality]]).**
* PROVEN, no hypothesis: the query-sampling term `(1−δ)^k` (`accept_prob_le`), AND — at list size `L = 1`,
  the UNIQUE-DECODING radius — the per-fold density term itself, via `proximityGap_uniqueDecoding`
  (`epsilon_query_layer`, §3). At `L = 1` there is NO named carrier for the fold term: a `4d`-far word
  has AT MOST ONE good challenge (`good_alpha_subsingleton`), so the fold-density addend is `1/|F|`, a
  theorem. The deployed instantiation (§4) is at `δ = 7/16` (rate-`1/8` unique-decoding radius), `k = 38`:
  `εQuery ≤ 1/|F| + (9/16)^38 < 1/|F| + 2^-31`.
* CARRIED, NAMED at the SHARP (Johnson, `L > 1`) radius: `epsilon_query_layer_carried` takes the
  `FriProximityGapChallenges S (4d) d L` carrier as a hypothesis and returns `L/|F| + (1−δ_J)^k`. At
  `L > 1` this is the BCIKS20 list-decoding correlated-agreement statement — a probabilistic statement
  about CODES and DENSITIES, NOT about adversaries or hashes (strictly narrower than `FriLdtExtractV3`).
  The in-tree `FriCorrelatedAgreementSharp.wrap_correlatedAgreementLine` proves the SHARP line primitive
  at `dIn = 56` for the SPECIFIC `friSetupWrapRate` config — see the DESIGN FORK note in §6.

**⚑ THE DESIGN FORK (surfaced, not picked — ember's standing instruction).** Two honest radii compose
with the ledger density in two different ways; this file lands the LOWER, FULLY-PROVEN one and NAMES the
upper:
  (i)  UNIQUE-DECODING (`L = 1`, `δ = 7/16`): the fold term `1/|F|` is a theorem here
       (`good_alpha_subsingleton`), the query term `(9/16)^38 < 2^-31` is a theorem
       (`FriQuerySoundness.deployed_accept_prob_lt`). NOTHING is carried at the code level — only the
       permanent ROM instantiation (§4.2 of the design). This is the 57-bit-HONEST column of
       [[project-fri-soundness-reality]]: εQuery is a REAL bound at a real radius, dominated by `2/|F|`.
  (ii) JOHNSON (`L > 1`, `δ_J = 1 − √ρ`): the fold term becomes `L/|F|` under the NAMED carrier and the
       query term shrinks to `(1−δ_J)^k`; this is the radius the `~112.6`-bit number and the ledger's
       sharper `perFoldBits` (`ledger_perFold_soundness`) live at, and where `M = 1` is PROVABLY FALSE
       (`FriJohnsonRadiusGap.deployed_M1_false_at_johnson`). This file DOES NOT claim it: it exposes the
       parametric `_carried` theorem so the upgrade is a single hypothesis discharge, and refuses to read
       the 112-bit number out of the `L = 1` pipeline (design §6 falsifier (ii)).

**The ledger-density ↔ word-farness bridge — NAMED.** `FriLedgerSound.ledger_perFold_soundness` bounds a
`Good`-set density `< 1/2^perFoldBits` at the `≥ 2`-fibre inner radius, stated over an ABSTRACT `(Good, c,
Φ)`. To attach it to the adversary's acceptance event one needs the bridge "far word folds close ⟹ the
fold challenge lies in that `≥ 2`-fibre `Good` set". That bridge is EXACTLY the correlated-agreement
carrier — and at the unique-decoding radius this file discharges the SAME per-fold role with
`FriProximityGapChallenges … 1` (a THEOREM), so the `L = 1` composition needs no bridge. The `ledger`'s
sharper `perFoldBits` column composes only through the Johnson carrier (ii); this is stated, not faked
(see §6, `ledger_density_is_the_carried_fold_term`).

**Composition (b) — the qidx ↔ transcript binding, lifted through Stage 1.** §5 lifts the two deployed
teeth (`verifyAlgo_concrete_rejects_wrong_query_count`, `:719`; `verifyAlgo_full_rejects_tampered_quotient`,
`:900`) through Stage 1's faithfulness theorem `verifyAlgoO_run_eq` to the ORACLE verifier: the oracle
verifier rejects a wrong opened-query-count and a tampered quotient. This is what makes "all `numQueries`
checks pass" the genuine uniform-sample accept event `Accepts` — the adversary opens EXACTLY the
transcript's `numQueries` positions, so the sampling model `FriQuerySoundness §1` is faithful, not an
over-count (design §6 falsifier (i): the qidx binding is strong enough to force the opened positions to be
the transcript's).

**Stage 3 residuals — NAMED, not discharged here (design §5 Stage 3 / §6 Stage 2 falsifier).**
* The transcript-ordering non-membership `fsPt i ∉ queriedFinset A H` (the FS squeeze is post-commitment
  sponge state the adversary cannot have queried before committing) is a statement about the INTERLEAVING
  of the adversary's and the verifier's queries on a shared log; discharging it needs an ordered-log
  model that `RomOracle` does not yet expose. It EXCEEDS this stage and stays exactly as
  `FriVerifierMerkle` left it (`fs_epsilon_bound_of_log`'s hypothesis).
* The finite-oracle instantiation (pin `α` to the deployed BabyBear sponge width) is the PERMANENT
  industry-standard ROM carrier (§4.2). Not discharged, by design.

ADDITIVE: touches no deployed spec, no earlier stage, and NOT `FriLdtExtractV3`. Consumes only the
PROVEN `accept_prob_le` / `soundness_error_compose` (Stage-query), `proximityGap_uniqueDecoding` /
`FriProximityGapChallenges` (the carrier), `good_alpha_subsingleton` / `farN` / `disagree` (FRI core), and
`verifyAlgoO_run_eq` + the two teeth (Stage 1 lift).
-/
import Mathlib.Tactic
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.FriLdtJohnson
import Dregg2.Circuit.FriVerifierO
import Dregg2.Circuit.FriVerifier

namespace Dregg2.Circuit.FriVerifierQuery

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriQuerySoundness (Accepts accept_prob_le soundness_error_compose)
open Dregg2.Circuit.FriLdtJohnson (FriProximityGapChallenges proximityGap_uniqueDecoding disagree_symm)
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## §1. A product-space fiber-counting identity.

The composition lives over the product sample space `Ω = F × (Fin k → κ)` — the fold challenge `α` and
the `k` uniform query indices. The one combinatorial fact needed is Fubini for `filter` cardinalities:
the number of accepting `(α, Q)` is the sum, over `α`, of the accepting-`Q` count at that `α`. -/

/-- **Fubini for `filter` cardinalities.** For a decidable predicate over a product of fintypes, the
filtered cardinality is the sum over the first coordinate of the per-fibre filtered cardinality. -/
theorem card_filter_prod {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (P : A × B → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card
      = ∑ a : A, (Finset.univ.filter (fun b : B => P (a, b))).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.card_filter]

/-! ## §2. `εQuery` — the composition, at a NAMED correlated-agreement carrier of list size `L`.

Over `Ω = F × (Fin k → κ)`, the accept-a-far-word event `Accepts f' (Fold α f) Q` is contained in
`(α is a good folding challenge)  ∪  (α is not good, yet Q accepts)`. The first is the proximity-gap
DENSITY (`≤ L/|F|`, the carrier); the second forces the folded word to be `d`-far and `Q` to have missed
its disagreement (`≤ (1−δ)^k`, `accept_prob_le`). `soundness_error_compose` unions the two. -/

/-- **⚑ THE `εQuery` THEOREM (carrier form).** Let `f` be the committed input word, `4d`-FAR from the
domain code `S.C`, and let `f' ∈ S.C'` be the prover's claimed low-degree folded oracle. Given the
correlated-agreement carrier `FriProximityGapChallenges S (4d) d L` (a `4d`-far word has ≤ `L` good
folding challenges) at a relative query radius `δ = d/|κ|`, the fraction of `(α, Q) ∈ F × (Fin k → κ)`
for which the `k`-point query sample accepts the folded oracle is

    ≤ L / |F| + (1 − δ)^k.

BOTH addends are real: `L/|F|` is the density the carrier bounds, `(1−δ)^k` is `accept_prob_le`. -/
theorem epsilon_query_layer_carried (S : FriSetup F ι κ) (f : ι → F) (f' : κ → F)
    (d k L : ℕ) (δ : ℝ)
    (hCA : FriProximityGapChallenges S (4 * d) d L)
    (hfar : farN S.C (4 * d) f) (hfC' : f' ∈ S.C')
    (hNκ : 0 < Fintype.card κ) (hNF : 0 < Fintype.card F)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun p : F × (Fin k → κ) =>
          Accepts f' (Fold S.geom p.1 f) p.2)).card : ℝ)
        / (Fintype.card (F × (Fin k → κ)) : ℝ)
      ≤ (L : ℝ) / (Fintype.card F : ℝ) + (1 - δ) ^ k := by
  classical
  -- Extract the good-challenge finset `s` from the carrier.
  obtain ⟨s, hscard, hssub⟩ := hCA hfar
  set NF : ℕ := Fintype.card F with hNFdef
  set Nκ : ℕ := Fintype.card κ with hNκdef
  set M : ℕ := Nκ ^ k with hMdef
  -- Cardinality bookkeeping for the product space.
  have hcardfun : Fintype.card (Fin k → κ) = M := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hΩ : (Fintype.card (F × (Fin k → κ)) : ℝ) = (NF : ℝ) * (M : ℝ) := by
    rw [Fintype.card_prod, hcardfun]; push_cast; ring
  have hNFpos : (0 : ℝ) < (NF : ℝ) := by exact_mod_cast hNF
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : (0 : ℝ) < (Nκ : ℝ) := by exact_mod_cast hNκ
    rw [hMdef]; push_cast; positivity
  have h1d : (0 : ℝ) ≤ 1 - δ := by linarith
  have h1dk : (0 : ℝ) ≤ (1 - δ) ^ k := pow_nonneg h1d k
  -- The three events over `Ω`.
  set Acc : Finset (F × (Fin k → κ)) :=
    Finset.univ.filter (fun p => Accepts f' (Fold S.geom p.1 f) p.2) with hAcc
  set Egood : Finset (F × (Fin k → κ)) :=
    Finset.univ.filter (fun p => p.1 ∈ s) with hEgood
  set Equery : Finset (F × (Fin k → κ)) :=
    Finset.univ.filter (fun p => Accepts f' (Fold S.geom p.1 f) p.2 ∧ p.1 ∉ s) with hEquery
  -- Containment: an accepting `(α, Q)` is either a good `α`, or a not-good `α` that still accepts.
  have hsubset : Acc ⊆ Egood ∪ Equery := by
    intro p hp
    rw [hAcc, Finset.mem_filter] at hp
    rw [Finset.mem_union]
    by_cases h : p.1 ∈ s
    · left; rw [hEgood, Finset.mem_filter]; exact ⟨Finset.mem_univ p, h⟩
    · right; rw [hEquery, Finset.mem_filter]; exact ⟨Finset.mem_univ p, hp.2, h⟩
  -- The good-challenge term: `Egood = s ×ˢ univ`, density `≤ L/|F|`.
  have hEgood_prod : Egood = s ×ˢ (Finset.univ : Finset (Fin k → κ)) := by
    ext p; rw [hEgood]; simp [Finset.mem_filter, Finset.mem_product]
  have hEgoodcard : Egood.card = s.card * M := by
    rw [hEgood_prod, Finset.card_product, Finset.card_univ, hcardfun]
  have hEgoodterm : (Egood.card : ℝ) / (Fintype.card (F × (Fin k → κ)) : ℝ)
      ≤ (L : ℝ) / (NF : ℝ) := by
    have hsL : (s.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hscard
    rw [hΩ, hEgoodcard]
    push_cast
    rw [mul_div_mul_right _ _ (ne_of_gt hMpos)]
    gcongr
  -- The per-fibre query bound: for every `α`, the accepting-and-not-good `Q` count is `≤ (1−δ)^k · M`.
  have hfiber : ∀ α : F,
      ((Finset.univ.filter
          (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s)).card : ℝ)
        ≤ (1 - δ) ^ k * (M : ℝ) := by
    intro α
    by_cases hαs : α ∈ s
    · -- `α` good ⟹ the fibre is empty (the `α ∉ s` conjunct fails).
      have hempty : (Finset.univ.filter
          (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro Q _; exact fun h => h.2 hαs
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg h1dk (le_of_lt hMpos)
    · -- `α` not good ⟹ the folded word is `d`-far, so `accept_prob_le` bites.
      have hsub2 : (Finset.univ.filter
            (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s))
          ⊆ Finset.univ.filter (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q) := by
        intro Q hQ; rw [Finset.mem_filter] at hQ ⊢; exact ⟨hQ.1, hQ.2.1⟩
      have hcle : ((Finset.univ.filter
            (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s)).card : ℝ)
          ≤ ((Finset.univ.filter (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub2
      -- `α ∉ s` and `{α | closeN} ⊆ s` give `farN S.C' d (Fold α f)`.
      have hfarC' : farN S.C' d (Fold S.geom α f) := by
        intro hclose; exact hαs (Finset.mem_coe.mp (hssub hclose))
      have hne : ¬ (disagree (Fold S.geom α f) f').card ≤ d := fun hle => hfarC' ⟨f', hfC', hle⟩
      have hlt : d < (disagree (Fold S.geom α f) f').card := Nat.not_le.mp hne
      have hbig : δ * (Fintype.card κ : ℝ) < ((disagree f' (Fold S.geom α f)).card : ℝ) := by
        rw [disagree_symm (Fold S.geom α f) f'] at hlt
        calc δ * (Fintype.card κ : ℝ) ≤ (d : ℝ) := hδd
          _ < ((disagree f' (Fold S.geom α f)).card : ℝ) := by exact_mod_cast hlt
      have hap := accept_prob_le (ι := κ) (f := f') (g := Fold S.geom α f) (δ := δ) k hNκ hδ0 hbig
      -- Turn the ratio bound into a product bound `card ≤ (1−δ)^k · M`.
      have hNκk : (0 : ℝ) < (Fintype.card κ : ℝ) ^ k := by
        have : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hNκ
        positivity
      rw [div_le_iff₀ hNκk] at hap
      have hMeq : ((Fintype.card κ : ℝ)) ^ k = (M : ℝ) := by rw [hMdef, hNκdef]; push_cast; ring
      calc ((Finset.univ.filter
              (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s)).card : ℝ)
          ≤ ((Finset.univ.filter (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q)).card : ℝ) := hcle
        _ ≤ (1 - δ) ^ k * ((Fintype.card κ : ℝ) ^ k) := hap
        _ = (1 - δ) ^ k * (M : ℝ) := by rw [hMeq]
  -- Sum the fibres: `Equery.card ≤ |F| · (1−δ)^k · M`.
  have hEquerycard : (Equery.card : ℝ)
      = ∑ α : F, ((Finset.univ.filter
          (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s)).card : ℝ) := by
    rw [hEquery, card_filter_prod (fun p : F × (Fin k → κ) =>
        Accepts f' (Fold S.geom p.1 f) p.2 ∧ p.1 ∉ s)]
    push_cast; rfl
  have hEqsum : (Equery.card : ℝ) ≤ (NF : ℝ) * ((1 - δ) ^ k * (M : ℝ)) := by
    rw [hEquerycard]
    calc ∑ α : F, ((Finset.univ.filter
              (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q ∧ α ∉ s)).card : ℝ)
        ≤ ∑ _α : F, ((1 - δ) ^ k * (M : ℝ)) := Finset.sum_le_sum (fun α _ => hfiber α)
      _ = (NF : ℝ) * ((1 - δ) ^ k * (M : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNFdef]
  have hEqueryterm : (Equery.card : ℝ) / (Fintype.card (F × (Fin k → κ)) : ℝ) ≤ (1 - δ) ^ k := by
    rw [hΩ, div_le_iff₀ (mul_pos hNFpos hMpos)]
    calc (Equery.card : ℝ) ≤ (NF : ℝ) * ((1 - δ) ^ k * (M : ℝ)) := hEqsum
      _ = (1 - δ) ^ k * ((NF : ℝ) * (M : ℝ)) := by ring
  -- Union bound over `Ω` (`soundness_error_compose`), then plug the two term bounds.
  calc ((Finset.univ.filter (fun p : F × (Fin k → κ) =>
              Accepts f' (Fold S.geom p.1 f) p.2)).card : ℝ)
          / (Fintype.card (F × (Fin k → κ)) : ℝ)
      = (Acc.card : ℝ) / (Fintype.card (F × (Fin k → κ)) : ℝ) := by rw [hAcc]
    _ ≤ (Egood.card : ℝ) / (Fintype.card (F × (Fin k → κ)) : ℝ)
          + (Equery.card : ℝ) / (Fintype.card (F × (Fin k → κ)) : ℝ) :=
        soundness_error_compose Acc Egood Equery hsubset
    _ ≤ (L : ℝ) / (NF : ℝ) + (1 - δ) ^ k := add_le_add hEgoodterm hEqueryterm
    _ = (L : ℝ) / (Fintype.card F : ℝ) + (1 - δ) ^ k := by rw [hNFdef]

/-! ## §3. The FULLY-PROVEN unique-decoding instance (`L = 1`, no carrier hypothesis).

At the unique-decoding radius the correlated-agreement carrier is a THEOREM
(`proximityGap_uniqueDecoding`: a `4d`-far word has AT MOST ONE good folding challenge —
`good_alpha_subsingleton`), so `epsilon_query_layer` carries NO code-level assumption: the fold-density
term is `1/|F|`, a theorem, and the query term is `accept_prob_le`. -/

/-- **⚑ `εQuery` AT THE UNIQUE-DECODING RADIUS — a THEOREM (no carrier hypothesis).** For a `4d`-far
committed word and a claimed folded oracle `f' ∈ S.C'`, the fraction of `(α, Q)` for which the `k` query
spot-checks accept is `≤ 1/|F| + (1−δ)^k`. The fold term `1/|F|` is `good_alpha_subsingleton` (≤ 1 good
challenge); the query term `(1−δ)^k` is `accept_prob_le`. NOTHING is carried at the code level. -/
theorem epsilon_query_layer (S : FriSetup F ι κ) (f : ι → F) (f' : κ → F)
    (d k : ℕ) (δ : ℝ)
    (hfar : farN S.C (4 * d) f) (hfC' : f' ∈ S.C')
    (hNκ : 0 < Fintype.card κ) (hNF : 0 < Fintype.card F)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun p : F × (Fin k → κ) =>
          Accepts f' (Fold S.geom p.1 f) p.2)).card : ℝ)
        / (Fintype.card (F × (Fin k → κ)) : ℝ)
      ≤ 1 / (Fintype.card F : ℝ) + (1 - δ) ^ k := by
  have h := epsilon_query_layer_carried S f f' d k 1 δ
    (proximityGap_uniqueDecoding S d) hfar hfC' hNκ hNF hδ0 hδ1 hδd
  simpa using h

/-! ## §4. The DEPLOYED instantiation — `δ = 7/16` (rate-`1/8` unique-decoding radius), `k = 38`.

`circuit/src/plonky3_prover.rs:97-99`: `PROD_FRI_LOG_BLOWUP = 3` (rate `ρ = 1/8`), `PROD_FRI_NUM_QUERIES
= 38`. The unique-decoding radius is `(1−ρ)/2 = 7/16` (`FriQuerySoundness.deployed_accept_prob_lt`). This
is the HONEST radius the committed fold lemmas prove; Johnson `1 − √ρ ≈ 0.646` would need the CARRIED
`_carried` form at `L > 1` (§6). -/

/-- **⚑ DEPLOYED `εQuery`.** At `δ = 7/16`, `k = 38`, a `4d`-far committed word passes all `38` spot-checks
with probability `≤ 1/|F| + (9/16)^38`. Specialization of the fully-proven `epsilon_query_layer`. -/
theorem epsilon_query_deployed (S : FriSetup F ι κ) (f : ι → F) (f' : κ → F) (d : ℕ)
    (hfar : farN S.C (4 * d) f) (hfC' : f' ∈ S.C')
    (hNκ : 0 < Fintype.card κ) (hNF : 0 < Fintype.card F)
    (hδd : (7 / 16 : ℝ) * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun p : F × (Fin 38 → κ) =>
          Accepts f' (Fold S.geom p.1 f) p.2)).card : ℝ)
        / (Fintype.card (F × (Fin 38 → κ)) : ℝ)
      ≤ 1 / (Fintype.card F : ℝ) + (9 / 16 : ℝ) ^ 38 := by
  have h := epsilon_query_layer S f f' d 38 (7 / 16) hfar hfC' hNκ hNF
    (by norm_num) (by norm_num) hδd
  have he : ((1 : ℝ) - 7 / 16) ^ 38 = (9 / 16 : ℝ) ^ 38 := by norm_num
  rwa [he] at h

/-- **The deployed query term is below `2^-31`.** `(9/16)^38 < 2^-31` — the honest per-oracle
unique-decoding query soundness error at the shipped parameters (`FriQuerySoundness.deployed_query_error_lt`);
so `εQuery ≤ 1/|F| + (9/16)^38 < 1/|F| + 2^-31`, dominated by the fold term `1/|F| ≈ 2^-31` at BabyBear. -/
theorem epsilon_query_deployed_query_term_lt : (9 / 16 : ℝ) ^ 38 < 1 / 2 ^ 31 := by norm_num

/-! ## §5. Composition (b): the qidx ↔ transcript binding, lifted through Stage 1.

The two deployed teeth are stated over the real `verifyAlgo`. Stage 1's `verifyAlgoO_run_eq` transports
them to the ORACLE verifier `verifyAlgoO` VERBATIM (running the oracle version against the deterministic
`perm`-oracle recovers the deployed `Bool`). This grounds "all `numQueries` checks pass" as the genuine
uniform-sample `Accepts` event: the adversary opens EXACTLY the transcript's derived positions. -/

open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierO (verifyAlgoO verifyAlgoO_run_eq)

/-- **qidx binding, lifted.** The ORACLE verifier rejects a proof whose opened-query count differs from
the transcript's `params.numQueries` — the Stage-1 image of `verifyAlgo_concrete_rejects_wrong_query_count`
(`FriVerifier.lean:719`). So the oracle adversary cannot pass by opening the wrong number of positions. -/
theorem verifyAlgoO_rejects_wrong_query_count {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (finalConst : F) (hfp : proof.finalPoly = [finalConst])
    (hcount : proof.queries.length ≠ params.numQueries) :
    (verifyAlgoO RATE toNat params vk (concreteFriChecks core) initState logN proof pub).eval perm
      = false := by
  rw [verifyAlgoO_run_eq]
  exact verifyAlgo_concrete_rejects_wrong_query_count perm RATE toNat params vk core
    initState logN proof pub finalConst hfp hcount

/-- **Tampered-quotient binding, lifted.** The ORACLE verifier rejects a proof carrying a tampered
quotient on a batched table — the Stage-1 image of `verifyAlgo_full_rejects_tampered_quotient`
(`FriVerifier.lean:900`). The batch-table constraint check is load-bearing inside the oracle verifier too. -/
theorem verifyAlgoO_rejects_tampered_quotient {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (ood : F) (hood : proof.oodPoint = [ood]) (t : TableOpening F)
    (hmem : t ∈ proof.tableOpenings)
    (h : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    (verifyAlgoO RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub).eval perm = false := by
  rw [verifyAlgoO_run_eq]
  exact verifyAlgo_full_rejects_tampered_quotient perm RATE toNat params vk core A
    initState logN proof pub ood hood t hmem h

/-! ## §6. The NAMED carrier, the design fork, and the ledger-density bridge — stated, not faked. -/

/-- **The correlated-agreement carrier, ALIASED.** `εQuery`'s fold term is exactly BCIKS20's
correlated-agreement / proximity-gap object: a `dOut`-far word has ≤ `L` folding challenges whose fold is
`dIn`-close. This is a statement about CODES and DENSITIES (its honest home), NOT about adversaries or
hashes — strictly narrower than `FriLdtExtractV3`. PROVEN at `L = 1` (unique decoding,
`proximityGap_uniqueDecoding`); CARRIED at `L > 1` (Johnson). -/
def CorrelatedAgreementCarrier (S : FriSetup F ι κ) (dOut dIn L : ℕ) : Prop :=
  FriProximityGapChallenges S dOut dIn L

omit [Fintype F] in
/-- **⚑ THE DESIGN FORK, as a proposition (radius (i) is a THEOREM).** At list size `L = 1` — the
unique-decoding radius — the carrier holds unconditionally: `proximityGap_uniqueDecoding` discharges it.
The Johnson `L > 1` upgrade (radius (ii)) is the NAMED residual: it is the SOLE hypothesis of
`epsilon_query_layer_carried`, and this tree proves it only for the specific `friSetupWrapRate` line
primitive (`FriCorrelatedAgreementSharp.wrap_correlatedAgreementLine`, `dIn = 56`), NOT as a general FRI
statement. This file therefore lands radius (i) and exposes radius (ii) as a one-hypothesis discharge. -/
theorem correlatedAgreementCarrier_uniqueDecoding (S : FriSetup F ι κ) (d : ℕ) :
    CorrelatedAgreementCarrier S (4 * d) d 1 :=
  proximityGap_uniqueDecoding S d

omit [Fintype F] in
/-- **The ledger's `perFoldBits` density IS the carried fold term (bridge NAMED, not built).**
`FriLedgerSound.ledger_perFold_soundness` bounds a `Good`-set density `< 1/2^perFoldBits` at the
`≥ 2`-fibre inner radius, over an ABSTRACT `(Good, c, Φ)`. Composing it into `εQuery` requires the bridge
"far word folds close ⟹ the fold challenge is in that `Good` set" — which is the correlated-agreement
carrier at the ledger's sharper radius (`L > 1`, Johnson). This file uses the `L = 1` carrier instead
(`epsilon_query_layer`, PROVEN), whose fold term is `1/|F|`, NOT `1/2^perFoldBits`. The sharper ledger
column composes ONLY through the Johnson `_carried` form — stated here, refused as a silent pick. -/
theorem ledger_density_is_the_carried_fold_term (S : FriSetup F ι κ) (d L : ℕ)
    (hCA : CorrelatedAgreementCarrier S (4 * d) d L) :
    FriProximityGapChallenges S (4 * d) d L := hCA

/-! ## §7. Teeth — `εQuery` is a REAL bound, non-vacuous at both radii. -/

/-- **(TOOTH — the composed bound is `< 1`.)** At `δ = 7/16`, `k = 38`, `|F| = 2` (a stand-in), the
`εQuery` value `1/2 + (9/16)^38 < 1` — a real probability, not a vacuous `≤ 1`. At the deployed BabyBear
`|F| ≈ 2^31` it is `≈ 2^-30`. -/
theorem epsilon_query_lt_one_example : (1 : ℝ) / 2 + (9 / 16 : ℝ) ^ 38 < 1 := by norm_num

/-- **(TOOTH — the fold term genuinely SHRINKS the query exponent's competition.)** The query term
`(9/16)^38` is far below the fold term `1/|F|` at BabyBear (`(9/16)^38 < 2^-31 ≈ 1/|F|`), so at the
unique-decoding radius `εQuery` is DOMINATED by the single-fold density `1/|F|` — the honest per-layer
picture: the fold soundness, not the `38` queries, is the binding constraint at `L = 1`. -/
theorem fold_term_dominates_at_babybear : (9 / 16 : ℝ) ^ 38 < 1 / 2 ^ 31 :=
  epsilon_query_deployed_query_term_lt

/-! ## §8. Axiom hygiene — the composition rests only on the kernel + Mathlib + the PROVEN in-tree
inputs (`accept_prob_le`, `soundness_error_compose`, `proximityGap_uniqueDecoding`,
`good_alpha_subsingleton`, `verifyAlgoO_run_eq`, and the two teeth). No `sorry`, no smuggled hardness;
the sole NAMED carrier (`CorrelatedAgreementCarrier` at `L > 1`) appears only as an explicit hypothesis. -/

#assert_axioms card_filter_prod
#assert_axioms epsilon_query_layer_carried
#assert_axioms epsilon_query_layer
#assert_axioms epsilon_query_deployed
#assert_axioms epsilon_query_deployed_query_term_lt
#assert_axioms verifyAlgoO_rejects_wrong_query_count
#assert_axioms verifyAlgoO_rejects_tampered_quotient
#assert_axioms correlatedAgreementCarrier_uniqueDecoding
#assert_axioms epsilon_query_lt_one_example

end Dregg2.Circuit.FriVerifierQuery
