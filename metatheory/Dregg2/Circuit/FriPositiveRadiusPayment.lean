/-
# `Dregg2.Circuit.FriPositiveRadiusPayment` — the POSITIVE-RADIUS quantitative decode and the
`(1−δ)^k` payment, wired from the PROVED arity-`n` keystone; plus the PRECISE reason the deployed
`friSetupK8` instance cannot exhibit it non-vacuously.

## What this closes, and what it CANNOT (the honest first sentence)

`FriFarnessReconcile` named the last residual of blocker (a): the two files reconcile the FRI-farness
radii by DETERMINISTIC COLLAPSE — under `DeployedFriEmbedding` both far events are empty on accepting
runs (`friProximityK8_discharge0`, the `d = 0` instance), so `εQuery` is discharged with `Pr = 0`, NOT
paid probabilistically at a positive radius. Making it pay needs the QUANTITATIVE decode firing at
`d > 0`: "the committed oracle is `(n²·d)`-FAR ⟹ some fold is `d`-far from the folded code", which is
the CONTRAPOSITIVE of the already-PROVED `fold_close_of_arity_challenges` (`= friProximityK8_discharge`
at `d > 0`, `FriQuerySoundness.arity_constant_bites` in its `64·d` form). That contrapositive plus the
PROVED `accept_prob_le_of_farN` is the paid `(1−δ)^k` bound.

## STEP-1 GROUND TRUTH — `friProximityK8_discharge` at `d > 0` is PROVED, not a residual

It is `fold_close_of_arity_challenges friSetupK8 hα h`, and `fold_close_of_arity_challenges` is a
FULL size-`n` Vandermonde reconstruction (BBHR18) — `d` universally quantified, no `sorry`, no
smuggled hardness, `#assert_axioms`-clean (`FriFoldArity`). It is NOT the deep FRI proximity / ethSTARK
list-decoding conjecture: that conjectural, PROBABILISTIC content lives in `εQuery`'s `L > 1` Johnson
carrier and in the two NAMED blockers of `FriVerifierCompose` (the word↔proof bridge and the
`sampleBits` uniformity defect). The deterministic reconstruction transported here is real and proved.

So we are in the "IF PROVED — wire it" case. The wiring lemmas (`far_oracle_has_far_fold`,
`far_fold_query_payment`, `far_oracle_query_payment`) are proved GENERICALLY over any
`FriSetupK F ι κ n`, so they are mechanical the instant a realistic-domain instance is supplied.

## THE PRECISE RESIDUAL — the deployed `friSetupK8` domain is TOO SMALL for a positive radius

`friSetupK8 : FriSetupK BabyBear (Fin 16) (Fin 2) 8` models the FRI coset at size `|L| = 16`, folded
domain `|κ| = 2` — the minimal genuine arity-8 instance (`FriFoldArity` §4). Farness caps at the
domain size: `|disagree f g| ≤ |ι|`. The reconstruction constant is `n²·d = 64·d`, so a positive
radius `64·d` (`d ≥ 1`) EXCEEDS `|ι| = 16` — every word is `64`-CLOSE to every codeword, so
`farN friSetupK8.C (64·d) f` is UNINHABITED (`friSetupK8_no_positive_far_oracle`). Likewise on the
folded domain `|κ| = 2`: every word is `1`-close to a constant, so `farN friSetupK8.C' d` is
UNINHABITED for `d ≥ 1` (`friSetupK8_no_positive_far_fold`). Hence the payment specialized to
`friSetupK8` is VACUOUS at `d ≥ 1` — and this is proved, not hand-waved. The residual is therefore a
MODEL-RESOLUTION gap (the size-16 coset), NOT the proximity math (proved) and NOT a conjecture: a
non-vacuous positive-radius payment needs a `FriSetupK` whose `|ι| > n²·d` and `|κ| > d` — the domain
sharpened toward realistic size (`|L| = 2^24` in production). At `d = 0` the whole story collapses to
the deterministic instance already deployed — and `far_oracle_has_far_fold` at `d = 0` RECOVERS the
committed `f0_no_injective_good` tooth (`f0_no_injective_good_via_positive_radius`), so the generic
lemma strictly generalizes it.

## Discipline
Sorry-free; no `axiom`; no `def …Sound`/`…Hard` carrier. ADDITIVE new file; all imports read-only.
`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.FriQuerySoundness

namespace Dregg2.Circuit.FriPositiveRadiusPayment

open Dregg2.Circuit.FriSoundness (closeN farN disagree mem_disagree closeN_zero_iff_mem
  farN_zero_iff_not_mem)
open Dregg2.Circuit.FriFoldArity
  (FriSetupK FriGeomK Fold friSetupK8 fold_close_of_arity_challenges f0 f0_not_mem)
open Dregg2.Circuit.FriQuerySoundness (Accepts accept_prob_le_of_farN)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ}

/-! ## §1 — THE POSITIVE-RADIUS QUANTITATIVE DECODE (generic, the contrapositive of the keystone). -/

/-- **⚑ `far_oracle_has_far_fold` — the QUANTITATIVE decode at `d > 0`.** If the committed oracle `f`
is `(n²·d)`-FAR from the domain code and the `n` fold challenges `α` are DISTINCT, then SOME fold
`Fold S.geom (α i) f` is `d`-FAR from the folded code `S.C'`. This is the exact contrapositive of the
PROVED `fold_close_of_arity_challenges` (which says: all folds `d`-close ⟹ oracle `(n²·d)`-close), so
it discharges the "bundle fails ⟹ some fold is far at a positive radius" shape `εQuery` consumes —
generalizing the committed `d = 0` `no_injective_good` (all folds IN `C'` ⟹ oracle IN `C`). -/
theorem far_oracle_has_far_fold {S : FriSetupK F ι κ n} {f : ι → F} {α : Fin n → F}
    (hα : Function.Injective α) {d : ℕ}
    (hfar : farN S.C (n ^ 2 * d) f) :
    ∃ i, farN S.C' d (Fold S.geom (α i) f) := by
  by_contra hno
  apply hfar
  refine fold_close_of_arity_challenges S hα (fun i => ?_)
  by_contra hc
  exact hno ⟨i, hc⟩

/-! ## §2 — THE `(1−δ)^k` PAYMENT at the caught far fold (generic, `accept_prob_le_of_farN`). -/

/-- **⚑ `far_fold_query_payment` — the paid probabilistic bound at ONE caught far fold.** A fold
`Fold S.geom α₀ f` that is `d`-FAR from the folded code `S.C'` passes the `k`-point query check
against ANY claimed folded oracle `f' ∈ S.C'` with probability `≤ (1−δ)^k` (over the uniform
`Q : Fin k → κ`), whenever `δ·|κ| ≤ d`. Direct `accept_prob_le_of_farN` at the folded domain `κ`,
`C := S.C'`. This is the `(1−δ)^k` addend of `εQuery`, paid at a POSITIVE radius — NOT `Pr = 0`. -/
theorem far_fold_query_payment {S : FriSetupK F ι κ n} {g : κ → F} {f' : κ → F}
    {d k : ℕ} {δ : ℝ}
    (hf'C : f' ∈ S.C') (hκ : 0 < Fintype.card κ) (hδ0 : 0 ≤ δ)
    (hfar : farN S.C' d g) (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin k → κ => Accepts g f' Q)).card : ℝ)
        / ((Fintype.card κ : ℝ) ^ k)
      ≤ (1 - δ) ^ k :=
  accept_prob_le_of_farN k hκ hδ0 hf'C hfar hδd

/-- **⚑⚑ `far_oracle_query_payment` — POSITIVE-RADIUS PAYMENT, oracle to query in one step.** From a
`(n²·d)`-FAR committed oracle `f`, `n` distinct challenges, and any claimed folded oracle `f' ∈ S.C'`,
there EXISTS a fold index `i` whose fold-check passes the `k`-query sample with probability
`≤ (1−δ)^k`. This is the compose file's `εQuery` addend attached to the arity-`n` FRI proximity at a
genuine positive radius: `far_oracle_has_far_fold` (the PROVED keystone's contrapositive) catches the
far fold, `far_fold_query_payment` (`accept_prob_le_of_farN`) pays it — replacing the deterministic
`Pr = 0` collapse of `FriFarnessReconcile`. -/
theorem far_oracle_query_payment {S : FriSetupK F ι κ n} {f : ι → F} {f' : κ → F}
    {α : Fin n → F} {d k : ℕ} {δ : ℝ}
    (hα : Function.Injective α) (hfar : farN S.C (n ^ 2 * d) f)
    (hf'C : f' ∈ S.C') (hκ : 0 < Fintype.card κ) (hδ0 : 0 ≤ δ)
    (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    ∃ i, ((Finset.univ.filter (fun Q : Fin k → κ =>
            Accepts (Fold S.geom (α i) f) f' Q)).card : ℝ)
          / ((Fintype.card κ : ℝ) ^ k)
        ≤ (1 - δ) ^ k := by
  obtain ⟨i, hfi⟩ := far_oracle_has_far_fold hα hfar
  exact ⟨i, far_fold_query_payment hf'C hκ hδ0 hfi hδd⟩

/-! ## §3 — THE PRECISE RESIDUAL: `friSetupK8`'s size-16 domain is TOO SMALL for a positive radius. -/

/-- Every folded word over the size-`2` domain is `1`-CLOSE to a constant (`S.C'` = constants): pick
the constant `f 0`, disagreeing with `f` only possibly at the single point `1`. -/
theorem friSetupK8_folded_close_one (f : Fin 2 → BabyBear) : closeN friSetupK8.C' 1 f := by
  refine ⟨fun _ => f 0, ⟨f 0, rfl⟩, ?_⟩
  have hsub : disagree f (fun _ => f 0) ⊆ ({1} : Finset (Fin 2)) := by
    intro x hx
    rw [mem_disagree] at hx
    fin_cases x
    · exact absurd rfl hx
    · exact Finset.mem_singleton_self 1
  calc (disagree f (fun _ => f 0)).card
      ≤ ({1} : Finset (Fin 2)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton 1

/-- **⚑ THE FOLDED-DOMAIN FARNESS IS UNINHABITED AT `d ≥ 1`.** Over `friSetupK8`'s size-`2` folded
domain no word is `d`-far from `S.C'` for any `d ≥ 1` — every word is `1`-close (`≤ d`-close). So the
`d`-far fold hypothesis of `far_fold_query_payment` CANNOT be met at `friSetupK8` with `d ≥ 1`: the
positive-radius payment is VACUOUS there. -/
theorem friSetupK8_no_positive_far_fold (f : Fin 2 → BabyBear) {d : ℕ} (hd : 1 ≤ d) :
    ¬ farN friSetupK8.C' d f := by
  intro hfar
  obtain ⟨g, hg, hcard⟩ := friSetupK8_folded_close_one f
  exact hfar ⟨g, hg, le_trans hcard hd⟩

/-- **⚑ THE ORACLE-DOMAIN FARNESS IS UNINHABITED AT RADIUS `64·d`, `d ≥ 1`.** Over `friSetupK8`'s
size-`16` domain every word is `≤ 16`-close to the zero codeword, and `64·d ≥ 64 > 16` for `d ≥ 1`, so
no word is `(64·d)`-far from `friSetupK8.C`. Hence the `(n²·d) = 64·d`-far oracle hypothesis of
`far_oracle_query_payment` CANNOT be met at `friSetupK8` with `d ≥ 1`. -/
theorem friSetupK8_no_positive_far_oracle (f : Fin 16 → BabyBear) {d : ℕ} (hd : 1 ≤ d) :
    ¬ farN friSetupK8.C (64 * d) f := by
  intro hfar
  apply hfar
  refine ⟨0, friSetupK8.C.zero_mem, ?_⟩
  have h : (disagree f (0 : Fin 16 → BabyBear)).card ≤ 16 := by
    have := Finset.card_le_univ (disagree f (0 : Fin 16 → BabyBear))
    rwa [Fintype.card_fin] at this
  omega

/-- **⚑⚑ THE RESIDUAL, AS A THEOREM.** For the DEPLOYED `friSetupK8` and any `d ≥ 1`, BOTH the
`(64·d)`-far oracle premise and the `d`-far fold premise of the positive-radius payment are
UNINHABITED. So `far_oracle_query_payment` at `friSetupK8`, `d ≥ 1` is vacuously satisfiable / never
fires: the positive-radius payment is not exhibitable at the size-16 model. This pins the residual to
DOMAIN SIZE — not the proximity math (`far_oracle_has_far_fold` is proved) and not a conjecture. -/
theorem positive_radius_payment_vacuous_at_friSetupK8 {d : ℕ} (hd : 1 ≤ d) :
    (∀ f : Fin 16 → BabyBear, ¬ farN friSetupK8.C (64 * d) f)
      ∧ (∀ g : Fin 2 → BabyBear, ¬ farN friSetupK8.C' d g) :=
  ⟨fun f => friSetupK8_no_positive_far_oracle f hd,
   fun g => friSetupK8_no_positive_far_fold g hd⟩

/-! ## §4 — TEETH: `d = 0` recovers the committed deterministic tooth; the payment is a real prob. -/

/-- **`d = 0` RECOVERS `f0_no_injective_good`.** At the honest distance `d = 0` (`n²·0 = 0`), the
generic `far_oracle_has_far_fold` specializes to: the frequency-8 far word `f0` (`∉ friSetupK8.C`)
admits no `8` distinct challenges all folding it INTO `friSetupK8.C'` — the committed
`FriFoldArity.f0_no_injective_good`, re-derived through the positive-radius lemma. This witnesses that
`far_oracle_has_far_fold` STRICTLY GENERALIZES the deployed `d = 0` instance, and is non-vacuous at
`d = 0`: the far side is inhabited (`f0`). -/
theorem f0_no_injective_good_via_positive_radius :
    ¬ ∃ α : Fin 8 → BabyBear, Function.Injective α ∧
        ∀ i, Fold friSetupK8.geom (α i) f0 ∈ friSetupK8.C' := by
  rintro ⟨α, hα, hg⟩
  have hfar : farN friSetupK8.C (8 ^ 2 * 0) f0 := by
    rw [Nat.mul_zero, farN_zero_iff_not_mem]; exact f0_not_mem
  obtain ⟨i, hfi⟩ := far_oracle_has_far_fold hα hfar
  rw [farN_zero_iff_not_mem] at hfi
  exact hfi (hg i)

/-- **THE PAYMENT IS A REAL PROBABILITY (`< 1`), NOT VACUOUS `≤ 1`.** At the deployed folded
unique-decoding radius `δ = 7/16` and `k = 38` queries, the paid `(1−δ)^k = (9/16)^38 < 1` — a genuine
sub-`1` acceptance probability. So `far_fold_query_payment`'s bound, when its `d`-far fold premise is
met (a larger-domain instance), genuinely constrains the adversary rather than restating `≤ 1`. -/
theorem payment_lt_one_deployed : (1 - (7 / 16 : ℝ)) ^ 38 < 1 := by norm_num

/-- **The paid term equals the deployed `(9/16)^38`** — the same query-soundness figure
`FriQuerySoundness.deployed_query_error_lt` bounds below `2^-31`, now attached to the arity-`n`
positive-radius decode. -/
theorem payment_eq_deployed : (1 - (7 / 16 : ℝ)) ^ 38 = (9 / 16 : ℝ) ^ 38 := by norm_num

#assert_axioms far_oracle_has_far_fold
#assert_axioms far_fold_query_payment
#assert_axioms far_oracle_query_payment
#assert_axioms friSetupK8_folded_close_one
#assert_axioms friSetupK8_no_positive_far_fold
#assert_axioms friSetupK8_no_positive_far_oracle
#assert_axioms positive_radius_payment_vacuous_at_friSetupK8
#assert_axioms f0_no_injective_good_via_positive_radius

end Dregg2.Circuit.FriPositiveRadiusPayment
