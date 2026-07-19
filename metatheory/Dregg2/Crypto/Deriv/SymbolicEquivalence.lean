/-
# Dregg2.Crypto.Deriv.SymbolicEquivalence — THE ~20-LINE COROLLARY the full-closure audit
# (`docs/DESIGN-symbolic-decidability-status.md`) found already assembled but unwritten:
# DECIDABLE LANGUAGE EQUIVALENCE of two deployed guards, `Decidable (∀ w, derives w R = derives w S)`.

`SymbolicDecision.lean` assembled the `n`-free symbolic emptiness decision
`predRE_emptiness_decidable : (R : DeployedRE) → Decidable (∃ w, derives w R.val = true)` on the
deployed-guard fragment `DeployedRE = {R : PredRE // IsDeployed R}`. Language EQUIVALENCE is a
symmetric-difference corollary of exactly that, and needs no new machinery:

  two guards `R`, `S` are LANGUAGE-EQUIVALENT (`∀ w, derives w R = derives w S`) iff their SYMMETRIC
  DIFFERENCE `(R ⋒ ¬S) ⋓ (¬R ⋒ S)` accepts NO word — i.e. is EMPTY.

`PredRE` has native `alt`/`inter`/`neg`, and `derives` is a Boolean HOMOMORPHISM over them
(`derives_alt`/`derives_inter`/`derives_neg`, `Correctness.lean`). So `derives w (symDiff R S)` is the
Boolean XOR `derives w R != derives w S` (`derives_symDiff`), and "accepts no word" is precisely
"the languages agree on every word" (`langEq_iff_symDiff_empty`). The one fragment obligation —
`symDiff` of two DEPLOYED guards is again DEPLOYED — is immediate from `IsDeployed`'s constructor
closure under `alt`/`inter`/`neg` (`SymbolicEmptiness.lean:243-247`), so `predRE_emptiness_decidable`
applies to the symmetric difference and DECIDES equivalence.

## What RUNS, and the honest tractability pole (inherited verbatim from the emptiness decision)

The equivalence decision is genuinely COMPUTABLE — `decidable_of_iff` off the COMPUTABLE emptiness
decision, NOT `Classical.dec`. But it inherits the emptiness decision's tractability pole EXACTLY:
`predRE_emptiness_decidable` only kernel-evaluates when `emptinessBound (symDiff R S)` is tiny, and
`symDiff` (three combinators over `R` and `S`, with two `neg`s) has a bound far past kernel reach
even for `R = S = ε`. So the DECISION-LEVEL `#guard` (fire `decide` through
`predRE_equivalence_decidable`) is NAMED AS CARRIED, exactly as `SymbolicDecision`'s negative pole is.

What DOES run at a tractable resolution, kernel-evaluated:
  * the REFLEXIVE proposition `∀ w, derives w R = derives w R` — TRUE trivially (`equiv_refl`); and its
    symmetric difference has NO short witness (`nonemptyWithin 3 (symDiff contradictionRE
    contradictionRE) = false`), a COMPLETE bounded verdict.
  * a genuinely DISTINCT deployed pair decides NOT-equivalent: `ε` accepts `[]`, `contradictionRE`
    does not, so `¬ ∀ w, derives w ε = derives w contradictionRE` (`eps_not_equiv_contradiction`),
    and their symmetric difference accepts `[]` at bound 0
    (`nonemptyWithin 0 (symDiff ε contradictionRE) = true`).

`#assert_axioms`-clean, `sorry`-free. Only `SymbolicEquivalence.lean` is authored here.
-/
import Dregg2.Crypto.Deriv.SymbolicDecision

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open PredRE (derives null der derives_alt derives_inter derives_neg)

/-! ## §1 The symmetric difference, and its fragment closure. -/

/-- **`symDiff R S`** — the SYMMETRIC DIFFERENCE regex `(R ⋒ ¬S) ⋓ (¬R ⋒ S)`, built entirely from
`PredRE`'s native `alt`/`inter`/`neg`. A word is in its language iff it lies in exactly one of `R`,
`S` (`derives_symDiff`), so `symDiff R S` is empty iff `R` and `S` are language-equivalent. -/
def symDiff (R S : PredRE) : PredRE :=
  .alt (.inter R (.neg S)) (.inter (.neg R) S)

/-- **`symDiff_deployed`** — the symmetric difference of two DEPLOYED guards is again DEPLOYED. Direct
from `IsDeployed`'s constructor closure under `alt`/`inter`/`neg` (`SymbolicEmptiness.lean:243-247`):
`symDiff` uses only those three combinators, so the corollary lands inside the SAME fragment the
emptiness decision lives on — the load-bearing fact that makes the whole corollary go through. -/
theorem symDiff_deployed {R S : PredRE} (hR : IsDeployed R) (hS : IsDeployed S) :
    IsDeployed (symDiff R S) := by
  simp only [symDiff, IsDeployed]
  exact ⟨⟨hR, hS⟩, ⟨hR, hS⟩⟩

/-! ## §2 `derives` over `symDiff` is Boolean XOR — pure Boolean algebra of the derivative. -/

/-- **`derives_symDiff`** — `derives w (symDiff R S) = (derives w R != derives w S)`. The symmetric
difference accepts `w` exactly when `R` and `S` DISAGREE on `w`. Proof is the Boolean homomorphism of
`derives` (`derives_alt`/`derives_inter`/`derives_neg`) then the two-bit XOR identity
`(a && !b) || (!a && b) = (a != b)`, discharged by casing both Booleans. -/
theorem derives_symDiff (w : List Value) (R S : PredRE) :
    derives w (symDiff R S) = (derives w R != derives w S) := by
  simp only [symDiff, derives_alt, derives_inter, derives_neg]
  cases derives w R <;> cases derives w S <;> rfl

/-! ## §3 Language equivalence ⟺ symmetric difference empty. -/

/-- **`langEq_iff_symDiff_empty`** — the CROSSING lemma: `R` and `S` accept the SAME words iff their
symmetric difference accepts NONE. Both directions collapse to `derives_symDiff`: agreement on `w`
makes `derives w (symDiff R S)` the XOR of equal bits (`false`), and conversely a `false` XOR forces
the bits equal. This is what turns EQUIVALENCE into the EMPTINESS problem the decision already
settles. -/
theorem langEq_iff_symDiff_empty (R S : PredRE) :
    (∀ w, derives w R = derives w S) ↔ ¬ ∃ w, derives w (symDiff R S) = true := by
  constructor
  · rintro hEq ⟨w, hw⟩
    rw [derives_symDiff, hEq w, bne_self_eq_false] at hw
    exact Bool.noConfusion hw
  · intro hEmpty w
    by_contra hne
    exact hEmpty ⟨w, by rw [derives_symDiff]; exact bne_iff_ne.mpr hne⟩

/-! ## §4 THE DECISION — decidable language equivalence on the deployed fragment. -/

/-- The symmetric difference of two bundled deployed guards, bundled — the object the emptiness
decision is applied to. -/
def symDiffDeployed (R S : DeployedRE) : DeployedRE :=
  ⟨symDiff R.val S.val, symDiff_deployed R.property S.property⟩

/-- **`predRE_equivalence_decidable`** — THE COROLLARY: language equivalence of two deployed guards,
`Decidable (∀ w, derives w R.val = derives w S.val)`, over words of EVERY length across the infinite
`Value` alphabet. Built by `decidable_of_iff` from the (negation of the) `n`-free emptiness decision
`predRE_emptiness_decidable` applied to `symDiffDeployed R S`, through `langEq_iff_symDiff_empty`. NOT
`Classical.dec`: the underlying emptiness decision is the COMPUTABLE `nonemptyWithin`-at-the-bound
procedure. Its tractability pole is inherited verbatim (see the header). -/
def predRE_equivalence_decidable (R S : DeployedRE) :
    Decidable (∀ w, derives w R.val = derives w S.val) :=
  letI : Decidable (∃ w, derives w (symDiff R.val S.val) = true) :=
    predRE_emptiness_decidable (symDiffDeployed R S)
  decidable_of_iff _ (langEq_iff_symDiff_empty R.val S.val).symm

/-- Registered as an INSTANCE on the fragment type, so `decide`/typeclass resolution find the
equivalence decision for any pair of bundled deployed guards. -/
instance instDecidableLangEqDeployed (R S : DeployedRE) :
    Decidable (∀ w, derives w R.val = derives w S.val) :=
  predRE_equivalence_decidable R S

/-! ## §5 The decision at both poles — REFLEXIVE true, a DISTINCT pair false. -/

/-- **`equiv_refl`** — the reflexive equivalence proposition holds trivially: every guard is
language-equivalent to itself. (This is the PROPOSITION the decision returns TRUE on; deciding it
THROUGH `predRE_equivalence_decidable` by kernel eval is intractable — `emptinessBound (symDiff R R)`
is astronomical — so the decision-level `#guard` is named as carried below, and this direct proof is
the tractable statement.) -/
theorem equiv_refl (R : DeployedRE) : ∀ w, derives w R.val = derives w R.val := fun _ => rfl

/-- The reflexive pole at the TRACTABLE resolution: `symDiff R R` has NO accepting word of length
`≤ 3` — a COMPLETE bounded verdict (`contradictionRE` is deployed, so `nonemptyWithin_iff_bounded`
makes the `false` complete, not merely a search miss). The `n`-free `false` (hence `equiv_refl`
via the decision) is the same verdict at the intractable bound. -/
theorem refl_symDiff_no_short_word :
    ¬ ∃ w, w.length ≤ 3 ∧ derives w (symDiff contradictionRE contradictionRE) = true := by
  rw [← nonemptyWithin_iff_bounded (n := 3)
        (symDiff_deployed contradiction_isDeployed contradiction_isDeployed)]
  decide

/-- **`eps_not_equiv_contradiction`** — a genuinely DISTINCT deployed pair is NOT equivalent: `ε`
accepts the empty word, `contradictionRE` accepts nothing, so they disagree on `[]`. This is the
FALSE pole of the equivalence decision, proven directly (kernel-cheap) rather than through the
intractable emptiness bound. -/
theorem eps_not_equiv_contradiction :
    ¬ ∀ w, derives w PredRE.ε = derives w contradictionRE := by
  intro h; exact Bool.noConfusion (h [])

section Guards

-- REFLEXIVE pole (tractable): the symmetric difference of a guard with itself has no short witness —
-- a COMPLETE `false` for words of length ≤ 3, the equivalence-decision `true` at a runnable depth.
#guard nonemptyWithin 3 (symDiff contradictionRE contradictionRE) = false

-- DISTINCT pole (tractable): `ε` and `contradictionRE` genuinely differ on `[]`, so their symmetric
-- difference ACCEPTS a word — nonempty already at bound 0. This is the equivalence decision's FALSE
-- verdict, witnessed at a runnable depth (the `[]` disagreement).
#guard nonemptyWithin 0 (symDiff PredRE.ε contradictionRE) = true

-- CARRIED (intractable): firing `decide` THROUGH `predRE_equivalence_decidable` itself — reflexive
-- TRUE or the distinct pair FALSE by kernel eval — requires evaluating `nonemptyWithin (emptinessBound
-- (symDiff …))`, whose bound is astronomical (two `neg`s over a power-set `⊕`). Same performance pole
-- as `SymbolicDecision.contradiction_empty_of_bound_false`; the tractable verdicts above and the
-- direct `equiv_refl` / `eps_not_equiv_contradiction` carry the content, closed by frontier `≅`-dedup.

end Guards

/-! ## Axiom hygiene — the equivalence corollary is kernel-clean. -/

#assert_all_clean [
  symDiff_deployed,
  derives_symDiff,
  langEq_iff_symDiff_empty,
  predRE_equivalence_decidable,
  equiv_refl,
  refl_symDiff_no_short_word,
  eps_not_equiv_contradiction
]

end Dregg2.Crypto.Deriv
