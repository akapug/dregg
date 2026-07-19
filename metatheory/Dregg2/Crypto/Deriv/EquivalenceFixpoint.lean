/-
# Dregg2.Crypto.Deriv.EquivalenceFixpoint — TEMPLATE EQUIVALENCE made RUNNABLE: the adaptive
`≅`-fixpoint composed onto the symmetric difference.

## The gap this closes

`SymbolicEquivalence.lean` PROVED decidable language equivalence
(`predRE_equivalence_decidable : Decidable (∀ w, derives w R = derives w S)`) via emptiness of the
symmetric difference `symDiff R S = (R ⋒ ¬S) ⋓ (¬R ⋒ S)` — but the underlying emptiness decision
evaluates at `emptinessBound (symDiff R S)`, a powerset bound made astronomical by the two `neg`s.
Its own header names the decision-level `#guard` AS CARRIED: the equivalence was decidable and
kernel-INTRACTABLE. `SymbolicFixpoint.lean` then landed the runnable emptiness decision
(`predRE_emptiness_decidable_fix`: worklist + `≅`-dedup, saturating in a handful of pops) — for
EMPTINESS. This module is the missing composition: run the FIXPOINT on the symmetric difference.

## What is built

* **`rigidRE_symDiff`** — the fragment obligation: `symDiff` of two `RigidFull` regexes is
  `RigidFull`. `rigidRE` recurses structurally through `alt`/`inter`/`neg`, so this is direct —
  and the `¬S` factors' LEAVES were already `S`'s own (regex-level `neg` invents no `Pred`-level
  leaf). Together with `isSymbolic_symDiff` (leaf sets concatenate), the symmetric difference of
  two runnable-fragment guards is itself in the runnable fragment.
* **`predRE_equivalence_decidable_fix`** — the RUNNABLE equivalence decision on
  `RigidSymbolicRE = {R : SymbolicRE // RigidFull R.val}`: `emptyFix`-first emptiness of the
  symmetric difference (falling back to the proven bound-based decision only on fuel exhaustion,
  so the instance is TOTAL and correct at every fuel), crossed through
  `langEq_iff_symDiff_empty`. Same correctness perimeter as `predRE_equivalence_decidable`
  (all word lengths, infinite `Value` alphabet); the tractability pole is GONE whenever the
  fixpoint saturates — which the `#guard`s below kernel-witness.
* **The deliverable `#guard`s** — the decision FIRES through `decide` on real pairs, at fixpoint
  cost (a handful of `≅`-classes), where the bound-based route needed `3^15+` residuals:
  - two genuinely DIFFERENT `symEq` guards (`role = 3` vs `role = 4` — they disagree on the
    1-frame word `[{role ↦ sym 3}]`, not merely on `[]`) decide NOT equivalent;
  - two syntactically DIFFERENT spellings of the SAME language (`role3 ⋓ role3` vs `role3`)
    decide EQUIVALENT — the pair the ACI machinery exists for;
  - `R` vs `R` decides equivalent (the reflexive pole `SymbolicEquivalence` had to prove by hand);
  - one-or-more vs zero-or-more (`rolePlus` vs `star role3` — cat/star machines differing exactly
    on `[]`) decide NOT equivalent.
  The raw `emptyFix` verdicts and the saturated frontier SIZES (≤ 8 `≅`-classes) are `#guard`ed
  alongside, on the same candidate lists the instance itself computes (`fixCands`).

Enabled by the 07-19 `predBEq` widening (AciNormal): `predBEq` descends `not`/`and`/`or`
structurally, so `Pred`-level complement leaves no longer eject a guard from `RigidFull` — though
note the `neg`s `symDiff` itself introduces are REGEX-level and were never the obstruction; the
widening's direct payoff here is that guards carrying compound leaves (e.g. `contradictionRE`)
now enter this decision's fragment too.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicFixpoint

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (derives null der RigidFull rigidRE)

/-! ## §1 The fragment obligation — `symDiff` stays rigid. -/

/-- **`rigidRE_symDiff`** — the symmetric difference of two rigid regexes is rigid: `rigidRE`
recurses structurally through the three combinators `symDiff` uses (`alt`/`inter`/`neg`), and the
leaf multiset of `symDiff R S` is exactly `R`'s and `S`'s own leaves (regex-level `neg` invents no
`Pred`-level leaf). -/
theorem rigidRE_symDiff {R S : PredRE} (hR : rigidRE R = true) (hS : rigidRE S = true) :
    rigidRE (symDiff R S) = true := by
  simp only [symDiff, PredRE.rigidRE, Bool.and_eq_true]
  exact ⟨⟨hR, hS⟩, hR, hS⟩

/-- **`RigidSymbolicRE`** — the runnable-equivalence fragment as a type: a decidable-leaf guard
(`IsSymbolic`, so a minterm cover is computable) whose root is `RigidFull` (so `simDecide` decides
`≅` on its whole reachable state space — `rigidRE_der`). -/
abbrev RigidSymbolicRE : Type := {R : SymbolicRE // RigidFull R.val}

/-- The symmetric difference of two rigid symbolic guards, bundled back into the fragment —
`isSymbolic_symDiff` for the cover half, `rigidRE_symDiff` for the dedup half. -/
def symDiffRigid (R S : RigidSymbolicRE) : RigidSymbolicRE :=
  ⟨⟨symDiff R.val.val S.val.val, isSymbolic_symDiff R.val.property S.val.property⟩,
   rigidRE_symDiff R.property S.property⟩

/-! ## §2 THE DECISION — runnable language equivalence. -/

/-- **`predRE_equivalence_decidable_fix`** — RUNNABLE decidable language equivalence
`Decidable (∀ w, derives w R = derives w S)` on the rigid symbolic fragment: the adaptive
`≅`-fixpoint emptiness decision (`predRE_emptiness_decidable_fix`) applied to the symmetric
difference, crossed through `langEq_iff_symDiff_empty`. TOTAL and correct at every fuel (fuel
exhaustion falls back to the proven bound-based decision inside the emptiness instance);
kernel-tractable exactly when the fixpoint saturates on `symDiff R S` — `#guard`-witnessed below
on machines whose `emptinessBound` route is astronomical. -/
def predRE_equivalence_decidable_fix (fuel : Nat) (R S : RigidSymbolicRE) :
    Decidable (∀ w, derives w R.val.val = derives w S.val.val) :=
  letI : Decidable (∃ w, derives w (symDiff R.val.val S.val.val) = true) :=
    predRE_emptiness_decidable_fix fuel (symDiffRigid R S).val (symDiffRigid R S).property
  decidable_of_iff _ (langEq_iff_symDiff_empty R.val.val S.val.val).symm

/-! ## §3 The deliverable `#guard`s — the equivalence decision KERNEL-RUNS on real pairs.

The candidate frames are the ones the instance itself computes (`fixCands` mirrors the
`coverOfSymbolic` arm of `predRE_emptiness_decidable_fix`), so the raw `emptyFix`/`reachFix`
guards exercise the same search the `decide` guards fire end-to-end. -/

/-- The candidate list the fixpoint instance runs on (the `coverOfSymbolic` arm, computably). -/
def fixCands (R : PredRE) : List Value :=
  match atomsOfLeaves? (leavesOf R) with
  | some A => atomCands A
  | none   => []

section Guards

/-- `role = 3` — the strict-generalization guard of `SymbolicMinterms` (`roleP = symEq "role" 3`). -/
def role3RE : PredRE := .sym roleP

/-- `role = 4` — genuinely different from `role3RE`: they DISAGREE on `[{role ↦ sym 3}]` (and on
`[{role ↦ sym 4}]`), while AGREEING on `[]` and on every frame reading neither symbol. -/
def role4RE : PredRE := .sym (.symEq "role" 4)

/-- The ACI-redundant spelling `role3 ⋓ role3` — syntactically DIFFERENT from `role3RE`, same
language. -/
def role3AltRE : PredRE := .alt role3RE role3RE

/-- Zero-or-more role frames — differs from `rolePlus` (one-or-more) exactly on `[]`. -/
def roleStarRE : PredRE := .star role3RE

-- All four are in the runnable fragment (kernel-checked)...
#guard rigidRE role3RE && rigidRE role4RE && rigidRE role3AltRE && rigidRE roleStarRE

def role3R : RigidSymbolicRE :=
  ⟨⟨role3RE, by rw [IsSymbolic]; rfl⟩, show rigidRE role3RE = true from rfl⟩
def role4R : RigidSymbolicRE :=
  ⟨⟨role4RE, by rw [IsSymbolic]; rfl⟩, show rigidRE role4RE = true from rfl⟩
def role3AltR : RigidSymbolicRE :=
  ⟨⟨role3AltRE, by rw [IsSymbolic]; rfl⟩, show rigidRE role3AltRE = true from rfl⟩
def roleStarR : RigidSymbolicRE :=
  ⟨⟨roleStarRE, by rw [IsSymbolic]; rfl⟩, show rigidRE roleStarRE = true from rfl⟩
def rolePlusR : RigidSymbolicRE := ⟨rolePlusSymbolic, rolePlus_rigid⟩

-- THE FIXPOINT SATURATES on the symmetric differences, at tiny fuel, in a HANDFUL of `≅`-classes
-- (this is the whole point — `emptinessBound (symDiff …)` with its two `neg`s is astronomical):
#guard (reachFix (fixCands (symDiff role3RE role4RE)) 64 (symDiff role3RE role4RE)).isSome
#guard ((reachFix (fixCands (symDiff role3RE role4RE)) 64
          (symDiff role3RE role4RE)).map List.length).getD 1000 ≤ 8
#guard ((reachFix (fixCands (symDiff rolePlus roleStarRE)) 256
          (symDiff rolePlus roleStarRE)).map List.length).getD 1000 ≤ 8

-- The RAW `emptyFix` verdicts on the symmetric differences: a genuinely-different pair is
-- NON-empty (`some false` — a real separating word exists), the redundant-spelling pair and the
-- reflexive pair are EMPTY (`some true` — equivalence, at ALL word lengths):
#guard emptyFix (fixCands (symDiff role3RE role4RE)) 64 (symDiff role3RE role4RE) = some false
#guard emptyFix (fixCands (symDiff role3AltRE role3RE)) 64
         (symDiff role3AltRE role3RE) = some true
#guard emptyFix (fixCands (symDiff role3RE role3RE)) 64 (symDiff role3RE role3RE) = some true
#guard emptyFix (fixCands (symDiff rolePlus roleStarRE)) 256
         (symDiff rolePlus roleStarRE) = some false

-- THE END-TO-END DECISION, fired through `decide` by kernel evaluation — fragment check, cover
-- enumeration, worklist saturation, `≅`-dedup, XOR crossing — each in a handful of pops:

-- NOT equivalent: `role = 3` vs `role = 4` (they disagree on the 1-frame word `[{role ↦ 3}]` —
-- a REAL derivative-level disagreement, not the `[]` nullability one).
#guard !(@decide _ (predRE_equivalence_decidable_fix 64 role3R role4R))
-- EQUIVALENT, on syntactically DIFFERENT terms: `role3 ⋓ role3` vs `role3`.
#guard @decide _ (predRE_equivalence_decidable_fix 64 role3AltR role3R)
-- EQUIVALENT, reflexive: `R` vs `R` — the pole `SymbolicEquivalence` could only prove by hand
-- (`equiv_refl`), now a kernel computation.
#guard @decide _ (predRE_equivalence_decidable_fix 64 role3R role3R)
-- NOT equivalent: one-or-more vs zero-or-more (cat/star machines, disagreeing exactly on `[]`).
#guard !(@decide _ (predRE_equivalence_decidable_fix 256 rolePlusR roleStarR))

/-- The separation, CONCLUDED from the running fixpoint: `role = 3` and `role = 4` are NOT
language-equivalent — some word of some length separates them. -/
theorem role3_not_equiv_role4 : ¬ ∀ w, derives w role3RE = derives w role4RE :=
  @of_decide_eq_false _ (predRE_equivalence_decidable_fix 64 role3R role4R) (by rfl)

/-- The identification, CONCLUDED from the running fixpoint: the ACI-redundant spelling and the
leaf accept EXACTLY the same words — every length, infinite alphabet. The decision-level verdict
`SymbolicEquivalence.lean` named as carried, now a `rfl`. -/
theorem role3Alt_equiv_role3 : ∀ w, derives w role3AltRE = derives w role3RE :=
  @of_decide_eq_true _ (predRE_equivalence_decidable_fix 64 role3AltR role3R) (by rfl)

/-- One-or-more vs zero-or-more, separated by the running fixpoint. -/
theorem rolePlus_not_equiv_roleStar : ¬ ∀ w, derives w rolePlus = derives w roleStarRE :=
  @of_decide_eq_false _ (predRE_equivalence_decidable_fix 256 rolePlusR roleStarR) (by rfl)

end Guards

/-! ## Axiom hygiene — the runnable equivalence is kernel-clean. -/

#assert_all_clean [
  rigidRE_symDiff,
  predRE_equivalence_decidable_fix,
  role3_not_equiv_role4,
  role3Alt_equiv_role3,
  rolePlus_not_equiv_roleStar
]

end Dregg2.Crypto.Deriv
