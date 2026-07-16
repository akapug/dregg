/-
# `Dregg2.Crypto.HardQuantVacuity` — the `*HardQuant` floor family carries NO problem content.
TEETH for the VACUITY SWEEP (2026-07-16).

## What this file proves

`ProbCrypto` defines FIVE named "quantitative hardness floors":

  * `MSISHardQuantShape  {S} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)`
  * `MLWEHardQuantShape  {S} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)`
  * `DLHardQuantShape    {S} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)`
  * `HashCRHardQuantShape{S} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)`
  * `DecisionMLWEHardQuantShape {S} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)`

They are **the same `Prop`** (§1, `Iff.rfl` five ways). Nothing in any of them mentions a lattice, a
curve, a hash, `IsMSISSolution`, or a distinguishing game: the problem lives ENTIRELY in the name and
the docstring. `DecisionMLWEHardQuantShape`'s own doc says *"The **intended** `adv` is a
`DecisionFamily.adv`"* — **intended**, never enforced. That is the `CoCurvilinearity` defect verbatim
(a constraint stated in prose is not a constraint), one level up: here the prose is the whole problem.

**The consumers are hypothesis application.** Every "re-grounded keystone" riding this family has the
shape

    theorem <problem>_advantage_bound {S} (adv : S → Ensemble) (s : S) (hfloor : <X>HardQuant adv) :
        Negl (adv s)

whose hypothesis UNFOLDS to `∀ s, Negl (adv s)` and whose conclusion is that hypothesis at `s`. It is
`hfloor s` — a `P → P` instantiation. §2 proves the point the only way it can be proved: the SAME
statement is derived here from the **wrong** floor (`HashCRHardQuantShape`), and from no floor content at
all. A theorem named `lattice_vrf_uniqueness_advantage_bound` that follows from the HASH floor is not
about lattice VRF uniqueness. Affected (statement-identical, checked 2026-07-16):
`VrfRegrounded.lattice_vrf_uniqueness_advantage_bound`,
`VrfRegrounded.lattice_vrf_uniqueness_with_guessing_bound`,
`ThreadAdvantageBound.forger_advantage_bound_under_msis`,
`ThreadAdvantageBound.forger_advantage_with_challenge_bound`,
`ThreadAdvantageBound.decision_distinguisher_advantage_bound`,
`ThreadAdvantageBound.lossy_id_advantage_bound`.

## §3 — THE DILEMMA (the load-bearing result)

The tree's own lemmas close both horns. `adv` is either tied to the problem or it is not:

* **Horn A — tie `adv` to MSIS and the floor is FALSE at deployed parameters.** The one `adv` in the
  tree genuinely indexed by MSIS solving is `FloorBridge.msisSolverAdv`, and
  `CryptoFloorTeeth.msisHardQuant_solverAdv_iff_msisHard` proves
  `MSISHardQuantShape (msisSolverAdv A β) ↔ Lattice.MSISHard A β` — the Boolean floor verbatim, which is
  FALSE at a compressing `A` (pigeonhole). So on the MSIS-tied instantiation every consumer is
  VACUOUSLY true.
* **Horn B — leave `adv` untied and the floor holds while MSIS is COMPLETELY BROKEN.** `guessAdv`
  (`fun l => 1/2^l`), the tree's own non-vacuity witness for the "proper" floor, mentions no `A`, no
  `β`, no `IsMSISSolution`. §3 proves `MSISHardQuantShape (fun _ : Unit => guessAdv)` holds SIMULTANEOUSLY
  with `¬ MSISHard (augmented id 1) 0` — the floor is satisfied in a world where the MSIS instance it
  is named after is refuted. It constrains nothing about MSIS.

Either way the "re-grounded" keystones carry no MSIS content. This is not a claim that the concrete-
security *direction* is wrong — it is the honest statement of where the wiring currently stops.

## §4 — why the existing non-vacuity test did not catch it (the METHOD tooth)

`CryptoFloorTeeth.proper_floor_is_genuine` offers, as evidence that the floor is "a GENUINE assumption
— satisfiable AND refutable — not a theorem", the pair (`msisHardQuant_guess_holds`,
`msisHardQuant_const_one_refuted`). §4 exhibits `SheepCountingHardQuant` — same shape, name chosen to
mean nothing — and proves it passes that **exact** test, while being *definitionally* `MSISHardQuantShape`.
So "satisfiable AND refutable" measures the SHAPE of a predicate over an arbitrary `adv`; it cannot
see whether the floor is ABOUT its named problem. The test is necessary, not sufficient — and it is
the falsifier-confusion of the sweep's precedent #2 at the meta level: refuting `MSISHardQuantShape` at
`adv := const 1` refutes the PREDICATE at a chosen argument, which says nothing about whether any
CONSUMER carries content.

## What is NOT claimed

The Boolean floors (`Lattice.MSISHard` and friends) were already known-broken and are doc-marked as
such; this file does not re-litigate them. Nor is any downstream theorem WRONG: they are all true.
The finding is that they are true for a reason that has nothing to do with their names. The repair
(out of this lane's scope, named with its consumer impact in `docs/deos/VACUITY-SWEEP.md`) is to index
`adv` by a genuine RESOURCE-BOUNDED adversary against the actual problem relation, so that
`MSISHardQuantShape adv` is neither the Boolean floor (Horn A) nor problem-free (Horn B).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`. Every verdict
in this file is PROVED, not asserted — the sweep exists because three carriers looked rigorous in prose.
-/
import Dregg2.Crypto.CryptoFloorTeeth
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.VrfRegrounded
import Dregg2.Tactics

namespace Dregg2.Crypto.HardQuantVacuity

open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.CryptoFloorTeeth
open Dregg2.Crypto.FloorBridge
open Dregg2.Crypto.HermineSelfTargetMSIS

set_option autoImplicit false

/-! ## §1 — the five named floors are ONE `Prop`.

Five names, one predicate. A proof "under the MSIS floor" IS a proof "under the hash-CR floor": the
names are not distinguishable by anything the kernel can see. -/

/-- **TOOTH 1 — the five `*HardQuant` floors are definitionally the same `Prop`.** Each `Iff` is
`Iff.rfl`: no unfolding, no lemma, nothing to prove — because there is nothing there to distinguish.
Whatever separates MSIS from discrete-log from hash-collision-resistance, it is not in these defs. -/
theorem the_five_floors_are_one_prop {S : Type*} (adv : S → Ensemble) :
    (MSISHardQuantShape adv ↔ MLWEHardQuantShape adv) ∧
      (MSISHardQuantShape adv ↔ DLHardQuantShape adv) ∧
      (MSISHardQuantShape adv ↔ HashCRHardQuantShape adv) ∧
      (MSISHardQuantShape adv ↔ DecisionMLWEHardQuantShape adv) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## §2 — the consumers are hypothesis application.

`<X>HardQuant adv` unfolds to `∀ s, Negl (adv s)`. A theorem concluding `Negl (adv s)` from it is
`hfloor s`. The way to SHOW a statement carries no problem content is to derive it from a floor about
a different problem, and from a floor with no name at all. -/

/-- **TOOTH 2a — the generic schema.** Every `*HardQuant` consumer in the tree is this statement up to
renaming: the conclusion is the hypothesis at `s`. No lattice, no VRF, no reduction, no hash. -/
theorem hardquant_consumer_is_hypothesis_application {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuantShape adv) : Negl (adv s) :=
  hfloor s

/-- **TOOTH 2b — `lattice_vrf_uniqueness_advantage_bound` follows from the HASH floor.** This is the
EXACT statement of `VrfRegrounded.lattice_vrf_uniqueness_advantage_bound` (`{S} (adv) (s)`, concluding
`Negl (adv s)`), derived from `HashCRHardQuantShape` — a floor about Poseidon2 collisions, not about
lattices. A theorem whose name says "lattice VRF uniqueness" and which proves equally well from the
hash floor is not about lattice VRF uniqueness. (It typechecks because of §1.) -/
theorem vrf_uniqueness_bound_from_the_hash_floor {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : HashCRHardQuantShape adv) : Negl (adv s) :=
  hfloor s

/-! ### TOOTH 2b′ — the DEPLOYED keystone itself accepted the WRONG floor. ⚑ RETIRED BY THE REPAIR.

As written on 2026-07-16 this tooth did not restate a consumer — it CALLED
`VrfRegrounded.lattice_vrf_uniqueness_advantage_bound`, passing a `HashCRHardQuantShape` proof into the
argument that signature declared as `MSISHardQuantShape`. It TYPECHECKED, because the two were one `Prop`.

**It cannot be written any more, and that is the gate.** The keystone's floor slot is now
`FloorGames.MSISHardQuant (vrfMsisFamily F) Eff` — a floor at the MSIS game of a specific augmented map —
and a hash-collision floor is not of that type. §6 pins the refusal permanently, with the same adversary,
the same keystone, and `fail_if_success` around it.

What survives here unchanged is the SHAPE-level finding: the five `*HardQuantShape` predicates are still
one `Prop` (§1), and anything stated over them is still hypothesis application (2a, 2b, 2c, 2d). That is
the regression this file exists to hold, and it is why the old defs were kept rather than deleted. -/

/-- **TOOTH 2c — and from the discrete-log floor.** Same statement, third unrelated problem. The
`adv` is an arbitrary function `S → Ensemble`; nothing anywhere ties it to any of the three. -/
theorem vrf_uniqueness_bound_from_the_dl_floor {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : DLHardQuantShape adv) : Negl (adv s) :=
  hfloor s

/-- **TOOTH 2d — the mixed-bound consumers add nothing.** `forger_advantage_with_challenge_bound` /
`lattice_vrf_uniqueness_with_guessing_bound` decorate the schema with a `1/2ⁿ` term that is negligible
on its own (`negl_two_pow`, no floor needed). The floor still enters only as `hfloor s`. Derived here
from the WRONG floor again, to show the decoration carries no problem content either. -/
theorem mixed_bound_from_the_hash_floor {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : HashCRHardQuantShape adv) : Negl (fun n => (1 / (2 : ℝ) ^ n) + adv s n) :=
  negl_add negl_two_pow (hfloor s)

/-! ## §3 — THE DILEMMA: tie `adv` to MSIS and the floor is FALSE; leave it untied and it says
nothing about MSIS.

Both horns are closed by lemmas ALREADY IN THE TREE — this section only puts them side by side, which
is what nobody had done. -/

/-- **HORN A — the MSIS-tied instantiation is FALSE at the deployed compressing instance.**
`msisSolverAdv A β` is the only `adv` in the tree indexed by genuine MSIS solving, and under it the
"quantitative" floor IS the Boolean floor (`msisHardQuant_solverAdv_iff_msisHard`), which pigeonhole
refutes at `augmented id 1`. So on the honest instantiation every consumer is VACUOUSLY true. -/
theorem horn_A_msis_tied_floor_is_false_at_deployed_params :
    ¬ MSISHardQuantShape
        (msisSolverAdv (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0)) :=
  msisHardQuant_solverAdv_augmented_id_false

/-- **HORN B — the untied instantiation HOLDS while MSIS is BROKEN.** `guessAdv = fun l => 1/2^l` is
the tree's own non-vacuity witness for the "proper" floor; it mentions no `A`, no `β`, no
`IsMSISSolution`. Here the floor it satisfies and the refutation of the MSIS instance it is named
after are proved TOGETHER, in one statement. A floor that holds in a world where its own problem is
refuted does not constrain that problem. -/
theorem horn_B_floor_holds_while_msis_is_broken :
    MSISHardQuantShape (fun _ : Unit => guessAdv) ∧
      ¬ MSISHard (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0) :=
  ⟨msisHardQuant_guess_holds, not_msisHard_augmented_id⟩

/-- **THE DILEMMA, assembled.** Either horn kills the MSIS content of every `*HardQuant` consumer: on
the MSIS-tied `adv` the floor is false (so the consumers are vacuous), and on the untied `adv` the
floor is true but compatible with MSIS being refuted (so the consumers say nothing about MSIS). There
is no third instantiation in the tree. -/
theorem hardquant_dilemma :
    (¬ MSISHardQuantShape
        (msisSolverAdv (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0))) ∧
      (MSISHardQuantShape (fun _ : Unit => guessAdv) ∧
        ¬ MSISHard (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0)) :=
  ⟨horn_A_msis_tied_floor_is_false_at_deployed_params, horn_B_floor_holds_while_msis_is_broken⟩

/-! ## §4 — the METHOD tooth: why "satisfiable AND refutable" did not catch this.

`CryptoFloorTeeth.proper_floor_is_genuine` presents `⟨msisHardQuant_guess_holds,
msisHardQuant_const_one_refuted⟩` as evidence that the floor is a genuine assumption. That evidence is
about the SHAPE of a predicate over an arbitrary `adv`. Here is a floor named after counting sheep that
passes the identical test — and that IS `MSISHardQuantShape`, by `Iff.rfl`. -/

/-- A floor whose name was chosen to mean nothing, with the `*HardQuant` shape. -/
def SheepCountingHardQuant {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

/-- The sheep floor is SATISFIABLE — by a genuinely decaying advantage, not a trivial `0`. -/
theorem sheep_floor_is_satisfiable : SheepCountingHardQuant (fun _ : Unit => guessAdv) :=
  fun _ => negl_two_pow

/-- The sheep floor is REFUTABLE — a constant-`1` advantage breaks it. -/
theorem sheep_floor_is_refutable :
    ¬ SheepCountingHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  fun h => not_negl_one (h ())

/-- **TOOTH 4a — the sheep floor passes the tree's non-vacuity test verbatim.** Same pair, same
shape, same conclusion "satisfiable AND refutable, hence a genuine assumption" — for a floor that is
about nothing. So the test cannot distinguish a real floor from a naming. -/
theorem sheep_floor_passes_the_same_non_vacuity_test :
    SheepCountingHardQuant (fun _ : Unit => guessAdv) ∧
      ¬ SheepCountingHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  ⟨sheep_floor_is_satisfiable, sheep_floor_is_refutable⟩

/-- **TOOTH 4b — and the sheep floor IS `MSISHardQuantShape`.** `Iff.rfl`. The name carried all the
content; the kernel sees one predicate. This is what §1 means in practice. -/
theorem sheep_floor_is_msisHardQuant {S : Type*} (adv : S → Ensemble) :
    SheepCountingHardQuant adv ↔ MSISHardQuantShape adv :=
  Iff.rfl

/-- **TOOTH 4c — the sheep floor discharges the VRF keystone's statement.** The statement of
`lattice_vrf_uniqueness_advantage_bound`, proved from a floor about counting sheep. The point is not
that the VRF theorem is false — it is true — but that its truth never depended on lattices. -/
theorem vrf_uniqueness_bound_from_the_sheep_floor {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : SheepCountingHardQuant adv) : Negl (adv s) :=
  hfloor s

/-! ## §6 — ⚑ THE GATE: the wrong floor NO LONGER TYPECHECKS (the 2026-07-16 repair, canaried).

§2b′ is the sweep's sharpest tooth: the real VRF keystone, discharged by the Poseidon2 collision floor.
The repair's success criterion is that the SAME tooth now fails to elaborate. These four teeth are that
criterion, made permanent — each wraps `fail_if_success` around an application that USED to typecheck.

The tree's negative-test idiom is `fail_if_success` (there is no `#guard_msgs` on a type error anywhere in
`Dregg2`; `ThreadAdvantageBound` §5 pins its tactic's refusals the same way). A `fail_if_success` around an
elaboration failure is exactly a compiled-in expected-failure test: if a future edit makes any of these
applications typecheck again, THIS FILE GOES RED. -/

section Gate

open Dregg2.Crypto.FloorGames
open Dregg2.Crypto.VrfRegrounded
open Dregg2.Circuit.HashFloorHonesty (KeyedHashFamily)

/-- **⚑ THE GATE — a `HashCRHardQuant` proof does NOT discharge the `MSISHardQuant` slot.** The exact tooth
of §2b′, re-run against the repaired keystone: same keystone, same adversary, hash floor in the MSIS slot.
It no longer elaborates — `HashCRHardQuant H EffH` is `Hard (hashGame H) EffH` and the slot wants
`Hard (msisGame (vrfMsisFamily F)) Eff`; the two games are different objects, so there is nothing to unify.
This is the criterion the repair is judged by, and it is compiled. -/
example (F : LatticeVrfFamily) (H : KeyedHashFamily)
    (EffH : Adversary (hashGame H) → Prop) (hHash : HashCRHardQuant H EffH)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F)) (hEff : Eff (uniqBreakToMsisSolver F A)) : True := by
  fail_if_success
    (have : Negl (gameAdv (vrfUniqGame F) A) :=
      lattice_vrf_uniqueness_advantage_bound F Eff A hEff hHash)
  trivial

/-- **THE GATE, second horn — the DECISIONAL floor does not discharge it either.** A different problem, a
different type, the same refusal. -/
example (F : LatticeVrfFamily) (D : MLWEDistFamily)
    (EffD : Distinguisher D → Prop) (hDec : DecisionMLWEHardQuant D EffD)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F)) (hEff : Eff (uniqBreakToMsisSolver F A)) : True := by
  fail_if_success
    (have : Negl (gameAdv (vrfUniqGame F) A) :=
      lattice_vrf_uniqueness_advantage_bound F Eff A hEff hDec)
  trivial

/-- **THE SHEEP FLOOR NO LONGER INHABITS A REAL FLOOR'S SLOT.** §4's `SheepCountingHardQuant` — the floor
named after nothing, which passes `CryptoFloorTeeth.proper_floor_is_genuine`'s "satisfiable AND refutable"
test verbatim and IS `MSISHardQuantShape` by `Iff.rfl` — cannot discharge the repaired keystone. The test
that could not see it is now backstopped by one that can: not "is this predicate satisfiable and
refutable?" but "does the CONSUMER accept the WRONG floor?". -/
example (F : LatticeVrfFamily) (adv : Unit → Ensemble) (hsheep : SheepCountingHardQuant adv)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F)) (hEff : Eff (uniqBreakToMsisSolver F A)) : True := by
  fail_if_success
    (have : Negl (gameAdv (vrfUniqGame F) A) :=
      lattice_vrf_uniqueness_advantage_bound F Eff A hEff hsheep)
  trivial

/-- **AND THE OLD SHAPE ITSELF IS REFUSED.** `MSISHardQuantShape` — the content-free predicate that used to
BE this keystone's floor, under this keystone's exact former name — cannot discharge the repaired one. The
costume does not fit the repair: that is what it means for the repair not to be a fourth costume. -/
example (F : LatticeVrfFamily) (adv : Unit → Ensemble) (hshape : MSISHardQuantShape adv)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F)) (hEff : Eff (uniqBreakToMsisSolver F A)) : True := by
  fail_if_success
    (have : Negl (gameAdv (vrfUniqGame F) A) :=
      lattice_vrf_uniqueness_advantage_bound F Eff A hEff hshape)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a broken
keystone, not a fixed one. With the MSIS floor at the game the reduction actually attacks, the keystone
fires and concludes negligibility of the VRF uniqueness-breaking advantage. Refusal is discrimination only
if acceptance still happens. -/
theorem the_repaired_keystone_fires_on_the_right_floor (F : LatticeVrfFamily)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F)) (hEff : Eff (uniqBreakToMsisSolver F A))
    (hfloor : MSISHardQuant (vrfMsisFamily F) Eff) :
    Negl (gameAdv (vrfUniqGame F) A) :=
  lattice_vrf_uniqueness_advantage_bound F Eff A hEff hfloor

/-- **THE FIVE REPAIRED FLOORS ARE NOT ONE `Prop`.** §1 proves the five OLD floors are one predicate, four
`Iff.rfl`s. The repaired five cannot be compared that way at all — `MSISHardQuant F Eff` and
`HashCRHardQuant H EffH` are `Hard` at different `Game`s over different types, so no `Iff` between them is
even well-typed for arbitrary `F`, `H`. That un-statability IS the fix, and the `fail_if_success` teeth
above are how a type-level fact gets pinned as a compiled test. What CAN be stated positively is that each
repaired floor carries its problem: -/
theorem the_five_repaired_floors_are_not_one_prop (F : MSISFamily) (l : ℕ) (i : F.Inst l)
    (z : F.M l) (H : KeyedHashFamily) (l' : ℕ) (k : H.Key l') (p : H.Input × H.Input) :
    ((msisGame F).wins l i z ↔
        (letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
         letI := F.nGrp l; letI := F.nMod l
         Dregg2.Crypto.Lattice.IsMSISSolution (F.A l i) (F.β l) z)) ∧
      ((hashGame H).wins l' k p ↔ (p.1 ≠ p.2 ∧ H.H l' k p.1 = H.H l' k p.2)) :=
  ⟨msisGame_wins_iff F l i z, hashGame_wins_iff H l' k p⟩

end Gate

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms the_five_floors_are_one_prop
#assert_axioms hardquant_consumer_is_hypothesis_application
#assert_axioms vrf_uniqueness_bound_from_the_hash_floor
#assert_axioms the_five_repaired_floors_are_not_one_prop
#assert_axioms vrf_uniqueness_bound_from_the_dl_floor
#assert_axioms mixed_bound_from_the_hash_floor
#assert_axioms horn_A_msis_tied_floor_is_false_at_deployed_params
#assert_axioms horn_B_floor_holds_while_msis_is_broken
#assert_axioms hardquant_dilemma
#assert_axioms sheep_floor_passes_the_same_non_vacuity_test
#assert_axioms sheep_floor_is_msisHardQuant
#assert_axioms vrf_uniqueness_bound_from_the_sheep_floor

end Dregg2.Crypto.HardQuantVacuity
