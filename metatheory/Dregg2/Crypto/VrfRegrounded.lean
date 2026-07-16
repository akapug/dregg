/-
# `Dregg2.Crypto.VrfRegrounded` — the lattice LB-VRF UNIQUENESS keystone, CARRYING its reduction.

## What this file says

A validator that double-claims a committee seat is one that produces two DISTINCT short outputs `y₁ ≠ y₂`
with short proofs that both verify against the same public key and the same per-input commitment. That is
`vrfUniqGame`: a first-class adversary against a λ-indexed sampled LB-VRF instance, whose win relation IS
`VRF.latticeVerify` twice over. `lattice_vrf_uniqueness_advantage_bound` bounds its advantage under the
Module-SIS floor at the AUGMENTED map `[A | t]` — the object the reduction actually attacks.

The Boolean "two verifying outputs ⟹ equal" becomes "⟹ equal EXCEPT with negligible probability".

## The reduction is IN the statement — which is the whole point of this file's 2026-07-16 rewrite

`VRF.lattice_vrf_uniqueness_reduces_to_msis` turns two distinct short verifying outputs on a shared
commitment into a genuine `Lattice.IsMSISSolution` of `[A | t]`: the difference `(z₁ − z₂, −(y₁ − y₂))`,
nonzero from the OUTPUT coordinate, short by the triangle inequality, in the kernel because the extractor
cancels the shared commitment. That theorem was ALWAYS real. Until 07-16 it was not in this file's
statements — it was in this file's PROSE, while the theorem said

    (adv : S → Ensemble) (s : S) (hfloor : MSISHardQuantShape adv) : Negl (adv s)

whose proof is `hfloor s`, and which `HardQuantVacuity.the_vrf_keystone_accepts_the_hash_floor` discharged
by passing the POSEIDON2 COLLISION floor into the slot marked `MSISHardQuant`. It typechecked, because the
five `*HardQuant` floors were one content-free `Prop`. See `docs/deos/VACUITY-SWEEP.md` Finding 1.

Now the reduction is a chain of proof terms:

  * `uniqBreakToMsisSolver` — the extractor, as a map from uniqueness-breakers to MSIS solvers;
  * `uniqBreak_reduces_to_msis` — win preservation, which IS `lattice_vrf_uniqueness_reduces_to_msis` applied;
  * `uniqBreak_adv_le_msis_adv` — the advantage inequality, by `winProb_le_of_imp` over the shared
    instance space;
  * `lattice_vrf_uniqueness_advantage_bound` — the floor, applied to the EXTRACTED solver, dominated down.

Delete the reduction and the keystone does not follow: hypothesis and conclusion are now about DIFFERENT
games, and §2's canary compiles that fact (`fail_if_success` on `hfloor B hB`). Under the old statement
that canary was unwritable — hypothesis and conclusion were the same `Negl (adv s)`.

## The floor, and what it costs — read this before citing the keystone

`FloorGames.MSISHardQuant (vrfMsisFamily F) Eff` is the standard Module-SIS game at the augmented map, with
`IsMSISSolution` in the win relation. `Eff` is the adversary class, and it is a PARAMETER: this tree has no
cost model (`FloorGames` §8). Both poles are proved rather than promised — `Eff := ⊤` makes the floor FALSE
at compressing parameters (`lattice_vrf_floor_top_false_of_compressing`, which is why MSIS is a hard SEARCH
problem), `Eff := ⊥` makes it vacuous (`lattice_vrf_floor_satisfiable_vacuously`). The keystone's `hEff`
side condition — "the extracted solver is in the class" — is the standard "the reduction is efficient". It
is UNDISCHARGED, it is a named parameter at the use site, and it is the honest remaining gap.

## Axiom hygiene

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`, no
`native_decide`. The Boolean-floor consumer `VRF.lattice_vrf_unique_under_msis` is KEPT untouched.

## Coordination

Lattice search-floor leg. The signature forking `MSISHard` consumers ride `Crypto.ForkingDischarge`; those
are NOT re-grounded — no reduction in the tree connects `forkProb` to an `MSISFamily` adversary's advantage,
and `ThreadAdvantageBound` §4 names that obligation rather than dressing it. Stays in the VRF subtree.
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.VRF

namespace Dregg2.Crypto.VrfRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.ProbCrypto (MSISHardQuantShape msisHardQuant_zero msisHardQuant_broken)

set_option autoImplicit false

/-! ## §1 — the uniqueness keystone, ROUTED THROUGH THE REAL REDUCTION.

The 07-16 vacuity sweep proved the previous version of this section carried no lattice content: its
statement was `(adv) (s) (hfloor : MSISHardQuantShape adv) : Negl (adv s)`, whose proof is `hfloor s`, and
`HardQuantVacuity.the_vrf_keystone_accepts_the_hash_floor` discharged it by passing a POSEIDON2 COLLISION
floor into the slot. The reduction this file's own header cited —
`VRF.lattice_vrf_uniqueness_reduces_to_msis` — is real, and was simply never in the statement.

It is now. The uniqueness-breaking adversary is a first-class object (`vrfUniqGame`), the reduction MAPS it
to an MSIS solver (`uniqBreakToMsisSolver`, whose output IS the extractor's `(z₁ − z₂, −(y₁ − y₂))`), the
map is PROVED win-preserving (`uniqBreak_reduces_to_msis`, which is the extractor theorem applied), and the
advantage inequality follows by monotonicity of `winProb`. The floor then bites on the EXTRACTED solver, at
the MSIS game of the AUGMENTED map — the object the reduction actually attacks. -/

open Dregg2.Crypto.FloorGames
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS (augmented augmented_apply instShortNormProd)
open scoped Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)

/-- **A λ-indexed lattice LB-VRF family.** At each security parameter: the ring, the proof module, the
commitment module, a FINITE space of sampled instances (public key `t`, public map `A`, and the per-input
commitment `w` the two claimed outputs share), and the shortness bounds `βz` (proofs) and `βy` (outputs).

This is the object the uniqueness game is played over. It carries the deployed LB-VRF's data and nothing
else; `vrfUniqGame` reads its `latticeVerify` relation directly. -/
structure LatticeVrfFamily where
  /-- The ring `R_q` at parameter `l` (the VRF output lives here). -/
  Rq : ℕ → Type
  /-- The proof module at parameter `l`. -/
  M : ℕ → Type
  /-- The commitment module at parameter `l`. -/
  N : ℕ → Type
  /-- `Rq l` is a commutative ring. -/
  rqRing : ∀ l, CommRing (Rq l)
  /-- The shortness seminorm on outputs. -/
  rqNrm : ∀ l, letI := rqRing l; ShortNorm (Rq l)
  /-- Decidable equality on outputs (the game checks `y₁ ≠ y₂`). -/
  rqDec : ∀ l, DecidableEq (Rq l)
  /-- `M l` is an abelian group. -/
  mGrp : ∀ l, AddCommGroup (M l)
  /-- `M l` is an `Rq l`-module. -/
  mMod : ∀ l, letI := rqRing l; letI := mGrp l; Module (Rq l) (M l)
  /-- The shortness seminorm on proofs. -/
  mNrm : ∀ l, letI := mGrp l; ShortNorm (M l)
  /-- Decidable equality on proofs. -/
  mDec : ∀ l, DecidableEq (M l)
  /-- `N l` is an abelian group. -/
  nGrp : ∀ l, AddCommGroup (N l)
  /-- `N l` is an `Rq l`-module. -/
  nMod : ∀ l, letI := rqRing l; letI := nGrp l; Module (Rq l) (N l)
  /-- Decidable equality on commitments (the game checks the verify equation). -/
  nDec : ∀ l, DecidableEq (N l)
  /-- The instance space (key/commitment sampling randomness). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The public map `A` at parameter `l` on instance `i`. -/
  A : ∀ l, Inst l →
    (letI := rqRing l; letI := mGrp l; letI := mMod l; letI := nGrp l; letI := nMod l;
     M l →ₗ[Rq l] N l)
  /-- The public key `t` at parameter `l` on instance `i`. -/
  t : ∀ l, Inst l → N l
  /-- The per-input commitment `w` the two claimed outputs share. -/
  w : ∀ l, Inst l → N l
  /-- The proof shortness bound. -/
  βz : ℕ → ℕ
  /-- The output shortness bound. -/
  βy : ℕ → ℕ

/-- The uniqueness-breaker's claim: two outputs and two proofs. -/
abbrev LatticeVrfFamily.Claim (F : LatticeVrfFamily) (l : ℕ) : Type :=
  (F.Rq l × F.Rq l) × (F.M l × F.M l)

/-- **THE VRF-UNIQUENESS GAME.** The adversary is given a sampled LB-VRF instance and WINS iff it produces
two DISTINCT short outputs `y₁ ≠ y₂` with short proofs `z₁`, `z₂` that BOTH verify against the same public
key and the same commitment — i.e. iff it breaks `VRF.UniqueOutputs` on that instance. Winning this game is
a validator double-claiming a committee seat; nothing here is a docstring. -/
def vrfUniqGame (F : LatticeVrfFamily) : Game where
  Inst := F.Inst
  Ans := F.Claim
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i c =>
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l
    c.1.1 ≠ c.1.2 ∧
      nrm c.2.1 ≤ F.βz l ∧ nrm c.2.2 ≤ F.βz l ∧
      nrm c.1.1 ≤ F.βy l ∧ nrm c.1.2 ≤ F.βy l ∧
      Dregg2.Crypto.VRF.latticeVerify (F.A l i) (F.t l i) (F.w l i) c.1.1 c.2.1 ∧
      Dregg2.Crypto.VRF.latticeVerify (F.A l i) (F.t l i) (F.w l i) c.1.2 c.2.2
  winsDec := fun l i c => by
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.rqDec l
    letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l; letI := F.mDec l
    letI := F.nGrp l; letI := F.nMod l; letI := F.nDec l
    unfold Dregg2.Crypto.VRF.latticeVerify Dregg2.Crypto.HermineThreshold.verify
    infer_instance

/-- **THE MSIS INSTANCE THE REDUCTION ATTACKS.** The augmented map `[A | t]` over the augmented solution
space `M × R_q`, at the extracted bound `(βz + βz) + (βy + βy)` — exactly the map, space and bound
`VRF.lattice_vrf_uniqueness_reduces_to_msis` produces a solution for. The MSIS floor below is stated at
THIS family, not at an abstract index set. -/
def vrfMsisFamily (F : LatticeVrfFamily) : MSISFamily where
  Rq := F.Rq
  M := fun l => F.M l × F.Rq l
  N := F.N
  rqRing := F.rqRing
  mGrp := fun l => letI := F.rqRing l; letI := F.mGrp l; inferInstance
  mMod := fun l => letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; inferInstance
  mNrm := fun l => letI := F.rqRing l; letI := F.mGrp l; letI := F.mNrm l; letI := F.rqNrm l;
    instShortNormProd
  nGrp := F.nGrp
  nMod := F.nMod
  mDec := fun l => letI := F.mDec l; letI := F.rqDec l; inferInstance
  nDec := F.nDec
  Inst := F.Inst
  instFin := F.instFin
  instNe := F.instNe
  A := fun l i =>
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l
    augmented (F.A l i) (F.t l i)
  β := fun l => (F.βz l + F.βz l) + (F.βy l + F.βy l)

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A uniqueness-breaker becomes an MSIS solver by SUBTRACTING
its two claims: `(z₁ − z₂, −(y₁ − y₂))`. This is not a re-indexing and not a rename — it is the extractor
of `VRF.lattice_vrf_uniqueness_reduces_to_msis`, written as a function. -/
def uniqBreakToMsisSolver (F : LatticeVrfFamily) (A : Adversary (vrfUniqGame F)) :
    Adversary (msisGame (vrfMsisFamily F)) where
  run := fun l i =>
    letI := F.rqRing l; letI := F.mGrp l
    let c := A.run l i
    (c.2.1 - c.2.2, -(c.1.1 - c.1.2))

/-- **⚑ THE REDUCTION IS WIN-PRESERVING — and this is `lattice_vrf_uniqueness_reduces_to_msis`, applied.**
Wherever the uniqueness-breaker wins, the extracted vector IS an `IsMSISSolution` of the augmented map. The
lattice content of this file now lives in a proof term, not in a sentence about one. -/
theorem uniqBreak_reduces_to_msis (F : LatticeVrfFamily) (A : Adversary (vrfUniqGame F))
    (l : ℕ) (i : F.Inst l) (hwin : (vrfUniqGame F).wins l i (A.run l i)) :
    (msisGame (vrfMsisFamily F)).wins l i ((uniqBreakToMsisSolver F A).run l i) := by
  letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
  letI := F.nGrp l; letI := F.nMod l
  obtain ⟨hne, hz₁, hz₂, hy₁, hy₂, hv₁, hv₂⟩ := hwin
  exact Dregg2.Crypto.VRF.lattice_vrf_uniqueness_reduces_to_msis
    (F.A l i) (F.t l i) (F.w l i) _ _ _ _ (F.βz l) (F.βy l) hz₁ hz₂ hy₁ hy₂ hne hv₁ hv₂

/-- **THE ADVANTAGE INEQUALITY.** The uniqueness-breaker's advantage is at most the extracted MSIS solver's
advantage, at every parameter — the two play over the SAME instance space, and every instance the breaker
wins the solver wins. A genuine reduction inequality over real advantages, proved by `winProb_le_of_imp`. -/
theorem uniqBreak_adv_le_msis_adv (F : LatticeVrfFamily) (A : Adversary (vrfUniqGame F)) (l : ℕ) :
    gameAdv (vrfUniqGame F) A l ≤ gameAdv (msisGame (vrfMsisFamily F)) (uniqBreakToMsisSolver F A) l := by
  refine @winProb_le_of_imp _ (F.instFin l) _ _ (fun i hi => ?_)
  rw [Adversary.hit_eq_true] at hi ⊢
  exact uniqBreak_reduces_to_msis F A l i hi

/-- **⚑ RE-GROUNDED LATTICE-VRF UNIQUENESS — from MSIS hardness, VIA the reduction.**

Under the MSIS floor at the AUGMENTED family the reduction attacks, a uniqueness-breaking adversary whose
extracted solver is in the floor's adversary class has NEGLIGIBLE advantage: a validator double-claims a
committee seat only with negligible probability. The Boolean "two verifying outputs ⟹ equal" becomes
"⟹ equal except with negligible probability", and — unlike its predecessor — this statement is FALSE if
you delete the reduction: the conclusion is about the VRF game, the hypothesis about the MSIS game, and
`uniqBreak_adv_le_msis_adv` is the only bridge.

⚑ **THE `hEff` OBLIGATION IS UNDISCHARGED AND THAT IS THE HONEST STATE.** `hEff` says the extracted MSIS
solver is in the class the floor quantifies over — the standard side condition "the reduction is
efficient". It is trivial for the class the reduction preserves and unprovable in general, because this
tree has no cost model (`FloorGames` §8). It is a PARAMETER here, in the open, at the use site. It is NOT a
costume: `FloorGames.hard_top_iff_solvableFrac_negl` proves that filling it with `⊤` makes the floor false
and `hard_bot_vacuous` that filling it with `⊥` makes it vacuous, so the reader can price it exactly. -/
theorem lattice_vrf_uniqueness_advantage_bound (F : LatticeVrfFamily)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F))
    (hEff : Eff (uniqBreakToMsisSolver F A))
    (hfloor : MSISHardQuant (vrfMsisFamily F) Eff) :
    Negl (gameAdv (vrfUniqGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (vrfUniqGame F) A l).1)
    (uniqBreak_adv_le_msis_adv F A) (hfloor _ hEff)

/-- A mixed lattice-VRF bound: a decaying output-space guessing term `1/2ⁿ` PLUS the uniqueness-breaking
advantage. The guessing leg is negligible on its own (`negl_two_pow`); the uniqueness leg goes through the
reduction. Models the total uniqueness-failure advantage of an adversary that either guesses the output or
extracts an MSIS solution. -/
theorem lattice_vrf_uniqueness_with_guessing_bound (F : LatticeVrfFamily)
    (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F))
    (hEff : Eff (uniqBreakToMsisSolver F A))
    (hfloor : MSISHardQuant (vrfMsisFamily F) Eff) :
    Negl (fun n => (1 / (2 : ℝ) ^ n) + gameAdv (vrfUniqGame F) A n) :=
  Dregg2.Crypto.ConcreteSecurity.negl_add Dregg2.Crypto.ConcreteSecurity.negl_two_pow
    (lattice_vrf_uniqueness_advantage_bound F Eff A hEff hfloor)

/-! ## §2 — the CANARY: break the reduction and the keystone goes RED.

The sweep's lesson is that a floor consumer must be checked by asking whether it survives the WRONG
hypothesis. Two teeth, both negative, both permanent. -/

/-- **(CANARY — the keystone does NOT follow from the floor alone.)** Strip the reduction — try to conclude
the VRF adversary's negligibility from the MSIS floor applied at some OTHER solver — and the proof does not
go through: the floor bounds the extracted solver, and only `uniqBreak_adv_le_msis_adv` connects that to
the VRF game. Under the OLD statement this tooth was impossible to write: hypothesis and conclusion were
the same `Negl (adv s)`, so `hfloor s` closed it. Here `exact hfloor B hB` cannot: it proves `Negl` of the
WRONG advantage. -/
example (F : LatticeVrfFamily) (Eff : Adversary (msisGame (vrfMsisFamily F)) → Prop)
    (A : Adversary (vrfUniqGame F)) (B : Adversary (msisGame (vrfMsisFamily F))) (hB : Eff B)
    (hfloor : MSISHardQuant (vrfMsisFamily F) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (vrfUniqGame F) A) := hfloor B hB)
  trivial

/-! ## §3 — non-vacuity: the floor is a genuine constraint on the MSIS game. -/

/-- **(TOOTH — the floor is SATISFIABLE.)** At the empty adversary class the floor holds for any family.
Recorded HONESTLY, and it is not evidence of anything: `FloorGames.hard_bot_vacuous` is exactly the
statement that this satisfiability is vacuous. The predecessor of this file offered the analogous witness
(`msisHardQuant_zero`, the all-zero solver family) as evidence the floor was "a GENUINE assumption"; the
sweep's `SheepCountingHardQuantShape` passed the identical test. So this tooth is kept as a REMINDER of
what a satisfiability witness is worth, which is nothing without the refutation beside it. -/
theorem lattice_vrf_floor_satisfiable_vacuously (F : LatticeVrfFamily) :
    MSISHardQuant (vrfMsisFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the floor is FALSE at the unrestricted class, when the augmented map is compressing.)** The
real content: if a short nonzero kernel vector of `[A | t]` exists at every sampled instance — which
pigeonhole forces at deployed parameters, and which is WHY MSIS is a hard search problem — then the floor
at `Eff := ⊤` is FALSE, and the keystone above is vacuous there. This is the price of `hEff`, stated as a
theorem instead of a promise. -/
theorem lattice_vrf_floor_top_false_of_compressing (F : LatticeVrfFamily)
    (hsolv : ∀ l (i : F.Inst l),
      ∃ z, (letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l
            letI := F.mNrm l; letI := F.nGrp l; letI := F.nMod l
            IsMSISSolution (augmented (F.A l i) (F.t l i)) ((F.βz l + F.βz l) + (F.βy l + F.βy l)) z)) :
    ¬ MSISHardQuant (vrfMsisFamily F) (fun _ => True) :=
  msisHardQuant_top_false_of_compressing (vrfMsisFamily F) hsolv

#assert_all_clean [
  uniqBreak_reduces_to_msis,
  uniqBreak_adv_le_msis_adv,
  lattice_vrf_uniqueness_advantage_bound,
  lattice_vrf_uniqueness_with_guessing_bound,
  lattice_vrf_floor_satisfiable_vacuously,
  lattice_vrf_floor_top_false_of_compressing
]

end Dregg2.Crypto.VrfRegrounded
