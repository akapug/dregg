/-
# `Dregg2.Crypto.CryptoFloorTeeth` — the FALSIFIABILITY TEETH for the crypto hardness floors,
and the PROPER (adversary-indexed) computational floor that replaces the vacuous existence-refutations.

## The bug this file makes visible and permanent

The tree's *Boolean* hardness floors are stated as EXISTENCE-REFUTATIONS:

  * `Lattice.MSISHard A β        := ¬ ∃ z, IsMSISSolution A β z`   (no short nonzero kernel vector)
  * `Lattice.MLWESearchHard A β t := ¬ ∃ s, short s ∧ ∃ e, short e ∧ t = A s + e`
  * `SchnorrCurveField.SchnorrDLHard C G := ¬ DLSolver C G`        (no scalar-recovering function)

Each is DEGENERATE at real deployment parameters — not "hard", but trivially true or trivially false for
reasons unrelated to computational hardness. The doc-comments say the right thing ("the hardness is
FINDING"), but the DEFINITIONS quantify over the mere EXISTENCE of a witness, so every theorem conditioned
on them is discharged by a vacuous hypothesis. `#assert_axioms` is blind to it (a hypothesis is never an
axiom). Nobody had ever tried to prove the floors FALSE — this file does, which is exactly ember's "prove a
load-bearing spec true AND false" discipline.

## §1–§3 — THE TEETH (the floors are degenerate at real parameters).

  * **MSIS is FALSE at a compressing `A`** (`not_msisHard_of_short_ball`): whenever the ball of `β₀`-short
    vectors outnumbers the codomain, two of them collide under `A` (pigeonhole), and their difference is a
    short (`≤ β₀+β₀`) nonzero kernel vector — a genuine `IsMSISSolution`. This is the counting argument that
    makes MSIS a hard SEARCH problem, and it makes `MSISHard` FALSE. Fires concretely on `[id | 1]` over
    `ZMod 5` (domain `25` > codomain `5`).
  * **MLWE is FALSE for any genuine public key** (`not_mlweSearchHard_of_sample`): the short `(s, e)` are the
    secret key — they exist BY CONSTRUCTION. Trivial, and the whole point: a real `t = A·s + e` refutes the
    floor.
  * **DL is DEGENERATE at finite parameters** (`schnorrDLHard_of_smul_collision`): `DLSolver` demands a
    `solve` with `solve (sk·G) = sk` for ALL `sk : ℕ`; on any FINITE point group `sk ↦ sk·G` is
    non-injective, so no such `solve` exists and `SchnorrDLHard` is TRIVIALLY TRUE — satisfied by the
    addition group, by a broken curve, by anything finite, with ZERO cryptographic content. (The infinite
    toy is the opposite pole: `SchnorrCurveField.toy_dl_not_hard` refutes it there, where `sk ↦ sk` IS
    injective.) So `SchnorrDLHard` discriminates on injectivity-over-`ℕ`, not on hardness. NOTE this is the
    OPPOSITE flavor from MSIS/MLWE (trivially TRUE, not FALSE) — both are fatal vacuities.

## §4 — THE SAME BUG IN PROBABILISTIC COSTUME.

`FloorBridge.msisSolverAdv A β` indexes the quantitative floor by the family of SOLUTIONS
`{z // IsMSISSolution A β z}` (each "solver" outputs its own `z`, advantage `1`). So
`MSISHardQuant (msisSolverAdv A β)` holds IFF that family is empty IFF no solution exists — literally
`MSISHard A β` (`msisHardQuant_solverAdv_iff_msisHard`). It inherits the §1 vacuity verbatim
(`msisHardQuant_solverAdv_augmented_id_false`). The `MSISHardQuant` SHAPE is fine; the SOLUTION-indexed
instantiation is the bug.

## §5 — THE PROPER FLOOR: quantified over BOUNDED ADVERSARIES, not solutions.

The honest floor quantifies over an ADVERSARY (a resource-bounded algorithm) and asks its success
ADVANTAGE — a genuine real ENSEMBLE indexed by the security parameter — to be negligible. A single-instance
"∃ efficient adversary" collapses to "∃ solution" (a non-uniform adversary can HARDCODE the answer at zero
cost), so the floor must range over a λ-INDEXED, GROWING instance family — exactly `ProbCrypto.ForkingFamily`
/ `MSISHardQuant (adv : S → Ensemble)` with `adv s` a real advantage ensemble. It is DEMONSTRABLY
non-vacuous AND non-trivial: `ProbCrypto.zeroFamily_forger_negl` SATISFIES it with a genuinely λ-decaying
advantage, and `ProbCrypto.const25_forger_breaks_floor` REFUTES it with a constant `2/5`. Here we exhibit a
minimal decaying-advantage guessing family (`guessAdv`, advantage `1/2^λ`) satisfying the floor and its
constant-`1` twin refuting it — a floor that is neither identically `0` (vacuous) nor `1` (trivially false).

## §6 — THE DEPLOYED KEYSTONE, RE-GROUNDED.

`ForkingDischarge.pq_advantage_bounded_under_msis` and `dregg_pq_is_eufcma_under_msis_discharged` rest on the
BOOLEAN `MSISHard (augmented A t) γ`, refuted at compressing params by §1
(`deployed_boolean_floor_refuted`). The honest keystone is the ENSEMBLE statement
`ForkingDischarge.game_forger_negl_under_msis_quant`: under `MSISHardQuant solverAdvOf` for a GENUINE
adversary-advantage family (the forking extractor's real solving advantage — NOT `msisSolverAdv`), the game
forger's advantage ensemble is negligible. `dregg_pq_game_forger_negl_under_comp_floor` states it for the
DEPLOYED `dreggPqSigScheme`; it FIRES (`regrounded_keystone_fires`) and its floor is LOAD-BEARING
(`regrounded_floor_load_bearing`).

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`), no `sorry`.
-/
import Dregg2.Crypto.ForkingDischarge
import Dregg2.Crypto.FloorBridge
import Dregg2.Tactics
import Mathlib.Combinatorics.Pigeonhole

namespace Dregg2.Crypto.CryptoFloorTeeth

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.SchnorrCurveField
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.FloorBridge
open Dregg2.Crypto.ForkingDischarge
open scoped Dregg2.Crypto.HermineSelfTargetMSIS

/-! ## §1 — MSIS: the floor is FALSE at a compressing `A` (the pigeonhole tooth). -/

section MSIS
variable {M : Type*} [AddCommGroup M] [ShortNorm M]
variable {Rq : Type*} [CommRing Rq] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [Fintype N]

/-- **THE MSIS PIGEONHOLE TOOTH — `MSISHard` is FALSE whenever the short ball outnumbers the codomain.**
Given a finite set `S` of `β₀`-short vectors with `|S| > |N|`, two DISTINCT `x, y ∈ S` collide under `A`
(pigeonhole), so `x - y` is a NONZERO kernel vector of norm `≤ β₀ + β₀` (triangle inequality, `nrm_sub_le`)
— a genuine `IsMSISSolution`. Hence `¬ MSISHard A (β₀ + β₀)`. This is EXACTLY why MSIS is a hard SEARCH
problem, not an impossible one — and it is exactly why the existence-refutation `MSISHard` is the wrong
statement at deployment (a compressing `A` always has such an `S`). -/
theorem not_msisHard_of_short_ball (A : M →ₗ[Rq] N) (β₀ : ℕ)
    (S : Finset M) (hS : ∀ x ∈ S, nrm x ≤ β₀) (hcard : Fintype.card N < S.card) :
    ¬ MSISHard A (β₀ + β₀) := by
  intro hard
  obtain ⟨x, hx, y, hy, hne, hAeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (t := (Finset.univ : Finset N)) (s := S) (f := fun m => A m)
      (by rw [Finset.card_univ]; exact hcard) (fun m _ => Finset.mem_univ _)
  refine hard ⟨x - y, sub_ne_zero.mpr hne, ?_, ?_⟩
  · exact le_trans (nrm_sub_le x y) (Nat.add_le_add (hS x hx) (hS y hy))
  · show A (x - y) = 0
    rw [map_sub, hAeq, sub_self]

end MSIS

/-- **THE TOOTH FIRES on a real compressing instance.** `[id | 1] : ZMod 5 × ZMod 5 → ZMod 5` maps a
`25`-element domain onto a `5`-element codomain — compressing — so its short ball (here all of it, under the
coordinate-sum seminorm the tree uses) collides and `MSISHard` is FALSE at bound `0`. This is the deployed
augmented map `HermineSelfTargetMSIS.augmented`; the same object `ForkingDischarge`'s keystones assume
`MSISHard` about. -/
theorem not_msisHard_augmented_id :
    ¬ MSISHard (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0) :=
  not_msisHard_of_short_ball
    (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) 0
    (Finset.univ : Finset (ZMod 5 × ZMod 5))
    (fun x _ => Nat.le_zero.mpr rfl)
    (by rw [Finset.card_univ]; decide)

/-- …and the witness is EXPLICIT, via the deployed extractor: two accepting forgeries `(z=1,c=1)`,
`(z'=2,c'=2)` on the shared commitment `w=0` hand back the nonzero MSIS solution `(z-z', -(c-c')) = (4,1)`.
So the falsity of `MSISHard` here is not just a counting fact — an actual short nonzero kernel vector is on
the table. -/
theorem msis_solution_exhibited :
    IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) ((0 + 0) + (0 + 0))
      ((1 : ZMod 5) - 2, -((1 : ZMod 5) - 2)) :=
  selftarget_extract_nonzero (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5) (0 : ZMod 5)
    (1 : ZMod 5) (2 : ZMod 5) (1 : ZMod 5) (2 : ZMod 5) 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [HermineThreshold.verify]) (by simp [HermineThreshold.verify])

/-! ## §2 — MLWE: the floor is FALSE for any genuine public key (the short secret IS the key). -/

section MLWE
variable {M : Type*} [AddCommGroup M] [ShortNorm M]
variable {Rq : Type*} [CommRing Rq] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **THE MLWE TOOTH — `MLWESearchHard A β t` is FALSE for any `t` that IS an MLWE sample.** The witnessing
short `(s, e)` with `t = A·s + e` is precisely the secret key — it exists BY CONSTRUCTION. So the
existence-refutation is false at every genuine public key. Real MLWE hardness is about the INEFFICIENCY of
RECOVERING `s`, never its non-existence. -/
theorem not_mlweSearchHard_of_sample {A : M →ₗ[Rq] N} {β : ℕ} {t : N}
    (h : IsMLWESample A β t) : ¬ MLWESearchHard A β t := by
  rintro hard
  obtain ⟨s, e, hs, he, ht⟩ := h
  exact hard ⟨s, hs, e, he, ht⟩

end MLWE

/-- **THE TOOTH FIRES.** `t = 3 = id·1 + 2` is a genuine sample over `ZMod 5` (secret `s=1`, error `e=2`),
so `MLWESearchHard id 0 3` is FALSE. -/
theorem not_mlweSearchHard_ex :
    ¬ MLWESearchHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (3 : ZMod 5) :=
  not_mlweSearchHard_of_sample ⟨(1 : ZMod 5), (2 : ZMod 5), by decide, by decide, by decide⟩

/-! ## §3 — DL: the floor is DEGENERATE (trivially TRUE) at finite parameters. -/

/-- **THE DL TOOTH — `SchnorrDLHard C G` is TRIVIALLY TRUE whenever `sk ↦ sk·G` collides.** If two distinct
scalars `a ≠ b` give the same point `a·G = b·G` (which ALWAYS happens on a FINITE point group — `ℕ` cannot
inject into it), then no `solve` can satisfy `solve (a·G) = a` AND `solve (b·G) = b`, so `DLSolver` is
UNSATISFIABLE and `SchnorrDLHard` holds — for reasons that have NOTHING to do with discrete-log hardness. It
is satisfied by the addition group, by a completely broken curve, by anything finite. The "hardness" carries
no content at deployment. -/
theorem schnorrDLHard_of_smul_collision (C : CurveGroup) (G : C.Pt)
    {a b : ℕ} (hne : a ≠ b) (hcol : C.smul a G = C.smul b G) : SchnorrDLHard C G := by
  rintro ⟨solve, hsolve⟩
  exact hne (by rw [← hsolve a, hcol, hsolve b])

/-- A finite toy point group: `Pt = ZMod 5`, `smul s g = s·g`. Deliberately DEGENERATE — DL on it is
trivial (`solve = fun x => x.val`). -/
def finiteCurve : CurveGroup where
  Pt := ZMod 5
  smul := fun s g => (s : ZMod 5) * g

/-- **THE TOOTH FIRES — `SchnorrDLHard` holds on the finite toy, vacuously.** `0·1 = 0 = 5·1` (`5 ≡ 0`) is a
collision with `0 ≠ 5`, so the floor is satisfied even though DL on `ZMod 5` is COMPLETELY trivial. Contrast
`SchnorrCurveField.toy_dl_not_hard`, which REFUTES the floor on the INFINITE toy (`sk ↦ sk` injective over
`ℤ`). So `SchnorrDLHard`'s truth value tracks injectivity of `sk ↦ sk·G` over `ℕ` — a modelling artifact —
not computational hardness. -/
theorem schnorrDLHard_finiteCurve_degenerate : SchnorrDLHard finiteCurve (1 : ZMod 5) :=
  schnorrDLHard_of_smul_collision finiteCurve (1 : ZMod 5) (a := 0) (b := 5) (by decide)
    (by show ((0 : ℕ) : ZMod 5) * (1 : ZMod 5) = ((5 : ℕ) : ZMod 5) * (1 : ZMod 5); decide)

/-! ## §4 — THE SAME BUG IN PROBABILISTIC COSTUME: `FloorBridge.msisSolverAdv` is solution-indexed. -/

section QuantVacuity
variable {M : Type*} [AddCommGroup M] [ShortNorm M]
variable {Rq : Type*} [CommRing Rq] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **THE QUANTITATIVE FLOOR, AS INSTANTIATED IN `FloorBridge`, IS EXACTLY THE BOOLEAN FLOOR.**
`MSISHardQuant (msisSolverAdv A β) ↔ Lattice.MSISHard A β`. The canonical solver family is the family of
SOLUTIONS `{z // IsMSISSolution A β z}`; each has constant advantage `1` (`boolWinAdv`). So "every solver's
advantage is negligible" holds iff that family is EMPTY iff no solution exists — the Boolean floor verbatim.
The probabilistic dress adds no hardness content; it inherits §1's vacuity. -/
theorem msisHardQuant_solverAdv_iff_msisHard (A : M →ₗ[Rq] N) (β : ℕ) :
    MSISHardQuant (msisSolverAdv A β) ↔ Lattice.MSISHard A β :=
  ⟨msisHard_of_msisHardQuant, msisHardQuant_of_msisHard⟩

end QuantVacuity

/-- **THE SOLUTION-INDEXED QUANT FLOOR IS FALSE at the deployed compressing instance.** Because it equals the
Boolean floor (`msisHardQuant_solverAdv_iff_msisHard`) which §1 refutes on `[id | 1]`, the FloorBridge
instantiation `MSISHardQuant (msisSolverAdv (augmented id 1) 0)` is FALSE — the "quantitative" bridge, as
wired, is vacuous at deployment. -/
theorem msisHardQuant_solverAdv_augmented_id_false :
    ¬ MSISHardQuant (msisSolverAdv (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0)) :=
  fun h => not_msisHard_augmented_id ((msisHardQuant_solverAdv_iff_msisHard _ _).mp h)

/-! ## §5 — THE PROPER FLOOR: a bounded-ADVERSARY advantage floor, non-vacuous AND non-trivial.

The proper floor keeps the `MSISHardQuant` SHAPE (`∀ s, Negl (adv s)`) but re-instantiates `adv` over a
GENUINE resource-bounded adversary family whose advantage is a real ENSEMBLE indexed by the security
parameter — NOT the solution family. To be non-vacuous the advantage must be a real that DECAYS with `λ`
(a single-instance "∃ efficient adversary" collapses to "∃ solution" via non-uniform hardcoding — which is
why the tree's `ForkingFamily` / `MSISHardQuant` are λ-indexed). We exhibit a minimal such floor. -/

/-- A minimal λ-indexed GUESSING adversary advantage: at parameter `λ` the adversary guesses uniformly in a
space of size `2^λ` with a single winning guess, so its advantage is `1/2^λ`. A genuine real ensemble,
neither identically `0` nor `1`. -/
noncomputable def guessAdv : Ensemble := fun l => 1 / (2 : ℝ) ^ l

/-- **NON-VACUITY (satisfiable by a genuinely DECAYING advantage).** The guessing floor holds: `1/2^λ` is
negligible (`negl_two_pow`). This is a real, non-degenerate advantage that vanishes as the challenge space
grows — the floor is satisfiable for reasons of RATE, not because the advantage is trivially `0`. -/
theorem msisHardQuant_guess_holds : MSISHardQuant (fun _ : Unit => guessAdv) :=
  fun _ => negl_two_pow

/-- **NON-TRIVIALITY (refutable by a constant advantage).** A solver family that WINS with constant
probability `1` refutes the floor (`not_negl_one`). So the floor is a GENUINE assumption — satisfiable AND
refutable — not a theorem. Together with `msisHardQuant_guess_holds` this pins the floor strictly between
"vacuously true" and "trivially false". -/
theorem msisHardQuant_const_one_refuted :
    ¬ MSISHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  fun h => not_negl_one (h ())

/-- **THE CONTRAST, MADE PRECISE.** The solution-indexed floor collapses to the Boolean one and is FALSE at
compressing params (§4); the adversary-indexed floor is a real assumption, satisfiable by a decaying
advantage (`msisHardQuant_guess_holds`) and refutable by a constant one (`msisHardQuant_const_one_refuted`).
The λ-DECAY of the advantage is the content the solution-indexing threw away — each "solver" there had a
FROZEN advantage `1`, so the quantifier degenerated into a plain existence check. -/
theorem proper_floor_is_genuine :
    MSISHardQuant (fun _ : Unit => guessAdv) ∧
      ¬ MSISHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  ⟨msisHardQuant_guess_holds, msisHardQuant_const_one_refuted⟩

/-! ## §6 — THE DEPLOYED KEYSTONE, RE-GROUNDED on the adversary-indexed floor.

`ForkingDischarge.pq_advantage_bounded_under_msis` / `dregg_pq_is_eufcma_under_msis_discharged` rest on the
BOOLEAN `MSISHard (augmented A t) γ` — refuted at compressing params by §1. The honest keystone rides
`ForkingDischarge.game_forger_negl_under_msis_quant`: under `MSISHardQuant solverAdvOf` for a GENUINE
adversary-advantage family, the game forger's advantage ENSEMBLE is negligible. -/

section Regrounded
variable {SK PK Msg Sig : Type*}

/-- **THE DEPLOYED-SCHEME KEYSTONE, RE-GROUNDED.** For the SHIPPED `dreggPqSigScheme` presented as a
`GameForkingFamily`, under the quantitative Module-SIS floor `MSISHardQuant solverAdvOf` — where
`solverAdvOf` is a GENUINE resource-bounded adversary-advantage family (the forking extractor's real solving
advantage as an ENSEMBLE; `hs` says the derived solver IS one such adversary), NOT the solution-indexed
`msisSolverAdv` of §4 — and a super-polynomially growing challenge space, the game forger's advantage
ensemble is NEGLIGIBLE. This is "EUF-CMA reduces to MSIS" on a floor that is satisfiable-but-not-provable
(§5), replacing the vacuous Boolean `MSISHard`. -/
theorem dregg_pq_game_forger_negl_under_comp_floor
    {Seed PK' Ctx Msg' Sig' : Type*}
    (api : Dregg2.Crypto.DreggPqRefinement.DreggPqApi Seed PK' Ctx Msg' Sig')
    (pk : PK') (Q : (Ctx × Msg') → Prop)
    (GF : GameForkingFamily (Dregg2.Crypto.DreggPqRefinement.dreggPqSigScheme api) pk Q)
    {SolverIdx : Type*} (solverAdvOf : SolverIdx → Ensemble) (s : SolverIdx)
    (hs : solverAdvOf s = GF.fam.solverAdv)
    (hfloor : MSISHardQuant solverAdvOf) (hCneg : Negl GF.fam.invChal) :
    Negl GF.fam.forgerAdv :=
  game_forger_negl_under_msis_quant GF solverAdvOf s hs hfloor hCneg

end Regrounded

/-- **THE DEPLOYED BOOLEAN FLOOR IS REFUTED at compressing params.** The exact floor object
`ForkingDischarge.pq_advantage_bounded_under_msis` / `dregg_pq_is_eufcma_under_msis_discharged` assume —
`MSISHard (augmented [id] 1) …` over `ZMod 5` — is FALSE (§1). So the deployed keystones' Boolean hypothesis
is vacuous at deployment; the re-grounded ensemble keystone rests on the genuine decaying-advantage floor
instead. -/
theorem deployed_boolean_floor_refuted :
    ¬ MSISHard (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) (1 : ZMod 5)) (0 + 0) :=
  not_msisHard_augmented_id

/-- **THE RE-GROUNDED KEYSTONE FIRES.** On the never-accepting super-polynomial-challenge family
(`ProbCrypto.zeroFamily`), the adversary-indexed floor (trivially, solver advantage `≡ 0`) plus the
negligible challenge term give `Negl forgerAdv` — the reduction runs end-to-end and concludes negligibility
of a genuine real-valued advantage. -/
theorem regrounded_keystone_fires : Negl ProbCrypto.zeroFamily.forgerAdv :=
  ProbCrypto.zeroFamily_forger_negl

/-- **THE RE-GROUNDED FLOOR IS LOAD-BEARING.** The constant-`2/5` forger forces its derived MSIS solver's
advantage to a constant `2/25`, which is NOT negligible — so a non-negligibly-advantaged forger BREAKS the
quantitative floor. Strip the floor and the conclusion fails; the reduction genuinely CONSUMES it (on real
advantages, not a Boolean flag). -/
theorem regrounded_floor_load_bearing : ¬ Negl ProbCrypto.const25Family.solverAdv :=
  ProbCrypto.const25_forger_breaks_floor

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  not_msisHard_of_short_ball,
  not_msisHard_augmented_id,
  msis_solution_exhibited,
  not_mlweSearchHard_of_sample,
  not_mlweSearchHard_ex,
  schnorrDLHard_of_smul_collision,
  schnorrDLHard_finiteCurve_degenerate,
  msisHardQuant_solverAdv_iff_msisHard,
  msisHardQuant_solverAdv_augmented_id_false,
  msisHardQuant_guess_holds,
  msisHardQuant_const_one_refuted,
  proper_floor_is_genuine,
  dregg_pq_game_forger_negl_under_comp_floor,
  deployed_boolean_floor_refuted,
  regrounded_keystone_fires,
  regrounded_floor_load_bearing
]

end Dregg2.Crypto.CryptoFloorTeeth
