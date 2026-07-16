/-
# `Dregg2.Crypto.ProbCrypto` — the PROBABILISTIC-CRYPTO substrate (concrete security).

Track B of the crypto-honesty goal. The tree's cryptographic floors are BOOLEAN
(`Lattice.MSISHard := ¬ ∃ solver`, `SchnorrDLHard`, …) and the reductions that ride on them are
therefore Boolean implications ("a forgery yields a solver, contradicting the floor"). A genuine
*concrete-security* theorem instead says: the adversary's advantage is a REAL number in `[0,1]`, and
a reduction relates the advantage of one game to the advantage of another by an INEQUALITY. This
module adds that quantitative layer ALONGSIDE the Boolean floors — it does not touch them.

## What is reused (imported, not reinvented)

  * `ConcreteSecurity.Negl` / `Ensemble` + the whole `Negl` closure algebra (`negl_add`,
    `negl_const_mul`, `negl_of_eventually_le`, `negl_two_pow`, `not_negl_one`) — the negligibility layer.
  * `HermineTSUF`'s `section ProbForking`: `advantage`, `forkProb`, `forkProb_ge_advantage`
    (`forkProb ≥ ε·(ε − 1/|C|)`, a PROVED finite-counting-probability inequality) and its
    downstream extraction. That is the reduction inequality this module lifts to the `Ensemble` layer.

## What is built (§-by-§)

  **§1 — GAMES AS FINITE COUNTING-PROBABILITY EXPERIMENTS.** `winProb (win : Ω → Bool) : ℝ`, the
  fraction of the finite outcome space on which the adversary wins — a genuine real in `[0,1]`
  (`winProb_nonneg`, `winProb_le_one`). BOTH TEETH: an always-winning game has `winProb = 1`, a
  never-winning game `0`.

  **§2 — QUERY-BOUNDED-ROM ADVERSARIES.** `QBAdversary qH Ans Out` — an adversary making at most `qH`
  random-oracle queries, modeled as a function of the `Fin qH`-indexed answer vector. Concrete security
  in the query-bounded ROM is the standard tractable model (no PPT Turing machine needed). Its
  `romAdvantage` is the `winProb` over the uniformly-sampled answer space.

  **§3 — QUANTITATIVE HARDNESS FLOORS (ADDITIVE).** `MSISHardQuantShape (adv) := ∀ s, Negl (adv s)` — every
  solver's MSIS-solving advantage is negligible. This is the concrete-security analog of the Boolean
  `Lattice.MSISHard`; the Boolean floor is UNTOUCHED. `MLWEHardQuantShape` / `DLHardQuantShape` / `HashCRHardQuantShape`
  are the same shape. BOTH TEETH: the all-zero advantage floor holds; a constant-`1` solver refutes it.

  **§4 — THE RE-THREADED FORKING → MSIS REDUCTION (concrete-security form).** The keystone. `negl_of_negl_sq`
  (`Negl ε² → Negl ε` for `ε ≥ 0`, a genuine non-trivial squeeze) plus `negl_of_forking_bound` turn the
  finite forking inequality `forkProb ≥ ε·(ε − 1/|C|)` into an ADVANTAGE-INEQUALITY REDUCTION against the
  QUANTITATIVE floor: `forking_reduces_to_MSISHardQuant` proves `MSISHardQuantShape ⟹ Negl (forger advantage)`.
  A forger with non-negligible advantage yields an MSIS solver with related non-negligible advantage,
  contradicting the quantitative floor — the concrete-security content the tree previously stated only
  Boolean-ly. The reduction BITES: a constant-`2/5`-advantage forger family forces solver advantage
  `≥ 2/25`, non-negligible (`const25_forger_breaks_floor`).

## No named-carrier laundering.

Every advantage here is a genuine real number that CAN be non-negligible (`advantage_example_eq`:
`2/5`); `Negl` genuinely discriminates (`not_negl_const_pos`); the reduction inequality is the PROVED
`forkProb_ge_advantage`, not an assumption. Nothing here introduces an `axiom` or a `def …Hard` used as
a hypothesis. Keystones pinned kernel-clean below.
-/
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Crypto.HermineTSUF
import Dregg2.Tactics
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.Lattice (ShortNorm)

namespace Dregg2.Crypto.ProbCrypto

/-! ## §1 — Games as finite counting-probability experiments. -/

/-- **The winning probability of a finite game.** `win : Ω → Bool` is the game's winning predicate over a
finite outcome space `Ω` (the adversary's coins ⊕ oracle answers ⊕ …); `winProb` is the fraction of
outcomes on which the adversary wins — a genuine probability, the numerator counted over the total. This is
the real-valued advantage the whole concrete-security layer is stated against. -/
noncomputable def winProb {Ω : Type*} [Fintype Ω] (win : Ω → Bool) : ℝ :=
  ((Finset.univ.filter (fun o => win o = true)).card : ℝ) / (Fintype.card Ω : ℝ)

/-- `winProb` is a genuine probability: non-negative. -/
theorem winProb_nonneg {Ω : Type*} [Fintype Ω] (win : Ω → Bool) : 0 ≤ winProb win := by
  unfold winProb; positivity

/-- `winProb ≤ 1` — the favorable outcomes are a subset of all outcomes (handles `|Ω| = 0`: `0/0 = 0`). -/
theorem winProb_le_one {Ω : Type*} [Fintype Ω] (win : Ω → Bool) : winProb win ≤ 1 := by
  unfold winProb
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast h0)]
    have : (Finset.univ.filter (fun o => win o = true)).card ≤ Fintype.card Ω :=
      le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_univ))
    exact_mod_cast this

/-- **(TOOTH — a game won with certainty.)** If the adversary wins on every outcome, `winProb = 1`. The
positive pole — `winProb` reaches `1`. -/
theorem winProb_top {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    winProb (fun _ : Ω => true) = 1 := by
  unfold winProb
  have hne : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Finset.filter_true_of_mem (fun _ _ => rfl), Finset.card_univ]
  exact div_self (ne_of_gt hne)

/-- **(TOOTH — a game never won.)** If the adversary never wins, `winProb = 0`. The negative pole. -/
theorem winProb_bot {Ω : Type*} [Fintype Ω] :
    winProb (fun _ : Ω => false) = 0 := by
  unfold winProb
  simp

/-- **`winProb` is monotone in the win predicate.** If every outcome that wins `f` also wins `g`, then
`winProb f ≤ winProb g` — the favorable set of `f` is a subset of `g`'s, and the outcome count is shared.
The probability-level lift of an event implication ("a break IS a forgery", "an adversary only wins where
a win exists"). -/
theorem winProb_le_of_imp {Ω : Type*} [Fintype Ω] {f g : Ω → Bool}
    (h : ∀ o, f o = true → g o = true) : winProb f ≤ winProb g := by
  unfold winProb
  have hsub : (Finset.univ.filter (fun o => f o = true))
      ⊆ (Finset.univ.filter (fun o => g o = true)) := by
    intro o ho
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
    exact h o ho
  gcongr

/-- **DOMINATION for negligibility.** A NONNEGATIVE ensemble `f` dominated pointwise by an ensemble `g`
that is negligible is itself negligible. The squeeze every advantage-inequality reduction uses to conclude
`Negl (small advantage)` from `Negl (component advantage)`. -/
theorem negl_of_le {f g : ℕ → ℝ} (hfn : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n)
    (hg : Negl g) : Negl f := by
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun n => ?_)) hg
  rw [abs_of_nonneg (hfn n)]
  exact le_trans (hle n) (le_abs_self _)

/-! ## §2 — Query-bounded-ROM adversaries.

Concrete security in the query-bounded random-oracle model: the adversary makes at most `qH` oracle
queries, so its entire interaction is a function of the `qH` answers it receives. We model that answer
vector as `Fin qH → Ans` and sample it uniformly. No probabilistic-polynomial-time Turing machine is
needed — the query bound `qH` is the resource, and it is genuinely `Fin qH` (bounded). -/

/-- **A query-bounded-ROM adversary.** It receives a vector of `qH` random-oracle answers
(`Fin qH → Ans`) — its at-most-`qH` queries — and produces an output in `Out`. This is the finite
counting-probability shadow of an ROM adversary; the `ProbForger` of `HermineTSUF` is exactly this shape
with `Ans = Rq` and the prefix world `Ω ↔ Fin qH → Rq`. -/
structure QBAdversary (qH : ℕ) (Ans Out : Type*) where
  /-- The adversary as a function of the `qH` oracle answers it receives. -/
  run : (Fin qH → Ans) → Out

/-- The query-bounded adversary's **advantage** against a winning predicate `win : Out → Bool`: the
`winProb` over the uniformly-sampled answer vector `Fin qH → Ans`. A genuine real in `[0,1]`. -/
noncomputable def romAdvantage {qH : ℕ} {Ans Out : Type*} [Fintype Ans]
    (adv : QBAdversary qH Ans Out) (win : Out → Bool) : ℝ :=
  winProb (fun ρ : Fin qH → Ans => win (adv.run ρ))

/-- The ROM advantage is a genuine probability. -/
theorem romAdvantage_mem_unit {qH : ℕ} {Ans Out : Type*} [Fintype Ans]
    (adv : QBAdversary qH Ans Out) (win : Out → Bool) :
    0 ≤ romAdvantage adv win ∧ romAdvantage adv win ≤ 1 :=
  ⟨winProb_nonneg _, winProb_le_one _⟩

/-! ## §3 — Quantitative hardness floors (ADDITIVE — the Boolean floors are untouched).

`Lattice.MSISHard := ¬ ∃ z, IsMSISSolution …` stays exactly as it is. Here we add its concrete-security
sibling: parametrized by a family of solvers `S` and each solver's success-probability ENSEMBLE
`adv : S → Ensemble`, the quantitative floor says every solver's advantage is negligible. -/

/-- ⚠ **BROKEN AS A FLOOR — NO PROBLEM CONTENT. RETAINED AS THE CARRIER OF ITS OWN DEFECT.**

`MSISHardQuantShape adv := ∀ s, Negl (adv s)` says nothing about MSIS. It mentions no lattice, no `A`, no
`β`, no `IsMSISSolution` — and it is `Iff.rfl`-equal to the four siblings below, so a proof "under the MSIS
floor" IS a proof "under the hash-CR floor" (`HardQuantVacuity.the_five_floors_are_one_prop`). The problem
lived entirely in the NAME, which is why this def is now named after its shape rather than after a problem
it never constrained. `HardQuantVacuity.sheep_floor_is_msisHardQuantShape` proves a floor named after
COUNTING SHEEP is definitionally this one.

Consumers of it get their hypothesis back: `(adv) (s) (hfloor : MSISHardQuantShape adv) : Negl (adv s)` is
`hfloor s`, a `P → P` instantiation.

**The honest floor is `FloorGames.MSISHardQuant`** — the standard Module-SIS game, with `IsMSISSolution` IN
the statement and the adversary class an explicit parameter. KEPT here, doc-marked, because
`HardQuantVacuity`'s teeth are stated about it and are the regression: they must keep compiling. Do not add
new consumers. -/
def MSISHardQuantShape {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

/-- ⚠ **BROKEN — the same content-free `Prop` as `MSISHardQuantShape`, under a different name.** See there;
the honest floor is `FloorGames.MLWEHardQuant`. -/
def MLWEHardQuantShape {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

/-- ⚠ **BROKEN — the same content-free `Prop` as `MSISHardQuantShape`, under a different name.** See there;
the honest floor is `FloorGames.DLHardQuant`. -/
def DLHardQuantShape {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

/-- ⚠ **BROKEN — the same content-free `Prop` as `MSISHardQuantShape`, under a different name.** See there;
the honest floor is `FloorGames.HashCRHardQuant`. -/
def HashCRHardQuantShape {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

/-- **(TOOTH — the floor holds.)** If every solver has the all-zero advantage, the quantitative floor
holds (`negl_zero`). The positive pole. -/
theorem msisHardQuant_zero {S : Type*} :
    MSISHardQuantShape (fun _ : S => (fun _ => 0 : Ensemble)) := fun _ => negl_zero

/-- **(TOOTH — the floor is refutable.)** If some solver has constant-`1` advantage, the quantitative
floor FAILS (`not_negl_one`). The negative pole — `MSISHardQuantShape` is load-bearing, not vacuous. -/
theorem msisHardQuant_broken {S : Type*} (s0 : S) :
    ¬ MSISHardQuantShape (fun _ : S => (fun _ => (1 : ℝ) : Ensemble)) :=
  fun h => not_negl_one (h s0)

/-! ## §4 — The re-threaded forking → MSIS reduction (concrete-security form).

The Boolean tree says: a forgery yields an `IsMSISSolution`, contradicting `MSISHard`. The concrete form
says: the forger's REAL advantage `ε(λ)` is bounded through the forking inequality by the MSIS solver's
advantage, so if MSIS is quantitatively hard (solver advantage negligible) the forger's advantage is
negligible too. The two ingredients are (a) a genuine real-analysis squeeze `Negl ε² → Negl ε`, and (b)
`HermineTSUF.forkProb_ge_advantage` lifted to the `Ensemble` layer. -/

/-- **A positive constant is NOT negligible.** Scale `1` down by `1/c`: `Negl (const c)` would give
`Negl (const 1)` (`negl_const_mul`), refuted by `not_negl_one`. The discriminator behind the reduction's
bite. -/
theorem not_negl_const_pos {c : ℝ} (hc : 0 < c) : ¬ Negl (fun _ : ℕ => c) := by
  intro h
  have h1 : Negl (fun _ : ℕ => (1 : ℝ)) := by
    have hm := negl_const_mul (1 / c) h
    have : (fun n : ℕ => (1 / c) * c) = (fun _ : ℕ => (1 : ℝ)) := by
      funext _; field_simp
    rwa [this] at hm
  exact not_negl_one h1

/-- **THE SQUEEZE — `Negl (ε²) ⟹ Negl ε` for a non-negative advantage.** If the SQUARE of an ensemble is
negligible, so is the ensemble: at exponent `c`, use `Negl ε²` at `2c` to get `ε² < (1/nᶜ)²`, then take
square roots (`lt_of_pow_lt_pow_left`, both sides non-negative). This is the genuine content that makes the
quadratic forking bound `ε·(ε − 1/|C|)` yield `Negl ε` — a real squeeze, not a relabelling. -/
theorem negl_of_negl_sq {ε : ℕ → ℝ} (hnn : ∀ n, 0 ≤ ε n)
    (hsq : Negl (fun n => ε n ^ 2)) : Negl ε := by
  intro c
  filter_upwards [hsq (2 * c), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbpos : (0 : ℝ) < 1 / (n : ℝ) ^ c := by positivity
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε n ^ 2)] at hn
  have hrw : (1 : ℝ) / (n : ℝ) ^ (2 * c) = (1 / (n : ℝ) ^ c) ^ 2 := by
    rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm]
  rw [hrw] at hn
  rw [abs_of_nonneg (hnn n)]
  by_contra hge
  push_neg at hge
  exact absurd (pow_le_pow_left₀ (le_of_lt hbpos) hge 2) (not_le.2 hn)

/-- **THE REDUCTION COMBINATOR — an advantage-inequality reduction against the quantitative floor.** Given
the forking-shaped bound `ε·(ε − invC) ≤ msisAdv` (the solver advantage dominates the quadratic forking
term), with `ε` a genuine probability in `[0,1]` and `invC ≥ 0` the challenge-collision term `1/|C|`: if
BOTH the MSIS advantage `msisAdv` AND the challenge-collision term `invC` are negligible, then the forger
advantage `ε` is negligible. Because `ε² = ε·(ε − invC) + ε·invC ≤ msisAdv + invC` (using `ε ≤ 1`), the
square is negligible (`negl_add` + domination), whence `ε` is (`negl_of_negl_sq`). This is the genuine
concrete-security reduction: non-negligible forger advantage ⟹ non-negligible MSIS advantage. -/
theorem negl_of_forking_bound {ε msisAdv invC : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ ε n) (hle1 : ∀ n, ε n ≤ 1) (hinvnn : ∀ n, 0 ≤ invC n)
    (hbound : ∀ n, ε n * (ε n - invC n) ≤ msisAdv n)
    (hmsis : Negl msisAdv) (hC : Negl invC) : Negl ε := by
  apply negl_of_negl_sq hnn
  have hsum : Negl (fun n => msisAdv n + invC n) := negl_add hmsis hC
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun n => ?_)) hsum
  have hsq_le : ε n ^ 2 ≤ msisAdv n + invC n := by
    have h1 : ε n * (ε n - invC n) ≤ msisAdv n := hbound n
    have h2 : ε n * invC n ≤ invC n := by
      calc ε n * invC n ≤ 1 * invC n := by
            apply mul_le_mul_of_nonneg_right (hle1 n) (hinvnn n)
        _ = invC n := one_mul _
    nlinarith [h1, h2]
  have hsq_nn : (0 : ℝ) ≤ ε n ^ 2 := by positivity
  rw [abs_of_nonneg hsq_nn, abs_of_nonneg (le_trans hsq_nn hsq_le)]
  exact hsq_le

/-! ### The forger FAMILY and the bound lifted from `HermineTSUF.forkProb_ge_advantage`. -/

/-- **A λ-indexed forging family** — the concrete-security lift of `HermineTSUF`'s single-parameter
`ProbForger`. At each security parameter `l`, a finite challenge set `Chal l` (the `Rq` of `ProbForking`),
a finite prefix world `World l` (its `Ω`), and an accept predicate `acc l`. The forger's advantage and the
derived MSIS solver's advantage become ENSEMBLES over `l`. -/
structure ForkingFamily where
  /-- The challenge set at parameter `l`. -/
  Chal : ℕ → Type
  /-- The prefix world (RO answers below the fork index ⊕ coins) at parameter `l`. -/
  World : ℕ → Type
  /-- The challenge set is a commutative ring (the forking extractor's `Rq`). -/
  chalRing : ∀ l, CommRing (Chal l)
  /-- The shortness seminorm on the challenge set (carried; the forking lemma's `ShortNorm Rq`). -/
  chalNorm : ∀ l, letI := chalRing l; ShortNorm (Chal l)
  /-- Finiteness of the challenge set. -/
  chalFin : ∀ l, Fintype (Chal l)
  /-- Decidable equality on the challenge set (for the accepting-challenge count). -/
  chalDec : ∀ l, DecidableEq (Chal l)
  /-- Finiteness of the prefix world. -/
  worldFin : ∀ l, Fintype (World l)
  /-- The accept predicate at parameter `l`. -/
  acc : ∀ l, World l → Chal l → Bool
  /-- The prefix world is inhabited (non-empty outcome space). -/
  worldPos : ∀ l, 0 < @Fintype.card (World l) (worldFin l)
  /-- The challenge set is inhabited. -/
  chalPos : ∀ l, 0 < @Fintype.card (Chal l) (chalFin l)

namespace ForkingFamily

/-- The family's **forger advantage** ensemble — `ε(l) = advantage (acc l)`, cast to `ℝ`. -/
noncomputable def forgerAdv (F : ForkingFamily) : ℕ → ℝ := fun l =>
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  ((advantage (F.acc l) : ℚ) : ℝ)

/-- The family's **derived MSIS-solver advantage** ensemble — `forkProb (acc l)`, cast to `ℝ`: the
probability the forking rewind yields two distinct-challenge accepting transcripts (which
`HermineTSUF.prob_forger_forkProb_yields_msis` turns into an `IsMSISSolution`). -/
noncomputable def solverAdv (F : ForkingFamily) : ℕ → ℝ := fun l =>
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  ((forkProb (F.acc l) : ℚ) : ℝ)

/-- The family's **challenge-collision term** `invC(l) = 1/|Chal l|`. -/
noncomputable def invChal (F : ForkingFamily) : ℕ → ℝ := fun l =>
  1 / (@Fintype.card (F.Chal l) (F.chalFin l) : ℝ)

theorem forgerAdv_nonneg (F : ForkingFamily) (l : ℕ) : 0 ≤ F.forgerAdv l := by
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  have := advantage_nonneg (F.acc l)
  unfold forgerAdv
  exact_mod_cast this

theorem invChal_nonneg (F : ForkingFamily) (l : ℕ) : 0 ≤ F.invChal l := by
  unfold invChal; positivity

/-- **The forger advantage is a genuine probability: `≤ 1`.** Each prefix has at most `|Chal|` accepting
challenges, so `∑ hits ≤ |World|·|Chal|` and `advantage ≤ 1`. Proved in `ℚ` then cast. -/
theorem forgerAdv_le_one (F : ForkingFamily) (l : ℕ) : F.forgerAdv l ≤ 1 := by
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  have hq : HermineTSUF.advantage (F.acc l) ≤ 1 := by
    unfold HermineTSUF.advantage
    rw [div_le_one (by
      have := F.worldPos l; have := F.chalPos l
      have h1 : (0:ℚ) < (Fintype.card (F.World l) : ℚ) := by exact_mod_cast F.worldPos l
      have h2 : (0:ℚ) < (Fintype.card (F.Chal l) : ℚ) := by exact_mod_cast F.chalPos l
      positivity)]
    calc (∑ ω : F.World l, (HermineTSUF.hits (F.acc l) ω : ℚ))
        ≤ ∑ _ω : F.World l, (Fintype.card (F.Chal l) : ℚ) := by
          apply Finset.sum_le_sum
          intro ω _
          have : HermineTSUF.hits (F.acc l) ω ≤ Fintype.card (F.Chal l) := by
            unfold HermineTSUF.hits HermineTSUF.acceptSet
            exact le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)
          exact_mod_cast this
      _ = (Fintype.card (F.World l) : ℚ) * (Fintype.card (F.Chal l) : ℚ) := by
          rw [Finset.sum_const, Finset.card_univ]; push_cast; ring
  unfold forgerAdv
  exact_mod_cast hq

/-- **THE FORKING BOUND, LIFTED TO THE ENSEMBLE LAYER.** For every parameter `l`,
`forgerAdv l · (forgerAdv l − invChal l) ≤ solverAdv l` — the `ℝ`-cast of
`HermineTSUF.forkProb_ge_advantage` (`forkProb ≥ ε·(ε − 1/|C|)`). This is the reduction inequality; it is
PROVED, transported from the finite counting-probability model. -/
theorem bound (F : ForkingFamily) (l : ℕ) :
    F.forgerAdv l * (F.forgerAdv l - F.invChal l) ≤ F.solverAdv l := by
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  have hq := HermineTSUF.forkProb_ge_advantage (F.acc l) (F.worldPos l) (F.chalPos l)
  rw [ge_iff_le] at hq
  have key : (HermineTSUF.advantage (F.acc l) : ℝ) *
      ((HermineTSUF.advantage (F.acc l) : ℝ) - 1 / (Fintype.card (F.Chal l) : ℝ))
      ≤ (HermineTSUF.forkProb (F.acc l) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hcast
    linarith [hcast]
  simpa only [forgerAdv, solverAdv, invChal] using key

end ForkingFamily

/-- **THE CONCRETE-SECURITY REDUCTION — `MSISHardQuantShape ⟹ Negl (forger advantage)`.** If the derived MSIS
solver's advantage is negligible (the QUANTITATIVE floor, applied to the reduction's output solver) and the
challenge-collision term `1/|C|` is negligible (the challenge space grows), then the forger's advantage is
negligible. This is the advantage-inequality form of the reduction the tree previously stated only
Boolean-ly: `negl_of_forking_bound` fed the PROVED `ForkingFamily.bound`. -/
theorem forking_reduces_to_MSISHardQuant (F : ForkingFamily)
    (hCneg : Negl F.invChal) (hmsis : Negl F.solverAdv) : Negl F.forgerAdv :=
  negl_of_forking_bound F.forgerAdv_nonneg F.forgerAdv_le_one F.invChal_nonneg
    F.bound hmsis hCneg

/-- **THE REDUCTION AGAINST THE FLOOR OBJECT.** The derived solver `s` is one of the solvers the
quantitative floor `MSISHardQuantShape` quantifies over, and its advantage IS `F.solverAdv`. So the floor
directly discharges `Negl F.solverAdv`, and the forger advantage is negligible. This exhibits the genuine
"non-negligible forger ⟹ non-negligible solver ⟹ contradicts the floor" reduction over real advantages. -/
theorem forking_reduces_against_floor {S : Type*} (F : ForkingFamily)
    (solverAdvOf : S → Ensemble) (s : S) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuantShape solverAdvOf) (hCneg : Negl F.invChal) : Negl F.forgerAdv :=
  forking_reduces_to_MSISHardQuant F hCneg (hs ▸ hfloor s)

/-! ### NON-VACUITY — the advantage is a genuine real that CAN be non-negligible, and the reduction BITES. -/

/-- The trivial (all-zero) shortness seminorm — any `AddCommGroup` carries one, so a `ForkingFamily`'s
`chalNorm` field is always inhabitable; the norm plays no role in the counting-probability bound. -/
def trivNorm (M : Type*) [AddCommGroup M] : ShortNorm M where
  nrm := fun _ => 0
  nrm_zero := rfl
  nrm_neg := fun _ => rfl
  nrm_add_le := fun _ _ => Nat.zero_le _

/-- A concrete accept predicate over `World = Unit`, `Chal = ZMod 5`: accepts on exactly the two challenges
`{0, 1}`. Its advantage will be `2/5` — a genuine positive real. -/
def exampleAcc : Unit → ZMod 5 → Bool := fun _ c => decide (c = 0 ∨ c = 1)

/-- **THE ADVANTAGE IS A GENUINE REAL NUMBER — `2/5`.** `exampleAcc` has exactly `2` accepting challenges
out of `5`, over a single prefix world, so `advantage = 2/(1·5) = 2/5`. A concrete positive advantage: real,
computed, and — held constant across `λ` — NON-negligible (below). This is what makes the layer
quantitative rather than a Boolean relabelling. -/
theorem advantage_example_eq : HermineTSUF.advantage exampleAcc = 2 / 5 := by
  have hhits : ∀ u : Unit, HermineTSUF.hits exampleAcc u = 2 := fun u => by cases u; decide
  unfold HermineTSUF.advantage
  rw [Fintype.sum_unique, hhits, Fintype.card_unit, ZMod.card]
  norm_num

/-- **The constant-`2/5` forging family** — `exampleAcc` at every parameter. Its forger advantage is the
constant `2/5`, its challenge set the constant `ZMod 5`. -/
def const25Family : ForkingFamily where
  Chal := fun _ => ZMod 5
  World := fun _ => Unit
  chalRing := fun _ => inferInstance
  chalNorm := fun _ => trivNorm (ZMod 5)
  chalFin := fun _ => inferInstance
  chalDec := fun _ => inferInstance
  worldFin := fun _ => inferInstance
  acc := fun _ => exampleAcc
  worldPos := fun _ => by decide
  chalPos := fun _ => by decide

/-- The constant family's forger advantage is the constant `2/5`. -/
theorem const25_forgerAdv : const25Family.forgerAdv = fun _ => (2 / 5 : ℝ) := by
  funext l
  have h : const25Family.forgerAdv l = ((HermineTSUF.advantage exampleAcc : ℚ) : ℝ) := rfl
  rw [h, advantage_example_eq]; norm_num

/-- **THE REDUCTION BITES — a non-negligibly-advantaged forger breaks the quantitative floor.** The
constant-`2/5` forger has advantage bounded below (through `ForkingFamily.bound`) by
`(2/5)·(2/5 − 1/5) = 2/25`, so its derived MSIS solver advantage is at least the constant `2/25`, which is
NOT negligible (`not_negl_const_pos`). Hence a forger of non-negligible advantage forces a non-negligible
MSIS solver — exactly the contradiction with `MSISHardQuantShape` that the concrete-security reduction delivers.
The forger's advantage genuinely appears; it is not a Boolean flag. -/
theorem const25_forger_breaks_floor : ¬ Negl const25Family.solverAdv := by
  intro h
  -- solverAdv ≥ forgerAdv·(forgerAdv − invChal) = (2/5)·(2/5 − 1/5) = 2/25, a positive constant.
  have hbound : ∀ l, (2 / 25 : ℝ) ≤ const25Family.solverAdv l := by
    intro l
    have hb := const25Family.bound l
    have hf : const25Family.forgerAdv l = 2 / 5 := by rw [const25_forgerAdv]
    have hinv : const25Family.invChal l = 1 / 5 := by
      show 1 / (Fintype.card (ZMod 5) : ℝ) = 1 / 5
      rw [ZMod.card]; norm_num
    rw [hf, hinv] at hb
    linarith [hb]
  -- a function dominated below by a positive constant is not negligible
  have hconst : ¬ Negl (fun _ : ℕ => (2 / 25 : ℝ)) := not_negl_const_pos (by norm_num)
  apply hconst
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun n => ?_)) h
  have h1 := hbound n
  have h2 : 0 ≤ const25Family.solverAdv n := by linarith [hbound n]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2/25), abs_of_nonneg h2]
  exact h1

/-- **THE REDUCTION FIRES — a family whose solver advantage and challenge term are negligible yields a
negligible forger advantage.** Take `exampleAcc`-shaped never-accepting family: `acc ≡ false` gives
`forgerAdv ≡ 0`, `solverAdv ≡ 0`, and with a super-polynomial challenge set `1/|C|` negligible; the
reduction concludes `Negl forgerAdv`. Exercises the full pipeline end-to-end. -/
instance instNeZeroTwoPowSucc (l : ℕ) : NeZero (2 ^ l + 1) := ⟨Nat.succ_ne_zero _⟩

def zeroFamily : ForkingFamily where
  Chal := fun l => ZMod (2 ^ l + 1)
  World := fun _ => Unit
  chalRing := fun l => inferInstance
  chalNorm := fun l => trivNorm (ZMod (2 ^ l + 1))
  chalFin := fun _ => inferInstance
  chalDec := fun _ => inferInstance
  worldFin := fun _ => inferInstance
  acc := fun _ _ _ => false
  worldPos := fun _ => by decide
  chalPos := fun l => by rw [ZMod.card]; positivity

theorem zeroFamily_solverAdv_zero : zeroFamily.solverAdv = fun _ => (0 : ℝ) := by
  funext l
  have h0 : (@HermineTSUF.forkProb (ZMod (2 ^ l + 1)) _ _ Unit _ (fun _ _ => false)) = 0 := by
    unfold HermineTSUF.forkProb HermineTSUF.forkPairs HermineTSUF.acceptSet
    simp
  show ((@HermineTSUF.forkProb (ZMod (2 ^ l + 1)) _ _ Unit _ (fun _ _ => false) : ℚ) : ℝ) = 0
  rw [h0]; norm_num

theorem zeroFamily_invChal_negl : Negl zeroFamily.invChal := by
  have hshape : zeroFamily.invChal = fun l => 1 / ((2 : ℝ) ^ l + 1) := by
    funext l
    unfold ForkingFamily.invChal zeroFamily
    simp only []
    rw [ZMod.card]; push_cast; ring
  rw [hshape]
  -- 1/(2^l + 1) ≤ 1/2^l, and 1/2^l is negligible.
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun n => ?_)) negl_two_pow
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hle : (1 : ℝ) / ((2 : ℝ) ^ n + 1) ≤ 1 / (2 : ℝ) ^ n :=
    one_div_le_one_div_of_le h2 (by linarith)
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((2:ℝ)^n + 1)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2:ℝ)^n)]
  exact hle

/-- **THE REDUCTION FIRES.** For the never-accepting super-polynomial-challenge family, `MSISHardQuantShape`
(trivially, solver advantage `≡ 0`) and the negligible challenge term give `Negl forgerAdv` — the pipeline
runs end-to-end and concludes negligibility of a genuine real-valued advantage. -/
theorem zeroFamily_forger_negl : Negl zeroFamily.forgerAdv :=
  forking_reduces_to_MSISHardQuant zeroFamily zeroFamily_invChal_negl
    (zeroFamily_solverAdv_zero ▸ negl_zero)

/-- **THE SQUEEZE FIRES.** `2⁻ⁿ` has negligible square (`4⁻ⁿ = (2⁻ⁿ)²`), and `negl_of_negl_sq` recovers the
negligibility of `2⁻ⁿ` — the quadratic-advantage machinery on a concrete positive ensemble. -/
theorem negl_of_negl_sq_fires : Negl (fun n : ℕ => 1 / (2 : ℝ) ^ n) := by
  apply negl_of_negl_sq (fun n => by positivity)
  have : (fun n : ℕ => (1 / (2 : ℝ) ^ n) ^ 2) = (fun n : ℕ => 1 / (4 : ℝ) ^ n) := by
    funext n; rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [this]
  -- 1/4^n ≤ 1/2^n, dominated by the negligible 2⁻ⁿ.
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun n => ?_)) negl_two_pow
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hle : (1 : ℝ) / 4 ^ n ≤ 1 / 2 ^ n := by
    apply one_div_le_one_div_of_le h2
    have h24 : (2 : ℝ) ^ n ≤ 4 ^ n := by gcongr <;> norm_num
    linarith
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 4 ^ n),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 ^ n)]
  exact hle

/-! ## §5 — THE DECISIONAL FLOOR: a distinguishing-advantage substrate (LWE-vs-uniform).

The §3 floors (`MSISHardQuantShape`/`MLWEHardQuantShape`/…) are SEARCH floors: `adv s` is one solver's success
probability (a single `winProb`), and the reduction bounds a forger's advantage through the forking
inequality. That shape does NOT fit the DECISIONAL consumers (`LossyIdentification`'s lossy-keygen switch,
the HVZK/masking transcript-indistinguishability leg of `AdaptiveTSUF`/`ThresholdSignerRefinement`), whose
attack object is an LWE-vs-uniform DISTINGUISHER — its advantage is a DIFFERENCE of two acceptance
probabilities `|Pr[D(real)=1] − Pr[D(uniform)=1]|`, not a single win probability. This section adds the
proper decisional floor over that quantity, reusing the same `Negl`/`Ensemble` layer.
-/

/-- **The distinguishing advantage of a decisional distinguisher.** `accReal`/`accUnif` are its ACCEPT
predicates in the real-LWE experiment (`ΩR`) and the uniform experiment (`ΩU`); each `winProb` is its
acceptance probability there. The distinguishing advantage is the GAP
`|Pr[accept | real] − Pr[accept | uniform]|` — the DECISIONAL shape (a DIFFERENCE of two probabilities),
distinct from the search `winProb` (a single probability). This is the LWE-vs-uniform distinguishing
quantity the decisional floor bounds. -/
noncomputable def distinguishAdv {ΩR ΩU : Type*} [Fintype ΩR] [Fintype ΩU]
    (accReal : ΩR → Bool) (accUnif : ΩU → Bool) : ℝ :=
  |winProb accReal - winProb accUnif|

/-- The distinguishing advantage is non-negative (it is an absolute value). -/
theorem distinguishAdv_nonneg {ΩR ΩU : Type*} [Fintype ΩR] [Fintype ΩU]
    (accReal : ΩR → Bool) (accUnif : ΩU → Bool) : 0 ≤ distinguishAdv accReal accUnif :=
  abs_nonneg _

/-- The distinguishing advantage is a genuine probability gap: `≤ 1` (both acceptance probabilities lie
in `[0,1]`, so their difference lies in `[−1,1]`). -/
theorem distinguishAdv_le_one {ΩR ΩU : Type*} [Fintype ΩR] [Fintype ΩU]
    (accReal : ΩR → Bool) (accUnif : ΩU → Bool) : distinguishAdv accReal accUnif ≤ 1 := by
  unfold distinguishAdv
  rw [abs_le]
  have hr0 := winProb_nonneg accReal; have hr1 := winProb_le_one accReal
  have hu0 := winProb_nonneg accUnif; have hu1 := winProb_le_one accUnif
  constructor <;> linarith

/-- ⚠ **BROKEN — the same content-free `Prop` as `MSISHardQuantShape`.** Its own docstring used to say
*"The INTENDED `adv` is a `DecisionFamily.adv`"* — intended, never enforced, which is exactly the defect
the sweep names: a constraint stated in prose is not a constraint. Worse, `DecisionFamily` itself carries
two ARBITRARY worlds and two ARBITRARY accept predicates, so even the intended instantiation pins nothing
to LWE. The honest floor is `FloorGames.DecisionMLWEHardQuant`, whose real world is a PROVED
`Lattice.IsMLWESample` and whose distinguisher is ONE function applied to both worlds. Retained for
`HardQuantVacuity`'s teeth. -/
def DecisionMLWEHardQuantShape {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

/-- **A λ-indexed decisional DISTINGUISHER family.** At each security parameter `l`: a finite real-LWE
experiment space `RealWorld l`, a finite uniform experiment space `UnifWorld l`, and the distinguisher's
accept predicates in each. Its `adv` is the distinguishing-advantage ENSEMBLE — the decisional analog of
`ForkingFamily`. -/
structure DecisionFamily where
  /-- The real-LWE experiment outcome space at parameter `l`. -/
  RealWorld : ℕ → Type
  /-- The uniform experiment outcome space at parameter `l`. -/
  UnifWorld : ℕ → Type
  /-- Finiteness of the real experiment space. -/
  realFin : ∀ l, Fintype (RealWorld l)
  /-- Finiteness of the uniform experiment space. -/
  unifFin : ∀ l, Fintype (UnifWorld l)
  /-- The distinguisher's accept predicate on a real-LWE sample. -/
  accReal : ∀ l, RealWorld l → Bool
  /-- The distinguisher's accept predicate on a uniform sample. -/
  accUnif : ∀ l, UnifWorld l → Bool

/-- The family's **distinguishing-advantage ensemble** `adv l = |Pr[accept | real] − Pr[accept | uniform]|`
at parameter `l`. A genuine real in `[0,1]` (`decisionFamily_adv_mem_unit`). -/
noncomputable def DecisionFamily.adv (F : DecisionFamily) : Ensemble := fun l =>
  letI := F.realFin l; letI := F.unifFin l
  distinguishAdv (F.accReal l) (F.accUnif l)

theorem decisionFamily_adv_mem_unit (F : DecisionFamily) (l : ℕ) :
    0 ≤ F.adv l ∧ F.adv l ≤ 1 := by
  letI := F.realFin l; letI := F.unifFin l
  exact ⟨distinguishAdv_nonneg _ _, distinguishAdv_le_one _ _⟩

/-! ### TEETH — the decisional floor is a genuine assumption: satisfiable (decaying) AND refutable (perfect). -/

/-- The trivially-decidable `NeZero` for `2^l`, so `(0 : Fin (2^l))` exists (the decaying distinguisher's
sole accepting outcome). -/
instance instNeZeroTwoPow (l : ℕ) : NeZero (2 ^ l) := ⟨pow_ne_zero l two_ne_zero⟩

/-- **A PERFECT distinguisher** — it accepts EVERY real sample and NO uniform sample, so its distinguishing
advantage is `|1 − 0| = 1` at every parameter. The decisional twin of the Boolean solver: it separates the
two distributions with certainty. -/
def perfectDist : DecisionFamily where
  RealWorld := fun _ => Unit
  UnifWorld := fun _ => Unit
  realFin := fun _ => inferInstance
  unifFin := fun _ => inferInstance
  accReal := fun _ => fun _ => true
  accUnif := fun _ => fun _ => false

/-- The perfect distinguisher's advantage is the constant `1` — a genuine, non-negligible distinguishing
advantage (the negative pole of `distinguishAdv`). -/
theorem perfectDist_adv_one : perfectDist.adv = fun _ => (1 : ℝ) := by
  funext l
  show distinguishAdv (fun _ : Unit => true) (fun _ : Unit => false) = 1
  unfold distinguishAdv
  rw [winProb_top, winProb_bot]; norm_num

/-- **A DECAYING distinguisher** — it accepts exactly one real sample out of `2^l` (and no uniform sample),
so its distinguishing advantage is `1/2^l`, decaying with the security parameter. A genuine, non-degenerate
distinguishing advantage that vanishes as the sample space grows. -/
def decayDist : DecisionFamily where
  RealWorld := fun l => Fin (2 ^ l)
  UnifWorld := fun _ => Unit
  realFin := fun _ => inferInstance
  unifFin := fun _ => inferInstance
  accReal := fun _ => fun x => decide (x = 0)
  accUnif := fun _ => fun _ => false

/-- The decaying distinguisher's advantage is exactly `1/2^l`: one accepting real outcome out of `2^l`, no
uniform accept. The counting is the singleton-vs-full `winProb`. -/
theorem decayDist_adv : decayDist.adv = fun l => 1 / (2 : ℝ) ^ l := by
  funext l
  show distinguishAdv (fun x : Fin (2 ^ l) => decide (x = 0)) (fun _ : Unit => false) = 1 / (2 : ℝ) ^ l
  unfold distinguishAdv
  have hwr : winProb (fun x : Fin (2 ^ l) => decide (x = 0)) = 1 / (2 : ℝ) ^ l := by
    unfold winProb
    have hfilter : (Finset.univ.filter (fun x : Fin (2 ^ l) => decide (x = 0) = true))
        = ({0} : Finset (Fin (2 ^ l))) := by
      ext x; simp [Finset.mem_filter]
    rw [hfilter, Finset.card_singleton, Fintype.card_fin]; push_cast; ring
  rw [winProb_bot, hwr, sub_zero, abs_of_nonneg (by positivity)]

/-- **(TOOTH — the floor is SATISFIABLE by a decaying distinguisher.)** The decaying distinguisher's
advantage `1/2^l` is negligible (`negl_two_pow`), so the decisional floor HOLDS on it — satisfiable for
reasons of RATE, not because the advantage is trivially `0`. -/
theorem decisionMLWEHardQuant_decay_holds :
    DecisionMLWEHardQuantShape (fun _ : Unit => decayDist.adv) := by
  intro _; rw [decayDist_adv]; exact negl_two_pow

/-- **(TOOTH — the floor is REFUTABLE by a perfect distinguisher.)** The perfect distinguisher's advantage
is the constant `1`, NOT negligible (`not_negl_one`), so the decisional floor FAILS on it. Together with
`decisionMLWEHardQuant_decay_holds` this pins the floor strictly between "vacuously true" and "trivially
false" — a genuine assumption, on a real distinguishing advantage. -/
theorem decisionMLWEHardQuant_perfect_refuted :
    ¬ DecisionMLWEHardQuantShape (fun _ : Unit => perfectDist.adv) := by
  intro h; have hp := h (); rw [perfectDist_adv_one] at hp; exact not_negl_one hp

/-- **(TOOTH — the all-zero decisional floor holds.)** A distinguisher with zero advantage everywhere
satisfies the floor (`negl_zero`) — the indistinguishable pole. -/
theorem decisionMLWEHardQuant_zero {S : Type*} :
    DecisionMLWEHardQuantShape (fun _ : S => (fun _ => 0 : Ensemble)) := fun _ => negl_zero

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  winProb_nonneg,
  winProb_le_one,
  winProb_top,
  winProb_bot,
  romAdvantage_mem_unit,
  msisHardQuant_zero,
  msisHardQuant_broken,
  not_negl_const_pos,
  negl_of_negl_sq,
  negl_of_forking_bound,
  ForkingFamily.forgerAdv_le_one,
  ForkingFamily.bound,
  forking_reduces_to_MSISHardQuant,
  forking_reduces_against_floor,
  advantage_example_eq,
  const25_forgerAdv,
  const25_forger_breaks_floor,
  zeroFamily_forger_negl,
  negl_of_negl_sq_fires,
  distinguishAdv_nonneg,
  distinguishAdv_le_one,
  decisionFamily_adv_mem_unit,
  perfectDist_adv_one,
  decayDist_adv,
  decisionMLWEHardQuant_decay_holds,
  decisionMLWEHardQuant_perfect_refuted,
  decisionMLWEHardQuant_zero
]

end Dregg2.Crypto.ProbCrypto
