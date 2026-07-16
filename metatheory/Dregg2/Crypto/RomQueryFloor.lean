/-
# `Dregg2.Crypto.RomQueryFloor` — a floor that is **PROVED**, because its adversary class is
**QUERY-BOUNDED** rather than unrestricted.

## The situation this file answers (all of it mechanized, in `FloorGames`)

`FloorGames.hard_top_iff_solvableFrac_negl` proves, for EVERY game `G`:

    Hard G (fun _ => True)  ↔  Negl (solvableFrac G)

At the unrestricted adversary class a game floor IS the probabilistic existence floor, because
`FloorGames.choiceAdv` — `Classical.choice`, reading the instance and picking a winning answer — is
a perfectly good `Adversary`. So every floor is FALSE at deployed parameters (pigeonhole), and
`Eff := ⊥` is vacuous (`hard_bot_vacuous`). `FloorGames` §8 names the residual: **`Eff` is a
parameter with no content, because the tree has no cost model.** `solvableIsAFiniteSearch` sharpens
it — brute force IS computable; what disqualifies it is COST, and `Fintype` cannot say `2^128`.

## What this file does: it gives `Eff` content, WITHOUT a cost model

The escape is not a complexity class. It is **the random oracle**.

An `Adversary G` is `run : ∀ l, G.Inst l → G.Ans l` — an arbitrary function OF THE WHOLE INSTANCE.
When the instance is an ORACLE (a uniformly sampled function `H : D l → R l`), that type lets the
adversary read all of `H` for free, and `choiceAdv` does exactly that. A real attacker cannot. It
learns `H` only by CALLING it, and each call is one unit of work.

`RomOracle.OracleComp` makes that a TYPE: a decision tree that branches only on answers it asked
for, with `RomOracle.QueryBounded Q M` bounding the calls along every path. `RomOracle.OracleComp.
eval_congr_of_agree_on_queried` is the load-bearing fact — two oracles agreeing on what `M` queried
are indistinguishable to `M`. `RomEff F Q` (§4) is then a genuine `Eff : Adversary G → Prop`: the
adversaries that FACTOR THROUGH a `Q`-query tree.

⚑ **This is a resource bound with no complexity theory in it.** `QueryBounded` is a property of the
adversary's SYNTAX, and the determination theorem converts that syntax into a constraint on its
BEHAVIOUR. Nothing here counts steps, no machine model appears, and no computational assumption is
made. Contrast `ConcreteSecurity.StepBound.PPT`, which is already in the tree: it is
`PolyBoundedNat` applied to a bare `steps : ℕ → ℕ` that is attached to no adversary and constrains
no behaviour — a name for a number sequence. It cannot serve as an `Eff`, and nothing uses it as one.

## §5 — the bound, and it is INFORMATION-THEORETIC

`birthday_cond` proves, by induction on the query tree over `RomCounting`'s lazy-sampling-as-counting
lemmas:

    condProb (cyl S σ) (collWin M)  ≤  (Q * S.card + Q * Q + 1) / |R|

At `S = ∅` that is `birthday_bound`: **a `Q`-query adversary finds a collision in a random oracle
with probability at most `(Q² + 1)/|R|`.** The classic birthday bound. There is no assumption under
it — no MSIS, no MLWE, no "hash is collision resistant". It is a counting fact about the function
space `D → R`, and the whole of its content is `RomCounting.condProb_fresh_eq`: *what the adversary
has not queried, it does not know.*

## §6–§7 — BOTH ESCAPES, PROVED

  * **The class is not `⊤` in disguise.** `romCollision_hard`: at a `λ`-growing range
    (`|R l| = 2^l`) and a polynomially-bounded budget, `Hard (romCollisionGame F) (RomEff F Q)` is
    TRUE. `romCollision_top_false`: at the SAME game, `Hard _ ⊤` is FALSE — by the SAME pigeonhole
    that refutes `HashFloorHonesty.CollisionResistant` (`FloorGames.collisionResistant_false_of_
    compressing`). `romEff_not_iff_solvableFrac_negl` states the consequence directly: **the
    collapse `↔` FAILS for `RomEff`.** `choiceAdv_not_romEff` names the reason — `Classical.choice`'s
    adversary is PROVED not to be in the class. It cannot query; it would have to already know.
  * **The class is not `⊥` in disguise.** `twoPointAdv_in_romEff` exhibits a member that genuinely
    uses its queries, and `twoPointAdv_gameAdv_eq` computes its advantage EXACTLY: `1/|R l|`,
    which `twoPointAdv_gameAdv_pos` shows is nonzero. A real adversary, really in the class, really
    winning sometimes.

⚑ **So one floor in this tree is now PROVED rather than assumed**, and the honest scope is exactly
that: this route works for HASH-BASED soundness (a random oracle), and for NOTHING ELSE. MSIS and
MLWE remain assumptions — correctly, nobody proves them — and their `Eff` residual stands as
`FloorGames` §8 states it.

## The named residual, not closed here

`RomEff`'s budget is a QUERY count, not a running time. A `Q`-query adversary may do unbounded work
BETWEEN queries (the continuations `k : R → OracleComp ..` are arbitrary functions, and may be
`Classical.choice`). That is sound for hash-based bounds — the classic ROM bounds are exactly of
this shape, and the whole point is that they hold against a computationally UNBOUNDED, query-bounded
adversary — but it is not a cost model, and it does not restrict a lattice adversary at all, which
makes no oracle calls. The general PPT `Eff` remains open, and it remains a parameter.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.RomCounting
import Dregg2.Crypto.RomOracle
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomQueryFloor

open Dregg2.Crypto.ConcreteSecurity
  (Ensemble Negl PolyBounded negl_two_pow negl_mul_poly negl_of_eventually_le not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary Hard gameAdv gameAdv_mem_unit solvableFrac choiceAdv choiceAdv_gameAdv
   hard_top_iff_solvableFrac_negl not_hard_top_of_always_solvable)
open Dregg2.Crypto.RomCounting
  (cyl mem_cyl cyl_empty cyl_nonempty cyl_card_pos condProb condProb_nonneg condProb_le_one
   condProb_congr condProb_le_of_imp condProb_eq_zero condProb_eq_one condProb_cyl_empty
   condProb_split condProb_fresh_eq)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)

set_option autoImplicit false

/-! ## §1 — the collision win event of an oracle computation. -/

/-- **THE COLLISION WIN EVENT.** `M` wins against oracle `H` iff the pair it outputs is a genuine
collision of `H` — distinct points, equal images. The problem is IN the predicate. -/
def collWin {D R : Type} [DecidableEq D] [DecidableEq R]
    (M : OracleComp D R (D × D)) : (D → R) → Bool := fun H =>
  let p := M.eval H
  decide (p.1 ≠ p.2) && decide (H p.1 = H p.2)

/-- A halted computation wins iff the pair it holds is a collision. -/
theorem collWin_pure {D R : Type} [DecidableEq D] [DecidableEq R] (a : D × D) (H : D → R) :
    collWin (OracleComp.pure a : OracleComp D R (D × D)) H
      = (decide (a.1 ≠ a.2) && decide (H a.1 = H a.2)) := rfl

/-- **A QUERY IS A REDUCTION TO THE CONTINUATION.** Running `query d k` against `H` is running the
continuation at the answer `H d`. The step the induction of §5 takes. -/
theorem collWin_query {D R : Type} [DecidableEq D] [DecidableEq R]
    (d : D) (k : R → OracleComp D R (D × D)) (H : D → R) :
    collWin (OracleComp.query d k) H = collWin (k (H d)) H := rfl

section Bound

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-! ## §2 — two points collide with probability at most `1/|R|`, whatever is already known.

The base case of §5, and the place `RomCounting.condProb_fresh_eq` does its work: a point the
conditioning has not pinned takes a uniform value, so it lands on any fixed target with probability
exactly `1/|R|`. -/

/-- **TWO FRESH POINTS COLLIDE WITH PROBABILITY EXACTLY `1/|R|`.** Neither `x` nor `y` is pinned by
the conditioning: split on `x`'s value, and `y` — still fresh — must hit it. -/
theorem condProb_two_fresh_eq (S : Finset D) (σ : D → R) (x y : D)
    (hx : x ∉ S) (hy : y ∉ S) (hxy : x ≠ y) :
    condProb (cyl S σ) (fun H => decide (H x = H y)) = 1 / (Fintype.card R : ℝ) := by
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [condProb_split S σ x hx]
  have hval : ∀ r : R, condProb (cyl (insert x S) (Function.update σ x r))
      (fun H => decide (H x = H y)) = 1 / (Fintype.card R : ℝ) := by
    intro r
    have hpin : ∀ H ∈ cyl (insert x S) (Function.update σ x r), H x = r := by
      intro H hH
      have := (mem_cyl.1 hH) x (Finset.mem_insert_self x S)
      simpa using this
    have hyfresh : y ∉ insert x S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hxy h.symm, hy⟩
    rw [condProb_congr (win' := fun H => decide (H y = r)) ?_]
    · exact condProb_fresh_eq _ _ y hyfresh r
    · intro H hH
      rw [hpin H hH]
      by_cases h : r = H y <;> simp [h, eq_comm]
  rw [Finset.sum_congr rfl (fun r _ => hval r), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **TWO POINTS COLLIDE WITH PROBABILITY AT MOST `1/|R|` — under any collision-free conditioning.**
All four cases: both points already pinned (then `σ` collision-freeness makes the event impossible),
one pinned (the fresh one must hit the pinned value), or neither (`condProb_two_fresh_eq`). -/
theorem condProb_collide_le (S : Finset D) (σ : D → R) (x y : D) (hxy : x ≠ y)
    (hσ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b) :
    condProb (cyl S σ) (fun H => decide (H x = H y)) ≤ 1 / (Fintype.card R : ℝ) := by
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · -- Both pinned: `σ` has no collision on `S`, so the event is empty.
      refine le_of_eq_of_le (condProb_eq_zero ?_) (by positivity)
      intro H hH
      have h1 := (mem_cyl.1 hH) x hx
      have h2 := (mem_cyl.1 hH) y hy
      simp only [decide_eq_false_iff_not, h1, h2]
      exact hσ x hx y hy hxy
    · -- `x` pinned to `σ x`, `y` fresh: `y` must hit `σ x`.
      refine le_of_eq ?_
      rw [condProb_congr (win' := fun H => decide (H y = σ x)) ?_]
      · exact condProb_fresh_eq _ _ y hy (σ x)
      · intro H hH
        rw [(mem_cyl.1 hH) x hx]
        by_cases h : σ x = H y <;> simp [h, eq_comm]
  · by_cases hy : y ∈ S
    · -- `y` pinned to `σ y`, `x` fresh: `x` must hit `σ y`.
      refine le_of_eq ?_
      rw [condProb_congr (win' := fun H => decide (H x = σ y)) ?_]
      · exact condProb_fresh_eq _ _ x hx (σ y)
      · intro H hH
        rw [(mem_cyl.1 hH) y hy]
    · exact le_of_eq (condProb_two_fresh_eq S σ x y hx hy hxy)

/-! ## §3 — ⚑ THE BIRTHDAY BOUND, by induction on the query tree.

The invariant is the whole argument: `σ` records what the adversary has ALREADY LEARNED, and it is
maintained COLLISION-FREE — because the moment two learned answers collide the adversary has won,
and the induction pays for that branch at full price (`condProb_le_one`). A fresh query lands in the
already-learned image with probability at most `|S|/|R|`, which is what accumulates to `Q²/|R|`. -/

/-- **⚑ THE CONDITIONAL BIRTHDAY BOUND.** A `Q`-query computation, run against an oracle already
pinned to a collision-free `σ` on `S`, outputs a collision with probability at most
`(Q·|S| + Q² + 1)/|R|`.

The three sources of the bound, visible in the proof: the `+1` is the final guess (an unqueried pair
collides with probability `1/|R|`, §2); the `Q·|S|` is the chance a fresh query lands on an
already-known answer; the `Q²` accumulates that as `|S|` grows by one per query.

NOTHING IS ASSUMED. This is a counting statement about the finite function space `D → R`. -/
theorem birthday_cond {Q : ℕ} {M : OracleComp D R (D × D)} (hM : QueryBounded Q M) :
    ∀ (S : Finset D) (σ : D → R), (∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b) →
      condProb (cyl S σ) (collWin M) ≤ (Q * S.card + Q * Q + 1) / (Fintype.card R : ℝ) := by
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  induction hM with
  | pure n a =>
      intro S σ hσ
      have hone : condProb (cyl S σ) (collWin (OracleComp.pure a : OracleComp D R (D × D)))
          ≤ 1 / (Fintype.card R : ℝ) := by
        by_cases hne : a.1 = a.2
        · refine le_of_eq_of_le (condProb_eq_zero ?_) (by positivity)
          intro H _
          simp [collWin_pure, hne]
        · rw [condProb_congr (win' := fun H => decide (H a.1 = H a.2))
            (fun H _ => by simp [collWin_pure, hne])]
          exact condProb_collide_le S σ a.1 a.2 hne hσ
      refine hone.trans ?_
      rw [div_le_div_iff_of_pos_right hRpos]
      have : (1 : ℝ) ≤ ((n * S.card + n * n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
      push_cast at this ⊢
      linarith
  | query n d k _hk ih =>
      intro S σ hσ
      by_cases hd : d ∈ S
      · -- The query is already answered by the conditioning: it learns nothing new.
        have hcongr : condProb (cyl S σ) (collWin (OracleComp.query d k))
            = condProb (cyl S σ) (collWin (k (σ d))) := by
          refine condProb_congr (fun H hH => ?_)
          rw [collWin_query, (mem_cyl.1 hH) d hd]
        rw [hcongr]
        refine (ih (σ d) S σ hσ).trans ?_
        rw [div_le_div_iff_of_pos_right hRpos]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) S.card, Nat.cast_nonneg (α := ℝ) n]
      · -- A FRESH query. Split on its answer.
        rw [condProb_split S σ d hd]
        set B : ℝ := (n * (S.card + 1) + n * n + 1) / (Fintype.card R : ℝ) with hB
        have hBnn : 0 ≤ B := by rw [hB]; positivity
        -- Each slice: the continuation at the answer, bounded by the IH when the answer is NEW.
        have hterm : ∀ r : R,
            condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k))
              = condProb (cyl (insert d S) (Function.update σ d r)) (collWin (k r)) := by
          intro r
          refine condProb_congr (fun H hH => ?_)
          have hpin : H d = r := by
            have := (mem_cyl.1 hH) d (Finset.mem_insert_self d S)
            simpa using this
          rw [collWin_query, hpin]
        have hgood : ∀ r ∈ Finset.univ \ S.image σ,
            condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k))
              ≤ B := by
          intro r hr
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image,
            not_exists] at hr
          have hrnew : ∀ a ∈ S, σ a ≠ r := by
            intro a ha h
            exact hr a ⟨ha, h⟩
          rw [hterm r]
          have hσ' : ∀ a ∈ insert d S, ∀ b ∈ insert d S, a ≠ b →
              Function.update σ d r a ≠ Function.update σ d r b := by
            intro a ha b hb hab
            simp only [Finset.mem_insert] at ha hb
            rcases ha with rfl | ha
            · rcases hb with rfl | hb
              · exact absurd rfl hab
              · have hbd : b ≠ a := fun h => hd (h ▸ hb)
                rw [Function.update_self, Function.update_of_ne hbd]
                exact fun h => hrnew b hb h.symm
            · rcases hb with rfl | hb
              · have had : a ≠ b := fun h => hd (h ▸ ha)
                rw [Function.update_self, Function.update_of_ne had]
                exact hrnew a ha
              · have had : a ≠ d := fun h => hd (h ▸ ha)
                have hbd : b ≠ d := fun h => hd (h ▸ hb)
                rw [Function.update_of_ne had, Function.update_of_ne hbd]
                exact hσ a ha b hb hab
          have := ih r (insert d S) (Function.update σ d r) hσ'
          rw [hB]
          refine this.trans (le_of_eq ?_)
          rw [Finset.card_insert_of_notMem hd]
          push_cast
          ring
        -- The BAD answers — the ones that collide with something already known — are at most `|S|`
        -- many, and we pay full price on each.
        have hsub : S.image σ ⊆ (Finset.univ : Finset R) := Finset.subset_univ _
        have hsplit : (∑ r : R,
              condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
            = (∑ r ∈ Finset.univ \ S.image σ,
                condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
              + (∑ r ∈ S.image σ,
                condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
            := (Finset.sum_sdiff hsub).symm
        have hbad : (∑ r ∈ S.image σ,
              condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
            ≤ (S.card : ℝ) := by
          refine (Finset.sum_le_card_nsmul _ _ 1 (fun r _ => condProb_le_one _ _)).trans ?_
          rw [nsmul_eq_mul, mul_one]
          exact_mod_cast Finset.card_image_le
        have hgoodsum : (∑ r ∈ Finset.univ \ S.image σ,
              condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
            ≤ (Fintype.card R : ℝ) * B := by
          refine (Finset.sum_le_card_nsmul _ _ B hgood).trans ?_
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hBnn
          have : (Finset.univ \ S.image σ).card ≤ Fintype.card R := by
            simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ \ S.image σ))
          exact_mod_cast this
        have hRB : (Fintype.card R : ℝ) * B = ((n * (S.card + 1) + n * n + 1 : ℕ) : ℝ) := by
          rw [hB, mul_div_assoc']
          rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hRpos), mul_one]
          push_cast
          ring
        rw [hsplit]
        rw [div_le_iff₀ hRpos]
        have hnum : (∑ r ∈ Finset.univ \ S.image σ,
              condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
            + (∑ r ∈ S.image σ,
              condProb (cyl (insert d S) (Function.update σ d r)) (collWin (OracleComp.query d k)))
            ≤ ((n * (S.card + 1) + n * n + 1 : ℕ) : ℝ) + (S.card : ℝ) := by
          refine add_le_add (hgoodsum.trans (le_of_eq hRB)) hbad
        refine hnum.trans ?_
        rw [div_mul_cancel₀ _ (ne_of_gt hRpos)]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) S.card, Nat.cast_nonneg (α := ℝ) n]

/-- **⚑ THE BIRTHDAY BOUND — a `Q`-query adversary finds a collision in a random oracle with
probability at most `(Q² + 1)/|R|`.**

`birthday_cond` at the EMPTY conditioning: the adversary starts knowing nothing. This is the classic
unconditional ROM bound, and it is a THEOREM here — not a hypothesis, not a named carrier, not an
assumption about any hash function. Its only inputs are that the oracle is a uniformly sampled
element of the finite type `D → R` and that the adversary makes at most `Q` calls. -/
theorem birthday_bound (Q : ℕ) (M : OracleComp D R (D × D)) (hM : QueryBounded Q M) :
    Dregg2.Crypto.ProbCrypto.winProb (collWin M) ≤ (Q * Q + 1) / (Fintype.card R : ℝ) := by
  have h := birthday_cond hM ∅ (fun _ => Classical.arbitrary R) (by simp)
  rw [condProb_cyl_empty] at h
  simpa using h

end Bound

/-! ## §4 — the random-oracle family, its collision GAME, and the query-bounded CLASS. -/

/-- **A RANDOM-ORACLE FAMILY.** At each security parameter, a finite domain and a finite range. The
oracle is a uniformly sampled function `D l → R l`; it IS the instance of the game below. No hash
function is named, and none is needed — in the random oracle model the sampled function is the
object. -/
structure RomFamily where
  /-- The oracle's domain at parameter `l` — what can be hashed. -/
  D : ℕ → Type
  /-- The oracle's range at parameter `l` — the digest space. -/
  R : ℕ → Type
  /-- The domain is finite. -/
  dFin : ∀ l, Fintype (D l)
  /-- Decidable equality on the domain (the win event checks `x ≠ y`). -/
  dDec : ∀ l, DecidableEq (D l)
  /-- The domain is inhabited. -/
  dNe : ∀ l, Nonempty (D l)
  /-- The range is finite (the oracle space `D l → R l` must be a finite outcome space). -/
  rFin : ∀ l, Fintype (R l)
  /-- Decidable equality on the range (the win event checks the digests agree). -/
  rDec : ∀ l, DecidableEq (R l)
  /-- The range is inhabited. -/
  rNe : ∀ l, Nonempty (R l)

/-- **THE ROM COLLISION GAME.** The instance is THE ORACLE — a uniformly sampled `H : D l → R l`.
The adversary outputs a pair, and WINS iff that pair is a genuine collision of `H`.

⚑ Note what the `Game` schema does to an oracle: `Adversary G` is `∀ l, (D l → R l) → (D l × D l)`,
a function that receives the WHOLE function `H`. That type is the disease — it hands the adversary
the oracle's entire truth table for free. §4's `RomEff` is the cure, and it is a restriction on that
same `Adversary` type, so this game plugs into `FloorGames.Hard` unchanged. -/
def romCollisionGame (F : RomFamily) : Game where
  Inst := fun l => F.D l → F.R l
  Ans := fun l => F.D l × F.D l
  instFin := fun l => by
    letI := F.dFin l; letI := F.dDec l; letI := F.rFin l
    infer_instance
  instNe := fun l => by
    letI := F.rNe l
    exact ⟨fun _ => Classical.arbitrary (F.R l)⟩
  wins := fun _ H p => p.1 ≠ p.2 ∧ H p.1 = H p.2
  winsDec := fun l _ _ => by
    letI := F.dDec l; letI := F.rDec l
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the ROM collision game's win relation is a genuine
collision of the sampled oracle. -/
theorem romCollisionGame_wins_iff (F : RomFamily) (l : ℕ) (H : (romCollisionGame F).Inst l)
    (p : (romCollisionGame F).Ans l) :
    (romCollisionGame F).wins l H p ↔ (p.1 ≠ p.2 ∧ H p.1 = H p.2) := Iff.rfl

/-- A family of oracle computations, one per security parameter — the syntax of an attack. -/
abbrev RomComp (F : RomFamily) : Type :=
  ∀ l, OracleComp (F.D l) (F.R l) (F.D l × F.D l)

/-- The ordinary adversary a query tree induces: run the tree against the oracle. -/
def romAdv (F : RomFamily) (M : RomComp F) : Adversary (romCollisionGame F) where
  run := fun l H => (M l).eval H

/-- **⚑ THE QUERY-BOUNDED ADVERSARY CLASS — the `Eff` this whole development is for.**

`RomEff F Q A` says: `A` FACTORS THROUGH a query tree that makes at most `Q l` oracle calls. It is a
predicate on the SAME `Adversary (romCollisionGame F)` type `FloorGames.Hard` quantifies over, so
`Hard (romCollisionGame F) (RomEff F Q)` is the tree's existing floor schema at a class with real
content.

⚑ It is neither pole, and both facts are PROVED below, not asserted: not `⊤`
(`choiceAdv_not_romEff` — `Classical.choice`'s adversary is excluded, because it would have to know
answers it never asked for), and not `⊥` (`twoPointAdv_in_romEff`, which has advantage exactly
`1/|R l| > 0`). -/
def RomEff (F : RomFamily) (Q : ℕ → ℕ) : Adversary (romCollisionGame F) → Prop := fun A =>
  ∃ M : RomComp F, (∀ l, QueryBounded (Q l) (M l)) ∧
    ∀ l (H : (romCollisionGame F).Inst l), A.run l H = (M l).eval H

/-! ## §5 — the `⊤` pole of THIS game is FALSE, by the SAME pigeonhole. -/

/-- **EVERY ORACLE OF A COMPRESSING FAMILY HAS A COLLISION.** Pigeonhole, on the tree's own
counting: strictly more inputs than digests means no oracle is injective. This is the defining
property of a hash, and it is why `FloorGames.collisionResistant_false_of_compressing` refutes the
unrestricted floor. -/
theorem romCollision_always_solvable (F : RomFamily)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l; Fintype.card (F.R l) < Fintype.card (F.D l))
    (l : ℕ) (H : (romCollisionGame F).Inst l) :
    ∃ p, (romCollisionGame F).wins l H p := by
  letI := F.dFin l; letI := F.rFin l
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt H (hc l)
  exact ⟨(x, y), hne, heq⟩

/-- **THE UNRESTRICTED FLOOR IS FALSE AT THIS GAME.** A collision exists at every oracle, so
`solvableFrac` is the constant `1` and `FloorGames.hard_top_iff_solvableFrac_negl` refutes the
floor. The SAME fate as every other floor in the tree — and §6 proves the query-bounded floor at
this same game is TRUE, which is the entire point. -/
theorem romCollision_top_false (F : RomFamily)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l; Fintype.card (F.R l) < Fintype.card (F.D l)) :
    ¬ Hard (romCollisionGame F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (romCollisionGame F) (fun l => ?_)
    (romCollision_always_solvable F hc)
  letI := F.dNe l
  exact ⟨(Classical.arbitrary (F.D l), Classical.arbitrary (F.D l))⟩

/-! ## §6 — ⚑ THE FLOOR, PROVED. -/

/-- The induced adversary's win event IS the collision win event of its tree. -/
theorem romAdv_hit (F : RomFamily) (M : RomComp F) (l : ℕ) (H : (romCollisionGame F).Inst l) :
    letI := F.dDec l; letI := F.rDec l
    (romAdv F M).hit l H = collWin (M l) H := by
  letI := F.dDec l; letI := F.rDec l
  unfold Adversary.hit collWin romAdv
  simp only [romCollisionGame, Bool.decide_and]

/-- **A `Q`-QUERY ADVERSARY'S ADVANTAGE AT PARAMETER `l` IS AT MOST `(Q² + 1)/|R l|`.** The
`birthday_bound` transported onto the game's advantage. -/
theorem romAdv_gameAdv_le (F : RomFamily) (Q : ℕ → ℕ) (M : RomComp F)
    (hM : ∀ l, QueryBounded (Q l) (M l)) (l : ℕ) :
    gameAdv (romCollisionGame F) (romAdv F M) l
      ≤ ((Q l) * (Q l) + 1) / (letI := F.rFin l; (Fintype.card (F.R l) : ℝ)) := by
  letI := F.dFin l; letI := F.dDec l; letI := F.rFin l; letI := F.rDec l; letI := F.rNe l
  have h := birthday_bound (D := F.D l) (R := F.R l) (Q l) (M l) (hM l)
  unfold gameAdv
  rw [show ((romAdv F M).hit l) = collWin (M l) from funext (romAdv_hit F M l)]
  exact h

/-- **⚑⚑ THE HASH FLOOR, PROVED — not assumed.**

At a `λ`-growing digest space (`|R l| = 2^l`, the deployed shape of a hash) and a polynomially
bounded query budget, EVERY query-bounded adversary's collision advantage is negligible.

⚑ Compare what this replaces. `HashFloorHonesty.CollisionResistant F` is `HashCRHardQuant F ⊤`
(`FloorGames.collisionResistant_iff_hashCRHardQuant_top`) and is FALSE at a compressing family
(`FloorGames.collisionResistant_false_of_compressing`). `MSISHardQuant F Eff` is a floor whose `Eff`
has no content. THIS statement has a hypothesis-free adversary class, a proved bound
(`birthday_bound`), and no cryptographic assumption anywhere under it. The `Negl` comes from
`negl_two_pow` — the digest space outruns the budget.

The two hypotheses are exactly the deployed facts and nothing more: the digest is `λ` bits wide, and
the attacker makes polynomially many calls. -/
theorem romCollision_hard (F : RomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l) :
    Hard (romCollisionGame F) (RomEff F Q) := by
  rintro A ⟨M, hMQ, hrun⟩
  have hAM : gameAdv (romCollisionGame F) A = gameAdv (romCollisionGame F) (romAdv F M) := by
    unfold gameAdv Adversary.hit
    funext l
    congr 1
    funext H
    rw [hrun l H]
    rfl
  rw [hAM]
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun l => ?_))
    (negl_mul_poly hQ negl_two_pow)
  have h0 : 0 ≤ gameAdv (romCollisionGame F) (romAdv F M) l :=
    (gameAdv_mem_unit (romCollisionGame F) (romAdv F M) l).1
  have hle := romAdv_gameAdv_le F Q M hMQ l
  rw [hw l] at hle
  have hkey : ((Q l : ℝ) * (Q l : ℝ) + 1) * (1 / (2 : ℝ) ^ l)
      = ((Q l : ℝ) * (Q l : ℝ) + 1) / ((2 ^ l : ℕ) : ℝ) := by
    push_cast
    ring
  rw [abs_of_nonneg h0, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((Q l : ℝ) * (Q l : ℝ) + 1) * (1 / (2:ℝ) ^ l)),
    hkey]
  exact hle

/-! ## §7 — ⚑ BOTH ESCAPES, PROVED. -/

/-- **⚑⚑⚑ `Classical.choice`'S ADVERSARY IS NOT IN THE CLASS — proved.**

This is the load-bearing exclusion, and the reason the whole approach works. `FloorGames.choiceAdv`
reads the oracle's entire truth table and returns a collision; its advantage is `solvableFrac`, the
constant `1` at a compressing family. If it were query-bounded, `romCollision_hard` would make `1`
negligible.

⚑ The INFORMATIONAL content, which is what makes this different from a definitional dodge: a query
tree's output is a function of the answers it received (`RomOracle.OracleComp.eval_congr_of_agree_
on_queried`) and of nothing else. `choiceAdv` would have to KNOW where the collision is without
asking. In the random oracle model there is nowhere to know it from. -/
theorem choiceAdv_not_romEff (F : RomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l; Fintype.card (F.R l) < Fintype.card (F.D l))
    (hne : ∀ l, Nonempty ((romCollisionGame F).Ans l)) :
    ¬ RomEff F Q (choiceAdv (romCollisionGame F) hne) := by
  intro hmem
  have hnegl := romCollision_hard F Q hQ hw _ hmem
  rw [choiceAdv_gameAdv] at hnegl
  exact romCollision_top_false F hc ((hard_top_iff_solvableFrac_negl (romCollisionGame F) hne).mpr hnegl)

/-- **⚑⚑⚑ THE COLLAPSE FAILS FOR `RomEff` — the escape, stated as the direct negation of
`FloorGames.hard_top_iff_solvableFrac_negl`'s shape.**

    ¬ (Hard G (RomEff F Q)  ↔  Negl (solvableFrac G))

At `Eff := ⊤` the equivalence is a THEOREM (`hard_top_iff_solvableFrac_negl`) and it is what makes
every unrestricted floor false at deployed parameters. At `Eff := RomEff F Q` the left side is TRUE
(`romCollision_hard`) and the right side is FALSE (a collision exists at every oracle, so
`solvableFrac = 1`). The query-bounded class is therefore PROVABLY not the unrestricted one, and the
argument that refutes every other floor in this tree does not reach this one. -/
theorem romEff_not_iff_solvableFrac_negl (F : RomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l; Fintype.card (F.R l) < Fintype.card (F.D l)) :
    ¬ (Hard (romCollisionGame F) (RomEff F Q) ↔ Negl (solvableFrac (romCollisionGame F))) := by
  intro h
  have hne : ∀ l, Nonempty ((romCollisionGame F).Ans l) := fun l => by
    letI := F.dNe l
    exact ⟨(Classical.arbitrary (F.D l), Classical.arbitrary (F.D l))⟩
  have hsolv := h.mp (romCollision_hard F Q hQ hw)
  exact romCollision_top_false F hc ((hard_top_iff_solvableFrac_negl (romCollisionGame F) hne).mpr hsolv)

/-- **⚑ THE CLASS IS NOT `⊤`.** The immediate corollary: `RomEff F Q` is not the unrestricted class,
as a `Prop`-valued predicate. -/
theorem romEff_ne_top (F : RomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l; Fintype.card (F.R l) < Fintype.card (F.D l)) :
    RomEff F Q ≠ (fun _ => True) := by
  intro h
  have hhard := romCollision_hard F Q hQ hw
  rw [h] at hhard
  exact romCollision_top_false F hc hhard

/-! ### The other pole: the class is NOT `⊥` — it contains a real, winning adversary. -/

/-- **A GENUINE TWO-QUERY ADVERSARY.** It queries `x`, queries `y`, and outputs the pair `(x, y)` iff
the two answers agree — otherwise it outputs `(x, x)`, which is not a collision. It USES what it
learned: its output is a nonconstant function of the oracle's answers. -/
def twoPointComp (F : RomFamily) (l : ℕ) (x y : F.D l) :
    OracleComp (F.D l) (F.R l) (F.D l × F.D l) :=
  letI := F.rDec l
  .query x (fun rx => .query y (fun ry => if rx = ry then .pure (x, y) else .pure (x, x)))

/-- The two-query adversary makes two queries. -/
theorem twoPointComp_bounded (F : RomFamily) (l : ℕ) (x y : F.D l) :
    QueryBounded 2 (twoPointComp F l x y) := by
  letI := F.rDec l
  refine QueryBounded.query 1 x _ (fun rx => QueryBounded.query 0 y _ (fun ry => ?_))
  by_cases h : rx = ry <;> simp only [h, reduceIte] <;>
    exact QueryBounded.pure 0 _


/-- **THE TWO-QUERY ADVERSARY WINS EXACTLY WHEN ITS TWO PROBES COLLIDE.** -/
theorem twoPointComp_collWin (F : RomFamily) (l : ℕ) (x y : F.D l) (hxy : x ≠ y)
    (H : F.D l → F.R l) :
    letI := F.dDec l; letI := F.rDec l
    collWin (twoPointComp F l x y) H = decide (H x = H y) := by
  letI := F.dDec l; letI := F.rDec l
  by_cases h : H x = H y
  · simp only [collWin, twoPointComp, OracleComp.eval, h, reduceIte, decide_true,
      Bool.and_true, decide_not]
    simpa using hxy
  · simp only [collWin, twoPointComp, OracleComp.eval, h, reduceIte]
    simp

/-- **⚑ THE CLASS IS INHABITED BY A REAL ADVERSARY.** The two-query attack is in `RomEff F Q` for
any budget `Q ≥ 2`. -/
theorem twoPointAdv_in_romEff (F : RomFamily) (Q : ℕ → ℕ) (hQ : ∀ l, 2 ≤ Q l)
    (x y : ∀ l, F.D l) :
    RomEff F Q (romAdv F (fun l => twoPointComp F l (x l) (y l))) :=
  ⟨fun l => twoPointComp F l (x l) (y l),
   fun l => (twoPointComp_bounded F l (x l) (y l)).mono (hQ l),
   fun _ _ => rfl⟩

/-- **⚑⚑ NOT VACUOUS — the class contains an adversary whose advantage is EXACTLY `1/|R l|`.**

`hard_bot_vacuous` proves `Eff := ⊥` satisfies every floor, so a floor is only as good as the
witness that its class is inhabited. This is that witness, and it is stronger than inhabitation: the
advantage is computed exactly, and it is NONZERO (`twoPointAdv_gameAdv_pos`). The class contains an
attack that really runs, really queries, and really wins sometimes — so `romCollision_hard` is a
statement about something. -/
theorem twoPointAdv_gameAdv_eq (F : RomFamily) (l : ℕ) (x y : ∀ l, F.D l) (hxy : x l ≠ y l) :
    gameAdv (romCollisionGame F) (romAdv F (fun l => twoPointComp F l (x l) (y l))) l
      = 1 / (letI := F.rFin l; (Fintype.card (F.R l) : ℝ)) := by
  letI := F.dFin l; letI := F.dDec l; letI := F.rFin l; letI := F.rDec l; letI := F.rNe l
  have hkey := condProb_two_fresh_eq (D := F.D l) (R := F.R l) ∅
    (fun _ => Classical.arbitrary (F.R l)) (x l) (y l) (by simp) (by simp) hxy
  rw [condProb_cyl_empty] at hkey
  unfold gameAdv
  rw [show ((romAdv F (fun l => twoPointComp F l (x l) (y l))).hit l)
        = (fun H => decide (H (x l) = H (y l))) from
      funext (fun H => by
        rw [romAdv_hit F (fun l => twoPointComp F l (x l) (y l)) l H]
        exact twoPointComp_collWin F l (x l) (y l) hxy H)]
  exact hkey

/-- **(TOOTH — the member's advantage is positive.)** The class is not `⊥` in disguise. -/
theorem twoPointAdv_gameAdv_pos (F : RomFamily) (l : ℕ) (x y : ∀ l, F.D l) (hxy : x l ≠ y l) :
    0 < gameAdv (romCollisionGame F) (romAdv F (fun l => twoPointComp F l (x l) (y l))) l := by
  letI := F.rFin l; letI := F.rNe l
  rw [twoPointAdv_gameAdv_eq F l x y hxy]
  have : (0 : ℝ) < (Fintype.card (F.R l) : ℝ) := by exact_mod_cast Fintype.card_pos
  positivity

/-! ## §8 — a DEPLOYED-SHAPE instance: a `λ`-bit digest, twice as many inputs. -/

/-- **THE DEPLOYED SHAPE.** A `λ`-bit digest space and a strictly larger domain — compressing, which
is what a hash is. Everything above fires on it: the unrestricted floor is FALSE
(`binaryRom_top_false`) and the query-bounded floor is TRUE (`binaryRom_hard`), at the same game. -/
def binaryRomFamily : RomFamily where
  D := fun l => Fin (2 * 2 ^ l)
  R := fun l => Fin (2 ^ l)
  dFin := fun _ => inferInstance
  dDec := fun _ => inferInstance
  dNe := fun l => ⟨⟨0, by positivity⟩⟩
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun l => ⟨⟨0, by positivity⟩⟩

theorem binaryRom_card_R (l : ℕ) :
    letI := binaryRomFamily.rFin l
    Fintype.card (binaryRomFamily.R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp only [Fintype.card_fin]

theorem binaryRom_compressing (l : ℕ) :
    letI := binaryRomFamily.dFin l; letI := binaryRomFamily.rFin l
    Fintype.card (binaryRomFamily.R l) < Fintype.card (binaryRomFamily.D l) := by
  show Fintype.card (Fin (2 ^ l)) < Fintype.card (Fin (2 * 2 ^ l))
  simp only [Fintype.card_fin]
  have : 0 < 2 ^ l := by positivity
  omega

/-- **(TOOTH — the unrestricted floor is FALSE at the deployed shape.)** -/
theorem binaryRom_top_false : ¬ Hard (romCollisionGame binaryRomFamily) (fun _ => True) :=
  romCollision_top_false binaryRomFamily binaryRom_compressing

/-- **⚑⚑⚑ THE FLOOR HOLDS AT THE DEPLOYED SHAPE, FOR ANY POLYNOMIAL BUDGET — PROVED.**

The headline, at a concrete family: a `λ`-bit random oracle on a compressing domain is
collision-resistant against every polynomially-many-query adversary. `binaryRom_top_false` says the
unrestricted floor at this very game is FALSE. Same game, same win relation, two different `Eff`s,
opposite verdicts — which is exactly what it means for `Eff` to be doing real work. -/
theorem binaryRom_hard (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    Hard (romCollisionGame binaryRomFamily) (RomEff binaryRomFamily Q) :=
  romCollision_hard binaryRomFamily Q hQ binaryRom_card_R

/-- **(TOOTH — a concrete polynomial budget.)** `Q l = l` is polynomially bounded, so the floor
holds against an `l`-query adversary at every `l`. The floor is not vacuous on its hypothesis. -/
theorem binaryRom_hard_linear_budget :
    Hard (romCollisionGame binaryRomFamily) (RomEff binaryRomFamily (fun l => l)) := by
  refine binaryRom_hard (fun l => l) ⟨2, 2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-! ## §9 — the CANARY: the floor is not provable from the wrong game.

`HardQuantVacuity` §6's permanent tooth is that a `HashCRHardQuant` proof no longer elaborates in an
`MSISHardQuant` slot. The same tooth applies here, and it must: `romCollisionGame F` is a different
`Game` from `msisGame`/`mlweGame`/`dlGame`/`hashGame`, so `Hard` at it is a different `Prop`. -/

/-- **(CANARY.)** The ROM floor does NOT follow from the unrestricted floor at the same game — the
implication direction that would make this file's content free. `Hard G ⊤ → Hard G (RomEff F Q)` is
TRUE and uninteresting (a smaller class); the canary is that the CONVERSE fails, which is
`romEff_ne_top`. Recorded here as the shape of the tooth: the two floors are not interderivable. -/
theorem romEff_hard_of_top (F : RomFamily) (Q : ℕ → ℕ) (h : Hard (romCollisionGame F) (fun _ => True)) :
    Hard (romCollisionGame F) (RomEff F Q) :=
  fun A _ => h A trivial

/-- **(CANARY — the converse FAILS.)** `Hard G (RomEff F Q) → Hard G ⊤` is FALSE at the deployed
shape: the left side is a theorem (`binaryRom_hard_linear_budget`) and the right side is refuted
(`binaryRom_top_false`). So the query-bounded floor is STRICTLY weaker than the unrestricted one —
which is the whole reason it is provable. -/
theorem binaryRom_romEff_not_implies_top :
    ¬ (Hard (romCollisionGame binaryRomFamily) (RomEff binaryRomFamily (fun l => l)) →
       Hard (romCollisionGame binaryRomFamily) (fun _ => True)) :=
  fun h => binaryRom_top_false (h binaryRom_hard_linear_budget)

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  collWin_query,
  condProb_two_fresh_eq,
  condProb_collide_le,
  birthday_cond,
  birthday_bound,
  romCollisionGame_wins_iff,
  romCollision_always_solvable,
  romCollision_top_false,
  romAdv_hit,
  romAdv_gameAdv_le,
  romCollision_hard,
  choiceAdv_not_romEff,
  romEff_not_iff_solvableFrac_negl,
  romEff_ne_top,
  twoPointComp_bounded,
  twoPointComp_collWin,
  twoPointAdv_in_romEff,
  twoPointAdv_gameAdv_eq,
  twoPointAdv_gameAdv_pos,
  binaryRom_card_R,
  binaryRom_compressing,
  binaryRom_top_false,
  binaryRom_hard,
  binaryRom_hard_linear_budget,
  binaryRom_romEff_not_implies_top
]

end Dregg2.Crypto.RomQueryFloor
