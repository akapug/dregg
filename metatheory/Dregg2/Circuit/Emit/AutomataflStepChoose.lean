/-
# `choose_offset` and the automaton step, at ARBITRARY board size `n` (Leg A, the last lane)

This file closes the back half of Leg A over `automataflStepDescN n`:

* §1 — the `forced_ge0` range gadget at an ARBITRARY bit width `rbits` (the committed
  `AutomataflStepBackend.ge0N_of_sat` is hard-wired to the FIVE-bit unrolling in
  `evalHStep_ge0Bits`; `sgt`/`slt` are `SCORE_RBITS = 20` wide, so the score compare could not be
  reached from it at all).
* §2 — the SCORE order embedding at a distance envelope `≤ 99`, and the CEILING that forces that
  bound: `SCORE_ATT = 100` is a RADIX, so `decScore` stops being an order embedding of
  `decisionCmp` the moment a ray distance reaches `100`.
* §3 — the `oy` head NAMED (`oyHeadN`) so it can be located and evaluated; the `choose_offset`
  gates (`sgt`, `xmove`/`ymove`, the `col` pin, the two offset equalities) at `A_CHOOSE_BASE n`.
* §4 — the per-axis SCORE-FIELD determination `daScoreN`, base-generic, over all nine
  `evaluate_axis` cases (the `n = 2` `xScoreEval`/`yScoreEval` twins).
* §5 — `offset_matches_chooseOffsetN` and `automatonOffset_of_satN`.

Nothing here assumes: every field value is read off the emitted object. The one place a bound is
REQUIRED is stated as an explicit hypothesis (`n ≤ 99`) and its necessity is documented in §2.
-/
import Dregg2.Circuit.Emit.AutomataflStepBackend

namespace Dregg2.Circuit.Emit.AutomataflStepChoose

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflStepCoord
open Dregg2.Circuit.Emit.AutomataflStepBackend
open Dregg2.Circuit.Emit.AutomataflCoord (varsVal termVal sum_map_mul_left)
open Dregg2.Games.Automatafl (Board Coord Particle Dir Decision Raycast evaluateAxis chooseOffset
  decisionCmp tiebreak revCmp)

set_option linter.unusedVariables false

/-! ## §1 — the `forced_ge0` guard at an ARBITRARY range width.

`AutomataflStepBackend.ge0N_of_sat` is column-generic but WIDTH-SPECIFIC: its head lemma
`evalHStep_ge0Bits` unrolls `List.range SMALL_RBITS = [0,1,2,3,4]` by `decide`, and its bit-sum
bound is the five explicit `rcases`. The score compare is 20 bits wide, so it is not an instance.
Everything below is the same content with `rbits` a variable. -/

/-- `bitsFrom` has the length it advertises. -/
theorem bitsFrom_length (s l : Nat) : (bitsFrom s l).length = l := by
  simp [bitsFrom]

/-- A weighted bit-sum over `rbits` boolean columns lies in `[0, 2^rbits − 1]`. Induction on the
width — the `n = 2` chain did this by `rcases` on five explicit bits. -/
theorem bitSum_bounds (a : Nat → ℤ) (bit0 : Nat) : ∀ (R : Nat),
    (∀ k, k < R → a (bit0 + k) = 0 ∨ a (bit0 + k) = 1) →
    0 ≤ ((List.range R).map (fun k => (2 : ℤ) ^ k * a (bit0 + k))).sum
    ∧ ((List.range R).map (fun k => (2 : ℤ) ^ k * a (bit0 + k))).sum ≤ 2 ^ R - 1 := by
  intro R
  induction R with
  | zero => intro _; simp
  | succ R ih =>
      intro hb
      have hprev := ih (fun k hk => hb k (by omega))
      have hlast := hb R (by omega)
      rw [List.range_succ]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      have hpow : (0 : ℤ) < 2 ^ R := by positivity
      have hpow2 : (2 : ℤ) ^ (R + 1) = 2 * 2 ^ R := by ring
      rcases hlast with h | h <;> rw [h] <;> constructor <;> omega

/-- The `range_nonneg` recomposition head over a `forced_ge0` term, at an ARBITRARY width. -/
theorem evalHStep_ge0BitsR (a : Nat → ℤ) (ib bit0 R : Nat) (dh : Head) :
    evalHStep ((List.range R).foldl
        (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) ((bitsFrom bit0 R)[k]!))
        (forcedGe0Term ib dh)) a
      = (2 * a ib * evalHStep dh a + a ib - evalHStep dh a - 1)
        - ((List.range R).map (fun k => (2 : ℤ) ^ k * a (bit0 + k))).sum := by
  rw [evalHStep_foldl_addLinF, evalHStep_forcedGe0Term]
  have hmap : ((List.range R).map
        (fun k => -((2 : ℤ) ^ k) * a ((bitsFrom bit0 R)[k]!)))
      = (List.range R).map (fun k => -((2 : ℤ) ^ k * a (bit0 + k))) := by
    apply List.map_congr_left
    intro k hk
    rw [show (bitsFrom bit0 R)[k]! = bit0 + k from
      getElem!_range_map R (bit0 + ·) (List.mem_range.mp hk)]
    ring
  rw [hmap]
  rw [show ((List.range R).map (fun k => -((2 : ℤ) ^ k * a (bit0 + k))))
        = (List.range R).map (fun k => (-1 : ℤ) * ((2 : ℤ) ^ k * a (bit0 + k))) from by
      apply List.map_congr_left; intro k _; ring]
  rw [sum_map_mul_left]
  ring

/-- **The `forced_ge0` NO-WRAP heart at a `10⁸` window** — wide enough for BOTH a 20-bit range
witness (`2²⁰ − 1 = 1048575`) and a score difference (`|D| ≤ 4·10⁵`), which
`AutomataflStepBackend.forcedGe0_coreW`'s `10⁶` cap is NOT (it is below `2²⁰`). -/
theorem forcedGe0_coreG {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 100000000)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -100000000 ≤ D) (hDhi : D ≤ 100000000) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0 : ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_wide (by omega) (by omega) hmod
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1 : ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_wide (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hc; omega⟩

section Ge0R
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- **`ge0RN_of_sat` — the `forced_ge0` bit IS the comparison, at ARBITRARY columns AND width.**
The width-`5` instance is `AutomataflStepBackend.ge0N_of_sat`; `sgt`/`slt` need width `20`. -/
theorem ge0RN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (ib bit0 R : Nat) (dh : Head) (D : ℤ)
    (hR : (2 : ℤ) ^ R ≤ 100000000)
    (hibG : cg (gBin ib) ∈ d.constraints)
    (hbits : ∀ k, k < R → cg (gBin (bit0 + k)) ∈ d.constraints)
    (hhead : cgH ((List.range R).foldl
        (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) ((bitsFrom bit0 R)[k]!))
        (forcedGe0Term ib dh)) ∈ d.constraints)
    (hD : evalHStep dh (envAt t i).loc = D)
    (hDlo : -100000000 ≤ D) (hDhi : D ≤ 100000000) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
    ∧ ((envAt t i).loc ib = 1 → 0 ≤ D) ∧ ((envAt t i).loc ib = 0 → D ≤ -1) := by
  set e := envAt t i with he
  have hibB : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (sgate hsat i hi hibG) (canon_loc hc i _)
  have hbb : ∀ k, k < R → e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 := by
    intro k hk
    exact bin_of_gate (sgate hsat i hi (hbits k hk)) (canon_loc hc i _)
  obtain ⟨hS0, hS1⟩ := bitSum_bounds e.loc bit0 R hbb
  have hg := sgateH hsat i hi hhead
  rw [← he] at hg
  rw [headToExpr_evalStep, evalHStep_ge0BitsR, hD] at hg
  have hmod : (2 * e.loc ib * D + e.loc ib - D - 1)
      ≡ ((List.range R).map (fun k => (2 : ℤ) ^ k * e.loc (bit0 + k))).sum [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  have core := forcedGe0_coreG (ib := e.loc ib) (D := D) hibB hS0 (by omega) hmod hDlo hDhi
  exact ⟨hibB, core.1, core.2⟩

end Ge0R

/-! ## §2 — the SCORE order embedding, and its CEILING.

`decScore` (`AutomataflStepRefine.decScore`) encodes a `Decision` as
`priority-tier·100000 − 100·att − rep` and the circuit compares those felts. The reference order
`decisionCmp` is `priority` then `revCmp att` then `revCmp rep`. The felt encoding reproduces that
order ONLY while the distance fields stay below the RADIX `SCORE_ATT = 100`:

  att₁ = att₂ + 1, rep₁ = 0, rep₂ = 150  ⇒  100·att₁ + rep₁ = 100·att₂ + 100
                                             100·att₂ + rep₂ = 100·att₂ + 150
  so the felt says d₁ ranks ABOVE d₂, while `revCmp att` says d₁ ranks BELOW it.

Ray distances live in `[1, n]`, so the embedding — and therefore the `sgt`/`slt` score compare, and
therefore `chooseOffset` — is faithful exactly while `n ≤ 99`. This is a REAL CEILING of the emitted
circuit, not of the proof: at `n ≥ 100` the deployed `choose_offset` block can pick the WRONG axis.
The deployed board is `n = 11`; the `n = 2` chain never saw this because its `attRep2` envelope
(`≤ 2`) is below the radix by construction. -/

/-- The distance envelope of a decoded decision at board size `N`: every distance field it carries
is `≤ N`. (`AutomataflStepRefine.attRep2` is the `N = 2` instance.) -/
def attRepB (N : Nat) : Decision → Prop
  | .unbalancedPair _ a r => a ≤ N ∧ r ≤ N
  | .fromRepulsor _ r     => r ≤ N
  | .towardAttractor _ a  => a ≤ N
  | .none                 => True

theorem revCmp_gt_iff (a b : Nat) : revCmp a b = .gt ↔ a < b := by
  unfold revCmp
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [Nat.compare_eq_lt.mpr h]; simp [h]
  · subst h; rw [show compare a a = Ordering.eq from Nat.compare_eq_eq.mpr rfl]; simp
  · rw [Nat.compare_eq_gt.mpr h]; simp; omega

theorem revCmp_eq_iff (a b : Nat) : revCmp a b = .eq ↔ a = b := by
  unfold revCmp
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [Nat.compare_eq_lt.mpr h]; simp; omega
  · subst h; rw [show compare a a = Ordering.eq from Nat.compare_eq_eq.mpr rfl]; simp
  · rw [Nat.compare_eq_gt.mpr h]; simp; omega

theorem then_eq_gt_iff (x y : Ordering) :
    x.then y = .gt ↔ x = .gt ∨ (x = .eq ∧ y = .gt) := by
  cases x <;> simp [Ordering.then]

theorem int_compare_gt_iff (a b : ℤ) : compare a b = .gt ↔ b < a := by
  rw [Int.compare_eq_gt]

/-- **`decisionCmp = .gt` IS the felt score comparison — under the radix envelope `≤ 99`.**
This is the whole content `choose_offset` needs (its `col = true` cascade only distinguishes `.gt`
from `{.lt, .eq}`). The `99` is the `SCORE_ATT = 100` radix; see the section header. -/
theorem decisionCmp_gt_iff_scoreB (d1 d2 : Decision)
    (h1 : attRepB 99 d1) (h2 : attRepB 99 d2) :
    decisionCmp d1 d2 = .gt ↔ decScore d2 < decScore d1 := by
  rcases d1 with ⟨p1, a1, r1⟩ | ⟨p1, r1⟩ | ⟨p1, a1⟩ | _ <;>
    rcases d2 with ⟨p2, a2, r2⟩ | ⟨p2, r2⟩ | ⟨p2, a2⟩ | _ <;>
    simp only [attRepB] at h1 h2 <;>
    simp only [decisionCmp, decScore, Dregg2.Games.Automatafl.Decision.priority, tiebreak,
      then_eq_gt_iff, revCmp_gt_iff, revCmp_eq_iff]
  -- same-tier cases carry the tie-break; cross-tier cases are decided by the `100000` tier gap.
  all_goals (norm_num [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt]
             try push_cast
             try omega)
  -- `omega` does not split a DISJUNCTIVE hypothesis, and the same-tier lexicographic case is
  -- exactly that; split it by hand (the radix `100 > 99 ≥ rep` is what makes each branch linear).
  all_goals first
    | (simp; done)
    | omega
    | (constructor
       · rintro (h | h | ⟨h, h'⟩) <;> first | exact h.elim | omega
       · intro h; omega)

/-- **THE CEILING, EXHIBITED.** At a distance of `150` the felt encoding INVERTS the reference
order: `decisionCmp d₁ d₂ = .lt` (d₁'s attractor distance is larger, so it ranks BELOW d₂) while the
circuit's score comparison reports `decScore d₂ < decScore d₁` — i.e. `sgt` would fire and the
daemon would step along the WRONG axis. `100·att` overflowing into the next `att` digit is the whole
mechanism; it cannot happen while every distance is `≤ 99`. -/
theorem score_embedding_fails_at_150 :
    decisionCmp (.unbalancedPair true 2 0) (.unbalancedPair true 1 150) = .lt
    ∧ decScore (.unbalancedPair true 1 150) < decScore (.unbalancedPair true 2 0) := by
  constructor
  · decide
  · norm_num [decScore]

/-- The boundary is EXACTLY `99`: at `100` the two decisions already collide in the felt encoding
(equal scores) while the reference strictly orders them. -/
theorem score_embedding_collides_at_100 :
    decisionCmp (.unbalancedPair true 2 0) (.unbalancedPair true 1 100) = .lt
    ∧ decScore (.unbalancedPair true 1 100) = decScore (.unbalancedPair true 2 0) := by
  constructor
  · decide
  · norm_num [decScore]

/-! ## §3 — the `choose_offset` gates at `A_CHOOSE_BASE n`.

Column map (all relative to `C = NGen.A_CHOOSE_BASE n`, which is `152` at `n = 2` and `524` at the
deployed `n = 11`): `sgt = C`, `slt = C+21`, `xmove = C+42`, `ymove = C+48`, `col = C+54`,
`ox = C+55`, `oy = C+56`. The decision blocks are at `X = A_DECIDE_X_BASE n` and
`Y = A_DECIDE_Y_BASE n` (`variant`, `pos`, `att`, `rep` at `+0..+3`).

The `oy` equality is a FOUR-FOLD `push_f` in the emitter, so it has no name to locate; `oyHeadN`
gives it one (residual (b) of the back-end lane). -/

/-- `air.rs`'s `push_f` at `n`-parametric columns: `f·<extra>` with `f = 2·ymove·posy − ymove`. -/
def pushFN (n : Nat) (h : Head) (sign : ℤ) (extra : List Nat) : Head :=
  (h.addProd (-sign * 2) ([NGen.A_CHOOSE_BASE n + 48, NGen.A_DECIDE_Y_BASE n + 1] ++ extra)).addProd
    sign ([NGen.A_CHOOSE_BASE n + 48] ++ extra)

/-- **The `oy` equality head, NAMED at arbitrary `n`** — `oy − (2·posy−1)·ymove·ywins == 0`. -/
def oyHeadN (n : Nat) : Head :=
  pushFN n (pushFN n (pushFN n (pushFN n (Head.lin 1 (NGen.A_CHOOSE_BASE n + 56)) 1
    [NGen.A_CHOOSE_BASE n + 21]) 1 [NGen.A_CHOOSE_BASE n + 54]) (-1)
    [NGen.A_CHOOSE_BASE n, NGen.A_CHOOSE_BASE n + 54]) (-1)
    [NGen.A_CHOOSE_BASE n + 21, NGen.A_CHOOSE_BASE n + 54]

/-- **The `ox` equality head, NAMED at arbitrary `n`** — `ox − 2·sgt·xmove·posx + sgt·xmove == 0`. -/
def oxHeadN (n : Nat) : Head :=
  ((Head.lin 1 (NGen.A_CHOOSE_BASE n + 55)).addProd (-2)
      [NGen.A_CHOOSE_BASE n, NGen.A_CHOOSE_BASE n + 42, NGen.A_DECIDE_X_BASE n + 1]).addProd 1
      [NGen.A_CHOOSE_BASE n, NGen.A_CHOOSE_BASE n + 42]

theorem evalHStep_scoreHead (a : Nat → ℤ) (v at_ rp : Nat) :
    evalHStep (scoreHead v at_ rp) a = 100000 * a v - 100 * a at_ - a rp := by
  simp only [scoreHead, evalHStep_addLin, evalHStep_lin, SCORE_PRI, SCORE_ATT]
  ring

theorem varsVal_nil (a : Nat → ℤ) : varsVal a [] = 1 := by simp [varsVal]

theorem evalHStep_pushFN (a : Nat → ℤ) (n : Nat) (h : Head) (sign : ℤ) (extra : List Nat) :
    evalHStep (pushFN n h sign extra) a
      = evalHStep h a
        - sign * (a (NGen.A_CHOOSE_BASE n + 48) * (2 * a (NGen.A_DECIDE_Y_BASE n + 1) - 1))
            * varsVal a extra := by
  simp only [pushFN, evalHStep_addProd, varsVal_cons, varsVal_append, varsVal_nil]
  ring

theorem evalHStep_oyHeadN (a : Nat → ℤ) (n : Nat) :
    evalHStep (oyHeadN n) a
      = a (NGen.A_CHOOSE_BASE n + 56)
        - a (NGen.A_CHOOSE_BASE n + 48) * (2 * a (NGen.A_DECIDE_Y_BASE n + 1) - 1)
          * (a (NGen.A_CHOOSE_BASE n + 21) + a (NGen.A_CHOOSE_BASE n + 54)
             - a (NGen.A_CHOOSE_BASE n) * a (NGen.A_CHOOSE_BASE n + 54)
             - a (NGen.A_CHOOSE_BASE n + 21) * a (NGen.A_CHOOSE_BASE n + 54)) := by
  simp only [oyHeadN, evalHStep_pushFN, evalHStep_lin, varsVal_single, varsVal_pair]
  ring

theorem evalHStep_oxHeadN (a : Nat → ℤ) (n : Nat) :
    evalHStep (oxHeadN n) a
      = a (NGen.A_CHOOSE_BASE n + 55)
        - a (NGen.A_CHOOSE_BASE n) * a (NGen.A_CHOOSE_BASE n + 42)
          * (2 * a (NGen.A_DECIDE_X_BASE n + 1) - 1) := by
  simp only [oxHeadN, evalHStep_addProd, evalHStep_lin, varsVal_pair, varsVal_triple]
  ring

/-! ### §3.1 — segment membership for the pieces the back-end lane did not name. -/

/-- The `slt` score-compare guard block (`sy − sx − 1 ≥ 0`) at `A_CHOOSE_BASE n + 21`. -/
theorem mem_co_slt (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_CHOOSE_BASE n + 21)
          (((scoreHead (NGen.A_DECIDE_Y_BASE n) (NGen.A_DECIDE_Y_BASE n + 2)
                (NGen.A_DECIDE_Y_BASE n + 3)).append
             ((scoreHead (NGen.A_DECIDE_X_BASE n) (NGen.A_DECIDE_X_BASE n + 2)
                (NGen.A_DECIDE_X_BASE n + 3)).scale (-1))).addConst (-1))
          (bitsFrom (NGen.A_CHOOSE_BASE n + 22) SCORE_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

theorem mem_co_oxEq (n : Nat) : cgH (oxHeadN n) ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem mem_co_oyEq (n : Nat) : cgH (oyHeadN n) ∈ (automataflStepDescN n).constraints := by
  apply mem_be_choose; unfold NGen.chooseOffsetConstraints
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

section ChooseGates
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`sgt` = `[sx > sy]`, SOUND at arbitrary `n`, no wrap.** The 20-bit range witness is decoded by
`ge0RN_of_sat` (the committed 5-bit `ge0N_of_sat` cannot reach this block at all), and the `10⁸`
window dwarfs the score magnitudes (`|sx − sy − 1| ≤ 3·10⁵ + 2·10⁴`). -/
theorem sgtN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hxv : (envAt t i).loc (NGen.A_DECIDE_X_BASE n) ≤ 3)
    (hxa : (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2) ≤ 99)
    (hxr : (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3) ≤ 99)
    (hyv : (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) ≤ 3)
    (hya : (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2) ≤ 99)
    (hyr : (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3) ≤ 99) :
    ((envAt t i).loc (NGen.A_CHOOSE_BASE n) = 0 ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n) = 1)
    ∧ ((envAt t i).loc (NGen.A_CHOOSE_BASE n) = 1 →
        100000 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n)
            - 100 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2)
            - (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3)
          < 100000 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n)
            - 100 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2)
            - (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3))
    ∧ ((envAt t i).loc (NGen.A_CHOOSE_BASE n) = 0 →
        100000 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n)
            - 100 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2)
            - (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3)
          ≤ 100000 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n)
            - 100 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2)
            - (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3)) := by
  set e := envAt t i with he
  set C := NGen.A_CHOOSE_BASE n with hC
  set X := NGen.A_DECIDE_X_BASE n with hX
  set Y := NGen.A_DECIDE_Y_BASE n with hY
  have c0 : (0:ℤ) ≤ e.loc X := (canon_loc hc i _).1
  have c1 : (0:ℤ) ≤ e.loc (X + 2) := (canon_loc hc i _).1
  have c2 : (0:ℤ) ≤ e.loc (X + 3) := (canon_loc hc i _).1
  have c3 : (0:ℤ) ≤ e.loc Y := (canon_loc hc i _).1
  have c4 : (0:ℤ) ≤ e.loc (Y + 2) := (canon_loc hc i _).1
  have c5 : (0:ℤ) ≤ e.loc (Y + 3) := (canon_loc hc i _).1
  have hh := mem_ge0_head C (((scoreHead X (X + 2) (X + 3)).append
      ((scoreHead Y (Y + 2) (Y + 3)).scale (-1))).addConst (-1))
      (bitsFrom (C + 1) SCORE_RBITS)
  rw [bitsFrom_length] at hh
  have h := ge0RN_of_sat hsat hc i hi C (C + 1) SCORE_RBITS
    (((scoreHead X (X + 2) (X + 3)).append ((scoreHead Y (Y + 2) (Y + 3)).scale (-1))).addConst (-1))
    ((100000 * e.loc X - 100 * e.loc (X + 2) - e.loc (X + 3))
      - (100000 * e.loc Y - 100 * e.loc (Y + 2) - e.loc (Y + 3)) - 1)
    (by norm_num [SCORE_RBITS])
    (mem_co_sgt n (mem_ge0_ib _ _ _))
    (fun k hk => mem_co_sgt n (mem_ge0_bit _ _ _ (mem_bitsFrom (C + 1) SCORE_RBITS k hk)))
    (mem_co_sgt n hh)
    (by rw [evalHStep_addConst, evalHStep_append, evalHStep_scale, evalHStep_scoreHead,
          evalHStep_scoreHead]; ring)
    (by omega) (by omega)
  exact ⟨h.1, fun hx => by have := h.2.1 hx; omega, fun hx => by have := h.2.2 hx; omega⟩

/-- **`xmove` = `[xvariant ≥ 1]`** — the `x` decision is not `.none`. 5-bit gadget. -/
theorem xmoveN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hxv : (envAt t i).loc (NGen.A_DECIDE_X_BASE n) ≤ 3) :
    (envAt t i).loc (NGen.A_CHOOSE_BASE n + 42)
      = if 1 ≤ (envAt t i).loc (NGen.A_DECIDE_X_BASE n) then 1 else 0 := by
  set e := envAt t i with he
  have c0 : (0:ℤ) ≤ e.loc (NGen.A_DECIDE_X_BASE n) := (canon_loc hc i _).1
  have h := ge0N_of_sat hsat hc i hi (NGen.A_CHOOSE_BASE n + 42) (NGen.A_CHOOSE_BASE n + 43)
    ((Head.lin 1 (NGen.A_DECIDE_X_BASE n)).addConst (-1)) (e.loc (NGen.A_DECIDE_X_BASE n) - 1)
    (mem_co_xmove n (mem_ge0_ib _ _ _))
    (fun k hk => mem_co_xmove n (mem_ge0_bit _ _ _
      (mem_bitsFrom (NGen.A_CHOOSE_BASE n + 43) SMALL_RBITS k hk)))
    (by
      have hh := mem_ge0_head (NGen.A_CHOOSE_BASE n + 42)
        ((Head.lin 1 (NGen.A_DECIDE_X_BASE n)).addConst (-1))
        (bitsFrom (NGen.A_CHOOSE_BASE n + 43) SMALL_RBITS)
      rw [bitsFrom_length] at hh
      exact mem_co_xmove n hh)
    (by rw [evalHStep_addConst, evalHStep_lin]; ring) (by omega) (by omega)
  rcases h.1 with hb | hb <;> rw [hb]
  · rw [if_neg (by have := h.2.2 hb; omega)]
  · rw [if_pos (by have := h.2.1 hb; omega)]

/-- **`ymove` = `[yvariant ≥ 1]`.** -/
theorem ymoveN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hyv : (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) ≤ 3) :
    (envAt t i).loc (NGen.A_CHOOSE_BASE n + 48)
      = if 1 ≤ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) then 1 else 0 := by
  set e := envAt t i with he
  have c0 : (0:ℤ) ≤ e.loc (NGen.A_DECIDE_Y_BASE n) := (canon_loc hc i _).1
  have h := ge0N_of_sat hsat hc i hi (NGen.A_CHOOSE_BASE n + 48) (NGen.A_CHOOSE_BASE n + 49)
    ((Head.lin 1 (NGen.A_DECIDE_Y_BASE n)).addConst (-1)) (e.loc (NGen.A_DECIDE_Y_BASE n) - 1)
    (mem_co_ymove n (mem_ge0_ib _ _ _))
    (fun k hk => mem_co_ymove n (mem_ge0_bit _ _ _
      (mem_bitsFrom (NGen.A_CHOOSE_BASE n + 49) SMALL_RBITS k hk)))
    (by
      have hh := mem_ge0_head (NGen.A_CHOOSE_BASE n + 48)
        ((Head.lin 1 (NGen.A_DECIDE_Y_BASE n)).addConst (-1))
        (bitsFrom (NGen.A_CHOOSE_BASE n + 49) SMALL_RBITS)
      rw [bitsFrom_length] at hh
      exact mem_co_ymove n hh)
    (by rw [evalHStep_addConst, evalHStep_lin]; ring) (by omega) (by omega)
  rcases h.1 with hb | hb <;> rw [hb]
  · rw [if_neg (by have := h.2.2 hb; omega)]
  · rw [if_pos (by have := h.2.1 hb; omega)]

/-- **The column rule is pinned `true`** (`col == col_rule`, `COL_RULE = 1`), at arbitrary `n`. -/
theorem colPinN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_CHOOSE_BASE n + 54) = 1 := by
  have hg := sgateH hsat i hi (mem_co_colRule n)
  rw [headToExpr_evalStep, evalHStep_addConst, evalHStep_lin, COL_RULE] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hg)

/-- **The `ox` offset equality**, at arbitrary `n`. -/
theorem oxN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)
      ≡ (envAt t i).loc (NGen.A_CHOOSE_BASE n) * ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 42)
          * (2 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1) - 1)) [ZMOD 2013265921] := by
  have hg := sgateH hsat i hi (mem_co_oxEq n)
  rw [headToExpr_evalStep, evalHStep_oxHeadN] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- **The `oy` offset equality with the column rule discharged** (`col = 1` collapses the four-fold
`push_f` to `oy = ymove·(2·posy−1)·(1 − sgt)`), at arbitrary `n`. -/
theorem oyN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)
      ≡ (1 - (envAt t i).loc (NGen.A_CHOOSE_BASE n))
          * ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 48)
             * (2 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1) - 1)) [ZMOD 2013265921] := by
  have hcol := colPinN_of_sat hsat hc i hi
  have hg := sgateH hsat i hi (mem_co_oyEq n)
  rw [headToExpr_evalStep, evalHStep_oyHeadN, hcol] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- The two offset columns are cardinal in field terms (`{0, 1, p−1}`), at arbitrary `n`. -/
theorem offsetN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55) = 0
      ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n + 55) = 1
      ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n + 55) = 2013265920)
    ∧ ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56) = 0
      ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n + 56) = 1
      ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n + 56) = 2013265920) :=
  ⟨tri_of_gate (sgate hsat i hi (mem_co_oxMem n)) (canon_loc hc i _),
   tri_of_gate (sgate hsat i hi (mem_co_oyMem n)) (canon_loc hc i _)⟩

end ChooseGates

/-! ## §4 — the SCORE-FIELD determination at an ARBITRARY base (`daScoreN`).

The `n = 2` twins are `AutomataflStepRefine.xScoreEval` / `yScoreEval`; they read 36 gates by
`decide` at frozen numerals. This one runs the same nine cases through
`AutomataflStepBackend.daCaseField_of_sat`, so the base and the distance envelope are variables. -/

/-- `attRepB N` of a decoded decision follows from the raw `att`/`rep` envelope. -/
theorem attRepB_of_env {v pos att rep : ℤ} (ha : att ≤ 99) (hr : rep ≤ 99)
    (ha0 : 0 ≤ att) (hr0 : 0 ≤ rep) : attRepB 99 (decodeDecision v pos att rep) := by
  unfold decodeDecision
  split_ifs <;> simp only [attRepB] <;>
    first
      | trivial
      | omega

section Score
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

set_option maxHeartbeats 4000000 in
/-- **THE SCORE-FIELD DETERMINATION, `∀ n`, at an ARBITRARY base.** On a satisfying canonical trace
the witnessed `(variant, att, rep)` block at `b` satisfies: `variant ≤ 3`, the distance fields are
inside the board envelope `N`, and the felt score head `100000·variant − 100·att − rep` IS `decScore`
of the decoded decision. Every value is forced by an emitted `assert_case` gate. -/
theorem daScoreN (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b pw nw pd nd : Nat) {N : ℤ}
    (hmem : ∀ x, x ∈ decideAxisConstraints b pw nw pd nd → x ∈ d.constraints)
    (hpd1 : 1 ≤ (envAt t i).loc pd) (hpdn : (envAt t i).loc pd ≤ N)
    (hnd1 : 1 ≤ (envAt t i).loc nd) (hndn : (envAt t i).loc nd ≤ N) (hN : N ≤ 99)
    (hpwm : (envAt t i).loc pw = 0 ∨ (envAt t i).loc pw = 1 ∨ (envAt t i).loc pw = 2)
    (hnwm : (envAt t i).loc nw = 0 ∨ (envAt t i).loc nw = 1 ∨ (envAt t i).loc nw = 2) :
    (envAt t i).loc b ≤ 3 ∧ (envAt t i).loc (b + 2) ≤ 99 ∧ (envAt t i).loc (b + 3) ≤ 99
    ∧ attRepB 99 (decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1))
        ((envAt t i).loc (b + 2)) ((envAt t i).loc (b + 3)))
    ∧ 100000 * (envAt t i).loc b - 100 * (envAt t i).loc (b + 2) - (envAt t i).loc (b + 3)
        = decScore (decodeDecision ((envAt t i).loc b) ((envAt t i).loc (b + 1))
            ((envAt t i).loc (b + 2)) ((envAt t i).loc (b + 3))) := by
  have hN6 : N ≤ 1000000 := by omega
  have hv : (envAt t i).loc b = 0 ∨ (envAt t i).loc b = 1 ∨ (envAt t i).loc b = 2 ∨ (envAt t i).loc b = 3 :=
    mem4_of_gate (sgate hsat i hi (hmem _ (mem_da_variant b pw nw pd nd))) (canon_loc hc i _)
  have ca : (0:ℤ) ≤ (envAt t i).loc (b + 2) := (canon_loc hc i _).1
  have cr : (0:ℤ) ≤ (envAt t i).loc (b + 3) := (canon_loc hc i _).1
  obtain ⟨i0, i1, i2, isum, iidx⟩ := da_ipw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨n0, n1, n2, nsum, nidx⟩ := da_inw_sel hsat hc i hi b pw nw pd nd hmem
  obtain ⟨gpdB, gpd1, gpd0⟩ := da_gpd_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hN6
  obtain ⟨gndB, gnd1, gnd0⟩ := da_gnd_sound hsat hc i hi b pw nw pd nd hmem hnd1 hndn hN6
  obtain ⟨ltB, lt1, lt0⟩ := da_lt_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN6
  obtain ⟨gtB, gt1, gt0⟩ := da_gt_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN6
  obtain ⟨leB, le1, le0⟩ := da_le_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN6
  obtain ⟨gmB, gm1, gm0⟩ := da_gm_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN6
  have hmin := da_min_sound hsat hc i hi b pw nw pd nd hmem hpd1 hpdn hnd1 hndn hN6
  have hminlo : 1 ≤ (envAt t i).loc (b + 40) := by rw [hmin]; rcases leB with h | h <;> rw [h] <;> omega
  have hminhi : (envAt t i).loc (b + 40) ≤ N := by
    rw [hmin]; rcases leB with h | h <;> rw [h] <;> omega
  -- table-entry locators
  have T21 : ((2, 1), [Head.lin 3 (b + 10), Head.lin 1 (b + 10), Head.zero.addProd 1 [b + 10, pd],
        Head.zero.addProd 1 [b + 10, nd]])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_self
  have T12 : ((1, 2), [Head.lin 3 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd],
        Head.zero.addProd 1 [b + 16, pd]])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have T11 : ((1, 1), [(Head.lin 2 (b + 22)).addLin 2 (b + 28), Head.lin 1 (b + 28), Head.zero,
        (Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40]])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have T10 : ((1, 0), [Head.lin 2 (b + 16), Head.zero, Head.zero,
        Head.zero.addProd 1 [b + 16, pd]])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have T01 : ((0, 1), [Head.lin 2 (b + 10), Head.lin 1 (b + 10), Head.zero,
        Head.zero.addProd 1 [b + 10, nd]])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have T22 : ((2, 2), [(Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41],
        Head.zero.addProd 1 [b + 22, b + 41],
        (Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40],
        Head.zero])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have T20 : ((2, 0), [Head.lin 1 (b + 10), Head.lin 1 (b + 10),
        Head.zero.addProd 1 [b + 10, pd], Head.zero])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))
  have T02 : ((0, 2), [Head.lin 1 (b + 16), Head.zero, Head.zero.addProd 1 [b + 16, nd],
        Head.zero])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))))
  have T00 : ((0, 0), [Head.zero, Head.zero, Head.zero, Head.zero])
      ∈ casesTable pd nd (b + 40) (b + 10) (b + 16) (b + 22) (b + 28) (b + 41) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
  rcases hpwm with hp | hp | hp <;> rcases hnwm with hn | hn | hn <;>
    rw [hp] at iidx <;> rw [hn] at nidx
  · -- (vac, vac): every field pinned to zero.
    have hip : (envAt t i).loc (b + 4) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 7) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) b
      Head.zero (mem_decideCases T00 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) (b + 2)
      Head.zero (mem_decideCases T00 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 7) (b + 3)
      Head.zero (mem_decideCases T00 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    rw [evalHStep_zero] at hvar hatt hrep
    exact ⟨by omega, by omega, by omega,
      attRepB_of_env (by omega) (by omega) ca cr,
      decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (vac, rep): variant = 2·gpd, att = 0, rep = gpd·nd.
    have hip : (envAt t i).loc (b + 4) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 8) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) b
      (Head.lin 2 (b + 10)) (mem_decideCases T01 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) (b + 2)
      Head.zero (mem_decideCases T01 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 8) (b + 3)
      (Head.zero.addProd 1 [b + 10, nd]) (mem_decideCases T01 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    rw [evalHStep_lin] at hvar
    rw [evalHStep_zero] at hatt
    rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hrep
    rcases gpdB with hg | hg <;> rw [hg] at hvar hrep <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (vac, att): variant = gnd, att = gnd·nd, rep = 0.
    have hip : (envAt t i).loc (b + 4) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 9) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) b
      (Head.lin 1 (b + 16)) (mem_decideCases T02 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) (b + 2)
      (Head.zero.addProd 1 [b + 16, nd]) (mem_decideCases T02 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 4) (b + 9) (b + 3)
      Head.zero (mem_decideCases T02 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    rw [evalHStep_lin] at hvar
    rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt
    rw [evalHStep_zero] at hrep
    rcases gndB with hg | hg <;> rw [hg] at hvar hatt <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (rep, vac): variant = 2·gnd, att = 0, rep = gnd·pd.
    have hip : (envAt t i).loc (b + 5) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 7) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) b
      (Head.lin 2 (b + 16)) (mem_decideCases T10 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) (b + 2)
      Head.zero (mem_decideCases T10 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 7) (b + 3)
      (Head.zero.addProd 1 [b + 16, pd]) (mem_decideCases T10 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    rw [evalHStep_lin] at hvar
    rw [evalHStep_zero] at hatt
    rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hrep
    rcases gndB with hg | hg <;> rw [hg] at hvar hrep <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (rep, rep): variant = 2·lt + 2·gt, att = 0, rep = (lt + gt)·min.
    have hip : (envAt t i).loc (b + 5) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 8) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) b
      ((Head.lin 2 (b + 22)).addLin 2 (b + 28)) (mem_decideCases T11 (k := 0) (by decide)) rfl
      hip hin
      (by rw [evalHStep_addLin, evalHStep_lin]; rcases ltB with h|h <;> rcases gtB with h'|h' <;>
        rw [h, h'] <;> exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) (b + 2)
      Head.zero (mem_decideCases T11 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 8) (b + 3)
      ((Head.zero.addProd 1 [b + 22, b + 40]).addProd 1 [b + 28, b + 40])
      (mem_decideCases T11 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h, h'] <;>
            exact canon_of_bounds (by omega) (by omega))
    rw [evalHStep_addLin, evalHStep_lin] at hvar
    rw [evalHStep_zero] at hatt
    rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair] at hrep
    rcases ltB with hl | hl <;> rcases gtB with hg2 | hg2 <;> rw [hl, hg2] at hvar hrep <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (rep, att): variant = 3·gnd, att = gnd·nd, rep = gnd·pd.
    have hip : (envAt t i).loc (b + 5) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 9) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) b
      (Head.lin 3 (b + 16)) (mem_decideCases T12 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) (b + 2)
      (Head.zero.addProd 1 [b + 16, nd]) (mem_decideCases T12 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 5) (b + 9) (b + 3)
      (Head.zero.addProd 1 [b + 16, pd]) (mem_decideCases T12 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gndB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    rw [evalHStep_lin] at hvar
    rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt hrep
    rcases gndB with hg | hg <;> rw [hg] at hvar hatt hrep <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (att, vac): variant = gpd, att = gpd·pd, rep = 0.
    have hip : (envAt t i).loc (b + 6) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 7) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) b
      (Head.lin 1 (b + 10)) (mem_decideCases T20 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) (b + 2)
      (Head.zero.addProd 1 [b + 10, pd]) (mem_decideCases T20 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 7) (b + 3)
      Head.zero (mem_decideCases T20 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    rw [evalHStep_lin] at hvar
    rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt
    rw [evalHStep_zero] at hrep
    rcases gpdB with hg | hg <;> rw [hg] at hvar hatt <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (att, rep): variant = 3·gpd, att = gpd·pd, rep = gpd·nd.
    have hip : (envAt t i).loc (b + 6) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 8) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) b
      (Head.lin 3 (b + 10)) (mem_decideCases T21 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_lin]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) (b + 2)
      (Head.zero.addProd 1 [b + 10, pd]) (mem_decideCases T21 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 8) (b + 3)
      (Head.zero.addProd 1 [b + 10, nd]) (mem_decideCases T21 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_zero, varsVal_pair]; rcases gpdB with h|h <;> rw [h] <;>
        exact canon_of_bounds (by omega) (by omega))
    rw [evalHStep_lin] at hvar
    rw [evalHStep_addProd, evalHStep_zero, varsVal_pair] at hatt hrep
    rcases gpdB with hg | hg <;> rw [hg] at hvar hatt hrep <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩
  · -- (att, att): variant = (lt + gt)·gm, att = (lt + gt)·gm·min, rep = 0.
    have hip : (envAt t i).loc (b + 6) = 1 := by rcases i1 with h|h <;> rcases i2 with h'|h' <;> omega
    have hin : (envAt t i).loc (b + 9) = 1 := by rcases n1 with h|h <;> rcases n2 with h'|h' <;> omega
    have hvar := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) b
      ((Head.zero.addProd 1 [b + 22, b + 41]).addProd 1 [b + 28, b + 41])
      (mem_decideCases T22 (k := 0) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with h''|h'' <;>
            rw [h, h', h''] <;> exact canon_of_bounds (by norm_num) (by norm_num))
    have hatt := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) (b + 2)
      ((Head.zero.addProd 1 [b + 22, b + 41, b + 40]).addProd 1 [b + 28, b + 41, b + 40])
      (mem_decideCases T22 (k := 2) (by decide)) rfl hip hin
      (by rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_triple, varsVal_triple]
          rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with h''|h'' <;>
            rw [h, h', h''] <;> exact canon_of_bounds (by omega) (by omega))
    have hrep := daCaseField_of_sat hsat hc i hi b pw nw pd nd hmem (b + 6) (b + 9) (b + 3)
      Head.zero (mem_decideCases T22 (k := 3) (by decide)) rfl hip hin
      (by rw [evalHStep_zero]; exact canon_zero)
    rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_pair, varsVal_pair] at hvar
    rw [evalHStep_addProd, evalHStep_addProd, evalHStep_zero, varsVal_triple, varsVal_triple] at hatt
    rw [evalHStep_zero] at hrep
    rcases ltB with hl | hl <;> rcases gtB with hg2 | hg2 <;> rcases gmB with hgm | hgm <;>
      rw [hl, hg2, hgm] at hvar hatt <;>
      exact ⟨by omega, by omega, by omega,
        attRepB_of_env (by omega) (by omega) ca cr,
        decScore_of_fields hv ca cr (by omega) (by omega) (by omega)⟩

end Score

/-! ## §5 — `chooseOffset` and `automatonOffset` at arbitrary `n`.

`n ≤ 99` is carried EXPLICITLY (see §2 — it is the emitted circuit's radix ceiling, not a proof
convenience). The deployed board is `n = 11`. -/

section Offset
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepCapstone (rayN_of_sat boardDecodeN raycast_xp_of_satN
  raycast_xn_of_satN raycast_yp_of_satN raycast_yn_of_satN)

/-- The `xdec` score block at arbitrary `n`: `variant ≤ 3`, distances inside the board, and the felt
score head IS `decScore` of the decoded X decision. -/
theorem daScoreX_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921) (hn99 : (n : ℤ) ≤ 99)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_DECIDE_X_BASE n) ≤ 3
    ∧ (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2) ≤ 99
    ∧ (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3) ≤ 99
    ∧ attRepB 99 (decodeDecision ((envAt t i).loc (NGen.A_DECIDE_X_BASE n))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2))
        ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3)))
    ∧ 100000 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n)
        - 100 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2)
        - (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3)
      = decScore (decodeDecision ((envAt t i).loc (NGen.A_DECIDE_X_BASE n))
          ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1))
          ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2))
          ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3))) := by
  obtain ⟨K0, hK0a, hK0b, hd0, _⟩ :=
    rayN_of_sat (t := t) n 0 1 0 hn (fun x hx => mem_fe_ray0 hx) hsat hc i hi
  obtain ⟨K1, hK1a, hK1b, hd1, _⟩ :=
    rayN_of_sat (t := t) n 1 (-1) 0 hn (fun x hx => mem_fe_ray1 hx) hsat hc i hi
  exact daScoreN hsat hc i hi (NGen.A_DECIDE_X_BASE n) (NGen.rWhat n 0) (NGen.rWhat n 1)
    (NGen.rDist n 0) (NGen.rDist n 1) (N := (n : ℤ)) (fun x hx => mem_be_decideX hx)
    (by rw [hd0]; exact_mod_cast hK0a) (by rw [hd0]; exact_mod_cast hK0b)
    (by rw [hd1]; exact_mod_cast hK1a) (by rw [hd1]; exact_mod_cast hK1b) hn99
    (mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 0) [0, 1, 2])
      (mem_fe_ray0 ray_whatMem_mem)) (canon_loc hc i _))
    (mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 1) [0, 1, 2])
      (mem_fe_ray1 ray_whatMem_mem)) (canon_loc hc i _))

/-- The `ydec` score block at arbitrary `n`. -/
theorem daScoreY_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921) (hn99 : (n : ℤ) ≤ 99)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) ≤ 3
    ∧ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2) ≤ 99
    ∧ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3) ≤ 99
    ∧ attRepB 99 (decodeDecision ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2))
        ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3)))
    ∧ 100000 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n)
        - 100 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2)
        - (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3)
      = decScore (decodeDecision ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n))
          ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1))
          ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2))
          ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3))) := by
  obtain ⟨K2, hK2a, hK2b, hd2, _⟩ :=
    rayN_of_sat (t := t) n 2 0 1 hn (fun x hx => mem_fe_ray2 hx) hsat hc i hi
  obtain ⟨K3, hK3a, hK3b, hd3, _⟩ :=
    rayN_of_sat (t := t) n 3 0 (-1) hn (fun x hx => mem_fe_ray3 hx) hsat hc i hi
  exact daScoreN hsat hc i hi (NGen.A_DECIDE_Y_BASE n) (NGen.rWhat n 2) (NGen.rWhat n 3)
    (NGen.rDist n 2) (NGen.rDist n 3) (N := (n : ℤ)) (fun x hx => mem_be_decideY hx)
    (by rw [hd2]; exact_mod_cast hK2a) (by rw [hd2]; exact_mod_cast hK2b)
    (by rw [hd3]; exact_mod_cast hK3a) (by rw [hd3]; exact_mod_cast hK3b) hn99
    (mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 2) [0, 1, 2])
      (mem_fe_ray2 ray_whatMem_mem)) (canon_loc hc i _))
    (mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 3) [0, 1, 2])
      (mem_fe_ray3 ray_whatMem_mem)) (canon_loc hc i _))

set_option maxHeartbeats 1000000 in
/-- **LEG (4), `∀ n ≤ 99`: the decoded offset IS `chooseOffset`.** The witnessed `(ox, oy)` at
`A_CHOOSE_BASE n + 55/56` equals the reference cross-axis tie-break of the two decoded axis
decisions under the column rule `true`. UNCONDITIONAL — the score-field determination is discharged
by `daScoreX_of_sat`/`daScoreY_of_sat`, not assumed. -/
theorem offset_matches_chooseOffsetN (n : Nat) (hn : (n : ℤ) < 2013265921) (hn99 : (n : ℤ) ≤ 99)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
     decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)))
      = chooseOffset
          (decodeDecision ((envAt t i).loc (NGen.A_DECIDE_X_BASE n))
            ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1))
            ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2))
            ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3)))
          (decodeDecision ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n))
            ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1))
            ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2))
            ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3)))
          true := by
  obtain ⟨hxv, hxa, hxr, hxe, hsx⟩ := daScoreX_of_sat n hn hn99 hsat hc i hi
  obtain ⟨hyv, hya, hyr, hye, hsy⟩ := daScoreY_of_sat n hn hn99 hsat hc i hi
  set dx := decodeDecision ((envAt t i).loc (NGen.A_DECIDE_X_BASE n))
    ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1)) ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 2))
    ((envAt t i).loc (NGen.A_DECIDE_X_BASE n + 3)) with hdx
  set dy := decodeDecision ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n))
    ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1)) ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 2))
    ((envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 3)) with hdy
  -- field alphabets
  have h58 : (envAt t i).loc (NGen.A_DECIDE_X_BASE n) = 0
      ∨ (envAt t i).loc (NGen.A_DECIDE_X_BASE n) = 1
      ∨ (envAt t i).loc (NGen.A_DECIDE_X_BASE n) = 2
      ∨ (envAt t i).loc (NGen.A_DECIDE_X_BASE n) = 3 :=
    mem4_of_gate (sgate hsat i hi (mem_be_decideX
      (mem_da_variant (NGen.A_DECIDE_X_BASE n) (NGen.rWhat n 0) (NGen.rWhat n 1)
        (NGen.rDist n 0) (NGen.rDist n 1)))) (canon_loc hc i _)
  have h105 : (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) = 0
      ∨ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) = 1
      ∨ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) = 2
      ∨ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n) = 3 :=
    mem4_of_gate (sgate hsat i hi (mem_be_decideY
      (mem_da_variant (NGen.A_DECIDE_Y_BASE n) (NGen.rWhat n 2) (NGen.rWhat n 3)
        (NGen.rDist n 2) (NGen.rDist n 3)))) (canon_loc hc i _)
  have hp59 : (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1) = 0
      ∨ (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1) = 1 :=
    bin_of_gate (sgate hsat i hi (mem_be_decideX
      (mem_da_posBin (NGen.A_DECIDE_X_BASE n) (NGen.rWhat n 0) (NGen.rWhat n 1)
        (NGen.rDist n 0) (NGen.rDist n 1)))) (canon_loc hc i _)
  have hp106 : (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1) = 0
      ∨ (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1) = 1 :=
    bin_of_gate (sgate hsat i hi (mem_be_decideY
      (mem_da_posBin (NGen.A_DECIDE_Y_BASE n) (NGen.rWhat n 2) (NGen.rWhat n 3)
        (NGen.rDist n 2) (NGen.rDist n 3)))) (canon_loc hc i _)
  have hsgt := sgtN_of_sat hsat hc i hi hxv hxa hxr hyv hya hyr
  have hsgtb := hsgt.1
  have hxm := xmoveN_of_sat hsat hc i hi hxv
  have hym := ymoveN_of_sat hsat hc i hi hyv
  have hxmb : (envAt t i).loc (NGen.A_CHOOSE_BASE n + 42) = 0
      ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n + 42) = 1 := by rw [hxm]; split_ifs <;> simp
  have hymb : (envAt t i).loc (NGen.A_CHOOSE_BASE n + 48) = 0
      ∨ (envAt t i).loc (NGen.A_CHOOSE_BASE n + 48) = 1 := by rw [hym]; split_ifs <;> simp
  have hoxtri := (offsetN_of_sat hsat hc i hi).1
  have hoytri := (offsetN_of_sat hsat hc i hi).2
  have hoxv : decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))
      = (envAt t i).loc (NGen.A_CHOOSE_BASE n)
        * ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 42)
           * (2 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1) - 1)) := by
    refine decodeOff_eq_of hoxtri ?_ (oxN_of_sat hsat hc i hi)
    rcases hsgtb with h|h <;> rcases hxmb with h2|h2 <;> rcases hp59 with h3|h3 <;>
      rw [h, h2, h3] <;> norm_num
  have hoyv : decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))
      = (1 - (envAt t i).loc (NGen.A_CHOOSE_BASE n))
        * ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 48)
           * (2 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1) - 1)) := by
    refine decodeOff_eq_of hoytri ?_ (oyN_of_sat hsat hc i hi)
    rcases hsgtb with h|h <;> rcases hymb with h2|h2 <;> rcases hp106 with h3|h3 <;>
      rw [h, h2, h3] <;> norm_num
  have hdeltax : (dx.delta (1, 0)).1
      = (envAt t i).loc (NGen.A_CHOOSE_BASE n + 42)
        * (2 * (envAt t i).loc (NGen.A_DECIDE_X_BASE n + 1) - 1) := by
    rw [hdx, decodeDecision_delta_x_fst _ _ _ _ h58 hp59, hxm]
  have hdeltay : (dy.delta (0, 1)).2
      = (envAt t i).loc (NGen.A_CHOOSE_BASE n + 48)
        * (2 * (envAt t i).loc (NGen.A_DECIDE_Y_BASE n + 1) - 1) := by
    rw [hdy, decodeDecision_delta_y_snd _ _ _ _ h105 hp106, hym]
  have hcmpiff := decisionCmp_gt_iff_scoreB dx dy hxe hye
  rw [← hsx, ← hsy] at hcmpiff
  rcases Dregg2.Games.Automatafl.decisionCmp_total dx dy with hcmp|hcmp|hcmp
  · have hsgt0 : (envAt t i).loc (NGen.A_CHOOSE_BASE n) = 0 := by
      rcases hsgtb with h|h
      · exact h
      · have := hcmpiff.mpr (hsgt.2.1 h); rw [hcmp] at this; exact absurd this (by decide)
    have hchoose : chooseOffset dx dy true = dy.delta (0, 1) := by simp only [chooseOffset, hcmp]
    rw [hchoose]
    apply Prod.ext
    · rw [hoxv, hsgt0, decodeDecision_delta_y_fst]; ring
    · rw [hoyv, hsgt0, hdeltay]; ring
  · have hsgt0 : (envAt t i).loc (NGen.A_CHOOSE_BASE n) = 0 := by
      rcases hsgtb with h|h
      · exact h
      · have := hcmpiff.mpr (hsgt.2.1 h); rw [hcmp] at this; exact absurd this (by decide)
    have hchoose : chooseOffset dx dy true = dy.delta (0, 1) := by simp only [chooseOffset, hcmp]
    rw [hchoose]
    apply Prod.ext
    · rw [hoxv, hsgt0, decodeDecision_delta_y_fst]; ring
    · rw [hoyv, hsgt0, hdeltay]; ring
  · have hsgt1 : (envAt t i).loc (NGen.A_CHOOSE_BASE n) = 1 := by
      rcases hsgtb with h|h
      · have h1 := hsgt.2.2 h; have h2 := hcmpiff.mp hcmp; omega
      · exact h
    have hchoose : chooseOffset dx dy true = dx.delta (1, 0) := by simp only [chooseOffset, hcmp]
    rw [hchoose]
    apply Prod.ext
    · rw [hoxv, hsgt1, hdeltax]; ring
    · rw [hoyv, hsgt1, decodeDecision_delta_x_snd]; ring

/-- **LEGS (1)–(4) COMPOSED, `∀ n ≤ 99`: the offset columns ARE `automatonOffset` of the decoded
board.** Rays ▸ per-axis decision ▸ score compare ▸ offset. Every step is forced by the emitted
`automataflStepDescN n` gates. -/
theorem automatonOffset_of_satN (n : Nat) (hn : (n : ℤ) < 2013265921) (hn99 : (n : ℤ) ≤ 99)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Dregg2.Games.Automatafl.automatonOffset (boardDecodeN n (envAt t i))
      = (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
         decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))) := by
  have hxp := raycast_xp_of_satN (t := t) n hn hsat hc i hi
  have hxn := raycast_xn_of_satN (t := t) n hn hsat hc i hi
  have hyp := raycast_yp_of_satN (t := t) n hn hsat hc i hi
  have hyn := raycast_yn_of_satN (t := t) n hn hsat hc i hi
  have hx := decideAxis_x_soundN n hn (by omega) hsat hc i hi
  have hy := decideAxis_y_soundN n hn (by omega) hsat hc i hi
  have hoff := offset_matches_chooseOffsetN n hn hn99 hsat hc i hi
  unfold Dregg2.Games.Automatafl.automatonOffset
  rw [show (boardDecodeN n (envAt t i)).useColumnRule = true from rfl, hxp, hxn, hyp, hyn,
    ← hx, ← hy]
  exact hoff.symm

/-- Non-vacuity at the DEPLOYED board size. -/
theorem automatonOffset_of_sat_n11
    (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Dregg2.Games.Automatafl.automatonOffset (boardDecodeN 11 (envAt t i))
      = (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE 11 + 55)),
         decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE 11 + 56))) :=
  automatonOffset_of_satN 11 (by norm_num) (by norm_num) hsat hc i hi

/-- Non-vacuity at `n = 3` — the first size at which the frozen `n = 2` numerals are wrong. -/
theorem automatonOffset_of_sat_n3
    (hsat : Satisfied2 hash (automataflStepDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Dregg2.Games.Automatafl.automatonOffset (boardDecodeN 3 (envAt t i))
      = (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE 3 + 55)),
         decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE 3 + 56))) :=
  automatonOffset_of_satN 3 (by norm_num) (by norm_num) hsat hc i hi

end Offset

/-! ## §6 — FOUNDATION FOR LEG (5) at arbitrary `n` (the step + board update).

The step block's SEGMENT MEMBERSHIP (the `n = 2` chain locates every one of these by `decide` over
the concrete 418-constraint list), the MOD-AWARE range gadget the edge guards need (the offset felt
`p − 1 ≡ −1` makes `ax + ox` a LARGE field value congruent to a small signed one), and the two
consequences that need nothing `n`-wide: the decoded offset is a cardinal step, and `offnz` is its
squared length. What is NOT here — the `n`-wide row×column target read and the board-update fold —
is the named residual (see the file header). -/

/-- `[offnz = ox² + oy²]` gate, at `A_STEP_BASE n + 33 + 2n`. -/
theorem mem_st_offnz (n : Nat) :
    cgH (((Head.lin 1 (NGen.A_STEP_BASE n + 33 + 2 * n)).addProd (-1)
        [NGen.A_CHOOSE_BASE n + 55, NGen.A_CHOOSE_BASE n + 55]).addProd (-1)
        [NGen.A_CHOOSE_BASE n + 56, NGen.A_CHOOSE_BASE n + 56])
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- `[targ_vac = 1 − nz]` gate, at `A_STEP_BASE n + 32 + 2n`. -/
theorem mem_st_targVac (n : Nat) :
    cgH (((Head.lin 1 (NGen.A_STEP_BASE n + 32 + 2 * n)).addLin 1
        (NGen.A_STEP_BASE n + 26 + 2 * n)).addConst (-1))
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- `[m = offnz·tib·targ_vac]` — the MOVE mask, at `A_STEP_BASE n + 34 + 2n`. -/
theorem mem_st_moved (n : Nat) :
    cgH ((Head.lin 1 (NGen.A_STEP_BASE n + 34 + 2 * n)).addProd (-1)
        [NGen.A_STEP_BASE n + 33 + 2 * n, NGen.A_STEP_BASE n + 24,
         NGen.A_STEP_BASE n + 32 + 2 * n])
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- `[tib = ∏ edge bits]` — the target-in-bounds product, at `A_STEP_BASE n + 24`. -/
theorem mem_st_tib (n : Nat) :
    cgH ((Head.lin 1 (NGen.A_STEP_BASE n + 24)).addProd (-1)
        [NGen.A_STEP_BASE n, NGen.A_STEP_BASE n + 6, NGen.A_STEP_BASE n + 12,
         NGen.A_STEP_BASE n + 18])
      ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The `[tx ≥ 0]` edge guard block, at `A_STEP_BASE n`. -/
theorem mem_st_txlo (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_STEP_BASE n)
          ((Head.lin 1 (NGen.AX n)).addLin 1 (NGen.A_CHOOSE_BASE n + 55))
          (bitsFrom (NGen.A_STEP_BASE n + 1) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact h

/-- The `[ty ≥ 0]` edge guard block, at `A_STEP_BASE n + 12`. -/
theorem mem_st_tylo (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_STEP_BASE n + 12)
          ((Head.lin 1 (NGen.AY n)).addLin 1 (NGen.A_CHOOSE_BASE n + 56))
          (bitsFrom (NGen.A_STEP_BASE n + 13) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The `[tx ≤ n−1]` edge guard block, at `A_STEP_BASE n + 6`. -/
theorem mem_st_txhi (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_STEP_BASE n + 6)
          (((Head.c ((n : ℤ) - 1)).addLin (-1) (NGen.AX n)).addLin (-1)
            (NGen.A_CHOOSE_BASE n + 55))
          (bitsFrom (NGen.A_STEP_BASE n + 7) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The `[ty ≤ n−1]` edge guard block, at `A_STEP_BASE n + 18`. -/
theorem mem_st_tyhi (n : Nat) {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_STEP_BASE n + 18)
          (((Head.c ((n : ℤ) - 1)).addLin (-1) (NGen.AY n)).addLin (-1)
            (NGen.A_CHOOSE_BASE n + 56))
          (bitsFrom (NGen.A_STEP_BASE n + 19) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

/-- **The MOD-AWARE `forced_ge0` heart at a `10⁸` window and ARBITRARY width.** The compared field
value `D` may be large; the bit decides `[D' ≥ 0]` for the SMALL residue `D' ≡ D`. This is what the
step's edge guards need (`ax + ox` with `ox = p − 1 ≡ −1`), at any `n`. -/
theorem forcedGe0_coreGMod {ib D D' S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 100000000)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDD' : D ≡ D' [ZMOD 2013265921]) (hlo : -100000000 ≤ D') (hhi : D' ≤ 100000000) :
    (ib = 1 → 0 ≤ D') ∧ (ib = 0 → D' ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0 : ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have hcong : (-D - 1) ≡ (-D' - 1) [ZMOD 2013265921] := (hDD'.neg).sub_right 1
    have heq : -D' - 1 = S := eq_of_modEq_wide (by omega) (by omega) (hcong.symm.trans hmod)
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1 : ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D' = S := eq_of_modEq_wide (by omega) (by omega) (hDD'.symm.trans hmod)
    exact ⟨by intro _; omega, by intro hc; omega⟩

section Leg5Found
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- **`ge0RN_mod_of_sat`** — `ge0RN_of_sat` with the compared head read MODULO `p`. Descriptor- and
column-generic, arbitrary range width. -/
theorem ge0RN_mod_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (ib bit0 R : Nat) (dh : Head) (D D' : ℤ)
    (hR : (2 : ℤ) ^ R ≤ 100000000)
    (hibG : cg (gBin ib) ∈ d.constraints)
    (hbits : ∀ k, k < R → cg (gBin (bit0 + k)) ∈ d.constraints)
    (hhead : cgH ((List.range R).foldl
        (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) ((bitsFrom bit0 R)[k]!))
        (forcedGe0Term ib dh)) ∈ d.constraints)
    (hD : evalHStep dh (envAt t i).loc = D)
    (hDD' : D ≡ D' [ZMOD 2013265921])
    (hDlo : -100000000 ≤ D') (hDhi : D' ≤ 100000000) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
    ∧ ((envAt t i).loc ib = 1 → 0 ≤ D') ∧ ((envAt t i).loc ib = 0 → D' ≤ -1) := by
  have hibB : (envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1 :=
    bin_of_gate (sgate hsat i hi hibG) (canon_loc hc i _)
  have hbb : ∀ k, k < R → (envAt t i).loc (bit0 + k) = 0 ∨ (envAt t i).loc (bit0 + k) = 1 := by
    intro k hk
    exact bin_of_gate (sgate hsat i hi (hbits k hk)) (canon_loc hc i _)
  obtain ⟨hS0, hS1⟩ := bitSum_bounds (envAt t i).loc bit0 R hbb
  have hg := sgateH hsat i hi hhead
  rw [headToExpr_evalStep, evalHStep_ge0BitsR, hD] at hg
  have hmod : (2 * (envAt t i).loc ib * D + (envAt t i).loc ib - D - 1)
      ≡ ((List.range R).map (fun k => (2 : ℤ) ^ k * (envAt t i).loc (bit0 + k))).sum
        [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
  have core := forcedGe0_coreGMod (ib := (envAt t i).loc ib) (D := D) (D' := D') hibB hS0
    (by omega) hmod hDD' hDlo hDhi
  exact ⟨hibB, core.1, core.2⟩

/-- **The decoded offset is one of the five cardinal steps, `∀ n ≤ 99`** — leg (4) composed with the
reference `automatonOffset_cases`. -/
theorem offCardN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921) (hn99 : (n : ℤ) ≤ 99)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
     decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))) = ((1:ℤ), (0:ℤ))
    ∨ (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
       decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))) = ((-1:ℤ), (0:ℤ))
    ∨ (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
       decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))) = ((0:ℤ), (1:ℤ))
    ∨ (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
       decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))) = ((0:ℤ), (-1:ℤ))
    ∨ (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)),
       decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))) = ((0:ℤ), (0:ℤ)) := by
  have hcases := Dregg2.Games.Automatafl.automatonOffset_cases
    (Dregg2.Circuit.Emit.AutomataflStepCapstone.boardDecodeN n (envAt t i))
  rw [automatonOffset_of_satN n hn hn99 hsat hc i hi] at hcases
  exact hcases

/-- **`offnz = ox² + oy²` at arbitrary `n`** — the move-nonzero column IS the squared length of the
decoded offset (so `0` on a freeze and `1` on a genuine cardinal step). -/
theorem offnzN_of_sat {n : Nat} (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n)
      = decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))
          * decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))
        + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))
          * decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)) := by
  obtain ⟨hoxtri, hoytri⟩ := offsetN_of_sat hsat hc i hi
  have hoxm := decodeOff_modEq hoxtri
  have hoym := decodeOff_modEq hoytri
  have hg := sgateH hsat i hi (mem_st_offnz n)
  rw [headToExpr_evalStep, evalHStep_addProd, evalHStep_addProd, evalHStep_lin,
    varsVal_pair, varsVal_pair] at hg
  have hmod := (gate_modEq_iff
    (a := (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n))
    (b := (envAt t i).loc (NGen.A_CHOOSE_BASE n + 55) * (envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)
        + (envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)
          * (envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)) (by ring)).mp hg
  have hsq := Int.ModEq.add (hoxm.mul hoxm) (hoym.mul hoym)
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ (hmod.trans hsq)
  rcases decodeOff_val hoxtri with h | h | h <;> rcases decodeOff_val hoytri with h' | h' | h' <;>
    rw [h, h'] <;> exact ⟨by norm_num, by norm_num⟩

end Leg5Found

/-! ## §7 — Axiom pins. -/

#assert_axioms bitSum_bounds
#assert_axioms ge0RN_of_sat
#assert_axioms decisionCmp_gt_iff_scoreB
#assert_axioms score_embedding_fails_at_150
#assert_axioms sgtN_of_sat
#assert_axioms xmoveN_of_sat
#assert_axioms colPinN_of_sat
#assert_axioms oxN_of_sat
#assert_axioms oyN_of_sat
#assert_axioms daScoreN
#assert_axioms offset_matches_chooseOffsetN
#assert_axioms automatonOffset_of_satN
#assert_axioms automatonOffset_of_sat_n11
#assert_axioms automatonOffset_of_sat_n3
#assert_axioms ge0RN_mod_of_sat
#assert_axioms offCardN_of_sat
#assert_axioms offnzN_of_sat
#assert_axioms mem_st_txlo
#assert_axioms mem_st_moved

end Dregg2.Circuit.Emit.AutomataflStepChoose
