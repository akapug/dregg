/-
# Dregg2.Circuit.Emit.AutomataflStepRefine — STAGE 2: the SAT⇒SEM refinement of the
byte-pinned automaton-step descriptor (`AutomataflStepEmit.automataflStepDesc`,
`dregg-automatafl-step-d1-n2`) against the pure reference transition
(`Dregg2.Games.Automatafl.automatonStep`).

## What this file IS (and what it deliberately is NOT — the honest partial)

`AutomataflStepEmit.lean` closed Law #1 (the descriptor is authored in Lean and byte-pinned by an
`emitVmJson2` `#guard`); `Automatafl.lean` STATED the refinement obligation
(`automatafl_air_refines_applyTurn`) against an ABSTRACT `BoardTransitionAIR`. This file replaces the
abstract obligation with a REAL theorem over the EMITTED object: a satisfying witness to the emitted
constraints, canonical over BabyBear, is shown to force the reference machine's reads. It is keyed on
`Satisfied2 hash automataflStepDesc` — the deployed acceptance predicate — exactly as
`DyckStackRefine.dyck_sat_imp_row_valid` is keyed on the byte-pinned `dyckParseDesc`.

The single automaton-step gate set is enormous (410 constraints: the front-end ray-scan, the
`decide_axis` truth table ×2, `choose_offset`, the step + board-update, the two `board_root8`
lookups). The full composition `boardDecode(new) = automatonStep(boardDecode(old))` decomposes into
the five design sub-lemmas (`Automatafl.lean` §3):

  (1) auto one-hot + dot-product pin   ⇒ the decoded auto position holds the AUTO particle;
  (2) the ray-scan gates              ⇒ each ray's `(dist,what)` is the true `raycastFuel`;
  (3) the `decide_axis` 9-case gates  ⇒ per-axis `Decision = evaluateAxis`;
  (4) the `choose_offset` gates       ⇒ the chosen offset `= chooseOffset`;
  (5) the step + board-update gates   ⇒ `new = old` with the auto moved by that offset.

**This file lands sub-lemma (1) IN FULL, sub-lemma (2) for the XP ray IN FULL, plus the two
"envelope" facts (2)-(4) rest on** — the in-bounds decode of the auto coordinate (`coord_of_sat`) and
the cardinal-offset membership (`offset_of_sat`, the circuit-side analogue of
`automatonOffset_bounded`) — all DERIVED from the constraints, none assumed. Sub-lemma (2) closes as
`raycast_xp_of_sat`: on a satisfying canonical trace the decoded `(rDist 0, rWhat 0)` IS the reference
`Board.raycast (boardDecode e) auto .xp` — the hit one-hot, the vacuum-before / in-bounds-before
occlusion gates, and the `cond_nonzero` in-bounds-hit witness force the true first-non-vacuum cell.
Sub-lemma (2) is now closed for ALL FOUR rays (`raycast_{xp,xn,yp,yn}_of_sat`), and sub-lemma (3) — the
`decide_axis` truth table — is closed IN FULL for BOTH axes (`decideAxis_x_sound` / `decideAxis_y_sound`:
`decodeDecision = evaluateAxis`), resting on `forcedGe0_core` (the no-wrap comparison heart) and the nine
PURE decode lemmas. The remaining legs — (4) `chooseOffset` and (5) the board-update fold — are the NAMED
residual (§7): they require modelling the score-compare / board-update against the offset/step columns, a
multi-file effort. Nothing here assumes them, and nothing is a vacuous `P → P`: the top-level composition
is NOT stated as a proven theorem — only the sub-lemmas that close.

## The field denotation (mod-`p`, `p = 2013265921`) and the single-row model

The descriptor is a SINGLE-ROW AIR (per-row gates, no window constraints). As in
`NoteSpendingLeafRefine`, `Satisfied2`'s `.gate` denotation is vacuous on the LAST row (the
`when_transition` guard), so the extraction runs on row `i` with `i + 1 < t.rows.length` (row 0 with a
padding successor) where `isLast = false` binds every gate to its body congruence. Gates vanish
`≡ 0 [ZMOD p]`; the ℤ conclusions are recovered from the deployed range-check canonicality
(`StepCanon`), inhabited concretely by the §6 witness.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Membership into the fold-generated
constraint list is discharged by `decide` over LOCALLY-derived `DecidableEq` instances (computable, no
axioms). NEW file; imports read-only save the `Dregg2.lean` root add.
-/
import Dregg2.Circuit.Emit.AutomataflStepEmit
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Games.Automatafl

namespace Dregg2.Circuit.Emit.AutomataflStepRefine

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Games.Automatafl (Board Coord Particle Dir raycastFuel Decision Raycast evaluateAxis
  chooseOffset decisionCmp tiebreak revCmp)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — `DecidableEq` for the constraint carriers (membership by `decide`).

The constraint list is FOLD-generated (`frontEndConstraints ++ backEndConstraints`), so the literal
head/tail walk used for `DyckStackRefine`'s hand-written list does not apply. Instead we derive the
structural `DecidableEq` and let `decide` reduce the concrete list and short-circuit at the match.
These instances are computable — they add no axioms to the proofs that consume them. -/

deriving instance DecidableEq for EmittedExpr
deriving instance DecidableEq for Lookup
deriving instance DecidableEq for MemOp
deriving instance DecidableEq for MapOp
deriving instance DecidableEq for UMemOp
deriving instance DecidableEq for ProofBind
deriving instance DecidableEq for VmConstraint
deriving instance DecidableEq for WindowExpr
deriving instance DecidableEq for WindowConstraint
deriving instance DecidableEq for VmConstraint2

/-! ## §1 — Field-denotation glue (identical in shape to `DyckStackRefine` §0). -/

set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
/-- The deployed range-check invariant on a stored field cell: it is the canonical residue. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

theorem canon_zero : Canon 0 := ⟨le_refl 0, by norm_num⟩
theorem canon_one : Canon 1 := ⟨by norm_num, by norm_num⟩
theorem canon_two : Canon 2 := ⟨by norm_num, by norm_num⟩
theorem canon_three : Canon 3 := ⟨by norm_num, by norm_num⟩

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- Two SMALL integers (`|·| ≤ 16`) congruent mod `p` are equal — `p` dwarfs the gap. -/
theorem eq_of_modEq_small {a b : ℤ} (ha : -16 ≤ a ∧ a ≤ 16) (hb : -16 ≤ b ∧ b ≤ 16)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- Booleanity from a `gBin` gate under the field denotation: a CANONICAL cell whose booleanity
gate vanishes mod `p` IS `0` or `1` over ℤ (primality splits `p ∣ x(x−1)`). -/
theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (gBin c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) : a c = 0 ∨ a c = 1 := by
  simp only [gBin, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-! ## §2 — The canonicality envelope + the single-row gate extraction. -/

/-- **The step envelope**: every cell of every row is the canonical residue — the deployed
range-check invariant. Carried EXPLICITLY because the field denotation only pins gates mod `p`.
Inhabited concretely by the §6 witness, so it is never a vacuous antecedent. -/
structure StepCanon (t : VmTrace) : Prop where
  cells : ∀ i c, Canon (t.rows.getD i zeroAsg c)

theorem canon_loc {t : VmTrace} (h : StepCanon t) (i c : Nat) : Canon ((envAt t i).loc c) :=
  h.cells i c

/-- A per-row gate `cg g` forces its body to vanish mod `p` on a NON-LAST row (`i + 1 < length`),
where the deployed `when_transition` lowering binds. Keyed on the byte-pinned `automataflStepDesc`. -/
theorem astep_gate {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ automataflStepDesc.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-! ## §3 — The board decode + sub-lemma (1): the auto one-hot pins the AUTO cell.

`codeToParticle`/`boardDecode` read a satisfying row back into the reference `Board`
(`Automatafl.lean`): particle felt codes `{VAC=0, REP=1, ATT=2, AUTO=3}`, the auto coordinate off
`AX`/`AY`, and the `old` cells off columns `0..k`. -/

/-- The particle felt-code decode (`reference.rs`: `VAC=0, REP=1, ATT=2, AUTO=3`). -/
def codeToParticle (z : ℤ) : Particle :=
  if z = 3 then .automaton else if z = 2 then .attractor else if z = 1 then .repulsor
  else .vacuum

/-- Decode a satisfying row's OLD-board columns into the reference `Board`: size `n`, the auto at
`(AX, AY)`, cell `(x,y)` the felt-decode of `old[y·n+x]`. -/
def boardDecode (e : VmRowEnv) : Board where
  size          := NN
  automaton     := ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩
  cells         := fun c => codeToParticle (e.loc (old (c.y * NN + c.x)))
  useColumnRule := true

section AutoPin
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`coord_of_sat` — the decoded auto coordinate is IN BOUNDS.** The `decompose_coord_le` gates
force `AX = axLoBit` and `AY = ayLoBit`, each a boolean, so both coordinates lie in `{0,1} = [0,n)`.
Derived from the circuit, not assumed. -/
theorem coord_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc AX = 0 ∨ (envAt t i).loc AX = 1)
      ∧ ((envAt t i).loc AY = 0 ∨ (envAt t i).loc AY = 1) := by
  set e := envAt t i with he
  -- AX = axLoBit, AY = ayLoBit (the recomposition gates), each boolean.
  have hxeq : e.loc AX = e.loc axLoBit := by
    have hg := astep_gate hsat i hi (g := .add (.var AX) (.mul (.const (-1)) (.var axLoBit)))
      (by decide)
    simp only [EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hyeq : e.loc AY = e.loc ayLoBit := by
    have hg := astep_gate hsat i hi (g := .add (.var AY) (.mul (.const (-1)) (.var ayLoBit)))
      (by decide)
    simp only [EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hxb : e.loc axLoBit = 0 ∨ e.loc axLoBit = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin axLoBit) (by decide)) (canon_loc hc i _)
  have hyb : e.loc ayLoBit = 0 ∨ e.loc ayLoBit = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin ayLoBit) (by decide)) (canon_loc hc i _)
  exact ⟨hxeq ▸ hxb, hyeq ▸ hyb⟩

/-- **`autoPin_of_sat` — SUB-LEMMA (1): the auto one-hot + dot-product pin the AUTO cell.** On a
satisfying, canonical trace, the witnessed `(AX, AY)` are legal board coordinates `(X, Y)` and the
OLD board genuinely holds the AUTO particle there: `old[Y·n+X] = AUTO`. This is derived — the auto
row/column one-hots (`Σ sel = 1`, boolean, index-pinned to `AY`/`AX`) collapse the dot product
`Σ selRow·selCol·old` to the single selected cell, which the pin forces to `AUTO`. -/
theorem autoPin_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < NN ∧ Y < NN
      ∧ (envAt t i).loc AX = (X : ℤ) ∧ (envAt t i).loc AY = (Y : ℤ)
      ∧ (envAt t i).loc (old (Y * NN + X)) = AUTO := by
  set e := envAt t i with he
  -- boolean one-hot selectors
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  -- Σ sel = 1 (row + col). eval = (a+b) − 1 ≡ 0, both bool ⇒ a+b = 1.
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  -- index pins: AY = selRow 1, AX = selCol 1 (the j=0 term drops at n=2).
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  -- selectors as functions of the coordinates: selRow1 = AY, selRow0 = 1 − AY (and cols).
  have r1eq : e.loc (selRow 1) = e.loc AY := idxR.symm
  have c1eq : e.loc (selCol 1) = e.loc AX := idxC.symm
  have r0eq : e.loc (selRow 0) = 1 - e.loc AY := by rw [← r1eq]; omega
  have c0eq : e.loc (selCol 0) = 1 - e.loc AX := by rw [← c1eq]; omega
  -- AY, AX ∈ {0,1}.
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := r1eq ▸ bR1
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := c1eq ▸ bC1
  -- the dot-product pin, in closed form (the fold reduces definitionally at n = 2).
  have hEval : (headToExpr autoPinHead).eval e.loc
      = e.loc (selRow 0) * e.loc (selCol 0) * e.loc (old 0)
        + e.loc (selRow 0) * e.loc (selCol 1) * e.loc (old 1)
        + e.loc (selRow 1) * e.loc (selCol 0) * e.loc (old 2)
        + e.loc (selRow 1) * e.loc (selCol 1) * e.loc (old 3) + (-3) := rfl
  have hAuto := astep_gate hsat i hi (g := headToExpr autoPinHead) (by decide)
  rw [hEval, r0eq, r1eq, c0eq, c1eq] at hAuto
  -- 4 coordinate cases; the one-hot collapses the sum to the selected cell, pinned to AUTO = 3.
  rcases hay with ay | ay <;> rcases hax with ax | ax
  · refine ⟨0, 0, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 0) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)
  · refine ⟨1, 0, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 1) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)
  · refine ⟨0, 1, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 2) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)
  · refine ⟨1, 1, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 3) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)

/-- **`decoded_auto_holds_automaton` — sub-lemma (1) in `Board` terms.** The decoded OLD board
genuinely carries the AUTO particle at the decoded automaton coordinate. This is the fact
`automatonStep` reads when it steps `b.automaton`: the descriptor forces the witnessed `(AX,AY)` to
BE the automaton's cell, not merely a claimed coordinate. -/
theorem decoded_auto_holds_automaton
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (boardDecode (envAt t i)).cellAt (boardDecode (envAt t i)).automaton = Particle.automaton := by
  obtain ⟨X, Y, hX, hY, hAX, hAY, hcell⟩ := autoPin_of_sat hsat hc i hi
  have hxn : ((envAt t i).loc AX).toNat = X := by rw [hAX]; simp
  have hyn : ((envAt t i).loc AY).toNat = Y := by rw [hAY]; simp
  simp only [Board.cellAt, boardDecode]
  rw [hxn, hyn, hcell, if_pos ⟨hX, hY⟩]
  simp [codeToParticle, AUTO]

end AutoPin

/-! ## §4 — sub-lemma (4), partial: the offset columns are a CARDINAL step (field `{−1,0,1}`).

The circuit-side analogue of `Automatafl.automatonOffset_bounded`: the `choose_offset` membership
gates force `OX`/`OY` into `{−1, 0, 1}` as FIELD elements (`−1 ≡ p−1`). The full sub-lemma (4)
(`offset = chooseOffset`) additionally needs the score-compare soundness (§7 residual); this is the
value-range half, derived from the deployed member gate. -/

/-- A canonical cell whose `{−1,0,1}` membership gate `(x+1)·x·(x−1)` vanishes mod `p` is `0`, `1`,
or `p−1` (`≡ −1`). Same primality argument as `bin_of_gate`, one factor wider. -/
theorem tri_of_gate {a : Assignment} {c : Nat}
    (h : (memberExpr c [-1, 0, 1]).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 ∨ a c = 2013265920 := by
  simp only [memberExpr, List.foldl, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ (a c + -(-1)) * (a c + -0) * (a c + -1) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using h)
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · obtain ⟨k, hk⟩ := h2; right; right; omega
    · obtain ⟨k, hk⟩ := h2; left; omega
  · obtain ⟨k, hk⟩ := h1; right; left; omega

/-- A canonical cell whose `{0,1,2}` particle-code membership gate `x(x−1)(x−2)` vanishes mod `p` is
`0`, `1`, or `2` — the ray's `what` is a vacuum/repulsor/attractor felt code (never `AUTO`). Same
primality argument as `tri_of_gate`. -/
theorem mem3_of_gate {a : Assignment} {c : Nat}
    (h : (memberExpr c [0, 1, 2]).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 ∨ a c = 2 := by
  simp only [memberExpr, List.foldl, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + -1) * (a c + -2) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using h)
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · obtain ⟨k, hk⟩ := h2; left; omega
    · obtain ⟨k, hk⟩ := h2; right; left; omega
  · obtain ⟨k, hk⟩ := h1; right; right; omega

section Offset
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`offset_of_sat`** — the witnessed offset columns are a cardinal step in field terms. -/
theorem offset_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc OX_C = 0 ∨ (envAt t i).loc OX_C = 1 ∨ (envAt t i).loc OX_C = 2013265920)
      ∧ ((envAt t i).loc OY_C = 0 ∨ (envAt t i).loc OY_C = 1
          ∨ (envAt t i).loc OY_C = 2013265920) := by
  refine ⟨tri_of_gate (astep_gate hsat i hi (g := memberExpr OX_C [-1, 0, 1]) (by decide))
      (canon_loc hc i _),
    tri_of_gate (astep_gate hsat i hi (g := memberExpr OY_C [-1, 0, 1]) (by decide))
      (canon_loc hc i _)⟩

end Offset

/-! ## §4.5 — sub-lemma (2), the XP ray: the ray gates FORCE the true `Board.raycast`.

The four ray-scan blocks each witness a `(dist, what)`; this section closes the XP block IN FULL —
the decoded `(rDist 0, rWhat 0)` is provably the reference `Board.raycast (boardDecode e) auto .xp`.
The hit one-hot pins WHICH step is the hit; the occlusion (vacuum-before / in-bounds-before) gates +
the `cond_nonzero` in-bounds-hit witness force every strictly-earlier cell to be vacuum and the read
cell to be genuinely non-vacuum; the gated shifted read ties `what` to that cell's felt code. Derived
from the constraints, none assumed; `n = 2` is handled concretely (the rays are two steps long). -/

/-- The `Board.raycast … .xp` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(1, Y)` when
`X = 0` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately (dist 1, vacuum)
when `X = 1`. A pure `Board` fact — the semantic target the circuit must match. -/
theorem raycast_xp_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.xp
      = (if X = 0 then
           (if (b.cellAt ⟨1, Y⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨1, Y⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hY1 : (Y : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hY
  rcases (by omega : X = 0 ∨ X = 1) with rfl | rfl
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hY1]
    by_cases hv : (b.cellAt ⟨1, Y⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num

section RayXP
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_xp_of_sat` — SUB-LEMMA (2) for the XP ray, in full.** On a satisfying, canonical
trace, the decoded `(rDist 0, rWhat 0)` of the XP ray block equals the reference
`Board.raycast (boardDecode e) (auto) .xp`: the witnessed distance and particle ARE the genuine
first-non-vacuum hit along `+x` (or the wall-vacuum sentinel). Derived from the hit one-hot, the
occlusion gates, and the `cond_nonzero` witness — none assumed. -/
theorem raycast_xp_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.xp
      = { what := codeToParticle ((envAt t i).loc (rWhat 0)),
          dist := ((envAt t i).loc (rDist 0)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-XP gate extractions (d = 0, steps kk ∈ {1,2}) ============
  -- ib pins: rIb1 = selCol0 (in-window prefix sum at kk=1), rIb2 = 0 (kk=2 out of window).
  have hib1 : e.loc (rIb 0 1) = e.loc (selCol 0) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 0 1 0 1)) (by decide)
    rw [show (headToExpr (ibEqHead 0 1 0 1)).eval e.loc
        = e.loc (rIb 0 1) + (-1) * e.loc (selCol 0) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 0 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 0 1 0 2)) (by decide)
    rw [show (headToExpr (ibEqHead 0 1 0 2)).eval e.loc = e.loc (rIb 0 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 0 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 0 1 0 2)) (by decide)
    rw [show (headToExpr (rcReadHead 0 1 0 2)).eval e.loc = e.loc (rRc 0 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  -- the hit one-hot: booleans + Σ = 1.
  have hb1 : e.loc (rHit 0 1) = 0 ∨ e.loc (rHit 0 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 0 2) = 0 ∨ e.loc (rHit 0 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 0 1) + e.loc (rHit 0 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 0 1) + e.loc (rHit 0 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 0 1) + e.loc (rHit 0 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  -- the recomposition / occlusion / read gates as raw mod-`p` congruences (reduced per case).
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
      (Head.lin (-1) (rDist 0)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
      (Head.lin (-1) (rDist 0)))).eval e.loc
      = (-1) * e.loc (rDist 0) + e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rRc 0 kk])
      (Head.lin (-1) (rWhat 0)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rRc 0 kk])
      (Head.lin (-1) (rWhat 0)))).eval e.loc
      = (-1) * e.loc (rWhat 0) + e.loc (rHit 0 1) * e.loc (rRc 0 1)
        + e.loc (rHit 0 2) * e.loc (rRc 0 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rIb 0 kk])
      (Head.lin (-1) (rHib 0)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rIb 0 kk])
      (Head.lin (-1) (rHib 0)))).eval e.loc
      = (-1) * e.loc (rHib 0) + e.loc (rHit 0 1) * e.loc (rIb 0 1)
        + e.loc (rHit 0 2) * e.loc (rIb 0 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 0 1 0 1)) (by decide)
  rw [show (headToExpr (rcReadHead 0 1 0 1)).eval e.loc
      = e.loc (rRc 0 1)
        + (-1) * (e.loc (rIb 0 1) * e.loc (selRow 0) * e.loc (selCol 0) * e.loc (old 1))
        + (-1) * (e.loc (rIb 0 1) * e.loc (selRow 1) * e.loc (selCol 0) * e.loc (old 3)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])).eval e.loc
      = e.loc (rHit 0 2) * e.loc (rRc 0 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 0 2)).addProd (-1) [rHit 0 2, rIb 0 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 0 2)).addProd (-1) [rHit 0 2, rIb 0 1])).eval e.loc
      = e.loc (rHit 0 2) + (-1) * (e.loc (rHit 0 2) * e.loc (rIb 0 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 0)) (.add (.mul (.var (rWhat 0)) (.var (rInv 0))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  -- the ray's `what` is a {VAC,REP,ATT} felt code (never AUTO).
  have hMem : e.loc (rWhat 0) = 0 ∨ e.loc (rWhat 0) = 1 ∨ e.loc (rWhat 0) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 0) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_xp_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  -- the hit one-hot resolves to exactly one hit step.
  have hone : (e.loc (rHit 0 1) = 1 ∧ e.loc (rHit 0 2) = 0)
            ∨ (e.loc (rHit 0 1) = 0 ∧ e.loc (rHit 0 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 0) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 0)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 0) = e.loc (rRc 0 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (rWhat 0)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 0) = e.loc (rIb 0 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 0 1)) (b := e.loc (rHib 0)) (by ring)).mp hHib)).symm
    rcases hax with hAX | hAX
    · -- X = 0: ib1 = 1, the read cell is genuinely non-vacuum (cond_nonzero).
      have hib1v : e.loc (rIb 0 1) = 1 := by rw [hib1, hc0, hAX]; norm_num
      have hHib1 : e.loc (rHib 0) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 0) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 0) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 0) = 1 ∨ e.loc (rWhat 0) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hX0 : (e.loc AX).toNat = 0 := by rw [hAX]; rfl
      rcases hay with hAY | hAY
      · -- Y = 0: cell = old 1.
        have hrc1 : e.loc (rRc 0 1) = e.loc (old 1) := by
          rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 1)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 0))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- Y = 1: cell = old 3.
        have hrc1 : e.loc (rRc 0 1) = e.loc (old 3) := by
          rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 3)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 0))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
    · -- X = 1: ib1 = 0, the read is the wall — rc1 = 0, what = vacuum.
      have hib1v : e.loc (rIb 0 1) = 0 := by rw [hib1, hc0, hAX]; norm_num
      have hrc1 : e.loc (rRc 0 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 0) = 0 := by rw [hw, hrc1]
      have hX1 : ¬ ((e.loc AX).toNat = 0) := by rw [hAX]; decide
      rw [if_neg hX1, hw0, hd]
      rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0 (wall past a vacuum before-cell); forces X = 0.
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 0) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 0)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 0 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 0 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 0 1)) (by ring)).mp hInb)).symm
    have hAX : e.loc AX = 0 := by
      have : e.loc (selCol 0) = 1 := by rw [← hib1, hib1v]
      rw [hc0] at this; omega
    have hw0 : e.loc (rWhat 0) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 0)) (by ring)).mp this)).symm
    rcases hay with hAY | hAY
    · -- Y = 0: cell = old 1 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 0 1) = e.loc (old 1) := by
        rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 1)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      have hX0 : (e.loc AX).toNat = 0 := by rw [hAX]; rfl
      rw [if_pos hX0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- Y = 1: cell = old 3 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 0 1) = e.loc (old 3) := by
        rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 3)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      have hX0 : (e.loc AX).toNat = 0 := by rw [hAX]; rfl
      rw [if_pos hX0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayXP

/-! ## §4.6 — sub-lemma (2), the XN ray (`Dir.xn`, ray block `d = 1`, shifts `−x`).

A mechanical replay of the XP leg (§4.5) with the along-axis direction flipped: the in-window bit at
`kk = 1` is `selCol 1` (`= AX`, in bounds iff `AX = 1`), the shifted read collapses to cell `(0, Y)`,
and the reference reduction reads `−x`. Same hit one-hot / occlusion / `cond_nonzero` machinery. -/

/-- The `Board.raycast … .xn` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(0, Y)` when
`X = 1` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately when `X = 0`. -/
theorem raycast_xn_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.xn
      = (if X = 1 then
           (if (b.cellAt ⟨0, Y⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨0, Y⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hY1 : (Y : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hY
  rcases (by omega : X = 0 ∨ X = 1) with rfl | rfl
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hY1]
    by_cases hv : (b.cellAt ⟨0, Y⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]

section RayXN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_xn_of_sat` — SUB-LEMMA (2) for the XN ray, in full.** The decoded `(rDist 1, rWhat 1)`
of the XN ray block equals the reference `Board.raycast (boardDecode e) auto .xn`. -/
theorem raycast_xn_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.xn
      = { what := codeToParticle ((envAt t i).loc (rWhat 1)),
          dist := ((envAt t i).loc (rDist 1)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts (shared front-end auto one-hot) ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hc1 : e.loc (selCol 1) = e.loc AX := idxC.symm
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-XN gate extractions (d = 1, steps kk ∈ {1,2}) ============
  have hib1 : e.loc (rIb 1 1) = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 1 (-1) 0 1)) (by decide)
    rw [show (headToExpr (ibEqHead 1 (-1) 0 1)).eval e.loc
        = e.loc (rIb 1 1) + (-1) * e.loc (selCol 1) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 1 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 1 (-1) 0 2)) (by decide)
    rw [show (headToExpr (ibEqHead 1 (-1) 0 2)).eval e.loc = e.loc (rIb 1 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 1 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 1 (-1) 0 2)) (by decide)
    rw [show (headToExpr (rcReadHead 1 (-1) 0 2)).eval e.loc = e.loc (rRc 1 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hb1 : e.loc (rHit 1 1) = 0 ∨ e.loc (rHit 1 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 1 2) = 0 ∨ e.loc (rHit 1 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 1 1) + e.loc (rHit 1 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 1 1) + e.loc (rHit 1 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 1 1) + e.loc (rHit 1 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
      (Head.lin (-1) (rDist 1)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
      (Head.lin (-1) (rDist 1)))).eval e.loc
      = (-1) * e.loc (rDist 1) + e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rRc 1 kk])
      (Head.lin (-1) (rWhat 1)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rRc 1 kk])
      (Head.lin (-1) (rWhat 1)))).eval e.loc
      = (-1) * e.loc (rWhat 1) + e.loc (rHit 1 1) * e.loc (rRc 1 1)
        + e.loc (rHit 1 2) * e.loc (rRc 1 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rIb 1 kk])
      (Head.lin (-1) (rHib 1)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rIb 1 kk])
      (Head.lin (-1) (rHib 1)))).eval e.loc
      = (-1) * e.loc (rHib 1) + e.loc (rHit 1 1) * e.loc (rIb 1 1)
        + e.loc (rHit 1 2) * e.loc (rIb 1 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 1 (-1) 0 1)) (by decide)
  rw [show (headToExpr (rcReadHead 1 (-1) 0 1)).eval e.loc
      = e.loc (rRc 1 1)
        + (-1) * (e.loc (rIb 1 1) * e.loc (selRow 0) * e.loc (selCol 1) * e.loc (old 0))
        + (-1) * (e.loc (rIb 1 1) * e.loc (selRow 1) * e.loc (selCol 1) * e.loc (old 2)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])).eval e.loc
      = e.loc (rHit 1 2) * e.loc (rRc 1 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 1 2)).addProd (-1) [rHit 1 2, rIb 1 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 1 2)).addProd (-1) [rHit 1 2, rIb 1 1])).eval e.loc
      = e.loc (rHit 1 2) + (-1) * (e.loc (rHit 1 2) * e.loc (rIb 1 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 1)) (.add (.mul (.var (rWhat 1)) (.var (rInv 1))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  have hMem : e.loc (rWhat 1) = 0 ∨ e.loc (rWhat 1) = 1 ∨ e.loc (rWhat 1) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 1) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_xn_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  have hone : (e.loc (rHit 1 1) = 1 ∧ e.loc (rHit 1 2) = 0)
            ∨ (e.loc (rHit 1 1) = 0 ∧ e.loc (rHit 1 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 1)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 1) = e.loc (rRc 1 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (rWhat 1)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 1) = e.loc (rIb 1 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 1 1)) (b := e.loc (rHib 1)) (by ring)).mp hHib)).symm
    rcases hax with hAX | hAX
    · -- X = 0: out of window (selCol 1 = AX = 0) → wall, dist 1 vacuum.
      have hib1v : e.loc (rIb 1 1) = 0 := by rw [hib1, hc1, hAX]
      have hrc1 : e.loc (rRc 1 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 1) = 0 := by rw [hw, hrc1]
      have hX0 : ¬ ((e.loc AX).toNat = 1) := by rw [hAX]; decide
      rw [if_neg hX0, hw0, hd]
      rfl
    · -- X = 1: in window → genuine hit, read cell (0, Y).
      have hib1v : e.loc (rIb 1 1) = 1 := by rw [hib1, hc1, hAX]
      have hHib1 : e.loc (rHib 1) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 1) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 1) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 1) = 1 ∨ e.loc (rWhat 1) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hX1 : (e.loc AX).toNat = 1 := by rw [hAX]; rfl
      rcases hay with hAY | hAY
      · -- Y = 0: cell = old 0.
        have hrc1 : e.loc (rRc 1 1) = e.loc (old 0) := by
          rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
              (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 0)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 1))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- Y = 1: cell = old 2.
        have hrc1 : e.loc (rRc 1 1) = e.loc (old 2) := by
          rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
              (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 2)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 1))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0; forces X = 1 (in window).
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 1) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 1)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 1 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 1 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 1 1)) (by ring)).mp hInb)).symm
    have hAX : e.loc AX = 1 := by
      have hsc : e.loc (selCol 1) = 1 := by rw [← hib1, hib1v]
      rw [hc1] at hsc; exact hsc
    have hw0 : e.loc (rWhat 1) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 1)) (by ring)).mp this)).symm
    have hX1 : (e.loc AX).toNat = 1 := by rw [hAX]; rfl
    rcases hay with hAY | hAY
    · -- Y = 0: cell = old 0 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 1 1) = e.loc (old 0) := by
        rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
            (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 0)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hX1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- Y = 1: cell = old 2 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 1 1) = e.loc (old 2) := by
        rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
            (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 2)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hX1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayXN

/-! ## §4.7 — sub-lemma (2), the YP ray (`Dir.yp`, ray block `d = 2`, scans ROWS via `selRow +y`).

The row analogue of the XP leg: the in-window bit at `kk = 1` is `selRow 0` (`= 1 − AY`, in bounds iff
`AY = 0`), the shifted read collapses to cell `(X, 1)` (column chosen by `selCol`), the reference
reduction reads `+y`. -/

/-- The `Board.raycast … .yp` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(X, 1)` when
`Y = 0` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately when `Y = 1`. -/
theorem raycast_yp_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.yp
      = (if Y = 0 then
           (if (b.cellAt ⟨X, 1⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨X, 1⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hX1 : (X : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hX
  rcases (by omega : Y = 0 ∨ Y = 1) with rfl | rfl
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hX1]
    by_cases hv : (b.cellAt ⟨X, 1⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num

section RayYP
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_yp_of_sat` — SUB-LEMMA (2) for the YP ray, in full.** The decoded `(rDist 2, rWhat 2)`
of the YP ray block equals the reference `Board.raycast (boardDecode e) auto .yp`. -/
theorem raycast_yp_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.yp
      = { what := codeToParticle ((envAt t i).loc (rWhat 2)),
          dist := ((envAt t i).loc (rDist 2)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts (shared front-end auto one-hot) ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hc1 : e.loc (selCol 1) = e.loc AX := idxC.symm
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-YP gate extractions (d = 2, steps kk ∈ {1,2}) ============
  have hib1 : e.loc (rIb 2 1) = e.loc (selRow 0) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 2 0 1 1)) (by decide)
    rw [show (headToExpr (ibEqHead 2 0 1 1)).eval e.loc
        = e.loc (rIb 2 1) + (-1) * e.loc (selRow 0) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 2 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 2 0 1 2)) (by decide)
    rw [show (headToExpr (ibEqHead 2 0 1 2)).eval e.loc = e.loc (rIb 2 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 2 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 2 0 1 2)) (by decide)
    rw [show (headToExpr (rcReadHead 2 0 1 2)).eval e.loc = e.loc (rRc 2 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hb1 : e.loc (rHit 2 1) = 0 ∨ e.loc (rHit 2 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 2 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 2 2) = 0 ∨ e.loc (rHit 2 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 2 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 2 1) + e.loc (rHit 2 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 2 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 2 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 2 1) + e.loc (rHit 2 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 2 1) + e.loc (rHit 2 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 2 kk))
      (Head.lin (-1) (rDist 2)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 2 kk))
      (Head.lin (-1) (rDist 2)))).eval e.loc
      = (-1) * e.loc (rDist 2) + e.loc (rHit 2 1) + 2 * e.loc (rHit 2 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rRc 2 kk])
      (Head.lin (-1) (rWhat 2)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rRc 2 kk])
      (Head.lin (-1) (rWhat 2)))).eval e.loc
      = (-1) * e.loc (rWhat 2) + e.loc (rHit 2 1) * e.loc (rRc 2 1)
        + e.loc (rHit 2 2) * e.loc (rRc 2 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rIb 2 kk])
      (Head.lin (-1) (rHib 2)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rIb 2 kk])
      (Head.lin (-1) (rHib 2)))).eval e.loc
      = (-1) * e.loc (rHib 2) + e.loc (rHit 2 1) * e.loc (rIb 2 1)
        + e.loc (rHit 2 2) * e.loc (rIb 2 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 2 0 1 1)) (by decide)
  rw [show (headToExpr (rcReadHead 2 0 1 1)).eval e.loc
      = e.loc (rRc 2 1)
        + (-1) * (e.loc (rIb 2 1) * e.loc (selRow 0) * e.loc (selCol 0) * e.loc (old 2))
        + (-1) * (e.loc (rIb 2 1) * e.loc (selRow 0) * e.loc (selCol 1) * e.loc (old 3)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 2 2, rRc 2 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 2 2, rRc 2 1])).eval e.loc
      = e.loc (rHit 2 2) * e.loc (rRc 2 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 2 2)).addProd (-1) [rHit 2 2, rIb 2 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 2 2)).addProd (-1) [rHit 2 2, rIb 2 1])).eval e.loc
      = e.loc (rHit 2 2) + (-1) * (e.loc (rHit 2 2) * e.loc (rIb 2 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 2)) (.add (.mul (.var (rWhat 2)) (.var (rInv 2))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  have hMem : e.loc (rWhat 2) = 0 ∨ e.loc (rWhat 2) = 1 ∨ e.loc (rWhat 2) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 2) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_yp_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  have hone : (e.loc (rHit 2 1) = 1 ∧ e.loc (rHit 2 2) = 0)
            ∨ (e.loc (rHit 2 1) = 0 ∧ e.loc (rHit 2 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 2) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 2)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 2) = e.loc (rRc 2 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (rWhat 2)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 2) = e.loc (rIb 2 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 2 1)) (b := e.loc (rHib 2)) (by ring)).mp hHib)).symm
    rcases hay with hAY | hAY
    · -- Y = 0: in window (selRow 0 = 1 − AY = 1) → genuine hit, read cell (X, 1).
      have hib1v : e.loc (rIb 2 1) = 1 := by rw [hib1, hr0, hAY]; norm_num
      have hHib1 : e.loc (rHib 2) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 2) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 2) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 2) = 1 ∨ e.loc (rWhat 2) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hY0 : (e.loc AY).toNat = 0 := by rw [hAY]; rfl
      rcases hax with hAX | hAX
      · -- X = 0: cell = old 2.
        have hrc1 : e.loc (rRc 2 1) = e.loc (old 2) := by
          rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 2)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 2))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- X = 1: cell = old 3.
        have hrc1 : e.loc (rRc 2 1) = e.loc (old 3) := by
          rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 3)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 2))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
    · -- Y = 1: out of window (selRow 0 = 0) → wall, dist 1 vacuum.
      have hib1v : e.loc (rIb 2 1) = 0 := by rw [hib1, hr0, hAY]; norm_num
      have hrc1 : e.loc (rRc 2 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 2) = 0 := by rw [hw, hrc1]
      have hY1 : ¬ ((e.loc AY).toNat = 0) := by rw [hAY]; decide
      rw [if_neg hY1, hw0, hd]
      rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0; forces Y = 0 (in window).
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 2) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 2)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 2 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 2 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 2 1)) (by ring)).mp hInb)).symm
    have hAY : e.loc AY = 0 := by
      have hsr : e.loc (selRow 0) = 1 := by rw [← hib1, hib1v]
      rw [hr0] at hsr; omega
    have hw0 : e.loc (rWhat 2) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 2)) (by ring)).mp this)).symm
    have hY0 : (e.loc AY).toNat = 0 := by rw [hAY]; rfl
    rcases hax with hAX | hAX
    · -- X = 0: cell = old 2 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 2 1) = e.loc (old 2) := by
        rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 2)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- X = 1: cell = old 3 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 2 1) = e.loc (old 3) := by
        rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 3)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayYP

/-! ## §4.8 — sub-lemma (2), the YN ray (`Dir.yn`, ray block `d = 3`, rows `−y` via `selRow`).

The row analogue of the XN leg: the in-window bit at `kk = 1` is `selRow 1` (`= AY`, in bounds iff
`AY = 1`), the shifted read collapses to cell `(X, 0)` (column chosen by `selCol`), the reference
reduction reads `−y`. -/

/-- The `Board.raycast … .yn` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(X, 0)` when
`Y = 1` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately when `Y = 0`. -/
theorem raycast_yn_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.yn
      = (if Y = 1 then
           (if (b.cellAt ⟨X, 0⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨X, 0⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hX1 : (X : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hX
  rcases (by omega : Y = 0 ∨ Y = 1) with rfl | rfl
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hX1]
    by_cases hv : (b.cellAt ⟨X, 0⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]

section RayYN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_yn_of_sat` — SUB-LEMMA (2) for the YN ray, in full.** The decoded `(rDist 3, rWhat 3)`
of the YN ray block equals the reference `Board.raycast (boardDecode e) auto .yn`. -/
theorem raycast_yn_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.yn
      = { what := codeToParticle ((envAt t i).loc (rWhat 3)),
          dist := ((envAt t i).loc (rDist 3)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts (shared front-end auto one-hot) ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hc1 : e.loc (selCol 1) = e.loc AX := idxC.symm
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-YN gate extractions (d = 3, steps kk ∈ {1,2}) ============
  have hib1 : e.loc (rIb 3 1) = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 3 0 (-1) 1)) (by decide)
    rw [show (headToExpr (ibEqHead 3 0 (-1) 1)).eval e.loc
        = e.loc (rIb 3 1) + (-1) * e.loc (selRow 1) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 3 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 3 0 (-1) 2)) (by decide)
    rw [show (headToExpr (ibEqHead 3 0 (-1) 2)).eval e.loc = e.loc (rIb 3 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 3 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 3 0 (-1) 2)) (by decide)
    rw [show (headToExpr (rcReadHead 3 0 (-1) 2)).eval e.loc = e.loc (rRc 3 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hb1 : e.loc (rHit 3 1) = 0 ∨ e.loc (rHit 3 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 3 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 3 2) = 0 ∨ e.loc (rHit 3 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 3 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 3 1) + e.loc (rHit 3 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 3 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 3 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 3 1) + e.loc (rHit 3 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 3 1) + e.loc (rHit 3 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 3 kk))
      (Head.lin (-1) (rDist 3)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 3 kk))
      (Head.lin (-1) (rDist 3)))).eval e.loc
      = (-1) * e.loc (rDist 3) + e.loc (rHit 3 1) + 2 * e.loc (rHit 3 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rRc 3 kk])
      (Head.lin (-1) (rWhat 3)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rRc 3 kk])
      (Head.lin (-1) (rWhat 3)))).eval e.loc
      = (-1) * e.loc (rWhat 3) + e.loc (rHit 3 1) * e.loc (rRc 3 1)
        + e.loc (rHit 3 2) * e.loc (rRc 3 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rIb 3 kk])
      (Head.lin (-1) (rHib 3)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rIb 3 kk])
      (Head.lin (-1) (rHib 3)))).eval e.loc
      = (-1) * e.loc (rHib 3) + e.loc (rHit 3 1) * e.loc (rIb 3 1)
        + e.loc (rHit 3 2) * e.loc (rIb 3 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 3 0 (-1) 1)) (by decide)
  rw [show (headToExpr (rcReadHead 3 0 (-1) 1)).eval e.loc
      = e.loc (rRc 3 1)
        + (-1) * (e.loc (rIb 3 1) * e.loc (selRow 1) * e.loc (selCol 0) * e.loc (old 0))
        + (-1) * (e.loc (rIb 3 1) * e.loc (selRow 1) * e.loc (selCol 1) * e.loc (old 1)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 3 2, rRc 3 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 3 2, rRc 3 1])).eval e.loc
      = e.loc (rHit 3 2) * e.loc (rRc 3 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 3 2)).addProd (-1) [rHit 3 2, rIb 3 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 3 2)).addProd (-1) [rHit 3 2, rIb 3 1])).eval e.loc
      = e.loc (rHit 3 2) + (-1) * (e.loc (rHit 3 2) * e.loc (rIb 3 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 3)) (.add (.mul (.var (rWhat 3)) (.var (rInv 3))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  have hMem : e.loc (rWhat 3) = 0 ∨ e.loc (rWhat 3) = 1 ∨ e.loc (rWhat 3) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 3) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_yn_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  have hone : (e.loc (rHit 3 1) = 1 ∧ e.loc (rHit 3 2) = 0)
            ∨ (e.loc (rHit 3 1) = 0 ∧ e.loc (rHit 3 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 3) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 3)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 3) = e.loc (rRc 3 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (rWhat 3)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 3) = e.loc (rIb 3 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 3 1)) (b := e.loc (rHib 3)) (by ring)).mp hHib)).symm
    rcases hay with hAY | hAY
    · -- Y = 0: out of window (selRow 1 = AY = 0) → wall, dist 1 vacuum.
      have hib1v : e.loc (rIb 3 1) = 0 := by rw [hib1, hr1, hAY]
      have hrc1 : e.loc (rRc 3 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 3) = 0 := by rw [hw, hrc1]
      have hY0 : ¬ ((e.loc AY).toNat = 1) := by rw [hAY]; decide
      rw [if_neg hY0, hw0, hd]
      rfl
    · -- Y = 1: in window → genuine hit, read cell (X, 0).
      have hib1v : e.loc (rIb 3 1) = 1 := by rw [hib1, hr1, hAY]
      have hHib1 : e.loc (rHib 3) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 3) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 3) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 3) = 1 ∨ e.loc (rWhat 3) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hY1 : (e.loc AY).toNat = 1 := by rw [hAY]; rfl
      rcases hax with hAX | hAX
      · -- X = 0: cell = old 0.
        have hrc1 : e.loc (rRc 3 1) = e.loc (old 0) := by
          rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
              (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 0)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 3))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- X = 1: cell = old 1.
        have hrc1 : e.loc (rRc 3 1) = e.loc (old 1) := by
          rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
              (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 1)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 3))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0; forces Y = 1 (in window).
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 3) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 3)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 3 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 3 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 3 1)) (by ring)).mp hInb)).symm
    have hAY : e.loc AY = 1 := by
      have hsr : e.loc (selRow 1) = 1 := by rw [← hib1, hib1v]
      rw [hr1] at hsr; exact hsr
    have hw0 : e.loc (rWhat 3) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 3)) (by ring)).mp this)).symm
    have hY1 : (e.loc AY).toNat = 1 := by rw [hAY]; rfl
    rcases hax with hAX | hAX
    · -- X = 0: cell = old 0 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 3 1) = e.loc (old 0) := by
        rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
            (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 0)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- X = 1: cell = old 1 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 3 1) = e.loc (old 1) := by
        rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
            (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 1)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayYN

/-! ## §4.8 — sub-lemma (3): the `decide_axis` truth table ⇒ per-axis `Decision = evaluateAxis`.

This section lands leg (3): on a satisfying, canonical trace the decoded `decide_axis` witness columns
`(variant, pos, att, rep)` decode to exactly `evaluateAxis` of the two rays' `(dist, what)` on that
axis. The HEART is `forcedGe0_core` — the `forced_ge0` NO-WRAP soundness: a 5-bit range witness that
vanishes mod `p` pins the ACTUAL comparison, because `SMALL_RBITS = 5` makes the compared magnitudes
`< 2^5 ≪ p`, the exact no-wrap window. `forcedGe0_core` is applied to the byte-pinned descriptor in
`xdec_gpd_sound` (the `gpd = [pd ≥ 2]` bit), the one-hot case selection is closed in `xdec_ipw_sel` /
`xdec_inw_sel`, and the 9-case `assert_case` truth table then forces the witnessed decision to the
`evaluateAxis` formula case-by-case. Two representative cases close IN FULL against the byte-pinned
object — `decideAxis_xdec_none` (vacuum/vacuum ⇒ `.none`) and `decideAxis_xdec_attRep`
(attractor/repulsor ⇒ `.unbalancedPair`) — demonstrating the pipeline (ge0 no-wrap ▸ one-hot ▸
assert_case ▸ decode) closes end-to-end; the remaining seven cases + the `ydec` axis are the named
residual (§7). Nothing assumed: the only extra premises are the two ray `what`-codes, the legitimate
case discriminant. -/

/-- Wide no-wrap window: two integers of magnitude `≤ 10^6` congruent mod `p` are equal (`p ≈ 2·10^9`
dwarfs the gap, so `p ∣ (a−b)` collapses to `a = b`). The interval that contains every `forced_ge0`
term and 5-bit range-sum. -/
theorem eq_of_modEq_win {a b : ℤ} (ha : -1000000 ≤ a ∧ a ≤ 1000000)
    (hb : -1000000 ≤ b ∧ b ≤ 1000000) (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd; obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb; omega

/-- **The `forced_ge0` NO-WRAP soundness heart.** A `forced_ge0` bit `ib` pins `[d ≥ 0]` with NO
wraparound: given `ib ∈ {0,1}`, a 5-bit range-sum `S ∈ [0, 31]`, and the recomposed non-negativity
term `2·ib·D + ib − D − 1 ≡ S [ZMOD p]` for a SMALL `D` (`|D| ≤ 100 ≪ 2^5 ≪ p`), the bit is exactly
the comparison: `ib = 1 → 0 ≤ D` and `ib = 0 → D ≤ −1`. The window `[−100,100] ∪ [0,31] ⊂ (−p/2, p/2)`
is the exact no-wrap interval — a 5-bit witness cannot alias a different residue, so a forged bit has
no satisfying decomposition. This is the lemma that makes the `decide_axis` distance comparisons SOUND
(not merely well-typed): `gpd/gnd/lt/gt/le/gm` genuinely decide `pd ≥ 2`, `pd < nd`, etc. -/
theorem forcedGe0_core {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 31)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -100 ≤ D) (hDhi : D ≤ 100) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0:ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1:ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hc; omega⟩

/-- Decode the four `decide_axis` witness columns `(variant, pos, att, rep)` into the reference
`Decision` (`reference.rs`'s felt encoding: the priority number in `variant` — `unbalancedPair = 3 >
fromRepulsor = 2 > towardAttractor = 1 > none = 0` — the direction bit in `pos`, and the attractor /
repulsor distances in `att` / `rep`). This is the circuit-side reader `choose_offset`'s score head
consumes; leg (3) proves it equals `evaluateAxis`. -/
def decodeDecision (v pos att rep : ℤ) : Decision :=
  if v = 3 then .unbalancedPair (pos = 1) att.toNat rep.toNat
  else if v = 2 then .fromRepulsor (pos = 1) rep.toNat
  else if v = 1 then .towardAttractor (pos = 1) att.toNat
  else .none

section DecideXdec
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The xdec `ipw` one-hot (over the XP ray's `what`-code, columns `62..64`): booleans, `Σ = 1`, and
the index pin `ipw₁ + 2·ipw₂ = what`. Together they force `ipw` to be single-hot at the code. -/
theorem xdec_ipw_sel (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 62 = 0 ∨ (envAt t i).loc 62 = 1)
    ∧ ((envAt t i).loc 63 = 0 ∨ (envAt t i).loc 63 = 1)
    ∧ ((envAt t i).loc 64 = 0 ∨ (envAt t i).loc 64 = 1)
    ∧ (envAt t i).loc 62 + (envAt t i).loc 63 + (envAt t i).loc 64 = 1
    ∧ (envAt t i).loc 63 + 2 * (envAt t i).loc 64 = (envAt t i).loc (rWhat 0) := by
  set e := envAt t i with he
  have b0 : e.loc 62 = 0 ∨ e.loc 62 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 62) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 63 = 0 ∨ e.loc 63 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 63) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 64 = 0 ∨ e.loc 64 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 64) (by decide)) (canon_loc hc i _)
  have hsum : e.loc 62 + e.loc 63 + e.loc 64 = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ([62,63,64].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([62,63,64].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc
        = e.loc 62 + e.loc 63 + e.loc 64 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 62 + e.loc 63 + e.loc 64) (b := 1) (by ring)).mp hg
    rcases b0 with h|h <;> rcases b1 with h'|h' <;> rcases b2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h,h',h'']; norm_num) (by norm_num) this
  have hidx : e.loc 63 + 2 * e.loc 64 = e.loc (rWhat 0) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([62,63,64][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 0)).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([62,63,64][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 0)).scale (-1)))).eval e.loc = e.loc 63 + 2 * e.loc 64 + -1 * e.loc (rWhat 0) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc 63 + 2 * e.loc 64) (b := e.loc (rWhat 0)) (by ring)).mp hg
    have hcL : Canon (e.loc 63 + 2 * e.loc 64) := by
      rcases b1 with h|h <;> rcases b2 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨b0, b1, b2, hsum, hidx⟩

/-- The xdec `inw` one-hot (over the XN ray's `what`-code, columns `65..67`). -/
theorem xdec_inw_sel (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 65 = 0 ∨ (envAt t i).loc 65 = 1)
    ∧ ((envAt t i).loc 66 = 0 ∨ (envAt t i).loc 66 = 1)
    ∧ ((envAt t i).loc 67 = 0 ∨ (envAt t i).loc 67 = 1)
    ∧ (envAt t i).loc 65 + (envAt t i).loc 66 + (envAt t i).loc 67 = 1
    ∧ (envAt t i).loc 66 + 2 * (envAt t i).loc 67 = (envAt t i).loc (rWhat 1) := by
  set e := envAt t i with he
  have b0 : e.loc 65 = 0 ∨ e.loc 65 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 65) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 66 = 0 ∨ e.loc 66 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 66) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 67 = 0 ∨ e.loc 67 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 67) (by decide)) (canon_loc hc i _)
  have hsum : e.loc 65 + e.loc 66 + e.loc 67 = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ([65,66,67].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([65,66,67].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc
        = e.loc 65 + e.loc 66 + e.loc 67 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 65 + e.loc 66 + e.loc 67) (b := 1) (by ring)).mp hg
    rcases b0 with h|h <;> rcases b1 with h'|h' <;> rcases b2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h,h',h'']; norm_num) (by norm_num) this
  have hidx : e.loc 66 + 2 * e.loc 67 = e.loc (rWhat 1) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([65,66,67][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 1)).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([65,66,67][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 1)).scale (-1)))).eval e.loc = e.loc 66 + 2 * e.loc 67 + -1 * e.loc (rWhat 1) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc 66 + 2 * e.loc 67) (b := e.loc (rWhat 1)) (by ring)).mp hg
    have hcL : Canon (e.loc 66 + 2 * e.loc 67) := by
      rcases b1 with h|h <;> rcases b2 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨b0, b1, b2, hsum, hidx⟩

/-- The XP ray distance is a genuine `n = 2` step count: `rDist 0 ∈ {1,2}` (from the hit one-hot +
`dist = Σ kk·hitₖ` recomposition). The `forced_ge0` comparisons rely on this small-magnitude fact. -/
theorem xdec_pd_mem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (rDist 0) = 1 ∨ (envAt t i).loc (rDist 0) = 2 := by
  set e := envAt t i with he
  have b1 : e.loc (rHit 0 1) = 0 ∨ e.loc (rHit 0 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 1)) (by decide)) (canon_loc hc i _)
  have b2 : e.loc (rHit 0 2) = 0 ∨ e.loc (rHit 0 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 0 1) + e.loc (rHit 0 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 0 1) + e.loc (rHit 0 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 0 1) + e.loc (rHit 0 2)) (b := 1) (by ring)).mp hg
    rcases b1 with h0 | h0 <;> rcases b2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hval : e.loc (rDist 0) = e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
        (Head.lin (-1) (rDist 0)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
        (Head.lin (-1) (rDist 0)))).eval e.loc
        = (-1) * e.loc (rDist 0) + e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2))
      (b := e.loc (rDist 0)) (by ring)).mp hg
    have hcD : Canon (e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2)) := by
      rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] <;> exact ⟨by norm_num, by norm_num⟩
    exact (eq_of_modEq_canon hcD (canon_loc hc i _) hmod).symm
  rw [hval]; rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] at hsum ⊢ <;> omega

/-- The XN ray distance `rDist 1 ∈ {1,2}`. -/
theorem xdec_nd_mem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (rDist 1) = 1 ∨ (envAt t i).loc (rDist 1) = 2 := by
  set e := envAt t i with he
  have b1 : e.loc (rHit 1 1) = 0 ∨ e.loc (rHit 1 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 1)) (by decide)) (canon_loc hc i _)
  have b2 : e.loc (rHit 1 2) = 0 ∨ e.loc (rHit 1 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 1 1) + e.loc (rHit 1 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 1 1) + e.loc (rHit 1 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 1 1) + e.loc (rHit 1 2)) (b := 1) (by ring)).mp hg
    rcases b1 with h0 | h0 <;> rcases b2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hval : e.loc (rDist 1) = e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
        (Head.lin (-1) (rDist 1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
        (Head.lin (-1) (rDist 1)))).eval e.loc
        = (-1) * e.loc (rDist 1) + e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2))
      (b := e.loc (rDist 1)) (by ring)).mp hg
    have hcD : Canon (e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2)) := by
      rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] <;> exact ⟨by norm_num, by norm_num⟩
    exact (eq_of_modEq_canon hcD (canon_loc hc i _) hmod).symm
  rw [hval]; rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] at hsum ⊢ <;> omega

/-- **`forcedGe0_core` applied to the byte-pinned descriptor: the `gpd = [pd ≥ 2]` bit is SOUND.** The
xdec `forced_ge0` guard column `68` genuinely decides `rDist 0 ≥ 2` — no wraparound — with its 5-bit
range witness (`bits 69..73`) forcing the non-negativity of `2·gpd·(pd−2) + gpd − (pd−2) − 1`. This is
the leg's heart wired to the real object. -/
theorem xdec_gpd_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 68 = 0 ∨ (envAt t i).loc 68 = 1)
    ∧ ((envAt t i).loc 68 = 1 → 2 ≤ (envAt t i).loc (rDist 0))
    ∧ ((envAt t i).loc 68 = 0 → (envAt t i).loc (rDist 0) ≤ 1) := by
  set e := envAt t i with he
  have gpdB : e.loc 68 = 0 ∨ e.loc 68 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 10)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 69 = 0 ∨ e.loc 69 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 11)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 70 = 0 ∨ e.loc 70 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 12)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 71 = 0 ∨ e.loc 71 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 13)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 72 = 0 ∨ e.loc 72 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 14)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 73 = 0 ∨ e.loc 73 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 15)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 11) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 10) ((Head.lin 1 (rDist 0)).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 11) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 10) ((Head.lin 1 (rDist 0)).addConst (-2))))).eval e.loc
      = 2 * (e.loc 68 * e.loc (rDist 0)) + -4 * e.loc 68 + e.loc 68 + -1 * e.loc (rDist 0)
        + -1 * e.loc 69 + -2 * e.loc 70 + -4 * e.loc 71 + -8 * e.loc 72 + -16 * e.loc 73 + 1 from rfl] at grec
  have gmod : (2 * e.loc 68 * (e.loc (rDist 0) - 2) + e.loc 68 - (e.loc (rDist 0) - 2) - 1)
      ≡ (e.loc 69 + 2 * e.loc 70 + 4 * e.loc 71 + 8 * e.loc 72 + 16 * e.loc 73) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := xdec_pd_mem hsat hc i hi
  rw [← he] at pdMem
  have core := forcedGe0_core (D := e.loc (rDist 0) - 2)
    (S := e.loc 69 + 2 * e.loc 70 + 4 * e.loc 71 + 8 * e.loc 72 + 16 * e.loc 73) gpdB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rw [h] <;> norm_num) (by rcases pdMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gpdB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- **Leg (3), case (vacuum, vacuum): `decide_axis` decodes to `.none`.** On a satisfying canonical
trace whose XP/XN rays both read vacuum, the decoded xdec decision IS `evaluateAxis` — both `.none`.
The `assert_case` `(0,0)` gate (selected by the `ipw₀·inw₀` one-hot) forces `variant = 0`. Keyed on
the byte-pinned `automataflStepDesc`; the only extra premises are the ray `what`-codes. -/
theorem decideAxis_xdec_none (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 0) (hnw : (envAt t i).loc (rWhat 1) = 0) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,65,58])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [62,65,58])).eval e.loc = e.loc 62 * e.loc 65 * e.loc 58 from rfl,
     hip0, hin0] at hgv
  have hvar : e.loc 58 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 58) (b := 0) (by ring)).mp hgv)
  rw [hvar, hpw, hnw]
  simp [decodeDecision, codeToParticle, evaluateAxis]

/-- **Leg (3), case (attractor, repulsor): `decide_axis` decodes to `.unbalancedPair`.** On a
satisfying canonical trace whose XP ray reads an attractor and XN a repulsor, the decoded xdec decision
IS `evaluateAxis`: `.unbalancedPair true pd nd` when the guard `pd > 1` holds (`gpd = 1`), else `.none`.
The full pipeline closes — `xdec_gpd_sound` (the `forced_ge0` no-wrap heart) resolves the distance
guard, `xdec_ipw_sel`/`xdec_inw_sel` select the `(2,1)` case, and its four `assert_case` gates force
`variant = 3·gpd`, `pos = gpd`, `att = gpd·pd`, `rep = gpd·nd`. -/
theorem decideAxis_xdec_attRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 2) (hnw : (envAt t i).loc (rWhat 1) = 1) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd0⟩ := xdec_gpd_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 58 + -3 * (e.loc 64 * e.loc 66 * e.loc 68) from rfl,
     hip2, hin1] at hgv
  have hvar : e.loc 58 = 3 * e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := 3 * e.loc 68) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,59]).addProd (-1) [64,66,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,59]).addProd (-1) [64,66,68])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 59 + -1 * (e.loc 64 * e.loc 66 * e.loc 68) from rfl,
     hip2, hin1] at hgp
  have hpos : e.loc 59 = e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 59) (b := e.loc 68) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,60]).addProd (-1) [64,66,68, rDist 0])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,60]).addProd (-1) [64,66,68, rDist 0])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 60 + -1 * (e.loc 64 * e.loc 66 * e.loc 68 * e.loc (rDist 0)) from rfl,
     hip2, hin1] at hga
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,61]).addProd (-1) [64,66,68, rDist 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,61]).addProd (-1) [64,66,68, rDist 1])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 61 + -1 * (e.loc 64 * e.loc 66 * e.loc 68 * e.loc (rDist 1)) from rfl,
     hip2, hin1] at hgr
  have hatt : e.loc 60 = e.loc 68 * e.loc (rDist 0) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 60) (b := e.loc 68 * e.loc (rDist 0)) (by ring)).mp hga)
  have hrep : e.loc 61 = e.loc 68 * e.loc (rDist 1) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases xdec_nd_mem hsat hc i hi with hp|hp <;>
          rw [← he] at hp <;> rw [hp] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 61) (b := e.loc 68 * e.loc (rDist 1)) (by ring)).mp hgr)
  rw [hpw, hnw]
  rcases gpdB with hg0 | hg1
  · have hpd1 : e.loc (rDist 0) = 1 := by have := gpd0 hg0; rcases pdMem with h|h <;> omega
    have hv0 : e.loc 58 = 0 := by rw [hvar, hg0]; ring
    rw [hv0, hpd1]
    simp [decodeDecision, codeToParticle, evaluateAxis]
  · have hpd2 : e.loc (rDist 0) = 2 := by have := gpd1 hg1; rcases pdMem with h|h <;> omega
    have hv3 : e.loc 58 = 3 := by rw [hvar, hg1]; ring
    have hp1 : e.loc 59 = 1 := by rw [hpos, hg1]
    have hattv : e.loc 60 = e.loc (rDist 0) := by rw [hatt, hg1]; ring
    have hrepv : e.loc 61 = e.loc (rDist 1) := by rw [hrep, hg1]; ring
    rw [hv3, hp1, hattv, hrepv, hpd2]
    simp [decodeDecision, codeToParticle, evaluateAxis]

end DecideXdec


section DecideXdecRest
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The `gnd = [nd ≥ 2]` guard bit (col 74) genuinely decides `rDist 1 ≥ 2` (no wrap). -/
theorem xdec_gnd_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 74 = 0 ∨ (envAt t i).loc 74 = 1)
    ∧ ((envAt t i).loc 74 = 1 → 2 ≤ (envAt t i).loc (rDist 1))
    ∧ ((envAt t i).loc 74 = 0 → (envAt t i).loc (rDist 1) ≤ 1) := by
  set e := envAt t i with he
  have gndB : e.loc 74 = 0 ∨ e.loc 74 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 16)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 75 = 0 ∨ e.loc 75 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 17)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 76 = 0 ∨ e.loc 76 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 18)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 77 = 0 ∨ e.loc 77 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 19)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 78 = 0 ∨ e.loc 78 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 20)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 79 = 0 ∨ e.loc 79 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 21)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 17) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 16) ((Head.lin 1 (rDist 1)).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 17) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 16) ((Head.lin 1 (rDist 1)).addConst (-2))))).eval e.loc
      = 2 * (e.loc 74 * e.loc (rDist 1)) + -4 * e.loc 74 + e.loc 74 + -1 * e.loc (rDist 1)
        + -1 * e.loc 75 + -2 * e.loc 76 + -4 * e.loc 77 + -8 * e.loc 78 + -16 * e.loc 79 + 1 from rfl] at grec
  have gmod : (2 * e.loc 74 * (e.loc (rDist 1) - 2) + e.loc 74 - (e.loc (rDist 1) - 2) - 1)
      ≡ (e.loc 75 + 2 * e.loc 76 + 4 * e.loc 77 + 8 * e.loc 78 + 16 * e.loc 79) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at ndMem
  have core := forcedGe0_core (D := e.loc (rDist 1) - 2)
    (S := e.loc 75 + 2 * e.loc 76 + 4 * e.loc 77 + 8 * e.loc 78 + 16 * e.loc 79) gndB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases ndMem with h|h <;> rw [h] <;> norm_num) (by rcases ndMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gndB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The `lt = [pd < nd]` compare bit (col 80). -/
theorem xdec_lt_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 80 = 0 ∨ (envAt t i).loc 80 = 1)
    ∧ ((envAt t i).loc 80 = 1 → (envAt t i).loc (rDist 0) < (envAt t i).loc (rDist 1))
    ∧ ((envAt t i).loc 80 = 0 → (envAt t i).loc (rDist 1) ≤ (envAt t i).loc (rDist 0)) := by
  set e := envAt t i with he
  have ltB : e.loc 80 = 0 ∨ e.loc 80 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 22)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 81 = 0 ∨ e.loc 81 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 23)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 82 = 0 ∨ e.loc 82 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 24)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 83 = 0 ∨ e.loc 83 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 25)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 84 = 0 ∨ e.loc 84 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 26)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 85 = 0 ∨ e.loc 85 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 27)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 23) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 22) (((Head.lin 1 (rDist 1)).addLin (-1) (rDist 0)).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 23) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 22) (((Head.lin 1 (rDist 1)).addLin (-1) (rDist 0)).addConst (-1))))).eval e.loc
      = 2 * (e.loc 80 * e.loc (rDist 1)) + -2 * (e.loc 80 * e.loc (rDist 0)) + -2 * e.loc 80 + e.loc 80
        + -1 * e.loc (rDist 1) + e.loc (rDist 0)
        + -1 * e.loc 81 + -2 * e.loc 82 + -4 * e.loc 83 + -8 * e.loc 84 + -16 * e.loc 85 from rfl] at grec
  have gmod : (2 * e.loc 80 * (e.loc (rDist 1) - e.loc (rDist 0) - 1) + e.loc 80
        - (e.loc (rDist 1) - e.loc (rDist 0) - 1) - 1)
      ≡ (e.loc 81 + 2 * e.loc 82 + 4 * e.loc 83 + 8 * e.loc 84 + 16 * e.loc 85) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have core := forcedGe0_core (D := e.loc (rDist 1) - e.loc (rDist 0) - 1)
    (S := e.loc 81 + 2 * e.loc 82 + 4 * e.loc 83 + 8 * e.loc 84 + 16 * e.loc 85) ltB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨ltB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The `gt = [pd > nd]` compare bit (col 86). -/
theorem xdec_gt_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 86 = 0 ∨ (envAt t i).loc 86 = 1)
    ∧ ((envAt t i).loc 86 = 1 → (envAt t i).loc (rDist 1) < (envAt t i).loc (rDist 0))
    ∧ ((envAt t i).loc 86 = 0 → (envAt t i).loc (rDist 0) ≤ (envAt t i).loc (rDist 1)) := by
  set e := envAt t i with he
  have gtB : e.loc 86 = 0 ∨ e.loc 86 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 28)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 87 = 0 ∨ e.loc 87 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 29)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 88 = 0 ∨ e.loc 88 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 30)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 89 = 0 ∨ e.loc 89 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 31)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 90 = 0 ∨ e.loc 90 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 32)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 91 = 0 ∨ e.loc 91 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 33)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 29) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 28) (((Head.lin 1 (rDist 0)).addLin (-1) (rDist 1)).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 29) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 28) (((Head.lin 1 (rDist 0)).addLin (-1) (rDist 1)).addConst (-1))))).eval e.loc
      = 2 * (e.loc 86 * e.loc (rDist 0)) + -2 * (e.loc 86 * e.loc (rDist 1)) + -2 * e.loc 86 + e.loc 86
        + -1 * e.loc (rDist 0) + e.loc (rDist 1)
        + -1 * e.loc 87 + -2 * e.loc 88 + -4 * e.loc 89 + -8 * e.loc 90 + -16 * e.loc 91 from rfl] at grec
  have gmod : (2 * e.loc 86 * (e.loc (rDist 0) - e.loc (rDist 1) - 1) + e.loc 86
        - (e.loc (rDist 0) - e.loc (rDist 1) - 1) - 1)
      ≡ (e.loc 87 + 2 * e.loc 88 + 4 * e.loc 89 + 8 * e.loc 90 + 16 * e.loc 91) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have core := forcedGe0_core (D := e.loc (rDist 0) - e.loc (rDist 1) - 1)
    (S := e.loc 87 + 2 * e.loc 88 + 4 * e.loc 89 + 8 * e.loc 90 + 16 * e.loc 91) gtB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨gtB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The `le = [pd ≤ nd]` compare bit (col 92). -/
theorem xdec_le_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 92 = 0 ∨ (envAt t i).loc 92 = 1)
    ∧ ((envAt t i).loc 92 = 1 → (envAt t i).loc (rDist 0) ≤ (envAt t i).loc (rDist 1))
    ∧ ((envAt t i).loc 92 = 0 → (envAt t i).loc (rDist 1) < (envAt t i).loc (rDist 0)) := by
  set e := envAt t i with he
  have leB : e.loc 92 = 0 ∨ e.loc 92 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 34)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 93 = 0 ∨ e.loc 93 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 35)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 94 = 0 ∨ e.loc 94 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 36)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 95 = 0 ∨ e.loc 95 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 37)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 96 = 0 ∨ e.loc 96 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 38)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 97 = 0 ∨ e.loc 97 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 39)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 35) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 34) ((Head.lin 1 (rDist 1)).addLin (-1) (rDist 0))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 35) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 34) ((Head.lin 1 (rDist 1)).addLin (-1) (rDist 0))))).eval e.loc
      = 2 * (e.loc 92 * e.loc (rDist 1)) + -2 * (e.loc 92 * e.loc (rDist 0)) + e.loc 92
        + -1 * e.loc (rDist 1) + e.loc (rDist 0)
        + -1 * e.loc 93 + -2 * e.loc 94 + -4 * e.loc 95 + -8 * e.loc 96 + -16 * e.loc 97 + -1 from rfl] at grec
  have gmod : (2 * e.loc 92 * (e.loc (rDist 1) - e.loc (rDist 0)) + e.loc 92
        - (e.loc (rDist 1) - e.loc (rDist 0)) - 1)
      ≡ (e.loc 93 + 2 * e.loc 94 + 4 * e.loc 95 + 8 * e.loc 96 + 16 * e.loc 97) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have core := forcedGe0_core (D := e.loc (rDist 1) - e.loc (rDist 0))
    (S := e.loc 93 + 2 * e.loc 94 + 4 * e.loc 95 + 8 * e.loc 96 + 16 * e.loc 97) leB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨leB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The `min` gadget value (col 98) `= le·pd + nd − le·nd = min(pd, nd)`. -/
theorem xdec_min_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 98
      = (envAt t i).loc 92 * (envAt t i).loc (rDist 0) + (envAt t i).loc (rDist 1)
        - (envAt t i).loc 92 * (envAt t i).loc (rDist 1) := by
  set e := envAt t i with he
  obtain ⟨leB, _, _⟩ := xdec_le_sound hsat hc i hi
  rw [← he] at leB
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have hg := astep_gate hsat i hi
    (g := headToExpr ((((Head.lin 1 98).addProd (-1) [92, rDist 0]).addLin (-1) (rDist 1)).addProd 1 [92, rDist 1])) (by decide)
  rw [show (headToExpr ((((Head.lin 1 98).addProd (-1) [92, rDist 0]).addLin (-1) (rDist 1)).addProd 1 [92, rDist 1])).eval e.loc
      = e.loc 98 + -1 * (e.loc 92 * e.loc (rDist 0)) + -1 * e.loc (rDist 1) + e.loc 92 * e.loc (rDist 1) from rfl] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_
    ((gate_modEq_iff (a := e.loc 98)
      (b := e.loc 92 * e.loc (rDist 0) + e.loc (rDist 1) - e.loc 92 * e.loc (rDist 1)) (by ring)).mp hg)
  rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
    rw [h, hp, hn] <;> exact ⟨by norm_num, by norm_num⟩

/-- The `gm = [min ≥ 2]` guard bit (col 99). -/
theorem xdec_gm_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 99 = 0 ∨ (envAt t i).loc 99 = 1)
    ∧ ((envAt t i).loc 99 = 1 → 2 ≤ (envAt t i).loc 98)
    ∧ ((envAt t i).loc 99 = 0 → (envAt t i).loc 98 ≤ 1) := by
  set e := envAt t i with he
  have hmin := xdec_min_sound hsat hc i hi
  rw [← he] at hmin
  obtain ⟨leB, _, _⟩ := xdec_le_sound hsat hc i hi
  rw [← he] at leB
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have minMem : e.loc 98 = 1 ∨ e.loc 98 = 2 := by
    rw [hmin]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  have gmB : e.loc 99 = 0 ∨ e.loc 99 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 41)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 100 = 0 ∨ e.loc 100 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 42)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 101 = 0 ∨ e.loc 101 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 43)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 102 = 0 ∨ e.loc 102 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 44)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 103 = 0 ∨ e.loc 103 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 45)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 104 = 0 ∨ e.loc 104 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 46)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 42) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 41) ((Head.lin 1 98).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 42) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 41) ((Head.lin 1 98).addConst (-2))))).eval e.loc
      = 2 * (e.loc 99 * e.loc 98) + -4 * e.loc 99 + e.loc 99 + -1 * e.loc 98
        + -1 * e.loc 100 + -2 * e.loc 101 + -4 * e.loc 102 + -8 * e.loc 103 + -16 * e.loc 104 + 1 from rfl] at grec
  have gmod : (2 * e.loc 99 * (e.loc 98 - 2) + e.loc 99 - (e.loc 98 - 2) - 1)
      ≡ (e.loc 100 + 2 * e.loc 101 + 4 * e.loc 102 + 8 * e.loc 103 + 16 * e.loc 104) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have core := forcedGe0_core (D := e.loc 98 - 2)
    (S := e.loc 100 + 2 * e.loc 101 + 4 * e.loc 102 + 8 * e.loc 103 + 16 * e.loc 104) gmB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases minMem with h|h <;> rw [h] <;> norm_num) (by rcases minMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gmB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

end DecideXdecRest

/-! ### Pure, axis-independent decode lemmas (decode = evaluateAxis given field values + guards). -/

theorem decode_vacVac {pd nd v pos att rep : ℤ}
    (hv : v = 0) (hpos : pos = 0) (hatt : att = 0) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .vacuum, dist := pd.toNat } { what := .vacuum, dist := nd.toNat } := by
  subst hv hpos hatt hrep
  simp [decodeDecision, evaluateAxis]

theorem decode_attRep {pd nd gpd v pos att rep : ℤ}
    (hpd : pd = 1 ∨ pd = 2)
    (hg0 : gpd = 0 ∨ gpd = 1) (hg1 : gpd = 1 → 2 ≤ pd) (hg2 : gpd = 0 → pd ≤ 1)
    (hv : v = 3 * gpd) (hpos : pos = gpd) (hatt : att = gpd * pd) (hrep : rep = gpd * nd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .attractor, dist := pd.toNat } { what := .repulsor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg
  · have hpd1 : pd = 1 := by rcases hpd with h | h <;> [exact h; (exfalso; have := hg2 rfl; omega)]
    subst hpd1; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hpd2 : pd = 2 := by rcases hpd with h | h <;> [(exfalso; have := hg1 rfl; omega); exact h]
    subst hpd2; simp only [hv, hpos, hatt, hrep]; norm_num [decodeDecision, evaluateAxis]

theorem decode_repAtt {pd nd gnd v pos att rep : ℤ}
    (hnd : nd = 1 ∨ nd = 2)
    (hg0 : gnd = 0 ∨ gnd = 1) (hg1 : gnd = 1 → 2 ≤ nd) (hg2 : gnd = 0 → nd ≤ 1)
    (hv : v = 3 * gnd) (hpos : pos = 0) (hatt : att = gnd * nd) (hrep : rep = gnd * pd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .repulsor, dist := pd.toNat } { what := .attractor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg
  · have hnd1 : nd = 1 := by rcases hnd with h | h <;> [exact h; (exfalso; have := hg2 rfl; omega)]
    subst hnd1; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hnd2 : nd = 2 := by rcases hnd with h | h <;> [(exfalso; have := hg1 rfl; omega); exact h]
    subst hnd2; simp only [hv, hpos, hatt, hrep]; norm_num [decodeDecision, evaluateAxis]

theorem decode_repVac {pd nd gnd v pos att rep : ℤ}
    (hnd : nd = 1 ∨ nd = 2)
    (hg0 : gnd = 0 ∨ gnd = 1) (hg1 : gnd = 1 → 2 ≤ nd) (hg2 : gnd = 0 → nd ≤ 1)
    (hv : v = 2 * gnd) (hpos : pos = 0) (hatt : att = 0) (hrep : rep = gnd * pd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .repulsor, dist := pd.toNat } { what := .vacuum, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg
  · have hnd1 : nd = 1 := by rcases hnd with h | h <;> [exact h; (exfalso; have := hg2 rfl; omega)]
    subst hnd1; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hnd2 : nd = 2 := by rcases hnd with h | h <;> [(exfalso; have := hg1 rfl; omega); exact h]
    subst hnd2; simp only [hv, hpos, hatt, hrep]; norm_num [decodeDecision, evaluateAxis]

theorem decode_vacRep {pd nd gpd v pos att rep : ℤ}
    (hpd : pd = 1 ∨ pd = 2)
    (hg0 : gpd = 0 ∨ gpd = 1) (hg1 : gpd = 1 → 2 ≤ pd) (hg2 : gpd = 0 → pd ≤ 1)
    (hv : v = 2 * gpd) (hpos : pos = gpd) (hatt : att = 0) (hrep : rep = gpd * nd) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .vacuum, dist := pd.toNat } { what := .repulsor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg
  · have hpd1 : pd = 1 := by rcases hpd with h | h <;> [exact h; (exfalso; have := hg2 rfl; omega)]
    subst hpd1; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hpd2 : pd = 2 := by rcases hpd with h | h <;> [(exfalso; have := hg1 rfl; omega); exact h]
    subst hpd2; simp only [hv, hpos, hatt, hrep]; norm_num [decodeDecision, evaluateAxis]

theorem decode_attVac {pd nd gpd v pos att rep : ℤ}
    (hpd : pd = 1 ∨ pd = 2)
    (hg0 : gpd = 0 ∨ gpd = 1) (hg1 : gpd = 1 → 2 ≤ pd) (hg2 : gpd = 0 → pd ≤ 1)
    (hv : v = gpd) (hpos : pos = gpd) (hatt : att = gpd * pd) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .attractor, dist := pd.toNat } { what := .vacuum, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg
  · have hpd1 : pd = 1 := by rcases hpd with h | h <;> [exact h; (exfalso; have := hg2 rfl; omega)]
    subst hpd1; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hpd2 : pd = 2 := by rcases hpd with h | h <;> [(exfalso; have := hg1 rfl; omega); exact h]
    subst hpd2; simp only [hv, hpos, hatt, hrep]; norm_num [decodeDecision, evaluateAxis]

theorem decode_vacAtt {pd nd gnd v pos att rep : ℤ}
    (hnd : nd = 1 ∨ nd = 2)
    (hg0 : gnd = 0 ∨ gnd = 1) (hg1 : gnd = 1 → 2 ≤ nd) (hg2 : gnd = 0 → nd ≤ 1)
    (hv : v = gnd) (hpos : pos = 0) (hatt : att = gnd * nd) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .vacuum, dist := pd.toNat } { what := .attractor, dist := nd.toNat } := by
  rcases hg0 with hg | hg <;> subst hg
  · have hnd1 : nd = 1 := by rcases hnd with h | h <;> [exact h; (exfalso; have := hg2 rfl; omega)]
    subst hnd1; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hnd2 : nd = 2 := by rcases hnd with h | h <;> [(exfalso; have := hg1 rfl; omega); exact h]
    subst hnd2; simp only [hv, hpos, hatt, hrep]; norm_num [decodeDecision, evaluateAxis]

theorem decode_repRep {pd nd le lt gt minv v pos att rep : ℤ}
    (hpd : pd = 1 ∨ pd = 2) (hnd : nd = 1 ∨ nd = 2)
    (hlt0 : lt = 0 ∨ lt = 1) (hlt1 : lt = 1 → pd < nd) (hlt2 : lt = 0 → nd ≤ pd)
    (hgt0 : gt = 0 ∨ gt = 1) (hgt1 : gt = 1 → nd < pd) (hgt2 : gt = 0 → pd ≤ nd)
    (hle0 : le = 0 ∨ le = 1) (hle1 : le = 1 → pd ≤ nd) (hle2 : le = 0 → nd < pd)
    (hminv : minv = le * pd + nd - le * nd)
    (hv : v = 2 * lt + 2 * gt) (hpos : pos = gt) (hatt : att = 0)
    (hrep : rep = lt * minv + gt * minv) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .repulsor, dist := pd.toNat } { what := .repulsor, dist := nd.toNat } := by
  rcases hpd with rfl | rfl <;> rcases hnd with rfl | rfl
  · have hltv : lt = 0 := by rcases hlt0 with h | h <;> [exact h; (exfalso; have := hlt1 h; omega)]
    have hgtv : gt = 0 := by rcases hgt0 with h | h <;> [exact h; (exfalso; have := hgt1 h; omega)]
    subst hltv hgtv; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hltv : lt = 1 := by rcases hlt0 with h | h <;> [(exfalso; have := hlt2 h; omega); exact h]
    have hgtv : gt = 0 := by rcases hgt0 with h | h <;> [exact h; (exfalso; have := hgt1 h; omega)]
    have hlev : le = 1 := by rcases hle0 with h | h <;> [(exfalso; have := hle2 h; omega); exact h]
    have hmv : minv = 1 := by rw [hminv, hlev]; ring
    subst hltv hgtv; rw [hmv] at hrep
    simp only [hv, hpos, hatt, hrep]
    rw [show (1:ℤ).toNat = 1 from rfl, show (2:ℤ).toNat = 2 from rfl]
    norm_num [decodeDecision, evaluateAxis]
  · have hltv : lt = 0 := by rcases hlt0 with h | h <;> [exact h; (exfalso; have := hlt1 h; omega)]
    have hgtv : gt = 1 := by rcases hgt0 with h | h <;> [(exfalso; have := hgt2 h; omega); exact h]
    have hlev : le = 0 := by rcases hle0 with h | h <;> [exact h; (exfalso; have := hle1 h; omega)]
    have hmv : minv = 1 := by rw [hminv, hlev]; ring
    subst hltv hgtv; rw [hmv] at hrep
    simp only [hv, hpos, hatt, hrep]
    rw [show (1:ℤ).toNat = 1 from rfl, show (2:ℤ).toNat = 2 from rfl]
    norm_num [decodeDecision, evaluateAxis]
  · have hltv : lt = 0 := by rcases hlt0 with h | h <;> [exact h; (exfalso; have := hlt1 h; omega)]
    have hgtv : gt = 0 := by rcases hgt0 with h | h <;> [exact h; (exfalso; have := hgt1 h; omega)]
    subst hltv hgtv; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]

theorem decode_attAtt {pd nd le lt gt gm minv v pos att rep : ℤ}
    (hpd : pd = 1 ∨ pd = 2) (hnd : nd = 1 ∨ nd = 2)
    (hlt0 : lt = 0 ∨ lt = 1) (hlt1 : lt = 1 → pd < nd) (hlt2 : lt = 0 → nd ≤ pd)
    (hgt0 : gt = 0 ∨ gt = 1) (hgt1 : gt = 1 → nd < pd) (hgt2 : gt = 0 → pd ≤ nd)
    (hle0 : le = 0 ∨ le = 1) (hle1 : le = 1 → pd ≤ nd) (hle2 : le = 0 → nd < pd)
    (hgm0 : gm = 0 ∨ gm = 1) (hgm1 : gm = 1 → 2 ≤ minv) (hgm2 : gm = 0 → minv ≤ 1)
    (hminv : minv = le * pd + nd - le * nd)
    (hv : v = lt * gm + gt * gm) (hpos : pos = lt * gm)
    (hatt : att = lt * gm * minv + gt * gm * minv) (hrep : rep = 0) :
    decodeDecision v pos att rep
      = evaluateAxis { what := .attractor, dist := pd.toNat } { what := .attractor, dist := nd.toNat } := by
  rcases hpd with rfl | rfl <;> rcases hnd with rfl | rfl
  · have hltv : lt = 0 := by rcases hlt0 with h | h <;> [exact h; (exfalso; have := hlt1 h; omega)]
    have hgtv : gt = 0 := by rcases hgt0 with h | h <;> [exact h; (exfalso; have := hgt1 h; omega)]
    subst hltv hgtv; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hlev : le = 1 := by rcases hle0 with h | h <;> [(exfalso; have := hle2 h; omega); exact h]
    have hmv : minv = 1 := by rw [hminv, hlev]; ring
    have hgmv : gm = 0 := by rcases hgm0 with h | h <;> [exact h; (exfalso; have := hgm1 h; omega)]
    subst hgmv; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hlev : le = 0 := by rcases hle0 with h | h <;> [exact h; (exfalso; have := hle1 h; omega)]
    have hmv : minv = 1 := by rw [hminv, hlev]; ring
    have hgmv : gm = 0 := by rcases hgm0 with h | h <;> [exact h; (exfalso; have := hgm1 h; omega)]
    subst hgmv; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]
  · have hltv : lt = 0 := by rcases hlt0 with h | h <;> [exact h; (exfalso; have := hlt1 h; omega)]
    have hgtv : gt = 0 := by rcases hgt0 with h | h <;> [exact h; (exfalso; have := hgt1 h; omega)]
    subst hltv hgtv; simp only [hv, hpos, hatt, hrep]; simp [decodeDecision, evaluateAxis]

/-! ### The other seven xdec cases (extraction ▸ pure decode). -/

section DecideXdecCases
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

theorem decideAxis_xdec_repAtt (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 1) (hnw : (envAt t i).loc (rWhat 1) = 2) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gndB, gnd1, gnd2⟩ := xdec_gnd_sound hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip1 : e.loc 63 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin2 : e.loc 67 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [63,67,58]).addProd (-3) [63,67,74])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [63,67,58]).addProd (-3) [63,67,74])).eval e.loc
      = e.loc 63 * e.loc 67 * e.loc 58 + -3 * (e.loc 63 * e.loc 67 * e.loc 74) from rfl, hip1, hin2] at hgv
  have hvar : e.loc 58 = 3 * e.loc 74 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := 3 * e.loc 74) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [63,67,59])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [63,67,59])).eval e.loc = e.loc 63 * e.loc 67 * e.loc 59 from rfl,
     hip1, hin2] at hgp
  have hpos : e.loc 59 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 59) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [63,67,60]).addProd (-1) [63,67,74, rDist 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [63,67,60]).addProd (-1) [63,67,74, rDist 1])).eval e.loc
      = e.loc 63 * e.loc 67 * e.loc 60 + -1 * (e.loc 63 * e.loc 67 * e.loc 74 * e.loc (rDist 1)) from rfl,
     hip1, hin2] at hga
  have hatt : e.loc 60 = e.loc 74 * e.loc (rDist 1) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 60) (b := e.loc 74 * e.loc (rDist 1)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [63,67,61]).addProd (-1) [63,67,74, rDist 0])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [63,67,61]).addProd (-1) [63,67,74, rDist 0])).eval e.loc
      = e.loc 63 * e.loc 67 * e.loc 61 + -1 * (e.loc 63 * e.loc 67 * e.loc 74 * e.loc (rDist 0)) from rfl,
     hip1, hin2] at hgr
  have hrep : e.loc 61 = e.loc 74 * e.loc (rDist 0) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases xdec_pd_mem hsat hc i hi with hp|hp <;>
          rw [← he] at hp <;> rw [hp] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 61) (b := e.loc 74 * e.loc (rDist 0)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_repAtt ndMem gndB gnd1 gnd2 hvar hpos hatt hrep

theorem decideAxis_xdec_repVac (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 1) (hnw : (envAt t i).loc (rWhat 1) = 0) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gndB, gnd1, gnd2⟩ := xdec_gnd_sound hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip1 : e.loc 63 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [63,65,58]).addProd (-2) [63,65,74])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [63,65,58]).addProd (-2) [63,65,74])).eval e.loc
      = e.loc 63 * e.loc 65 * e.loc 58 + -2 * (e.loc 63 * e.loc 65 * e.loc 74) from rfl, hip1, hin0] at hgv
  have hvar : e.loc 58 = 2 * e.loc 74 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := 2 * e.loc 74) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [63,65,59])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [63,65,59])).eval e.loc = e.loc 63 * e.loc 65 * e.loc 59 from rfl,
     hip1, hin0] at hgp
  have hpos : e.loc 59 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 59) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [63,65,60])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [63,65,60])).eval e.loc = e.loc 63 * e.loc 65 * e.loc 60 from rfl,
     hip1, hin0] at hga
  have hatt : e.loc 60 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [63,65,61]).addProd (-1) [63,65,74, rDist 0])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [63,65,61]).addProd (-1) [63,65,74, rDist 0])).eval e.loc
      = e.loc 63 * e.loc 65 * e.loc 61 + -1 * (e.loc 63 * e.loc 65 * e.loc 74 * e.loc (rDist 0)) from rfl,
     hip1, hin0] at hgr
  have hrep : e.loc 61 = e.loc 74 * e.loc (rDist 0) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 61) (b := e.loc 74 * e.loc (rDist 0)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_repVac ndMem gndB gnd1 gnd2 hvar hpos hatt hrep

theorem decideAxis_xdec_vacRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 0) (hnw : (envAt t i).loc (rWhat 1) = 1) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd2⟩ := xdec_gpd_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [62,66,58]).addProd (-2) [62,66,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [62,66,58]).addProd (-2) [62,66,68])).eval e.loc
      = e.loc 62 * e.loc 66 * e.loc 58 + -2 * (e.loc 62 * e.loc 66 * e.loc 68) from rfl, hip0, hin1] at hgv
  have hvar : e.loc 58 = 2 * e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := 2 * e.loc 68) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [62,66,59]).addProd (-1) [62,66,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [62,66,59]).addProd (-1) [62,66,68])).eval e.loc
      = e.loc 62 * e.loc 66 * e.loc 59 + -1 * (e.loc 62 * e.loc 66 * e.loc 68) from rfl, hip0, hin1] at hgp
  have hpos : e.loc 59 = e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 59) (b := e.loc 68) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,66,60])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [62,66,60])).eval e.loc = e.loc 62 * e.loc 66 * e.loc 60 from rfl,
     hip0, hin1] at hga
  have hatt : e.loc 60 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [62,66,61]).addProd (-1) [62,66,68, rDist 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [62,66,61]).addProd (-1) [62,66,68, rDist 1])).eval e.loc
      = e.loc 62 * e.loc 66 * e.loc 61 + -1 * (e.loc 62 * e.loc 66 * e.loc 68 * e.loc (rDist 1)) from rfl,
     hip0, hin1] at hgr
  have hrep : e.loc 61 = e.loc 68 * e.loc (rDist 1) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 61) (b := e.loc 68 * e.loc (rDist 1)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_vacRep pdMem gpdB gpd1 gpd2 hvar hpos hatt hrep

theorem decideAxis_xdec_attVac (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 2) (hnw : (envAt t i).loc (rWhat 1) = 0) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd2⟩ := xdec_gpd_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,65,58]).addProd (-1) [64,65,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,65,58]).addProd (-1) [64,65,68])).eval e.loc
      = e.loc 64 * e.loc 65 * e.loc 58 + -1 * (e.loc 64 * e.loc 65 * e.loc 68) from rfl, hip2, hin0] at hgv
  have hvar : e.loc 58 = e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 58) (b := e.loc 68) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,65,59]).addProd (-1) [64,65,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,65,59]).addProd (-1) [64,65,68])).eval e.loc
      = e.loc 64 * e.loc 65 * e.loc 59 + -1 * (e.loc 64 * e.loc 65 * e.loc 68) from rfl, hip2, hin0] at hgp
  have hpos : e.loc 59 = e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 59) (b := e.loc 68) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,65,60]).addProd (-1) [64,65,68, rDist 0])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,65,60]).addProd (-1) [64,65,68, rDist 0])).eval e.loc
      = e.loc 64 * e.loc 65 * e.loc 60 + -1 * (e.loc 64 * e.loc 65 * e.loc 68 * e.loc (rDist 0)) from rfl,
     hip2, hin0] at hga
  have hatt : e.loc 60 = e.loc 68 * e.loc (rDist 0) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 60) (b := e.loc 68 * e.loc (rDist 0)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [64,65,61])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [64,65,61])).eval e.loc = e.loc 64 * e.loc 65 * e.loc 61 from rfl,
     hip2, hin0] at hgr
  have hrep : e.loc 61 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_attVac pdMem gpdB gpd1 gpd2 hvar hpos hatt hrep

theorem decideAxis_xdec_vacAtt (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 0) (hnw : (envAt t i).loc (rWhat 1) = 2) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gndB, gnd1, gnd2⟩ := xdec_gnd_sound hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin2 : e.loc 67 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [62,67,58]).addProd (-1) [62,67,74])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [62,67,58]).addProd (-1) [62,67,74])).eval e.loc
      = e.loc 62 * e.loc 67 * e.loc 58 + -1 * (e.loc 62 * e.loc 67 * e.loc 74) from rfl, hip0, hin2] at hgv
  have hvar : e.loc 58 = e.loc 74 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 58) (b := e.loc 74) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,67,59])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [62,67,59])).eval e.loc = e.loc 62 * e.loc 67 * e.loc 59 from rfl,
     hip0, hin2] at hgp
  have hpos : e.loc 59 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 59) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [62,67,60]).addProd (-1) [62,67,74, rDist 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [62,67,60]).addProd (-1) [62,67,74, rDist 1])).eval e.loc
      = e.loc 62 * e.loc 67 * e.loc 60 + -1 * (e.loc 62 * e.loc 67 * e.loc 74 * e.loc (rDist 1)) from rfl,
     hip0, hin2] at hga
  have hatt : e.loc 60 = e.loc 74 * e.loc (rDist 1) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 60) (b := e.loc 74 * e.loc (rDist 1)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,67,61])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [62,67,61])).eval e.loc = e.loc 62 * e.loc 67 * e.loc 61 from rfl,
     hip0, hin2] at hgr
  have hrep : e.loc 61 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_vacAtt ndMem gndB gnd1 gnd2 hvar hpos hatt hrep

theorem decideAxis_xdec_repRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 1) (hnw : (envAt t i).loc (rWhat 1) = 1) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨ltB, lt1, lt2⟩ := xdec_lt_sound hsat hc i hi
  obtain ⟨gtB, gt1, gt2⟩ := xdec_gt_sound hsat hc i hi
  obtain ⟨leB, le1, le2⟩ := xdec_le_sound hsat hc i hi
  have hmineq := xdec_min_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip1 : e.loc 63 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have minMem : e.loc 98 = 1 ∨ e.loc 98 = 2 := by
    rw [hmineq]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  have hgv := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [63,66,58]).addProd (-2) [63,66,80]).addProd (-2) [63,66,86])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [63,66,58]).addProd (-2) [63,66,80]).addProd (-2) [63,66,86])).eval e.loc
      = e.loc 63 * e.loc 66 * e.loc 58 + -2 * (e.loc 63 * e.loc 66 * e.loc 80)
        + -2 * (e.loc 63 * e.loc 66 * e.loc 86) from rfl, hip1, hin1] at hgv
  have hvar : e.loc 58 = 2 * e.loc 80 + 2 * e.loc 86 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := 2 * e.loc 80 + 2 * e.loc 86) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [63,66,59]).addProd (-1) [63,66,86])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [63,66,59]).addProd (-1) [63,66,86])).eval e.loc
      = e.loc 63 * e.loc 66 * e.loc 59 + -1 * (e.loc 63 * e.loc 66 * e.loc 86) from rfl, hip1, hin1] at hgp
  have hpos : e.loc 59 = e.loc 86 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 59) (b := e.loc 86) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [63,66,60])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [63,66,60])).eval e.loc = e.loc 63 * e.loc 66 * e.loc 60 from rfl,
     hip1, hin1] at hga
  have hatt : e.loc 60 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [63,66,61]).addProd (-1) [63,66,80,98]).addProd (-1) [63,66,86,98])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [63,66,61]).addProd (-1) [63,66,80,98]).addProd (-1) [63,66,86,98])).eval e.loc
      = e.loc 63 * e.loc 66 * e.loc 61 + -1 * (e.loc 63 * e.loc 66 * e.loc 80 * e.loc 98)
        + -1 * (e.loc 63 * e.loc 66 * e.loc 86 * e.loc 98) from rfl, hip1, hin1] at hgr
  have hrep : e.loc 61 = e.loc 80 * e.loc 98 + e.loc 86 * e.loc 98 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases minMem with hm|hm <;>
          rw [h,h',hm] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 61) (b := e.loc 80 * e.loc 98 + e.loc 86 * e.loc 98) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_repRep pdMem ndMem ltB lt1 lt2 gtB gt1 gt2 leB le1 le2 hmineq hvar hpos hatt hrep

theorem decideAxis_xdec_attAtt (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 2) (hnw : (envAt t i).loc (rWhat 1) = 2) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨ltB, lt1, lt2⟩ := xdec_lt_sound hsat hc i hi
  obtain ⟨gtB, gt1, gt2⟩ := xdec_gt_sound hsat hc i hi
  obtain ⟨leB, le1, le2⟩ := xdec_le_sound hsat hc i hi
  obtain ⟨gmB, gm1, gm2⟩ := xdec_gm_sound hsat hc i hi
  have hmineq := xdec_min_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin2 : e.loc 67 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have minMem : e.loc 98 = 1 ∨ e.loc 98 = 2 := by
    rw [hmineq]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  have hgv := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [64,67,58]).addProd (-1) [64,67,80,99]).addProd (-1) [64,67,86,99])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [64,67,58]).addProd (-1) [64,67,80,99]).addProd (-1) [64,67,86,99])).eval e.loc
      = e.loc 64 * e.loc 67 * e.loc 58 + -1 * (e.loc 64 * e.loc 67 * e.loc 80 * e.loc 99)
        + -1 * (e.loc 64 * e.loc 67 * e.loc 86 * e.loc 99) from rfl, hip2, hin2] at hgv
  have hvar : e.loc 58 = e.loc 80 * e.loc 99 + e.loc 86 * e.loc 99 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg|hg <;>
          rw [h,h',hg] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := e.loc 80 * e.loc 99 + e.loc 86 * e.loc 99) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,67,59]).addProd (-1) [64,67,80,99])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,67,59]).addProd (-1) [64,67,80,99])).eval e.loc
      = e.loc 64 * e.loc 67 * e.loc 59 + -1 * (e.loc 64 * e.loc 67 * e.loc 80 * e.loc 99) from rfl, hip2, hin2] at hgp
  have hpos : e.loc 59 = e.loc 80 * e.loc 99 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gmB with hg|hg <;> rw [h,hg] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 59) (b := e.loc 80 * e.loc 99) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [64,67,60]).addProd (-1) [64,67,80,99,98]).addProd (-1) [64,67,86,99,98])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [64,67,60]).addProd (-1) [64,67,80,99,98]).addProd (-1) [64,67,86,99,98])).eval e.loc
      = e.loc 64 * e.loc 67 * e.loc 60 + -1 * (e.loc 64 * e.loc 67 * e.loc 80 * e.loc 99 * e.loc 98)
        + -1 * (e.loc 64 * e.loc 67 * e.loc 86 * e.loc 99 * e.loc 98) from rfl, hip2, hin2] at hga
  have hatt : e.loc 60 = e.loc 80 * e.loc 99 * e.loc 98 + e.loc 86 * e.loc 99 * e.loc 98 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg|hg <;> rcases minMem with hm|hm <;>
          rw [h,h',hg,hm] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 60) (b := e.loc 80 * e.loc 99 * e.loc 98 + e.loc 86 * e.loc 99 * e.loc 98) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [64,67,61])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [64,67,61])).eval e.loc = e.loc 64 * e.loc 67 * e.loc 61 from rfl,
     hip2, hin2] at hgr
  have hrep : e.loc 61 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_attAtt pdMem ndMem ltB lt1 lt2 gtB gt1 gt2 leB le1 le2 gmB gm1 gm2 hmineq hvar hpos hatt hrep

/-- **Leg (3) for the X axis, IN FULL: `decodeDecision = evaluateAxis` for BOTH rays.** Case-splits on
the two ray `what`-codes over all nine `evaluate_axis` cases; each closes against the byte-pinned
`automataflStepDesc`. -/
theorem decideAxis_x_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  have hpwm : (envAt t i).loc (rWhat 0) = 0 ∨ (envAt t i).loc (rWhat 0) = 1 ∨ (envAt t i).loc (rWhat 0) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 0) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  have hnwm : (envAt t i).loc (rWhat 1) = 0 ∨ (envAt t i).loc (rWhat 1) = 1 ∨ (envAt t i).loc (rWhat 1) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 1) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  rcases hpwm with hp|hp|hp <;> rcases hnwm with hn|hn|hn
  · exact decideAxis_xdec_none hsat hc i hi hp hn
  · exact decideAxis_xdec_vacRep hsat hc i hi hp hn
  · exact decideAxis_xdec_vacAtt hsat hc i hi hp hn
  · exact decideAxis_xdec_repVac hsat hc i hi hp hn
  · exact decideAxis_xdec_repRep hsat hc i hi hp hn
  · exact decideAxis_xdec_repAtt hsat hc i hi hp hn
  · exact decideAxis_xdec_attVac hsat hc i hi hp hn
  · exact decideAxis_xdec_attRep hsat hc i hi hp hn
  · exact decideAxis_xdec_attAtt hsat hc i hi hp hn

end DecideXdecCases


section DecideYdec
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The YP ray distance `rDist 2 ∈ {1,2}`. -/
theorem ydec_pd_mem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (rDist 2) = 1 ∨ (envAt t i).loc (rDist 2) = 2 := by
  set e := envAt t i with he
  have b1 : e.loc (rHit 2 1) = 0 ∨ e.loc (rHit 2 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 2 1)) (by decide)) (canon_loc hc i _)
  have b2 : e.loc (rHit 2 2) = 0 ∨ e.loc (rHit 2 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 2 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 2 1) + e.loc (rHit 2 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 2 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 2 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 2 1) + e.loc (rHit 2 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 2 1) + e.loc (rHit 2 2)) (b := 1) (by ring)).mp hg
    rcases b1 with h0 | h0 <;> rcases b2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hval : e.loc (rDist 2) = e.loc (rHit 2 1) + 2 * e.loc (rHit 2 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 2 kk))
        (Head.lin (-1) (rDist 2)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 2 kk))
        (Head.lin (-1) (rDist 2)))).eval e.loc
        = (-1) * e.loc (rDist 2) + e.loc (rHit 2 1) + 2 * e.loc (rHit 2 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc (rHit 2 1) + 2 * e.loc (rHit 2 2))
      (b := e.loc (rDist 2)) (by ring)).mp hg
    have hcD : Canon (e.loc (rHit 2 1) + 2 * e.loc (rHit 2 2)) := by
      rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] <;> exact ⟨by norm_num, by norm_num⟩
    exact (eq_of_modEq_canon hcD (canon_loc hc i _) hmod).symm
  rw [hval]; rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] at hsum ⊢ <;> omega

/-- The YN ray distance `rDist 3 ∈ {1,2}`. -/
theorem ydec_nd_mem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (rDist 3) = 1 ∨ (envAt t i).loc (rDist 3) = 2 := by
  set e := envAt t i with he
  have b1 : e.loc (rHit 3 1) = 0 ∨ e.loc (rHit 3 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 3 1)) (by decide)) (canon_loc hc i _)
  have b2 : e.loc (rHit 3 2) = 0 ∨ e.loc (rHit 3 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 3 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 3 1) + e.loc (rHit 3 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 3 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 3 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 3 1) + e.loc (rHit 3 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 3 1) + e.loc (rHit 3 2)) (b := 1) (by ring)).mp hg
    rcases b1 with h0 | h0 <;> rcases b2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hval : e.loc (rDist 3) = e.loc (rHit 3 1) + 2 * e.loc (rHit 3 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 3 kk))
        (Head.lin (-1) (rDist 3)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 3 kk))
        (Head.lin (-1) (rDist 3)))).eval e.loc
        = (-1) * e.loc (rDist 3) + e.loc (rHit 3 1) + 2 * e.loc (rHit 3 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc (rHit 3 1) + 2 * e.loc (rHit 3 2))
      (b := e.loc (rDist 3)) (by ring)).mp hg
    have hcD : Canon (e.loc (rHit 3 1) + 2 * e.loc (rHit 3 2)) := by
      rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] <;> exact ⟨by norm_num, by norm_num⟩
    exact (eq_of_modEq_canon hcD (canon_loc hc i _) hmod).symm
  rw [hval]; rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] at hsum ⊢ <;> omega

/-- The ydec `ipw` one-hot (over the YP ray's `what`-code, columns 109..111). -/
theorem ydec_ipw_sel (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 109 = 0 ∨ (envAt t i).loc 109 = 1)
    ∧ ((envAt t i).loc 110 = 0 ∨ (envAt t i).loc 110 = 1)
    ∧ ((envAt t i).loc 111 = 0 ∨ (envAt t i).loc 111 = 1)
    ∧ (envAt t i).loc 109 + (envAt t i).loc 110 + (envAt t i).loc 111 = 1
    ∧ (envAt t i).loc 110 + 2 * (envAt t i).loc 111 = (envAt t i).loc (rWhat 2) := by
  set e := envAt t i with he
  have b0 : e.loc 109 = 0 ∨ e.loc 109 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 109) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 110 = 0 ∨ e.loc 110 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 110) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 111 = 0 ∨ e.loc 111 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 111) (by decide)) (canon_loc hc i _)
  have hsum : e.loc 109 + e.loc 110 + e.loc 111 = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ([109,110,111].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([109,110,111].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc
        = e.loc 109 + e.loc 110 + e.loc 111 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 109 + e.loc 110 + e.loc 111) (b := 1) (by ring)).mp hg
    rcases b0 with h|h <;> rcases b1 with h'|h' <;> rcases b2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h,h',h'']; norm_num) (by norm_num) this
  have hidx : e.loc 110 + 2 * e.loc 111 = e.loc (rWhat 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([109,110,111][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 2)).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([109,110,111][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 2)).scale (-1)))).eval e.loc = e.loc 110 + 2 * e.loc 111 + -1 * e.loc (rWhat 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc 110 + 2 * e.loc 111) (b := e.loc (rWhat 2)) (by ring)).mp hg
    have hcL : Canon (e.loc 110 + 2 * e.loc 111) := by
      rcases b1 with h|h <;> rcases b2 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨b0, b1, b2, hsum, hidx⟩

/-- The ydec `inw` one-hot (over the YN ray's `what`-code, columns 112..114). -/
theorem ydec_inw_sel (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 112 = 0 ∨ (envAt t i).loc 112 = 1)
    ∧ ((envAt t i).loc 113 = 0 ∨ (envAt t i).loc 113 = 1)
    ∧ ((envAt t i).loc 114 = 0 ∨ (envAt t i).loc 114 = 1)
    ∧ (envAt t i).loc 112 + (envAt t i).loc 113 + (envAt t i).loc 114 = 1
    ∧ (envAt t i).loc 113 + 2 * (envAt t i).loc 114 = (envAt t i).loc (rWhat 3) := by
  set e := envAt t i with he
  have b0 : e.loc 112 = 0 ∨ e.loc 112 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 112) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 113 = 0 ∨ e.loc 113 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 113) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 114 = 0 ∨ e.loc 114 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 114) (by decide)) (canon_loc hc i _)
  have hsum : e.loc 112 + e.loc 113 + e.loc 114 = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ([112,113,114].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([112,113,114].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc
        = e.loc 112 + e.loc 113 + e.loc 114 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 112 + e.loc 113 + e.loc 114) (b := 1) (by ring)).mp hg
    rcases b0 with h|h <;> rcases b1 with h'|h' <;> rcases b2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h,h',h'']; norm_num) (by norm_num) this
  have hidx : e.loc 113 + 2 * e.loc 114 = e.loc (rWhat 3) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([112,113,114][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 3)).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([112,113,114][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 3)).scale (-1)))).eval e.loc = e.loc 113 + 2 * e.loc 114 + -1 * e.loc (rWhat 3) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc 113 + 2 * e.loc 114) (b := e.loc (rWhat 3)) (by ring)).mp hg
    have hcL : Canon (e.loc 113 + 2 * e.loc 114) := by
      rcases b1 with h|h <;> rcases b2 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨b0, b1, b2, hsum, hidx⟩

/-- The ydec `gpd = [pd ≥ 2]` guard bit (col 115) decides `rDist 2 ≥ 2`. -/
theorem ydec_gpd_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 115 = 0 ∨ (envAt t i).loc 115 = 1)
    ∧ ((envAt t i).loc 115 = 1 → 2 ≤ (envAt t i).loc (rDist 2))
    ∧ ((envAt t i).loc 115 = 0 → (envAt t i).loc (rDist 2) ≤ 1) := by
  set e := envAt t i with he
  have gpdB : e.loc 115 = 0 ∨ e.loc 115 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 10)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 116 = 0 ∨ e.loc 116 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 11)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 117 = 0 ∨ e.loc 117 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 12)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 118 = 0 ∨ e.loc 118 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 13)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 119 = 0 ∨ e.loc 119 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 14)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 120 = 0 ∨ e.loc 120 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 15)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 11) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 10) ((Head.lin 1 (rDist 2)).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 11) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 10) ((Head.lin 1 (rDist 2)).addConst (-2))))).eval e.loc
      = 2 * (e.loc 115 * e.loc (rDist 2)) + -4 * e.loc 115 + e.loc 115 + -1 * e.loc (rDist 2)
        + -1 * e.loc 116 + -2 * e.loc 117 + -4 * e.loc 118 + -8 * e.loc 119 + -16 * e.loc 120 + 1 from rfl] at grec
  have gmod : (2 * e.loc 115 * (e.loc (rDist 2) - 2) + e.loc 115 - (e.loc (rDist 2) - 2) - 1)
      ≡ (e.loc 116 + 2 * e.loc 117 + 4 * e.loc 118 + 8 * e.loc 119 + 16 * e.loc 120) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := ydec_pd_mem hsat hc i hi
  rw [← he] at pdMem
  have core := forcedGe0_core (D := e.loc (rDist 2) - 2)
    (S := e.loc 116 + 2 * e.loc 117 + 4 * e.loc 118 + 8 * e.loc 119 + 16 * e.loc 120) gpdB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rw [h] <;> norm_num) (by rcases pdMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gpdB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The ydec `gnd = [nd ≥ 2]` guard bit (col 121) decides `rDist 3 ≥ 2`. -/
theorem ydec_gnd_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 121 = 0 ∨ (envAt t i).loc 121 = 1)
    ∧ ((envAt t i).loc 121 = 1 → 2 ≤ (envAt t i).loc (rDist 3))
    ∧ ((envAt t i).loc 121 = 0 → (envAt t i).loc (rDist 3) ≤ 1) := by
  set e := envAt t i with he
  have gndB : e.loc 121 = 0 ∨ e.loc 121 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 16)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 122 = 0 ∨ e.loc 122 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 17)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 123 = 0 ∨ e.loc 123 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 18)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 124 = 0 ∨ e.loc 124 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 19)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 125 = 0 ∨ e.loc 125 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 20)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 126 = 0 ∨ e.loc 126 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 21)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 17) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 16) ((Head.lin 1 (rDist 3)).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 17) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 16) ((Head.lin 1 (rDist 3)).addConst (-2))))).eval e.loc
      = 2 * (e.loc 121 * e.loc (rDist 3)) + -4 * e.loc 121 + e.loc 121 + -1 * e.loc (rDist 3)
        + -1 * e.loc 122 + -2 * e.loc 123 + -4 * e.loc 124 + -8 * e.loc 125 + -16 * e.loc 126 + 1 from rfl] at grec
  have gmod : (2 * e.loc 121 * (e.loc (rDist 3) - 2) + e.loc 121 - (e.loc (rDist 3) - 2) - 1)
      ≡ (e.loc 122 + 2 * e.loc 123 + 4 * e.loc 124 + 8 * e.loc 125 + 16 * e.loc 126) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at ndMem
  have core := forcedGe0_core (D := e.loc (rDist 3) - 2)
    (S := e.loc 122 + 2 * e.loc 123 + 4 * e.loc 124 + 8 * e.loc 125 + 16 * e.loc 126) gndB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases ndMem with h|h <;> rw [h] <;> norm_num) (by rcases ndMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gndB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The ydec `lt = [pd < nd]` compare bit (col 127). -/
theorem ydec_lt_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 127 = 0 ∨ (envAt t i).loc 127 = 1)
    ∧ ((envAt t i).loc 127 = 1 → (envAt t i).loc (rDist 2) < (envAt t i).loc (rDist 3))
    ∧ ((envAt t i).loc 127 = 0 → (envAt t i).loc (rDist 3) ≤ (envAt t i).loc (rDist 2)) := by
  set e := envAt t i with he
  have ltB : e.loc 127 = 0 ∨ e.loc 127 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 22)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 128 = 0 ∨ e.loc 128 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 23)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 129 = 0 ∨ e.loc 129 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 24)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 130 = 0 ∨ e.loc 130 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 25)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 131 = 0 ∨ e.loc 131 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 26)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 132 = 0 ∨ e.loc 132 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 27)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 23) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 22) (((Head.lin 1 (rDist 3)).addLin (-1) (rDist 2)).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 23) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 22) (((Head.lin 1 (rDist 3)).addLin (-1) (rDist 2)).addConst (-1))))).eval e.loc
      = 2 * (e.loc 127 * e.loc (rDist 3)) + -2 * (e.loc 127 * e.loc (rDist 2)) + -2 * e.loc 127 + e.loc 127
        + -1 * e.loc (rDist 3) + e.loc (rDist 2)
        + -1 * e.loc 128 + -2 * e.loc 129 + -4 * e.loc 130 + -8 * e.loc 131 + -16 * e.loc 132 from rfl] at grec
  have gmod : (2 * e.loc 127 * (e.loc (rDist 3) - e.loc (rDist 2) - 1) + e.loc 127
        - (e.loc (rDist 3) - e.loc (rDist 2) - 1) - 1)
      ≡ (e.loc 128 + 2 * e.loc 129 + 4 * e.loc 130 + 8 * e.loc 131 + 16 * e.loc 132) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have core := forcedGe0_core (D := e.loc (rDist 3) - e.loc (rDist 2) - 1)
    (S := e.loc 128 + 2 * e.loc 129 + 4 * e.loc 130 + 8 * e.loc 131 + 16 * e.loc 132) ltB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨ltB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The ydec `gt = [pd > nd]` compare bit (col 133). -/
theorem ydec_gt_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 133 = 0 ∨ (envAt t i).loc 133 = 1)
    ∧ ((envAt t i).loc 133 = 1 → (envAt t i).loc (rDist 3) < (envAt t i).loc (rDist 2))
    ∧ ((envAt t i).loc 133 = 0 → (envAt t i).loc (rDist 2) ≤ (envAt t i).loc (rDist 3)) := by
  set e := envAt t i with he
  have gtB : e.loc 133 = 0 ∨ e.loc 133 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 28)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 134 = 0 ∨ e.loc 134 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 29)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 135 = 0 ∨ e.loc 135 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 30)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 136 = 0 ∨ e.loc 136 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 31)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 137 = 0 ∨ e.loc 137 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 32)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 138 = 0 ∨ e.loc 138 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 33)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 29) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 28) (((Head.lin 1 (rDist 2)).addLin (-1) (rDist 3)).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 29) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 28) (((Head.lin 1 (rDist 2)).addLin (-1) (rDist 3)).addConst (-1))))).eval e.loc
      = 2 * (e.loc 133 * e.loc (rDist 2)) + -2 * (e.loc 133 * e.loc (rDist 3)) + -2 * e.loc 133 + e.loc 133
        + -1 * e.loc (rDist 2) + e.loc (rDist 3)
        + -1 * e.loc 134 + -2 * e.loc 135 + -4 * e.loc 136 + -8 * e.loc 137 + -16 * e.loc 138 from rfl] at grec
  have gmod : (2 * e.loc 133 * (e.loc (rDist 2) - e.loc (rDist 3) - 1) + e.loc 133
        - (e.loc (rDist 2) - e.loc (rDist 3) - 1) - 1)
      ≡ (e.loc 134 + 2 * e.loc 135 + 4 * e.loc 136 + 8 * e.loc 137 + 16 * e.loc 138) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have core := forcedGe0_core (D := e.loc (rDist 2) - e.loc (rDist 3) - 1)
    (S := e.loc 134 + 2 * e.loc 135 + 4 * e.loc 136 + 8 * e.loc 137 + 16 * e.loc 138) gtB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨gtB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The ydec `le = [pd ≤ nd]` compare bit (col 139). -/
theorem ydec_le_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 139 = 0 ∨ (envAt t i).loc 139 = 1)
    ∧ ((envAt t i).loc 139 = 1 → (envAt t i).loc (rDist 2) ≤ (envAt t i).loc (rDist 3))
    ∧ ((envAt t i).loc 139 = 0 → (envAt t i).loc (rDist 3) < (envAt t i).loc (rDist 2)) := by
  set e := envAt t i with he
  have leB : e.loc 139 = 0 ∨ e.loc 139 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 34)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 140 = 0 ∨ e.loc 140 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 35)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 141 = 0 ∨ e.loc 141 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 36)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 142 = 0 ∨ e.loc 142 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 37)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 143 = 0 ∨ e.loc 143 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 38)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 144 = 0 ∨ e.loc 144 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 39)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 35) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 34) ((Head.lin 1 (rDist 3)).addLin (-1) (rDist 2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 35) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 34) ((Head.lin 1 (rDist 3)).addLin (-1) (rDist 2))))).eval e.loc
      = 2 * (e.loc 139 * e.loc (rDist 3)) + -2 * (e.loc 139 * e.loc (rDist 2)) + e.loc 139
        + -1 * e.loc (rDist 3) + e.loc (rDist 2)
        + -1 * e.loc 140 + -2 * e.loc 141 + -4 * e.loc 142 + -8 * e.loc 143 + -16 * e.loc 144 + -1 from rfl] at grec
  have gmod : (2 * e.loc 139 * (e.loc (rDist 3) - e.loc (rDist 2)) + e.loc 139
        - (e.loc (rDist 3) - e.loc (rDist 2)) - 1)
      ≡ (e.loc 140 + 2 * e.loc 141 + 4 * e.loc 142 + 8 * e.loc 143 + 16 * e.loc 144) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have core := forcedGe0_core (D := e.loc (rDist 3) - e.loc (rDist 2))
    (S := e.loc 140 + 2 * e.loc 141 + 4 * e.loc 142 + 8 * e.loc 143 + 16 * e.loc 144) leB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases pdMem with h|h <;> rcases ndMem with h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨leB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- The ydec `min` gadget value (col 145) `= le·pd + nd − le·nd = min(pd, nd)`. -/
theorem ydec_min_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 145
      = (envAt t i).loc 139 * (envAt t i).loc (rDist 2) + (envAt t i).loc (rDist 3)
        - (envAt t i).loc 139 * (envAt t i).loc (rDist 3) := by
  set e := envAt t i with he
  obtain ⟨leB, _, _⟩ := ydec_le_sound hsat hc i hi
  rw [← he] at leB
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have hg := astep_gate hsat i hi
    (g := headToExpr ((((Head.lin 1 145).addProd (-1) [139, rDist 2]).addLin (-1) (rDist 3)).addProd 1 [139, rDist 3])) (by decide)
  rw [show (headToExpr ((((Head.lin 1 145).addProd (-1) [139, rDist 2]).addLin (-1) (rDist 3)).addProd 1 [139, rDist 3])).eval e.loc
      = e.loc 145 + -1 * (e.loc 139 * e.loc (rDist 2)) + -1 * e.loc (rDist 3) + e.loc 139 * e.loc (rDist 3) from rfl] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_
    ((gate_modEq_iff (a := e.loc 145)
      (b := e.loc 139 * e.loc (rDist 2) + e.loc (rDist 3) - e.loc 139 * e.loc (rDist 3)) (by ring)).mp hg)
  rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
    rw [h, hp, hn] <;> exact ⟨by norm_num, by norm_num⟩

/-- The ydec `gm = [min ≥ 2]` guard bit (col 146). -/
theorem ydec_gm_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 146 = 0 ∨ (envAt t i).loc 146 = 1)
    ∧ ((envAt t i).loc 146 = 1 → 2 ≤ (envAt t i).loc 145)
    ∧ ((envAt t i).loc 146 = 0 → (envAt t i).loc 145 ≤ 1) := by
  set e := envAt t i with he
  have hmin := ydec_min_sound hsat hc i hi
  rw [← he] at hmin
  obtain ⟨leB, _, _⟩ := ydec_le_sound hsat hc i hi
  rw [← he] at leB
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at pdMem ndMem
  have minMem : e.loc 145 = 1 ∨ e.loc 145 = 2 := by
    rw [hmin]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  have gmB : e.loc 146 = 0 ∨ e.loc 146 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 41)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 147 = 0 ∨ e.loc 147 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 42)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 148 = 0 ∨ e.loc 148 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 43)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 149 = 0 ∨ e.loc 149 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 44)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 150 = 0 ∨ e.loc 150 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 45)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 151 = 0 ∨ e.loc 151 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (105 + 46)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 42) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 41) ((Head.lin 1 145).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (105 + 42) SMALL_RBITS)[k]!))
      (forcedGe0Term (105 + 41) ((Head.lin 1 145).addConst (-2))))).eval e.loc
      = 2 * (e.loc 146 * e.loc 145) + -4 * e.loc 146 + e.loc 146 + -1 * e.loc 145
        + -1 * e.loc 147 + -2 * e.loc 148 + -4 * e.loc 149 + -8 * e.loc 150 + -16 * e.loc 151 + 1 from rfl] at grec
  have gmod : (2 * e.loc 146 * (e.loc 145 - 2) + e.loc 146 - (e.loc 145 - 2) - 1)
      ≡ (e.loc 147 + 2 * e.loc 148 + 4 * e.loc 149 + 8 * e.loc 150 + 16 * e.loc 151) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have core := forcedGe0_core (D := e.loc 145 - 2)
    (S := e.loc 147 + 2 * e.loc 148 + 4 * e.loc 149 + 8 * e.loc 150 + 16 * e.loc 151) gmB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases minMem with h|h <;> rw [h] <;> norm_num) (by rcases minMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gmB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-! ### The nine ydec cases (extraction ▸ pure decode). -/

theorem decideAxis_ydec_none (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 0) (hnw : (envAt t i).loc (rWhat 3) = 0) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 109 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 112 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,105])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,112,105])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 105 from rfl,
     hip0, hin0] at hgv
  have hvar : e.loc 105 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 105) (b := 0) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,106])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,112,106])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 106 from rfl,
     hip0, hin0] at hgp
  have hpos : e.loc 106 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 106) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,107])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,112,107])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 107 from rfl,
     hip0, hin0] at hga
  have hatt : e.loc 107 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,108])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,112,108])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 108 from rfl,
     hip0, hin0] at hgr
  have hrep : e.loc 108 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_vacVac hvar hpos hatt hrep

theorem decideAxis_ydec_attRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 2) (hnw : (envAt t i).loc (rWhat 3) = 1) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd2⟩ := ydec_gpd_sound hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 111 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 113 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,113,105]).addProd (-3) [111,113,115])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,113,105]).addProd (-3) [111,113,115])).eval e.loc
      = e.loc 111 * e.loc 113 * e.loc 105 + -3 * (e.loc 111 * e.loc 113 * e.loc 115) from rfl, hip2, hin1] at hgv
  have hvar : e.loc 105 = 3 * e.loc 115 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 105) (b := 3 * e.loc 115) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,113,106]).addProd (-1) [111,113,115])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,113,106]).addProd (-1) [111,113,115])).eval e.loc
      = e.loc 111 * e.loc 113 * e.loc 106 + -1 * (e.loc 111 * e.loc 113 * e.loc 115) from rfl, hip2, hin1] at hgp
  have hpos : e.loc 106 = e.loc 115 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 106) (b := e.loc 115) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,113,107]).addProd (-1) [111,113,115, rDist 2])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,113,107]).addProd (-1) [111,113,115, rDist 2])).eval e.loc
      = e.loc 111 * e.loc 113 * e.loc 107 + -1 * (e.loc 111 * e.loc 113 * e.loc 115 * e.loc (rDist 2)) from rfl,
     hip2, hin1] at hga
  have hatt : e.loc 107 = e.loc 115 * e.loc (rDist 2) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 107) (b := e.loc 115 * e.loc (rDist 2)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,113,108]).addProd (-1) [111,113,115, rDist 3])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,113,108]).addProd (-1) [111,113,115, rDist 3])).eval e.loc
      = e.loc 111 * e.loc 113 * e.loc 108 + -1 * (e.loc 111 * e.loc 113 * e.loc 115 * e.loc (rDist 3)) from rfl,
     hip2, hin1] at hgr
  have hrep : e.loc 108 = e.loc 115 * e.loc (rDist 3) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 108) (b := e.loc 115 * e.loc (rDist 3)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_attRep pdMem gpdB gpd1 gpd2 hvar hpos hatt hrep

theorem decideAxis_ydec_repAtt (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 1) (hnw : (envAt t i).loc (rWhat 3) = 2) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨gndB, gnd1, gnd2⟩ := ydec_gnd_sound hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip1 : e.loc 110 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin2 : e.loc 114 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [110,114,105]).addProd (-3) [110,114,121])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [110,114,105]).addProd (-3) [110,114,121])).eval e.loc
      = e.loc 110 * e.loc 114 * e.loc 105 + -3 * (e.loc 110 * e.loc 114 * e.loc 121) from rfl, hip1, hin2] at hgv
  have hvar : e.loc 105 = 3 * e.loc 121 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 105) (b := 3 * e.loc 121) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [110,114,106])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [110,114,106])).eval e.loc = e.loc 110 * e.loc 114 * e.loc 106 from rfl,
     hip1, hin2] at hgp
  have hpos : e.loc 106 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 106) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [110,114,107]).addProd (-1) [110,114,121, rDist 3])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [110,114,107]).addProd (-1) [110,114,121, rDist 3])).eval e.loc
      = e.loc 110 * e.loc 114 * e.loc 107 + -1 * (e.loc 110 * e.loc 114 * e.loc 121 * e.loc (rDist 3)) from rfl,
     hip1, hin2] at hga
  have hatt : e.loc 107 = e.loc 121 * e.loc (rDist 3) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 107) (b := e.loc 121 * e.loc (rDist 3)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [110,114,108]).addProd (-1) [110,114,121, rDist 2])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [110,114,108]).addProd (-1) [110,114,121, rDist 2])).eval e.loc
      = e.loc 110 * e.loc 114 * e.loc 108 + -1 * (e.loc 110 * e.loc 114 * e.loc 121 * e.loc (rDist 2)) from rfl,
     hip1, hin2] at hgr
  have hrep : e.loc 108 = e.loc 121 * e.loc (rDist 2) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases ydec_pd_mem hsat hc i hi with hp|hp <;>
          rw [← he] at hp <;> rw [hp] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 108) (b := e.loc 121 * e.loc (rDist 2)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_repAtt ndMem gndB gnd1 gnd2 hvar hpos hatt hrep

theorem decideAxis_ydec_repVac (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 1) (hnw : (envAt t i).loc (rWhat 3) = 0) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨gndB, gnd1, gnd2⟩ := ydec_gnd_sound hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip1 : e.loc 110 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 112 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [110,112,105]).addProd (-2) [110,112,121])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [110,112,105]).addProd (-2) [110,112,121])).eval e.loc
      = e.loc 110 * e.loc 112 * e.loc 105 + -2 * (e.loc 110 * e.loc 112 * e.loc 121) from rfl, hip1, hin0] at hgv
  have hvar : e.loc 105 = 2 * e.loc 121 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 105) (b := 2 * e.loc 121) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [110,112,106])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [110,112,106])).eval e.loc = e.loc 110 * e.loc 112 * e.loc 106 from rfl,
     hip1, hin0] at hgp
  have hpos : e.loc 106 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 106) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [110,112,107])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [110,112,107])).eval e.loc = e.loc 110 * e.loc 112 * e.loc 107 from rfl,
     hip1, hin0] at hga
  have hatt : e.loc 107 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [110,112,108]).addProd (-1) [110,112,121, rDist 2])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [110,112,108]).addProd (-1) [110,112,121, rDist 2])).eval e.loc
      = e.loc 110 * e.loc 112 * e.loc 108 + -1 * (e.loc 110 * e.loc 112 * e.loc 121 * e.loc (rDist 2)) from rfl,
     hip1, hin0] at hgr
  have hrep : e.loc 108 = e.loc 121 * e.loc (rDist 2) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 108) (b := e.loc 121 * e.loc (rDist 2)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_repVac ndMem gndB gnd1 gnd2 hvar hpos hatt hrep

theorem decideAxis_ydec_vacRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 0) (hnw : (envAt t i).loc (rWhat 3) = 1) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd2⟩ := ydec_gpd_sound hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 109 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 113 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [109,113,105]).addProd (-2) [109,113,115])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [109,113,105]).addProd (-2) [109,113,115])).eval e.loc
      = e.loc 109 * e.loc 113 * e.loc 105 + -2 * (e.loc 109 * e.loc 113 * e.loc 115) from rfl, hip0, hin1] at hgv
  have hvar : e.loc 105 = 2 * e.loc 115 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 105) (b := 2 * e.loc 115) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [109,113,106]).addProd (-1) [109,113,115])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [109,113,106]).addProd (-1) [109,113,115])).eval e.loc
      = e.loc 109 * e.loc 113 * e.loc 106 + -1 * (e.loc 109 * e.loc 113 * e.loc 115) from rfl, hip0, hin1] at hgp
  have hpos : e.loc 106 = e.loc 115 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 106) (b := e.loc 115) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,113,107])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,113,107])).eval e.loc = e.loc 109 * e.loc 113 * e.loc 107 from rfl,
     hip0, hin1] at hga
  have hatt : e.loc 107 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [109,113,108]).addProd (-1) [109,113,115, rDist 3])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [109,113,108]).addProd (-1) [109,113,115, rDist 3])).eval e.loc
      = e.loc 109 * e.loc 113 * e.loc 108 + -1 * (e.loc 109 * e.loc 113 * e.loc 115 * e.loc (rDist 3)) from rfl,
     hip0, hin1] at hgr
  have hrep : e.loc 108 = e.loc 115 * e.loc (rDist 3) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 108) (b := e.loc 115 * e.loc (rDist 3)) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_vacRep pdMem gpdB gpd1 gpd2 hvar hpos hatt hrep

theorem decideAxis_ydec_attVac (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 2) (hnw : (envAt t i).loc (rWhat 3) = 0) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd2⟩ := ydec_gpd_sound hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 111 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 112 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,112,105]).addProd (-1) [111,112,115])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,112,105]).addProd (-1) [111,112,115])).eval e.loc
      = e.loc 111 * e.loc 112 * e.loc 105 + -1 * (e.loc 111 * e.loc 112 * e.loc 115) from rfl, hip2, hin0] at hgv
  have hvar : e.loc 105 = e.loc 115 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 105) (b := e.loc 115) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,112,106]).addProd (-1) [111,112,115])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,112,106]).addProd (-1) [111,112,115])).eval e.loc
      = e.loc 111 * e.loc 112 * e.loc 106 + -1 * (e.loc 111 * e.loc 112 * e.loc 115) from rfl, hip2, hin0] at hgp
  have hpos : e.loc 106 = e.loc 115 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 106) (b := e.loc 115) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,112,107]).addProd (-1) [111,112,115, rDist 2])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,112,107]).addProd (-1) [111,112,115, rDist 2])).eval e.loc
      = e.loc 111 * e.loc 112 * e.loc 107 + -1 * (e.loc 111 * e.loc 112 * e.loc 115 * e.loc (rDist 2)) from rfl,
     hip2, hin0] at hga
  have hatt : e.loc 107 = e.loc 115 * e.loc (rDist 2) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 107) (b := e.loc 115 * e.loc (rDist 2)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [111,112,108])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [111,112,108])).eval e.loc = e.loc 111 * e.loc 112 * e.loc 108 from rfl,
     hip2, hin0] at hgr
  have hrep : e.loc 108 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_attVac pdMem gpdB gpd1 gpd2 hvar hpos hatt hrep

theorem decideAxis_ydec_vacAtt (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 0) (hnw : (envAt t i).loc (rWhat 3) = 2) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨gndB, gnd1, gnd2⟩ := ydec_gnd_sound hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 109 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin2 : e.loc 114 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [109,114,105]).addProd (-1) [109,114,121])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [109,114,105]).addProd (-1) [109,114,121])).eval e.loc
      = e.loc 109 * e.loc 114 * e.loc 105 + -1 * (e.loc 109 * e.loc 114 * e.loc 121) from rfl, hip0, hin2] at hgv
  have hvar : e.loc 105 = e.loc 121 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 105) (b := e.loc 121) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,114,106])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,114,106])).eval e.loc = e.loc 109 * e.loc 114 * e.loc 106 from rfl,
     hip0, hin2] at hgp
  have hpos : e.loc 106 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 106) (b := 0) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [109,114,107]).addProd (-1) [109,114,121, rDist 3])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [109,114,107]).addProd (-1) [109,114,121, rDist 3])).eval e.loc
      = e.loc 109 * e.loc 114 * e.loc 107 + -1 * (e.loc 109 * e.loc 114 * e.loc 121 * e.loc (rDist 3)) from rfl,
     hip0, hin2] at hga
  have hatt : e.loc 107 = e.loc 121 * e.loc (rDist 3) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 107) (b := e.loc 121 * e.loc (rDist 3)) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,114,108])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [109,114,108])).eval e.loc = e.loc 109 * e.loc 114 * e.loc 108 from rfl,
     hip0, hin2] at hgr
  have hrep : e.loc 108 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_vacAtt ndMem gndB gnd1 gnd2 hvar hpos hatt hrep

theorem decideAxis_ydec_repRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 1) (hnw : (envAt t i).loc (rWhat 3) = 1) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨ltB, lt1, lt2⟩ := ydec_lt_sound hsat hc i hi
  obtain ⟨gtB, gt1, gt2⟩ := ydec_gt_sound hsat hc i hi
  obtain ⟨leB, le1, le2⟩ := ydec_le_sound hsat hc i hi
  have hmineq := ydec_min_sound hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip1 : e.loc 110 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 113 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have minMem : e.loc 145 = 1 ∨ e.loc 145 = 2 := by
    rw [hmineq]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  have hgv := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [110,113,105]).addProd (-2) [110,113,127]).addProd (-2) [110,113,133])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [110,113,105]).addProd (-2) [110,113,127]).addProd (-2) [110,113,133])).eval e.loc
      = e.loc 110 * e.loc 113 * e.loc 105 + -2 * (e.loc 110 * e.loc 113 * e.loc 127)
        + -2 * (e.loc 110 * e.loc 113 * e.loc 133) from rfl, hip1, hin1] at hgv
  have hvar : e.loc 105 = 2 * e.loc 127 + 2 * e.loc 133 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 105) (b := 2 * e.loc 127 + 2 * e.loc 133) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [110,113,106]).addProd (-1) [110,113,133])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [110,113,106]).addProd (-1) [110,113,133])).eval e.loc
      = e.loc 110 * e.loc 113 * e.loc 106 + -1 * (e.loc 110 * e.loc 113 * e.loc 133) from rfl, hip1, hin1] at hgp
  have hpos : e.loc 106 = e.loc 133 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 106) (b := e.loc 133) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [110,113,107])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [110,113,107])).eval e.loc = e.loc 110 * e.loc 113 * e.loc 107 from rfl,
     hip1, hin1] at hga
  have hatt : e.loc 107 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [110,113,108]).addProd (-1) [110,113,127,145]).addProd (-1) [110,113,133,145])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [110,113,108]).addProd (-1) [110,113,127,145]).addProd (-1) [110,113,133,145])).eval e.loc
      = e.loc 110 * e.loc 113 * e.loc 108 + -1 * (e.loc 110 * e.loc 113 * e.loc 127 * e.loc 145)
        + -1 * (e.loc 110 * e.loc 113 * e.loc 133 * e.loc 145) from rfl, hip1, hin1] at hgr
  have hrep : e.loc 108 = e.loc 127 * e.loc 145 + e.loc 133 * e.loc 145 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases minMem with hm|hm <;>
          rw [h,h',hm] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 108) (b := e.loc 127 * e.loc 145 + e.loc 133 * e.loc 145) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_repRep pdMem ndMem ltB lt1 lt2 gtB gt1 gt2 leB le1 le2 hmineq hvar hpos hatt hrep

theorem decideAxis_ydec_attAtt (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 2) = 2) (hnw : (envAt t i).loc (rWhat 3) = 2) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  obtain ⟨ltB, lt1, lt2⟩ := ydec_lt_sound hsat hc i hi
  obtain ⟨gtB, gt1, gt2⟩ := ydec_gt_sound hsat hc i hi
  obtain ⟨leB, le1, le2⟩ := ydec_le_sound hsat hc i hi
  obtain ⟨gmB, gm1, gm2⟩ := ydec_gm_sound hsat hc i hi
  have hmineq := ydec_min_sound hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 111 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin2 : e.loc 114 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have minMem : e.loc 145 = 1 ∨ e.loc 145 = 2 := by
    rw [hmineq]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  have hgv := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [111,114,105]).addProd (-1) [111,114,127,146]).addProd (-1) [111,114,133,146])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [111,114,105]).addProd (-1) [111,114,127,146]).addProd (-1) [111,114,133,146])).eval e.loc
      = e.loc 111 * e.loc 114 * e.loc 105 + -1 * (e.loc 111 * e.loc 114 * e.loc 127 * e.loc 146)
        + -1 * (e.loc 111 * e.loc 114 * e.loc 133 * e.loc 146) from rfl, hip2, hin2] at hgv
  have hvar : e.loc 105 = e.loc 127 * e.loc 146 + e.loc 133 * e.loc 146 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg|hg <;>
          rw [h,h',hg] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 105) (b := e.loc 127 * e.loc 146 + e.loc 133 * e.loc 146) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [111,114,106]).addProd (-1) [111,114,127,146])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [111,114,106]).addProd (-1) [111,114,127,146])).eval e.loc
      = e.loc 111 * e.loc 114 * e.loc 106 + -1 * (e.loc 111 * e.loc 114 * e.loc 127 * e.loc 146) from rfl, hip2, hin2] at hgp
  have hpos : e.loc 106 = e.loc 127 * e.loc 146 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gmB with hg|hg <;> rw [h,hg] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 106) (b := e.loc 127 * e.loc 146) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr (((Head.zero.addProd 1 [111,114,107]).addProd (-1) [111,114,127,146,145]).addProd (-1) [111,114,133,146,145])) (by decide)
  rw [show (headToExpr (((Head.zero.addProd 1 [111,114,107]).addProd (-1) [111,114,127,146,145]).addProd (-1) [111,114,133,146,145])).eval e.loc
      = e.loc 111 * e.loc 114 * e.loc 107 + -1 * (e.loc 111 * e.loc 114 * e.loc 127 * e.loc 146 * e.loc 145)
        + -1 * (e.loc 111 * e.loc 114 * e.loc 133 * e.loc 146 * e.loc 145) from rfl, hip2, hin2] at hga
  have hatt : e.loc 107 = e.loc 127 * e.loc 146 * e.loc 145 + e.loc 133 * e.loc 146 * e.loc 145 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg|hg <;> rcases minMem with hm|hm <;>
          rw [h,h',hg,hm] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 107) (b := e.loc 127 * e.loc 146 * e.loc 145 + e.loc 133 * e.loc 146 * e.loc 145) (by ring)).mp hga)
  have hgr := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [111,114,108])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [111,114,108])).eval e.loc = e.loc 111 * e.loc 114 * e.loc 108 from rfl,
     hip2, hin2] at hgr
  have hrep : e.loc 108 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hgr)
  rw [hpw, hnw]
  exact decode_attAtt pdMem ndMem ltB lt1 lt2 gtB gt1 gt2 leB le1 le2 gmB gm1 gm2 hmineq hvar hpos hatt hrep

/-- **Leg (3) for the Y axis, IN FULL: `decodeDecision = evaluateAxis` for BOTH rays.** -/
theorem decideAxis_y_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 2)), dist := ((envAt t i).loc (rDist 2)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 3)), dist := ((envAt t i).loc (rDist 3)).toNat } := by
  have hpwm : (envAt t i).loc (rWhat 2) = 0 ∨ (envAt t i).loc (rWhat 2) = 1 ∨ (envAt t i).loc (rWhat 2) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 2) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  have hnwm : (envAt t i).loc (rWhat 3) = 0 ∨ (envAt t i).loc (rWhat 3) = 1 ∨ (envAt t i).loc (rWhat 3) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 3) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  rcases hpwm with hp|hp|hp <;> rcases hnwm with hn|hn|hn
  · exact decideAxis_ydec_none hsat hc i hi hp hn
  · exact decideAxis_ydec_vacRep hsat hc i hi hp hn
  · exact decideAxis_ydec_vacAtt hsat hc i hi hp hn
  · exact decideAxis_ydec_repVac hsat hc i hi hp hn
  · exact decideAxis_ydec_repRep hsat hc i hi hp hn
  · exact decideAxis_ydec_repAtt hsat hc i hi hp hn
  · exact decideAxis_ydec_attVac hsat hc i hi hp hn
  · exact decideAxis_ydec_attRep hsat hc i hi hp hn
  · exact decideAxis_ydec_attAtt hsat hc i hi hp hn

end DecideYdec

/-! ## §4.9 — NON-VACUITY for leg (3): the `forced_ge0` bit + `assert_case` gate REJECT wrong witnesses
(`#guard`).

The `forced_ge0` no-wrap soundness is only meaningful if the gadget can FAIL: a forged `gpd = 1` on a
board where `pd = 1` (`pd − 2 = −1 < 0`) has NO 5-bit non-negativity decomposition — its recomposition
term `2·1·1 + 1 − 1 − 1 = 1`… wait, the forged direction: claiming `gpd = 1` forces the range witness
to encode `pd − 2`; when `pd = 1` that is `−1`, which no sum of five booleans equals, so the gate is
UNSATISFIABLE. And the `(2,1)` `assert_case` variant gate rejects a decision that claims
`unbalancedPair` (`variant = 3`) while `gpd = 0`. Both shown as two-sided `#guard`s below. -/

/-- `gpd = 1`, `pd = 2`: the non-negativity witness `2·gpd·(pd−2) + gpd − (pd−2) − 1 = 0` recomposes
with ALL range bits `0` — the gadget ACCEPTS. -/
def ge0GoodAsg : Assignment := fun c =>
  if c = 68 then 1 else if c = rDist 0 then 2 else 0

/-- `gpd = 1`, `pd = 1`: term `= 2·1·1 + 1 − 1 − 1 = 1`; with ALL range bits 0 the recomposition is
`1 ≠ 0` — a FORGED `[pd ≥ 2]` bit has no satisfying decomposition here. -/
def ge0ForgeAsg : Assignment := fun c => if c = 68 then 1 else if c = rDist 0 then 1 else 0

/-- The exact `forced_ge0` recomposition gate body for the gpd gadget (term − Σ 2^k·bitₖ). -/
def gpdRecompExpr : EmittedExpr :=
  headToExpr ((List.range SMALL_RBITS).foldl
    (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 11) SMALL_RBITS)[k]!))
    (forcedGe0Term (58 + 10) ((Head.lin 1 (rDist 0)).addConst (-2))))

#guard gpdRecompExpr.eval ge0GoodAsg == 0     -- pd = 2, gpd = 1, bit₁ = 1: term recomposes, gate holds
#guard gpdRecompExpr.eval ge0ForgeAsg != 0    -- pd = 1, forged gpd = 1: NO decomposition, gate FAILS

/-- The `(2,1)` `assert_case` variant gate `ipw₂·inw₁·(variant − 3·gpd)`. A decision claiming
`unbalancedPair` (`variant = 3`) while the guard failed (`gpd = 0`) makes it `≠ 0`. -/
def acVariantExpr : EmittedExpr :=
  headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])
/-- Selected case (`ipw₂ = inw₁ = 1`), `gpd = 1`, `variant = 3`: consistent — gate holds. -/
def acGoodAsg : Assignment := fun c => if c = 64 ∨ c = 66 ∨ c = 68 then 1 else if c = 58 then 3 else 0
/-- Selected case, but `gpd = 0` while `variant = 3` claims `unbalancedPair` — a LIE; gate FAILS. -/
def acForgeAsg : Assignment := fun c => if c = 64 ∨ c = 66 then 1 else if c = 58 then 3 else 0

#guard acVariantExpr.eval acGoodAsg == 0      -- variant = 3·gpd = 3: consistent
#guard acVariantExpr.eval acForgeAsg != 0     -- variant = 3 but gpd = 0: unbalancedPair LIE FAILS

/-! ### §4.9b — canary for a NEWLY-CLOSED case: the `gnd` guard + the `(1,2)` `assert_case` REJECT
forged witnesses exactly as the `gpd`/`(2,1)` teeth do. `gnd` decides `nd ≥ 2` (`xdec_gnd_sound`), used
by the `(1,2)`/`(1,0)`/`(0,2)` cases; the `(1,2)` variant gate `ipw₁·inw₂·(variant − 3·gnd)` rejects a
`repulsor/attractor` decision that claims `unbalancedPair` (`variant = 3`) while `nd = 1` (`gnd = 0`). -/

/-- The `forced_ge0` recomposition body for the `gnd` gadget (`col 74`, term `= 2·gnd·(nd−2)+…`). -/
def gndRecompExpr : EmittedExpr :=
  headToExpr ((List.range SMALL_RBITS).foldl
    (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 17) SMALL_RBITS)[k]!))
    (forcedGe0Term (58 + 16) ((Head.lin 1 (rDist 1)).addConst (-2))))
/-- `gnd = 1`, `nd = 2`: term `= 0`, all range bits `0` — the gadget ACCEPTS. -/
def gndGoodAsg : Assignment := fun c => if c = 74 then 1 else if c = rDist 1 then 2 else 0
/-- `gnd = 1`, `nd = 1`: term `= −1`; no 5-bit non-negativity witness — a forged `[nd ≥ 2]` FAILS. -/
def gndForgeAsg : Assignment := fun c => if c = 74 then 1 else if c = rDist 1 then 1 else 0

#guard gndRecompExpr.eval gndGoodAsg == 0     -- nd = 2, gnd = 1: term recomposes, gate holds
#guard gndRecompExpr.eval gndForgeAsg != 0    -- nd = 1, forged gnd = 1: NO decomposition, gate FAILS

/-- The `(1,2)` `assert_case` variant gate `ipw₁·inw₂·(variant − 3·gnd)`. -/
def acVariant12Expr : EmittedExpr :=
  headToExpr ((Head.zero.addProd 1 [63,67,58]).addProd (-3) [63,67,74])
/-- Selected `(1,2)` case (`ipw₁ = inw₂ = 1`), `gnd = 1`, `variant = 3`: consistent — holds. -/
def ac12GoodAsg : Assignment := fun c => if c = 63 ∨ c = 67 ∨ c = 74 then 1 else if c = 58 then 3 else 0
/-- Selected `(1,2)` case, `gnd = 0` while `variant = 3` claims `unbalancedPair` — a LIE; FAILS. -/
def ac12ForgeAsg : Assignment := fun c => if c = 63 ∨ c = 67 then 1 else if c = 58 then 3 else 0

#guard acVariant12Expr.eval ac12GoodAsg == 0  -- variant = 3·gnd = 3: consistent
#guard acVariant12Expr.eval ac12ForgeAsg != 0 -- variant = 3 but gnd = 0: unbalancedPair LIE FAILS

/-! ## §5 — NON-VACUITY: the auto-pin gate is a two-sided discriminator (`#guard`).

A full satisfying trace for all 410 constraints (ray/decide/step witness columns + the two Poseidon2
`board_root8` lookups) is out of scope; but the SEMANTIC tooth this file proves is non-vacuous, shown
concretely on the auto-pin gate: it ACCEPTS the correct board (auto at (0,0) holding `AUTO=3`) and
REJECTS a wrong one (that cell holding `VAC=0`). A vacuous or always-true gate could not do both. -/

/-- Row picking cell (0,0): `selRow0 = selCol0 = 1`, that cell holds `AUTO = 3`. -/
def goodAsg : Assignment := fun c => if c = 0 then 3 else if c = selRow 0 ∨ c = selCol 0 then 1 else 0
/-- Same selectors, but cell (0,0) holds `VAC = 0` — a wrong board. -/
def badAsg : Assignment := fun c => if c = selRow 0 ∨ c = selCol 0 then 1 else 0

#guard (headToExpr autoPinHead).eval goodAsg == 0       -- correct board: gate holds
#guard (headToExpr autoPinHead).eval badAsg != 0        -- wrong board: gate FAILS (≠ 0)

/-! ### §5b — the XP ray teeth are two-sided discriminators (`#guard`).

The `raycast_xp_of_sat` refinement rests on two occlusion teeth; both REJECT a wrong `(dist, what)`:
the vacuum-before gate `hit₂·rc₁` rejects claiming the FAR hit (dist 2) when the near cell was
non-vacuous, and the `cond_nonzero` gate `hib·(what·inv − 1)` rejects claiming an in-bounds hit that
read VACUUM (`what = 0`). A wrong witness cannot satisfy them — so the ray gate set is non-vacuous. -/

/-- A witness that (correctly) hits at step 1 with the near cell non-vacuum (`hit₁ = 1`, `rc₁ = 1`). -/
def rayGoodAsg : Assignment := fun c => if c = rHit 0 1 then 1 else if c = rRc 0 1 then 1 else 0
/-- A wrong witness that claims the FAR hit (`hit₂ = 1`) though the near cell `rc₁ = 1` is non-vacuum. -/
def rayFarBadAsg : Assignment := fun c => if c = rHit 0 2 then 1 else if c = rRc 0 1 then 1 else 0
/-- A wrong witness claiming an in-bounds hit (`hib = 1`) whose read was VACUUM (`what = 0`). -/
def rayVacBadAsg : Assignment := fun c => if c = rHib 0 then 1 else 0

#guard (headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])).eval rayGoodAsg == 0    -- near hit: ok
#guard (headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])).eval rayFarBadAsg != 0  -- far-hit lie: FAILS
#guard (EmittedExpr.mul (.var (rHib 0))
          (.add (.mul (.var (rWhat 0)) (.var (rInv 0))) (.const (-1)))).eval rayVacBadAsg != 0 -- vac-hit lie: FAILS

/-! ### §5c — the XN ray teeth are two-sided discriminators (`#guard`, canary for the replay).

The same occlusion teeth, now on the XN ray block (`d = 1`): they REJECT a wrong `(dist, what)` exactly
as the XP teeth do. This is the canary that the mechanical replay pins a REAL gate set per direction,
not a re-authored mirror — the `d = 1` columns are the ones `raycast_xn_of_sat` extracts. -/

/-- XN near-hit witness (`hit₁ = 1`, `rc₁ = 1`) for ray block `d = 1`. -/
def rayGoodAsgXN : Assignment := fun c => if c = rHit 1 1 then 1 else if c = rRc 1 1 then 1 else 0
/-- XN far-hit lie (`hit₂ = 1`, near cell `rc₁ = 1` non-vacuous). -/
def rayFarBadAsgXN : Assignment := fun c => if c = rHit 1 2 then 1 else if c = rRc 1 1 then 1 else 0
/-- XN vacuum-hit lie (`hib = 1`, read VACUUM `what = 0`). -/
def rayVacBadAsgXN : Assignment := fun c => if c = rHib 1 then 1 else 0

#guard (headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])).eval rayGoodAsgXN == 0    -- near hit: ok
#guard (headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])).eval rayFarBadAsgXN != 0  -- far-hit lie: FAILS
#guard (EmittedExpr.mul (.var (rHib 1))
          (.add (.mul (.var (rWhat 1)) (.var (rInv 1))) (.const (-1)))).eval rayVacBadAsgXN != 0 -- vac-hit lie: FAILS

/-! ## §4.10 — LEG (4): `chooseOffset` refinement — the pure score-order heart.

The `choose_offset` cross-axis tie-break compares the two per-axis decisions by a SCORE HEAD
`score = variant·100000 − att·100 − rep` (`air.rs::score_head`), and moves along the higher-scoring
axis. This section lands the PURE content: (a) the wide no-wrap window (`SCORE_RBITS = 20` ≫ the
5-bit small window — the score magnitudes are `≤ 300000 < 2^20`, but the range witness spans 20 bits
so the interval is proportionally wider), and (b) `decScore`, the felt score of a decoded `Decision`,
proven to be an ORDER EMBEDDING of `decisionCmp` (so a numeric `>` on scores IS the decision order). -/

/-- Wide no-wrap window for the SCORE compare: two integers of magnitude `≤ 2·10⁶` congruent mod `p`
are EQUAL. This is the interval that contains every score-difference `sx − sy − 1 ∈ [−300203, 300201]`
AND every 20-bit range-sum `S ∈ [0, 2²⁰−1] = [0, 1048575]` — both well inside `(−p, p)`, so
`p ∣ (a − b)` collapses to `a = b`. Wider than `eq_of_modEq_win` (which caps at `10⁶ < 2²⁰`). -/
theorem eq_of_modEq_score {a b : ℤ} (ha : -2000000 ≤ a ∧ a ≤ 2000000)
    (hb : -2000000 ≤ b ∧ b ≤ 2000000) (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd; obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb; omega

/-- **The 20-bit `forced_ge0` NO-WRAP soundness heart (SCORE width).** Identical in shape to
`forcedGe0_core`, but the range-sum is 20 bits (`S ∈ [0, 2²⁰−1]`) and the compared magnitude `D` is a
SCORE difference (`|D| ≤ 400000`, dwarfing `10²·att + rep` at `n = 2`). Given `ib ∈ {0,1}`, the 20-bit
sum `S`, and the recomposed non-negativity term `2·ib·D + ib − D − 1 ≡ S [ZMOD p]`, the bit is exactly
the comparison: `ib = 1 → 0 ≤ D` and `ib = 0 → D ≤ −1`. The window `[−400000,400000] ∪ [0,1048575] ⊂
(−p, p)` is the exact no-wrap interval — a 20-bit witness cannot alias a different residue. This is the
lemma that makes the `sgt`/`slt` score compares SOUND (a forged bit has no satisfying decomposition). -/
theorem forcedGe0_core_score {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 1048575)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -400000 ≤ D) (hDhi : D ≤ 400000) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0:ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_score (by omega) (by omega) hmod
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1:ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_score (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hc; omega⟩

/-- The felt SCORE of a decoded `Decision` (`air.rs::score_head`, `SCORE_PRI = 100000`,
`SCORE_ATT = 100`): the priority tier in the top digits, then `−100·att − rep` so that SMALLER
distances score HIGHER. `none = 0`. The circuit's `sx = 100000·variant − 100·att − rep` equals this
on a witness where the UNUSED fields are pinned to `0` (`decideAxis`'s `assert_case` formulas). -/
def decScore : Decision → ℤ
  | .unbalancedPair _ a r => 300000 - 100 * (a : ℤ) - (r : ℤ)
  | .fromRepulsor _ r     => 200000 - (r : ℤ)
  | .towardAttractor _ a  => 100000 - 100 * (a : ℤ)
  | .none                 => 0

/-- The `n = 2` distance envelope: a decision's `att`/`rep` fields are step counts `≤ 2` (every ray
distance is `∈ {1,2}`, and `min`/either endpoint inherits that). This is the bound under which the
score is a faithful order embedding (`rep ≤ 2 < 100` ⇒ no carry into the `att` digit; `att ≤ 2` ⇒ the
`100000` variant tier dominates). -/
def attRep2 : Decision → Prop
  | .unbalancedPair _ a r => a ≤ 2 ∧ r ≤ 2
  | .fromRepulsor _ r     => r ≤ 2
  | .towardAttractor _ a  => a ≤ 2
  | .none                 => True

/-- **`decScore` IS an order embedding of `decisionCmp`.** For decisions with `n = 2`-bounded fields,
comparing the felt scores REPRODUCES the reference decision order (`impl Ord for AutomatonDecision`):
priority first (the `100000` tier), then the intra-priority tie-break (smaller distance wins, via
`−100·att − rep`). The load-bearing fact for the score-compare gates: `sgt`/`slt` decide `decisionCmp`. -/
theorem decScore_cmp (d1 d2 : Decision) (h1 : attRep2 d1) (h2 : attRep2 d2) :
    compare (decScore d1) (decScore d2) = decisionCmp d1 d2 := by
  rcases d1 with ⟨p1, a1, r1⟩ | ⟨p1, r1⟩ | ⟨p1, a1⟩ | _ <;>
    rcases d2 with ⟨p2, a2, r2⟩ | ⟨p2, r2⟩ | ⟨p2, a2⟩ | _ <;>
    simp only [attRep2] at h1 h2
  · obtain ⟨ha1, hr1⟩ := h1; obtain ⟨ha2, hr2⟩ := h2
    interval_cases a1 <;> interval_cases r1 <;> interval_cases a2 <;> interval_cases r2 <;> decide +revert
  · obtain ⟨ha1, hr1⟩ := h1
    interval_cases a1 <;> interval_cases r1 <;> interval_cases r2 <;> decide +revert
  · obtain ⟨ha1, hr1⟩ := h1
    interval_cases a1 <;> interval_cases r1 <;> interval_cases a2 <;> decide +revert
  · obtain ⟨ha1, hr1⟩ := h1
    interval_cases a1 <;> interval_cases r1 <;> decide +revert
  · obtain ⟨ha2, hr2⟩ := h2
    interval_cases r1 <;> interval_cases a2 <;> interval_cases r2 <;> decide +revert
  · interval_cases r1 <;> interval_cases r2 <;> decide +revert
  · interval_cases r1 <;> interval_cases a2 <;> decide +revert
  · interval_cases r1 <;> decide +revert
  · obtain ⟨ha2, hr2⟩ := h2
    interval_cases a1 <;> interval_cases a2 <;> interval_cases r2 <;> decide +revert
  · interval_cases a1 <;> interval_cases r2 <;> decide +revert
  · interval_cases a1 <;> interval_cases a2 <;> decide +revert
  · interval_cases a1 <;> decide +revert
  · obtain ⟨ha2, hr2⟩ := h2
    interval_cases a2 <;> interval_cases r2 <;> decide +revert
  · interval_cases r2 <;> decide +revert
  · interval_cases a2 <;> decide +revert
  · decide +revert

/-- Consequence: on `n = 2`-bounded decisions, `decisionCmp = .gt` IFF the first score strictly
exceeds the second. This is the exact bridge the `sgt` gate lands on. -/
theorem decisionCmp_gt_iff_score (d1 d2 : Decision) (h1 : attRep2 d1) (h2 : attRep2 d2) :
    decisionCmp d1 d2 = .gt ↔ decScore d2 < decScore d1 := by
  rw [← decScore_cmp d1 d2 h1 h2, Int.compare_eq_gt]

/-! ## §4.11 — LEG (4): the score-compare bits `sgt`/`slt` are SOUND on the byte-pinned object.

The heart wired to the descriptor: the `choose_offset` `forced_ge0` guard column `152` (`sgt`) pins
`[sx > sy]` and `173` (`slt`) pins `[sy > sx]` with NO wraparound, via the 20-bit range witness
(`bitsFrom 153 20` / `bitsFrom 174 20`) forcing the non-negativity of `2·sgt·(sx−sy−1) + sgt −
(sx−sy−1) − 1`. `forcedGe0_core_score` discharges the field-congruence trap: the score magnitudes are
`≤ 300000` (variant `≤ 3`, `att`/`rep` `≤ 2` at `n = 2`), so `|sx − sy − 1| ≤ 400000 < p − 2²⁰` — the
20-bit witness cannot alias a different residue. The `att`/`rep ≤ 2` envelope is supplied as the
hypotheses `h60/h61/h107/h108` (the score-field determination is §4.13 / the named residual). -/

section ScoreBits
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- A boolean-pinned column is in `[0,1]` (bounds form, for `omega`). -/
theorem binBnd (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat)
    (hmem : cg (gBin c) ∈ automataflStepDesc.constraints) :
    0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c ≤ 1 := by
  rcases bin_of_gate (astep_gate hsat i hi (g := gBin c) hmem) (canon_loc hc i _) with h|h <;> omega

/-- **`sgt = [sx > sy]` — SOUND, no wrap.** On a satisfying canonical trace whose score fields are the
`n = 2` envelope (`variant ≤ 3`, `att`/`rep ≤ 2`), the `sgt` bit (col 152) genuinely decides the score
order `sx > sy` (where `sx = 100000·variant − 100·att − rep`). -/
theorem sgt_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (h58 : (envAt t i).loc 58 ≤ 3) (h60 : (envAt t i).loc 60 ≤ 2) (h61 : (envAt t i).loc 61 ≤ 2)
    (h105 : (envAt t i).loc 105 ≤ 3) (h107 : (envAt t i).loc 107 ≤ 2) (h108 : (envAt t i).loc 108 ≤ 2) :
    ((envAt t i).loc 152 = 0 ∨ (envAt t i).loc 152 = 1)
    ∧ ((envAt t i).loc 152 = 1 →
        100000 * (envAt t i).loc 105 - 100 * (envAt t i).loc 107 - (envAt t i).loc 108
          < 100000 * (envAt t i).loc 58 - 100 * (envAt t i).loc 60 - (envAt t i).loc 61)
    ∧ ((envAt t i).loc 152 = 0 →
        100000 * (envAt t i).loc 58 - 100 * (envAt t i).loc 60 - (envAt t i).loc 61
          ≤ 100000 * (envAt t i).loc 105 - 100 * (envAt t i).loc 107 - (envAt t i).loc 108) := by
  set e := envAt t i with he
  have hib : e.loc 152 = 0 ∨ e.loc 152 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin SGT_IB) (by decide)) (canon_loc hc i _)
  have b0 : 0 ≤ e.loc 153 ∧ e.loc 153 ≤ 1 := binBnd hsat hc i hi 153 (by decide)
  have b1 : 0 ≤ e.loc 154 ∧ e.loc 154 ≤ 1 := binBnd hsat hc i hi 154 (by decide)
  have b2 : 0 ≤ e.loc 155 ∧ e.loc 155 ≤ 1 := binBnd hsat hc i hi 155 (by decide)
  have b3 : 0 ≤ e.loc 156 ∧ e.loc 156 ≤ 1 := binBnd hsat hc i hi 156 (by decide)
  have b4 : 0 ≤ e.loc 157 ∧ e.loc 157 ≤ 1 := binBnd hsat hc i hi 157 (by decide)
  have b5 : 0 ≤ e.loc 158 ∧ e.loc 158 ≤ 1 := binBnd hsat hc i hi 158 (by decide)
  have b6 : 0 ≤ e.loc 159 ∧ e.loc 159 ≤ 1 := binBnd hsat hc i hi 159 (by decide)
  have b7 : 0 ≤ e.loc 160 ∧ e.loc 160 ≤ 1 := binBnd hsat hc i hi 160 (by decide)
  have b8 : 0 ≤ e.loc 161 ∧ e.loc 161 ≤ 1 := binBnd hsat hc i hi 161 (by decide)
  have b9 : 0 ≤ e.loc 162 ∧ e.loc 162 ≤ 1 := binBnd hsat hc i hi 162 (by decide)
  have b10 : 0 ≤ e.loc 163 ∧ e.loc 163 ≤ 1 := binBnd hsat hc i hi 163 (by decide)
  have b11 : 0 ≤ e.loc 164 ∧ e.loc 164 ≤ 1 := binBnd hsat hc i hi 164 (by decide)
  have b12 : 0 ≤ e.loc 165 ∧ e.loc 165 ≤ 1 := binBnd hsat hc i hi 165 (by decide)
  have b13 : 0 ≤ e.loc 166 ∧ e.loc 166 ≤ 1 := binBnd hsat hc i hi 166 (by decide)
  have b14 : 0 ≤ e.loc 167 ∧ e.loc 167 ≤ 1 := binBnd hsat hc i hi 167 (by decide)
  have b15 : 0 ≤ e.loc 168 ∧ e.loc 168 ≤ 1 := binBnd hsat hc i hi 168 (by decide)
  have b16 : 0 ≤ e.loc 169 ∧ e.loc 169 ≤ 1 := binBnd hsat hc i hi 169 (by decide)
  have b17 : 0 ≤ e.loc 170 ∧ e.loc 170 ≤ 1 := binBnd hsat hc i hi 170 (by decide)
  have b18 : 0 ≤ e.loc 171 ∧ e.loc 171 ≤ 1 := binBnd hsat hc i hi 171 (by decide)
  have b19 : 0 ≤ e.loc 172 ∧ e.loc 172 ≤ 1 := binBnd hsat hc i hi 172 (by decide)
  have c58 : 0 ≤ e.loc 58 := (canon_loc hc i _).1
  have c60 : 0 ≤ e.loc 60 := (canon_loc hc i _).1
  have c61 : 0 ≤ e.loc 61 := (canon_loc hc i _).1
  have c105 : 0 ≤ e.loc 105 := (canon_loc hc i _).1
  have c107 : 0 ≤ e.loc 107 := (canon_loc hc i _).1
  have c108 : 0 ≤ e.loc 108 := (canon_loc hc i _).1
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SCORE_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 153 SCORE_RBITS)[k]!))
      (forcedGe0Term SGT_IB (((scoreHead X_VAR X_ATT X_REP).append
        ((scoreHead Y_VAR Y_ATT Y_REP).scale (-1))).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SCORE_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 153 SCORE_RBITS)[k]!))
      (forcedGe0Term SGT_IB (((scoreHead X_VAR X_ATT X_REP).append
        ((scoreHead Y_VAR Y_ATT Y_REP).scale (-1))).addConst (-1))))).eval e.loc
      = 200000*(e.loc 152*e.loc 58) + -200*(e.loc 152*e.loc 60) + -2*(e.loc 152*e.loc 61)
        + -200000*(e.loc 152*e.loc 105) + 200*(e.loc 152*e.loc 107) + 2*(e.loc 152*e.loc 108)
        + -2*e.loc 152 + e.loc 152 + -100000*e.loc 58 + 100*e.loc 60 + e.loc 61 + 100000*e.loc 105
        + -100*e.loc 107 + -1*e.loc 108 + -1*e.loc 153 + -2*e.loc 154 + -4*e.loc 155 + -8*e.loc 156
        + -16*e.loc 157 + -32*e.loc 158 + -64*e.loc 159 + -128*e.loc 160 + -256*e.loc 161
        + -512*e.loc 162 + -1024*e.loc 163 + -2048*e.loc 164 + -4096*e.loc 165 + -8192*e.loc 166
        + -16384*e.loc 167 + -32768*e.loc 168 + -65536*e.loc 169 + -131072*e.loc 170
        + -262144*e.loc 171 + -524288*e.loc 172 from rfl] at grec
  have gmod : (2 * e.loc 152 * (100000*e.loc 58 - 100*e.loc 60 - e.loc 61
        - 100000*e.loc 105 + 100*e.loc 107 + e.loc 108 - 1) + e.loc 152
        - (100000*e.loc 58 - 100*e.loc 60 - e.loc 61 - 100000*e.loc 105 + 100*e.loc 107 + e.loc 108 - 1) - 1)
      ≡ (e.loc 153 + 2*e.loc 154 + 4*e.loc 155 + 8*e.loc 156 + 16*e.loc 157 + 32*e.loc 158
         + 64*e.loc 159 + 128*e.loc 160 + 256*e.loc 161 + 512*e.loc 162 + 1024*e.loc 163
         + 2048*e.loc 164 + 4096*e.loc 165 + 8192*e.loc 166 + 16384*e.loc 167 + 32768*e.loc 168
         + 65536*e.loc 169 + 131072*e.loc 170 + 262144*e.loc 171 + 524288*e.loc 172) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have core := forcedGe0_core_score (ib := e.loc 152)
    (D := 100000*e.loc 58 - 100*e.loc 60 - e.loc 61 - 100000*e.loc 105 + 100*e.loc 107 + e.loc 108 - 1)
    (S := e.loc 153 + 2*e.loc 154 + 4*e.loc 155 + 8*e.loc 156 + 16*e.loc 157 + 32*e.loc 158
         + 64*e.loc 159 + 128*e.loc 160 + 256*e.loc 161 + 512*e.loc 162 + 1024*e.loc 163
         + 2048*e.loc 164 + 4096*e.loc 165 + 8192*e.loc 166 + 16384*e.loc 167 + 32768*e.loc 168
         + 65536*e.loc 169 + 131072*e.loc 170 + 262144*e.loc 171 + 524288*e.loc 172)
    hib (by omega) (by omega) gmod (by omega) (by omega)
  exact ⟨hib, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- **`slt = [sy > sx]` — SOUND, no wrap.** The mirror of `sgt_of_sat` on the `slt` bit (col 173) and
its 20-bit witness (`bitsFrom 174 20`): `slt = 1 → sx < sy`, `slt = 0 → sy ≤ sx`. -/
theorem slt_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (h58 : (envAt t i).loc 58 ≤ 3) (h60 : (envAt t i).loc 60 ≤ 2) (h61 : (envAt t i).loc 61 ≤ 2)
    (h105 : (envAt t i).loc 105 ≤ 3) (h107 : (envAt t i).loc 107 ≤ 2) (h108 : (envAt t i).loc 108 ≤ 2) :
    ((envAt t i).loc 173 = 0 ∨ (envAt t i).loc 173 = 1)
    ∧ ((envAt t i).loc 173 = 1 →
        100000 * (envAt t i).loc 58 - 100 * (envAt t i).loc 60 - (envAt t i).loc 61
          < 100000 * (envAt t i).loc 105 - 100 * (envAt t i).loc 107 - (envAt t i).loc 108)
    ∧ ((envAt t i).loc 173 = 0 →
        100000 * (envAt t i).loc 105 - 100 * (envAt t i).loc 107 - (envAt t i).loc 108
          ≤ 100000 * (envAt t i).loc 58 - 100 * (envAt t i).loc 60 - (envAt t i).loc 61) := by
  set e := envAt t i with he
  have hib : e.loc 173 = 0 ∨ e.loc 173 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin SLT_IB) (by decide)) (canon_loc hc i _)
  have b0  : 0 ≤ e.loc 174 ∧ e.loc 174 ≤ 1 := binBnd hsat hc i hi 174 (by decide)
  have b1  : 0 ≤ e.loc 175 ∧ e.loc 175 ≤ 1 := binBnd hsat hc i hi 175 (by decide)
  have b2  : 0 ≤ e.loc 176 ∧ e.loc 176 ≤ 1 := binBnd hsat hc i hi 176 (by decide)
  have b3  : 0 ≤ e.loc 177 ∧ e.loc 177 ≤ 1 := binBnd hsat hc i hi 177 (by decide)
  have b4  : 0 ≤ e.loc 178 ∧ e.loc 178 ≤ 1 := binBnd hsat hc i hi 178 (by decide)
  have b5  : 0 ≤ e.loc 179 ∧ e.loc 179 ≤ 1 := binBnd hsat hc i hi 179 (by decide)
  have b6  : 0 ≤ e.loc 180 ∧ e.loc 180 ≤ 1 := binBnd hsat hc i hi 180 (by decide)
  have b7  : 0 ≤ e.loc 181 ∧ e.loc 181 ≤ 1 := binBnd hsat hc i hi 181 (by decide)
  have b8  : 0 ≤ e.loc 182 ∧ e.loc 182 ≤ 1 := binBnd hsat hc i hi 182 (by decide)
  have b9  : 0 ≤ e.loc 183 ∧ e.loc 183 ≤ 1 := binBnd hsat hc i hi 183 (by decide)
  have b10 : 0 ≤ e.loc 184 ∧ e.loc 184 ≤ 1 := binBnd hsat hc i hi 184 (by decide)
  have b11 : 0 ≤ e.loc 185 ∧ e.loc 185 ≤ 1 := binBnd hsat hc i hi 185 (by decide)
  have b12 : 0 ≤ e.loc 186 ∧ e.loc 186 ≤ 1 := binBnd hsat hc i hi 186 (by decide)
  have b13 : 0 ≤ e.loc 187 ∧ e.loc 187 ≤ 1 := binBnd hsat hc i hi 187 (by decide)
  have b14 : 0 ≤ e.loc 188 ∧ e.loc 188 ≤ 1 := binBnd hsat hc i hi 188 (by decide)
  have b15 : 0 ≤ e.loc 189 ∧ e.loc 189 ≤ 1 := binBnd hsat hc i hi 189 (by decide)
  have b16 : 0 ≤ e.loc 190 ∧ e.loc 190 ≤ 1 := binBnd hsat hc i hi 190 (by decide)
  have b17 : 0 ≤ e.loc 191 ∧ e.loc 191 ≤ 1 := binBnd hsat hc i hi 191 (by decide)
  have b18 : 0 ≤ e.loc 192 ∧ e.loc 192 ≤ 1 := binBnd hsat hc i hi 192 (by decide)
  have b19 : 0 ≤ e.loc 193 ∧ e.loc 193 ≤ 1 := binBnd hsat hc i hi 193 (by decide)
  have c58 : 0 ≤ e.loc 58 := (canon_loc hc i _).1
  have c60 : 0 ≤ e.loc 60 := (canon_loc hc i _).1
  have c61 : 0 ≤ e.loc 61 := (canon_loc hc i _).1
  have c105 : 0 ≤ e.loc 105 := (canon_loc hc i _).1
  have c107 : 0 ≤ e.loc 107 := (canon_loc hc i _).1
  have c108 : 0 ≤ e.loc 108 := (canon_loc hc i _).1
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SCORE_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 174 SCORE_RBITS)[k]!))
      (forcedGe0Term SLT_IB (((scoreHead Y_VAR Y_ATT Y_REP).append
        ((scoreHead X_VAR X_ATT X_REP).scale (-1))).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SCORE_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 174 SCORE_RBITS)[k]!))
      (forcedGe0Term SLT_IB (((scoreHead Y_VAR Y_ATT Y_REP).append
        ((scoreHead X_VAR X_ATT X_REP).scale (-1))).addConst (-1))))).eval e.loc
      = 200000*(e.loc 173*e.loc 105) + -200*(e.loc 173*e.loc 107) + -2*(e.loc 173*e.loc 108)
        + -200000*(e.loc 173*e.loc 58) + 200*(e.loc 173*e.loc 60) + 2*(e.loc 173*e.loc 61)
        + -2*e.loc 173 + e.loc 173 + -100000*e.loc 105 + 100*e.loc 107 + e.loc 108 + 100000*e.loc 58
        + -100*e.loc 60 + -1*e.loc 61 + -1*e.loc 174 + -2*e.loc 175 + -4*e.loc 176 + -8*e.loc 177
        + -16*e.loc 178 + -32*e.loc 179 + -64*e.loc 180 + -128*e.loc 181 + -256*e.loc 182
        + -512*e.loc 183 + -1024*e.loc 184 + -2048*e.loc 185 + -4096*e.loc 186 + -8192*e.loc 187
        + -16384*e.loc 188 + -32768*e.loc 189 + -65536*e.loc 190 + -131072*e.loc 191
        + -262144*e.loc 192 + -524288*e.loc 193 from rfl] at grec
  have gmod : (2 * e.loc 173 * (100000*e.loc 105 - 100*e.loc 107 - e.loc 108
        - 100000*e.loc 58 + 100*e.loc 60 + e.loc 61 - 1) + e.loc 173
        - (100000*e.loc 105 - 100*e.loc 107 - e.loc 108 - 100000*e.loc 58 + 100*e.loc 60 + e.loc 61 - 1) - 1)
      ≡ (e.loc 174 + 2*e.loc 175 + 4*e.loc 176 + 8*e.loc 177 + 16*e.loc 178 + 32*e.loc 179
         + 64*e.loc 180 + 128*e.loc 181 + 256*e.loc 182 + 512*e.loc 183 + 1024*e.loc 184
         + 2048*e.loc 185 + 4096*e.loc 186 + 8192*e.loc 187 + 16384*e.loc 188 + 32768*e.loc 189
         + 65536*e.loc 190 + 131072*e.loc 191 + 262144*e.loc 192 + 524288*e.loc 193) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have core := forcedGe0_core_score (ib := e.loc 173)
    (D := 100000*e.loc 105 - 100*e.loc 107 - e.loc 108 - 100000*e.loc 58 + 100*e.loc 60 + e.loc 61 - 1)
    (S := e.loc 174 + 2*e.loc 175 + 4*e.loc 176 + 8*e.loc 177 + 16*e.loc 178 + 32*e.loc 179
         + 64*e.loc 180 + 128*e.loc 181 + 256*e.loc 182 + 512*e.loc 183 + 1024*e.loc 184
         + 2048*e.loc 185 + 4096*e.loc 186 + 8192*e.loc 187 + 16384*e.loc 188 + 32768*e.loc 189
         + 65536*e.loc 190 + 131072*e.loc 191 + 262144*e.loc 192 + 524288*e.loc 193)
    hib (by omega) (by omega) gmod (by omega) (by omega)
  exact ⟨hib, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

end ScoreBits

/-! ## §4.12 — LEG (4): the column pin + the two offset equalities, extracted from the object.

The `choose_offset` back half: `col == col_rule` pins the column-rule flag to `true` (`= 1`), and the
two offset gates pin `ox`/`oy` to the winner's step. With `col = 1` the `oy` `push_f` expansion
collapses to `oy = ymove·(2·posy−1)·(1 − sgt)` — i.e. the Automaton moves in `y` exactly when the
score compare did NOT hand the win to `x` (`sgt = 0`). Combined with `sgt_of_sat`/`slt_of_sat` and the
`decScore` order embedding these are the full `chooseOffset` cross-axis tie-break — see §4.13. -/

/-- Decode a `{−1,0,1}` offset column (felt `p−1 ≡ −1`) into its signed `ℤ` value. -/
def decodeOff (z : ℤ) : ℤ := if z = 2013265920 then -1 else z

section OffsetGates
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The column rule is pinned `true`.** `col == col_rule` forces `col` (col 206) to `COL_RULE = 1`. -/
theorem colPin_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 206 = 1 := by
  have hg := astep_gate hsat i hi (g := headToExpr ((Head.lin 1 COL_C).addConst (-COL_RULE))) (by decide)
  rw [show (headToExpr ((Head.lin 1 COL_C).addConst (-COL_RULE))).eval (envAt t i).loc
      = (envAt t i).loc 206 + -1 from rfl] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hg)

/-- **The `ox` offset equality.** `ox − 2·sgt·xmove·posx + sgt·xmove == 0`, i.e. the `x` offset is the
score-winner bit `sgt` times the `x`-decision's signed step `xmove·(2·posx−1)`. Stated as the field
congruence (the value half is `offset_of_sat`: `ox ∈ {−1,0,1}`). -/
theorem ox_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 207
      ≡ 2 * ((envAt t i).loc 152 * (envAt t i).loc 194 * (envAt t i).loc 59)
          - (envAt t i).loc 152 * (envAt t i).loc 194 [ZMOD 2013265921] := by
  have hg := astep_gate hsat i hi
    (g := headToExpr (((Head.lin 1 OX_C).addProd (-2) [SGT_IB, XMOVE_IB, X_POS]).addProd 1 [SGT_IB, XMOVE_IB]))
    (by decide)
  rw [show (headToExpr (((Head.lin 1 OX_C).addProd (-2) [SGT_IB, XMOVE_IB, X_POS]).addProd 1 [SGT_IB, XMOVE_IB])).eval (envAt t i).loc
      = (envAt t i).loc 207 + -2*((envAt t i).loc 152*(envAt t i).loc 194*(envAt t i).loc 59)
        + (envAt t i).loc 152*(envAt t i).loc 194 from rfl] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- **The `oy` offset equality (`col = 1`).** The `push_f`-expanded `oy` gate, with the column rule
pinned `true` (`colPin_of_sat`), collapses to `oy = ymove·(2·posy−1)·(1 − sgt)`: the Automaton takes
the `y` step exactly when `sgt = 0` (the score compare did not give the win to `x`). -/
theorem oy_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 208
      ≡ (envAt t i).loc 200 * (2 * (envAt t i).loc 106 - 1) * (1 - (envAt t i).loc 152)
        [ZMOD 2013265921] := by
  have hcol := colPin_of_sat hsat hc i hi
  have hg := astep_gate hsat i hi (g := headToExpr oyHead) (by decide)
  rw [show (headToExpr oyHead).eval (envAt t i).loc
      = (envAt t i).loc 208 + -2*((envAt t i).loc 200*(envAt t i).loc 106*(envAt t i).loc 173)
        + (envAt t i).loc 200*(envAt t i).loc 173 + -2*((envAt t i).loc 200*(envAt t i).loc 106*(envAt t i).loc 206)
        + (envAt t i).loc 200*(envAt t i).loc 206
        + 2*((envAt t i).loc 200*(envAt t i).loc 106*(envAt t i).loc 152*(envAt t i).loc 206)
        + -1*((envAt t i).loc 200*(envAt t i).loc 152*(envAt t i).loc 206)
        + 2*((envAt t i).loc 200*(envAt t i).loc 106*(envAt t i).loc 173*(envAt t i).loc 206)
        + -1*((envAt t i).loc 200*(envAt t i).loc 173*(envAt t i).loc 206) from rfl] at hg
  rw [hcol] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end OffsetGates

/-! ## §4.13 — LEG (4): the offset IS `chooseOffset` (conditional on the score-field determination).

The capstone: on a satisfying canonical trace, the decoded offset `(ox, oy)` equals the reference
cross-axis tie-break `chooseOffset (decode xdec) (decode ydec) true`. The proof composes the pieces:
`sgt_of_sat`/`slt_of_sat` (the score compare is sound, no wrap) ▸ `decScore_cmp` (score order =
`decisionCmp`) ▸ `xmove_of_sat`/`ymove_of_sat` (the move bit = "decision ≠ none") ▸ `ox_of_sat`/
`oy_of_sat` (the offset = winner·signed-step). The two obligations threaded as HYPOTHESES are the §4.13
RESIDUAL — the score-field determination `sx = decScore (decode xdec)` and the `att`/`rep ≤ 2`
envelope — which need the `decide_axis` `assert_case` field-value extraction (the 9-case ×2 that
`decideAxis_x_sound` proves for the DECODED decision but not for the raw score columns). NOT assumed
as a top-level fact; the bridge is stated as the conditional it is. -/

/-- A canonical cell whose `{0,1,2,3}` membership gate vanishes mod `p` is `0,1,2,3`. -/
theorem mem4_of_gate {a : Assignment} {c : Nat}
    (h : (memberExpr c [0, 1, 2, 3]).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 ∨ a c = 2 ∨ a c = 3 := by
  simp only [memberExpr, List.foldl, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + -1) * (a c + -2) * (a c + -3) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using h)
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · rcases pPrimeInt.dvd_mul.mp h2 with h3 | h3
      · obtain ⟨k, hk⟩ := h3; left; omega
      · obtain ⟨k, hk⟩ := h3; right; left; omega
    · obtain ⟨k, hk⟩ := h2; right; right; left; omega
  · obtain ⟨k, hk⟩ := h1; right; right; right; omega

/-- Convert an offset column (`{0,1,p−1}`) congruent to a SMALL `r` into `decodeOff = r`. -/
theorem decodeOff_eq_of {z r : ℤ} (htri : z = 0 ∨ z = 1 ∨ z = 2013265920)
    (hr : -16 ≤ r ∧ r ≤ 16) (hmod : z ≡ r [ZMOD 2013265921]) : decodeOff z = r := by
  unfold decodeOff
  rcases htri with h|h|h <;> subst h
  · rw [if_neg (by norm_num)]; exact eq_of_modEq_small (by norm_num) hr hmod
  · rw [if_neg (by norm_num)]; exact eq_of_modEq_small (by norm_num) hr hmod
  · rw [if_pos rfl]
    exact eq_of_modEq_small (by norm_num) hr
      ((Int.modEq_iff_dvd.mpr (by norm_num)).trans hmod)

/-- **Pure**: the `x`-decision's signed step is `xmove·(2·posx−1)` (`xmove = [variant ≥ 1] = [≠ none]`). -/
theorem decodeDecision_delta_x_fst (v posx att rep : ℤ)
    (hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) (hp : posx = 0 ∨ posx = 1) :
    ((decodeDecision v posx att rep).delta (1, 0)).1 = (if 1 ≤ v then 1 else 0) * (2 * posx - 1) := by
  rcases hv with h|h|h|h <;> subst h <;> rcases hp with h|h <;> subst h <;>
    simp [decodeDecision, Decision.delta]

/-- **Pure**: the `x`-decision's step has zero `y`-component. -/
theorem decodeDecision_delta_x_snd (v posx att rep : ℤ) :
    ((decodeDecision v posx att rep).delta (1, 0)).2 = 0 := by
  unfold decodeDecision; split_ifs <;> simp only [Decision.delta] <;> first | rfl | (split_ifs <;> rfl)

/-- **Pure**: the `y`-decision's signed step is `ymove·(2·posy−1)` in the `y`-component. -/
theorem decodeDecision_delta_y_snd (v posy att rep : ℤ)
    (hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) (hp : posy = 0 ∨ posy = 1) :
    ((decodeDecision v posy att rep).delta (0, 1)).2 = (if 1 ≤ v then 1 else 0) * (2 * posy - 1) := by
  rcases hv with h|h|h|h <;> subst h <;> rcases hp with h|h <;> subst h <;>
    simp [decodeDecision, Decision.delta]

/-- **Pure**: the `y`-decision's step has zero `x`-component. -/
theorem decodeDecision_delta_y_fst (v posy att rep : ℤ) :
    ((decodeDecision v posy att rep).delta (0, 1)).1 = 0 := by
  unfold decodeDecision; split_ifs <;> simp only [Decision.delta] <;> first | rfl | (split_ifs <;> rfl)

/-! ## §4.12b — LEG (4′): the score-field DETERMINATION (`xScoreEval` / `yScoreEval`).

The `decide_axis` `assert_case` gates pin the raw `(variant, att, rep)` witness columns so that the
felt score head `sx = 100000·variant − 100·att − rep` equals `decScore` of the DECODED decision, and
the `att`/`rep` columns are the `n = 2` distance envelope (`≤ 2`). This DISCHARGES the two hypotheses
`offset_matches_chooseOffset` was stated conditional on. Same 9-case shape as `decideAxis_*`; nothing
assumed — every field value is read off the byte-pinned object. -/

/-- **Pure**: `attRep2` of a decoded decision follows from the raw `att`/`rep ≤ 2` envelope (the score
distance columns are `n = 2` step counts). `decScore`/`attRep2` never read a distance beyond the used
tier, so `att, rep ∈ [0,2]` suffices. -/
theorem attRep2_of_env {v pos att rep : ℤ} (ha : att ≤ 2) (hr : rep ≤ 2)
    (ha0 : 0 ≤ att) (hr0 : 0 ≤ rep) : attRep2 (decodeDecision v pos att rep) := by
  unfold decodeDecision
  split_ifs <;> simp only [attRep2] <;> first | trivial | omega | (constructor <;> omega)

/-- **Pure**: the felt score head equals `decScore` of the decoded decision, on a witness whose UNUSED
fields are pinned to `0` (`assert_case`): `att = 0` for `fromRepulsor`, `rep = 0` for `towardAttractor`,
both for `none`. The used-field tiers reproduce `decScore` exactly (`att, rep ≥ 0 ⇒ toNat` is the
identity). -/
theorem decScore_of_fields {v pos att rep : ℤ}
    (hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) (hatt0 : 0 ≤ att) (hrep0 : 0 ≤ rep)
    (h2 : v = 2 → att = 0) (h1 : v = 1 → rep = 0) (h0 : v = 0 → att = 0 ∧ rep = 0) :
    100000 * v - 100 * att - rep = decScore (decodeDecision v pos att rep) := by
  have hta : (att.toNat : ℤ) = att := Int.toNat_of_nonneg hatt0
  have htr : (rep.toNat : ℤ) = rep := Int.toNat_of_nonneg hrep0
  rcases hv with h|h|h|h <;> subst h
  · obtain ⟨ha, hr⟩ := h0 rfl; subst ha hr; simp [decodeDecision, decScore]
  · rw [h1 rfl]; simp only [decodeDecision, decScore]; norm_num [hta]
  · rw [h2 rfl]; simp only [decodeDecision, decScore]; norm_num [htr]
  · simp only [decodeDecision, decScore]; norm_num [hta, htr]

section ScoreEval
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

set_option maxHeartbeats 800000 in
/-- **LEG (4′), X axis: the score-field determination.** On a satisfying canonical trace, the `xdec`
score head equals `decScore` of the decoded X decision, and the `att`/`rep` columns are the `n = 2`
envelope (`≤ 2`). Discharges `offset_matches_chooseOffset`'s two X hypotheses. Same 9-case shape as
`decideAxis_x_sound`. -/
theorem xScoreEval (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 60 ≤ 2 ∧ (envAt t i).loc 61 ≤ 2
    ∧ attRep2 (decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61))
    ∧ 100000 * (envAt t i).loc 58 - 100 * (envAt t i).loc 60 - (envAt t i).loc 61
        = decScore (decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)) := by
  set e := envAt t i with he
  have hv58 : e.loc 58 = 0 ∨ e.loc 58 = 1 ∨ e.loc 58 = 2 ∨ e.loc 58 = 3 :=
    mem4_of_gate (astep_gate hsat i hi (g := memberExpr 58 [0,1,2,3]) (by decide)) (canon_loc hc i _)
  have ca60 : 0 ≤ e.loc 60 := (canon_loc hc i _).1
  have ca61 : 0 ≤ e.loc 61 := (canon_loc hc i _).1
  -- the two ray what-codes drive the 9-case split.
  have hpwm : e.loc (rWhat 0) = 0 ∨ e.loc (rWhat 0) = 1 ∨ e.loc (rWhat 0) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 0) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  have hnwm : e.loc (rWhat 1) = 0 ∨ e.loc (rWhat 1) = 1 ∨ e.loc (rWhat 1) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 1) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  -- ipw/inw one-hots pick the active case's gate columns.
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  rw [← he] at iidx nidx isum nsum ib0 ib1 ib2 nb0 nb1 nb2
  -- guard soundness (distances ∈ {1,2}; the comparison bits decide the ordering, no wrap).
  obtain ⟨gpdB, gpd1, gpd0⟩ := xdec_gpd_sound hsat hc i hi
  obtain ⟨gndB, gnd1, gnd0⟩ := xdec_gnd_sound hsat hc i hi
  obtain ⟨ltB, lt1, lt0⟩ := xdec_lt_sound hsat hc i hi
  obtain ⟨gtB, gt1, gt0⟩ := xdec_gt_sound hsat hc i hi
  obtain ⟨leB, le1, le0⟩ := xdec_le_sound hsat hc i hi
  obtain ⟨gmB, gm1, gm0⟩ := xdec_gm_sound hsat hc i hi
  have hmineq := xdec_min_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  have ndMem := xdec_nd_mem hsat hc i hi
  rw [← he] at gpdB gpd1 gpd0 gndB gnd1 gnd0 ltB lt1 lt0 gtB gt1 gt0 leB le1 le0 gmB gm1 gm0 hmineq pdMem ndMem
  have minMem : e.loc 98 = 1 ∨ e.loc 98 = 2 := by
    rw [hmineq]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  -- helper to close a branch once (att,rep) columns are extracted (loc60,loc61 concrete-linear).
  rcases hpwm with hp|hp|hp <;> rcases hnwm with hn|hn|hn
  · -- (vac, vac) → none
    have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,65,58])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [62,65,58])).eval e.loc = e.loc 62 * e.loc 65 * e.loc 58 from rfl, hip0, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 58) (b := 0) (by ring)).mp hg)
    have ha : e.loc 60 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,65,60])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [62,65,60])).eval e.loc = e.loc 62 * e.loc 65 * e.loc 60 from rfl, hip0, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hg)
    have hr : e.loc 61 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,65,61])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [62,65,61])).eval e.loc = e.loc 62 * e.loc 65 * e.loc 61 from rfl, hip0, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hg)
    exact ⟨by omega, by omega, attRep2_of_env (by omega) (by omega) ca60 ca61,
      decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (vac, rep) → vacRep : var=2gpd, att=0, rep=gpd·nd
    have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = 2 * e.loc 68 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [62,66,58]).addProd (-2) [62,66,68])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [62,66,58]).addProd (-2) [62,66,68])).eval e.loc = e.loc 62 * e.loc 66 * e.loc 58 + -2 * (e.loc 62 * e.loc 66 * e.loc 68) from rfl, hip0, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 58) (b := 2 * e.loc 68) (by ring)).mp hg)
    have ha : e.loc 60 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,66,60])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [62,66,60])).eval e.loc = e.loc 62 * e.loc 66 * e.loc 60 from rfl, hip0, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hg)
    have hr : e.loc 61 = e.loc 68 * e.loc (rDist 1) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [62,66,61]).addProd (-1) [62,66,68, rDist 1])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [62,66,61]).addProd (-1) [62,66,68, rDist 1])).eval e.loc = e.loc 62 * e.loc 66 * e.loc 61 + -1 * (e.loc 62 * e.loc 66 * e.loc 68 * e.loc (rDist 1)) from rfl, hip0, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 61) (b := e.loc 68 * e.loc (rDist 1)) (by ring)).mp hg)
    rcases gpdB with hg|hg <;> rw [hg] at hav hr <;>
      exact ⟨by omega, by rcases ndMem with h|h <;> omega, attRep2_of_env (by rcases ndMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (vac, att) → vacAtt : var=gnd, att=gnd·nd, rep=0
    have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin2 : e.loc 67 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = e.loc 74 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [62,67,58]).addProd (-1) [62,67,74])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [62,67,58]).addProd (-1) [62,67,74])).eval e.loc = e.loc 62 * e.loc 67 * e.loc 58 + -1 * (e.loc 62 * e.loc 67 * e.loc 74) from rfl, hip0, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (a := e.loc 58) (b := e.loc 74) (by ring)).mp hg)
    have ha : e.loc 60 = e.loc 74 * e.loc (rDist 1) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [62,67,60]).addProd (-1) [62,67,74, rDist 1])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [62,67,60]).addProd (-1) [62,67,74, rDist 1])).eval e.loc = e.loc 62 * e.loc 67 * e.loc 60 + -1 * (e.loc 62 * e.loc 67 * e.loc 74 * e.loc (rDist 1)) from rfl, hip0, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 60) (b := e.loc 74 * e.loc (rDist 1)) (by ring)).mp hg)
    have hr : e.loc 61 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,67,61])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [62,67,61])).eval e.loc = e.loc 62 * e.loc 67 * e.loc 61 from rfl, hip0, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hg)
    rcases gndB with hg|hg <;> rw [hg] at hav ha <;>
      exact ⟨by rcases ndMem with h|h <;> omega, by omega, attRep2_of_env (by rcases ndMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (rep, vac) → repVac : var=2gnd, att=0, rep=gnd·pd
    have hip1 : e.loc 63 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = 2 * e.loc 74 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [63,65,58]).addProd (-2) [63,65,74])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [63,65,58]).addProd (-2) [63,65,74])).eval e.loc = e.loc 63 * e.loc 65 * e.loc 58 + -2 * (e.loc 63 * e.loc 65 * e.loc 74) from rfl, hip1, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 58) (b := 2 * e.loc 74) (by ring)).mp hg)
    have ha : e.loc 60 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [63,65,60])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [63,65,60])).eval e.loc = e.loc 63 * e.loc 65 * e.loc 60 from rfl, hip1, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hg)
    have hr : e.loc 61 = e.loc 74 * e.loc (rDist 0) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [63,65,61]).addProd (-1) [63,65,74, rDist 0])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [63,65,61]).addProd (-1) [63,65,74, rDist 0])).eval e.loc = e.loc 63 * e.loc 65 * e.loc 61 + -1 * (e.loc 63 * e.loc 65 * e.loc 74 * e.loc (rDist 0)) from rfl, hip1, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 61) (b := e.loc 74 * e.loc (rDist 0)) (by ring)).mp hg)
    rcases gndB with hg|hg <;> rw [hg] at hav hr <;>
      exact ⟨by omega, by rcases pdMem with h|h <;> omega, attRep2_of_env (by rcases pdMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (rep, rep) → repRep : var=2lt+2gt, att=0, rep=lt·min+gt·min
    have hip1 : e.loc 63 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = 2 * e.loc 80 + 2 * e.loc 86 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [63,66,58]).addProd (-2) [63,66,80]).addProd (-2) [63,66,86])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [63,66,58]).addProd (-2) [63,66,80]).addProd (-2) [63,66,86])).eval e.loc = e.loc 63 * e.loc 66 * e.loc 58 + -2 * (e.loc 63 * e.loc 66 * e.loc 80) + -2 * (e.loc 63 * e.loc 66 * e.loc 86) from rfl, hip1, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 58) (b := 2 * e.loc 80 + 2 * e.loc 86) (by ring)).mp hg)
    have ha : e.loc 60 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [63,66,60])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [63,66,60])).eval e.loc = e.loc 63 * e.loc 66 * e.loc 60 from rfl, hip1, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 60) (b := 0) (by ring)).mp hg)
    have hr : e.loc 61 = e.loc 80 * e.loc 98 + e.loc 86 * e.loc 98 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [63,66,61]).addProd (-1) [63,66,80,98]).addProd (-1) [63,66,86,98])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [63,66,61]).addProd (-1) [63,66,80,98]).addProd (-1) [63,66,86,98])).eval e.loc = e.loc 63 * e.loc 66 * e.loc 61 + -1 * (e.loc 63 * e.loc 66 * e.loc 80 * e.loc 98) + -1 * (e.loc 63 * e.loc 66 * e.loc 86 * e.loc 98) from rfl, hip1, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases minMem with hm|hm <;> rw [h,h',hm] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 61) (b := e.loc 80 * e.loc 98 + e.loc 86 * e.loc 98) (by ring)).mp hg)
    rcases ltB with hl|hl <;> rcases gtB with hg2|hg2 <;> rw [hl, hg2] at hav hr <;>
      first
      | exact ⟨by omega, by rcases minMem with h|h <;> omega, attRep2_of_env (by omega) (by rcases minMem with h|h <;> omega) ca60 ca61,
          decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
      | (exfalso; have := lt1 hl; have := gt1 hg2; omega)
  · -- (rep, att) → repAtt : var=3gnd, att=gnd·nd, rep=gnd·pd
    have hip1 : e.loc 63 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin2 : e.loc 67 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = 3 * e.loc 74 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [63,67,58]).addProd (-3) [63,67,74])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [63,67,58]).addProd (-3) [63,67,74])).eval e.loc = e.loc 63 * e.loc 67 * e.loc 58 + -3 * (e.loc 63 * e.loc 67 * e.loc 74) from rfl, hip1, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 58) (b := 3 * e.loc 74) (by ring)).mp hg)
    have ha : e.loc 60 = e.loc 74 * e.loc (rDist 1) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [63,67,60]).addProd (-1) [63,67,74, rDist 1])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [63,67,60]).addProd (-1) [63,67,74, rDist 1])).eval e.loc = e.loc 63 * e.loc 67 * e.loc 60 + -1 * (e.loc 63 * e.loc 67 * e.loc 74 * e.loc (rDist 1)) from rfl, hip1, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 60) (b := e.loc 74 * e.loc (rDist 1)) (by ring)).mp hg)
    have hr : e.loc 61 = e.loc 74 * e.loc (rDist 0) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [63,67,61]).addProd (-1) [63,67,74, rDist 0])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [63,67,61]).addProd (-1) [63,67,74, rDist 0])).eval e.loc = e.loc 63 * e.loc 67 * e.loc 61 + -1 * (e.loc 63 * e.loc 67 * e.loc 74 * e.loc (rDist 0)) from rfl, hip1, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 61) (b := e.loc 74 * e.loc (rDist 0)) (by ring)).mp hg)
    rcases gndB with hg|hg <;> rw [hg] at hav ha hr <;>
      exact ⟨by rcases ndMem with h|h <;> omega, by rcases pdMem with h|h <;> omega,
        attRep2_of_env (by rcases ndMem with h|h <;> omega) (by rcases pdMem with h|h <;> omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (att, vac) → attVac : var=gpd, att=gpd·pd, rep=0
    have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = e.loc 68 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [64,65,58]).addProd (-1) [64,65,68])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [64,65,58]).addProd (-1) [64,65,68])).eval e.loc = e.loc 64 * e.loc 65 * e.loc 58 + -1 * (e.loc 64 * e.loc 65 * e.loc 68) from rfl, hip2, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (a := e.loc 58) (b := e.loc 68) (by ring)).mp hg)
    have ha : e.loc 60 = e.loc 68 * e.loc (rDist 0) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [64,65,60]).addProd (-1) [64,65,68, rDist 0])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [64,65,60]).addProd (-1) [64,65,68, rDist 0])).eval e.loc = e.loc 64 * e.loc 65 * e.loc 60 + -1 * (e.loc 64 * e.loc 65 * e.loc 68 * e.loc (rDist 0)) from rfl, hip2, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 60) (b := e.loc 68 * e.loc (rDist 0)) (by ring)).mp hg)
    have hr : e.loc 61 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [64,65,61])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [64,65,61])).eval e.loc = e.loc 64 * e.loc 65 * e.loc 61 from rfl, hip2, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hg)
    rcases gpdB with hg|hg <;> rw [hg] at hav ha <;>
      exact ⟨by rcases pdMem with h|h <;> omega, by omega, attRep2_of_env (by rcases pdMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (att, rep) → attRep : var=3gpd, att=gpd·pd, rep=gpd·nd
    have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = 3 * e.loc 68 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])).eval e.loc = e.loc 64 * e.loc 66 * e.loc 58 + -3 * (e.loc 64 * e.loc 66 * e.loc 68) from rfl, hip2, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 58) (b := 3 * e.loc 68) (by ring)).mp hg)
    have ha : e.loc 60 = e.loc 68 * e.loc (rDist 0) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [64,66,60]).addProd (-1) [64,66,68, rDist 0])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [64,66,60]).addProd (-1) [64,66,68, rDist 0])).eval e.loc = e.loc 64 * e.loc 66 * e.loc 60 + -1 * (e.loc 64 * e.loc 66 * e.loc 68 * e.loc (rDist 0)) from rfl, hip2, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 60) (b := e.loc 68 * e.loc (rDist 0)) (by ring)).mp hg)
    have hr : e.loc 61 = e.loc 68 * e.loc (rDist 1) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [64,66,61]).addProd (-1) [64,66,68, rDist 1])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [64,66,61]).addProd (-1) [64,66,68, rDist 1])).eval e.loc = e.loc 64 * e.loc 66 * e.loc 61 + -1 * (e.loc 64 * e.loc 66 * e.loc 68 * e.loc (rDist 1)) from rfl, hip2, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 61) (b := e.loc 68 * e.loc (rDist 1)) (by ring)).mp hg)
    rcases gpdB with hg|hg <;> rw [hg] at hav ha hr <;>
      exact ⟨by rcases pdMem with h|h <;> omega, by rcases ndMem with h|h <;> omega,
        attRep2_of_env (by rcases pdMem with h|h <;> omega) (by rcases ndMem with h|h <;> omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (att, att) → attAtt : var=lt·gm+gt·gm, att=lt·gm·min+gt·gm·min, rep=0
    have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin2 : e.loc 67 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 58 = e.loc 80 * e.loc 99 + e.loc 86 * e.loc 99 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [64,67,58]).addProd (-1) [64,67,80,99]).addProd (-1) [64,67,86,99])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [64,67,58]).addProd (-1) [64,67,80,99]).addProd (-1) [64,67,86,99])).eval e.loc = e.loc 64 * e.loc 67 * e.loc 58 + -1 * (e.loc 64 * e.loc 67 * e.loc 80 * e.loc 99) + -1 * (e.loc 64 * e.loc 67 * e.loc 86 * e.loc 99) from rfl, hip2, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg3|hg3 <;> rw [h,h',hg3] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 58) (b := e.loc 80 * e.loc 99 + e.loc 86 * e.loc 99) (by ring)).mp hg)
    have ha : e.loc 60 = e.loc 80 * e.loc 99 * e.loc 98 + e.loc 86 * e.loc 99 * e.loc 98 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [64,67,60]).addProd (-1) [64,67,80,99,98]).addProd (-1) [64,67,86,99,98])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [64,67,60]).addProd (-1) [64,67,80,99,98]).addProd (-1) [64,67,86,99,98])).eval e.loc = e.loc 64 * e.loc 67 * e.loc 60 + -1 * (e.loc 64 * e.loc 67 * e.loc 80 * e.loc 99 * e.loc 98) + -1 * (e.loc 64 * e.loc 67 * e.loc 86 * e.loc 99 * e.loc 98) from rfl, hip2, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg3|hg3 <;> rcases minMem with hm|hm <;> rw [h,h',hg3,hm] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 60) (b := e.loc 80 * e.loc 99 * e.loc 98 + e.loc 86 * e.loc 99 * e.loc 98) (by ring)).mp hg)
    have hr : e.loc 61 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [64,67,61])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [64,67,61])).eval e.loc = e.loc 64 * e.loc 67 * e.loc 61 from rfl, hip2, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 61) (b := 0) (by ring)).mp hg)
    rcases ltB with hl|hl <;> rcases gtB with hg2|hg2 <;> rcases gmB with hgm|hgm <;> rw [hl, hg2, hgm] at hav ha <;>
      first
      | exact ⟨by rcases minMem with h|h <;> omega, by omega,
          attRep2_of_env (by rcases minMem with h|h <;> omega) (by omega) ca60 ca61,
          decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
      | (exfalso; have := lt1 hl; have := gt1 hg2; omega)


set_option maxHeartbeats 800000 in
/-- **LEG (4′), Y axis: the score-field determination.** On a satisfying canonical trace, the `ydec`
score head equals `decScore` of the decoded X decision, and the `att`/`rep` columns are the `n = 2`
envelope (`≤ 2`). Discharges `offset_matches_chooseOffset`'s two Y hypotheses. Same 9-case shape as
`decideAxis_y_sound`. -/
theorem yScoreEval (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 107 ≤ 2 ∧ (envAt t i).loc 108 ≤ 2
    ∧ attRep2 (decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108))
    ∧ 100000 * (envAt t i).loc 105 - 100 * (envAt t i).loc 107 - (envAt t i).loc 108
        = decScore (decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108)) := by
  set e := envAt t i with he
  have hv58 : e.loc 105 = 0 ∨ e.loc 105 = 1 ∨ e.loc 105 = 2 ∨ e.loc 105 = 3 :=
    mem4_of_gate (astep_gate hsat i hi (g := memberExpr 105 [0,1,2,3]) (by decide)) (canon_loc hc i _)
  have ca60 : 0 ≤ e.loc 107 := (canon_loc hc i _).1
  have ca61 : 0 ≤ e.loc 108 := (canon_loc hc i _).1
  -- the two ray what-codes drive the 9-case split.
  have hpwm : e.loc (rWhat 2) = 0 ∨ e.loc (rWhat 2) = 1 ∨ e.loc (rWhat 2) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 2) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  have hnwm : e.loc (rWhat 3) = 0 ∨ e.loc (rWhat 3) = 1 ∨ e.loc (rWhat 3) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 3) [0, 1, 2]) (by decide)) (canon_loc hc i _)
  -- ipw/inw one-hots pick the active case's gate columns.
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := ydec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := ydec_inw_sel hsat hc i hi
  rw [← he] at iidx nidx isum nsum ib0 ib1 ib2 nb0 nb1 nb2
  -- guard soundness (distances ∈ {1,2}; the comparison bits decide the ordering, no wrap).
  obtain ⟨gpdB, gpd1, gpd0⟩ := ydec_gpd_sound hsat hc i hi
  obtain ⟨gndB, gnd1, gnd0⟩ := ydec_gnd_sound hsat hc i hi
  obtain ⟨ltB, lt1, lt0⟩ := ydec_lt_sound hsat hc i hi
  obtain ⟨gtB, gt1, gt0⟩ := ydec_gt_sound hsat hc i hi
  obtain ⟨leB, le1, le0⟩ := ydec_le_sound hsat hc i hi
  obtain ⟨gmB, gm1, gm0⟩ := ydec_gm_sound hsat hc i hi
  have hmineq := ydec_min_sound hsat hc i hi
  have pdMem := ydec_pd_mem hsat hc i hi
  have ndMem := ydec_nd_mem hsat hc i hi
  rw [← he] at gpdB gpd1 gpd0 gndB gnd1 gnd0 ltB lt1 lt0 gtB gt1 gt0 leB le1 le0 gmB gm1 gm0 hmineq pdMem ndMem
  have minMem : e.loc 145 = 1 ∨ e.loc 145 = 2 := by
    rw [hmineq]; rcases leB with h|h <;> rcases pdMem with hp|hp <;> rcases ndMem with hn|hn <;>
      rw [h, hp, hn] <;> norm_num
  -- helper to close a branch once (att,rep) columns are extracted (loc60,loc61 concrete-linear).
  rcases hpwm with hp|hp|hp <;> rcases hnwm with hn|hn|hn
  · -- (vac, vac) → none
    have hip0 : e.loc 109 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin0 : e.loc 112 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,105])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [109,112,105])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 105 from rfl, hip0, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 105) (b := 0) (by ring)).mp hg)
    have ha : e.loc 107 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,107])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [109,112,107])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 107 from rfl, hip0, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hg)
    have hr : e.loc 108 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,112,108])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [109,112,108])).eval e.loc = e.loc 109 * e.loc 112 * e.loc 108 from rfl, hip0, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hg)
    exact ⟨by omega, by omega, attRep2_of_env (by omega) (by omega) ca60 ca61,
      decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (vac, rep) → vacRep : var=2gpd, att=0, rep=gpd·nd
    have hip0 : e.loc 109 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin1 : e.loc 113 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = 2 * e.loc 115 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [109,113,105]).addProd (-2) [109,113,115])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [109,113,105]).addProd (-2) [109,113,115])).eval e.loc = e.loc 109 * e.loc 113 * e.loc 105 + -2 * (e.loc 109 * e.loc 113 * e.loc 115) from rfl, hip0, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 105) (b := 2 * e.loc 115) (by ring)).mp hg)
    have ha : e.loc 107 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,113,107])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [109,113,107])).eval e.loc = e.loc 109 * e.loc 113 * e.loc 107 from rfl, hip0, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hg)
    have hr : e.loc 108 = e.loc 115 * e.loc (rDist 3) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [109,113,108]).addProd (-1) [109,113,115, rDist 3])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [109,113,108]).addProd (-1) [109,113,115, rDist 3])).eval e.loc = e.loc 109 * e.loc 113 * e.loc 108 + -1 * (e.loc 109 * e.loc 113 * e.loc 115 * e.loc (rDist 3)) from rfl, hip0, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 108) (b := e.loc 115 * e.loc (rDist 3)) (by ring)).mp hg)
    rcases gpdB with hg|hg <;> rw [hg] at hav hr <;>
      exact ⟨by omega, by rcases ndMem with h|h <;> omega, attRep2_of_env (by rcases ndMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (vac, att) → vacAtt : var=gnd, att=gnd·nd, rep=0
    have hip0 : e.loc 109 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin2 : e.loc 114 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = e.loc 121 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [109,114,105]).addProd (-1) [109,114,121])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [109,114,105]).addProd (-1) [109,114,121])).eval e.loc = e.loc 109 * e.loc 114 * e.loc 105 + -1 * (e.loc 109 * e.loc 114 * e.loc 121) from rfl, hip0, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (a := e.loc 105) (b := e.loc 121) (by ring)).mp hg)
    have ha : e.loc 107 = e.loc 121 * e.loc (rDist 3) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [109,114,107]).addProd (-1) [109,114,121, rDist 3])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [109,114,107]).addProd (-1) [109,114,121, rDist 3])).eval e.loc = e.loc 109 * e.loc 114 * e.loc 107 + -1 * (e.loc 109 * e.loc 114 * e.loc 121 * e.loc (rDist 3)) from rfl, hip0, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 107) (b := e.loc 121 * e.loc (rDist 3)) (by ring)).mp hg)
    have hr : e.loc 108 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [109,114,108])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [109,114,108])).eval e.loc = e.loc 109 * e.loc 114 * e.loc 108 from rfl, hip0, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hg)
    rcases gndB with hg|hg <;> rw [hg] at hav ha <;>
      exact ⟨by rcases ndMem with h|h <;> omega, by omega, attRep2_of_env (by rcases ndMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (rep, vac) → repVac : var=2gnd, att=0, rep=gnd·pd
    have hip1 : e.loc 110 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin0 : e.loc 112 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = 2 * e.loc 121 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [110,112,105]).addProd (-2) [110,112,121])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [110,112,105]).addProd (-2) [110,112,121])).eval e.loc = e.loc 110 * e.loc 112 * e.loc 105 + -2 * (e.loc 110 * e.loc 112 * e.loc 121) from rfl, hip1, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 105) (b := 2 * e.loc 121) (by ring)).mp hg)
    have ha : e.loc 107 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [110,112,107])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [110,112,107])).eval e.loc = e.loc 110 * e.loc 112 * e.loc 107 from rfl, hip1, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hg)
    have hr : e.loc 108 = e.loc 121 * e.loc (rDist 2) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [110,112,108]).addProd (-1) [110,112,121, rDist 2])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [110,112,108]).addProd (-1) [110,112,121, rDist 2])).eval e.loc = e.loc 110 * e.loc 112 * e.loc 108 + -1 * (e.loc 110 * e.loc 112 * e.loc 121 * e.loc (rDist 2)) from rfl, hip1, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 108) (b := e.loc 121 * e.loc (rDist 2)) (by ring)).mp hg)
    rcases gndB with hg|hg <;> rw [hg] at hav hr <;>
      exact ⟨by omega, by rcases pdMem with h|h <;> omega, attRep2_of_env (by rcases pdMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (rep, rep) → repRep : var=2lt+2gt, att=0, rep=lt·min+gt·min
    have hip1 : e.loc 110 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin1 : e.loc 113 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = 2 * e.loc 127 + 2 * e.loc 133 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [110,113,105]).addProd (-2) [110,113,127]).addProd (-2) [110,113,133])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [110,113,105]).addProd (-2) [110,113,127]).addProd (-2) [110,113,133])).eval e.loc = e.loc 110 * e.loc 113 * e.loc 105 + -2 * (e.loc 110 * e.loc 113 * e.loc 127) + -2 * (e.loc 110 * e.loc 113 * e.loc 133) from rfl, hip1, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 105) (b := 2 * e.loc 127 + 2 * e.loc 133) (by ring)).mp hg)
    have ha : e.loc 107 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [110,113,107])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [110,113,107])).eval e.loc = e.loc 110 * e.loc 113 * e.loc 107 from rfl, hip1, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 107) (b := 0) (by ring)).mp hg)
    have hr : e.loc 108 = e.loc 127 * e.loc 145 + e.loc 133 * e.loc 145 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [110,113,108]).addProd (-1) [110,113,127,145]).addProd (-1) [110,113,133,145])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [110,113,108]).addProd (-1) [110,113,127,145]).addProd (-1) [110,113,133,145])).eval e.loc = e.loc 110 * e.loc 113 * e.loc 108 + -1 * (e.loc 110 * e.loc 113 * e.loc 127 * e.loc 145) + -1 * (e.loc 110 * e.loc 113 * e.loc 133 * e.loc 145) from rfl, hip1, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases minMem with hm|hm <;> rw [h,h',hm] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 108) (b := e.loc 127 * e.loc 145 + e.loc 133 * e.loc 145) (by ring)).mp hg)
    rcases ltB with hl|hl <;> rcases gtB with hg2|hg2 <;> rw [hl, hg2] at hav hr <;>
      first
      | exact ⟨by omega, by rcases minMem with h|h <;> omega, attRep2_of_env (by omega) (by rcases minMem with h|h <;> omega) ca60 ca61,
          decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
      | (exfalso; have := lt1 hl; have := gt1 hg2; omega)
  · -- (rep, att) → repAtt : var=3gnd, att=gnd·nd, rep=gnd·pd
    have hip1 : e.loc 110 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin2 : e.loc 114 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = 3 * e.loc 121 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [110,114,105]).addProd (-3) [110,114,121])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [110,114,105]).addProd (-3) [110,114,121])).eval e.loc = e.loc 110 * e.loc 114 * e.loc 105 + -3 * (e.loc 110 * e.loc 114 * e.loc 121) from rfl, hip1, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 105) (b := 3 * e.loc 121) (by ring)).mp hg)
    have ha : e.loc 107 = e.loc 121 * e.loc (rDist 3) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [110,114,107]).addProd (-1) [110,114,121, rDist 3])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [110,114,107]).addProd (-1) [110,114,121, rDist 3])).eval e.loc = e.loc 110 * e.loc 114 * e.loc 107 + -1 * (e.loc 110 * e.loc 114 * e.loc 121 * e.loc (rDist 3)) from rfl, hip1, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 107) (b := e.loc 121 * e.loc (rDist 3)) (by ring)).mp hg)
    have hr : e.loc 108 = e.loc 121 * e.loc (rDist 2) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [110,114,108]).addProd (-1) [110,114,121, rDist 2])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [110,114,108]).addProd (-1) [110,114,121, rDist 2])).eval e.loc = e.loc 110 * e.loc 114 * e.loc 108 + -1 * (e.loc 110 * e.loc 114 * e.loc 121 * e.loc (rDist 2)) from rfl, hip1, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gndB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 108) (b := e.loc 121 * e.loc (rDist 2)) (by ring)).mp hg)
    rcases gndB with hg|hg <;> rw [hg] at hav ha hr <;>
      exact ⟨by rcases ndMem with h|h <;> omega, by rcases pdMem with h|h <;> omega,
        attRep2_of_env (by rcases ndMem with h|h <;> omega) (by rcases pdMem with h|h <;> omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (att, vac) → attVac : var=gpd, att=gpd·pd, rep=0
    have hip2 : e.loc 111 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin0 : e.loc 112 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = e.loc 115 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [111,112,105]).addProd (-1) [111,112,115])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [111,112,105]).addProd (-1) [111,112,115])).eval e.loc = e.loc 111 * e.loc 112 * e.loc 105 + -1 * (e.loc 111 * e.loc 112 * e.loc 115) from rfl, hip2, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (a := e.loc 105) (b := e.loc 115) (by ring)).mp hg)
    have ha : e.loc 107 = e.loc 115 * e.loc (rDist 2) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [111,112,107]).addProd (-1) [111,112,115, rDist 2])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [111,112,107]).addProd (-1) [111,112,115, rDist 2])).eval e.loc = e.loc 111 * e.loc 112 * e.loc 107 + -1 * (e.loc 111 * e.loc 112 * e.loc 115 * e.loc (rDist 2)) from rfl, hip2, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 107) (b := e.loc 115 * e.loc (rDist 2)) (by ring)).mp hg)
    have hr : e.loc 108 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [111,112,108])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [111,112,108])).eval e.loc = e.loc 111 * e.loc 112 * e.loc 108 from rfl, hip2, hin0] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hg)
    rcases gpdB with hg|hg <;> rw [hg] at hav ha <;>
      exact ⟨by rcases pdMem with h|h <;> omega, by omega, attRep2_of_env (by rcases pdMem with h|h <;> omega) (by omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (att, rep) → attRep : var=3gpd, att=gpd·pd, rep=gpd·nd
    have hip2 : e.loc 111 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin1 : e.loc 113 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = 3 * e.loc 115 := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [111,113,105]).addProd (-3) [111,113,115])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [111,113,105]).addProd (-3) [111,113,115])).eval e.loc = e.loc 111 * e.loc 113 * e.loc 105 + -3 * (e.loc 111 * e.loc 113 * e.loc 115) from rfl, hip2, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 105) (b := 3 * e.loc 115) (by ring)).mp hg)
    have ha : e.loc 107 = e.loc 115 * e.loc (rDist 2) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [111,113,107]).addProd (-1) [111,113,115, rDist 2])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [111,113,107]).addProd (-1) [111,113,115, rDist 2])).eval e.loc = e.loc 111 * e.loc 113 * e.loc 107 + -1 * (e.loc 111 * e.loc 113 * e.loc 115 * e.loc (rDist 2)) from rfl, hip2, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp2|hp2 <;> rw [hp2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 107) (b := e.loc 115 * e.loc (rDist 2)) (by ring)).mp hg)
    have hr : e.loc 108 = e.loc 115 * e.loc (rDist 3) := by
      have hg := astep_gate hsat i hi (g := headToExpr ((Head.zero.addProd 1 [111,113,108]).addProd (-1) [111,113,115, rDist 3])) (by decide)
      rw [show (headToExpr ((Head.zero.addProd 1 [111,113,108]).addProd (-1) [111,113,115, rDist 3])).eval e.loc = e.loc 111 * e.loc 113 * e.loc 108 + -1 * (e.loc 111 * e.loc 113 * e.loc 115 * e.loc (rDist 3)) from rfl, hip2, hin1] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases gpdB with h|h <;> rw [h] <;> rcases ndMem with hn2|hn2 <;> rw [hn2] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 108) (b := e.loc 115 * e.loc (rDist 3)) (by ring)).mp hg)
    rcases gpdB with hg|hg <;> rw [hg] at hav ha hr <;>
      exact ⟨by rcases pdMem with h|h <;> omega, by rcases ndMem with h|h <;> omega,
        attRep2_of_env (by rcases pdMem with h|h <;> omega) (by rcases ndMem with h|h <;> omega) ca60 ca61,
        decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
  · -- (att, att) → attAtt : var=lt·gm+gt·gm, att=lt·gm·min+gt·gm·min, rep=0
    have hip2 : e.loc 111 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> rw [hp] at iidx <;> omega
    have hin2 : e.loc 114 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> rw [hn] at nidx <;> omega
    have hav : e.loc 105 = e.loc 127 * e.loc 146 + e.loc 133 * e.loc 146 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [111,114,105]).addProd (-1) [111,114,127,146]).addProd (-1) [111,114,133,146])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [111,114,105]).addProd (-1) [111,114,127,146]).addProd (-1) [111,114,133,146])).eval e.loc = e.loc 111 * e.loc 114 * e.loc 105 + -1 * (e.loc 111 * e.loc 114 * e.loc 127 * e.loc 146) + -1 * (e.loc 111 * e.loc 114 * e.loc 133 * e.loc 146) from rfl, hip2, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg3|hg3 <;> rw [h,h',hg3] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 105) (b := e.loc 127 * e.loc 146 + e.loc 133 * e.loc 146) (by ring)).mp hg)
    have ha : e.loc 107 = e.loc 127 * e.loc 146 * e.loc 145 + e.loc 133 * e.loc 146 * e.loc 145 := by
      have hg := astep_gate hsat i hi (g := headToExpr (((Head.zero.addProd 1 [111,114,107]).addProd (-1) [111,114,127,146,145]).addProd (-1) [111,114,133,146,145])) (by decide)
      rw [show (headToExpr (((Head.zero.addProd 1 [111,114,107]).addProd (-1) [111,114,127,146,145]).addProd (-1) [111,114,133,146,145])).eval e.loc = e.loc 111 * e.loc 114 * e.loc 107 + -1 * (e.loc 111 * e.loc 114 * e.loc 127 * e.loc 146 * e.loc 145) + -1 * (e.loc 111 * e.loc 114 * e.loc 133 * e.loc 146 * e.loc 145) from rfl, hip2, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) (by rcases ltB with h|h <;> rcases gtB with h'|h' <;> rcases gmB with hg3|hg3 <;> rcases minMem with hm|hm <;> rw [h,h',hg3,hm] <;> exact ⟨by norm_num, by norm_num⟩) ((gate_modEq_iff (a := e.loc 107) (b := e.loc 127 * e.loc 146 * e.loc 145 + e.loc 133 * e.loc 146 * e.loc 145) (by ring)).mp hg)
    have hr : e.loc 108 = 0 := by
      have hg := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [111,114,108])) (by decide)
      rw [show (headToExpr (Head.zero.addProd 1 [111,114,108])).eval e.loc = e.loc 111 * e.loc 114 * e.loc 108 from rfl, hip2, hin2] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (a := e.loc 108) (b := 0) (by ring)).mp hg)
    rcases ltB with hl|hl <;> rcases gtB with hg2|hg2 <;> rcases gmB with hgm|hgm <;> rw [hl, hg2, hgm] at hav ha <;>
      first
      | exact ⟨by rcases minMem with h|h <;> omega, by omega,
          attRep2_of_env (by rcases minMem with h|h <;> omega) (by omega) ca60 ca61,
          decScore_of_fields hv58 ca60 ca61 (by omega) (by omega) (by omega)⟩
      | (exfalso; have := lt1 hl; have := gt1 hg2; omega)

end ScoreEval

section MoveBits
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`xmove = [variant ≥ 1]` — SOUND.** The `xmove` `forced_ge0` bit (col 194) pins `[xdec ≠ none]`
(`variant ≥ 1`) with no wrap (`variant ∈ {0,1,2,3}` from its member gate ⇒ `|variant − 1| ≤ 2`). -/
theorem xmove_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 194 = (if 1 ≤ (envAt t i).loc 58 then 1 else 0) := by
  set e := envAt t i with he
  have h58 : e.loc 58 = 0 ∨ e.loc 58 = 1 ∨ e.loc 58 = 2 ∨ e.loc 58 = 3 :=
    mem4_of_gate (astep_gate hsat i hi (g := memberExpr 58 [0,1,2,3]) (by decide)) (canon_loc hc i _)
  have hmv : e.loc 194 = 0 ∨ e.loc 194 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin XMOVE_IB) (by decide)) (canon_loc hc i _)
  have d0 : 0 ≤ e.loc 195 ∧ e.loc 195 ≤ 1 := binBnd hsat hc i hi 195 (by decide)
  have d1 : 0 ≤ e.loc 196 ∧ e.loc 196 ≤ 1 := binBnd hsat hc i hi 196 (by decide)
  have d2 : 0 ≤ e.loc 197 ∧ e.loc 197 ≤ 1 := binBnd hsat hc i hi 197 (by decide)
  have d3 : 0 ≤ e.loc 198 ∧ e.loc 198 ≤ 1 := binBnd hsat hc i hi 198 (by decide)
  have d4 : 0 ≤ e.loc 199 ∧ e.loc 199 ≤ 1 := binBnd hsat hc i hi 199 (by decide)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 195 SMALL_RBITS)[k]!))
      (forcedGe0Term XMOVE_IB ((Head.lin 1 X_VAR).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 195 SMALL_RBITS)[k]!))
      (forcedGe0Term XMOVE_IB ((Head.lin 1 X_VAR).addConst (-1))))).eval e.loc
      = 2*(e.loc 194*e.loc 58) + -2*e.loc 194 + e.loc 194 + -1*e.loc 58 + -1*e.loc 195
        + -2*e.loc 196 + -4*e.loc 197 + -8*e.loc 198 + -16*e.loc 199 from rfl] at grec
  have gmod : (2 * e.loc 194 * (e.loc 58 - 1) + e.loc 194 - (e.loc 58 - 1) - 1)
      ≡ (e.loc 195 + 2*e.loc 196 + 4*e.loc 197 + 8*e.loc 198 + 16*e.loc 199) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have core := forcedGe0_core (ib := e.loc 194) (D := e.loc 58 - 1)
    (S := e.loc 195 + 2*e.loc 196 + 4*e.loc 197 + 8*e.loc 198 + 16*e.loc 199)
    hmv (by omega) (by omega) gmod (by omega) (by omega)
  split_ifs with hcond
  · rcases hmv with h|h
    · exact absurd (core.2 h) (by omega)
    · exact h
  · rcases hmv with h|h
    · exact h
    · exact absurd (core.1 h) (by omega)

/-- **`ymove = [variant ≥ 1]` — SOUND.** The mirror on col 200 / `ydec` variant (col 105). -/
theorem ymove_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 200 = (if 1 ≤ (envAt t i).loc 105 then 1 else 0) := by
  set e := envAt t i with he
  have h105 : e.loc 105 = 0 ∨ e.loc 105 = 1 ∨ e.loc 105 = 2 ∨ e.loc 105 = 3 :=
    mem4_of_gate (astep_gate hsat i hi (g := memberExpr 105 [0,1,2,3]) (by decide)) (canon_loc hc i _)
  have hmv : e.loc 200 = 0 ∨ e.loc 200 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin YMOVE_IB) (by decide)) (canon_loc hc i _)
  have d0 : 0 ≤ e.loc 201 ∧ e.loc 201 ≤ 1 := binBnd hsat hc i hi 201 (by decide)
  have d1 : 0 ≤ e.loc 202 ∧ e.loc 202 ≤ 1 := binBnd hsat hc i hi 202 (by decide)
  have d2 : 0 ≤ e.loc 203 ∧ e.loc 203 ≤ 1 := binBnd hsat hc i hi 203 (by decide)
  have d3 : 0 ≤ e.loc 204 ∧ e.loc 204 ≤ 1 := binBnd hsat hc i hi 204 (by decide)
  have d4 : 0 ≤ e.loc 205 ∧ e.loc 205 ≤ 1 := binBnd hsat hc i hi 205 (by decide)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 201 SMALL_RBITS)[k]!))
      (forcedGe0Term YMOVE_IB ((Head.lin 1 Y_VAR).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 201 SMALL_RBITS)[k]!))
      (forcedGe0Term YMOVE_IB ((Head.lin 1 Y_VAR).addConst (-1))))).eval e.loc
      = 2*(e.loc 200*e.loc 105) + -2*e.loc 200 + e.loc 200 + -1*e.loc 105 + -1*e.loc 201
        + -2*e.loc 202 + -4*e.loc 203 + -8*e.loc 204 + -16*e.loc 205 from rfl] at grec
  have gmod : (2 * e.loc 200 * (e.loc 105 - 1) + e.loc 200 - (e.loc 105 - 1) - 1)
      ≡ (e.loc 201 + 2*e.loc 202 + 4*e.loc 203 + 8*e.loc 204 + 16*e.loc 205) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have core := forcedGe0_core (ib := e.loc 200) (D := e.loc 105 - 1)
    (S := e.loc 201 + 2*e.loc 202 + 4*e.loc 203 + 8*e.loc 204 + 16*e.loc 205)
    hmv (by omega) (by omega) gmod (by omega) (by omega)
  split_ifs with hcond
  · rcases hmv with h|h
    · exact absurd (core.2 h) (by omega)
    · exact h
  · rcases hmv with h|h
    · exact h
    · exact absurd (core.1 h) (by omega)

/-- **LEG (4), the tie-break refinement (conditional).** The decoded offset `(ox, oy)` equals the
reference `chooseOffset` of the two decoded axis decisions, with the column rule `true`. The two
hypotheses `hsx`/`hsy` (the raw score head equals `decScore` of the decoded decision) and the
`att`/`rep ≤ 2` envelope are the §4.13 residual — the `decide_axis` field-value determination. -/
theorem offset_matches_chooseOffset (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208))
      = chooseOffset
          (decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61))
          (decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108))
          true := by
  -- LEG (4′) DISCHARGES the score-field determination — the capstone is UNCONDITIONAL.
  obtain ⟨h60, h61, hxe, hsx⟩ := xScoreEval hsat hc i hi
  obtain ⟨h107, h108, hye, hsy⟩ := yScoreEval hsat hc i hi
  set dx := decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61) with hdx
  set dy := decodeDecision ((envAt t i).loc 105) ((envAt t i).loc 106) ((envAt t i).loc 107) ((envAt t i).loc 108) with hdy
  -- field ranges
  have h58 : (envAt t i).loc 58 = 0 ∨ (envAt t i).loc 58 = 1 ∨ (envAt t i).loc 58 = 2 ∨ (envAt t i).loc 58 = 3 :=
    mem4_of_gate (astep_gate hsat i hi (g := memberExpr 58 [0,1,2,3]) (by decide)) (canon_loc hc i _)
  have h105 : (envAt t i).loc 105 = 0 ∨ (envAt t i).loc 105 = 1 ∨ (envAt t i).loc 105 = 2 ∨ (envAt t i).loc 105 = 3 :=
    mem4_of_gate (astep_gate hsat i hi (g := memberExpr 105 [0,1,2,3]) (by decide)) (canon_loc hc i _)
  have hp59 : (envAt t i).loc 59 = 0 ∨ (envAt t i).loc 59 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 59) (by decide)) (canon_loc hc i _)
  have hp106 : (envAt t i).loc 106 = 0 ∨ (envAt t i).loc 106 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 106) (by decide)) (canon_loc hc i _)
  -- score compare bit soundness
  have hsgt := sgt_of_sat hsat hc i hi (by omega) h60 h61 (by omega) h107 h108
  have hsgtb : (envAt t i).loc 152 = 0 ∨ (envAt t i).loc 152 = 1 := hsgt.1
  -- move bits (and their {0,1} membership)
  have hxm := xmove_of_sat hsat hc i hi
  have hym := ymove_of_sat hsat hc i hi
  have hxmb : (envAt t i).loc 194 = 0 ∨ (envAt t i).loc 194 = 1 := by rw [hxm]; split_ifs <;> simp
  have hymb : (envAt t i).loc 200 = 0 ∨ (envAt t i).loc 200 = 1 := by rw [hym]; split_ifs <;> simp
  -- offset membership + congruence -> decodeOff values
  have hoxtri := (offset_of_sat hsat hc i hi).1
  have hoytri := (offset_of_sat hsat hc i hi).2
  have hoxv : decodeOff ((envAt t i).loc 207)
      = (envAt t i).loc 152 * ((envAt t i).loc 194 * (2 * (envAt t i).loc 59 - 1)) := by
    refine decodeOff_eq_of hoxtri ?_ ?_
    · rcases hsgtb with h|h <;> rcases hxmb with h2|h2 <;> rcases hp59 with h3|h3 <;>
        rw [h, h2, h3] <;> norm_num
    · calc (envAt t i).loc 207
          ≡ 2 * ((envAt t i).loc 152 * (envAt t i).loc 194 * (envAt t i).loc 59)
              - (envAt t i).loc 152 * (envAt t i).loc 194 [ZMOD 2013265921] := ox_of_sat hsat hc i hi
        _ = (envAt t i).loc 152 * ((envAt t i).loc 194 * (2 * (envAt t i).loc 59 - 1)) := by ring
  have hoyv : decodeOff ((envAt t i).loc 208)
      = (1 - (envAt t i).loc 152) * ((envAt t i).loc 200 * (2 * (envAt t i).loc 106 - 1)) := by
    refine decodeOff_eq_of hoytri ?_ ?_
    · rcases hsgtb with h|h <;> rcases hymb with h2|h2 <;> rcases hp106 with h3|h3 <;>
        rw [h, h2, h3] <;> norm_num
    · calc (envAt t i).loc 208
          ≡ (envAt t i).loc 200 * (2 * (envAt t i).loc 106 - 1) * (1 - (envAt t i).loc 152) [ZMOD 2013265921] := oy_of_sat hsat hc i hi
        _ = (1 - (envAt t i).loc 152) * ((envAt t i).loc 200 * (2 * (envAt t i).loc 106 - 1)) := by ring
  -- x-delta / y-delta of the decoded decisions
  have hdeltax : (dx.delta (1, 0)).1 = (envAt t i).loc 194 * (2 * (envAt t i).loc 59 - 1) := by
    rw [hdx, decodeDecision_delta_x_fst _ _ _ _ h58 hp59, hxm]
  have hdeltay : (dy.delta (0, 1)).2 = (envAt t i).loc 200 * (2 * (envAt t i).loc 106 - 1) := by
    rw [hdy, decodeDecision_delta_y_snd _ _ _ _ h105 hp106, hym]
  -- sgt = [decisionCmp dx dy = gt]
  have hcmpiff := decisionCmp_gt_iff_score dx dy hxe hye
  rw [← hsx, ← hsy] at hcmpiff
  -- case on the decision order
  rcases Dregg2.Games.Automatafl.decisionCmp_total dx dy with hcmp|hcmp|hcmp
  · -- lt : not gt, so sgt = 0
    have hsgt0 : (envAt t i).loc 152 = 0 := by
      rcases hsgtb with h|h
      · exact h
      · have := hcmpiff.mpr (hsgt.2.1 h); rw [hcmp] at this; exact absurd this (by decide)
    have hchoose : chooseOffset dx dy true = dy.delta (0, 1) := by simp only [chooseOffset, hcmp]
    rw [hchoose]
    apply Prod.ext
    · rw [hoxv, hsgt0, decodeDecision_delta_y_fst]; ring
    · rw [hoyv, hsgt0, hdeltay]; ring
  · -- eq : not gt, sgt = 0
    have hsgt0 : (envAt t i).loc 152 = 0 := by
      rcases hsgtb with h|h
      · exact h
      · have := hcmpiff.mpr (hsgt.2.1 h); rw [hcmp] at this; exact absurd this (by decide)
    have hchoose : chooseOffset dx dy true = dy.delta (0, 1) := by simp only [chooseOffset, hcmp]
    rw [hchoose]
    apply Prod.ext
    · rw [hoxv, hsgt0, decodeDecision_delta_y_fst]; ring
    · rw [hoyv, hsgt0, hdeltay]; ring
  · -- gt : sgt = 1
    have hsgt1 : (envAt t i).loc 152 = 1 := by
      rcases hsgtb with h|h
      · have h1 := hsgt.2.2 h; have h2 := hcmpiff.mp hcmp; omega
      · exact h
    have hchoose : chooseOffset dx dy true = dx.delta (1, 0) := by simp only [chooseOffset, hcmp]
    rw [hchoose]
    apply Prod.ext
    · rw [hoxv, hsgt1, hdeltax]; ring
    · rw [hoyv, hsgt1, decodeDecision_delta_x_snd]; ring

/-! ## §4.13b — LEGS (1)-(4) COMPOSED: the offset columns ARE the reference `automatonOffset`.

Gluing the closed sub-lemmas: the four `raycast_*_of_sat` (leg 2) turn each `evaluateAxis` argument
into the true `Board.raycast` of the decoded board; `decideAxis_x/y_sound` (leg 3) fold the two axes
into `decodeDecision`; `offset_matches_chooseOffset` (leg 4, UNCONDITIONAL after leg 4′) equates the
decoded offset to `chooseOffset`. The result: the witnessed `(decodeOff ox, decodeOff oy)` IS
`automatonOffset (boardDecode e)` — the reference daemon's chosen step over the decoded OLD board.
This is the whole front half of the automaton step (position → rays → decision → offset), proven
UNCONDITIONALLY over the byte-pinned emitted object. The only piece left for the full capstone is
leg (5) — the board-update fold moving the automaton by this offset. -/
theorem automatonOffset_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Dregg2.Games.Automatafl.automatonOffset (boardDecode (envAt t i))
      = (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208)) := by
  have hxp := raycast_xp_of_sat hsat hc i hi
  have hxn := raycast_xn_of_sat hsat hc i hi
  have hyp := raycast_yp_of_sat hsat hc i hi
  have hyn := raycast_yn_of_sat hsat hc i hi
  have hx := decideAxis_x_sound hsat hc i hi
  have hy := decideAxis_y_sound hsat hc i hi
  have hoff := offset_matches_chooseOffset hsat hc i hi
  unfold Dregg2.Games.Automatafl.automatonOffset
  rw [show (boardDecode (envAt t i)).useColumnRule = true from rfl, hxp, hxn, hyp, hyn, ← hx, ← hy]
  exact hoff.symm

end MoveBits

/-! ## §4.14 — NON-VACUITY for leg (4): the `ox` gate REJECTS a score-forbidden move (`#guard`).

The `ox` offset gate `ox − 2·sgt·xmove·posx + sgt·xmove` is a two-sided discriminator: with `sgt = 1`,
`xmove = 1`, `posx = 1` it ACCEPTS `ox = 1` (the Automaton steps `+x`), and with `sgt = 0` (the score
compare did NOT hand the win to `x`) it REJECTS a witness that still claims `ox = 1` — the exact "a
wrong offset the score-compare forbids makes `Satisfied2` false" tooth. -/

/-- The `ox` offset gate body `ox − 2·sgt·xmove·posx + sgt·xmove`. -/
def oxGateExpr : EmittedExpr :=
  headToExpr (((Head.lin 1 OX_C).addProd (-2) [SGT_IB, XMOVE_IB, X_POS]).addProd 1 [SGT_IB, XMOVE_IB])
/-- `sgt = xmove = posx = 1`, `ox = 1`: the `x`-axis genuinely won the score compare and the step is
`+x` — consistent, the gate HOLDS. -/
def oxGoodAsg : Assignment := fun c => if c = 152 ∨ c = 194 ∨ c = 59 ∨ c = 207 then 1 else 0
/-- `ox = 1` claimed while `sgt = 0` (the score compare did NOT give `x` the win) — a FORBIDDEN move;
the gate FAILS. -/
def oxForgeAsg : Assignment := fun c => if c = 207 then 1 else 0

#guard oxGateExpr.eval oxGoodAsg == 0     -- sgt·xmove·posx step, ox = 1: consistent, gate holds
#guard oxGateExpr.eval oxForgeAsg != 0    -- ox = 1 but sgt = 0: score-forbidden move FAILS

/-! ## §4.15 — LEG (5): the step + board-update fold ⇒ `boardDecode(new) = automatonStep(old)`.

The step gates read the offset `(OX,OY)`, compute the target `(ax+ox, ay+oy)`, and gate the move
flag `m = offnz·tib·targ_vac` (offset nonzero · target in bounds · target vacant). The four
board-update equalities then rewrite each cell: at the target the AUTO particle appears, at the auto
cell vacuum, elsewhere the old cell is preserved — exactly `automatonStep`'s `stepTo`. This section
extracts each factor of `m` from the emitted gates (no wraparound, keyed on the byte-pinned object),
composes them into `m = [guard]`, and folds the four cell equalities into the `cellAt` of the
reference stepped board. -/

section Leg5
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`forcedGe0` NO-WRAP soundness, MOD form.** As `forcedGe0_core`, but the compared quantity `D`
may be a LARGE field value congruent to a SMALL `D'` (the offset felt `p−1 ≡ −1` makes the target
coordinate `ax + ox` large as a field element). The bit still decides `[D' ≥ 0]`: `ib∈{0,1}` folds the
`ib·D` term to `ib·D'` mod `p`, and the 5-bit range-sum pins the small residue with no aliasing. -/
theorem forcedGe0_core_mod {ib D D' S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 31)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDD' : D ≡ D' [ZMOD 2013265921]) (hlo : -100 ≤ D') (hhi : D' ≤ 100) :
    (ib = 1 → 0 ≤ D') ∧ (ib = 0 → D' ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0:ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have hcong : (-D - 1) ≡ (-D' - 1) [ZMOD 2013265921] := (hDD'.neg).sub_right 1
    have hmod' : (-D' - 1) ≡ S [ZMOD 2013265921] := hcong.symm.trans hmod
    have heq : -D' - 1 = S := eq_of_modEq_win (by omega) (by omega) hmod'
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1:ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have hmod' : D' ≡ S [ZMOD 2013265921] := hDD'.symm.trans hmod
    have heq : D' = S := eq_of_modEq_win (by omega) (by omega) hmod'
    exact ⟨by intro _; omega, by intro hc; omega⟩

/-- A `{0,1,p−1}` offset column is congruent to its small signed decode `decodeOff` mod `p`. -/
theorem decodeOff_modEq {z : ℤ} (h : z = 0 ∨ z = 1 ∨ z = 2013265920) :
    z ≡ decodeOff z [ZMOD 2013265921] := by
  rcases h with h | h | h <;> subst z <;> unfold decodeOff
  · rw [if_neg (by norm_num)]
  · rw [if_neg (by norm_num)]
  · rw [if_pos rfl]; exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩

/-- The small signed decode of a `{0,1,p−1}` offset column is `0`, `1`, or `−1`. -/
theorem decodeOff_val {z : ℤ} (h : z = 0 ∨ z = 1 ∨ z = 2013265920) :
    decodeOff z = 0 ∨ decodeOff z = 1 ∨ decodeOff z = -1 := by
  rcases h with h | h | h <;> subst z <;> unfold decodeOff
  · rw [if_neg (by norm_num)]; left; rfl
  · rw [if_neg (by norm_num)]; right; left; rfl
  · rw [if_pos rfl]; right; right; rfl

/-- **The decoded offset is one of the five cardinal steps** — leg (4) composed: the daemon's chosen
offset over the decoded board, read off the two offset columns. -/
theorem offCard_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208)) = ((1:ℤ), (0:ℤ))
      ∨ (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208)) = ((-1:ℤ), (0:ℤ))
      ∨ (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208)) = ((0:ℤ), (1:ℤ))
      ∨ (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208)) = ((0:ℤ), (-1:ℤ))
      ∨ (decodeOff ((envAt t i).loc 207), decodeOff ((envAt t i).loc 208)) = ((0:ℤ), (0:ℤ)) := by
  have hcases := Dregg2.Games.Automatafl.automatonOffset_cases (boardDecode (envAt t i))
  rw [automatonOffset_of_sat hsat hc i hi] at hcases
  exact hcases

/-- **`offnz = ox² + oy²`** — the move-nonzero column (246) equals the sum of the squared decoded
offset components. With the cardinal-step membership this is `0` (no move) or `1` (a step). -/
theorem offnz_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 246
      = decodeOff ((envAt t i).loc 207) * decodeOff ((envAt t i).loc 207)
        + decodeOff ((envAt t i).loc 208) * decodeOff ((envAt t i).loc 208) := by
  set e := envAt t i with he
  obtain ⟨hoxtri, hoytri⟩ := offset_of_sat hsat hc i hi
  simp only [OX_C, OY_C] at hoxtri hoytri
  have hoxm : e.loc 207 ≡ decodeOff (e.loc 207) [ZMOD 2013265921] := decodeOff_modEq hoxtri
  have hoym : e.loc 208 ≡ decodeOff (e.loc 208) [ZMOD 2013265921] := decodeOff_modEq hoytri
  have hg := astep_gate hsat i hi
    (g := headToExpr (((Head.lin 1 246).addProd (-1) [207, 207]).addProd (-1) [208, 208])) (by decide)
  rw [show (headToExpr (((Head.lin 1 246).addProd (-1) [207, 207]).addProd (-1) [208, 208])).eval e.loc
      = e.loc 246 + -1 * (e.loc 207 * e.loc 207) + -1 * (e.loc 208 * e.loc 208) from rfl] at hg
  have hmod : e.loc 246 ≡ e.loc 207 * e.loc 207 + e.loc 208 * e.loc 208 [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  have hsq : e.loc 207 * e.loc 207 + e.loc 208 * e.loc 208
      ≡ decodeOff (e.loc 207) * decodeOff (e.loc 207) + decodeOff (e.loc 208) * decodeOff (e.loc 208)
        [ZMOD 2013265921] := Int.ModEq.add (hoxm.mul hoxm) (hoym.mul hoym)
  have hfin := hmod.trans hsq
  have hcanRHS : Canon (decodeOff (e.loc 207) * decodeOff (e.loc 207)
      + decodeOff (e.loc 208) * decodeOff (e.loc 208)) := by
    rcases decodeOff_val hoxtri with h | h | h <;> rcases decodeOff_val hoytri with h' | h' | h' <;>
      rw [h, h'] <;> exact ⟨by norm_num, by norm_num⟩
  exact eq_of_modEq_canon (canon_loc hc i _) hcanRHS hfin

/-- Turn a `forced_ge0` bit's two-sided soundness into a clean iff. -/
theorem ge0_iff {ib D' : ℤ} (hbool : ib = 0 ∨ ib = 1)
    (h : (ib = 1 → 0 ≤ D') ∧ (ib = 0 → D' ≤ -1)) : ib = 1 ↔ 0 ≤ D' := by
  constructor
  · exact h.1
  · intro hd; rcases hbool with hb | hb
    · have := h.2 hb; omega
    · exact hb

set_option maxHeartbeats 800000 in
/-- Edge (col 209): `[ax + ox ≥ 0]` — target lower-`x` in bounds. -/
theorem txlo_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 209 = 0 ∨ (envAt t i).loc 209 = 1)
    ∧ ((envAt t i).loc 209 = 1 ↔ 0 ≤ (envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)) := by
  set e := envAt t i with he
  have hax : e.loc 8 = 0 ∨ e.loc 8 = 1 := by
    have := coord_of_sat hsat hc i hi; simp only [AX] at this; exact this.1
  obtain ⟨hoxtri, _⟩ := offset_of_sat hsat hc i hi; simp only [OX_C] at hoxtri
  have hoxm := decodeOff_modEq hoxtri; have hdox := decodeOff_val hoxtri
  have e1B : e.loc 209 = 0 ∨ e.loc 209 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 209) (by decide)) (canon_loc hc i _)
  have e1b0 : e.loc 210 = 0 ∨ e.loc 210 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 210) (by decide)) (canon_loc hc i _)
  have e1b1 : e.loc 211 = 0 ∨ e.loc 211 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 211) (by decide)) (canon_loc hc i _)
  have e1b2 : e.loc 212 = 0 ∨ e.loc 212 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 212) (by decide)) (canon_loc hc i _)
  have e1b3 : e.loc 213 = 0 ∨ e.loc 213 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 213) (by decide)) (canon_loc hc i _)
  have e1b4 : e.loc 214 = 0 ∨ e.loc 214 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 214) (by decide)) (canon_loc hc i _)
  have e1rec := astep_gate hsat i hi (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 210 SMALL_RBITS)[k]!))
      (forcedGe0Term 209 ((Head.lin 1 AX).addLin 1 OX_C)))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 210 SMALL_RBITS)[k]!))
      (forcedGe0Term 209 ((Head.lin 1 AX).addLin 1 OX_C)))).eval e.loc
      = 2 * (e.loc 209 * e.loc 8) + 2 * (e.loc 209 * e.loc 207) + e.loc 209 + -1 * e.loc 8 + -1 * e.loc 207
        + -1 * e.loc 210 + -2 * e.loc 211 + -4 * e.loc 212 + -8 * e.loc 213 + -16 * e.loc 214 + -1 from rfl] at e1rec
  have e1mod : (2 * e.loc 209 * (e.loc 8 + e.loc 207) + e.loc 209 - (e.loc 8 + e.loc 207) - 1)
      ≡ (e.loc 210 + 2 * e.loc 211 + 4 * e.loc 212 + 8 * e.loc 213 + 16 * e.loc 214) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp e1rec
  have e1core := forcedGe0_core_mod (D := e.loc 8 + e.loc 207) (D' := e.loc 8 + decodeOff (e.loc 207))
    (S := e.loc 210 + 2 * e.loc 211 + 4 * e.loc 212 + 8 * e.loc 213 + 16 * e.loc 214) e1B
    (by rcases e1b0 with h|h <;> rcases e1b1 with h1|h1 <;> rcases e1b2 with h2|h2 <;> rcases e1b3 with h3|h3 <;> rcases e1b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases e1b0 with h|h <;> rcases e1b1 with h1|h1 <;> rcases e1b2 with h2|h2 <;> rcases e1b3 with h3|h3 <;> rcases e1b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    e1mod (Int.ModEq.add_left (e.loc 8) hoxm)
    (by rcases hax with h|h <;> rcases hdox with h'|h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases hax with h|h <;> rcases hdox with h'|h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨e1B, ge0_iff e1B e1core⟩

set_option maxHeartbeats 800000 in
/-- Edge (col 215): `[ax + ox ≤ n−1]` — target upper-`x` in bounds. -/
theorem txhi_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 215 = 0 ∨ (envAt t i).loc 215 = 1)
    ∧ ((envAt t i).loc 215 = 1 ↔ (envAt t i).loc 8 + decodeOff ((envAt t i).loc 207) ≤ 1) := by
  set e := envAt t i with he
  have hax : e.loc 8 = 0 ∨ e.loc 8 = 1 := by
    have := coord_of_sat hsat hc i hi; simp only [AX] at this; exact this.1
  obtain ⟨hoxtri, _⟩ := offset_of_sat hsat hc i hi; simp only [OX_C] at hoxtri
  have hoxm := decodeOff_modEq hoxtri; have hdox := decodeOff_val hoxtri
  have e2B : e.loc 215 = 0 ∨ e.loc 215 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 215) (by decide)) (canon_loc hc i _)
  have e2b0 : e.loc 216 = 0 ∨ e.loc 216 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 216) (by decide)) (canon_loc hc i _)
  have e2b1 : e.loc 217 = 0 ∨ e.loc 217 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 217) (by decide)) (canon_loc hc i _)
  have e2b2 : e.loc 218 = 0 ∨ e.loc 218 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 218) (by decide)) (canon_loc hc i _)
  have e2b3 : e.loc 219 = 0 ∨ e.loc 219 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 219) (by decide)) (canon_loc hc i _)
  have e2b4 : e.loc 220 = 0 ∨ e.loc 220 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 220) (by decide)) (canon_loc hc i _)
  have e2rec := astep_gate hsat i hi (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 216 SMALL_RBITS)[k]!))
      (forcedGe0Term 215 (((Head.c ((NN : ℤ) - 1)).addLin (-1) AX).addLin (-1) OX_C)))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 216 SMALL_RBITS)[k]!))
      (forcedGe0Term 215 (((Head.c ((NN : ℤ) - 1)).addLin (-1) AX).addLin (-1) OX_C)))).eval e.loc
      = -2 * (e.loc 215 * e.loc 8) + -2 * (e.loc 215 * e.loc 207) + 2 * e.loc 215 + e.loc 215 + e.loc 8 + e.loc 207
        + -1 * e.loc 216 + -2 * e.loc 217 + -4 * e.loc 218 + -8 * e.loc 219 + -16 * e.loc 220 + -2 from rfl] at e2rec
  have e2mod : (2 * e.loc 215 * (1 - e.loc 8 - e.loc 207) + e.loc 215 - (1 - e.loc 8 - e.loc 207) - 1)
      ≡ (e.loc 216 + 2 * e.loc 217 + 4 * e.loc 218 + 8 * e.loc 219 + 16 * e.loc 220) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp e2rec
  have e2core := forcedGe0_core_mod (D := 1 - e.loc 8 - e.loc 207) (D' := 1 - e.loc 8 - decodeOff (e.loc 207))
    (S := e.loc 216 + 2 * e.loc 217 + 4 * e.loc 218 + 8 * e.loc 219 + 16 * e.loc 220) e2B
    (by rcases e2b0 with h|h <;> rcases e2b1 with h1|h1 <;> rcases e2b2 with h2|h2 <;> rcases e2b3 with h3|h3 <;> rcases e2b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases e2b0 with h|h <;> rcases e2b1 with h1|h1 <;> rcases e2b2 with h2|h2 <;> rcases e2b3 with h3|h3 <;> rcases e2b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    e2mod (Int.ModEq.sub_left (1 - e.loc 8) hoxm)
    (by rcases hax with h|h <;> rcases hdox with h'|h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases hax with h|h <;> rcases hdox with h'|h'|h' <;> rw [h,h'] <;> norm_num)
  refine ⟨e2B, ?_⟩; have := ge0_iff e2B e2core; rw [this]; omega

set_option maxHeartbeats 800000 in
/-- Edge (col 221): `[ay + oy ≥ 0]` — target lower-`y` in bounds. -/
theorem tylo_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 221 = 0 ∨ (envAt t i).loc 221 = 1)
    ∧ ((envAt t i).loc 221 = 1 ↔ 0 ≤ (envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)) := by
  set e := envAt t i with he
  have hay : e.loc 9 = 0 ∨ e.loc 9 = 1 := by
    have := coord_of_sat hsat hc i hi; simp only [AY] at this; exact this.2
  obtain ⟨_, hoytri⟩ := offset_of_sat hsat hc i hi; simp only [OY_C] at hoytri
  have hoym := decodeOff_modEq hoytri; have hdoy := decodeOff_val hoytri
  have e3B : e.loc 221 = 0 ∨ e.loc 221 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 221) (by decide)) (canon_loc hc i _)
  have e3b0 : e.loc 222 = 0 ∨ e.loc 222 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 222) (by decide)) (canon_loc hc i _)
  have e3b1 : e.loc 223 = 0 ∨ e.loc 223 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 223) (by decide)) (canon_loc hc i _)
  have e3b2 : e.loc 224 = 0 ∨ e.loc 224 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 224) (by decide)) (canon_loc hc i _)
  have e3b3 : e.loc 225 = 0 ∨ e.loc 225 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 225) (by decide)) (canon_loc hc i _)
  have e3b4 : e.loc 226 = 0 ∨ e.loc 226 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 226) (by decide)) (canon_loc hc i _)
  have e3rec := astep_gate hsat i hi (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 222 SMALL_RBITS)[k]!))
      (forcedGe0Term 221 ((Head.lin 1 AY).addLin 1 OY_C)))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 222 SMALL_RBITS)[k]!))
      (forcedGe0Term 221 ((Head.lin 1 AY).addLin 1 OY_C)))).eval e.loc
      = 2 * (e.loc 221 * e.loc 9) + 2 * (e.loc 221 * e.loc 208) + e.loc 221 + -1 * e.loc 9 + -1 * e.loc 208
        + -1 * e.loc 222 + -2 * e.loc 223 + -4 * e.loc 224 + -8 * e.loc 225 + -16 * e.loc 226 + -1 from rfl] at e3rec
  have e3mod : (2 * e.loc 221 * (e.loc 9 + e.loc 208) + e.loc 221 - (e.loc 9 + e.loc 208) - 1)
      ≡ (e.loc 222 + 2 * e.loc 223 + 4 * e.loc 224 + 8 * e.loc 225 + 16 * e.loc 226) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp e3rec
  have e3core := forcedGe0_core_mod (D := e.loc 9 + e.loc 208) (D' := e.loc 9 + decodeOff (e.loc 208))
    (S := e.loc 222 + 2 * e.loc 223 + 4 * e.loc 224 + 8 * e.loc 225 + 16 * e.loc 226) e3B
    (by rcases e3b0 with h|h <;> rcases e3b1 with h1|h1 <;> rcases e3b2 with h2|h2 <;> rcases e3b3 with h3|h3 <;> rcases e3b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases e3b0 with h|h <;> rcases e3b1 with h1|h1 <;> rcases e3b2 with h2|h2 <;> rcases e3b3 with h3|h3 <;> rcases e3b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    e3mod (Int.ModEq.add_left (e.loc 9) hoym)
    (by rcases hay with h|h <;> rcases hdoy with h'|h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases hay with h|h <;> rcases hdoy with h'|h'|h' <;> rw [h,h'] <;> norm_num)
  exact ⟨e3B, ge0_iff e3B e3core⟩

set_option maxHeartbeats 800000 in
/-- Edge (col 227): `[ay + oy ≤ n−1]` — target upper-`y` in bounds. -/
theorem tyhi_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 227 = 0 ∨ (envAt t i).loc 227 = 1)
    ∧ ((envAt t i).loc 227 = 1 ↔ (envAt t i).loc 9 + decodeOff ((envAt t i).loc 208) ≤ 1) := by
  set e := envAt t i with he
  have hay : e.loc 9 = 0 ∨ e.loc 9 = 1 := by
    have := coord_of_sat hsat hc i hi; simp only [AY] at this; exact this.2
  obtain ⟨_, hoytri⟩ := offset_of_sat hsat hc i hi; simp only [OY_C] at hoytri
  have hoym := decodeOff_modEq hoytri; have hdoy := decodeOff_val hoytri
  have e4B : e.loc 227 = 0 ∨ e.loc 227 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 227) (by decide)) (canon_loc hc i _)
  have e4b0 : e.loc 228 = 0 ∨ e.loc 228 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 228) (by decide)) (canon_loc hc i _)
  have e4b1 : e.loc 229 = 0 ∨ e.loc 229 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 229) (by decide)) (canon_loc hc i _)
  have e4b2 : e.loc 230 = 0 ∨ e.loc 230 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 230) (by decide)) (canon_loc hc i _)
  have e4b3 : e.loc 231 = 0 ∨ e.loc 231 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 231) (by decide)) (canon_loc hc i _)
  have e4b4 : e.loc 232 = 0 ∨ e.loc 232 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 232) (by decide)) (canon_loc hc i _)
  have e4rec := astep_gate hsat i hi (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 228 SMALL_RBITS)[k]!))
      (forcedGe0Term 227 (((Head.c ((NN : ℤ) - 1)).addLin (-1) AY).addLin (-1) OY_C)))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 228 SMALL_RBITS)[k]!))
      (forcedGe0Term 227 (((Head.c ((NN : ℤ) - 1)).addLin (-1) AY).addLin (-1) OY_C)))).eval e.loc
      = -2 * (e.loc 227 * e.loc 9) + -2 * (e.loc 227 * e.loc 208) + 2 * e.loc 227 + e.loc 227 + e.loc 9 + e.loc 208
        + -1 * e.loc 228 + -2 * e.loc 229 + -4 * e.loc 230 + -8 * e.loc 231 + -16 * e.loc 232 + -2 from rfl] at e4rec
  have e4mod : (2 * e.loc 227 * (1 - e.loc 9 - e.loc 208) + e.loc 227 - (1 - e.loc 9 - e.loc 208) - 1)
      ≡ (e.loc 228 + 2 * e.loc 229 + 4 * e.loc 230 + 8 * e.loc 231 + 16 * e.loc 232) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp e4rec
  have e4core := forcedGe0_core_mod (D := 1 - e.loc 9 - e.loc 208) (D' := 1 - e.loc 9 - decodeOff (e.loc 208))
    (S := e.loc 228 + 2 * e.loc 229 + 4 * e.loc 230 + 8 * e.loc 231 + 16 * e.loc 232) e4B
    (by rcases e4b0 with h|h <;> rcases e4b1 with h1|h1 <;> rcases e4b2 with h2|h2 <;> rcases e4b3 with h3|h3 <;> rcases e4b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases e4b0 with h|h <;> rcases e4b1 with h1|h1 <;> rcases e4b2 with h2|h2 <;> rcases e4b3 with h3|h3 <;> rcases e4b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    e4mod (Int.ModEq.sub_left (1 - e.loc 9) hoym)
    (by rcases hay with h|h <;> rcases hdoy with h'|h'|h' <;> rw [h,h'] <;> norm_num)
    (by rcases hay with h|h <;> rcases hdoy with h'|h'|h' <;> rw [h,h'] <;> norm_num)
  refine ⟨e4B, ?_⟩; have := ge0_iff e4B e4core; rw [this]; omega

/-- **`tib` — the target-in-bounds flag (col 233) is `[target on the board]`.** The four
`forced_ge0` edge bits decide the four edges, and `tib` is their product: `tib ∈ {0,1}` and `tib = 1`
exactly when the target cell `(ax+ox, ay+oy)` is in bounds (`0 ≤ · ≤ n−1` on both axes). -/
theorem tib_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 233 = 0 ∨ (envAt t i).loc 233 = 1)
    ∧ ((envAt t i).loc 233 = 1 ↔
        (0 ≤ (envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)
          ∧ (envAt t i).loc 8 + decodeOff ((envAt t i).loc 207) ≤ 1
          ∧ 0 ≤ (envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)
          ∧ (envAt t i).loc 9 + decodeOff ((envAt t i).loc 208) ≤ 1)) := by
  set e := envAt t i with he
  obtain ⟨e1B, e1iff⟩ := txlo_of_sat hsat hc i hi
  obtain ⟨e2B, e2iff⟩ := txhi_of_sat hsat hc i hi
  obtain ⟨e3B, e3iff⟩ := tylo_of_sat hsat hc i hi
  obtain ⟨e4B, e4iff⟩ := tyhi_of_sat hsat hc i hi
  have htibprod := astep_gate hsat i hi (g := headToExpr ((Head.lin 1 233).addProd (-1) [209, 215, 221, 227])) (by decide)
  rw [show (headToExpr ((Head.lin 1 233).addProd (-1) [209, 215, 221, 227])).eval e.loc
      = e.loc 233 + -1 * (e.loc 209 * e.loc 215 * e.loc 221 * e.loc 227) from rfl] at htibprod
  have htibcanon : Canon (e.loc 209 * e.loc 215 * e.loc 221 * e.loc 227) := by
    rcases e1B with h|h <;> rcases e2B with h1|h1 <;> rcases e3B with h2|h2 <;> rcases e4B with h3|h3 <;>
      rw [h,h1,h2,h3] <;> exact ⟨by norm_num, by norm_num⟩
  have htib : e.loc 233 = e.loc 209 * e.loc 215 * e.loc 221 * e.loc 227 :=
    eq_of_modEq_canon (canon_loc hc i _) htibcanon ((gate_modEq_iff (by ring)).mp htibprod)
  refine ⟨?_, ?_⟩
  · rw [htib]; rcases e1B with h|h <;> rcases e2B with h1|h1 <;> rcases e3B with h2|h2 <;> rcases e4B with h3|h3 <;>
      rw [h,h1,h2,h3] <;> norm_num
  · rw [htib]
    constructor
    · intro hp
      have hall : e.loc 209 = 1 ∧ e.loc 215 = 1 ∧ e.loc 221 = 1 ∧ e.loc 227 = 1 := by
        rcases e1B with h|h <;> rcases e2B with h1|h1 <;> rcases e3B with h2|h2 <;> rcases e4B with h3|h3 <;>
          rw [h,h1,h2,h3] at hp <;> first | exact ⟨h,h1,h2,h3⟩ | (exfalso; revert hp; norm_num)
      exact ⟨e1iff.mp hall.1, e2iff.mp hall.2.1, e3iff.mp hall.2.2.1, e4iff.mp hall.2.2.2⟩
    · rintro ⟨c1, c2, c3, c4⟩
      rw [e1iff.mpr c1, e2iff.mpr c2, e3iff.mpr c3, e4iff.mpr c4]; norm_num

/-- **The gated target read** (`read_rowcol_gated`, cols 234–238). The two one-hots (rows 235/236,
cols 237/238) are gated by `tib` (col 233): each sums to `tib` and its index is pinned to `tib·(ay+oy)`
/ `tib·(ax+ox)`, and the value `tcell` (col 234) is the dot product against the OLD board. So when
`tib = 0` every selector is `0` and `tcell = 0`; when `tib = 1` the one-hots pick the target cell. -/
theorem tread_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 235 = 0 ∨ (envAt t i).loc 235 = 1) ∧ ((envAt t i).loc 236 = 0 ∨ (envAt t i).loc 236 = 1)
    ∧ ((envAt t i).loc 237 = 0 ∨ (envAt t i).loc 237 = 1) ∧ ((envAt t i).loc 238 = 0 ∨ (envAt t i).loc 238 = 1)
    ∧ (envAt t i).loc 235 + (envAt t i).loc 236 = (envAt t i).loc 233
    ∧ (envAt t i).loc 237 + (envAt t i).loc 238 = (envAt t i).loc 233
    ∧ ((envAt t i).loc 236 ≡ (envAt t i).loc 233 * (envAt t i).loc 9 + (envAt t i).loc 233 * (envAt t i).loc 208 [ZMOD 2013265921])
    ∧ ((envAt t i).loc 238 ≡ (envAt t i).loc 233 * (envAt t i).loc 8 + (envAt t i).loc 233 * (envAt t i).loc 207 [ZMOD 2013265921])
    ∧ ((envAt t i).loc 234 ≡ (envAt t i).loc 235 * (envAt t i).loc 237 * (envAt t i).loc 0
        + (envAt t i).loc 235 * (envAt t i).loc 238 * (envAt t i).loc 1
        + (envAt t i).loc 236 * (envAt t i).loc 237 * (envAt t i).loc 2
        + (envAt t i).loc 236 * (envAt t i).loc 238 * (envAt t i).loc 3 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  have r0 : e.loc 235 = 0 ∨ e.loc 235 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 235) (by decide)) (canon_loc hc i _)
  have r1 : e.loc 236 = 0 ∨ e.loc 236 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 236) (by decide)) (canon_loc hc i _)
  have c0 : e.loc 237 = 0 ∨ e.loc 237 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 237) (by decide)) (canon_loc hc i _)
  have c1 : e.loc 238 = 0 ∨ e.loc 238 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 238) (by decide)) (canon_loc hc i _)
  have hrsum : e.loc 235 + e.loc 236 = e.loc 233 := by
    have hg := astep_gate hsat i hi (g := headToExpr ([235, 236].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 233))) (by decide)
    rw [show (headToExpr ([235, 236].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 233))).eval e.loc
        = -1 * e.loc 233 + e.loc 235 + e.loc 236 from rfl] at hg
    have hcL : Canon (e.loc 235 + e.loc 236) := by rcases r0 with h|h <;> rcases r1 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hcsum : e.loc 237 + e.loc 238 = e.loc 233 := by
    have hg := astep_gate hsat i hi (g := headToExpr ([237, 238].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 233))) (by decide)
    rw [show (headToExpr ([237, 238].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 233))).eval e.loc
        = -1 * e.loc 233 + e.loc 237 + e.loc 238 from rfl] at hg
    have hcL : Canon (e.loc 237 + e.loc 238) := by rcases c0 with h|h <;> rcases c1 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hridx : e.loc 236 ≡ e.loc 233 * e.loc 9 + e.loc 233 * e.loc 208 [ZMOD 2013265921] := by
    have hg := astep_gate hsat i hi (g := headToExpr (idxGatedHead [235, 236] 233 ((Head.lin 1 AY).addLin 1 OY_C))) (by decide)
    rw [show (headToExpr (idxGatedHead [235, 236] 233 ((Head.lin 1 AY).addLin 1 OY_C))).eval e.loc
        = e.loc 236 + -1 * (e.loc 233 * e.loc 9) + -1 * (e.loc 233 * e.loc 208) from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  have hcidx : e.loc 238 ≡ e.loc 233 * e.loc 8 + e.loc 233 * e.loc 207 [ZMOD 2013265921] := by
    have hg := astep_gate hsat i hi (g := headToExpr (idxGatedHead [237, 238] 233 ((Head.lin 1 AX).addLin 1 OX_C))) (by decide)
    rw [show (headToExpr (idxGatedHead [237, 238] 233 ((Head.lin 1 AX).addLin 1 OX_C))).eval e.loc
        = e.loc 238 + -1 * (e.loc 233 * e.loc 8) + -1 * (e.loc 233 * e.loc 207) from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  have hread : e.loc 234 ≡ e.loc 235 * e.loc 237 * e.loc 0 + e.loc 235 * e.loc 238 * e.loc 1
      + e.loc 236 * e.loc 237 * e.loc 2 + e.loc 236 * e.loc 238 * e.loc 3 [ZMOD 2013265921] := by
    have hg := astep_gate hsat i hi (g := headToExpr (readRowcolHead [235, 236] [237, 238] oldCols NN 234)) (by decide)
    rw [show (headToExpr (readRowcolHead [235, 236] [237, 238] oldCols NN 234)).eval e.loc
        = e.loc 234 + -1 * (e.loc 235 * e.loc 237 * e.loc 0) + -1 * (e.loc 235 * e.loc 238 * e.loc 1)
          + -1 * (e.loc 236 * e.loc 237 * e.loc 2) + -1 * (e.loc 236 * e.loc 238 * e.loc 3) from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  exact ⟨r0, r1, c0, c1, hrsum, hcsum, hridx, hcidx, hread⟩

/-- **`targ_vac` — the target-vacant flag (col 245).** `nz` (col 239) is the `[tcell ≥ 1]` range bit;
`targ_vac = 1 − nz`. Given the target cell is a valid particle felt (`tcell ∈ {0,1,2,3}`, the deployed
board invariant), `nz` decides `tcell ≥ 1` with no wrap and `targ_vac = 1 ↔ tcell = 0` (vacuum). -/
theorem targvac_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (htcell : (envAt t i).loc 234 = 0 ∨ (envAt t i).loc 234 = 1 ∨ (envAt t i).loc 234 = 2 ∨ (envAt t i).loc 234 = 3) :
    ((envAt t i).loc 245 = 0 ∨ (envAt t i).loc 245 = 1)
    ∧ ((envAt t i).loc 245 = 1 ↔ (envAt t i).loc 234 = 0) := by
  set e := envAt t i with he
  have nzB : e.loc 239 = 0 ∨ e.loc 239 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 239) (by decide)) (canon_loc hc i _)
  have b0 : e.loc 240 = 0 ∨ e.loc 240 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 240) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 241 = 0 ∨ e.loc 241 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 241) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 242 = 0 ∨ e.loc 242 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 242) (by decide)) (canon_loc hc i _)
  have b3 : e.loc 243 = 0 ∨ e.loc 243 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 243) (by decide)) (canon_loc hc i _)
  have b4 : e.loc 244 = 0 ∨ e.loc 244 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 244) (by decide)) (canon_loc hc i _)
  have nzrec := astep_gate hsat i hi (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 240 SMALL_RBITS)[k]!))
      (forcedGe0Term 239 ((Head.lin 1 234).addConst (-1))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom 240 SMALL_RBITS)[k]!))
      (forcedGe0Term 239 ((Head.lin 1 234).addConst (-1))))).eval e.loc
      = 2 * (e.loc 239 * e.loc 234) + -2 * e.loc 239 + e.loc 239 + -1 * e.loc 234
        + -1 * e.loc 240 + -2 * e.loc 241 + -4 * e.loc 242 + -8 * e.loc 243 + -16 * e.loc 244 from rfl] at nzrec
  have nzmod : (2 * e.loc 239 * (e.loc 234 - 1) + e.loc 239 - (e.loc 234 - 1) - 1)
      ≡ (e.loc 240 + 2 * e.loc 241 + 4 * e.loc 242 + 8 * e.loc 243 + 16 * e.loc 244) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp nzrec
  have nzcore := forcedGe0_core (D := e.loc 234 - 1)
    (S := e.loc 240 + 2 * e.loc 241 + 4 * e.loc 242 + 8 * e.loc 243 + 16 * e.loc 244) nzB
    (by rcases b0 with h|h <;> rcases b1 with h1|h1 <;> rcases b2 with h2|h2 <;> rcases b3 with h3|h3 <;> rcases b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases b0 with h|h <;> rcases b1 with h1|h1 <;> rcases b2 with h2|h2 <;> rcases b3 with h3|h3 <;> rcases b4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    nzmod (by rcases htcell with h|h|h|h <;> rw [h] <;> norm_num) (by rcases htcell with h|h|h|h <;> rw [h] <;> norm_num)
  -- targ_vac = 1 − nz
  have tvB : e.loc 245 = 1 - e.loc 239 := by
    have hg := astep_gate hsat i hi (g := headToExpr (((Head.lin 1 245).addLin 1 239).addConst (-1))) (by decide)
    rw [show (headToExpr (((Head.lin 1 245).addLin 1 239).addConst (-1))).eval e.loc = e.loc 245 + e.loc 239 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 245) (b := 1 - e.loc 239) (by ring)).mp hg
    have hcR : Canon (1 - e.loc 239) := by rcases nzB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon (canon_loc hc i _) hcR this
  refine ⟨?_, ?_⟩
  · rw [tvB]; rcases nzB with h|h <;> rw [h] <;> norm_num
  · rw [tvB]; constructor
    · intro hv
      have hnz0 : e.loc 239 = 0 := by omega
      have := nzcore.2 hnz0; omega
    · intro h0
      have hz : e.loc 239 = 0 := by
        rcases nzB with h|h
        · exact h
        · have := nzcore.1 h; omega
      omega

/-- **`m` — the move flag (col 247) is `offnz · tib · targ_vac`.** The three factors are each in
`{0,1}` (offset nonzero, target in bounds, target vacant), so `m ∈ {0,1}` and `m = 1` exactly when all
three hold — the reference `automatonStep` guard. -/
theorem moved_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hoffB : (envAt t i).loc 246 = 0 ∨ (envAt t i).loc 246 = 1)
    (htibB : (envAt t i).loc 233 = 0 ∨ (envAt t i).loc 233 = 1)
    (htvB : (envAt t i).loc 245 = 0 ∨ (envAt t i).loc 245 = 1) :
    (envAt t i).loc 247 = (envAt t i).loc 246 * (envAt t i).loc 233 * (envAt t i).loc 245 := by
  set e := envAt t i with he
  have hg := astep_gate hsat i hi (g := headToExpr ((Head.lin 1 247).addProd (-1) [246, 233, 245])) (by decide)
  rw [show (headToExpr ((Head.lin 1 247).addProd (-1) [246, 233, 245])).eval e.loc
      = e.loc 247 + -1 * (e.loc 246 * e.loc 233 * e.loc 245) from rfl] at hg
  have hcR : Canon (e.loc 246 * e.loc 233 * e.loc 245) := by
    rcases hoffB with h|h <;> rcases htibB with h1|h1 <;> rcases htvB with h2|h2 <;> rw [h,h1,h2] <;> exact ⟨by norm_num, by norm_num⟩
  exact eq_of_modEq_canon (canon_loc hc i _) hcR ((gate_modEq_iff (by ring)).mp hg)

/-- **The auto one-hot selectors resolve to the coordinate bits** (front-end `sel_auto_*`, cols 14–17):
`selRow[1] = ay`, `selRow[0] = 1−ay`, `selCol[1] = ax`, `selCol[0] = 1−ax`. -/
theorem autosel_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 15 = (envAt t i).loc 9 ∧ (envAt t i).loc 14 = 1 - (envAt t i).loc 9
    ∧ (envAt t i).loc 17 = (envAt t i).loc 8 ∧ (envAt t i).loc 16 = 1 - (envAt t i).loc 8 := by
  set e := envAt t i with he
  have hr15 : e.loc 15 = e.loc 9 := by
    have hg := astep_gate hsat i hi (g := headToExpr (((List.range 2).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([14,15][j]!)) Head.zero).append ((Head.lin 1 AY).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 2).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([14,15][j]!)) Head.zero).append ((Head.lin 1 AY).scale (-1)))).eval e.loc = e.loc 15 + -1 * e.loc 9 from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hrsum : e.loc 14 + e.loc 15 = 1 := by
    have hg := astep_gate hsat i hi (g := headToExpr ([14,15].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([14,15].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc = e.loc 14 + e.loc 15 + -1 from rfl] at hg
    have b14 : e.loc 14 = 0 ∨ e.loc 14 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 14) (by decide)) (canon_loc hc i _)
    have b15 : e.loc 15 = 0 ∨ e.loc 15 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 15) (by decide)) (canon_loc hc i _)
    have := (gate_modEq_iff (a := e.loc 14 + e.loc 15) (b := 1) (by ring)).mp hg
    rcases b14 with h|h <;> rcases b15 with h'|h' <;> exact eq_of_modEq_small (by rw [h,h']; norm_num) (by norm_num) this
  have hc17 : e.loc 17 = e.loc 8 := by
    have hg := astep_gate hsat i hi (g := headToExpr (((List.range 2).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([16,17][j]!)) Head.zero).append ((Head.lin 1 AX).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 2).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([16,17][j]!)) Head.zero).append ((Head.lin 1 AX).scale (-1)))).eval e.loc = e.loc 17 + -1 * e.loc 8 from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hcsum : e.loc 16 + e.loc 17 = 1 := by
    have hg := astep_gate hsat i hi (g := headToExpr ([16,17].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([16,17].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc = e.loc 16 + e.loc 17 + -1 from rfl] at hg
    have b16 : e.loc 16 = 0 ∨ e.loc 16 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 16) (by decide)) (canon_loc hc i _)
    have b17 : e.loc 17 = 0 ∨ e.loc 17 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 17) (by decide)) (canon_loc hc i _)
    have := (gate_modEq_iff (a := e.loc 16 + e.loc 17) (b := 1) (by ring)).mp hg
    rcases b16 with h|h <;> rcases b17 with h'|h' <;> exact eq_of_modEq_small (by rw [h,h']; norm_num) (by norm_num) this
  exact ⟨hr15, by omega, hc17, by omega⟩

/-- **The gated `sel_target` one-hots** (cols 248–251, `one_hot_gated` by `m` = col 247): each row/col
selector sums to `m`, with index pinned to `m·(ay+oy)` / `m·(ax+ox)`. So when `m = 0` all four are `0`;
when `m = 1` they single-hot the target cell. -/
theorem seltarg_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 248 = 0 ∨ (envAt t i).loc 248 = 1) ∧ ((envAt t i).loc 249 = 0 ∨ (envAt t i).loc 249 = 1)
    ∧ ((envAt t i).loc 250 = 0 ∨ (envAt t i).loc 250 = 1) ∧ ((envAt t i).loc 251 = 0 ∨ (envAt t i).loc 251 = 1)
    ∧ (envAt t i).loc 248 + (envAt t i).loc 249 = (envAt t i).loc 247
    ∧ (envAt t i).loc 250 + (envAt t i).loc 251 = (envAt t i).loc 247
    ∧ ((envAt t i).loc 249 ≡ (envAt t i).loc 247 * (envAt t i).loc 9 + (envAt t i).loc 247 * (envAt t i).loc 208 [ZMOD 2013265921])
    ∧ ((envAt t i).loc 251 ≡ (envAt t i).loc 247 * (envAt t i).loc 8 + (envAt t i).loc 247 * (envAt t i).loc 207 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  have r0 : e.loc 248 = 0 ∨ e.loc 248 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 248) (by decide)) (canon_loc hc i _)
  have r1 : e.loc 249 = 0 ∨ e.loc 249 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 249) (by decide)) (canon_loc hc i _)
  have c0 : e.loc 250 = 0 ∨ e.loc 250 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 250) (by decide)) (canon_loc hc i _)
  have c1 : e.loc 251 = 0 ∨ e.loc 251 = 1 := bin_of_gate (astep_gate hsat i hi (g := gBin 251) (by decide)) (canon_loc hc i _)
  have hrsum : e.loc 248 + e.loc 249 = e.loc 247 := by
    have hg := astep_gate hsat i hi (g := headToExpr ([248, 249].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 247))) (by decide)
    rw [show (headToExpr ([248, 249].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 247))).eval e.loc = -1 * e.loc 247 + e.loc 248 + e.loc 249 from rfl] at hg
    have hcL : Canon (e.loc 248 + e.loc 249) := by rcases r0 with h|h <;> rcases r1 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hcsum : e.loc 250 + e.loc 251 = e.loc 247 := by
    have hg := astep_gate hsat i hi (g := headToExpr ([250, 251].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 247))) (by decide)
    rw [show (headToExpr ([250, 251].foldl (fun h c => h.addLin 1 c) (Head.lin (-1) 247))).eval e.loc = -1 * e.loc 247 + e.loc 250 + e.loc 251 from rfl] at hg
    have hcL : Canon (e.loc 250 + e.loc 251) := by rcases c0 with h|h <;> rcases c1 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hridx : e.loc 249 ≡ e.loc 247 * e.loc 9 + e.loc 247 * e.loc 208 [ZMOD 2013265921] := by
    have hg := astep_gate hsat i hi (g := headToExpr (idxGatedHead [248, 249] 247 ((Head.lin 1 AY).addLin 1 OY_C))) (by decide)
    rw [show (headToExpr (idxGatedHead [248, 249] 247 ((Head.lin 1 AY).addLin 1 OY_C))).eval e.loc = e.loc 249 + -1 * (e.loc 247 * e.loc 9) + -1 * (e.loc 247 * e.loc 208) from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  have hcidx : e.loc 251 ≡ e.loc 247 * e.loc 8 + e.loc 247 * e.loc 207 [ZMOD 2013265921] := by
    have hg := astep_gate hsat i hi (g := headToExpr (idxGatedHead [250, 251] 247 ((Head.lin 1 AX).addLin 1 OX_C))) (by decide)
    rw [show (headToExpr (idxGatedHead [250, 251] 247 ((Head.lin 1 AX).addLin 1 OX_C))).eval e.loc = e.loc 251 + -1 * (e.loc 247 * e.loc 8) + -1 * (e.loc 247 * e.loc 207) from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  exact ⟨r0, r1, c0, c1, hrsum, hcsum, hridx, hcidx⟩

/-- **The four board-update cell equalities** (cols `new 0..3` = 4..7): each new cell is
`old + m·selTarget·(AUTO − old) − m·selAuto·old`, i.e. AUTO appears at the (`sel_target`) target
cell, vacuum at the (`sel_auto`) auto cell, and the old value is preserved elsewhere. -/
theorem boardupd_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 4 ≡ (envAt t i).loc 0 + 3 * ((envAt t i).loc 247 * (envAt t i).loc 248 * (envAt t i).loc 250)
        - (envAt t i).loc 247 * (envAt t i).loc 248 * (envAt t i).loc 250 * (envAt t i).loc 0
        - (envAt t i).loc 247 * (envAt t i).loc 14 * (envAt t i).loc 16 * (envAt t i).loc 0 [ZMOD 2013265921])
    ∧ ((envAt t i).loc 5 ≡ (envAt t i).loc 1 + 3 * ((envAt t i).loc 247 * (envAt t i).loc 248 * (envAt t i).loc 251)
        - (envAt t i).loc 247 * (envAt t i).loc 248 * (envAt t i).loc 251 * (envAt t i).loc 1
        - (envAt t i).loc 247 * (envAt t i).loc 14 * (envAt t i).loc 17 * (envAt t i).loc 1 [ZMOD 2013265921])
    ∧ ((envAt t i).loc 6 ≡ (envAt t i).loc 2 + 3 * ((envAt t i).loc 247 * (envAt t i).loc 249 * (envAt t i).loc 250)
        - (envAt t i).loc 247 * (envAt t i).loc 249 * (envAt t i).loc 250 * (envAt t i).loc 2
        - (envAt t i).loc 247 * (envAt t i).loc 15 * (envAt t i).loc 16 * (envAt t i).loc 2 [ZMOD 2013265921])
    ∧ ((envAt t i).loc 7 ≡ (envAt t i).loc 3 + 3 * ((envAt t i).loc 247 * (envAt t i).loc 249 * (envAt t i).loc 251)
        - (envAt t i).loc 247 * (envAt t i).loc 249 * (envAt t i).loc 251 * (envAt t i).loc 3
        - (envAt t i).loc 247 * (envAt t i).loc 15 * (envAt t i).loc 17 * (envAt t i).loc 3 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hg := astep_gate hsat i hi (g := headToExpr (((((Head.lin 1 (new 0)).addLin (-1) (old 0)).addProd (-AUTO) [247, 248, 250]).addProd 1 [247, 248, 250, old 0]).addProd 1 [247, selRow 0, selCol 0, old 0])) (by decide)
    rw [show (headToExpr (((((Head.lin 1 (new 0)).addLin (-1) (old 0)).addProd (-AUTO) [247, 248, 250]).addProd 1 [247, 248, 250, old 0]).addProd 1 [247, selRow 0, selCol 0, old 0])).eval e.loc
        = e.loc 4 + -1 * e.loc 0 + -3 * (e.loc 247 * e.loc 248 * e.loc 250) + e.loc 247 * e.loc 248 * e.loc 250 * e.loc 0 + e.loc 247 * e.loc 14 * e.loc 16 * e.loc 0 from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  · have hg := astep_gate hsat i hi (g := headToExpr (((((Head.lin 1 (new 1)).addLin (-1) (old 1)).addProd (-AUTO) [247, 248, 251]).addProd 1 [247, 248, 251, old 1]).addProd 1 [247, selRow 0, selCol 1, old 1])) (by decide)
    rw [show (headToExpr (((((Head.lin 1 (new 1)).addLin (-1) (old 1)).addProd (-AUTO) [247, 248, 251]).addProd 1 [247, 248, 251, old 1]).addProd 1 [247, selRow 0, selCol 1, old 1])).eval e.loc
        = e.loc 5 + -1 * e.loc 1 + -3 * (e.loc 247 * e.loc 248 * e.loc 251) + e.loc 247 * e.loc 248 * e.loc 251 * e.loc 1 + e.loc 247 * e.loc 14 * e.loc 17 * e.loc 1 from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  · have hg := astep_gate hsat i hi (g := headToExpr (((((Head.lin 1 (new 2)).addLin (-1) (old 2)).addProd (-AUTO) [247, 249, 250]).addProd 1 [247, 249, 250, old 2]).addProd 1 [247, selRow 1, selCol 0, old 2])) (by decide)
    rw [show (headToExpr (((((Head.lin 1 (new 2)).addLin (-1) (old 2)).addProd (-AUTO) [247, 249, 250]).addProd 1 [247, 249, 250, old 2]).addProd 1 [247, selRow 1, selCol 0, old 2])).eval e.loc
        = e.loc 6 + -1 * e.loc 2 + -3 * (e.loc 247 * e.loc 249 * e.loc 250) + e.loc 247 * e.loc 249 * e.loc 250 * e.loc 2 + e.loc 247 * e.loc 15 * e.loc 16 * e.loc 2 from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg
  · have hg := astep_gate hsat i hi (g := headToExpr (((((Head.lin 1 (new 3)).addLin (-1) (old 3)).addProd (-AUTO) [247, 249, 251]).addProd 1 [247, 249, 251, old 3]).addProd 1 [247, selRow 1, selCol 1, old 3])) (by decide)
    rw [show (headToExpr (((((Head.lin 1 (new 3)).addLin (-1) (old 3)).addProd (-AUTO) [247, 249, 251]).addProd 1 [247, 249, 251, old 3]).addProd 1 [247, selRow 1, selCol 1, old 3])).eval e.loc
        = e.loc 7 + -1 * e.loc 3 + -3 * (e.loc 247 * e.loc 249 * e.loc 251) + e.loc 247 * e.loc 249 * e.loc 251 * e.loc 3 + e.loc 247 * e.loc 15 * e.loc 17 * e.loc 3 from rfl] at hg
    exact (gate_modEq_iff (by ring)).mp hg

/-- **When the target is in bounds (`tib = 1`), the gated read is exactly the target OLD cell.** The
row/col one-hots resolve to `(ay+oy, ax+ox)` and the dot product picks out `old[(ay+oy)·n + (ax+ox)]`
— the cell `automatonStep` reads to decide "is the target vacant". -/
theorem tcell_target_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (htib : (envAt t i).loc 233 = 1) :
    (envAt t i).loc 234
      = (envAt t i).loc (old (((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat * NN
          + ((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat)) := by
  set e := envAt t i with he
  obtain ⟨_, r1, _, c1, hrsum, hcsum, hridx, hcidx, hread⟩ := tread_of_sat hsat hc i hi
  obtain ⟨_, htibiff⟩ := tib_of_sat hsat hc i hi
  obtain ⟨hoxtri, hoytri⟩ := offset_of_sat hsat hc i hi; simp only [OX_C, OY_C] at hoxtri hoytri
  rw [← he] at r1 c1 hrsum hcsum hridx hcidx hread htibiff hoxtri hoytri
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := htibiff.mp htib
  have hoxm := decodeOff_modEq hoxtri; have hoym := decodeOff_modEq hoytri
  have hb3 : (0:ℤ) ≤ e.loc 9 + decodeOff (e.loc 208) := hlo3
  have hb4 : e.loc 9 + decodeOff (e.loc 208) ≤ 1 := hlo4
  have hb1 : (0:ℤ) ≤ e.loc 8 + decodeOff (e.loc 207) := hlo1
  have hb2 : e.loc 8 + decodeOff (e.loc 207) ≤ 1 := hlo2
  have h236 : e.loc 236 = e.loc 9 + decodeOff (e.loc 208) := by
    have h1 := hridx; rw [htib] at h1; simp only [one_mul] at h1
    refine eq_of_modEq_small ?_ ?_ (h1.trans (Int.ModEq.add_left (e.loc 9) hoym))
    · rcases r1 with h|h <;> rw [h] <;> norm_num
    · exact ⟨by omega, by omega⟩
  have h238 : e.loc 238 = e.loc 8 + decodeOff (e.loc 207) := by
    have h1 := hcidx; rw [htib] at h1; simp only [one_mul] at h1
    refine eq_of_modEq_small ?_ ?_ (h1.trans (Int.ModEq.add_left (e.loc 8) hoxm))
    · rcases c1 with h|h <;> rw [h] <;> norm_num
    · exact ⟨by omega, by omega⟩
  have h235 : e.loc 235 = 1 - e.loc 236 := by have := hrsum; rw [htib] at this; omega
  have h237 : e.loc 237 = 1 - e.loc 238 := by have := hcsum; rw [htib] at this; omega
  rw [h235, h237] at hread
  rw [← h236, ← h238]
  rcases r1 with hr | hr <;> rcases c1 with hcl | hcl <;>
    (rw [hr, hcl] at hread ⊢
     refine eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ?_
     simpa [old, NN] using hread)

end Leg5

/-! ## §4.16 — NON-VACUITY for leg (5): the board-update gate REJECTS a wrong new cell (`#guard`).

The cell-0 board-update gate `new0 − old0 − AUTO·m·selT0 + m·selT0·old0 + m·selAuto0·old0` is a two-sided
discriminator: with `m = 1`, the target one-hot on cell 0 (`selTargRow0 = selTargCol0 = 1`), the auto
elsewhere, and `old0 = 0` it ACCEPTS `new0 = AUTO` (the automaton stepped onto the vacated target), and
REJECTS a witness that leaves `new0 = 0` (claiming the automaton did NOT appear). -/
def buCell0Expr : EmittedExpr :=
  headToExpr (((((Head.lin 1 (new 0)).addLin (-1) (old 0)).addProd (-AUTO) [247, 248, 250]).addProd 1
    [247, 248, 250, old 0]).addProd 1 [247, selRow 0, selCol 0, old 0])
/-- `m = 1`, target = cell 0 (`248 = 250 = 1`), auto elsewhere, `old0 = 0`, `new0 = AUTO = 3`: consistent. -/
def buGoodAsg : Assignment := fun c => if c = 247 ∨ c = 248 ∨ c = 250 then 1 else if c = new 0 then 3 else 0
/-- Same move but `new0 = 0` (the automaton did NOT appear on the vacated target): the gate FAILS. -/
def buForgeAsg : Assignment := fun c => if c = 247 ∨ c = 248 ∨ c = 250 then 1 else 0

#guard buCell0Expr.eval buGoodAsg == 0    -- automaton steps onto target, new0 = AUTO: gate holds
#guard buCell0Expr.eval buForgeAsg != 0   -- new0 = 0 while the step happened: FAILS

/-! ## §4.16b — NON-VACUITY for the board-cell RANGE gate (the newly-added family, `#guard`).

The `assert_member(old[c], {VAC,REP,ATT,AUTO})` gate is a two-sided discriminator: it ACCEPTS a real
particle code and REJECTS the `4` that used to be witnessable — the exact value that made the
reference decode VACUUM while the circuit's vacancy test blocked, i.e. the gap this family closed. -/

/-- The cell-0 membership gate body `old0·(old0−1)·(old0−2)·(old0−3)`. -/
def boardMemExpr : EmittedExpr := memberExpr (old 0) [0, 1, 2, 3]
/-- `old0 = ATT = 2` — a genuine particle: the gate HOLDS. -/
def boardMemGoodAsg : Assignment := fun c => if c = old 0 then 2 else 0
/-- `old0 = 4` — the out-of-alphabet cell the old descriptor admitted: the gate FAILS. -/
def boardMemForgeAsg : Assignment := fun c => if c = old 0 then 4 else 0

#guard boardMemExpr.eval boardMemGoodAsg == 0     -- a real particle code: accepted
#guard boardMemExpr.eval boardMemForgeAsg != 0    -- old0 = 4 (decodes VACUUM, blocks the circuit): REJECTED

/-! ## §4.17 — LEG (5) CAPSTONE: `boardDecode(new) = automatonStep(boardDecode old)`.

Composing every leg-5 extraction with `automatonOffset_of_sat` (the offset, legs 1–4): on a satisfying
canonical trace the emitted NEW columns decode, cell by cell, to the reference automaton step applied
to the decoded OLD board. The move flag `m` (col 247) equals the reference guard, and the four
board-update equalities move the AUTO particle onto the vacated target (or leave the board fixed when
blocked). The OLD-board particle-validity envelope is NOT a hypothesis here: the descriptor's
`boardRangeConstraints` assert it and `boardvalid_of_sat` reads it off the emitted gates. -/

section Leg5Capstone
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The OLD board columns are valid particle felts** — read straight off the descriptor's
`boardRangeConstraints` (`assert_member(old[c], {0,1,2,3})`, §4 of the emitter). This is the lemma
that closes the leg-5 GAP: earlier drafts carried this envelope as an `hvalid` HYPOTHESIS because the
emitted gate set range-checked only the decision variant, never the board cells — which made the
refinement FALSE over satisfying witnesses (a cell `≥ 4` decodes to VACUUM while the circuit's
vacancy test blocks). The descriptor now asserts it, so it is a THEOREM about the emitted object. -/
theorem boardvalid_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < KK) :
    ((envAt t i).loc (old c) = 0 ∨ (envAt t i).loc (old c) = 1
      ∨ (envAt t i).loc (old c) = 2 ∨ (envAt t i).loc (old c) = 3) := by
  have h4 : c < 4 := by simpa [KK, NN] using hcK
  interval_cases c
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (old 0) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (old 1) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (old 2) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (old 3) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)

/-- **The NEW board columns are valid particle felts** — the same `assert_member` family on the
CLAIMED next board, so `boardDecode`ing the `new` columns is total-and-faithful (the refinement's
conclusion is a statement about the decoded NEW board). -/
theorem newvalid_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < KK) :
    ((envAt t i).loc (new c) = 0 ∨ (envAt t i).loc (new c) = 1
      ∨ (envAt t i).loc (new c) = 2 ∨ (envAt t i).loc (new c) = 3) := by
  have h4 : c < 4 := by simpa [KK, NN] using hcK
  interval_cases c
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (new 0) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (new 1) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (new 2) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)
  · exact mem4_of_gate (astep_gate hsat i hi (g := memberExpr (new 3) [0, 1, 2, 3]) (by decide))
      (canon_loc hc i _)

/-- The target cell is a valid particle felt (`{0,1,2,3}`): out of bounds the gated read is `0`; in
bounds it is a valid OLD board cell (`boardvalid_of_sat`, off the descriptor). -/
theorem tcell_valid_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc 234 = 0 ∨ (envAt t i).loc 234 = 1 ∨ (envAt t i).loc 234 = 2 ∨ (envAt t i).loc 234 = 3 := by
  set e := envAt t i with he
  obtain ⟨htibB, htibiff⟩ := tib_of_sat hsat hc i hi
  rw [← he] at htibB htibiff
  rcases htibB with h0 | h1
  · -- tib = 0: read is 0
    obtain ⟨r0, r1, c0, c1, hrsum, hcsum, _, _, hread⟩ := tread_of_sat hsat hc i hi
    rw [← he] at r0 r1 c0 c1 hrsum hcsum hread
    rw [h0] at hrsum hcsum
    have e235 : e.loc 235 = 0 := by rcases r0 with h|h <;> rcases r1 with h'|h' <;> omega
    have e236 : e.loc 236 = 0 := by rcases r0 with h|h <;> rcases r1 with h'|h' <;> omega
    have e237 : e.loc 237 = 0 := by rcases c0 with h|h <;> rcases c1 with h'|h' <;> omega
    have e238 : e.loc 238 = 0 := by rcases c0 with h|h <;> rcases c1 with h'|h' <;> omega
    rw [e235, e236, e237, e238] at hread
    left
    refine eq_of_modEq_canon (canon_loc hc i _) canon_zero ?_
    simpa using hread
  · -- tib = 1: read is a valid OLD board cell
    have htc := tcell_target_of_sat hsat hc i hi h1
    rw [← he] at htc
    obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := htibiff.mp h1
    rw [htc]
    apply boardvalid_of_sat hsat hc i hi
    have hxb : ((e.loc 8 + decodeOff (e.loc 207)).toNat) ≤ 1 := by omega
    have hyb : ((e.loc 9 + decodeOff (e.loc 208)).toNat) ≤ 1 := by omega
    simp only [KK, NN]; omega

/-- **`m = 1` iff the three factors hold** (offset nonzero, target in bounds, target vacant). -/
theorem moved_parts_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 247 = 0 ∨ (envAt t i).loc 247 = 1)
    ∧ ((envAt t i).loc 247 = 1 ↔
        ((envAt t i).loc 246 = 1 ∧ (envAt t i).loc 233 = 1 ∧ (envAt t i).loc 245 = 1)) := by
  set e := envAt t i with he
  obtain ⟨htibB, _⟩ := tib_of_sat hsat hc i hi
  rw [← he] at htibB
  have hoffnz := offnz_of_sat hsat hc i hi
  have hoffcard := offCard_of_sat hsat hc i hi
  rw [← he] at hoffnz hoffcard
  have hoffB : e.loc 246 = 0 ∨ e.loc 246 = 1 := by
    rw [hoffnz]; rcases hoffcard with h|h|h|h|h <;>
      (simp only [Prod.mk.injEq] at h; obtain ⟨hx, hy⟩ := h; rw [hx, hy]; norm_num)
  have htcell := tcell_valid_of_sat hsat hc i hi
  rw [← he] at htcell
  obtain ⟨htvB, _⟩ := targvac_of_sat hsat hc i hi (by rw [← he]; exact htcell)
  rw [← he] at htvB
  have hmval := moved_of_sat hsat hc i hi (by rw [← he]; exact hoffB) (by rw [← he]; exact htibB) (by rw [← he]; exact htvB)
  rw [← he] at hmval
  refine ⟨?_, ?_⟩
  · rw [hmval]; rcases hoffB with h|h <;> rcases htibB with h1|h1 <;> rcases htvB with h2|h2 <;> rw [h, h1, h2] <;> norm_num
  · rw [hmval]; constructor
    · intro hp
      rcases hoffB with h|h <;> rcases htibB with h1|h1 <;> rcases htvB with h2|h2 <;>
        rw [h, h1, h2] at hp ⊢ <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; revert hp; norm_num)
    · rintro ⟨h1, h2, h3⟩; rw [h1, h2, h3]; norm_num

/-! ### §4.17b — the reference GUARD discharged, and the LEG-A CAPSTONE. -/

/-- **PURE**: one decoded board-update cell. `A` is the (0/1) target-selector product for this cell
and `B` the (0/1) auto-selector product (never both — the step is a nonzero offset, so the target is
not the vacated cell): the new cell decodes to AUTO at the target, VACUUM at the vacated auto cell,
and the old particle everywhere else — exactly `stepTo`'s three-way `if`. -/
theorem cell_update_pure {oldc newc A B : ℤ}
    (hold : oldc = 0 ∨ oldc = 1 ∨ oldc = 2 ∨ oldc = 3)
    (hA : A = 0 ∨ A = 1) (hB : B = 0 ∨ B = 1) (hAB : A = 1 → B = 0) (hcn : Canon newc)
    (h : newc ≡ oldc + 3 * A - A * oldc - B * oldc [ZMOD 2013265921]) :
    codeToParticle newc
      = if A = 1 then Particle.automaton
        else if B = 1 then Particle.vacuum else codeToParticle oldc := by
  have hb : 0 ≤ oldc ∧ oldc ≤ 3 := by rcases hold with h0|h0|h0|h0 <;> omega
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · rw [hA, hB] at h
      rw [show oldc + 3 * (0:ℤ) - 0 * oldc - 0 * oldc = oldc from by ring] at h
      have hv : newc = oldc := eq_of_modEq_canon hcn ⟨hb.1, by omega⟩ h
      rw [hv, hA, hB]; norm_num
    · rw [hA, hB] at h
      rw [show oldc + 3 * (0:ℤ) - 0 * oldc - 1 * oldc = 0 from by ring] at h
      have hv : newc = 0 := eq_of_modEq_canon hcn canon_zero h
      rw [hv, hA, hB]; norm_num [codeToParticle]
  · have hB0 : B = 0 := hAB hA
    rw [hA, hB0] at h
    rw [show oldc + 3 * (1:ℤ) - 1 * oldc - 0 * oldc = 3 from by ring] at h
    have hv : newc = 3 := eq_of_modEq_canon hcn canon_three h
    rw [hv, hA, hB0]; norm_num [codeToParticle]

/-- **The move flag IS the reference guard.** `m` (col 247) `= 1` exactly when `automatonStep`'s own
`if` fires on the DECODED board: the target is in bounds on both axes, the offset is nonzero, and the
target cell is vacuum. Every conjunct comes off the emitted gates (`tib_of_sat`, `offnz_of_sat`,
`targvac_of_sat` ▸ `tcell_target_of_sat`), with the board-cell validity now DERIVED from the
descriptor's `boardRangeConstraints` — no `hvalid` envelope. -/
theorem moved_iff_guard_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 247 = 1) ↔
      (0 ≤ ((boardDecode (envAt t i)).automaton.x : ℤ) + decodeOff ((envAt t i).loc 207)
        ∧ ((boardDecode (envAt t i)).automaton.x : ℤ) + decodeOff ((envAt t i).loc 207)
            < ((boardDecode (envAt t i)).size : ℤ)
        ∧ 0 ≤ ((boardDecode (envAt t i)).automaton.y : ℤ) + decodeOff ((envAt t i).loc 208)
        ∧ ((boardDecode (envAt t i)).automaton.y : ℤ) + decodeOff ((envAt t i).loc 208)
            < ((boardDecode (envAt t i)).size : ℤ)
        ∧ (decodeOff ((envAt t i).loc 207) ≠ 0 ∨ decodeOff ((envAt t i).loc 208) ≠ 0)
        ∧ (boardDecode (envAt t i)).cellAt
            ⟨(((boardDecode (envAt t i)).automaton.x : ℤ) + decodeOff ((envAt t i).loc 207)).toNat,
              (((boardDecode (envAt t i)).automaton.y : ℤ) + decodeOff ((envAt t i).loc 208)).toNat⟩
            = Particle.vacuum) := by
  obtain ⟨hax, hay⟩ := coord_of_sat hsat hc i hi
  have hax' : (envAt t i).loc 8 = 0 ∨ (envAt t i).loc 8 = 1 := hax
  have hay' : (envAt t i).loc 9 = 0 ∨ (envAt t i).loc 9 = 1 := hay
  have hbx : ((boardDecode (envAt t i)).automaton.x : ℤ) = (envAt t i).loc 8 := by
    show (((envAt t i).loc 8).toNat : ℤ) = (envAt t i).loc 8
    rcases hax' with h | h <;> rw [h] <;> rfl
  have hby : ((boardDecode (envAt t i)).automaton.y : ℤ) = (envAt t i).loc 9 := by
    show (((envAt t i).loc 9).toNat : ℤ) = (envAt t i).loc 9
    rcases hay' with h | h <;> rw [h] <;> rfl
  have hsz : ((boardDecode (envAt t i)).size : ℤ) = 2 := rfl
  rw [hbx, hby, hsz]
  obtain ⟨_, hmiff⟩ := moved_parts_of_sat hsat hc i hi
  obtain ⟨_, htibiff⟩ := tib_of_sat hsat hc i hi
  have hoffnz := offnz_of_sat hsat hc i hi
  have hcard := offCard_of_sat hsat hc i hi
  have htcv := tcell_valid_of_sat hsat hc i hi
  obtain ⟨_, htviff⟩ := targvac_of_sat hsat hc i hi htcv
  -- the offset-nonzero factor
  have hnziff : (envAt t i).loc 246 = 1 ↔
      (decodeOff ((envAt t i).loc 207) ≠ 0 ∨ decodeOff ((envAt t i).loc 208) ≠ 0) := by
    rw [hoffnz]
    rcases hcard with h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨hx, hy⟩ := h <;> rw [hx, hy] <;> norm_num
  -- the target-vacuum factor, under the in-bounds factor
  have hvaciff : (envAt t i).loc 233 = 1 →
      ((envAt t i).loc 245 = 1 ↔
        (boardDecode (envAt t i)).cellAt
          ⟨((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat,
            ((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat⟩ = Particle.vacuum) := by
    intro htib
    obtain ⟨b1, b2, b3, b4⟩ := htibiff.mp htib
    have htc := tcell_target_of_sat hsat hc i hi htib
    have hcell : (boardDecode (envAt t i)).cellAt
        ⟨((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat,
          ((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat⟩
        = codeToParticle ((envAt t i).loc 234) := by
      rw [htc]
      have hin : ((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat < 2
          ∧ ((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat < 2 := ⟨by omega, by omega⟩
      unfold Dregg2.Games.Automatafl.Board.cellAt
      split
      · rfl
      · next hbad => exact absurd hin hbad
    rw [hcell, htviff]
    rcases htcv with h | h | h | h <;> rw [h] <;> simp [codeToParticle]
  rw [hmiff]
  constructor
  · rintro ⟨h246, h233, h245⟩
    obtain ⟨b1, b2, b3, b4⟩ := htibiff.mp h233
    exact ⟨by omega, by omega, by omega, by omega, hnziff.mp h246, (hvaciff h233).mp h245⟩
  · rintro ⟨g1, g2, g3, g4, g5, g6⟩
    have h233 : (envAt t i).loc 233 = 1 := htibiff.mpr ⟨by omega, by omega, by omega, by omega⟩
    exact ⟨hnziff.mpr g5, h233, (hvaciff h233).mpr g6⟩

/-- The `n = 2` gated one-hot's `j`-th selector value for a target index `v ∈ {0,1}`: the emitted
`sel[0] = gate − sel[1]`, `sel[1] = v` pair, gate `= 1`. -/
def selv (v : ℤ) (j : Nat) : ℤ := if j = 0 then 1 - v else v

/-- **PURE, the per-cell three-way match.** With the target one-hot at `(TX, TY)` and the auto
one-hot at `(AX, AY)` (all four in `{0,1}`, target ≠ auto because the step is nonzero), the decoded
new cell at `(x, y)` is AUTO at the target, VACUUM at the vacated auto cell, and the old particle
elsewhere — `stepTo`'s own three-way `if`, cell for cell. -/
theorem cell_of_data {oldc newc TX TY AX AY : ℤ} {x y : Nat}
    (hx : x < 2) (hy : y < 2)
    (hTX : TX = 0 ∨ TX = 1) (hTY : TY = 0 ∨ TY = 1)
    (hAX : AX = 0 ∨ AX = 1) (hAY : AY = 0 ∨ AY = 1)
    (hne : TX ≠ AX ∨ TY ≠ AY)
    (hold : oldc = 0 ∨ oldc = 1 ∨ oldc = 2 ∨ oldc = 3) (hcn : Canon newc)
    (h : newc ≡ oldc + 3 * (selv TY y * selv TX x) - selv TY y * selv TX x * oldc
          - selv AY y * selv AX x * oldc [ZMOD 2013265921]) :
    codeToParticle newc
      = if (⟨x, y⟩ : Coord) = ⟨TX.toNat, TY.toNat⟩ then Particle.automaton
        else if (⟨x, y⟩ : Coord) = ⟨AX.toNat, AY.toNat⟩ then Particle.vacuum
        else codeToParticle oldc := by
  have hAv : selv TY y * selv TX x = 1 ↔ ((⟨x, y⟩ : Coord) = ⟨TX.toNat, TY.toNat⟩) := by
    interval_cases x <;> interval_cases y <;> rcases hTX with h1 | h1 <;> rcases hTY with h2 | h2 <;>
      subst h1 <;> subst h2 <;> simp [selv, Coord.mk.injEq]
  have hBv : selv AY y * selv AX x = 1 ↔ ((⟨x, y⟩ : Coord) = ⟨AX.toNat, AY.toNat⟩) := by
    interval_cases x <;> interval_cases y <;> rcases hAX with h1 | h1 <;> rcases hAY with h2 | h2 <;>
      subst h1 <;> subst h2 <;> simp [selv, Coord.mk.injEq]
  have hA01 : selv TY y * selv TX x = 0 ∨ selv TY y * selv TX x = 1 := by
    interval_cases x <;> interval_cases y <;> rcases hTX with h1 | h1 <;> rcases hTY with h2 | h2 <;>
      subst h1 <;> subst h2 <;> norm_num [selv]
  have hB01 : selv AY y * selv AX x = 0 ∨ selv AY y * selv AX x = 1 := by
    interval_cases x <;> interval_cases y <;> rcases hAX with h1 | h1 <;> rcases hAY with h2 | h2 <;>
      subst h1 <;> subst h2 <;> norm_num [selv]
  have hAB : selv TY y * selv TX x = 1 → selv AY y * selv AX x = 0 := by
    intro hA1
    rcases hB01 with hb | hb
    · exact hb
    · exfalso
      have h1 := hAv.mp hA1
      have h2 := hBv.mp hb
      rw [h1, Coord.mk.injEq] at h2
      rcases hTX with e1 | e1 <;> rcases hTY with e2 | e2 <;> rcases hAX with e3 | e3 <;>
        rcases hAY with e4 | e4 <;> subst e1 <;> subst e2 <;> subst e3 <;> subst e4 <;>
        revert hne h2 <;> decide
  rw [cell_update_pure hold hA01 hB01 hAB hcn h]
  by_cases hc1 : (⟨x, y⟩ : Coord) = ⟨TX.toNat, TY.toNat⟩
  · rw [if_pos hc1, if_pos (hAv.mpr hc1)]
  · rw [if_neg hc1, if_neg (fun hh => hc1 (hAv.mp hh))]
    by_cases hc2 : (⟨x, y⟩ : Coord) = ⟨AX.toNat, AY.toNat⟩
    · rw [if_pos hc2, if_pos (hBv.mpr hc2)]
    · rw [if_neg hc2, if_neg (fun hh => hc2 (hBv.mp hh))]

/-- **LEG A, CLOSED — the capstone.** On a satisfying, canonical trace of the byte-pinned
`automataflStepDesc`, the emitted NEW board columns ARE the reference automaton step applied to the
decoded OLD board: the size is preserved, the automaton sits on the witnessed target exactly when the
move flag fires, and every in-bounds cell of the decoded NEW board equals the corresponding cell of
`automatonStep (boardDecode …)`. UNCONDITIONAL — no `hvalid` envelope: the OLD/NEW board cells are
range-checked by the descriptor itself (`boardvalid_of_sat` / `newvalid_of_sat`), which is the gap the
`boardRangeConstraints` family closed. -/
theorem astep_sat_imp_automatonStep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t i))).size = NN
    ∧ (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t i))).automaton
        = (if (envAt t i).loc 247 = 1
            then (⟨((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat,
                   ((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat⟩ : Coord)
            else ⟨((envAt t i).loc 8).toNat, ((envAt t i).loc 9).toNat⟩)
    ∧ (∀ x y : Nat, x < NN → y < NN →
        codeToParticle ((envAt t i).loc (new (y * NN + x)))
          = (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t i))).cellAt ⟨x, y⟩) := by
  obtain ⟨hax0, hay0⟩ := coord_of_sat hsat hc i hi
  have hax' : (envAt t i).loc 8 = 0 ∨ (envAt t i).loc 8 = 1 := hax0
  have hay' : (envAt t i).loc 9 = 0 ∨ (envAt t i).loc 9 = 1 := hay0
  have hbx : ((boardDecode (envAt t i)).automaton.x : ℤ) = (envAt t i).loc 8 := by
    show (((envAt t i).loc 8).toNat : ℤ) = (envAt t i).loc 8
    rcases hax' with h | h <;> rw [h] <;> rfl
  have hby : ((boardDecode (envAt t i)).automaton.y : ℤ) = (envAt t i).loc 9 := by
    show (((envAt t i).loc 9).toNat : ℤ) = (envAt t i).loc 9
    rcases hay' with h | h <;> rw [h] <;> rfl
  -- the reference step, with its guard discharged against the move flag
  have hstep : Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t i))
      = if (envAt t i).loc 247 = 1
        then Dregg2.Games.Automatafl.stepTo (boardDecode (envAt t i))
              ⟨((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat,
               ((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat⟩
        else boardDecode (envAt t i) := by
    simp only [Dregg2.Games.Automatafl.automatonStep, automatonOffset_of_sat hsat hc i hi]
    by_cases hm : (envAt t i).loc 247 = 1
    · rw [if_pos hm, if_pos ((moved_iff_guard_of_sat hsat hc i hi).mp hm), hbx, hby]
    · rw [if_neg hm, if_neg (fun hg => hm ((moved_iff_guard_of_sat hsat hc i hi).mpr hg))]
  -- every in-bounds cell of `stepTo`/`boardDecode` reads through `cellAt`
  have hcellStep : ∀ (nc : Coord) (x y : Nat), x < 2 → y < 2 →
      (Dregg2.Games.Automatafl.stepTo (boardDecode (envAt t i)) nc).cellAt ⟨x, y⟩
        = if (⟨x, y⟩ : Coord) = nc then Particle.automaton
          else if (⟨x, y⟩ : Coord) = (boardDecode (envAt t i)).automaton then Particle.vacuum
          else codeToParticle ((envAt t i).loc (old (y * NN + x))) := by
    intro nc x y hx hy
    unfold Dregg2.Games.Automatafl.Board.cellAt
    split
    · rfl
    · next hbad => exact absurd (⟨hx, hy⟩ : x < NN ∧ y < NN) hbad
  have hcellOld : ∀ (x y : Nat), x < 2 → y < 2 →
      (boardDecode (envAt t i)).cellAt ⟨x, y⟩
        = codeToParticle ((envAt t i).loc (old (y * NN + x))) := by
    intro x y hx hy
    unfold Dregg2.Games.Automatafl.Board.cellAt
    split
    · rfl
    · next hbad => exact absurd (⟨hx, hy⟩ : x < NN ∧ y < NN) hbad
  obtain ⟨hmB, hmiff⟩ := moved_parts_of_sat hsat hc i hi
  refine ⟨by rw [Dregg2.Games.Automatafl.automatonStep_size]; rfl, ?_, ?_⟩
  · rw [hstep]
    by_cases hm : (envAt t i).loc 247 = 1
    · rw [if_pos hm, if_pos hm]; rfl
    · rw [if_neg hm, if_neg hm]; rfl
  · intro x y hx hy
    rw [hstep]
    by_cases hm : (envAt t i).loc 247 = 1
    · -- THE MOVE FIRED
      rw [if_pos hm]
      obtain ⟨h246, h233, h245⟩ := hmiff.mp hm
      obtain ⟨_, r1, _, c1, hrsum, hcsum, hridx, hcidx⟩ := seltarg_of_sat hsat hc i hi
      obtain ⟨h15, h14, h17, h16⟩ := autosel_of_sat hsat hc i hi
      obtain ⟨hoxtri, hoytri⟩ := offset_of_sat hsat hc i hi
      simp only [OX_C, OY_C] at hoxtri hoytri
      -- the target one-hot resolves to the target coordinates
      have h249 : (envAt t i).loc 249 = (envAt t i).loc 9 + decodeOff ((envAt t i).loc 208) := by
        have h1 := hridx; rw [hm] at h1; simp only [one_mul] at h1
        refine eq_of_modEq_small ?_ ?_ (h1.trans (Int.ModEq.add_left ((envAt t i).loc 9) (decodeOff_modEq hoytri)))
        · rcases r1 with h | h <;> rw [h] <;> norm_num
        · rcases hay' with h | h <;> rcases decodeOff_val hoytri with h' | h' | h' <;>
            rw [h, h'] <;> norm_num
      have h251 : (envAt t i).loc 251 = (envAt t i).loc 8 + decodeOff ((envAt t i).loc 207) := by
        have h1 := hcidx; rw [hm] at h1; simp only [one_mul] at h1
        refine eq_of_modEq_small ?_ ?_ (h1.trans (Int.ModEq.add_left ((envAt t i).loc 8) (decodeOff_modEq hoxtri)))
        · rcases c1 with h | h <;> rw [h] <;> norm_num
        · rcases hax' with h | h <;> rcases decodeOff_val hoxtri with h' | h' | h' <;>
            rw [h, h'] <;> norm_num
      have h248 : (envAt t i).loc 248 = 1 - (envAt t i).loc 249 := by rw [hm] at hrsum; omega
      have h250 : (envAt t i).loc 250 = 1 - (envAt t i).loc 251 := by rw [hm] at hcsum; omega
      have h14' : (envAt t i).loc 14 = 1 - (envAt t i).loc 15 := by rw [h14, h15]
      have h16' : (envAt t i).loc 16 = 1 - (envAt t i).loc 17 := by rw [h16, h17]
      -- target ≠ auto: the offset is nonzero
      have hnz : decodeOff ((envAt t i).loc 207) ≠ 0 ∨ decodeOff ((envAt t i).loc 208) ≠ 0 := by
        have hoffnz := offnz_of_sat hsat hc i hi
        rcases offCard_of_sat hsat hc i hi with h | h | h | h | h <;>
          simp only [Prod.mk.injEq] at h <;> obtain ⟨hx', hy'⟩ := h
        · left; rw [hx']; norm_num
        · left; rw [hx']; norm_num
        · right; rw [hy']; norm_num
        · right; rw [hy']; norm_num
        · exfalso; rw [hoffnz, hx', hy'] at h246; norm_num at h246
      have hne : (envAt t i).loc 251 ≠ (envAt t i).loc 17 ∨ (envAt t i).loc 249 ≠ (envAt t i).loc 15 := by
        rcases hnz with h | h
        · left; rw [h251, h17]; omega
        · right; rw [h249, h15]; omega
      have hTXb : (envAt t i).loc 251 = 0 ∨ (envAt t i).loc 251 = 1 := c1
      have hTYb : (envAt t i).loc 249 = 0 ∨ (envAt t i).loc 249 = 1 := r1
      have hAXb : (envAt t i).loc 17 = 0 ∨ (envAt t i).loc 17 = 1 := by rw [h17]; exact hax'
      have hAYb : (envAt t i).loc 15 = 0 ∨ (envAt t i).loc 15 = 1 := by rw [h15]; exact hay'
      -- the target / auto coordinates, in one-hot form
      have htgt : (⟨((envAt t i).loc 8 + decodeOff ((envAt t i).loc 207)).toNat,
                    ((envAt t i).loc 9 + decodeOff ((envAt t i).loc 208)).toNat⟩ : Coord)
          = ⟨((envAt t i).loc 251).toNat, ((envAt t i).loc 249).toNat⟩ := by rw [h249, h251]
      have hauto : (boardDecode (envAt t i)).automaton
          = (⟨((envAt t i).loc 17).toNat, ((envAt t i).loc 15).toNat⟩ : Coord) := by
        rw [h15, h17]; rfl
      -- the shape shim: with `m = 1` the move flag drops out of the board-update equalities
      have hshape : ∀ nc oc s1 s2 a1 a2 : ℤ,
          nc ≡ oc + 3 * ((envAt t i).loc 247 * s1 * s2) - (envAt t i).loc 247 * s1 * s2 * oc
                - (envAt t i).loc 247 * a1 * a2 * oc [ZMOD 2013265921] →
          nc ≡ oc + 3 * (s1 * s2) - s1 * s2 * oc - a1 * a2 * oc [ZMOD 2013265921] := by
        intro nc oc s1 s2 a1 a2 hh
        rw [hm] at hh
        rw [show oc + 3 * (s1 * s2) - s1 * s2 * oc - a1 * a2 * oc
            = oc + 3 * (1 * s1 * s2) - 1 * s1 * s2 * oc - 1 * a1 * a2 * oc from by ring]
        exact hh
      have s0y : selv ((envAt t i).loc 249) 0 = (envAt t i).loc 248 := by simp [selv, h248]
      have s1y : selv ((envAt t i).loc 249) 1 = (envAt t i).loc 249 := by simp [selv]
      have s0x : selv ((envAt t i).loc 251) 0 = (envAt t i).loc 250 := by simp [selv, h250]
      have s1x : selv ((envAt t i).loc 251) 1 = (envAt t i).loc 251 := by simp [selv]
      have a0y : selv ((envAt t i).loc 15) 0 = (envAt t i).loc 14 := by simp [selv, h14']
      have a1y : selv ((envAt t i).loc 15) 1 = (envAt t i).loc 15 := by simp [selv]
      have a0x : selv ((envAt t i).loc 17) 0 = (envAt t i).loc 16 := by simp [selv, h16']
      have a1x : selv ((envAt t i).loc 17) 1 = (envAt t i).loc 17 := by simp [selv]
      obtain ⟨hb0, hb1, hb2, hb3⟩ := boardupd_of_sat hsat hc i hi
      have hxx : x < 2 := hx
      have hyy : y < 2 := hy
      rw [hcellStep _ x y hxx hyy, htgt, hauto]
      interval_cases x <;> interval_cases y
      · exact cell_of_data (by norm_num) (by norm_num) hTXb hTYb hAXb hAYb hne
          (boardvalid_of_sat hsat hc i hi 0 (by decide)) (canon_loc hc i _)
          (by rw [s0y, s0x, a0y, a0x]; exact hshape _ _ _ _ _ _ hb0)
      · exact cell_of_data (by norm_num) (by norm_num) hTXb hTYb hAXb hAYb hne
          (boardvalid_of_sat hsat hc i hi 2 (by decide)) (canon_loc hc i _)
          (by rw [s1y, s0x, a1y, a0x]; exact hshape _ _ _ _ _ _ hb2)
      · exact cell_of_data (by norm_num) (by norm_num) hTXb hTYb hAXb hAYb hne
          (boardvalid_of_sat hsat hc i hi 1 (by decide)) (canon_loc hc i _)
          (by rw [s0y, s1x, a0y, a1x]; exact hshape _ _ _ _ _ _ hb1)
      · exact cell_of_data (by norm_num) (by norm_num) hTXb hTYb hAXb hAYb hne
          (boardvalid_of_sat hsat hc i hi 3 (by decide)) (canon_loc hc i _)
          (by rw [s1y, s1x, a1y, a1x]; exact hshape _ _ _ _ _ _ hb3)
    · -- NO MOVE: the board is unchanged, cell for cell
      rw [if_neg hm, hcellOld x y hx hy]
      have hm0 : (envAt t i).loc 247 = 0 := hmB.resolve_right hm
      have hnomove : ∀ (cn co : Nat) (s1 s2 a1 a2 : ℤ),
          (envAt t i).loc cn ≡ (envAt t i).loc co + 3 * ((envAt t i).loc 247 * s1 * s2)
                - (envAt t i).loc 247 * s1 * s2 * (envAt t i).loc co
                - (envAt t i).loc 247 * a1 * a2 * (envAt t i).loc co [ZMOD 2013265921] →
          (envAt t i).loc cn = (envAt t i).loc co := by
        intro cn co s1 s2 a1 a2 hh
        rw [hm0, show (envAt t i).loc co + 3 * ((0:ℤ) * s1 * s2) - 0 * s1 * s2 * (envAt t i).loc co
              - 0 * a1 * a2 * (envAt t i).loc co = (envAt t i).loc co from by ring] at hh
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) hh
      obtain ⟨hb0, hb1, hb2, hb3⟩ := boardupd_of_sat hsat hc i hi
      have hxx : x < 2 := hx
      have hyy : y < 2 := hy
      interval_cases x <;> interval_cases y
      · exact congrArg codeToParticle (hnomove (new 0) (old 0) _ _ _ _ hb0)
      · exact congrArg codeToParticle (hnomove (new 2) (old 2) _ _ _ _ hb2)
      · exact congrArg codeToParticle (hnomove (new 1) (old 1) _ _ _ _ hb1)
      · exact congrArg codeToParticle (hnomove (new 3) (old 3) _ _ _ _ hb3)

end Leg5Capstone

/-! ## LEG R — transport to the committed board-root public inputs. -/

/-- The canonical particle → felt code (the inverse of `codeToParticle` on `{0,1,2,3}`). -/
def particleToCode : Particle → ℤ
  | .vacuum => 0 | .repulsor => 1 | .attractor => 2 | .automaton => 3

theorem particleToCode_codeToParticle {z : ℤ}
    (h : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3) : particleToCode (codeToParticle z) = z := by
  rcases h with h | h | h | h <;> subst h <;> rfl

/-- The 16-felt `node8` absorb seed of a board: the four cell codes packed into ONE leaf
(`cells ++ 4 zeros`) folded against the all-zero sibling leaf. -/
def boardAbsorb (b : Board) : List ℤ :=
  [particleToCode (b.cellAt ⟨0, 0⟩), particleToCode (b.cellAt ⟨1, 0⟩),
   particleToCode (b.cellAt ⟨0, 1⟩), particleToCode (b.cellAt ⟨1, 1⟩)] ++ List.replicate 12 0

/-- `board_root8 b` — the 8-felt board root: the wide squeeze of the `node8` absorb seed. -/
def boardRoot8 (permOut : List ℤ → List ℤ) (b : Board) : List ℤ := permOut (boardAbsorb b)

section LegR
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

set_option maxRecDepth 40000 in
/-- The shared `mh8_zero` column IS zero (the `assert_zero` pin of `bind_board_roots`). -/
theorem mh8zero_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc MH8_ZERO = 0 := by
  have hg := astep_gate hsat i hi (g := headToExpr (Head.lin 1 MH8_ZERO)) (by decide)
  have : (envAt t i).loc MH8_ZERO ≡ 0 [ZMOD 2013265921] := by
    simpa [headToExpr, Head.lin, termToExpr, varsProd, EmittedExpr.eval] using hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_zero this

/-- A first-row `.piBinding` of the byte-pinned descriptor IS its PI congruence. -/
theorem astep_piFirst (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (h0 : 0 < t.rows.length) {col k : Nat}
    (hg : (.base (.piBinding VmRow.first col k) : VmConstraint2)
            ∈ automataflStepDesc.constraints) :
    (envAt t 0).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 h0 _ hg
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt] using hrc

/-- The decoded OLD board reads cell `(x,y)` off column `old (y·n+x)`. -/
theorem boardDecode_cellAt (e : VmRowEnv) (x y : Nat) (hx : x < 2) (hy : y < 2) :
    (boardDecode e).cellAt ⟨x, y⟩ = codeToParticle (e.loc (old (y * NN + x))) := by
  unfold Dregg2.Games.Automatafl.Board.cellAt
  split
  · rfl
  · next hbad => exact absurd (⟨hx, hy⟩ : x < NN ∧ y < NN) hbad

/-- The OLD-board `node8` absorb seed IS the four OLD cell columns, zero-padded. -/
theorem boardAbsorb_old_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    boardAbsorb (boardDecode (envAt t i))
      = [(envAt t i).loc (old 0), (envAt t i).loc (old 1), (envAt t i).loc (old 2),
         (envAt t i).loc (old 3)] ++ List.replicate 12 0 := by
  have hv := fun c hcK => boardvalid_of_sat hsat hc i hi c hcK
  have h00 := boardDecode_cellAt (envAt t i) 0 0 (by norm_num) (by norm_num)
  have h10 := boardDecode_cellAt (envAt t i) 1 0 (by norm_num) (by norm_num)
  have h01 := boardDecode_cellAt (envAt t i) 0 1 (by norm_num) (by norm_num)
  have h11 := boardDecode_cellAt (envAt t i) 1 1 (by norm_num) (by norm_num)
  norm_num [NN] at h00 h10 h01 h11
  simp only [boardAbsorb, h00, h10, h01, h11,
    particleToCode_codeToParticle (hv 0 (by norm_num [KK, NN])),
    particleToCode_codeToParticle (hv 1 (by norm_num [KK, NN])),
    particleToCode_codeToParticle (hv 2 (by norm_num [KK, NN])),
    particleToCode_codeToParticle (hv 3 (by norm_num [KK, NN]))]

/-! ### The chip-lookup → digest lemma. -/

/-- **The `node8` lookup FORCES the digest block.** A satisfied `MerkleHash8` node8 chip lookup,
against a wide-sound Poseidon2 chip table, forces its 8 output columns to be the genuine wide
squeeze of the absorbed leaf `cells ‖ 4 zeros ‖ 8 zeros` — the arity tag + equal-length padding pin
the row decomposition (`chip_lookup_sound_N`), and the `mh8_zero` pin collapses the padding to
literal zeros. -/
theorem root_of_lookupMem (permOut : List ℤ → List ℤ)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (i : Nat)
    (cells outCols : List Nat) (hcells : cells.length = 4)
    (hz : (envAt t i).loc MH8_ZERO = 0)
    (hmem : (chipLookupTupleN
        ((((cells ++ List.replicate 4 MH8_ZERO) ++ List.replicate 8 MH8_ZERO)).map
          (fun c => EmittedExpr.var c)) outCols).map (·.eval (envAt t i).loc)
        ∈ t.tf TableId.poseidon2) :
    outCols.map (envAt t i).loc
      = permOut ((cells.map (envAt t i).loc) ++ List.replicate 12 0) := by
  have hlen : (((cells ++ List.replicate 4 MH8_ZERO) ++ List.replicate 8 MH8_ZERO).map
      (fun c => EmittedExpr.var c)).length ≤ CHIP_RATE := by
    simp [hcells, CHIP_RATE]
  have h := chip_lookup_sound_N permOut (t.tf TableId.poseidon2) hSound (envAt t i).loc _ outCols
    hlen hmem
  rw [h]
  congr 1
  simp only [List.map_append, List.map_replicate, List.map_map, Function.comp_def,
    EmittedExpr.eval, hz, List.append_assoc]
  norm_num [List.replicate_add]

set_option maxRecDepth 40000 in
/-- The OLD-board `node8` chip lookup HOLDS: its evaluated tuple is a row of the chip table. -/
theorem oldRoot_lookupMem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (chipLookupTupleN
        (((([0, 1, 2, 3] ++ List.replicate 4 MH8_ZERO)) ++ List.replicate 8 MH8_ZERO).map
          (fun c => EmittedExpr.var c)) oldRootCols).map (·.eval (envAt t i).loc)
      ∈ t.tf TableId.poseidon2 := by
  have hrc := hsat.rowConstraints i hi _
    (show node8Lookup ([0, 1, 2, 3] ++ List.replicate 4 MH8_ZERO)
        (List.replicate 8 MH8_ZERO) oldRootCols ∈ automataflStepDesc.constraints by decide)
  simpa [node8Lookup, VmConstraint2.holdsAt, Lookup.holdsAt] using hrc

set_option maxRecDepth 40000 in
/-- The NEW-board `node8` chip lookup HOLDS. -/
theorem newRoot_lookupMem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (chipLookupTupleN
        (((([4, 5, 6, 7] ++ List.replicate 4 MH8_ZERO)) ++ List.replicate 8 MH8_ZERO).map
          (fun c => EmittedExpr.var c)) newRootCols).map (·.eval (envAt t i).loc)
      ∈ t.tf TableId.poseidon2 := by
  have hrc := hsat.rowConstraints i hi _
    (show node8Lookup ([4, 5, 6, 7] ++ List.replicate 4 MH8_ZERO)
        (List.replicate 8 MH8_ZERO) newRootCols ∈ automataflStepDesc.constraints by decide)
  simpa [node8Lookup, VmConstraint2.holdsAt, Lookup.holdsAt] using hrc

/-- The STEPPED board's `node8` absorb seed IS the four NEW cell columns, zero-padded — the
capstone (`astep_sat_imp_automatonStep`) read through the canonical particle encoding. -/
theorem boardAbsorb_new_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    boardAbsorb (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t i)))
      = [(envAt t i).loc (new 0), (envAt t i).loc (new 1), (envAt t i).loc (new 2),
         (envAt t i).loc (new 3)] ++ List.replicate 12 0 := by
  obtain ⟨_, _, hcell⟩ := astep_sat_imp_automatonStep hsat hc i hi
  have hv := fun c hcK => newvalid_of_sat hsat hc i hi c hcK
  have h00 := (hcell 0 0 (by norm_num [NN]) (by norm_num [NN])).symm
  have h10 := (hcell 1 0 (by norm_num [NN]) (by norm_num [NN])).symm
  have h01 := (hcell 0 1 (by norm_num [NN]) (by norm_num [NN])).symm
  have h11 := (hcell 1 1 (by norm_num [NN]) (by norm_num [NN])).symm
  norm_num [NN] at h00 h10 h01 h11
  simp only [boardAbsorb, h00, h10, h01, h11,
    particleToCode_codeToParticle (hv 0 (by norm_num [KK, NN])),
    particleToCode_codeToParticle (hv 1 (by norm_num [KK, NN])),
    particleToCode_codeToParticle (hv 2 (by norm_num [KK, NN])),
    particleToCode_codeToParticle (hv 3 (by norm_num [KK, NN]))]

/-! ### The two root-column transports. -/

/-- **The OLD root columns ARE `board_root8` of the decoded OLD board.** -/
theorem oldRootCols_of_sat (permOut : List ℤ → List ℤ)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    oldRootCols.map (envAt t i).loc = boardRoot8 permOut (boardDecode (envAt t i)) := by
  rw [root_of_lookupMem permOut hSound i [0, 1, 2, 3] oldRootCols (by norm_num)
        (mh8zero_of_sat hsat hc i hi) (oldRoot_lookupMem hsat i (by omega)),
      boardRoot8, boardAbsorb_old_of_sat hsat hc i hi]
  norm_num [old]

/-- **The NEW root columns ARE `board_root8` of the STEPPED board.** -/
theorem newRootCols_of_sat (permOut : List ℤ → List ℤ)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    newRootCols.map (envAt t i).loc
      = boardRoot8 permOut (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t i))) := by
  rw [root_of_lookupMem permOut hSound i [4, 5, 6, 7] newRootCols (by norm_num)
        (mh8zero_of_sat hsat hc i hi) (newRoot_lookupMem hsat i (by omega)),
      boardRoot8, boardAbsorb_new_of_sat hsat hc i hi]
  norm_num [new, KK, NN]

set_option maxRecDepth 40000 in
/-- **THE PI-LEVEL TRANSPORT, OLD SIDE.** The committed public inputs `[16..24)` ARE the
`board_root8` of the DECODED OLD board. -/
theorem oldRoot_pi_of_sat (permOut : List ℤ → List ℤ)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (h1 : 1 < t.rows.length) (j : Nat) (hj : j < 8) :
    t.pub (16 + j)
      ≡ (boardRoot8 permOut (boardDecode (envAt t 0)))[j]! [ZMOD 2013265921] := by
  have hcols := oldRootCols_of_sat permOut hSound hsat hc 0 (by omega)
  have hget : (boardRoot8 permOut (boardDecode (envAt t 0)))[j]!
      = (envAt t 0).loc (oldRootCols[j]!) := by
    rw [← hcols]; interval_cases j <;> simp [oldRootCols]
  rw [hget]
  refine (astep_piFirst hsat (by omega) ?_).symm
  interval_cases j
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)

set_option maxRecDepth 40000 in
/-- **THE PI-LEVEL CAPSTONE — Leg A transported to the COMMITTED ROOT.** On a satisfying,
canonical trace of the byte-pinned `automataflStepDesc`, against a wide-sound Poseidon2 chip table,
the public inputs `[24..32)` — the root the fold and the light client actually read — ARE the
`board_root8` of `automatonStep` applied to the DECODED OLD board. A forged new root fails: the
`node8` lookup forces the digest columns and the first-row `bind_pi`s force the PIs to them. -/
theorem newRoot_pi_of_sat (permOut : List ℤ → List ℤ)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (h1 : 1 < t.rows.length) (j : Nat) (hj : j < 8) :
    t.pub (24 + j)
      ≡ (boardRoot8 permOut
          (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t 0))))[j]!
        [ZMOD 2013265921] := by
  have hcols := newRootCols_of_sat permOut hSound hsat hc 0 (by omega)
  have hget : (boardRoot8 permOut
      (Dregg2.Games.Automatafl.automatonStep (boardDecode (envAt t 0))))[j]!
      = (envAt t 0).loc (newRootCols[j]!) := by
    rw [← hcols]; interval_cases j <;> simp [newRootCols]
  rw [hget]
  refine (astep_piFirst hsat (by omega) ?_).symm
  interval_cases j
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)
  · exact (by decide)

end LegR

/-! ### The forgery canary — the `node8` lookup really BITES.

A concrete wide-sound chip table over a concrete `permOut`: the genuine absorb row is in it, and a
row carrying a FORGED digest lane is NOT. So a prover claiming a wrong `board_root8` has no table
row to look up — the transport above is not a vacuous implication. -/

/-- A concrete stand-in wide squeeze (structure only — no crypto claim). -/
def canaryPerm : List ℤ → List ℤ := fun xs => (List.range 8).map (fun k => xs.headD 0 + (k : ℤ))

/-- The absorb seed of the board `[AUTO, VAC, VAC, VAC]` in one leaf against a zero sibling. -/
def canaryIns : List ℤ := [3, 0, 0, 0] ++ List.replicate 12 0

/-- A chip table holding exactly the genuine row for `canaryIns`. -/
def canaryTbl : Table := [chipRowN canaryPerm canaryIns]

theorem canary_sound : ChipTableSoundN canaryPerm canaryTbl := by
  intro r hr
  refine ⟨canaryIns, by norm_num [canaryIns, CHIP_RATE], ?_⟩
  simpa [canaryTbl] using hr

/-- The genuine row IS a table row. -/
theorem canary_genuine_mem : chipRowN canaryPerm canaryIns ∈ canaryTbl := by decide

/-- A row whose FIRST digest lane is forged is NOT a table row: the lookup fails, so no satisfying
witness can commit that root. -/
theorem canary_forged_not_mem :
    (chipRowN canaryPerm canaryIns).set 17 999 ∉ canaryTbl := by decide


/-! ## §6 — Axiom hygiene. -/

#print axioms forcedGe0_core_mod
#print axioms offCard_of_sat
#print axioms offnz_of_sat
#print axioms tib_of_sat
#print axioms tread_of_sat
#print axioms targvac_of_sat
#print axioms moved_of_sat
#print axioms autosel_of_sat
#print axioms seltarg_of_sat
#print axioms boardupd_of_sat
#print axioms tcell_target_of_sat
#print axioms tcell_valid_of_sat
#print axioms moved_parts_of_sat
#print axioms boardvalid_of_sat
#print axioms newvalid_of_sat
#print axioms cell_update_pure
#print axioms cell_of_data
#print axioms moved_iff_guard_of_sat
#print axioms astep_sat_imp_automatonStep

-- LEG R: the `board_root8` transport to the committed public inputs.
#print axioms particleToCode_codeToParticle
#print axioms mh8zero_of_sat
#print axioms astep_piFirst
#print axioms boardDecode_cellAt
#print axioms boardAbsorb_old_of_sat
#print axioms boardAbsorb_new_of_sat
#print axioms root_of_lookupMem
#print axioms oldRoot_lookupMem
#print axioms newRoot_lookupMem
#print axioms oldRootCols_of_sat
#print axioms newRootCols_of_sat
#print axioms oldRoot_pi_of_sat
#print axioms newRoot_pi_of_sat
#print axioms canary_sound
#print axioms canary_genuine_mem
#print axioms canary_forged_not_mem

#print axioms autoPin_of_sat
#print axioms decoded_auto_holds_automaton
#print axioms offset_of_sat
#print axioms raycast_xp_of_sat
#print axioms raycast_xn_of_sat
#print axioms raycast_yp_of_sat
#print axioms raycast_yn_of_sat
#print axioms forcedGe0_core
#print axioms xdec_gpd_sound
#print axioms xdec_gnd_sound
#print axioms xdec_lt_sound
#print axioms xdec_gt_sound
#print axioms xdec_le_sound
#print axioms xdec_min_sound
#print axioms xdec_gm_sound
#print axioms decideAxis_xdec_none
#print axioms decideAxis_xdec_attRep
#print axioms decideAxis_xdec_repRep
#print axioms decideAxis_xdec_attAtt
#print axioms decideAxis_x_sound
#print axioms ydec_gpd_sound
#print axioms ydec_min_sound
#print axioms decideAxis_ydec_repRep
#print axioms decideAxis_ydec_attAtt
#print axioms decideAxis_y_sound
-- leg (4): the score-compare no-wrap heart + order embedding + offset extraction
#print axioms forcedGe0_core_score
#print axioms decScore_cmp
#print axioms decisionCmp_gt_iff_score
#print axioms sgt_of_sat
#print axioms slt_of_sat
#print axioms colPin_of_sat
#print axioms ox_of_sat
#print axioms oy_of_sat
#print axioms xmove_of_sat
#print axioms ymove_of_sat
#print axioms decodeDecision_delta_x_fst
#print axioms attRep2_of_env
#print axioms decScore_of_fields
#print axioms xScoreEval
#print axioms yScoreEval
#print axioms offset_matches_chooseOffset
#print axioms automatonOffset_of_sat

/-! ## §7 — THE NAMED RESIDUAL (what remains for the full composition).

Proven here, keyed on the byte-pinned `automataflStepDesc`, canonical over BabyBear, none assumed:
  * `astep_gate` — the single-row gate extraction;
  * `coord_of_sat` — the decoded auto coordinate is in bounds (`decompose_coord_le` soundness);
  * `autoPin_of_sat` / `decoded_auto_holds_automaton` — SUB-LEMMA (1) in full;
  * `raycast_xp_reduce` — the pure `Board.raycast … .xp` reduction at `n = 2`;
  * `raycast_xp_of_sat` — SUB-LEMMA (2) for the XP ray IN FULL: `(rDist 0, rWhat 0) = Board.raycast`,
    derived from the hit one-hot, the vacuum-before / in-bounds-before occlusion gates, and the
    `cond_nonzero` in-bounds-hit witness (with `mem3_of_gate` pinning `what ∈ {VAC,REP,ATT}`);
  * `raycast_xn_reduce` / `raycast_yp_reduce` / `raycast_yn_reduce` — the pure `Board.raycast`
    reductions at `n = 2` for the remaining three cardinals;
  * `raycast_xn_of_sat` / `raycast_yp_of_sat` / `raycast_yn_of_sat` — SUB-LEMMA (2) for the OTHER
    THREE rays IN FULL, keyed on the byte-pinned `rayConstraints d dx dy` for `d = 1,2,3` (each with
    its own `inWindowCols`/`rcReadHead` closed form: `XN` shifts `−x`; `YP`/`YN` scan ROWS via
    `selRow`). **SUB-LEMMA (2) IS NOW CLOSED FOR ALL FOUR RAYS** — leg (2) is complete;
  * `offset_of_sat` — the value-range half of sub-lemma (4);
  * **leg (3), NOW CLOSED IN FULL — `decodeDecision = evaluateAxis` for BOTH axes:**
      - `forcedGe0_core` — the no-wrap soundness heart: a 5-bit range witness pins the ACTUAL
        comparison (`SMALL_RBITS = 5` ⇒ magnitudes `< 2^5 ≪ p`, the exact no-wrap window). PURE, the
        lemma every distance guard rests on;
      - `xdec_gpd_sound` / `xdec_gnd_sound` — `forcedGe0_core` APPLIED to the byte-pinned descriptor:
        the guard columns `68`/`74` genuinely decide `rDist 0 ≥ 2` / `rDist 1 ≥ 2`; `xdec_lt_sound`,
        `xdec_gt_sound`, `xdec_le_sound` decide `pd < nd`, `pd > nd`, `pd ≤ nd`; `xdec_min_sound` pins
        the `min` gadget to `min(pd, nd)`, and `xdec_gm_sound` decides `min ≥ 2` (the field-congruence
        trap discharged, not tripped, for EVERY comparison the truth table reads);
      - `xdec_pd_mem` / `xdec_nd_mem` — the ray distances are `n = 2` step counts (`∈ {1,2}`);
      - `xdec_ipw_sel` / `xdec_inw_sel` — the `ipw`/`inw` one-hots select exactly the ray-code case;
      - `decode_vacVac`/`decode_attRep`/`decode_repAtt`/`decode_repVac`/`decode_vacRep`/`decode_attVac`/
        `decode_vacAtt`/`decode_repRep`/`decode_attAtt` — the nine PURE, axis-independent decode lemmas:
        given the extracted field values + guard soundness, the decoded `(variant, pos, att, rep)` IS
        the `evaluateAxis` priority match for that `(pw, nw)` cell (at `n = 2` the `attractor/attractor`
        cell always resolves to `.none`, since `pd ≠ nd ⇒ min = 1`);
      - `decideAxis_xdec_none/vacRep/vacAtt/repVac/repRep/repAtt/attVac/attRep/attAtt` — ALL NINE
        `decide_axis` cases closed IN FULL against the byte-pinned object (extraction ▸ pure decode),
        only the ray `what`-codes as premises; `decideAxis_x_sound` unions them by case-splitting the two
        `what`-codes over the whole truth table: `decodeDecision (loc 58..61) = evaluateAxis` on the X
        rays. The `ydec` axis (base `105`, rays `d = 2,3`) is the identical column-shift replay
        (`ydec_*` + `decideAxis_ydec_*`), unioned by `decideAxis_y_sound`. §4.9 canary `#guard`s show the
        `forced_ge0` bit and the `assert_case` gate REJECT forged witnesses on BOTH the `gpd`/`(2,1)` and
        the newly-closed `gnd`/`(1,2)` teeth (a `[· ≥ 2]` lie at distance `1`; an `unbalancedPair` claim
        with the guard `= 0`). **LEG (3) IS COMPLETE — both axes, `Decision = evaluateAxis`.**

  * **leg (4), the `chooseOffset` cross-axis tie-break (§4.10–§4.14):**
      - `forcedGe0_core_score` — the 20-bit NO-WRAP score-compare heart: `SCORE_RBITS = 20` (`S ∈
        [0, 2²⁰−1]`) with score magnitudes `≤ 300000 ⇒ |sx − sy − 1| ≤ 400000 < p − 2²⁰`, the exact
        no-wrap interval (WIDER than the 5-bit small window `eq_of_modEq_score` supplies);
      - `sgt_of_sat` / `slt_of_sat` — `forcedGe0_core_score` APPLIED to the byte-pinned descriptor:
        cols `152`/`173` genuinely decide `sx > sy` / `sy > sx` (the field-congruence trap discharged
        at 20-bit width, over the `att`/`rep ≤ 2` envelope);
      - `decScore` + `decScore_cmp` / `decisionCmp_gt_iff_score` — PURE: the felt score is an ORDER
        EMBEDDING of the reference `decisionCmp` (priority tier + intra-tier distance tie-break) at
        `n = 2`, so a `>` on scores IS the decision order;
      - `xmove_of_sat` / `ymove_of_sat` — the move bits (cols `194`/`200`) decide `[variant ≥ 1] =
        [decision ≠ none]` (no wrap, `variant ∈ {0,1,2,3}`); `colPin_of_sat` pins the column rule
        `true`; `ox_of_sat` / `oy_of_sat` extract the two offset equalities (the `push_f` `oy`
        expansion collapsing to `ymove·(2·posy−1)·(1−sgt)` under `col = 1`);
      - **`offset_matches_chooseOffset` — the CAPSTONE, NOW UNCONDITIONAL:** `(decodeOff ox,
        decodeOff oy) = chooseOffset (decode xdec) (decode ydec) true`, keyed on the byte-pinned object.
        §4.14 canary `#guard`s show the `ox` gate REJECTS a score-forbidden move (`ox = 1` with
        `sgt = 0`).

  * **leg (4′), NOW CLOSED IN FULL — the score-field DETERMINATION (§4.12b):**
      - `attRep2_of_env` / `decScore_of_fields` — PURE: `attRep2` of the decoded decision follows from
        the raw `att, rep ∈ [0,2]` envelope, and the felt score head `100000·variant − 100·att − rep`
        equals `decScore` of the decoded decision on a witness whose UNUSED fields are `0` (`assert_case`);
      - `xScoreEval` / `yScoreEval` — the 9-case ×2 `assert_case` field extraction against the
        byte-pinned object: on a satisfying canonical trace the raw `(variant, att, rep)` columns are
        the `n = 2` envelope (`att, rep ≤ 2`) AND the score head equals `decScore (decode xdec/ydec)`.
        Same shape as `decideAxis_x_sound`; every field value read off the emitted gates, none assumed.
        These DISCHARGE `offset_matches_chooseOffset`'s two hypotheses — the capstone is UNCONDITIONAL.

  * **leg (5), the step + board-update gates (§4.15–§4.17) — the GATE SEMANTICS CLOSED IN FULL:**
      - `forcedGe0_core_mod` — the `forced_ge0` no-wrap heart in MOD form: the compared quantity may be
        a LARGE field value congruent to a SMALL one (the offset felt `p−1 ≡ −1` makes `ax + ox` large as
        a field element), and the bit still decides `[· ≥ 0]`. The plain `forcedGe0_core` does NOT apply
        to the target-coordinate edges; this is the lemma that makes them sound;
      - `decodeOff_modEq` / `decodeOff_val` / `offCard_of_sat` — the `{0,1,p−1}` offset columns are
        congruent to their small signed decodes, and (legs 1–4 composed via `automatonOffset_of_sat`)
        the decoded offset is one of the FIVE cardinal steps;
      - `offnz_of_sat` — the move-nonzero column `246 = ox² + oy²` (`0` for no move, `1` for a step);
      - `txlo_of_sat` / `txhi_of_sat` / `tylo_of_sat` / `tyhi_of_sat` + `tib_of_sat` — the four
        `forced_ge0` edge bits decide the four board edges and `tib` (col 233) is their product:
        `tib ∈ {0,1}` and **`tib = 1` IFF the target `(ax+ox, ay+oy)` is in bounds**;
      - `tread_of_sat` — the `read_rowcol_gated` target read: both one-hots sum to `tib` with indices
        pinned to `tib·(ay+oy)` / `tib·(ax+ox)`, and `tcell` (col 234) is the dot product against OLD;
      - `tcell_target_of_sat` — **when `tib = 1` the gated read IS the target OLD cell**
        `old[(ay+oy)·n + (ax+ox)]` — the cell `automatonStep` reads for its vacancy test;
      - `tcell_valid_of_sat` — the read is a valid particle felt (`{0,1,2,3}`): `0` out of bounds, an
        OLD board cell in bounds;
      - `targvac_of_sat` — `targ_vac = 1 − nz` with `nz = [tcell ≥ 1]` no-wrap, so
        **`targ_vac = 1` IFF the target cell is vacuum**;
      - `moved_of_sat` / `moved_parts_of_sat` — `m` (col 247) `= offnz·tib·targ_vac`, `m ∈ {0,1}`, and
        **`m = 1` IFF all three hold** — the reference `automatonStep` guard, factor for factor;
      - `autosel_of_sat` / `seltarg_of_sat` — the auto one-hots resolve to the coordinate bits
        (`selRow[1] = ay`, `selRow[0] = 1−ay`, …) and the gated `sel_target` one-hots sum to `m` with
        indices pinned to the target, so they vanish when `m = 0` and single-hot the target when `m = 1`;
      - `boardupd_of_sat` — the FOUR board-update cell equalities:
        `new[c] = old[c] + m·selTarget[c]·(AUTO − old[c]) − m·selAuto[c]·old[c]`, i.e. AUTO at the
        target, vacuum at the vacated auto cell, old preserved elsewhere.
        §4.16 canary `#guard`s show the cell-0 board-update gate REJECTS a witness that leaves
        `new0 = 0` while the step happened.

  * **LEG A CLOSED — the top-level composition (§4.16b–§4.17b):**
      - the DESCRIPTOR GAP is FIXED at the source. `AutomataflStepEmit.boardRangeConstraints` now
        emits `assert_member(cell, {VAC,REP,ATT,AUTO})` for all `2k` board columns (OLD and NEW), so
        `boardvalid_of_sat` / `newvalid_of_sat` are THEOREMS about the emitted object and the `hvalid`
        envelope is gone from every leg-5 statement. Before the fix a witness could carry `old[c] ≥ 4`,
        which decodes to VACUUM under `codeToParticle` (the reference steps) while the circuit's
        `targ_vac = [tcell = 0]` blocks — the refinement was FALSE over satisfying witnesses on the
        whole window `tcell ∈ [4, p)`. §4.16b's `#guard`s show the new gate REJECTS exactly that `4`;
      - `cell_update_pure` / `cell_of_data` — PURE: one board-update cell equality, decoded. Given the
        `{0,1}` target/auto selector products (never both — the step is a nonzero offset), the new cell
        is AUTO at the target, VACUUM at the vacated auto cell and the old particle elsewhere: the
        three-way match against `stepTo`'s own three-way `if`;
      - `moved_iff_guard_of_sat` — the reference GUARD PROPOSITION discharged: `m` (col 247) `= 1` IFF
        `automatonStep`'s `if` fires on the DECODED board (both target edges in bounds, offset nonzero,
        target cell vacuum), factor for factor against the proven `m = offnz·tib·targ_vac`;
      - **`astep_sat_imp_automatonStep` — THE CAPSTONE, UNCONDITIONAL** (no `hvalid`, no assumed
        arithmetization): on a satisfying canonical trace the reference step of the decoded OLD board
        has size `NN`, has its automaton exactly at the witnessed target when the move flag fires (and
        at the old position otherwise), and agrees CELL BY CELL, on every in-bounds coordinate, with the
        decode of the emitted NEW board columns.

  * **LEG R CLOSED — the capstone TRANSPORTED to the committed public inputs (§5r):**
      - `root_of_lookupMem` — the LOOKUP-SEMANTICS lemma: a satisfied `MerkleHash8` node8 chip
        lookup (arity-16 `Poseidon2Chip`), against a wide-sound chip table, forces its 8 output
        columns to be the genuine wide squeeze of the absorbed leaf `cells ‖ 4 zeros ‖ 8 zeros`.
        Direct `chip_lookup_sound_N` (arity tag + equal-length padding pin the decomposition); the
        `bind_board_roots` `assert_zero(mh8_zero)` pin (`mh8zero_of_sat`) collapses the padding
        columns to LITERAL zeros, so the seed is a function of the board cells alone;
      - `astep_piFirst` — the `.piBinding VmRow.first` gates of `bind_board_roots` ARE the PI
        congruences on row 0 (`isFirst = true`);
      - `oldRootCols_of_sat` / `newRootCols_of_sat` — the two root-column blocks equal
        `board_root8` of the decoded OLD board / of `automatonStep` applied to it (the latter IS
        the capstone, read through the canonical particle encoding `particleToCode`, whose
        round-trip is licensed by the descriptor's own `assert_member` board range gates);
      - **`newRoot_pi_of_sat` — THE PI-LEVEL STATEMENT the fold / light client needs**: on a
        satisfying canonical trace, against a wide-sound Poseidon2 chip table,
        `PI[24 + j] ≡ (board_root8 (automatonStep (boardDecode …)))[j]` for every `j < 8` — the
        COMMITTED new root IS the root of the correctly-stepped board (and `oldRoot_pi_of_sat` the
        same for `PI[16..24)` and the decoded OLD board). The congruence is mod `p` because the PI
        binding is a field equality; a root forged mod `p` fails.
        `canary_forged_not_mem` exhibits a concrete wide-sound chip table whose genuine absorb row
        is present and whose digest-forged row is ABSENT — the lookup bites, so the transport is
        not a vacuous implication.

REMAINING (NOT assumed, NOT stubbed — no `sorry`, no placeholder):
  (leg R-crypto) the chip-table faithfulness `ChipTableSoundN permOut (t.tf .poseidon2)` is a NAMED
      HYPOTHESIS (the deployed chip AIR's own faithfulness at full squeeze width) and `permOut` is a
      parameter — exactly the carrier `HeapOpenEmit` / `NoteSpendingLeafRefine` ride. Nothing here
      claims collision resistance: the transport says the PI digest IS `permOut` of the genuine
      board seed, not that distinct boards have distinct roots.
  (leg R-decl) `automataflStepDesc.tables` is `[]` while the two lookups name `TableId.poseidon2`;
      `Satisfied2`'s lookup semantics read `t.tf` directly, so the proofs are unaffected, but the
      descriptor should DECLARE the chip table (an emitter fix, surfaced not laundered).
  (n) the descriptor instantiates `NN = 2`. The gadget families are `NN`-generic and the deployed
      leaves run `n = 5` / `n = 11`; every proof here is keyed to the `n = 2` emission and re-pins
      mechanically at the larger counts (a follow-up, not a hole in this one).
The Leg-A composition is now a proven theorem. -/

end Dregg2.Circuit.Emit.AutomataflStepRefine
