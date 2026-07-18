/-
# Dregg2.Circuit.Emit.AutomataflResolveRefine — LEG R, the SAT ⇒ SEMANTICS refinement of the
byte-pinned automatafl m=2 move-adjudication descriptor (`automataflResolveDesc`).

## What this file IS

`AutomataflResolveEmit.lean` is Stage 1: the Leg R descriptor STRUCTURE, byte-pinned by an
`emitVmJson2` `#guard` (306 columns, 371 constraints, 32 public inputs). This file is Stage 2: for
each of the descriptor's eight legs, a theorem DERIVING the reference semantics
(`Dregg2.Games.Automatafl`) from the EMITTED constraints on a satisfying, canonical trace. Nothing
is assumed: every fact is extracted from a constraint proved to be a MEMBER of the byte-pinned
`automataflResolveDesc.constraints` (`by decide` over the fold-generated list), exactly as
`AutomataflStepRefine.lean` closed Leg A.

The field glue (`Canon`, `bin_of_gate`, `eq_of_modEq_canon`, `forcedGe0_core`, `StepCanon`,
`codeToParticle`) is REUSED from `AutomataflStepRefine`; it is descriptor-agnostic.

## The DEFECT this refinement surfaced (§0.1) — the board cells are NOT range-checked

`automataflStepDesc` carries `boardRangeConstraints` — `assert_member(cell, {0,1,2,3})` on every
OLD and NEW board column. That family is what let Leg A's capstone be UNCONDITIONAL.

`automataflResolveDesc` HAS NO SUCH FAMILY. `resolveConstraints` is
`onePin :: autoRead ++ validateMove×2 ++ validateOcclusion×2 ++ srcNonVac ++ patternBits ++
selection ++ carry ++ flowThrough ++ writeMid ++ bindBoardRoots` — no membership gate on any
`old c` or `mid c`.

This is LOAD-BEARING, not cosmetic. The source-non-vacuum bit is
`anz = forced_ge0(fp − 1, SMALL_RBITS=5)`, so a witnessed source particle `fp = 4` satisfies
`anz = 1` (the circuit treats the cell as CARRYING A PIECE), while `codeToParticle 4 = .vacuum`
(the reference treats it as EMPTY). A satisfying witness with an out-of-alphabet cell therefore
makes the naive capstone FALSE. §0.1 records this as an explicit `BoardAlphabet` envelope; the
capstone (`resolve_sat_imp_resolveMid`) takes it as a hypothesis and NAMES it as the descriptor
gap. The fix is to add `boardRangeConstraints`-for-`old`/`mid` to `automataflResolveEmit` and
re-pin the wire golden — at which point `BoardAlphabet` becomes a theorem
(`boardvalid_of_sat`-style) and the hypothesis drops. That change is NOT made here: the descriptor
is byte-pinned and registered, so re-pinning it is a separate, deliberate edit.

Every result BELOW the capstone (R1–R5, and the occlusion/geometry content of R6) is
UNCONDITIONAL — it does not touch the particle alphabet at all.

## Axiom hygiene

`#print axioms` on every exported theorem; the subset is `{propext, Classical.choice, Quot.sound}`.
No `sorry`, no `native_decide`, no assumed arithmetization hypothesis.
-/
import Dregg2.Circuit.Emit.AutomataflResolveEmit
import Dregg2.Circuit.Emit.AutomataflStepRefine
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Games.Automatafl

namespace Dregg2.Circuit.Emit.AutomataflResolveRefine

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (Canon canon_zero canon_one canon_two canon_three eq_of_modEq_canon eq_of_modEq_small
   eq_of_modEq_win bin_of_gate StepCanon canon_loc forcedGe0_core codeToParticle)
open Dregg2.Games.Automatafl (Board Coord Particle Move MoveValid moveValidB conflictResolve
  occluded applyMoves interior frmConflict toConflict hasTwoDistinct)

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! ## §0 — The single-row gate extraction, keyed on the BYTE-PINNED `automataflResolveDesc`. -/

/-- A per-row gate `cg g` of the Leg-R descriptor forces its body to vanish mod `p` on a non-last
row. The `hg` argument is discharged by `decide` against the fold-generated constraint list, so
every downstream fact is anchored to the byte-pinned descriptor. -/
theorem rgate {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ automataflResolveDesc.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- The `Head` form of `rgate` (`cgH h` is `cg (headToExpr h)` definitionally). -/
theorem rgateH {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head}
    (hg : cgH h ∈ automataflResolveDesc.constraints) :
    (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] :=
  rgate hsat i hi hg

/-! ## §0.2 — Reusable extractors for the two gadget families the descriptor is built from. -/

section Extractors
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The `Builder::one_hot` extractor.** A two-selector one-hot pinned to a BARE coordinate column
forces `sel1 = idx`, `sel0 = 1 − idx`, and `idx ∈ {0,1} = [0, n)`. Every one-hot in the descriptor
(the auto read, both source reads, both `e_to` endpoint pins) is an instance. -/
theorem oneHot_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (s0 s1 idx : Nat)
    (h0 : cg (gBin s0) ∈ automataflResolveDesc.constraints)
    (h1 : cg (gBin s1) ∈ automataflResolveDesc.constraints)
    (hs : cgH (((Head.c (-1)).addLin 1 s0).addLin 1 s1) ∈ automataflResolveDesc.constraints)
    (hx : cgH ((Head.lin 1 s1).addLin (-1) idx) ∈ automataflResolveDesc.constraints) :
    ((envAt t i).loc idx = 0 ∨ (envAt t i).loc idx = 1)
      ∧ (envAt t i).loc s1 = (envAt t i).loc idx
      ∧ (envAt t i).loc s0 = 1 - (envAt t i).loc idx := by
  set e := envAt t i with he
  have b0 : e.loc s0 = 0 ∨ e.loc s0 = 1 :=
    bin_of_gate (rgate hsat i hi h0) (canon_loc hc i _)
  have b1 : e.loc s1 = 0 ∨ e.loc s1 = 1 :=
    bin_of_gate (rgate hsat i hi h1) (canon_loc hc i _)
  have hsum : e.loc s0 + e.loc s1 = 1 := by
    have hg := rgateH hsat i hi hs
    have hE : (headToExpr (((Head.c (-1)).addLin 1 s0).addLin 1 s1)).eval e.loc
        = e.loc s0 + e.loc s1 + (-1) := rfl
    rw [hE] at hg
    have := (gate_modEq_iff (x := e.loc s0 + e.loc s1 + -1)
      (a := e.loc s0 + e.loc s1) (b := 1) (by ring)).mp hg
    rcases b0 with h | h <;> rcases b1 with h' | h' <;>
      exact eq_of_modEq_small (by rw [h, h']; norm_num) (by norm_num) this
  have hidx : e.loc s1 = e.loc idx := by
    have hg := rgateH hsat i hi hx
    have hE : (headToExpr ((Head.lin 1 s1).addLin (-1) idx)).eval e.loc
        = e.loc s1 + (-1) * e.loc idx := rfl
    rw [hE] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  exact ⟨hidx ▸ b1, hidx, by omega⟩

/-- **The `one` pin.** The always-on `cond_nonzero` selector column really is `1`. -/
theorem one_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc ONE = 1 := by
  have hg := rgateH hsat i hi (h := (Head.lin 1 ONE).addConst (-1)) (by decide)
  have hE : (headToExpr ((Head.lin 1 ONE).addConst (-1))).eval (envAt t i).loc
      = (envAt t i).loc ONE + (-1) := rfl
  rw [hE] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hg)

/-- **The `cond_nonzero` extractor.** `one·(v·inv − 1) == 0` with `one = 1` forces `v ≢ 0 [ZMOD p]`;
for a value already known to lie in a small window that is `v ≠ 0` over ℤ. -/
theorem condNonzero_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (v inv : Nat)
    (hg : cg (gCondNonzero ONE v inv) ∈ automataflResolveDesc.constraints) :
    ¬ ((envAt t i).loc v ≡ 0 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  have hone := one_of_sat hsat hc i hi
  rw [← he] at hone
  have h := rgate hsat i hi hg
  simp only [gCondNonzero, EmittedExpr.eval] at h
  rw [hone, one_mul] at h
  intro hz
  have : (e.loc v * e.loc inv + -1) ≡ (0 * e.loc inv + -1) [ZMOD 2013265921] :=
    Int.ModEq.add (Int.ModEq.mul hz (Int.ModEq.refl _)) (Int.ModEq.refl _)
  have h2 : (0 : ℤ) ≡ -1 [ZMOD 2013265921] := by
    calc (0 : ℤ) ≡ e.loc v * e.loc inv + -1 [ZMOD 2013265921] := h.symm
    _ ≡ 0 * e.loc inv + -1 [ZMOD 2013265921] := this
    _ = -1 := by ring
  exact absurd (eq_of_modEq_small (by norm_num) (by norm_num) h2) (by norm_num)

end Extractors

/-! ## §1 — R1: the WITNESSED auto read pins `(ax, ay)` to the board cell holding AUTO.

The direct mirror of `AutomataflStepRefine.autoPin_of_sat`, keyed on the Leg-R descriptor's own
auto-read block (`autoReadConstraints`, columns `AX_C`/`AY_C` + the `2n` selectors). -/

/-- Decode a satisfying Leg-R row's OLD-board columns into the reference `Board`: size `n`, the
automaton at the witnessed `(AX_C, AY_C)`, cell `(x,y)` the felt-decode of `old[y·n+x]`. -/
def boardDecodeOld (e : VmRowEnv) : Board where
  size          := NN
  automaton     := ⟨(e.loc AX_C).toNat, (e.loc AY_C).toNat⟩
  cells         := fun c => codeToParticle (e.loc (old (c.y * NN + c.x)))
  useColumnRule := true

/-- The same decode over the CLAIMED MID board columns (the automaton is unmoved by resolution —
`applyMoves` never relocates it, and `validate_move` forbids either endpoint being the auto cell). -/
def boardDecodeMid (e : VmRowEnv) : Board where
  size          := NN
  automaton     := ⟨(e.loc AX_C).toNat, (e.loc AY_C).toNat⟩
  cells         := fun c => codeToParticle (e.loc (mid (c.y * NN + c.x)))
  useColumnRule := true

section AutoPin
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **R1 — `autoPinR_of_sat`.** On a satisfying, canonical trace the witnessed `(AX_C, AY_C)` are
legal board coordinates and the OLD board genuinely holds the AUTO particle there. Derived: the
auto row/column one-hots collapse `Σ selRow·selCol·old` to the single selected cell, which
`autoPinHead` forces to `AUTO_CODE = 3`. -/
theorem autoPinR_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < NN ∧ Y < NN
      ∧ (envAt t i).loc AX_C = (X : ℤ) ∧ (envAt t i).loc AY_C = (Y : ℤ)
      ∧ (envAt t i).loc (old (Y * NN + X)) = AUTO_CODE := by
  set e := envAt t i with he
  obtain ⟨hay, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (selAutoRow 0) (selAutoRow 1) AY_C (by decide) (by decide)
      (by decide) (by decide)
  obtain ⟨hax, hc1, hc0⟩ :=
    oneHot_of_sat hsat hc i hi (selAutoCol 0) (selAutoCol 1) AX_C (by decide) (by decide)
      (by decide) (by decide)
  rw [← he] at hay hr1 hr0 hax hc1 hc0
  have hEval : (headToExpr autoPinHead).eval e.loc
      = e.loc (selAutoRow 0) * e.loc (selAutoCol 0) * e.loc (old 0)
        + e.loc (selAutoRow 0) * e.loc (selAutoCol 1) * e.loc (old 1)
        + e.loc (selAutoRow 1) * e.loc (selAutoCol 0) * e.loc (old 2)
        + e.loc (selAutoRow 1) * e.loc (selAutoCol 1) * e.loc (old 3) + (-3) := rfl
  have hAuto := rgateH hsat i hi (h := autoPinHead) (by decide)
  rw [hEval, hr0, hr1, hc0, hc1] at hAuto
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

/-- **R1, in `Board` terms.** The decoded OLD board carries the AUTO particle at the decoded
automaton coordinate — the descriptor forces `(ax, ay)` to BE the automaton's cell, not merely a
claimed coordinate, so the `frm ≠ auto` / `to ≠ auto` gates below gate against the real automaton. -/
theorem decodedOld_auto_holds_automaton
    (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (boardDecodeOld (envAt t i)).cellAt (boardDecodeOld (envAt t i)).automaton
      = Particle.automaton := by
  obtain ⟨X, Y, hX, hY, hAX, hAY, hcell⟩ := autoPinR_of_sat hsat hc i hi
  have hxn : ((envAt t i).loc AX_C).toNat = X := by rw [hAX]; simp
  have hyn : ((envAt t i).loc AY_C).toNat = Y := by rw [hAY]; simp
  simp only [Board.cellAt, boardDecodeOld]
  rw [hxn, hyn, hcell, if_pos ⟨hX, hY⟩]
  simp [codeToParticle, AUTO_CODE]

end AutoPin

/-! ## §2 — R2: `validate_move` ⇒ the reference `MoveValid`, and `fp` is the REAL source cell. -/

/-- Decode a move's witnessed coordinate columns into the reference `Move`. -/
def moveDecode (e : VmRowEnv) (which : Nat) : Move :=
  Move.mk 0
    ⟨(e.loc (cFx (mvBase which))).toNat, (e.loc (cFy (mvBase which))).toNat⟩
    ⟨(e.loc (cTx (mvBase which))).toNat, (e.loc (cTy (mvBase which))).toNat⟩

/-- The `validate_move` gate bundle for the move at base `b`, as membership facts in the
BYTE-PINNED constraint list. Both instances are discharged by `decide`, so every R2 fact is
anchored to the emitted descriptor. -/
structure MoveGates (b : Nat) : Prop where
  fxBin  : cg (gBin (cFxLo b)) ∈ automataflResolveDesc.constraints
  fxPin  : cgH ((Head.lin 1 (cFx b)).addLin (-1) (cFxLo b)) ∈ automataflResolveDesc.constraints
  fyBin  : cg (gBin (cFyLo b)) ∈ automataflResolveDesc.constraints
  fyPin  : cgH ((Head.lin 1 (cFy b)).addLin (-1) (cFyLo b)) ∈ automataflResolveDesc.constraints
  txBin  : cg (gBin (cTxLo b)) ∈ automataflResolveDesc.constraints
  txPin  : cgH ((Head.lin 1 (cTx b)).addLin (-1) (cTxLo b)) ∈ automataflResolveDesc.constraints
  tyBin  : cg (gBin (cTyLo b)) ∈ automataflResolveDesc.constraints
  tyPin  : cgH ((Head.lin 1 (cTy b)).addLin (-1) (cTyLo b)) ∈ automataflResolveDesc.constraints
  rook   : cgH (rookAlignHead b) ∈ automataflResolveDesc.constraints
  dsqDef : cgH (dsqHead b) ∈ automataflResolveDesc.constraints
  dsqNz  : cg (gCondNonzero ONE (cDsq b) (cDistinctInv b)) ∈ automataflResolveDesc.constraints
  faDef  : cgH (autoDistHead (cFa b) (cFx b) (cFy b)) ∈ automataflResolveDesc.constraints
  faNz   : cg (gCondNonzero ONE (cFa b) (cFnaInv b)) ∈ automataflResolveDesc.constraints
  taDef  : cgH (autoDistHead (cTa b) (cTx b) (cTy b)) ∈ automataflResolveDesc.constraints
  taNz   : cg (gCondNonzero ONE (cTa b) (cTnaInv b)) ∈ automataflResolveDesc.constraints
  srR0   : cg (gBin (cSelRow0 b)) ∈ automataflResolveDesc.constraints
  srR1   : cg (gBin (cSelRow1 b)) ∈ automataflResolveDesc.constraints
  srRs   : cgH (((Head.c (-1)).addLin 1 (cSelRow0 b)).addLin 1 (cSelRow1 b))
             ∈ automataflResolveDesc.constraints
  srRi   : cgH ((Head.lin 1 (cSelRow1 b)).addLin (-1) (cFy b)) ∈ automataflResolveDesc.constraints
  srC0   : cg (gBin (cSelCol0 b)) ∈ automataflResolveDesc.constraints
  srC1   : cg (gBin (cSelCol1 b)) ∈ automataflResolveDesc.constraints
  srCs   : cgH (((Head.c (-1)).addLin 1 (cSelCol0 b)).addLin 1 (cSelCol1 b))
             ∈ automataflResolveDesc.constraints
  srCi   : cgH ((Head.lin 1 (cSelCol1 b)).addLin (-1) (cFx b)) ∈ automataflResolveDesc.constraints
  srcRd  : cgH (sourceReadHead b) ∈ automataflResolveDesc.constraints

theorem moveGates_a : MoveGates (mvBase 0) := by constructor <;> decide
theorem moveGates_b : MoveGates (mvBase 1) := by constructor <;> decide

section ValidateMove
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- A `decompose_coord_le` edge pins its column to its lower bit, hence into `{0,1} = [0, n)`. -/
theorem coord01_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (col lo : Nat)
    (hb : cg (gBin lo) ∈ automataflResolveDesc.constraints)
    (hp : cgH ((Head.lin 1 col).addLin (-1) lo) ∈ automataflResolveDesc.constraints) :
    (envAt t i).loc col = 0 ∨ (envAt t i).loc col = 1 := by
  set e := envAt t i with he
  have hbit : e.loc lo = 0 ∨ e.loc lo = 1 := bin_of_gate (rgate hsat i hi hb) (canon_loc hc i _)
  have hg := rgateH hsat i hi hp
  have hE : (headToExpr ((Head.lin 1 col).addLin (-1) lo)).eval e.loc
      = e.loc col + (-1) * e.loc lo := rfl
  rw [hE] at hg
  have heq : e.loc col = e.loc lo :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  exact heq ▸ hbit

/-- **PURE**: a witnessed squared-distance column over two `{0,1}` coordinate pairs is exactly the
integer squared distance. The window `[0,2] ⊂ [0,p)` makes the field congruence an ℤ equality. -/
theorem sqdist_pure {d x1 x2 y1 y2 : ℤ} (hd : Canon d)
    (hx1 : x1 = 0 ∨ x1 = 1) (hx2 : x2 = 0 ∨ x2 = 1)
    (hy1 : y1 = 0 ∨ y1 = 1) (hy2 : y2 = 0 ∨ y2 = 1)
    (h : d + (-1) * (x1 * x1) + 2 * (x1 * x2) + (-1) * (x2 * x2)
          + (-1) * (y1 * y1) + 2 * (y1 * y2) + (-1) * (y2 * y2) ≡ 0 [ZMOD 2013265921]) :
    d = (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2) := by
  have hval : Canon ((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)) := by
    rcases hx1 with h1 | h1 <;> rcases hx2 with h2 | h2 <;> rcases hy1 with h3 | h3 <;>
      rcases hy2 with h4 | h4 <;> subst h1 <;> subst h2 <;> subst h3 <;> subst h4 <;>
      exact ⟨by norm_num, by norm_num⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-- **R2 — `validMove_of_sat`.** The `validate_move` block for the move at base `b` FORCES the
reference `MoveValid` on the decoded OLD board: rook-aligned, source ≠ destination, both endpoints
in bounds, and neither endpoint the (witnessed, R1-pinned) automaton cell. -/
theorem validMove_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which b : Nat)
    (hb : b = mvBase which) (mg : MoveGates b) :
    MoveValid (boardDecodeOld (envAt t i)) (moveDecode (envAt t i) which) := by
  subst hb
  set e := envAt t i with he
  set b := mvBase which with hbdef
  have hfx : e.loc (cFx b) = 0 ∨ e.loc (cFx b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.fxBin mg.fxPin
  have hfy : e.loc (cFy b) = 0 ∨ e.loc (cFy b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.fyBin mg.fyPin
  have htx : e.loc (cTx b) = 0 ∨ e.loc (cTx b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.txBin mg.txPin
  have hty : e.loc (cTy b) = 0 ∨ e.loc (cTy b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.tyBin mg.tyPin
  obtain ⟨X, Y, hXlt, hYlt, hAX, hAY, _⟩ := autoPinR_of_sat hsat hc i hi
  rw [← he] at hAX hAY
  have hax : e.loc AX_C = 0 ∨ e.loc AX_C = 1 := by
    rw [hAX]; have : X < 2 := by simpa [NN] using hXlt
    interval_cases X <;> simp
  have hay : e.loc AY_C = 0 ∨ e.loc AY_C = 1 := by
    rw [hAY]; have : Y < 2 := by simpa [NN] using hYlt
    interval_cases Y <;> simp
  -- rook alignment
  have hrook : (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFy b) - e.loc (cTy b)) = 0 := by
    have hg := rgateH hsat i hi mg.rook
    have hE : (headToExpr (rookAlignHead b)).eval e.loc
        = e.loc (cFx b) * e.loc (cFy b) + (-1) * (e.loc (cFx b) * e.loc (cTy b))
          + (-1) * (e.loc (cTx b) * e.loc (cFy b)) + e.loc (cTx b) * e.loc (cTy b) := rfl
    rw [hE] at hg
    have hmod : (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFy b) - e.loc (cTy b))
        ≡ 0 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
    refine eq_of_modEq_small ?_ (by norm_num) hmod
    rcases hfx with h1 | h1 <;> rcases htx with h2 | h2 <;> rcases hfy with h3 | h3 <;>
      rcases hty with h4 | h4 <;> rw [h1, h2, h3, h4] <;> norm_num
  -- distinctness
  have hdsq : e.loc (cDsq b)
      = (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFx b) - e.loc (cTx b))
        + (e.loc (cFy b) - e.loc (cTy b)) * (e.loc (cFy b) - e.loc (cTy b)) := by
    have hg := rgateH hsat i hi mg.dsqDef
    have hE : (headToExpr (dsqHead b)).eval e.loc
        = e.loc (cDsq b) + (-1) * (e.loc (cFx b) * e.loc (cFx b))
          + 2 * (e.loc (cFx b) * e.loc (cTx b)) + (-1) * (e.loc (cTx b) * e.loc (cTx b))
          + (-1) * (e.loc (cFy b) * e.loc (cFy b)) + 2 * (e.loc (cFy b) * e.loc (cTy b))
          + (-1) * (e.loc (cTy b) * e.loc (cTy b)) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) hfx htx hfy hty hg
  have hdnz : ¬ ((e.loc (cDsq b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzero_of_sat hsat hc i hi (cDsq b) (cDistinctInv b) mg.dsqNz
    rwa [← he] at this
  have hdistinct : ¬ (e.loc (cFx b) = e.loc (cTx b) ∧ e.loc (cFy b) = e.loc (cTy b)) := by
    rintro ⟨h1, h2⟩
    exact hdnz (by rw [hdsq, h1, h2]; simp [Int.ModEq])
  -- frm ≠ auto
  have hfa : e.loc (cFa b)
      = (e.loc (cFx b) - e.loc AX_C) * (e.loc (cFx b) - e.loc AX_C)
        + (e.loc (cFy b) - e.loc AY_C) * (e.loc (cFy b) - e.loc AY_C) := by
    have hg := rgateH hsat i hi mg.faDef
    have hE : (headToExpr (autoDistHead (cFa b) (cFx b) (cFy b))).eval e.loc
        = e.loc (cFa b) + (-1) * (e.loc (cFx b) * e.loc (cFx b))
          + 2 * (e.loc (cFx b) * e.loc AX_C) + (-1) * (e.loc AX_C * e.loc AX_C)
          + (-1) * (e.loc (cFy b) * e.loc (cFy b)) + 2 * (e.loc (cFy b) * e.loc AY_C)
          + (-1) * (e.loc AY_C * e.loc AY_C) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) hfx hax hfy hay hg
  have hfanz : ¬ ((e.loc (cFa b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzero_of_sat hsat hc i hi (cFa b) (cFnaInv b) mg.faNz
    rwa [← he] at this
  have hfnotauto : ¬ (e.loc (cFx b) = e.loc AX_C ∧ e.loc (cFy b) = e.loc AY_C) := by
    rintro ⟨h1, h2⟩
    exact hfanz (by rw [hfa, h1, h2]; simp [Int.ModEq])
  -- to ≠ auto
  have hta : e.loc (cTa b)
      = (e.loc (cTx b) - e.loc AX_C) * (e.loc (cTx b) - e.loc AX_C)
        + (e.loc (cTy b) - e.loc AY_C) * (e.loc (cTy b) - e.loc AY_C) := by
    have hg := rgateH hsat i hi mg.taDef
    have hE : (headToExpr (autoDistHead (cTa b) (cTx b) (cTy b))).eval e.loc
        = e.loc (cTa b) + (-1) * (e.loc (cTx b) * e.loc (cTx b))
          + 2 * (e.loc (cTx b) * e.loc AX_C) + (-1) * (e.loc AX_C * e.loc AX_C)
          + (-1) * (e.loc (cTy b) * e.loc (cTy b)) + 2 * (e.loc (cTy b) * e.loc AY_C)
          + (-1) * (e.loc AY_C * e.loc AY_C) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) htx hax hty hay hg
  have htanz : ¬ ((e.loc (cTa b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzero_of_sat hsat hc i hi (cTa b) (cTnaInv b) mg.taNz
    rwa [← he] at this
  have htnotauto : ¬ (e.loc (cTx b) = e.loc AX_C ∧ e.loc (cTy b) = e.loc AY_C) := by
    rintro ⟨h1, h2⟩
    exact htanz (by rw [hta, h1, h2]; simp [Int.ModEq])
  -- assemble `MoveValid`
  have hcast : ∀ z : ℤ, (z = 0 ∨ z = 1) → ((z.toNat : ℤ) = z ∧ z.toNat < 2) := by
    rintro z (h | h) <;> subst h <;> exact ⟨rfl, by norm_num⟩
  obtain ⟨cfx, lfx⟩ := hcast _ hfx
  obtain ⟨cfy, lfy⟩ := hcast _ hfy
  obtain ⟨ctx', ltx⟩ := hcast _ htx
  obtain ⟨cty, lty⟩ := hcast _ hty
  obtain ⟨cax, lax⟩ := hcast _ hax
  obtain ⟨cay, lay⟩ := hcast _ hay
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- frm ≠ to
    intro hEq
    simp only [moveDecode, ← hbdef, Coord.mk.injEq] at hEq
    exact hdistinct ⟨by omega, by omega⟩
  · -- rook-aligned
    simp only [moveDecode, ← hbdef]
    rcases mul_eq_zero.mp hrook with h | h
    · left; omega
    · right; omega
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using lfx
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using lfy
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using ltx
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using lty
  · -- frm is not the automaton
    intro hEq
    simp only [Board.isAutomaton, boardDecodeOld, moveDecode, ← hbdef, Coord.mk.injEq] at hEq
    exact hfnotauto ⟨by omega, by omega⟩
  · -- to is not the automaton
    intro hEq
    simp only [Board.isAutomaton, boardDecodeOld, moveDecode, ← hbdef, Coord.mk.injEq] at hEq
    exact htnotauto ⟨by omega, by omega⟩
  · simp [Board.isConflict, boardDecodeOld]
  · simp [Board.isConflict, boardDecodeOld]

/-- **R2 (cont.) — `sourceRead_of_sat`.** The witnessed source particle `fp` IS the OLD board cell
the move claims to move from: the row×column one-hot collapses `Σ selRow·selCol·old` to the single
cell at `(fx, fy)`. So the non-vacuum bit downstream reads the REAL board, not a free column. -/
theorem sourceRead_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b : Nat) (mg : MoveGates b) :
    ∃ X Y : Nat, X < NN ∧ Y < NN
      ∧ (envAt t i).loc (cFx b) = (X : ℤ) ∧ (envAt t i).loc (cFy b) = (Y : ℤ)
      ∧ (envAt t i).loc (cFp b) = (envAt t i).loc (old (Y * NN + X)) := by
  set e := envAt t i with he
  obtain ⟨hfy, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelRow0 b) (cSelRow1 b) (cFy b) mg.srR0 mg.srR1 mg.srRs mg.srRi
  obtain ⟨hfx, hc1, hc0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelCol0 b) (cSelCol1 b) (cFx b) mg.srC0 mg.srC1 mg.srCs mg.srCi
  rw [← he] at hfy hr1 hr0 hfx hc1 hc0
  have hg := rgateH hsat i hi mg.srcRd
  have hE : (headToExpr (sourceReadHead b)).eval e.loc
      = e.loc (cFp b)
        + (-1) * (e.loc (cSelRow0 b) * e.loc (cSelCol0 b) * e.loc (old 0))
        + (-1) * (e.loc (cSelRow0 b) * e.loc (cSelCol1 b) * e.loc (old 1))
        + (-1) * (e.loc (cSelRow1 b) * e.loc (cSelCol0 b) * e.loc (old 2))
        + (-1) * (e.loc (cSelRow1 b) * e.loc (cSelCol1 b) * e.loc (old 3)) := rfl
  rw [hE, hr0, hr1, hc0, hc1] at hg
  rcases hfy with hy | hy <;> rcases hfx with hx | hx
  · refine ⟨0, 0, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 0)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  · refine ⟨1, 0, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 1)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  · refine ⟨0, 1, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 2)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  · refine ⟨1, 1, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 3)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)

end ValidateMove

/-! ## §3 — The `forced_ge0` extractor.

EVERY threshold bit in the descriptor (`iv`, `eqx`, `eqy`, `occ`, `anz`, `bnz`, the four
`eq_coords` bits) is `forced_ge0` over the SAME head shape `(Head.lin 1 val).addConst (-1)`, i.e.
`ib == [val − 1 ≥ 0] == [val ≥ 1]`. One extractor therefore serves the whole descriptor. -/

/-- The `DIFF_RBITS = 9` no-wrap window (the 5-bit twin is `AutomataflStepRefine.forcedGe0_core`).
Given `ib ∈ {0,1}`, a 9-bit range-sum `S ∈ [0, 511]`, and `2·ib·D + ib − D − 1 ≡ S [ZMOD p]` for a
SMALL `D`, the bit IS the comparison — a forged bit has no satisfying decomposition. -/
theorem forcedGe0_wide {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 511)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -1000 ≤ D) (hDhi : D ≤ 1000) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0:ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro hcx; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1:ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hcx; omega⟩

/-- The 9-bit `forced_ge0` gate bundle at a site `(val, ib, bit0)`. -/
structure Ge0Gates9 (val ib bit0 : Nat) : Prop where
  ibBin : cg (gBin ib) ∈ automataflResolveDesc.constraints
  rb0 : cg (gBin (bit0 + 0)) ∈ automataflResolveDesc.constraints
  rb1 : cg (gBin (bit0 + 1)) ∈ automataflResolveDesc.constraints
  rb2 : cg (gBin (bit0 + 2)) ∈ automataflResolveDesc.constraints
  rb3 : cg (gBin (bit0 + 3)) ∈ automataflResolveDesc.constraints
  rb4 : cg (gBin (bit0 + 4)) ∈ automataflResolveDesc.constraints
  rb5 : cg (gBin (bit0 + 5)) ∈ automataflResolveDesc.constraints
  rb6 : cg (gBin (bit0 + 6)) ∈ automataflResolveDesc.constraints
  rb7 : cg (gBin (bit0 + 7)) ∈ automataflResolveDesc.constraints
  rb8 : cg (gBin (bit0 + 8)) ∈ automataflResolveDesc.constraints
  recomp : cgH ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ automataflResolveDesc.constraints

/-- The `eq == 1 − neq` closing gate of an `eq_scalar` / `eq_coords` block. -/
structure EqPinGate (eqCol neqCol : Nat) : Prop where
  pin : cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))
          ∈ automataflResolveDesc.constraints

section Ge0
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The 9-bit `forced_ge0` site extractor.** The witnessed bit `ib` is EXACTLY `[val ≥ 1]`,
provided `val` is known to sit in a small window (which the callers establish from the geometry —
it is never assumed). Derived from the emitted booleanity + recomposition gates. -/
theorem ge0_9_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (gg : Ge0Gates9 val ib bit0)
    (hlo : -999 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 999) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hib : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (rgate hsat i hi gg.ibBin) (canon_loc hc i _)
  have B : ∀ k : Nat, cg (gBin (bit0 + k)) ∈ automataflResolveDesc.constraints →
      (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (rgate hsat i hi hk) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 gg.rb0
  have h1 := B 1 gg.rb1
  have h2 := B 2 gg.rb2
  have h3 := B 3 gg.rb3
  have h4 := B 4 gg.rb4
  have h5 := B 5 gg.rb5
  have h6 := B 6 gg.rb6
  have h7 := B 7 gg.rb7
  have h8 := B 8 gg.rb8
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) + 32 * e.loc (bit0 + 5)
    + 64 * e.loc (bit0 + 6) + 128 * e.loc (bit0 + 7) + 256 * e.loc (bit0 + 8) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 511 := by rw [hS]; omega
  have hg := rgateH hsat i hi gg.recomp
  have hE : (headToExpr ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) + (-32) * e.loc (bit0 + 5)
        + (-64) * e.loc (bit0 + 6) + (-128) * e.loc (bit0 + 7)
        + (-256) * e.loc (bit0 + 8) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_wide hib hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hib, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- The `eq == 1 − neq` gate: the equality bit is the boolean complement of the threshold bit. -/
theorem eqPin_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (eqCol neqCol : Nat)
    (gp : EqPinGate eqCol neqCol)
    (hneq : (envAt t i).loc neqCol = 0 ∨ (envAt t i).loc neqCol = 1) :
    (envAt t i).loc eqCol = 1 - (envAt t i).loc neqCol := by
  set e := envAt t i with he
  have hg := rgateH hsat i hi gp.pin
  have hE : (headToExpr (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))).eval e.loc
      = e.loc eqCol + e.loc neqCol + (-1) := rfl
  rw [hE] at hg
  have hmod := (gate_modEq_iff (x := e.loc eqCol + e.loc neqCol + -1)
    (a := e.loc eqCol) (b := 1 - e.loc neqCol) (by ring)).mp hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
  rcases hneq with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

end Ge0

/-! ## §4 — R3: the WITNESSED `is_vertical` bit IS the real geometry, and `occ` IS `occluded`. -/

/-- **PURE**: a witnessed 1-D squared-distance column over two `{0,1}` coordinates is exactly the
integer squared difference (the `eq_scalar` head). -/
theorem sq1d_pure {d a c : ℤ} (hd : Canon d) (ha : a = 0 ∨ a = 1) (hcv : c = 0 ∨ c = 1)
    (h : d + (-1) * (a * a) + 2 * (a * c) + (-1) * (c * c) ≡ 0 [ZMOD 2013265921]) :
    d = (a - c) * (a - c) := by
  have hval : Canon ((a - c) * (a - c)) := by
    rcases ha with h1 | h1 <;> rcases hcv with h2 | h2 <;> subst h1 <;> subst h2 <;>
      exact ⟨by norm_num, by norm_num⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-- The `is_vertical` pin gate bundle for the move at base `b`, occlusion block at `o`. -/
structure IvGates (b o : Nat) : Prop where
  dsqDef : cgH ((((Head.lin 1 (cIvDsq o)).addProd (-1) [cFx b, cFx b]).addProd 2
              [cFx b, cTx b]).addProd (-1) [cTx b, cTx b]) ∈ automataflResolveDesc.constraints
  ge0    : Ge0Gates9 (cIvDsq o) (cIvNeq o) (ivNeqBit o 0)
  eqPin  : EqPinGate (cIv o) (cIvNeq o)

/-- The occlusion tail gate bundle: the two `seg` gates, the masked-sum gate, and the `occ`
threshold site. -/
structure OccGates (o : Nat) : Prop where
  seg0 : cgH (segHead o 0) ∈ automataflResolveDesc.constraints
  seg1 : cgH (segHead o 1) ∈ automataflResolveDesc.constraints
  msum : cgH (msumHead o) ∈ automataflResolveDesc.constraints
  ge0  : Ge0Gates9 (cMsum o) (cOcc o) (occBit o 0)

theorem ivGates_a : IvGates (mvBase 0) (occBase 0) := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by decide⟩⟩ <;> decide
theorem ivGates_b : IvGates (mvBase 1) (occBase 1) := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by decide⟩⟩ <;> decide
theorem occGates_a : OccGates (occBase 0) := by
  refine ⟨by decide, by decide, by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> decide
theorem occGates_b : OccGates (occBase 1) := by
  refine ⟨by decide, by decide, by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> decide

section Occlusion
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **R3a — `iv_of_sat`.** The witnessed direction bit is boolean and is EXACTLY the real
geometry: `iv = 1 ↔ fx = tx`. The bit that selects the line scan, the endpoint one-hots and the
passable comparison therefore cannot disagree with the move it gates — this is the property the
compile-time `let is_vertical = …` bake in `moves.rs` could not have. -/
theorem iv_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o : Nat)
    (ig : IvGates b o)
    (hfx : (envAt t i).loc (cFx b) = 0 ∨ (envAt t i).loc (cFx b) = 1)
    (htx : (envAt t i).loc (cTx b) = 0 ∨ (envAt t i).loc (cTx b) = 1) :
    ((envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
      ∧ ((envAt t i).loc (cIv o) = 1 ↔ (envAt t i).loc (cFx b) = (envAt t i).loc (cTx b)) := by
  set e := envAt t i with he
  have hdsq : e.loc (cIvDsq o)
      = (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFx b) - e.loc (cTx b)) := by
    have hg := rgateH hsat i hi ig.dsqDef
    have hE : (headToExpr ((((Head.lin 1 (cIvDsq o)).addProd (-1) [cFx b, cFx b]).addProd 2
          [cFx b, cTx b]).addProd (-1) [cTx b, cTx b])).eval e.loc
        = e.loc (cIvDsq o) + (-1) * (e.loc (cFx b) * e.loc (cFx b))
          + 2 * (e.loc (cFx b) * e.loc (cTx b))
          + (-1) * (e.loc (cTx b) * e.loc (cTx b)) := rfl
    rw [hE] at hg
    exact sq1d_pure (canon_loc hc i _) hfx htx hg
  have hbnd : -999 ≤ e.loc (cIvDsq o) ∧ e.loc (cIvDsq o) ≤ 999 := by
    rw [hdsq]; rcases hfx with h1 | h1 <;> rcases htx with h2 | h2 <;> rw [h1, h2] <;> norm_num
  obtain ⟨hnb, hn1, hn0⟩ :=
    ge0_9_of_sat hsat hc i hi (cIvDsq o) (cIvNeq o) (ivNeqBit o 0) ig.ge0 hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hiv : e.loc (cIv o) = 1 - e.loc (cIvNeq o) := by
    have := eqPin_of_sat hsat hc i hi (cIv o) (cIvNeq o) ig.eqPin hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hiv, h] <;> norm_num, ?_⟩
  constructor
  · intro h1
    have hn : e.loc (cIvNeq o) = 0 := by omega
    have := hn0 hn
    rw [hdsq] at this
    rcases hfx with a | a <;> rcases htx with c | c <;> rw [a, c] at this ⊢ <;>
      first | rfl | (exfalso; revert this; norm_num)
  · intro heq
    have hz : e.loc (cIvDsq o) = 0 := by rw [hdsq, heq]; ring
    have : e.loc (cIvNeq o) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-- **R3b — `occ_of_sat`.** The occlusion bit is FORCED to `0`. At `n = 2` the strictly-between
mask is empty (`segHead` reduces to `seg[k] == 0`), so the masked interior sum is `0` and the
`forced_ge0(msum − 1)` threshold cannot fire. Derived from the emitted gates, not from the
emitter's comment. -/
theorem occ_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (o : Nat) (og : OccGates o) :
    (envAt t i).loc (cOcc o) = 0 := by
  set e := envAt t i with he
  have hseg : ∀ k : Nat, cgH (segHead o k) ∈ automataflResolveDesc.constraints →
      (headToExpr (segHead o k)).eval e.loc = e.loc (cSeg o k) → e.loc (cSeg o k) = 0 := by
    intro k hk hE
    have hg := rgateH hsat i hi hk
    rw [hE] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hs0 : e.loc (cSeg o 0) = 0 := hseg 0 og.seg0 rfl
  have hs1 : e.loc (cSeg o 1) = 0 := hseg 1 og.seg1 rfl
  have hmsum : e.loc (cMsum o) = 0 := by
    have hg := rgateH hsat i hi og.msum
    have hE : (headToExpr (msumHead o)).eval e.loc
        = e.loc (cMsum o) + (-1) * (e.loc (cSeg o 0) * e.loc (cLine o 0))
          + e.loc (cSeg o 0) * e.loc (cOsrc o 0) * e.loc (cLine o 0)
          + (-1) * (e.loc (cSeg o 1) * e.loc (cLine o 1))
          + e.loc (cSeg o 1) * e.loc (cOsrc o 1) * e.loc (cLine o 1) := rfl
    rw [hE, hs0, hs1] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  obtain ⟨hb, h1, _⟩ :=
    ge0_9_of_sat hsat hc i hi (cMsum o) (cOcc o) (occBit o 0) og.ge0
      (by rw [← he, hmsum]; norm_num) (by rw [← he, hmsum]; norm_num)
  rw [← he] at hb h1
  rcases hb with h | h
  · exact h
  · exact absurd (h1 h) (by rw [hmsum]; norm_num)

end Occlusion

/-- **R3b, the reference side.** At `n = 2` a rook move has NO strictly-interior cell, so the
reference `occluded` is constantly `false`. Together with `occ_of_sat` this closes the occlusion
leg: circuit bit `= 0 =` reference predicate, for EVERY in-bounds move and every source set. -/
theorem interior_nil_n2 (f g : Coord) (hf : f.x < 2 ∧ f.y < 2) (hg : g.x < 2 ∧ g.y < 2) :
    interior f g = [] := by
  obtain ⟨fx, fy⟩ := f; obtain ⟨gx, gy⟩ := g
  obtain ⟨h1, h2⟩ := hf; obtain ⟨h3, h4⟩ := hg
  simp only at h1 h2 h3 h4
  interval_cases fx <;> interval_cases fy <;> interval_cases gx <;> interval_cases gy <;> decide

theorem occluded_false_n2 (bd : Board) (srcs : List Coord) (m : Move)
    (hf : m.frm.x < 2 ∧ m.frm.y < 2) (ht : m.to.x < 2 ∧ m.to.y < 2) :
    occluded bd srcs m = false := by
  simp [occluded, interior_nil_n2 m.frm m.to hf ht]

/-! ## §5 — R4: the four `eq_coords` pattern bits + the fork/collide/survive selection.

The pattern bits (§5.1) and the selection ALGEBRA (§5.2) are UNCONDITIONAL. Tying the selection to
the reference `conflictResolve` (§5.4) additionally needs the source-non-vacuum bits to mean
"the source cell is non-vacuum", which is where the descriptor's MISSING board-alphabet range check
(§0, the defect) becomes load-bearing: it is carried as the explicit `BoardAlphabet` envelope. -/

/-- **THE DESCRIPTOR GAP, named.** `automataflResolveDesc` emits NO `assert_member(cell,{0,1,2,3})`
family (contrast `AutomataflStepEmit.boardRangeConstraints`, which is exactly what made Leg A's
capstone unconditional). Without it a satisfying witness may carry `old c = 4`, which
`codeToParticle` decodes to VACUUM while the circuit's `anz = forced_ge0(fp − 1, 5)` reads as
NON-VACUUM. Everything that reads the particle ALPHABET therefore carries this envelope, and it is
a HYPOTHESIS, not a theorem — that is the defect to fix in the emitter. -/
def BoardAlphabet (e : VmRowEnv) : Prop :=
  ∀ c, c < KK →
    ((e.loc (old c) = 0 ∨ e.loc (old c) = 1 ∨ e.loc (old c) = 2 ∨ e.loc (old c) = 3)
      ∧ (e.loc (mid c) = 0 ∨ e.loc (mid c) = 1 ∨ e.loc (mid c) = 2 ∨ e.loc (mid c) = 3))

/-- The 5-bit (`SMALL_RBITS`) `forced_ge0` gate bundle — the shape the `anz`/`bnz` bits use. -/
structure Ge0Gates5 (val ib bit0 : Nat) : Prop where
  ibBin : cg (gBin ib) ∈ automataflResolveDesc.constraints
  rb0 : cg (gBin (bit0 + 0)) ∈ automataflResolveDesc.constraints
  rb1 : cg (gBin (bit0 + 1)) ∈ automataflResolveDesc.constraints
  rb2 : cg (gBin (bit0 + 2)) ∈ automataflResolveDesc.constraints
  rb3 : cg (gBin (bit0 + 3)) ∈ automataflResolveDesc.constraints
  rb4 : cg (gBin (bit0 + 4)) ∈ automataflResolveDesc.constraints
  recomp : cgH ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ automataflResolveDesc.constraints

/-- An `eq_coords` block: the 2-D squared-distance definition, the threshold site, the `eq` pin. -/
structure EqCoordsGates (xa ya xb yb ec : Nat) : Prop where
  dsqDef : cgH ((((((Head.lin 1 (cEqDsq ec)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
              [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb])
             ∈ automataflResolveDesc.constraints
  ge0    : Ge0Gates9 (cEqDsq ec) (cEqNeq ec) (eqBitAt ec 0)
  eqPin  : EqPinGate (cEqBit ec) (cEqNeq ec)

section Selection
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The 5-bit `forced_ge0` site extractor (the `anz`/`bnz` twin of `ge0_9_of_sat`). -/
theorem ge0_5_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (gg : Ge0Gates5 val ib bit0)
    (hlo : -99 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 99) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hib : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (rgate hsat i hi gg.ibBin) (canon_loc hc i _)
  have B : ∀ k : Nat, cg (gBin (bit0 + k)) ∈ automataflResolveDesc.constraints →
      (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (rgate hsat i hi hk) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 gg.rb0
  have h1 := B 1 gg.rb1
  have h2 := B 2 gg.rb2
  have h3 := B 3 gg.rb3
  have h4 := B 4 gg.rb4
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 31 := by rw [hS]; omega
  have hg := rgateH hsat i hi gg.recomp
  have hE : (headToExpr ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_core hib hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hib, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- **R4a — `eqCoords_of_sat`.** An `eq_coords` bit is EXACTLY the coordinate-pair equality of the
two witnessed coordinate pairs. Unconditional: the coordinates are pinned to `{0,1}` by
`validate_move`'s `decompose_coord_le`, so the squared distance sits in the `[0,2]` no-wrap window
and the 9-bit `forced_ge0` decides it. -/
theorem eqCoords_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (xa ya xb yb ec : Nat)
    (eg : EqCoordsGates xa ya xb yb ec)
    (h1 : (envAt t i).loc xa = 0 ∨ (envAt t i).loc xa = 1)
    (h2 : (envAt t i).loc ya = 0 ∨ (envAt t i).loc ya = 1)
    (h3 : (envAt t i).loc xb = 0 ∨ (envAt t i).loc xb = 1)
    (h4 : (envAt t i).loc yb = 0 ∨ (envAt t i).loc yb = 1) :
    ((envAt t i).loc (cEqBit ec) = 0 ∨ (envAt t i).loc (cEqBit ec) = 1)
      ∧ ((envAt t i).loc (cEqBit ec) = 1 ↔
          ((envAt t i).loc xa = (envAt t i).loc xb ∧ (envAt t i).loc ya = (envAt t i).loc yb)) := by
  set e := envAt t i with he
  have hdsq : e.loc (cEqDsq ec)
      = (e.loc xa - e.loc xb) * (e.loc xa - e.loc xb)
        + (e.loc ya - e.loc yb) * (e.loc ya - e.loc yb) := by
    have hg := rgateH hsat i hi eg.dsqDef
    have hE : (headToExpr ((((((Head.lin 1 (cEqDsq ec)).addProd (-1) [xa, xa]).addProd 2
          [xa, xb]).addProd (-1) [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb]
          |>.addProd (-1) [yb, yb])).eval e.loc
        = e.loc (cEqDsq ec) + (-1) * (e.loc xa * e.loc xa) + 2 * (e.loc xa * e.loc xb)
          + (-1) * (e.loc xb * e.loc xb) + (-1) * (e.loc ya * e.loc ya)
          + 2 * (e.loc ya * e.loc yb) + (-1) * (e.loc yb * e.loc yb) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) h1 h3 h2 h4 hg
  have hbnd : -999 ≤ e.loc (cEqDsq ec) ∧ e.loc (cEqDsq ec) ≤ 999 := by
    rw [hdsq]; rcases h1 with a|a <;> rcases h2 with b|b <;> rcases h3 with c|c <;>
      rcases h4 with d|d <;> rw [a, b, c, d] <;> norm_num
  obtain ⟨hnb, hn1, hn0⟩ :=
    ge0_9_of_sat hsat hc i hi (cEqDsq ec) (cEqNeq ec) (eqBitAt ec 0) eg.ge0 hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hbit : e.loc (cEqBit ec) = 1 - e.loc (cEqNeq ec) := by
    have := eqPin_of_sat hsat hc i hi (cEqBit ec) (cEqNeq ec) eg.eqPin hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hbit, h] <;> norm_num, ?_⟩
  constructor
  · intro hone
    have hn : e.loc (cEqNeq ec) = 0 := by omega
    have hle := hn0 hn
    rw [hdsq] at hle
    rcases h1 with a|a <;> rcases h2 with b|b <;> rcases h3 with c|c <;> rcases h4 with d|d <;>
      rw [a, b, c, d] at hle ⊢ <;> first | exact ⟨rfl, rfl⟩ | (exfalso; revert hle; norm_num)
  · rintro ⟨e1, e2⟩
    have hz : e.loc (cEqDsq ec) = 0 := by rw [hdsq, e1, e2]; ring
    have : e.loc (cEqNeq ec) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-- **R4b — `selection_of_sat`, the SELECTION TRUTH TABLE.** The emitted `fork`, `collide` and
`surv` columns are booleans, and each is EXACTLY its reference condition as a function of the four
pattern bits and the two non-vacuum bits:
`fork ↔ eq_ff ∧ ¬eq_tt`, `collide ↔ eq_tt ∧ ¬eq_ff ∧ anz ∧ bnz`, `surv ↔ ¬fork ∧ ¬collide`.
Unconditional — pure gate algebra over columns already known boolean. -/
theorem selection_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hff : (envAt t i).loc (cEqBit (eqBase 0)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 0)) = 1)
    (htt : (envAt t i).loc (cEqBit (eqBase 1)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 1)) = 1)
    (hanz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hbnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1) :
    ((envAt t i).loc cFork = 1 ↔
        ((envAt t i).loc (cEqBit (eqBase 0)) = 1 ∧ (envAt t i).loc (cEqBit (eqBase 1)) = 0))
    ∧ ((envAt t i).loc cCollide = 1 ↔
        ((envAt t i).loc (cEqBit (eqBase 1)) = 1 ∧ (envAt t i).loc (cEqBit (eqBase 0)) = 0
          ∧ (envAt t i).loc cAnz = 1 ∧ (envAt t i).loc cBnz = 1))
    ∧ ((envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1)
    ∧ ((envAt t i).loc cSurv = 1 ↔
        ((envAt t i).loc cFork = 0 ∧ (envAt t i).loc cCollide = 0)) := by
  set e := envAt t i with he
  have hforkv : e.loc cFork
      = e.loc (cEqBit (eqBase 0)) - e.loc (cEqBit (eqBase 0)) * e.loc (cEqBit (eqBase 1)) := by
    have hg := rgateH hsat i hi
      (h := ((Head.lin 1 cFork).addLin (-1) (cEqBit (eqBase 0))).addProd 1
              [cEqBit (eqBase 0), cEqBit (eqBase 1)]) (by decide)
    have hE : (headToExpr (((Head.lin 1 cFork).addLin (-1) (cEqBit (eqBase 0))).addProd 1
          [cEqBit (eqBase 0), cEqBit (eqBase 1)])).eval e.loc
        = e.loc cFork + (-1) * e.loc (cEqBit (eqBase 0))
          + e.loc (cEqBit (eqBase 0)) * e.loc (cEqBit (eqBase 1)) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc cNeqFf = 1 - e.loc (cEqBit (eqBase 0)) := by
    have hg := rgateH hsat i hi (h := ((Head.lin 1 cNeqFf).addLin 1 (cEqBit (eqBase 0))).addConst (-1))
      (by decide)
    have hE : (headToExpr (((Head.lin 1 cNeqFf).addLin 1 (cEqBit (eqBase 0))).addConst (-1))).eval
        e.loc = e.loc cNeqFf + e.loc (cEqBit (eqBase 0)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rw [a] <;> exact ⟨by norm_num, by norm_num⟩
  have hcol1 : e.loc cCol1 = e.loc (cEqBit (eqBase 1)) * e.loc cNeqFf := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCol1).addProd 1 [cEqBit (eqBase 1), cNeqFf])
      (by decide)
    have hE : (headToExpr ((Head.lin (-1) cCol1).addProd 1
        [cEqBit (eqBase 1), cNeqFf])).eval e.loc
        = (-1) * e.loc cCol1 + e.loc (cEqBit (eqBase 1)) * e.loc cNeqFf := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rw [hnff, a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hcol2 : e.loc cCol2 = e.loc cCol1 * e.loc cAnz := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCol2).addProd 1 [cCol1, cAnz]) (by decide)
    have hE : (headToExpr ((Head.lin (-1) cCol2).addProd 1 [cCol1, cAnz])).eval e.loc
        = (-1) * e.loc cCol2 + e.loc cCol1 * e.loc cAnz := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rw [hcol1, hnff, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  have hcollv : e.loc cCollide = e.loc cCol2 * e.loc cBnz := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCollide).addProd 1 [cCol2, cBnz]) (by decide)
    have hE : (headToExpr ((Head.lin (-1) cCollide).addProd 1 [cCol2, cBnz])).eval e.loc
        = (-1) * e.loc cCollide + e.loc cCol2 * e.loc cBnz := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hsurvv : e.loc cSurv
      = 1 - e.loc cFork - e.loc cCollide + e.loc cFork * e.loc cCollide := by
    have hg := rgateH hsat i hi
      (h := ((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1 cCollide).addProd (-1)
              [cFork, cCollide]) (by decide)
    have hE : (headToExpr (((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1
        cCollide).addProd (-1) [cFork, cCollide])).eval e.loc
        = e.loc cSurv + e.loc cFork + e.loc cCollide
          + (-1) * (e.loc cFork * e.loc cCollide) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hforkv, hcollv, hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
    rcases hbnz with d | d <;>
    rw [hcollv, hcol2, hcol1, hnff] at hsurvv ⊢ <;> rw [hforkv] at hsurvv ⊢ <;>
    rw [a, b, c, d] at hsurvv ⊢ <;> norm_num at hsurvv ⊢ <;>
    simp_all


/-- **R4c — `srcNonVac_of_sat`.** The source-non-vacuum bit is EXACTLY the reference predicate
"the decoded OLD board carries a piece at this move's source". This is the ONE place where the
missing board-alphabet range check bites: without `halpha` a witness may set `fp = 4`, satisfying
`anz = 1` while `codeToParticle 4 = .vacuum`. See §0 — `halpha` is the named descriptor gap. -/
theorem srcNonVac_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which ib bit0 : Nat)
    (mg : MoveGates (mvBase which)) (gg : Ge0Gates5 (cFp (mvBase which)) ib bit0)
    (halpha : BoardAlphabet (envAt t i)) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 ↔
          ((boardDecodeOld (envAt t i)).cellAt (moveDecode (envAt t i) which).frm).isVacuum
            = false) := by
  set e := envAt t i with he
  obtain ⟨X, Y, hX, hY, hfx, hfy, hfp⟩ := sourceRead_of_sat hsat hc i hi (mvBase which) mg
  rw [← he] at hfx hfy hfp
  have hXY : Y * NN + X < KK := by
    have : X < 2 := by simpa [NN] using hX
    have : Y < 2 := by simpa [NN] using hY
    simp only [KK, NN]; omega
  obtain ⟨hcellAlpha, _⟩ := halpha (Y * NN + X) hXY
  have hbnd : -99 ≤ e.loc (cFp (mvBase which)) ∧ e.loc (cFp (mvBase which)) ≤ 99 := by
    rw [hfp]; rcases hcellAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hb, h1, h0⟩ :=
    ge0_5_of_sat hsat hc i hi (cFp (mvBase which)) ib bit0 gg hbnd.1 hbnd.2
  rw [← he] at hb h1 h0
  -- the decoded board cell at the move's source IS `fp`
  have hcell : (boardDecodeOld e).cellAt (moveDecode e which).frm
      = codeToParticle (e.loc (cFp (mvBase which))) := by
    have hxn : (e.loc (cFx (mvBase which))).toNat = X := by rw [hfx]; simp
    have hyn : (e.loc (cFy (mvBase which))).toNat = Y := by rw [hfy]; simp
    simp only [Board.cellAt, boardDecodeOld, moveDecode]
    rw [hxn, hyn, if_pos ⟨by simpa [NN] using hX, by simpa [NN] using hY⟩, hfp]
  rw [hcell]
  have hfpv : e.loc (cFp (mvBase which)) = 0 ∨ e.loc (cFp (mvBase which)) = 1
      ∨ e.loc (cFp (mvBase which)) = 2 ∨ e.loc (cFp (mvBase which)) = 3 := by
    rw [hfp]; exact hcellAlpha
  refine ⟨hb, ?_⟩
  rcases hfpv with hv | hv | hv | hv <;> rw [hv] at h1 h0 ⊢ <;>
    norm_num [codeToParticle, Particle.isVacuum] <;>
    (first
      | (intro hone; have := h1 hone; omega)
      | (rcases hb with hz | ho
         · exact absurd (h0 hz) (by norm_num)
         · exact ho))

end Selection

/-! ## §6 — The remaining gate bundles, discharged by `decide` against the byte-pinned list. -/

theorem eqGates_ff : EqCoordsGates (cFx (mvBase 0)) (cFy (mvBase 0)) (cFx (mvBase 1))
    (cFy (mvBase 1)) (eqBase 0) := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by decide⟩⟩ <;> decide
theorem eqGates_tt : EqCoordsGates (cTx (mvBase 0)) (cTy (mvBase 0)) (cTx (mvBase 1))
    (cTy (mvBase 1)) (eqBase 1) := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by decide⟩⟩ <;> decide
theorem eqGates_ab : EqCoordsGates (cTx (mvBase 0)) (cTy (mvBase 0)) (cFx (mvBase 1))
    (cFy (mvBase 1)) (eqBase 2) := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by decide⟩⟩ <;> decide
theorem eqGates_ba : EqCoordsGates (cTx (mvBase 1)) (cTy (mvBase 1)) (cFx (mvBase 0))
    (cFy (mvBase 0)) (eqBase 3) := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by decide⟩⟩ <;> decide

theorem anzGates : Ge0Gates5 (cFp (mvBase 0)) cAnz (anzBit 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem bnzGates : Ge0Gates5 (cFp (mvBase 1)) cBnz (bnzBit 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7 — NON-VACUITY canaries: the gates BITE.

Each canary evaluates the ACTUAL emitted gate polynomial on a good assignment (`== 0`, satisfied)
and on a forged one (`!= 0`, rejected). Two-sided, so none of the above is a vacuous implication. -/

/-- The auto pin: a board that does NOT hold AUTO at the witnessed one-hot index has no witness. -/
def canonAutoGood : Assignment := fun c =>
  if c = old 0 then 3 else if c = selAutoRow 0 ∨ c = selAutoCol 0 then 1 else 0
def canonAutoForge : Assignment := fun c =>
  if c = selAutoRow 0 ∨ c = selAutoCol 0 then 1 else 0

#guard (headToExpr autoPinHead).eval canonAutoGood == 0    -- AUTO really at (0,0): gate holds
#guard (headToExpr autoPinHead).eval canonAutoForge != 0   -- forged empty cell: gate FAILS

/-- The distinctness `cond_nonzero`: a move with `frm == to` (so `dsq = 0`) has NO inverse witness,
whatever the prover picks for `distinct_inv`. -/
def canonDistinctExpr : EmittedExpr := gCondNonzero ONE (cDsq (mvBase 0)) (cDistinctInv (mvBase 0))
def canonDistGood : Assignment := fun c =>
  if c = ONE ∨ c = cDsq (mvBase 0) ∨ c = cDistinctInv (mvBase 0) then 1 else 0
def canonDistForge : Assignment := fun c =>
  if c = ONE ∨ c = cDistinctInv (mvBase 0) then 1 else 0   -- dsq = 0: the degenerate "move"

#guard canonDistinctExpr.eval canonDistGood == 0     -- dsq = 1, inv = 1: satisfied
#guard canonDistinctExpr.eval canonDistForge != 0    -- dsq = 0 (frm == to): NO witness, REJECTED

/-- The `write_mid_witnessed` cell gate: a forged MID cell (a "dropped move" lie, or any rewrite
that does not match `resolve_mid`) fails the per-cell equality. Here both carries are `0`, so the
gate degenerates to `mid[0] == old[0]`: the board must be UNCHANGED when nothing journeys. -/
def canonMidExpr : EmittedExpr := headToExpr (writeCellHead 0)
def canonMidGood : Assignment := fun c => if c = old 0 ∨ c = mid 0 then 2 else 0
def canonMidForge : Assignment := fun c => if c = old 0 then 2 else 0  -- mid[0] forged to VACUUM

#guard canonMidExpr.eval canonMidGood == 0     -- no carry: mid == old, gate holds
#guard canonMidExpr.eval canonMidForge != 0    -- forged mid (piece silently deleted): REJECTED

/-- The `surv` inclusion–exclusion gate: claiming SURVIVAL while a fork is detected fails. -/
def canonSurvExpr : EmittedExpr :=
  headToExpr (((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1 cCollide).addProd (-1)
    [cFork, cCollide])
def canonSurvGood : Assignment := fun c => if c = cSurv then 1 else 0
def canonSurvForge : Assignment := fun c => if c = cSurv ∨ c = cFork then 1 else 0

#guard canonSurvExpr.eval canonSurvGood == 0    -- no fork, no collide, surv = 1: consistent
#guard canonSurvExpr.eval canonSurvForge != 0   -- fork = 1 but surv = 1 claimed: REJECTED

/-- The occlusion `seg` gate at `n = 2`: the strictly-between mask is FORCED to zero, so a prover
cannot manufacture an interior blocker to fake an occlusion. -/
def canonSegExpr : EmittedExpr := headToExpr (segHead (occBase 0) 0)
def canonSegGood : Assignment := fun _ => 0
def canonSegForge : Assignment := fun c => if c = cSeg (occBase 0) 0 then 1 else 0

#guard canonSegExpr.eval canonSegGood == 0     -- seg = 0: the only satisfying value
#guard canonSegExpr.eval canonSegForge != 0    -- forged interior cell: REJECTED

/-! ## §8 — Axiom hygiene. Every exported theorem, kernel-clean. -/

#print axioms rgate
#print axioms rgateH
#print axioms oneHot_of_sat
#print axioms one_of_sat
#print axioms condNonzero_of_sat
#print axioms autoPinR_of_sat
#print axioms decodedOld_auto_holds_automaton
#print axioms moveGates_a
#print axioms moveGates_b
#print axioms coord01_of_sat
#print axioms sqdist_pure
#print axioms validMove_of_sat
#print axioms sourceRead_of_sat
#print axioms forcedGe0_wide
#print axioms ge0_9_of_sat
#print axioms eqPin_of_sat
#print axioms sq1d_pure
#print axioms ivGates_a
#print axioms ivGates_b
#print axioms occGates_a
#print axioms occGates_b
#print axioms iv_of_sat
#print axioms occ_of_sat
#print axioms interior_nil_n2
#print axioms occluded_false_n2
#print axioms ge0_5_of_sat
#print axioms eqCoords_of_sat
#print axioms selection_of_sat
#print axioms srcNonVac_of_sat
#print axioms eqGates_ff
#print axioms eqGates_tt
#print axioms eqGates_ab
#print axioms eqGates_ba
#print axioms anzGates
#print axioms bnzGates

end Dregg2.Circuit.Emit.AutomataflResolveRefine
