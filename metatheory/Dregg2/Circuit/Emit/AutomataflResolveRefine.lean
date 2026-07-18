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

## DEFECT #4, FOUND HERE AND NOW FIXED AT SOURCE — the board cells were NOT range-checked

`automataflStepDesc` carries `boardRangeConstraints` — `assert_member(cell, {0,1,2,3})` on every
OLD and NEW board column. That family is what let Leg A's capstone be UNCONDITIONAL.

`automataflResolveDesc` HAD NO SUCH FAMILY, and that was LOAD-BEARING, not cosmetic. The
source-non-vacuum bit is `anz = forced_ge0(fp − 1, SMALL_RBITS=5)`, so a witnessed source particle
`fp = 4` satisfies `anz = 1` (the circuit treats the cell as CARRYING A PIECE) while
`codeToParticle 4 = .vacuum` (the reference treats it as EMPTY) — and the 5-bit comparison supplies
no a-priori window that would exclude it. A satisfying witness with an out-of-alphabet cell
therefore made the capstone FALSE.

FIXED: `AutomataflResolveEmit.boardRangeConstraints` now emits `assert_member(cell, {0,1,2,3})` on
every OLD and MID board column (constraints 371 → 379, wire golden re-pinned, descriptor
regenerated). The `BoardAlphabet` envelope is consequently a THEOREM here — `boardvalid_of_sat` —
extracted from the byte-pinned constraint list, and `srcNonVac_of_sat` no longer takes it as a
hypothesis. Every result in this file is UNCONDITIONAL: there is no assumed envelope left.

## DEFECT #5, FOUND HERE — the identical-move turn has NO satisfying witness (COMPLETENESS)

`write_mid_witnessed`'s cell polynomial subtracts `carry_i·src_i[c]·old[c]` once PER PIECE. When
both moves clear the SAME square (`frm_a = frm_b` with both sources carrying — two players proposing
the identical move, which the reference explicitly does NOT treat as a conflict, see
`Automatafl.conflictResolve`) the old particle is subtracted TWICE, forcing `mid[frm] ≡ −old[frm]`.
Since DEFECT #4's alphabet gates now pin both cells into `{0,1,2,3}`, that forces `old[frm] = 0` —
contradicting the carry. So the leaf is UNSATISFIABLE on that legal turn.

This is a COMPLETENESS defect, not a soundness one: no forged board is admitted, a legal one is
refused. It is recorded (`noSharedSource`, `canonDoubleGood`) rather than papered over, and it is
the fact that rules the double-count configurations out of the R6 algebra.

## What is CLOSED here, and what is NOT (the honest residual)

CLOSED: R1 (auto pin) · R2 (`validate_move` ⇒ `MoveValid`, witnessed source read) · R3 (witnessed
`is_vertical`, occlusion) · the R4 pattern bits, selection truth table and `srcNonVac`
(now unconditional) · (a) `boardvalid_of_sat` · (b) `conflictResolve_pair`, the R4 corollary
identifying the emitted `fork`/`collide`/`surv` selection with the reference `conflictResolve` on
the 2-element move list · (c) THE `m = 2` CATERPILLAR, BOTH SIDES:

  * reference — `nextOf_pair` and the FOUR terminal shapes `followChain_own`,
    `followChain_own_landing`, `followChain_flowThrough` and (NEW, §5.6) `followChain_twoCycle`,
    plus their B-side mirrors, assembled into `chainDest_a` / `chainDest_b`: the landing square is
    `to_other` EXACTLY on the circuit's `ft` pattern and `to_own` otherwise. (The three earlier
    lemmas were NOT jointly exhaustive — the 2-cycle `to_a = frm_b`, `¬bnz`, `to_b = frm_a` fell
    through all of them; `followChain_twoCycle` closes that hole.)
  * circuit — `carry_of_sat` / `ft_of_sat` (§5.7) and their four instances `carryA/B_of_sat`,
    `ftA/B_of_sat`: `carry = surv ∧ nz ∧ ¬occ` and
    `ft = eq_chain ∧ ¬other_nz ∧ surv ∧ ¬occ_other ∧ ¬eq_back`, over the byte-pinned
    `carryConstraints` / `flowThroughConstraints`.

(d) R6's EXTRACTORS AND ALGEBRA (§5.8): `dstOneHot_of_sat` (the landing selector is pinned to the
INTERPOLATED `destHead`, so the one-hot cannot name a square the `ft` bit did not select),
`writeCell_of_sat` (the per-cell gate as an extracted field congruence, its polynomial SHAPE
discharged by `rfl` against the emitted head at each of the four cells), and `cellAlgebra` — the
seven live cases of the sixteen indicator combinations, proving the emitted cell polynomial equals
the reference `applyMoves` rewrite VALUE (landing particle / cleared-source vacuum / kept cell)
given the structural exclusions, of which the shared-source one is `noSharedSource`.

NOT CLOSED, precisely — ONE bookkeeping layer and the two theorems above it:

  (i) the INDICATOR GLUE: `A = carry_a · wSrcRow a y · wSrcCol a x` (and the three siblings) must be
      identified with the decidable Coord predicates `⟨x,y⟩ = ma.frm` / `⟨x,y⟩ = dest_a` that
      `cellAlgebra`'s conclusion and the reference rewrite are phrased in — a per-cell unfolding of
      the one-hot values at literal `(x, y)`, plus the `Int.toNat` bridge between the witnessed
      coordinate columns and `moveDecode`'s `Coord` fields;
  (ii) the REFERENCE UNFOLDING of `applyMoves bd [ma, mb]` into that same per-cell if-chain, in the
      four `(anz, bnz)` shapes of `pieceSrcs` (its `filter`/`map`/`find?` evaluated);
  (iii) and therefore THE CAPSTONE `resolve_sat_imp_resolveMid`, and the WHOLE-TURN composition
      through `Automatafl.applyTurn_factors` with `AutomataflStepRefine.astep_sat_imp_automatonStep`
      (which additionally needs an `automatonStep` congruence over boards agreeing on `cellAt` at
      in-bounds coordinates, since the mid seam is a cell-wise agreement, not a `Board` equality).

None of (i)–(iii) is stated: there is no `sorry`, no assumed arithmetization hypothesis, no assumed
mid-board link, and no weakened or vacuous capstone standing in for them.

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

/-- **THE PARTICLE-ALPHABET ENVELOPE — now a THEOREM (`boardvalid_of_sat`), not a hypothesis.**

DEFECT #4, as this refinement found it: `automataflResolveDesc` emitted NO
`assert_member(cell,{0,1,2,3})` family (contrast `AutomataflStepEmit.boardRangeConstraints`, which is
exactly what made Leg A's capstone unconditional). Without it a satisfying witness could carry
`old c = 4`, which `codeToParticle` decodes to VACUUM while the circuit's
`anz = forced_ge0(fp − 1, 5)` reads as NON-VACUUM — a genuine descriptor/reference DISAGREEMENT over
the whole window `fp ∈ [4, p)`, which made the naive capstone FALSE.

FIXED AT SOURCE: `AutomataflResolveEmit.boardRangeConstraints` now emits the `KK + KK` membership
gates on every OLD and MID board column, the wire golden was re-pinned (371 → 379 constraints), and
this predicate is DERIVED from the descriptor by `boardvalid_of_sat` below. It survives as a named
`Prop` only because it is the convenient shape to thread through the alphabet-sensitive lemmas. -/
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

/-- **(a) — `boardvalid_of_sat`: THE ALPHABET ENVELOPE IS A THEOREM.** Every OLD and MID board cell
of a satisfying, canonical Leg-R trace lies in the particle alphabet `{VAC, REP, ATT, AUTO}`,
because the descriptor now EMITS `assert_member(cell, {0,1,2,3})` on each of them
(`AutomataflResolveEmit.boardRangeConstraints`). Each membership gate is proved a MEMBER of the
byte-pinned constraint list by `decide`, so this is anchored to the emitted object — not assumed.
With it, `srcNonVac_of_sat` (and everything above it) becomes UNCONDITIONAL. -/
theorem boardvalid_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    BoardAlphabet (envAt t i) := by
  intro c hcK
  have hK : c < 4 := by simpa [KK, NN] using hcK
  interval_cases c <;>
    exact ⟨AutomataflStepRefine.mem4_of_gate
             (rgate hsat i hi (g := memberExpr (old _) [0, 1, 2, 3]) (by decide))
             (canon_loc hc i _),
           AutomataflStepRefine.mem4_of_gate
             (rgate hsat i hi (g := memberExpr (mid _) [0, 1, 2, 3]) (by decide))
             (canon_loc hc i _)⟩

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
board-alphabet range check is load-bearing: without it a witness may set `fp = 4`, satisfying
`anz = 1` while `codeToParticle 4 = .vacuum`. That check is now EMITTED (DEFECT #4, fixed), so the
envelope arrives from `boardvalid_of_sat` and this theorem is UNCONDITIONAL. -/
theorem srcNonVac_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which ib bit0 : Nat)
    (mg : MoveGates (mvBase which)) (gg : Ge0Gates5 (cFp (mvBase which)) ib bit0) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 ↔
          ((boardDecodeOld (envAt t i)).cellAt (moveDecode (envAt t i) which).frm).isVacuum
            = false) := by
  have halpha : BoardAlphabet (envAt t i) := boardvalid_of_sat hsat hc i hi
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

/-! ## §5.5 — (b) R4 COROLLARY: the emitted selection IS the reference `conflictResolve`.

The circuit's leg 4 computes three booleans (`fork`, `collide`, `surv`) out of four coordinate-pair
equality bits and two source-non-vacuum bits. The reference computes a LIST: it filters `[ma, mb]`
by "touches no conflicted source and no conflicted destination", where each conflict is an
order-free `hasTwoDistinct` over a sub-list. These are different shapes; this section proves them
the same object at `m = 2`.

The key structural facts, both proved below by exhausting the four decidable equalities: at a
2-element move list `frmConflict` and `toConflict` take the SAME value on `ma` as on `mb` — so the
filter keeps BOTH moves or NEITHER — and those values are literally the circuit's `fork` and
`collide` patterns. -/

section ConflictPair

/-- `frmConflict` at `m = 2` is the circuit's `fork` pattern `eq_ff ∧ ¬eq_tt`, on either move. -/
theorem frmConflict_pair (ma mb : Move) :
    (frmConflict [ma, mb] ma = true ↔ (ma.frm = mb.frm ∧ ma.to ≠ mb.to))
      ∧ (frmConflict [ma, mb] mb = true ↔ (ma.frm = mb.frm ∧ ma.to ≠ mb.to)) := by
  constructor <;>
    (by_cases hf : ma.frm = mb.frm <;> by_cases ht : ma.to = mb.to <;>
      simp [frmConflict, hasTwoDistinct, hf, ht, eq_comm])

/-- `toConflict` at `m = 2` is the circuit's `collide` pattern
`eq_tt ∧ ¬eq_ff ∧ anz ∧ bnz`, on either move. The two non-vacuum conjuncts enter because the
reference's destination-conflict filter only counts sources that CARRY a piece — exactly the
`anz`/`bnz` conjuncts of `selectionConstraints`. -/
theorem toConflict_pair (bd : Board) (ma mb : Move) :
    (toConflict bd [ma, mb] ma = true ↔
        (ma.to = mb.to ∧ ma.frm ≠ mb.frm
          ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false))
      ∧ (toConflict bd [ma, mb] mb = true ↔
        (ma.to = mb.to ∧ ma.frm ≠ mb.frm
          ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)) := by
  constructor <;>
    (by_cases hf : ma.frm = mb.frm <;> by_cases ht : ma.to = mb.to <;>
      by_cases hva : (bd.cellAt ma.frm).isVacuum = true <;>
      by_cases hvb : (bd.cellAt mb.frm).isVacuum = true <;>
      simp_all [toConflict, hasTwoDistinct, Particle.isVacuum] <;>
      first
        | exact ⟨fun h => ht h.symm, fun h => absurd h.symm ht⟩
        | exact fun h => absurd h.symm ht
        | exact fun h => absurd h.symm hf
        | tauto)

/-- **(b) — `conflictResolve_pair`: THE R4 COROLLARY.** On the 2-element move list the reference
conflict resolution is ALL-OR-NOTHING, and the "all" branch is precisely the circuit's `surv = 1`:

    conflictResolve bd [ma, mb] = if fork ∨ collide then [] else [ma, mb]

with `fork` and `collide` spelled in exactly the terms `selection_of_sat` delivers. -/
theorem conflictResolve_pair (bd : Board) (ma mb : Move) :
    conflictResolve bd [ma, mb]
      = if (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)
        then [] else [ma, mb] := by
  obtain ⟨hfa, hfb⟩ := frmConflict_pair ma mb
  obtain ⟨hta, htb⟩ := toConflict_pair bd ma mb
  by_cases hcond : (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)
  · rcases hcond with h | h
    · simp [conflictResolve, List.filter, hfa.mpr h, hfb.mpr h,
        if_pos (show (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false
               ∧ (bd.cellAt mb.frm).isVacuum = false) from Or.inl h)]
    · simp [conflictResolve, List.filter, hta.mpr h, htb.mpr h,
        if_pos (show (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false
               ∧ (bd.cellAt mb.frm).isVacuum = false) from Or.inr h)]
  · have h1 : frmConflict [ma, mb] ma = false := by
      simpa using fun h => hcond (Or.inl (hfa.mp h))
    have h2 : frmConflict [ma, mb] mb = false := by
      simpa using fun h => hcond (Or.inl (hfb.mp h))
    have h3 : toConflict bd [ma, mb] ma = false := by
      simpa using fun h => hcond (Or.inr (hta.mp h))
    have h4 : toConflict bd [ma, mb] mb = false := by
      simpa using fun h => hcond (Or.inr (htb.mp h))
    simp [conflictResolve, List.filter, h1, h2, h3, h4, if_neg hcond]

end ConflictPair

/-! ## §5.6 — (c), the REFERENCE HALF of R5: the `m = 2` caterpillar, resolved.

Leg 6 of the descriptor computes two flow-through bits and interpolates each piece's landing square
between its own `to` and the other piece's `to`. The reference computes the same landing by
`followChain` over the move graph `nextOf`. These four lemmas resolve the reference side completely
at `n = 2`: the move graph is a two-entry lookup table (`nextOf_pair` — using `occluded_false_n2`,
so no occlusion survives at this board size), and the chain terminates in exactly the three shapes
the circuit's `ft` bit distinguishes:

  * `followChain_own` — no chain relation (`to_a ≠ frm_b`): the piece lands on its OWN `to`;
  * `followChain_own_landing` — the chain relation holds but the next square is a PIECE source
    (`bnz`, the circuit's `¬ft` conjunct): the caterpillar STOPS there, again the piece's own `to`;
  * `followChain_flowThrough` — the chain relation holds, the next square is VACATING (`¬bnz`) and
    the 2-cycle is broken (`to_b ≠ frm_a`, the circuit's `¬eq_ba` conjunct): the piece flows
    THROUGH to `to_b`. This is exactly `ft_a = 1 ⇒ dest_a = to_b`.

The three cases are jointly exhaustive and pairwise exclusive on the same conditions the emitted
`flowThroughConstraints` branch on, so the reference landing square is a function of precisely the
circuit's `ft` bit. What is NOT yet proven here is the CIRCUIT half of R5 (an `ft_of_sat` extractor
tying the `cFtA`/`cFtB` columns to those conditions) — see the file header for the residual. -/

section Caterpillar

open Dregg2.Games.Automatafl (nextOf followChain)

/-- The `m = 2` move graph is a two-entry lookup: `frm_a ↦ to_a`, `frm_b ↦ to_b`, nothing else.
At `n = 2` no rook move has a strictly-interior cell, so `occluded` never fires (`interior_nil_n2`)
and the graph is unconditional in the board. -/
theorem nextOf_pair (bd : Board) (ma mb : Move) (c : Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2) :
    nextOf bd [ma, mb] [ma.frm, mb.frm] c
      = if c = ma.frm then some ma.to else if c = mb.frm then some mb.to else none := by
  have oa := occluded_false_n2 bd [ma.frm, mb.frm] ma h1 h2
  have ob := occluded_false_n2 bd [ma.frm, mb.frm] mb h3 h4
  by_cases ha : c = ma.frm
  · subst ha; simp [nextOf, oa]
  · by_cases hb : c = mb.frm
    · subst hb; simp [nextOf, oa, ob, Ne.symm ha, ha]
    · simp [nextOf, oa, ob, ha, hb, Ne.symm ha, Ne.symm hb]

/-- NO chain relation (`to_a ≠ frm_b`) ⇒ the piece lands on its own destination. -/
theorem followChain_own (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hd : ma.frm ≠ ma.to) (hne : ma.to ≠ mb.frm) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1) = ma.to := by
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains ma.to = true)]
  by_cases hps : ps.contains ma.to = true
  · rw [if_pos hps]
  · rw [if_neg hps, nextOf_pair bd ma mb ma.to h1 h2 h3 h4, if_neg (Ne.symm hd), if_neg hne]

/-- The next square is itself a PIECE source (the circuit's `bnz` conjunct, which NEGATES `ft`) ⇒
the caterpillar STOPS: the piece still lands on its own destination. -/
theorem followChain_own_landing (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hd : ma.frm ≠ ma.to) (hps : ps.contains ma.to = true) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1) = ma.to := by
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains ma.to = true), if_pos hps]

/-- **THE FLOW-THROUGH CASE.** `to_a = frm_b` (the circuit's `eq_ab`), `frm_b` is NOT a piece source
(`¬bnz`), and the 2-cycle is broken (`to_b ≠ frm_a`, the circuit's `¬eq_ba`) ⇒ the piece rides the
vacating square and lands on `to_b`. This IS `ft_a = 1 ⇒ dest_a = to_b`, on the reference side. -/
theorem followChain_flowThrough (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hab : ma.to = mb.frm) (hba : mb.to ≠ ma.frm)
    (hps : ps.contains mb.frm = false) (hpsb : ps.contains mb.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1) = mb.to := by
  have hfrm : mb.frm ≠ ma.frm := by rw [← hab]; exact fun h => hda h.symm
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [hab, if_neg (by simp : ¬ ([] : List Coord).contains mb.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [if_neg (by simpa using hba), if_neg (by rw [hpsb]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.to h1 h2 h3 h4, if_neg hba, if_neg (Ne.symm hdb)]

/-- **THE FOURTH CASE — the 2-CYCLE, which the other three lemmas do NOT cover.** `to_a = frm_b`
(the chain relation), `frm_b` is vacating (`¬bnz`, so the caterpillar does not stop there) and
`to_b = frm_a` — the two moves swap. `followChain` detects the revisit of `frm_a` and returns the
square it was standing on, i.e. `to_a`. The circuit agrees by NEGATION: `ft_a` carries the `¬eq_ba`
conjunct, so `ft_a = 0` and the interpolated destination is the piece's own `to_a`.

FOUND WHILE CLOSING R5: the three earlier lemmas are NOT jointly exhaustive — `to_a = mb.frm`,
`¬ps.contains mb.frm`, `to_b = frm_a` falls through all of them. This lemma closes that hole. -/
theorem followChain_twoCycle (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hda : ma.frm ≠ ma.to) (hab : ma.to = mb.frm) (hba : mb.to = ma.frm)
    (hps : ps.contains mb.frm = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1) = ma.to := by
  have hfrm : mb.frm ≠ ma.frm := by rw [← hab]; exact fun h => hda h.symm
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [hab, if_neg (by simp : ¬ ([] : List Coord).contains mb.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [hba, if_pos (by simp : ([ma.frm] : List Coord).contains ma.frm = true)]

/-- **THE A-SIDE LANDING, ALL FOUR CASES.** The reference chain destination from `frm_a` is `to_b`
EXACTLY on the circuit's `ft_a` pattern (`eq_ab ∧ ¬bnz ∧ ¬eq_ba`, with `surv`/`¬occ` already
discharged), and the piece's own `to_a` otherwise. This is the reference half of R5, complete. -/
theorem chainDest_a (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hpsb : ma.to = mb.frm → ps.contains mb.frm = false → mb.to ≠ ma.frm →
      ps.contains mb.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
      = if ma.to = mb.frm ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm then mb.to else ma.to := by
  by_cases hab : ma.to = mb.frm
  · by_cases hbnz : ps.contains mb.frm = false
    · by_cases hba : mb.to = ma.frm
      · rw [if_neg (by rintro ⟨_, _, h⟩; exact h hba)]
        exact followChain_twoCycle bd ma mb ps h1 h2 h3 h4 hda hab hba hbnz f
      · rw [if_pos ⟨hab, hbnz, hba⟩]
        exact followChain_flowThrough bd ma mb ps h1 h2 h3 h4 hda hdb hab hba hbnz
          (hpsb hab hbnz hba) f
    · rw [if_neg (by rintro ⟨_, h, _⟩; exact hbnz h)]
      exact followChain_own_landing bd ma mb ps h1 h2 h3 h4 hda
        (by rw [hab]; simpa using hbnz) (f + 1)
  · rw [if_neg (by rintro ⟨h, _, _⟩; exact hab h)]
    exact followChain_own bd ma mb ps h1 h2 h3 h4 hda hab (f + 1)

/-! ### The B-SIDE mirrors. `nextOf`'s lookup table is scanned in list order, so the B-side chain
needs the sources DISTINCT (`frm_a ≠ frm_b`) for `frm_b`'s edge to be reachable — which is exactly
the configuration the capstone establishes whenever piece B carries. -/

theorem followChain_ownB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hd : mb.frm ≠ mb.to) (hnb : mb.to ≠ ma.frm) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1) = mb.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains mb.to = true)]
  by_cases hps : ps.contains mb.to = true
  · rw [if_pos hps]
  · rw [if_neg hps, nextOf_pair bd ma mb mb.to h1 h2 h3 h4, if_neg hnb, if_neg (Ne.symm hd)]

theorem followChain_own_landingB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hps : ps.contains mb.to = true) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1) = mb.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains mb.to = true), if_pos hps]

theorem followChain_flowThroughB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hba : mb.to = ma.frm) (hab : ma.to ≠ mb.frm)
    (hps : ps.contains ma.frm = false) (hpsa : ps.contains ma.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1) = ma.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [hba, if_neg (by simp : ¬ ([] : List Coord).contains ma.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simpa using hab), if_neg (by rw [hpsa]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.to h1 h2 h3 h4, if_neg (Ne.symm hda), if_neg hab]

theorem followChain_twoCycleB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hdb : mb.frm ≠ mb.to)
    (hba : mb.to = ma.frm) (hab : ma.to = mb.frm)
    (hps : ps.contains ma.frm = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1) = mb.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [hba, if_neg (by simp : ¬ ([] : List Coord).contains ma.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [hab, if_pos (by simp : ([mb.frm] : List Coord).contains mb.frm = true)]

/-- **THE B-SIDE LANDING, ALL FOUR CASES** — the mirror of `chainDest_a`, under distinct sources. -/
theorem chainDest_b (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hpsa : mb.to = ma.frm → ps.contains ma.frm = false → ma.to ≠ mb.frm →
      ps.contains ma.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
      = if mb.to = ma.frm ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm then ma.to else mb.to := by
  by_cases hba : mb.to = ma.frm
  · by_cases hanz : ps.contains ma.frm = false
    · by_cases hab : ma.to = mb.frm
      · rw [if_neg (by rintro ⟨_, _, h⟩; exact h hab)]
        exact followChain_twoCycleB bd ma mb ps h1 h2 h3 h4 hne hdb hba hab hanz f
      · rw [if_pos ⟨hba, hanz, hab⟩]
        exact followChain_flowThroughB bd ma mb ps h1 h2 h3 h4 hne hda hdb hba hab hanz
          (hpsa hba hanz hab) f
    · rw [if_neg (by rintro ⟨_, h, _⟩; exact hanz h)]
      exact followChain_own_landingB bd ma mb ps h1 h2 h3 h4 hne
        (by rw [hba]; simpa using hanz) (f + 1)
  · rw [if_neg (by rintro ⟨h, _, _⟩; exact hba h)]
    exact followChain_ownB bd ma mb ps h1 h2 h3 h4 hne hdb hba (f + 1)

end Caterpillar

/-! ## §5.7 — (1) THE CIRCUIT HALF OF R5: `carry_of_sat` and `ft_of_sat`.

Leg 5 and leg 6 of the descriptor are built from exactly two primitives — `Builder::alloc_prod`
(`prodPin`) and `not_bit` (`notBitPin`) — so two mechanical extractors serve both legs. The results
tie `cCarryA`/`cCarryB` and `cFtA`/`cFtB` to PRECISELY the conditions the four `chainDest_*` cases
branch on, which is what makes the reference landing a function of the circuit's `ft` bit. -/

/-- `Builder::alloc_prod(a, b)` forces the fresh column to the product. -/
theorem prod_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out a b : Nat)
    (hg : cgH ((Head.lin (-1) out).addProd 1 [a, b]) ∈ automataflResolveDesc.constraints)
    (ha : (envAt t i).loc a = 0 ∨ (envAt t i).loc a = 1)
    (hb : (envAt t i).loc b = 0 ∨ (envAt t i).loc b = 1) :
    (envAt t i).loc out = (envAt t i).loc a * (envAt t i).loc b := by
  set e := envAt t i with he
  have hgg := rgateH hsat i hi hg
  have hE : (headToExpr ((Head.lin (-1) out).addProd 1 [a, b])).eval e.loc
      = (-1) * e.loc out + e.loc a * e.loc b := rfl
  rw [hE] at hgg
  refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hgg)).symm
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;>
    exact ⟨by norm_num, by norm_num⟩

/-- `not_bit(col)` forces the fresh column to `1 − col`. -/
theorem notBit_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out col : Nat)
    (hg : notBitPin out col ∈ automataflResolveDesc.constraints)
    (hb : (envAt t i).loc col = 0 ∨ (envAt t i).loc col = 1) :
    (envAt t i).loc out = 1 - (envAt t i).loc col := by
  set e := envAt t i with he
  have hgg := rgateH hsat i hi hg
  have hE : (headToExpr (((Head.lin 1 out).addLin 1 col).addConst (-1))).eval e.loc
      = e.loc out + e.loc col + (-1) := rfl
  rw [hE] at hgg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
  rcases hb with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- **(1a) — `carry_of_sat`.** The carry column is EXACTLY "the turn survived adjudication AND this
move's source carried a piece AND its line was clear": `carry = surv ∧ nz ∧ ¬occ`. -/
theorem carry_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (sa1 carry surv nz occ : Nat)
    (hp : cgH ((Head.lin (-1) sa1).addProd 1 [surv, nz]) ∈ automataflResolveDesc.constraints)
    (hq : cgH (((Head.lin 1 carry).addProd (-1) [sa1]).addProd 1 [sa1, occ])
            ∈ automataflResolveDesc.constraints)
    (hsurv : (envAt t i).loc surv = 0 ∨ (envAt t i).loc surv = 1)
    (hnz : (envAt t i).loc nz = 0 ∨ (envAt t i).loc nz = 1)
    (hocc : (envAt t i).loc occ = 0 ∨ (envAt t i).loc occ = 1) :
    ((envAt t i).loc carry = 0 ∨ (envAt t i).loc carry = 1)
      ∧ ((envAt t i).loc carry = 1 ↔
          ((envAt t i).loc surv = 1 ∧ (envAt t i).loc nz = 1 ∧ (envAt t i).loc occ = 0)) := by
  set e := envAt t i with he
  have hsa : e.loc sa1 = e.loc surv * e.loc nz := by
    exact prod_of_sat hsat hc i hi sa1 surv nz hp hsurv hnz
  have hcv : e.loc carry = e.loc sa1 - e.loc sa1 * e.loc occ := by
    have hgg := rgateH hsat i hi hq
    have hE : (headToExpr (((Head.lin 1 carry).addProd (-1) [sa1]).addProd 1 [sa1, occ])).eval e.loc
        = e.loc carry + (-1) * e.loc sa1 + e.loc sa1 * e.loc occ := rfl
    rw [hE] at hgg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hocc with c | c <;>
      rw [hsa, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hocc with c | c <;>
    rw [hsa, a, b, c] at hcv <;> norm_num at hcv <;> rw [hcv, a, b, c] <;> norm_num

/-- **(1b) — `ft_of_sat`.** The flow-through bit is EXACTLY the five-way conjunction the emitted
chain computes: `ft = eq_chain ∧ ¬other_nz ∧ surv ∧ ¬occ_other ∧ ¬eq_back`. These are precisely the
conditions `chainDest_a` / `chainDest_b` branch on, so the reference landing square is a function of
this bit. -/
theorem ft_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (nB nO nE f1 f2 f3 ft eqAb bnz occB eqBa surv : Nat)
    (g1 : notBitPin nB bnz ∈ automataflResolveDesc.constraints)
    (g2 : notBitPin nO occB ∈ automataflResolveDesc.constraints)
    (g3 : notBitPin nE eqBa ∈ automataflResolveDesc.constraints)
    (g4 : cgH ((Head.lin (-1) f1).addProd 1 [eqAb, nB]) ∈ automataflResolveDesc.constraints)
    (g5 : cgH ((Head.lin (-1) f2).addProd 1 [f1, surv]) ∈ automataflResolveDesc.constraints)
    (g6 : cgH ((Head.lin (-1) f3).addProd 1 [f2, nO]) ∈ automataflResolveDesc.constraints)
    (g7 : cgH ((Head.lin (-1) ft).addProd 1 [f3, nE]) ∈ automataflResolveDesc.constraints)
    (hab : (envAt t i).loc eqAb = 0 ∨ (envAt t i).loc eqAb = 1)
    (hbnz : (envAt t i).loc bnz = 0 ∨ (envAt t i).loc bnz = 1)
    (hocc : (envAt t i).loc occB = 0 ∨ (envAt t i).loc occB = 1)
    (hba : (envAt t i).loc eqBa = 0 ∨ (envAt t i).loc eqBa = 1)
    (hsurv : (envAt t i).loc surv = 0 ∨ (envAt t i).loc surv = 1) :
    ((envAt t i).loc ft = 0 ∨ (envAt t i).loc ft = 1)
      ∧ ((envAt t i).loc ft = 1 ↔
          ((envAt t i).loc eqAb = 1 ∧ (envAt t i).loc bnz = 0 ∧ (envAt t i).loc surv = 1
            ∧ (envAt t i).loc occB = 0 ∧ (envAt t i).loc eqBa = 0)) := by
  set e := envAt t i with he
  have hnB : e.loc nB = 1 - e.loc bnz := by
    exact notBit_of_sat hsat hc i hi nB bnz g1 hbnz
  have hnO : e.loc nO = 1 - e.loc occB := by
    exact notBit_of_sat hsat hc i hi nO occB g2 hocc
  have hnE : e.loc nE = 1 - e.loc eqBa := by
    exact notBit_of_sat hsat hc i hi nE eqBa g3 hba
  have bnB : e.loc nB = 0 ∨ e.loc nB = 1 := by rcases hbnz with h | h <;> rw [hnB, h] <;> norm_num
  have bnO : e.loc nO = 0 ∨ e.loc nO = 1 := by rcases hocc with h | h <;> rw [hnO, h] <;> norm_num
  have bnE : e.loc nE = 0 ∨ e.loc nE = 1 := by rcases hba with h | h <;> rw [hnE, h] <;> norm_num
  have hf1 : e.loc f1 = e.loc eqAb * e.loc nB := by
    exact prod_of_sat hsat hc i hi f1 eqAb nB g4 hab bnB
  have bf1 : e.loc f1 = 0 ∨ e.loc f1 = 1 := by
    rcases hab with a | a <;> rcases bnB with b | b <;> rw [hf1, a, b] <;> norm_num
  have hf2 : e.loc f2 = e.loc f1 * e.loc surv := by
    exact prod_of_sat hsat hc i hi f2 f1 surv g5 bf1 hsurv
  have bf2 : e.loc f2 = 0 ∨ e.loc f2 = 1 := by
    rcases bf1 with a | a <;> rcases hsurv with b | b <;> rw [hf2, a, b] <;> norm_num
  have hf3 : e.loc f3 = e.loc f2 * e.loc nO := by
    exact prod_of_sat hsat hc i hi f3 f2 nO g6 bf2 bnO
  have bf3 : e.loc f3 = 0 ∨ e.loc f3 = 1 := by
    rcases bf2 with a | a <;> rcases bnO with b | b <;> rw [hf3, a, b] <;> norm_num
  have hft : e.loc ft = e.loc f3 * e.loc nE := by
    exact prod_of_sat hsat hc i hi ft f3 nE g7 bf3 bnE
  rcases hab with a | a <;> rcases hbnz with b | b <;> rcases hsurv with c | c <;>
    rcases hocc with d | d <;> rcases hba with f | f <;>
    rw [hft, hf3, hf2, hf1, hnB, hnO, hnE, a, b, c, d, f] <;> norm_num

/-- The Leg-5 / Leg-6 gate memberships, `decide`d against the byte-pinned constraint list. -/
theorem carryA_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1)
    (hnz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 0)) = 0 ∨ (envAt t i).loc (cOcc (occBase 0)) = 1) :
    ((envAt t i).loc cCarryA = 0 ∨ (envAt t i).loc cCarryA = 1)
      ∧ ((envAt t i).loc cCarryA = 1 ↔
          ((envAt t i).loc cSurv = 1 ∧ (envAt t i).loc cAnz = 1
            ∧ (envAt t i).loc (cOcc (occBase 0)) = 0)) :=
  carry_of_sat hsat hc i hi cSa1 cCarryA cSurv cAnz (cOcc (occBase 0)) (by decide) (by decide)
    hsurv hnz hocc

theorem carryB_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1)
    (hnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 1)) = 0 ∨ (envAt t i).loc (cOcc (occBase 1)) = 1) :
    ((envAt t i).loc cCarryB = 0 ∨ (envAt t i).loc cCarryB = 1)
      ∧ ((envAt t i).loc cCarryB = 1 ↔
          ((envAt t i).loc cSurv = 1 ∧ (envAt t i).loc cBnz = 1
            ∧ (envAt t i).loc (cOcc (occBase 1)) = 0)) :=
  carry_of_sat hsat hc i hi cSb1 cCarryB cSurv cBnz (cOcc (occBase 1)) (by decide) (by decide)
    hsurv hnz hocc

theorem ftA_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (cEqBit (eqBase 2)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 2)) = 1)
    (hbnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 1)) = 0 ∨ (envAt t i).loc (cOcc (occBase 1)) = 1)
    (hba : (envAt t i).loc (cEqBit (eqBase 3)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 3)) = 1)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1) :
    ((envAt t i).loc cFtA = 0 ∨ (envAt t i).loc cFtA = 1)
      ∧ ((envAt t i).loc cFtA = 1 ↔
          ((envAt t i).loc (cEqBit (eqBase 2)) = 1 ∧ (envAt t i).loc cBnz = 0
            ∧ (envAt t i).loc cSurv = 1 ∧ (envAt t i).loc (cOcc (occBase 1)) = 0
            ∧ (envAt t i).loc (cEqBit (eqBase 3)) = 0)) :=
  ft_of_sat hsat hc i hi cNBnz cNOccb cNEqba cFa1 cFa2 cFa3 cFtA (cEqBit (eqBase 2)) cBnz
    (cOcc (occBase 1)) (cEqBit (eqBase 3)) cSurv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hab hbnz hocc hba hsurv

theorem ftB_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hba : (envAt t i).loc (cEqBit (eqBase 3)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 3)) = 1)
    (hanz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 0)) = 0 ∨ (envAt t i).loc (cOcc (occBase 0)) = 1)
    (hab : (envAt t i).loc (cEqBit (eqBase 2)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 2)) = 1)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1) :
    ((envAt t i).loc cFtB = 0 ∨ (envAt t i).loc cFtB = 1)
      ∧ ((envAt t i).loc cFtB = 1 ↔
          ((envAt t i).loc (cEqBit (eqBase 3)) = 1 ∧ (envAt t i).loc cAnz = 0
            ∧ (envAt t i).loc cSurv = 1 ∧ (envAt t i).loc (cOcc (occBase 0)) = 0
            ∧ (envAt t i).loc (cEqBit (eqBase 2)) = 0)) :=
  ft_of_sat hsat hc i hi cNAnz cNOcca cNEqab cFb1 cFb2 cFb3 cFtB (cEqBit (eqBase 3)) cAnz
    (cOcc (occBase 0)) (cEqBit (eqBase 2)) cSurv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hba hanz hocc hab hsurv

/-! ## §5.8 — (2) R6: the `write_mid_witnessed` endpoints and the per-cell rewrite gate.

Leg 7 is two families: `one_hot_rowcol` on each endpoint of each piece (source pinned to the move's
own `(fx, fy)`, destination pinned to the INTERPOLATED `destHead`), and the `k` per-cell equalities
`mid[c] == keep[c]·old[c] + Σ_i carry_i·dst_i[c]·particle_i` with the swap-restore term. The source
one-hots are ordinary `Builder::one_hot`s (`oneHot_of_sat` applies verbatim — the emitted gate
polynomial is literally the same expression); the destination one-hots need their own extractor
because the index is a HEAD, not a bare column. -/

/-- **The DESTINATION one-hot extractor.** The selector pair is pinned to the interpolated landing
coordinate `own + ft·(other − own)`: on `ft = 0` the piece's own destination, on `ft = 1` the chain
endpoint. No prover freedom — the one-hot cannot name a square the `ft` bit did not select. -/
theorem dstOneHot_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (sel0 sel1 own other ft : Nat)
    (h0 : cg (gBin sel0) ∈ automataflResolveDesc.constraints)
    (h1 : cg (gBin sel1) ∈ automataflResolveDesc.constraints)
    (hs : cgH (((Head.c (-1)).addLin 1 sel0).addLin 1 sel1) ∈ automataflResolveDesc.constraints)
    (hx : cgH (((Head.lin 0 sel0).addLin 1 sel1).append ((destHead own other ft).scale (-1)))
            ∈ automataflResolveDesc.constraints)
    (hown : (envAt t i).loc own = 0 ∨ (envAt t i).loc own = 1)
    (hoth : (envAt t i).loc other = 0 ∨ (envAt t i).loc other = 1)
    (hft : (envAt t i).loc ft = 0 ∨ (envAt t i).loc ft = 1) :
    ((envAt t i).loc sel1
        = (envAt t i).loc own
          + (envAt t i).loc ft * ((envAt t i).loc other - (envAt t i).loc own))
      ∧ (envAt t i).loc sel0 = 1 - (envAt t i).loc sel1
      ∧ ((envAt t i).loc sel1 = 0 ∨ (envAt t i).loc sel1 = 1) := by
  set e := envAt t i with he
  have b0 : e.loc sel0 = 0 ∨ e.loc sel0 = 1 :=
    bin_of_gate (rgate hsat i hi h0) (canon_loc hc i _)
  have b1 : e.loc sel1 = 0 ∨ e.loc sel1 = 1 :=
    bin_of_gate (rgate hsat i hi h1) (canon_loc hc i _)
  have hsum : e.loc sel0 + e.loc sel1 = 1 := by
    have hg := rgateH hsat i hi hs
    have hE : (headToExpr (((Head.c (-1)).addLin 1 sel0).addLin 1 sel1)).eval e.loc
        = e.loc sel0 + e.loc sel1 + (-1) := rfl
    rw [hE] at hg
    have := (gate_modEq_iff (x := e.loc sel0 + e.loc sel1 + -1)
      (a := e.loc sel0 + e.loc sel1) (b := 1) (by ring)).mp hg
    rcases b0 with h | h <;> rcases b1 with h' | h' <;>
      exact eq_of_modEq_small (by rw [h, h']; norm_num) (by norm_num) this
  have hval : e.loc sel1 = e.loc own + e.loc ft * (e.loc other - e.loc own) := by
    have hg := rgateH hsat i hi hx
    have hE : (headToExpr (((Head.lin 0 sel0).addLin 1 sel1).append
        ((destHead own other ft).scale (-1)))).eval e.loc
        = e.loc sel1 + (-1) * e.loc own + (-1) * (e.loc ft * e.loc other)
          + e.loc ft * e.loc own := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hown with a | a <;> rcases hoth with b | b <;> rcases hft with c | c <;>
      rw [a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  exact ⟨hval, by omega, b1⟩

/-- **The PER-CELL REWRITE GATE, as an extracted field equation.** `write_mid_witnessed`'s cell
gate, rearranged: the MID cell is the OLD cell KEPT (unless it is a cleared source or a landing
target), plus each landing piece's particle. Stated mod `p` — the raw polynomial can leave the
canonical window on a witness the alphabet gates then reject, and that rejection is exactly how the
double-count configurations are ruled out downstream. `Sa`/`Da` are the row×column one-hot products
of piece A's source and (interpolated) destination at this cell; likewise `Sb`/`Db`. -/
theorem writeCell_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c y x : Nat)
    (hmem : cgH (writeCellHead c) ∈ automataflResolveDesc.constraints)
    (hshape : (headToExpr (writeCellHead c)).eval (envAt t i).loc
        = (envAt t i).loc (mid c) + (-1) * (envAt t i).loc (old c)
          + (envAt t i).loc (carryCol 0) * (envAt t i).loc (wSrcRow 0 y)
              * (envAt t i).loc (wSrcCol 0 x) * (envAt t i).loc (old c)
          + (envAt t i).loc (carryCol 0) * (envAt t i).loc (wDstRow 0 y)
              * (envAt t i).loc (wDstCol 0 x) * (envAt t i).loc (old c)
          + (-1) * ((envAt t i).loc (carryCol 0) * (envAt t i).loc (wDstRow 0 y)
              * (envAt t i).loc (wDstCol 0 x) * (envAt t i).loc (particleCol 0))
          + (envAt t i).loc (carryCol 1) * (envAt t i).loc (wSrcRow 1 y)
              * (envAt t i).loc (wSrcCol 1 x) * (envAt t i).loc (old c)
          + (envAt t i).loc (carryCol 1) * (envAt t i).loc (wDstRow 1 y)
              * (envAt t i).loc (wDstCol 1 x) * (envAt t i).loc (old c)
          + (-1) * ((envAt t i).loc (carryCol 1) * (envAt t i).loc (wDstRow 1 y)
              * (envAt t i).loc (wDstCol 1 x) * (envAt t i).loc (particleCol 1))
          + (-1) * ((envAt t i).loc (carryCol 0) * (envAt t i).loc (wSrcRow 0 y)
              * (envAt t i).loc (wSrcCol 0 x) * (envAt t i).loc (carryCol 1)
              * (envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)
              * (envAt t i).loc (old c))
          + (-1) * ((envAt t i).loc (carryCol 1) * (envAt t i).loc (wSrcRow 1 y)
              * (envAt t i).loc (wSrcCol 1 x) * (envAt t i).loc (carryCol 0)
              * (envAt t i).loc (wDstRow 0 y) * (envAt t i).loc (wDstCol 0 x)
              * (envAt t i).loc (old c))) :
    (envAt t i).loc (mid c)
      ≡ (1 - (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wSrcRow 0 y)
                * (envAt t i).loc (wSrcCol 0 x))
           - (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wDstRow 0 y)
                * (envAt t i).loc (wDstCol 0 x))
           - (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wSrcRow 1 y)
                * (envAt t i).loc (wSrcCol 1 x))
           - (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wDstRow 1 y)
                * (envAt t i).loc (wDstCol 1 x))
           + (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wSrcRow 0 y)
                * (envAt t i).loc (wSrcCol 0 x)) * ((envAt t i).loc (carryCol 1)
                * ((envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)))
           + (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wSrcRow 1 y)
                * (envAt t i).loc (wSrcCol 1 x)) * ((envAt t i).loc (carryCol 0)
                * ((envAt t i).loc (wDstRow 0 y) * (envAt t i).loc (wDstCol 0 x))))
          * (envAt t i).loc (old c)
        + (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wDstRow 0 y)
            * (envAt t i).loc (wDstCol 0 x)) * (envAt t i).loc (particleCol 0)
        + (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wDstRow 1 y)
            * (envAt t i).loc (wDstCol 1 x)) * (envAt t i).loc (particleCol 1)
        [ZMOD 2013265921] := by
  have hg := rgateH hsat i hi hmem
  rw [hshape] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- The four cells' instances — each `(c, y, x)` triple's membership `decide`d against the
byte-pinned list and its polynomial SHAPE discharged by `rfl` on the emitted head. -/
example (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) : True := by
  have _h0 := writeCell_of_sat hsat i hi 0 0 0 (by decide) rfl
  have _h1 := writeCell_of_sat hsat i hi 1 0 1 (by decide) rfl
  have _h2 := writeCell_of_sat hsat i hi 2 1 0 (by decide) rfl
  have _h3 := writeCell_of_sat hsat i hi 3 1 1 (by decide) rfl
  trivial

end Selection

/-! ### §5.8.1 — The FIELD ALGEBRA of the per-cell gate, discharged once for all cells.

`writeCell_of_sat` delivers a congruence mod `p`; these two lemmas turn it into the reference's
per-cell VALUE. Both are pure integer statements over the four indicator products
`A = carry_a·src_a[c]`, `B = carry_a·dst_a[c]`, `C = carry_b·src_b[c]`, `D = carry_b·dst_b[c]`, so
they hold for every cell and every board without further case analysis upstream. -/

/-- **THE DOUBLE-COUNT EXCLUSION — and a DESCRIPTOR DEFECT (completeness), found here.**

If BOTH pieces carry and BOTH clear the SAME cell (`frm_a = frm_b`, the "two players propose the
identical move" turn, which the reference explicitly does NOT treat as a conflict —
`Automatafl.conflictResolve`'s doc: "Identical `(src,dst)` moves are NOT a conflict"), the emitted
cell gate subtracts the old particle TWICE, forcing `mid ≡ −old`. With both cells range-checked into
the particle alphabet that pins `old = 0` — i.e. the source was VACUUM, contradicting the carry.

So the descriptor has NO satisfying witness on an identical-move turn: soundness is intact (this is
the fact the capstone leans on to rule out the double-count configurations), but the leaf is
INCOMPLETE — a legal automatafl turn it cannot prove. Recorded as a defect, not papered over. -/
theorem noSharedSource {oldc midc : ℤ} (hold : 0 ≤ oldc ∧ oldc ≤ 3) (hmid : 0 ≤ midc ∧ midc ≤ 3)
    (hmod : midc ≡ -oldc [ZMOD 2013265921]) : oldc = 0 := by
  have h : midc + oldc ≡ 0 [ZMOD 2013265921] := by
    have := hmod.add_right oldc
    simpa using this
  have := eq_of_modEq_canon (a := midc + oldc) (b := 0) ⟨by omega, by omega⟩ canon_zero h
  omega

/-- **(2) THE PER-CELL REWRITE, RESOLVED.** With the two structural exclusions (a cell is never both
a cleared source and a landing of the SAME piece; and — by `noSharedSource` — never a shared source
or a shared landing of BOTH pieces), the emitted cell polynomial evaluates to exactly the reference
`applyMoves` rewrite of that cell: a landing piece's particle, else vacuum on a cleared source, else
the old cell kept. Seven live cases out of sixteen; the other nine are the excluded products. -/
theorem cellAlgebra {oldc midc pa pb A B C D : ℤ}
    (hA : A = 0 ∨ A = 1) (hB : B = 0 ∨ B = 1) (hC : C = 0 ∨ C = 1) (hD : D = 0 ∨ D = 1)
    (hAB : A * B = 0) (hCD : C * D = 0) (hAC : A * C = 0) (hBD : B * D = 0)
    (hold : 0 ≤ oldc ∧ oldc ≤ 3) (hmid : 0 ≤ midc ∧ midc ≤ 3)
    (hpa : 0 ≤ pa ∧ pa ≤ 3) (hpb : 0 ≤ pb ∧ pb ≤ 3)
    (hmod : midc ≡ (1 - A - B - C - D + A * D + C * B) * oldc + B * pa + D * pb
              [ZMOD 2013265921]) :
    midc = if B = 1 then pa else if D = 1 then pb else if A = 1 ∨ C = 1 then 0 else oldc := by
  have hcan : ∀ z : ℤ, 0 ≤ z → z ≤ 3 → Canon z := fun z h1 h2 => ⟨h1, by omega⟩
  rcases hA with a | a <;> rcases hB with b | b <;> rcases hC with c | c <;> rcases hD with d | d <;>
    subst a <;> subst b <;> subst c <;> subst d <;>
    first
      | (exfalso; simp only [mul_one, one_mul, mul_zero, zero_mul] at hAB hAC hBD hCD; omega)
      | (norm_num at hmod ⊢;
         refine eq_of_modEq_canon (hcan _ hmid.1 hmid.2) ?_ hmod;
         first
           | exact hcan _ hold.1 hold.2
           | exact hcan _ hpa.1 hpa.2
           | exact hcan _ hpb.1 hpb.2
           | exact canon_zero)

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

/-- **THE DEFECT-#4 CANARY.** The newly emitted board-cell alphabet gate REJECTS exactly the witness
that broke the capstone: `old[0] = 4`, which the circuit's `anz = forced_ge0(fp − 1, 5)` would have
read as "carries a piece" while `codeToParticle 4 = .vacuum` reads it as empty. Two-sided: an
in-alphabet cell passes, the out-of-alphabet cell that made the refinement FALSE does not. -/
def canonAlphaExpr : EmittedExpr := memberExpr (old 0) [0, 1, 2, 3]
def canonAlphaGood : Assignment := fun c => if c = old 0 then 2 else 0   -- ATTRACTOR: legal
def canonAlphaForge : Assignment := fun c => if c = old 0 then 4 else 0  -- the DEFECT witness

#guard canonAlphaExpr.eval canonAlphaGood == 0    -- in-alphabet cell: ACCEPTED
#guard canonAlphaExpr.eval canonAlphaForge != 0   -- `old[0] = 4`: REJECTED (was accepted before)
#guard (memberExpr (mid 0) [0, 1, 2, 3]).eval (fun c => if c = mid 0 then 4 else 0) != 0
#guard cg (memberExpr (old 0) [0,1,2,3]) ∈ automataflResolveDesc.constraints
#guard cg (memberExpr (mid 3) [0,1,2,3]) ∈ automataflResolveDesc.constraints

/-- **THE CARRY CANARY.** The carry gate `carry == sa1·(1 − occ)` REJECTS a prover who claims the
piece journeyed while its line was occluded: with `sa1 = 1` and `occ = 1` the only satisfying carry
is `0`, so the forged `carry = 1` fails. -/
def canonCarryExpr : EmittedExpr :=
  headToExpr (((Head.lin 1 cCarryA).addProd (-1) [cSa1]).addProd 1 [cSa1, cOcc (occBase 0)])
def canonCarryGood : Assignment := fun c => if c = cSa1 ∨ c = cCarryA then 1 else 0
def canonCarryForge : Assignment := fun c =>
  if c = cSa1 ∨ c = cCarryA ∨ c = cOcc (occBase 0) then 1 else 0

#guard canonCarryExpr.eval canonCarryGood == 0     -- clear line, source carries: carry = 1 holds
#guard canonCarryExpr.eval canonCarryForge != 0    -- occluded but carry claimed: REJECTED

/-- **THE FLOW-THROUGH CANARY.** `ft` rides `not_bit(bnz)`: a prover who wants the chain bonus must
claim the square ahead is VACATING. Claiming `¬bnz` while `bnz = 1` fails the pin, so a piece can
never flow through a square that still holds a piece. -/
def canonFtExpr : EmittedExpr := headToExpr (((Head.lin 1 cNBnz).addLin 1 cBnz).addConst (-1))
def canonFtGood : Assignment := fun c => if c = cNBnz then 1 else 0
def canonFtForge : Assignment := fun c => if c = cNBnz ∨ c = cBnz then 1 else 0

#guard canonFtExpr.eval canonFtGood == 0     -- bnz = 0, nBnz = 1: the honest vacating square
#guard canonFtExpr.eval canonFtForge != 0    -- bnz = 1 with nBnz = 1 claimed: REJECTED

/-- **THE DESTINATION-ONE-HOT CANARY.** The landing selector is pinned to the INTERPOLATED
destination `to_own + ft·(to_other − to_own)`. With `ft = 0` and `ty_a = 1` the only satisfying
selector is `1`: a prover cannot land the piece on a square the `ft` bit did not select. -/
def canonDstExpr : EmittedExpr :=
  headToExpr (((Head.lin 0 (wDstRow 0 0)).addLin 1 (wDstRow 0 1)).append
    ((destHead (cTy (mvBase 0)) (cTy (mvBase 1)) cFtA).scale (-1)))
def canonDstGood : Assignment := fun c =>
  if c = wDstRow 0 1 ∨ c = cTy (mvBase 0) then 1 else 0
def canonDstForge : Assignment := fun c => if c = cTy (mvBase 0) then 1 else 0

#guard canonDstExpr.eval canonDstGood == 0     -- ft = 0: the piece lands on its OWN `to`
#guard canonDstExpr.eval canonDstForge != 0    -- landing square forged away from `to`: REJECTED

/-- **THE DOUBLE-COUNT CANARY** (the completeness defect, witnessed). On the identical-move turn
(`frm_a = frm_b`, both carrying) the emitted cell gate subtracts the source particle TWICE, so the
only satisfying `mid` at that cell is `−old` — out of the particle alphabet for every non-vacuum
source. Both gates are shown biting on the SAME assignment: the cell gate is satisfiable only at
`mid = −1`, which the alphabet gate then rejects. -/
def canonDoubleGood : Assignment := fun c =>
  if c = old 0 ∨ c = particleCol 0 ∨ c = particleCol 1 then 1
  else if c = carryCol 0 ∨ c = carryCol 1 ∨ c = wSrcRow 0 0 ∨ c = wSrcCol 0 0
       ∨ c = wSrcRow 1 0 ∨ c = wSrcCol 1 0 then 1
  else if c = mid 0 then -1 else 0

#guard (headToExpr (writeCellHead 0)).eval canonDoubleGood == 0        -- forced: mid = −old
#guard (memberExpr (mid 0) [0, 1, 2, 3]).eval canonDoubleGood != 0     -- and −1 is NOT a particle

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
#print axioms boardvalid_of_sat
#print axioms frmConflict_pair
#print axioms toConflict_pair
#print axioms conflictResolve_pair
#print axioms nextOf_pair
#print axioms followChain_own
#print axioms followChain_own_landing
#print axioms followChain_flowThrough
#print axioms followChain_twoCycle
#print axioms chainDest_a
#print axioms followChain_ownB
#print axioms followChain_own_landingB
#print axioms followChain_flowThroughB
#print axioms followChain_twoCycleB
#print axioms chainDest_b
#print axioms prod_of_sat
#print axioms notBit_of_sat
#print axioms carry_of_sat
#print axioms ft_of_sat
#print axioms carryA_of_sat
#print axioms carryB_of_sat
#print axioms ftA_of_sat
#print axioms ftB_of_sat
#print axioms dstOneHot_of_sat
#print axioms writeCell_of_sat
#print axioms noSharedSource
#print axioms cellAlgebra

end Dregg2.Circuit.Emit.AutomataflResolveRefine
