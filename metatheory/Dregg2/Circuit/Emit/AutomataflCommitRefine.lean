/-
# `AutomataflCommitRefine` — the SEAM-DISCHARGE bridge off `automataflCommitDesc n`

Step 2 of the n-generic board-commitment rebuild, and the mechanism that KILLS the whole-turn seam
residual. `AutomataflCommit.lean` (Step 1) emitted the base-4 pack family and proved the PURE-Lean
`pack_injective` / `pack_injective_modp` / `packBoard_injective`. Those live on abstract cell columns;
they say NOTHING yet about what a satisfying witness of the emitted descriptor actually publishes.

This file closes that gap over the EMITTED object `automataflCommitDesc n` (LEAN-AUTHORED AIR — the
pack gates, the alphabet range gates, and the packed-felt PI bindings are all `VmConstraint2` emitted
in `AutomataflCommit`; Rust only calls the emit path). It lands two theorems, both keyed on the
deployed acceptance predicate `Satisfied2`, in the exact extraction style of
`AutomataflStepRefine`/`AutomataflResolveRefine` (gate ⇐ `Satisfied2`, `.piBinding` ⇐ `Satisfied2`,
canonicality via `StepCanon`):

  (1) **`pack_pi_of_sat` — THE PACKED TRANSPORT.** On a satisfying, canonical trace, the committed
      public input `t.pub (16 + j)` is congruent mod `p` to `packBoard`'s `j`-th felt of the board
      DECODED off the cell columns. Derived from the emitted `packBoardConstraints` gate (the linear
      pack `packed_j − Σ 4^i·cell = 0`), the emitted `commitBoardConstraints` `.piBinding`
      (`packed_j = PI[16+j]`), and the emitted `boardRangeCells` alphabet gates (which make the
      `{0,1,2,3}` decode a THEOREM, not an assumption). The `mod-p`/no-wrap collapse rides
      `AutomataflCommit.packCell_nonneg`.

  (2) **`seam_of_equal_pis` — THE SEAM-DISCHARGE LEMMA.** Two satisfying, canonical witnesses whose
      committed PIs are EQUAL (`t_R.pub(16+j) = t_A.pub(16+j)` — exactly what the fold-level connect
      enforces when Leg R publishes the mid-commitment and Leg A consumes the old-commitment) have
      cell-wise-agreeing decoded boards. Proof: `pack_pi_of_sat` both sides ⇒ the two packed felt
      tuples agree mod `p` ⇒ `AutomataflCommit.pack_injective_modp` ⇒ cell-wise agreement.
      UNCONDITIONAL, PURE Lean, NO crypto floor — this is the reusable lemma that turns the
      whole-turn seam HYPOTHESIS into a discharged consequence of the fold PI-equality once the
      Leg R/A descriptors adopt this commitment (the coupled `descN` refactor; NOT done here).

Nothing is a vacuous `P → P`; the forge canary (`forge_rejected` + the `#guard`s) shows the transport
gate BITES. ADDITIVE: does not touch the capstones or the Step/Resolve descriptors.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Membership into the fold-generated
constraint list is discharged by `List.mem_map`/`List.mem_append_*` on the `n`-generic families
(no `decide` over a variable-length list), so the proofs are n-generic.
-/
import Dregg2.Circuit.Emit.AutomataflCommit
import Dregg2.Circuit.Emit.AutomataflStepRefine

namespace Dregg2.Circuit.Emit.AutomataflCommitRefine

open Dregg2.Circuit.Emit.AutomataflCommit
open Dregg2.Circuit.Emit.AutomataflStepRefine (Canon eq_of_modEq_canon StepCanon canon_loc codeToParticle)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Games.Automatafl (Board Coord Particle)
open Dregg2.Circuit (Assignment)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §0 — Pure list/eval glue for the emitted linear gate. -/

/-- The reference linear combination `Σ (coeff · loc[col])` of a gate's term list. -/
def linComb (terms : List (ℤ × Nat)) (a : Assignment) : ℤ :=
  (terms.map (fun t => t.1 * a t.2)).sum

/-- `sumExpr` (the left-folded gate sum) evaluates to the list-sum of the pieces. -/
theorem foldl_add_eval (a : Assignment) :
    ∀ (rest : List EmittedExpr) (init : EmittedExpr),
      (rest.foldl (fun acc x => .add acc x) init).eval a
        = init.eval a + (rest.map (fun e => e.eval a)).sum := by
  intro rest
  induction rest with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    simp only [List.foldl_cons]
    rw [ih (.add init x)]
    simp only [EmittedExpr.eval, List.map_cons, List.sum_cons]
    ring

theorem sumExpr_eval (a : Assignment) (es : List EmittedExpr) :
    (sumExpr es).eval a = (es.map (fun e => e.eval a)).sum := by
  cases es with
  | nil => simp [sumExpr, EmittedExpr.eval]
  | cons e rest =>
    simp only [sumExpr]
    rw [foldl_add_eval a rest e]
    simp only [List.map_cons, List.sum_cons]

/-- Each emitted `varTerm (c, col)` evaluates to `c · loc[col]`. -/
theorem varTerm_eval (a : Assignment) (t : ℤ × Nat) : (varTerm t).eval a = t.1 * a t.2 := by
  obtain ⟨c, col⟩ := t
  simp only [varTerm]
  split
  · next h => have hc1 : c = 1 := by simpa using h
              subst hc1; simp [EmittedExpr.eval]
  · next _ => simp [EmittedExpr.eval]

/-- The emitted gate body `sumExpr (terms.map varTerm)` evaluates to the reference `linComb`. -/
theorem sumExpr_varTerm_eval (a : Assignment) (terms : List (ℤ × Nat)) :
    (sumExpr (terms.map varTerm)).eval a = linComb terms a := by
  rw [sumExpr_eval]
  simp only [List.map_map, linComb]
  apply congrArg
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  exact varTerm_eval a t

/-- Dropping zero-coefficient terms (the `linGate` filter) does not change the linear combination. -/
theorem linComb_filter (a : Assignment) (terms : List (ℤ × Nat)) :
    linComb (terms.filter (fun t => t.1 != 0)) a = linComb terms a := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    rw [List.filter_cons]
    simp only [linComb] at ih
    by_cases h : (t.1 != 0) = true
    · rw [if_pos h]
      simp only [linComb, List.map_cons, List.sum_cons, ih]
    · rw [if_neg h]
      have h0 : t.1 = 0 := by simpa [bne_iff_ne] using h
      simp only [linComb, List.map_cons, List.sum_cons, ih, h0, zero_mul, zero_add]

/-- `linGate terms 0` is `.base (.gate (sumExpr (…filter…)))` — the second `let` collapses at `k = 0`. -/
theorem linGate_zero (terms : List (ℤ × Nat)) :
    linGate terms 0
      = .base (.gate (sumExpr ((terms.filter (fun t => t.1 != 0)).map varTerm))) := by
  simp [linGate]

/-- Signed base-4 negation glue. -/
theorem sum_map_neg {α : Type*} (l : List α) (g : α → ℤ) :
    (l.map (fun x => -(g x))).sum = -(l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `filterMap (if P then some (g,h) else none)` mapped+summed = the `if…else 0` map+sum. -/
theorem sum_map_filterMap_if {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (g : α → ℤ) (h : α → Nat) (a : Assignment) :
    (((l.filterMap (fun x => if P x then some (g x, h x) else none)).map
        (fun t => t.1 * a t.2)).sum)
      = (l.map (fun x => if P x then g x * a (h x) else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : P x
    · simp only [List.filterMap_cons, if_pos hp, List.map_cons, List.sum_cons, ih]
    · simp only [List.filterMap_cons, if_neg hp, List.map_cons, List.sum_cons, ih, zero_add]

/-- `horner4` of a length-15 `range`-map is the explicit weighted sum `Σ_{i<15} 4^i · f i`. The
felt width `CELLS_PER_FELT = 15` is concrete, so this closes by unfolding + `ring`. -/
theorem horner4_range15 (f : Nat → ℤ) :
    horner4 ((List.range 15).map f)
      = ((List.range 15).map (fun i => (4:ℤ) ^ i * f i)).sum := by
  show horner4 (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List Nat).map f)
    = (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List Nat).map (fun i => (4:ℤ) ^ i * f i)).sum
  simp only [List.map_cons, List.map_nil, horner4_cons, horner4_nil, List.sum_cons, List.sum_nil,
             pow_succ, pow_zero]
  ring

/-! ## §1 — The decoded board and the alphabet decode. -/

/-- Decode a row's cell columns `[0, n²)` into the reference `Board`: cell `(x,y)` is the felt-decode
of `loc[y·n + x]` (the working `n²`-cell representation `PACK_CELL c = c`). The `automaton` field is
irrelevant to the pack (`boardCode` reads only `cellAt`), so it is a placeholder. -/
def boardDecodeCommit (n : Nat) (e : VmRowEnv) : Board where
  size          := n
  automaton     := ⟨0, 0⟩
  cells         := fun c => codeToParticle (e.loc (c.y * n + c.x))
  useColumnRule := true

/-- `particleCode ∘ codeToParticle = id` on the alphabet `{0,1,2,3}` (the exact inverse the pack
needs to read the circuit cell back off the decoded board). -/
theorem particleCode_codeToParticle {z : ℤ} (h : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3) :
    particleCode (codeToParticle z) = z := by
  rcases h with h | h | h | h <;> subst h <;> decide

/-- **The circuit cell IS the decoded board cell** (on the alphabet). For an in-bounds index the
board-code of `boardDecodeCommit` is exactly the circuit column value; padding indices are `0`. This
is where the `boardRangeCells` alphabet gate pays off: `hmem` is supplied by `cell_mem_of_sat`. -/
theorem boardCode_decode_eq (n : Nat) (e : VmRowEnv) (idx : Nat)
    (hmem : idx < n * n → (e.loc idx = 0 ∨ e.loc idx = 1 ∨ e.loc idx = 2 ∨ e.loc idx = 3)) :
    boardCode (boardDecodeCommit n e) n idx = if idx < n * n then e.loc idx else 0 := by
  unfold boardCode
  by_cases hlt : idx < n * n
  · rw [if_pos hlt, if_pos hlt]
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hlt
      · exact h
    have hxlt : idx % n < n := Nat.mod_lt _ hn
    have hylt : idx / n < n := Nat.div_lt_of_lt_mul hlt
    have hidx : (idx / n) * n + idx % n = idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod idx n
    have hcell : (boardDecodeCommit n e).cellAt ⟨idx % n, idx / n⟩ = codeToParticle (e.loc idx) := by
      simp only [Board.cellAt, boardDecodeCommit]
      rw [if_pos ⟨hxlt, hylt⟩, hidx]
    rw [hcell, particleCode_codeToParticle (hmem hlt)]
  · rw [if_neg hlt, if_neg hlt]

/-! ## §2 — Single-row gate / `.piBinding` extraction off `Satisfied2 (automataflCommitDesc n)`. -/

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- A per-row `.gate` of the commitment descriptor vanishes mod `p` on a NON-LAST row. -/
theorem commit_gate (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {body : EmittedExpr}
    (hg : (.base (.gate body) : VmConstraint2) ∈ (automataflCommitDesc n).constraints) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have : i + 1 ≠ t.rows.length := by omega
    simpa using this
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **The alphabet gate DERIVES `{0,1,2,3}`.** A `boardRangeCells` member gate on a canonical trace
forces the in-bounds cell into the two-bit alphabet — so `pack_injective`'s precondition is a theorem
of the descriptor, not an assumption. Mirrors `mem3_of_gate` with one factor wider. -/
theorem cell_mem_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (idx : Nat) (hidx : idx < n * n) :
    (envAt t 0).loc idx = 0 ∨ (envAt t 0).loc idx = 1 ∨ (envAt t 0).loc idx = 2
      ∨ (envAt t 0).loc idx = 3 := by
  have hmem : (.base (.gate (memberExpr (PACK_CELL idx) [0, 1, 2, 3])) : VmConstraint2)
      ∈ (automataflCommitDesc n).constraints := by
    show _ ∈ boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩
  have hg := commit_gate hsat 0 (by omega) hmem
  simp only [PACK_CELL, memberExpr, List.foldl, EmittedExpr.eval] at hg
  have hd : (2013265921 : ℤ) ∣
      ((((envAt t 0).loc idx + -0) * ((envAt t 0).loc idx + -1)) * ((envAt t 0).loc idx + -2))
        * ((envAt t 0).loc idx + -3) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using hg)
  obtain ⟨hc0, hc1⟩ := canon_loc hc 0 idx
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · rcases pPrimeInt.dvd_mul.mp h2 with h3 | h3
      · obtain ⟨k, hk⟩ := h3; left; omega
      · obtain ⟨k, hk⟩ := h3; right; left; omega
    · obtain ⟨k, hk⟩ := h2; right; right; left; omega
  · obtain ⟨k, hk⟩ := h1; right; right; right; omega

/-- The emitted pack gate `packed_j − Σ 4^i·cell = 0` forces `linComb (packTerms n j) loc ≡ 0`. -/
theorem pack_gate_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    linComb (packTerms n j) (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hmem : (linGate (packTerms n j) 0) ∈ (automataflCommitDesc n).constraints := by
    show _ ∈ boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  rw [linGate_zero] at hmem
  have hg := commit_gate hsat 0 (by omega) hmem
  rwa [sumExpr_varTerm_eval, linComb_filter] at hg

/-- The emitted `commitBoardConstraints` `.piBinding` forces `packed_j ≡ PI[16+j]` on the first row. -/
theorem commit_pi_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    (envAt t 0).loc (PACK_FELT n j) ≡ (envAt t 0).pub (COMMIT_PI_BASE + j) [ZMOD 2013265921] := by
  have hmem : (.base (.piBinding VmRow.first (PACK_FELT n j) (COMMIT_PI_BASE + j)) : VmConstraint2)
      ∈ (automataflCommitDesc n).constraints := by
    show _ ∈ boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have hrc := hsat.rowConstraints 0 (by omega) _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrc
  exact hrc rfl

end Extract

/-! ## §3 — The two per-felt integer identities that bridge the gate to `packCell`. -/

/-- The circuit-side weighted cell sum for felt `j` (the `if idx<n²` padding mirrors `boardCode`). -/
def packCircSum (n j : Nat) (a : Assignment) : ℤ :=
  ((List.range 15).map (fun i => if 15 * j + i < n * n then (4:ℤ) ^ i * a (15 * j + i) else 0)).sum

/-- **L1.** The emitted pack gate value `= loc[packed_j] − packCircSum`. -/
theorem linComb_packTerms (n j : Nat) (a : Assignment) :
    linComb (packTerms n j) a = a (PACK_FELT n j) - packCircSum n j a := by
  have h1 : (((List.range 15).filterMap (fun i =>
        if 15 * j + i < n * n then some (-(4:ℤ) ^ i, 15 * j + i) else none)).map
        (fun t => t.1 * a t.2)).sum = -(packCircSum n j a) := by
    rw [sum_map_filterMap_if (List.range 15) (fun i => 15 * j + i < n * n)
      (fun i => -(4:ℤ) ^ i) (fun i => 15 * j + i) a]
    rw [show (fun i => if 15 * j + i < n * n then (-(4:ℤ) ^ i) * a (15 * j + i) else 0)
          = (fun i => -(if 15 * j + i < n * n then (4:ℤ) ^ i * a (15 * j + i) else 0)) from ?_]
    · rw [sum_map_neg]; rfl
    · funext i; split_ifs <;> ring
  simp only [linComb, packTerms, PACK_CELL, List.map_cons, List.sum_cons, one_mul]
  rw [h1]; ring

/-- **L2.** `packCell` of the decoded board `= packCircSum` (needs the alphabet membership). -/
theorem packCell_boardCode_eq (n j : Nat) (e : VmRowEnv)
    (hcells : ∀ idx, idx < n * n →
      (e.loc idx = 0 ∨ e.loc idx = 1 ∨ e.loc idx = 2 ∨ e.loc idx = 3)) :
    packCell (boardCode (boardDecodeCommit n e) n) j = packCircSum n j e.loc := by
  unfold packCell
  rw [horner4_range15 (fun i => boardCode (boardDecodeCommit n e) n (15 * j + i))]
  simp only [packCircSum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [boardCode_decode_eq n e (15 * j + i) (fun hh => hcells (15 * j + i) hh)]
  split_ifs <;> ring

/-! ## §4 — (1) THE PACKED TRANSPORT and (2) THE SEAM-DISCHARGE LEMMA. -/

section Transport
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- **`pack_pi_of_sat` — (1) THE PACKED TRANSPORT.** On a satisfying, canonical trace the committed
public input `PI[16+j]` equals (mod `p`) the `j`-th packed felt of the board decoded off the cell
columns. Every ingredient is extracted from the emitted `automataflCommitDesc n` — the pack gate, the
`.piBinding`, and the alphabet gates — none assumed. -/
theorem pack_pi_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (COMMIT_PI_BASE + j)
      ≡ packCell (boardCode (boardDecodeCommit n (envAt t 0)) n) j [ZMOD 2013265921] := by
  have hcells : ∀ idx, idx < n * n →
      ((envAt t 0).loc idx = 0 ∨ (envAt t 0).loc idx = 1 ∨ (envAt t 0).loc idx = 2
        ∨ (envAt t 0).loc idx = 3) :=
    fun idx hidx => cell_mem_of_sat hsat hc hlen idx hidx
  have hgate : linComb (packTerms n j) (envAt t 0).loc ≡ 0 [ZMOD 2013265921] :=
    pack_gate_of_sat hsat hlen j hj
  rw [linComb_packTerms, ← packCell_boardCode_eq n j (envAt t 0) hcells] at hgate
  have hfelt : (envAt t 0).loc (PACK_FELT n j)
      ≡ packCell (boardCode (boardDecodeCommit n (envAt t 0)) n) j [ZMOD 2013265921] :=
    (gate_modEq_iff rfl).mp hgate
  have hpi := commit_pi_of_sat hsat hlen j hj
  exact (hpi.symm).trans hfelt

/-- **`forge_rejected` — the transport BITES.** No satisfying, canonical witness can publish a
committed PI that is NOT the genuine packed board felt: the pack gate + `.piBinding` force
`PI[16+j] ≡ packCell(…) [ZMOD p]`, so a non-congruent (forged) PI is refused. The contrapositive of
`pack_pi_of_sat`. -/
theorem forge_rejected (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n)
    (hforge : ¬ (t.pub (COMMIT_PI_BASE + j)
      ≡ packCell (boardCode (boardDecodeCommit n (envAt t 0)) n) j [ZMOD 2013265921])) :
    False :=
  hforge (pack_pi_of_sat hsat hc hlen j hj)

end Transport

/-- **`seam_of_equal_pis` — (2) THE SEAM-DISCHARGE LEMMA (unconditional, pure Lean, no crypto).**
Two satisfying, canonical witnesses of `automataflCommitDesc n` whose committed PIs agree publish
cell-wise-agreeing decoded boards. This is the reusable object: once Leg R and Leg A adopt this
commitment, the fold's PI-equality (`t_R.pub(16+j) = t_A.pub(16+j)`) DISCHARGES the whole-turn seam
"the two decoded boards agree cell-wise" as a theorem — via `pack_pi_of_sat` on both sides feeding
`AutomataflCommit.pack_injective_modp`. -/
theorem seam_of_equal_pis {hash : List ℤ → ℤ} {n : Nat}
    {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (hsatR : Satisfied2 hash (automataflCommitDesc n) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hash (automataflCommitDesc n) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hpi : ∀ j, j < feltCount n →
      tR.pub (COMMIT_PI_BASE + j) = tA.pub (COMMIT_PI_BASE + j)) :
    ∀ x y : Nat, x < n → y < n →
      (boardDecodeCommit n (envAt tR 0)).cellAt ⟨x, y⟩
        = (boardDecodeCommit n (envAt tA 0)).cellAt ⟨x, y⟩ := by
  have hcodes : ∀ i, i < 15 * feltCount n →
      boardCode (boardDecodeCommit n (envAt tR 0)) n i
        = boardCode (boardDecodeCommit n (envAt tA 0)) n i := by
    refine pack_injective_modp (boardCode (boardDecodeCommit n (envAt tR 0)) n)
      (boardCode (boardDecodeCommit n (envAt tA 0)) n) (feltCount n)
      (fun i _ => boardCode_mem _ n i) (fun i _ => boardCode_mem _ n i) ?_
    intro j hj
    have hR := pack_pi_of_sat hsatR hcR hlenR j hj
    have hA := pack_pi_of_sat hsatA hcA hlenA j hj
    have hcong : packCell (boardCode (boardDecodeCommit n (envAt tR 0)) n) j
        ≡ packCell (boardCode (boardDecodeCommit n (envAt tA 0)) n) j [ZMOD 2013265921] :=
      (hR.symm.trans ((hpi j hj) ▸ hA))
    exact hcong
  intro x y hx hy
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidx : y * n + x < 15 * feltCount n := lt_of_lt_of_le hlt (sq_le_feltCount n)
  have hcc := hcodes (y * n + x) hidx
  rw [boardCode_inbounds _ n x y hx hy, boardCode_inbounds _ n x y hx hy] at hcc
  exact particleCode_inj hcc

/-! ## §5 — Non-vacuity: the transport gate is REAL and two-sided (`#guard`). -/

/-- Concrete `n = 2` genuine row: cells `[REP,ATT,AUTO,VAC] = [1,2,3,0]` at columns `0..3`, the packed
felt at column `PACK_FELT 2 0 = 4` set to the genuine pack `1 + 4·2 + 16·3 + 64·0 = 57`. -/
def demoLoc2 : Assignment := fun c =>
  if c = 0 then 1 else if c = 1 then 2 else if c = 2 then 3 else if c = 4 then 57 else 0
/-- Same row, but the committed felt is FORGED to `99 ≠ 57`. -/
def demoLoc2Forge : Assignment := fun c =>
  if c = 0 then 1 else if c = 1 then 2 else if c = 2 then 3 else if c = 4 then 99 else 0
/-- Env carrying the genuine row (nxt/pub unused by the pack gate). -/
def demoEnv2 : VmRowEnv := ⟨demoLoc2, demoLoc2, demoLoc2⟩

-- The emitted pack gate on the GENUINE row vanishes (the transport is satisfiable) …
#guard (sumExpr (((packTerms 2 0).filter (fun t => t.1 != 0)).map varTerm)).eval demoLoc2 = 0
-- … and on the FORGED committed felt it does NOT (the transport gate BITES).
#guard (sumExpr (((packTerms 2 0).filter (fun t => t.1 != 0)).map varTerm)).eval demoLoc2Forge ≠ 0
-- The gate value IS the reference linear combination on both rows.
#guard linComb (packTerms 2 0) demoLoc2 = 0
#guard linComb (packTerms 2 0) demoLoc2Forge = 42
-- The genuine committed felt (57) IS the packed board felt the transport targets; the forge (99) is not.
#guard packCell (boardCode (boardDecodeCommit 2 demoEnv2) 2) 0 = 57
#guard packCell (boardCode (boardDecodeCommit 2 demoEnv2) 2) 0 ≠ 99
#guard packCircSum 2 0 demoLoc2 = 57
-- The decoded board reads the genuine cells back.
#guard (boardDecodeCommit 2 demoEnv2).cellAt ⟨0, 0⟩ = Particle.repulsor
#guard (boardDecodeCommit 2 demoEnv2).cellAt ⟨1, 0⟩ = Particle.attractor
#guard (boardDecodeCommit 2 demoEnv2).cellAt ⟨0, 1⟩ = Particle.automaton

/-! ## §6 — Axiom hygiene. -/

#assert_axioms sumExpr_varTerm_eval
#assert_axioms linComb_filter
#assert_axioms horner4_range15
#assert_axioms boardCode_decode_eq
#assert_axioms cell_mem_of_sat
#assert_axioms pack_gate_of_sat
#assert_axioms commit_pi_of_sat
#assert_axioms linComb_packTerms
#assert_axioms packCell_boardCode_eq
#assert_axioms pack_pi_of_sat
#assert_axioms forge_rejected
#assert_axioms seam_of_equal_pis

end Dregg2.Circuit.Emit.AutomataflCommitRefine
