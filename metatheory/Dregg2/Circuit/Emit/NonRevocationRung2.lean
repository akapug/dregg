/-
# Dregg2.Circuit.Emit.NonRevocationRung2 — the RUNG-2 discharge of the `FieldCanonicalDiffs`
residual for the emitted non-revocation descriptor (`nonRevocationDesc`, the `revocation` family).

## What Rung 1 gave us and what remained

`NonRevocationRefine.lean` (RUNG 1) proves the whole-descriptor bridge
`nonRevocation_nonmembership` : `Satisfied2 ∧ ChipTableSound ∧ RangeTableSound ∧ FieldCanonicalDiffs
∧ (sorted, adjacent spine) ⟹ NonMember spine x` — the queried item is a GENUINE non-member of the
committed set (NOT revoked). But it consumes an EXPLICIT residual hypothesis
`FieldCanonicalDiffs t := 0 ≤ DIFF_L ∧ 0 ≤ DIFF_R` (Rung 1's status PARTIAL): the STRICT-LOWER half
of the half-field ordering. The half-field range argument only certifies `RL = HALF_P_MINUS_1 − diff
∈ [0, 2^30)`, which over ℤ bounds `diff ∈ (HALF_P_MINUS_1 − 2^30, HALF_P_MINUS_1]` — the UPPER half.
The lower bound `diff ≥ 0` is NOT forced.

## The measured gap (MODEL-FOUND — this is a REAL circuit seam, not a modelling artifact)

`HALF_P_MINUS_1 = 1006632959` and `2^30 = 1073741824 > (p−1)/2`, so the single range lookup
`RL ∈ [0, 2^30)` OVERSHOOTS the honest positive window by exactly `2^30 − 1 − HALF_P_MINUS_1 = 2^26`.
Both the ℤ `Satisfied2` model AND the deployed BabyBear circuit (`revocation.rs`: `HALF_P_MINUS_1 −
diff` reconstructed from 30 bits) admit a NEGATIVE window `diff ∈ [−2^26, −1]`: a canonical felt
`diff = p−1` (signed `−1`) gives `RL = HALF_P_MINUS_1 + 1 = 1006632960 < 2^30`, which decomposes into
30 bits. So the ℤ model is FAITHFUL to the field here, and the gap is genuine on BOTH sides —
`satisfied_admits_negative_window` extracts the exact ℤ lower bound `−2^26 ≤ DIFF_L`, and
`cheat_carriers_do_not_force_nonmembership` exhibits a concrete forgery: the queried item set EQUAL to
a present leaf (`x = L = 100`, `diff_left = −1`) PROVABLY `Satisfied2`s `nonRevocationDesc` against
realizable `ChipTableSound` / `RangeTableSound`, yet `x` is a genuine MEMBER — a revoked item forging
freshness. `Satisfied2` + the two named carriers alone therefore CANNOT force non-membership.

## The discharge + the NAMED carrier / emit-fix

The carrier that closes it is `DiffLowerRangeSound` — the range argument ALSO certifies the diff
wires THEMSELVES lie in `[0, 2^30)` (`0 ≤ diff_left, diff_right < 2^30`). This is the TWIN of Rung 1's
`RangeTableSound` on the `RL`/`RR` range-wires, and is exactly the lower-gap tooth the emitted
descriptor is MISSING. `lowerRange_discharges_canon` derives `FieldCanonicalDiffs` from it (the `0 ≤`
halves), and `nonRevocation_rung2` composes with Rung 1 for the genuine no-forgery conclusion
`NonMember spine x`. The carrier is NAMED (never a Lean axiom), is proven LOAD-BEARING (the cheat
above `Satisfied2`s yet violates it), and NON-VACUOUS (the honest witness satisfies it and the full
bridge fires — `honest_rung2_fires` proves `200 ∉ [100,300]`).

### PRECISE emit-fix (the residual this file names, status RUNG2_PARTIAL)

`nonRevocationDesc` must add two range lookups binding `DIFF_L`, `DIFF_R` directly to `[0, 2^30)`
(equivalently: `revocation.rs` must range-check `diff_left`/`diff_right` themselves, not only
`HALF_P_MINUS_1 − diff`; equivalently, bound the leaf/query value domain below `(p−1)/2 − 2^26`). As
emitted, the `2^26` negative window admits a revoked-item freshness forgery. With that tooth present,
`DiffLowerRangeSound` is DISCHARGED by `RangeTableSound` on the new columns and the Rung-2 conclusion
becomes unconditional.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The range-argument faithfulness enters
ONLY as the NAMED `DiffLowerRangeSound` / `RangeTableSound` hypotheses; the Poseidon2 CR enters ONLY
as `ChipTableSound`; the exclusion core `sorted_gap_excludes` is unconditional combinatorics. NEW
file; all imports read-only.
-/
import Dregg2.Circuit.Emit.NonRevocationRefine

namespace Dregg2.Circuit.Emit.NonRevocationRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   Table memLog mapLog)
open Dregg2.Circuit.Emit.NonRevocationEmit
open Dregg2.Circuit.Emit.NonRevocationRefine
open Dregg2.Crypto.NonMembership (Sorted Adjacent NonMember sorted_gap_excludes)

set_option autoImplicit false

/-- Constraint-membership tactic (twin of Rung 1's local `nr_mem`): every constraint we name is
literally in `nonRevocationDesc`. -/
local macro "nr_mem" : tactic =>
  `(tactic| (simp [nonRevocationDesc, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup]))

/-! ## §1 — MEASURING the gap (the half-field overshoot is exactly `2^26`). -/

/-- The single range lookup `RL ∈ [0, 2^30)` overshoots the honest positive window `[0,
HALF_P_MINUS_1]` by exactly `2^26` — the width of the negative window both models admit. -/
theorem window_width : (2 : ℤ) ^ ORDERING_BITS - 1 - HALF_P_MINUS_1 = 2 ^ 26 := by decide

/-- **The ℤ model is FAITHFUL to the field: it admits `DIFF_L` down to exactly `−2^26`.** From the
range lookup `RL < 2^30` and the binding `RL = HALF_P_MINUS_1 − DIFF_L`, `Satisfied2` forces only
`DIFF_L ≥ HALF_P_MINUS_1 − (2^30 − 1) = −2^26`. So the negative window `[−2^26, −1]` is genuinely
un-forced — this is a REAL circuit gap, not a modelling loss (`revocation.rs` reconstructs the SAME
`HALF_P_MINUS_1 − diff` from 30 bits, admitting `diff = p−1` as signed `−1`). -/
theorem satisfied_admits_negative_window {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range)) :
    (-(2 ^ 26) : ℤ) ≤ (envAt t 0).loc DIFF_L := by
  have hrl := (rangeLBind_body_zero_iff _).mp (gateZero0 hsat hlen rangeLBindBody (by nr_mem))
  have hub := (range0 hsat hRange hlen RL (by nr_mem)).2
  rw [hrl] at hub
  have hpow : (2 : ℤ) ^ ORDERING_BITS = 1073741824 := by decide
  rw [hpow] at hub
  simp only [HALF_P_MINUS_1] at hub
  have : ((2 : ℤ) ^ 26) = 67108864 := by decide
  omega

/-! ## §2 — THE NAMED CARRIER (the lower-gap range tooth) + the discharge. -/

/-- **`DiffLowerRangeSound t` — THE NAMED CARRIER (= the emit-fix).** The range argument certifies the
diff wires THEMSELVES lie in `[0, 2^30)` — the twin of `RangeTableSound` applied to `DIFF_L`/`DIFF_R`
directly, i.e. the lower-gap range lookup `nonRevocationDesc` is MISSING. NAMED, never a Lean axiom. -/
def DiffLowerRangeSound (t : VmTrace) : Prop :=
  (0 ≤ (envAt t 0).loc DIFF_L ∧ (envAt t 0).loc DIFF_L < 2 ^ ORDERING_BITS) ∧
  (0 ≤ (envAt t 0).loc DIFF_R ∧ (envAt t 0).loc DIFF_R < 2 ^ ORDERING_BITS)

/-- **`lowerRange_discharges_canon`** — the carrier discharges Rung 1's `FieldCanonicalDiffs` residual
(its `0 ≤` halves). Genuine, not laundering: `DiffLowerRangeSound` STRICTLY refines
`FieldCanonicalDiffs` (it additionally caps the diffs at `2^30`), and — proven in §4 —
`Satisfied2` + Rung 1's carriers do NOT imply it. -/
theorem lowerRange_discharges_canon {t : VmTrace} (h : DiffLowerRangeSound t) :
    FieldCanonicalDiffs t :=
  ⟨h.1.1, h.2.1⟩

/-- **`nonRevocation_rung2` — THE RUNG-2 NO-FORGERY DISCHARGE (conditional on the named emit-fix).**
A `Satisfied2` active-row-0 window, against the Poseidon2 chip carrier, the `RL`/`RR` range carrier,
AND the missing lower-gap range tooth `DiffLowerRangeSound`, with the committed sorted spine in which
the bracketing leaves are adjacent, forces the queried item to be a GENUINE non-member of the
committed set (NOT revoked) — `NonMember spine x`, welded to `sorted_gap_excludes`. WITHOUT
`FieldCanonicalDiffs` as a hypothesis: it is discharged by the named carrier. -/
theorem nonRevocation_rung2 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range))
    (hlower : DiffLowerRangeSound t)
    (spine : List ℤ)
    (hsorted : Sorted spine)
    (hadj : Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)) :
    NonMember spine ((envAt t 0).loc X) :=
  nonRevocation_nonmembership hlen hsat hChip hRange (lowerRange_discharges_canon hlower)
    spine hsorted hadj

#assert_axioms window_width
#assert_axioms satisfied_admits_negative_window
#assert_axioms lowerRange_discharges_canon
#assert_axioms nonRevocation_rung2

/-! ## §3 — the shared committed tree + honest / cheating traces.

A depth-2 tree over the adjacent bottom siblings `L = 100`, `R = 300` under sibling `sib = 7`, folding
to the committed root `hash [hash [100,300], 7]`, at consecutive positions `5, 6`. -/

/-- A concrete little-endian digit hash (base `10^6`): `[100,300] ↦ 100000300` (twin of Rung 1's). -/
private def demoHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) 0

/-- The shared Poseidon2 chip table: the two genuine node hashes of the committed tree. -/
private def demoTbl : List (List ℤ) :=
  [ chipRow demoHash [100, 300] (List.replicate 7 0)
  , chipRow demoHash [100000300, 7] (List.replicate 7 0) ]

/-- The shared chip table is genuinely SOUND (so `ChipTableSound` is realizable, not just assumed). -/
private theorem demoTbl_chipSound (tf : TableId → Table) (h : tf .poseidon2 = demoTbl) :
    ChipTableSound demoHash (tf .poseidon2) := by
  rw [h]
  intro r hr
  simp only [demoTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[100, 300], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[100000300, 7], List.replicate 7 0, by decide, by decide, rfl⟩

/-! ### §3a — the HONEST witness (`x = 200`, strictly bracketed, `diff = 99`). -/

private def hnRow : Assignment := fun c =>
  if c = X then 200
  else if c = LEAF_L then 100
  else if c = LEAF_R then 300
  else if c = LPOS then 5
  else if c = RPOS then 6
  else if c = DIFF_L then 99
  else if c = DIFF_R then 99
  else if c = RL then 1006632860
  else if c = RR then 1006632860
  else if c = PAR0 then 100000300
  else if c = CUR1 then 100000300
  else if c = SIB1 then 7
  else if c = PAR1 then 100000300000007
  else 0

private def hnPub : Assignment := fun k =>
  if k = ROOT_PI then 100000300000007 else if k = QUERIED_PI then 200 else 0

private def hnRangeTbl : List (List ℤ) := [[1006632860]]

private def hnTrace : VmTrace :=
  { rows := [hnRow, hnRow], pub := hnPub
    tf := fun tid => match tid with
      | .poseidon2 => demoTbl
      | .range => hnRangeTbl
      | _ => [] }

private theorem hn_sat :
    Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] hnTrace := by
  have hmemlog : memLog nonRevocationDesc hnTrace = [] := rfl
  have hmaplog : mapLog nonRevocationDesc hnTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hnTrace.rows.length = 2 from rfl] at hi
    simp only [nonRevocationDesc, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup] at hc
    interval_cases i
    · have hF : ((0 : Nat) == 0) = true := rfl
      have hLf : ((0 : Nat) + 1 == hnTrace.rows.length) = false := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hF, hLf] <;>
        decide
    · have hFf : ((1 : Nat) == 0) = false := rfl
      have hL : ((1 : Nat) + 1 == hnTrace.rows.length) = true := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hFf, hL] <;>
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

private theorem hn_chipSound : ChipTableSound demoHash (hnTrace.tf .poseidon2) :=
  demoTbl_chipSound _ rfl

private theorem hn_rangeSound : RangeTableSound ORDERING_BITS (hnTrace.tf .range) := by
  intro r hr
  simp only [hnTrace, hnRangeTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl
  exact ⟨1006632860, rfl, by decide, by decide⟩

/-- The honest witness SATISFIES the named lower-gap carrier (`diff = 99 ∈ [0, 2^30)`). -/
private theorem hn_lower : DiffLowerRangeSound hnTrace :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **NON-VACUITY (TRUE half) — the RUNG-2 discharge FIRES end-to-end.** Every hypothesis of
`nonRevocation_rung2` jointly holds on the concrete honest instance (inhabited `Satisfied2`,
realizable chip / range carriers, the named lower-gap carrier, a concrete sorted spine with `100`/`300`
adjacent), and the conclusion is the GENUINE non-membership `200 ∉ [100,300]` — WITHOUT any
`FieldCanonicalDiffs` hypothesis. Not a hollow green. -/
theorem honest_rung2_fires : NonMember ([100, 300] : List ℤ) 200 := by
  have hsorted : Sorted ([100, 300] : List ℤ) := by simp [Sorted, List.pairwise_cons]
  have hadj : Adjacent ([100, 300] : List ℤ)
      ((envAt hnTrace 0).loc LEAF_L) ((envAt hnTrace 0).loc LEAF_R) := ⟨[], [], rfl⟩
  exact nonRevocation_rung2 (by decide) hn_sat hn_chipSound hn_rangeSound hn_lower
    [100, 300] hsorted hadj

/-! ### §3b — THE LOAD-BEARING CHEAT (the model-found forgery): `x = L = 100`, `diff_left = −1`.

A revoked item forges freshness. The queried item is set EQUAL to the present left neighbor
(`x = LEAF_L = 100`), so `diff_left = x − L − 1 = −1`, a canonical felt `p−1` whose range-wire
`RL = HALF_P_MINUS_1 + 1 = 1006632960 < 2^30` decomposes into 30 bits (the negative window). Same
committed tree/root as the honest witness — only the queried item and the diff/range wires change. -/

private def chRow : Assignment := fun c =>
  if c = X then 100
  else if c = LEAF_L then 100
  else if c = LEAF_R then 300
  else if c = LPOS then 5
  else if c = RPOS then 6
  else if c = DIFF_L then -1
  else if c = DIFF_R then 199
  else if c = RL then 1006632960
  else if c = RR then 1006632760
  else if c = PAR0 then 100000300
  else if c = CUR1 then 100000300
  else if c = SIB1 then 7
  else if c = PAR1 then 100000300000007
  else 0

private def chPub : Assignment := fun k =>
  if k = ROOT_PI then 100000300000007 else if k = QUERIED_PI then 100 else 0

private def chRangeTbl : List (List ℤ) := [[1006632960], [1006632760]]

private def chTrace : VmTrace :=
  { rows := [chRow, chRow], pub := chPub
    tf := fun tid => match tid with
      | .poseidon2 => demoTbl
      | .range => chRangeTbl
      | _ => [] }

/-- **The forgery PROVABLY `Satisfied2`s the DEPLOYED descriptor.** With `x = L = 100`,
`diff_left = −1`, and the range-wire `RL = 1006632960 ∈ [0, 2^30)`, every constraint of
`nonRevocationDesc` holds on the active row 0 (and the vacuous/lookup legs on the padding row 1). The
`Satisfied2` hypothesis of Rung 1 is met by an item that is a genuine member. -/
theorem cheat_sat :
    Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] chTrace := by
  have hmemlog : memLog nonRevocationDesc chTrace = [] := rfl
  have hmaplog : mapLog nonRevocationDesc chTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show chTrace.rows.length = 2 from rfl] at hi
    simp only [nonRevocationDesc, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup] at hc
    interval_cases i
    · have hF : ((0 : Nat) == 0) = true := rfl
      have hLf : ((0 : Nat) + 1 == chTrace.rows.length) = false := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hF, hLf] <;>
        decide
    · have hFf : ((1 : Nat) == 0) = false := rfl
      have hL : ((1 : Nat) + 1 == chTrace.rows.length) = true := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hFf, hL] <;>
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

theorem cheat_chipSound : ChipTableSound demoHash (chTrace.tf .poseidon2) :=
  demoTbl_chipSound _ rfl

theorem cheat_rangeSound : RangeTableSound ORDERING_BITS (chTrace.tf .range) := by
  intro r hr
  simp only [chTrace, chRangeTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨1006632960, rfl, by decide, by decide⟩
  · exact ⟨1006632760, rfl, by decide, by decide⟩

/-- The cheat VIOLATES the named lower-gap carrier (`diff_left = −1 < 0`) — the exact tooth the
deployed descriptor lacks. -/
theorem cheat_violates_lower : ¬ DiffLowerRangeSound chTrace := by
  intro h; exact absurd h.1.1 (by decide)

/-- The cheat VIOLATES Rung 1's `FieldCanonicalDiffs` residual too (`0 ≤ DIFF_L` is `0 ≤ −1`). -/
theorem cheat_violates_canon : ¬ FieldCanonicalDiffs chTrace := by
  intro h; exact absurd h.1 (by decide)

/-- **THE ANCHOR IS LOAD-BEARING — `Satisfied2` + Rung 1's two carriers do NOT force non-membership.**
On the forgery: the descriptor `Satisfied2`s, both named carriers (`ChipTableSound`,
`RangeTableSound`) are realizable, the committed spine `[100,300]` is sorted with `100`/`300` adjacent
— yet the queried item `x = 100` is a genuine MEMBER (`¬ NonMember [100,300] 100`). So NO theorem
concluding `NonMember` from `Satisfied2` + those carriers alone can exist: the `DiffLowerRangeSound`
carrier (equivalently the `FieldCanonicalDiffs` residual, which the cheat violates) is a REAL filter,
not `True`. This is the revoked-item freshness forgery the `2^26` negative window admits. -/
theorem cheat_carriers_do_not_force_nonmembership :
    Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] chTrace
    ∧ ChipTableSound demoHash (chTrace.tf .poseidon2)
    ∧ RangeTableSound ORDERING_BITS (chTrace.tf .range)
    ∧ Sorted ([100, 300] : List ℤ)
    ∧ Adjacent ([100, 300] : List ℤ) ((envAt chTrace 0).loc LEAF_L) ((envAt chTrace 0).loc LEAF_R)
    ∧ (envAt chTrace 0).loc X ∈ ([100, 300] : List ℤ)
    ∧ ¬ NonMember ([100, 300] : List ℤ) ((envAt chTrace 0).loc X)
    ∧ ¬ FieldCanonicalDiffs chTrace := by
  refine ⟨cheat_sat, cheat_chipSound, cheat_rangeSound, ?_, ⟨[], [], rfl⟩, ?_, ?_, cheat_violates_canon⟩
  · simp [Sorted, List.pairwise_cons]
  · show (100 : ℤ) ∈ ([100, 300] : List ℤ); simp
  · rintro ⟨_, hni⟩
    exact hni (by show (100 : ℤ) ∈ ([100, 300] : List ℤ); simp)

#assert_axioms honest_rung2_fires
#assert_axioms cheat_sat
#assert_axioms cheat_violates_lower
#assert_axioms cheat_violates_canon
#assert_axioms cheat_carriers_do_not_force_nonmembership

end Dregg2.Circuit.Emit.NonRevocationRung2
