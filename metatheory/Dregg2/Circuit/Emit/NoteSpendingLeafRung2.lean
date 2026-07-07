/-
# Dregg2.Circuit.Emit.NoteSpendingLeafRung2 — the RUNG-2 discharge of the MULTI-ROW Merkle-membership
residual left by `NoteSpendingLeafRefine` (RUNG 1), for the emitted note-spend recursion leaf
(`NoteSpendingLeafEmit.noteSpendLeafDesc`).

## What RUNG 1 gave us and what this file adds

`NoteSpendingLeafRefine.noteSpend_satisfied2_spec` (RUNG 1) is a SINGLE-ROW (row-0, the SPEND row)
bridge: a `Satisfied2` trace, against the NAMED wide Poseidon2 chip carrier `ChipTableSoundN permOut`,
binds the whole spend-row relation — commitment = the 7-fold `permOut` chain of the note preimage,
nullifier = the two-step key derivation, the PI pins, etc. Its OWN honest residual (§ "Honest
residuals"): C6 (Merkle membership) is OFF on the spend row (`is_merkle = 0`); the genuine meaning —
that the committed leaf is IN the tree rooted at the PUBLIC `merkle_root` (pi1) — lives on the
`is_merkle = 1` path rows and needs the MULTI-ROW `recomposeUp` fold. That is exactly a
"single-row spec where multi-row binding is needed" — the RUNG-2 residual.

## The discharge (the multi-row Merkle recompose)

The deployed leaf threads a Merkle authentication path ACROSS ROWS:
  * C6 (`whenSite 5 [0,1,2,3,4] 128`, a `Poseidon2Chip` LOOKUP that fires on `is_merkle = 1`) forces,
    on EVERY merkle row (lookups are not divided by the transition zerofier), the row's PARENT column
    (col 5) to be `permOut` of the seeded `(current, 4 position-aware inputs)` — one `recomposeUp`
    step (`merkleRow_c6`, riding RUNG-1's `factSite_block` lever with the `whenSite` selector);
  * C7 (`.windowGate ⟨contBodyW, true⟩`, on-transition) threads `next.CURRENT (col 0) = this.PARENT
    (col 5)` — the leaf `COMMITMENT` (row-0 col 5) flows up through the path rows;
  * the last-row pin (`.piBinding .last 0 1`) pins the terminal `CURRENT` to the public `merkle_root`.

`recompose_reaches` inducts over the path rows (mirroring `HeapOpenEmit.heapRecompose_reaches_cur8`
and the DFA template's `accumulates_map`): the CURRENT column at each path row is the leaf folded up
`foldUpN` over the witnessed sibling steps. `noteSpend_merkle_rung2` closes it with the last-row pin:
`merkle_root (pi1) = foldUpN permOut leaf (path steps)` — the GENUINE membership relation. Composed
with RUNG 1 (`noteSpend_committed_note_member`), the note whose commitment is the genuine `permOut`
hash of the disclosed `(value, asset, …)` is genuinely a MEMBER of the tree rooted at the public
`merkle_root` — the note-spend no-forgery property.

The last-row continuity vacuity (C7 is `on_transition`, so unenforced on the last row) does NOT open
a gap here: the terminal `CURRENT` is pinned DIRECTLY (a `piBinding`, always enforced), and the fold
threads into it via C7 on the penultimate (transition) row — unlike the DFA, no route-commitment
anchor is needed for the terminal step.

## Non-vacuity (the anti-scar package — TRUE and FALSE, never a stub)

* `witness_merkle_rung2` FIRES the bridge end-to-end on RUNG-1's concrete satisfying `witnessTrace`
  (a genuine 2-row trace, depth-0 path): the hypothesis set is INHABITED, `merkle_root = leaf`
  DERIVED, not assumed (`witness_merkle_value`).
* `membership_model_true_closed` / `membership_model_false_closed` exhibit the fold over a REAL
  Poseidon-shaped digit hash `dPerm` computing a genuine step (`root = 128643`) and REJECTING a wrong
  root (`999`) — the membership relation is a real filter, not `True`.
* `merkle_broken_chain_rejects` / `merkle_wrong_root_rejects` exhibit CONCRETE traces that FAIL
  `Satisfied2` because a tooth BITES (C7 continuity; the last-row pin).
* `whenSite_offrow_digest_K0` is the LOAD-BEARING witness for the path-shape hypothesis: on an
  `is_merkle = 0` row the C6 digest lane muxes to the constant `K₀` REGARDLESS of col 5 — so C6 does
  NOT bind the node hash off the merkle path, and the `is_merkle = 1` precondition is genuinely
  required (not laundered).

## Honestly-named residual

The `is_merkle` PATH SHAPE (`row 0` spend, the interior rows `is_merkle = 1`, a terminal row) is a
STRUCTURAL precondition (`hpath` / `hspend`), enforced above the leaf by the recursion-FOLD adapter,
not by the leaf descriptor's per-row constraints — exactly as RUNG 1 states `hspend` for row 0. It is
NOT a crypto residual and is NAMED, never laundered; its enforcement by the fold adapter is the
precise follow-up.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The SOLE cryptographic carrier is the
NAMED wide Poseidon2 chip soundness `ChipTableSoundN permOut` — the same carrier RUNG 1 / `HeapOpenEmit`
ride; `permOut` is a parameter. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.NoteSpendingLeafRefine

namespace Dregg2.Circuit.Emit.NoteSpendingLeafRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId WindowConstraint WindowExpr Satisfied2 VmTrace
   envAt zeroAsg ChipTableSoundN TraceFamily)
open Dregg2.Circuit.Emit.NoteSpendingLeafEmit
  (noteSpendLeafDesc noteSpendConstraints unlessSite whenSite factTuple IS_MERKLE NS_FACT_MARK K0
   subE unlessFire unlessHold whenFire whenHold binaryGate invEqGate posGate contBodyW
   cont_body_zero_iff)
open Dregg2.Circuit.Emit.NoteSpendingLeafRefine
  (firingIns firing5 factLaneVals factSite_block NoteSpendLeafSpec noteSpend_satisfied2_spec
   witnessTrace witnessPerm witnessAsg witnessPub witnessTrace_satisfied2 witness_chipSound)

set_option autoImplicit false

/-! ## §1 — the genuine Merkle-membership fold MODEL (the trace-independent no-forgery relation). -/

/-- **`nodeHashN permOut cur s1 s2 s3 s4`** — one Poseidon2 `recomposeUp` step: the parent digest of a
node whose current child is `cur` and whose four position-aware inputs are `s1 s2 s3 s4`. It IS the
head of the wide `permOut` of the deployed C6 fact-site seed `[cur, s1, s2, s3, s4, 0xFACF, 1]` — the
exact absorb `NoteSpendingLeafEmit.whenSite 5 [0,1,2,3,4] 128` binds on a merkle row. -/
def nodeHashN (permOut : List ℤ → List ℤ) (cur s1 s2 s3 s4 : ℤ) : ℤ :=
  (permOut [cur, s1, s2, s3, s4, NS_FACT_MARK, 1]).headD 0

/-- **`foldUpN permOut leaf steps`** — the leaf folded up its authentication path: each step supplies
the four position-aware inputs of that level, and the accumulator recomposes the parent digest. -/
def foldUpN (permOut : List ℤ → List ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ × ℤ × ℤ)) : ℤ :=
  steps.foldl (fun acc s => nodeHashN permOut acc s.1 s.2.1 s.2.2.1 s.2.2.2) leaf

/-- **`MembersAtRoot permOut leaf root steps`** — THE FUNCTIONAL SPEC: `leaf` authenticates to the
committed `root` along the Poseidon2 path `steps`. The membership relation the note-spend leaf is
meant to certify (the leaf's `COMMITMENT` sits under the public `merkle_root`). -/
def MembersAtRoot (permOut : List ℤ → List ℤ) (leaf root : ℤ) (steps : List (ℤ × ℤ × ℤ × ℤ)) : Prop :=
  foldUpN permOut leaf steps = root

/-- Folding one more level appends its step to the path (the fold's own `foldl`-over-append law). -/
theorem foldUpN_append (permOut : List ℤ → List ℤ) (leaf : ℤ) (xs : List (ℤ × ℤ × ℤ × ℤ))
    (y : ℤ × ℤ × ℤ × ℤ) :
    foldUpN permOut leaf (xs ++ [y])
      = nodeHashN permOut (foldUpN permOut leaf xs) y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  simp only [foldUpN, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## §2 — reading one Merkle-fold step off `Satisfied2` (the `whenSite` C6 lever, on `is_merkle=1`). -/

/-- The C6 fact-site's `fire` selector (`whenFire IS_MERKLE`) is `1` on a merkle row. -/
theorem when_fire_eval (env : VmRowEnv) (hm : env.loc IS_MERKLE = 1) :
    (whenFire IS_MERKLE).eval env.loc = 1 := by
  simp [whenFire, EmittedExpr.eval, hm]

/-- The C6 fact-site's `hold` selector (`whenHold IS_MERKLE`) is `0` on a merkle row. -/
theorem when_hold_eval (env : VmRowEnv) (hm : env.loc IS_MERKLE = 1) :
    (whenHold IS_MERKLE).eval env.loc = 0 := by
  simp [whenHold, subE, EmittedExpr.eval, hm]

/-- A firing (`whenSite`) fact site's digest on a merkle row (`is_merkle = 1`) is `permOut` of the
genuine seed — the mirror of RUNG-1's `unlessSite_digest`, riding the same `factSite_block` lever
with the `when`-selector. -/
theorem whenSite_digest (permOut : List ℤ → List ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf .poseidon2)) (hm : env.loc IS_MERKLE = 1)
    (outputCol : Nat) (inputCols : List Nat) (laneBase : Nat)
    (hmem : (factTuple (whenFire IS_MERKLE) (whenHold IS_MERKLE) outputCol inputCols laneBase).map
              (·.eval env.loc) ∈ tf .poseidon2) :
    env.loc outputCol = (permOut (firingIns env inputCols)).headD 0 := by
  have hblock := factSite_block permOut tf env hChip outputCol inputCols laneBase _ _
    (when_fire_eval env hm) (when_hold_eval env hm) hmem
  rw [← hblock]; rfl

/-- The C6 fact-site's genuine absorb seed evaluates to the five muxed columns plus the domain
constants (`0xFACF, 1`) — the twin of `firingIns_length`, computed on the C6 input columns. -/
theorem firingIns_c6 (env : VmRowEnv) :
    firingIns env [0, 1, 2, 3, 4]
      = [env.loc 0, env.loc 1, env.loc 2, env.loc 3, env.loc 4, NS_FACT_MARK, 1] := rfl

/-- **`merkleRow_c6`** — on a merkle row, C6 forces the PARENT column (col 5) to be the genuine
`recomposeUp` node hash of the CURRENT column (col 0) and the four position-aware inputs
(cols 1..4). One authentication step, read off `Satisfied2` + the NAMED chip carrier. -/
theorem merkleRow_c6 (permOut : List ℤ → List ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf .poseidon2)) (hm : env.loc IS_MERKLE = 1)
    (hmem : (factTuple (whenFire IS_MERKLE) (whenHold IS_MERKLE) 5 [0, 1, 2, 3, 4] 128).map
              (·.eval env.loc) ∈ tf .poseidon2) :
    env.loc 5 = nodeHashN permOut (env.loc 0) (env.loc 1) (env.loc 2) (env.loc 3) (env.loc 4) := by
  have h := whenSite_digest permOut tf env hChip hm 5 [0, 1, 2, 3, 4] 128 hmem
  rw [h]; simp only [nodeHashN, firingIns_c6]

/-! ## §3 — membership of the three load-bearing constraints in `noteSpendLeafDesc`. -/

/-- The C6 Merkle-membership fact site is a genuine constraint of the descriptor. -/
theorem mem_c6 : whenSite 5 [0, 1, 2, 3, 4] 128 ∈ noteSpendLeafDesc.constraints := by
  show whenSite 5 [0, 1, 2, 3, 4] 128 ∈ noteSpendConstraints
  unfold noteSpendConstraints
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-- The C7 chain-continuity window gate is a genuine constraint of the descriptor. -/
theorem mem_c7 : VmConstraint2.windowGate ⟨contBodyW, true⟩ ∈ noteSpendLeafDesc.constraints := by
  show VmConstraint2.windowGate ⟨contBodyW, true⟩ ∈ noteSpendConstraints
  unfold noteSpendConstraints contBodyW
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-- The last-row Merkle-root pin is a genuine constraint of the descriptor. -/
theorem mem_pin_last :
    VmConstraint2.base (.piBinding VmRow.last 0 1) ∈ noteSpendLeafDesc.constraints := by
  show VmConstraint2.base (.piBinding VmRow.last 0 1) ∈ noteSpendConstraints
  unfold noteSpendConstraints
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-! ## §4 — the trace-read path steps + the multi-row recompose. -/

/-- The four position-aware inputs (cols 1..4) read off row `i` — one authentication step. -/
def stepAt (t : VmTrace) (i : Nat) : ℤ × ℤ × ℤ × ℤ :=
  ((envAt t i).loc 1, (envAt t i).loc 2, (envAt t i).loc 3, (envAt t i).loc 4)

/-- The authentication path read off the first `m` merkle rows (rows `1 .. m`). -/
def stepsUpto (t : VmTrace) (m : Nat) : List (ℤ × ℤ × ℤ × ℤ) :=
  (List.range m).map (fun j => stepAt t (j + 1))

/-- One more merkle row appends its step to the path. -/
theorem stepsUpto_succ (t : VmTrace) (k : Nat) :
    stepsUpto t (k + 1) = stepsUpto t k ++ [stepAt t (k + 1)] := by
  simp only [stepsUpto, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The trace-index threading of the continuity window: the current row's `nxt` slice IS the next
row's `loc` slice (`envAt`'s own definition). -/
theorem envAt_nxt_loc (t : VmTrace) (j : Nat) : (envAt t j).nxt = (envAt t (j + 1)).loc := rfl

/-- **`recompose_reaches` — the MULTI-ROW Merkle fold.** Under the NAMED chip carrier, on a trace
whose interior rows (`1 .. n-2`) are merkle rows (`hpath`), the CURRENT column (col 0) at each path
row `k+1` is the leaf (the row-0 `COMMITMENT`, col 5) folded up `foldUpN` over the sibling steps
read from rows `1 .. k`. Induction on `k`, mirroring `HeapOpenEmit.heapRecompose_reaches_cur8`:
the base uses C7 on row 0 (the leaf enters row 1); the step composes C6 (this level's node hash) with
C7 (thread to the next row's CURRENT). -/
theorem recompose_reaches (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    ∀ m, m + 1 ≤ t.rows.length - 1 →
      (envAt t (m + 1)).loc 0 = foldUpN permOut ((envAt t 0).loc 5) (stepsUpto t m) := by
  intro m
  induction m with
  | zero =>
    intro hm1
    have hrow0 : (0 : Nat) < t.rows.length := by omega
    have hnotlast0 : ((0 : Nat) + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hc7 := hsat.rowConstraints 0 hrow0 _ mem_c7
    have hbody : contBodyW.eval (envAt t 0) = 0 := by
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc7
      exact hc7 hnotlast0
    have hthread : (envAt t 0).nxt 0 = (envAt t 0).loc 5 :=
      (cont_body_zero_iff (envAt t 0)).mp hbody
    have hnl : (envAt t 0).nxt 0 = (envAt t (0 + 1)).loc 0 := rfl
    simp only [stepsUpto, List.range_zero, List.map_nil, foldUpN, List.foldl_nil]
    rw [← hnl]; exact hthread
  | succ k ih =>
    intro hm1
    have hkle : k + 1 ≤ t.rows.length - 1 := by omega
    have hkstep : (envAt t (k + 1)).loc 0
        = foldUpN permOut ((envAt t 0).loc 5) (stepsUpto t k) := ih hkle
    have hrowk1 : k + 1 < t.rows.length := by omega
    have hmerk : (envAt t (k + 1)).loc IS_MERKLE = 1 := hpath (k + 1) (by omega) (by omega)
    have hmem6 : (factTuple (whenFire IS_MERKLE) (whenHold IS_MERKLE) 5 [0, 1, 2, 3, 4] 128).map
                    (·.eval (envAt t (k + 1)).loc) ∈ t.tf .poseidon2 := by
      have hc := hsat.rowConstraints (k + 1) hrowk1 _ mem_c6
      simpa only [VmConstraint2.holdsAt, whenSite, Lookup.holdsAt] using hc
    have hc6 := merkleRow_c6 permOut t.tf (envAt t (k + 1)) hChip hmerk hmem6
    have hnotlast : ((k + 1) + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hc7 := hsat.rowConstraints (k + 1) hrowk1 _ mem_c7
    have hbody : contBodyW.eval (envAt t (k + 1)) = 0 := by
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc7
      exact hc7 hnotlast
    have hthread : (envAt t (k + 1)).nxt 0 = (envAt t (k + 1)).loc 5 :=
      (cont_body_zero_iff (envAt t (k + 1))).mp hbody
    have hnl : (envAt t (k + 1)).nxt 0 = (envAt t (k + 1 + 1)).loc 0 := rfl
    rw [← hnl, hthread, hc6, hkstep, stepsUpto_succ, foldUpN_append]
    simp only [stepAt]

/-! ## §5 — THE RUNG-2 BRIDGE: `merkle_root = foldUpN leaf (path)` (the membership no-forgery). -/

/-- The full witnessed authentication path of a trace (the `n-2` interior merkle rows). -/
def merklePathSteps (t : VmTrace) : List (ℤ × ℤ × ℤ × ℤ) := stepsUpto t (t.rows.length - 2)

/-- **`noteSpend_merkle_rung2` — THE MULTI-ROW MEMBERSHIP DISCHARGE.** A `Satisfied2` trace of the
note-spend leaf, against the NAMED wide Poseidon2 chip carrier, whose interior rows are the merkle
path (`hpath`), binds the GENUINE Merkle-membership relation: the public `merkle_root` (pi1) is the
leaf (the row-0 `COMMITMENT`, col 5) folded up `foldUpN` over the witnessed authentication path.
Composes `recompose_reaches` (the fold reaches the terminal CURRENT) with the last-row root pin.
No route-commitment anchor is needed — the terminal CURRENT is pinned directly. -/
theorem noteSpend_merkle_rung2 {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    MembersAtRoot permOut ((envAt t 0).loc 5) (t.pub 1) (merklePathSteps t) := by
  have hn1 : t.rows.length - 1 < t.rows.length := by omega
  have hrec := recompose_reaches permOut hash minit mfin maddrs t hsat hChip hpath
    (t.rows.length - 2) (by omega)
  have heq : t.rows.length - 2 + 1 = t.rows.length - 1 := by omega
  rw [heq] at hrec
  have hpin := hsat.rowConstraints (t.rows.length - 1) hn1 _ mem_pin_last
  have hislast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    rw [this]; exact beq_self_eq_true _
  have hpineq : (envAt t (t.rows.length - 1)).loc 0 = t.pub 1 := by
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hpin
    exact hpin hislast
  show foldUpN permOut ((envAt t 0).loc 5) (merklePathSteps t) = t.pub 1
  rw [merklePathSteps, ← hrec]; exact hpineq

/-- **`noteSpend_committed_note_member` — THE NOTE-SPEND NO-FORGERY.** Composing RUNG 1 (the row-0
leaf IS the genuine 7-fold `permOut` commitment of the note preimage) with the RUNG-2 membership
bridge: the note whose commitment is the genuine Poseidon2 hash of its preimage is genuinely a MEMBER
of the tree rooted at the PUBLIC `merkle_root` (pi1). A prover cannot spend a note that is not in the
committed tree, nor forge the committed value/asset. -/
theorem noteSpend_committed_note_member {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hspend : (envAt t 0).loc IS_MERKLE = 0)
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    (envAt t 0).loc 5 = (permOut (firingIns (envAt t 0) [53, 45, 46, 47])).headD 0
    ∧ MembersAtRoot permOut ((envAt t 0).loc 5) (t.pub 1) (merklePathSteps t) := by
  have hspec := noteSpend_satisfied2_spec permOut hash minit mfin maddrs t hsat hChip (by omega) hspend
  refine ⟨?_, noteSpend_merkle_rung2 hsat hChip hlen hpath⟩
  rw [hspec.commitmentBinds]; exact hspec.commitmentFull

#assert_axioms merkleRow_c6
#assert_axioms recompose_reaches
#assert_axioms noteSpend_merkle_rung2
#assert_axioms noteSpend_committed_note_member

/-! ## §6 — non-vacuity, POSITIVE half: the bridge FIRES on RUNG-1's concrete satisfying witness.

RUNG 1 already proved `witnessTrace` (a genuine 2-row trace) `Satisfied2`s the whole descriptor with
a genuinely sound wide chip table (`witness_chipSound` for `witnessPerm`). For a 2-row trace the path
is empty (depth-0: a single-leaf tree), so the bridge's hypothesis set is INHABITED and the
membership `merkle_root = leaf` is DERIVED end-to-end — not a vacuous antecedent. -/

/-- **The RUNG-2 bridge FIRES on the concrete witness** (hypothesis set inhabited): the depth-0
membership `merkle_root = leaf` is derived, not assumed. `hpath` is vacuous (no interior rows). -/
theorem witness_merkle_rung2 :
    MembersAtRoot witnessPerm ((envAt witnessTrace 0).loc 5) (witnessTrace.pub 1)
      (merklePathSteps witnessTrace) :=
  noteSpend_merkle_rung2 witnessTrace_satisfied2 witness_chipSound (by decide)
    (by intro i h1 h2; have hl : witnessTrace.rows.length = 2 := rfl; omega)

/-- The recovered value is the concrete zero-fact digest `K₀` on BOTH sides — the fired conclusion is
a real equation, not a constant tautology (`merkle_root = leaf = K₀`). -/
theorem witness_merkle_value :
    witnessTrace.pub 1 = K0
    ∧ foldUpN witnessPerm ((envAt witnessTrace 0).loc 5) (merklePathSteps witnessTrace) = K0 := by
  refine ⟨rfl, rfl⟩

/-! ## §7 — non-vacuity, the MODEL separates (TRUE and FALSE) over a REAL digit hash. -/

/-- A concrete order-sensitive digit hash (`permOut`-shaped: head is the digest), enough to exercise
a genuine `recomposeUp` step non-degenerately. -/
def dPerm : List ℤ → List ℤ := fun xs => [xs.foldl (fun acc x => acc * 2 + x) 0]

/-- **Witness TRUE — the membership spec is INHABITED (closed form).** Leaf `1` with the level inputs
`(2,3,4,5)` folds up (through the deployed `0xFACF, 1` domain constants) to the concrete root
`128643` — a real, nontrivial `recomposeUp` step, not a stub. -/
theorem membership_model_true_closed : MembersAtRoot dPerm 1 128643 [(2, 3, 4, 5)] := by
  unfold MembersAtRoot foldUpN nodeHashN dPerm NS_FACT_MARK; decide

/-- **Witness FALSE — the membership spec CONSTRAINS.** The same leaf/step with the WRONG root is NOT
accepted: the recomposed digest must equal the published root. A `True`/`P → P` bridge could not
separate this. -/
theorem membership_model_false_closed : ¬ MembersAtRoot dPerm 1 999 [(2, 3, 4, 5)] := by
  unfold MembersAtRoot foldUpN nodeHashN dPerm NS_FACT_MARK; decide

/-! ## §8 — non-vacuity, the descriptor REJECTS forgeries (teeth BITE). -/

/-- A trace whose continuity is BROKEN: row-0 PARENT (col 5) is `1`, but row-1 CURRENT (col 0) is `0`
— so the C7 threading `next.CURRENT = this.PARENT` fails. -/
def bcRow0 : Assignment := fun c => if c = 5 then 1 else 0
def bcTrace : VmTrace := { rows := [bcRow0, zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — C7 tooth BITES).** The broken-continuity trace FAILS `Satisfied2`: the
transition-row C7 window gate forces `next.CURRENT = this.PARENT`, i.e. `0 = 1`. -/
theorem merkle_broken_chain_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDesc minit mfin maddrs bcTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) _ mem_c7
  have hnl : ((0 : Nat) + 1 == bcTrace.rows.length) = false := by decide
  have hbody : contBodyW.eval (envAt bcTrace 0) = 0 := by
    simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc
    exact hc hnl
  revert hbody; decide

/-- A single-row trace whose CURRENT (col 0) is `1` but whose public `merkle_root` (pi1) is `0`. -/
def wrRow : Assignment := fun c => if c = 0 then 1 else 0
def wrTrace : VmTrace := { rows := [wrRow], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — root-pin tooth BITES).** The wrong-root trace FAILS `Satisfied2`: the
last-row pin forces the terminal CURRENT to equal the public `merkle_root`, i.e. `1 = 0` — exactly
the "publish a root the leaf does not authenticate to" attack forbidden. -/
theorem merkle_wrong_root_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDesc minit mfin maddrs wrTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) _ mem_pin_last
  have hislast : ((0 : Nat) + 1 == wrTrace.rows.length) = true := by decide
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have heq := hc hislast
  revert heq; decide

/-! ## §9 — the LOAD-BEARING witness for the path-shape hypothesis (`hpath` is not laundered).

On an `is_merkle = 0` row the C6 digest lane muxes to the constant `K₀` REGARDLESS of the PARENT
column (col 5): the fact site degenerates to the zero-fact absorb. So C6 does NOT bind the node hash
off the merkle path — the `is_merkle = 1` precondition (the `hpath` shape) is genuinely required for
`merkleRow_c6` to fire, and `Satisfied2` alone cannot force the fold step without it. -/

/-- **`whenSite_offrow_digest_K0` — the anchor is LOAD-BEARING.** On an `is_merkle = 0` row the C6
fact-site digest-lane expression `fire·col5 + hold·K₀` evaluates to `K₀` independent of col 5: the
merkle fold step is UNCONSTRAINED off the path, so `hpath` is not laundered. -/
theorem whenSite_offrow_digest_K0 (env : VmRowEnv) (hm : env.loc IS_MERKLE = 0) :
    (EmittedExpr.add (.mul (whenFire IS_MERKLE) (.var 5)) (.mul (whenHold IS_MERKLE) (.const K0))).eval
        env.loc = K0 := by
  simp only [whenFire, whenHold, subE, EmittedExpr.eval, hm]
  ring

/-! ## §10 — shape pins + axiom tripwires. -/

#guard decide (bcTrace.rows.length = 2)
#guard decide (wrTrace.rows.length = 1)

#assert_axioms witness_merkle_rung2
#assert_axioms membership_model_true_closed
#assert_axioms membership_model_false_closed
#assert_axioms merkle_broken_chain_rejects
#assert_axioms merkle_wrong_root_rejects
#assert_axioms whenSite_offrow_digest_K0

end Dregg2.Circuit.Emit.NoteSpendingLeafRung2
