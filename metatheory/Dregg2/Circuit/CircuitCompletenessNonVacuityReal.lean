/-
# Dregg2.Circuit.CircuitCompletenessNonVacuityReal — completeness is NON-VACUOUS by a REAL transfer.

## What this closes (the upgrade over the empty-trace floor)

`CircuitCompletenessNonVacuity.satisfied2_transferV3_empty` inhabits `Satisfied2 hash transferV3 …`
with the EMPTY trace (`rows = []`). That refutes only "the type is `False`": every per-row gate is
`∀ i < 0`, vacuously true, so even a CONTRADICTORY gate set would admit the empty trace. The
meaningful question — are `transferV3`'s per-row gates JOINTLY SATISFIABLE by a trace that actually
COMPUTES a transfer — was witnessed only in Rust (the prove+verify roundtrips).

This module internalizes that satisfiability in Lean: it constructs a NON-EMPTY trace with ONE real
transfer row and proves `Satisfied2 hash transferV3 minit mfin maddrs realTransferTrace` for it.
`completeness_genuinely_nonvacuous` is the strictly-stronger statement: the gates are jointly
satisfiable by a NON-EMPTY real-row transfer (`∃ a trace with `rows ≠ []` satisfying `Satisfied2`).

## The concrete row (a genuine debit + nonce tick)

`transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)`. The Lean per-row
`transition` constraint is UNCONDITIONAL (`env.nxt (sbCol hi) = env.loc (saCol lo)` on EVERY row,
including the last — distinct from the Rust STARK transition polynomial which excludes the last row).
On a SINGLE-row trace `env.nxt = zeroAsg`, so the transition forces the after-state block to be
ALL-ZERO. A genuine transfer row must therefore land its after-state on zero. The honest, non-trivial
row that does this:

  * `s_transfer = 1`, `s_noop = 0` (a real transfer row, not a pad);
  * BEFORE: `bal_lo = 10`, `nonce = -1`, all other state limbs `0`;
  * AFTER: every state limb `0` (so the single unconditional transition `0 = after[i]` holds);
  * params: `amount = 10`, `direction = 1` (an OUTGOING transfer — a debit).

Then the transfer arithmetic is GENUINELY exercised, not zeroed away:
  * `gBalLo`: `after.bal_lo (0) = before.bal_lo (10) + amount (10)·(1 - 2·dir (1)) = 10 + 10·(-1) = 0` ✓
    — a real debit of `10`, balance `10 → 0`;
  * `gNonce` (active, `s_noop = 0`): `after.nonce (0) = before.nonce (-1) + 1` ✓ — a real nonce tick;
  * `gDirBool`: `dir (1)·(dir - 1) = 0` ✓;
  * `gBalHi`/`gCapPass`/`gResPass`/the 8 `gFieldPass`: `0 = 0` (frame frozen at zero) ✓.

(`nonce` is unconstrained by any range tooth — only the two after-balance limbs are range-checked, and
both are `0 ∈ [0, 2^30)`. A `-1` starting nonce is unusual but it is a genuine ℤ transfer move; the
SINGLE-row unconditional-transition obstruction makes a `0 → 1` natural-nonce single-row trace
unsatisfiable, see the report. The point is that the gate SET is jointly satisfied by a real,
non-zero-amount debit.)

## The auxiliary tables (lookups by literal membership; NO chip-soundness needed)

`Satisfied2`'s lookup leg is `Lookup.holdsAt tf env l := l.tuple.map (·.eval env.loc) ∈ tf l.table` —
PURE membership; it does NOT require `ChipTableSound`. So the Poseidon2 chip table and the range table
are constructed AS the list of the row's own evaluated lookup tuples (`tfReal`): every lookup hits its
own tuple by `List.mem_filterMap`. (The chip-soundness `out == permOut(ins)` is the SEPARATE soundness
direction; the completeness/satisfiability direction only needs the table to CONTAIN the looked-up
rows, which the honest prover's chip table does.) The memory / map-ops legs collapse exactly as in the
empty case: `graduateV1` emits no mem/map ops, so `memLog`/`mapLog` are empty and `tf .memory = []`,
`tf .mapOps = []` (the `filterMap` skips them — no `.memory`/`.mapOps` lookup exists), against the
empty boundary `maddrs = []`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The `Satisfied2` inhabitant is
CONSTRUCTED, not carried. No `sorry`, no `native_decide` substituting for a real discharge, no
`:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompletenessNonVacuity

namespace Dregg2.Circuit.CircuitCompletenessNonVacuityReal

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — the generic lookup-table-faithfulness machinery.

`Satisfied2`'s `rowConstraints` quantifies the per-row constraints over the whole trace; the lookup
constraints want their evaluated tuple to be a row of the named auxiliary table. We BUILD the table
as exactly the row's own evaluated lookup tuples, so membership is `List.mem_filterMap`. -/

/-- The lookup carried by a v2 constraint, if any. -/
def asLookup : VmConstraint2 → Option Lookup
  | .lookup l => some l
  | _ => none

/-- The auxiliary table for `tbl` built from the descriptor's lookups evaluated on the row `a`: the
list of `l.tuple.map (·.eval a)` over every lookup `l` of the descriptor with `l.table = tbl`. -/
def tfOf (d : EffectVmDescriptor2) (a : Assignment) : TraceFamily := fun tbl =>
  d.constraints.filterMap fun c =>
    match asLookup c with
    | some l => if l.table = tbl then some (l.tuple.map (·.eval a)) else none
    | none => none

/-- **Every lookup of the descriptor holds against `tfOf d a`** (membership by construction). For a
lookup constraint `.lookup l ∈ d.constraints`, the evaluated tuple `l.tuple.map (·.eval a)` is the
`filterMap` image of that very constraint, so it is a member of `tfOf d a l.table`. -/
theorem lookup_holdsAt_tfOf (d : EffectVmDescriptor2) (a : Assignment)
    (env : VmRowEnv) (henv : env.loc = a)
    (l : Lookup) (hl : VmConstraint2.lookup l ∈ d.constraints) :
    l.holdsAt (tfOf d a) env := by
  -- `Lookup.holdsAt` is exactly: the evaluated tuple is a row of the named table.
  show l.tuple.map (·.eval env.loc) ∈ tfOf d a l.table
  rw [henv, tfOf, List.mem_filterMap]
  exact ⟨.lookup l, hl, by simp [asLookup]⟩

/-- The TWO-ROW auxiliary table: the union of each row's evaluated lookup tuples. A 2-row real trace
needs BOTH rows' lookups to hit, so the table carries both rows' tuples (the deployed prover's auxiliary
table likewise spans every row). -/
def tfOf2 (d : EffectVmDescriptor2) (a b : Assignment) : TraceFamily :=
  fun tbl => tfOf d a tbl ++ tfOf d b tbl

/-- **A lookup holds against the union table from EITHER row.** For `.lookup l ∈ d.constraints` and an
env whose `loc` is one of the two rows, the evaluated tuple is in that row's `tfOf` summand, hence in the
union. (`henv` selects the summand; `List.mem_append` injects it.) -/
theorem lookup_holdsAt_tfOf2_left (d : EffectVmDescriptor2) (a b : Assignment)
    (env : VmRowEnv) (henv : env.loc = a)
    (l : Lookup) (hl : VmConstraint2.lookup l ∈ d.constraints) :
    l.holdsAt (tfOf2 d a b) env := by
  show l.tuple.map (·.eval env.loc) ∈ tfOf2 d a b l.table
  refine List.mem_append.mpr (Or.inl ?_)
  rw [henv, tfOf, List.mem_filterMap]
  exact ⟨.lookup l, hl, by simp [asLookup]⟩

theorem lookup_holdsAt_tfOf2_right (d : EffectVmDescriptor2) (a b : Assignment)
    (env : VmRowEnv) (henv : env.loc = b)
    (l : Lookup) (hl : VmConstraint2.lookup l ∈ d.constraints) :
    l.holdsAt (tfOf2 d a b) env := by
  show l.tuple.map (·.eval env.loc) ∈ tfOf2 d a b l.table
  refine List.mem_append.mpr (Or.inr ?_)
  rw [henv, tfOf, List.mem_filterMap]
  exact ⟨.lookup l, hl, by simp [asLookup]⟩

/-! ## §2 — the concrete REAL transfer row + trace.

A single transfer row, columns set to the genuine debit values; everything unmentioned is `0`. The
rotated welded limbs `r0 ↔ bal_lo` (col 188) and `r1 ↔ nonce` (col 189) carry the BEFORE-state
balance/nonce (so the `weldsAt` `colEq` ties hold); the after block and all other rotated/caveat
limbs are `0`. -/

/-- The concrete real transfer row (`Assignment`): `s_transfer = 1`, before-`bal_lo = 10`,
before-`nonce = -1`, `amount = 10`, `direction = 1`; after-state and all rotated limbs `0`, except the
two welded BEFORE limbs `r0`(col 188)`= bal_lo = 10` and `r1`(col 189)`= nonce = -1`. -/
def realRow : Assignment := fun v =>
  if v = sel.TRANSFER then 1                    -- col 1
  else if v = sbCol state.BALANCE_LO then 10    -- col 54
  else if v = sbCol state.NONCE then -1         -- col 56
  else if v = prmCol param.AMOUNT then 10       -- col 68
  else if v = prmCol param.DIRECTION then 1     -- col 69
  else if v = 188 then 10                        -- rotated BEFORE r0 (welded to bal_lo)
  else if v = 189 then -1                        -- rotated BEFORE r1 (welded to nonce)
  else 0

/-- The public inputs forced by the boundary/rotated PI pins. The v1 first-row pins
(`nonce → ACTOR_NONCE`, `bal_lo → INIT_BAL_LO`, `bal_hi → INIT_BAL_HI`, `state_commit → OLD_COMMIT`)
and the last-row pins (`state_commit → NEW_COMMIT`, `bal_lo/bal_hi → FINAL_*`) plus the four rotated
commit pins — all read columns that are `0` on `realRow` except `ACTOR_NONCE (= before nonce = -1)`
and `INIT_BAL_LO (= before bal_lo = 10)`. -/
def realPub : Assignment := fun k =>
  if k = pi.ACTOR_NONCE then -1     -- = realRow (sbCol NONCE)
  else if k = pi.INIT_BAL_LO then 10 -- = realRow (sbCol BALANCE_LO)
  else 0

/-- The WRAP/PAD last row: the zero assignment. Under the deployed `when_transition()` denotation the
per-row gates are vacuous on the last row, so the wrap row carries only the boundary-LAST pins (all of
which read columns that are `0` here, matching `realPub = 0` there). The real transfer row therefore
rides the ACTIVE (first) row, where the gates GENUINELY bite. -/
def lastRow : Assignment := zeroAsg

/-- The TWO-ROW REAL transfer trace: the genuine transfer row `realRow` (the ACTIVE/first row, where the
per-row gates fire) followed by the zero wrap row `lastRow` (the last row, where gates are vacuous and
the boundary-last pins read 0). The auxiliary table is the union of both rows' evaluated lookup tuples
(`tfOf2`), so every chip / range lookup hits on whichever row carries it. This is the HONEST shape: a
single-row trace would make `realRow` itself the last row, where the new `holdsVm` makes every gate
vacuous — so the witness would not actually exercise the gates. The active first row does. -/
def realTransferTrace : VmTrace where
  rows := [realRow, lastRow]
  pub  := realPub
  tf   := tfOf2 transferV3 realRow lastRow

@[simp] theorem realTransferTrace_rows : realTransferTrace.rows = [realRow, lastRow] := rfl
@[simp] theorem realTransferTrace_rows_ne : realTransferTrace.rows ≠ [] := by simp

/-- The ACTIVE (first) row window: `loc = realRow`, `nxt = lastRow = zeroAsg`, `pub = realPub`,
`isFirst = true`, `isLast = false` (two rows, so row 0 is not last). The gates GENUINELY bite here. -/
theorem envAt_realTransferTrace_zero :
    envAt realTransferTrace 0 = { loc := realRow, nxt := zeroAsg, pub := realPub } := by
  simp [envAt, realTransferTrace, lastRow, List.getD]

/-- The WRAP (last) row window: `loc = lastRow = zeroAsg`, `nxt = zeroAsg`, `pub = realPub`,
`isFirst = false`, `isLast = true`. The per-row gates are vacuous here. -/
theorem envAt_realTransferTrace_one :
    envAt realTransferTrace 1 = { loc := zeroAsg, nxt := zeroAsg, pub := realPub } := by
  simp [envAt, realTransferTrace, lastRow, List.getD]

/-! ## §3 — the named column reads of `realRow` (the `if`-cascade resolved). -/

/-- The named-column values of `realRow`, as a normal form. All state offsets are concrete naturals;
the cascade resolves to the explicit value. -/
theorem realRow_vals :
    realRow sel.TRANSFER = 1
    ∧ realRow sel.NOOP = 0
    ∧ realRow (sbCol state.BALANCE_LO) = 10
    ∧ realRow (sbCol state.NONCE) = -1
    ∧ realRow (sbCol state.BALANCE_HI) = 0
    ∧ realRow (sbCol state.CAP_ROOT) = 0
    ∧ realRow (sbCol state.RESERVED) = 0
    ∧ realRow (prmCol param.AMOUNT) = 10
    ∧ realRow (prmCol param.DIRECTION) = 1
    ∧ realRow (saCol state.BALANCE_LO) = 0
    ∧ realRow (saCol state.NONCE) = 0
    ∧ realRow (saCol state.BALANCE_HI) = 0
    ∧ realRow (saCol state.CAP_ROOT) = 0
    ∧ realRow (saCol state.RESERVED) = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [realRow, sel.TRANSFER, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.BALANCE_HI, state.NONCE, state.CAP_ROOT, state.RESERVED, param.AMOUNT,
      param.DIRECTION] <;> norm_num

/-! ## §4 — `realRow` is a transfer row realizing the transfer intent. -/

/-- The row environment used throughout (the single window of `realTransferTrace`). -/
def envReal : VmRowEnv := { loc := realRow, nxt := zeroAsg, pub := realPub }

theorem isTransferRow_envReal : IsTransferRow envReal := by
  obtain ⟨ht, hn, _⟩ := realRow_vals
  exact ⟨ht, hn⟩

/-- `realRow` realizes `TransferRowIntent`: bal_lo `10 → 0 = 10 + 10·(1 - 2·1)`, hi/frame fixed at
`0`, nonce `-1 → 0`. A GENUINE debit of `10` with a real nonce tick. -/
theorem transferRowIntent_envReal : TransferRowIntent envReal := by
  obtain ⟨_, _, hblo, hbn, hbhi, hbcap, hbres, ham, hdir, halo, han, hahi, hacap, hares⟩ := realRow_vals
  unfold TransferRowIntent
  simp only [envReal]
  refine ⟨Or.inr hdir, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [halo, hblo, ham, hdir]; ring
  · rw [hahi, hbhi]
  · rw [han, hbn]; ring
  · rw [hacap, hbcap]
  · rw [hares, hbres]
  · intro i hi
    -- both after-field (saCol 3+i) and before-field (sbCol 3+i) miss every named column ⇒ both 0.
    show realRow (saCol (state.FIELD_BASE + i)) = realRow (sbCol (state.FIELD_BASE + i))
    have ha : realRow (saCol (state.FIELD_BASE + i)) = 0 := by
      simp only [realRow, sel.TRANSFER, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
        PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
        state.FIELD_BASE, param.AMOUNT, param.DIRECTION]
      have e1 : ¬ (76 + (3 + i) = 1) := by omega
      have e2 : ¬ (76 + (3 + i) = 54) := by omega
      have e3 : ¬ (76 + (3 + i) = 56) := by omega
      have e4 : ¬ (76 + (3 + i) = 68) := by omega
      have e5 : ¬ (76 + (3 + i) = 69) := by omega
      have e6 : ¬ (76 + (3 + i) = 188) := by omega
      have e7 : ¬ (76 + (3 + i) = 189) := by omega
      simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6, if_neg e7]
    have hb : realRow (sbCol (state.FIELD_BASE + i)) = 0 := by
      simp only [realRow, sel.TRANSFER, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
        PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
        state.FIELD_BASE, param.AMOUNT, param.DIRECTION]
      have e1 : ¬ (54 + (3 + i) = 1) := by omega
      have e2 : ¬ (54 + (3 + i) = 54) := by omega
      have e3 : ¬ (54 + (3 + i) = 56) := by omega
      have e4 : ¬ (54 + (3 + i) = 68) := by omega
      have e5 : ¬ (54 + (3 + i) = 69) := by omega
      have e6 : ¬ (54 + (3 + i) = 188) := by omega
      have e7 : ¬ (54 + (3 + i) = 189) := by omega
      simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6, if_neg e7]
    rw [ha, hb]

/-! ## §5 — `realRow` is `0` off the seven named columns (the bulk evaluator). -/

/-- Off the seven named columns (`1, 54, 56, 68, 69, 188, 189`), `realRow` is `0`. -/
theorem realRow_zero_of {v : Nat} (h1 : v ≠ 1) (h54 : v ≠ 54) (h56 : v ≠ 56)
    (h68 : v ≠ 68) (h69 : v ≠ 69) (h188 : v ≠ 188) (h189 : v ≠ 189) : realRow v = 0 := by
  simp only [realRow, sel.TRANSFER, sbCol, prmCol, STATE_BEFORE_BASE, PARAM_BASE, NUM_EFFECTS,
    STATE_SIZE, state.BALANCE_LO, state.NONCE, param.AMOUNT, param.DIRECTION]
  rw [if_neg h1, if_neg h54, if_neg h56, if_neg h68, if_neg h69, if_neg h188, if_neg h189]

/-! ## §6 — the base constraints of the rotated frozen-authority transfer descriptor all hold. -/

/-- **Every base (v1 + rotation) constraint of `rotateV3FrozenAuthority transferVmDescriptor` holds on
`envReal` (both boundary flags set).** Group by group: the transfer gates (`transferVm_faithful` ←
`transferRowIntent_envReal`); the transition continuity (`nxt = 0 = after-state`); the v1 boundary PI
pins (forced columns equal `realPub`); the selector gate (`s_transfer = 1`); the welds (`r0 = bal_lo`,
`r1 = nonce`, every other welded pair `0 = 0`); the four rotated PI pins (`0 = realPub = 0`); the six
frozen-authority continuity welds (`0 = 0`). -/
theorem base_constraints_hold :
    ∀ c ∈ (rotateV3FrozenAuthority transferVmDescriptor).constraints,
      c.holdsVm envReal true false := by
  -- the transfer gates hold (faithfulness) on the ACTIVE row (`isLast = false`); `.gate.holdsVm`
  -- ignores `isFirst`, so the `false false` faithfulness witness transports to `true false`.
  have hgates : ∀ c ∈ transferRowGates, c.holdsVm envReal true false := by
    have h := (transferVm_faithful envReal isTransferRow_envReal).mpr transferRowIntent_envReal
    intro c hc
    have := h c hc
    unfold transferRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  -- `realRow C = V` for the named first-row pin columns; `realPub K = V` likewise.
  obtain ⟨ht, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := realRow_vals
  have hrowNonce : realRow (sbCol state.NONCE) = -1 := realRow_vals.2.2.2.1
  have hrowBalLo : realRow (sbCol state.BALANCE_LO) = 10 := realRow_vals.2.2.1
  have hpubNonce : realPub pi.ACTOR_NONCE = -1 := rfl
  have hpubBalLo : realPub pi.INIT_BAL_LO = 10 := rfl
  rw [rotateV3FrozenAuthority_constraints]
  intro c hc
  rw [List.mem_append] at hc
  rcases hc with hrot | hfrozen
  · simp only [rotateV3, show transferVmDescriptor.constraints
          = transferRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
            ++ selectorGates sel.TRANSFER from rfl, List.mem_append] at hrot
    rcases hrot with (((((hg | htr) | hbf) | hbl) | hsel) | ((hwb | hwa) | hpins))
    · exact hgates c hg
    · -- transition i i : `0 = realRow (saCol i)` and `saCol i ∈ [76, 89]` ⇒ off the named cols.
      unfold transitionAll at htr
      simp only [List.mem_map, List.mem_range] at htr
      obtain ⟨i, hi, rfl⟩ := htr
      have hi' : i < 14 := by simpa [STATE_SIZE] using hi
      show envReal.nxt (sbCol i) = envReal.loc (saCol i)
      show (0 : ℤ) = realRow (saCol i)
      have : realRow (saCol i) = 0 := by
        apply realRow_zero_of <;>
          · simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
              STATE_SIZE, NUM_PARAMS]; omega
      rw [this]
    · -- boundaryFirstPins.
      unfold boundaryFirstPins at hbf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbf
      rcases hbf with rfl | rfl | rfl | rfl <;>
        · refine fun _ => ?_
          simp only [envReal]
          first
          | rw [hrowNonce, hpubNonce]
          | rw [hrowBalLo, hpubBalLo]
          | (rw [realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
               (by decide) (by decide)]; rfl)
    · -- boundaryLastPins (all read 0 columns; realPub = 0 there).
      unfold boundaryLastPins at hbl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbl
      rcases hbl with rfl | rfl | rfl <;>
        · refine fun _ => ?_
          simp only [envReal]
          rw [realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; rfl
    · -- selectorGates sel.TRANSFER.
      unfold selectorGates at hsel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsel
      rw [hsel]
      exact selectorGate_holds_of_active sel.TRANSFER envReal true false ht
    · -- before-block welds: r0(188)=bal_lo(54)=10, r1(189)=nonce(56)=-1, else 0 = 0.
      unfold weldsAt at hwb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwb
      -- r0(188)=bal_lo(54)=10, r1(189)=nonce(56)=-1, and every other welded pair `0 = 0` — all
      -- reduce by computation (`realRow` evaluates each column to its literal).
      rcases hwb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [colEq_holds_iff _ _ _ _ _ rfl]; rfl
    · -- after-block welds: base 238, all 0 = 0.
      unfold weldsAt at hwa
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwa
      rcases hwa with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [colEq_holds_iff _ _ _ _ _ rfl]
          simp only [envReal]
          rw [realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide),
            realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
    · -- rotPins (all read 0 columns; realPub = 0 there).
      unfold rotPins at hpins
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpins
      rcases hpins with rfl | rfl | rfl | rfl <;>
        · refine fun _ => ?_
          simp only [envReal]
          rw [realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; rfl
  · -- the 6 frozen-authority colEqs: before vs after, all 0 = 0.
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfrozen
    rcases hfrozen with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [colEq_holds_iff _ _ _ _ _ rfl]
        simp only [envReal]
        rw [realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide),
          realRow_zero_of (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]

/-! ## §7 — the per-row constraint discharge for `transferV3` (base ∨ lookup).

`transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)`, so its constraints split
into `.base c` (re-anchored v1+rotation constraints) and `.lookup l` (the chip / range lookups). The
base ones hold by `base_constraints_hold`; the lookups hold by `lookup_holdsAt_tfOf` against the
constructed table. -/

theorem row0_constraints_hold (hash : List ℤ → ℤ) :
    ∀ c ∈ transferV3.constraints,
      c.holdsAt hash realTransferTrace.tf (envAt realTransferTrace 0) (0 == 0) (0 + 1 == 2) := by
  intro c hc
  rw [envAt_realTransferTrace_zero]
  show c.holdsAt hash (tfOf2 transferV3 realRow lastRow) envReal true false
  -- transferV3.constraints = (d'.constraints.map .base) ++ chipLookups ++ rangeLookups.
  rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl] at hc ⊢
  -- keep the original membership for the lookup cases; destructure a COPY for the shape.
  have hc' := hc
  rw [graduateV1] at hc'
  simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc'
  rcases hc' with (⟨c₀, hc₀, rfl⟩ | ⟨i, s, hs, rfl⟩) | ⟨r, hr, rfl⟩
  · -- a re-anchored base constraint — discharged on the ACTIVE row (`true false`).
    show c₀.holdsVm envReal true false
    exact base_constraints_hold c₀ hc₀
  · -- a chip lookup: `.lookup l` `holdsAt` is defeq `l.holdsAt`; hits the `realRow` summand of the union.
    exact lookup_holdsAt_tfOf2_left (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor))
      realRow lastRow envReal rfl _ hc
  · -- a range lookup: same.
    exact lookup_holdsAt_tfOf2_left (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor))
      realRow lastRow envReal rfl _ hc

/-- **`row1_constraints_hold` — the WRAP (last) row satisfies every `transferV3` constraint.** On the
last row (`isLast = true`) the per-row `.gate`/`.transition` constraints are VACUOUS (the deployed
`when_transition()`); the boundary-LAST `.piBinding` pins read columns that are `0` on the zero wrap row,
matching `realPub = 0` there; and the chip / range lookups hit the `lastRow` summand of the union table
(built from the zero row's own evaluated tuples). -/
theorem row1_constraints_hold (hash : List ℤ → ℤ) :
    ∀ c ∈ transferV3.constraints,
      c.holdsAt hash realTransferTrace.tf (envAt realTransferTrace 1) (1 == 0) (1 + 1 == 2) := by
  intro c hc
  rw [envAt_realTransferTrace_one]
  show c.holdsAt hash (tfOf2 transferV3 realRow lastRow)
    { loc := zeroAsg, nxt := zeroAsg, pub := realPub } false true
  rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl] at hc ⊢
  have hc' := hc
  rw [graduateV1] at hc'
  simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc'
  rcases hc' with (⟨c₀, hc₀, rfl⟩ | ⟨i, s, hs, rfl⟩) | ⟨r, hr, rfl⟩
  · -- a re-anchored base constraint, on the LAST row (`false true`).
    show c₀.holdsVm { loc := zeroAsg, nxt := zeroAsg, pub := realPub } false true
    -- on the last row every `.gate`/`.transition` is vacuous (`True`); the boundary-LAST pins read
    -- zero columns (= `realPub 0`); the first-row pins are vacuous. Discharge by constraint shape.
    rw [rotateV3FrozenAuthority_constraints] at hc₀
    rw [List.mem_append] at hc₀
    rcases hc₀ with hrot | hfrozen
    · simp only [rotateV3, show transferVmDescriptor.constraints
            = transferRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
              ++ selectorGates sel.TRANSFER from rfl, List.mem_append] at hrot
      rcases hrot with (((((hg | htr) | hbf) | hbl) | hsel) | ((hwb | hwa) | hpins))
      · -- transfer gates: `.gate`, vacuous on the last row.
        unfold transferRowGates gFieldPassAll at hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
          List.mem_range] at hg
        rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
          exact trivial
      · -- transition: vacuous on the last row.
        unfold transitionAll at htr
        simp only [List.mem_map, List.mem_range] at htr
        obtain ⟨i, hi, rfl⟩ := htr
        exact trivial
      · -- boundary-FIRST pins: vacuous (`isFirst = false`).
        unfold boundaryFirstPins at hbf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbf
        rcases hbf with rfl | rfl | rfl | rfl <;> exact fun h => absurd h (by decide)
      · -- boundary-LAST pins: read zero columns; `zeroAsg col = 0 = realPub k`.
        unfold boundaryLastPins at hbl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbl
        rcases hbl with rfl | rfl | rfl <;>
          · refine fun _ => ?_
            rfl
      · -- selector gate: `.gate`, vacuous on the last row.
        unfold selectorGates at hsel
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsel
        rw [hsel]; exact trivial
      · -- before-block welds: `.gate` (`colEq`), vacuous on the last row.
        unfold weldsAt at hwb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwb
        rcases hwb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact trivial
      · -- after-block welds: same.
        unfold weldsAt at hwa
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwa
        rcases hwa with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact trivial
      · -- rotPins (`.piBinding .last`): read zero columns; `zeroAsg col = 0 = realPub k`.
        unfold rotPins at hpins
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpins
        rcases hpins with rfl | rfl | rfl | rfl <;>
          · refine fun _ => ?_
            rfl
    · -- the 6 frozen-authority colEqs: `.gate`, vacuous on the last row.
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfrozen
      rcases hfrozen with rfl | rfl | rfl | rfl | rfl | rfl <;> exact trivial
  · -- a chip lookup: hits the `lastRow` (zero-row) summand of the union table.
    exact lookup_holdsAt_tfOf2_right (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor))
      realRow lastRow { loc := zeroAsg, nxt := zeroAsg, pub := realPub } rfl _ hc
  · -- a range lookup: same.
    exact lookup_holdsAt_tfOf2_right (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor))
      realRow lastRow { loc := zeroAsg, nxt := zeroAsg, pub := realPub } rfl _ hc

/-! ## §8 — the full `Satisfied2` for the NON-EMPTY real transfer trace. -/

/-- **`satisfied2_transferV3_real` — the CONCRETE non-empty `Satisfied2` inhabitant.** For ANY `hash`,
`minit`, `mfin`, the NON-EMPTY single-real-transfer-row trace `realTransferTrace` SATISFIES the live
`transferV3` descriptor against the empty declared address list. The per-row leg is the genuine
discharge `row0_constraints_hold` (the transfer arithmetic / nonce / direction / frame gates, the
transition, the boundary/rotated PI pins, the welds, the frozen-authority continuity, AND the chip /
range lookups — all on the single real row); the hash-site / range legs are vacuous (`graduateV1`
emits no legacy `hashSites`/`ranges`); the memory legs collapse to the empty log/boundary (`graduateV1`
emits no mem/map ops). -/
theorem satisfied2_transferV3_real (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash transferV3 minit mfin [] realTransferTrace where
  rowConstraints := by
    intro i hi c hc
    -- the trace has TWO rows: the ACTIVE real transfer row (0) and the WRAP row (1).
    have hlen : realTransferTrace.rows.length = 2 := by simp [realTransferTrace_rows]
    rw [hlen] at hi ⊢
    interval_cases i
    · exact row0_constraints_hold hash c hc
    · exact row1_constraints_hold hash c hc
  rowHashes := by
    intro i hi
    -- transferV3.hashSites = [] (graduateV1), so siteHoldsAll is `True`.
    show siteHoldsAll hash _ transferV3.hashSites
    rw [show transferV3.hashSites = [] from rfl]
    trivial
  rowRanges := by
    intro i hi r hr
    -- transferV3.ranges = [] (graduateV1).
    rw [show transferV3.ranges = [] from rfl] at hr
    simp at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    -- memLog (graduateV1 …) = [] ⇒ no ops.
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1] at hop
    simp at hop
  memDisciplined := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    trivial
  memBalanced := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  memTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    -- t.tf .memory = [] (the tfOf filterMap skips: no `.memory`-tabled lookup exists).
    show tfOf (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)) realRow .memory
        = ([] : List MemTraceOp).map opRow
    rw [List.map_nil]
    rw [tfOf, List.filterMap_eq_nil_iff]
    intro c hc
    -- every graduated constraint is a `.base` or a `.lookup` of a CHIP / RANGE table (never .memory).
    rcases constraints_graduateV1_shapes _ c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
    · rfl
    · -- a `.lookup l`; its table is `.poseidon2` or `.range`, never `.memory`.
      show (if l.table = TableId.memory then _ else none) = none
      rw [if_neg]
      -- l is a chip (`.poseidon2`) or range (`.range`) lookup; neither is `.memory`.
      have : l.table = TableId.poseidon2 ∨ l.table = TableId.range := by
        rw [graduateV1] at hc
        simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc
        rcases hc with (⟨c₀, _, hc1⟩ | ⟨i, _, hc1⟩) | ⟨r, _, hc1⟩
        · exact absurd hc1 (by simp)
        · left; injection hc1 with hc1; rw [← hc1]; rfl
        · right; injection hc1 with hc1; rw [← hc1]; rfl
      rcases this with h | h <;> rw [h] <;> decide
  mapTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      mapLog_graduateV1]
    show tfOf (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)) realRow .mapOps = []
    rw [tfOf, List.filterMap_eq_nil_iff]
    intro c hc
    rcases constraints_graduateV1_shapes _ c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
    · rfl
    · show (if l.table = TableId.mapOps then _ else none) = none
      rw [if_neg]
      have : l.table = TableId.poseidon2 ∨ l.table = TableId.range := by
        rw [graduateV1] at hc
        simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc
        rcases hc with (⟨c₀, _, hc1⟩ | ⟨i, _, hc1⟩) | ⟨r, _, hc1⟩
        · exact absurd hc1 (by simp)
        · left; injection hc1 with hc1; rw [← hc1]; rfl
        · right; injection hc1 with hc1; rw [← hc1]; rfl
      rcases this with h | h <;> rw [h] <;> decide

/-! ## §9 — `completeness_genuinely_nonvacuous`: the gates are JOINTLY SATISFIABLE by a real transfer.

The strictly-stronger statement: there is a NON-EMPTY trace (one genuine transfer row, balance `10 → 0`
via amount `10`·direction `1`, a real nonce tick) satisfying the live `transferV3`. A contradictory
gate set would still admit the empty trace — but it would NOT admit THIS real row, whose gates are all
jointly satisfied. So completeness's carried satisfiability conjunct is non-vacuous IN THE MEANINGFUL
SENSE (a real computation realizes it), not merely type-inhabited. -/

/-- **`completeness_genuinely_nonvacuous`** — `transferV3`'s per-row gates are JOINTLY SATISFIABLE by a
NON-EMPTY trace that actually COMPUTES a transfer: there exist a memory boundary and a trace with a
NON-EMPTY row list (`t.rows ≠ []`) satisfying `Satisfied2 hash transferV3 …`. Strictly stronger than
`CircuitCompletenessNonVacuity.completeness_satisfiability_nonvacuous` (which used the empty trace) —
the gate set is realized by a genuine debit, not vacuously. -/
theorem completeness_genuinely_nonvacuous (hash : List ℤ → ℤ) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      t.rows ≠ [] ∧ Satisfied2 hash transferV3 minit mfin maddrs t :=
  ⟨fun _ => 0, fun _ => (0, 0), [], realTransferTrace,
   realTransferTrace_rows_ne,
   satisfied2_transferV3_real hash (fun _ => 0) (fun _ => (0, 0))⟩

/-! ## §10 — axiom hygiene. -/

#assert_axioms lookup_holdsAt_tfOf
#assert_axioms base_constraints_hold
#assert_axioms row0_constraints_hold
#assert_axioms satisfied2_transferV3_real
#assert_axioms completeness_genuinely_nonvacuous

end Dregg2.Circuit.CircuitCompletenessNonVacuityReal
