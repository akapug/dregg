/-
# Dregg2.Circuit.Emit.EffectVmEmitRefusal — the `refusal` effect's EffectVM-row circuit, EMITTED.

`refusal` writes the `"refusal"` audit slot of `cell`'s RECORD to `1` (dregg1's cross-cell SetState
refusal commitment), BALANCE-NEUTRAL, self-targeted receipt prepended. Its FULL universe-A soundness is
`Inst.RefusalA.refusalA_full_sound ⇒ RefusalSpec` (the EffectSpec layer; all 17 kernel fields + log,
`cell` the ONE touched component — the `refusal := 1` audit write — and every other field frozen).

A FRAME-HEAVY flag effect (group hint): the audit write lands in a NON-`balance` RECORD field
(`refusalField = "refusal"`) that has NO EffectVM column (the 14-col economic block carries the
conserved `balance` measure, not arbitrary audit slots). So the per-row circuit pins the cell's
ECONOMIC block is FROZEN and bound into `state_commit`; the refusal-slot write is OFF-ROW.

## What the EffectVM row CAN pin

  * the cell's 14-column economic block is FROZEN (`after[off] = before[off]` every column) — the
    refusal write is balance-neutral (`auditCellWrite_correct`: a write to a slot `≠ balance` leaves
    the conserved balance untouched);
  * the (unchanged) after-block is bound into `state_commit` under Poseidon2 CR.

## What the EffectVM row CANNOT enforce (the honest boundary — the WHOLE point of the effect)

  * the `refusal := 1` audit slot write — a NON-`balance` RECORD field, NO EffectVM column;
  * the self-targeted receipt; the three-leg audit guard.

The row witnesses the balance-neutrality of refusal but NOT the refusal commitment itself; it CANNOT
distinguish a refusing cell from a non-refusing one. The refusal SOUNDNESS lives ONLY in
`refusalA_full_sound`.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR named hypothesis only. No
`sorry`/`:= True`/`native_decide`. Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Emit.EffectVmEmitRefusal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA eSB eSub)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (refusalField)
open Dregg2.Exec (balanceField)
open Dregg2.Circuit.Spec.CellStateAudit

set_option linter.unusedVariables false

/-! ## §0 — the `refusal` selector column (local). -/

/-- The `refusal` selector column index. -/
def SEL_REFUSAL : Nat := 7

/-! ## §1 — the FROZEN-block per-row gates (the cell's economic block passes through unchanged). -/

/-- The passthrough gate for state-block column `off`: `state_after[off] - state_before[off] = 0`. -/
def gFreeze (off : Nat) : VmConstraint := .gate (eSub (eSA off) (eSB off))

/-- The 13 frozen-block passthrough gates (every economic-data column). -/
def refusalRowGates : List VmConstraint :=
  [ gFreeze state.BALANCE_LO, gFreeze state.BALANCE_HI, gFreeze state.NONCE
  , gFreeze state.CAP_ROOT, gFreeze state.RESERVED ]
  ++ (List.range 8).map (fun i => gFreeze (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def refusalHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted descriptor. -/

def refusalVmAirName : String := "dregg-effectvm-refusal-v1"

/-- **`refusalVmDescriptor`** — the `refusal` EffectVM-row circuit: the 13 economic-freeze passthrough
gates + the 4 ordered GROUP-4 hash sites binding the (unchanged) block into `state_commit`. -/
def refusalVmDescriptor : EffectVmDescriptor :=
  { name := refusalVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := refusalRowGates
  , hashSites := refusalHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the FROZEN-block row intent. -/

/-- **`FrozenBlockIntent env`** — the row's whole economic block is preserved (after = before). The
EffectVM-row projection of `refusal`'s balance-neutrality. -/
def FrozenBlockIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §5 — FAITHFULNESS. -/

theorem refusalVm_faithful (env : VmRowEnv) :
    (∀ c ∈ refusalRowGates, c.holdsVm env false false) ↔ FrozenBlockIntent env := by
  unfold refusalRowGates FrozenBlockIntent
  constructor
  · intro h
    have hLo := h (gFreeze state.BALANCE_LO) (by simp [gFreeze])
    have hHi := h (gFreeze state.BALANCE_HI) (by simp [gFreeze])
    have hN  := h (gFreeze state.NONCE) (by simp [gFreeze])
    have hCap := h (gFreeze state.CAP_ROOT) (by simp [gFreeze])
    have hRes := h (gFreeze state.RESERVED) (by simp [gFreeze])
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (gFreeze (state.FIELD_BASE + i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [gFreeze, VmConstraint.holdsVm, eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hN hCap hRes
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [gFreeze, VmConstraint.holdsVm, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simp only [gFreeze, VmConstraint.holdsVm, eSA, eSB, eSub, EmittedExpr.eval]
    · rw [hLo]; ring
    · rw [hHi]; ring
    · rw [hN]; ring
    · rw [hCap]; ring
    · rw [hRes]; ring
    · rw [hFld i hi]; ring

/-! ## §6 — ANTI-GHOST. -/

theorem refusalVm_rejects_unfrozen (env : VmRowEnv) (hwrong : ¬ FrozenBlockIntent env) :
    ¬ (∀ c ∈ refusalRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((refusalVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a
refusal write cannot silently move value. -/
theorem refusalVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (gFreeze state.BALANCE_LO).holdsVm env false false := by
  simp only [gFreeze, VmConstraint.holdsVm, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §7 — the commitment binding (inherited from the keystone). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols absorbed_determined_by_commit)

theorem refusalVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ refusalHashSites)
    (hs₂ : siteHoldsAll hash e₂ refusalHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — CONNECTOR to universe-A `RefusalSpec` via `cellProj`.

`RefusalSpec`'s `cell` clause is `s'.kernel.cell = auditCellMap s.kernel cell refusalField`; since
`refusalField ≠ balanceField`, `auditCellWrite_correct` gives `balOf (post cell) = balOf (pre cell)`.
So the projected economic block is preserved across refusal — EXACTLY the row's `FrozenBlockIntent` on
the balance dimension. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`refusal_balance_frozen` — the OVERLAP, from the executor.** A committed `refusal` freezes the
cell's economic balance: the `refusal := 1` write lands in a slot `≠ balance`, so `balOf` is
preserved (`auditCellWrite_correct`). So the row's `FrozenBlockIntent` on the balance dimension is the
executor's balance-neutrality. -/
theorem refusal_balance_frozen (s s' : RecChainedState) (actor cell : CellId)
    (hspec : RefusalSpec s actor cell s') :
    (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  -- RefusalSpec: guard, cell (= auditCellMap), log, frame...
  obtain ⟨_, hcellmap, _⟩ := hspec
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hcellmap]
  have hf : refusalField ≠ balanceField := by decide
  exact (auditCellWrite_correct s.kernel cell refusalField hf).2.1

/-- **`refusal_row_matches_executor` — the CONNECTOR.** If the row's blocks decode, the gates hold,
and the executor commits `RefusalSpec`, the row's pinned post-`balLo` equals the pre-`balLo` AND the
executor's frozen post-`balLo` equals its pre-`balLo`. -/
theorem refusal_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ refusalRowGates, c.holdsVm env false false)
    (s s' : RecChainedState) (actor cell : CellId)
    (hspec : RefusalSpec s actor cell s')
    (hpre : pre.balLo = (cellProj s.kernel cell).balLo) :
    post.balLo = pre.balLo
    ∧ (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  obtain ⟨hLo, _, _, _, _, _⟩ := (refusalVm_faithful env).mp hgates
  obtain ⟨hsbLo, _, _, _, _, _, _, _, _, hsaLo, _⟩ := henc
  refine ⟨?_, refusal_balance_frozen s s' actor cell hspec⟩
  rw [← hsaLo, hLo, hsbLo]

/-! ## §9 — THE HONEST BOUNDARY: the refusal-slot write is OFF-ROW. -/

/-- **`refusal_offrow_unenforced` — the loud finding.** `FrozenBlockIntent` is invariant under any
change OUTSIDE the economic block columns: two rows agreeing on all economic columns satisfy the intent
equally, regardless of the (unrepresented) `refusal := 1` audit slot or receipt. The refusal write is
OFF-ROW; the row CANNOT distinguish a refusing cell from a non-refusing one. -/
theorem refusal_offrow_unenforced :
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off) ∧
                     env₁.loc (sbCol off) = env₂.loc (sbCol off)) →
      (FrozenBlockIntent env₁ ↔ FrozenBlockIntent env₂)) := by
  intro env₁ env₂ hagree
  unfold FrozenBlockIntent
  rw [(hagree state.BALANCE_LO).1, (hagree state.BALANCE_LO).2,
      (hagree state.BALANCE_HI).1, (hagree state.BALANCE_HI).2,
      (hagree state.NONCE).1, (hagree state.NONCE).2,
      (hagree state.CAP_ROOT).1, (hagree state.CAP_ROOT).2,
      (hagree state.RESERVED).1, (hagree state.RESERVED).2]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by
      rw [← (hagree (state.FIELD_BASE + i)).1, ← (hagree (state.FIELD_BASE + i)).2]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by
      rw [(hagree (state.FIELD_BASE + i)).1, (hagree (state.FIELD_BASE + i)).2]; exact f i hi⟩

/-! ## §10 — NON-VACUITY. -/

/-- A concrete frozen row (single underlying value per matched economic column). -/
def frozenRow : VmRowEnv where
  loc := fun v => if v = sbCol state.BALANCE_LO ∨ v = saCol state.BALANCE_LO then 100 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `frozenRow`'s `saCol`/`sbCol` reads agree on every economic offset. -/
theorem frozenRow_col_agree (off : Nat) (hoff : off < STATE_SIZE) :
    frozenRow.loc (saCol off) = frozenRow.loc (sbCol off) := by
  show (if saCol off = sbCol state.BALANCE_LO ∨ saCol off = saCol state.BALANCE_LO then (100:ℤ) else 0)
      = (if sbCol off = sbCol state.BALANCE_LO ∨ sbCol off = saCol state.BALANCE_LO then 100 else 0)
  by_cases hb : off = state.BALANCE_LO
  · subst hb
    rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl)]
  · have h1 : ¬ (saCol off = sbCol state.BALANCE_LO ∨ saCol off = saCol state.BALANCE_LO) := by
      unfold saCol sbCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE
        NUM_PARAMS state.BALANCE_LO at *
      omega
    have h2 : ¬ (sbCol off = sbCol state.BALANCE_LO ∨ sbCol off = saCol state.BALANCE_LO) := by
      unfold saCol sbCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE
        NUM_PARAMS state.BALANCE_LO at *
      omega
    rw [if_neg h1, if_neg h2]

/-- **NON-VACUITY (witness TRUE).** `frozenRow` realizes the frozen-block intent. -/
theorem frozenRow_realizes_intent : FrozenBlockIntent frozenRow := by
  refine ⟨frozenRow_col_agree _ (by decide), frozenRow_col_agree _ (by decide),
    frozenRow_col_agree _ (by decide), frozenRow_col_agree _ (by decide),
    frozenRow_col_agree _ (by decide), ?_⟩
  intro i hi
  exact frozenRow_col_agree (state.FIELD_BASE + i) (by unfold state.FIELD_BASE STATE_SIZE; omega)

/-- A FORGED row: `frozenRow` with post-`bal_lo` moved to `999`. -/
def forgedRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else frozenRow.loc v
  nxt := frozenRow.nxt
  pub := frozenRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `forgedRow`'s post-`bal_lo` (999) ≠
pre-`bal_lo` (100), so the freeze gate REJECTS it. -/
theorem forgedRow_rejected : ¬ (gFreeze state.BALANCE_LO).holdsVm forgedRow false false := by
  apply refusalVm_rejects_moved_balance
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (999:ℤ)
      else frozenRow.loc (saCol state.BALANCE_LO))
      ≠ frozenRow.loc (sbCol state.BALANCE_LO)
  rw [if_pos rfl]
  show (999:ℤ) ≠ (if sbCol state.BALANCE_LO = sbCol state.BALANCE_LO
      ∨ sbCol state.BALANCE_LO = saCol state.BALANCE_LO then 100 else 0)
  rw [if_pos (Or.inl rfl)]; norm_num

/-! ## §11 — axiom-hygiene tripwires. -/

#guard refusalVmDescriptor.constraints.length == 13
#guard refusalVmDescriptor.hashSites.length == 4
#guard refusalVmDescriptor.traceWidth == 186

#assert_axioms refusalVm_faithful
#assert_axioms refusalVm_rejects_unfrozen
#assert_axioms refusalVm_rejects_moved_balance
#assert_axioms refusalVm_commit_binds_block
#assert_axioms refusal_balance_frozen
#assert_axioms refusal_row_matches_executor
#assert_axioms refusal_offrow_unenforced
#assert_axioms frozenRow_realizes_intent
#assert_axioms forgedRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitRefusal
