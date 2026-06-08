/-
# Dregg2.Circuit.Emit.EffectVmEmitCellSeal — the `cellSeal` effect's EffectVM-row circuit, EMITTED.

`cellSeal` flips `cell`'s `lifecycle` SIDE-TABLE entry Live → Sealed, BALANCE-NEUTRAL, self-targeted
receipt prepended. Its FULL universe-A soundness is `Inst.CellSealA.cellSealA_full_sound ⇒ CellSealSpec`
(the EffectCommit2 layer; all 18 components + log, `lifecycle` the ONE touched side-table, the cell's
economic state literally frozen).

A FRAME-HEAVY lifecycle/flag effect (group hint): it touches only the `lifecycle` flag, which lives in
a per-cell SIDE-TABLE the EffectVM 14-column economic block does NOT carry. The per-row circuit pins the
cell's ECONOMIC block is FROZEN and bound into `state_commit`; the lifecycle flip is OFF-ROW.

## What the EffectVM row CAN pin

  * the cell's 14-column economic block is FROZEN (`after[off] = before[off]` every column);
  * the (unchanged) after-block is bound into `state_commit` under Poseidon2 CR.

## What the EffectVM row CANNOT enforce (the honest boundary — the WHOLE point of the effect)

  * the `lifecycle` flip Live → Sealed — a per-cell SIDE-TABLE, NO EffectVM column;
  * the self-targeted receipt; the self-authority + is-Live guard.

The row witnesses the balance-neutrality of seal but NOT the seal itself; it CANNOT distinguish a
sealed cell from a live one. The seal SOUNDNESS lives ONLY in `cellSealA_full_sound`.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR named hypothesis only. No
`sorry`/`:= True`/`native_decide`. Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Emit.EffectVmEmitCellSeal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA eSB eSub)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Circuit.Spec.CellLifecycle

set_option linter.unusedVariables false

/-! ## §0 — the `cellSeal` selector column (local). -/

/-- The `cellSeal` selector column index. -/
def SEL_CELLSEAL : Nat := 5

/-! ## §1 — the FROZEN-block per-row gates. -/

/-- The passthrough gate for state-block column `off`: `state_after[off] - state_before[off] = 0`. -/
def gFreeze (off : Nat) : VmConstraint := .gate (eSub (eSA off) (eSB off))

/-- The 13 frozen-block passthrough gates (every economic-data column). -/
def cellSealRowGates : List VmConstraint :=
  [ gFreeze state.BALANCE_LO, gFreeze state.BALANCE_HI, gFreeze state.NONCE
  , gFreeze state.CAP_ROOT, gFreeze state.RESERVED ]
  ++ (List.range 8).map (fun i => gFreeze (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def cellSealHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted descriptor. -/

def cellSealVmAirName : String := "dregg-effectvm-cellseal-v1"

/-- **`cellSealVmDescriptor`** — the `cellSeal` EffectVM-row circuit: the 13 economic-freeze gates +
the 4 ordered GROUP-4 hash sites binding the (unchanged) block into `state_commit`. -/
def cellSealVmDescriptor : EffectVmDescriptor :=
  { name := cellSealVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := cellSealRowGates
  , hashSites := cellSealHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the FROZEN-block row intent. -/

/-- **`FrozenBlockIntent env`** — the row's whole economic block is preserved (after = before). The
EffectVM-row projection of `cellSeal`'s balance-neutrality. -/
def FrozenBlockIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §5 — FAITHFULNESS. -/

theorem cellSealVm_faithful (env : VmRowEnv) :
    (∀ c ∈ cellSealRowGates, c.holdsVm env false false) ↔ FrozenBlockIntent env := by
  unfold cellSealRowGates FrozenBlockIntent
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

theorem cellSealVm_rejects_unfrozen (env : VmRowEnv) (hwrong : ¬ FrozenBlockIntent env) :
    ¬ (∀ c ∈ cellSealRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((cellSealVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate. -/
theorem cellSealVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (gFreeze state.BALANCE_LO).holdsVm env false false := by
  simp only [gFreeze, VmConstraint.holdsVm, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §7 — the commitment binding (inherited from the keystone). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols absorbed_determined_by_commit)

theorem cellSealVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ cellSealHashSites)
    (hs₂ : siteHoldsAll hash e₂ cellSealHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — CONNECTOR to universe-A `CellSealSpec` via `cellProj`.

`CellSealSpec` freezes the cell record (`s'.kernel.cell = s.kernel.cell`), so the projected economic
block is preserved across seal — EXACTLY the row's `FrozenBlockIntent` on the balance dimension. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`cellSeal_balance_frozen` — the OVERLAP, from the executor.** A committed `cellSeal` freezes the
cell's economic balance (the cell record is framed unchanged). So the row's `FrozenBlockIntent` on the
balance dimension is the executor's balance-neutrality. -/
theorem cellSeal_balance_frozen (s s' : RecChainedState) (actor cell : CellId)
    (hspec : CellSealSpec s actor cell s') :
    (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  -- CellSealSpec: guard, lifecycle, log, accounts, cell (position 5)
  obtain ⟨_, _, _, _, hcellmap, _⟩ := hspec
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hcellmap]

/-- **`cellSeal_row_matches_executor` — the CONNECTOR.** If the row's blocks decode, the gates hold,
and the executor commits `CellSealSpec`, the row's pinned post-`balLo` equals the pre-`balLo` AND the
executor's frozen post-`balLo` equals its pre-`balLo`. -/
theorem cellSeal_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ cellSealRowGates, c.holdsVm env false false)
    (s s' : RecChainedState) (actor cell : CellId)
    (hspec : CellSealSpec s actor cell s')
    (hpre : pre.balLo = (cellProj s.kernel cell).balLo) :
    post.balLo = pre.balLo
    ∧ (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  obtain ⟨hLo, _, _, _, _, _⟩ := (cellSealVm_faithful env).mp hgates
  obtain ⟨hsbLo, _, _, _, _, _, _, _, _, hsaLo, _⟩ := henc
  refine ⟨?_, cellSeal_balance_frozen s s' actor cell hspec⟩
  rw [← hsaLo, hLo, hsbLo]

/-! ## §9 — THE HONEST BOUNDARY: the lifecycle flip is OFF-ROW. -/

/-- **`cellSeal_offrow_unenforced` — the loud finding.** `FrozenBlockIntent` is invariant under any
change OUTSIDE the economic block columns: two rows agreeing on all economic columns satisfy the intent
equally, regardless of the (unrepresented) lifecycle flag or receipt. The seal transition is OFF-ROW;
the row CANNOT distinguish a sealed cell from a live one. -/
theorem cellSeal_offrow_unenforced :
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
  apply cellSealVm_rejects_moved_balance
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (999:ℤ)
      else frozenRow.loc (saCol state.BALANCE_LO))
      ≠ frozenRow.loc (sbCol state.BALANCE_LO)
  rw [if_pos rfl]
  show (999:ℤ) ≠ (if sbCol state.BALANCE_LO = sbCol state.BALANCE_LO
      ∨ sbCol state.BALANCE_LO = saCol state.BALANCE_LO then 100 else 0)
  rw [if_pos (Or.inl rfl)]; norm_num

/-! ## §11 — axiom-hygiene tripwires. -/

#guard cellSealVmDescriptor.constraints.length == 13
#guard cellSealVmDescriptor.hashSites.length == 4
#guard cellSealVmDescriptor.traceWidth == 186

#assert_axioms cellSealVm_faithful
#assert_axioms cellSealVm_rejects_unfrozen
#assert_axioms cellSealVm_rejects_moved_balance
#assert_axioms cellSealVm_commit_binds_block
#assert_axioms cellSeal_balance_frozen
#assert_axioms cellSeal_row_matches_executor
#assert_axioms cellSeal_offrow_unenforced
#assert_axioms frozenRow_realizes_intent
#assert_axioms forgedRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCellSeal
