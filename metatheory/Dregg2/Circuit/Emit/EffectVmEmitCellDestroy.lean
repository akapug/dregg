/-
# Dregg2.Circuit.Emit.EffectVmEmitCellDestroy — the `cellDestroy` effect's EffectVM-row circuit, EMITTED.

`cellDestroy` flips `cell`'s `lifecycle` SIDE-TABLE entry to `Destroyed` and binds a `deathCert` at
`cell`, BALANCE-NEUTRAL, self-targeted receipt prepended. Its FULL universe-A soundness is
`Inst.cellDestroyA.cellDestroyA_full_sound ⇒ CellDestroySpec` (the EffectCommit2-DUAL layer; all 18
components + log, with `lifecycle`/`deathCert` the two TOUCHED side-tables and the cell's economic
state literally frozen).

This is a FRAME-HEAVY lifecycle/flag effect (group hint): it touches a lifecycle FLAG + a death-cert,
both of which live in per-cell SIDE-TABLES the EffectVM 14-column economic block does NOT carry. So the
per-row circuit pins the cell's ECONOMIC block is FROZEN (`state_after = state_before`, column by
column) and bound into `state_commit` — and the actual lifecycle side-effect is entirely OFF-ROW.

## What the EffectVM row CAN pin (honest)

  * the cell's 14-column economic block is FROZEN (`after[off] = before[off]` for every column);
  * the (unchanged) after-block is bound into the published `state_commit` under Poseidon2 CR.

## What the EffectVM row CANNOT enforce (the honest boundary — the WHOLE point of the effect)

  * the `lifecycle` flip to `Destroyed` — a per-cell SIDE-TABLE, NO EffectVM column;
  * the `deathCert` bind — likewise a side-table;
  * the self-targeted receipt; the self-authority + not-already-destroyed guard.

The per-row circuit witnesses the BALANCE-NEUTRALITY of destroy (nothing economic moved) but NOT the
lifecycle transition itself. We connect the economic-freeze overlap and FLAG the lifecycle/deathCert/
receipt/guard as off-row — the row CANNOT distinguish a destroyed cell from a live one.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR named hypothesis only. No
`sorry`/`:= True`/`native_decide`. Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Emit.EffectVmEmitCellDestroy

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA eSB eSub)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Circuit.Spec.CellLifecycle

set_option linter.unusedVariables false

/-! ## §0 — the `cellDestroy` selector column (local). -/

/-- The `cellDestroy` selector column index. -/
def SEL_CELLDESTROY : Nat := 4

/-! ## §1 — the FROZEN-block per-row gates (the cell's economic block passes through unchanged).

For every economic-data column `off`, the row asserts `state_after[off] = state_before[off]` (the
balance-neutral, frame-passthrough nature of a lifecycle flag flip). 13 passthrough gates. -/

/-- The passthrough gate for state-block column `off`: `state_after[off] - state_before[off] = 0`. -/
def gFreeze (off : Nat) : VmConstraint := .gate (eSub (eSA off) (eSB off))

/-- The 13 frozen-block passthrough gates (every economic-data column). -/
def cellDestroyRowGates : List VmConstraint :=
  [ gFreeze state.BALANCE_LO, gFreeze state.BALANCE_HI, gFreeze state.NONCE
  , gFreeze state.CAP_ROOT, gFreeze state.RESERVED ]
  ++ (List.range 8).map (fun i => gFreeze (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def cellDestroyHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted descriptor. -/

def cellDestroyVmAirName : String := "dregg-effectvm-celldestroy-v1"

/-- **`cellDestroyVmDescriptor`** — the `cellDestroy` EffectVM-row circuit: the 13 economic-freeze
passthrough gates + the 4 ordered GROUP-4 hash sites binding the (unchanged) block into `state_commit`. -/
def cellDestroyVmDescriptor : EffectVmDescriptor :=
  { name := cellDestroyVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := cellDestroyRowGates
  , hashSites := cellDestroyHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the FROZEN-block row intent (the per-cell economic block is preserved). -/

/-- **`FrozenBlockIntent env`** — the row's whole economic block is preserved: every economic-data
column equal after = before. The EffectVM-row projection of `cellDestroy`'s balance-neutrality. -/
def FrozenBlockIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §5 — FAITHFULNESS: the emitted per-row gates ⟺ the frozen-block intent. -/

theorem cellDestroyVm_faithful (env : VmRowEnv) :
    (∀ c ∈ cellDestroyRowGates, c.holdsVm env false false) ↔ FrozenBlockIntent env := by
  unfold cellDestroyRowGates FrozenBlockIntent
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

theorem cellDestroyVm_rejects_unfrozen (env : VmRowEnv) (hwrong : ¬ FrozenBlockIntent env) :
    ¬ (∀ c ∈ cellDestroyRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((cellDestroyVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate —
a lifecycle flag flip cannot silently move value. -/
theorem cellDestroyVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (gFreeze state.BALANCE_LO).holdsVm env false false := by
  simp only [gFreeze, VmConstraint.holdsVm, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §7 — the commitment binding (inherited from the keystone). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols absorbed_determined_by_commit)

theorem cellDestroyVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ cellDestroyHashSites)
    (hs₂ : siteHoldsAll hash e₂ cellDestroyHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — CONNECTOR to universe-A `CellDestroySpec` via `cellProj`.

`CellDestroySpec` freezes both `bal` (`s'.kernel.bal = s.kernel.bal`) and the cell record
(`s'.kernel.cell = s.kernel.cell`), so the projected economic block is preserved across destroy —
EXACTLY the row's `FrozenBlockIntent` on the balance dimension. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`cellDestroy_balance_frozen` — the OVERLAP, from the executor.** A committed `cellDestroy`
freezes the cell's economic balance: `cellProj` of `cell` is identical pre and post (the cell record
and `bal` table are both framed unchanged). So the row's `FrozenBlockIntent` on the balance dimension
is the executor's genuine balance-neutrality. -/
theorem cellDestroy_balance_frozen (s s' : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (hspec : CellDestroySpec s actor cell certHash s') :
    (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  -- CellDestroySpec freezes the cell record (`s'.kernel.cell = s.kernel.cell`)
  obtain ⟨_, _, _, _, _, hcellmap, _⟩ := hspec
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hcellmap]

/-- **`cellDestroy_row_matches_executor` — the CONNECTOR.** If the row's blocks decode (`RowEncodes`),
the gates hold, and the executor commits `CellDestroySpec`, the row's pinned post-`balLo` equals the
executor's frozen post-`balLo` AND equals its pre-`balLo` (nothing moved). The economic-freeze the row
witnesses is the executor's balance-neutrality. -/
theorem cellDestroy_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ cellDestroyRowGates, c.holdsVm env false false)
    (s s' : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (hspec : CellDestroySpec s actor cell certHash s')
    (hpre : pre.balLo = (cellProj s.kernel cell).balLo) :
    post.balLo = pre.balLo
    ∧ (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  obtain ⟨hLo, _, _, _, _, _⟩ := (cellDestroyVm_faithful env).mp hgates
  obtain ⟨hsbLo, _, _, _, _, _, _, _, _, hsaLo, _⟩ := henc
  refine ⟨?_, cellDestroy_balance_frozen s s' actor cell certHash hspec⟩
  -- post.balLo = env (saCol bal_lo) = env (sbCol bal_lo) = pre.balLo
  rw [← hsaLo, hLo, hsbLo]

/-! ## §9 — THE HONEST BOUNDARY: the lifecycle/deathCert/receipt side-effect is OFF-ROW.

The WHOLE POINT of `cellDestroy` — the `lifecycle` flip to `Destroyed` and the `deathCert` bind — lives
in per-cell SIDE-TABLES that have NO EffectVM column. The row's `FrozenBlockIntent` says NOTHING about
them: a row witnessing a frozen economic block is identical whether the cell was destroyed or left
live. The destroy SOUNDNESS lives ONLY in `cellDestroyA_full_sound`. -/

/-- **`cellDestroy_offrow_unenforced` — the loud finding.** `FrozenBlockIntent` is invariant under any
change OUTSIDE the economic state-block columns (`state_before`/`state_after`): two rows agreeing on
all economic block columns satisfy the intent equally, regardless of the (unrepresented) lifecycle
flag, death cert, or receipt. The lifecycle transition is OFF-ROW; the row CANNOT distinguish a
destroyed cell from a live one. -/
theorem cellDestroy_offrow_unenforced :
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

/-- A concrete frozen row: every economic column has `state_after = state_before` (we set both the
`sbCol`/`saCol` of `BALANCE_LO` to `100`, all others default `0` — and a `before`/`after` reader that
returns the SAME value on each economic column). To keep the witness trivially frozen, `loc` reads a
single underlying per-offset value for BOTH the before and after column of each economic offset. -/
def frozenRow : VmRowEnv where
  loc := fun v => if v = sbCol state.BALANCE_LO ∨ v = saCol state.BALANCE_LO then 100 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- For an economic offset, `frozenRow`'s `saCol`/`sbCol` reads agree (both `100` for `BALANCE_LO`,
both `0` otherwise) — because the only nonzero columns are exactly the matched `BALANCE_LO` pair. -/
theorem frozenRow_col_agree (off : Nat) (hoff : off < STATE_SIZE) :
    frozenRow.loc (saCol off) = frozenRow.loc (sbCol off) := by
  show (if saCol off = sbCol state.BALANCE_LO ∨ saCol off = saCol state.BALANCE_LO then (100:ℤ) else 0)
      = (if sbCol off = sbCol state.BALANCE_LO ∨ sbCol off = saCol state.BALANCE_LO then 100 else 0)
  by_cases hb : off = state.BALANCE_LO
  · subst hb
    rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl)]
  · -- off ≠ BALANCE_LO: saCol off and sbCol off both miss both named columns
    have h1 : ¬ (saCol off = sbCol state.BALANCE_LO ∨ saCol off = saCol state.BALANCE_LO) := by
      unfold saCol sbCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE
        NUM_PARAMS state.BALANCE_LO at *
      omega
    have h2 : ¬ (sbCol off = sbCol state.BALANCE_LO ∨ sbCol off = saCol state.BALANCE_LO) := by
      unfold saCol sbCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE
        NUM_PARAMS state.BALANCE_LO at *
      omega
    rw [if_neg h1, if_neg h2]

/-- **NON-VACUITY (witness TRUE).** `frozenRow` realizes the frozen-block intent: every economic
column has `after = before` (`frozenRow_col_agree`). -/
theorem frozenRow_realizes_intent : FrozenBlockIntent frozenRow := by
  refine ⟨frozenRow_col_agree _ (by decide), frozenRow_col_agree _ (by decide),
    frozenRow_col_agree _ (by decide), frozenRow_col_agree _ (by decide),
    frozenRow_col_agree _ (by decide), ?_⟩
  intro i hi
  exact frozenRow_col_agree (state.FIELD_BASE + i) (by unfold state.FIELD_BASE STATE_SIZE; omega)

/-- A FORGED row: `frozenRow` with post-`bal_lo` moved to `999` (a lifecycle flip cannot move value). -/
def forgedRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else frozenRow.loc v
  nxt := frozenRow.nxt
  pub := frozenRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `forgedRow`'s post-`bal_lo` (999) ≠
pre-`bal_lo` (100), so the freeze gate REJECTS it. -/
theorem forgedRow_rejected : ¬ (gFreeze state.BALANCE_LO).holdsVm forgedRow false false := by
  apply cellDestroyVm_rejects_moved_balance
  -- post-bal_lo = 999 (the overwrite); pre-bal_lo = frozenRow's sbCol = 100
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (999:ℤ)
      else frozenRow.loc (saCol state.BALANCE_LO))
      ≠ frozenRow.loc (sbCol state.BALANCE_LO)
  rw [if_pos rfl]
  show (999:ℤ) ≠ (if sbCol state.BALANCE_LO = sbCol state.BALANCE_LO
      ∨ sbCol state.BALANCE_LO = saCol state.BALANCE_LO then 100 else 0)
  rw [if_pos (Or.inl rfl)]; norm_num

/-! ## §11 — axiom-hygiene tripwires. -/

#guard cellDestroyVmDescriptor.constraints.length == 13
#guard cellDestroyVmDescriptor.hashSites.length == 4
#guard cellDestroyVmDescriptor.traceWidth == 186

#assert_axioms cellDestroyVm_faithful
#assert_axioms cellDestroyVm_rejects_unfrozen
#assert_axioms cellDestroyVm_rejects_moved_balance
#assert_axioms cellDestroyVm_commit_binds_block
#assert_axioms cellDestroy_balance_frozen
#assert_axioms cellDestroy_row_matches_executor
#assert_axioms cellDestroy_offrow_unenforced
#assert_axioms frozenRow_realizes_intent
#assert_axioms forgedRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
