/-
# Dregg2.Circuit.Emit.EffectVmEmitEmitEvent — the OBSERVATION-LOG effect `emitEventA`, EMITTED onto
  the runnable EffectVM row, welded to universe-A's `EmitEventSpec`.

## The "ONE circuit" thesis for `emitEventA` — the pure LOG effect (whole state-block frozen)

`emitEventA` writes the observation `log` and NOTHING in the kernel (`Spec/cellstatelog.lean`): a committed
emit prepends one self-targeted receipt row and leaves the ENTIRE `RecordKernelState` literally unchanged
(`execFullA_emitEvent_kernel`). At the EffectVM row level that is a NO-STATE-MOVE row: EVERY one of the 14
state-block columns is FROZEN (`state_after[i] = state_before[i]`), and the post-state (= the pre-state)
is bound into `state_commit` via the GROUP-4 hash chain. The log mutation itself is OFF the per-row
state-block (it is a chained-component the turn layer threads), so the row carries no log column — exactly
the honest boundary: this descriptor pins the STATE FREEZE the emit guarantees, and CITES the log receipt
to the turn layer.

`emitEventVmDescriptor` emits exactly that: 14 passthrough gates `state_after[i] - state_before[i] = 0`
(the whole block, INCLUDING the nonce — an emit does NOT tick it), with the GROUP-4 hash chain.

## What is PROVED

  * `emitEventVm_faithful` — emitted per-row gates ⟺ `EmitRowIntent` (the WHOLE block frozen).
  * `emitEventDescriptor_full_sound` — satisfying the descriptor under `RowEncodes` forces
    `CellFreezeSpec` (post = pre on every block component) AND publishes `post.commit = PI[NEW_COMMIT]`.
  * `emitEventDescriptor_commit_binds_state` — anti-ghost (reuses the transfer keystone; same chain). A
    tampered post-column that claims the published `NEW_COMMIT` is UNSAT.
  * `unify_emitEvent` / `unify_emitEvent_exec` — a committed `EmitEventSpec` (= the executor's
    `.emitEventA` arm), projected per cell under `cellProjE`, satisfies `CellFreezeSpec` EXACTLY (the WHOLE
    kernel is frozen, so EVERY projected component is frozen). The runnable freeze IS universe-A's
    kernel-freeze.

## HONEST BOUNDARY

  * PER-CELL / PER-ROW STATE FREEZE. The descriptor pins ONE cell's full state FREEZE + the binding of
    the (unchanged) after-state into `state_commit`. The LOG RECEIPT itself (the one mutation a committed
    emit makes) is a chained-component OFF the per-row state block — it is the turn layer's
    (`TurnEmit`), CITED not claimed. So this descriptor proves the emit's STATE-INVARIANCE, and defers the
    log-row payload to composition.
  * The `cell` index + the `emitGuard` (cell-liveness) have no row column; in universe-A's spec (cited).
  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding); frozen by its
    per-row passthrough gate.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatelog

namespace Dregg2.Circuit.Emit.EffectVmEmitEmitEvent

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.CellStateLog

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the emit-event effect row. -/

namespace selE
/-- The `emitEventA` effect selector column. -/
def EMIT_EVENT : Nat := 7
end selE

def eSelEmit : EmittedExpr := .var selE.EMIT_EVENT

/-! ## §1 — The emit-event row gates (the WHOLE state block frozen).

A committed emit moves NO kernel state, so every state-block column passes through unchanged. We emit one
passthrough gate per state offset 0..13 (balance limbs, nonce, 8 fields, cap_root, state_commit, reserved
— the 14 columns; the `state_commit` passthrough is consistent with the hash chain pinning it). -/

/-- Passthrough body for state offset `off`: `state_after[off] - state_before[off]`. -/
def gFreeze (off : Nat) : EmittedExpr := eSub (eSA off) (eSB off)

/-- The 14 whole-block passthrough gates (offsets 0..13). -/
def emitRowGates : List VmConstraint :=
  (List.range STATE_SIZE).map (fun off => VmConstraint.gate (gFreeze off))

/-! ## §2 — The emitted EMIT-EVENT descriptor. -/

def emitVmAirName : String := "dregg-effectvm-emitEvent-v1"

/-- **`emitEventVmDescriptor`** — the `emitEventA` effect's full concrete circuit: the 14 whole-block
passthrough gates ++ transition continuity ++ the 7 boundary PI pins, GROUP-4 hash sites, balance range
checks. -/
def emitEventVmDescriptor : EffectVmDescriptor :=
  { name := emitVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := emitRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The EMIT-EVENT ROW INTENT (the whole block frozen). -/

/-- **`EmitRowIntent env`** — every state-block offset 0..13 is frozen `after = before`. -/
def EmitRowIntent (env : VmRowEnv) : Prop :=
  ∀ off < STATE_SIZE, env.loc (saCol off) = env.loc (sbCol off)

def IsEmitRow (env : VmRowEnv) : Prop :=
  env.loc selE.EMIT_EVENT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

theorem emitEventVm_faithful (env : VmRowEnv) :
    (∀ c ∈ emitRowGates, c.holdsVm env false false) ↔ EmitRowIntent env := by
  unfold emitRowGates EmitRowIntent
  constructor
  · intro h off hoff
    have := h (.gate (gFreeze off)) (by
      simp only [List.mem_map, List.mem_range]; exact ⟨off, hoff, rfl⟩)
    simp only [VmConstraint.holdsVm, gFreeze, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · intro h c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨off, hoff, rfl⟩ := hc
    simp only [VmConstraint.holdsVm, gFreeze, eSA, eSB, eSub, EmittedExpr.eval]
    rw [h off hoff]; ring

/-- **Anti-ghost (state tamper).** A row where some state offset `off < 14` is NOT frozen fails the
`gFreeze off` gate (UNSAT). -/
theorem emitEventVm_rejects_state_move (env : VmRowEnv) (off : Nat)
    (hwrong : env.loc (saCol off) ≠ env.loc (sbCol off)) :
    ¬ (VmConstraint.gate (gFreeze off)).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith [h]

/-! ## §5 — `CellFreezeSpec` + `RowEncodes` → structured per-cell soundness (post = pre). -/

/-- The per-cell freeze spec: post equals pre on EVERY block component. -/
def CellFreezeSpec (pre : CellState) (post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

def RowEncodes (env : VmRowEnv) (pre : CellState) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodes env pre post) (hint : EmitRowIntent env) :
    CellFreezeSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hint state.BALANCE_LO (by decide)
  · rw [← hsaHi, ← hsbHi]; exact hint state.BALANCE_HI (by decide)
  · rw [← hsaN, ← hsbN]; exact hint state.NONCE (by decide)
  · intro i
    rw [← hsaF i, ← hsbF i]
    exact hint (state.FIELD_BASE + i.val) (by have := i.isLt; unfold state.FIELD_BASE STATE_SIZE; omega)
  · rw [← hsaCap, ← hsbCap]; exact hint state.CAP_ROOT (by decide)
  · rw [← hsaRes, ← hsbRes]; exact hint state.RESERVED (by decide)

theorem emitRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ emitRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ emitRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold emitRowGates at hc
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨off, hoff, rfl⟩ := hc
  simpa only [VmConstraint.holdsVm] using this

theorem emitEventDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodes env pre post)
    (hsat : satisfiedVm hash emitEventVmDescriptor env true true) :
    CellFreezeSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hgates : ∀ c ∈ emitRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold emitEventVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := emitRowGates_flag_indep env true true hgates
  have hint := (emitEventVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ emitEventVmDescriptor.constraints := by
      unfold emitEventVmDescriptor; simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone). -/

theorem emit_sites_eq : emitEventVmDescriptor.hashSites = transferHashSites := rfl

theorem emitEventDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjE` to universe-A's `EmitEventSpec`.

`cellProjE k c` reads cell `c`'s conserved `balLo` (`balOf`) and `nonce` (`fieldOf nonceField`); the EffectVM
columns with no record analogue are `0`. A committed emit leaves the WHOLE kernel unchanged
(`execFullA_emitEvent_kernel`), so `cellProjE` of the post-kernel equals `cellProjE` of the pre-kernel
— the whole projection is FROZEN. -/

def cellProjE (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := fieldOf nonceField (k.cell c)
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_emitEvent` — THE UNIFICATION.** A committed `EmitEventSpec` (the executor leaves the WHOLE
kernel unchanged), projected onto any cell `c` under `cellProjE`, satisfies `CellFreezeSpec` EXACTLY:
post = pre on every block component (because `k' = k` for the whole kernel). So `CellFreezeSpec` IS the
emit's kernel-freeze restricted to one cell. -/
theorem unify_emitEvent (s s' : RecChainedState) (actor cell c : CellId) (topic data : Int)
    (hspec : EmitEventSpec s actor cell topic data s') :
    CellFreezeSpec (cellProjE s.kernel c) (cellProjE s'.kernel c) := by
  -- the whole kernel is unchanged: rebuild k' = k from the 17 frame clauses
  obtain ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hspec
  have hk : s'.kernel = s.kernel := recKernel_ext h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19
  rw [hk]
  exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-- **`unify_emitEvent_exec` — same, against the executor directly.** -/
theorem unify_emitEvent_exec (s s' : RecChainedState) (actor cell c : CellId) (topic data : Int)
    (h : execFullA s (.emitEventA actor cell topic data) = some s') :
    CellFreezeSpec (cellProjE s.kernel c) (cellProjE s'.kernel c) :=
  unify_emitEvent s s' actor cell c topic data
    ((execFullA_emitEvent_iff_spec s actor cell topic data s').mp h)

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement.** With `pre = cellProjE
s.kernel c`, the descriptor's pinned post-state agrees with the executor's post-cell projection on EVERY
clause (the whole block frozen, matching the kernel-freeze). No divergence. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (actor cell c : CellId) (topic data : Int) (post : CellState)
    (henc : RowEncodes env (cellProjE s.kernel c) post)
    (hsat : satisfiedVm hash emitEventVmDescriptor env true true)
    (hexec : execFullA s (.emitEventA actor cell topic data) = some s') :
    post.balLo = (cellProjE s'.kernel c).balLo
    ∧ post.balHi = (cellProjE s'.kernel c).balHi
    ∧ post.nonce = (cellProjE s'.kernel c).nonce
    ∧ (∀ i, post.fields i = (cellProjE s'.kernel c).fields i)
    ∧ post.capRoot = (cellProjE s'.kernel c).capRoot
    ∧ post.reserved = (cellProjE s'.kernel c).reserved := by
  obtain ⟨hcirc, _⟩ := emitEventDescriptor_full_sound hash env (cellProjE s.kernel c) post henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, heN, heF, heCap, heRes⟩ := unify_emitEvent_exec s s' actor cell c topic data hexec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · rw [hcN, heN]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §8 — NON-VACUITY. -/

/-- A concrete emit row: only the selector is hot; the WHOLE state block is `0` before and after
(trivially frozen). The pure log effect moves no state, so the all-zero block is a genuine witness. -/
def goodEmitRow : VmRowEnv where
  loc := fun v => if v = selE.EMIT_EVENT then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodEmitRow` REALIZES the freeze intent: every state offset's
`after = before` (both `0`, since neither `saCol off` nor `sbCol off` is the selector column 7). -/
theorem goodEmitRow_realizes_intent : EmitRowIntent goodEmitRow := by
  intro off hoff
  show goodEmitRow.loc (saCol off) = goodEmitRow.loc (sbCol off)
  have hsb : sbCol off = 54 + off := by simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS]
  have hsa : saCol off = 76 + off := by
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS]
  show (if saCol off = selE.EMIT_EVENT then (1:ℤ) else 0)
      = (if sbCol off = selE.EMIT_EVENT then (1:ℤ) else 0)
  rw [hsb, hsa]
  unfold selE.EMIT_EVENT
  rw [if_neg (by omega), if_neg (by omega)]

/-- A FORGED emit row: `goodEmitRow` with post-`bal_lo` tampered to `999 ≠ 5` (a state move on a
no-state-move effect). -/
def badEmitRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodEmitRow.loc v
  nxt := goodEmitRow.nxt
  pub := goodEmitRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badEmitRow`'s post-`bal_lo` is NOT frozen
(`999 ≠ 5`), so the `gFreeze BALANCE_LO` gate REJECTS it. -/
theorem badEmitRow_rejected :
    ¬ (VmConstraint.gate (gFreeze state.BALANCE_LO)).holdsVm badEmitRow false false := by
  apply emitEventVm_rejects_state_move
  have hsa : saCol state.BALANCE_LO = 76 := by
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.BALANCE_LO]
  have hsb : sbCol state.BALANCE_LO = 54 := by
    simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.BALANCE_LO]
  show badEmitRow.loc (saCol state.BALANCE_LO) ≠ badEmitRow.loc (sbCol state.BALANCE_LO)
  rw [hsa, hsb]
  -- badEmitRow at 76 = 999 (the overwrite); at 54 = 0 (the all-zero block)
  have ht : badEmitRow.loc 76 = 999 := by
    show (if (76:Nat) = saCol state.BALANCE_LO then (999:ℤ) else goodEmitRow.loc 76) = 999
    rw [if_pos (by rw [hsa])]
  have hg : badEmitRow.loc 54 = 0 := by
    show (if (54:Nat) = saCol state.BALANCE_LO then (999:ℤ) else goodEmitRow.loc 54) = 0
    rw [if_neg (by rw [hsa]; omega)]
    show goodEmitRow.loc 54 = 0
    show (if (54:Nat) = selE.EMIT_EVENT then (1:ℤ) else 0) = 0
    unfold selE.EMIT_EVENT
    rw [if_neg (by omega)]
  rw [ht, hg]; norm_num

/-! ## §9 — Axiom-hygiene tripwires. -/

#guard emitEventVmDescriptor.constraints.length == 14 + 14 + 4 + 3
#guard emitEventVmDescriptor.hashSites.length == 4
#guard emitEventVmDescriptor.traceWidth == 186

#assert_axioms emitEventVm_faithful
#assert_axioms emitEventVm_rejects_state_move
#assert_axioms intent_to_cellSpec
#assert_axioms emitRowGates_flag_indep
#assert_axioms emitEventDescriptor_full_sound
#assert_axioms emitEventDescriptor_commit_binds_state
#assert_axioms unify_emitEvent
#assert_axioms unify_emitEvent_exec
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodEmitRow_realizes_intent
#assert_axioms badEmitRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
