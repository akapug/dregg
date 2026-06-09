/-
# Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation — the AUTHORITY-REVOCATION effect `revokeDelegationA`'s
  EffectVM-row circuit, EMITTED, RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and
  GRADUATED into the descriptor cutover (v2).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover runs `revokeDelegation` (selector 30) as a member of the **Stage-3 passthrough batch**
(`air.rs:983-1018`, `trace.rs:604`): the trace arm parks `child_hash[0]` into `params[0]` and does
`new_state.nonce += 1` — it does NOT move `cap_root` on the row. Every economic state-block column
(balance limbs, `cap_root`, all 8 fields, reserved) is FROZEN by the passthrough batch; the GLOBAL nonce
gate ticks the nonce by 1. The cap-table edge removal LIVES OFF-TRACE (bound via `compute_effects_hash`).

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the cellDestroy gauntlet). The PRE-v2
descriptor REUSED the `attenuateA` cap-root-MOVE descriptor (`new_cap_root − param2`) that the runtime
hand-AIR does NOT enforce on a revoke row (it FREEZES `cap_root`); that descriptor "passed" the honest
trace only by fixture accident (`cap_root = param2 = 0`) and froze the nonce. This v2 emits the runtime
passthrough + nonce TICK directly, and binds the cap-table edge-removal OFF-row via the universe-A
connector (§9).

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the honest boundary — the cap-table move is OFF-ROW)

  * the `caps := removeEdgeCaps caps holder t` edge removal — the `cap_root` is the SCALAR digest of the
    cap-table FUNCTION; the runtime hand-AIR FREEZES the on-row `cap_root` column and binds the actual
    removal via `effects_hash` OFF the per-row state block. The removal SOUNDNESS lives in universe-A's
    `revokeDelegationA_full_sound` / `Function.Injective D` (cited via the §connector).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
cap-table digest ONLY as `Function.Injective D`. No `sorry`/`:= True`/`native_decide`/rfl-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA

namespace Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.RevokeDelegationA (RevokeArgs revokeDelegationE revokeDelegationA_full_sound)
open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec removeEdgeCaps)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `revokeDelegation` selector column (runtime `sel::REVOKE_DELEGATION = 30`). -/

/-- The `revokeDelegation` selector column index (runtime `sel::REVOKE_DELEGATION = 30`). -/
def SEL_REVOKE_DELEGATION : Nat := 30

/-- The revoke row: `s_revoke = 1`, `s_noop = 0` (load-bearing for the nonce TICK gate). -/
def IsRevokeRow (env : VmRowEnv) : Prop :=
  env.loc SEL_REVOKE_DELEGATION = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body (revocation moves no value; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH (incl. `cap_root`) + nonce TICK (`gNonce`). -/
def revokeRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def revokeVmAirName : String := "dregg-effectvm-revokeDelegation-v2"

def revokeHashSites : List VmHashSite := transferHashSites

/-- **`revokeVmDescriptor`** — the `revokeDelegationA` EffectVM-row circuit, RECONCILED onto the runtime
hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary PI
pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def revokeVmDescriptor : EffectVmDescriptor :=
  { name := revokeVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := revokeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 30
  , hashSites := revokeHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`RevokeRowIntent env`** — every economic state-block column UNCHANGED (incl. `cap_root`) EXCEPT the
nonce, which TICKS by 1 (on a non-NoOp row `s_noop = 0`). The cap-table edge removal is out-of-row. -/
def RevokeRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

theorem revokeVm_faithful (env : VmRowEnv) :
    (∀ c ∈ revokeRowGates, c.holdsVm env false false) ↔ RevokeRowIntent env := by
  unfold revokeRowGates gFieldPassAll RevokeRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨by linarith [hLo], by linarith [hHi], by linarith [hNon], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST. -/

theorem revokeVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ RevokeRowIntent env) :
    ¬ (∀ c ∈ revokeRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((revokeVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate. -/
theorem revokeVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (cap-root tamper on row).** A row whose post-`cap_root` ≠ pre-`cap_root` fails the freeze
gate — the runtime row freezes `cap_root` (the move rides effects_hash); no on-row cap move is allowed. -/
theorem revokeVm_rejects_moved_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapPass).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. -/
theorem revokeVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §6 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem revokeVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ revokeHashSites)
    (hs₂ : siteHoldsAll hash e₂ revokeHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesRevoke env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesRevoke (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`RevokeCellSpec pre post`** — the per-cell FULL-state revoke row spec: economic block (incl.
`capRoot`) FROZEN; the nonce TICKS by 1. (The cap-table edge removal is off-row.) -/
def RevokeCellSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRevoke env pre post) (hint : RevokeRowIntent env) :
    RevokeCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN, hnon, hnoop]; ring
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §8 — the full descriptor soundness + the commitment binding. -/

theorem revokeDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRevoke env pre post)
    (hsat : satisfiedVm hash revokeVmDescriptor env true true) :
    RevokeCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ revokeRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ revokeVmDescriptor.constraints := by
      unfold revokeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcs c hmem
    unfold revokeRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (revokeVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ revokeVmDescriptor.constraints := by
      unfold revokeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

theorem revokeDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash revokeVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash revokeVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ revokeHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ revokeHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash revokeVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ revokeVmDescriptor.constraints := by
        unfold revokeVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hc e₁ hsat₁, hc e₂ hsat₂, hpub]
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §9 — THE CONNECTOR — the cap-table edge removal (OFF-ROW), via `revokeDelegationA_full_sound`.

The on-row `cap_root` is FROZEN (the runtime convention), but the cap-table edge removal IS the effect's
semantic content; it rides `effects_hash` off the per-row state block. We carry the validated universe-A
removal as a NAMED OFF-ROW theorem (`revokeCapDigest_removed_via_full_sound`), reported, not papered. -/

/-- The cap-table digest projection (the whole-function injective digest `D`). -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- The predicted post cap-digest for `revokeDelegationA`: `D` of `removeEdgeCaps caps holder t`. -/
def revokeCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : RevokeArgs) : ℤ :=
  D (removeEdgeCaps s.kernel.caps args.holder args.t)

/-- **`unify_revoke` — THE OFF-ROW CONNECTOR.** When `RevokeSpec` holds, the projected post cap-digest is
EXACTLY the edge-removed cap-digest `revokeCapDigestNew D s args`. This is the effect's actual semantic
content, enforced OFF the per-row state block (the runtime binds it via `effects_hash`). -/
theorem unify_revoke (D : Caps → ℤ) (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (hspec : RevokeSpec s args.holder args.t s') :
    capRootProj D s'.kernel = revokeCapDigestNew D s args := by
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (removeEdgeCaps s.kernel.caps args.holder args.t)
  rw [hcaps]

/-- **`unify_revoke_via_full_sound` — inherits the VALIDATED guarantee (off-row cap-table removal).** -/
theorem unify_revoke_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RevokeDelegationA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s')) :
    capRootProj D s'.kernel = revokeCapDigestNew D s args :=
  unify_revoke D s args s' (revokeDelegationA_full_sound S D hD hRest hLog s args s' h)

/-! ## §10 — NON-VACUITY. -/

/-- A concrete revoke row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodRevokeRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_REVOKE_DELEGATION then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodRevokeRow_noop : goodRevokeRow.loc sel.NOOP = 0 := by
  show goodRevokeRow.loc 0 = 0
  simp only [goodRevokeRow, SEL_REVOKE_DELEGATION, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodRevokeRow` REALIZES the runtime revoke intent. -/
theorem goodRevokeRow_realizes_intent : RevokeRowIntent goodRevokeRow := by
  unfold RevokeRowIntent
  have hnoop : goodRevokeRow.loc sel.NOOP = 0 := goodRevokeRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodRevokeRow.loc (saCol state.NONCE) = goodRevokeRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodRevokeRow, SEL_REVOKE_DELEGATION, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodRevokeRow.loc (saCol (state.FIELD_BASE + i)) = goodRevokeRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodRevokeRow, SEL_REVOKE_DELEGATION, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 30) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 30) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED revoke row: `goodRevokeRow` with the post-`bal_lo` minted to `999`. -/
def badRevokeRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodRevokeRow.loc v
  nxt := goodRevokeRow.nxt
  pub := goodRevokeRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badRevokeRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badRevokeRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badRevokeRow false false := by
  apply revokeVm_rejects_moved_balance
  simp only [badRevokeRow, goodRevokeRow, sbCol, saCol, SEL_REVOKE_DELEGATION, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE revoke row: `goodRevokeRow` with the post-nonce held at `5`. -/
def staleNonceRevokeRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodRevokeRow.loc v
  nxt := goodRevokeRow.nxt
  pub := goodRevokeRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceRevokeRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceRevokeRow false false := by
  apply revokeVm_rejects_nonce_freeze
  simp only [staleNonceRevokeRow, goodRevokeRow, sel.NOOP, sbCol, saCol, SEL_REVOKE_DELEGATION,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num


/-! ## §G — THE GENUINE CLASS-A `revoke` — `cap_root` RECOMPUTED in-row (inherits the shared primitive).

`revoke` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the GENUINE class-A descriptor
`attenuateVmDescriptorGenuine` (the opaque `param.CAP_DIGEST_NEW` move REPLACED by the FORCED in-row
recompute `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`). The
`revoke`-specific content is the OP tag `capOp.REVOKE` carried in the edge leaf (the cap-edge removal), plus the existing
connector to universe-A. We re-export the genuine soundness + edge-binding anti-ghost for `revoke`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuine attenuateGenuineRowGates CapCellSpecGenuine attenuateHashSites
   attenuateGenuine_sound attenuateGenuine_binds_edge CapRowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds)

/-- **`revokeVmDescriptorGenuine`** — the GENUINE `revoke` circuit: definitionally the shared genuine
cap-root-recompute descriptor (the opaque digest param is GONE; `cap_root` is FORCED in-row). -/
def revokeVmDescriptorGenuine : EffectVmDescriptor := attenuateVmDescriptorGenuine

/-- **`revokeGenuine_sound` — THE CLASS-A THEOREM for `revoke`.** Satisfying the genuine descriptor's
frame-freeze gates AND the in-row cap-root recompute forces the GENUINE full per-cell post-state:
`post.capRoot` is the FORCED advance `hash[edge_leaf, pre.capRoot]` (NOT an opaque parameter), every other
field frozen. Inherited from the shared `attenuateGenuine_sound`. -/
theorem revokeGenuine_sound (hash : List ℤ → ℤ) (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env pre post :=
  attenuateGenuine_sound hash env pre post capDigestNew henc hgates hrec

/-- **`revokeGenuine_binds_edge` — the genuine class-A anti-ghost for `revoke`.** Two genuine `revoke` rows
with EQUAL published `state_commit` share the old `cap_root` AND every bound edge field
(holder/target/rights/op) — so tampering the cap-edge mutation moves `cap_root`, moves `state_commit` ⇒
UNSAT. Inherited from the shared `attenuateGenuine_binds_edge`. -/
theorem revokeGenuine_binds_edge (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (e₁ e₂ : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hsCommit₁ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₁ attenuateHashSites)
    (hsCommit₂ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₂ attenuateHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP) :=
  attenuateGenuine_binds_edge hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hrec₁ hrec₂ hcommit

#assert_axioms revokeGenuine_sound
#assert_axioms revokeGenuine_binds_edge


/-! ## §11 — Axiom-hygiene tripwires. -/

#guard revokeVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard revokeVmDescriptor.hashSites.length == 4
#guard revokeVmDescriptor.traceWidth == 186

#assert_axioms revokeVm_faithful
#assert_axioms revokeVm_rejects_wrong_output
#assert_axioms revokeVm_rejects_moved_balance
#assert_axioms revokeVm_rejects_moved_capRoot
#assert_axioms revokeVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms revokeDescriptor_full_sound
#assert_axioms revokeDescriptor_commit_binds_state
#assert_axioms unify_revoke
#assert_axioms unify_revoke_via_full_sound
#assert_axioms goodRevokeRow_realizes_intent
#assert_axioms badRevokeRow_rejected
#assert_axioms staleNonceRevokeRow_rejected

/-! ## §W — THE MAGNESIUM LIFT: `revokeDelegation`'s RUNNABLE descriptor binds the FULL 17-field
post-state (on the EXISTING kernel; the `DELEG`-EPOCH advance is the reported residual).

`revokeDelegation` is a PASSTHROUGH+nonce-TICK cap-graph row (cap_root FROZEN on-row; the `caps` edge
removal rides OFF-row via `unify_revoke`). Its WIDE descriptor widens `revokeVmDescriptor` to
`EFFECT_VM_WIDTH_SYSROOTS` with `wideHashSites`, so the published `state_commit` now absorbs the
`system_roots` digest. The kernel step (`recKRevokeTarget`) edits ONLY `caps` — it does NOT touch the
`delegations`/`revoked` (`DELEG`) side-table — so on the EXISTING kernel the 8 side-table roots are
FROZEN, and the full clause is the per-cell `RevokeCellSpec` (frame frozen, nonce ticked) AND `postRoots =
preRoots`.

⚑ SCOPED CIRCUIT FOLLOW-UP (the `delegation_epoch` / `DELEG` advance — kernel CLOSED, circuit-binding
PENDING): dregg1's revokeDelegation bumps the parent's `delegation_epoch` + clears the child's snapshot.
The KERNEL now MODELS this faithfully via the dedicated step `recKRevokeDelegationFull` (`AuthTurn.lean
§3.EPOCH`, proved in `revokeKernel_models_runtime_epoch`). What remains is purely a CIRCUIT-binding step:
THIS lift's descriptor binds the shared cap-edge leg `recKRevokeTarget` (which frames the epoch), so on
that descriptor the `DELEG`/epoch sub-root is FROZEN. Routing the RUNNING RevokeDelegation descriptor onto
`recKRevokeDelegationFull` (so `state_commit` absorbs the advanced epoch) is the scoped follow-up;
`revoke_DELEG_epoch_residual` pins the precise boundary (kernel models it; this descriptor's cap-root leg
is epoch-independent), a checked fact, not a buried assumption. -/

open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound wide_rejects_root_tamper)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest N_SYSTEM_ROOTS emptySystemRoots)

/-- **`revokeDelegationVmDescriptorWide`** — the runnable `revokeDelegation` FULL-state circuit:
`revokeVmDescriptor` WIDENED to `EFFECT_VM_WIDTH_SYSROOTS` with `hashSites := wideHashSites`. Strictly
additive: the constraint list is byte-identical; only the width grows by 2 and site 3's spare slot becomes
the side-table digest carrier. -/
def revokeDelegationVmDescriptorWide : EffectVmDescriptor :=
  { revokeVmDescriptor with
    name := "dregg-effectvm-revokeDelegation-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide revoke descriptor's constraints ARE `revokeVmDescriptor`'s. -/
theorem revokeWide_constraints_eq :
    revokeDelegationVmDescriptorWide.constraints = revokeVmDescriptor.constraints := rfl

/-- **`RevokeFullClause`** — the FULL declarative revokeDelegation post-state: the per-cell
`RevokeCellSpec` (balance/cap_root/fields/reserved FROZEN, nonce TICKED) AND the `system_roots` sub-block
FROZEN (`postRoots = preRoots` — on the existing kernel, the `DELEG` epoch is not advanced; the `caps`
edge removal rides off-row). Non-vacuous: `revokeWide_realizes`. -/
def RevokeFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  RevokeCellSpec pre post ∧ postRoots = preRoots

/-- **`revokeRunnableSpec` — the revokeDelegation FULL-state RUNNABLE instance.** `decodeAfter` is
`RowEncodesRevoke` PLUS the frozen-roots witness; `decodeFull` projects the wide descriptor's
passthrough+tick gates (= revoke's) to `revokeVm_faithful` + `intent_to_cellSpec`, then carries the
frozen-roots fact. THIN + NON-VACUOUS. -/
def revokeRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := revokeDelegationVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsRevokeRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesRevoke env pre post ∧ postRoots = preRoots
  fullClause    := RevokeFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    obtain ⟨_hsel, hnoop⟩ := hrow
    have hgates' : ∀ c ∈ revokeRowGates, c.holdsVm env false false := by
      intro c hc
      have hmem : c ∈ revokeDelegationVmDescriptorWide.constraints := by
        show c ∈ revokeVmDescriptor.constraints
        unfold revokeVmDescriptor
        simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
      have hh := hgates c hmem
      unfold revokeRowGates gFieldPassAll at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
        simpa only [VmConstraint.holdsVm] using hh
    exact ⟨intent_to_cellSpec env pre post hnoop henc ((revokeVm_faithful env).mp hgates'), hroots⟩

/-- **`revokeDelegation_runnable_full_sound` — THE MAGNESIUM CROWN for `revokeDelegation`.** A row
satisfying the runnable `revokeDelegation` WIDE descriptor (`satisfiedVm`, first/last active), under the
structured decode, pins the FULL 17-field post-state: the per-cell frame freeze + nonce tick AND the
frozen `system_roots` sub-block (binding the 8 side-table roots). The `caps` edge removal is the named
OFF-ROW `unify_revoke` connector; the `DELEG`-epoch advance is the reported residual (frozen here). -/
theorem revokeDelegation_runnable_full_sound (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsRevokeRow env)
    (henc : RowEncodesRevoke env pre post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash revokeDelegationVmDescriptorWide env true true) :
    RevokeFullClause preRoots pre post postRoots :=
  runnable_full_sound (revokeRunnableSpec preRoots) hash env pre post postRoots
    hrow ⟨henc, hroots⟩ hsat

/-- **`revokeDelegation_runnable_rejects_root_tamper` — the side-table anti-ghost for `revokeDelegation`.**
Two wide revoke rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table
sub-blocks DIFFER at some index cannot both satisfy — UNSAT. The 8 side-table roots (incl. `DELEG`) are
bound by the runnable commitment (so a forged frozen-`DELEG` is rejected; an HONEST advance would require
the kernel-widen wave to MOVE it, the reported residual). -/
theorem revokeDelegation_runnable_rejects_root_tamper (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash revokeDelegationVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash revokeDelegationVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (revokeRunnableSpec preRoots) hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`revokeWide_realizes` — NON-VACUITY (witness TRUE).** A real passthrough+tick revoke cell transition
(frame frozen, nonce `5 → 6`) with frozen roots inhabits `RevokeFullClause`. -/
theorem revokeWide_realizes :
    RevokeCellSpec
      { balLo := 0, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 0,
        commit := 0 }
      { balLo := 0, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 9, reserved := 0,
        commit := 0 } :=
  ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-- **`revokeWide_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
nonce did NOT tick FAILS `RevokeCellSpec` — the clause is not vacuously true. -/
theorem revokeWide_clause_not_trivial :
    ¬ RevokeCellSpec
        { balLo := 0, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 0,
          commit := 0 }
        { balLo := 0, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 0,
          commit := 0 } := by
  rintro ⟨_, _, hnon, _⟩
  exact absurd hnon (by decide)

/-- **`revoke_DELEG_epoch_residual` — the precise boundary, as a checked theorem (kernel CLOSED;
circuit-binding scoped).** Two facts, both PROVED:

  (a) **the KERNEL models the epoch** — the faithful full delegation-revoke step
      `recKRevokeDelegationFull k parent child` ADVANCES the parent's `delegationEpoch` by EXACTLY `+1`
      (`revokeKernel_models_runtime_epoch`); the divergence is CLOSED at the kernel layer;

  (b) **this lift's cap-root leg is epoch-INDEPENDENT** — the shared cap-edge `recKRevokeTarget` (which
      THIS descriptor binds) reads/writes ONLY `caps`, so the EffectVM-row `cap_root` digest `capRootProj
      D` is unchanged by the `delegations`/epoch sub-table: two states with identical `caps` but DIFFERENT
      `delegations` share a `cap_root` yet differ on the `DELEG` root.

So binding the (kernel-modeled) epoch advance into the RUNNING descriptor requires routing it onto
`recKRevokeDelegationFull` + carrying the `DELEG` sub-root through `state_commit` — the scoped circuit
follow-up. Pinned so neither the close (a) nor the remaining binding (b) is a buried assumption. -/
theorem revoke_DELEG_epoch_residual (D : Caps → ℤ)
    (k : RecordKernelState) (parent child : CellId)
    (g₁ g₂ : CellId → List Cap) (hne : D g₁ ≠ D g₂) :
    -- (a) the kernel CLOSES the epoch: the faithful full step advances the parent epoch by +1.
    (recKRevokeDelegationFull k parent child).delegationEpoch parent = k.delegationEpoch parent + 1
    -- (b) this descriptor's cap-root leg is epoch/`DELEG`-independent (the scoped circuit-binding boundary).
    ∧ capRootProj D { k with delegations := g₁ } = capRootProj D { k with delegations := g₂ }
    ∧ D ({ k with delegations := g₁ } : RecordKernelState).delegations
        ≠ D ({ k with delegations := g₂ } : RecordKernelState).delegations := by
  refine ⟨recKRevokeDelegationFull_bumps_parent_epoch k parent child, ?_, hne⟩
  show D ({ k with delegations := g₁ } : RecordKernelState).caps
      = D ({ k with delegations := g₂ } : RecordKernelState).caps
  rfl

#assert_axioms revokeWide_constraints_eq
#assert_axioms revokeDelegation_runnable_full_sound
#assert_axioms revokeDelegation_runnable_rejects_root_tamper
#assert_axioms revokeWide_realizes
#assert_axioms revokeWide_clause_not_trivial
#assert_axioms revoke_DELEG_epoch_residual

#guard revokeDelegationVmDescriptorWide.traceWidth == 188
#guard revokeDelegationVmDescriptorWide.hashSites.length == 4

end Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
