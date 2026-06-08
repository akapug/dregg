/-
# Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize — the bridgeFinalize (bridge-outbound-FINALIZE)
effect's concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

This is the bridge-group analogue of `EffectVmEmitTransfer` + `…TransferSound` + `…TransferUnify`,
built for `bridgeFinalizeA`. Universe A (`Spec/bridgeoutboundfinalize.lean`) carries the FULL-state
soundness `bridgeFinalizeChainA_iff_spec ⇒ BridgeFinalizeSpec`: a committed finalize is the §8
confirmation arriving from the other chain — the parked value genuinely LEFT, a no-credit OUTFLOW. Its
ONLY touched kernel field is `escrows` (`markResolved … id`); `bal` is FRAMED-UNCHANGED (the value
already departed the per-cell ledger at LOCK time), as are the other 15 kernel fields, plus the log
advances by one escrow receipt.

## What the EffectVM IR (a 14-column state block + GROUP-4 commitment) DOES support for bridgeFinalize

The conserved `bal` measure is FROZEN: a finalize performs NO `bal` move at all (the honest contrast
with cancel/release, which credit). So on the EffectVM row the originator cell's `state.BALANCE_LO`
limb is UNCHANGED — a pure FREEZE, exactly the transfer-row frame-freeze with the move dropped. The
nonce is likewise FROZEN (the executor rewrites neither `bal` nor `nonce` on a finalize), and the whole
frame (bal_hi/cap_root/reserved/8 fields) is frozen. The GROUP-4 commitment chain binds the whole
after-state block into `state_commit` exactly as for transfer (the post-state IS the pre-state on every
data column).

So bridgeFinalize is the DEGENERATE balance case: `post.balLo = pre.balLo` (no delta). The IR carries
it totally — every column frozen — and the commitment binds the whole 14-column block.

## THE IR-EXTENSION FLAG (the escrows set-membership / resolve leg)

`BridgeFinalizeSpec`'s entire SEMANTIC content is the `escrows := markResolved … id` update — a
SET-MEMBERSHIP / list-digest mutation flipping the parked record's `resolved` flag. The EffectVM
14-column state block has NO escrow-root column, and the GROUP-4 hash-sites absorb NONE of the escrows
list. So the IR as it stands CANNOT bind the escrows resolve into `state_commit`.

  ⇒ **needs IR extension: an escrows-list-root column in the EffectVM state block (a 15th data column,
     or repurposing one named field as `ESCROW_ROOT`) absorbed by a new hash-site, so the
     `markResolved` update is bound into the published `state_commit`.** Universe A binds it via the
     `escrows` list equality; the EffectVM row has no counterpart column. This module proves what the
     IR DOES support (the whole-balance/frame FREEZE + the 14-column commitment) and reports the
     escrows resolve as out-of-IR — NOT papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.bridgeoutboundfinalize

namespace Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   site0 site1 site2 site3 transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The bridgeFinalize selector.

The EffectVM layout names `sel.NOOP = 0`, `sel.TRANSFER = 1`; the bridge-outbound-finalize effect takes
the next free selector column (a LAYOUT CHOICE local to this descriptor — the running prover's
`columns.rs` would assign it; we keep the index explicit so the emitted gates are selector-specialized
exactly as the transfer template specializes on `s_transfer`). A finalize takes NO move parameter — it
moves nothing. -/

/-- The bridge-outbound-finalize selector column index. -/
def SEL_BRIDGE_FINALIZE : Nat := 3

/-- The finalize row is a bridge-finalize row: `s_bridge_finalize = 1`, `s_noop = 0`. -/
def IsBridgeFinalizeRow (env : VmRowEnv) : Prop :=
  env.loc SEL_BRIDGE_FINALIZE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The bridgeFinalize per-row gate bodies (FULL freeze, term-for-term).

A finalize moves NO value: the conserved `bal_lo` limb is FROZEN (no debit/credit), the nonce is
FROZEN, and the whole frame (bal_hi/cap_root/reserved/8 fields) is FROZEN. So EVERY data column is the
transfer-template freeze polynomial `after − before`. -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (a finalize moves nothing on the ledger). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the finalize leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted bridgeFinalize descriptor. -/

/-- The bridge-outbound-finalize AIR identity. -/
def bridgeFinalizeVmAirName : String := "dregg-effectvm-bridgefinalize-v1"

/-- The bridge-finalize per-row gates: balance freeze, bal_hi freeze, nonce freeze, cap/reserved
freeze, 8 fields freeze. -/
def bridgeFinalizeRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`bridgeFinalizeVmDescriptor`** — the bridgeFinalize effect's concrete EffectVM circuit: the
per-row full-freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered
GROUP-4 hash sites (REUSED — the post-state commitment chain is the SAME 14-column binding) and the 2
balance-limb range checks. -/
def bridgeFinalizeVmDescriptor : EffectVmDescriptor :=
  { name := bridgeFinalizeVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeFinalizeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The bridgeFinalize ROW INTENT (the independent faithfulness target). -/

/-- **`BridgeFinalizeRowIntent env`** — the intended finalize move on the row `env.loc`: NOTHING moves.
The balance limbs, the nonce, and the whole frame are all FIXED. This is the EffectVM-row projection of
`BridgeFinalizeSpec`'s `bal`-frame (no-credit outflow) + the per-cell frame freeze. -/
def BridgeFinalizeRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`bridgeFinalizeVm_faithful`.** On a bridge-finalize row, the emitted descriptor's per-row gates
all hold IFF `BridgeFinalizeRowIntent` holds — the gates pin EXACTLY the full freeze. -/
theorem bridgeFinalizeVm_faithful (env : VmRowEnv) :
    (∀ c ∈ bridgeFinalizeRowGates, c.holdsVm env false false) ↔ BridgeFinalizeRowIntent env := by
  unfold bridgeFinalizeRowGates gFieldPassAll BridgeFinalizeRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, ePrm, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a wrong-output finalize row fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A finalize row whose post-state is NOT the full freeze (any moved limb,
ticked nonce, tampered frame) does NOT satisfy the per-row gates. -/
theorem bridgeFinalizeVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ BridgeFinalizeRowIntent env) :
    ¬ (∀ c ∈ bridgeFinalizeRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((bridgeFinalizeVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A finalize row whose post-`bal_lo` is NOT the frozen value
(claiming a phantom credit/debit) has no satisfying gate set — the `gBalLoFreeze` gate alone rejects it
(UNSAT). This is the no-credit-outflow tooth: a finalize cannot smuggle a balance move. -/
theorem bridgeFinalizeVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + the keystone soundness (REUSING `CellState`). -/

/-- The (empty) finalize parameters — a finalize carries no move magnitude. -/
structure FinalizeParams where
  dummy : Unit := ()

/-- `RowEncodesFinalize env pre post` ties the row's state-block columns to a `(pre, post)` cell
transition (the finalize's `RowEncodes` analogue: no param). -/
def RowEncodesFinalize (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellFinalizeSpec pre post`** — the per-cell FULL-state finalize spec: the WHOLE cell state is
FROZEN (balLo, balHi, nonce, the 8 fields, capRoot, reserved all literally unchanged). This is the
EffectVM-row projection of `BridgeFinalizeSpec`'s `bal`-frame (no-credit outflow) on the cell. -/
def CellFinalizeSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesFinalize`, `BridgeFinalizeRowIntent` IS the structured
`CellFinalizeSpec`. -/
theorem intent_to_cellFinalizeSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesFinalize env pre post) (hint : BridgeFinalizeRowIntent env) :
    CellFinalizeSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §7 — The full descriptor soundness (gates + boundary) + the commitment binding (REUSED). -/

/-- **`bridgeFinalizeDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor (gates +
transitions + boundaries + hash sites), under the `RowEncodesFinalize` decoding, forces the structured
per-cell `CellFinalizeSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem bridgeFinalizeDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesFinalize env pre post)
    (hsat : satisfiedVm hash bridgeFinalizeVmDescriptor env true true) :
    CellFinalizeSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ bridgeFinalizeRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ bridgeFinalizeVmDescriptor.constraints := by
      unfold bridgeFinalizeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold bridgeFinalizeRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (bridgeFinalizeVm_faithful env).mp hgates'
  refine ⟨intent_to_cellFinalizeSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ bridgeFinalizeVmDescriptor.constraints := by
      unfold bridgeFinalizeVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §8 — The anti-ghost commitment tooth (REUSED from the transfer keystone, hash sites identical). -/

/-- **`bridgeFinalizeDescriptor_commit_binds_state`** — the keystone anti-ghost for bridgeFinalize: two
descriptor-satisfying finalize rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns. So a prover cannot keep `NEW_COMMIT` while tampering any absorbed cell of the frozen
post-state. -/
theorem bridgeFinalizeDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash bridgeFinalizeVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeFinalizeVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash bridgeFinalizeVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ bridgeFinalizeVmDescriptor.constraints := by
        unfold bridgeFinalizeVmDescriptor
        simp only [List.mem_append]
        exact Or.inr hc
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

/-! ## §9 — CONNECTOR to universe-A: `CellFinalizeSpec` IS `BridgeFinalizeSpec`'s per-cell bal image.

`bridgeFinalizeChainA_iff_spec ⇒ BridgeFinalizeSpec` carries the `bal`-FRAME clause (`s'.kernel.bal =
s.kernel.bal`, the no-credit outflow). We project ANY cell of the kernel `bal` ledger into the keystone
`CellState` (the conserved `balLo` limb reads the per-asset entry `bal c asset`; the EffectVM limbs
with no universe-A analogue — balHi/fields/capRoot/reserved — are `0`, FROZEN), and prove the
projection satisfies `CellFinalizeSpec` EXACTLY: every column frozen, because `bal' = bal`.

The DIVERGENCE pattern: the escrows-resolve (`markResolved`) is NOT in this per-cell projection (no
escrow column in the EffectVM block — the §IR-extension flag). And `BridgeFinalizeSpec`'s `bal`-frame
is a WHOLE-function equality; the per-cell projection reads the `(c, asset)` entry of it. -/

open Dregg2.Exec (RecordKernelState RecChainedState CellId AssetId)
open Dregg2.Circuit.Spec.BridgeOutboundFinalize (BridgeFinalizeSpec finalize_bal_neutral)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). The other EffectVM limbs have no universe-A analogue on the conserved ledger entry, so
they are `0` (frozen). -/
def cellProjFinalize (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_finalize_freeze`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`BridgeFinalizeSpec` post-state, satisfies the keystone's `CellFinalizeSpec` EXACTLY: `balLo` is FROZEN
(`bal' = bal`); balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen. So `CellFinalizeSpec` IS
`BridgeFinalizeSpec`'s per-cell `bal` image (a pure freeze — NOT a fourth spec). -/
theorem unify_finalize_freeze (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (asset0 : AssetId) (amount0 : ℤ) (c : CellId) (asset : AssetId)
    (hspec : BridgeFinalizeSpec s id actor asset0 amount0 s') :
    CellFinalizeSpec (cellProjFinalize s.kernel.bal c asset)
      (cellProjFinalize s'.kernel.bal c asset) := by
  have hbal : s'.kernel.bal = s.kernel.bal := finalize_bal_neutral s id actor asset0 amount0 s' hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal c asset = s.kernel.bal c asset
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_finalize`** — a satisfying run of the runnable descriptor
encoding any cell of a committed finalize agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= the frozen pre value) equals the executor's frozen `bal c asset`,
and the frozen frame agrees. The escrows-resolve is out-of-IR (reported as the §IR flag). -/
theorem descriptor_agrees_with_executor_finalize
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (id : Nat) (actor : CellId) (asset0 : AssetId) (amount0 : ℤ)
    (c : CellId) (asset : AssetId) (post : CellState)
    (henc : RowEncodesFinalize env (cellProjFinalize s.kernel.bal c asset) post)
    (hsat : satisfiedVm hash bridgeFinalizeVmDescriptor env true true)
    (hspec : BridgeFinalizeSpec s id actor asset0 amount0 s') :
    post.balLo = (cellProjFinalize s'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjFinalize s'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjFinalize s'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjFinalize s'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjFinalize s'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := bridgeFinalizeDescriptor_full_sound hash env
    (cellProjFinalize s.kernel.bal c asset) post henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_finalize_freeze s s' id actor asset0 amount0 c asset hspec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — NON-VACUITY: a concrete finalize row realizes the intent; a forged one is rejected. -/

/-- A concrete finalize row: `bal_lo 100 → 100` (FROZEN), nonce 5 → 5 (FROZEN), frame fixed at 0. -/
def goodFinalizeRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_BRIDGE_FINALIZE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodFinalizeRow` REALIZES the finalize intent: bal_lo `100 → 100`
(frozen), nonce frozen `5 → 5`, frame fixed. -/
theorem goodFinalizeRow_realizes_intent : BridgeFinalizeRowIntent goodFinalizeRow := by
  unfold BridgeFinalizeRowIntent goodFinalizeRow
  simp only [sbCol, saCol, prmCol, SEL_BRIDGE_FINALIZE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 3) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have f1 : (54 + (3 + i) = 3) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED finalize row: `goodFinalizeRow` with the post-`bal_lo` tampered to `999` (a phantom
credit, not the frozen `100`). -/
def badFinalizeRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodFinalizeRow.loc v
  nxt := goodFinalizeRow.nxt
  pub := goodFinalizeRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badFinalizeRow`'s post-`bal_lo` is NOT the
frozen value (a smuggled credit), so the `gBalLoFreeze` gate REJECTS it — a concrete UNSAT. -/
theorem badFinalizeRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badFinalizeRow false false := by
  apply bridgeFinalizeVm_rejects_wrong_balance
  simp only [badFinalizeRow, goodFinalizeRow, sbCol, saCol, prmCol, SEL_BRIDGE_FINALIZE,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §12 — Axiom-hygiene pins. -/

#guard bridgeFinalizeVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard bridgeFinalizeVmDescriptor.hashSites.length == 4
#guard bridgeFinalizeVmDescriptor.traceWidth == 186

#assert_axioms bridgeFinalizeVm_faithful
#assert_axioms bridgeFinalizeVm_rejects_wrong_output
#assert_axioms bridgeFinalizeVm_rejects_wrong_balance
#assert_axioms intent_to_cellFinalizeSpec
#assert_axioms bridgeFinalizeDescriptor_full_sound
#assert_axioms bridgeFinalizeDescriptor_commit_binds_state
#assert_axioms unify_finalize_freeze
#assert_axioms descriptor_agrees_with_executor_finalize
#assert_axioms goodFinalizeRow_realizes_intent
#assert_axioms badFinalizeRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize
