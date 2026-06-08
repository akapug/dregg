/-
# Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend — the apply-time-neutral clock tick `pipelinedSendA`,
  EMITTED onto the runnable EffectVM row as a FULL state-block FREEZE, with the supported per-row
  faithfulness + anti-ghost commitment tooth + the connector to universe-A `pipelinedSendA_full_sound`,
  and a PRECISE, LOUD flag of the one IR-blocked part (the off-block log-receipt).

## The supported part vs where the per-row IR STOPS

`pipelinedSendA actor` is TOTAL (no fail-closed guard) and LOG-ONLY: it prepends one NEUTRAL receipt
to the log and LITERALLY FREEZES the ENTIRE kernel — ALL 17 `RecordKernelState` fields unchanged
(`PipelinedSendSpec`: `st'.log = pipelinedSendReceipt actor :: st.log` ∧ all 17 kernel fields frozen).
Validation `pipelinedSendA_full_sound ⇒ PipelinedSendSpec` is DONE (`Inst/pipelinedSendA.lean`).

This is the CLEANEST swiss-family effect for the per-row IR: the kernel is FROZEN, so at the row level
the supported part is a FULL STATE-BLOCK FREEZE — every one of the 14 state columns (balance limbs,
nonce, 8 fields, `cap_root`/`swiss_root`, reserved, `state_commit`) has `after = before`. The EffectVM
row layout expresses this TOTALLY (no digest move, no guard, no list structure to express). The
published `state_commit` is the genuine digest of the (unchanged) after-state, bound under Poseidon2 CR
exactly as the keystone binds it. `pipelinedSendVmDescriptor` emits the full-freeze gate set + GROUP-4
commitment.

## The CONNECTOR — to universe-A's `pipelinedSendA_full_sound`

Since `PipelinedSendSpec` freezes ALL 17 kernel fields, EVERY projection of the post-kernel equals the
projection of the pre-kernel. `unify_pipelinedSend` shows the swiss-table digest (and, by the same
argument, the cap-table digest and the balance) are FROZEN across a committed `pipelinedSendA` — i.e.
the runnable row's FREEZE intent IS universe-A's whole-kernel freeze, projected to the columns. Not a
fourth spec.

## ===================  IR-BLOCKED — the precise ask  ===================

  * **IR GAP — the off-block log-receipt (`st'.log = pipelinedSendReceipt actor :: st.log`).** The
    pipelinedSend's ONLY state change is the LOG — and the EffectVM row's 14-column state block has NO
    log column (the log is a SEPARATE `RecChainedState` component, committed by universe-A's
    `logHashInjective LH` portal, not by the per-row state block). So the descriptor pins the KERNEL
    freeze (the whole state block) + the commitment binding, but does NOT carry the log-receipt prepend
    in-circuit; that lives in universe-A's `pipelinedSendA_full_sound` (carried). ASK: a `VmConstraint`
    log-receipt form (a dedicated log-digest column with `new_log_root = H(receipt, old_log_root)`)
    would internalize the log update; until then the receipt prepend is enforced only out-of-band. NOTE
    this gap is BENIGN for the freeze content — the kernel-freeze (the soundness-load-bearing part:
    "nothing in the kernel moved") IS fully in-circuit; only the additive log-receipt is off-block.

  * PER-CELL / PER-ROW; `state.RESERVED` absorbed nowhere (inherited keystone finding) — but here
    `reserved` is FROZEN by its passthrough gate, the same as every other column.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR
hash`; the kernel-field projections enter ONLY as abstract functions of the frozen post-kernel. No
`sorry`/`:= True`/`native_decide`/`rfl`-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.pipelinedSendA

namespace Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop site0 site1 transitionAll boundaryFirstPins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective cellLeafInjective RestHashIffFrame AccountsWF)
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE encodeE)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector offset. The pipelined-send tick has its own per-effect selector. -/

namespace selPS
/-- The `pipelinedSendA` effect selector column. -/
def PIPELINED_SEND : Nat := 7
end selPS

/-- The `pipelinedSendA` selector as an expression. -/
def eSelPipelinedSend : EmittedExpr := .var selPS.PIPELINED_SEND

/-! ## §1 — The pipelined-send row gates (the SUPPORTED part: a FULL state-block FREEZE). -/

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body. -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
/-- Cap-root (swiss_root) freeze body. -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
/-- Field-`i` freeze body. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `pipelinedSendA` AIR identity. -/
def pipelinedSendVmAirName : String := "dregg-effectvm-pipelinedSendA-v1"

/-- The pipelined-send per-row gates: the FULL state-block FREEZE (every data column `after =
before`). -/
def pipelinedSendRowGates : List VmConstraint :=
  [ .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix, .gate gCapFix, .gate gResFix ] ++ gFieldFixAll

/-- The ordered GROUP-4 hash sites (identical chain to the transfer keystone; binds the unchanged
after-state into `state_commit`). -/
def pipelinedSendHashSites : List VmHashSite :=
  [site0, site1, Dregg2.Circuit.Emit.EffectVmEmitTransfer.site2,
   Dregg2.Circuit.Emit.EffectVmEmitTransfer.site3]

/-- **`pipelinedSendVmDescriptor`** — the `pipelinedSendA` SUPPORTED concrete circuit: the FULL
state-block freeze gates ++ transition continuity ++ row-0 boundary pins, with the 4 GROUP-4 hash
sites. The log-receipt prepend is IR-BLOCKED (header), NOT in this descriptor. -/
def pipelinedSendVmDescriptor : EffectVmDescriptor :=
  { name := pipelinedSendVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := pipelinedSendRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := pipelinedSendHashSites
  , ranges := [] }

/-! ## §3 — The pipelined-send ROW INTENT (the SUPPORTED faithfulness target: a full freeze). -/

/-- **`PipelinedSendRowIntent env`** — the FULL state-block freeze: every data column frozen. -/
def PipelinedSendRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a pipelined-send row: `s_pipelinedSend = 1`, `s_noop = 0`. -/
def IsPipelinedSendRow (env : VmRowEnv) : Prop :=
  env.loc selPS.PIPELINED_SEND = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

/-- **`pipelinedSendRowGates_holds_iff`** — on a pipelined-send row, the gates all hold IFF
`PipelinedSendRowIntent` holds (the full freeze). -/
theorem pipelinedSendRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ pipelinedSendRowGates, c.holdsVm env false false) ↔ PipelinedSendRowIntent env := by
  unfold pipelinedSendRowGates gFieldFixAll PipelinedSendRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFix, gBalHiFix, gNonceFix, gCapFix, gResFix,
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨by linarith [hLo], by linarith [hHi], by linarith [hNon], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **`pipelinedSendVm_faithful` — THE supported deliverable.** -/
theorem pipelinedSendVm_faithful (env : VmRowEnv) :
    (∀ c ∈ pipelinedSendRowGates, c.holdsVm env false false) ↔ PipelinedSendRowIntent env :=
  pipelinedSendRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row): any state-column MOVE fails the freeze. -/

/-- **Anti-ghost (cap_root/swiss_root tamper).** A row whose post-`cap_root` is NOT its pre-`cap_root`
fails the `gCapFix` freeze gate (UNSAT) — a pipelined-send may not move the swiss/cap digest. -/
theorem pipelinedSendVm_rejects_moved_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapFix).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (balance tamper).** A row whose post-`bal_lo` is NOT its pre-`bal_lo` fails the
`gBalLoFix` freeze gate — a pipelined-send is balance-neutral. -/
theorem pipelinedSendVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFix).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the full freeze does NOT satisfy the per-row
gates. -/
theorem pipelinedSendVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ PipelinedSendRowIntent env) :
    ¬ (∀ c ∈ pipelinedSendRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((pipelinedSendVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness: the post `CellState` EQUALS the pre `CellState`. -/

/-- **`RowEncodes env pre post`** — the row decodes to `(pre, post)` cell states (no params). -/
def RowEncodes (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell freeze spec: the post-state's data columns are ALL equal to the pre-state's. -/
def CellFreezeSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ post.capRoot = pre.capRoot
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `RowEncodes`, `PipelinedSendRowIntent` IS the structured per-cell `CellFreezeSpec`. -/
theorem intent_to_cellFreezeSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodes env pre post) (hint : PipelinedSendRowIntent env) :
    CellFreezeSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hlo, hhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`pipelinedSendDescriptor_full_sound` — the structured soundness (supported part).** Satisfying the
per-row gates under `RowEncodes` forces the structured per-cell `CellFreezeSpec` (the whole cell state
frozen). -/
theorem pipelinedSendDescriptor_full_sound (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodes env pre post)
    (hgates : ∀ c ∈ pipelinedSendRowGates, c.holdsVm env false false) :
    CellFreezeSpec pre post :=
  intent_to_cellFreezeSpec env pre post henc ((pipelinedSendVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `pipelinedSendHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem pipelinedSendHashSites_eq : pipelinedSendHashSites = transferHashSites := rfl

/-- **`pipelinedSendDescriptor_commit_binds_state` — the whole-state tooth.** Two pipelined-send rows
that satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns. -/
theorem pipelinedSendDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ pipelinedSendHashSites)
    (hs₂ : siteHoldsAll hash e₂ pipelinedSendHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [pipelinedSendHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — to universe-A's `pipelinedSendA_full_sound`.

`PipelinedSendSpec` freezes ALL 17 kernel fields, so EVERY projection of the post-kernel equals the
projection of the pre-kernel. We exhibit the swiss-table digest (and by the same argument any
projection) FROZEN across a committed `pipelinedSendA` — the runnable row's freeze IS universe-A's
whole-kernel freeze, projected. -/

open Dregg2.Circuit.Inst.PipelinedSendA (PipelinedSendArgs)
open Dregg2.Circuit.Spec.QueuePipelinedSend (PipelinedSendSpec)

/-- **`swissRootProj D k`** — the EffectVM `swiss_root` column value: the whole-list digest `D`. -/
def swissRootProj (D : List SwissRecord → ℤ) (k : RecordKernelState) : ℤ := D k.swiss

/-- **`unify_pipelinedSend` — THE CONNECTOR (swiss leg).** When universe-A's `PipelinedSendSpec` holds,
`s'.kernel.swiss = s.kernel.swiss` (the swiss-freeze clause), so the projected `swiss_root` is FROZEN:
`swissRootProj D s'.kernel = swissRootProj D s.kernel`. The runnable row's freeze IS universe-A's
whole-kernel freeze, projected to the swiss-digest column. -/
theorem unify_pipelinedSend (D : List SwissRecord → ℤ)
    (s : RecChainedState) (actor : CellId) (s' : RecChainedState)
    (hspec : PipelinedSendSpec s actor s') :
    swissRootProj D s'.kernel = swissRootProj D s.kernel := by
  -- PipelinedSendSpec's `swiss` clause is `s'.kernel.swiss = s.kernel.swiss`.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hSw, _⟩ := hspec
  show D s'.kernel.swiss = D s.kernel.swiss
  rw [hSw]

/-- **`unify_pipelinedSend_via_full_sound` — the runnable freeze inherits the VALIDATED guarantee.**
A satisfying universe-A `pipelinedSendA_full_sound` witness ⟹ `PipelinedSendSpec` ⟹ the projected
`swiss_root` is FROZEN. So the runnable freeze is universe-A's validated whole-kernel freeze, not a
fourth spec. (The additive log-receipt stays enforced ONLY inside the full_sound — IR-BLOCKED at the
row, header.) -/
theorem unify_pipelinedSend_via_full_sound
    (S : CommitSurface) (D : List SwissRecord → ℤ)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendE
        (encodeE S Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendE s args s')) :
    swissRootProj D s'.kernel = swissRootProj D s.kernel :=
  unify_pipelinedSend D s args.actor s'
    (Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendA_full_sound S hN hL hRest hLog s args s' hwf hwf' h)

/-! ## §9 — NON-VACUITY. -/

/-- A concrete pipelined-send row: every column frozen (pre = post = 0 everywhere; the selector hot). -/
def freezeRow : VmRowEnv where
  loc := fun v => if v = selPS.PIPELINED_SEND then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `freezeRow` is a genuine pipelined-send row. -/
theorem freezeRow_isPipelinedSendRow : IsPipelinedSendRow freezeRow := by
  unfold IsPipelinedSendRow freezeRow
  constructor <;> norm_num [selPS.PIPELINED_SEND, sel.NOOP]

/-- **NON-VACUITY (witness TRUE).** `freezeRow` REALIZES the full-freeze intent: every `after` column
equals its `before` column (both `0`, since no state column is named). -/
theorem freezeRow_realizes_intent : PipelinedSendRowIntent freezeRow := by
  -- every state column index ≠ selPS.PIPELINED_SEND (= 7); a state column's after/before both hit the
  -- `else 0` branch. State columns are ≥ 54 (STATE_BEFORE_BASE), so all ≠ 7.
  have hcol : ∀ col : Nat, col ≠ selPS.PIPELINED_SEND → freezeRow.loc col = 0 := by
    intro col hc
    show (if col = selPS.PIPELINED_SEND then (1:ℤ) else 0) = 0
    rw [if_neg hc]
  have hsb : ∀ off : Nat, (sbCol off ≠ selPS.PIPELINED_SEND) := by
    intro off
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS selPS.PIPELINED_SEND; omega
  have hsa : ∀ off : Nat, (saCol off ≠ selPS.PIPELINED_SEND) := by
    intro off
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      selPS.PIPELINED_SEND; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcol _ (hsa _), hcol _ (hsb _)]
  · rw [hcol _ (hsa _), hcol _ (hsb _)]
  · rw [hcol _ (hsa _), hcol _ (hsb _)]
  · rw [hcol _ (hsa _), hcol _ (hsb _)]
  · rw [hcol _ (hsa _), hcol _ (hsb _)]
  · intro i hi; rw [hcol _ (hsa _), hcol _ (hsb _)]

/-- A forged pipelined-send row: `freezeRow` with post-`cap_root` moved to `999` (≠ its frozen pre
`0`). -/
def movedRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else freezeRow.loc v
  nxt := freezeRow.nxt
  pub := freezeRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `movedRow` moves the `cap_root`/`swiss_root`
column (`0 → 999`), so the `gCapFix` freeze gate REJECTS it — a concrete UNSAT (a pipelined-send may
not move any kernel digest). -/
theorem movedRow_rejected : ¬ (VmConstraint.gate gCapFix).holdsVm movedRow false false := by
  apply pipelinedSendVm_rejects_moved_capRoot
  -- post cap_root = 999 (overwrite); pre cap_root: sbCol CAP_ROOT (=65) ≠ saCol CAP_ROOT (=87) and
  -- ≠ selPS (=7), so it is `else 0`. 999 ≠ 0.
  have hsbcap : sbCol state.CAP_ROOT = 65 := by
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.CAP_ROOT; rfl
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have rsa : movedRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ) else freezeRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have rsb : movedRow.loc (sbCol state.CAP_ROOT) = 0 := by
    show (if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ) else freezeRow.loc (sbCol state.CAP_ROOT)) = 0
    have hne : ¬ (sbCol state.CAP_ROOT = saCol state.CAP_ROOT) := by rw [hsbcap, hsacap]; decide
    rw [if_neg hne]
    show (if sbCol state.CAP_ROOT = selPS.PIPELINED_SEND then (1:ℤ) else 0) = 0
    have hne2 : ¬ (sbCol state.CAP_ROOT = selPS.PIPELINED_SEND) := by
      rw [hsbcap]; unfold selPS.PIPELINED_SEND; decide
    rw [if_neg hne2]
  rw [rsa, rsb]; decide

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard pipelinedSendVmDescriptor.constraints.length == 13 + 14 + 4
#guard pipelinedSendVmDescriptor.hashSites.length == 4
#guard pipelinedSendVmDescriptor.traceWidth == 186

#assert_axioms pipelinedSendRowGates_holds_iff
#assert_axioms pipelinedSendVm_faithful
#assert_axioms pipelinedSendVm_rejects_moved_capRoot
#assert_axioms pipelinedSendVm_rejects_moved_balance
#assert_axioms pipelinedSendVm_rejects_wrong_output
#assert_axioms intent_to_cellFreezeSpec
#assert_axioms pipelinedSendDescriptor_full_sound
#assert_axioms pipelinedSendDescriptor_commit_binds_state
#assert_axioms unify_pipelinedSend
#assert_axioms unify_pipelinedSend_via_full_sound
#assert_axioms freezeRow_realizes_intent
#assert_axioms movedRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
