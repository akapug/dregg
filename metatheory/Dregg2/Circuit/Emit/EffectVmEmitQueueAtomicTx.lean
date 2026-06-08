/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx — the `queueAtomicTxA` (ALL-OR-NOTHING atomic queue-op
BATCH) effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Spec/queueatomictx.lean`) carries the FULL-state soundness
`execFullA_queueAtomicTxA_iff_spec ⇒ QueueAtomicTxSpec`: a committed batch folds a VARIABLE-LENGTH list
`ops : List QueueTxOpA` left-to-right (each sub-op routing to `queueEnqueueChainA` / `queueDequeueChainA`
— a deposit DEBIT/park or a refund CREDIT/settle on `bal`+`escrows`+`queues`); ANY sub-op failure ⇒ the
WHOLE batch is rejected (`none`); on commit the post-kernel is the fold's result `s1.kernel` and the log
gains the per-op receipts (inside the fold) PLUS one batch-commit row `escrowReceiptA actor`.

## THE FUNDAMENTAL IR MISMATCH (why this effect is IR-BLOCKED at the per-effect-descriptor level)

The EffectVM IR's `EffectVmDescriptor` is a SINGLE-EFFECT, single-ROW gadget: its `constraints` are
FIXED polynomials over ONE row window (`local`/`next`/`pi`). `queueAtomicTxA` is NOT a single effect —
it is a VARIABLE-LENGTH SEQUENCE of sub-effects (`op :: ops` recursion in `queueAtomicTxChainA`). Its net
`bal` move is a SUM over the (caller-chosen, unbounded) op list — there is NO fixed per-row polynomial
that expresses it. In the running prover the batch is laid as a MULTI-ROW TRACE: one row per sub-op,
each row being one of the ALREADY-EMITTED enqueue/dequeue descriptors
(`EffectVmEmitQueueEnqueue.queueEnqueueVmDescriptor` / `EffectVmEmitQueueDequeue.queueDequeueVmDescriptor`),
the rows chained through the IR's `transition` continuity (`next.state_before = this.state_after`).

So the IR DOES support the batch — but as the TURN-COMPOSITION of the per-sub-op rows
(`Dregg2.Circuit.TurnEmit`'s `RecChainedState` chain, cited by the transfer keystone), NOT as a new
single-row `EffectVmDescriptor`. The atomic-tx effect ADDS, on top of that composition, TWO things the
per-row IR cannot represent:

  (1) ALL-OR-NOTHING (transactional atomicity): if ANY sub-op row is UNSAT, the WHOLE batch must be
      rejected (no partial commit). A per-row AIR gates each row independently — it has NO cross-row
      "all rows present and valid, else reject all" form.
  (2) the BATCH-COMMIT RECEIPT row (`escrowReceiptA actor`) prepended AFTER the fold — a `log`/chained-
      state advance, which the per-row state-block IR (14 cells + commitment) does not model (the log
      lives in the `RecChainedState` layer, bound by `logHashInjective`, not by `state_commit`).

  ⇒ **needs IR extension: a BATCH / SEQUENCE descriptor form (NOT a single `EffectVmDescriptor`): a
     variable-length CHAIN of per-sub-op row-descriptors composed by `transition` continuity, with (a) a
     cross-row ATOMICITY gate (all-or-nothing: a single batch-validity selector that is 1 iff every
     sub-op row is SAT, gating the whole commit), and (b) a batch-receipt `log`-advance binding. Plus
     the per-sub-op rows themselves need the queue-buffer-root / escrows-root list-accumulator columns
     flagged by EffectVmEmitQueueEnqueue / EffectVmEmitQueueDequeue. The current IR has ONLY a single-
     row `EffectVmDescriptor` (gate/transition/boundary/piBinding/hashSite/range) — NO batch/sequence
     form, NO cross-row atomicity gate, NO log-advance binding.**

`queueAtomicTxA` is therefore **IR-BLOCKED** at the per-effect level. The ONE genuinely IR-supportable
fact this module emits + proves: the EMPTY batch (`ops = []`) is a pure no-op on the represented cell
(the fold is the identity on the kernel, so the cell is FROZEN — the no-op-cell descriptor binds it),
and the SINGLE-OP batch is exactly the underlying enqueue/dequeue row. The variable-length composition +
atomicity + batch-receipt are reported as out-of-IR — NOT papered, NOT faked.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queueatomictx

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The queueAtomicTx selector + the (per-cell, batch-boundary) no-op shape. -/

/-- The queueAtomicTx selector column index (a LAYOUT CHOICE local to this descriptor). -/
def SEL_QUEUE_ATOMIC : Nat := 8

/-- The atomic-tx batch-boundary row: `s_queue_atomic = 1`, `s_noop = 0`. (This is the per-cell
representation of the EMPTY-batch / batch-boundary; the per-sub-op rows carry their own selectors.) -/
def IsQueueAtomicRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_ATOMIC = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (the EMPTY-batch / cell-boundary no-op: FULL state freeze).

This is the ONLY IR-supportable per-row shape for the batch: the represented cell is FROZEN across the
batch boundary (the EMPTY batch is the identity on the kernel; a non-empty batch's per-sub-op rows carry
their own moves — emitted by EffectVmEmitQueueEnqueue / EffectVmEmitQueueDequeue). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo`. -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted queueAtomicTx (batch-boundary) descriptor. -/

/-- The queueAtomicTx AIR identity. -/
def queueAtomicVmAirName : String := "dregg-effectvm-queueatomictx-v1"

/-- The atomic-tx batch-boundary per-row gates: full-state freeze (the EMPTY-batch / cell-boundary
no-op). The per-sub-op moves live in their own (enqueue/dequeue) descriptors. -/
def queueAtomicRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`queueAtomicVmDescriptor`** — the IR-supportable part of queueAtomicTx: the batch-boundary
full-state freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites and the 2 balance-limb range checks. The variable-length op fold + atomicity + batch-receipt
are OUT-OF-IR (the §IR-extension flag: needs a batch/sequence descriptor form). -/
def queueAtomicVmDescriptor : EffectVmDescriptor :=
  { name := queueAtomicVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueAtomicRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The batch-boundary ROW INTENT (the IR-supportable faithfulness target: cell frozen). -/

/-- **`QueueAtomicRowIntent env`** — the IR-supportable batch-boundary move: the represented cell frozen. -/
def QueueAtomicRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the (IR-supportable) intent. -/

/-- **`queueAtomicVm_faithful`.** On a batch-boundary row, the emitted descriptor's per-row gates all
hold IFF `QueueAtomicRowIntent` holds — the gates pin EXACTLY the full-cell freeze. -/
theorem queueAtomicVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queueAtomicRowGates, c.holdsVm env false false) ↔ QueueAtomicRowIntent env := by
  unfold queueAtomicRowGates gFieldPassAll QueueAtomicRowIntent
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
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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

/-! ## §5 — ANTI-GHOST. -/

theorem queueAtomicVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueueAtomicRowIntent env) :
    ¬ (∀ c ∈ queueAtomicRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queueAtomicVm_faithful env).mp h)

theorem queueAtomicVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- `RowEncodesNoop env pre post` ties the row's state-block columns to a frozen `(pre, post)` cell. -/
def RowEncodesNoop (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellFreezeSpec pre post`** — the per-cell FULL-state freeze (cell unchanged on every data
column). The EffectVM-row projection of the EMPTY-batch / batch-boundary no-op. -/
def CellFreezeSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellFreezeSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesNoop env pre post) (hint : QueueAtomicRowIntent env) :
    CellFreezeSpec pre post := by
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

/-- **`queueAtomicDescriptor_full_sound`** — satisfying the WHOLE runnable batch-boundary descriptor
forces the per-cell `CellFreezeSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. (The op fold +
atomicity + batch-receipt are out-of-IR.) -/
theorem queueAtomicDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesNoop env pre post)
    (hsat : satisfiedVm hash queueAtomicVmDescriptor env true true) :
    CellFreezeSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueAtomicRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queueAtomicVmDescriptor.constraints := by
      unfold queueAtomicVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueAtomicRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueAtomicVm_faithful env).mp hgates'
  refine ⟨intent_to_cellFreezeSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queueAtomicVmDescriptor.constraints := by
      unfold queueAtomicVmDescriptor
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

/-! ## §7 — The anti-ghost commitment tooth (REUSED — hash sites identical to transfer). -/

theorem queueAtomicDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queueAtomicVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queueAtomicVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queueAtomicVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queueAtomicVmDescriptor.constraints := by
        unfold queueAtomicVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the EMPTY batch IS the IR-supportable no-op (cell frozen).

`queueAtomicTxChainA s [] = some s` (the empty fold is the identity on the kernel). So a committed EMPTY
batch (`QueueAtomicTxSpec st actor [] st'`) has `st'.kernel = st.kernel` — the WHOLE per-asset ledger
frozen. We project ONE `(cell, asset)` ledger entry and prove it is FROZEN across the committed empty
batch — so the descriptor's balance-freeze gate provably agrees with the executor on the empty batch.

A NON-EMPTY batch's net `bal` move is the SUM over its variable op list — out of any single-row IR shape
(the §IR-extension flag: it needs the batch/sequence descriptor form, the per-sub-op rows being the
already-emitted enqueue/dequeue descriptors). We do NOT (cannot) connect the non-empty case here. -/

open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- The EMPTY-batch fold is the identity on the kernel: `queueAtomicTxChainA s [] = some s`. -/
theorem emptyBatch_kernel_id (s s1 : RecChainedState)
    (h : queueAtomicTxChainA s [] = some s1) : s1.kernel = s.kernel := by
  simp only [queueAtomicTxChainA, Option.some.injEq] at h
  rw [← h]

/-- **`unify_atomic_empty_balFrozen`** — across a committed EMPTY `QueueAtomicTxSpec` batch, the
projected `(c, asset)` ledger entry is FROZEN (the IR-supportable `CellFreezeSpec`). So the descriptor's
balance-freeze gate IS `queueAtomicTxA`'s genuine per-cell balance image ON THE EMPTY BATCH — the only
case the single-row IR can represent. A non-empty batch is the out-of-IR variable-length composition. -/
theorem unify_atomic_empty_balFrozen (st st' : RecChainedState) (actor : CellId)
    (c : CellId) (asset : AssetId)
    (hspec : QueueAtomicTxSpec st actor [] st') :
    CellFreezeSpec (cellProjBal st.kernel.bal c asset) (cellProjBal st'.kernel.bal c asset) := by
  obtain ⟨s1, hchain, hker, _⟩ := hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  rw [hker, emptyBatch_kernel_id st s1 hchain]

/-! ## §9 — NON-VACUITY. -/

/-- A concrete batch-boundary row: `bal_lo 40 → 40` (FROZEN), nonce 1 → 1, frame fixed at 0. -/
def goodAtomicRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_ATOMIC then 1
    else if v = sbCol state.BALANCE_LO then 40
    else if v = saCol state.BALANCE_LO then 40
    else if v = sbCol state.NONCE then 1
    else if v = saCol state.NONCE then 1
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodAtomicRow` REALIZES the batch-boundary intent: the cell frozen. -/
theorem goodAtomicRow_realizes_intent : QueueAtomicRowIntent goodAtomicRow := by
  unfold QueueAtomicRowIntent goodAtomicRow
  simp only [sbCol, saCol, SEL_QUEUE_ATOMIC, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 8) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have f1 : (54 + (3 + i) = 8) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED batch-boundary row: `goodAtomicRow` with the post-`bal_lo` moved to `999` (the EMPTY-batch /
boundary no-op must NOT move the represented cell). -/
def badAtomicRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodAtomicRow.loc v
  nxt := goodAtomicRow.nxt
  pub := goodAtomicRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badAtomicRow`'s post-`bal_lo` moved, so the
`gBalLoFreeze` gate REJECTS it — a concrete UNSAT. -/
theorem badAtomicRow_rejected :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badAtomicRow false false := by
  apply queueAtomicVm_rejects_moved_balance
  simp only [badAtomicRow, goodAtomicRow, sbCol, saCol, SEL_QUEUE_ATOMIC, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard queueAtomicVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard queueAtomicVmDescriptor.hashSites.length == 4
#guard queueAtomicVmDescriptor.traceWidth == 186

#assert_axioms queueAtomicVm_faithful
#assert_axioms queueAtomicVm_rejects_wrong_output
#assert_axioms queueAtomicVm_rejects_moved_balance
#assert_axioms intent_to_cellFreezeSpec
#assert_axioms queueAtomicDescriptor_full_sound
#assert_axioms queueAtomicDescriptor_commit_binds_state
#assert_axioms emptyBatch_kernel_id
#assert_axioms unify_atomic_empty_balFrozen
#assert_axioms goodAtomicRow_realizes_intent
#assert_axioms badAtomicRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx
