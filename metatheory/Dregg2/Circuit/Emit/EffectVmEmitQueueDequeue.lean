/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue — the `queueDequeueA` (FIFO pop-front + deposit REFUND)
effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueDequeueA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueDequeueA_full_sound ⇒ QueueDequeueSpec`: a committed dequeue POP-FRONTS queue `id`'s FIFO buffer
(`queueDequeueK`), CREDITS the per-asset ledger `bal` at `(actor, r.asset)` by the deposit's amount, and
RESOLVES the deposit `EscrowRecord` in `escrows` (`settleEscrowRawAsset`), advances the log, and FREEZES
the other 14 kernel fields.

## What the EffectVM IR (a 14-column per-cell state block + GROUP-4 commitment) DOES support

The conserved `bal` move is a SINGLE-cell single-asset CREDIT: `settleEscrowRawAsset` rewrites
`bal := recBalCreditCell k₁.bal actor r.asset r.amount` — the dequeuer's `(actor, r.asset)` ledger entry
RISES by the refund amount. On the EffectVM row this is the actor cell's `state.BALANCE_LO` limb moving
UP by `amount` — the transfer-CREDIT leg (`signedMove = +amount`). The IR carries it totally, and the
GROUP-4 commitment chain binds the whole after-state block into `state_commit` exactly as for transfer.
The nonce is FROZEN (the executor does NOT tick it — the refund settle rewrites only `bal` + `escrows`).

## THE IR-EXTENSION FLAGS (the FIFO pop-front + the escrows-settle set-membership legs)

`QueueDequeueSpec` ALSO (1) POP-FRONTS the FIFO buffer (`queueDequeueK` — owner-gated, fail-closed on
empty, returning the head as the FIFO-ORDER witness) and (2) marks the deposit record RESOLVED in
`escrows` (`markResolved` — a list-membership update). Both are MERKLE/LIST-ACCUMULATOR MEMBERSHIP+ORDER
properties universe A binds via `listComponent`/`listDigest`. The EffectVM 14-column state block has NO
queue-buffer-root and NO escrows-root column, and the GROUP-4 hash-sites absorb NEITHER. So the IR
CANNOT bind the FIFO pop OR the escrow settle into `state_commit`, and CANNOT express that the popped
element is the FIFO HEAD (the order property), nor that the buffer was non-empty.

  ⇒ **needs IR extension: (a) a queue-buffer-root column absorbed by a NEW merkle/list-accumulator
     hash-site that ALSO exposes the HEAD element (so the FIFO-order pop — head removed, order of the
     rest preserved, owner-gated — is bound into `state_commit`); and (b) an escrows-root column
     absorbed by a hash-site (so the markResolved settle is bound). The current IR has NO list-
     accumulator gate-kind and NO membership-update / head-exposure form — only gate/transition/boundary/
     piBinding/hashSite(fixed-arity-per-row)/range.**

`queueDequeueA` is therefore **PARTIAL**: the deposit REFUND (the conserved `bal` move) is FULLY in IR;
the FIFO pop-front and the escrows settle are out-of-IR. NOT papered, NOT faked.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue

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

/-! ## §0 — The queueDequeue selector + the refund CREDIT parameter. -/

/-- The queueDequeue selector column index (a LAYOUT CHOICE local to this descriptor). -/
def SEL_QUEUE_DEQUEUE : Nat := 6

/-- The dequeue row: `s_queue_dequeue = 1`, `s_noop = 0`. -/
def IsQueueDequeueRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_DEQUEUE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (refund CREDIT + full frame freeze, nonce freeze). -/

/-- Balance-lo CREDIT body: `new_bal_lo − old_bal_lo − amount`. The refund (`param.AMOUNT`) arrives in
the dequeuer's ledger entry: the limb RISES by exactly `amount`. -/
def gBalLoCredit : EmittedExpr :=
  eSub (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (ePrm param.AMOUNT)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the refund settle leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted queueDequeue descriptor. -/

/-- The queueDequeue AIR identity. -/
def queueDequeueVmAirName : String := "dregg-effectvm-queuedequeue-v1"

/-- The dequeue per-row gates: balance credit, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. -/
def queueDequeueRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`queueDequeueVmDescriptor`** — the IR-supportable part of queueDequeue: the per-row refund-credit
+ freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash sites
and the 2 balance-limb range checks. The FIFO pop-front + escrows settle are OUT-OF-IR. -/
def queueDequeueVmDescriptor : EffectVmDescriptor :=
  { name := queueDequeueVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueDequeueRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueDequeue ROW INTENT (the IR-supportable faithfulness target: refund credit). -/

/-- **`QueueDequeueRowIntent env`** — the IR-supportable dequeue move: the dequeuer cell's `bal_lo` rises
by `amount` (the refund), the hi limb / nonce / whole frame are FIXED. -/
def QueueDequeueRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the (IR-supportable) intent. -/

/-- **`queueDequeueVm_faithful`.** On a dequeue row, the emitted descriptor's per-row gates all hold IFF
`QueueDequeueRowIntent` holds — the gates pin EXACTLY the refund credit + nonce-freeze + frame-freeze. -/
theorem queueDequeueVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queueDequeueRowGates, c.holdsVm env false false) ↔ QueueDequeueRowIntent env := by
  unfold queueDequeueRowGates gFieldPassAll QueueDequeueRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHi, gNonceFreeze, gCapPass, gResPass,
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
    · simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
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

theorem queueDequeueVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueueDequeueRowIntent env) :
    ¬ (∀ c ∈ queueDequeueRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queueDequeueVm_faithful env).mp h)

theorem queueDequeueVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The refund parameter carried in the param block. -/
structure RefundParams where
  amount : ℤ

/-- `RowEncodesCredit env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition (the refund's `RowEncodes`: a single `amount` param). -/
def RowEncodesCredit (env : VmRowEnv) (pre : CellState) (p : RefundParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.AMOUNT) = p.amount
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellCreditSpec pre p post`** — the per-cell FULL-state refund-credit spec: the dequeuer cell's
`balLo` rises by `amount`, the nonce is FROZEN, and the whole frame is LITERALLY unchanged. The
EffectVM-row projection of `QueueDequeueSpec`'s `bal` credit + frame freeze on the dequeuer cell. -/
def CellCreditSpec (pre : CellState) (p : RefundParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo + p.amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellCreditSpec (env : VmRowEnv) (pre post : CellState) (p : RefundParams)
    (henc : RowEncodesCredit env pre p post) (hint : QueueDequeueRowIntent env) :
    CellCreditSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.AMOUNT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`queueDequeueDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor forces the
per-cell `CellCreditSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. (FIFO pop + escrows settle
are out-of-IR.) -/
theorem queueDequeueDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : RefundParams)
    (henc : RowEncodesCredit env pre p post)
    (hsat : satisfiedVm hash queueDequeueVmDescriptor env true true) :
    CellCreditSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueDequeueRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queueDequeueVmDescriptor.constraints := by
      unfold queueDequeueVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueDequeueRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueDequeueVm_faithful env).mp hgates'
  refine ⟨intent_to_cellCreditSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queueDequeueVmDescriptor.constraints := by
      unfold queueDequeueVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §7 — The anti-ghost commitment tooth (REUSED — hash sites identical to transfer). -/

theorem queueDequeueDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queueDequeueVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queueDequeueVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queueDequeueVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queueDequeueVmDescriptor.constraints := by
        unfold queueDequeueVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the refund CREDIT IS `QueueDequeueSpec`'s per-cell `bal` image.

`QueueDequeueSpec` commits `st'.kernel = k'` where `queueDequeueRefundK st.kernel id actor depId =
some (k', m)`. That helper composes `queueDequeueK` (balance-NEUTRAL — touches only `queues`) with
`settleEscrowRawAsset k₁ depId actor r.asset r.amount` (where `r = findUnresolvedDeposit k₁ depId`),
which rewrites `bal := recBalCreditCell k₁.bal actor r.asset r.amount` — the dequeuer's `(actor, r.asset)`
ledger entry RISES by `r.amount`. We prove the dequeuer cell's projection satisfies `CellCreditSpec`
EXACTLY for the refund amount `r.amount` AT the refund asset `r.asset`. The FIFO pop + escrows settle are
out-of-IR. -/

open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec

/-- `queueDequeueK` is balance-preserving on the raw `bal` function (it rewrites only `queues`). -/
theorem queueDequeueK_bal {k k₁ : RecordKernelState} {id : Nat} {actor : CellId} {mh : Nat}
    (h : queueDequeueK k id actor = some (k₁, mh)) : k₁.bal = k.bal := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none          => rw [hd] at h; exact absurd h (by simp)
        | some hr       =>
            obtain ⟨m, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk; rfl
      · rw [if_neg ho] at h; exact absurd h (by simp)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_dequeue_credit`** — across a committed `QueueDequeueSpec` post-state, the dequeuer cell's
projected `(actor, r.asset)` ledger entry satisfies the keystone's `CellCreditSpec` EXACTLY for the
witnessed refund amount `r.amount`: `balLo` rises by `r.amount`; balHi/fields/capRoot/reserved frozen;
nonce frozen. The refund's asset `r.asset` and amount `r.amount` are extracted from the dequeue's
`findUnresolvedDeposit` witness. So `CellCreditSpec` IS `QueueDequeueSpec`'s per-cell `bal` image — NOT a
fourth spec. The FIFO pop + escrows settle are out-of-IR. -/
theorem unify_dequeue_credit (st st' : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (hspec : QueueDequeueSpec st id actor cell depId st') :
    ∃ (asset : AssetId) (amount : ℤ),
      CellCreditSpec (cellProjBal st.kernel.bal actor asset) ⟨amount⟩
        (cellProjBal st'.kernel.bal actor asset) := by
  obtain ⟨_, _, _, _, k', m, hk, hker, _⟩ := hspec
  -- unfold queueDequeueRefundK to expose the settle credit
  unfold queueDequeueRefundK at hk
  cases hk₁ : queueDequeueK st.kernel id actor with
  | none => simp only [hk₁] at hk; exact absurd hk (by simp)
  | some kr =>
      obtain ⟨k₁, mh⟩ := kr
      simp only [hk₁] at hk
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh = true
      · rw [if_pos hbind] at hk
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at hk; exact absurd hk (by simp)
        | some r =>
            simp only [hfind] at hk
            by_cases hacc : actor ∈ k₁.accounts
            · rw [if_pos hacc] at hk
              simp only [Option.some.injEq, Prod.mk.injEq] at hk
              obtain ⟨hkeq, _⟩ := hk
              refine ⟨r.asset, r.amount, ?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
              show st'.kernel.bal actor r.asset = st.kernel.bal actor r.asset + r.amount
              rw [hker, ← hkeq]
              show (settleEscrowRawAsset k₁ depId actor r.asset r.amount).bal actor r.asset
                  = st.kernel.bal actor r.asset + r.amount
              have hbalfn : (settleEscrowRawAsset k₁ depId actor r.asset r.amount).bal
                  = recBalCreditCell k₁.bal actor r.asset r.amount := rfl
              rw [hbalfn]
              unfold recBalCreditCell
              rw [if_pos (And.intro rfl rfl), queueDequeueK_bal hk₁]
            · rw [if_neg hacc] at hk; exact absurd hk (by simp)
      · rw [if_neg hbind] at hk; exact absurd hk (by simp)

/-! ## §9 — NON-VACUITY. -/

/-- A concrete dequeue row: `bal_lo 70 → 95` (refund 25), nonce 4 → 4 (FROZEN), frame fixed at 0. -/
def goodDequeueRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_DEQUEUE then 1
    else if v = sbCol state.BALANCE_LO then 70
    else if v = saCol state.BALANCE_LO then 95
    else if v = sbCol state.NONCE then 4
    else if v = saCol state.NONCE then 4
    else if v = prmCol param.AMOUNT then 25
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodDequeueRow` REALIZES the dequeue intent: bal_lo `70 → 95`
(credit 25), nonce frozen `4 → 4`, frame fixed. -/
theorem goodDequeueRow_realizes_intent : QueueDequeueRowIntent goodDequeueRow := by
  unfold QueueDequeueRowIntent goodDequeueRow
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_DEQUEUE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 6) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have f1 : (54 + (3 + i) = 6) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED dequeue row: `goodDequeueRow` with the post-`bal_lo` tampered to `999` (not the credit `95`). -/
def badDequeueRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodDequeueRow.loc v
  nxt := goodDequeueRow.nxt
  pub := goodDequeueRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badDequeueRow`'s post-`bal_lo` is NOT the
credit, so the `gBalLoCredit` gate REJECTS it — a concrete UNSAT. -/
theorem badDequeueRow_rejected :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm badDequeueRow false false := by
  apply queueDequeueVm_rejects_wrong_balance
  simp only [badDequeueRow, goodDequeueRow, sbCol, saCol, prmCol, SEL_QUEUE_DEQUEUE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard queueDequeueVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard queueDequeueVmDescriptor.hashSites.length == 4
#guard queueDequeueVmDescriptor.traceWidth == 186

#assert_axioms queueDequeueVm_faithful
#assert_axioms queueDequeueVm_rejects_wrong_output
#assert_axioms queueDequeueVm_rejects_wrong_balance
#assert_axioms intent_to_cellCreditSpec
#assert_axioms queueDequeueDescriptor_full_sound
#assert_axioms queueDequeueDescriptor_commit_binds_state
#assert_axioms queueDequeueK_bal
#assert_axioms unify_dequeue_credit
#assert_axioms goodDequeueRow_realizes_intent
#assert_axioms badDequeueRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue
