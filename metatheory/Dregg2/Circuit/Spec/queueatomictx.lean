/-
# Dregg2.Circuit.Spec.queueatomictx — INDEPENDENT full-state spec + executor⟺spec for
`queueAtomicTxA` (the ALL-OR-NOTHING atomic queue-op batch).

`execFullA s (.queueAtomicTxA actor ops) = queueAtomicTxA s actor ops` (`TurnExecutorFull:3590`).

    queueAtomicTxA s actor ops                                              -- :2414
      = match queueAtomicTxChainA s ops with
        | some s1 => some { kernel := s1.kernel, log := escrowReceiptA actor :: s1.log }
        | none    => none

    queueAtomicTxChainA s ops                                               -- :2334
      = fold left-to-right through `queueTxOpStepA` (each sub-op routes to
        `queueEnqueueChainA` / `queueDequeueChainA`); ANY failure ⇒ `none`.

The batch touches THREE kernel components (`queues` + `bal` + `escrows`) through its sub-ops; the
other 14 kernel fields are the FRAME (each sub-op preserves them). On commit the per-op receipts land
inside the fold's log, then ONE batch-commit row `escrowReceiptA actor` is prepended.
-/
import Dregg2.Circuit.Spec.queuefifocore
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.QueueAtomicTx

open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the atomic-batch admissibility guard + declarative spec. -/

/-- The atomic-batch admissibility guard: the all-or-nothing fold COMMITS (every sub-op succeeds). -/
def atomicTxGuard (st : RecChainedState) (ops : List QueueTxOpA) : Prop :=
  ∃ s1, queueAtomicTxChainA st ops = some s1

/-- **The full-state declarative spec of a committed `queueAtomicTxA`.** The batch fold commits to
`s1`; the post-kernel is EXACTLY `s1.kernel`; the chained `log` is the fold's log advanced by the
batch-commit row `escrowReceiptA actor`. -/
def QueueAtomicTxSpec (st : RecChainedState) (actor : CellId) (ops : List QueueTxOpA)
    (st' : RecChainedState) : Prop :=
  ∃ s1, queueAtomicTxChainA st ops = some s1
    ∧ st'.kernel = s1.kernel
    ∧ st'.log = escrowReceiptA actor :: s1.log

/-! ## §2 — executor ⟺ spec (BOTH directions). -/

/-- **`queueAtomicTxA_iff_spec` — the chained atomic-tx step ⟺ the independent spec.** -/
theorem queueAtomicTxA_iff_spec (st : RecChainedState) (actor : CellId) (ops : List QueueTxOpA)
    (st' : RecChainedState) :
    queueAtomicTxA st actor ops = some st'
      ↔ QueueAtomicTxSpec st actor ops st' := by
  unfold queueAtomicTxA QueueAtomicTxSpec
  cases hf : queueAtomicTxChainA st ops with
  | none =>
      simp only [hf]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨s1, hf1, _⟩; exact absurd hf1 (by simp)
  | some s1 =>
      simp only [hf]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨s1, rfl, rfl, rfl⟩
      · rintro ⟨_, hf1, hker, hlog⟩
        simp only [Option.some.injEq] at hf1; subst hf1
        obtain ⟨k', l'⟩ := st'
        simp only at hker hlog
        subst hker hlog
        rfl

/-- **`execFullA_queueAtomicTxA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueAtomicTxA_iff_spec (st : RecChainedState) (actor : CellId)
    (ops : List QueueTxOpA) (st' : RecChainedState) :
    execFullA st (.queueAtomicTxA actor ops) = some st'
      ↔ QueueAtomicTxSpec st actor ops st' := by
  show queueAtomicTxA st actor ops = some st' ↔ QueueAtomicTxSpec st actor ops st'
  exact queueAtomicTxA_iff_spec st actor ops st'

/-! ## §3 — batch frame preservation (the 14 non-`queues`-non-`bal`-non-`escrows` fields). -/

private theorem queueEnqueueK_preserves_rest {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt := by
  unfold queueEnqueueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [if_neg hc] at h; exact absurd h (by simp)

private theorem createEscrowRawAssetQueue_preserves_rest (k₁ : RecordKernelState) (depId : Nat)
    (actor cell : CellId) (dAsset : AssetId) (deposit : ℤ) (id m : Nat) :
    (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).accounts = k₁.accounts
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).cell = k₁.cell
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).caps = k₁.caps
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).nullifiers = k₁.nullifiers
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).revoked = k₁.revoked
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).commitments = k₁.commitments
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).swiss = k₁.swiss
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).slotCaveats = k₁.slotCaveats
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).factories = k₁.factories
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).lifecycle = k₁.lifecycle
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).deathCert = k₁.deathCert
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).delegate = k₁.delegate
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).delegations = k₁.delegations
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).sealedBoxes = k₁.sealedBoxes
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).delegationEpoch = k₁.delegationEpoch
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).delegationEpochAt = k₁.delegationEpochAt := by
  dsimp [createEscrowRawAssetQueue]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem settleEscrowRawAsset_preserves_rest (k₁ : RecordKernelState) (id : Nat) (target : CellId)
    (asset : AssetId) (amount : ℤ) :
    (settleEscrowRawAsset k₁ id target asset amount).accounts = k₁.accounts
      ∧ (settleEscrowRawAsset k₁ id target asset amount).cell = k₁.cell
      ∧ (settleEscrowRawAsset k₁ id target asset amount).caps = k₁.caps
      ∧ (settleEscrowRawAsset k₁ id target asset amount).nullifiers = k₁.nullifiers
      ∧ (settleEscrowRawAsset k₁ id target asset amount).revoked = k₁.revoked
      ∧ (settleEscrowRawAsset k₁ id target asset amount).commitments = k₁.commitments
      ∧ (settleEscrowRawAsset k₁ id target asset amount).swiss = k₁.swiss
      ∧ (settleEscrowRawAsset k₁ id target asset amount).slotCaveats = k₁.slotCaveats
      ∧ (settleEscrowRawAsset k₁ id target asset amount).factories = k₁.factories
      ∧ (settleEscrowRawAsset k₁ id target asset amount).lifecycle = k₁.lifecycle
      ∧ (settleEscrowRawAsset k₁ id target asset amount).deathCert = k₁.deathCert
      ∧ (settleEscrowRawAsset k₁ id target asset amount).delegate = k₁.delegate
      ∧ (settleEscrowRawAsset k₁ id target asset amount).delegations = k₁.delegations
      ∧ (settleEscrowRawAsset k₁ id target asset amount).sealedBoxes = k₁.sealedBoxes
      ∧ (settleEscrowRawAsset k₁ id target asset amount).delegationEpoch = k₁.delegationEpoch
      ∧ (settleEscrowRawAsset k₁ id target asset amount).delegationEpochAt = k₁.delegationEpochAt := by
  dsimp [settleEscrowRawAsset]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem queueDequeueK_preserves_rest {k k' : RecordKernelState} {id : Nat} {actor : CellId} {m : Nat}
    (h : queueDequeueK k id actor = some (k', m)) :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none           => rw [hd] at h; exact absurd h (by simp)
        | some hr        =>
            obtain ⟨hm, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [if_neg ho] at h; exact absurd h (by simp)

private theorem queueDequeueRefundK_preserves_rest {k k' : RecordKernelState} {id : Nat} {actor : CellId}
    {depId m : Nat} (h : queueDequeueRefundK k id actor depId = some (k', m)) :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt := by
  unfold queueDequeueRefundK at h
  cases hk₁ : queueDequeueK k id actor with
  | none => simp only [hk₁] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k₁, mh⟩ := kr
      simp only [hk₁] at h
      split at h
      · cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk', _⟩ := h; subst hk'
              rcases settleEscrowRawAsset_preserves_rest k₁ depId actor r.asset r.amount with
                ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB, hDE, hDEA⟩
              rcases queueDequeueK_preserves_rest hk₁ with
                ⟨hAcc₁, hCell₁, hCaps₁, hNul₁, hRev₁, hCom₁, hSw₁, hSC₁, hFac₁, hLif₁, hDC₁, hDel₁, hDgs₁, hSB₁, hDE₁, hDEA₁⟩
              exact ⟨hAcc.trans hAcc₁, hCell.trans hCell₁, hCaps.trans hCaps₁, hNul.trans hNul₁,
                hRev.trans hRev₁, hCom.trans hCom₁, hSw.trans hSw₁, hSC.trans hSC₁, hFac.trans hFac₁,
                hLif.trans hLif₁, hDC.trans hDC₁, hDel.trans hDel₁, hDgs.trans hDgs₁, hSB.trans hSB₁,
                hDE.trans hDE₁, hDEA.trans hDEA₁⟩
            · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- Each atomic sub-op leaves the 14 non-`queues`-non-`bal`-non-`escrows` kernel fields unchanged. -/
theorem queueTxOpStepA_preserves_rest {s s' : RecChainedState} {op : QueueTxOpA}
    (h : queueTxOpStepA s op = some s') :
    s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
      ∧ s'.kernel.caps = s.kernel.caps ∧ s'.kernel.nullifiers = s.kernel.nullifiers
      ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
      ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
      ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
      ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
      ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
      ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
      ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA] at h
      rcases queueEnqueueChainA_iff_spec s id m actor cell depId dAsset deposit s' |>.mp h with
        ⟨k₁, _, _, hk₁, _, _, _, _, hker, _⟩
      rcases createEscrowRawAssetQueue_preserves_rest k₁ depId actor cell dAsset deposit id m with
        ⟨hAcc₂, hCell₂, hCaps₂, hNul₂, hRev₂, hCom₂, hSw₂, hSC₂, hFac₂, hLif₂, hDC₂, hDel₂, hDgs₂, hSB₂, hDE₂, hDEA₂⟩
      rcases queueEnqueueK_preserves_rest hk₁ with
        ⟨hAcc₁, hCell₁, hCaps₁, hNul₁, hRev₁, hCom₁, hSw₁, hSC₁, hFac₁, hLif₁, hDC₁, hDel₁, hDgs₁, hSB₁, hDE₁, hDEA₁⟩
      simpa [hker] using
        ⟨hAcc₂.trans hAcc₁, hCell₂.trans hCell₁, hCaps₂.trans hCaps₁, hNul₂.trans hNul₁,
          hRev₂.trans hRev₁, hCom₂.trans hCom₁, hSw₂.trans hSw₁, hSC₂.trans hSC₁, hFac₂.trans hFac₁,
          hLif₂.trans hLif₁, hDC₂.trans hDC₁, hDel₂.trans hDel₁, hDgs₂.trans hDgs₁, hSB₂.trans hSB₁,
          hDE₂.trans hDE₁, hDEA₂.trans hDEA₁⟩
  | dequeue id actor cell depId =>
      simp only [queueTxOpStepA] at h
      rcases queueDequeueChainA_iff_spec s id actor cell depId s' |>.mp h with
        ⟨_, _, _, _, k', _, hk, hker, _⟩
      simpa [hker] using queueDequeueRefundK_preserves_rest hk

/-- The atomic batch fold preserves the 14 non-`queues`-non-`bal`-non-`escrows` kernel fields. -/
theorem queueAtomicTxChainA_preserves_rest {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') :
    s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
      ∧ s'.kernel.caps = s.kernel.caps ∧ s'.kernel.nullifiers = s.kernel.nullifiers
      ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
      ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
      ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
      ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
      ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
      ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
      ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt := by
  induction ops generalizing s with
  | nil =>
      simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none    => rw [hop] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hop] at h
          rcases queueTxOpStepA_preserves_rest hop with
            ⟨hAcc1, hCell1, hCaps1, hNul1, hRev1, hCom1, hSw1, hSC1, hFac1, hLif1, hDC1, hDel1, hDgs1, hSB1, hDE1, hDEA1⟩
          rcases ih h with
            ⟨hAcc2, hCell2, hCaps2, hNul2, hRev2, hCom2, hSw2, hSC2, hFac2, hLif2, hDC2, hDel2, hDgs2, hSB2, hDE2, hDEA2⟩
          exact ⟨hAcc2.trans hAcc1, hCell2.trans hCell1, hCaps2.trans hCaps1, hNul2.trans hNul1,
            hRev2.trans hRev1, hCom2.trans hCom1, hSw2.trans hSw1, hSC2.trans hSC1, hFac2.trans hFac1,
            hLif2.trans hLif1, hDC2.trans hDC1, hDel2.trans hDel1, hDgs2.trans hDgs1, hSB2.trans hSB1,
            hDE2.trans hDE1, hDEA2.trans hDEA1⟩

/-! ## §4 — non-vacuity (atomic rollback). -/

/-- **`atomicTx_rejects_on_head_failure` — PROVED (the ATOMICITY teeth).** If the head sub-op fails,
the whole batch (and hence `queueAtomicTxA`) returns `none`. -/
theorem atomicTx_rejects_on_head_failure (st : RecChainedState) (actor : CellId)
    (op : QueueTxOpA) (rest : List QueueTxOpA)
    (h : queueTxOpStepA st op = none) :
    queueAtomicTxA st actor (op :: rest) = none := by
  unfold queueAtomicTxA
  simp only [queueAtomicTxChainA_head_fails (s := st) (op := op) (rest := rest) h]

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms queueTxOpStepA_preserves_rest
#assert_axioms queueAtomicTxChainA_preserves_rest
#assert_axioms queueAtomicTxA_iff_spec
#assert_axioms execFullA_queueAtomicTxA_iff_spec
#assert_axioms atomicTx_rejects_on_head_failure

end Dregg2.Circuit.Spec.QueueAtomicTx