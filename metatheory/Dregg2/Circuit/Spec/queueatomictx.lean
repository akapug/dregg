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

F1b: the deposit/refund legs are GONE with the kernel escrow holding-store — the batch touches ONLY
`queues` through its sub-ops; the other kernel fields are the FRAME (each sub-op preserves them). On
commit the per-op receipts land inside the fold's log, then ONE batch-commit row
`escrowReceiptA actor` is prepended.
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

/-! ## §3 — batch frame preservation (the non-`queues` fields; F1b: the sub-ops are queues-only). -/

/-- Each atomic sub-op leaves the non-`queues` kernel fields (besides `bal`, framed separately by
bal-neutrality) unchanged — read off the `queuefifocore` full-state specs. -/
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
  | enqueue id m actor cell =>
      simp only [queueTxOpStepA] at h
      rcases (queueEnqueueChainA_iff_spec s id m actor cell s').mp h with
        ⟨_, _, _, h1, h2, h3, h4, h5, h6, _hbal, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  | dequeue id actor cell =>
      simp only [queueTxOpStepA] at h
      rcases (queueDequeueChainA_iff_spec s id actor cell s').mp h with
        ⟨_, _, _, h1, h2, h3, h4, h5, h6, _hbal, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The atomic batch fold preserves the non-`queues` kernel fields (besides `bal`). -/
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