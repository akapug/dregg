/-
# Dregg2.Circuit.Spec.swissframe — shared helpers for swiss-table effect specs.

Swiss kernel steps touch ONLY `kernel.swiss`; chained wrappers prepend a receipt to `log`.
Specs use the queue-atomic existential witness pattern so iff proofs avoid per-field destructuring.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SwissFrame

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — kernel extensionality + swiss-only updates preserve the frame. -/

theorem recKernel_ext {k k' : RecordKernelState}
    (h1 : k'.accounts = k.accounts) (h2 : k'.cell = k.cell) (h3 : k'.caps = k.caps)
    (h4 : k'.escrows = k.escrows) (h5 : k'.nullifiers = k.nullifiers) (h6 : k'.revoked = k.revoked)
    (h7 : k'.commitments = k.commitments) (h8 : k'.bal = k.bal) (h9 : k'.queues = k.queues)
    (h10 : k'.swiss = k.swiss) (h11 : k'.slotCaveats = k.slotCaveats)
    (h12 : k'.factories = k.factories) (h13 : k'.lifecycle = k.lifecycle)
    (h14 : k'.deathCert = k.deathCert) (h15 : k'.delegate = k.delegate)
    (h16 : k'.delegations = k.delegations) (h17 : k'.sealedBoxes = k.sealedBoxes) :
    k' = k := by
  cases k; cases k'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rfl

theorem withSwiss_preserves_rest (k : RecordKernelState) (ss : List SwissRecord) :
    let k' := { k with swiss := ss }
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.queues = k.queues
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes := by
  dsimp
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#assert_axioms recKernel_ext
#assert_axioms withSwiss_preserves_rest

end Dregg2.Circuit.Spec.SwissFrame