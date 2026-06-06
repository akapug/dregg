/-
# Dregg2.Circuit.Spec.celllifecycle — INDEPENDENT full-state spec + executor⟺spec for the Wave-3
  cell LIFECYCLE effect family (`cellSealA`, `cellUnsealA`, `cellDestroyA`).

Each arm drives the `lifecycle` side-table (and `deathCert` on destroy) through the chained executors
`cellSealChainA` / `cellUnsealChainA` / `cellDestroyChainA` (`TurnExecutorFull.lean:1654`–`:1681`):
authority-gated (`stateAuthB actor cell`), state-machine-gated, balance-neutral, one self-targeted
receipt row prepended to the log.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellLifecycle

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — shared receipt + kernel extensionality. -/

/-- The self-targeted receipt row every committed lifecycle transition prepends. -/
def cellLifecycleReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- Rebuild a `RecordKernelState` from 17 per-field equalities (the `←` reconstruction helper). -/
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

/-! ## §1 — `cellSealA`: Live → Sealed. -/

/-- **The admissibility guard** for `cellSealA`: self-authority over `cell` AND `cell` is Live
(`acceptsEffects`). -/
def CellSealGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true

/-- The declarative post-`lifecycle` map: flip `cell` to Sealed, every other cell unchanged. -/
def sealLifecycleMap (k : RecordKernelState) (cell : CellId) : CellId → Nat :=
  (setLifecycle k cell lcSealed).lifecycle

/-- **The full-state declarative spec of a committed `cellSealA`.** -/
def CellSealSpec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) : Prop :=
  CellSealGuard s actor cell
  ∧ s'.kernel.lifecycle = sealLifecycleMap s.kernel cell
  ∧ s'.log = cellLifecycleReceipt actor cell :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps ∧ s'.kernel.escrows = s.kernel.escrows
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.queues = s.kernel.queues ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-- **`cellSeal_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** -/
theorem cellSeal_iff_spec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) :
    execFullA s (.cellSealA actor cell) = some s' ↔ CellSealSpec s actor cell s' := by
  unfold CellSealSpec CellSealGuard sealLifecycleMap
  simp only [execFullA, cellSealChainA]
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl⟩
    · rintro ⟨_, hlif, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      obtain ⟨k', lg'⟩ := s'
      obtain ⟨acc, cellm, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
      simp only at hlif hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hlif hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §2 — `cellUnsealA`: Sealed → Live. -/

/-- **The admissibility guard** for `cellUnsealA`: self-authority AND `cell` is Sealed. -/
def CellUnsealGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true

/-- The declarative post-`lifecycle` map: flip `cell` back to Live. -/
def unsealLifecycleMap (k : RecordKernelState) (cell : CellId) : CellId → Nat :=
  (setLifecycle k cell lcLive).lifecycle

/-- **The full-state declarative spec of a committed `cellUnsealA`.** -/
def CellUnsealSpec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) : Prop :=
  CellUnsealGuard s actor cell
  ∧ s'.kernel.lifecycle = unsealLifecycleMap s.kernel cell
  ∧ s'.log = cellLifecycleReceipt actor cell :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps ∧ s'.kernel.escrows = s.kernel.escrows
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.queues = s.kernel.queues ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-- **`cellUnseal_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** -/
theorem cellUnseal_iff_spec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) :
    execFullA s (.cellUnsealA actor cell) = some s' ↔ CellUnsealSpec s actor cell s' := by
  unfold CellUnsealSpec CellUnsealGuard unsealLifecycleMap
  simp only [execFullA, cellUnsealChainA]
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl⟩
    · rintro ⟨_, hlif, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      obtain ⟨k', lg'⟩ := s'
      obtain ⟨acc, cellm, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
      simp only at hlif hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hlif hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §3 — `cellDestroyA`: non-terminal → Destroyed + death-cert bind. -/

/-- **The admissibility guard** for `cellDestroyA`: self-authority AND `cell` is not already Destroyed. -/
def CellDestroyGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell != lcDestroyed) = true

/-- The declarative post-`deathCert` map: bind `certHash` at `cell`, every other cell unchanged. -/
def destroyDeathCertMap (k : RecordKernelState) (cell : CellId) (certHash : Nat) : CellId → Nat :=
  fun c => if c = cell then certHash else k.deathCert c

/-- The declarative post-kernel of a destroy: flip lifecycle + bind death cert. -/
def destroyKernelMap (k : RecordKernelState) (cell : CellId) (certHash : Nat) : RecordKernelState :=
  { (setLifecycle k cell lcDestroyed) with
    deathCert := destroyDeathCertMap k cell certHash }

/-- **The full-state declarative spec of a committed `cellDestroyA`.** -/
def CellDestroySpec (s : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (s' : RecChainedState) : Prop :=
  CellDestroyGuard s actor cell
  ∧ s'.kernel.lifecycle = (destroyKernelMap s.kernel cell certHash).lifecycle
  ∧ s'.kernel.deathCert = (destroyKernelMap s.kernel cell certHash).deathCert
  ∧ s'.log = cellLifecycleReceipt actor cell :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps ∧ s'.kernel.escrows = s.kernel.escrows
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.queues = s.kernel.queues ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.delegate = s.kernel.delegate ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-- **`cellDestroy_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** -/
theorem cellDestroy_iff_spec (s : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (s' : RecChainedState) :
    execFullA s (.cellDestroyA actor cell certHash) = some s'
      ↔ CellDestroySpec s actor cell certHash s' := by
  unfold CellDestroySpec CellDestroyGuard destroyKernelMap destroyDeathCertMap
  simp only [execFullA, cellDestroyChainA]
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell != lcDestroyed) = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl⟩
    · rintro ⟨_, hlif, hdc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      obtain ⟨k', lg'⟩ := s'
      obtain ⟨acc, cellm, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
      simp only at hlif hdc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      subst hlif hdc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §4 — axiom-hygiene tripwires. -/

#assert_axioms cellSeal_iff_spec
#assert_axioms cellUnseal_iff_spec
#assert_axioms cellDestroy_iff_spec

end Dregg2.Circuit.Spec.CellLifecycle