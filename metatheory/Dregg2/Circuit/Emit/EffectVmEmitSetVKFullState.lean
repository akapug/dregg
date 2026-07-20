/-
# Dregg2.Circuit.Emit.EffectVmEmitSetVKFullState — setVerificationKey LIFTED to FULL-STATE on the
RUNNABLE descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitSetVK` welds the per-cell block (`CellSetVKSpec`: economic block FROZEN, the seq-nonce TICKS)
on the 186-wide RUNNABLE descriptor; its `state_commit` absorbs only the 13 state-block columns, NOT the
8 side-table roots. This module CLOSES that by amplifying the RUNNABLE descriptor to the WIDE
(`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell block AND every one of the 8 side-table roots FROZEN.

setVerificationKey writes the cell's VK OFF the VM trace (its SOUNDNESS is the universe-A leg); the
RUNNABLE row is the frozen-frame + nonce-tick passthrough. So its `system_roots` sub-block is FROZEN; the
magnesium win is the WIDE commitment now BINDS all 8 roots. The §RECIPE applied to setVK.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The anti-ghost theorems carry NO
collision-resistance hypothesis: they conclude a disjunction naming the sponge collision they
would otherwise assume away.
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitSetVKFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitSetVK
  (SEL_SET_VK IsSetVKRow setVKRowGates setVKVmDescriptor RowEncodesVK CellSetVKSpec
   setVKVm_faithful intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds_or_collides
   wide_rejects_root_tamper_or_collides WideColl RootsColl wideHashSites)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE setVK descriptor (width + sites; constraints UNCHANGED). -/

def setVKVmDescriptorWide : EffectVmDescriptor :=
  { setVKVmDescriptor with
    name := setVKVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem setVKWide_constraints_eq :
    setVKVmDescriptorWide.constraints = setVKVmDescriptor.constraints := rfl

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis). -/

theorem setVKGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesVK env pre post)
    (hgates : ∀ c ∈ setVKVmDescriptor.constraints, c.holdsVm env true false) :
    CellSetVKSpec pre post := by
  have hrowgates : ∀ c ∈ setVKRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ setVKVmDescriptor.constraints := by
      unfold setVKVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold setVKRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((setVKVm_faithful env).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

def SetVKFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellSetVKSpec pre post ∧ postRoots = preRoots

def setVKRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := setVKVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsSetVKRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesVK env pre post ∧ postRoots = preRoots
  fullClause    := SetVKFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨setVKGates_give_cellSpec env pre post hrow.2 henc
            (setVKWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `setVerificationKey_runnable_full_sound`. -/

/-- **`setVerificationKey_runnable_full_sound` — the magnesium crown for setVerificationKey.** A row
satisfying the WIDE RUNNABLE descriptor, decoded by `RowEncodesVK` with the frozen-roots witness, pins the
FULL 17-field post-state: the per-cell block (`CellSetVKSpec`) AND all 8 side-table roots FROZEN. -/
theorem setVerificationKey_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsSetVKRow env)
    (henc : RowEncodesVK env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash setVKVmDescriptorWide env true false) :
    CellSetVKSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (setVKRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST. -/

/-- **`setVerificationKey_runnable_full_commit_binds_or_collides` — the setVK anti-ghost.** Two wide
setVK rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) EITHER agree on all 12
absorbed state-block columns AND pointwise on the 8 side-table roots, OR exhibit a collision of the
deployed sponge — at the wide absorb, or at the two root lists.

The old form concluded the bare conjunction from `Poseidon2SpongeCR hash`, which the deployed sponge
REFUTES; at deployed parameters it was vacuous. The disjunction is formally weaker and HOLDS of the
deployed sponge. -/
theorem setVerificationKey_runnable_full_commit_binds_or_collides (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash setVKVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash setVKVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  runnable_full_commit_binds_or_collides (setVKRunnableSpec preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`setVerificationKey_rejects_root_tamper_or_collides` — side-table anti-ghost for setVK.** Two
wide setVK rows publishing the same `NEW_COMMIT` whose side-table sub-blocks DIFFER at some index `i`
exhibit a collision of the deployed sponge: forging a side-table root under a fixed commitment costs a
sponge collision.

The old form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed sponge REFUTES; at
deployed parameters it was vacuous. This one names the collision instead of assuming it away. -/
theorem setVerificationKey_rejects_root_tamper_or_collides (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash setVKVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash setVKVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_root_tamper_or_collides (setVKRunnableSpec preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY. -/

def setVKPreRoots : SysRoots := emptySystemRoots

def setVKPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def setVKPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodSetVK_realizes :
    (setVKRunnableSpec setVKPreRoots).fullClause setVKPre setVKPost setVKPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem setVK_clause_not_trivial :
    ¬ SetVKFullClause setVKPreRoots setVKPre { setVKPost with balLo := 999 } setVKPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [setVKPre] at hbal
  norm_num at hbal

theorem setVK_clause_rejects_root_drop :
    ¬ SetVKFullClause setVKPreRoots setVKPre setVKPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [setVKPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard setVKVmDescriptorWide.traceWidth == 190
#guard setVKVmDescriptorWide.hashSites.length == 4
#guard setVKVmDescriptorWide.constraints.length == setVKVmDescriptor.constraints.length

#assert_axioms setVKGates_give_cellSpec
#assert_axioms setVerificationKey_runnable_full_sound
#assert_axioms setVerificationKey_runnable_full_commit_binds_or_collides
#assert_axioms setVerificationKey_rejects_root_tamper_or_collides
#assert_axioms goodSetVK_realizes
#assert_axioms setVK_clause_not_trivial
#assert_axioms setVK_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitSetVKFullState
