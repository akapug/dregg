/-
# Dregg2.Circuit.Argus.Effects.Mint — the SUPPLY-MINT effect's FULL-STATE-on-RUNNABLE welded into Argus.

`mintA`'s per-cell EffectVM soundness (`EffectVmEmitMint.mintDescriptor_full_sound`) and its Argus weld
(`Argus/Compile.lean`, `compileE .mint = mintVmDescriptor`) already stand. `EffectVmEmitMintRunnable`
amplified the per-cell soundness to FULL-state on the RUNNABLE descriptor via the validated recipe
(`mintVmDescriptorWide` + the generic `runnable_full_sound`): a satisfying wide mint row pins all 17
RecordKernelState fields (the per-cell credit + frame freeze AND the 8 side-table roots frozen), with the
anti-ghost on every column/root (`mint_rejects_state_tamper_or_collides` /
`mint_rejects_root_tamper_or_collides`). ⚑ Read those teeth at their real strength: each concludes a
DISJUNCTION — the tamper is excluded OR the deployed sponge genuinely collides at a pair a total
extractor returns. Their earlier form assumed `Poseidon2SpongeCR`, which
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` refutes at deployed BabyBear parameters, so it
excluded nothing there. The disjunction is formally weaker and actually holds of the deployed sponge.

This module welds that full-state-on-RUNNABLE result into the Argus library (so the coherence anchor
`Dregg2.Circuit.Argus` carries it), re-exporting the deliverable under the Argus effect namespace. It owns
only its own declarations and imports the audited runnable module read-only.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the sole crypto carrier is the NAMED
`Poseidon2SpongeCR` portal (inside the reused generic theorem).
-/
import Dregg2.Circuit.Emit.EffectVmEmitMintRunnable

namespace Dregg2.Circuit.Argus.Effects.Mint

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitMint (CellMintSpec RowEncodes IsMintRow)
open Dregg2.Circuit.Emit.EffectVmEmitMintRunnable
  (mintVmDescriptorWide mint_runnable_full_sound)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`mint_full_state_on_runnable` — the Argus-welded deliverable.** A row satisfying the RUNNABLE wide
mint descriptor `mintVmDescriptorWide` (the circuit the EffectVM prover runs), under the structured decode,
pins the FULL 17-field declarative post-state: the per-cell `CellMintSpec` (balance credited by `amt`, the
whole frame — incl. the frozen nonce — frozen) AND the 8 side-table roots FROZEN. The genuine full-state
soundness lives in `EffectVmEmitMintRunnable.mint_runnable_full_sound`; this names it under the Argus effect
namespace so the coherence anchor carries it. -/
theorem mint_full_state_on_runnable (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsMintRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash mintVmDescriptorWide env true false) :
    CellMintSpec pre amt post ∧ postRoots = preRoots :=
  mint_runnable_full_sound amt preRoots hash env pre post postRoots hrow henc hroots hsat

#assert_axioms mint_full_state_on_runnable

end Dregg2.Circuit.Argus.Effects.Mint
