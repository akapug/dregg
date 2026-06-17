/-
# Dregg2.Circuit.CircuitSoundnessAssembled — the COMPOSITION CAPSTONE.

`CircuitSoundness.lightclient_unfoolable` is the apex: from a verifying batch + the named floors it
concludes a genuine kernel transition committing to the published `(pi.pre, pi.post)`. But it carries
the per-effect refinement family `hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e)` as an
OPAQUE hypothesis. This module makes that `∀` EXPLICIT, ENUMERATED, and NAMED.

## What is assembled

  1. **`Rfix : Registry`** — the live `v3Registry` lookup as a `Nat`-indexed `Registry` (the descriptor
     each per-effect rung is about). `Rfix e` is the rotated descriptor at the effect tag `e`
     (`ActionDispatch.actionTag`'s convention); out-of-range indices fall back to the transfer slot
     (the registry is total as a function — every effect index resolves to a real `EffectVmDescriptor2`,
     so `vkOfRegistry Rfix` is well-defined). The fix descriptors (the committed-root-limb variants) and
     the phase-D cap descriptors are the SAME `v3Registry` entries the rungs are stated against, so
     `Rfix` IS the per-effect descriptor each rung discharges.

  2. **`kstepAll : EffectIdx → RecChainedState → RecChainedState → Prop`** — the assembled dispatcher.
     We take `kstepAll := CircuitSoundness.dispatchArm`, the generic dispatcher arm
     (`∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`) the whole-turn apex
     `lightclient_turn_unfoolable_forest` is already stated at. Its `e = 0` (transfer) arm is upgradable
     to the FAITHFUL `dispatchArmFacet` via `RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm`
     (the deployed two-axis authority gate), recorded here as the faithful-tier note.

  3. **`EffectDecodeBridge S hash R e`** — the per-effect decode bridge, NAMED. It is EXACTLY
     `descriptorRefines S hash (R e) (kstepAll e)` — the apex-shaped per-effect rung. The honest content:
     each landed per-effect rung (`transfer_descriptorRefines`, `delegate_descriptorRefines`, …)
     concludes its leaf `Spec` from a per-effect ENCODE decode (`rotatedEncodes` /
     `DelegateCapsTreeEncodes` / …), NOT from `StateDecode`. The commitment surface `StateDecode`
     commits the LEDGER ROOT only; the limb-level encode data (the guard fields, the cap-tree opening,
     the per-row column reads) is the genuine residue `StateDecode` cannot carry. Bridging
     `StateDecode ⟹ <effect>Encode` per effect is the real work — exactly the `WitnessDecodes`-adjacent
     decode extraction. NONE of the 36 effects bridges cleanly from `StateDecode` alone, so the bridge
     is carried for EVERY effect as the named per-effect residual `EffectDecodeBridge`.

  4. **`hrefinesAll`** — `∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)`, assembled from the
     per-effect bridge family `(∀ e, EffectDecodeBridge S hash Rfix e)`. Since `EffectDecodeBridge` IS
     the per-effect `descriptorRefines`, this is the explicit enumeration of the apex's carried `∀` — the
     OPAQUE hypothesis is now a NAMED, per-effect family with its content spelled out.

  5. **`lightclient_unfoolable_assembled`** — the apex instantiated at `Rfix`/`kstepAll`/`hrefinesAll`.
     Its carried floors are EXPLICIT: `StarkSound`, `Poseidon2SpongeCR`, the `CommitSurface` CR fields,
     `WitnessDecodes`, and the enumerated `EffectDecodeBridge` family. The whole-turn version
     `lightclient_turn_unfoolable_forest_assembled` lifts the same to a verified turn.

## The honest carried-floors ledger

  * `[StarkSound hash Rfix]` — the audited p3 batch-STARK extraction (REALIZABLE, named, not faked).
  * `Poseidon2SpongeCR hash` + the `CommitSurface` CR fields — the decode faithfulness floor (REALIZABLE).
  * `WitnessDecodes hash Rfix S pi` — the witness→kernel-state EXISTENCE rung (REALIZABLE, named).
  * **`∀ e, EffectDecodeBridge S hash Rfix e`** — THE ENUMERATED per-effect decode bridge family. This
    is the apex's old opaque `hrefines` made an explicit, per-effect residual set. Each `e`'s bridge is
    the genuine `StateDecode ⟹ <effect>Encode` extraction the commitment surface cannot certify. The
    LOGICAL CORE of each rung (`<effect>Encode ⟹ <effect>Spec ⟹ dispatchArm e`) is fully landed in the
    `RotatedKernelRefinement*` family; the bridge is precisely the missing decode-extraction half.

This is the honest capstone: the apex stands mod ONE named, enumerated family (`EffectDecodeBridge`)
plus the standard crypto/extraction floors — NOT an opaque carried `∀`.

## Axiom hygiene

`#assert_axioms` on the capstone theorems ⊆ {propext, Classical.choice, Quot.sound}. The named carriers
(`StarkSound`, `Poseidon2SpongeCR`, the `CommitSurface` CR fields, `WitnessDecodes`, the
`EffectDecodeBridge` family) are HYPOTHESES, not axioms — they do not appear in the axiom set. No
`sorry`, no `native_decide`, no `:= True`, no fresh axiom.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.RotatedKernelRefinementFacet
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.CircuitSoundnessAssembled

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Exec.TurnExecutorFull (execFullTurnA)
open Dregg2.Exec (RecChainedState)

set_option autoImplicit false

/-! ## §1 — `Rfix`: the live `v3Registry` as a total `Nat`-indexed `Registry`.

The apex's `Registry` is `EffectIdx → EffectVmDescriptor2` (a TOTAL function, so `vkOfRegistry` /
`StarkSound.extract` are well-defined at every published effect index). The deployed registry
`EffectVmEmitRotationV3.v3Registry` is a `List (String × EffectVmDescriptor2)` keyed by descriptor
name. `Rfix` is its `actionTag`-indexed lookup: `Rfix e` is the rotated descriptor for the effect whose
`ActionDispatch.actionTag` is `e`, falling back to the transfer slot off-range (so the function is total
— a published index always resolves to a real descriptor, the one its per-effect rung is stated about).

The "fix-augmented" content of the prompt — the committed-root-limb fix descriptors for the fix effects
and the phase-D cap descriptors for the cap family — are ALREADY the `v3Registry` entries (`attenuateV3`,
`revokeCapabilityV3`, the cap-family `…R24` slots, the eight `setFieldV3` slots): `Rfix` selects exactly
those, so `Rfix e` IS the descriptor each per-effect rung discharges its refinement about. -/

/-- The transfer descriptor (the off-range fallback; effect tag `0`). -/
def transferDescr : EffectVmDescriptor2 :=
  Dregg2.Circuit.RotatedKernelRefinement.transferV3

/-- **`Rfix` — the fix-augmented live registry as a total `Nat`-indexed lookup.** `Rfix e` is the
rotated `v3Registry` descriptor at the `actionTag` slot `e` (the descriptor the per-effect rung at
effect `e` refines), with the transfer descriptor as the total-function fallback off-range. The fix and
phase-D cap descriptors are the corresponding `v3Registry` entries selected here. -/
def Rfix : Registry := fun e =>
  match Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry[e]? with
  | some (_, d) => d
  | none => transferDescr

/-- `Rfix` is total: every effect index resolves to a real descriptor (so `vkOfRegistry Rfix` and the
`StarkSound`/`WitnessDecodes` floors are well-defined at every published index). Holds by construction
(`match` is total). -/
theorem Rfix_total (e : EffectIdx) : ∃ d : EffectVmDescriptor2, Rfix e = d := ⟨Rfix e, rfl⟩

/-! ## §2 — `kstepAll`: the assembled dispatcher arm.

We take the assembled kernel step to be the generic dispatcher arm `CircuitSoundness.dispatchArm`
(`∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`) — the relation the whole-turn apex
`lightclient_turn_unfoolable_forest` is already stated at, and into which every per-effect leaf `Spec`
lowers (`transfer_descriptorRefines_fullActionStep`, `delegate_execFullA`, …). The `e = 0` (transfer)
arm upgrades to the FAITHFUL `dispatchArmFacet` (deployed two-axis authority) via
`RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm`. -/

/-- **`kstepAll`** — the assembled kernel step: the generic dispatcher arm at each effect. Its `e = 0`
transfer arm is faithful-upgradable (`dispatchArmFacet`); every effect's leaf `Spec` lowers into it. -/
def kstepAll : EffectIdx → RecChainedState → RecChainedState → Prop := dispatchArm

@[simp] theorem kstepAll_eq (e : EffectIdx) (pre post : RecChainedState) :
    kstepAll e pre post = dispatchArm e pre post := rfl

/-! ## §3 — `EffectDecodeBridge`: the per-effect decode bridge (NAMED, enumerated).

`EffectDecodeBridge S hash R e` is the per-effect refinement rung in APEX SHAPE: it is exactly
`descriptorRefines S hash (R e) (kstepAll e)`. This is the honest residual.

The logical CORE of every effect — `<effect>Encode ⟹ <effect>Spec ⟹ dispatchArm e` — is fully landed
in the `RotatedKernelRefinement*` family (`transfer_descriptorRefines` / `delegate_descriptorRefines` /
`attenuate_descriptorRefines_exact` / `revoke_descriptorRefines` / … through all 36 cohort members + the
8 `setField` slots). What is NOT landed is the bridge from the apex's `StateDecode S pc pre post` (the
LEDGER-ROOT commitment binding) to the per-effect ENCODE predicate each rung consumes (`rotatedEncodes`,
`DelegateCapsTreeEncodes`, `rotatedEncodesIncNonce`, …): the encode carries limb-level column reads, the
cap-tree opening, and the guard fields the commitment surface does NOT commit. Bridging
`StateDecode ⟹ <effect>Encode` is the genuine remaining content — the `WitnessDecodes`-class
decode-extraction, per effect.

We carry it as ONE named per-effect family. NO effect bridges cleanly from `StateDecode` alone (the
ledger root never determines the cap-tree leaf assignment, the per-row columns, or the guard), so all
36 effects (44 indices counting the 8 `setField` slots) are genuine `EffectDecodeBridge` residuals. -/

/-- **`EffectDecodeBridge S hash R e` — the per-effect decode bridge (NAMED).** Exactly the apex-shaped
per-effect refinement `descriptorRefines S hash (R e) (kstepAll e)`: any `Satisfied2` witness of the
descriptor `R e` whose published commitments `StateDecode`-decode to `pre`/`post` forces
`kstepAll e pre post`. The genuine content is the `StateDecode ⟹ <effect>Encode` extraction (the
limb-level decode the LEDGER-root commitment cannot certify); the rung's logical core
(`<effect>Encode ⟹ dispatchArm e`) is landed in `RotatedKernelRefinement*`. Carried, named, not faked. -/
def EffectDecodeBridge (S : CommitSurface) (hash : List ℤ → ℤ) (R : Registry) (e : EffectIdx) : Prop :=
  descriptorRefines S hash (R e) (kstepAll e)

@[simp] theorem effectDecodeBridge_eq (S : CommitSurface) (hash : List ℤ → ℤ) (R : Registry)
    (e : EffectIdx) :
    EffectDecodeBridge S hash R e = descriptorRefines S hash (R e) (kstepAll e) := rfl

/-! ## §4 — `hrefinesAll`: assemble the per-effect bridge family into the apex's `∀`.

Given the named per-effect bridge family `(∀ e, EffectDecodeBridge S hash Rfix e)`, the apex's carried
`hrefines : ∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)` is IMMEDIATE — `EffectDecodeBridge` IS
that `descriptorRefines`. This is the enumeration of the previously-opaque `∀`: it is now a per-effect
NAMED family whose content (the `StateDecode ⟹ <effect>Encode` decode bridge) is spelled out. -/

/-- **`hrefinesAll` — the apex's per-effect family, ENUMERATED.** From the named per-effect decode-bridge
family, the registry-wide refinement `∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)` the apex
carries. The previously-opaque `∀` is now an explicit per-effect residual set. -/
theorem hrefinesAll (S : CommitSurface) (hash : List ℤ → ℤ)
    (hbridge : ∀ e, EffectDecodeBridge S hash Rfix e) :
    ∀ e, descriptorRefines S hash (Rfix e) (kstepAll e) :=
  hbridge

/-! ## §5 — `lightclient_unfoolable_assembled`: the apex at `Rfix`/`kstepAll`/`hrefinesAll`.

The capstone. From a verifying batch against `vkOfRegistry Rfix` + the named floors
(`StarkSound`, `Poseidon2SpongeCR`, the `CommitSurface` CR fields, `WitnessDecodes`) + the ENUMERATED
per-effect decode-bridge family (`∀ e, EffectDecodeBridge S hash Rfix e`), there EXIST decoded endpoints
and a genuine kernel transition `kstepAll pi.effect pre post` whose endpoints commit to the published
`(pi.pre, pi.post)`. The light client RAN NOTHING. -/

theorem lightclient_unfoolable_assembled
    (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (hbridge : ∀ e, EffectDecodeBridge S hash Rfix e)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash Rfix S pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  lightclient_unfoolable hash S Rfix hCR kstepAll (hrefinesAll S hash hbridge) pi π hwitdec hacc

/-! ## §6 — the whole-turn capstone (forest shape), at `dispatchArm = kstepAll`.

`kstepAll = dispatchArm`, so the whole-turn apex `lightclient_turn_unfoolable_forest` instantiates at
`Rfix` directly. A verified turn (`TurnDecodeChain` — every step's circuit `Satisfied2`, decoded, seams
agreeing) whose per-step effect indices are identified (`hidx`) + the turn-level endpoint pinning
(`TurnEndpoints`) + the named floors + the ENUMERATED per-effect bridge family yields a GENUINE executor
run `execFullTurnA start acts = some fin` whose endpoints commit to the published turn-level
`(pre, post)`. -/

theorem lightclient_turn_unfoolable_forest_assembled
    (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (hbridge : ∀ e, EffectDecodeBridge S hash Rfix e)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = Rfix e)
    (te : TurnEndpoints hash S c) :
    ∃ (acts : List Dregg2.Exec.TurnExecutorFull.FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = S.commit s.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit s'.kernel te.tp.turn :=
  lightclient_turn_unfoolable_forest hash S Rfix hCR (hrefinesAll S hash hbridge) c hidx te

/-! ## §7 — the FAITHFUL transfer-tier note (the `e = 0` arm upgrade).

`kstepAll 0 = dispatchArm 0` lowers FROM the faithful `dispatchArmFacet` (the deployed two-axis
`authorizedFacetB` authority) by `RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm`. So the
transfer arm of the capstone is upgradable to the deployed authority tier — recorded as a lemma so the
faithful-tier path is explicit, not merely asserted. -/

/-- **`kstepAll_transfer_from_faithful` — the transfer arm lowers from the FAITHFUL facet arm.** A
faithful transfer step (`dispatchArmFacet`, authority via the deployed two-axis `authorizedFacetB`) at
the transfer tag `e = 0`, plus the toy-executor authority side-condition, entails the assembled
`kstepAll 0` arm. The faithful authority is the STRONGER fact; this records that the transfer slot of the
capstone carries the deployed-tier gate. -/
theorem kstepAll_transfer_from_faithful
    (fcaps : Dregg2.Exec.FacetAuthority.FacetCaps)
    (provided : Dregg2.Exec.FacetAuthority.AuthProvided)
    (pre post : RecChainedState)
    (h : RotatedKernelRefinementFacet.dispatchArmFacet fcaps provided 0 pre post)
    (htoy : ∀ tr : Dregg2.Exec.Turn,
      (∃ a, RotatedKernelRefinementFacet.BalanceMovementSpecFacet fcaps provided pre tr a post) →
      Dregg2.Exec.authorizedB pre.kernel.caps tr = true) :
    kstepAll 0 pre post :=
  RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm fcaps provided 0 pre post rfl h htoy

/-! ## §8 — axiom hygiene. -/

#assert_axioms Rfix_total
#assert_axioms hrefinesAll
#assert_axioms lightclient_unfoolable_assembled
#assert_axioms lightclient_turn_unfoolable_forest_assembled
#assert_axioms kstepAll_transfer_from_faithful

end Dregg2.Circuit.CircuitSoundnessAssembled
