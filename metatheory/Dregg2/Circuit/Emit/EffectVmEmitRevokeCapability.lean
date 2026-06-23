/-
# Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability — the cap-REMOVAL effect `RevokeCapability`
  (effect selector 24), EMITTED onto the runnable EffectVM `cap_root` column as its v1 FACE.

## What this module is (the v1 FACE — the graduation base for `revokeCapabilityVmDescriptor2`)

`RevokeCapability` removes a slot from the actor's c-list, so the `cap_root` MOVES to the digest of
the post (slot-deleted) cap-table while the rest of the cell state is FROZEN — structurally the SAME
row shape as `AttenuateCapability` (a `cap_root` COLUMN MOVE + frame freeze + the GROUP-4 commitment
chain binding the moved post-state). The kernel target is `recKRevokeTarget` /
`execFull_revoke_removeEdge` of `Exec/TurnExecutorFull.lean` (revocation always commits — it only
SUBTRACTS authority), which `Exec/EffectsAuthority.lean` flags as "already fully characterized."

This module emits that v1 face by REUSING the validated `EffectVmEmitAttenuateA` row-gate set
(`attenuateRowGates`: cap-root MOVE + balance/nonce/reserved freeze + 8 fields freeze) and its
ordered GROUP-4 hash sites (`attenuateHashSites`): the cap-graph row shape is identical (one
`cap_root` move, everything else frozen, the moved root bound into `state_commit`), only the AIR
IDENTITY (name) differs. So every faithfulness / anti-ghost / commitment-binding theorem of
`EffectVmEmitAttenuateA` applies VERBATIM — we re-export the deliverables under the revoke name.

The GENUINE cap-table content (the sorted-tree slot DELETION: membership-open the held leaf, post
root = the zero/padding leaf folded up the same path) is the v2 leg
(`EffectVmEmitV2.revokeCapabilityVmDescriptor2`): a `MapOp.read` of the held value authenticated
against the before `cap_root` + a `MapOp.write` of the ZERO sentinel value (the slot's rights
removed), under the named Poseidon2-CR floor (`opensTo_functional` / `writesTo_functional`). The v1
face here pins only the `cap_root` COLUMN MOVE; the in-circuit cap-table opening is the v2 `MapOp`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem (inherited from the
reused `EffectVmEmitAttenuateA` lemmas — no new proof obligation is introduced). Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA

namespace Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateRowGates attenuateHashSites AttenRowIntent attenuateRowGates_holds_iff
   attenuateVm_rejects_wrong_output)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The emitted v1 FACE descriptor.

The cap-graph row gates (`attenuateRowGates`) + the GROUP-4 hash sites (`attenuateHashSites`) are
the validated `EffectVmEmitAttenuateA` set — the cap-graph row shape is identical for revoke (one
`cap_root` move, everything else frozen). Only the `name` (the AIR fingerprint) differs. -/

/-- The `RevokeCapability` AIR identity (the fingerprint binding). Distinct from `attenuateA-v1`
so the descriptor registry keys it to selector 24, not the attenuate template. -/
def revokeCapabilityVmAirName : String := "dregg-effectvm-revokecapability-v1"

/-- **`revokeCapabilityVmDescriptor`** — the `RevokeCapability` effect's concrete circuit v1 face:
the cap-root MOVE + frame-freeze gates ++ transition continuity ++ the row-0 boundary pins (REUSED
from `EffectVmEmitAttenuateA.attenuateVmDescriptor`), with the 4 ordered GROUP-4 hash sites binding
the moved post-state. Only the `name` differs from the attenuate template. -/
def revokeCapabilityVmDescriptor : EffectVmDescriptor :=
  { EffectVmEmitAttenuateA.attenuateVmDescriptor with name := revokeCapabilityVmAirName }

/-- The descriptor's row gates ARE the attenuate set (the cap-graph row shape is identical). -/
theorem revokeCapabilityVmDescriptor_constraints :
    revokeCapabilityVmDescriptor.constraints = EffectVmEmitAttenuateA.attenuateVmDescriptor.constraints :=
  rfl

/-- The descriptor's hash sites ARE the attenuate GROUP-4 chain (same commitment binding). -/
theorem revokeCapabilityVmDescriptor_hashSites :
    revokeCapabilityVmDescriptor.hashSites = attenuateHashSites :=
  rfl

/-! ## §2 — FAITHFULNESS + ANTI-GHOST, re-exported under the revoke name.

The cap-graph row faithfulness (`attenuateRowGates_holds_iff`: the per-row gates hold IFF the
cap-graph move intent holds) and the anti-ghost (a wrong cap-root move is UNSAT) are the
`EffectVmEmitAttenuateA` deliverables; the revoke v1 face's gate list is DEFINITIONALLY theirs, so
they re-state by `rfl`-transport. -/

/-- **`revokeCapabilityVm_faithful`** — on a cap-graph (revoke) row, the emitted descriptor's per-row
gates hold IFF the cap-graph move intent holds. The revoke v1 face's gate set IS the attenuate set
(`revokeCapabilityVmDescriptor.constraints = attenuateRowGates ++ …` by `rfl`), so the
`EffectVmEmitAttenuateA` faithfulness theorem is the revoke face's faithfulness theorem. -/
theorem revokeCapabilityVm_faithful (env : VmRowEnv) :
    (∀ c ∈ attenuateRowGates, c.holdsVm env false false) ↔ AttenRowIntent env :=
  attenuateRowGates_holds_iff env

/-- **Anti-ghost (revoke).** A row whose post-state is NOT the intent move does NOT satisfy the
per-row gates — the same tooth `EffectVmEmitAttenuateA` proves, under the revoke name. -/
theorem revokeCapabilityVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ AttenRowIntent env) :
    ¬ (∀ c ∈ attenuateRowGates, c.holdsVm env false false) :=
  attenuateVm_rejects_wrong_output env hwrong

#assert_axioms revokeCapabilityVm_faithful
#assert_axioms revokeCapabilityVm_rejects_wrong_output

end Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability
