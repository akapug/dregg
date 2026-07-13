import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.RotatedLayout

/-
# RotatedLayoutBridge — the emit's hand-carried positions ARE the RotatedLayout projection

Phase 2b, non-invasive: rather than rewrite the DEPLOYED `EffectVmEmitRotationV3.*GroupCol` defs (which
risks moving a descriptor byte / VK), we PROVE each one equals `rotated178.groupCol`. This makes the
verified `RotatedLayout` (whose `Legal` proof guarantees disjointness/bounds/alignment) the proven
source of truth for the emit's geometry — WITHOUT changing a single emitted byte.

Once every group is bridged here, the emit defs can be refactored to literally project (a pure,
proof-backed refactor), and the producer/circuit mirrors pinned to the same source — killing the drift
class that caused the revoked-root carrier bug. This file starts with `nullifier` as the pattern.
-/

namespace Dregg2.Circuit.Emit

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (nullifierRootGroupCol B_NULLIFIER_ROOT_OFF)

/-- The deployed `nullifierRootGroupCol` DERIVES from the layout: its hand-carried position equals the
    `RotatedLayout` projection at every lane. rotated178 is now the PROVEN source for this group. -/
theorem nullifierRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    nullifierRootGroupCol blockBase i
      = blockBase + (rotated178.groupCol .nullifier i).getD 0 := by
  unfold nullifierRootGroupCol
  congr 1
  fin_cases i <;> native_decide

end Dregg2.Circuit.Emit
