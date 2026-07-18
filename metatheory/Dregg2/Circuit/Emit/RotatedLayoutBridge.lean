import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.RotatedLayout

/-
# RotatedLayoutBridge — the emit positions ARE the RotatedLayout projection

The deployed `EffectVmEmitRotationV3.*GroupCol` definitions now literally project from `rotated178`.
These equalities remain as the public proof surface and descriptor-byte tripwire: each closes by
reduction, while `rotated178_legal` carries width/name/disjointness/bounds/alignment.
-/

namespace Dregg2.Circuit.Emit

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3

/-- Every deployed `*GroupCol` DERIVES from `rotated178.groupCol` at every lane — the emit geometry is
    the verified layout's projection, byte-for-byte unchanged. -/
theorem capRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    capRootGroupCol blockBase i = blockBase + (rotated178.groupCol .cap i).getD 0 := by
  rfl

theorem heapRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    heapRootGroupCol blockBase i = blockBase + (rotated178.groupCol .heap i).getD 0 := by
  rfl

theorem fieldsRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    fieldsRootGroupCol blockBase i = blockBase + (rotated178.groupCol .fields i).getD 0 := by
  rfl

theorem nullifierRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    nullifierRootGroupCol blockBase i = blockBase + (rotated178.groupCol .nullifier i).getD 0 := by
  rfl

theorem commitmentsRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    commitmentsRootGroupCol blockBase i = blockBase + (rotated178.groupCol .commitments i).getD 0 := by
  rfl

theorem revokedRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    revokedRootGroupCol blockBase i = blockBase + (rotated178.groupCol .revoked i).getD 0 := by
  rfl

theorem cellsRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    cellsRootGroupCol blockBase i = blockBase + (rotated178.groupCol .cells i).getD 0 := by
  rfl

end Dregg2.Circuit.Emit
