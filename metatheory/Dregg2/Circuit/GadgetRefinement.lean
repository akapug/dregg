/-
# Dregg2.Circuit.GadgetRefinement — §8 gadget witnesses as refinements of the circuit tower.

Links the emitted wire forms in `Exec/CircuitEmit` and `Exec/CircuitEmitGadgets` to the Crypto
portal predicates (`MerkleMembers`, `NonMember`, `InWindow`) via the relational refinement
framework in `Refinement.lean`. Each bridge composes emit-faithfulness with the gadget's own
`*_bridge` theorem — the same soundness∧completeness the Rust decoder inherits.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Exec.CircuitEmit
import Dregg2.Exec.CircuitEmitGadgets
import Dregg2.Crypto.Merkle
import Dregg2.Crypto.NonMembership
import Dregg2.Crypto.Temporal

namespace Dregg2.Circuit.GadgetRefinement

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.CircuitEmitGadgets
open Dregg2.Crypto.Merkle

/-! ## §1 — Merkle membership: emitted witness ⊑ portal. -/

section Merkle
variable {Digest : Type} [LinearOrder Digest]
variable (compress : Digest → Digest → Digest)

/-- **`gadget_step`** — auth-witness verification as a `StepRel`: public inputs `(root, leaf)`,
witness = emitted Merkle trace, post = the same boundary (identity on PIs). -/
def gadget_step : StepRel (Digest × Digest) (List (Row Digest)) (Digest × Digest) :=
  fun (root, leaf) rows (root', leaf') =>
    root' = root ∧ leaf' = leaf ∧
    satisfiedEmittedMerkle compress emittedMerkle rows root leaf

/-- The CRYPTO portal step: same boundary, outcome = `MerkleMembers`. -/
def merklePortalStep : StepRel (Digest × Digest) (List (Row Digest)) (Digest × Digest) :=
  fun (root, leaf) _ (root', leaf') =>
    root' = root ∧ leaf' = leaf ∧ MerkleMembers compress root leaf

/-- **`merkle_membership_refines_portal`** — SOUNDNESS: every emitted Merkle witness refines to
genuine membership. Composes `emittedMerkle_bridge` with boundary equalities. -/
theorem merkle_membership_refines_portal :
    Refines (gadget_step compress) (merklePortalStep compress) := by
  intro ⟨root, leaf⟩ rows ⟨root', leaf'⟩ h
  obtain ⟨hroot, hleaf, hsat⟩ := h
  rw [hroot, hleaf]
  exact ⟨rfl, rfl, (emittedMerkle_bridge compress root leaf).mp ⟨rows, hsat⟩⟩

/-- Existential emitted satisfaction ⟺ portal membership (the headline bridge). -/
theorem merkle_emitted_iff_portal (root leaf : Digest) :
    (∃ rows, satisfiedEmittedMerkle compress emittedMerkle rows root leaf)
      ↔ MerkleMembers compress root leaf :=
  emittedMerkle_bridge compress root leaf

end Merkle

/-! ## §2 — Non-membership: emitted witness ⊑ portal. -/

section NonMembershipBridge
open Dregg2.Crypto.NonMembership
variable {Digest : Type} [LinearOrder Digest]
variable (compress : Digest → Digest → Digest)

/-- The EMITTED non-membership step. -/
def nonmembershipEmittedStep :
    StepRel (Digest × Digest) (Dregg2.Crypto.NonMembership.CircuitIR Digest × List Digest)
      (Digest × Digest) :=
  fun (root, e) ⟨circuit, leaves⟩ (root', e') =>
    root' = root ∧ e' = e ∧
    satisfiedEmittedNonMembership compress emittedNonMembership circuit root e leaves

/-- The CRYPTO portal step: genuine absence. -/
def nonmembershipPortalStep :
    StepRel (Digest × Digest) (Dregg2.Crypto.NonMembership.CircuitIR Digest × List Digest)
      (Digest × Digest) :=
  fun (root, e) ⟨_, leaves⟩ (root', e') =>
    root' = root ∧ e' = e ∧ NonMember leaves e

/-- **`nonmembership_refines_portal`** — SOUNDNESS via `emittedNonMembership_bridge`. -/
theorem nonmembership_refines_portal :
    Refines (nonmembershipEmittedStep compress) nonmembershipPortalStep := by
  intro ⟨root, e⟩ ⟨circuit, leaves⟩ ⟨root', e'⟩ h
  obtain ⟨hroot, he, hsat⟩ := h
  rw [hroot, he]
  exact ⟨rfl, rfl, (emittedNonMembership_bridge compress root e leaves).1 circuit hsat⟩

end NonMembershipBridge

/-! ## §3 — Temporal: emitted witness ⊑ `InWindow`. -/

section TemporalBridge
open Dregg2.Crypto.Temporal

/-- Public inputs `(lo, hi, t)`. -/
abbrev TemporalPI := Int × Int × Int

/-- The EMITTED temporal step. -/
def temporalEmittedStep : StepRel TemporalPI Dregg2.Crypto.Temporal.CircuitIR TemporalPI :=
  fun (lo, hi, t) circuit (lo', hi', t') =>
    lo' = lo ∧ hi' = hi ∧ t' = t ∧
    satisfiedEmittedTemporal emittedTemporal circuit lo hi t

/-- The CRYPTO portal step: `InWindow`. -/
def temporalPortalStep : StepRel TemporalPI Dregg2.Crypto.Temporal.CircuitIR TemporalPI :=
  fun (lo, hi, t) _ (lo', hi', t') =>
    lo' = lo ∧ hi' = hi ∧ t' = t ∧ InWindow lo hi t

/-- **`temporal_refines_portal`** — SOUNDNESS via `emittedTemporal_bridge`. -/
theorem temporal_refines_portal :
    Refines temporalEmittedStep temporalPortalStep := by
  intro ⟨lo, hi, t⟩ circuit ⟨lo', hi', t'⟩ h
  obtain ⟨hlo, hhi, ht, hsat⟩ := h
  rw [hlo, hhi, ht]
  exact ⟨rfl, rfl, rfl, (emittedTemporal_bridge lo hi t).mp ⟨circuit, hsat⟩⟩

end TemporalBridge

#assert_axioms merkle_membership_refines_portal
#assert_axioms merkle_emitted_iff_portal
#assert_axioms nonmembership_refines_portal
#assert_axioms temporal_refines_portal

end Dregg2.Circuit.GadgetRefinement