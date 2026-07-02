/-
# Dregg2.Circuit.Emit.CarrierComposed — STEP-3 CHIP-GATE COMPOSES (sovereign · membership).

The RESOLVED-FORK chip-compress lane: the two v12-walled carriers whose teeth are a Poseidon2
COMPRESS of the committed pubkey octet (`B_PUBKEY8` = limbs 104..=111, filled UNCONDITIONALLY by the
STEP-2 producer as `canonical_32_to_felts_8(pubkey)`). This module WIRES the pre-proven
`CarrierOctetGates` gates onto the deployed descriptors — it is the natural composition site (imports
BOTH `EffectVmEmitRotationV3` (via `CarrierOctetGates`) and the gates), which did not exist before
STEP-3. NO registry touch, NO regen (the big-bang regen — the main loop — wires these into the emit
set, bumps `public_input_count`, and re-keys the apex); this module only DEFINES the composed
descriptors and re-exports the forcing keystones so they type-check against the real bases.

## §Sovereign — EXACT executor match (SAT by construction)

`withSovereignKeyCommit makeSovereignV3 SOVEREIGN_KEY_COMMIT_COL` binds the FOUR executor KEY_COMMIT
teeth (`columns.rs::WITNESS_KEY_COMMIT_0..3` = cols 23..=26, row-0-pinned to PI by the ALREADY-CLOSED
record-pin family — `makeSovereignV3.piCount = 54` is UNTOUCHED, the gate only widens `traceWidth` and
appends 4 chip lookups + 4 teeth welds) to the in-AIR `canonical_32_to_felts_4` of the committed
`B_PUBKEY8` octet. The executor's `KEY_COMMIT` (`proof_verify.rs::pubkey_to_witness_key_commit` =
`canonical_32_to_felts_8` then FOUR `hash_4_to_1` over the interleave quads) EQUALS this in-AIR
function LANE-FOR-LANE (the `CarrierOctetGates` module-doc EXECUTOR-COMPRESS VERDICT, verified), and
the octet is filled with the SAME `canonical_32_to_felts_8` — so the gate is SAT on every honest
sovereign turn.

## §Membership — chip-native `node8`, executor RE-ALIGNED (SAT since `687601953`)

`withMembershipPubkeyCompress` realizes the chip-native injective 1-felt compress (arity-16 `node8`
over `pubkey8 ‖ 0⁸`). The CarrierOctetGates module-doc NAMED the executor re-alignment as owed; commit
`687601953` (`feat(big-bang/membership): re-align the executor membership compress to the chip-native
node8 form`) LANDED it — `membership_verifier::compress` is now `compress_member` = lane 0 of the
deployed chip's `node8` row, so the fail-open law is satisfied and the gate binds teeth the executor
actually checks. `effFieldsReadOpenV3` anchors the `authorized_root` (a fields-map value under the
committed ~124-bit `fields_root`). The membership BASE descriptor is NOT yet a committed registry
member (STEP-3 open — see the module note below), so this module composes the gates onto the
parametric base; the main-loop regen pins the concrete base + teeth/index columns.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the
named `ChipTableSoundN` hypotheses, exactly as in the underlying gates.
-/
import Dregg2.Circuit.Emit.CarrierOctetGates

namespace Dregg2.Circuit.Emit.CarrierComposed

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 Satisfied2 ChipTableSoundN VmTrace envAt)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (makeSovereignV3)
open Dregg2.Circuit.Emit.CarrierOctetGates
  (withSovereignKeyCommit withSovereignKeyCommit_forces withSovereignKeyCommit_rejects_forged
   keyCommitSpec octetVals permOutOf B_PUBKEY8 BEFORE_BLOCK_BASE)

set_option autoImplicit false

/-- The sovereign KEY_COMMIT teeth column base (`columns.rs::WITNESS_KEY_COMMIT_0`, cols 23..=26 —
the executor's row-0-PI-pinned owner-key-commit teeth). -/
def SOVEREIGN_KEY_COMMIT_COL : Nat := 23

/-- **`makeSovereignV3Keyed`** — the deployed `makeSovereignVmDescriptor2R24` COMPOSED with the in-AIR
KEY_COMMIT compress gate: the 4 executor teeth (cols 23..=26) are forced EQUAL to
`canonical_32_to_felts_4` of the committed `B_PUBKEY8` octet. `piCount = 54` UNCHANGED (the record-pin
is closed; the gate binds EXISTING teeth columns, adding only trace width + chip lookups). -/
def makeSovereignV3Keyed : EffectVmDescriptor2 :=
  withSovereignKeyCommit makeSovereignV3 SOVEREIGN_KEY_COMMIT_COL

/-- The KEY_COMMIT compose does NOT touch the closed record-pin PI count (54). -/
theorem makeSovereignV3Keyed_piCount : makeSovereignV3Keyed.piCount = makeSovereignV3.piCount := rfl

/-- **THE SOVEREIGN KEYSTONE, on the deployed base.** A `Satisfied2` of the composed descriptor
forces every published KEY_COMMIT tooth (cols 23..=26) EQUAL to `canonical_32_to_felts_4`
(`A := chip_absorb_all_lanes`) of the committed BEFORE `B_PUBKEY8` octet — a forged sovereign owner
key is UNSAT for a ledgerless client. Direct instantiation of `withSovereignKeyCommit_forces`. -/
theorem makeSovereignV3Keyed_forces (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash makeSovereignV3Keyed minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ q : Fin 4, (envAt t i).loc (SOVEREIGN_KEY_COMMIT_COL + q.val)
      = keyCommitSpec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) q :=
  withSovereignKeyCommit_forces A hash makeSovereignV3 SOVEREIGN_KEY_COMMIT_COL
    minit mfin maddrs t hChip hsat i hi hnotlast

/-- **TOOTH, on the deployed base** — a forged owner key (a KEY_COMMIT tooth that is not the compress
of the committed pubkey octet) is UNSAT. -/
theorem makeSovereignV3Keyed_rejects_forged (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) (q : Fin 4)
    (hforged : (envAt t i).loc (SOVEREIGN_KEY_COMMIT_COL + q.val)
      ≠ keyCommitSpec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) q) :
    ¬ Satisfied2 hash makeSovereignV3Keyed minit mfin maddrs t :=
  withSovereignKeyCommit_rejects_forged A hash makeSovereignV3 SOVEREIGN_KEY_COMMIT_COL
    minit mfin maddrs t hChip i hi hnotlast q hforged

#assert_axioms makeSovereignV3Keyed_forces
#assert_axioms makeSovereignV3Keyed_rejects_forged

-- The compose preserves the closed record-pin PI count.
#guard makeSovereignV3Keyed.piCount == makeSovereignV3.piCount

end Dregg2.Circuit.Emit.CarrierComposed
