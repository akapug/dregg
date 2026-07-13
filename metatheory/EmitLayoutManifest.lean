/-
# EmitLayoutManifest — the EffectVM rotated LAYOUT, exported from Lean as Rust source.

Lean is the source of truth for the rotated column geometry: it defines the limb layout and it emits
the constraint descriptors that READ those columns. But the Rust side ALSO needs the layout — the
producer (`turn::rotation_witness`) WRITES witness values into those columns, and the audit gates
check them. Historically Rust re-declared the whole geometry by hand (~89 `pub const`s mirroring
these defs), and the two drifted:

* the REVOKED-ROOT flag day inserted `revoked_root` at base limb 37 and shifted every limb ≥ 37 by
  +1. The producer moved (`write_lanes([33, 38..=44])`); the Lean perms/VK completion welds did NOT
  (they still read limb 37 — which IS `revoked_root` lane-0). Every honest setPermissions /
  setVerificationKey turn was UNSAT in-circuit until that was found;
* `B_SPAN` grew 227 → 239 and a hand-pinned Rust audit column rotted 439 → 451 silently;
* the `vaultSat` satisfaction span grew 64 columns and its hand-pinned width rotted too.

Every one of those is a producer/constraint (or gate/artifact) disagreement about a number that has
exactly ONE true value. So this emitter prints the layout AS RUST, the emit pipeline installs it as
`circuit/src/effect_vm/layout_generated.rs`, and both sides read the same constants. A disagreement
becomes a compile-time impossibility rather than a soundness bug that proves fine on the members you
happened to test.

What stays hand-written: the SEMANTIC teeth (does a forged witness refuse, does the weld bite). Those
must remain independent — they test properties, not coordinates.

SCRATCH executable: `lake env lean --run EmitLayoutManifest.lean`
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmit (EFFECT_VM_WIDTH)

namespace EmitLayoutManifest

/-- One exported constant: Rust name, value, and the doc line that travels with it. -/
structure Item where
  name : String
  value : Nat
  doc : String

/-- The rotated-layout spine. Each entry is a number the Rust side previously re-declared by hand. -/
def items : List Item :=
  [ { name := "EFFECT_VM_WIDTH", value := EFFECT_VM_WIDTH,
      doc := "the v1 EffectVM face width — the base every rotated member graduates from" }
  , { name := "B_SPAN", value := B_SPAN,
      doc := "one rotated state block's span (BEFORE and AFTER each occupy B_SPAN columns)" }
  , { name := "AFTER_BLOCK_OFF", value := AFTER_BLOCK_OFF,
      doc := "column offset from a member's face to its AFTER block (= B_SPAN)" }
  , { name := "C_SPAN", value := C_SPAN,
      doc := "the caveat region's span" }
  , { name := "C_COMMIT", value := C_COMMIT,
      doc := "the caveat commitment carrier, in-region" }
  , { name := "C_RC_OFF", value := C_RC_OFF,
      doc := "the DFA route-commitment (rc) carrier, in-region" }
  , { name := "APPENDIX_SPAN", value := APPENDIX_SPAN,
      doc := "2*B_SPAN + C_SPAN — the rotated appendix appended to the v1 face" }
    -- the committed base limbs (pre-iroot)
  , { name := "B_RECORD_DIGEST", value := B_RECORD_DIGEST,
      doc := "committed record/authority digest limb" }
  , { name := "B_CAP_ROOT", value := B_CAP_ROOT, doc := "committed capability-root limb" }
  , { name := "B_NULLIFIER_ROOT_OFF", value := B_NULLIFIER_ROOT_OFF,
      doc := "committed nullifier-root limb" }
  , { name := "B_COMMITMENTS_ROOT", value := B_COMMITMENTS_ROOT,
      doc := "committed commitments-root limb" }
  , { name := "B_HEAP_ROOT", value := B_HEAP_ROOT, doc := "committed heap-root limb" }
  , { name := "B_LIFECYCLE", value := B_LIFECYCLE, doc := "committed lifecycle limb" }
  , { name := "B_EPOCH", value := B_EPOCH, doc := "committed epoch limb" }
  , { name := "B_COMMITTED_HEIGHT", value := B_COMMITTED_HEIGHT,
      doc := "last SCALAR pre-iroot limb (disc/perms/vk/mode/fields-root ride past it)" }
  , { name := "B_DISC", value := B_DISC, doc := "WAVE-1 committed discriminant limb" }
  , { name := "B_PERMS", value := B_PERMS,
      doc := "WAVE-2 committed permissions-digest limb (lane 0 of the faithful 8-felt group)" }
  , { name := "B_VK", value := B_VK,
      doc := "WAVE-2 committed verification-key-digest limb (lane 0 of the 8-felt group)" }
  , { name := "B_MODE", value := B_MODE, doc := "WAVE-3 committed mode limb" }
  , { name := "B_FIELDS_ROOT", value := B_FIELDS_ROOT,
      doc := "WAVE-3 committed fields-root digest limb" }
  , { name := "B_REVOKED_ROOT", value := B_REVOKED_ROOT,
      doc := "REVOKED-ROOT flag-day limb — inserted at 37, shifting every limb >= 37 by +1" }
    -- THE WELD OFFSETS. These are the numbers the setPerms/setVK bug lived in.
  , { name := "B_PERMS_COMPLETION", value := B_PERMS_COMPLETION,
      doc := "FIRST perms-digest completion limb; permsHash[1..7] ride B_PERMS_COMPLETION..+6. \
              The producer writes these lanes and the in-circuit weld reads them: ONE source." }
  , { name := "B_VK_COMPLETION", value := B_VK_COMPLETION,
      doc := "FIRST vk-digest completion limb; vkHash[1..7] ride B_VK_COMPLETION..+6" }
  , { name := "B_IROOT", value := B_IROOT, doc := "the iroot limb (pre-iroot limbs end here)" }
  , { name := "B_STATE_COMMIT", value := B_STATE_COMMIT, doc := "the state-commitment limb" }
  ]

/-- Emit one Rust `pub const`. -/
def renderItem (i : Item) : String :=
  s!"/// {i.doc}\npub const {i.name}: usize = {i.value};\n"

def header : String :=
  "// @generated by metatheory/EmitLayoutManifest.lean — DO NOT EDIT BY HAND.\n\
   //\n\
   // The rotated EffectVM column layout, exported from the Lean that DEFINES it and that emits the\n\
   // constraint descriptors READING it. The Rust producer (`turn::rotation_witness`) WRITES these\n\
   // same columns, and the audit gates check them — so all three now read one source instead of\n\
   // three hand-maintained mirrors.\n\
   //\n\
   // This module exists because the mirrors drifted, and drift here is not a lint failure — it is a\n\
   // soundness bug. The perms/VK completion weld once read limb 37 (`revoked_root` lane-0) while the\n\
   // producer wrote limb 38, and every honest setPermissions/setVerificationKey turn was UNSAT.\n\
   //\n\
   // Regenerate with the ack-gated emit pipeline (`scripts/emit_descriptors.py`); never hand-edit.\n\n"

def main : IO Unit := do
  IO.print header
  for i in items do
    IO.print (renderItem i)
    IO.print "\n"

end EmitLayoutManifest

def main : IO Unit := EmitLayoutManifest.main
