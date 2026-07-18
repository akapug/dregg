# Verified rotated layout: final architecture and flag-day procedure

Status: **BUILT, byte-preserving.** This is Goal A only. The deployed wide descriptors and VKs did
not move; the narrow optimizer deployment remains Goal B.

## One source and its proof

`metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` owns the rotated pre-iroot geometry. The current
source is `rotatedNumPreLimbs` plus the `rotated178 : RotatedLayout` data instance. In particular,
the ten faithful-8 groups—including non-contiguous `fields` and circuit-only `cells`—have concrete
coordinates only in `rotated178.groups`.

`Legal rotated178` proves, by `native_decide`, that:

- every named group has one lane-0 column and exactly seven completion columns;
- group names are unique and every `GroupName` is present;
- all occupied columns are disjoint and below `numPreLimbs`; and
- the post-head body is divisible into arity-3 fold groups.

Together with `rotated178_complete`, those obligations make the current 178 columns a complete
tiling of `0..177`: no overlap, no gap, no missing semantic group, and no partial fold chunk.

## How consumers derive

1. **Lean emit.** `EffectVmEmitRotationV3.layoutGroupCol` projects named lanes through
   `rotated178.groupCol`; all deployed `*GroupCol` definitions use that projection. The theorems in
   `RotatedLayoutBridge.lean` are now definitional equalities (`rfl`), retained as the public proof
   surface and byte-drift tripwire. The block extent and carrier counts derive from
   `rotatedNumPreLimbs`.
2. **Lean → Rust.** `EmitLayoutManifest.lean` emits `NUM_PRE_LIMBS`, the literal
   `ROTATED_GROUP_TABLE`, and generated semantic aliases such as `FIELDS_ROOT_GROUP`. The numeric
   table is emitted once; aliases index it rather than duplicating coordinates.
3. **Rust producers and AIR.** `cell/src/commitment.rs::compute_rotated_pre_limbs`, the independent
   live producer `turn/src/rotation_witness.rs::produce`, and
   `circuit/src/effect_vm/trace_rotated.rs` all consume the generated constants. There are no local
   named-group coordinate arrays or `*_group_col` formulas left. `cells` remains intentionally
   producer-zero: its generated completion columns 169..175 are filled only by the create-cell
   circuit path.

The scalar spine (`B_SPAN`, octet bases, and related deployed offsets) is still authored in Lean and
emitted by the same manifest. It is not an independent Rust layout. The Rust tiling unit test remains
as an artifact-integrity check over generated data, not as the legality source.

Current HEAD geometry: 178 pre-limbs, ten faithful-8 groups, block span 239, 134 rotated chip sites,
42 v1 PIs, 46 base rotated PIs, and 66 wide PIs.

## Geometry flag-day procedure

1. Edit `rotatedNumPreLimbs` and/or the `rotated178` data in `RotatedLayout.lean`. A group relocation
   is changed only there. Do not hand-edit generated Rust.
2. Close `rotated178_legal` and `rotated178_complete` with `native_decide`; an overlap, missing group,
   wrong group width, out-of-bounds column, or bad fold extent must fail here.
3. Build `RotatedLayoutBridge` and the narrow/wide refinement closure. The bridge should remain
   definitional; if it does not, the emit stopped deriving.
4. Run `scripts/emit-descriptors.sh`. A code-projection-only update may install without a regeneration
   acknowledgment only when descriptor bytes and fingerprint constants are identical. A real deployed
   geometry change will alter descriptor bytes and must remain blocked until a separately authorized
   federation re-key supplies `DREGG_VK_REGEN_ACK`.
5. Run the Rust layout tiling/disjointness tests and `scripts/check-descriptor-drift.sh`.

For the byte-preserving Goal-A refactor recorded here, step 4 took the generated-Rust-only branch:
one Lean-authored module changed, while descriptor bytes and fingerprint constants remained identical.

## Explicitly not done

Goal B is untouched: no narrow descriptor was deployed, no VK was regenerated, and the named
`effNarrow_rejects_wrong_facet` / narrow WIRE-wrapper residuals remain exactly that—named deployment
work, not proof holes in Goal A. Dead AIR columns such as `BUS_FACT` are also not byte-safe cleanup;
removing them belongs to a separately acknowledged descriptor change.
