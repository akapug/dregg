/-
# Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide — the Lean-emitted WIDE+UMEM WELDED registry
(STAGED, VK-RISK-FREE): the MISSING VERIFIER LEG's grounded descriptor set.

The WIDE+umem weld (`prove_wide_umem_welded_staged` + the IVC fold) had a producer leg and an IVC
leg but NO Lean-emitted, byte-pinned descriptor set the wire verifier could iterate — so a welded
proof verified under no DEPLOYED descriptor (only against the descriptor the producer just built,
or the leg's own carried copy). This module CLOSES that: it welds the universal-memory cohort leg
INTO every member of the verified `CapOpenEmit.v3RegistryCapOpenWide` (the 45-member 8-felt wide
registry), IN LEAN — so the welded VK is Lean-grounded (the ONE-Lean-derived-circuit/VK invariant),
NOT hand-welded in Rust. The driver `EmitWideUMemWeldRegistryProbe.lean` writes these exact bytes to
`circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv`, pinned by
`WIDE_UMEM_WELD_REGISTRY_FP` (the sha256 the Rust side asserts) + the per-member parity tooth
(Rust's `weld_umem_into_wide_descriptor` of the bare member byte-equals the Lean-emitted welded
member). The Rust verify paths (`verify_effect_vm_rotated_with_cutover`, the IVC `admit_welded_leg`)
iterate THIS registry as a NEW accepted form beside the bare wide registry.

## The weld (the Lean twin of Rust `weld_umem_into_descriptor_with_suffix(_, dom, …, cohort:=false)`)

Purely ADDITIVE: append the single-domain cohort `umemOp` over 7 fresh main columns
`[base .. base+7)` (`base` = the wide trace width, PAST the wide carriers) + the `umemory` /
`umem_boundary` tables onto the wide member. It NEVER touches `public_input_count` nor any existing
constraint, so the wide member's whole PI vector + every PI binding (incl. all 16 wide-commit
`PiBinding`s = the 8-felt ~124-bit before/after anchors) survive UNCHANGED — the no-narrowing
property the VK epoch refused to cross. The single-domain `dom` the welded member carries is the
domain that member's effect touches (heap 1 / caps 2 / nullifiers 3, per `turn/src/umem.rs`).

## VK-RISK-FREE

A NEW registry constant BESIDE the deployed wide registry: no VK bump, nothing on the live wire,
`umem_witness_enabled` untouched. The deployed default prover/verifier stay bare until the gated VK
epoch (the owner's separate go).
-/
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.UniversalMemory (Domain)
open Dregg2.Circuit.Emit.CapOpenEmit (v3RegistryCapOpenWide)

set_option autoImplicit false

/-- The staged WIDE+umem weld name suffix (mirrors the Rust `WIDE_UMEM_WELD_SUFFIX`). A descriptor
whose `name` ends with this is the WIDE single-domain rotated+umem weld. -/
def wideUMemWeldSuffix : String := "-umem-wide-welded-staged"

/-- The single-domain universal-memory domain a wide member's effect touches, keyed by the LIVE
registry key. Mirrors the per-cell domain map of `turn/src/umem.rs` the cohort emitter uses
(Field/Heap/Balance/Nonce → `heap` (1); CapSlot → `caps` (2)): the capability verbs (grant /
attenuate / revoke / introduce / delegate / refresh / spawn, with their CapOpen / Write twins)
touch the `caps` plane; every other cohort member's state touch is a `heap`-domain write. The
multi-domain note/bridge verbs are NOT single-domain-weldable (the producer fails closed on them),
so their welded entry is unexercisable — keyed `heap` as a harmless placeholder. -/
def wideKeyUMemDomain (key : String) : Domain :=
  if "grant".isPrefixOf key || "attenuate".isPrefixOf key || "revoke".isPrefixOf key
      || "introduce".isPrefixOf key || "delegate".isPrefixOf key || "refresh".isPrefixOf key
      || "spawn".isPrefixOf key then
    Domain.caps
  else
    Domain.heap

/-- **The purely-ADDITIVE WIDE+umem weld.** The Lean twin of Rust
`weld_umem_into_descriptor_with_suffix(d, dom, WIDE_UMEM_WELD_SUFFIX, cohort := false)`: append the
single-domain cohort `umemOp` over 7 fresh main columns `[base .. base+7)` (`base = d.traceWidth`,
PAST the wide carriers) + the `umemory` (arity 8) / `umem_boundary` (arity 7, GENERAL — the wide
single-domain weld uses the general boundary, `cohort = false`) tables. The MAIN table arity is
bumped to the welded width; every OTHER table + EVERY existing constraint (incl. all 16 wide-commit
`PiBinding`s) survives untouched, and `piCount` is UNCHANGED — so the 8-felt anchors ride through at
the SAME PI offsets. NO narrowing. -/
def weldUMemIntoWide (d : EffectVmDescriptor2) (dom : Domain) : EffectVmDescriptor2 :=
  let base := d.traceWidth
  { d with
    name        := d.name ++ wideUMemWeldSuffix
    traceWidth  := base + 7
    tables      :=
      d.tables.map (fun t => if t.id = TableId.main then { t with arity := base + 7 } else t)
        ++ [umemTableDef, umemBoundaryTableDef]
    constraints :=
      d.constraints ++
        [ .umemOp
            { guard := .var (base + 6)
            , domain := dom
            , key := .var base
            , present := .var (base + 1)
            , value := .var (base + 2)
            , prevPresent := .var (base + 3)
            , prevValue := .var (base + 4)
            , prevSerial := .var (base + 5)
            , kind := Dregg2.Crypto.MemoryChecking.Kind.write } ] }

/-- **The Lean-emitted WIDE+UMEM WELDED registry (STAGED).** The welded twin of
`v3RegistryCapOpenWide`: every wide member welded with the domain its effect touches, keyed by the
SAME live registry key (name-stable, so the by-name executor verifier resolves the welded member as
`<live key>`). The driver writes these exact bytes to the staged TSV. -/
def weldedWideRegistry : List (String × EffectVmDescriptor2) :=
  v3RegistryCapOpenWide.map (fun e => (e.1, weldUMemIntoWide e.2 (wideKeyUMemDomain e.1)))

/-! ## STRUCTURAL pins (the committed-descriptor discipline — the byte-level pin is the Rust
`WIDE_UMEM_WELD_REGISTRY_FP` sha256 over the whole emitted TSV, matching how `WIDE_REGISTRY_STAGED`
is pinned; these `#guard`s pin the SHAPE the bytes realize). -/

-- Member-for-member cover of the wide registry, name-stable on the keys.
#guard weldedWideRegistry.length == 45
#guard weldedWideRegistry.map (·.1) == v3RegistryCapOpenWide.map (·.1)
-- Every welded member carries the staged weld marker + EXACTLY ONE welded umem op.
#guard weldedWideRegistry.all (fun e => e.2.name.endsWith wideUMemWeldSuffix)
#guard weldedWideRegistry.all (fun e => (umemOpsOf e.2).length == 1)
-- THE NO-NARROWING INVARIANT: the weld is additive — `traceWidth = host + 7` and `piCount` is
-- UNCHANGED (the 16 wide-commit PIs / the 8-felt anchors ride through at the same offsets).
#guard (v3RegistryCapOpenWide.zip weldedWideRegistry).all
  (fun p => p.2.2.traceWidth == p.1.2.traceWidth + 7 ∧ p.2.2.piCount == p.1.2.piCount)
-- The welded member declares the two universal-memory tables (umemory id 6, umem_boundary id 7).
#guard weldedWideRegistry.all (fun e =>
  e.2.tables.any (fun t => t.id = TableId.custom UMEM_TID) ∧
  e.2.tables.any (fun t => t.id = TableId.custom 2 ∧ t.name == "umem_boundary"))

end Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
