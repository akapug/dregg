/-
# Dregg2.Deos.BareCohortFloorRefuse — THE GENTIAN FLAG-DAY: closing the BARE-DESCRIPTOR DODGE.

## The dodge (the last hole before a sound deployed-default flip)

A `SettleEscrow` (and `Discharge`/`VaultDeposit`) executes on the deployed wire as a plain, zero-amount
`Transfer` routed to the BARE `transferVmDescriptor2R24` (or any bare cohort member): a descriptor with
NO capacity-satisfaction gate. So a forger settling a HALF-OPEN escrow on a cell that DECLARES the
escrow capacity produces an honest-looking transfer STARK that verifies under the bare descriptor's VK —
and a PURE light client (which only checks the batch proof against the deployed VKs) cannot reject it.
The welded satisfaction descriptor (`CarrierBoundFloorGadget.gentianCarrierDescriptor`) forces the
settle on cells routed THROUGH it — but nothing FORCES a declared-capacity cell onto it. That is the
bare-descriptor dodge.

## The fix — the FLOOR==0-REFUSE weld on EVERY bare cohort member

Weld onto every deployed bare cohort member the SAME caveat-manifest floor DECODE the satisfaction
carrier proves sound (`CarrierBoundFloorGadget.carrierGates` — the per-slot is-zero gadgets + the
running-OR fold into `GENTIAN_FLOOR_ESCROW_COL`, bound to the committed caveat manifest by the existing
`caveatCommit` chain at PI 45), PLUS a single new gate:

  * `floorZeroRefuseGate GENTIAN_FLOOR_ESCROW_COL` — `floorCol == 0` on every (non-last) row.

The decode forces `floorCol = escrowBitZ (manifestTags row)`; the refuse gate forces `floorCol = 0`.
A cell whose COMMITTED caveat manifest DECLARES the escrow tag decodes `floorCol = 1` (the decode is
pinned to the committed manifest by `caveatCommit_binds` — the deployed carrier collision-resistance
floor, NO new hypothesis), so the two constraints are jointly UNSATISFIABLE: the declared-capacity turn
CANNOT prove under the bare member and is FORCED onto the welded satisfaction descriptor. A cell that
declares NO escrow decodes `floorCol = 0` and the refuse gate is inert — the bare member still accepts
every non-declared turn (no false reject; the flip is complete, not just sound).

## Why this is the anti-launder gate (not a laundered flip)

The keystone `declared_escrow_unsat_under_bare` proves the forge is UNSAT on the bare path: a satisfying
witness of the refuse-welded bare member whose committed manifest requires the escrow tag is FALSE. The
forger's only freedom — the decode witness columns — is pinned to the committed manifest by the EXISTING
`caveatCommit` binding (`gentian_forged_floor_unsat_carrier`'s lever, reused here for REFUSE instead of
FORCE). There is no fake floor: a hollow (escrow-omitting) row manifest that matches the committed
caveat commit of a declaring cell is impossible.

## What is and is NOT a VK change

The floor BINDING needs NO new VK (the caveat manifest + its `caveatCommit` chain are already deployed —
the COVERAGE carrier). The only new constraint polynomials are the pure-arithmetic DECODE gates + the
one `floorCol == 0` refuse gate. `piCount` is UNCHANGED (the forcing is in-AIR, no new PI). This is the
whole-cohort flag-day: the SAME refuse block welds onto every bare member, so every bare cohort VK moves
(that is expected — the flag-day) but the shared `[0..46)` PI prefix and the geometry are untouched.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypothesis is `Poseidon2SpongeCR` (the deployed carrier
collision-resistance floor `caveatCommit_binds` already carries); never an axiom; no core edit.
Rust shadow: `circuit/src/effect_vm/bare_floor_refuse_weld.rs`.
-/
import Dregg2.Deos.CarrierBoundFloorGadget

namespace Dregg2.Deos.BareCohortFloorRefuse

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
  (RotCaveatManifest caveatCommit caveatCommit_binds zeroEntry)
open Dregg2.Deos.InAirAuthorityDigestSelector (GENTIAN_FLOOR_ESCROW_COL)
open Dregg2.Deos.InAirAuthorityDigestGadget
  (tagEscrowZ escrowBitZ isZeroDefGate isZeroForceGate isZero_from_gates)
open Dregg2.Deos.CarrierBoundFloorGadget
  (gadgetManifest manifestTags manifestTags_gadget carrierGates cavTagCol bitCol invCol orCol
   orSeedGate orFoldGate orStep)

set_option autoImplicit false

/-! ## §1 — the REFUSE gate. -/

/-- **`floorZeroRefuseGate`** — `floorCol == 0` on every (non-last) row. Welded onto every BARE cohort
member: combined with the caveat-manifest floor decode (which forces `floorCol = escrowBitZ tags`), a
cell that DECLARES the escrow capacity (`floorCol = 1`) has NO satisfying assignment — the bare member
REFUSES it, forcing it onto the welded satisfaction descriptor. A non-declaring cell decodes
`floorCol = 0` and this gate is inert (no false reject). Rust twin
`bare_floor_refuse_weld::floor_zero_refuse_gate`. -/
def floorZeroRefuseGate (floorCol : Nat) : VmConstraint2 :=
  .base (.gate (.var floorCol))

/-- The refuse-weld gate block: the PROVEN decode gadget (`carrierGates` — decode + first-row
selector-force + caveat-uniformity, whose decode into `GENTIAN_FLOOR_ESCROW_COL` is
`CarrierBoundFloorGadget.floor_decodes`) PLUS the single `floorZeroRefuseGate`. The selector-force gate
is inert on a bare member (it forces a free headroom selector column, never the refuse). -/
def refuseGates : List VmConstraint2 :=
  carrierGates ++ [floorZeroRefuseGate GENTIAN_FLOOR_ESCROW_COL]

/-! ## §2 — the WHOLE-COHORT refuse-weld transformer. -/

/-- **`gentianBareRefuseDescriptor d`** — an ARBITRARY deployed bare cohort member `d` welded with the
caveat-manifest floor decode + the `floorZeroRefuseGate`. STAGED source-of-truth: the deployed flag-day
maps this over the whole `v3RegistryBare` cohort. `piCount`/geometry unchanged (the forcing is in-AIR).
The name is suffixed so the emit distinguishes the welded member. -/
def gentianBareRefuseDescriptor (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with
    name        := d.name ++ "-gentian-bare-floor-refuse"
    constraints := d.constraints ++ refuseGates }

/-- The refuse-weld is additive: `piCount`, `traceWidth`, tables, sites, ranges are UNCHANGED. -/
theorem refuse_additive (d : EffectVmDescriptor2) :
    (gentianBareRefuseDescriptor d).piCount = d.piCount
    ∧ (gentianBareRefuseDescriptor d).traceWidth = d.traceWidth
    ∧ (gentianBareRefuseDescriptor d).tables = d.tables
    ∧ (gentianBareRefuseDescriptor d).hashSites = d.hashSites
    ∧ (gentianBareRefuseDescriptor d).ranges = d.ranges :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §3 — gate membership. -/

/-- A decode gadget gate (`∈ carrierGates`) is a member of the welded bare descriptor. -/
theorem carrierGate_mem_bare (d : EffectVmDescriptor2) (g : VmConstraint2) (hg : g ∈ carrierGates) :
    g ∈ (gentianBareRefuseDescriptor d).constraints := by
  unfold gentianBareRefuseDescriptor refuseGates
  simp only [List.mem_append]
  exact Or.inr (Or.inl hg)

/-- The refuse gate is a member of the welded bare descriptor. -/
theorem refuseGate_mem_bare (d : EffectVmDescriptor2) :
    floorZeroRefuseGate GENTIAN_FLOOR_ESCROW_COL ∈ (gentianBareRefuseDescriptor d).constraints := by
  unfold gentianBareRefuseDescriptor refuseGates
  exact List.mem_append_right d.constraints
    (List.mem_append_right carrierGates (List.mem_singleton.mpr rfl))

/-! ## §4 — the generic gate-forcing helper (mirror of `CarrierBoundFloorGadget.carrier_gate_holds`). -/

/-- A welded-bare gate's body vanishes on a satisfying NON-LAST row. -/
theorem bare_gate_holds (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianBareRefuseDescriptor d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ (gentianBareRefuseDescriptor d).constraints)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc = 0 := by
  have hrow := hsat.rowConstraints i hi g hg
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-! ## §5 — the per-slot bit decodes its tag column (mirror of `CarrierBoundFloorGadget.bit_decodes`). -/

/-- A per-slot is-zero gadget forces `bitCol k = escrowBitZ [tagColumn]` on a satisfying non-last row. -/
theorem bit_decodes_bare (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianBareRefuseDescriptor d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (k : Nat)
    (hdefmem : isZeroDefGate (cavTagCol k) (bitCol k) (invCol k) ∈ carrierGates)
    (hforcemem : isZeroForceGate (cavTagCol k) (bitCol k) ∈ carrierGates) :
    (envAt t i).loc (bitCol k) = escrowBitZ [(envAt t i).loc (cavTagCol k)] := by
  have hdef := bare_gate_holds hash d hsat i hi hnl
    (isZeroDefGate (cavTagCol k) (bitCol k) (invCol k)) (carrierGate_mem_bare d _ hdefmem) _ rfl
  have hforce := bare_gate_holds hash d hsat i hi hnl
    (isZeroForceGate (cavTagCol k) (bitCol k)) (carrierGate_mem_bare d _ hforcemem) _ rfl
  simp only [EmittedExpr.eval] at hdef hforce
  have hb := isZero_from_gates hdef hforce
  rw [hb]
  unfold escrowBitZ
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : (envAt t i).loc (cavTagCol k) + (-tagEscrowZ) = 0
  · rw [if_pos h, if_pos (by omega : tagEscrowZ = (envAt t i).loc (cavTagCol k))]
  · rw [if_neg h, if_neg (by omega : ¬ tagEscrowZ = (envAt t i).loc (cavTagCol k))]

/-! ## §6 — THE DECODE KEYSTONE (mirror of `CarrierBoundFloorGadget.floor_decodes`). -/

/-- **THE CARRIER DECODE (bare-welded).** On a satisfying NON-LAST row, the floor column is the
felt-domain escrow decode of the row's four caveat-manifest type tags. Proven arithmetic over the
caveat-bound type-tag columns — NO crypto floor. -/
theorem floor_decodes_bare (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianBareRefuseDescriptor d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false) :
    (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      = escrowBitZ (manifestTags (gadgetManifest (envAt t i).loc)) := by
  have hb0 := bit_decodes_bare hash d hsat i hi hnl 0 (by simp [carrierGates]) (by simp [carrierGates])
  have hb1 := bit_decodes_bare hash d hsat i hi hnl 1 (by simp [carrierGates]) (by simp [carrierGates])
  have hb2 := bit_decodes_bare hash d hsat i hi hnl 2 (by simp [carrierGates]) (by simp [carrierGates])
  have hb3 := bit_decodes_bare hash d hsat i hi hnl 3 (by simp [carrierGates]) (by simp [carrierGates])
  have hseed := bare_gate_holds hash d hsat i hi hnl
    (orSeedGate (orCol 0) (bitCol 0)) (carrierGate_mem_bare d _ (by simp [carrierGates])) _ rfl
  have hf1 := bare_gate_holds hash d hsat i hi hnl
    (orFoldGate (orCol 1) (orCol 0) (bitCol 1))
    (carrierGate_mem_bare d _ (by simp [carrierGates])) _ rfl
  have hf2 := bare_gate_holds hash d hsat i hi hnl
    (orFoldGate (orCol 2) (orCol 1) (bitCol 2))
    (carrierGate_mem_bare d _ (by simp [carrierGates])) _ rfl
  have hf3 := bare_gate_holds hash d hsat i hi hnl
    (orFoldGate GENTIAN_FLOOR_ESCROW_COL (orCol 2) (bitCol 3))
    (carrierGate_mem_bare d _ (by simp [carrierGates])) _ rfl
  simp only [EmittedExpr.eval] at hseed hf1 hf2 hf3
  have ho0 : (envAt t i).loc (orCol 0) = escrowBitZ [(envAt t i).loc (cavTagCol 0)] := by
    rw [show (envAt t i).loc (orCol 0) = (envAt t i).loc (bitCol 0) by linarith [hseed]]; exact hb0
  have ho1 : (envAt t i).loc (orCol 1)
      = escrowBitZ ([(envAt t i).loc (cavTagCol 0)] ++ [(envAt t i).loc (cavTagCol 1)]) :=
    orStep ho0 hb1 (by linarith [hf1])
  have ho2 : (envAt t i).loc (orCol 2)
      = escrowBitZ ([(envAt t i).loc (cavTagCol 0), (envAt t i).loc (cavTagCol 1)]
          ++ [(envAt t i).loc (cavTagCol 2)]) :=
    orStep ho1 hb2 (by linarith [hf2])
  have ho3 : (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL
      = escrowBitZ ([(envAt t i).loc (cavTagCol 0), (envAt t i).loc (cavTagCol 1),
          (envAt t i).loc (cavTagCol 2)] ++ [(envAt t i).loc (cavTagCol 3)]) :=
    orStep ho2 hb3 (by linarith [hf3])
  rw [ho3, manifestTags_gadget]
  simp only [List.cons_append, List.nil_append]

/-! ## §7 — THE REFUSE KEYSTONE: a declared-escrow cell is UNSAT under any bare member. -/

/-- **THE BARE-DESCRIPTOR DODGE, CLOSED (the anti-launder forge, proof form).** For ANY deployed bare
cohort member `d`, a satisfying witness of the refuse-welded `gentianBareRefuseDescriptor d` on a cell
whose COMMITTED caveat manifest requires the escrow tag is FALSE — under ONLY the deployed carrier
collision-resistance floor (`Poseidon2SpongeCR`), for a PURE light client. The decode pins the floor to
the committed manifest (via `caveatCommit_binds`); the committed declaration lights `floorCol = 1`; the
`floorZeroRefuseGate` demands `floorCol = 0`. There is no satisfying assignment: the forger settling a
half-open escrow via the bare descriptor is UNSAT on the DEFAULT path, and the honest declared-capacity
turn is FORCED onto the welded satisfaction descriptor. -/
theorem declared_escrow_unsat_under_bare (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianBareRefuseDescriptor d) minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash (gadgetManifest (envAt t 0).loc) = caveatCommit hash committedManifest)
    (hreq : tagEscrowZ ∈ manifestTags committedManifest) :
    False := by
  -- DISCHARGE: the existing caveat-commit binding forces the row manifest = the committed manifest.
  have hmeq : gadgetManifest (envAt t 0).loc = committedManifest := caveatCommit_binds hash hCR hbind
  have hrowreq : tagEscrowZ ∈ manifestTags (gadgetManifest (envAt t 0).loc) := by
    rw [hmeq]; exact hreq
  -- the decode lights the floor column from the bound type tags on the settle (row-0) row.
  have hdec := floor_decodes_bare hash d hsat 0 hi hnl
  have hfloor : (envAt t 0).loc GENTIAN_FLOOR_ESCROW_COL = 1 := by
    rw [hdec]; unfold escrowBitZ; rw [if_pos hrowreq]
  -- the REFUSE gate demands the floor column be 0 — contradiction.
  have hrefuse := bare_gate_holds hash d hsat 0 hi hnl
    (floorZeroRefuseGate GENTIAN_FLOOR_ESCROW_COL) (refuseGate_mem_bare d)
    (.var GENTIAN_FLOOR_ESCROW_COL) rfl
  simp only [EmittedExpr.eval] at hrefuse
  rw [hfloor] at hrefuse
  exact absurd hrefuse (by decide)

/-- **COMPLETENESS COROLLARY (no false reject).** The refuse gate is a `floorCol == 0` gate; a cell that
decodes `floorCol = 0` (declares NO escrow) satisfies it. The refuse thus bites EXACTLY the declared
cells — the flip is complete, not merely sound. (Stated as the decode identity + the refuse gate; a
non-declaring row has `escrowBitZ tags = 0`, so `floor_decodes_bare` gives `floorCol = 0`, and the
refuse gate `floorCol == 0` holds.) -/
theorem non_declared_floor_zero (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianBareRefuseDescriptor d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hno : tagEscrowZ ∉ manifestTags (gadgetManifest (envAt t i).loc)) :
    (envAt t i).loc GENTIAN_FLOOR_ESCROW_COL = 0 := by
  rw [floor_decodes_bare hash d hsat i hi hnl]; unfold escrowBitZ; rw [if_neg hno]

/-! ## §8 — NON-VACUITY TEETH (`#guard`): both polarities BITE. -/

section Witnesses

/-- A committed manifest declaring escrow in slot 0. -/
private def escrowManifest : RotCaveatManifest :=
  ⟨1, ⟨tagEscrowZ, 0, 0, 0, 0, 0, 0⟩, zeroEntry, zeroEntry, zeroEntry⟩
/-- A forger's manifest with NO escrow tag (the omission dodge — refused? no: it decodes floor 0). -/
private def hollowManifest : RotCaveatManifest :=
  ⟨1, ⟨6, 0, 0, 0, 0, 0, 0⟩, zeroEntry, zeroEntry, zeroEntry⟩

private def gateVal (g : VmConstraint2) (loc : Nat → ℤ) : ℤ :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999

-- The refuse gate BITES on floor = 1 (a declared cell) and VANISHES on floor = 0 (non-declared).
#guard gateVal (floorZeroRefuseGate GENTIAN_FLOOR_ESCROW_COL)
  (fun c => if c == GENTIAN_FLOOR_ESCROW_COL then 1 else 0) != 0
#guard gateVal (floorZeroRefuseGate GENTIAN_FLOOR_ESCROW_COL)
  (fun c => if c == GENTIAN_FLOOR_ESCROW_COL then 0 else 0) == 0

-- The decode over the committed manifest tags, both polarities (escrow ⟹ 1, hollow ⟹ 0).
#guard escrowBitZ (manifestTags escrowManifest) == 1
#guard escrowBitZ (manifestTags hollowManifest) == 0

-- The refuse block adds EXACTLY the decode gadget (17 gates) + the one refuse gate = 18.
#guard refuseGates.length == 18
#guard carrierGates.length == 17

-- Additivity witness on a toy base descriptor: piCount / width UNCHANGED (the forcing is in-AIR).
private def toyBase : EffectVmDescriptor2 :=
  { name := "toy", traceWidth := 100, piCount := 46, tables := [], constraints := [], hashSites := [],
    ranges := [] }
#guard (gentianBareRefuseDescriptor toyBase).piCount == 46
#guard (gentianBareRefuseDescriptor toyBase).traceWidth == 100
#guard (gentianBareRefuseDescriptor toyBase).constraints.length == 18

end Witnesses

/-! ## §9 — Axiom hygiene. -/

#assert_all_clean [
  refuse_additive,
  carrierGate_mem_bare,
  refuseGate_mem_bare,
  bare_gate_holds,
  bit_decodes_bare,
  floor_decodes_bare,
  declared_escrow_unsat_under_bare,
  non_declared_floor_zero
]

end Dregg2.Deos.BareCohortFloorRefuse
