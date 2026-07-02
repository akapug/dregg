/-
# Dregg2.Circuit.Emit.CarrierComposed — STEP-3 CHIP-GATE COMPOSES (sovereign · membership).

The RESOLVED-FORK chip-compress lane: the two v12-walled carriers whose teeth are a Poseidon2
COMPRESS of the committed pubkey octet (`B_PUBKEY8` = limbs 104..=111, filled UNCONDITIONALLY by the
STEP-2 producer as `canonical_32_to_felts_8(pubkey)`). This module WIRES the pre-proven
`CarrierOctetGates` gates onto the deployed descriptors — it is the natural composition site (imports
BOTH `EffectVmEmitRotationV3` (via `CarrierOctetGates`) and the gates), which did not exist before
STEP-3.

BIG-BANG REGEN (this pass): the composed descriptors are now REGISTRY-REAL. §4 below defines the
DEPLOYED sovereign member (`makeSovereignV3Deployed` narrow / `makeSovereignV3DeployedWide` wide —
teeth PI pins at the annotated post-rc slots 58..61 + the KEY_COMMIT chip gate) and §5 the DEPLOYED
membership-teeth transfer member (`transferV3Membership` / `transferV3MembershipWide` — the
`(sender_leaf, authorized_root)` teeth columns pinned at the annotated post-rc slots 50..51). The
apex re-key rides `CircuitSoundnessAssembled.v3RegistryHeap` tail positions (the refusal
`effFieldsWriteV3` precedent — the import topology forbids a bare-registry swap here, since
`CarrierOctetGates` imports `CapOpenEmit`); the wide TSV emits these under the LIVE keys via
`EmitWideRegistryProbe`'s in-place replacement (the same precedent).

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
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Circuit.Emit.CarrierComposed

open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 Satisfied2 ChipTableSoundN VmTrace envAt VmConstraint2
   memOpsOf mapOpsOf memLog mapLog)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint holdsVm_piFirst_true)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (makeSovereignV3 withDfaRcPins satisfied2_of_withDfaRcPins)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (wideAppend isLegacyCommitPin1)
open Dregg2.Circuit.Emit.CarrierOctetGates
  (withSovereignKeyCommit withSovereignKeyCommit_forces withSovereignKeyCommit_rejects_forged
   satisfied2_of_withSovereignKeyCommit
   keyCommitSpec octetVals permOutOf B_PUBKEY8 BEFORE_BLOCK_BASE)
open Dregg2.Circuit.Emit.CapOpenEmit (transferV3)

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

/-! ## §4 — THE DEPLOYED SOVEREIGN MEMBER (big-bang regen): teeth PI pins + the KEY_COMMIT gate.

The annotated fold-arm convention (`ivc_turn_chain.rs::SOVEREIGN_KEY_COMMIT_PI_LO = 58`,
`sovereign_binding_deployed_tooth.rs`): the 4 KEY_COMMIT teeth (cols 23..=26) publish at the
POST-rc tail — PIs 58..61 on the narrow member (54 record-pin + 4 rc, THEN the teeth), strictly
AHEAD of the 16 wide anchors on the wide member (62..77). So the compose order is
`gate ∘ teethPins ∘ rc` (narrow) and `gate ∘ wideAppend ∘ teethPins ∘ rc` (wide) — the teeth pins
ride the HOST so the wide anchors land past them, and the chip gate appends OUTERMOST so its
digest appendix sits past everything (`dgBase = base.traceWidth`), leaving every deployed column
position untouched (the producer twin appends the 32 appendix columns at the trace end). -/

/-- **`withSovereignTeethPins g`** — APPEND 4 `.piBinding .first` pins publishing the executor
KEY_COMMIT teeth columns (`SOVEREIGN_KEY_COMMIT_COL + q`, cols 23..=26) as 4 TAIL PIs
(`g.piCount + q`), bumping `piCount` by 4. Mirrors `withAfterOctetPins` exactly (additive; no
site / range / mem-op / map-op touched), at the `.first` row (the teeth are row-0 turn claims,
not AFTER-block state). -/
def withSovereignTeethPins (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    piCount := g.piCount + 4
    constraints := g.constraints ++ (List.range 4).map (fun q =>
      VmConstraint2.base (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q) (g.piCount + q))) }

/-- The 4 teeth pins are the ONLY constraints past the inner descriptor's (single `++`). -/
theorem withSovereignTeethPins_constraints (g : EffectVmDescriptor2) :
    (withSovereignTeethPins g).constraints
      = g.constraints ++ (List.range 4).map (fun q =>
          VmConstraint2.base (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q)
            (g.piCount + q))) := rfl

theorem memOpsOf_withSovereignTeethPins (g : EffectVmDescriptor2) :
    memOpsOf (withSovereignTeethPins g) = memOpsOf g := by
  simp [memOpsOf, withSovereignTeethPins, List.filterMap_append, List.filterMap_map]

theorem mapOpsOf_withSovereignTeethPins (g : EffectVmDescriptor2) :
    mapOpsOf (withSovereignTeethPins g) = mapOpsOf g := by
  simp [mapOpsOf, withSovereignTeethPins, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL — `Satisfied2 (withSovereignTeethPins g) ⟹ Satisfied2 g`** (the
`satisfied2_of_withAfterOctetPins` shape verbatim). -/
theorem satisfied2_of_withSovereignTeethPins (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withSovereignTeethPins g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withSovereignTeethPins g) t = memLog g t := by
    simp [memLog, memOpsOf_withSovereignTeethPins]
  have hmap : mapLog (withSovereignTeethPins g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withSovereignTeethPins]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withSovereignTeethPins_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withSovereignTeethPins_publishes`** — on the FIRST row of a `Satisfied2` witness, each of
the 4 published TAIL PIs (`g.piCount + q`) EQUALS its teeth column (cols 23..=26). The `.first`-row
twin of `withDfaRcPins_publishes`. -/
theorem withSovereignTeethPins_publishes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withSovereignTeethPins g) minit mfin maddrs t)
    (h0 : 0 < t.rows.length) :
    ∀ q : Fin 4, (envAt t 0).loc (SOVEREIGN_KEY_COMMIT_COL + q.val)
      = (envAt t 0).pub (g.piCount + q.val) := by
  intro q
  have hfirstt : ((0 : Nat) == 0) = true := rfl
  have hin : VmConstraint2.base
      (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q.val) (g.piCount + q.val))
      ∈ (withSovereignTeethPins g).constraints := by
    rw [withSovereignTeethPins_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨q.val, List.mem_range.mpr q.isLt, rfl⟩)
  have h := hsat.rowConstraints 0 h0 _ hin
  simp only [VmConstraint2.holdsAt, hfirstt, holdsVm_piFirst_true] at h
  exact h

#assert_axioms satisfied2_of_withSovereignTeethPins
#assert_axioms withSovereignTeethPins_publishes

/-- The deployed sovereign HOST: record-pin base + the cohort rc wrap + the teeth PI pins
(piCount `54 → 58 → 62`; teeth at PI 58..61, the annotated `SOVEREIGN_KEY_COMMIT_PI_LO`). -/
def makeSovereignV3Pinned : EffectVmDescriptor2 :=
  withSovereignTeethPins (withDfaRcPins makeSovereignV3)

/-- `makeSovereignV3Pinned`'s constraints unfolded to the pin-append form — the `rw`-able twin of
`withSovereignTeethPins_constraints` at the concrete host (`rw` does not see through the def). -/
theorem makeSovereignV3Pinned_constraints :
    makeSovereignV3Pinned.constraints
      = (withDfaRcPins makeSovereignV3).constraints ++ (List.range 4).map (fun q =>
          VmConstraint2.base (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q)
            ((withDfaRcPins makeSovereignV3).piCount + q))) := rfl

/-- **`makeSovereignV3Deployed`** — the NARROW deployed sovereign member (the apex `Rfix 38`
re-key target): the pinned host COMPOSED with the in-AIR KEY_COMMIT chip gate (the third edge —
teeth == `canonical_32_to_felts_4` of the committed `B_PUBKEY8` octet). -/
def makeSovereignV3Deployed : EffectVmDescriptor2 :=
  withSovereignKeyCommit makeSovereignV3Pinned SOVEREIGN_KEY_COMMIT_COL

/-- The in-block BEFORE base of the sovereign wide member (`makeSovereignRuntimeVmDescriptor`'s
face width — the `v3RegistryWideBB` position-21 entry). -/
def MS_WIDE_BB : Nat :=
  Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth

/-- **`makeSovereignV3DeployedWide`** — the WIDE deployed sovereign member (the
`WIDE_REGISTRY_STAGED_TSV` row under the live key, via `EmitWideRegistryProbe`'s in-place
replacement): teeth PIs 58..61 strictly AHEAD of the 16 wide anchors (62..77), the KEY_COMMIT
gate OUTERMOST (its 32-column digest appendix at the wide trace end, `dgBase = 1771`). -/
def makeSovereignV3DeployedWide : EffectVmDescriptor2 :=
  withSovereignKeyCommit (wideAppend makeSovereignV3Pinned MS_WIDE_BB (MS_WIDE_BB + 151))
    SOVEREIGN_KEY_COMMIT_COL

-- Geometry: narrow 62 PIs / width +32; wide 78 PIs / 1163+608+32 = 1803 wide, teeth ahead of anchors.
#guard makeSovereignV3.piCount == 54
#guard makeSovereignV3Pinned.piCount == 62
#guard makeSovereignV3Deployed.piCount == 62
#guard makeSovereignV3Deployed.traceWidth == makeSovereignV3.traceWidth + 32
#guard makeSovereignV3DeployedWide.piCount == 78
#guard makeSovereignV3DeployedWide.traceWidth == makeSovereignV3.traceWidth + 608 + 32
#guard makeSovereignV3.traceWidth == 1163
#guard MS_WIDE_BB == 188

/-- **THE FULL PEEL — `Satisfied2 makeSovereignV3Deployed ⟹ Satisfied2 makeSovereignV3`** (gate →
teeth pins → rc), the chain the apex `Rfix 38` rung re-key consumes. -/
theorem satisfied2_of_makeSovereignV3Deployed (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash makeSovereignV3Deployed minit mfin maddrs t) :
    Satisfied2 hash makeSovereignV3 minit mfin maddrs t :=
  satisfied2_of_withDfaRcPins hash makeSovereignV3
    (satisfied2_of_withSovereignTeethPins hash (withDfaRcPins makeSovereignV3)
      (satisfied2_of_withSovereignKeyCommit hash makeSovereignV3Pinned
        SOVEREIGN_KEY_COMMIT_COL _ _ _ _ h))

/-- **THE DEPLOYED SOVEREIGN EXPOSURE KEYSTONE (narrow).** On any `Satisfied2` witness of the
deployed narrow member with ≥ 2 rows, each published teeth PI (58..61) EQUALS the in-AIR
`canonical_32_to_felts_4` of the committed BEFORE `B_PUBKEY8` octet: the pin binds the PI to the
teeth column (row 0), the chip gate binds the teeth column to the compress (row 0 is not last).
A ledgerless client reads the owner-key commit OFF THE PI VECTOR; a forged claim is UNSAT. -/
theorem makeSovereignV3Deployed_publishes_key_commit (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash makeSovereignV3Deployed minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    ∀ q : Fin 4, (envAt t 0).pub ((withDfaRcPins makeSovereignV3).piCount + q.val)
      = keyCommitSpec A (octetVals (envAt t 0) BEFORE_BLOCK_BASE B_PUBKEY8) q := by
  intro q
  have h0 : 0 < t.rows.length := Nat.lt_trans Nat.zero_lt_one hlen
  have hnotlast : 0 + 1 ≠ t.rows.length := by omega
  -- the gate: teeth column == compress of the committed octet (row 0, not last).
  have hgate := withSovereignKeyCommit_forces A hash makeSovereignV3Pinned
    SOVEREIGN_KEY_COMMIT_COL minit mfin maddrs t hChip hsat 0 h0 hnotlast q
  -- the pin: teeth column == published PI (row 0 = the first row). The pin lives in the pinned
  -- host, whose constraints are members of the gate-composed deployed descriptor.
  have hin : VmConstraint2.base
      (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q.val)
        ((withDfaRcPins makeSovereignV3).piCount + q.val))
      ∈ makeSovereignV3Deployed.constraints := by
    refine List.mem_append_left _ ?_
    rw [makeSovereignV3Pinned_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨q.val, List.mem_range.mpr q.isLt, rfl⟩)
  have hfirstt : ((0 : Nat) == 0) = true := rfl
  have hpin := hsat.rowConstraints 0 h0 _ hin
  simp only [VmConstraint2.holdsAt, hfirstt, holdsVm_piFirst_true] at hpin
  rw [← hpin]
  exact hgate

/-- **TOOTH (narrow deployed)** — a forged published owner-key commit (a teeth PI that is not the
compress of the committed pubkey octet) is UNSAT for a ledgerless client. -/
theorem makeSovereignV3Deployed_rejects_forged_pi (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hlen : 1 < t.rows.length) (q : Fin 4)
    (hforged : (envAt t 0).pub ((withDfaRcPins makeSovereignV3).piCount + q.val)
      ≠ keyCommitSpec A (octetVals (envAt t 0) BEFORE_BLOCK_BASE B_PUBKEY8) q) :
    ¬ Satisfied2 hash makeSovereignV3Deployed minit mfin maddrs t :=
  fun hsat => hforged
    (makeSovereignV3Deployed_publishes_key_commit A hash minit mfin maddrs t hChip hsat hlen q)

/-- Host-constraint membership survives `wideAppend` when the constraint is not a retired legacy
1-felt commit pin. -/
theorem wideAppend_mem_of_host (h : EffectVmDescriptor2) (bb ab : Nat) (c : VmConstraint2)
    (hc : c ∈ h.constraints) (hnp : isLegacyCommitPin1 bb ab c = false) :
    c ∈ (wideAppend h bb ab).constraints := by
  rw [Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend_constraints]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ ?_)))
  exact List.mem_filter.mpr ⟨hc, by simp [hnp]⟩

/-- **THE DEPLOYED SOVEREIGN EXPOSURE KEYSTONE (wide — the `WIDE_REGISTRY_STAGED_TSV` member the
fold tooth proves).** Same statement as the narrow keystone, on the wide member: teeth PIs 58..61
== the compress of the committed octet. -/
theorem makeSovereignV3DeployedWide_publishes_key_commit (A : List ℤ → Digest8)
    (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash makeSovereignV3DeployedWide minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    ∀ q : Fin 4, (envAt t 0).pub ((withDfaRcPins makeSovereignV3).piCount + q.val)
      = keyCommitSpec A (octetVals (envAt t 0) BEFORE_BLOCK_BASE B_PUBKEY8) q := by
  intro q
  have h0 : 0 < t.rows.length := Nat.lt_trans Nat.zero_lt_one hlen
  have hnotlast : 0 + 1 ≠ t.rows.length := by omega
  have hgate := withSovereignKeyCommit_forces A hash
    (wideAppend makeSovereignV3Pinned MS_WIDE_BB (MS_WIDE_BB + 151))
    SOVEREIGN_KEY_COMMIT_COL minit mfin maddrs t hChip hsat 0 h0 hnotlast q
  -- the pin: member of the pinned host, surviving the wide legacy-pin filter (its column is a
  -- teeth column 23..=26, never `bb + B_STATE_COMMIT`).
  have hinHost : VmConstraint2.base
      (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q.val)
        ((withDfaRcPins makeSovereignV3).piCount + q.val))
      ∈ makeSovereignV3Pinned.constraints := by
    rw [makeSovereignV3Pinned_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨q.val, List.mem_range.mpr q.isLt, rfl⟩)
  have hnp : isLegacyCommitPin1 MS_WIDE_BB (MS_WIDE_BB + 151)
      (VmConstraint2.base (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q.val)
        ((withDfaRcPins makeSovereignV3).piCount + q.val))) = false := by
    have hq : q.val < 4 := q.isLt
    have hbb : MS_WIDE_BB + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_STATE_COMMIT = 301 := by
      decide
    simp only [isLegacyCommitPin1, beq_eq_false_iff_ne, ne_eq, hbb, SOVEREIGN_KEY_COMMIT_COL]
    omega
  have hin : VmConstraint2.base
      (.piBinding .first (SOVEREIGN_KEY_COMMIT_COL + q.val)
        ((withDfaRcPins makeSovereignV3).piCount + q.val))
      ∈ makeSovereignV3DeployedWide.constraints :=
    List.mem_append_left _
      (wideAppend_mem_of_host makeSovereignV3Pinned MS_WIDE_BB (MS_WIDE_BB + 151) _ hinHost hnp)
  have hfirstt : ((0 : Nat) == 0) = true := rfl
  have hpin := hsat.rowConstraints 0 h0 _ hin
  simp only [VmConstraint2.holdsAt, hfirstt, holdsVm_piFirst_true] at hpin
  rw [← hpin]
  exact hgate

#assert_axioms satisfied2_of_makeSovereignV3Deployed
#assert_axioms makeSovereignV3Deployed_publishes_key_commit
#assert_axioms makeSovereignV3Deployed_rejects_forged_pi
#assert_axioms makeSovereignV3DeployedWide_publishes_key_commit

/-! ## §5 — THE DEPLOYED MEMBERSHIP-TEETH TRANSFER MEMBER (big-bang regen): the
`(sender_leaf, authorized_root)` PI exposure.

The annotated fold-arm convention (`ivc_turn_chain.rs::MEMBERSHIP_CLAIM_PI_LO = 50`,
`membership_binding_deployed_tooth.rs`): two NEW teeth columns appended past the transfer host
width, row-0-pinned at the POST-rc tail (PIs 50..51 on the narrow member; 46 bare + 4 rc, THEN
the teeth; the 16 wide anchors land past them at 52..67).

⚑ HONEST SCOPE (the fail-open law, named): this is the PI EXPOSURE leg ONLY — the leg
`MembershipAuthRootEdge` names as "the deployed-leg PI EXPOSURE at fixed slots" among its
remaining seams. What binds the teeth is the FOLD edge (the chain prover's Membership arm binds
the published tuple lane-for-lane to a genuine re-proven `dsl::membership` STARK — the deployed
tooth's two poles). The THIRD edge stays open and NAMED:
  * the ROOT leg (`effFieldsReadOpenV3`, proven parametric in `MembershipAuthRootEdge`) is NOT
    composed here because the deployed transfer producer does not yet build the committed
    `fields_root` block as an openable tree, and the `SenderAuthorized` caveat is OPTIONAL on a
    transfer (an unconditional read weld would break every plain transfer — completeness);
  * the SENDER leg is the `MembershipAuthRootEdge` STOP (no committed sender-pubkey octet).
`MembershipBackingAttack` §A/§A′ therefore STAND as deployed-AIR facts; the fold narrows them
(a claimed tuple must be backed by SOME verifying membership STARK). -/

/-- **`withMembershipTeethPins g`** — APPEND the two membership teeth COLUMNS (at `g.traceWidth`,
`+1`) and their 2 `.piBinding .first` TAIL PI pins (`g.piCount + j`), bumping `traceWidth` by 2
and `piCount` by 2. The committed twin of the tooth's `insert_tail_claim_pins` staging. -/
def withMembershipTeethPins (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    traceWidth := g.traceWidth + 2
    piCount := g.piCount + 2
    constraints := g.constraints ++ (List.range 2).map (fun j =>
      VmConstraint2.base (.piBinding .first (g.traceWidth + j) (g.piCount + j))) }

theorem withMembershipTeethPins_constraints (g : EffectVmDescriptor2) :
    (withMembershipTeethPins g).constraints
      = g.constraints ++ (List.range 2).map (fun j =>
          VmConstraint2.base (.piBinding .first (g.traceWidth + j) (g.piCount + j))) := rfl

theorem memOpsOf_withMembershipTeethPins (g : EffectVmDescriptor2) :
    memOpsOf (withMembershipTeethPins g) = memOpsOf g := by
  simp [memOpsOf, withMembershipTeethPins, List.filterMap_append, List.filterMap_map]

theorem mapOpsOf_withMembershipTeethPins (g : EffectVmDescriptor2) :
    mapOpsOf (withMembershipTeethPins g) = mapOpsOf g := by
  simp [mapOpsOf, withMembershipTeethPins, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL — `Satisfied2 (withMembershipTeethPins g) ⟹ Satisfied2 g`.** -/
theorem satisfied2_of_withMembershipTeethPins (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withMembershipTeethPins g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withMembershipTeethPins g) t = memLog g t := by
    simp [memLog, memOpsOf_withMembershipTeethPins]
  have hmap : mapLog (withMembershipTeethPins g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withMembershipTeethPins]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withMembershipTeethPins_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- **`withMembershipTeethPins_publishes`** — on the FIRST row, each published teeth PI equals its
teeth column: the exposure the fold arm's admission gate requires (a genuine `PiBinding` at every
claim slot). -/
theorem withMembershipTeethPins_publishes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withMembershipTeethPins g) minit mfin maddrs t)
    (h0 : 0 < t.rows.length) :
    ∀ j : Fin 2, (envAt t 0).loc (g.traceWidth + j.val)
      = (envAt t 0).pub (g.piCount + j.val) := by
  intro j
  have hfirstt : ((0 : Nat) == 0) = true := rfl
  have hin : VmConstraint2.base
      (.piBinding .first (g.traceWidth + j.val) (g.piCount + j.val))
      ∈ (withMembershipTeethPins g).constraints := by
    rw [withMembershipTeethPins_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩)
  have h := hsat.rowConstraints 0 h0 _ hin
  simp only [VmConstraint2.holdsAt, hfirstt, holdsVm_piFirst_true] at h
  exact h

#assert_axioms satisfied2_of_withMembershipTeethPins
#assert_axioms withMembershipTeethPins_publishes

/-- **`transferV3Membership`** — the NARROW deployed membership-teeth transfer member (the apex
`Rfix 0` re-key target): the cohort transfer + rc + the two teeth pins (piCount `46 → 50 → 52`;
teeth at PI 50..51, the annotated `MEMBERSHIP_CLAIM_PI_LO`; teeth columns at 608..609). -/
def transferV3Membership : EffectVmDescriptor2 :=
  withMembershipTeethPins (withDfaRcPins transferV3)

/-- The transfer wide-member BEFORE base (`transferVmDescriptor`'s face width — the
`v3RegistryWideBB` position-0 entry). -/
def TR_WIDE_BB : Nat :=
  Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth

/-- **`transferV3MembershipWide`** — the WIDE deployed membership-teeth transfer member (the
`WIDE_REGISTRY_STAGED_TSV` row under the live key): teeth PIs 50..51 strictly AHEAD of the 16
wide anchors (52..67); the wide carriers base past the teeth columns (1165). -/
def transferV3MembershipWide : EffectVmDescriptor2 :=
  wideAppend transferV3Membership TR_WIDE_BB (TR_WIDE_BB + 151)

-- Geometry: narrow 52 PIs / width 1165; wide 68 PIs / 1773 wide.
#guard transferV3.piCount == 46
#guard transferV3Membership.piCount == 52
#guard transferV3Membership.traceWidth == transferV3.traceWidth + 2
#guard transferV3.traceWidth == 1163
#guard transferV3MembershipWide.piCount == 68
#guard transferV3MembershipWide.traceWidth == 1163 + 2 + 608

/-- **THE FULL PEEL — `Satisfied2 transferV3Membership ⟹ Satisfied2 transferV3`** (teeth pins →
rc), the chain the apex `Rfix 0` rung re-key consumes. -/
theorem satisfied2_of_transferV3Membership (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash transferV3Membership minit mfin maddrs t) :
    Satisfied2 hash transferV3 minit mfin maddrs t :=
  satisfied2_of_withDfaRcPins hash transferV3
    (satisfied2_of_withMembershipTeethPins hash (withDfaRcPins transferV3) h)

#assert_axioms satisfied2_of_transferV3Membership

end Dregg2.Circuit.Emit.CarrierComposed
