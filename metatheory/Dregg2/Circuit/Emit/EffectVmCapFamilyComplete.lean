/-
# Dregg2.Circuit.Emit.EffectVmCapFamilyComplete — the CAP-FAMILY sorted-tree WRITE-gate completeness
  (`←`) + the per-tag `air_accepts ⟺ spec` at the 8-felt cap-tree write resolution.

## What this closes and what it does NOT (read the resolution honestly)

`RotatedKernelRefinementCapFamily.lean` supplies the SOUNDNESS half for the cap family: from a satisfying
DEPLOYED `Satisfied2 hash (effCapOpenWriteV3 <baseV3> …)` (via `effCapOpenWriteV3_forces_write8`) each
cap-family tag gets `<XSpec> ∧ writesTo8 S8 oldRoot k v newRoot` — the `→` (SAT ⟹ SEM) over the FULL
committed 8-felt BEFORE/AFTER cap-root blocks.

This file supplies the COMPLEMENTARY `←` content for the SORTED-TREE WRITE gate, at the SAME 8-felt
`recomposeUp8` / `capLeafDigest8` resolution the deployment commits, reusing the LANDED
`DeployedCapTree.Cap8Scheme` machinery (`capOpen8_binds_leaf_or_collides`, composing the spine walk
and the leaf peel — the arity-16 chip binding, EXTRACTED AS DATA) rather than re-authoring a parallel shape:

  1. **the REALIZABILITY `←` (`capWrite8_realizes` / the per-tag `_write_realizes`)** — "producing the
     membership-open / after-root columns that `writesTo8` forces, from a genuine `<XSpec>`-style spec":
     given the sorted-tree decode (a before-leaf keyed `k`, an after-leaf keyed `k` with the narrowed
     rights felt `v`, and a shared membership path `p`), the DEPLOYED write relation `writesTo8` is
     GENUINELY SATISFIED. The honest kernel move INHABITS the deployed relation — the `←` direction the
     soundness leg does not give.

  2. **the ANTI-FORGE (`capWrite8_afterRoot_binds_leaf_or_collides` + the `⟺` restored at a
     non-colliding candidate, `capWrite8_afterRoot_iff_of_noColl` / the per-tag `_iff_spec_of_noColl`)** — the
     content-bearing biconditional: along the committed membership path `p`, the published AFTER cap-root
     opens to an after-leaf `nl'` IFF `nl'` is EXACTLY the genuine spec-narrowed after-leaf. `→` is the
     8-felt anti-forge (`capOpen8_binds_leaf_or_collides`); `←` is `congrArg`, unconditional. Both
     directions are REAL and NON-VACUOUS (a forged after-leaf yields a DIFFERENT root — the mutation
     canary bites), and the biconditional carries the spec's `slot_hash = k` / `mask_lo = v` welds, so it
     reads `the after-root accepts nl' ⟺ nl' commits the spec's narrowed rights at the spec's key`.

Welded per tag with the LANDED soundness `→` (`X_descriptorRefines_capOpenSat`, consumed unchanged, NOT
re-authored), these give — modulo the ONE named carrier bundle — the two-directional `air_accepts ⟺ spec`
for the cap-tree write GATE at full ~124-bit width.

## The named carrier bundle (honest, NOT laundered) and the SCOPED residuals

The `⟺` is modulo ONE named carrier: **the sorted-tree decode** (the before/after leaves + the shared membership path `p` — the honest prover's
in-circuit cap-open readout). This is the `SpineCommits`/`writesTo8` "sorted-tree decode" the cap family
already carries; it is a HYPOTHESIS the honest prover discharges from its trace, never an axiom.

⚑ THE CHIP CR IS NO LONGER IN THE BUNDLE. It used to be `Cap8Scheme.chip8CR : Compress8CR chipAbsorb8`,
a STRUCTURE FIELD that is FALSE at deployed BabyBear parameters — so `Cap8Scheme` had no deployed value
and every `∀ S8 : Cap8Scheme, …` theorem in this file was VACUOUS rather than modulo-anything. The
field is DELETED. The `→` legs are now unconditional disjunctions naming the pair a total extractor
returns (`CapOpenColl`), and the `⟺` is restored under `¬ CapOpenColl` — an instance-local side
condition the deployed chip SATISFIES at every non-colliding pair, not a global injectivity it refutes.
The probabilistic price of the collision disjunct lives in `InjectiveFloorRegrounded` §1.

What this file DOES NOT claim, stated plainly (the SCOPED residuals):
  * It is the WRITE-GATE (`writesTo8` / cap-root binding) `⟺`, NOT a single `Satisfied2 (effCapOpenWriteV3
    …) ⟺ <full effect spec>` biconditional. The SAT-reconstruction `←` (build a satisfying
    `effCapOpenWriteV3` trace — the 16-level chip-lookup appendix — from the spec) is the StarkComplete
    DUAL carried as a realizable trace floor exactly as `CircuitCompletenessAuthorityConstruct`'s
    `CapOpenTraceFloor` carries the AUTHORITY-leg opening; it is NOT reconstructed here and is NOT
    near-instantiation.
  * The DEPLOYED forcing weakens the committed-path conclusion to the free-path existential `writesTo8`
    (the path is read off the trace's sib/dir columns — a genuine readout, hence part of the sorted-tree
    decode carrier, NOT a fresh study face); the anti-forge `⟺` is stated at the committed path `p` the
    decode carries.
  * The after-leaf's NON-key / NON-rights fields (`target`/`auth_tag`/`mask_hi`/`expiry`/`breadstuff`) are
    NOT welded by the deployed write gate (only `slot_hash = k` and `mask_lo = v` are) — the documented
    "`(k,v) ↔ CapLeaf` other-field encoding" residual (`writesTo8`'s def). The decode carries the full
    after-leaf; the `⟺` binds the after-root to THAT leaf.
  * The kernel `Caps`-function ↔ cap-tree-commitment lift (`capsMove`) is the named faithful-encoding
    residual the cap family already carries (`RotatedKernelRefinementCapFamily`), unchanged.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto enters ONLY as the named
extracted-collision disjunct `CapOpenColl` (via `capOpen8_binds_leaf_or_collides`, inherited from
`DeployedCapTree`). ⚑ NO chip-CR HYPOTHESIS IS CARRIED ANYWHERE IN THIS FILE — the former
`Cap8Scheme.chip8CR : Compress8CR` FIELD is DELETED (it was false at deployed BabyBear parameters and
made `Cap8Scheme` uninhabitable, so every theorem here was vacuous). Consumes
`RotatedKernelRefinementCapFamily` / `CapOpenEmit` read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementCapFamily

namespace Dregg2.Circuit.Emit.EffectVmCapFamilyComplete

open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme
  (recomposeUp8 capLeafDigest8 capOpen8Find CapOpenColl capOpen8_binds_leaf_or_collides
   capOpen8_binds_leaf_of_injective capOpenColl_refutable_of_injective)
open Dregg2.Circuit.CapMerkleGeneric (StepG)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (writesTo8)

set_option autoImplicit false

/-! ## §1 — the GENERIC cap-tree write-gate cores (CR-carried; the two directions, discharged once).

`recomposeUp8 S8 (capLeafDigest8 S8 ·) path` is the 8-felt cap-tree opening: fold the leaf digest up the
committed sibling/direction path. The two cores below are the write gate's `→` (anti-forge: the after-root
BINDS the after-leaf) and `←` (realizability: the honest narrowed leaf REACHES the after-root along the
before-leaf's path). Both are pure `Cap8Scheme` — every cap tag instantiates them. -/

/-- **`capWrite8_afterRoot_binds_leaf_or_collides` — the 8-felt anti-forge (`→` core), UNCONDITIONAL.**
Along a FIXED membership path, two after-leaves opening to the SAME published after-root are EITHER
EQUAL, OR the deployed arity-16 chip genuinely COLLIDES at the two blocks `capOpen8Find` hands back. A
prover cannot keep the published after cap-root while swapping the written leaf except at that named
collision.

⚑ This replaces `capWrite8_afterRoot_binds_leaf`, which composed `recomposeUp8_inj_of_path` with
`capLeafDigest8_injective` — both discharged from the `Cap8Scheme.chip8CR : Compress8CR` FIELD. That
field is FALSE at deployed BabyBear parameters, so `Cap8Scheme` had NO deployed value and this theorem,
like every `∀ S8 : Cap8Scheme, …` statement in this file, was VACUOUSLY TRUE. The field is deleted;
`DeployedCapTree` §5b.D exhibits a real inhabitant, and the peel is now extraction-as-data. -/
theorem capWrite8_afterRoot_binds_leaf_or_collides (S8 : Cap8Scheme) (path : List (StepG Digest8))
    {nl₁ nl₂ : CapLeaf}
    (h : recomposeUp8 S8 (capLeafDigest8 S8 nl₁) path = recomposeUp8 S8 (capLeafDigest8 S8 nl₂) path) :
    nl₁ = nl₂ ∨ CapOpenColl S8 nl₁ nl₂ path :=
  capOpen8_binds_leaf_or_collides S8 path h

/-- **`capWrite8_afterRoot_reaches` — the `←` half, UNCONDITIONAL and floor-free.** The genuine written
after-leaf DOES open to its own committed after-root along the path. Never rode any CR. -/
theorem capWrite8_afterRoot_reaches (S8 : Cap8Scheme) (path : List (StepG Digest8)) {nl nl' : CapLeaf}
    (h : nl' = nl) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') path = recomposeUp8 S8 (capLeafDigest8 S8 nl) path := by
  rw [h]

/-- **`capWrite8_afterRoot_iff_of_noColl` — THE GENERIC WRITE-GATE BICONDITIONAL, restored.** Fix a
membership path `p` and the genuine written after-leaf `nl`. PROVIDED the candidate/genuine pair is not
an actual chip collision, a candidate after-leaf `nl'` opens to `nl`'s committed after-root along `p`
IFF `nl' = nl`.

⚑ Read the hypothesis carefully — it is NOT the deleted floor. `¬ CapOpenColl S8 nl' nl p` is a claim
about TWO SPECIFIC input blocks, and it is SATISFIED by the deployed chip at every pair that is not one
of its (existent, by pigeonhole) collisions. The deleted `Compress8CR` quantified over ALL pairs and is
therefore refuted outright; this one is an instance-local, checkable, refutable side condition. That is
the whole difference between a vacuous keystone and a true one. -/
theorem capWrite8_afterRoot_iff_of_noColl (S8 : Cap8Scheme) (path : List (StepG Digest8))
    (nl nl' : CapLeaf) (hnc : ¬ CapOpenColl S8 nl' nl path) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') path = recomposeUp8 S8 (capLeafDigest8 S8 nl) path
      ↔ nl' = nl :=
  ⟨fun h => (capOpen8_binds_leaf_or_collides S8 path h).resolve_right hnc, fun h => by rw [h]⟩

/-- **NO STRENGTH LOST — the deleted `capWrite8_afterRoot_binds_leaf` is the injective special case.**
Assume exactly the injectivity the deleted `chip8CR` field asserted and the collision disjunct becomes
impossible, so the old bare `nl₁ = nl₂` falls straight out. What the deletion gave up is not a proved
conclusion — it is the pretence that the deployed arity-16 chip satisfies the hypothesis. Deliberately a
STANDALONE bridge and NOT a hypothesis on any keystone above: `Compress8CR` is FALSE at deployed
BabyBear parameters, so a keystone carrying it would be right back in the vacuity this repair removed. -/
theorem capWrite8_afterRoot_binds_leaf_of_injective (S8 : Cap8Scheme)
    (hCR : Dregg2.Circuit.DeployedCapTree.Compress8CR S8.chipAbsorb8)
    (path : List (StepG Digest8)) {nl₁ nl₂ : CapLeaf}
    (h : recomposeUp8 S8 (capLeafDigest8 S8 nl₁) path = recomposeUp8 S8 (capLeafDigest8 S8 nl₂) path) :
    nl₁ = nl₂ :=
  capOpen8_binds_leaf_of_injective S8 hCR path h

/-- **`capWrite8_realizes` — THE REALIZABILITY `←` (the honest move INHABITS the deployed write relation).**
Given the sorted-tree decode — a before-leaf `bl` keyed `k`, an after-leaf `nl` keyed `k` with narrowed
rights felt `v`, and a shared membership path `p` — the DEPLOYED write relation `writesTo8` is GENUINELY
SATISFIED at the openings of `bl`/`nl` along `p`. This is the "producing the membership-open / after-root
columns that `writesTo8` forces, from a genuine spec" leg: the constructed columns satisfy the relation. -/
theorem capWrite8_realizes (S8 : Cap8Scheme) (bl nl : CapLeaf) (path : List (StepG Digest8)) (k v : ℤ)
    (hblk : bl.slot_hash = k) (hnlk : nl.slot_hash = k) (hnlv : nl.mask_lo = v) :
    writesTo8 S8 (recomposeUp8 S8 (capLeafDigest8 S8 bl) path) k v
      (recomposeUp8 S8 (capLeafDigest8 S8 nl) path) :=
  ⟨bl, nl, path, hblk, hnlk, hnlv, rfl, rfl⟩

/-! ## §2 — the per-tag sorted-tree WRITE DECODE + the per-tag `air_accepts ⟺ spec`.

Each cap tag carries a `<X>WriteDecode` — the honest prover's cap-open write readout: the before/after
leaves + the shared membership path, with the after-leaf's key pinned to the tag's committed cap key and
its rights felt to the tag's narrowed rights (the sorted-tree decode carrier). From it:
  * `<X>_write_realizes` — the DEPLOYED `writesTo8` at the tag's `(k, v)` is realized (`capWrite8_realizes`);
  * `<X>_afterRoot_binds_or_collides_spec` — the write-gate `→` (unconditional): the after cap-root
    binds exactly the tag's genuine narrowed after-leaf, OR the deployed chip collides at a named pair;
    `<X>_afterRoot_iff_spec_of_noColl` restores the `⟺` at any non-colliding candidate;
  * `<X>_write_forge_rejected_or_collides` — the mutation canary (a leaf that is NOT the genuine narrowed
    leaf cannot reach the published after-root, unless it exhibits the named chip collision).
The soundness `→` is the LANDED `RotatedKernelRefinementCapFamily.<X>_descriptorRefines_capOpenSat`
(consumed, not re-authored). -/

/-- **`CapWriteDecode` — the shared sorted-tree WRITE decode carrier (the honest prover's cap-open write
readout).** The before-leaf `beforeLeaf` (keyed `k`), the genuine narrowed after-leaf `afterLeaf` (keyed
`k`, rights felt `v`), the shared committed membership path `path`, and the committed before/after
cap-roots `oldRoot`/`newRoot` the openings recompose to. `k`/`v` are pinned to the tag's committed cap key
and narrowed rights by the per-tag welds (`hbeforeKey`/`hafterKey`/`hafterRights`). DATA-bearing. -/
structure CapWriteDecode (S8 : Cap8Scheme) (k v : ℤ) (oldRoot newRoot : Digest8) : Type where
  beforeLeaf : CapLeaf
  afterLeaf : CapLeaf
  path : List (StepG Digest8)
  hbeforeKey : beforeLeaf.slot_hash = k
  hafterKey : afterLeaf.slot_hash = k
  hafterRights : afterLeaf.mask_lo = v
  hbeforeOpen : recomposeUp8 S8 (capLeafDigest8 S8 beforeLeaf) path = oldRoot
  hafterOpen : recomposeUp8 S8 (capLeafDigest8 S8 afterLeaf) path = newRoot

/-- **`capWriteDecode_realizes` — the DEPLOYED write relation is realized by the decode (the `←`).** The
sorted-tree decode's before/after openings GENUINELY SATISFY `writesTo8` at the committed key/rights — the
honest move inhabits the deployed cap-tree write relation. -/
theorem capWriteDecode_realizes (S8 : Cap8Scheme) (k v : ℤ) (oldRoot newRoot : Digest8)
    (D : CapWriteDecode S8 k v oldRoot newRoot) :
    writesTo8 S8 oldRoot k v newRoot := by
  have h := capWrite8_realizes S8 D.beforeLeaf D.afterLeaf D.path k v
    D.hbeforeKey D.hafterKey D.hafterRights
  rw [D.hbeforeOpen, D.hafterOpen] at h
  exact h

/-- **`capWriteDecode_afterRoot_binds_or_collides` — the WRITE-GATE `→` over the decode, UNCONDITIONAL.**
Along the decode's committed membership path, a candidate after-leaf `nl'` that opens to the published
after cap-root EITHER IS the decode's genuine narrowed after-leaf (keyed `k`, rights `v`), OR the
deployed chip collides at the two named blocks. TRUE of the deployed system, where the old
`chip8CR`-conditioned form was empty. -/
theorem capWriteDecode_afterRoot_binds_or_collides (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hopen : recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot) :
    nl' = D.afterLeaf ∨ CapOpenColl S8 nl' D.afterLeaf D.path :=
  capWrite8_afterRoot_binds_leaf_or_collides S8 D.path (hopen.trans D.hafterOpen.symm)

/-- **`capWriteDecode_afterRoot_reaches` — the `←` half, floor-free.** The decode's genuine narrowed
after-leaf opens to the published after cap-root. Unconditional; this leg never rode any CR. -/
theorem capWriteDecode_afterRoot_reaches (S8 : Cap8Scheme) (k v : ℤ) (oldRoot newRoot : Digest8)
    (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf) (h : nl' = D.afterLeaf) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot := by
  rw [h]; exact D.hafterOpen

/-- **`capWriteDecode_afterRoot_iff_of_noColl` — THE WRITE-GATE BICONDITIONAL over the decode, restored
at any non-colliding candidate.** The `air_accepts ⟺ spec` for the tag's after-root write gate, now
carrying an instance-local side condition the deployed chip SATISFIES (rather than the deleted global
injectivity it refutes). -/
theorem capWriteDecode_afterRoot_iff_of_noColl (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hnc : ¬ CapOpenColl S8 nl' D.afterLeaf D.path) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot ↔ nl' = D.afterLeaf :=
  ⟨fun hopen =>
      (capWriteDecode_afterRoot_binds_or_collides S8 k v oldRoot newRoot D nl' hopen).resolve_right hnc,
   fun h => capWriteDecode_afterRoot_reaches S8 k v oldRoot newRoot D nl' h⟩

/-- **`capWriteDecode_forge_rejected_or_collides` — the mutation canary, UNCONDITIONAL.** Any after-leaf
`nl'` that is NOT the genuine narrowed after-leaf EITHER cannot open to the published after cap-root
along the committed path, OR is a genuine chip collision at the two named blocks. The write gate's
anti-forge bites at deployed parameters, and the exact price of it not biting is EXHIBITED. -/
theorem capWriteDecode_forge_rejected_or_collides (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hne : nl' ≠ D.afterLeaf) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path ≠ newRoot
      ∨ CapOpenColl S8 nl' D.afterLeaf D.path := by
  by_cases hopen : recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot
  · exact Or.inr
      ((capWriteDecode_afterRoot_binds_or_collides S8 k v oldRoot newRoot D nl' hopen).resolve_left hne)
  · exact Or.inl hopen

/-! ### §2.A — attenuate (tag 12, the priority-1 tag): the UPDATE-AT-KEY write, welded to `AttenuateSpec`.

The attenuate write is the in-place slot narrow: the after cap-root commits the narrowed leaf at the SAME
key. The decode's `afterLeaf` carries the committed cap key (`AttenuateCapsTreeEncodes.atKey`, = the
`CAP_KEY` param the deployed `attenuateV3` gate welds) and the narrowed rights felt (= the `KEEP_MASK`
param). The write-gate `⟺` + realizability below are the completeness leg; the soundness `→` is the LANDED
`attenuate_descriptorRefines_capOpenSat` (SAT ⟹ `AttenuateSpec` ∧ `writesTo8`). -/

open Dregg2.Exec (RecChainedState CellId)
open Dregg2.Authority (Auth)
open Dregg2.Circuit.RotatedKernelRefinementCapFamily
  (AttenuateCapsTreeEncodes attenuate_descriptorRefines_exact
   RefreshDelegationCapsTreeEncodes refreshDelegation_descriptorRefines
   DelegateCapsTreeEncodes delegate_descriptorRefines
   DelegateAttenCapsTreeEncodes delegateAtten_descriptorRefines
   RevokeCapsTreeEncodes revoke_descriptorRefines
   RevokeDelegationFullEncodes revokeDelegation_descriptorRefines)
open Dregg2.Circuit.Spec.AuthorityAttenuation (AttenuateSpec DelegateAttenSpec)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec)
open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec RevokeDelegationFullSpec)
open Dregg2.Circuit.Spec.RefreshDelegation (RefreshDelegationFullSpec)
open Dregg2.Circuit.SortedTreeNonMembership (keyOf keysOf SpineCommits sortedInsert)
open Dregg2.Circuit.CapTreeUpdate (sortedRemove capInsert_sound capRemove_sound)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (MembersAt8)
open Dregg2.Circuit.Emit.CapInsertEmit (capInserts8)
open Dregg2.Circuit.Emit.CapRemoveEmit (capRemoves8)

/-- **`attenuate_afterRoot_binds_or_collides_spec` — THE ATTENUATE WRITE-GATE `→`, UNCONDITIONAL.**
Along the committed membership path, an `nl'` the published after cap-root opens to EITHER IS the
genuine narrowed after-leaf (the in-place slot narrow at the committed key `k`, rights felt `v`), OR
exhibits a genuine collision of the deployed arity-16 chip. -/
theorem attenuate_afterRoot_binds_or_collides_spec (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hopen : recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot) :
    nl' = D.afterLeaf ∨ CapOpenColl S8 nl' D.afterLeaf D.path :=
  capWriteDecode_afterRoot_binds_or_collides S8 k v oldRoot newRoot D nl' hopen

/-- **`attenuate_afterRoot_iff_spec_of_noColl` — THE ATTENUATE WRITE-GATE `⟺`, at a non-colliding
candidate.** Both directions, with the instance-local non-collision side condition the deployed chip
satisfies (in place of the deleted global injectivity it refutes). -/
theorem attenuate_afterRoot_iff_spec_of_noColl (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hnc : ¬ CapOpenColl S8 nl' D.afterLeaf D.path) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot ↔ nl' = D.afterLeaf :=
  capWriteDecode_afterRoot_iff_of_noColl S8 k v oldRoot newRoot D nl' hnc

/-- **`attenuate_write_forge_rejected_or_collides` — the attenuate mutation canary, UNCONDITIONAL.** -/
theorem attenuate_write_forge_rejected_or_collides (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hne : nl' ≠ D.afterLeaf) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path ≠ newRoot
      ∨ CapOpenColl S8 nl' D.afterLeaf D.path :=
  capWriteDecode_forge_rejected_or_collides S8 k v oldRoot newRoot D nl' hne

/-- **`attenuate_spec_and_write_realized` — THE COMPLETENESS `←` COMPANION, SPEC-WELDED.** From the
attenuate KERNEL decode (`AttenuateCapsTreeEncodes`, delivering `AttenuateSpec` via the LANDED
`attenuate_descriptorRefines_exact`) AND the sorted-tree WRITE decode `D` over the SAME committed key
(`henc.atKey`) and cap-roots (`henc.oldRoot`/`henc.newRoot`), BOTH SEM legs are assembled: the kernel
`AttenuateSpec` AND the DEPLOYED write relation `writesTo8` (realized, `capWriteDecode_realizes`). This is
the `←`-realized companion to the LANDED soundness `attenuate_descriptorRefines_sat` (the `→`: SAT ⟹
`AttenuateSpec` ∧ `writesTo8`) — the genuine kernel move INHABITS the deployed cap-tree write, over the
decode's committed key/roots. -/
theorem attenuate_spec_and_write_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth) (v : ℤ)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep)
    (D : CapWriteDecode S8 henc.atKey v henc.oldRoot henc.newRoot) :
    AttenuateSpec pre actor idx keep post
    ∧ writesTo8 S8 henc.oldRoot henc.atKey v henc.newRoot :=
  ⟨attenuate_descriptorRefines_exact S8 pre post actor idx keep henc,
   capWriteDecode_realizes S8 henc.atKey v henc.oldRoot henc.newRoot D⟩

/-! ### §2.B — refreshDelegation (tag, priority 5): the UPDATE-AT-KEY write over the DELEGATIONS tree.

Refresh is the second UPDATE-AT-KEY tag: it overwrites the child's `delegations` snapshot in place (the
KEY — the child — stays; the leaf VALUE moves), so it rides the SAME `writesTo8` / `CapWriteDecode`
machinery as attenuate (over the delegations tree). The write-gate `⟺` + realizability below are the
completeness leg; the soundness `→` is the LANDED `refreshDelegation_descriptorRefines_capOpenSat`. -/

/-- **`refresh_afterRoot_binds_or_collides_spec` — THE REFRESH WRITE-GATE `→`, UNCONDITIONAL.** Along the
committed membership path, an `nl'` the published after DELEGATIONS-tree root opens to EITHER IS the
genuine in-place-overwritten after-leaf (keyed the committed child key `k`, snapshot felt `v`), OR
exhibits a genuine chip collision. -/
theorem refresh_afterRoot_binds_or_collides_spec (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hopen : recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot) :
    nl' = D.afterLeaf ∨ CapOpenColl S8 nl' D.afterLeaf D.path :=
  capWriteDecode_afterRoot_binds_or_collides S8 k v oldRoot newRoot D nl' hopen

/-- **`refresh_afterRoot_iff_spec_of_noColl` — THE REFRESH WRITE-GATE `⟺`, at a non-colliding
candidate.** -/
theorem refresh_afterRoot_iff_spec_of_noColl (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hnc : ¬ CapOpenColl S8 nl' D.afterLeaf D.path) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path = newRoot ↔ nl' = D.afterLeaf :=
  capWriteDecode_afterRoot_iff_of_noColl S8 k v oldRoot newRoot D nl' hnc

/-- **`refresh_write_forge_rejected_or_collides` — the refresh mutation canary, UNCONDITIONAL.** -/
theorem refresh_write_forge_rejected_or_collides (S8 : Cap8Scheme) (k v : ℤ)
    (oldRoot newRoot : Digest8) (D : CapWriteDecode S8 k v oldRoot newRoot) (nl' : CapLeaf)
    (hne : nl' ≠ D.afterLeaf) :
    recomposeUp8 S8 (capLeafDigest8 S8 nl') D.path ≠ newRoot
      ∨ CapOpenColl S8 nl' D.afterLeaf D.path :=
  capWriteDecode_forge_rejected_or_collides S8 k v oldRoot newRoot D nl' hne

/-- **`refresh_spec_and_write_realized` — the refresh completeness `←` companion, SPEC-WELDED.** From the
refresh KERNEL decode (`RefreshDelegationCapsTreeEncodes`, delivering `RefreshDelegationFullSpec` via the
LANDED `refreshDelegation_descriptorRefines`) AND the sorted-tree WRITE decode `D` over the same committed
key/roots, both SEM legs are assembled: the kernel `RefreshDelegationFullSpec` AND the DEPLOYED
`writesTo8` (realized). -/
theorem refresh_spec_and_write_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId) (v : ℤ)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child)
    (D : CapWriteDecode S8 henc.atKey v henc.oldRoot henc.newRoot) :
    RefreshDelegationFullSpec pre actor child post
    ∧ writesTo8 S8 henc.oldRoot henc.atKey v henc.newRoot :=
  ⟨refreshDelegation_descriptorRefines S8 pre post actor child henc,
   capWriteDecode_realizes S8 henc.atKey v henc.oldRoot henc.newRoot D⟩

/-! ## §3 — INSERT effects (delegate / delegateAtten / introduce): the sorted-tree INSERT completeness.

For INSERT the DEPLOYED relation is `capInserts8 S8 oldRoot leaf newRoot` (a fresh edge grows the committed
key set by exactly `keyOf leaf`). Its both-directions key-set characterization is the LANDED
`capInsert_sound` (`∀ y, y ∈ keysOf newRoot ↔ y = keyOf leaf ∨ y ∈ keysOf oldRoot`). The NEW `←` glue is
`capInsert8_realizes` (the honest fresh edge INHABITS `capInserts8`) and the per-tag SPEC-WELDED
realization companion (`<X>_spec_and_insert_realized`). The after-tree leaf membership (`MembersAt8`) is
the honest prover's cap-open readout (part of the named sorted-tree decode carrier). -/

/-- **`capInsert8_realizes` — the DEPLOYED insert relation is realized from the decode (the `←`).** Given
the sorted-tree insert decode — the old root binds `spine`, the fresh key `keyOf leaf ∉ keysOf oldRoot`,
the after-leaf's membership in the new tree, and the new root binds `sortedInsert (keyOf leaf) spine` — the
DEPLOYED `capInserts8` is GENUINELY SATISFIED. The honest fresh edge inhabits the deployed insert. -/
theorem capInsert8_realizes (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (leaf : CapLeaf)
    (spine : List ℤ) (hold : SpineCommits S8 oldRoot spine)
    (hfresh : keyOf leaf ∉ keysOf S8 oldRoot) (hafterMem : MembersAt8 S8 newRoot leaf)
    (hnew : SpineCommits S8 newRoot (sortedInsert (keyOf leaf) spine)) :
    capInserts8 S8 oldRoot leaf newRoot :=
  ⟨spine, hold, hfresh, hafterMem, hnew⟩

/-- **`capInsert_keyset_iff` — the INSERT key-set BICONDITIONAL (both directions, LANDED core).** The
committed key set after the insert is EXACTLY the old set plus the fresh key — `capInsert_sound`, re-exposed
as the write-gate's set-level `air_accepts ⟺ spec` (a forged key-set move is refuted by either direction). -/
theorem capInsert_keyset_iff (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ) (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine) (hfresh : k ∉ keysOf S8 oldRoot)
    (hnew : SpineCommits S8 newRoot (sortedInsert k spine)) :
    ∀ y, y ∈ keysOf S8 newRoot ↔ (y = k ∨ y ∈ keysOf S8 oldRoot) :=
  capInsert_sound S8 oldRoot newRoot k spine hold hfresh hnew

/-- **`CapInsertLeafWitness` — the after-tree leaf-membership carrier for an insert decode.** The honest
prover's cap-open readout of the freshly inserted leaf (keyed `newKey`) and its membership in the after
tree — the sorted-tree decode's leaf leg. -/
structure CapInsertLeafWitness (S8 : Cap8Scheme) (newKey : ℤ) (newRoot : Digest8) : Type where
  leaf : CapLeaf
  hkey : keyOf leaf = newKey
  hafterMem : MembersAt8 S8 newRoot leaf

/-- **`delegate_spec_and_insert_realized` — the delegate completeness `←` companion, SPEC-WELDED.** From the
delegate KERNEL decode (delivering `DelegateSpec` via LANDED `delegate_descriptorRefines`) + the after-tree
leaf witness, both SEM legs: `DelegateSpec` AND the DEPLOYED `capInserts8` at the committed fresh key/roots. -/
theorem delegate_spec_and_insert_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (lw : CapInsertLeafWitness S8 henc.newKey henc.newRoot) :
    DelegateSpec pre del rec t post ∧ capInserts8 S8 henc.oldRoot lw.leaf henc.newRoot := by
  refine ⟨delegate_descriptorRefines S8 pre post del rec t henc, ?_⟩
  refine capInsert8_realizes S8 henc.oldRoot henc.newRoot lw.leaf henc.spine henc.hold ?_ lw.hafterMem ?_
  · rw [lw.hkey]; exact henc.hfresh
  · rw [lw.hkey]; exact henc.hnew

/-- **`delegateAtten_spec_and_insert_realized` — the delegateAtten completeness `←` companion (attenuated
grant = INSERT of an attenuated cap).** -/
theorem delegateAtten_spec_and_insert_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep)
    (lw : CapInsertLeafWitness S8 henc.newKey henc.newRoot) :
    DelegateAttenSpec pre del rec t keep post ∧ capInserts8 S8 henc.oldRoot lw.leaf henc.newRoot := by
  refine ⟨delegateAtten_descriptorRefines S8 pre post del rec t keep henc, ?_⟩
  refine capInsert8_realizes S8 henc.oldRoot henc.newRoot lw.leaf henc.spine henc.hold ?_ lw.hafterMem ?_
  · rw [lw.hkey]; exact henc.hfresh
  · rw [lw.hkey]; exact henc.hnew

/-- **`introduce_spec_and_insert_realized` — the introduce completeness `←` companion.** Introduce shares
the delegate INSERT decode / `DelegateSpec` (its executor arm is `.introduceA`, `execFullA_introduceA_iff_spec`
= `DelegateSpec`), so the SEM assembly rides `delegate_descriptorRefines` + `capInsert8_realizes` at the
introduce edge. -/
theorem introduce_spec_and_insert_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (intro rec t : CellId)
    (henc : DelegateCapsTreeEncodes S8 pre post intro rec t)
    (lw : CapInsertLeafWitness S8 henc.newKey henc.newRoot) :
    DelegateSpec pre intro rec t post ∧ capInserts8 S8 henc.oldRoot lw.leaf henc.newRoot :=
  delegate_spec_and_insert_realized S8 pre post intro rec t henc lw

/-! ## §4 — REMOVE effects (revoke / revokeDelegation): the sorted-tree REMOVE completeness.

For REMOVE the DEPLOYED relation is `capRemoves8 S8 oldRoot leaf newRoot` (the revoked edge's key leaves the
committed set). Both-directions key-set characterization is the LANDED `capRemove_sound`. The NEW `←` glue is
`capRemove8_realizes` + the per-tag SPEC-WELDED companions. -/

/-- **`capRemove8_realizes` — the DEPLOYED remove relation is realized from the decode (the `←`).** Given
the sorted-tree remove decode — the old root binds `spine`, the revoked leaf's membership in the OLD tree,
its non-membership in the after tree, and the new root binds `sortedRemove (keyOf leaf) spine` — the DEPLOYED
`capRemoves8` is GENUINELY SATISFIED. -/
theorem capRemove8_realizes (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (leaf : CapLeaf)
    (spine : List ℤ) (hold : SpineCommits S8 oldRoot spine) (hbeforeMem : MembersAt8 S8 oldRoot leaf)
    (hgone : keyOf leaf ∉ keysOf S8 newRoot)
    (hnew : SpineCommits S8 newRoot (sortedRemove (keyOf leaf) spine)) :
    capRemoves8 S8 oldRoot leaf newRoot :=
  ⟨spine, hold, hbeforeMem, hgone, hnew⟩

/-- **`capRemove_keyset_iff` — the REMOVE key-set BICONDITIONAL (both directions, LANDED core).** The
committed key set after the revoke is EXACTLY the old set minus the revoked key — `capRemove_sound`. -/
theorem capRemove_keyset_iff (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ) (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine) (hnew : SpineCommits S8 newRoot (sortedRemove k spine)) :
    ∀ y, y ∈ keysOf S8 newRoot ↔ (y ∈ keysOf S8 oldRoot ∧ y ≠ k) :=
  capRemove_sound S8 oldRoot newRoot k spine hold hnew

/-- **`CapRemoveLeafWitness` — the revoked-leaf carrier for a remove decode.** The honest prover's cap-open
readout of the revoked leaf (keyed `remKey`), its membership in the OLD tree, and its non-membership in the
after tree. -/
structure CapRemoveLeafWitness (S8 : Cap8Scheme) (remKey : ℤ) (oldRoot newRoot : Digest8) : Type where
  leaf : CapLeaf
  hkey : keyOf leaf = remKey
  hbeforeMem : MembersAt8 S8 oldRoot leaf
  hgone : remKey ∉ keysOf S8 newRoot

/-- **`revoke_spec_and_remove_realized` — the revoke completeness `←` companion, SPEC-WELDED.** From the
revoke KERNEL decode (delivering `RevokeSpec` via LANDED `revoke_descriptorRefines`) + the revoked-leaf
witness, both SEM legs: `RevokeSpec` AND the DEPLOYED `capRemoves8` at the committed revoked key/roots. -/
theorem revoke_spec_and_remove_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t)
    (lw : CapRemoveLeafWitness S8 henc.remKey henc.oldRoot henc.newRoot) :
    RevokeSpec pre holder t post ∧ capRemoves8 S8 henc.oldRoot lw.leaf henc.newRoot := by
  refine ⟨revoke_descriptorRefines S8 pre post holder t henc, ?_⟩
  refine capRemove8_realizes S8 henc.oldRoot henc.newRoot lw.leaf henc.spine henc.hold lw.hbeforeMem ?_ ?_
  · rw [lw.hkey]; exact lw.hgone
  · rw [lw.hkey]; exact henc.hnew

/-- **`revokeDelegation_spec_and_remove_realized` — the delegation-revoke completeness `←` companion.** The
faithful delegation revoke composes the cap-edge REMOVE (the nested `capRemove` decode) with the epoch step;
this assembles `RevokeDelegationFullSpec` (via LANDED `revokeDelegation_descriptorRefines`) AND the DEPLOYED
`capRemoves8` at the removed edge. -/
theorem revokeDelegation_spec_and_remove_realized (S8 : Cap8Scheme)
    (pre post : RecChainedState) (parent child : CellId)
    (henc : RevokeDelegationFullEncodes S8 pre post parent child)
    (lw : CapRemoveLeafWitness S8 henc.capRemove.remKey henc.capRemove.oldRoot henc.capRemove.newRoot) :
    RevokeDelegationFullSpec pre parent child post
    ∧ capRemoves8 S8 henc.capRemove.oldRoot lw.leaf henc.capRemove.newRoot := by
  refine ⟨revokeDelegation_descriptorRefines S8 pre post parent child henc, ?_⟩
  refine capRemove8_realizes S8 henc.capRemove.oldRoot henc.capRemove.newRoot lw.leaf
    henc.capRemove.spine henc.capRemove.hold lw.hbeforeMem ?_ ?_
  · rw [lw.hkey]; exact lw.hgone
  · rw [lw.hkey]; exact henc.capRemove.hnew

/-! ### §4.C — CANARIES: the three sorted-tree moves are OBSERVABLY distinct (the key-set biconditionals
are non-vacuous; a `:= True` / identity stub would break these). The write-gate mutation canaries are the
per-tag `_write_forge_rejected` (update-at-key) and the load-bearing membership premises of
`capInsert8_realizes` / `capRemove8_realizes` (insert/remove). -/

-- INSERT (delegate / delegateAtten / introduce): the committed key set GROWS by exactly the fresh key.
#guard sortedInsert (25 : ℤ) [10, 20, 30] == [10, 20, 25, 30]
-- REMOVE (revoke / revokeDelegation): the committed key set SHRINKS by exactly the revoked key.
#guard sortedRemove (20 : ℤ) [10, 20, 30] == [10, 30]
-- UPDATE-AT-KEY (attenuate / refresh): the committed key SPINE is PRESERVED (the leaf narrows in place).
#guard sortedInsert (20 : ℤ) [10, 20, 30] == [10, 20, 30]

/-! ## §5 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms capWrite8_afterRoot_binds_leaf_or_collides
#assert_axioms capWrite8_afterRoot_reaches
#assert_axioms capWrite8_afterRoot_iff_of_noColl
#assert_axioms capWrite8_afterRoot_binds_leaf_of_injective
#assert_axioms capWrite8_realizes
#assert_axioms capWriteDecode_realizes
#assert_axioms capWriteDecode_afterRoot_binds_or_collides
#assert_axioms capWriteDecode_afterRoot_reaches
#assert_axioms capWriteDecode_afterRoot_iff_of_noColl
#assert_axioms capWriteDecode_forge_rejected_or_collides
#assert_axioms attenuate_afterRoot_binds_or_collides_spec
#assert_axioms attenuate_afterRoot_iff_spec_of_noColl
#assert_axioms attenuate_write_forge_rejected_or_collides
#assert_axioms attenuate_spec_and_write_realized
#assert_axioms refresh_afterRoot_binds_or_collides_spec
#assert_axioms refresh_afterRoot_iff_spec_of_noColl
#assert_axioms refresh_write_forge_rejected_or_collides
#assert_axioms refresh_spec_and_write_realized
#assert_axioms capInsert8_realizes
#assert_axioms capInsert_keyset_iff
#assert_axioms delegate_spec_and_insert_realized
#assert_axioms delegateAtten_spec_and_insert_realized
#assert_axioms introduce_spec_and_insert_realized
#assert_axioms capRemove8_realizes
#assert_axioms capRemove_keyset_iff
#assert_axioms revoke_spec_and_remove_realized
#assert_axioms revokeDelegation_spec_and_remove_realized

end Dregg2.Circuit.Emit.EffectVmCapFamilyComplete
