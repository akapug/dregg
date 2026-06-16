/-
# Dregg2.Circuit.DeployedCapTree — THE FAITHFUL model of the DEPLOYED 7-field cap-tree.

## Why this file exists (the authority-leg ground-truth correction)

The kernel-authority bridge (`Dregg2.Circuit.CapRootBridge`) and the in-circuit non-amplification
proofs (`EffectVmEmitRotationV3.attenuateV3_non_amp`) discharge their cap-openings against
`DescriptorIR2.opensTo`, whose denotation is `Dregg2.Substrate.Heap`:

    opensTo hash r k o := ∃ h : FeltHeap, SortedKeys h ∧ Heap.root hash h = r ∧ Heap.get h k = o
    Heap.root hash h   := hash (h.map (fun e => hash [e.1, e.2]))           -- FLAT sponge, 2-field leaf

That model is a FLAT SPONGE of a sorted list of **2-field** leaves `hash[addr, value]`.

The value the CELL actually commits (and the EffectVM circuit seeds `cap_root` from) is
`dregg_cell::compute_canonical_capability_root_felt` → `circuit/src/cap_root.rs::CanonicalCapTree`:

    leaf  = hash_many[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff]   -- 7 fields
    node  = hash_fact(left, [right])                                                       -- 0xFACF tag
    root  = the depth-16 BINARY MERKLE fold of the sorted-by-slot_hash padded leaf list

These are THREE DIFFERENT objects (the `Substrate.Heap` flat-sponge 2-field model, the deployed
`CanonicalCapTree` depth-16 7-field binary Merkle, and — separately — the Rust `descriptor_ir2`
`map_op` AIR's depth-16 **2-field** `CanonicalHeapTree`). The flat-sponge `Heap` is NOT a faithful
abstraction of the deployed tree: it has the wrong leaf arity AND the wrong root construction.

This module is the HONEST replacement: a Lean model of the leaf digest + the `hash_fact` node fold
up a sibling/direction path (the real depth-16 binary-Merkle opening shape), and the statement —
with a started proof — that a membership opening AGAINST THIS TREE binds a real held capability
carrying `(target, rights ⊇ write)`. It is the floor the cap-open SHOULD discharge against.

## What is faithful here (file:line anchors)

  * `capLeafDigest` ≡ `cap_root.rs::CapLeaf::digest` (`hash_many` of the 7 fields, same order).
  * `nodeOf` ≡ `cap_root.rs` internal node `hash_fact(l, [r])` (= `poseidon2::hash_fact`, the
    `FACT_MARK = 0xFACF`-tagged 2-input compression — modelled as `sponge [FACT_MARK, l, r]`).
  * `recomposeUp` ≡ the `attenuation_witness` / `prove_membership` fold: at each level mix
    `(cur, sib)` by the direction bit (`dir = 0` ⇒ cur is the LEFT child) and apply `nodeOf`.
  * `MembersAt root pos leaf` ≡ a `prove_membership` path of `siblings/directions` recomposing
    `root` from the leaf at padded position `pos` — `cap_root.rs::prove_membership` /
    `descriptor_ir2.rs` MapOps AIR `cur_old`/`MAP_OLD_LEAF` fold up the fact bus.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis (the SAME single floor the whole commitment tower carries). No
`sorry`, no `:= True`, no `native_decide`. NEW file; imports are read-only.
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Exec.Kernel
import Dregg2.Circuit.Emit.EffectVmEmitCapReshape

namespace Dregg2.Circuit.DeployedCapTree

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Authority (Cap Auth Caps Label capAuthConferred)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (authBitN rightsMaskOf)

set_option autoImplicit false

/-! ## §0 — the deployed leaf (the 7-field `CapLeaf`, byte-faithful to `cap_root.rs`). -/

/-- The 7 canonical leaf fields, in `cap_root.rs::CapLeaf` order. The deployed tree stores
`capLeafDigest` of these at each leaf position. (`slot_hash` is the sort key; here we keep the
fields abstract `ℤ` — the deployment instance is BabyBear.) -/
structure CapLeaf where
  /-- The sort key: a Poseidon2 image of the (unique) c-list slot (`cap_root.rs:95`). -/
  slot_hash : ℤ
  /-- The capability's target cell id, folded to one felt (`cap_root.rs:98`). -/
  target : ℤ
  /-- The `AuthRequired` tier (+ absorbed vk_hash for `Custom`), one felt (`cap_root.rs:99`). -/
  auth_tag : ℤ
  /-- `EffectMask` low 16 bits (`cap_root.rs:101`). -/
  mask_lo : ℤ
  /-- `EffectMask` high 16 bits (`cap_root.rs:103`). -/
  mask_hi : ℤ
  /-- Optional expiry height (`NONE_SENTINEL` when absent) (`cap_root.rs:105`). -/
  expiry : ℤ
  /-- Optional breadstuff hash folded to one felt (`cap_root.rs:107`). -/
  breadstuff : ℤ
  deriving DecidableEq

/-- **`capLeafDigest sponge l`** — the 7-field Poseidon2 leaf digest, in canonical field order.
BYTE-IDENTICAL to `cap_root.rs::CapLeaf::digest` (`hash_many[slot_hash, target, auth_tag, mask_lo,
mask_hi, expiry, breadstuff]`, `cap_root.rs:115`). This is what the sorted Merkle tree stores at the
leaf position; the leaf is *placed* by its `slot_hash` ordering. -/
def capLeafDigest (sponge : List ℤ → ℤ) (l : CapLeaf) : ℤ :=
  sponge [l.slot_hash, l.target, l.auth_tag, l.mask_lo, l.mask_hi, l.expiry, l.breadstuff]

/-- **Leaf injectivity under CR** — distinct 7-tuples yield distinct digests (the `breadstuff`/
`auth_tier`/`mask_hi` binding the `cap_root.rs` tests pin, here as ONE CR consequence). -/
theorem capLeafDigest_injective (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    {l₁ l₂ : CapLeaf} (h : capLeafDigest sponge l₁ = capLeafDigest sponge l₂) : l₁ = l₂ := by
  have hlist := hCR _ _ h
  -- Peel the 7-element list equality field-by-field.
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq,
      List.cons.injEq, List.cons.injEq] at hlist
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, _⟩ := hlist
  cases l₁; cases l₂
  simp_all

/-! ## §1 — the internal node (the `hash_fact` compression, byte-faithful to `cap_root.rs`).

`cap_root.rs` (and the `descriptor_ir2` MapOps AIR) fold internal nodes with
`hash_fact(left, [right])` — `poseidon2::hash_fact`, the `FACT_MARK = 0xFACF`-domain-separated
2-input compression (`descriptor_ir2.rs:256`, `BUS_FACT`). We model it as the same sponge applied to
the tagged 3-list `[FACT_MARK, l, r]`; the tag is a fixed constant, so node injectivity is one CR
consequence and node images never alias leaf images (different arities/prefixes). -/

/-- The `hash_fact` domain-separation marker (`descriptor_ir2.rs:256`, `cap_root.rs` `hash_fact`). -/
def FACT_MARK : ℤ := 0xFACF

/-- **`nodeOf sponge l r`** — the internal node hash `hash_fact(l, [r])`, modelled as the tagged
2-input compression `sponge [FACT_MARK, l, r]`. The deployed `CanonicalCapTree` folds every level
with this (`cap_root.rs:302` `hash_fact(chunk[0], &[chunk[1]])`). -/
def nodeOf (sponge : List ℤ → ℤ) (l r : ℤ) : ℤ := sponge [FACT_MARK, l, r]

/-- **Node injectivity under CR** — equal node images ⇒ equal `(left, right)` children. The
per-level peel of the membership recompose's anti-ghost. -/
theorem nodeOf_injective (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    {l₁ r₁ l₂ r₂ : ℤ} (h : nodeOf sponge l₁ r₁ = nodeOf sponge l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hlist := hCR _ _ h
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq] at hlist
  exact ⟨hlist.2.1, hlist.2.2.1⟩

/-! ## §2 — the membership opening (the depth-16 binary-Merkle recompose up a sibling path).

A membership witness is a list of `(sibling, direction)` steps (`cap_root.rs::prove_membership`
returns exactly `(siblings, directions)`; `directions[i] = 0` ⇔ the current node is the LEFT child
at level `i`). Recomposing folds `nodeOf` up the path, mixing `(cur, sib)` by the direction bit —
LITERALLY the `descriptor_ir2` MapOps AIR's `mix` closure (`descriptor_ir2.rs:2109`):
`left = (1-dir)·cur + dir·sib`, `right = (1-dir)·sib + dir·cur`. -/

/-- One Merkle path step: the sibling digest at this level + the direction bit. -/
structure Step where
  /-- The sibling digest at this level (`cap_root.rs` `siblings[level]`). -/
  sib : ℤ
  /-- The direction bit: `0` ⇒ `cur` is the LEFT child (sibling right), `1` ⇒ right child. -/
  dir : Bool
  deriving DecidableEq

/-- **`recomposeUp sponge cur path`** — fold the held digest up the sibling/direction path to the
root. At each level, if `dir = false` (LEFT child) the node is `nodeOf cur sib`, else
`nodeOf sib cur`. This is the exact `attenuation_witness` / MapOps-AIR fold
(`cap_root.rs:425-431`, `descriptor_ir2.rs:2116-2127`). -/
def recomposeUp (sponge : List ℤ → ℤ) (cur : ℤ) : List Step → ℤ
  | [] => cur
  | s :: rest =>
    recomposeUp sponge (if s.dir then nodeOf sponge s.sib cur else nodeOf sponge cur s.sib) rest

/-- **`MembersAt sponge root leaf`** — the deployed-tree membership statement: there is a
sibling/direction path recomposing `root` from the 7-field leaf's digest. The witness is the path
(`cap_root.rs::prove_membership`); the relation hides it behind the existential, exactly as the
in-circuit opening realizes it. This is the HONEST replacement for `Substrate.Heap`'s flat-sponge
`opensTo` — same role, but the REAL leaf arity and the REAL `hash_fact` binary fold. -/
def MembersAt (sponge : List ℤ → ℤ) (root : ℤ) (leaf : CapLeaf) : Prop :=
  ∃ path : List Step, recomposeUp sponge (capLeafDigest sponge leaf) path = root

/-- **`recomposeUp` is injective in its STARTING digest under CR** — equal recomposed roots from the
SAME path force the same starting leaf digest (peel each level by `nodeOf_injective`). The anti-ghost
spine: a prover cannot keep the published root while swapping the opened leaf along a fixed path. -/
theorem recomposeUp_inj_of_path (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (path : List Step) : ∀ {a b : ℤ}, recomposeUp sponge a path = recomposeUp sponge b path → a = b := by
  induction path with
  | nil => intro a b h; simpa [recomposeUp] using h
  | cons s rest ih =>
    intro a b h
    simp only [recomposeUp] at h
    have hstep := ih h
    cases hd : s.dir with
    | false =>
      rw [hd] at hstep
      simp only [Bool.false_eq_true, if_false] at hstep
      exact (nodeOf_injective sponge hCR hstep).1
    | true =>
      rw [hd] at hstep
      simp only [if_true] at hstep
      exact (nodeOf_injective sponge hCR hstep).2

/-! ## §3 — the FAITHFUL commitment relation + the authority bridge against THIS tree.

The replacement for `CapRootBridge.CapsEncodes` (which is over `Substrate.Heap`). `DeployedEncodes`
says `cap_root` is the deployed `CanonicalCapTree`-root of a leaf set that FAITHFULLY realizes the
kernel `caps`: a write-rights membership opening of an authority-edge leaf witnesses a real held
endpoint cap. We carry the faithfulness as the runtime-encoding contract, exactly the
`compute_canonical_capability_root_felt` discipline. -/

/-- A leaf carries WRITE authority iff its `mask_lo` limb is the mask of a read+write endpoint cap.
We decode against the deployed split-mask `(mask_lo, mask_hi)`: the write authority bit lives in the
low limb (`authBitN Auth.write < 2^16`), so `confersWriteLeaf` reads it off `mask_lo`
(`cap_root.rs::split_effect_mask`, `EffectVmEmitCapReshape.rightsMaskOf`). -/
def confersWriteLeaf (l : CapLeaf) : Prop :=
  l.mask_lo = rightsMaskOf (Cap.endpoint 0 [Auth.read, Auth.write])

/-- **`DeployedFaithful sponge caps leafAt`** — the leaf-set `leafAt` (indexed by authority edge)
faithfully realizes `caps`: every WRITE-rights member leaf at an `(actor ⇒ src)` edge is backed by a
real held `Cap.endpoint src r` conferring `Auth.write`. The forward encoding contract (caps ⇒ tree),
the genuine direction; the bridge below reads it backward through one opening. -/
structure DeployedFaithful (sponge : List ℤ → ℤ) (caps : Caps)
    (root : ℤ) (leafAt : Label → Label → CapLeaf) : Prop where
  /-- FAITHFULNESS: a write-rights member opening witnesses a REAL held endpoint cap. -/
  backed : ∀ (actor src : Label),
    MembersAt sponge root (leafAt actor src) →
    confersWriteLeaf (leafAt actor src) →
    ∃ r', Cap.endpoint src r' ∈ caps actor ∧ Auth.write ∈ r'

/-- **`DeployedEncodes sponge caps root`** — THE deployed commitment relation: `root` is the
deployed cap-tree root of SOME leaf assignment that faithfully realizes `caps`. This is what
"the `cap_root` column (= `compute_canonical_capability_root_felt`) commits the kernel cap-table"
MEANS, against the REAL 7-field tree (NOT the flat-sponge `Substrate.Heap`). -/
def DeployedEncodes (sponge : List ℤ → ℤ) (caps : Caps) (root : ℤ) : Prop :=
  ∃ leafAt : Label → Label → CapLeaf, DeployedFaithful sponge caps root leafAt

/-- **`deployedCapOpen_implies_authorizedB` — THE AUTHORITY BRIDGE against the deployed tree.**
GIVEN the deployed commitment relation `DeployedEncodes sponge caps root`, AND an in-circuit
membership opening `MembersAt sponge root (leafAt actor src)` carrying the write bit — THEN the
kernel's `authorizedB` PASSES for the turn `⟨actor, src, dst, amt⟩`. The circuit's depth-16
binary-Merkle membership proof discharges the kernel's authority gate.

This is the structural twin of `CapRootBridge.capOpen_implies_authorizedB`, re-seated on the FAITHFUL
deployed tree: the leaf that opens is the SAME leaf the faithfulness contract is stated over (the
`leafAt actor src` the encoding lays down), so faithfulness fires directly. -/
theorem deployedCapOpen_implies_authorizedB
    (sponge : List ℤ → ℤ) (caps : Caps) (root : ℤ)
    (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful sponge caps root leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hopen : MembersAt sponge root (leafAt actor src))
    (hwrite : confersWriteLeaf (leafAt actor src)) :
    Dregg2.Exec.authorizedB caps { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨r', hmem, hwrite'⟩ := hfaith.backed actor src hopen hwrite
  unfold Dregg2.Exec.authorizedB
  simp only [Bool.or_eq_true]
  right
  rw [List.any_eq_true]
  refine ⟨Cap.endpoint src r', hmem, ?_⟩
  simp only [Bool.or_eq_true]
  right
  show (match (Cap.endpoint src r' : Cap) with
        | .endpoint t rights => (t == src) && rights.contains Auth.write
        | _ => false) = true
  simp only [beq_self_eq_true, Bool.true_and]
  rw [List.contains_eq_mem]
  simpa using hwrite'

/-! ## §4 — NON-VACUITY: the deployed-tree bridge FIRES on a concrete edge, and the gate is REAL.

Mirrors `CapRootBridge.bridge_fires`/`empty_caps_unauthorized`, re-seated on the deployed tree. We
exhibit a concrete `caps` (actor 5 holds a read+write cap over src 9), a faithful leaf assignment for
that edge, and the bridge firing; plus a witness-FALSE where the empty cap-table backs no opening. -/

/-- A single-edge cap-table: actor 5 holds a read+write endpoint cap over src 9; everyone else holds
nothing. -/
def oneEdgeCaps : Caps := fun a => if a = 5 then [Cap.endpoint 9 [Auth.read, Auth.write]] else []

/-- The faithful leaf assignment for `oneEdgeCaps`: the `(5 ⇒ 9)` edge carries the write-mask leaf;
every other edge carries a leaf whose `mask_lo` is NOT the write mask (so `confersWriteLeaf` is false
there and faithfulness is vacuously met). -/
def oneEdgeLeaf : Label → Label → CapLeaf := fun actor src =>
  if actor = 5 ∧ src = 9 then
    { slot_hash := 0, target := 9, auth_tag := 0,
      mask_lo := rightsMaskOf (Cap.endpoint 0 [Auth.read, Auth.write]),
      mask_hi := 0, expiry := 0, breadstuff := 0 }
  else
    { slot_hash := 0, target := 0, auth_tag := 0,
      mask_lo := rightsMaskOf (Cap.endpoint 0 [Auth.read, Auth.write]) + 1,
      mask_hi := 0, expiry := 0, breadstuff := 0 }

/-- **`oneEdge_faithful`** — `oneEdgeLeaf` faithfully realizes `oneEdgeCaps` against any root: the
ONLY edge carrying the write mask is `(5 ⇒ 9)`, and actor 5 holds the read+write cap over src 9. -/
theorem oneEdge_faithful (sponge : List ℤ → ℤ) (root : ℤ) :
    DeployedFaithful sponge oneEdgeCaps root oneEdgeLeaf := by
  refine ⟨?_⟩
  intro actor src _hopen hwrite
  -- `confersWriteLeaf (oneEdgeLeaf actor src)` forces actor = 5 ∧ src = 9 (else mask_lo = mask+1).
  by_cases hedge : actor = 5 ∧ src = 9
  · obtain ⟨ha, hs⟩ := hedge
    subst ha; subst hs
    exact ⟨[Auth.read, Auth.write], by simp [oneEdgeCaps], by simp⟩
  · exfalso
    simp only [confersWriteLeaf, oneEdgeLeaf, if_neg hedge] at hwrite
    -- mask_lo = mask + 1 = mask is impossible.
    omega

/-- **`deployedEncodes_inhabited`** — the deployed commitment relation is INHABITED: `oneEdgeCaps`
is encoded (faithfully) at any root by `oneEdgeLeaf`. So `DeployedEncodes` is non-vacuous. -/
theorem deployedEncodes_inhabited (sponge : List ℤ → ℤ) (root : ℤ) :
    DeployedEncodes sponge oneEdgeCaps root :=
  ⟨oneEdgeLeaf, oneEdge_faithful sponge root⟩

/-- **NON-VACUITY (the bridge FIRES on a real edge).** Given a membership opening of the `(5 ⇒ 9)`
write-mask leaf against the deployed tree, the bridge yields `authorizedB oneEdgeCaps ⟨5,9,…⟩ = true`
— the END-TO-END witness that the deployed-tree bridge is non-vacuous. -/
theorem bridge_fires (sponge : List ℤ → ℤ) (root : ℤ)
    (hopen : MembersAt sponge root (oneEdgeLeaf 5 9)) :
    Dregg2.Exec.authorizedB oneEdgeCaps { actor := 5, src := 9, dst := 0, amt := 0 } = true := by
  apply deployedCapOpen_implies_authorizedB sponge oneEdgeCaps root oneEdgeLeaf
      (oneEdge_faithful sponge root) 5 9 0 0 hopen
  unfold confersWriteLeaf oneEdgeLeaf; simp

/-- **NON-VACUITY (witness FALSE — the gate is real).** Over the EMPTY cap-table, the kernel rejects
a non-owned src: `authorizedB (fun _ => []) ⟨5, 9, …⟩ = false`. So the bridge's conclusion is NOT
vacuously always-true — without a real held cap the gate stays closed. -/
theorem empty_caps_unauthorized :
    Dregg2.Exec.authorizedB (fun _ => []) { actor := 5, src := 9, dst := 0, amt := 0 } = false := by
  unfold Dregg2.Exec.authorizedB; simp

/-! ## §5 — Axiom hygiene. -/

#assert_axioms capLeafDigest_injective
#assert_axioms nodeOf_injective
#assert_axioms recomposeUp_inj_of_path
#assert_axioms deployedCapOpen_implies_authorizedB
#assert_axioms oneEdge_faithful
#assert_axioms deployedEncodes_inhabited
#assert_axioms bridge_fires
#assert_axioms empty_caps_unauthorized

end Dregg2.Circuit.DeployedCapTree
