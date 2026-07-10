/-
# `Dregg2.Deos.DocSubstrateSound` — the two genuine document-soundness properties, RE-HOMED onto the
WIDE 8-felt sorted-Poseidon2 MERKLE root the code actually commits (`compute_canonical_heap_root_8`).

## Why this file was re-homed (the SUPERSEDED-model correction)

The prior revision proved these two properties by composing over `Dregg2.Substrate.Heap.root_binds_get`
— but `Substrate.Heap.root hash h = hash (h.map leafOf)` is a FLAT SPONGE over the sorted leaf list,
folding each node to a SINGLE ~2^31 felt. The codebase itself flags that sponge as SUPERSEDED
(`Circuit/DeployedHeapTree` = "THE HONEST replacement for the flat-sponge Substrate.Heap opensTo"):
the deployed heap root is a depth-`d` binary Merkle map over `(addr, value)` leaves whose nodes ride the
arity-16 `node8` chip (`heap_root.rs::heap_node8`, ~124-bit), and the heap GENTIAN tooth
(`circuit/tests/heap_root_gentian_weld.rs`) exhibits two genuinely-different heaps that COLLIDE on the
1-felt lane-0 projection while topping DIFFERENT 8-felt roots. So the old composition proved properties
of a model that is NOT the code's commitment.

This file re-homes both theorems onto the FAITHFUL wide root, riding `Dregg2.Circuit.MapMerkleRoot`
(the depth-`d` `node8` binary fold) — NOT the sponge:

  * `MapMerkleRoot.mapRoot8_injective` — equal 8-felt root ⟹ equal heap, under the named arity-16 chip
    CR (`Heap8Scheme.chip8CR`, a HYPOTHESIS carried in `S8`, never an axiom), which is itself
    `perfectRoot8_injective` ∘ `DeployedHeapTree.heapNodeOf8_injective` composed up the perfect tree;
  * `MapMerkleRoot.opensToMerkle8_functional` — the consumable form: two heaps behind the SAME 8-felt
    root `r` reading at the same key `k` agree on the opened value. "The wide root binds every opened
    (key, value)." This is the whole-map "equal root ⟹ equal opened value" the doc composition needs.

The heavy lifting (the wide root binds each opened leaf VALUE) is thus DONE in `MapMerkleRoot`. This
file supplies the two document-level properties as THIN compositions on top of `opensToMerkle8_functional`:

  1. **`substrate_root_binds_element_structure`** — the wide root binds the Element STRUCTURE, not just
     opaque leaf bytes. `substrate.rs::leaf_for_atom` hashes `id ‖ canonical_bytes(Element) ‖ status ‖
     provenance`; we model that grammar (`encodeElement`), prove it injective by a TOTAL left-inverse
     decoder (`encodeElement_injective`, scheme-INDEPENDENT — canonical_bytes injectivity, unchanged by
     the re-home), then compose: `opensToMerkle8_functional` (wide root binds the opened leaf digest) ∘
     CR (digest ⟹ preimage) ∘ `atomLeafPreimage_injective` ∘ `encodeElement_injective`. Equal 8-felt
     heap-root ⟹ equal tag ∧ attrs ∧ children.

  2. **`substrate_root_binds_conflict_alternatives`** — conflict-as-state soundness on the WIDE commit.
     A conflict's alternatives are two `COLL_FIELDS` leaves (`substrate.rs::leaf_for_field`,
     `name ‖ value ‖ provenance`). From `opensToMerkle8_functional` at the two field keys, equal 8-felt
     root ⟹ both alternatives agree — value AND provenance. A forged alternative (same rendered value,
     different author) cannot hide under an equal WIDE root.

## The two crypto carriers (both HYPOTHESES, faithful to the code, honestly stated)

The wide commitment folds TWO named collision-resistant primitives, and both enter ONLY as hypotheses:

  * the TREE carrier `S8 : Heap8Scheme` — the arity-16 `node8`/leaf chip (`heap_root.rs`), carrying its
    CR as the `chip8CR` FIELD. The wide root `mapRoot8 S8 d h` and every leaf `heapLeafDigest8` ride it;
  * the LEAF-DIGEST carrier `hash : List ℤ → ℤ` with `hCR : Poseidon2SpongeCR hash` — the
    `leaf_for_atom` / `leaf_for_field` hash that maps a length-prefixed field preimage to the felt
    STORED at its heap key (`to_heap_map`'s value). In deployment this is a BLAKE3/Poseidon2 digest; the
    model collapses it to the ONE named CR sponge.

`to_heap_map` stores, at each key, `hash preimage`. So an opening `opensToMerkle8 S8 d r k
(some (hash preimage))` says exactly "the wide root `r` opens, at key `k`, the leaf digest of `preimage`".

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as the
named `S8.chip8CR` field (via `MapMerkleRoot`) and the named `Poseidon2SpongeCR hash` hypothesis, never
as an axiom. Read-only imports; `Substrate.Heap.root`/`root_binds_get` (the SUPERSEDED sponge) is NOT
used for the root binding.
-/
import Dregg2.Circuit.MapMerkleRoot
import Dregg2.Circuit.DeployedHeapTree
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Tactics
import Mathlib.Logic.Function.Basic

namespace Dregg2.Deos.DocSubstrateSound

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.MapMerkleRoot (opensToMerkle8 opensToMerkle8_functional)

/-! ## 1. The `canonical_bytes` Element grammar (`atom.rs::canonical_bytes`, the Element arm).

`canonical_bytes` for `AtomContent::Element { tag, attrs, children }` emits (`atom.rs:245-262`):
`push(1)` ‖ `run(tag)` ‖ `attrs.len()` ‖ (for each `(k,v)`: `run(k) ‖ run(v)`) ‖ `children.len()` ‖
(for each child: its fixed-width id). We model bytes as `ℤ` cells and each length/count as ONE `ℤ`
cell. This grammar + its decoder are SCHEME-INDEPENDENT: they decode the leaf PREIMAGE and are
unchanged by the re-home from the sponge to the wide Merkle root (only the ROOT the preimage rides
changes). -/

/-- The commitment's view of `atom.rs::AtomContent::Element`: the tag bytes, the ordered
`(key-bytes, value-bytes)` attrs, and the child atom ids. -/
structure ElementModel where
  /-- The DOM tag, as its canonical bytes (`run(tag.as_bytes())`). -/
  tag : List ℤ
  /-- DOM attributes in author order, each as `(key bytes, value bytes)`. -/
  attrs : List (List ℤ × List ℤ)
  /-- Child atom ids, in document order (each a fixed-width id cell). -/
  children : List ℤ
deriving DecidableEq, Repr

/-! ### The canonical, self-delimiting encoders (mirroring `canonical_bytes`). -/

/-- A length-prefixed run (`canonical_bytes::run`): the length, then the elements. Self-delimiting. -/
def encRun (xs : List ℤ) : List ℤ := (xs.length : ℤ) :: xs

/-- One attribute: `run(key) ‖ run(value)`. -/
def encAttr (kv : List ℤ × List ℤ) : List ℤ := encRun kv.1 ++ encRun kv.2

/-- One child id: a single fixed-width cell (`c.0.to_le_bytes()`, collapsed to one `ℤ`). -/
def encChild (c : ℤ) : List ℤ := [c]

/-- Concatenate a self-delimiting encoder over a list. -/
def encList {α : Type} (enc : α → List ℤ) : List α → List ℤ
  | [] => []
  | x :: xs => enc x ++ encList enc xs

/-- Count-prefixed list of self-delimiting elements (`len() as u64` then the elements). -/
def encListWith {α : Type} (enc : α → List ℤ) (xs : List α) : List ℤ :=
  (xs.length : ℤ) :: encList enc xs

/-- **`encodeElement`** — the Element `canonical_bytes` preimage: the discriminant `1`, then the
length-prefixed tag run, the count-prefixed attributes, and the count-prefixed children. Every
variable-length run is length-prefixed, so sections cannot be confused (the anti-concat-ambiguity
discipline of `canonical_bytes`). -/
def encodeElement (e : ElementModel) : List ℤ :=
  (1 : ℤ) :: (encRun e.tag ++ encListWith encAttr e.attrs ++ encListWith encChild e.children)

/-! ### The total left-inverse decoder ⟹ `encodeElement` is injective. -/

/-- A decoder: consume a prefix, return the value + the remainder. -/
abbrev Dec (α : Type) := List ℤ → Option (α × List ℤ)

def decRun : Dec (List ℤ)
  | [] => none
  | n :: rest => some (rest.take n.toNat, rest.drop n.toNat)

def decAttr : Dec (List ℤ × List ℤ) := fun s =>
  match decRun s with
  | some (k, r1) =>
    match decRun r1 with
    | some (v, r2) => some ((k, v), r2)
    | none => none
  | none => none

def decChild : Dec ℤ
  | c :: rest => some (c, rest)
  | [] => none

/-- Apply a decoder `k` times, threading the remainder. -/
def decN {α : Type} (dec : Dec α) : Nat → Dec (List α)
  | 0, s => some ([], s)
  | k + 1, s =>
    match dec s with
    | some (a, s') =>
      match decN dec k s' with
      | some (as, s'') => some (a :: as, s'')
      | none => none
    | none => none

/-- Decode a count-prefixed list. -/
def decListWith {α : Type} (dec : Dec α) : Dec (List α)
  | [] => none
  | n :: rest => decN dec n.toNat rest

/-- Decode an Element `canonical_bytes` preimage: check the discriminant `1`, then the tag run,
the count-prefixed attrs, and the count-prefixed children (rejecting any other discriminant, so a
`Text` preimage — discriminant `0` — is refused, not aliased). -/
def decElement : Dec ElementModel
  | [] => none
  | t :: rest =>
    if t = 1 then
      match decRun rest with
      | some (tag, r1) =>
        match decListWith decAttr r1 with
        | some (attrs, r2) =>
          match decListWith decChild r2 with
          | some (children, r3) => some (⟨tag, attrs, children⟩, r3)
          | none => none
        | none => none
      | none => none
    else none

/-! ### Roundtrip lemmas: each `dec (enc x ++ rest) = some (x, rest)`. -/

theorem decRun_enc (xs rest : List ℤ) : decRun (encRun xs ++ rest) = some (xs, rest) := by
  show decRun ((xs.length : ℤ) :: (xs ++ rest)) = some (xs, rest)
  simp only [decRun, Int.toNat_natCast, List.take_left, List.drop_left]

theorem decAttr_enc (kv : List ℤ × List ℤ) (rest : List ℤ) :
    decAttr (encAttr kv ++ rest) = some (kv, rest) := by
  cases kv with
  | mk k v =>
    show decAttr (encRun k ++ encRun v ++ rest) = _
    simp only [decAttr, List.append_assoc, decRun_enc]

theorem decChild_enc (c : ℤ) (rest : List ℤ) : decChild (encChild c ++ rest) = some (c, rest) := rfl

theorem decN_enc {α : Type} (enc : α → List ℤ) (dec : Dec α)
    (hrt : ∀ a r, dec (enc a ++ r) = some (a, r)) :
    ∀ (xs : List α) (rest : List ℤ),
      decN dec xs.length (encList enc xs ++ rest) = some (xs, rest) := by
  intro xs
  induction xs with
  | nil => intro rest; rfl
  | cons a as ih =>
    intro rest
    show decN dec (as.length + 1) (enc a ++ encList enc as ++ rest) = some (a :: as, rest)
    rw [List.append_assoc]
    simp only [decN, hrt a (encList enc as ++ rest), ih rest]

theorem decListWith_enc {α : Type} (enc : α → List ℤ) (dec : Dec α)
    (hrt : ∀ a r, dec (enc a ++ r) = some (a, r)) (xs : List α) (rest : List ℤ) :
    decListWith dec (encListWith enc xs ++ rest) = some (xs, rest) := by
  show decListWith dec ((xs.length : ℤ) :: (encList enc xs ++ rest)) = some (xs, rest)
  show decN dec ((xs.length : ℤ)).toNat (encList enc xs ++ rest) = some (xs, rest)
  rw [Int.toNat_natCast]
  exact decN_enc enc dec hrt xs rest

theorem decElement_enc (e : ElementModel) (rest : List ℤ) :
    decElement (encodeElement e ++ rest) = some (e, rest) := by
  cases e with
  | mk tag attrs children =>
    show decElement ((1 : ℤ) ::
      (encRun tag ++ encListWith encAttr attrs ++ encListWith encChild children) ++ rest) = _
    simp only [decElement, List.cons_append, List.append_assoc, ↓reduceIte,
      decRun_enc,
      decListWith_enc encAttr decAttr decAttr_enc,
      decListWith_enc encChild decChild decChild_enc]

/-- **`encodeElement_injective`** — the `canonical_bytes` Element grammar has a TOTAL left inverse
(`decElement`), so equal Element preimages force equal Element structure (tag, attrs, children).
Purely combinatorial: no crypto, scheme-INDEPENDENT (the re-home does not touch it). -/
theorem encodeElement_injective : Function.Injective encodeElement := by
  intro e e' h
  have he : decElement (encodeElement e) = some (e, ([] : List ℤ)) := by
    have := decElement_enc e []; rwa [List.append_nil] at this
  have he' : decElement (encodeElement e') = some (e', ([] : List ℤ)) := by
    have := decElement_enc e' []; rwa [List.append_nil] at this
  rw [h, he', Option.some.injEq, Prod.mk.injEq] at he
  exact he.1.symm

#assert_axioms encodeElement_injective

/-! ## 2. The `COLL_ATOMS` leaf preimage (`substrate.rs::leaf_for_atom`) binds the Element structure. -/

/-- The commitment's view of an Element `atom.rs::Atom`: id, its Element content, status byte, and
`(author, patch)` provenance. -/
structure AtomModel where
  id : ℤ
  elem : ElementModel
  status : ℤ
  author : ℤ
  patch : ℤ
deriving DecidableEq, Repr

/-- **`atomLeafPreimage`** — the `COLL_ATOMS` leaf preimage of `substrate.rs::leaf_for_atom`:
`id ‖ canonical_bytes(Element) ‖ status ‖ provenance`. The Element `canonical_bytes` are
self-delimiting, so `status`/`author`/`patch` follow unambiguously. -/
def atomLeafPreimage (a : AtomModel) : List ℤ :=
  a.id :: (encodeElement a.elem ++ [a.status, a.author, a.patch])

/-- The total left-inverse decoder for an atom leaf preimage. -/
def decAtomLeaf : Dec AtomModel
  | [] => none
  | id :: rest =>
    match decElement rest with
    | some (e, r1) =>
      match r1 with
      | status :: author :: patch :: r2 => some (⟨id, e, status, author, patch⟩, r2)
      | _ => none
    | none => none

theorem decAtomLeaf_enc (a : AtomModel) (rest : List ℤ) :
    decAtomLeaf (atomLeafPreimage a ++ rest) = some (a, rest) := by
  cases a with
  | mk id elem status author patch =>
    show decAtomLeaf (id :: (encodeElement elem ++ [status, author, patch]) ++ rest) = _
    simp only [decAtomLeaf, List.cons_append, List.append_assoc, List.cons_append, List.nil_append,
      decElement_enc]

/-- **`atomLeafPreimage_injective`** — the atom leaf preimage has a total left inverse, so equal
preimages force equal atoms (id, Element structure, status, provenance). No crypto yet. -/
theorem atomLeafPreimage_injective : Function.Injective atomLeafPreimage := by
  intro a a' h
  have ha : decAtomLeaf (atomLeafPreimage a) = some (a, ([] : List ℤ)) := by
    have := decAtomLeaf_enc a []; rwa [List.append_nil] at this
  have ha' : decAtomLeaf (atomLeafPreimage a') = some (a', ([] : List ℤ)) := by
    have := decAtomLeaf_enc a' []; rwa [List.append_nil] at this
  rw [h, ha', Option.some.injEq, Prod.mk.injEq] at ha
  exact ha.1.symm

/-- Heap collection holding the document's atoms (`substrate.rs::COLL_ATOMS`). -/
def COLL_ATOMS : ℤ := 0
/-- Heap collection holding the document's field assignments (`substrate.rs::COLL_FIELDS`). -/
def COLL_FIELDS : ℤ := 2

/-- **`substrate_root_binds_element_structure` — the WIDE 8-felt root binds Element STRUCTURE.**

Two documents committed to the SAME wide `substrate_commit` (the 8-felt Merkle root `r`), each opening
at key `key` the `leaf_for_atom` digest of an Element atom (`opensToMerkle8 … (some (hash
(atomLeafPreimage aᵢ)))`), agree on that atom's Element STRUCTURE: equal tag, equal attrs, equal
children — not merely equal opaque leaf bytes. Without this, the wide commit binds bytes; WITH it, it
binds the DOM structure the author authored.

The composition, each step reused not re-invented, RIDING THE WIDE MERKLE (never the sponge):
  * `opensToMerkle8_functional` (`MapMerkleRoot`, PROVEN — itself `mapRoot8_injective` ∘
    `perfectRoot8_injective` ∘ `DeployedHeapTree.heapNodeOf8_injective`) — equal 8-felt root ⟹ the
    opened leaf VALUE at `key` agrees: `hash (atomLeafPreimage a₁) = hash (atomLeafPreimage a₂)`;
  * `hCR` (the named `Poseidon2SpongeCR hash` leaf-digest carrier) — equal digest ⟹ equal preimage;
  * `atomLeafPreimage_injective` — equal preimage ⟹ equal atom;
  * `encodeElement_injective` — folded into the atom equality (the Element field), giving structure.
The two crypto steps are exactly the two named carriers: the arity-16 chip CR (in `S8`, via
`opensToMerkle8_functional`) and the leaf-digest `hCR`. -/
theorem substrate_root_binds_element_structure
    (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : Nat)
    {r : Digest8} (key : ℤ) (a₁ a₂ : AtomModel)
    (hv₁ : opensToMerkle8 S8 d r key (some (hash (atomLeafPreimage a₁))))
    (hv₂ : opensToMerkle8 S8 d r key (some (hash (atomLeafPreimage a₂)))) :
    a₁.elem.tag = a₂.elem.tag ∧ a₁.elem.attrs = a₂.elem.attrs
      ∧ a₁.elem.children = a₂.elem.children := by
  have hbind := opensToMerkle8_functional S8 d hv₁ hv₂
  have hpre : atomLeafPreimage a₁ = atomLeafPreimage a₂ := hCR _ _ (Option.some.inj hbind)
  have ha : a₁ = a₂ := atomLeafPreimage_injective hpre
  exact ⟨by rw [ha], by rw [ha], by rw [ha]⟩

#assert_axioms substrate_root_binds_element_structure

/-! ## 3. Conflict-as-state soundness on the WIDE commit (`substrate.rs::leaf_for_field`).

A conflict is two field assignments at the same name — two `COLL_FIELDS` leaves. Each leaf binds
`name ‖ value ‖ provenance` (`leaf_for_field`). We model that preimage and prove: equal WIDE 8-felt
root ⟹ both alternatives agree (value AND provenance). -/

/-- The commitment's view of one field assignment / conflict alternative
(`graph.rs::FieldAssign` + name): the field name bytes, the value bytes, and its `(author, patch)`
provenance — WHO authored this alternative. -/
structure FieldAssignModel where
  name : List ℤ
  value : List ℤ
  author : ℤ
  patch : ℤ
deriving DecidableEq, Repr

/-- **`fieldLeafPreimage`** — the `COLL_FIELDS` leaf preimage of `substrate.rs::leaf_for_field`:
`run(name) ‖ run(value) ‖ provenance`. Both clashing alternatives' provenance bind here. -/
def fieldLeafPreimage (f : FieldAssignModel) : List ℤ :=
  encRun f.name ++ encRun f.value ++ [f.author, f.patch]

/-- The total left-inverse decoder for a field leaf preimage. -/
def decFieldLeaf : Dec FieldAssignModel := fun s =>
  match decRun s with
  | some (name, r1) =>
    match decRun r1 with
    | some (value, r2) =>
      match r2 with
      | author :: patch :: r3 => some (⟨name, value, author, patch⟩, r3)
      | _ => none
    | none => none
  | none => none

theorem decFieldLeaf_enc (f : FieldAssignModel) (rest : List ℤ) :
    decFieldLeaf (fieldLeafPreimage f ++ rest) = some (f, rest) := by
  cases f with
  | mk name value author patch =>
    show decFieldLeaf (encRun name ++ encRun value ++ [author, patch] ++ rest) = _
    simp only [decFieldLeaf, List.append_assoc, decRun_enc, List.cons_append, List.nil_append]

/-- **`fieldLeafPreimage_injective`** — the field leaf preimage has a total left inverse, so equal
preimages force equal alternatives (name, value, AND provenance). No crypto yet. -/
theorem fieldLeafPreimage_injective : Function.Injective fieldLeafPreimage := by
  intro f f' h
  have hf : decFieldLeaf (fieldLeafPreimage f) = some (f, ([] : List ℤ)) := by
    have := decFieldLeaf_enc f []; rwa [List.append_nil] at this
  have hf' : decFieldLeaf (fieldLeafPreimage f') = some (f', ([] : List ℤ)) := by
    have := decFieldLeaf_enc f' []; rwa [List.append_nil] at this
  rw [h, hf', Option.some.injEq, Prod.mk.injEq] at hf
  exact hf.1.symm

/-- **`substrate_root_binds_conflict_alternatives` — conflict-as-state soundness on the WIDE commit.**

Two documents committed to the SAME wide `substrate_commit` (8-felt root `r`), each opening a
two-alternative conflict as the `COLL_FIELDS` leaves at keys `keyA`, `keyB` (`hash (fieldLeafPreimage
…)`), agree on BOTH alternatives — name, value AND provenance. So a substituted/forged alternative
(even one that renders identically but is authored by someone else) CANNOT hide under an equal WIDE
root: it would move some `COLL_FIELDS` leaf, refused by the arity-16 chip's collision-resistance —
a forge that survived a lossy lane-0 commit does NOT survive the 8-felt welded commit.

A THIN composition on the already-proven wide heavy lifting: `opensToMerkle8_functional` pins each
opened field leaf VALUE; the named `Poseidon2SpongeCR hash` carrier peels the digest;
`fieldLeafPreimage_injective` reads off the alternative. Never the sponge `root_binds_get`. -/
theorem substrate_root_binds_conflict_alternatives
    (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : Nat)
    {r : Digest8} (keyA keyB : ℤ) (altA altB altA' altB' : FieldAssignModel)
    (hA₁ : opensToMerkle8 S8 d r keyA (some (hash (fieldLeafPreimage altA))))
    (hB₁ : opensToMerkle8 S8 d r keyB (some (hash (fieldLeafPreimage altB))))
    (hA₂ : opensToMerkle8 S8 d r keyA (some (hash (fieldLeafPreimage altA'))))
    (hB₂ : opensToMerkle8 S8 d r keyB (some (hash (fieldLeafPreimage altB')))) :
    altA = altA' ∧ altB = altB' := by
  have hbindA := opensToMerkle8_functional S8 d hA₁ hA₂
  have hbindB := opensToMerkle8_functional S8 d hB₁ hB₂
  exact ⟨fieldLeafPreimage_injective (hCR _ _ (Option.some.inj hbindA)),
         fieldLeafPreimage_injective (hCR _ _ (Option.some.inj hbindB))⟩

#assert_axioms fieldLeafPreimage_injective
#assert_axioms substrate_root_binds_conflict_alternatives

/-! ## 4. NON-VACUITY over the WIDE root — the GENTIAN pair (`heap_root_gentian_weld.rs`): two
GENUINELY-DIFFERENT heaps that COLLIDE on lane 0 but SEPARATE at the full 8-felt root.

The whole point of the re-home: the sponge / lane-0 projection could NOT distinguish two heaps whose
lone entry is keyed differently but whose ~2^31 lane-0 root coincides (the GENTIAN birthday pair
`COLLIDE_SALT_A/B`). The WIDE 8-felt leaf digest DOES. We reconstruct that shape over a computable
reference 8-output chip whose lane 0 is a lossy projection (`% 5`, standing in for the deployed
~2^31 limb) and whose completion lanes carry the full sponge — so lane 0 can collide while the full
`Digest8` separates. -/

/-- The reference Horner sponge (computable; NOT real crypto — the deployment carrier is the arity-16
Poseidon2 chip behind `Heap8Scheme.chip8CR`). Local to the demo; the theorems above never touch it. -/
def demoSponge (xs : List ℤ) : ℤ := xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

/-- A reference 8-output chip: lane 0 is the LOSSY projection (`% 5`, the toy stand-in for the
deployed lane-0 ~2^31 limb), lanes 1..7 carry the FULL sponge. So two inputs congruent on lane 0 can
still separate on the completion lanes — the exact GENTIAN shape. -/
def refChip8 (xs : List ℤ) : Digest8 := fun i => if i.val = 0 then demoSponge xs % 5 else demoSponge xs

/-- The wide 8-felt leaf digest of a heap entry `(addr, value)` over the reference chip (the demo twin
of `DeployedHeapTree.heapLeafDigest8`; at depth 0 the perfect-tree root IS this single leaf digest). -/
def demoLeaf8 (e : ℤ × ℤ) : Digest8 := refChip8 [e.1, e.2]

/-- The pinned lane-0-colliding pair (models `heap_root_gentian_weld.rs`'s `COLLIDE_SALT_A/B`): the
lone heap entry maps the SAME value `42` at GENUINELY-DIFFERENT addresses `1` vs `6`. -/
def entryA : ℤ × ℤ := (1, 42)
def entryB : ℤ × ℤ := (6, 42)

-- The two heaps are GENUINELY different states (the entry sits at a different address):
#guard decide (entryA ≠ entryB)
-- LANE 0 COLLIDES — a verifier pinning only the lane-0 (~2^31) projection cannot tell them apart
-- (the 31-bit hole the sponge / lane-0 commit leaves open):
#guard demoLeaf8 entryA 0 == demoLeaf8 entryB 0
-- The FULL 8-felt root SEPARATES them — the completion lanes carry what lane 0 misses (the GENTIAN
-- close: the wide root binds the opened (addr, value) at full width):
#guard demoLeaf8 entryA 1 != demoLeaf8 entryB 1

/-- **`wideRoot_separates_lane0_collision`** — the wide-root non-vacuity, as a THEOREM (not merely a
`#guard`): the GENTIAN pair is two genuinely-different heaps (`entryA ≠ entryB`) whose lane-0
projections COLLIDE yet whose full 8-felt leaf digests are UNEQUAL. So the 8-felt root DISTINGUISHES
what the lossy lane-0 / sponge projection could not — the `substrate_root_binds_*` hypotheses
("equal 8-felt root") genuinely constrain the heap, and a lane-0-only commit would not have. -/
theorem wideRoot_separates_lane0_collision :
    entryA ≠ entryB
      ∧ demoLeaf8 entryA 0 = demoLeaf8 entryB 0
      ∧ demoLeaf8 entryA ≠ demoLeaf8 entryB := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have h1 := congrFun h 1
  revert h1
  decide

/-! ### The forged Element / forged conflict alternative each MOVE the WIDE leaf digest.

The stored heap VALUE at a key is the `leaf_for_atom` / `leaf_for_field` DIGEST (`demoSponge` of the
canonical preimage); the wide heap entry is `(addr, storedValue)`, whose wide leaf digest is
`demoLeaf8`. A tampered Element or a forged conflict author changes the preimage
(`*_injective` above), hence the stored digest, hence the WIDE leaf digest — so by
`substrate_root_binds_*` it cannot keep the published 8-felt root. -/

/-- The stored heap value for an atom leaf: its `leaf_for_atom` digest. -/
def atomStored (a : AtomModel) : ℤ := demoSponge (atomLeafPreimage a)
/-- The stored heap value for a field leaf: its `leaf_for_field` digest. -/
def fieldStored (f : FieldAssignModel) : ℤ := demoSponge (fieldLeafPreimage f)

-- An honest Element `<p>` and three FORGERIES of it (retagged / attr-injected / child-injected).
def elemHonest : ElementModel := ⟨[112], [], []⟩                 -- tag "p"
def elemForgedTag : ElementModel := ⟨[100, 105, 118], [], []⟩    -- tag "div" (retagged)
def elemForgedAttr : ElementModel := ⟨[112], [([115], [120])], []⟩ -- injected attr
def elemForgedChild : ElementModel := ⟨[112], [], [42]⟩          -- injected child

def atomHonest : AtomModel := ⟨1, elemHonest, 0, 7, 100⟩
def atomForgedTag : AtomModel := ⟨1, elemForgedTag, 0, 7, 100⟩
def atomForgedAttr : AtomModel := ⟨1, elemForgedAttr, 0, 7, 100⟩
def atomForgedChild : AtomModel := ⟨1, elemForgedChild, 0, 7, 100⟩

-- The Element grammar genuinely distinguishes structure (encoding + decidable-inequality witnesses):
#guard decide (elemHonest ≠ elemForgedTag)
#guard decide (elemHonest ≠ elemForgedAttr)
#guard decide (elemHonest ≠ elemForgedChild)
#guard encodeElement elemHonest != encodeElement elemForgedTag
#guard encodeElement elemHonest != encodeElement elemForgedAttr
#guard encodeElement elemHonest != encodeElement elemForgedChild

-- **Witness FALSE (anti-forge):** each Element forgery MOVES the WIDE leaf digest (completion lane 1
-- of `refChip8 [addr, leaf_for_atom digest]`) — the published 8-felt `heap_root` cannot be kept while
-- retagging, adding an attr, or adding a child:
#guard demoLeaf8 (0, atomStored atomForgedTag) 1 != demoLeaf8 (0, atomStored atomHonest) 1
#guard demoLeaf8 (0, atomStored atomForgedAttr) 1 != demoLeaf8 (0, atomStored atomHonest) 1
#guard demoLeaf8 (0, atomStored atomForgedChild) 1 != demoLeaf8 (0, atomStored atomHonest) 1

-- A genuine conflict alternative and a FORGED one: SAME name+value, FORGED author (13 ≠ 9).
def altHonest : FieldAssignModel := ⟨[116], [66], 9, 200⟩        -- name "t", value "B", author 9
def altForged : FieldAssignModel := ⟨[116], [66], 13, 200⟩       -- same value, author FORGED to 13

-- The forge is real (renders identically — same value bytes — but the author differs):
#guard altHonest.value == altForged.value
#guard decide (altHonest ≠ altForged)
#guard fieldLeafPreimage altHonest != fieldLeafPreimage altForged
-- **Witness FALSE (anti-forge):** the forged author MOVES the WIDE leaf digest — a conflict cannot
-- hide a forged alternative under an equal 8-felt `substrate_commit`:
#guard demoLeaf8 (0, fieldStored altForged) 1 != demoLeaf8 (0, fieldStored altHonest) 1

#assert_axioms wideRoot_separates_lane0_collision

end Dregg2.Deos.DocSubstrateSound
