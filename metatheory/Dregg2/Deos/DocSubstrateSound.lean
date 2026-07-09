/-
# `Dregg2.Deos.DocSubstrateSound` — the two genuine document-soundness properties, RE-HOMED onto
the DEPLOYED commit (`dregg-doc/src/substrate.rs::substrate_commit`, the sorted-Poseidon2 heap root).

## Why this file exists (the over-deletion, corrected)

An earlier campaign proved these two properties against a PARALLEL, NON-DEPLOYED linear-sponge
commitment (`Dregg2.Deos.DocCommit`, `docCommit hash d = hash (encode d)`), which was then deleted.
The deployed commitment is DIFFERENT: `substrate_commit(g) = compute_heap_root(to_heap_map(g))` — the
document projected into a sorted-Poseidon2 heap map `(collection_id, key) → leafDigest`, whose root's
INJECTIVITY IS ALREADY PROVEN in `Dregg2.Substrate.Heap`:

  * `root_injective` (Heap.lean:420) — equal heap root ⟹ equal leaf list, under the ONE named crypto
    carrier `Poseidon2SpongeCR` (a HYPOTHESIS, never an axiom);
  * `root_binds_get` (Heap.lean:435) — equal heap root ⟹ the value at EVERY `(collection_id, key)`
    address agrees. "The root binds every stored (key,value)."

So the heavy lifting (the root binds each leaf VALUE) is DONE. This file supplies the two document-
level properties the over-deletion removed, but now as THIN compositions on top of `root_binds_get`:

  1. **`substrate_root_binds_element_structure`** — the deployed root binds the Element STRUCTURE, not
     just opaque leaf bytes. `substrate.rs::leaf_for_atom` hashes `id ‖ content.canonical_bytes() ‖
     status ‖ provenance`; for an Element the `canonical_bytes` are the length-prefixed
     `tag ‖ attrs ‖ children` grammar (`atom.rs::canonical_bytes`, the Element arm). We model that
     grammar (`encodeElement`), prove it injective by a TOTAL left-inverse decoder
     (`encodeElement_injective`), then compose: `root_binds_get` (leaf digest bound) ∘ CR (digest ⟹
     preimage) ∘ `atomLeafPreimage_injective` (preimage ⟹ atom) ∘ `encodeElement_injective` (Element
     bytes ⟹ Element structure). Equal substrate heap-root ⟹ equal tag ∧ attrs ∧ children.

  2. **`substrate_root_binds_conflict_alternatives`** — conflict-as-state soundness ON THE DEPLOYED
     COMMIT. A conflict's alternatives are two `COLL_FIELDS` leaves (`substrate.rs::leaf_for_field`,
     `name ‖ value ‖ provenance`, one per field assignment). From `root_binds_get` at the two field
     keys, equal substrate heap-root ⟹ both alternatives agree — value AND provenance. This is the
     recovered `docCommit_conflict_binds_both`, but ABOUT `substrate_commit`. A forged alternative
     (same rendered value, different author) cannot hide under an equal deployed root.

## The modeling contract (faithful to `substrate.rs`, honestly stated)

`to_heap_map` stores, at each `(collection_id, key)`, a leaf DIGEST of a length-prefixed preimage.
We model that digest as `hash preimage` with `hash` the SAME `Poseidon2SpongeCR` carrier the heap
root is folded with — the Heap.lean idiom, where a leaf `hash[addr,value]` and the root `hash(leaves)`
already share ONE carrier (`Heap.leafOf` / `Heap.root`). In deployment the digest is BLAKE3 and the
fold is Poseidon2; both are collision-resistant, and the model collapses them to the one named CR
sponge — no NEW commitment scheme is introduced. The keys are the canonical sequential indices of
`to_heap_map` (an atom at `(COLL_ATOMS, idx)`, each conflict alternative at `(COLL_FIELDS, idx)`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as
the named `Poseidon2SpongeCR` hypothesis — exactly as in `Heap.lean`, never as a new axiom. Read-only
imports; the deleted `DocCommit` is NOT re-imported.
-/
import Dregg2.Substrate.Heap
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Tactics
import Mathlib.Logic.Function.Basic

namespace Dregg2.Deos.DocSubstrateSound

open Dregg2.Substrate.Heap
  (FeltHeap hget hset get root root_binds_get addrOf refSponge)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## 1. The `canonical_bytes` Element grammar (`atom.rs::canonical_bytes`, the Element arm).

`canonical_bytes` for `AtomContent::Element { tag, attrs, children }` emits (`atom.rs:245-262`):
`push(1)` ‖ `run(tag)` ‖ `attrs.len()` ‖ (for each `(k,v)`: `run(k) ‖ run(v)`) ‖ `children.len()` ‖
(for each child: its fixed-width id). We model bytes as `ℤ` cells and each length/count as ONE `ℤ`
cell (the Heap/DocCommit idiom). Strings enter as their `.as_bytes()` view — a `List ℤ` — which is
exactly what `canonical_bytes` hashes (it never sees the `String`, only its bytes); children are
their fixed-width integer ids. -/

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
Purely combinatorial: no crypto. This is the recovered injective-decoder technique, re-homed onto
`atom.rs::canonical_bytes`. -/
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

/-- **`substrate_root_binds_element_structure` — the deployed root binds Element STRUCTURE.**

Two documents committed to the SAME `substrate_commit` (`root hash h₁ = root hash h₂`), each storing
at `(COLL_ATOMS, key)` the `leaf_for_atom` digest of an Element atom (`hash (atomLeafPreimage aᵢ)`),
agree on that atom's Element STRUCTURE: equal tag, equal attrs, equal children — not merely equal
opaque leaf bytes. Without this, the deployed commit binds bytes; WITH it, it binds the DOM structure
the author authored.

The composition, each step reused not re-invented:
  * `root_binds_get` (Heap.lean, PROVEN) — equal substrate root ⟹ the leaf VALUE at `(COLL_ATOMS,
    key)` agrees: `hash (atomLeafPreimage a₁) = hash (atomLeafPreimage a₂)`;
  * `hCR` (the SAME `Poseidon2SpongeCR` carrier) — equal digest ⟹ equal preimage;
  * `atomLeafPreimage_injective` — equal preimage ⟹ equal atom;
  * `encodeElement_injective` — folded into the atom equality (the Element field), giving the
    structural conclusion.
No new commitment scheme: the SOLE crypto step is `root_binds_get`'s carrier, cited. -/
theorem substrate_root_binds_element_structure
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (key : ℤ) (a₁ a₂ : AtomModel)
    (hv₁ : hget hash h₁ COLL_ATOMS key = some (hash (atomLeafPreimage a₁)))
    (hv₂ : hget hash h₂ COLL_ATOMS key = some (hash (atomLeafPreimage a₂)))
    (hroot : root hash h₁ = root hash h₂) :
    a₁.elem.tag = a₂.elem.tag ∧ a₁.elem.attrs = a₂.elem.attrs
      ∧ a₁.elem.children = a₂.elem.children := by
  have hbind := root_binds_get hash hCR hroot COLL_ATOMS key
  rw [hv₁, hv₂] at hbind
  have hpre : atomLeafPreimage a₁ = atomLeafPreimage a₂ := hCR _ _ (Option.some.inj hbind)
  have ha : a₁ = a₂ := atomLeafPreimage_injective hpre
  exact ⟨by rw [ha], by rw [ha], by rw [ha]⟩

#assert_axioms substrate_root_binds_element_structure

/-! ## 3. Conflict-as-state soundness on the deployed commit (`substrate.rs::leaf_for_field`).

A conflict is two field assignments at the same name — two `COLL_FIELDS` leaves. Each leaf binds
`name ‖ value ‖ provenance` (`leaf_for_field`). We model that preimage and prove: equal substrate
root ⟹ both alternatives agree (value AND provenance). This is the recovered
`docCommit_conflict_binds_both`, but ABOUT `substrate_commit`. -/

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

/-- **`substrate_root_binds_conflict_alternatives` — conflict-as-state soundness on the DEPLOYED
commit.**

Two documents committed to the SAME `substrate_commit`, each storing a two-alternative conflict as
the `COLL_FIELDS` leaves at keys `keyA`, `keyB` (`hash (fieldLeafPreimage …)`), agree on BOTH
alternatives — name, value AND provenance. So a substituted/forged alternative (even one that renders
identically but is authored by someone else) CANNOT hide under an equal deployed root: it would move
some `COLL_FIELDS` leaf, refused by collision-resistance.

A THIN composition on the already-proven heavy lifting: `root_binds_get` pins each field leaf VALUE;
the SAME `Poseidon2SpongeCR` carrier peels the digest; `fieldLeafPreimage_injective` reads off the
alternative. No new commitment scheme. -/
theorem substrate_root_binds_conflict_alternatives
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (keyA keyB : ℤ) (altA altB altA' altB' : FieldAssignModel)
    (hA₁ : hget hash h₁ COLL_FIELDS keyA = some (hash (fieldLeafPreimage altA)))
    (hB₁ : hget hash h₁ COLL_FIELDS keyB = some (hash (fieldLeafPreimage altB)))
    (hA₂ : hget hash h₂ COLL_FIELDS keyA = some (hash (fieldLeafPreimage altA')))
    (hB₂ : hget hash h₂ COLL_FIELDS keyB = some (hash (fieldLeafPreimage altB')))
    (hroot : root hash h₁ = root hash h₂) :
    altA = altA' ∧ altB = altB' := by
  have hbindA := root_binds_get hash hCR hroot COLL_FIELDS keyA
  have hbindB := root_binds_get hash hCR hroot COLL_FIELDS keyB
  rw [hA₁, hA₂] at hbindA
  rw [hB₁, hB₂] at hbindB
  exact ⟨fieldLeafPreimage_injective (hCR _ _ (Option.some.inj hbindA)),
         fieldLeafPreimage_injective (hCR _ _ (Option.some.inj hbindB))⟩

#assert_axioms fieldLeafPreimage_injective
#assert_axioms substrate_root_binds_conflict_alternatives

/-! ## 4. NON-VACUITY — a forged Element and a forged conflict alternative each MOVE the deployed root.

Witnesses over the computable reference sponge `Dregg2.Substrate.Heap.refSponge` (the same Horner-tag
toy the Heap non-vacuity guards use). Each leaf VALUE is `refSponge preimage` — the model's digest —
stored at its canonical `(collection_id, key)`; the root is `Heap.root refSponge`. A tampered Element
or a forged conflict author provably MOVES that root: the binding theorems above are non-vacuous. -/

/-- Store one atom at `(COLL_ATOMS, 0)`, its leaf value the digest of its preimage. -/
def demoAtomHeap (a : AtomModel) : FeltHeap :=
  hset refSponge [] COLL_ATOMS 0 (refSponge (atomLeafPreimage a))
/-- Store one field alternative at `(COLL_FIELDS, 0)`. -/
def demoFieldHeap (f : FieldAssignModel) : FeltHeap :=
  hset refSponge [] COLL_FIELDS 0 (refSponge (fieldLeafPreimage f))

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

-- **Witness FALSE (anti-forge):** each Element forgery MOVES the deployed (substrate) root — the
-- published `heap_root` cannot be kept while retagging, adding an attr, or adding a child:
#guard root refSponge (demoAtomHeap atomForgedTag) != root refSponge (demoAtomHeap atomHonest)
#guard root refSponge (demoAtomHeap atomForgedAttr) != root refSponge (demoAtomHeap atomHonest)
#guard root refSponge (demoAtomHeap atomForgedChild) != root refSponge (demoAtomHeap atomHonest)

-- A genuine conflict alternative and a FORGED one: SAME name+value, FORGED author (13 ≠ 9).
def altHonest : FieldAssignModel := ⟨[116], [66], 9, 200⟩        -- name "t", value "B", author 9
def altForged : FieldAssignModel := ⟨[116], [66], 13, 200⟩       -- same value, author FORGED to 13

-- The forge is real (renders identically — same value bytes — but the author differs):
#guard altHonest.value == altForged.value
#guard decide (altHonest ≠ altForged)
#guard fieldLeafPreimage altHonest != fieldLeafPreimage altForged
-- **Witness FALSE (anti-forge):** the forged author MOVES the deployed root — a conflict cannot hide
-- a forged alternative under an equal `substrate_commit`:
#guard root refSponge (demoFieldHeap altForged) != root refSponge (demoFieldHeap altHonest)

end Dregg2.Deos.DocSubstrateSound
