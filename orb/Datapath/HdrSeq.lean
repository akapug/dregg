import Datapath.FlatHeaders

/-!
# Datapath.HdrSeq — the HEADER-GRAIN sibling of `Datapath.ByteSeq`

`Datapath.ByteSeq` is a typeclass of the byte-sequence ops a body/serialize stage
needs, with each op's denotation law proven ONCE per instance, so a stage written
once over `[ByteSeq T]` instantiates at `List UInt8` (the spec) and `ByteArray`
(the fast, genuinely-flat path) and its whole refinement FOLLOWS from the op laws.
The serve, though, crosses TWO grains: the response *body* (a byte sequence, done
by `ByteSeq`) and the response *header block*
(`Reactor.Response.headers : List (Proto.Bytes × Proto.Bytes)` — a header-PAIR
sequence). This module is the header-pair-grain instance of the SAME idea.

`HdrSeq H` carries the header-list ops a real header-transform stage uses —
`empty`, `push` (append one `(name, value)` pair), `append`, `filter` (keep the
pairs a predicate admits — the strip/remove primitive) — plus the denotation
`toHdrs : H → List (Bytes × Bytes)` (the abstraction relation to the deployed
`List`-typed header block) and the LAWS relating each op to its `List` meaning.
The laws are the op-level refinements (`empty_denote`, `push_denote`,
`append_denote`, `filter_denote`); proven once per instance, a header stage's
whole refinement is discharged from them.

Two instances:

* `instHdrSeqList : HdrSeq (List (Bytes × Bytes))` — the **spec**: `toHdrs := id`,
  every op the `List` op, every law `rfl`. A stage here *is* the deployed
  `List`-typed stage.
* `instHdrSeqBlock : HdrSeq HdrBlock` — the **fast, genuinely flat** path, reusing
  `Datapath.FlatHeaders.HdrBlock` (the header spine in a contiguous
  `Array (Bytes × Bytes)`): `push := Array.push` (amortized `O(1)`, no per-stage
  spine copy), `append := Array.append`, `filter := Array.filter` (a packed copy,
  NO cons-spine), `toHdrs := Array.toList` (the denotation, never run on the
  datapath). Each law is proven once from the core `Array` lemmas.

The single generic recursion lemma `foldPush_denote` (the header-grain sibling of
`ByteSeq.foldCat_denote`) pays the one induction a fixed-header-set fold needs, for
EVERY instance at once; every fixed-set header stage reuses it with no further
induction.
-/

namespace Datapath.HdrSeq

open Proto (Bytes)
open Datapath.FlatHeaders (HdrBlock)

/-- **The header-sequence typeclass.** The ops a real header-transform stage needs,
plus the denotation `toHdrs` (the abstraction relation to the deployed
`List (Bytes × Bytes)` header block) and the LAWS relating each op to its spec
meaning. Instances prove the laws ONCE; a stage over `[HdrSeq H]` gets its whole
refinement from them. -/
class HdrSeq (H : Type) where
  /-- The empty header block. -/
  empty : H
  /-- Push one `(name, value)` header pair onto the end (amortised on the flat
  instance). -/
  push : H → (Bytes × Bytes) → H
  /-- Concatenate two header blocks. -/
  append : H → H → H
  /-- Keep exactly the header pairs a predicate admits — the strip/remove
  primitive (a `filter`; the flat instance is a packed `Array.filter`, no cons). -/
  filter : H → ((Bytes × Bytes) → Bool) → H
  /-- **The denotation** — the abstract `List (Bytes × Bytes)` header block this
  value stands for. Never computed on the running datapath; it is the spec
  relation. -/
  toHdrs : H → List (Bytes × Bytes)
  /-- Law: the empty block denotes the empty header list. -/
  empty_denote : toHdrs empty = []
  /-- Law: push denotes appending the one-element list (the `addHeader`
  refinement). -/
  push_denote : ∀ h nv, toHdrs (push h nv) = toHdrs h ++ [nv]
  /-- Law: append denotes list concatenation. -/
  append_denote : ∀ a b, toHdrs (append a b) = toHdrs a ++ toHdrs b
  /-- Law: filter denotes `List.filter` on the denotation (the strip/remove
  refinement). -/
  filter_denote : ∀ h p, toHdrs (filter h p) = (toHdrs h).filter p

attribute [simp] HdrSeq.empty_denote HdrSeq.push_denote HdrSeq.append_denote
  HdrSeq.filter_denote

/-! ## The spec instance — `List (Bytes × Bytes)`, `toHdrs := id` -/

/-- **The spec instance.** Every op is the `List` op; `toHdrs` is the identity. A
stage instantiated here *is* the deployed `List`-typed header stage — no separate
"spec expression" is written. Every law is `rfl`. -/
instance instHdrSeqList : HdrSeq (List (Bytes × Bytes)) where
  empty := []
  push := fun h nv => h ++ [nv]
  append := (· ++ ·)
  filter := fun h p => h.filter p
  toHdrs := id
  empty_denote := rfl
  push_denote := fun _ _ => rfl
  append_denote := fun _ _ => rfl
  filter_denote := fun _ _ => rfl

/-! ## The fast instance — `HdrBlock`, genuinely flat -/

/-- **The fast instance — genuinely flat.** Reuses `Datapath.FlatHeaders.HdrBlock`
(the header spine in a contiguous `Array (Bytes × Bytes)`). `push` is
`Array.push` (amortised `O(1)`, no per-stage spine copy), `append` is
`Array.append`, `filter` is `Array.filter` (a packed copy, NO cons-spine).
`toHdrs` is `Array.toList` — the DENOTATION only, never run on the datapath. Each
law is proven once from the core `Array` lemmas. -/
instance instHdrSeqBlock : HdrSeq HdrBlock where
  empty := ⟨#[]⟩
  push := fun h nv => ⟨h.headers.push nv⟩
  append := fun a b => ⟨a.headers ++ b.headers⟩
  filter := fun h p => ⟨h.headers.filter p⟩
  toHdrs := HdrBlock.denote
  empty_denote := rfl
  push_denote := fun h nv => by
    show (h.headers.push nv).toList = h.headers.toList ++ [nv]
    rw [Array.push_toList]
  append_denote := fun a b => by
    show (a.headers ++ b.headers).toList = a.headers.toList ++ b.headers.toList
    rw [Array.toList_append]
  filter_denote := fun h p => by
    show (h.headers.filter p).toList = h.headers.toList.filter p
    rw [Array.toList_filter]

/-! ## The ONE generic recursion lemma — reused by every fixed-header-set stage

A header stage that stamps a fixed header set (`securityheaders`, the cors
allow branch, …) folds `push` over that `List (Bytes × Bytes)` set. `foldPush` is
that combinator, and `foldPush_denote` proves its denotation ONCE, by induction,
over an ABSTRACT `[HdrSeq H]` — using only `push_denote`. Every fixed-set header
stage reuses it with NO further induction: this is the single place induction is
paid for the whole family (the header-grain sibling of `ByteSeq.foldCat_denote`). -/

/-- Fold `push` over a fixed header set into an accumulator — polymorphic over the
header representation. -/
def foldPush {H : Type} [HdrSeq H] (xs : List (Bytes × Bytes)) (h : H) : H :=
  xs.foldl HdrSeq.push h

/-- **THE generic recursion lemma.** Folding a fixed header set `xs` onto any
`[HdrSeq H]` accumulator denotes to the `List` append `toHdrs h ++ xs`. Proven
ONCE, generic in `H`, from `push_denote` alone. Every fixed-set header stage's
refinement reuses this; no stage re-does the induction. -/
@[simp] theorem foldPush_denote {H : Type} [HdrSeq H] (xs : List (Bytes × Bytes)) :
    ∀ h : H, HdrSeq.toHdrs (foldPush xs h) = HdrSeq.toHdrs h ++ xs := by
  induction xs with
  | nil => intro h; simp [foldPush]
  | cons nv rest ih =>
    intro h
    rw [foldPush, List.foldl_cons, ← foldPush, ih (HdrSeq.push h nv), HdrSeq.push_denote]
    simp [List.append_assoc]

/-- At the spec instance `toHdrs = id`, so `foldPush` on a `List` header set is
exactly `h ++ xs` — the spec-side normal form the grounding lemmas use. -/
@[simp] theorem foldPush_list (xs h : List (Bytes × Bytes)) :
    foldPush (H := List (Bytes × Bytes)) xs h = h ++ xs := by
  have := foldPush_denote (H := List (Bytes × Bytes)) xs h
  simpa [HdrSeq.toHdrs, instHdrSeqList] using this

end Datapath.HdrSeq
