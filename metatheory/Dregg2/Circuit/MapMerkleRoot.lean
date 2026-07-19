/-
# Dregg2.Circuit.MapMerkleRoot — the DEPLOYED depth-16 binary-Merkle map root (the faithful map-op commitment).

## What this closes (deliverable 2 — the last real denotation gap)

`DescriptorIR2.opensTo`/`writesTo` (the `MapOp.holdsAt` legs for nullifiers / cells / commitments)
denoted a FLAT SPONGE `Dregg2.Substrate.Heap.root hash h = hash (h.map leafOf)` — a single sponge over
the sorted leaf list. The DEPLOYED map-op (`circuit/src/heap_root.rs`, `circuit/src/descriptor_ir2.rs`
`Ir2Air::MapOps`) commits a **depth-`d` BINARY MERKLE** root instead:

    leaf = hash[addr, value]                       -- ⚠ the PRE-IMT leaf (see below)
    node = hash[left, right]                       -- arity-2 `hash_fact(l, [r])` (the `mix` fold)
    root = the perfect binary fold of the (padded) sorted leaf-digest list, depth `HEAP_TREE_DEPTH = 16`

⚠ ARITY NOTE (gap-#5 IMT, 2026-07): the DEPLOYED `HeapLeaf::digest`/`digest8` is now the LINKED
arity-3 `hash[addr, value, next_addr]` (`IndexedMerkleTree.imtLeafHash`). The FAITHFUL 8-felt §5b
section below models exactly that (`linkHeap` + the arity-3 `heapLeafDigest8`). The SCALAR §2-§5
model in THIS section still folds the historical arity-2 `leafOf` — it is the lane-0/1-felt
DENOTATION layer (`DescriptorIR2.opensTo`/`writesTo`), a NAMED residue of the IMT cutover: its
`writesTo` describes the pre-IMT leaf function, pending the denotation rewire onto `ImtLeaf`.

This module models EXACTLY that binary fold (`mapNode`/`foldLevel`/`perfectRoot`) and proves it
INJECTIVE on the padded leaf-digest vector under the single named Poseidon2-CR floor
(`mapNode_injective` — the `hash[l,r]` 2-to-1 node CR — composed up the depth-`d` perfect tree by
`perfectRoot_injective`). `DescriptorIR2` re-defines `opensTo`/`writesTo` over THIS root (dropping the
flat-sponge `Heap.root`), so `MapOp.holdsAt` — a leg of the deployed `Satisfied2` — denotes the genuine
depth-16 binary-Merkle opening, and the anti-ghost `opensTo_functional`/`writesTo_functional` re-prove
against `perfectRoot_injective` (the binary-tree analog of `Heap.root_injective`), NOT the sponge.

## The model (faithful to `heap_root.rs`)

The deployed `CanonicalHeapTree` pads the sorted leaf list to `2^d` positions with the MIN/MAX
sentinels, then folds bottom-up by `hash_fact(l, [r])`. We model the COMMITMENT of a sorted heap as
`mapRoot hash h := perfectRoot hash d (padDigests d (h.map (leafOf hash)))`: the leaf digests of the
sorted entries, padded to `2^d` with a fixed sentinel digest, folded up the perfect tree. The sorted
discipline (`SortedKeys`) keeps the entry list canonical, so the heap MEANING (`Heap.get`) is unchanged
— only the COMMITMENT FUNCTION moves from the flat sponge to the binary fold. The named CR floor is the
SAME `Poseidon2SpongeCR`, now used at the 2-to-1 node (`mapNode`) and the leaf (`leafOf`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Crypto
enters ONLY as the named `Poseidon2SpongeCR` floor (at the node + leaf), the SAME floor the whole
commitment tower carries. NEW file; imports read-only.
-/
import Dregg2.Substrate.Heap
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.DeployedHeapTree

namespace Dregg2.Circuit.MapMerkleRoot

open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)

set_option autoImplicit false

/-- The deployed map-tree depth (`heap_root.rs::HEAP_TREE_DEPTH = 16`). The model is generic in `d`;
the deployment instance pins `d = 16`. -/
def HEAP_TREE_DEPTH : Nat := 16

/-! ## §1 — the 2-to-1 binary node (`hash[left, right]`, arity-2 — the deployed `hash_fact(l,[r])`). -/

/-- **`mapNode hash l r`** — the internal node digest, the arity-2 hash over `[left, right]`.
BYTE-IDENTICAL to `heap_root.rs`'s `hash_fact(cur, &[sib])` / `hash_fact(sib, &[cur])` fold node (a
length-2 absorb, NO domain marker — distinct from the cap node's `[FACT_MARK, l, r]`). -/
def mapNode (hash : List ℤ → ℤ) (l r : ℤ) : ℤ := hash [l, r]

/-- The 2-to-1 node is injective in its two children under CR: equal node images force equal
`[l, r]` lists, hence equal children. The per-level peel of the fold's anti-ghost. -/
theorem mapNode_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l₁ r₁ l₂ r₂ : ℤ} (h : mapNode hash l₁ r₁ = mapNode hash l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hlist := hCR _ _ h
  simp only [List.cons.injEq, and_true] at hlist
  exact ⟨hlist.1, hlist.2⟩

/-! ## §2 — the perfect-tree fold (a level pairs adjacent digests; `perfectRoot` folds `d` levels). -/

/-- **`foldLevel hash xs`** — one Merkle level: pair adjacent digests by `mapNode`. On a list of even
length `2n` this returns the `n` parent digests, matching `heap_root.rs`'s `chunks(2)` step. -/
def foldLevel (hash : List ℤ → ℤ) : List ℤ → List ℤ
  | [] => []
  | [x] => [x]                                   -- (unreached at even lengths; carry the orphan)
  | l :: r :: rest => mapNode hash l r :: foldLevel hash rest

/-- **`perfectRoot hash d xs`** — fold `d` levels and take the head: the perfect binary-tree root of
the `2^d` leaf digests `xs`. At `d = 0` the root is the single leaf (`xs.headD 0`). -/
def perfectRoot (hash : List ℤ → ℤ) : Nat → List ℤ → ℤ
  | 0,     xs => xs.headD 0
  | d + 1, xs => perfectRoot hash d (foldLevel hash xs)

/-! ## §3 — injectivity of one level, then of the whole fold (the binary `root_injective` analog). -/

/-- One fold level HALVES an even-length list: `(foldLevel hash xs).length = n` when
`xs.length = 2 * n`, matching `heap_root.rs`'s `chunks(2)` step. Inducts on the half-length `n`. -/
theorem foldLevel_length_half (hash : List ℤ → ℤ) :
    ∀ (n : Nat) (xs : List ℤ), xs.length = 2 * n → (foldLevel hash xs).length = n := by
  intro n
  induction n with
  | zero =>
    intro xs hn
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [foldLevel]
  | succ m ih =>
    intro xs hn
    match xs, hn with
    | l :: r :: rest, hn =>
      simp only [List.length_cons] at hn
      have hrest : rest.length = 2 * m := by omega
      simp only [foldLevel, List.length_cons, ih rest hrest]

/-- `foldLevel` is injective on lists of equal length `2*n` under the node CR: peel each pair by
`mapNode_injective`. (Lists that arise in `perfectRoot` always have length `2^d`, hence even at every
level above the leaves.) Inducts on the half-length `n`. -/
theorem foldLevel_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (n : Nat) {xs ys : List ℤ}, xs.length = 2 * n → ys.length = 2 * n →
      foldLevel hash xs = foldLevel hash ys → xs = ys := by
  intro n
  induction n with
  | zero =>
    intro xs ys hx hy _
    have hxe : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hye : ys = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hxe, hye]
  | succ m ih =>
    intro xs ys hx hy hfold
    match xs, hx, ys, hy with
    | l :: r :: rest, hx, l' :: r' :: rest', hy =>
      simp only [foldLevel, List.cons.injEq] at hfold
      obtain ⟨hnode, hrest⟩ := hfold
      obtain ⟨hl, hr⟩ := mapNode_injective hash hCR hnode
      simp only [List.length_cons] at hx hy
      have hxlen : rest.length = 2 * m := by omega
      have hylen : rest'.length = 2 * m := by omega
      have := ih hxlen hylen hrest
      rw [hl, hr, this]

/-- **`perfectRoot_injective` — the binary-Merkle root BINDS the whole leaf-digest vector.** Two
length-`2^d` leaf-digest lists with EQUAL perfect-tree roots are EQUAL, under the single named CR floor
— peel each of the `d` levels by `foldLevel_injective`. The binary-tree analog of the flat sponge's
`Heap.root_injective`: a prover cannot keep the published map root while tampering ANY leaf digest. -/
theorem perfectRoot_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (d : Nat) {xs ys : List ℤ}, xs.length = 2 ^ d → ys.length = 2 ^ d →
      perfectRoot hash d xs = perfectRoot hash d ys → xs = ys := by
  intro d
  induction d with
  | zero =>
    intro xs ys hx hy hroot
    -- length `2^0 = 1`: both are singletons, `perfectRoot 0 = headD`.
    rw [pow_zero] at hx hy
    match xs, ys, hx, hy with
    | [x], [y], _, _ =>
      simp only [perfectRoot, List.headD_cons] at hroot
      rw [hroot]
  | succ d ih =>
    intro xs ys hx hy hroot
    simp only [perfectRoot] at hroot
    -- both `xs`, `ys` have length `2^(d+1) = 2 * 2^d`; one level halves to length `2^d`.
    have hxlen : xs.length = 2 ^ d + 2 ^ d := by rw [hx]; ring
    have hylen : ys.length = 2 ^ d + 2 ^ d := by rw [hy]; ring
    have hfl_x : (foldLevel hash xs).length = 2 ^ d := foldLevel_length_half hash (2 ^ d) xs (by omega)
    have hfl_y : (foldLevel hash ys).length = 2 ^ d := foldLevel_length_half hash (2 ^ d) ys (by omega)
    have hfold := ih hfl_x hfl_y hroot
    exact foldLevel_injective hash hCR (2 ^ d) (by omega) (by omega) hfold

/-! ## §4 — `mapRoot`: the deployed map COMMITMENT (the binary fold of the sorted heap's leaf digests).

The sorted heap (`Heap.FeltHeap`, the abstract map MEANING) is committed by folding its leaf-digest list
through the depth-`d` perfect binary tree — the deployed `CanonicalHeapTree::root`. The heap MEANING
(`Heap.get`/`Heap.SortedKeys`) is UNCHANGED; only the COMMITMENT FUNCTION moves from the flat sponge
(`Heap.root hash h = hash (h.map leafOf)`) to this binary fold. The deployment pins every heap as the
fixed-depth `2^d`-leaf padded vector; the `RootedAt` relation below carries that `length = 2^d`
discipline so the root BINDS the heap (`mapRoot_injective`). -/

/-- **`mapRoot hash d h`** — the depth-`d` binary-Merkle root of the sorted heap `h`: the perfect-tree
fold of its leaf-digest list `h.map (Heap.leafOf hash)`. BYTE-IDENTICAL to `heap_root.rs`'s
`CanonicalHeapTree::root` (arity-2 `leafOf` leaves, arity-2 `mapNode` nodes, depth `d`). -/
def mapRoot (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) : ℤ :=
  perfectRoot hash d (h.map (Heap.leafOf hash))

/-- **`mapRoot_injective` — the binary-Merkle map root BINDS the whole heap (the anti-ghost), re-proved
against `perfectRoot_injective` (the NODE injectivity `mapNode_injective` composed up the tree), NOT the
flat-sponge `Heap.root_injective`.** Two depth-`d` `2^d`-leaf heaps publishing the same binary root are
EQUAL: the root injectivity peels the `d` node levels (`perfectRoot_injective`) to equal leaf-digest
lists, then the leaf CR (`Heap.map_leaf_injective`) peels each leaf to equal entries. A prover cannot keep
the published map root while tampering ANY address or value. -/
theorem mapRoot_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : Nat)
    {h₁ h₂ : Heap.FeltHeap} (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRoot hash d h₁ = mapRoot hash d h₂) : h₁ = h₂ := by
  have hmap : (h₁.map (Heap.leafOf hash)) = (h₂.map (Heap.leafOf hash)) :=
    perfectRoot_injective hash hCR d (by rw [List.length_map, hlen₁])
      (by rw [List.length_map, hlen₂]) h
  exact Heap.map_leaf_injective hash hCR h₁ h₂ hmap

/-! ## §5 — the faithful map OPENING (`opensToMerkle`/`writesToMerkle`) + the re-proved anti-ghost.

The binary-Merkle replacement for `DescriptorIR2.opensTo`/`writesTo`: a depth-`d` `2^d`-leaf sorted heap
behind the binary root reads / writes the abstract map. The `_functional` anti-ghost re-proves against
`mapRoot_injective` (hence `perfectRoot_injective`/`mapNode_injective`), NOT the sponge `root_injective` —
the deliverable-2 functional tooth over the deployed binary tree. -/

/-- **`opensToMerkle hash d r k o`** — some depth-`d` `2^d`-leaf sorted heap behind the BINARY-MERKLE
root `r` reads `o` at `k`. The faithful replacement of `DescriptorIR2.opensTo` over the deployed tree. -/
def opensToMerkle (hash : List ℤ → ℤ) (d : Nat) (r k : ℤ) (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d ∧ mapRoot hash d h = r ∧ Heap.get h k = o

/-- **`writesToMerkle hash d r k v r'`** — some depth-`d` `2^d`-leaf sorted heap behind binary root `r`
produces root `r'` under the sorted insert-or-update of `(k, v)`, with the post-heap still `2^d`-leaf. -/
def writesToMerkle (hash : List ℤ → ℤ) (d : Nat) (r k v r' : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d
    ∧ (Heap.set h k v).length = 2 ^ d
    ∧ mapRoot hash d h = r ∧ r' = mapRoot hash d (Heap.set h k v)

/-- **Binary-Merkle openings are FUNCTIONAL (the anti-ghost over the deployed tree).** Under CR, the
binary root + key determine the read: two openings of the same root at the same key agree. Re-proved
against `mapRoot_injective` (the binary fold), NOT the flat-sponge `Heap.root_injective`. -/
theorem opensToMerkle_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : Nat)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle hash d r k o₁) (h₂ : opensToMerkle hash d r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, _, hl₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, hr₂, hg₂⟩ := h₂
  have hm : m₁ = m₂ := mapRoot_injective hash hCR d hl₁ hl₂ (hr₁.trans hr₂.symm)
  rw [← hg₁, ← hg₂, hm]

/-- Membership and non-membership at the same binary root/key EXCLUDE each other (the nullifier / cap
non-membership tooth, over the deployed tree). -/
theorem opensToMerkle_some_excludes_none (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : Nat)
    {r k v : ℤ} (h₁ : opensToMerkle hash d r k (some v)) (h₂ : opensToMerkle hash d r k none) : False := by
  have := opensToMerkle_functional hash hCR d h₁ h₂
  simp at this

/-- **Binary-Merkle writes are FUNCTIONAL.** Under CR, binary root + key + value determine the new root:
the map-op row's `new_root` column cannot be forged. Re-proved against `mapRoot_injective`. -/
theorem writesToMerkle_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : Nat)
    {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkle hash d r k v r₁) (h₂ : writesToMerkle hash d r k v r₂) : r₁ = r₂ := by
  obtain ⟨m₁, _, hl₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, _, hr₂, he₂⟩ := h₂
  have hm : m₁ = m₂ := mapRoot_injective hash hCR d hl₁ hl₂ (hr₁.trans hr₂.symm)
  rw [he₁, he₂, hm]

/-! ## §5b — THE FAITHFUL 8-felt map denotation (Phase H-HEAP-8): the perfect-tree fold + opening over
`node8` (`Digest8`), the exact twin of §2–§5 but at the deployed ~124-bit width. The historical §2–§5
folded a SINGLE felt per node (`mapNode hash : ℤ → ℤ → ℤ`, ~2^31, below the FRI/STARK ~124-bit floor); the
GENTIAN tooth exhibits a colliding-lane-0 heap pair. This section commits the FULL 8-felt root: nodes ride
`Heap8Scheme.heapNodeOf8` (arity-16 `node8` chip), leaves `heapLeafDigest8`, and the anti-ghost re-proves
against `heapNodeOf8_injective` / `heapLeafDigest8_injective` (`DeployedHeapTree`), NOT the 1-felt sponge.
`MapOp.holdsAt`'s deployed denotation moves onto `opensToMerkle8` / `writesToMerkle8`. -/

section Faithful8
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (heapLeafDigest8 heapNodeOf8 heapLeafDigest8_injective
  heapNodeOf8_injective)

variable (S8 : Heap8Scheme)

/-- The all-zero `Digest8` (off-the-end default for `headD`; never semantically load-bearing on a
length-`2^d` vector). -/
def zeroDigest8 : Digest8 := fun _ => 0

/-- **`foldLevel8 S8 xs`** — one 8-felt Merkle level: pair adjacent `Digest8`s by `heapNodeOf8`. The
`node8` twin of `foldLevel`. -/
def foldLevel8 : List Digest8 → List Digest8
  | [] => []
  | [x] => [x]
  | l :: r :: rest => heapNodeOf8 S8 l r :: foldLevel8 rest

/-- **`perfectRoot8 S8 d xs`** — fold `d` 8-felt levels and take the head: the perfect binary-tree
`node8` root of the `2^d` leaf digests. At `d = 0` the root is the single leaf. -/
def perfectRoot8 : Nat → List Digest8 → Digest8
  | 0,     xs => xs.headD (zeroDigest8)
  | d + 1, xs => perfectRoot8 d (foldLevel8 S8 xs)

/-- One 8-felt fold level HALVES an even-length list (the `node8` twin of `foldLevel_length_half`). -/
theorem foldLevel8_length_half :
    ∀ (n : Nat) (xs : List Digest8), xs.length = 2 * n → (foldLevel8 S8 xs).length = n := by
  intro n
  induction n with
  | zero =>
    intro xs hn
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [foldLevel8]
  | succ m ih =>
    intro xs hn
    match xs, hn with
    | l :: r :: rest, hn =>
      simp only [List.length_cons] at hn
      have hrest : rest.length = 2 * m := by omega
      simp only [foldLevel8, List.length_cons, ih rest hrest]

/-- `foldLevel8` is injective on lists of equal length `2*n` under the `node8` injectivity (the `node8`
twin of `foldLevel_injective`; peels each pair by `heapNodeOf8_injective`). -/
theorem foldLevel8_injective :
    ∀ (n : Nat) {xs ys : List Digest8}, xs.length = 2 * n → ys.length = 2 * n →
      foldLevel8 S8 xs = foldLevel8 S8 ys → xs = ys := by
  intro n
  induction n with
  | zero =>
    intro xs ys hx hy _
    have hxe : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hye : ys = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hxe, hye]
  | succ m ih =>
    intro xs ys hx hy hfold
    match xs, hx, ys, hy with
    | l :: r :: rest, hx, l' :: r' :: rest', hy =>
      simp only [foldLevel8, List.cons.injEq] at hfold
      obtain ⟨hnode, hrest⟩ := hfold
      obtain ⟨hl, hr⟩ := heapNodeOf8_injective S8 hnode
      simp only [List.length_cons] at hx hy
      have hxlen : rest.length = 2 * m := by omega
      have hylen : rest'.length = 2 * m := by omega
      have := ih hxlen hylen hrest
      rw [hl, hr, this]

/-- **`perfectRoot8_injective` — the 8-felt binary-Merkle root BINDS the whole leaf-digest vector.**
Two length-`2^d` `Digest8` lists with EQUAL `node8` roots are EQUAL, under `heapNodeOf8_injective` — the
`node8` twin of `perfectRoot_injective`, at ~124-bit width. -/
theorem perfectRoot8_injective :
    ∀ (d : Nat) {xs ys : List Digest8}, xs.length = 2 ^ d → ys.length = 2 ^ d →
      perfectRoot8 S8 d xs = perfectRoot8 S8 d ys → xs = ys := by
  intro d
  induction d with
  | zero =>
    intro xs ys hx hy hroot
    rw [pow_zero] at hx hy
    match xs, ys, hx, hy with
    | [x], [y], _, _ =>
      simp only [perfectRoot8, List.headD_cons] at hroot
      rw [hroot]
  | succ d ih =>
    intro xs ys hx hy hroot
    simp only [perfectRoot8] at hroot
    have hfl_x : (foldLevel8 S8 xs).length = 2 ^ d := foldLevel8_length_half S8 (2 ^ d) xs (by omega)
    have hfl_y : (foldLevel8 S8 ys).length = 2 ^ d := foldLevel8_length_half S8 (2 ^ d) ys (by omega)
    have hfold := ih hfl_x hfl_y hroot
    exact foldLevel8_injective S8 (2 ^ d) (by omega) (by omega) hfold

/-- The `heapLeafDigest8` map is INJECTIVE on LINKED leaf lists (the `node8` twin of
`Heap.map_leaf_injective`): distinct linked entry lists yield distinct 8-felt leaf-digest lists, by
`heapLeafDigest8_injective` (the arity-3 IMT digest binds addr, value, AND pointer). -/
theorem map_leaf8_injective :
    ∀ (l₁ l₂ : List (ℤ × ℤ × ℤ)),
      l₁.map (heapLeafDigest8 S8) = l₂.map (heapLeafDigest8 S8) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ with
    | nil => rfl
    | cons hd t => simp at h
  | cons hd₁ t₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp at h
    | cons hd₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hleaf, htail⟩ := h
      rw [heapLeafDigest8_injective S8 hleaf, ih t₂ htail]

/-- The deployed TERMINAL pointer (`circuit/src/dsl/revocation.rs::SENTINEL_MAX = p − 1 =
2013265920`): the largest linked leaf points at it (the sorted chain's end). -/
def SENTINEL_MAX8 : ℤ := 2013265920

/-- **`linkHeap h`** — the gap-#5 IMT LINKING of a sorted pair-heap: each `(addr, value)` entry gains
the POINTER to its successor's `addr` (the last leaf → `SENTINEL_MAX8`). The model twin of
`heap_root.rs::relink_next_addrs` — the deployed commitment hashes LINKED `(addr, value, next)`
leaves (`HeapLeaf::digest8`, arity 3), while the map MEANING (`Heap.get`/`Heap.set`) stays the pair
list. -/
def linkHeap : Heap.FeltHeap → List (ℤ × ℤ × ℤ)
  | [] => []
  | (a, v) :: rest => (a, v, (rest.head?.map Prod.fst).getD SENTINEL_MAX8) :: linkHeap rest

/-- Dropping the pointers recovers the pair-heap: `linkHeap` loses nothing. -/
theorem linkHeap_unlink : ∀ h : Heap.FeltHeap,
    (linkHeap h).map (fun t => (t.1, t.2.1)) = h := by
  intro h
  induction h with
  | nil => rfl
  | cons hd rest ih => cases hd with
    | mk a v => simp only [linkHeap, List.map_cons, ih]

/-- `linkHeap` is INJECTIVE (unlink is a retraction). -/
theorem linkHeap_injective {h₁ h₂ : Heap.FeltHeap} (h : linkHeap h₁ = linkHeap h₂) : h₁ = h₂ := by
  have := congrArg (List.map (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1))) h
  rwa [linkHeap_unlink, linkHeap_unlink] at this

/-- `linkHeap` preserves length. -/
theorem linkHeap_length : ∀ h : Heap.FeltHeap, (linkHeap h).length = h.length := by
  intro h
  induction h with
  | nil => rfl
  | cons hd rest ih => cases hd with
    | mk a v => simp only [linkHeap, List.length_cons, ih]

/-- **`mapRoot8 S8 d h`** — the depth-`d` 8-felt binary-Merkle root of the sorted heap `h`: LINK the
pointers (`linkHeap` — `relink_next_addrs`), digest each linked leaf (arity-3 `heapLeafDigest8` —
`HeapLeaf::digest8`), fold the perfect `node8` tree. BYTE-IDENTICAL to `heap_root.rs`'s
`CanonicalHeapTree8::root` over the padded sorted vector. -/
def mapRoot8 (d : Nat) (h : Heap.FeltHeap) : Digest8 :=
  perfectRoot8 S8 d ((linkHeap h).map (heapLeafDigest8 S8))

/-- **`mapRoot8_injective` — the 8-felt root BINDS the whole heap.** Two depth-`d` `2^d`-leaf heaps
publishing the same 8-felt root are EQUAL, re-proved against `perfectRoot8_injective` / `heapNodeOf8`,
NOT the 1-felt sponge. -/
theorem mapRoot8_injective (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRoot8 S8 d h₁ = mapRoot8 S8 d h₂) : h₁ = h₂ := by
  have hmap : ((linkHeap h₁).map (heapLeafDigest8 S8)) = ((linkHeap h₂).map (heapLeafDigest8 S8)) :=
    perfectRoot8_injective S8 d (by rw [List.length_map, linkHeap_length, hlen₁])
      (by rw [List.length_map, linkHeap_length, hlen₂]) h
  exact linkHeap_injective (map_leaf8_injective S8 _ _ hmap)

/-- **`opensToMerkle8 S8 d r k o`** — some depth-`d` `2^d`-leaf sorted heap behind the 8-felt binary root
`r` reads `o` at `k`. The faithful `node8` replacement of `opensToMerkle`. -/
def opensToMerkle8 (d : Nat) (r : Digest8) (k : ℤ) (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d ∧ mapRoot8 S8 d h = r ∧ Heap.get h k = o

/-- **`writesToMerkle8 S8 d r k v r'`** — some depth-`d` `2^d`-leaf sorted heap behind 8-felt root `r`
produces root `r'` under the sorted insert-or-update of `(k, v)` (post-heap still `2^d`-leaf). -/
def writesToMerkle8 (d : Nat) (r : Digest8) (k v : ℤ) (r' : Digest8) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d
    ∧ (Heap.set h k v).length = 2 ^ d
    ∧ mapRoot8 S8 d h = r ∧ r' = mapRoot8 S8 d (Heap.set h k v)

/-- **8-felt openings are FUNCTIONAL (the anti-ghost over the `node8` tree).** Under the arity-16 chip
CR, the 8-felt root + key determine the read. Re-proved against `mapRoot8_injective`. -/
theorem opensToMerkle8_functional (d : Nat) {r : Digest8} {k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle8 S8 d r k o₁) (h₂ : opensToMerkle8 S8 d r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, _, hl₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, hr₂, hg₂⟩ := h₂
  have hm : m₁ = m₂ := mapRoot8_injective S8 d hl₁ hl₂ (hr₁.trans hr₂.symm)
  rw [← hg₁, ← hg₂, hm]

/-- Membership and non-membership at the same 8-felt root/key EXCLUDE each other (the `node8` nullifier /
non-membership tooth). -/
theorem opensToMerkle8_some_excludes_none (d : Nat) {r : Digest8} {k v : ℤ}
    (h₁ : opensToMerkle8 S8 d r k (some v)) (h₂ : opensToMerkle8 S8 d r k none) : False := by
  have := opensToMerkle8_functional S8 d h₁ h₂
  simp at this

/-- **8-felt writes are FUNCTIONAL.** Under the arity-16 chip CR, 8-felt root + key + value determine the
new root: the map-op row's `new_root` GROUP cannot be forged. Re-proved against `mapRoot8_injective`. -/
theorem writesToMerkle8_functional (d : Nat) {r : Digest8} {k v : ℤ} {r₁ r₂ : Digest8}
    (h₁ : writesToMerkle8 S8 d r k v r₁) (h₂ : writesToMerkle8 S8 d r k v r₂) : r₁ = r₂ := by
  obtain ⟨m₁, _, hl₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, _, hr₂, he₂⟩ := h₂
  have hm : m₁ = m₂ := mapRoot8_injective S8 d hl₁ hl₂ (hr₁.trans hr₂.symm)
  rw [he₁, he₂, hm]

end Faithful8

/-! ## §6 — Axiom hygiene. -/

#assert_axioms mapNode_injective
#assert_axioms foldLevel_length_half
#assert_axioms foldLevel_injective
#assert_axioms perfectRoot_injective
#assert_axioms mapRoot_injective
#assert_axioms opensToMerkle_functional
#assert_axioms opensToMerkle_some_excludes_none
#assert_axioms writesToMerkle_functional
-- §5b — the faithful 8-felt (`node8`) denotation, axiom-clean (crypto enters only as the named
-- `Heap8Scheme.chip8CR` arity-16 chip CR, via `DeployedHeapTree`).
#assert_axioms foldLevel8_injective
#assert_axioms perfectRoot8_injective
#assert_axioms mapRoot8_injective
#assert_axioms opensToMerkle8_functional
#assert_axioms opensToMerkle8_some_excludes_none
#assert_axioms writesToMerkle8_functional

end Dregg2.Circuit.MapMerkleRoot
