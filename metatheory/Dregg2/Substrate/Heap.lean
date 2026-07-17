/-
# Dregg2.Substrate.Heap — THE HEAP's sorted-map semantics (REFINEMENT-DESIGN Decision 1, wave R2).

A cell's programmable state becomes **registers + `heap_root`**: a sorted-Poseidon2 Merkle map over
`(collection_id, key) → value` (`.docs-history-noclaude/REFINEMENT-DESIGN.md` Decision 1). This module is the Lean
SEMANTIC FLOOR of that heap — the openable sorted map the circuit's gates will open against — built
as the GENERALIZATION of the proven `cap_root` machinery with a GENERIC leaf:

  * the SORTED-by-key invariant is the same strict `Pairwise (· < ·)` the non-membership bracketing
    proof rides (`Dregg2.Crypto.NonMembership.Sorted`, the cap/nullifier sorted tree);
  * NON-MEMBERSHIP openings reuse `sorted_gap_excludes` LITERALLY (the proven combinatorial heart of
    the sorted-tree non-membership AIR) — `get_none_of_gap` below is that theorem applied to the
    heap's key list;
  * the ROOT is a recomputed digest of the sorted leaf list, with the SAME single named crypto floor
    the cap-root advance carries (`Poseidon2SpongeCR`, `Circuit/Poseidon2Binding.lean`) and the same
    anti-ghost shape (`EffectVmEmitCapRoot.capRoot_binds_edge`): equal roots BIND the whole heap.

## Layer plan (mirrors the cap-root value model, `circuit/src/cap_root.rs` CanonicalCapTree)

  §1 — the GENERIC sorted map over any `LinearOrder` key: `get` / `set` (= sorted insert-or-update),
       proven: read-after-write, frame (untouched keys preserve openings), sorted-insert correctness
       (sortedness preserved + fresh-key grows by one + present-key updates in place), the
       membership characterization, the bracketing NON-MEMBERSHIP opening, and CANONICITY
       (`ext_get`: two sorted maps with the same lookup semantics are EQUAL — the determinism that
       makes the root a function of the map's MEANING, not its build history).
  §2 — the FELT heap (the deployed shape): addresses are key-hashes `addrOf = hash[coll, key]`
       (the sorted-by-key-hash tree of the design), leaves are `hash[addr, value]`, the root is the
       sponge of the sorted leaf list. Proven: `root_deterministic` (same semantics ⇒ same root,
       pure combinatorics) and `root_injective` (same root ⇒ same heap, under the ONE named CR
       hypothesis) — the two directions of "deterministic openable root", exactly the
       `KeyedCommit.KeyedDigestBindsKeys` discipline with a generic leaf.
  §3 — non-vacuity: concrete witnesses TRUE (reads back, frames, sorted) and FALSE (tampered value
       MOVES the root; absent key reads none) on a computable reference sponge.

The KERNEL face (how this sits beside `RecordKernelState` under the `write` verb's frame
discipline) is `Dregg2.Substrate.HeapKernel` — this module is executor/state-free on purpose.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as
the named `Poseidon2SpongeCR` hypothesis (the cap-root floor), never as an axiom. NEW file; imports are read-only.
-/
import Dregg2.Crypto.NonMembership
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Tactics

namespace Dregg2.Substrate.Heap

open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

universe u v

variable {κ : Type u} {ν : Type v} [LinearOrder κ]

/-! ## §1 — the generic sorted map (the openable-map semantics over ANY ordered key).

An entry is a `(key, value)` pair; the map is a key-sorted association list — the in-order leaf
list of the sorted Merkle tree (the same canonical realization the non-membership AIR is over,
`Crypto/NonMembership.lean §"The sorted committed set"`). -/

/-- The key list of a map (the sorted leaf-key spine the bracketing combinatorics read). -/
def keys (h : List (κ × ν)) : List κ := h.map Prod.fst

omit [LinearOrder κ] in
/-- `keys` on a cons (the definitional unfolding, named so proofs can `rw` it). -/
theorem keys_cons (k : κ) (v : ν) (t : List (κ × ν)) : keys ((k, v) :: t) = k :: keys t := rfl

/-- **The heap invariant** — the key spine is STRICTLY increasing (`Pairwise (· < ·)`, the exact
`Crypto.NonMembership.Sorted` predicate of the proven sorted tree). Strictness ⇒ keys are unique ⇒
the map is canonical (`ext_get`). -/
def SortedKeys (h : List (κ × ν)) : Prop := (keys h).Pairwise (· < ·)

/-- The head key of a sorted map is strictly below every tail key. -/
theorem sortedKeys_head_lt {k : κ} {v : ν} {t : List (κ × ν)}
    (hs : SortedKeys ((k, v) :: t)) : ∀ x ∈ keys t, k < x := by
  rw [SortedKeys, keys_cons] at hs
  exact (List.pairwise_cons.mp hs).1

/-- The tail of a sorted map is sorted. -/
theorem sortedKeys_tail {k : κ} {v : ν} {t : List (κ × ν)}
    (hs : SortedKeys ((k, v) :: t)) : SortedKeys t := by
  rw [SortedKeys, keys_cons] at hs
  exact (List.pairwise_cons.mp hs).2

/-- A sorted map's head key does NOT recur in its tail (strictness kills the duplicate). -/
theorem head_key_not_mem {k : κ} {v : ν} {t : List (κ × ν)}
    (hs : SortedKeys ((k, v) :: t)) : k ∉ keys t :=
  fun hmem => lt_irrefl k (sortedKeys_head_lt hs k hmem)

/-- **`get`** — the map lookup (the MEMBERSHIP OPENING's semantic content): the value at `k`, or
`none` when absent. First-match association lookup; on a `SortedKeys` map the match is unique. -/
def get : List (κ × ν) → κ → Option ν
  | [], _ => none
  | (k', v') :: rest, k => if k = k' then some v' else get rest k

@[simp] theorem get_nil (k : κ) : get ([] : List (κ × ν)) k = none := rfl

@[simp] theorem get_cons_self (k : κ) (v : ν) (t : List (κ × ν)) :
    get ((k, v) :: t) k = some v := by simp [get]

theorem get_cons_ne {k'' k' : κ} (v' : ν) (t : List (κ × ν)) (hne : k'' ≠ k') :
    get ((k', v') :: t) k'' = get t k'' := by simp [get, hne]

/-- **`set`** — the SORTED INSERT-OR-UPDATE (the leaf-update + sorted-insert gates' semantic
content): walk to the key's sorted position; overwrite in place if present, splice a fresh leaf if
absent. The single mutation primitive the `write` verb's heap instances reduce to. -/
def set : List (κ × ν) → κ → ν → List (κ × ν)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k = k' then (k, v) :: rest
    else (k', v') :: set rest k v

/-- **READ-AFTER-WRITE (`get_after_set`).** The written key reads back exactly the written value —
unconditionally (no sortedness needed; the walk places the binding before any stale duplicate). -/
theorem get_set_self (h : List (κ × ν)) (k : κ) (v : ν) : get (set h k v) k = some v := by
  induction h with
  | nil => simp [set]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]; simp
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · rw [if_pos heq]; simp
      · rw [if_neg heq]
        rw [get_cons_ne v' (set rest k v) heq]
        exact ih

/-- **FRAME (`get_set_frame`).** A write to key `k` leaves the opening of EVERY other key
untouched: `get (set h k v) k'' = get h k''` for `k'' ≠ k`. Untouched data costs (and changes)
nothing — the per-touched-key discipline of the design. -/
theorem get_set_frame (h : List (κ × ν)) (k k'' : κ) (v : ν) (hne : k'' ≠ k) :
    get (set h k v) k'' = get h k'' := by
  induction h with
  | nil => simp [set, get, hne]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt, get_cons_ne v ((k', v') :: rest) hne]
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · subst heq
        rw [if_pos rfl, get_cons_ne v rest hne, get_cons_ne v' rest hne]
      · rw [if_neg heq]
        by_cases h2 : k'' = k'
        · subst h2; simp
        · rw [get_cons_ne v' (set rest k v) h2, get_cons_ne v' rest h2]
          exact ih

/-- The key spine after a `set` is the old spine plus (at most) the written key. -/
theorem mem_keys_set_iff (h : List (κ × ν)) (k x : κ) (v : ν) :
    x ∈ keys (set h k v) ↔ x = k ∨ x ∈ keys h := by
  induction h with
  | nil => simp [set, keys]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]; simp [keys_cons, List.mem_cons]
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · subst heq
        rw [if_pos rfl]
        simp only [keys_cons, List.mem_cons]
        tauto
      · rw [if_neg heq]
        simp only [keys_cons, List.mem_cons, ih]
        tauto

/-- **SORTED-INSERT CORRECTNESS (invariant preservation).** `set` preserves the strict-sorted key
invariant — the splice lands the fresh leaf at its unique sorted position (the sorted-insert gate's
semantic obligation), and an in-place update never moves a key. -/
theorem set_sorted (h : List (κ × ν)) (k : κ) (v : ν) (hs : SortedKeys h) :
    SortedKeys (set h k v) := by
  induction h with
  | nil => simp [set, SortedKeys, keys]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]
      rw [SortedKeys, keys_cons, keys_cons]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hlt
        · exact hlt.trans (sortedKeys_head_lt hs x hx')
      · rw [SortedKeys, keys_cons] at hs; exact hs
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · subst heq
        rw [if_pos rfl]
        rw [SortedKeys, keys_cons]
        exact List.pairwise_cons.mpr ⟨sortedKeys_head_lt hs, sortedKeys_tail hs⟩
      · rw [if_neg heq]
        rw [SortedKeys, keys_cons]
        refine List.pairwise_cons.mpr ⟨?_, ih (sortedKeys_tail hs)⟩
        intro x hx
        rcases (mem_keys_set_iff rest k x v).mp hx with rfl | hx'
        · exact lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)
        · exact sortedKeys_head_lt hs x hx'

/-- **SORTED-INSERT CORRECTNESS (fresh key GROWS by one).** Writing an ABSENT key splices exactly
one new leaf — the insert face of `set`. -/
theorem length_set_fresh (h : List (κ × ν)) (k : κ) (v : ν) (hk : k ∉ keys h) :
    (set h k v).length = h.length + 1 := by
  induction h with
  | nil => simp [set]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    rw [keys_cons] at hk
    simp only [List.mem_cons, not_or] at hk
    obtain ⟨hne, hk'⟩ := hk
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]; simp
    · rw [if_neg hlt, if_neg hne]
      simp [ih hk']

/-- **SORTED-INSERT CORRECTNESS (present key UPDATES in place).** Writing a PRESENT key replaces
its leaf without growing the map — the leaf-update face of `set`. -/
theorem length_set_mem (h : List (κ × ν)) (k : κ) (v : ν) (hs : SortedKeys h)
    (hk : k ∈ keys h) : (set h k v).length = h.length := by
  induction h with
  | nil => simp [keys] at hk
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    rw [keys_cons] at hk
    rcases List.mem_cons.mp hk with rfl | hmem
    · simp [set]
    · have hgt : k' < k := sortedKeys_head_lt hs k hmem
      simp only [set]
      rw [if_neg (not_lt.mpr hgt.le), if_neg (ne_of_gt hgt)]
      simp [ih (sortedKeys_tail hs) hmem]

/-- **The membership characterization.** `get` returns `none` exactly when the key is OFF the
spine — the semantic content both the membership opening (`isSome`) and the non-membership opening
(`= none`) certify. -/
theorem get_eq_none_iff (h : List (κ × ν)) (k : κ) : get h k = none ↔ k ∉ keys h := by
  induction h with
  | nil => simp [keys]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    rw [keys_cons]
    by_cases heq : k = k'
    · subst heq; simp
    · rw [get_cons_ne v' rest heq]
      simp [heq, ih]

/-- **NON-MEMBERSHIP OPENING (`get_none_of_gap`) — the cap-root bracketing, REUSED.** If two
ADJACENT present keys `lo`, `hi` bracket `k` (`lo < k < hi`) on a sorted heap, then `k` is ABSENT:
`get h k = none`. The combinatorial heart is LITERALLY `Crypto.NonMembership.sorted_gap_excludes`
(the proven sorted-tree neighbor-bracketing of the nullifier/cap non-membership AIR), applied to
the heap's key spine — the design's "non-membership openings proven for nullifiers" generalized to
the generic-leaf heap with ZERO new combinatorics. -/
theorem get_none_of_gap (h : List (κ × ν)) (lo hi k : κ) (hs : SortedKeys h)
    (hadj : Adjacent (keys h) lo hi) (hlo : lo < k) (hhi : k < hi) :
    get h k = none :=
  (get_eq_none_iff h k).mpr (sorted_gap_excludes (keys h) lo hi k hs hadj hlo hhi)

/-- **CANONICITY (`ext_get`) — the determinism heart.** Two SORTED heaps with the SAME lookup
semantics are EQUAL (as leaf lists). This is what makes the committed root a function of the map's
MEANING: however a heap was built (any insert order, any update history), the sorted leaf list —
hence the root — is determined by `get` alone. The semantic twin of the canonical-tree property the
Rust `CanonicalCapTree` realizes by construction. -/
theorem ext_get : ∀ {h₁ h₂ : List (κ × ν)}, SortedKeys h₁ → SortedKeys h₂ →
    (∀ k, get h₁ k = get h₂ k) → h₁ = h₂ := by
  intro h₁
  induction h₁ with
  | nil =>
    intro h₂ _ _ hext
    cases h₂ with
    | nil => rfl
    | cons hd₂ t₂ =>
      obtain ⟨k₂, v₂⟩ := hd₂
      have h := hext k₂
      simp at h
  | cons hd₁ t₁ ih =>
    intro h₂ hs₁ hs₂ hext
    obtain ⟨k₁, v₁⟩ := hd₁
    cases h₂ with
    | nil =>
      have h := hext k₁
      simp at h
    | cons hd₂ t₂ =>
      obtain ⟨k₂, v₂⟩ := hd₂
      have hk : k₁ = k₂ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h := hext k₁
          rw [get_cons_self] at h
          have h2 : get ((k₂, v₂) :: t₂) k₁ = none := by
            rw [get_eq_none_iff, keys_cons]
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact lt_irrefl _ hlt
            · exact lt_irrefl _ (hlt.trans (sortedKeys_head_lt hs₂ _ hmem'))
          rw [h2] at h
          exact absurd h (by simp)
        · have h := (hext k₂).symm
          rw [get_cons_self] at h
          have h2 : get ((k₁, v₁) :: t₁) k₂ = none := by
            rw [get_eq_none_iff, keys_cons]
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact lt_irrefl _ hgt
            · exact lt_irrefl _ (hgt.trans (sortedKeys_head_lt hs₁ _ hmem'))
          rw [h2] at h
          exact absurd h (by simp)
      subst hk
      have hv : v₁ = v₂ := by
        have h := hext k₁
        rw [get_cons_self, get_cons_self] at h
        exact Option.some.inj h
      subst hv
      have htail : ∀ k, get t₁ k = get t₂ k := by
        intro k
        by_cases hkk : k = k₁
        · subst hkk
          rw [(get_eq_none_iff t₁ k).mpr (head_key_not_mem hs₁),
              (get_eq_none_iff t₂ k).mpr (head_key_not_mem hs₂)]
        · calc get t₁ k = get ((k₁, v₁) :: t₁) k := (get_cons_ne v₁ t₁ hkk).symm
            _ = get ((k₁, v₁) :: t₂) k := hext k
            _ = get t₂ k := get_cons_ne v₁ t₂ hkk
      exact congrArg (List.cons (k₁, v₁)) (ih (sortedKeys_tail hs₁) (sortedKeys_tail hs₂) htail)

-- §1 tripwires: every generic-map keystone is kernel-clean (pure combinatorics, NO crypto).
#assert_axioms get_set_self
#assert_axioms get_set_frame
#assert_axioms mem_keys_set_iff
#assert_axioms set_sorted
#assert_axioms length_set_fresh
#assert_axioms length_set_mem
#assert_axioms get_eq_none_iff
#assert_axioms get_none_of_gap
#assert_axioms ext_get

/-! ## §2 — the FELT heap: `(collection_id, key) → value` over the field, with the committed root.

The deployed shape (`REFINEMENT-DESIGN.md` Decision 1): the tree is sorted by KEY-HASH
`addrOf hash coll key = hash[coll, key]` (the `(collection_id, key)` address), the leaf binds the
address AND the value (`hash[addr, value]` — the generic-leaf generalization of the cap leaf
`hash[holder, target, rights, op]`, `EffectVmEmitCapRoot.siteCapEdgeLeaf`), and the root is the
sponge of the sorted leaf list (the `KeyedCommit.keyedDigest` shape). ONE crypto floor:
`Poseidon2SpongeCR` — the SAME named hypothesis the cap-root advance carries. -/

/-- The felt heap: a key-hash-addressed sorted map over the field (`ℤ` here, as everywhere in the
emit layer — the BabyBear felt is the deployment instance). -/
abbrev FeltHeap := List (ℤ × ℤ)

/-- **`addrOf`** — the heap ADDRESS of `(collection_id, key)`: the key-hash the tree is sorted by
(the design's "sorted-by-key-hash"). Distinct addresses ⇐ distinct pairs, under CR. -/
def addrOf (hash : List ℤ → ℤ) (coll key : ℤ) : ℤ := hash [coll, key]

/-- **`leafOf`** — the heap LEAF: `hash[addr, value]` — the generic-leaf generalization of the
cap-edge leaf (the address pins WHERE, the value pins WHAT; tampering either moves the leaf). -/
def leafOf (hash : List ℤ → ℤ) (e : ℤ × ℤ) : ℤ := hash [e.1, e.2]

/-- **`root`** — the committed heap root: the sponge of the (sorted) leaf list. The value the
`heap_root` register carries; the openable sorted-Poseidon2 root, computed from the SAME leaf list
the cell holds (cell≡circuit identity is BY DEFINITION at this layer — both read THIS function). -/
def root (hash : List ℤ → ℤ) (h : FeltHeap) : ℤ := hash (h.map (leafOf hash))

/-- `get` at a `(collection_id, key)` address. -/
def hget (hash : List ℤ → ℤ) (h : FeltHeap) (coll key : ℤ) : Option ℤ :=
  get h (addrOf hash coll key)

/-- `set` at a `(collection_id, key)` address (sorted insert-or-update). -/
def hset (hash : List ℤ → ℤ) (h : FeltHeap) (coll key v : ℤ) : FeltHeap :=
  set h (addrOf hash coll key) v

/-- Read-after-write at the addressed key (no crypto needed). -/
theorem hget_hset_self (hash : List ℤ → ℤ) (h : FeltHeap) (coll key v : ℤ) :
    hget hash (hset hash h coll key v) coll key = some v :=
  get_set_self h (addrOf hash coll key) v

/-- **FRAME at distinct addresses (under CR).** Writing `(coll, key)` preserves the opening of any
OTHER `(coll', key')`: CR forces distinct pairs onto distinct addresses, then the generic frame
applies. This is the design's "untouched data costs nothing", with the key-hash collision the ONLY
(named) way to break it — exactly the cap-root trust boundary. -/
theorem hget_hset_frame (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (coll key coll' key' v : ℤ) (hne : ¬(coll' = coll ∧ key' = key)) :
    hget hash (hset hash h coll key v) coll' key' = hget hash h coll' key' := by
  apply get_set_frame
  intro haddr
  have hlist := hCR _ _ haddr
  simp only [List.cons.injEq, and_true] at hlist
  exact hne ⟨hlist.1, hlist.2⟩

/-- The leaf-list map is injective under CR (heads peel by leaf-CR, tails by induction) — the
inner-leaf half of the root anti-ghost, mirroring `capRoot_binds_edge`'s two-stage peel. -/
theorem map_leaf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (l₁ l₂ : FeltHeap), l₁.map (leafOf hash) = l₂.map (leafOf hash) → l₁ = l₂ := by
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
      obtain ⟨a₁, b₁⟩ := hd₁
      obtain ⟨a₂, b₂⟩ := hd₂
      have hlist := hCR _ _ hleaf
      simp only [List.cons.injEq, and_true] at hlist
      rw [hlist.1, hlist.2, ih t₂ htail]

/-- **`root_injective` — the root BINDS the whole heap (the anti-ghost).** Two heaps with EQUAL
roots are EQUAL leaf lists, under the single named CR floor: peel the outer sponge (leaf lists
equal), then each leaf (entries equal). A prover cannot keep the published `heap_root` while
tampering ANY address or ANY value — the `capRoot_binds_edge` tooth with a generic leaf. -/
theorem root_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (h : root hash h₁ = root hash h₂) : h₁ = h₂ :=
  map_leaf_injective hash hCR h₁ h₂ (hCR _ _ h)

/-- **`root_deterministic` — the root is a function of the map's MEANING.** Two SORTED heaps with
the same lookup semantics have the SAME root (via canonicity `ext_get`; NO crypto). Build history
is invisible to the commitment — the openable root is well-defined on the abstract map. -/
theorem root_deterministic (hash : List ℤ → ℤ) {h₁ h₂ : FeltHeap}
    (hs₁ : SortedKeys h₁) (hs₂ : SortedKeys h₂)
    (hext : ∀ k, get h₁ k = get h₂ k) : root hash h₁ = root hash h₂ := by
  rw [ext_get hs₁ hs₂ hext]

/-- **`root_binds_get` — equal roots open identically.** Under CR, two heaps publishing the same
root agree at EVERY address: the membership/non-membership openings are pinned by the root alone.
The consumable form per-effect gates will cite. -/
theorem root_binds_get (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (h : root hash h₁ = root hash h₂) :
    ∀ coll key, hget hash h₁ coll key = hget hash h₂ coll key := by
  intro coll key
  rw [root_injective hash hCR h]

#assert_axioms hget_hset_self
#assert_axioms hget_hset_frame
#assert_axioms map_leaf_injective
#assert_axioms root_injective
#assert_axioms root_deterministic
#assert_axioms root_binds_get

/-! ## §3 — NON-VACUITY: concrete witnesses TRUE and FALSE on a computable reference sponge.

The same Horner-with-length-tag toy sponge the cap-root recompute uses (`EffectVmEmitCapRoot.cN`)
so the heap is computable and a tampered write provably MOVES the root. (The soundness theorems
above use the abstract CR sponge; these guards exhibit realizable witnesses.) -/

/-- The reference sponge (Horner with a length tag) — computable, injective-enough for the
concrete guards. NOT real crypto (the deployment instance is the p3 Poseidon2 sponge behind
`Poseidon2SpongeCR`). -/
def refSponge : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

/-- A hand-sorted raw heap (addresses 10, 20 holding 1, 2) for the bracketing witnesses. -/
def demoRaw : FeltHeap := [(10, 1), (20, 2)]

/-- `demoRaw` satisfies the sorted invariant (10 < 20). -/
theorem demoRaw_sorted : SortedKeys demoRaw := by
  norm_num [demoRaw, SortedKeys, keys, List.pairwise_cons]

/-- Addresses 10 and 20 are ADJACENT on `demoRaw`'s spine (nothing between). -/
theorem demoRaw_adjacent : Adjacent (keys demoRaw) 10 20 := ⟨[], [], rfl⟩

/-- **Non-vacuity of the NON-MEMBERSHIP opening**: 15 is bracketed by the adjacent present
addresses 10 < 15 < 20, so `get demoRaw 15 = none` — `sorted_gap_excludes` firing on the heap. -/
theorem demoRaw_gap_15 : get demoRaw (15 : ℤ) = none :=
  get_none_of_gap demoRaw 10 20 15 demoRaw_sorted demoRaw_adjacent
    (by norm_num) (by norm_num)

-- Membership/absence read off the same spine (the executable face of the same facts):
#guard get demoRaw (10 : ℤ) == some 1
#guard get demoRaw (15 : ℤ) == none
-- Sorted insert in the middle lands between the brackets and preserves reads:
#guard keys (set demoRaw (15 : ℤ) 99) == [10, 15, 20]
#guard get (set demoRaw (15 : ℤ) 99) (15 : ℤ) == some 99
#guard get (set demoRaw (15 : ℤ) 99) (10 : ℤ) == some 1   -- frame
#guard (set demoRaw (15 : ℤ) 99).length == 3              -- fresh key grows
#guard (set demoRaw (10 : ℤ) 99).length == 2              -- present key updates in place

/-- A concrete addressed heap: write (coll 1, key 2) := 42 then (coll 3, key 4) := 7. -/
def demoHeap : FeltHeap := hset refSponge (hset refSponge [] 1 2 42) 3 4 7

-- Read-after-write + frame at the addressed layer (witness TRUE):
#guard hget refSponge demoHeap 1 2 == some 42
#guard hget refSponge demoHeap 3 4 == some 7
#guard hget refSponge demoHeap 9 9 == none
#guard hget refSponge (hset refSponge demoHeap 1 2 50) 3 4 == some 7  -- untouched key preserved

-- **Witness FALSE (anti-ghost):** tampering ONE value MOVES the root — the published `heap_root`
-- cannot be kept while editing the heap (the executable shadow of `root_injective`):
#guard (root refSponge (hset refSponge demoHeap 1 2 50) != root refSponge demoHeap)
-- ...and writing a DIFFERENT address also moves it (addresses are bound, not just values):
#guard (root refSponge (hset refSponge demoHeap 5 6 42) != root refSponge demoHeap)

#assert_axioms demoRaw_sorted
#assert_axioms demoRaw_adjacent
#assert_axioms demoRaw_gap_15

end Dregg2.Substrate.Heap
