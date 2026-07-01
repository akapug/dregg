/-
# Dregg2.Circuit.Emit.HeapOpenEmit — the LIVE heap-membership open, the SECOND faithful-root after-spine.

The exact twin of `CapOpenEmit.lean` §11/§12 for the `heap_root` (the second faithful 8-felt Merkle root).
Where the cap-open read authenticates a HELD capability's authority (7-field `CapLeaf`, facet/mask gates),
the heap open authenticates a `(addr, value)` leaf against the committed 8-felt heap root — no authority
machinery, just membership. The keystone `heapOpen_writesTo8` reduces the faithful 8-felt heap-write to TWO
`HeapMembershipCore` witnesses sharing a path (before = old leaf against the BEFORE heap-root group; after =
in-place-updated leaf, SAME address, new value, against the AFTER heap-root group), FORCING
`EffectVmEmitRotationV3.heapWritesTo8` over the FULL ~124-bit root — NEVER the lane-0 squeeze the heap
GENTIAN tooth (`circuit/tests/heap_root_gentian_weld.rs`) refutes.

REUSE: the node-recompose spine is leaf-AGNOSTIC (`DeployedCapOpen.nodeLookup`/`nodeInputs`/`nodeInputs_eval`/
`dir_zero_or_one` over `CapOpenCols`, rides the ONE `node8` chip), so the heap membership reuses it verbatim
and re-instantiates the digest scheme at `Heap8Scheme` (`heapNodeOf8`, `heapLeafDigest8`). The SOLE
heap-specific material is the arity-2 leaf absorb (`heapLeafLookup`, `heapLeafDigest_sound8`) — the heap leaf
is `(addr, value)`, not a 7-field `CapLeaf`.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named WIDE
chip-soundness `ChipTableSoundN (heapPermOut S8)`, inherited from `DeployedHeapTree`/`DeployedCapOpen`.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.DeployedHeapTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.HeapOpenEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily Lookup VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2
   chipLookupTupleN chip_lookup_sound_N CHIP_RATE)
open Dregg2.Circuit.DeployedCapOpen
  (CapOpenCols DEPTH digestCols digestCols_map curCol nodeInputs nodeLookup nodeInputs_eval
   dirBoolGate dirBoolVal dir_zero_or_one rootPinGate pathOf8 groupVal)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (heapLeafDigest8 heapNodeOf8 recomposeUp8)
open Dregg2.Circuit.CapMerkleGeneric (StepG recomposeG)

set_option autoImplicit false

/-! ## §0 — the heap leaf columns + the arity-2 leaf absorb (the SOLE heap-specific chip lookup).

The heap membership reuses the `CapOpenCols` layout, reading leaf column 0 as the `addr` and leaf column 1
as the `value` (columns 2..6, and the facet/mask machinery, are UNUSED — the heap leaf carries no authority).
The leaf absorb is arity-2 (`heapLeafDigest8 S8 (addr, value) = S8.chipAbsorb8 [addr, value]`), NOT the cap
arity-7 `leafFields`. -/

/-- The `(addr, value)` heap leaf pair read off the row's leaf columns 0/1. -/
def heapLeafPairOf (c : CapOpenCols) (env : VmRowEnv) : ℤ × ℤ :=
  (env.loc (c.leaf 0), env.loc (c.leaf 1))

/-- The 2 heap-leaf column EXPRESSIONS `[addr, value]` (the arity-2 chip absorb's input tuple). -/
def heapLeafInputs (c : CapOpenCols) : List EmittedExpr :=
  [EmittedExpr.var (c.leaf 0), EmittedExpr.var (c.leaf 1)]

/-- The heap leaf inputs evaluate to exactly `[addr, value]` of the decoded pair. -/
theorem heapLeafInputs_eval (c : CapOpenCols) (env : VmRowEnv) :
    (heapLeafInputs c).map (·.eval env.loc)
      = [(heapLeafPairOf c env).1, (heapLeafPairOf c env).2] := by
  simp [heapLeafInputs, heapLeafPairOf, EmittedExpr.eval]

/-- **`heapPermOut S8`** — the WIDE permutation output the shared `node8` chip realizes for the heap
scheme: the 8 squeezed lanes of `S8.chipAbsorb8` read as a `List ℤ`. `heapPermOut S8 [addr,value] =
List.ofFn (heapLeafDigest8 S8 (addr,value))` and `heapPermOut S8 (pack8 l r) = List.ofFn (heapNodeOf8 S8
l r)` — both by `rfl` (`List.ofFn ∘ chipAbsorb8` of the input block). -/
def heapPermOut (S8 : Heap8Scheme) : List ℤ → List ℤ := fun xs => List.ofFn (S8.chipAbsorb8 xs)

/-- The 8-felt heap-leaf chip lookup tuple: absorb the 2 heap-leaf columns, output = the 8 bound
leaf-digest columns (the whole `node8` leaf block). -/
def heapLeafLookup (c : CapOpenCols) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN (heapLeafInputs c) (digestCols c.leafDigest) }

/-! ## §1 — the heap membership core + the node/leaf digest soundness (re-instantiated at `Heap8Scheme`). -/

/-- **`HeapMembershipCore tf c env`** — the four facts the 8-felt heap Merkle fold consumes: the arity-2
leaf absorb, the per-level `node8` absorbs (SHARED with cap — the same `nodeLookup`), direction booleanity,
and the (8-lane) root pin. The heap twin of `DeployedCapOpen.MembershipCore`. -/
structure HeapMembershipCore (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) : Prop where
  leafHashed : (heapLeafLookup c).holdsAt tf env
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  rootPinned : ∀ i : Fin 8, (rootPinGate c i).eval env.loc = 0

/-- **`heapLeafDigest_sound8`** — under a SOUND WIDE chip table, the 8 leaf-digest columns carry the genuine
native-8-felt `heapLeafDigest8 S8 (addr, value)`. The whole 8-felt block is bound, not just lane-0. The heap
twin of `leafDigest_sound8` (arity-2 leaf). -/
theorem heapLeafDigest_sound8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) :
    groupVal env c.leafDigest = heapLeafDigest8 S8 (heapLeafPairOf c env) := by
  have hlen : (heapLeafInputs c).length ≤ CHIP_RATE := by
    simp [heapLeafInputs, CHIP_RATE]
  have hmem : (chipLookupTupleN (heapLeafInputs c) (digestCols c.leafDigest)).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.leafHashed
    unfold Lookup.holdsAt heapLeafLookup at this
    exact this
  have h := chip_lookup_sound_N (heapPermOut S8) (tf .poseidon2) hChip env.loc (heapLeafInputs c)
    (digestCols c.leafDigest) hlen hmem
  rw [digestCols_map, heapLeafInputs_eval] at h
  -- `heapPermOut S8 [addr,value] = List.ofFn (heapLeafDigest8 S8 (addr,value))` by `rfl`.
  have hreal : heapPermOut S8 [(heapLeafPairOf c env).1, (heapLeafPairOf c env).2]
      = List.ofFn (heapLeafDigest8 S8 (heapLeafPairOf c env)) := rfl
  rw [hreal] at h
  exact List.ofFn_inj.mp h

/-- **`heapNode_sound8`** — under a SOUND WIDE chip table, level `lvl`'s 8 node columns carry the genuine
native-8-felt `heapNodeOf8 S8` of the dir-mixed `(cur8, sib8)` pair — one `recomposeUp8` step at full
~124-bit width. Reuses the SHARED `nodeInputs_eval` (the node block is leaf-agnostic). -/
theorem heapNode_sound8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) (lvl : Nat) (hlvl : lvl < DEPTH) :
    groupVal env (c.node lvl)
      = (if dirBoolVal c env lvl
          then heapNodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))
          else heapNodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := by
  have hlen : (nodeInputs c lvl).length ≤ CHIP_RATE := by
    simp [nodeInputs, List.length_append, List.length_map, List.length_finRange, CHIP_RATE]
  have hmem : (chipLookupTupleN (nodeInputs c lvl) (digestCols (c.node lvl))).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.nodeHashed lvl hlvl
    unfold Lookup.holdsAt nodeLookup at this
    exact this
  have h := chip_lookup_sound_N (heapPermOut S8) (tf .poseidon2) hChip env.loc (nodeInputs c lvl)
    (digestCols (c.node lvl)) hlen hmem
  rw [digestCols_map, nodeInputs_eval c env lvl (dir_zero_or_one c env lvl (hcore.dirBool lvl hlvl))] at h
  cases hb : dirBoolVal c env lvl
  · simp only [hb, Bool.false_eq_true, if_false] at h ⊢
    have hreal : heapPermOut S8 (pack8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl)))
        = List.ofFn (heapNodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h
  · simp only [hb, if_true] at h ⊢
    have hreal : heapPermOut S8 (pack8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl)))
        = List.ofFn (heapNodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h

/-- `recomposeUp8` (heap scheme) distributes over a path append (over the generic `recomposeG` spine). -/
theorem heapRecomposeUp8_append (S8 : Heap8Scheme) (cur : Digest8) (p q : List (StepG Digest8)) :
    recomposeUp8 S8 cur (p ++ q) = recomposeUp8 S8 (recomposeUp8 S8 cur p) q := by
  show recomposeG (heapNodeOf8 S8) cur (p ++ q)
     = recomposeG (heapNodeOf8 S8) (recomposeG (heapNodeOf8 S8) cur p) q
  induction p generalizing cur with
  | nil => rfl
  | cons s rest ih => simp only [List.cons_append, recomposeG]; rw [ih]

/-- Folding `recomposeUp8` over the first `n` levels reproduces `curCol c n` (as a `Digest8`), under the
WIDE chip soundness — the native 8-felt heap fold. The heap twin of `recompose_reaches_cur8`. -/
theorem heapRecompose_reaches_cur8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) :
    ∀ n, n ≤ DEPTH →
      recomposeUp8 S8 (groupVal env c.leafDigest) (pathOf8 c env n) = groupVal env (curCol c n) := by
  intro n
  induction n with
  | zero => intro _; simp [pathOf8, recomposeUp8, recomposeG, curCol]
  | succ k ih =>
    intro hk
    have hkd : k < DEPTH := Nat.lt_of_succ_le hk
    have hkle : k ≤ DEPTH := Nat.le_of_lt hkd
    have hpath : pathOf8 c env (k + 1)
        = pathOf8 c env k ++ [{ sib := groupVal env (c.sib k), dir := dirBoolVal c env k }] := by
      simp [pathOf8, List.range_succ, List.map_append]
    rw [hpath, heapRecomposeUp8_append, ih hkle]
    simp only [recomposeUp8, recomposeG]
    have hns := heapNode_sound8 S8 tf c env hChip hcore k hkd
    have hcur : curCol c (k + 1) = c.node k := rfl
    rw [hcur]
    cases hb : dirBoolVal c env k
    · simp only [hb, Bool.false_eq_true, if_false] at hns ⊢
      rw [hns]
    · simp only [hb, if_true] at hns ⊢
      rw [hns]

/-! ## §2 — the recompose from a single core + the STEP-A keystone `heapOpen_writesTo8`. -/

/-- **`heapOpen_recompose8`** — the explicit before/after recompose: under a sound WIDE chip table, the leaf's
native-8-felt heap digest recomposes the committed 8-felt heap-root GROUP along the column-read path. The
`heapWritesTo8` assembler instantiates this at BOTH the before and after spine. The heap twin of
`capOpen_recompose8`. -/
theorem heapOpen_recompose8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) :
    recomposeUp8 S8 (heapLeafDigest8 S8 (heapLeafPairOf c env)) (pathOf8 c env DEPTH)
      = groupVal env c.capRoot := by
  have hfold := heapRecompose_reaches_cur8 S8 tf c env hChip hcore DEPTH (le_refl _)
  have hleaf := heapLeafDigest_sound8 S8 tf c env hChip hcore
  rw [hleaf] at hfold
  have hcurTop : curCol c DEPTH = c.node (DEPTH - 1) := rfl
  rw [hcurTop] at hfold
  have hroot : groupVal env (c.node (DEPTH - 1)) = groupVal env c.capRoot := by
    funext i
    have hpin := hcore.rootPinned i
    unfold rootPinGate at hpin
    simp only [EmittedExpr.eval] at hpin
    simp only [groupVal]
    linarith
  rw [hfold, hroot]

/-- **`heapOpen_writesTo8` — THE STEP-A KEYSTONE.** Two `HeapMembershipCore` witnesses sharing the sibling
path (before = old leaf membership against the BEFORE heap-root group; after = updated-leaf membership, SAME
address, new value, against the AFTER heap-root group) FORCE the faithful 8-felt `heapWritesTo8` over the FULL
~124-bit root — NOT the lane-0 projection. The post root cannot be forged: a colliding heap tree (different
leaves, same lane-0) yields a different `node8` fold top and FAILS ≥1 of the 8 `rootPinGate` lanes of the
after core. Trace-forced: the witnesses come from `Satisfied2`, never from `henc`'s `SpineCommits`. -/
theorem heapOpen_writesTo8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (cBefore cAfter : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hBefore : HeapMembershipCore tf cBefore env)
    (hAfter  : HeapMembershipCore tf cAfter env)
    (hsib : cAfter.sib = cBefore.sib)
    (hdir : cAfter.dir = cBefore.dir)
    (hkey : (heapLeafPairOf cAfter env).1 = (heapLeafPairOf cBefore env).1) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
        (groupVal env cBefore.capRoot)
        ((heapLeafPairOf cBefore env).1) ((heapLeafPairOf cAfter env).2)
        (groupVal env cAfter.capRoot) := by
  refine ⟨(heapLeafPairOf cBefore env).2, pathOf8 cBefore env DEPTH, ?_, ?_⟩
  · -- before: recomposeUp8 (heapLeafDigest8 (k, oldVal)) path = groupVal cBefore.capRoot
    have hrec := heapOpen_recompose8 S8 tf cBefore env hChip hBefore
    -- (heapLeafPairOf cBefore env) = ((·).1, (·).2) definitionally, so the digest arg matches.
    simpa using hrec
  · -- after: recomposeUp8 (heapLeafDigest8 (k, v)) path = groupVal cAfter.capRoot along the SAME path
    have hpath : pathOf8 cAfter env DEPTH = pathOf8 cBefore env DEPTH := by
      simp only [pathOf8, dirBoolVal, hsib, hdir]
    have hrec := heapOpen_recompose8 S8 tf cAfter env hChip hAfter
    rw [hpath] at hrec
    -- rewrite the after leaf's addr to the shared key: (pairAfter).1 = (pairBefore).1.
    have hpair : heapLeafPairOf cAfter env
        = ((heapLeafPairOf cBefore env).1, (heapLeafPairOf cAfter env).2) := by
      rw [← hkey]
    rw [hpair] at hrec
    exact hrec

#assert_axioms heapLeafDigest_sound8
#assert_axioms heapNode_sound8
#assert_axioms heapRecompose_reaches_cur8
#assert_axioms heapOpen_recompose8
#assert_axioms heapOpen_writesTo8

end Dregg2.Circuit.Emit.HeapOpenEmit
