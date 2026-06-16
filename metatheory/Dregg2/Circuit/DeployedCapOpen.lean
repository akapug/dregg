/-
# Dregg2.Circuit.DeployedCapOpen — the IN-CIRCUIT cap-tree membership-open (authority leg foundation).

## Why this file exists (the critical-path authority leg)

`DeployedCapTree.lean` models the deployed 7-field depth-16 `hash_fact` cap-tree and proves the
KERNEL-side bridge `deployedCapOpen_implies_authorizedB`: a write-mask `MembersAt` opening implies
the kernel's `authorizedB`. But that bridge consumes `MembersAt` as a HYPOTHESIS — nothing in the
circuit denotation produced it. The deployed Rust `cap_root` column is, today, a FROZEN digest: the
depth-16 cap-tree is never OPENED in-circuit, so the authority leg of every `fullActionStep` arm
(`authorizedB`) is asserted, not witnessed.

This file closes that gap on the CIRCUIT side. It defines a CONSTRAINT — `CapOpenConstraint` — whose
denotation is exactly the in-circuit shape the Rust AIR realizes:

  * the 7 cap-leaf fields ride a Poseidon2 chip ABSORB (arity 7) producing the leaf digest column —
    `DescriptorIR2.chip_lookup_sound` ENFORCES `leafDigest = sponge[7 fields]` against a sound chip
    table (the EXACT `DeployedCapTree.capLeafDigest`);
  * each of the depth-16 levels rides a `hash_fact`-shaped chip absorb (the tagged 3-list
    `[FACT_MARK, l, r]`) mixing `(cur, sib)` by the direction bit — `chip_lookup_sound` ENFORCES each
    node equals `DeployedCapTree.nodeOf`, and the chain's top is CONSTRAINED `== cap_root` column;
  * the leaf's `target` column is CONSTRAINED `== src` (the turn's source cell), and the leaf's
    `mask_lo` column is CONSTRAINED to the write-endpoint mask (`confersWriteLeaf`).

The keystone `capOpen_sound` proves: a `Satisfied` `CapOpenConstraint` (against a sound chip table)
yields `DeployedCapTree.MembersAt cap_root leaf ∧ leaf.target = src ∧ confersWriteLeaf leaf`. Chained
through `DeployedCapTree.deployedCapOpen_implies_authorizedB` against the deployed commitment, this
DISCHARGES the kernel's `authorizedB` gate from the in-circuit membership proof. The cap path-witness
is no longer a `&[]`: the depth-16 fold IS the proof.

## What is faithful here (Rust anchors)

  * The leaf absorb mirrors `cap_root.rs::CapLeaf::digest` (`hash_many` of the 7 fields).
  * The per-level fold mirrors `descriptor_ir2.rs` MapOps `mix` (lines 2109-2135) and the Rust
    `CapMembership` AIR's `fact_bus` chain — `(left, right) = ((1-dir)·cur + dir·sib, …)` then the
    `hash_fact` node, with the LAST level constrained against the `cap_root` column. The leaf↔effect
    binding (`target == src`, write-mask) mirrors the AIR's `assert_zero(target - src)` gate.
  * `MembersAt`/`recomposeUp`/`capLeafDigest`/`nodeOf` are imported UNCHANGED from `DeployedCapTree`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis (the same single floor the chip lever already carries). No `sorry`, no
`native_decide`, no `:= True`. NEW file; imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.DeployedCapTree

namespace Dregg2.Circuit.DeployedCapOpen

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily TableId Lookup chipLookupTuple ChipTableSound chip_lookup_sound CHIP_RATE)
open Dregg2.Circuit.DeployedCapTree
  (CapLeaf Step capLeafDigest nodeOf FACT_MARK recomposeUp MembersAt confersWriteLeaf
   DeployedFaithful deployedCapOpen_implies_authorizedB)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (rightsMaskOf)
open Dregg2.Authority (Cap Auth Caps Label)

set_option autoImplicit false

/-! ## §0 — the column plan for one cap-membership row.

A `CapOpenConstraint` row carries (as columns, read off `env.loc`):

  * the 7 leaf-field columns (`leafCols`), one per `CapLeaf` field;
  * the leaf-digest column (`leafDigestCol`) — the chip absorb output;
  * for each of `DEPTH` levels: a sibling column (`sibCol lvl`), a direction column (`dirCol lvl`),
    and the level's node-output column (`nodeCol lvl`); the top node-output is constrained `== cap_root`;
  * the `cap_root` column and the `src` column (the turn's source cell id).

These are abstract column indices `Nat`; the Rust layout pins them (`descriptor_ir2.rs` cap-membership
table). The Lean denotation reads them through `env.loc`, exactly as every other v2 constraint does. -/

/-- The deployed cap-tree depth (`cap_root.rs::CAP_TREE_DEPTH = 16`). -/
def DEPTH : Nat := 16

/-- The column layout for a cap-membership row. All indices abstract `Nat`; the Rust AIR pins them. -/
structure CapOpenCols where
  /-- The 7 leaf-field columns, in `CapLeaf` order (slot_hash, target, auth_tag, mask_lo, mask_hi,
  expiry, breadstuff). -/
  leaf       : Fin 7 → Nat
  /-- The leaf-digest column (the chip absorb output). -/
  leafDigest : Nat
  /-- The sibling-digest column at each level. -/
  sib        : Nat → Nat
  /-- The direction-bit column at each level (0 ⇒ cur is LEFT child). -/
  dir        : Nat → Nat
  /-- The node-output column at each level (the `hash_fact` output; top == cap_root). -/
  node       : Nat → Nat
  /-- The committed `cap_root` column. -/
  capRoot    : Nat
  /-- The turn's source-cell-id column (the effect's `src`). -/
  src        : Nat

/-! ## §1 — the leaf-field accessors (decode the 7 leaf columns to a `CapLeaf`). -/

/-- Read the `CapLeaf` whose fields are the row's 7 leaf columns. -/
def leafOf (c : CapOpenCols) (env : VmRowEnv) : CapLeaf :=
  { slot_hash  := env.loc (c.leaf 0)
  , target     := env.loc (c.leaf 1)
  , auth_tag   := env.loc (c.leaf 2)
  , mask_lo    := env.loc (c.leaf 3)
  , mask_hi    := env.loc (c.leaf 4)
  , expiry     := env.loc (c.leaf 5)
  , breadstuff := env.loc (c.leaf 6) }

/-- The 7 leaf-field column EXPRESSIONS, in canonical order (the chip absorb's input tuple). -/
def leafInputs (c : CapOpenCols) : List EmittedExpr :=
  (List.finRange 7).map (fun i => EmittedExpr.var (c.leaf i))

/-- The leaf inputs evaluate to exactly the `capLeafDigest` argument list. -/
theorem leafInputs_eval (c : CapOpenCols) (env : VmRowEnv) :
    (leafInputs c).map (·.eval env.loc)
      = [ (leafOf c env).slot_hash, (leafOf c env).target, (leafOf c env).auth_tag,
          (leafOf c env).mask_lo, (leafOf c env).mask_hi, (leafOf c env).expiry,
          (leafOf c env).breadstuff ] := by
  simp only [leafInputs, List.map_map]
  rfl

/-! ## §2 — the chip-lookup tuples (leaf absorb + per-level node absorb).

Each is a `chipLookupTuple` — the SAME primitive `DescriptorIR2.chip_lookup_sound` enforces. The leaf
absorb is arity 7 (`capLeafDigest`); each node absorb is arity 3 (`nodeOf = sponge[FACT_MARK, l, r]`).
Both fit `CHIP_RATE = 8`. -/

/-- The leaf-digest chip lookup tuple: absorb the 7 leaf-field columns, output = `leafDigest`. -/
def leafLookup (c : CapOpenCols) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTuple (leafInputs c) c.leafDigest }

/-- The `cur` digest entering level `lvl`: the leaf digest at level 0, else the previous node. -/
def curCol (c : CapOpenCols) : Nat → Nat
  | 0       => c.leafDigest
  | (l + 1) => c.node l

/-- The `hash_fact` LEFT input at level `lvl`: `(1-dir)·cur + dir·sib`. -/
def leftExpr (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .add (.mul (.add (.const 1) (.mul (.const (-1)) (.var (c.dir lvl)))) (.var (curCol c lvl)))
       (.mul (.var (c.dir lvl)) (.var (c.sib lvl)))

/-- The `hash_fact` RIGHT input at level `lvl`: `(1-dir)·sib + dir·cur`. -/
def rightExpr (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .add (.mul (.add (.const 1) (.mul (.const (-1)) (.var (c.dir lvl)))) (.var (c.sib lvl)))
       (.mul (.var (c.dir lvl)) (.var (curCol c lvl)))

/-- The node chip lookup tuple at level `lvl`: absorb `[FACT_MARK, left, right]`, output = `node lvl`.
(The last level's output column is constrained `== capRoot` separately, §3.) -/
def nodeLookup (c : CapOpenCols) (lvl : Nat) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTuple [.const FACT_MARK, leftExpr c lvl, rightExpr c lvl] (c.node lvl) }

/-! ## §3 — the gate equations (booleanity, root pin, leaf↔effect binding). -/

/-- `dir` is boolean: `dir·(dir-1) = 0`. (Mirrors the Rust `assert_zero(dir*(dir-1))`.) -/
def dirBoolGate (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .mul (.var (c.dir lvl)) (.add (.var (c.dir lvl)) (.const (-1)))

/-- The root pin: the TOP node output equals the committed `cap_root` column. -/
def rootPinGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.node (DEPTH - 1))) (.mul (.const (-1)) (.var c.capRoot))

/-- The target binding: `leaf.target - src = 0`. -/
def targetBindGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 1)) (.mul (.const (-1)) (.var c.src))

/-- The write-mask binding: `leaf.mask_lo - WRITE_MASK = 0`, where `WRITE_MASK` is the
read+write endpoint mask (`confersWriteLeaf`'s pinned value). -/
def writeMaskGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 3)) (.const (-(rightsMaskOf (Cap.endpoint 0 [Auth.read, Auth.write]))))

/-! ## §4 — `Satisfied`: the full per-row denotation of one cap-membership constraint. -/

/-- **`Satisfied sponge tf c env`** — the cap-membership row is satisfied: every chip lookup is a
row of the (sound) chip table, every `dir` is boolean, the root pin / target / write-mask gates
vanish. This is the in-circuit denotation the Rust `CapMembership` AIR realizes. -/
structure Satisfied (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) : Prop where
  /-- The leaf-digest chip absorb is a chip-table row. -/
  leafHashed : (leafLookup c).holdsAt tf env
  /-- Each level's node absorb is a chip-table row. -/
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  /-- Each level's direction column is boolean. -/
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  /-- The top node output equals the committed cap_root. -/
  rootPinned : (rootPinGate c).eval env.loc = 0
  /-- The leaf's target equals the turn's src. -/
  targetBound : (targetBindGate c).eval env.loc = 0
  /-- The leaf's mask_lo is the write-endpoint mask. -/
  writeMasked : (writeMaskGate c).eval env.loc = 0

/-! ## §5 — soundness: the leaf-digest column carries the genuine `capLeafDigest`. -/

/-- Under a sound chip table, the leaf-digest column carries `capLeafDigest sponge (leafOf c env)`. -/
theorem leafDigest_sound (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hChip : ChipTableSound sponge (tf .poseidon2))
    (hsat : Satisfied sponge tf c env) :
    env.loc c.leafDigest = capLeafDigest sponge (leafOf c env) := by
  have hlen : (leafInputs c).length ≤ CHIP_RATE := by
    simp [leafInputs, List.length_map, List.length_finRange, CHIP_RATE]
    decide
  have hmem : (chipLookupTuple (leafInputs c) c.leafDigest).map (·.eval env.loc) ∈ tf .poseidon2 := by
    have := hsat.leafHashed
    unfold Lookup.holdsAt leafLookup at this
    exact this
  have h := chip_lookup_sound sponge (tf .poseidon2) hChip env.loc (leafInputs c) c.leafDigest hlen hmem
  rw [h, leafInputs_eval]
  rfl

/-- The direction BOOL value at a level (decoded from the boolean gate). -/
def dirBoolVal (c : CapOpenCols) (env : VmRowEnv) (lvl : Nat) : Bool :=
  env.loc (c.dir lvl) = 1

/-- A boolean dir column is `0` or `1`. -/
theorem dir_zero_or_one (c : CapOpenCols) (env : VmRowEnv) (lvl : Nat)
    (h : (dirBoolGate c lvl).eval env.loc = 0) :
    env.loc (c.dir lvl) = 0 ∨ env.loc (c.dir lvl) = 1 := by
  unfold dirBoolGate at h
  simp only [EmittedExpr.eval] at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · right; linarith

/-- Under a sound chip table, level `lvl`'s node column carries the genuine `nodeOf` of the mixed
`(cur, sib)` pair — exactly one `recomposeUp` step. -/
theorem node_sound (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hChip : ChipTableSound sponge (tf .poseidon2))
    (hsat : Satisfied sponge tf c env) (lvl : Nat) (hlvl : lvl < DEPTH) :
    env.loc (c.node lvl)
      = (if dirBoolVal c env lvl
          then nodeOf sponge (env.loc (c.sib lvl)) (env.loc (curCol c lvl))
          else nodeOf sponge (env.loc (curCol c lvl)) (env.loc (c.sib lvl))) := by
  have hlen : ([EmittedExpr.const FACT_MARK, leftExpr c lvl, rightExpr c lvl]).length ≤ CHIP_RATE := by
    show 3 ≤ CHIP_RATE
    rw [show CHIP_RATE = 8 from rfl]; omega
  have hmem : (chipLookupTuple [.const FACT_MARK, leftExpr c lvl, rightExpr c lvl] (c.node lvl)).map
      (·.eval env.loc) ∈ tf .poseidon2 := by
    have := hsat.nodeHashed lvl hlvl
    unfold Lookup.holdsAt nodeLookup at this
    exact this
  have h := chip_lookup_sound sponge (tf .poseidon2) hChip env.loc
    [.const FACT_MARK, leftExpr c lvl, rightExpr c lvl] (c.node lvl) hlen hmem
  rw [h]
  -- The absorbed list evaluates to `[FACT_MARK, leftVal, rightVal]`.
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval, leftExpr, rightExpr]
  -- Case on the direction bit.
  rcases dir_zero_or_one c env lvl (hsat.dirBool lvl hlvl) with hd0 | hd1
  · -- dir = 0 ⇒ cur is LEFT child ⇒ nodeOf cur sib.
    have hbool : dirBoolVal c env lvl = false := by
      simp only [dirBoolVal, hd0]; decide
    rw [hbool, hd0]
    simp only [Bool.false_eq_true, if_false]
    show sponge _ = nodeOf sponge _ _
    unfold nodeOf
    congr 1
    simp only [List.cons.injEq, and_true, true_and]
    constructor <;> ring
  · have hbool : dirBoolVal c env lvl = true := by
      simp only [dirBoolVal, hd1]; decide
    rw [hbool, hd1]
    simp only [if_true]
    show sponge _ = nodeOf sponge _ _
    unfold nodeOf
    congr 1
    simp only [List.cons.injEq, and_true, true_and]
    constructor <;> ring

/-! ## §6 — assembling the recompose: the node columns realize a `recomposeUp` path.

We read the `(sib, dir)` columns into a `Step` list and prove, by induction on the level count, that
folding `recomposeUp` from the leaf digest reproduces the TOP node column. The root pin then gives
`recomposeUp … = cap_root`, i.e. `MembersAt`. -/

/-- `recomposeUp` distributes over a path append: fold the prefix, then fold the suffix from there.
(`recomposeUp` is a left fold, so this is the standard `foldl_append`-shape decomposition.) -/
theorem recomposeUp_append (sponge : List ℤ → ℤ) (cur : ℤ) (p q : List Step) :
    recomposeUp sponge cur (p ++ q)
      = recomposeUp sponge (recomposeUp sponge cur p) q := by
  induction p generalizing cur with
  | nil => simp [recomposeUp]
  | cons s rest ih => simp only [List.cons_append, recomposeUp]; rw [ih]

/-- The membership path read off the row's columns: `(sib, dir)` for levels `[0, n)`. -/
def pathOf (c : CapOpenCols) (env : VmRowEnv) (n : Nat) : List Step :=
  (List.range n).map (fun lvl => { sib := env.loc (c.sib lvl), dir := dirBoolVal c env lvl })

/-- Folding `recomposeUp` over the first `n` levels reproduces `curCol c n` (the digest entering
level `n`), under chip soundness. The `cur` recurrence (`curCol c (l+1) = node l`) IS the fold step
that `node_sound` discharges. -/
theorem recompose_reaches_cur (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hChip : ChipTableSound sponge (tf .poseidon2))
    (hsat : Satisfied sponge tf c env) :
    ∀ n, n ≤ DEPTH →
      recomposeUp sponge (env.loc c.leafDigest) (pathOf c env n) = env.loc (curCol c n) := by
  intro n
  induction n with
  | zero => intro _; simp [pathOf, recomposeUp, curCol]
  | succ k ih =>
    intro hk
    have hkd : k < DEPTH := Nat.lt_of_succ_le hk
    have hkle : k ≤ DEPTH := Nat.le_of_lt hkd
    -- pathOf at k+1 = pathOf at k ++ [step k]
    have hpath : pathOf c env (k + 1)
        = pathOf c env k ++ [{ sib := env.loc (c.sib k), dir := dirBoolVal c env k }] := by
      simp [pathOf, List.range_succ, List.map_append]
    rw [hpath, recomposeUp_append, ih hkle]
    -- one more fold step from curCol c k, mixing (cur, sib) by dir.
    simp only [recomposeUp]
    have hns := node_sound sponge tf c env hChip hsat k hkd
    have hcur : curCol c (k + 1) = c.node k := rfl
    rw [hcur]
    cases hb : dirBoolVal c env k
    · simp only [hb, Bool.false_eq_true, if_false] at hns ⊢
      rw [hns]
    · simp only [hb, if_true] at hns ⊢
      rw [hns]

/-- **`capOpen_membership` — the in-circuit fold IS a `MembersAt` opening.** Under a sound chip
table, a `Satisfied` cap-membership row witnesses `DeployedCapTree.MembersAt sponge cap_root leaf`:
the depth-16 `(sib, dir)` path recomposes the committed `cap_root` from the genuine 7-field leaf
digest. THE in-circuit production of the membership the kernel bridge consumes. -/
theorem capOpen_membership (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hChip : ChipTableSound sponge (tf .poseidon2))
    (hsat : Satisfied sponge tf c env) :
    MembersAt sponge (env.loc c.capRoot) (leafOf c env) := by
  refine ⟨pathOf c env DEPTH, ?_⟩
  -- The fold over all DEPTH levels reaches curCol c DEPTH = node (DEPTH-1) = cap_root.
  have hfold := recompose_reaches_cur sponge tf c env hChip hsat DEPTH (le_refl _)
  -- Replace the leaf-digest column by the genuine capLeafDigest.
  have hleaf := leafDigest_sound sponge tf c env hChip hsat
  rw [hleaf] at hfold
  -- curCol c DEPTH = node (DEPTH-1).
  have hcurTop : curCol c DEPTH = c.node (DEPTH - 1) := rfl
  rw [hcurTop] at hfold
  -- root pin: node (DEPTH-1) = cap_root.
  have hpin := hsat.rootPinned
  unfold rootPinGate at hpin
  simp only [EmittedExpr.eval] at hpin
  have hroot : env.loc (c.node (DEPTH - 1)) = env.loc c.capRoot := by linarith
  rw [hfold, hroot]

/-! ## §7 — the leaf↔effect binding (target = src, write-mask). -/

/-- The target gate pins `leaf.target = src` (the `src` column). -/
theorem capOpen_target (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hsat : Satisfied sponge tf c env) :
    (leafOf c env).target = env.loc c.src := by
  have h := hsat.targetBound
  unfold targetBindGate at h
  simp only [EmittedExpr.eval] at h
  simp only [leafOf]
  linarith

/-- The write-mask gate pins `confersWriteLeaf leaf` (`mask_lo` is the read+write endpoint mask). -/
theorem capOpen_write (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hsat : Satisfied sponge tf c env) :
    confersWriteLeaf (leafOf c env) := by
  have h := hsat.writeMasked
  unfold writeMaskGate at h
  simp only [EmittedExpr.eval] at h
  unfold confersWriteLeaf
  simp only [leafOf]
  linarith

/-! ## §8 — THE KEYSTONE: `capOpen_sound` (Satisfied ⟹ MembersAt ∧ binding).

The deliverable. A `Satisfied` cap-membership row (against a sound chip table) PRODUCES the three
facts the kernel authority bridge consumes:
`MembersAt cap_root leaf ∧ leaf.target = src ∧ confersWriteLeaf leaf`. -/

/-- **`capOpen_sound`** — the in-circuit cap-membership row is SOUND: it opens the deployed cap-tree
at a write-mask leaf whose target is the turn's `src`. THE authority leg's circuit foundation. -/
theorem capOpen_sound (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hChip : ChipTableSound sponge (tf .poseidon2))
    (hsat : Satisfied sponge tf c env) :
    MembersAt sponge (env.loc c.capRoot) (leafOf c env)
    ∧ (leafOf c env).target = env.loc c.src
    ∧ confersWriteLeaf (leafOf c env) :=
  ⟨capOpen_membership sponge tf c env hChip hsat,
   capOpen_target sponge tf c env hsat,
   capOpen_write sponge tf c env hsat⟩

/-! ## §9 — CHAINING to the kernel `authorizedB` (the end-to-end authority leg).

Against the deployed commitment relation (`DeployedFaithful`), a satisfying cap-membership row whose
opened leaf is the faithfully-laid-down `(actor ⇒ src)` edge discharges the kernel `authorizedB` for
the turn. The membership the bridge demanded is now PRODUCED in-circuit. -/

/-- **`capOpen_authorizes` — THE END-TO-END AUTHORITY LEG.** GIVEN the deployed commitment
`DeployedFaithful caps cap_root leafAt`, a `Satisfied` cap-membership row whose opened leaf IS the
faithfulness contract's `(actor ⇒ src)` edge leaf — and whose `cap_root` column is the committed root,
whose `src` column is `src` — yields the kernel's `authorizedB caps ⟨actor, src, dst, amt⟩ = true`.
The in-circuit depth-16 binary-Merkle membership proof DISCHARGES the kernel's authority gate. -/
theorem capOpen_authorizes (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hChip : ChipTableSound sponge (tf .poseidon2))
    (hsat : Satisfied sponge tf c env)
    (caps : Caps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful sponge caps (env.loc c.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : env.loc c.src = (src : ℤ))
    (hedge : leafOf c env = leafAt actor src) :
    Dregg2.Exec.authorizedB caps
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hmem : MembersAt sponge (env.loc c.capRoot) (leafAt actor src) := by
    rw [← hedge]; exact capOpen_membership sponge tf c env hChip hsat
  have hwrite : confersWriteLeaf (leafAt actor src) := by
    rw [← hedge]; exact capOpen_write sponge tf c env hsat
  -- The opened leaf's target IS the turn's src (the leaf↔effect binding, authenticated).
  have htgt : (leafAt actor src).target = (src : ℤ) := by
    rw [← hedge, capOpen_target sponge tf c env hsat, hsrc]
  exact ⟨deployedCapOpen_implies_authorizedB sponge caps (env.loc c.capRoot) leafAt hfaith
    actor src dst amt hmem hwrite, htgt⟩

/-! ## §10 — NON-VACUITY: the constraint is satisfiable on a real opening, and the binding is REAL.

A witness-FALSE: with the write-mask gate failing (a non-write leaf), `capOpen_write` cannot fire — so
the conclusion `confersWriteLeaf` is not vacuously derivable. We pin the gate's discriminating power. -/

/-- **The write-mask gate is DISCRIMINATING (witness FALSE).** A leaf whose `mask_lo` is NOT the
write-endpoint mask makes the `writeMaskGate` non-zero — the constraint is UNSATISFIABLE for it, so
`capOpen_write` is not vacuous (it genuinely requires the committed write mask). -/
theorem writeMaskGate_discriminates (c : CapOpenCols) (env : VmRowEnv)
    (hbad : env.loc (c.leaf 3) = rightsMaskOf (Cap.endpoint 0 [Auth.read, Auth.write]) + 1) :
    (writeMaskGate c).eval env.loc ≠ 0 := by
  unfold writeMaskGate
  simp only [EmittedExpr.eval, hbad]
  intro h; linarith

/-- **The target gate is DISCRIMINATING (witness FALSE).** A leaf whose `target` differs from the
`src` column makes the `targetBindGate` non-zero — the binding genuinely authenticates the ACTOR's
write-cap over `src`, not an arbitrary leaf. -/
theorem targetBindGate_discriminates (c : CapOpenCols) (env : VmRowEnv)
    (hne : env.loc (c.leaf 1) ≠ env.loc c.src) :
    (targetBindGate c).eval env.loc ≠ 0 := by
  unfold targetBindGate
  simp only [EmittedExpr.eval]
  intro h
  apply hne
  linarith

/-! ## §11 — Axiom hygiene. -/

#assert_axioms leafDigest_sound
#assert_axioms node_sound
#assert_axioms recompose_reaches_cur
#assert_axioms capOpen_membership
#assert_axioms capOpen_sound
#assert_axioms capOpen_authorizes
#assert_axioms writeMaskGate_discriminates
#assert_axioms targetBindGate_discriminates

end Dregg2.Circuit.DeployedCapOpen
