/-
# Dregg2.Circuit.DeployedCapOpen — the IN-CIRCUIT cap-tree membership-open (authority leg foundation).

## Why this file exists (the critical-path authority leg)

`DeployedCapTree.lean` models the deployed 7-field depth-16 cap-tree (now committed to the SINGLE
chip absorb `cap_root.rs::cap_chip_absorb` — the arity-7 leaf + the arity-3 `[FACT_MARK, l, r]` node,
over the one `chipAbsorb` carrier) and proves the KERNEL-side bridge
`deployedCapOpen_implies_authorizedB`: a write-mask `MembersAt` opening implies the kernel's
`authorizedB`. But that bridge consumes `MembersAt` as a HYPOTHESIS — nothing in the circuit
denotation produced it.

This file closes that gap on the CIRCUIT side. It defines a CONSTRAINT — `CapOpenConstraint` — whose
denotation is exactly the in-circuit shape the Rust AIR realizes:

  * the 7 cap-leaf fields ride a Poseidon2 chip ABSORB (arity 7) producing the leaf digest column;
  * each of the depth-16 levels rides an arity-3 chip absorb (the tagged 3-list `[FACT_MARK, l, r]`)
    mixing `(cur, sib)` by the direction bit; the chain's top is CONSTRAINED `== cap_root` column;
  * the leaf's `target` column is CONSTRAINED `== src`, and `mask_lo` to the write-endpoint mask.

## The chip-rate reconciliation (DISCHARGED — decision #1, the gap CLOSED, §A)

The IR-v2 Poseidon2 chip (`DescriptorIR2`, `CHIP_RATE = babyBearD4W16.rate = 8`) realizes ONE rate-8
absorb of the lookup tuple: `chip_lookup_sound` enforces `digest = sponge (inputs.eval)` where
`sponge` is the chip's rate-8 list-hash. The deployed cap primitives are NOW the SAME single chip
absorb (`cap_root.rs::cap_chip_absorb`, mirrored in `DeployedCapTree`):

  * the leaf `capLeafDigest S = S.chipAbsorb ∘ leafFields` — ONE chip absorb of the 7 fields (arity 7);
  * the node `nodeOf S l r = S.chipAbsorb (packNode l r)` — ONE chip absorb of `[FACT_MARK, l, r]`
    (arity 3).

So the chip's `sponge (leafFields)` IS `capLeafDigest S leaf` and `sponge [FACT_MARK, l, r]` IS
`nodeOf S l r` — definitionally — when `sponge := S.chipAbsorb`. The reconciliation `SchemeRealizedBy
Chip sponge S` is therefore PROVABLE (`chipAbsorb_realizes`, §A): the chip genuinely realizes the
deployed cap hash now. The membership/soundness theorems specialize `sponge := S.chipAbsorb` and
DISCHARGE the bridge internally — it is no longer a carried hypothesis. (The named relation is kept as
documentation of the equations the realization satisfies.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR enters ONLY as the named
`CapHashScheme` carrier (`chipAbsorb`/`chipCR`, inherited from `DeployedCapTree`) + the chip-soundness
`ChipTableSound`.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.CapMerkleGeneric

namespace Dregg2.Circuit.DeployedCapOpen

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily TableId Lookup chipLookupTuple ChipTableSound chip_lookup_sound CHIP_RATE
   chipLookupTupleN ChipTableSoundN chip_lookup_sound_N)
open Dregg2.Circuit.DeployedCapTree
  (CapLeaf FACT_MARK leafFields packNode CapHashScheme Digest8 Cap8Scheme)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme
  (capLeafDigest8 nodeOf8 recomposeUp8 pack8 MembersAt8 DeployedFaithful8 DeployedFaithfulEff8
   deployedCapOpen8_implies_authorizedB deployedCapOpen8_implies_authorizedEffB
   deployedFaithfulEff_canonical8)
open Dregg2.Circuit.CapMerkleGeneric (StepG recomposeG)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (confersTransferLeaf confersLeaf maskOfLimbs facetOfLeaf tierOfTag capLeafDigest nodeOf)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (rightsMaskOf)
open Dregg2.Authority (Cap Auth Caps Label)
open Dregg2.Exec.FacetAuthority
  (AuthTier AuthProvided FacetCaps EffectMask EFFECT_TRANSFER isEffectPermitted authorizedFacetB
   authorizedFacetEffB)

set_option autoImplicit false

/-! ## §0 — the chip↔scheme realization bridge (NOW DISCHARGED — the chip IS the cap hash).

The chip's rate-8 `sponge : List ℤ → ℤ` realizes the deployed scheme `S` exactly when its single
absorb of the leaf-field list reproduces `capLeafDigest`, and its single absorb of `[FACT_MARK, l, r]`
reproduces `nodeOf`. Since the deployed scheme NOW commits exactly the chip absorb (`capLeafDigest S =
S.chipAbsorb ∘ leafFields`, `nodeOf S l r = S.chipAbsorb (packNode l r)`), the chip whose `sponge` is
`S.chipAbsorb` satisfies both equations DEFINITIONALLY — see `chipAbsorb_realizes` (§A). -/

/-- **`SchemeRealizedByChip sponge S`** — the chip's rate-8 list-hash `sponge` reproduces the deployed
cap scheme `S`'s leaf and node digests. With the cap-tree re-committed to the chip absorb, this is
DISCHARGED by `sponge := S.chipAbsorb` (`chipAbsorb_realizes`), not carried. (Kept as a named record
of the realization equations; `packNode S l r = [FACT_MARK, l, r]` is the chip's node block.) -/
structure SchemeRealizedByChip {State : Type} (sponge : List ℤ → ℤ) (S : CapHashScheme State) : Prop where
  /-- The chip's 7-field absorb reproduces the deployed leaf digest. -/
  leafRealized : ∀ l : CapLeaf, sponge (leafFields l) = capLeafDigest S l
  /-- The chip's `[FACT_MARK, l, r]` absorb reproduces the deployed node digest. -/
  nodeRealized : ∀ l r : ℤ, sponge (packNode l r) = nodeOf S l r

/-- **`chipAbsorb_realizes` — THE DISCHARGE.** The chip whose `sponge` is the deployed scheme's own
`chipAbsorb` carrier realizes `S`: both equations hold by `rfl` (`capLeafDigest`/`nodeOf` ARE
`S.chipAbsorb` of their input blocks). This is decision #1 made good — the cap-tree is re-committed to
the one in-circuit hash, so the chip genuinely realizes it. -/
theorem chipAbsorb_realizes {State : Type} (S : CapHashScheme State) :
    SchemeRealizedByChip S.chipAbsorb S :=
  { leafRealized := fun _ => rfl
  , nodeRealized := fun _ _ => rfl }

/-! ## §1 — the column plan for one cap-membership row.

(The COLUMN LAYOUT and the chip LOOKUPS are exactly what the Rust AIR realizes; with the cap-tree
re-committed to the chip absorb, the digest the chip soundness yields IS the deployed scheme's
`capLeafDigest`/`nodeOf` — no reconciliation step, the bridge discharges by `rfl`.) -/

/-- The deployed cap-tree depth (`cap_root.rs::CAP_TREE_DEPTH = 16`). -/
def DEPTH : Nat := 16

/-- The number of felts in a native cap-tree digest (`cap_root.rs::CAP_DIGEST_W = 8`). A leaf-digest /
node / root is an 8-COLUMN GROUP (Phase H-CAP-8), faithful to the FRI ~124-bit floor. -/
def CAP_W : Nat := 8

/-- The column layout for a cap-membership row. All indices abstract `Nat`; the Rust AIR pins them.
Phase H-CAP-8: `leafDigest`, `sib`, `node`, `capRoot` are 8-COLUMN GROUPS (`Fin 8 → Nat`) carrying
the native 8-felt digest; the 7 spare permutation lanes per absorb are PROMOTED into the bound 8-felt
fold (no `lanes` existential — the whole `node8` block is committed). -/
structure CapOpenCols where
  /-- The 7 leaf-field columns, in `CapLeaf` order (scalar leaf inputs, unchanged at 1-felt). -/
  leaf       : Fin 7 → Nat
  /-- The 8-felt leaf-digest column GROUP (the arity-7 chip absorb's 8 squeezed lanes). -/
  leafDigest : Fin 8 → Nat
  /-- The 8-felt sibling-digest column GROUP at each level. -/
  sib        : Nat → Fin 8 → Nat
  /-- The direction-bit column at each level (0 ⇒ cur is LEFT child). -/
  dir        : Nat → Nat
  /-- The 8-felt node-output column GROUP at each level (the arity-16 `node8` compression's 8 lanes). -/
  node       : Nat → Fin 8 → Nat
  /-- The committed 8-felt `cap_root` column GROUP. -/
  capRoot    : Fin 8 → Nat
  /-- The turn's source-cell-id column. -/
  src        : Nat
  /-- **(residual (a)) The turn's ACTUAL effect-kind bit column** — the `EFFECT_<kind>` the turn
  performs (a single `1 <<< n` bit). The general facet gate `facetEffGate` binds the leaf's `mask_lo`
  to THIS column (not the constant `EFFECT_TRANSFER`), so the cap-open authorizes the turn's genuine
  effect. The deployed transfer descriptor commits `EFFECT_TRANSFER` here (byte-faithful). -/
  effBit     : Nat
  /-- **(residual (a) — GENUINE MEMBERSHIP) The 16-bit decomposition of the leaf's low mask limb.**
  `bit i` is the boolean column carrying bit `i` of `mask_lo` (`i < MASK_BITS = 16`). The membership
  gate `facetEffGate` is NOT an equality `mask_lo == effBit`; it is the genuine `(effBit &&& mask_lo) =
  effBit` SUBMASK test, enforced soundly in-circuit by: booleaning each `bit i` (`maskBitBoolGate`),
  reconstructing `mask_lo = Σ bitᵢ·2ⁱ` (`maskReconGate`), and gating the SELECTED bit (bit `n`, where
  `effBit = 1 <<< n`) to `1` (`facetEffGate` ≡ the selected-bit clause). A BROAD honest cap
  (`mask_lo = 0xFFFF`, all 16 facets) decomposes with bit `n` set, so it PERMITS the effect — the
  over-strict equality gate it replaces would reject it. -/
  bit        : Nat → Nat

/-! ## §2 — the leaf-field accessors (decode the 7 leaf columns to a `CapLeaf`). -/

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

/-- The leaf inputs evaluate to exactly the `leafFields` of the decoded leaf. -/
theorem leafInputs_eval (c : CapOpenCols) (env : VmRowEnv) :
    (leafInputs c).map (·.eval env.loc) = leafFields (leafOf c env) := by
  simp only [leafInputs, List.map_map, leafFields]
  rfl

/-! ## §3 — the chip-lookup tuples (leaf absorb + per-level `node8` absorb), now 8-felt wide. -/

/-- **`capPermOut S8`** — the WIDE permutation output the cap chip realizes: the 8 squeezed lanes of
`S8.chipAbsorb8`, read as a `List ℤ` (`cap_root.rs::chip_absorb_all_lanes`). `capPermOut S8 (leafFields
l) = List.ofFn (capLeafDigest8 S8 l)` and `capPermOut S8 (pack8 l r) = List.ofFn (nodeOf8 S8 l r)` — by
`rfl` (both are `List.ofFn ∘ chipAbsorb8` of their input blocks). The `permOut` the wide lever binds. -/
def capPermOut (S8 : Cap8Scheme) : List ℤ → List ℤ := fun xs => List.ofFn (S8.chipAbsorb8 xs)

/-- Read an 8-felt column GROUP `g : Fin 8 → Nat` as the ordered list of its 8 column indices. -/
def digestCols (g : Fin 8 → Nat) : List Nat := (List.finRange 8).map g

/-- The 8-felt leaf-digest chip lookup tuple: absorb the 7 leaf-field columns, output = the 8 bound
leaf-digest columns (the whole `node8` leaf block, NOT just out0). -/
def leafLookup (c : CapOpenCols) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN (leafInputs c) (digestCols c.leafDigest) }

/-- The 8-felt `cur` digest GROUP entering level `lvl`: the leaf digest at level 0, else the previous
node group. -/
def curCol (c : CapOpenCols) : Nat → (Fin 8 → Nat)
  | 0       => c.leafDigest
  | (l + 1) => c.node l

/-- The `node8` LEFT input lane `i` at level `lvl`: `(1-dir)·cur_i + dir·sib_i`. -/
def leftExpr (c : CapOpenCols) (lvl : Nat) (i : Fin 8) : EmittedExpr :=
  .add (.mul (.add (.const 1) (.mul (.const (-1)) (.var (c.dir lvl)))) (.var (curCol c lvl i)))
       (.mul (.var (c.dir lvl)) (.var (c.sib lvl i)))

/-- The `node8` RIGHT input lane `i` at level `lvl`: `(1-dir)·sib_i + dir·cur_i`. -/
def rightExpr (c : CapOpenCols) (lvl : Nat) (i : Fin 8) : EmittedExpr :=
  .add (.mul (.add (.const 1) (.mul (.const (-1)) (.var (c.dir lvl)))) (.var (c.sib lvl i)))
       (.mul (.var (c.dir lvl)) (.var (curCol c lvl i)))

/-- The arity-16 `node8` input block at level `lvl`: `leftExpr lanes 0..7 ‖ rightExpr lanes 0..7`,
mirroring `cap_root.rs::cap_node8`'s `pack8 left8 right8` (`ins[..8] = L8; ins[8..] = R8`). -/
def nodeInputs (c : CapOpenCols) (lvl : Nat) : List EmittedExpr :=
  (List.finRange 8).map (leftExpr c lvl) ++ (List.finRange 8).map (rightExpr c lvl)

/-- The 8-felt node chip lookup tuple at level `lvl`: absorb the arity-16 `node8` block, output = the
8 bound node columns (the whole `node8` compression, faithful to ~124-bit). -/
def nodeLookup (c : CapOpenCols) (lvl : Nat) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN (nodeInputs c lvl) (digestCols (c.node lvl)) }

/-! ## §4 — the gate equations (booleanity, root pin, leaf↔effect binding). -/

/-- `dir` is boolean: `dir·(dir-1) = 0`. -/
def dirBoolGate (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .mul (.var (c.dir lvl)) (.add (.var (c.dir lvl)) (.const (-1)))

/-- The root pin at lane `i`: the TOP node output lane equals the committed `cap_root` lane. The 8-felt
root pin is the CONJUNCTION over all 8 lanes (`rootPinned` in `Satisfied` quantifies `∀ i`) — the
GENTIAN tooth: a colliding cap tree (same lane-0, different `node8` fold top) fails ≥1 lane pin. -/
def rootPinGate (c : CapOpenCols) (i : Fin 8) : EmittedExpr :=
  .add (.var (c.node (DEPTH - 1) i)) (.mul (.const (-1)) (.var (c.capRoot i)))

/-- The target binding: `leaf.target - src = 0`. -/
def targetBindGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 1)) (.mul (.const (-1)) (.var c.src))

/-- **`transferFacetGate`** (THE CUTOVER, FacetAuthority §10(C)) — the FACET binding: it pins the
leaf's low mask limb to `EFFECT_TRANSFER` and the high limb to `0`, so the decoded facet `maskOfLimbs
mask_lo mask_hi = EFFECT_TRANSFER` permits the `EFFECT_TRANSFER` bit (`facet.rs:123`). This REPLACES the
toy `writeMaskGate` (`mask_lo == write-mask`). Two equations as one zero-pinned sum is impossible, so
we pin `mask_lo` here and `mask_hi` in `facetHiGate`. -/
def transferFacetGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 3)) (.const (-(EFFECT_TRANSFER)))

/-! ### residual (a) — the GENUINE SUBMASK-MEMBERSHIP facet gate (NOT an equality).

The kernel predicate is `is_effect_permitted(Some m, bit) = (bit &&& m ≠ 0)` (`facet.rs:123`) — a
SUBMASK/membership test over the FULL `EffectMask` `m`, NOT equality. For a single effect bit `effBit =
1 <<< n`, that is exactly "bit `n` of `m` is set". The decoded facet is `m = maskOfLimbs mask_lo mask_hi
= mask_lo + mask_hi·65536` (the full u32 effect mask). The over-strict equality `mask_lo == effBit` it
replaces rejects every honest BROAD cap; this membership accepts any cap whose bit `n` is set — AND it
does NOT pin `mask_hi = 0` (a broad cap `EFFECT_ALL` has `mask_hi = 0xFFFF`, bit 1 still in `mask_lo`).

We enforce the membership soundly via a 32-bit decomposition of the FULL mask `m`:
  (1) booleanity — each `bit i` is `0` or `1` (`maskBitBoolGate`);
  (2) recomposition — `maskOfLimbs mask_lo mask_hi = Σ_{i<32} bitᵢ·2ⁱ` (`maskReconGate`), binding the
      bits to the committed FULL mask (both limbs);
  (3) the SELECTED-bit gate — bit `n` is `1` (`facetEffGate` / `selectedBitGate n`), where `n =
      log2 effBit` is the descriptor's compile-time effect index.
Bit `n` set + the recomposition ⟹ `(2ⁿ &&& m) = 2ⁿ ≠ 0`, i.e. the genuine `isEffectPermitted`. -/

/-- The width of the FULL `EffectMask` bit decomposition (a deployed `u32` — `EFFECT_ALL =
0xFFFF_FFFF`). The decoded facet `maskOfLimbs mask_lo mask_hi = mask_lo + mask_hi·65536` is the full
32-bit mask, so the decomposition spans all 32 bits: any deployed effect-kind bit `1 <<< n` (`n < 32`,
up to `EFFECT_ATTENUATE_CAPABILITY = 1 <<< 23`) is selectable, AND a broad cap (`EFFECT_ALL`, mask_hi =
0xFFFF) decomposes fully. The Rust twin is `CAP_OPEN_MASK_BITS`. -/
def MASK_BITS : Nat := 32

/-- The bit-weighted reconstruction `Σ_{i<W} bitᵢ·2ⁱ` of the full mask from its bit columns
(an `EmittedExpr` over the `bit` columns). The `maskReconGate` pins `maskOfLimbs mask_lo mask_hi` to this. -/
def reconMaskExpr (c : CapOpenCols) : Nat → EmittedExpr
  | 0     => .const 0
  | n + 1 => .add (reconMaskExpr c n) (.mul (.var (c.bit n)) (.const ((2 ^ n : Nat) : ℤ)))

/-- The Nat reconstruction `Σ_{i<W} bᵢ·2ⁱ` (the value the `EmittedExpr` reconstruction evaluates to,
cast to `ℤ`, when the bit columns are boolean). -/
def reconMaskN (b : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => reconMaskN b n + b n * 2 ^ n

/-- A boolean reconstruction over `[0,W)` is `< 2^W` (each bit contributes at most its weight). -/
theorem reconMaskN_lt (b : Nat → Nat) (W : Nat) (hb : ∀ i, i < W → b i = 0 ∨ b i = 1) :
    reconMaskN b W < 2 ^ W := by
  induction W with
  | zero => simp [reconMaskN]
  | succ w ih =>
    have ihw := ih (fun i hi => hb i (Nat.lt_succ_of_lt hi))
    unfold reconMaskN
    have hbw : b w ≤ 1 := by rcases hb w (Nat.lt_succ_self w) with h | h <;> omega
    have hle : b w * 2 ^ w ≤ 2 ^ w := by
      calc b w * 2 ^ w ≤ 1 * 2 ^ w := Nat.mul_le_mul_right _ hbw
        _ = 2 ^ w := by ring
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [pow_succ]; ring
    omega

/-- **`reconMaskN_testBit`** — bit `k` of the boolean reconstruction over `[0,W)` is exactly `b k`
(`k < W`). The load-bearing digit lemma: the recomposition `mask_lo = Σ bᵢ2ⁱ` makes the committed
mask's bit `k` READABLE as the carrier `b k`. -/
theorem reconMaskN_testBit (b : Nat → Nat) (W : Nat) (hb : ∀ i, i < W → b i = 0 ∨ b i = 1)
    (k : Nat) (hk : k < W) : (reconMaskN b W).testBit k = (b k == 1) := by
  induction W with
  | zero => omega
  | succ w ih =>
    have ihw := ih (fun i hi => hb i (Nat.lt_succ_of_lt hi))
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · unfold reconMaskN
      rw [show reconMaskN b w + b w * 2 ^ w = 2 ^ w * b w + reconMaskN b w by ring]
      rw [Nat.testBit_two_pow_mul_add (b w)
        (reconMaskN_lt b w (fun i hi => hb i (Nat.lt_succ_of_lt hi))) k]
      simp only [hlt, if_true]; exact ihw hlt
    · subst heq
      unfold reconMaskN
      rw [show reconMaskN b k + b k * 2 ^ k = 2 ^ k * b k + reconMaskN b k by ring]
      rw [Nat.testBit_two_pow_mul_add (b k)
        (reconMaskN_lt b k (fun i hi => hb i (Nat.lt_succ_of_lt hi))) k]
      simp only [Nat.lt_irrefl, if_false, Nat.sub_self]
      rcases hb k (Nat.lt_succ_self k) with h0 | h1
      · rw [h0]; decide
      · rw [h1]; decide

/-- The `EmittedExpr` reconstruction evaluates to the Nat reconstruction (cast to `ℤ`) of the bit
columns' `toNat`, when those columns are boolean over `[0,W)`. -/
theorem reconMaskExpr_eval (c : CapOpenCols) (env : VmRowEnv) (W : Nat)
    (hbit : ∀ i, i < W → env.loc (c.bit i) = 0 ∨ env.loc (c.bit i) = 1) :
    (reconMaskExpr c W).eval env.loc
      = ((reconMaskN (fun i => (env.loc (c.bit i)).toNat) W : Nat) : ℤ) := by
  induction W with
  | zero => simp [reconMaskExpr, reconMaskN, EmittedExpr.eval]
  | succ w ih =>
    have ihw := ih (fun i hi => hbit i (Nat.lt_succ_of_lt hi))
    simp only [reconMaskExpr, reconMaskN, EmittedExpr.eval, ihw]
    push_cast
    rcases hbit w (Nat.lt_succ_self w) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp

/-- **`maskBitBoolGate c i`** — bit `i` of the full mask is boolean: `bitᵢ·(bitᵢ − 1) = 0`. -/
def maskBitBoolGate (c : CapOpenCols) (i : Nat) : EmittedExpr :=
  .mul (.var (c.bit i)) (.add (.var (c.bit i)) (.const (-1)))

/-- **`maskReconGate c`** — the recomposition gate: `maskOfLimbs mask_lo mask_hi − Σ_{i<32} bitᵢ·2ⁱ =
0`, i.e. `(mask_lo + mask_hi·65536) − Σ bitᵢ·2ⁱ = 0`, binding the 32-bit decomposition to the committed
FULL `EffectMask` (both limbs). No `mask_hi = 0` pin is needed — the decode is the genuine full mask. -/
def maskReconGate (c : CapOpenCols) : EmittedExpr :=
  .add (.add (.var (c.leaf 3)) (.mul (.const 65536) (.var (c.leaf 4))))
       (.mul (.const (-1)) (reconMaskExpr c MASK_BITS))

/-! ### PER-16-BIT-LIMB reconstruction — the MASK-RECON-WRAP FIX (verdict A, deployed soundness gap #2).

`maskReconGate` binds `mask_lo + mask_hi·65536 = Σ_{i<32} bitᵢ·2ⁱ` only mod `p`, and `2p = 0xF0000002 <
2^32`, so a `p`-shifted 32-bit boolean decomposition of the committed mask (`M+p`, `M+2p`) ALSO vanishes
mod `p` with DIFFERENT bits — a capability-authorization forgery (a cap granting nothing can flip a
`selectedBit`). Narrowing is unavailable (`EFFECT_ALL = 0xFFFFFFFF ≥ p` is a legitimate mask). The FIX
reconstructs EACH 16-bit limb from its OWN 16 bits: `mask_lo = Σ_{i<16} bitᵢ·2ⁱ` and `mask_hi = Σ_{i<16}
bit_{16+i}·2ⁱ`. Each limb sum is `< 2^16 < p`, so the mod-`p` limb gate + cell canonicality (`0 ≤ mask_lo,
mask_hi < p`) pins the limb EXACTLY (residual in `(−p, p)`) — a GENUINE `mask_lo, mask_hi < 2^16` range
check with NO `p`-shift possible (`mask_lo + p > 2^16` fails it). The full 32-bit `maskReconGate` is then a
DERIVED consequence (`maskReconGate_of_limbs`), not an assumed carrier: `reconExact` is discharged. -/

/-- The per-limb bit width (`MASK_BITS = 2·MASK_LIMB_BITS`). -/
def MASK_LIMB_BITS : Nat := 16

/-- The bit-weighted reconstruction of the LIMB whose bits start at column offset `off`:
`Σ_{i<n} bit_{off+i}·2ⁱ` (an `EmittedExpr`). The low limb is `reconLimbExpr c 0 16`, the high limb
`reconLimbExpr c 16 16`. -/
def reconLimbExpr (c : CapOpenCols) (off : Nat) : Nat → EmittedExpr
  | 0     => .const 0
  | n + 1 => .add (reconLimbExpr c off n) (.mul (.var (c.bit (off + n))) (.const ((2 ^ n : Nat) : ℤ)))

/-- The Nat limb reconstruction `Σ_{i<n} b_{off+i}·2ⁱ`. -/
def reconLimbN (b : Nat → Nat) (off : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => reconLimbN b off n + b (off + n) * 2 ^ n

/-- A boolean limb reconstruction over `[off, off+W)` is `< 2^W` — the RANGE that makes the mod-`p`
limb gate exact (`2^16 < p`, so no `p`-shift). -/
theorem reconLimbN_lt (b : Nat → Nat) (off W : Nat)
    (hb : ∀ i, i < W → b (off + i) = 0 ∨ b (off + i) = 1) : reconLimbN b off W < 2 ^ W := by
  induction W with
  | zero => simp [reconLimbN]
  | succ w ih =>
    have ihw := ih (fun i hi => hb i (Nat.lt_succ_of_lt hi))
    unfold reconLimbN
    have hbw : b (off + w) ≤ 1 := by rcases hb w (Nat.lt_succ_self w) with h | h <;> omega
    have hle : b (off + w) * 2 ^ w ≤ 2 ^ w := by
      calc b (off + w) * 2 ^ w ≤ 1 * 2 ^ w := Nat.mul_le_mul_right _ hbw
        _ = 2 ^ w := by ring
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [pow_succ]; ring
    omega

/-- The `EmittedExpr` limb reconstruction evaluates to the Nat limb reconstruction (cast to `ℤ`),
when the limb's bit columns are boolean. -/
theorem reconLimbExpr_eval (c : CapOpenCols) (env : VmRowEnv) (off W : Nat)
    (hbit : ∀ i, i < W → env.loc (c.bit (off + i)) = 0 ∨ env.loc (c.bit (off + i)) = 1) :
    (reconLimbExpr c off W).eval env.loc
      = ((reconLimbN (fun i => (env.loc (c.bit i)).toNat) off W : Nat) : ℤ) := by
  induction W with
  | zero => simp [reconLimbExpr, reconLimbN, EmittedExpr.eval]
  | succ w ih =>
    have ihw := ih (fun i hi => hbit i (Nat.lt_succ_of_lt hi))
    simp only [reconLimbExpr, reconLimbN, EmittedExpr.eval, ihw]
    push_cast
    rcases hbit w (Nat.lt_succ_self w) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp

/-- **`maskReconLoGate c`** (the FIX) — the LOW-limb recomposition: `mask_lo − Σ_{i<16} bitᵢ·2ⁱ = 0`.
The sum is `< 2^16 < p`, so with `mask_lo` canonical (`< p`) the mod-`p` gate pins `mask_lo = Σ`
EXACTLY — a genuine `mask_lo < 2^16` range check; no `p`-shift. -/
def maskReconLoGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 3)) (.mul (.const (-1)) (reconLimbExpr c 0 MASK_LIMB_BITS))

/-- **`maskReconHiGate c`** (the FIX) — the HIGH-limb recomposition: `mask_hi − Σ_{i<16} bit_{16+i}·2ⁱ =
0`. Same per-limb range argument on the high 16 bit columns (`< 2^16 < p`). -/
def maskReconHiGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 4)) (.mul (.const (-1)) (reconLimbExpr c MASK_LIMB_BITS MASK_LIMB_BITS))

/-- `reconMaskExpr` splits at any offset `a`: the top `k` bits are a `reconLimbExpr` at offset `a`,
weighted by `2^a`. The structural fact behind `maskReconGate_of_limbs`. -/
theorem reconMaskExpr_add (c : CapOpenCols) (env : VmRowEnv) (a k : Nat) :
    (reconMaskExpr c (a + k)).eval env.loc
      = (reconMaskExpr c a).eval env.loc
        + (2 ^ a : ℤ) * (reconLimbExpr c a k).eval env.loc := by
  induction k with
  | zero => simp [reconLimbExpr, EmittedExpr.eval]
  | succ m ih =>
    have e1 : (reconMaskExpr c (a + (m + 1))).eval env.loc
        = (reconMaskExpr c (a + m)).eval env.loc
          + env.loc (c.bit (a + m)) * ((2 ^ (a + m) : Nat) : ℤ) := by
      show (reconMaskExpr c ((a + m) + 1)).eval env.loc = _
      simp only [reconMaskExpr, EmittedExpr.eval]
    have e2 : (reconLimbExpr c a (m + 1)).eval env.loc
        = (reconLimbExpr c a m).eval env.loc + env.loc (c.bit (a + m)) * ((2 ^ m : Nat) : ℤ) := by
      simp only [reconLimbExpr, EmittedExpr.eval]
    rw [e1, e2, ih]
    push_cast [pow_add]
    ring

/-- **`reconMask32_split`** — the full 32-bit reconstruction IS the low limb plus `2^16·` the high limb.
Both limbs read their own 16 bit columns, so pinning each limb pins the whole mask. -/
theorem reconMask32_split (c : CapOpenCols) (env : VmRowEnv) :
    (reconMaskExpr c MASK_BITS).eval env.loc
      = (reconLimbExpr c 0 MASK_LIMB_BITS).eval env.loc
        + (65536 : ℤ) * (reconLimbExpr c MASK_LIMB_BITS MASK_LIMB_BITS).eval env.loc := by
  have h1 : (reconMaskExpr c (MASK_LIMB_BITS + MASK_LIMB_BITS)).eval env.loc
      = (reconMaskExpr c MASK_LIMB_BITS).eval env.loc
        + (2 ^ MASK_LIMB_BITS : ℤ) * (reconLimbExpr c MASK_LIMB_BITS MASK_LIMB_BITS).eval env.loc :=
    reconMaskExpr_add c env MASK_LIMB_BITS MASK_LIMB_BITS
  have h0 : (reconMaskExpr c MASK_LIMB_BITS).eval env.loc
      = (reconLimbExpr c 0 MASK_LIMB_BITS).eval env.loc := by
    have h := reconMaskExpr_add c env 0 MASK_LIMB_BITS
    simpa [reconMaskExpr, EmittedExpr.eval, Nat.zero_add] using h
  have hbits : MASK_BITS = MASK_LIMB_BITS + MASK_LIMB_BITS := rfl
  rw [hbits, h1, h0]
  norm_num [MASK_LIMB_BITS]

/-- **`maskReconGate_of_limbs` — THE DISCHARGE.** The full 32-bit `maskReconGate` is DERIVED from the two
16-bit limb gates: if `mask_lo = Σ_{i<16} bitᵢ·2ⁱ` and `mask_hi = Σ_{i<16} bit_{16+i}·2ⁱ` (both exact over
ℤ), then `(mask_lo + mask_hi·65536) − Σ_{i<32} bitᵢ·2ⁱ = 0`. `reconExact` is no longer assumed — it FOLLOWS
from the two in-circuit per-limb range checks. -/
theorem maskReconGate_of_limbs (c : CapOpenCols) (env : VmRowEnv)
    (hlo : (maskReconLoGate c).eval env.loc = 0)
    (hhi : (maskReconHiGate c).eval env.loc = 0) :
    (maskReconGate c).eval env.loc = 0 := by
  have hsplit := reconMask32_split c env
  simp only [maskReconLoGate, EmittedExpr.eval] at hlo
  simp only [maskReconHiGate, EmittedExpr.eval] at hhi
  simp only [maskReconGate, EmittedExpr.eval, hsplit]
  linarith [hlo, hhi]

/-- **`maskReconLoGate_rejects_wrap` — THE FORGERY WITNESS (soundness, witness FALSE).** The MASK-RECON-WRAP
attack committed a `p`-shifted 32-bit decomposition (bits summing to `M + k·p`, `k ∈ {1,2}`, `2p < 2^32`)
whose low bits carry a value DIFFERENT from the honest `mask_lo` — flipping a `selectedBit` for an effect
the cap does NOT grant. The per-limb FIX kills it in the FIELD: if the committed `mask_lo` is canonical
(`< p`) and the low 16 bit-columns are boolean but their reconstruction `v` DIFFERS from `mask_lo` (which
any `p`-shifted decomposition forces, since `v < 2^16 ≤ mask_lo + p`), then the low-limb gate does NOT
vanish mod `p` — `mask_lo − v ∈ (−2^16, p)` is a nonzero non-multiple of `p`. The forged row is UNSAT. (The
high limb is symmetric.) -/
theorem maskReconLoGate_rejects_wrap (c : CapOpenCols) (env : VmRowEnv)
    (hlo : 0 ≤ env.loc (c.leaf 3) ∧ env.loc (c.leaf 3) < 2013265921)
    (hbits : ∀ i, i < MASK_LIMB_BITS → env.loc (c.bit (0 + i)) = 0 ∨ env.loc (c.bit (0 + i)) = 1)
    (hne : env.loc (c.leaf 3)
        ≠ ((reconLimbN (fun j => (env.loc (c.bit j)).toNat) 0 MASK_LIMB_BITS : Nat) : ℤ)) :
    ¬ ((maskReconLoGate c).eval env.loc ≡ 0 [ZMOD 2013265921]) := by
  intro h
  have hval := reconLimbExpr_eval c env 0 MASK_LIMB_BITS hbits
  have hlt := reconLimbN_lt (fun j => (env.loc (c.bit j)).toNat) 0 MASK_LIMB_BITS
    (fun k hk => by rcases hbits k hk with hh | hh <;> simp only [Nat.zero_add] at hh <;> simp [hh])
  have h16 : (2 : Nat) ^ MASK_LIMB_BITS = 65536 := by norm_num [MASK_LIMB_BITS]
  rw [h16] at hlt
  unfold maskReconLoGate at h
  simp only [EmittedExpr.eval] at h
  rw [hval] at h
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨q, hq⟩ := h
  have hvlt : ((reconLimbN (fun j => (env.loc (c.bit j)).toNat) 0 MASK_LIMB_BITS : Nat) : ℤ) < 65536 := by
    exact_mod_cast hlt
  have hvnn : (0 : ℤ) ≤ ((reconLimbN (fun j => (env.loc (c.bit j)).toNat) 0 MASK_LIMB_BITS : Nat) : ℤ) :=
    Int.natCast_nonneg _
  apply hne
  omega

/-- **`facetEffGate`** (residual (a) — the GENUINE membership SELECTED-bit gate, parametric in the
effect index). For a single effect bit `effBit = 1 <<< n`, the kernel predicate `(effBit &&& m) ≠ 0`
(over the full mask `m = maskOfLimbs mask_lo mask_hi`) is exactly "bit `n` of `m` is set".
`selectedBitGate c n` pins `bitₙ − 1 = 0` (bit `n` is `1`). Together with `maskBitBoolGate`/`maskReconGate`
(the bits decode the committed FULL mask), this yields the genuine in-circuit `isEffectPermitted
(facetOfLeaf leaf) (1<<<n) = true` — and a cap whose bit `n` is CLEAR makes the gate UNSAT
(`facetEffGate_rejects_wrong_facet`). This REPLACES the over-strict equality `mask_lo == effBit` (which
rejected every honest BROAD cap) AND the `mask_hi = 0` pin (which rejected EFFECT_ALL caps). -/
def selectedBitGate (c : CapOpenCols) (n : Nat) : EmittedExpr :=
  .add (.var (c.bit n)) (.const (-1))

/-- The transfer instance: `facetEffGate` selects bit `1` (`EFFECT_TRANSFER = 1 <<< 1`). -/
def facetEffGate (c : CapOpenCols) : EmittedExpr := selectedBitGate c 1

/-- **`effBitGate`** (residual (a)) — pins the committed effect-bit column `effBit` to the constant
`EFFECT_TRANSFER` FOR THE TRANSFER cap-open descriptor (so the prover cannot put an arbitrary effect bit
in the column). The descriptor for a DIFFERENT effect-kind pins its OWN bit here. Together with
`facetEffGate` (`mask_lo = effBit`) this yields the genuine in-circuit `isEffectPermitted` against the
turn's effect: for transfer the chain is `mask_lo = effBit = EFFECT_TRANSFER`, byte-identical to
`transferFacetGate`, but the FACET is now bound to a committed effect column, not a literal constant. -/
def effBitGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var c.effBit) (.const (-(EFFECT_TRANSFER)))

/-- The high-limb pin: `leaf.mask_hi = 0` (so `maskOfLimbs mask_lo mask_hi = mask_lo`). -/
def facetHiGate (c : CapOpenCols) : EmittedExpr :=
  .var (c.leaf 4)

/-- **`authTagGate`** (THE CUTOVER, FacetAuthority §10(C)) — the TIER binding: it pins the leaf's
`auth_tag` to the `Signature` tier byte `1` (`tierOfTag 1 = .signature`, satisfiable by a provided
signature). The tier-off-the-leaf generality (any committed `auth_tag`) is the NAMED §10 residual; here
the in-circuit row binds a concrete satisfiable tier. -/
def authTagGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 2)) (.const (-1))

/-! ## §5 — `Satisfied`: the full per-row denotation of one cap-membership constraint. -/

/-- **`Satisfied sponge tf c env`** — the cap-membership row is satisfied. The in-circuit denotation
the Rust `CapMembership` AIR realizes (the chip lookups + the base gates). -/
structure Satisfied (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) : Prop where
  /-- The leaf-digest chip absorb is a chip-table row. -/
  leafHashed : (leafLookup c).holdsAt tf env
  /-- Each level's node absorb is a chip-table row. -/
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  /-- Each level's direction column is boolean. -/
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  /-- Every lane of the top node output equals the committed cap_root lane (the 8-felt root pin). -/
  rootPinned : ∀ i : Fin 8, (rootPinGate c i).eval env.loc = 0
  /-- The leaf's target equals the turn's src. -/
  targetBound : (targetBindGate c).eval env.loc = 0
  /-- The leaf's `mask_lo` is `EFFECT_TRANSFER` (the facet permits TRANSFER). -/
  facetTransfer : (transferFacetGate c).eval env.loc = 0
  /-- The leaf's `mask_hi` is `0` (so the decoded facet is exactly `mask_lo`). -/
  facetHiZero : (facetHiGate c).eval env.loc = 0
  /-- The leaf's `auth_tag` is the `Signature` tier byte (satisfiable by a provided signature). -/
  tierTagged : (authTagGate c).eval env.loc = 0
  /-- **(residual (a))** The committed effect-bit column `effBit` is `EFFECT_TRANSFER` (the transfer
  descriptor pins its effect; a different effect's descriptor pins its own bit). -/
  effBitTransfer : (effBitGate c).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP)** Each `mask_lo` bit column is boolean. -/
  maskBitsBool : ∀ i < MASK_BITS, (maskBitBoolGate c i).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP, FIXED)** The low 16-bit decomposition reconstructs `mask_lo`
  (a per-limb range check: the sum is `< 2^16 < p`, so this pins `mask_lo` exactly). -/
  maskReconLo : (maskReconLoGate c).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP, FIXED)** The high 16-bit decomposition reconstructs `mask_hi`. -/
  maskReconHi : (maskReconHiGate c).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP)** The SELECTED bit (`EFFECT_TRANSFER`'s bit 1) is set —
  the genuine `(EFFECT_TRANSFER &&& mask_lo) ≠ 0` submask, NOT the over-strict equality. -/
  facetEffBound : (facetEffGate c).eval env.loc = 0

/-- **`MembershipCore sponge tf c env`** — the four fields the 8-felt Merkle fold consumes: the leaf
absorb, the per-level `node8` absorbs, direction-booleanity, and the (8-lane) root pin. Both `Satisfied`
and `SatisfiedEff` carry these; the digest-soundness lemmas + `capOpen_membership8` consume ONLY this. -/
structure MembershipCore (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) : Prop where
  leafHashed : (leafLookup c).holdsAt tf env
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  rootPinned : ∀ i : Fin 8, (rootPinGate c i).eval env.loc = 0

/-- A `Satisfied` row provides the membership core. -/
def Satisfied.toCore {sponge tf c env} (h : Satisfied sponge tf c env) :
    MembershipCore sponge tf c env :=
  ⟨h.leafHashed, h.nodeHashed, h.dirBool, h.rootPinned⟩

/-! ## §6 — soundness: the leaf-digest column carries the genuine `capLeafDigest`.

The chip enforces `leafDigest = sponge (leafFields)` with `sponge := S.chipAbsorb` — and the deployed
`capLeafDigest S = S.chipAbsorb ∘ leafFields`, so the two coincide (the realization is `chipAbsorb_
realizes`, discharged in place). -/

/-- Read an 8-felt column GROUP `g : Fin 8 → Nat` as the `Digest8` its columns carry under `env`. -/
def groupVal (env : VmRowEnv) (g : Fin 8 → Nat) : Digest8 := fun i => env.loc (g i)

/-- The 8 digest columns read under `env` ARE `List.ofFn (groupVal env g)` — the bridge between the
wide lever's `digestCols.map a` conclusion and the `Digest8` carrier the cap scheme folds. -/
theorem digestCols_map (g : Fin 8 → Nat) (env : VmRowEnv) :
    (digestCols g).map env.loc = List.ofFn (groupVal env g) := by
  unfold digestCols groupVal
  rw [List.map_map, List.ofFn_eq_map]
  rfl

/-- **`leafDigest_sound8`** — under a SOUND WIDE chip table (the chip's 8-felt squeeze IS the deployed
`capPermOut S8`), the 8 leaf-digest columns carry the genuine native-8-felt `capLeafDigest8 S8 (leafOf
c env)`. The whole 8-felt block is bound (the wide lever forces every lane), not just out0. -/
theorem leafDigest_sound8 (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hcore : MembershipCore sponge tf c env) :
    groupVal env c.leafDigest = capLeafDigest8 S8 (leafOf c env) := by
  have hlen : (leafInputs c).length ≤ CHIP_RATE := by
    simp [leafInputs, List.length_map, List.length_finRange, CHIP_RATE]
  have hmem : (chipLookupTupleN (leafInputs c) (digestCols c.leafDigest)).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.leafHashed
    unfold Lookup.holdsAt leafLookup at this
    exact this
  have h := chip_lookup_sound_N (capPermOut S8) (tf .poseidon2) hChip env.loc (leafInputs c)
    (digestCols c.leafDigest) hlen hmem
  rw [digestCols_map, leafInputs_eval] at h
  -- `capPermOut S8 (leafFields ·) = List.ofFn (capLeafDigest8 S8 ·)` by `rfl`.
  have hreal : capPermOut S8 (leafFields (leafOf c env))
      = List.ofFn (capLeafDigest8 S8 (leafOf c env)) := rfl
  rw [hreal] at h
  exact List.ofFn_inj.mp h

/-- The direction BOOL value at a level. -/
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

/-- The arity-16 `node8` input block at level `lvl` evaluates to `pack8 left8 right8`, where `left8`/
`right8` are the per-lane dir-mixed `cur8`/`sib8` 8-felt vectors. The dir-case split: `false` ⇒ `(cur,
sib)`, `true` ⇒ `(sib, cur)` — exactly `cap_root.rs::cap_node8`'s child order. -/
theorem nodeInputs_eval (c : CapOpenCols) (env : VmRowEnv) (lvl : Nat)
    (hd : env.loc (c.dir lvl) = 0 ∨ env.loc (c.dir lvl) = 1) :
    (nodeInputs c lvl).map (·.eval env.loc)
      = (if dirBoolVal c env lvl
          then pack8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))
          else pack8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := by
  -- generic: the 16-list eval IS `pack8 mixL mixR` whenever the lane evals match `mixL`/`mixR`.
  have key : ∀ (mixL mixR : Digest8),
      (∀ i, (leftExpr c lvl i).eval env.loc = mixL i) →
      (∀ i, (rightExpr c lvl i).eval env.loc = mixR i) →
      (nodeInputs c lvl).map (·.eval env.loc) = pack8 mixL mixR := by
    intro mixL mixR hL hR
    unfold nodeInputs pack8
    rw [List.map_append, List.ofFn_eq_map, List.ofFn_eq_map]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [List.map_map]; exact List.map_congr_left (fun i _ => hL i)
    · rw [List.map_map]; exact List.map_congr_left (fun i _ => hR i)
  rcases hd with hd0 | hd1
  · have hbool : dirBoolVal c env lvl = false := by simp only [dirBoolVal, hd0]; decide
    rw [hbool]; simp only [Bool.false_eq_true, if_false]
    exact key (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))
      (fun i => by simp only [leftExpr, EmittedExpr.eval, groupVal]; rw [hd0]; ring)
      (fun i => by simp only [rightExpr, EmittedExpr.eval, groupVal]; rw [hd0]; ring)
  · have hbool : dirBoolVal c env lvl = true := by simp only [dirBoolVal, hd1]; decide
    rw [hbool]; simp only [if_true]
    exact key (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))
      (fun i => by simp only [leftExpr, EmittedExpr.eval, groupVal]; rw [hd1]; ring)
      (fun i => by simp only [rightExpr, EmittedExpr.eval, groupVal]; rw [hd1]; ring)

/-- **`node_sound8`** — under a SOUND WIDE chip table, level `lvl`'s 8 node columns carry the genuine
native-8-felt `nodeOf8 S8` of the dir-mixed `(cur8, sib8)` pair — exactly one `recomposeUp8` step at
full ~124-bit width. The whole `node8` block is bound (all 8 lanes), not lane-0. -/
theorem node_sound8 (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hcore : MembershipCore sponge tf c env) (lvl : Nat) (hlvl : lvl < DEPTH) :
    groupVal env (c.node lvl)
      = (if dirBoolVal c env lvl
          then nodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))
          else nodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := by
  have hlen : (nodeInputs c lvl).length ≤ CHIP_RATE := by
    simp [nodeInputs, List.length_append, List.length_map, List.length_finRange, CHIP_RATE]
  have hmem : (chipLookupTupleN (nodeInputs c lvl) (digestCols (c.node lvl))).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.nodeHashed lvl hlvl
    unfold Lookup.holdsAt nodeLookup at this
    exact this
  have h := chip_lookup_sound_N (capPermOut S8) (tf .poseidon2) hChip env.loc (nodeInputs c lvl)
    (digestCols (c.node lvl)) hlen hmem
  rw [digestCols_map, nodeInputs_eval c env lvl (dir_zero_or_one c env lvl (hcore.dirBool lvl hlvl))] at h
  -- `capPermOut S8 (pack8 l r) = List.ofFn (nodeOf8 S8 l r)` by `rfl`; peel the `if` either way.
  cases hb : dirBoolVal c env lvl
  · simp only [hb, Bool.false_eq_true, if_false] at h ⊢
    have hreal : capPermOut S8 (pack8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl)))
        = List.ofFn (nodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h
  · simp only [hb, if_true] at h ⊢
    have hreal : capPermOut S8 (pack8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl)))
        = List.ofFn (nodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h

/-! ## §7 — assembling the recompose: the node columns realize a `recomposeUp` path. -/

/-- `recomposeUp8` distributes over a path append (over the generic `recomposeG` spine). -/
theorem recomposeUp8_append (S8 : Cap8Scheme) (cur : Digest8) (p q : List (StepG Digest8)) :
    recomposeUp8 S8 cur (p ++ q) = recomposeUp8 S8 (recomposeUp8 S8 cur p) q := by
  show recomposeG (nodeOf8 S8) cur (p ++ q)
     = recomposeG (nodeOf8 S8) (recomposeG (nodeOf8 S8) cur p) q
  induction p generalizing cur with
  | nil => rfl
  | cons s rest ih => simp only [List.cons_append, recomposeG]; rw [ih]

/-- The 8-felt membership path read off the row's columns: `(sib8, dir)` for levels `[0, n)`. -/
def pathOf8 (c : CapOpenCols) (env : VmRowEnv) (n : Nat) : List (StepG Digest8) :=
  (List.range n).map (fun lvl => { sib := groupVal env (c.sib lvl), dir := dirBoolVal c env lvl })

/-- Folding `recomposeUp8` over the first `n` levels reproduces `curCol c n` (as a `Digest8`), under
the WIDE chip soundness — the native 8-felt fold. -/
theorem recompose_reaches_cur8 (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hcore : MembershipCore sponge tf c env) :
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
    rw [hpath, recomposeUp8_append, ih hkle]
    simp only [recomposeUp8, recomposeG]
    have hns := node_sound8 S8 sponge tf c env hChip hcore k hkd
    have hcur : curCol c (k + 1) = c.node k := rfl
    rw [hcur]
    cases hb : dirBoolVal c env k
    · simp only [hb, Bool.false_eq_true, if_false] at hns ⊢
      rw [hns]
    · simp only [hb, if_true] at hns ⊢
      rw [hns]

/-- **`capOpen_membership8` — the in-circuit 8-felt fold IS a `MembersAt8` opening.** Under a SOUND
WIDE chip table (the chip's 8-felt squeeze IS `capPermOut S8`), a `Satisfied` row witnesses `MembersAt8
S8 cap_root leaf` against the FULL 8-felt root — the GENTIAN-tooth-real membership leg. -/
theorem capOpen_membership8 (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hcore : MembershipCore sponge tf c env) :
    MembersAt8 S8 (groupVal env c.capRoot) (leafOf c env) := by
  refine ⟨pathOf8 c env DEPTH, ?_⟩
  have hfold := recompose_reaches_cur8 S8 sponge tf c env hChip hcore DEPTH (le_refl _)
  have hleaf := leafDigest_sound8 S8 sponge tf c env hChip hcore
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

/-! ## §8 — the leaf↔effect binding (target = src, write-mask). -/

/-- The target gate pins `leaf.target = src`. -/
theorem capOpen_target (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hsat : Satisfied sponge tf c env) :
    (leafOf c env).target = env.loc c.src := by
  have h := hsat.targetBound
  unfold targetBindGate at h
  simp only [EmittedExpr.eval] at h
  simp only [leafOf]
  linarith

/-- **`capOpen_confers`** (THE CUTOVER) — the facet + tier gates pin the FAITHFUL two-axis
`confersTransferLeaf vkOfTag .signature leaf`: the decoded facet (`maskOfLimbs mask_lo mask_hi =
EFFECT_TRANSFER`) permits the TRANSFER bit, and the decoded tier (`tierOfTag auth_tag = .signature`,
since `auth_tag = 1`) is satisfied by a provided signature. Holds for ANY `vkOfTag` (the tag is `1`,
not the `Custom` byte `5`). -/
theorem capOpen_confers (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (vkOfTag : ℤ → Nat) (hsat : Satisfied sponge tf c env) :
    confersTransferLeaf vkOfTag .signature (leafOf c env) := by
  have hlo := hsat.facetTransfer
  have hhi := hsat.facetHiZero
  have htag := hsat.tierTagged
  unfold transferFacetGate at hlo
  unfold facetHiGate at hhi
  unfold authTagGate at htag
  simp only [EmittedExpr.eval] at hlo hhi htag
  -- decode: mask_lo = EFFECT_TRANSFER, mask_hi = 0, auth_tag = 1.
  have hmlo : (leafOf c env).mask_lo = EFFECT_TRANSFER := by simp only [leafOf]; linarith
  have hmhi : (leafOf c env).mask_hi = 0 := by simp only [leafOf]; exact hhi
  have htg : (leafOf c env).auth_tag = 1 := by simp only [leafOf]; linarith
  unfold confersTransferLeaf facetOfLeaf maskOfLimbs
  rw [hmlo, hmhi, htg]
  refine ⟨?_, ?_⟩
  · -- facet: maskOfLimbs EFFECT_TRANSFER 0 = EFFECT_TRANSFER permits EFFECT_TRANSFER.
    show isEffectPermitted (some (EFFECT_TRANSFER + (0 : ℤ) * 65536).toNat) EFFECT_TRANSFER = true
    decide
  · -- tier: tierOfTag vkOfTag 1 = .signature, satisfied by a provided signature (by rfl).
    show (tierOfTag vkOfTag 1).isSatisfiedBy .signature = true
    rfl

/-! ## §8.G — F6: the cap-open confers the GENERAL tier × facet (decoded, not pinned).

`capOpen_confers` above discharges `confersTransferLeaf … .signature` because the live descriptor's
`authTagGate` pins `auth_tag = 1` (Signature) and `transferFacetGate` pins `mask_lo = EFFECT_TRANSFER`.
F6 generalizes BOTH axes OFF THE COMMITTED LEAF:

  * **the TIER** (`§10` named residual) — instead of concluding the constant `.signature`, decode the
    committed `auth_tag` to `tierOfTag vkOfTag auth_tag` and conclude `confersTransferLeaf` for THAT
    tier against any `provided` the off-circuit AuthContext supplies that satisfies it. No `auth_tag`
    pin needed: the tier is GENUINELY read off the committed byte.
  * **the FACET** — `facetOfLeaf` already decodes the genuine `maskOfLimbs mask_lo mask_hi`; the
    general gate checks `isEffectPermitted` of the decoded mask against the turn's effect bit, rather
    than pinning the mask to a TRANSFER constant.

So `capOpen_confers_decoded` concludes `confersLeaf` for the GENERAL `(effectBit, provided)` from the
committed leaf, given only that the decoded facet permits `effectBit` and the decoded tier is
satisfied by `provided` — both read off the COMMITTED row, not pinned. -/

/-- **`capOpen_confers_decoded` (F6) — the cap-open confers the GENERAL tier × facet, DECODED.** From
a `Satisfied` row (the in-circuit membership open) plus the two facts read off the COMMITTED leaf —
the decoded facet `facetOfLeaf` permits `effectBit`, and the decoded tier `tierOfTag auth_tag` is
satisfied by `provided` — the leaf confers `effectBit` authority under `provided` (`confersLeaf`). The
tier is the GENUINE committed byte (NOT the Signature constant the `authTagGate` pins); the facet is
the GENUINE decoded `maskOfLimbs` (NOT the TRANSFER constant). This discharges the §10 tier residual:
the cap-open authorizes the general tier × facet, off the committed leaf. -/
theorem capOpen_confers_decoded (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (hfacet : isEffectPermitted (facetOfLeaf (leafOf c env)) effectBit = true)
    (htier : (tierOfTag vkOfTag (leafOf c env).auth_tag).isSatisfiedBy provided = true) :
    confersLeaf vkOfTag provided effectBit (leafOf c env) :=
  ⟨hfacet, htier⟩

/-! ## §8.E — residual (a): the IN-CIRCUIT GENERAL FACET gate (`facetEffGate`, not the constant pin).

`capOpen_confers`/`Satisfied.facetTransfer` pin `mask_lo = EFFECT_TRANSFER` — a CONSTANT, so the cap-open
only ever authorizes the transfer facet. `facetEffGate` instead binds `mask_lo` to the turn's ACTUAL
effect-bit COLUMN `effBit`. The lemma below shows that gate IS a genuine in-circuit `isEffectPermitted`:
if `facetEffGate` holds (`mask_lo = env.effBit`), `facetHiGate` holds (`mask_hi = 0`), and the committed
`effBit` is a nonzero single effect bit `1 <<< n`, then the decoded facet PERMITS that effect — and a
leaf whose `mask_lo` is any OTHER value fails the gate (the wrong-facet rejection). This is the genuine
facet generalization: the binding is against a committed column, not a constant. -/

/-- **`facetEffGate_permits` (residual (a) — the in-circuit general `isEffectPermitted`, GENUINE
SUBMASK over the FULL mask).** Given the genuine membership data — each mask bit column boolean
(`hboolGate`), the 32-bit decomposition reconstructing the FULL mask `maskOfLimbs mask_lo mask_hi`
(`hrecon`), and the SELECTED bit `n` set (`hsel`, `n < 32`) — the leaf's DECODED facet PERMITS the
effect bit `1 <<< n`: `isEffectPermitted (facetOfLeaf leaf) (1 <<< n) = true`. This is the genuine
`(2ⁿ &&& m) ≠ 0` SUBMASK membership over the full mask `m`: bit `n` of the committed full mask is set, so
a BROAD honest cap (`EFFECT_ALL`, mask_hi = 0xFFFF) PERMITS the effect — NO `mask_hi = 0` pin is required
(the decode is the genuine full mask), and the over-strict equality gate this replaces would reject it. -/
theorem facetEffGate_permits (c : CapOpenCols) (env : VmRowEnv) (n : Nat) (hn : n < MASK_BITS)
    (hboolGate : ∀ i, i < MASK_BITS → (maskBitBoolGate c i).eval env.loc = 0)
    (hrecon : (maskReconGate c).eval env.loc = 0)
    (hsel : env.loc (c.bit n) = 1) :
    isEffectPermitted (facetOfLeaf (leafOf c env)) (1 <<< n) = true := by
  -- each bit column is boolean, from the per-bit boolean gate `bitᵢ·(bitᵢ − 1) = 0`.
  have hbool : ∀ i, i < MASK_BITS → env.loc (c.bit i) = 0 ∨ env.loc (c.bit i) = 1 := by
    intro i hi
    have h := hboolGate i hi
    unfold maskBitBoolGate at h
    simp only [EmittedExpr.eval] at h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  -- the bit decomposition recomposes the FULL mask `maskOfLimbs mask_lo mask_hi` (as a Nat, cast to ℤ).
  set bN : Nat → Nat := fun i => (env.loc (c.bit i)).toNat with hbN
  have hbNbool : ∀ i, i < MASK_BITS → bN i = 0 ∨ bN i = 1 := by
    intro i hi
    rcases hbool i hi with h0 | h1
    · left; simp [hbN, h0]
    · right; simp [hbN, h1]
  -- the full mask is nonneg (it IS the Nat reconstruction cast to ℤ), so its `.toNat` round-trips.
  have hmask : maskOfLimbs (leafOf c env).mask_lo (leafOf c env).mask_hi
      = ((reconMaskN bN MASK_BITS : Nat) : ℤ) := by
    have hr := hrecon
    unfold maskReconGate at hr
    simp only [EmittedExpr.eval] at hr
    rw [reconMaskExpr_eval c env MASK_BITS hbool] at hr
    unfold maskOfLimbs
    simp only [leafOf]; linarith
  -- the decoded facet is `some (reconMaskN bN 32)` (the full mask's `.toNat`).
  have hdec : facetOfLeaf (leafOf c env) = some (reconMaskN bN MASK_BITS) := by
    unfold facetOfLeaf
    rw [hmask]; simp
  rw [hdec]
  -- bit n of the reconstruction is set.
  have hbn : bN n = 1 := by simp [hbN, hsel]
  have htb : (reconMaskN bN MASK_BITS).testBit n = true := by
    rw [reconMaskN_testBit bN MASK_BITS hbNbool n hn, hbn]; decide
  -- 1<<<n = 2^n; the genuine submask `2^n &&& mask_lo ≠ 0`.
  have hpow : (1 <<< n : Nat) = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hand : (1 <<< n) &&& (reconMaskN bN MASK_BITS) ≠ 0 := by
    rw [hpow]
    intro hz
    have := Nat.testBit_and (2 ^ n) (reconMaskN bN MASK_BITS) n
    rw [hz] at this
    simp [Nat.testBit_two_pow_self, htb] at this
  have hm0 : reconMaskN bN MASK_BITS ≠ 0 := by
    intro hz; rw [hz] at htb; simp at htb
  -- discharge `isEffectPermitted (some m) (1<<<n)`: the `some m` branch with m ≠ 0.
  unfold isEffectPermitted
  cases hm : reconMaskN bN MASK_BITS with
  | zero => exact absurd hm hm0
  | succ k => simp only [hm] at hand ⊢; simp [hand]

/-- **`facetEffGate_rejects_wrong_facet` (residual (a) — the WRONG-FACET tooth, witness FALSE, GENUINE
SUBMASK).** If the cap's mask bit `n` is CLEAR (the carrier `bitₙ = 0`, i.e. the cap does NOT permit the
effect-kind `1 <<< n`), then the SELECTED-bit gate `selectedBitGate c n` does NOT hold (`bitₙ − 1 = −1 ≠
0`) — the in-circuit binding REJECTS a cap whose facet does not carry the turn's effect bit. This is the
genuine membership bite: not "mask_lo ≠ effBit" but "the selected facet bit is unset". -/
theorem facetEffGate_rejects_wrong_facet (c : CapOpenCols) (env : VmRowEnv) (n : Nat)
    (hclear : env.loc (c.bit n) = 0) :
    (selectedBitGate c n).eval env.loc ≠ 0 := by
  unfold selectedBitGate
  simp only [EmittedExpr.eval, hclear]
  intro h; linarith

/-- **`capOpen_confers_via_effGate` (residual (a) — the LIVE general facet, transfer instance).** A
`Satisfied` row confers `EFFECT_TRANSFER` via the GENERAL facet path: the `effBitGate` pins the committed
effect-bit column to `EFFECT_TRANSFER = 1 <<< 1`, the `facetEffGate` binds `mask_lo` to that column, and
`facetEffGate_permits` then yields the genuine in-circuit `isEffectPermitted (facetOfLeaf leaf)
EFFECT_TRANSFER`. The TIER leg is the decoded `auth_tag`. So the cap-open confers the transfer effect
through a facet gate bound to a COMMITTED effect column, not the constant `EFFECT_TRANSFER`. -/
theorem capOpen_confers_via_effGate (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (vkOfTag : ℤ → Nat) (provided : AuthProvided) (hsat : Satisfied sponge tf c env)
    (htier : (tierOfTag vkOfTag (leafOf c env).auth_tag).isSatisfiedBy provided = true) :
    confersLeaf vkOfTag provided EFFECT_TRANSFER (leafOf c env) := by
  -- the SELECTED bit (transfer = bit 1) is set, from `facetEffGate = selectedBitGate 1`.
  have hsel : env.loc (c.bit 1) = 1 := by
    have h := hsat.facetEffBound
    unfold facetEffGate selectedBitGate at h
    simp only [EmittedExpr.eval] at h
    linarith
  have hperm : isEffectPermitted (facetOfLeaf (leafOf c env)) (1 <<< 1) = true :=
    facetEffGate_permits c env 1 (by decide) hsat.maskBitsBool
      (maskReconGate_of_limbs c env hsat.maskReconLo hsat.maskReconHi) hsel
  have hbit : (1 <<< 1 : Nat) = EFFECT_TRANSFER := by unfold EFFECT_TRANSFER; norm_num
  rw [hbit] at hperm
  exact ⟨hperm, htier⟩

/-! ## §9 — THE KEYSTONE: `capOpen_sound` (Satisfied ⟹ MembersAt ∧ binding). -/

/-- **`capOpen_sound`** — the in-circuit cap-membership row is SOUND: it opens the deployed cap-tree
at a write-mask leaf whose target is the turn's `src`. THE authority leg's circuit foundation. The
`SchemeRealizedByChip` chip↔scheme bridge is DISCHARGED (the chip's hash IS `S.chipAbsorb`, by
`chipAbsorb_realizes`) — no longer a carried hypothesis. -/
theorem capOpen_sound (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (vkOfTag : ℤ → Nat)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hsat : Satisfied sponge tf c env) :
    MembersAt8 S8 (groupVal env c.capRoot) (leafOf c env)
    ∧ (leafOf c env).target = env.loc c.src
    ∧ confersTransferLeaf vkOfTag .signature (leafOf c env) :=
  ⟨capOpen_membership8 S8 sponge tf c env hChip hsat.toCore,
   capOpen_target sponge tf c env hsat,
   capOpen_confers sponge tf c env vkOfTag hsat⟩

/-! ## §10 — CHAINING to the kernel `authorizedB` (the end-to-end authority leg). -/

/-- **`capOpen_authorizes` — THE END-TO-END AUTHORITY LEG.** GIVEN the deployed commitment, a
`Satisfied` row whose opened leaf IS the faithfulness contract's `(actor ⇒ src)` edge leaf yields the
kernel's `authorizedB = true`. The `SchemeRealizedByChip` bridge is DISCHARGED (`chipAbsorb_realizes`)
— the chip genuinely realizes the cap hash. -/
theorem capOpen_authorizes (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (vkOfTag : ℤ → Nat)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hsat : Satisfied sponge tf c env)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful8 S8 vkOfTag .signature caps (groupVal env c.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : env.loc c.src = (src : ℤ))
    (hedge : leafOf c env = leafAt actor src) :
    authorizedFacetB caps .signature
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hmem : MembersAt8 S8 (groupVal env c.capRoot) (leafAt actor src) := by
    rw [← hedge]; exact capOpen_membership8 S8 sponge tf c env hChip hsat.toCore
  have hconf : confersTransferLeaf vkOfTag .signature (leafAt actor src) := by
    rw [← hedge]; exact capOpen_confers sponge tf c env vkOfTag hsat
  have htgt : (leafAt actor src).target = (src : ℤ) := by
    rw [← hedge, capOpen_target sponge tf c env hsat, hsrc]
  exact ⟨deployedCapOpen8_implies_authorizedB S8 vkOfTag .signature caps (groupVal env c.capRoot) leafAt hfaith
    actor src dst amt hmem hconf, htgt⟩

/-- **`capOpen_authorizes_tierGeneral` (F6) — THE END-TO-END AUTHORITY LEG, GENERAL TIER.** The
generalization of `capOpen_authorizes` from the pinned `.signature` tier to ANY `provided` auth that
satisfies the tier DECODED off the committed leaf (`tierOfTag vkOfTag leaf.auth_tag`). The cap-open's
facet gate still binds the transfer facet (the kernel `authorizedFacetB` is over `turnEffectBit =
EFFECT_TRANSFER`), but the TIER is now the GENUINE committed `auth_tag` byte — NOT the Signature
constant the `authTagGate` pins. This discharges the §10 tier residual end-to-end: a cap-open whose
leaf commits ANY tier (None/Signature/Proof/Either/Impossible/Custom) authorizes exactly when the
off-circuit auth satisfies that committed tier. (`capOpen_authorizes` is the `.signature` instance,
recovered when `auth_tag = 1` and `provided = .signature`.) -/
theorem capOpen_authorizes_tierGeneral (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hsat : Satisfied sponge tf c env)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful8 S8 vkOfTag provided caps (groupVal env c.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : env.loc c.src = (src : ℤ))
    (hedge : leafOf c env = leafAt actor src)
    -- the off-circuit auth satisfies the tier DECODED off the committed leaf (not a constant).
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hmem : MembersAt8 S8 (groupVal env c.capRoot) (leafAt actor src) := by
    rw [← hedge]; exact capOpen_membership8 S8 sponge tf c env hChip hsat.toCore
  -- the facet leg is read off the COMMITTED (decoded) mask; the tier leg is the committed `auth_tag`.
  have hfacet : isEffectPermitted (facetOfLeaf (leafAt actor src)) EFFECT_TRANSFER = true := by
    rw [← hedge]; exact (capOpen_confers sponge tf c env vkOfTag hsat).1
  have hconf : confersTransferLeaf vkOfTag provided (leafAt actor src) := ⟨hfacet, htier⟩
  have htgt : (leafAt actor src).target = (src : ℤ) := by
    rw [← hedge, capOpen_target sponge tf c env hsat, hsrc]
  exact ⟨deployedCapOpen8_implies_authorizedB S8 vkOfTag provided caps (groupVal env c.capRoot) leafAt hfaith
    actor src dst amt hmem hconf, htgt⟩

/-! ## §A — THE CHIP-RATE GAP IS CLOSED (`SchemeRealizedByChip` DISCHARGED, not carried).

Decision #1: the cap-tree is re-committed to the chip's hash (`cap_root.rs::cap_chip_absorb`,
mirrored as `DeployedCapTree`'s single `chipAbsorb` carrier). So the chip whose `sponge` is
`S.chipAbsorb` realizes the deployed scheme DEFINITIONALLY — `chipAbsorb_realizes` (§0) supplies it,
and every soundness theorem above specializes `sponge := S.chipAbsorb` and discharges the bridge in
place. There is NO carried `SchemeRealizedByChip` hypothesis on the live path anymore.

The realization is NON-VACUOUS in the load-bearing sense: it is the chip-absorb collision-resistance
`S.chipCR` (a `Compress1CR`, primitive #4 — NOT `True`; a constant compression falsifies it) that
makes the membership leg's anti-ghost (`recomposeUp_inj_of_path`, `nodeOf_injective`,
`capLeafDigest_injective`) bite. We re-state the discharge as the headline fact, and pin that the
node and leaf domains are length-disjoint (the chip's per-row arity seeding that lets one `chipAbsorb`
serve both shapes). -/

/-- **THE DISCHARGE, re-stated as the §A headline.** The deployed scheme's own chip-absorb carrier
realizes the scheme — `SchemeRealizedByChip S.chipAbsorb S` holds (both equations by `rfl`). The
chip-rate gap the prior revision carried is CLOSED: the IR-v2 chip genuinely realizes the cap hash. -/
theorem schemeRealizedByChip_discharged {State : Type} (S : CapHashScheme State) :
    SchemeRealizedByChip S.chipAbsorb S :=
  chipAbsorb_realizes S

/-- The node block `packNode l r = [FACT_MARK, l, r]` (length 3) and any leaf-field block `leafFields
leaf` (length 7) are LENGTH-DISJOINT — the structural fact behind the chip serving both arities from
one `chipAbsorb` (the chip seeds by `(arity, padded inputs)`, so the two shapes never alias). -/
theorem node_leaf_length_disjoint (l r : ℤ) (leaf : CapLeaf) :
    (packNode l r).length ≠ (leafFields leaf).length := by
  simp [packNode, leafFields]

/-! ## §10.E — THE EFFECT-GENERAL CAP-OPEN (fan-out: any cap-authorized effect-kind, not just transfer).

`Satisfied`/`capOpen_authorizes` PIN the facet to `EFFECT_TRANSFER` (via `effBitGate`/`transferFacetGate`/
`authTagGate` constants), so they only ever authorize a TRANSFER-facet, Signature-tier cap. The fan-out to
the OTHER cap-authorized effects (delegate, introduce, grantCap, revoke, refreshDelegation, …) reuses the
WHOLE appendix verbatim EXCEPT the `effBitGate` constant: each effect's cap-open pins its OWN `EFFECT_<kind>`
bit `1 <<< n` in the `effBit` column, and the GENERAL `facetEffGate` binds `mask_lo = effBit`, so the cap
must permit THAT effect-kind. This section generalizes the gate by the bit exponent `n` and proves the
effect-general authority bridge into `authorizedFacetEffB … (1 <<< n)`.

The membership leg (`MembersAt`) and the target leg (`leaf.target = src`) are SHARED with `Satisfied` — they
read no effect-bit column. We factor them as a membership CORE (`MembershipCore`) that both `Satisfied` and
`SatisfiedEff` provide, so `capOpen_membership`/`capOpen_target` are restated over the core and reused. -/

/-- **`membershipCore_opens` — the core IS a `MembersAt8` opening** (the 8-felt fold over the four
shared fields). NOW an alias for `capOpen_membership8` (`MembershipCore` is defined in §5 and the
8-felt sound lemmas already consume it directly — no duplicated fold). -/
theorem membershipCore_opens (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hcore : MembershipCore sponge tf c env) :
    MembersAt8 S8 (groupVal env c.capRoot) (leafOf c env) :=
  capOpen_membership8 S8 sponge tf c env hChip hcore

/-- **`effBitGateFor c (eff : ℤ)`** — the GENERAL effect-bit pin: `effBit = eff`. `effBitGate` is the
`eff := EFFECT_TRANSFER` instance (`effBitGate_eq_for`). Each fan-out effect's cap-open descriptor pins its
OWN `EFFECT_<kind>` bit here. -/
def effBitGateFor (c : CapOpenCols) (eff : ℤ) : EmittedExpr :=
  .add (.var c.effBit) (.const (-eff))

/-- `effBitGate` is the `eff := EFFECT_TRANSFER` instance of the general `effBitGateFor`. -/
theorem effBitGate_eq_for (c : CapOpenCols) :
    effBitGate c = effBitGateFor c EFFECT_TRANSFER := rfl

/-- **`SatisfiedEff sponge tf c env n`** — the effect-GENERAL cap-membership row (residual (a), fan-out):
the membership CORE + target binding (shared with `Satisfied`), the high-limb zero, and — instead of the
transfer constant pins — the committed effect-bit column pinned to `1 <<< n` (`effBitGateFor … (1<<<n)`) and
the general facet binding `mask_lo = effBit` (`facetEffGate`). A `SatisfiedEff … n` row opens the cap-tree at
a leaf whose facet permits the effect-kind bit `1 <<< n` (NOT transfer), under the tier DECODED off the
committed `auth_tag`. -/
structure SatisfiedEff (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (n : Nat) : Prop where
  /-- The membership core (Merkle fold + root pin) — shared with `Satisfied`. -/
  core : MembershipCore sponge tf c env
  /-- The leaf's target equals the turn's src (shared). -/
  targetBound : (targetBindGate c).eval env.loc = 0
  /-- **(residual (a))** The committed effect-bit column `effBit` is THIS effect's bit `1 <<< n`. -/
  effBitPinned : (effBitGateFor c ((1 <<< n : Nat) : ℤ)).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP)** Each full-mask bit column is boolean. -/
  maskBitsBool : ∀ i < MASK_BITS, (maskBitBoolGate c i).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP, FIXED)** The low 16-bit decomposition reconstructs `mask_lo`
  (per-limb range check, sum `< 2^16 < p`). NO `mask_hi = 0` pin — a broad `EFFECT_ALL` cap decomposes
  fully. Together with `maskReconHi` these DERIVE the full `maskReconGate` (`maskReconGate_of_limbs`). -/
  maskReconLo : (maskReconLoGate c).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP, FIXED)** The high 16-bit decomposition reconstructs `mask_hi`. -/
  maskReconHi : (maskReconHiGate c).eval env.loc = 0
  /-- **(residual (a) — GENUINE MEMBERSHIP)** The SELECTED bit `n` (THIS effect's bit) is set — the
  genuine `(1<<<n &&& mask_lo) ≠ 0` submask, NOT the over-strict equality `mask_lo == 1<<<n`. -/
  facetEffBound : (selectedBitGate c n).eval env.loc = 0

/-- A `SatisfiedEff` row witnesses `MembersAt S cap_root leaf` (the shared Merkle fold over the core). -/
theorem capOpenEff_membership (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (n : Nat)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hsat : SatisfiedEff sponge tf c env n) :
    MembersAt8 S8 (groupVal env c.capRoot) (leafOf c env) :=
  membershipCore_opens S8 sponge tf c env hChip hsat.core

/-- A `SatisfiedEff` row binds `leaf.target = src` (shared target gate). -/
theorem capOpenEff_target (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (n : Nat) (hsat : SatisfiedEff sponge tf c env n) :
    (leafOf c env).target = env.loc c.src := by
  have h := hsat.targetBound
  unfold targetBindGate at h
  simp only [EmittedExpr.eval] at h
  simp only [leafOf]; linarith

/-- **`capOpenEff_confers` (fan-out) — the cap-open confers `1 <<< n` (THIS effect-kind), tier DECODED.**
A `SatisfiedEff … n` row confers the effect-kind bit `1 <<< n` for any `provided` satisfying the tier read
off the committed `auth_tag` (NOT a constant): the `effBitPinned` pins `effBit = 1 <<< n`, the `facetEffGate`
binds `mask_lo = effBit`, and `facetEffGate_permits` yields the genuine in-circuit `isEffectPermitted`
against `1 <<< n` — the facet must permit THAT effect-kind. The tier rides the decoded `auth_tag`. -/
theorem capOpenEff_confers (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (n : Nat) (hn : n < MASK_BITS) (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (hsat : SatisfiedEff sponge tf c env n)
    (htier : (tierOfTag vkOfTag (leafOf c env).auth_tag).isSatisfiedBy provided = true) :
    confersLeaf vkOfTag provided (1 <<< n) (leafOf c env) := by
  have hsel : env.loc (c.bit n) = 1 := by
    have h := hsat.facetEffBound
    unfold selectedBitGate at h
    simp only [EmittedExpr.eval] at h
    linarith
  have hperm : isEffectPermitted (facetOfLeaf (leafOf c env)) (1 <<< n) = true :=
    facetEffGate_permits c env n hn hsat.maskBitsBool
      (maskReconGate_of_limbs c env hsat.maskReconLo hsat.maskReconHi) hsel
  exact ⟨hperm, htier⟩

/-- **`capOpenEff_authorizes` — THE EFFECT-GENERAL AUTHORITY LEG (fan-out keystone).** A `SatisfiedEff … n`
row whose opened leaf IS the faithfulness contract's `(actor ⇒ src)` edge discharges the kernel's GENERAL
`authorizedFacetEffB … (1 <<< n)` for the turn — over the effect-kind `1 <<< n` (NOT transfer), under any
`provided` satisfying the committed tier. THE bridge each fan-out effect's cap-open descriptor consumes. -/
theorem capOpenEff_authorizes (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (n : Nat) (hn : n < MASK_BITS)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hsat : SatisfiedEff sponge tf c env n)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< n) caps (groupVal env c.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : env.loc c.src = (src : ℤ))
    (hedge : leafOf c env = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hmem : MembersAt8 S8 (groupVal env c.capRoot) (leafAt actor src) := by
    rw [← hedge]; exact capOpenEff_membership S8 sponge tf c env n hChip hsat
  have hconf : confersLeaf vkOfTag provided (1 <<< n) (leafAt actor src) := by
    rw [← hedge]
    exact capOpenEff_confers sponge tf c env n hn vkOfTag provided hsat (hedge ▸ htier)
  have htgt : (leafAt actor src).target = (src : ℤ) := by
    rw [← hedge, capOpenEff_target sponge tf c env n hsat, hsrc]
  exact ⟨deployedCapOpen8_implies_authorizedEffB S8 vkOfTag provided (1 <<< n) caps
    (groupVal env c.capRoot) leafAt hfaith actor src dst amt hmem hconf, htgt⟩

/-- **`satisfiedEff_rejects_wrong_facet` (fan-out NEGATIVE — the wrong-facet tooth bites, witness FALSE,
GENUINE SUBMASK).** A `SatisfiedEff … n` row requires the SELECTED bit `n` set; a leaf whose mask bit `n`
is CLEAR (the carrier `bitₙ = 0`, i.e. the cap does NOT permit the effect-kind `1 <<< n`) CANNOT satisfy
the row — the SELECTED-bit gate `selectedBitGate c n` does not hold. The cap-open for effect-kind `n`
authorizes a cap that genuinely CARRIES that bit; a cap whose facet lacks it is rejected in-circuit. -/
theorem satisfiedEff_rejects_wrong_facet (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (n : Nat) (hclear : env.loc (c.bit n) = 0) :
    ¬ SatisfiedEff sponge tf c env n := by
  intro hsat
  have hfacet := hsat.facetEffBound
  unfold selectedBitGate at hfacet
  simp only [EmittedExpr.eval, hclear] at hfacet
  linarith

/-! ## §11 — discriminating teeth (the gates are real). -/

/-- **The transfer-facet gate is DISCRIMINATING (witness FALSE).** A leaf whose `mask_lo` is NOT
`EFFECT_TRANSFER` fails the facet binding. -/
theorem transferFacetGate_discriminates (c : CapOpenCols) (env : VmRowEnv)
    (hbad : env.loc (c.leaf 3) = EFFECT_TRANSFER + 1) :
    (transferFacetGate c).eval env.loc ≠ 0 := by
  unfold transferFacetGate
  simp only [EmittedExpr.eval, hbad]
  intro h; linarith

/-- **The target gate is DISCRIMINATING (witness FALSE).** -/
theorem targetBindGate_discriminates (c : CapOpenCols) (env : VmRowEnv)
    (hne : env.loc (c.leaf 1) ≠ env.loc c.src) :
    (targetBindGate c).eval env.loc ≠ 0 := by
  unfold targetBindGate
  simp only [EmittedExpr.eval]
  intro h
  apply hne
  linarith

/-! ## §12 — Axiom hygiene. -/

#assert_axioms chipAbsorb_realizes
#assert_axioms leafDigest_sound8
#assert_axioms node_sound8
#assert_axioms recompose_reaches_cur8
#assert_axioms capOpen_membership8
#assert_axioms capOpen_confers
#assert_axioms capOpen_confers_decoded
#assert_axioms maskReconGate_of_limbs
#assert_axioms maskReconLoGate_rejects_wrap
#assert_axioms facetEffGate_permits
#assert_axioms facetEffGate_rejects_wrong_facet
#assert_axioms capOpen_confers_via_effGate
#assert_axioms capOpen_sound
#assert_axioms capOpen_authorizes
#assert_axioms capOpen_authorizes_tierGeneral
#assert_axioms membershipCore_opens
#assert_axioms capOpenEff_membership
#assert_axioms capOpenEff_target
#assert_axioms capOpenEff_confers
#assert_axioms capOpenEff_authorizes
#assert_axioms satisfiedEff_rejects_wrong_facet
#assert_axioms schemeRealizedByChip_discharged
#assert_axioms node_leaf_length_disjoint
#assert_axioms transferFacetGate_discriminates
#assert_axioms targetBindGate_discriminates

end Dregg2.Circuit.DeployedCapOpen
