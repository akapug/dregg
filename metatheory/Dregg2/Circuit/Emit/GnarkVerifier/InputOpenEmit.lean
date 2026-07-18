/-
# Dregg2.Circuit.Emit.GnarkVerifier.InputOpenEmit — the INPUT-OPEN MMCS opening
(input-MMCS leaf hash over the opened batch rows + the depth-N path to the input root)
as a LEAN-AUTHORED, EMITTED R1CS, with a ∀-refinement theorem.

SUBSTRATE, said out loud: **this is Lean-authored AIR/R1CS.** Every constraint below is
EMITTED from a Lean builder over the `R1csFr` foundation and the committed `Poseidon2Fr`
permutation model; nothing here is hand-written in Go/Rust. The deployed
`chain/gnark/stark_open_input.go` (`verifyOpenInputBatchNative`) +
`chain/gnark/fri_verify_native.go` (`multiField32HashNative` / `packShiftedBn254`) are the
pinned REFERENCE the emission is checked against (same shifted packing, same sponge block
structure, same Poseidon2 permutation), not the source of the constraints.

THE CHECK (the input-open opening — `verifyOpenInputBatchNative`, the last soundness seam of
the native STARK verify): a query opens a batch of committed columns; the opened row values
are hashed by the **MultiField32 padding-free sponge** into ONE BN254 leaf, then that leaf is
laddered bottom-up through a depth-`d` native Merkle path (one `Poseidon2Bn254Compress` per
level, the path bit steering left/right) to the committed input root.

WHAT IS NEW here vs `MerkleEmit` (which carries the single-slot commit-phase leaf hash
`leafHashRef` + the path walk): the input-open leaf hash is the GENERAL multi-block sponge —
the opened rows can be far wider than one rate slot (widths up to 388 base values in the
deployed instance), so the sponge absorbs in blocks of RATE·8 = 16 limbs, 8 shifted limbs
per rate slot, partial blocks overwriting only the slots they fill (overwrite mode, the
capacity + unfilled rate slots RETAIN the previous permutation output), one permutation per
block, digest = state[0]. That is `multiFieldHashRef` / `multiFieldHashW` below, KAT-anchored
to the Rust MMCS gold digests (kat4/kat16/kat20 — partial slot / two-slot one-block /
two-block slot-retention).

Deliverables (genuine ∀-theorems, not `#guard` samples):

  * **`multiFieldHashW_emits`** — the multi-block sponge builder emits a define-chain whose
    forced denotation is the reference sponge `multiFieldHashRef` over the row values, with
    the BabyBear→BN254 shifted packing (`packShiftedW`, reused from `MerkleEmit`) authored in
    Lean.
  * **`inputOpen_refines`** — for every `rows root : `, `sibs : List Fr`, `bits : List Bool`
    (`|bits| = |sibs|` = the path depth):
    `gHolds (inputOpenData |rows| |sibs|) (ioAsg …)
       ↔ refRoot (multiFieldHashRef rows) (sibs.zip bits) = root`,
    i.e. "hash(rows) laddered up the path == root". Both polarities: any tamper (a changed
    row limb — moving the leaf hash — a wrong sibling, a flipped bit, a corrupted root) that
    moves the recomputed root makes `gHolds` FALSE.
  * **`inputOpen_refines_emitted`** — the same iff at the emitted wire form, via the proven
    `emit_faithful` round trip.
  * **`inputOpen_sound`** — the adversarial face: ANY witness satisfying the circuit has its
    root variable equal to the leaf-hash-then-path recomputation from its own row/sibling/bit
    variables (no honest-fill hypothesis; the emitted defining constraints force every minted
    value).

`#guard` KAT teeth against the DEPLOYED Rust/Go gold vectors (fri_leaf_hash_kat_test.go):
the multi-block sponge reproduces `katLeafAHex`/`katLeafBHex` (8), `kat4Hex` (partial slot),
`kat16Hex` (two slots, one block), `kat20Hex` (two blocks, slot-retention) BIT-EXACTLY, plus
the composed leaf-hash + 1-level path against the real `MerkleTreeMmcs::commit` root
(`katMmcsRootHex`), accept + tampered-row reject.

Classified seam (named, not silent): `packShiftedW` writes the radix step as `const · acc` —
a `mul` node — so the lowering spends aux rows where the deployed gnark pack is
constraint-free linear. Semantically identical (a linear naming row forces a value, it does
not grant the prover freedom); cost-only, in the safe direction. Inherited verbatim from
`MerkleEmit`'s `packShiftedW`.
-/
import Mathlib.Data.List.GetD
import Dregg2.Circuit.Emit.GnarkVerifier.MerkleEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

namespace Dregg2.Circuit.Emit.GnarkVerifier.InputOpen

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.Poseidon2Fr (permute permuteW compress St BuilderM)
open Dregg2.Circuit.Emit.GnarkVerifier.Merkle

/-! ## §1 The multi-block MultiField32 sponge — the input-MMCS leaf hash. -/

/-- Chunk a list into blocks of 16 (the RATE·8 = 16-limb sponge block of
`multiField32HashNative`). Well-founded on length: a nonempty list's `drop 16` is strictly
shorter. -/
def chunk16 {α : Type} : List α → List (List α)
  | [] => []
  | (x :: xs) => (x :: xs).take 16 :: chunk16 ((x :: xs).drop 16)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem chunk16_nil {α : Type} : chunk16 ([] : List α) = [] := by rw [chunk16]

theorem chunk16_cons {α : Type} (x : α) (xs : List α) :
    chunk16 (x :: xs) = (x :: xs).take 16 :: chunk16 ((x :: xs).drop 16) := by
  rw [chunk16]

/-- Chunking commutes with an elementwise map. -/
theorem chunk16_map {α β : Type} (f : α → β) (l : List α) :
    chunk16 (l.map f) = (chunk16 l).map (List.map f) := by
  induction l using chunk16.induct with
  | case1 => simp [chunk16_nil]
  | case2 x xs ih =>
      have hcons : (x :: xs).map f = f x :: xs.map f := rfl
      rw [hcons, chunk16_cons (f x) (xs.map f), chunk16_cons x xs, List.map_cons]
      have e1 : (f x :: xs.map f).take 16 = (List.map f) ((x :: xs).take 16) := by
        rw [← hcons, List.map_take]
      have e2 : (f x :: xs.map f).drop 16 = ((x :: xs).drop 16).map f := by
        rw [← hcons, List.map_drop]
      rw [e1, e2, ih]

/-- One sponge block absorbed (overwrite mode): slot 0 = shifted pack of the first ≤ 8
limbs; slot 1 = shifted pack of the next ≤ 8 limbs when the block is > 8 wide, else RETAIN
the previous rate slot `st.2.1`; the capacity `st.2.2` is always retained; one permutation. -/
def absorbBlock (st : St) (blk : List Fr) : St :=
  permute
    ( packShifted (blk.take 8)
    , (if blk.length ≤ 8 then st.2.1 else packShifted (blk.drop 8))
    , st.2.2 )

/-- **The MultiField32 padding-free sponge** over the concatenated opened rows
(`mfRefSpongeHash` / `multiField32HashNative`): state `[0,0,0]`, absorb every 16-limb block,
digest = state[0]. This IS the input-MMCS leaf hash the deployed `hashGroup` applies to a
height class's opened rows. -/
def multiFieldHashRef (limbs : List Fr) : Fr :=
  ((chunk16 limbs).foldl absorbBlock (0, 0, 0)).1

/-! ## §2 The sponge as a Lean-emitted builder (the constraints). -/

/-- One block absorbed as a builder: the shifted packs are PURE wires (`packShiftedW`, reused
from `MerkleEmit`), one `permuteW` mints the permutation internals. -/
def absorbBlockW (st : Wire × Wire × Wire) (blk : List Wire) : BuilderM (Wire × Wire × Wire) :=
  permuteW
    ( packShiftedW (blk.take 8)
    , (if blk.length ≤ 8 then st.2.1 else packShiftedW (blk.drop 8))
    , st.2.2 )

/-- **The leaf-hash builder** — fold the block absorptions over the row wires and squeeze
lane 0. -/
def multiFieldHashW (vals : List Wire) : BuilderM Wire := do
  let final ← (chunk16 vals).foldlM absorbBlockW (Wire.const 0, Wire.const 0, Wire.const 0)
  pure final.1

/-- One block's emission spec: under any assignment satisfying the appended asserts the
result triple denotes `absorbBlock` of the block's evaluated values. -/
theorem absorbBlockW_emits (t : Wire × Wire × Wire) (blk : List Wire) {bound : ℕ}
    (ht : bel3 t bound) (hblk : ∀ w ∈ blk, wBelow w bound) :
    Emits3 (absorbBlockW t blk) bound
      (fun a => absorbBlock (ev3 t a) (blk.map (Wire.eval · a))) := by
  have hbel : bel3
      ( packShiftedW (blk.take 8)
      , (if blk.length ≤ 8 then t.2.1 else packShiftedW (blk.drop 8))
      , t.2.2 ) bound := by
    refine ⟨packShiftedW_below _ (fun w hw => hblk _ (List.mem_of_mem_take hw)), ?_, ht.2.2⟩
    by_cases hle : blk.length ≤ 8
    · simp only [if_pos hle]; exact ht.2.1
    · simp only [if_neg hle]
      exact packShiftedW_below _ (fun w hw => hblk _ (List.mem_of_mem_drop hw))
  refine (permuteW_emits _ hbel).congr (fun a => ?_)
  simp only [ev3, absorbBlock, apply_ite (f := fun w => Wire.eval w a), packShiftedW_eval,
    List.map_take, List.map_drop, List.length_map]

-- The block absorption wraps the 64-round `permute`/`permuteW`; keep BOTH the builder and
-- the semantic reference OPAQUE for every downstream unification (mirrors `MerkleEmit`'s
-- `compressW`), so `whnf` never reduces the Poseidon2 permutation while threading the
-- sponge/path builders and comparing their semantics.
attribute [local irreducible] absorbBlockW absorbBlock

/-- Generic `foldlM` spec for a triple-state accumulator threaded through element steps that
read their own witness (the sponge-block shape). The step `stepB` is kept ABSTRACT so the
whole proof runs WITHOUT ever unifying against the concrete (irreducible) `absorbBlockW` /
Poseidon2 monadic value — the same device `MerkleEmit.emitsW_walk` uses for `compressW`.
`spongeW_emits` is one instantiation. -/
theorem emits3_walk {β : Type} {belE : β → ℕ → Prop}
    {stepB : (Wire × Wire × Wire) → β → BuilderM (Wire × Wire × Wire)}
    {semF : St → β → Assignment → St}
    (belE_mono : ∀ p i j, belE p i → i ≤ j → belE p j)
    (hstepB : ∀ (t : Wire × Wire × Wire) (p : β) (bd : ℕ), bel3 t bd → belE p bd →
      Emits3 (stepB t p) bd (fun a => semF (ev3 t a) p a)) :
    ∀ (l : List β) (t : Wire × Wire × Wire) {bound : ℕ},
      bel3 t bound → (∀ p ∈ l, belE p bound) →
      Emits3 (l.foldlM stepB t) bound
        (fun a => l.foldl (fun st p => semF st p a) (ev3 t a)) := by
  intro l
  induction l with
  | nil =>
      intro t bound ht _
      rw [List.foldlM_nil]
      exact (Emits.pure bel3_mono t ht).congr fun a => by simp
  | cons hd tl ih =>
      intro t bound ht hps
      rw [List.foldlM_cons]
      exact (Emits.bind (g := fun st a => tl.foldl (fun st p => semF st p a) st)
        (hstepB t hd bound ht (hps hd List.mem_cons_self))
        (fun t' b hb ht' =>
          ih t' ht' (fun p hp => belE_mono p bound b (hps p (List.mem_cons_of_mem _ hp)) hb))).congr
        fun a => by rw [List.foldl_cons]

/-- The sponge-fold emission spec — one instantiation of `emits3_walk` with the concrete
`absorbBlockW` step (its spec `absorbBlockW_emits`). -/
theorem spongeW_emits (blocks : List (List Wire)) (t : Wire × Wire × Wire) {bound : ℕ}
    (ht : bel3 t bound) (hall : ∀ blk ∈ blocks, ∀ w ∈ blk, wBelow w bound) :
    Emits3 (blocks.foldlM absorbBlockW t) bound
      (fun a => blocks.foldl
        (fun st blk => absorbBlock st (blk.map (Wire.eval · a))) (ev3 t a)) :=
  emits3_walk (belE := fun blk n => ∀ w ∈ blk, wBelow w n)
    (semF := fun st blk a => absorbBlock st (blk.map (Wire.eval · a)))
    (fun _p _ _ h hij w hw => wBelow_mono (h w hw) hij)
    (fun t blk _ ht hblk => absorbBlockW_emits t blk ht hblk)
    blocks t ht hall

/-- **`multiFieldHashW_emits`** — the multi-block leaf-hash builder emits a define-chain whose
forced denotation is `multiFieldHashRef` over the row values. The BabyBear→BN254 shifted
packing is authored in Lean (`packShiftedW`); no constraint is supplied by the Go gadget. -/
theorem multiFieldHashW_emits (vals : List Wire) {bound : ℕ}
    (h : ∀ w ∈ vals, wBelow w bound) :
    EmitsW (multiFieldHashW vals) bound
      (fun a => multiFieldHashRef (vals.map (Wire.eval · a))) := by
  have hblocks : ∀ blk ∈ chunk16 vals, ∀ w ∈ blk, wBelow w bound := by
    intro blk hblk w hw
    -- every wire of every block is a wire of `vals`
    have : ∀ (l : List Wire), ∀ blk ∈ chunk16 l, ∀ w ∈ blk, w ∈ l := by
      intro l
      induction l using chunk16.induct with
      | case1 => intro blk hblk; simp [chunk16_nil] at hblk
      | case2 x xs ih =>
          intro blk hblk w hw
          rw [chunk16_cons] at hblk
          rcases List.mem_cons.mp hblk with rfl | hblk'
          · exact List.mem_of_mem_take hw
          · exact List.mem_of_mem_drop (ih blk hblk' w hw)
    exact h w (this vals blk hblk w hw)
  have hsponge := spongeW_emits (chunk16 vals) (Wire.const 0, Wire.const 0, Wire.const 0)
    (⟨trivial, trivial, trivial⟩ : bel3 (Wire.const 0, Wire.const 0, Wire.const 0) bound) hblocks
  have hbind := Emits.bind (g := fun st _ => (st : St).1) hsponge
    (fun st b _ hst => (Emits.pure (ev := Wire.eval) wBelow_mono' st.1 hst.1).congr fun a => rfl)
  refine hbind.congr fun a => ?_
  have hev0 : ev3 (Wire.const 0, Wire.const 0, Wire.const 0) a = ((0 : Fr), 0, 0) := rfl
  show (((chunk16 vals).foldl (fun st blk => absorbBlock st (blk.map (Wire.eval · a)))
      (ev3 (Wire.const 0, Wire.const 0, Wire.const 0) a)).1
    : Fr) = multiFieldHashRef (vals.map (Wire.eval · a))
  rw [hev0]
  show (((chunk16 vals).foldl (fun st blk => absorbBlock st (blk.map (Wire.eval · a)))
      ((0 : Fr), 0, 0)).1 : Fr)
    = (((chunk16 (vals.map (Wire.eval · a))).foldl absorbBlock ((0 : Fr), 0, 0)).1 : Fr)
  rw [chunk16_map (Wire.eval · a), List.foldl_map]

-- Opaque head for the composed builders: never reduce the multi-block permutation fold.
attribute [local irreducible] multiFieldHashW

/-! ## §3 A small list helper. -/

/-- Rebuilding a list from `getD` over its index range. -/
theorem map_getD_range (l : List Fr) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    have hn : n < l.length := by simpa using h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn, Option.getD_some]

/-! ## §4 The composed input-open opening circuit and its ∀-refinement.

Layout (row limbs first so the leaf-hash region is a clean prefix): `var 0 … var (W-1)` =
the `W` opened row limbs; `var W` = root; `var (W+1+2i)` = sibling `i`, `var (W+1+2i+1)` =
path bit `i`; Poseidon internals minted from `W+1+2d`. The circuit is the per-level
booleanity asserts, the leaf-hash sponge over the row vars, the compression path over the
sibling vars, and the `finalNode = root` assert. -/

/-- The row-limb wires `var 0 … var (W-1)`. -/
def rowVars (W : ℕ) : List Wire := (List.range W).map Wire.var

/-- The depth-`d` `(sibling, bit)` wire pairs, based past the row + root region. -/
def pairWiresIO (W d : ℕ) : List (Wire × Wire) := pairWiresFrom (W + 1) d

/-- The leaf-hash builder run at the canonical layout: the internals mint from `W+1+2d`.
Returns the leaf wire + its emitted define-chain. -/
def leafRun (W d : ℕ) : Wire × (ℕ × List (Wire × Wire)) :=
  multiFieldHashW (rowVars W) (W + 1 + 2 * d, [])

/-- The path-walk builder run, started at the counter the leaf hash ended at (so the two
define-chains concatenate into one). Returns the recomputed-root wire + its chain. -/
def pathRunIO (W d : ℕ) : Wire × (ℕ × List (Wire × Wire)) :=
  pathW (leafRun W d).1 (pairWiresIO W d) ((leafRun W d).2.1, [])

/-- **The input-open opening circuit** — booleanity asserts, the leaf-hash chain, the path
compression chain, and the `finalNode = root` assert. The two runs compose at the CIRCUIT
(list-append) level — NOT via a monadic bind of the two heavy builders — so each run is a
single `Emits` application (the `MerkleEmit` posture), avoiding the `Bind.bind`/StateM
`whnf` blowup. -/
def inputOpenCircuit (W d : ℕ) : Circuit :=
  ⟨bitBoolFrom (W + 1) d ++ ((leafRun W d).2.2 ++ (pathRunIO W d).2.2)
    ++ [((pathRunIO W d).1, Wire.var W)]⟩

/-- The emission package for the depth-`d`, width-`W` input-open opening. -/
def inputOpenData (W d : ℕ) : GnarkCircuitData :=
  { name         := "merkle_path_bn254_input_open_v1"
    publicInputs := [("root", W)]
    gadgets      := [⟨"VerifyMerklePathBn254InputOpen", [W]⟩]
    circuit      := inputOpenCircuit W d }

/-- The honest input fill: rows at `0…W-1`, root at `W`, siblings at even offsets, path bits
(as `0/1`) at odd offsets past `W`. The Poseidon internals are filled by `solveChain`. -/
def ioInAsg (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool) (W : ℕ) :
    Assignment := fun v =>
  if v < W then rows.getD v 0
  else if v = W then root
  else if (v - (W + 1)) % 2 = 0 then sibs.getD ((v - (W + 1)) / 2) 0
  else encB (bits.getD ((v - (W + 1)) / 2) false)

/-- **The honest witness** — inputs plus the solved Poseidon internals of both chains. -/
def ioAsg (W d : ℕ) (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool) :
    Assignment :=
  solveChain (ioInAsg rows root sibs bits W) ((leafRun W d).2.2 ++ (pathRunIO W d).2.2)

theorem ioInAsg_row (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (W v : ℕ) (hv : v < W) : ioInAsg rows root sibs bits W v = rows.getD v 0 := by
  simp only [ioInAsg, if_pos hv]

theorem ioInAsg_root (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (W : ℕ) : ioInAsg rows root sibs bits W W = root := by
  show (if W < W then rows.getD W 0
    else if W = W then root
    else if (W - (W + 1)) % 2 = 0 then sibs.getD ((W - (W + 1)) / 2) 0
    else encB (bits.getD ((W - (W + 1)) / 2) false)) = root
  rw [if_neg (Nat.lt_irrefl W), if_pos (rfl : W = W)]

theorem ioInAsg_sib (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (W i : ℕ) : ioInAsg rows root sibs bits W (W + 1 + 2 * i) = sibs.getD i 0 := by
  have h1 : ¬ (W + 1 + 2 * i < W) := by omega
  have h2 : ¬ (W + 1 + 2 * i = W) := by omega
  have h3 : (W + 1 + 2 * i - (W + 1)) % 2 = 0 := by omega
  have h4 : (W + 1 + 2 * i - (W + 1)) / 2 = i := by omega
  simp only [ioInAsg, if_neg h1, if_neg h2, if_pos h3, h4]

theorem ioInAsg_bit (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (W i : ℕ) : ioInAsg rows root sibs bits W (W + 1 + 2 * i + 1) = encB (bits.getD i false) := by
  have h1 : ¬ (W + 1 + 2 * i + 1 < W) := by omega
  have h2 : ¬ (W + 1 + 2 * i + 1 = W) := by omega
  have h3 : ¬ ((W + 1 + 2 * i + 1 - (W + 1)) % 2 = 0) := by omega
  have h4 : (W + 1 + 2 * i + 1 - (W + 1)) / 2 = i := by omega
  simp only [ioInAsg, if_neg h1, if_neg h2, if_neg h3, h4]

/-- The LEAF-HASH run's define-chain + forced denotation (a single `Emits` application of
`multiFieldHashW_emits` at the concrete start state). -/
theorem leafRun_props (W d : ℕ) :
    ∃ n1, DefChain (W + 1 + 2 * d) (leafRun W d).2.2 n1
      ∧ wBelow (leafRun W d).1 n1
      ∧ (leafRun W d).2.1 = n1
      ∧ ∀ a, (∀ p ∈ (leafRun W d).2.2, p.1.eval a = p.2.eval a) →
          (leafRun W d).1.eval a = multiFieldHashRef ((rowVars W).map (Wire.eval · a)) := by
  have hrows : ∀ w ∈ rowVars W, wBelow w (W + 1 + 2 * d) := by
    intro w hw
    simp only [rowVars, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact Nat.lt_of_lt_of_le hi (by omega)
  obtain ⟨Lw, n1, hashChain, hrun, hdc, hbleaf, hforce⟩ :=
    multiFieldHashW_emits (rowVars W) hrows (W + 1 + 2 * d) [] le_rfl
  have hleafEq : leafRun W d = (Lw, (n1, hashChain)) := by
    show multiFieldHashW (rowVars W) (W + 1 + 2 * d, []) = (Lw, (n1, hashChain))
    rw [hrun, List.nil_append]
  refine ⟨n1, ?_, ?_, ?_, ?_⟩
  · rw [hleafEq]; exact hdc
  · rw [hleafEq]; exact hbleaf
  · rw [hleafEq]
  · intro a ha; rw [hleafEq] at ha ⊢; exact hforce a ha

/-- The PATH-WALK run's define-chain (from where the leaf hash ended) + forced denotation
(a single `Emits` application of `pathW_emits`). -/
theorem pathRunIO_props (W d : ℕ) :
    ∃ n2, DefChain (leafRun W d).2.1 (pathRunIO W d).2.2 n2
      ∧ ∀ a, (∀ p ∈ (pathRunIO W d).2.2, p.1.eval a = p.2.eval a) →
          (pathRunIO W d).1.eval a
            = (pairWiresIO W d).foldl (fun nd p => stepFr nd (p.1.eval a, p.2.eval a))
                ((leafRun W d).1.eval a) := by
  obtain ⟨n1, hdc1, hbleaf, hn1, -⟩ := leafRun_props W d
  have hpairs : ∀ p ∈ pairWiresIO W d,
      wBelow p.1 (leafRun W d).2.1 ∧ wBelow p.2 (leafRun W d).2.1 := by
    intro p hp
    have hle : W + 1 + 2 * d ≤ (leafRun W d).2.1 := hn1 ▸ hdc1.le
    obtain ⟨h1, h2⟩ := pairWiresFrom_below (W + 1 + 2 * d) (W + 1) d (by omega) p hp
    exact ⟨wBelow_mono h1 hle, wBelow_mono h2 hle⟩
  have hbn : wBelow (leafRun W d).1 (leafRun W d).2.1 := hn1 ▸ hbleaf
  obtain ⟨Rw, n2, pathChain, hrun, hdc, -, hforce⟩ :=
    pathW_emits (pairWiresIO W d) (leafRun W d).1 hbn hpairs (leafRun W d).2.1 [] le_rfl
  have hpathEq : pathRunIO W d = (Rw, (n2, pathChain)) := by
    show pathW (leafRun W d).1 (pairWiresIO W d) ((leafRun W d).2.1, []) = (Rw, (n2, pathChain))
    rw [hrun, List.nil_append]
  refine ⟨n2, ?_, ?_⟩
  · rw [hpathEq]; exact hdc
  · intro a ha; rw [hpathEq] at ha ⊢; exact hforce a ha

/-- The COMBINED chain (leaf-hash ++ path) is a single define-chain from `W+1+2d`, and under
any assignment satisfying it the recomputed-root wire denotes the deployed input-open check:
the leaf hash of the rows laddered up the compression path. -/
theorem ioChain_props (W d : ℕ) :
    ∃ n2, DefChain (W + 1 + 2 * d) ((leafRun W d).2.2 ++ (pathRunIO W d).2.2) n2
      ∧ ∀ a, (∀ p ∈ (leafRun W d).2.2 ++ (pathRunIO W d).2.2, p.1.eval a = p.2.eval a) →
          (pathRunIO W d).1.eval a
            = (pairWiresIO W d).foldl (fun nd p => stepFr nd (p.1.eval a, p.2.eval a))
                (multiFieldHashRef ((rowVars W).map (Wire.eval · a))) := by
  obtain ⟨n1, hdc1, -, hn1, hforce1⟩ := leafRun_props W d
  obtain ⟨n2, hdc2, hforce2⟩ := pathRunIO_props W d
  refine ⟨n2, hdc1.append (hn1 ▸ hdc2), fun a ha => ?_⟩
  rw [List.forall_mem_append] at ha
  rw [hforce2 a ha.2, hforce1 a ha.1]

/-- **The frontend refinement**: the honest witness satisfies the input-open circuit IFF the
leaf hash of the rows, laddered up the path, reproduces the claimed root. -/
theorem inputOpen_frontend (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length) :
    (inputOpenCircuit rows.length sibs.length).satisfied
        (ioAsg rows.length sibs.length rows root sibs bits)
      ↔ refRoot (multiFieldHashRef rows) (sibs.zip bits) = root := by
  set W := rows.length with hW
  set d := sibs.length with hd
  set a := ioAsg W d rows root sibs bits with ha
  obtain ⟨n', hdc, hforce⟩ := ioChain_props W d
  have hbelow : ∀ v, v < W + 1 + 2 * d → a v = ioInAsg rows root sibs bits W v := fun v hv =>
    solveChain_agree_below ((leafRun W d).2.2 ++ (pathRunIO W d).2.2)
      (ioInAsg rows root sibs bits W) hdc v hv
  have hnew : ∀ p ∈ (leafRun W d).2.2 ++ (pathRunIO W d).2.2, p.1.eval a = p.2.eval a :=
    solveChain_sat ((leafRun W d).2.2 ++ (pathRunIO W d).2.2)
      (ioInAsg rows root sibs bits W) hdc
  have hrowsEq : (rowVars W).map (Wire.eval · a) = rows := by
    have e2 : (rowVars W).map (Wire.eval · a) = (List.range W).map (fun v => rows.getD v 0) := by
      rw [rowVars, List.map_map]
      apply List.map_congr_left
      intro v hv
      rw [List.mem_range] at hv
      show a v = rows.getD v 0
      rw [hbelow v (Nat.lt_of_lt_of_le hv (by omega)), ioInAsg_row rows root sibs bits W v hv]
    rw [e2, hW]
    exact map_getD_range rows
  have hroot : a W = root := by
    rw [hbelow W (by omega)]; exact ioInAsg_root rows root sibs bits W
  have hwalk : (pathRunIO W d).1.eval a = refRoot (multiFieldHashRef rows) (sibs.zip bits) := by
    rw [hforce a hnew, hrowsEq]
    show (pairWiresFrom (W + 1) sibs.length).foldl
        (fun nd p => stepFr nd (p.1.eval a, p.2.eval a)) (multiFieldHashRef rows)
      = refRoot (multiFieldHashRef rows) (sibs.zip bits)
    exact foldl_pairWiresFrom_refRoot a sibs (W + 1) bits (multiFieldHashRef rows) hlen
      (fun i hi => by rw [hbelow (W + 1 + 2 * i) (by omega)]; exact ioInAsg_sib rows root sibs bits W i)
      (fun i hi => by rw [hbelow (W + 1 + 2 * i + 1) (by omega)]; exact ioInAsg_bit rows root sibs bits W i)
  have hbool : ∀ p ∈ bitBoolFrom (W + 1) sibs.length, p.1.eval a = p.2.eval a :=
    bitBoolFrom_holds a (W + 1) sibs.length fun i hi => by
      rw [hbelow (W + 1 + 2 * i + 1) (by omega), ioInAsg_bit]
      cases bits.getD i false <;> simp [encB]
  show (∀ p ∈ (inputOpenCircuit W d).asserts, p.1.eval a = p.2.eval a) ↔ _
  show (∀ p ∈ bitBoolFrom (W + 1) sibs.length ++ ((leafRun W d).2.2 ++ (pathRunIO W d).2.2)
      ++ [((pathRunIO W d).1, Wire.var W)], p.1.eval a = p.2.eval a) ↔ _
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton]
  constructor
  · rintro ⟨_, hr⟩
    rw [← hwalk, hr]; exact hroot
  · intro hr
    refine ⟨⟨hbool, hnew⟩, ?_⟩
    show (pathRunIO W d).1.eval a = Wire.eval (Wire.var W) a
    rw [hwalk, hr]; exact hroot.symm

/-- **`inputOpen_refines`** — THE deliverable ∀-refinement, at the R1CS level the gnark
backend consumes: the lowered genuine R1CS of the emitted width-`|rows|` depth-`|sibs|`
input-open opening, under the honest witness, is satisfied IFF the input-MMCS leaf hash of
the opened rows (`multiFieldHashRef`, the MultiField32 shifted-pack sponge), laddered up the
native Merkle path (bottom-up 2-to-1 `Poseidon2Fr.compress`), reproduces the claimed input
root — for EVERY row list, root, sibling list, and (length-matched) bit list. A tampered row
limb (moving the leaf hash), a wrong sibling, a flipped bit, or a corrupted root all move
`refRoot`, refuting `gHolds`. -/
theorem inputOpen_refines (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (inputOpenData rows.length sibs.length)
        (ioAsg rows.length sibs.length rows root sibs bits)
      ↔ refRoot (multiFieldHashRef rows) (sibs.zip bits) = root := by
  unfold Dregg2.Circuit.Emit.GnarkVerifier.gHolds
  rw [← R1csFr.gHolds]
  exact inputOpen_frontend rows root sibs bits hlen

/-- Reject polarity, explicitly: a claimed root that the opened rows do not ladder to makes
the emitted R1CS unsatisfiable under the honest witness. -/
theorem inputOpen_rejects (rows : List Fr) (root : Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length)
    (h : refRoot (multiFieldHashRef rows) (sibs.zip bits) ≠ root) :
    ¬ Dregg2.Circuit.Emit.GnarkVerifier.gHolds (inputOpenData rows.length sibs.length)
        (ioAsg rows.length sibs.length rows root sibs bits) :=
  fun hg => h ((inputOpen_refines rows root sibs bits hlen).mp hg)

/-- Accept polarity (non-vacuity): the honest opening IS accepted. -/
theorem inputOpen_accepts (rows : List Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (inputOpenData rows.length sibs.length)
      (ioAsg rows.length sibs.length rows (refRoot (multiFieldHashRef rows) (sibs.zip bits))
        sibs bits) :=
  (inputOpen_refines rows _ sibs bits hlen).mpr rfl

/-- **The emit tie** — the same refinement at the SERIALIZED wire form, composing the proven
`emit_faithful` round trip (`EmitFaithful.lean`). The bytes the JSON grammar renders in §6
therefore denote exactly this input-open opening check. -/
theorem inputOpen_refines_emitted (rows : List Fr) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
        (Dregg2.Circuit.Emit.GnarkVerifier.emit (inputOpenData rows.length sibs.length))
        (ioAsg rows.length sibs.length rows root sibs bits)
      ↔ refRoot (multiFieldHashRef rows) (sibs.zip bits) = root :=
  (Dregg2.Circuit.Emit.GnarkVerifier.emit_faithful (inputOpenData rows.length sibs.length)
      (ioAsg rows.length sibs.length rows root sibs bits)).symm.trans
    (inputOpen_refines rows root sibs bits hlen)

/-! ## §5 The adversarial (soundness) face — no honest-fill hypothesis. -/

/-- **`inputOpen_sound`** — over EVERY witness (no honest fill): the claimed root variable
`var W` is forced to equal the leaf-hash-then-path recomputation from the witness's own row
values `var 0 … var (W-1)`, siblings `var (W+1+2i)`, and bit values `var (W+1+2i+1)`. The
prover cannot satisfy the circuit while claiming a root the opened rows do not ladder to —
the leaf hash and the `Select`-mux walk are deterministic functions of the witness, pinned
to `var W` by the final assert. (The muxes read back as the branch-selecting `refRoot` step
on a boolean bit — the named Pratt/primality seam of `R1csFr`, forced in-circuit by the
`b·b = b` asserts, exactly the `MerkleEmit` posture.) -/
theorem inputOpen_sound (W d : ℕ) (a : Assignment)
    (hsat : (inputOpenCircuit W d).satisfied a) :
    a W = (pairWiresIO W d).foldl (fun nd p => stepFr nd (p.1.eval a, p.2.eval a))
      (multiFieldHashRef ((rowVars W).map (Wire.eval · a))) := by
  obtain ⟨_, _, hforce⟩ := ioChain_props W d
  have hsat' : ∀ p ∈ bitBoolFrom (W + 1) d ++ ((leafRun W d).2.2 ++ (pathRunIO W d).2.2)
      ++ [((pathRunIO W d).1, Wire.var W)], p.1.eval a = p.2.eval a := hsat
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton] at hsat'
  obtain ⟨⟨_, hnew⟩, hroot⟩ := hsat'
  rw [show a W = (Wire.var W).eval a from rfl, ← hroot, hforce a hnew]

#assert_axioms multiFieldHashW_emits
#assert_axioms ioChain_props
#assert_axioms inputOpen_frontend
#assert_axioms inputOpen_refines
#assert_axioms inputOpen_rejects
#assert_axioms inputOpen_accepts
#assert_axioms inputOpen_refines_emitted
#assert_axioms inputOpen_sound

/-! ## §6 KAT teeth — against the DEPLOYED Rust MMCS gold vectors (fri_leaf_hash_kat_test.go).

The multi-block sponge (`multiFieldHashRef`, the input-MMCS leaf hash) reproduces the Rust
shrink layer's `MultiField32PaddingFreeSponge` digests bit-exactly across every absorb path,
and the composed leaf-hash + path reaches the real `MerkleTreeMmcs::commit` root. -/

/-- `kat4` = `[42, 0, p-1, 1]` (fri_leaf_hash_kat_test.go): a partial rate slot. -/
def kat4 : List Fr := [42, 0, 2013265920, 1]
/-- `kat16` = `katLeafA ++ katLeafB`: two rate slots, ONE permutation block. -/
def kat16 : List Fr := katLeafA ++ katLeafB
/-- `kat20` = `kat16 ++ [11, 22, 33, 44]`: a full block + a partial second block
(slot-1 retention path). -/
def kat20 : List Fr := kat16 ++ [11, 22, 33, 44]

/-- Rust MMCS digest of `kat4` (`kat4Hex`). -/
def kat4Digest : Fr := 0x2c1d1415d7a6209522147d85acc07a4e57ead13e8b1880c642b7fdfa15afeb54
/-- Rust MMCS digest of `kat16` (`kat16Hex`). -/
def kat16Digest : Fr := 0x01e162b091a9f8702ae974ed06ffe42d6c7273bcf54f72236495a67ff3958d80
/-- Rust MMCS digest of `kat20` (`kat20Hex`). -/
def kat20Digest : Fr := 0x21f3e87124673d957b16d062769c4c6c0ae8cd9927925be5d09976a3b7101e83

-- The multi-block sponge reproduces the Rust MMCS leaf digests BIT-EXACTLY (accept):
-- single 8-limb slot (= the commit-phase leaf hash), a partial 4-limb slot, two slots in one
-- block, and two blocks with slot-1 retention.
#guard multiFieldHashRef katLeafA = katLeafADigest
#guard multiFieldHashRef katLeafB = katLeafBDigest
#guard multiFieldHashRef kat4 = kat4Digest
#guard multiFieldHashRef kat16 = kat16Digest
#guard multiFieldHashRef kat20 = kat20Digest

-- Tampered row limb (limb 0: 0 → 1) — the leaf digest moves (reject canary).
#guard multiFieldHashRef (1 :: katLeafA.tail) ≠ katLeafADigest
-- Trailing-zero shift canary: the +1 shifted packing distinguishes a trailing zero limb.
#guard multiFieldHashRef (kat4 ++ [0]) ≠ multiFieldHashRef kat4

-- The COMPOSED leaf-hash + 1-level path reaches the real MerkleTreeMmcs::commit root: leaf =
-- multiField hash of leafA's row, sibling = multiField hash of leafB's row, bit = false
-- ⇒ compress(leaf, sib) — the refinement's right-hand predicate on the deployed gold root.
#guard refRoot (multiFieldHashRef katLeafA) [(multiFieldHashRef katLeafB, false)] = katMmcsRoot
-- Wrong sibling — the root moves (reject).
#guard refRoot (multiFieldHashRef katLeafA) [(multiFieldHashRef katLeafA, false)] ≠ katMmcsRoot
-- Tampered opened row (leaf digest moves) — the root moves (reject; the input-open leaf
-- binding is what commitment-binds the reduced openings).
#guard refRoot (multiFieldHashRef (1 :: katLeafA.tail)) [(multiFieldHashRef katLeafB, false)]
  ≠ katMmcsRoot

/-! ## §7 The emitted JSON artifact — the deployed depth-18 shape.

The committed instance is the deployed native path depth (`d = 18`) over a single-slot leaf
(`W = 8`, one row of two extension evals — the commit-phase width; the refinement above is
∀-quantified over every width and depth). The byte pin below is a length + FNV-1a digest of
the exact rendered string (a full literal pin of a multi-hundred-KB template inside the
source would be unreadable; the digest flips on ANY byte change). The same bytes are
committed at `chain/gnark/emitted/inputopen_template.json`. -/

/-- The canonical wire bytes of the depth-18 input-open template package. -/
def inputOpenTemplateJson : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (inputOpenData 8 18)

/-- FNV-1a over the UTF-8 bytes — the byte-pin digest. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

-- Structure pins for the depth-18 single-slot-leaf instance: the emitted assert count and
-- the lowered R1CS row count (the object the gnark backend consumes).
#guard (inputOpenCircuit 8 18).asserts.length == 8284
#guard (inputOpenCircuit 8 18).lower.length == 13038

-- The byte pin of the committed artifact `chain/gnark/emitted/inputopen_template.json`:
-- exact length + FNV-1a digest. Any byte drift in the emitted template flips the digest.
#guard inputOpenTemplateJson.length == 2981065
#guard fnv1a inputOpenTemplateJson == 7423181293044104491

end Dregg2.Circuit.Emit.GnarkVerifier.InputOpen
