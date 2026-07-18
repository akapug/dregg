# Automatafl n-generic descriptor architecture — blueprint (validated at n = 11)

Status: DESIGN (no build). Substrate: **Lean-authored AIR** — the descriptor and every
constraint family live in `metatheory/Dregg2/Circuit/Emit/`; `dregg-automatafl/src/*.rs` is read
as **spec only**. Nothing here is a Rust AIR edit.

Target board: **n = 11** (standard hnefatafl / tafl). The current descriptors instantiate the
minimal complete board **n = 2** and commit the board with a **single zero-padded MerkleHash8 leaf
that only exists because k = n² ≤ 8**. This doc replaces that with an **n-generic linear bit-pack +
one Poseidon2**, keeps the working representation unpacked, redoes the NN = 2-concrete `decide`
capstones as arguments over an explicit `n`, and reduces the whole-turn seam residual to
**root-injectivity on the packed commitment** — which becomes a *Lean theorem*, not a crypto floor,
if the packed felts are published directly.

The two descriptors this covers:

| Descriptor | File | Half of the turn | n = 2 today |
|---|---|---|---|
| `automataflResolveDesc` (Leg R) | `AutomataflResolveEmit.lean` | `old → mid` (validate · conflict · occlusion · rewrite) | 306 cols, 379 gates, 32 PI |
| `automataflStepDesc` (Leg A) | `AutomataflStepEmit.lean` | `mid → new` (raycast · decide-axis · choose-offset · step) | 269 cols, 418 gates, 32 PI |

Both carry the identical `node8Lookup` / `bind_board_roots` commitment. The commitment redesign is
one change made in both.

---

## 1. The smart commitment (the headline)

### 1.1 What is there now, and why it does not generalise

`bind_board_roots` (both files) commits a board by:

```
leaf(cells) := cells ++ replicate (8 - KK) mh8_zero      -- ONE 8-felt leaf, one cell per felt
root8       := Poseidon2_arity16 ( leaf ‖ zeroLeaf )     -- one node8, folded against a zero sibling
bind_pi     := 8 output lanes → PIs [16..24) / [24..32)
```

The comment at `AutomataflResolveEmit.lean:843` states the gap outright: *"At k ≤ 8 the whole board
packs into ONE zero-padded leaf. This is the ONE place the layout is [not generic] — at k > 8 …
a board_root8 Merkle TREE rather than a single padded leaf."* At n = 3 already k = 9 > 8, and at
n = 11 k = 121. The naive generalisation is a **Merkle tree of ~16–31 arity-16 Poseidon2 nodes**
per board — a new recursive family, a new depth-parametric injectivity proof, and ~200+ output-lane
columns. That tree is the thing we refuse to build.

### 1.2 The pack: base-4 positional, degree 1, ⌈n²/15⌉ felts

Cells hold a 2-bit code `{VAC=0, REP=1, ATT=2, AUTO=3}` (already range-pinned by
`boardRangeConstraints`, `assert_member(cell, {0,1,2,3})`). Pack 15 cells per BabyBear felt as a
base-4 number:

```
packed_j  :=  Σ_{i=0}^{14}  cell[15·j + i] · 4^i          -- j ∈ [0, ⌈n²/15⌉)
```

emitted as one linear gate per felt:  `packed_j − Σ_i 4^i · cell[15j+i] = 0`.

**Numbers, BabyBear p = 2³¹ − 2²⁷ + 1 = 2013265921:**

| Quantity | Value | Note |
|---|---|---|
| cells / felt | **15** | 4¹⁵ − 1 = 2³⁰ − 1 = 1073741823 **< p**; 16 cells (4¹⁶ = 2³²) would wrap |
| felts at n = 11 | **⌈121/15⌉ = 9** | 8 full felts (120 cells) + 1 felt holding the last cell |
| pack gate degree | **1** | 4ⁱ are constants; linear in the cell columns → adds *zero* degree |
| no-overflow guarantee | max felt = 4¹⁵ − 1 < p | distinct cell-tuples land in [0, 4¹⁵) ⊂ [0, p): **reduction mod p is the identity there** |

The pack is **injective on the constrained alphabet** by base-4 positional decode with no modular
collision. This is the fact that makes root-injectivity cheap (§6).

### 1.3 The hash: ONE Poseidon2, absorption count = 1

9 packed felts pad to 16 and enter a **single arity-16 Poseidon2 permutation** (the existing
`node8Lookup` chip, arity 16), output 8 lanes = the root:

```
board_root8(b) := Poseidon2_arity16 ( packed_0 … packed_8 ‖ zero×7 )   -- 8-lane digest
```

- **Absorption count: 1** for every n with n² ≤ 15·16 = 240, i.e. **n ≤ 15** — covers *every*
  standard tafl size (7, 9, 11, 13, 15). No Merkle tree, no depth parameter, no sponge, for the
  entire deployed range. (n ≥ 16 → ⌈n²/15⌉ > 16 → a two-block sponge; out of scope, noted.)
- Compare the naive path at n = 11: **1 Poseidon2 call vs ~16–31**. The Merkle generalisation gap
  is *eliminated*, not merely deferred.
- Degree impact: **none** — Poseidon2 is a lookup, not a polynomial gate; the pack that feeds it is
  degree 1.

### 1.4 Do we need the hash at all? — publish the packed felts as PIs

The 9 packed felts are **already a complete, injective, degree-1 commitment to the board.** The
hash exists only to produce a *fixed-width 8-lane digest* independent of n (the door state layer
speaks `old8 ‖ mid8`). Two options:

- **Option A — packed-felts-as-PI (recommended for n = 11).** Bind the 9 old + 9 mid packed felts
  directly to PIs `[16..34)`. **No Poseidon2, no root columns, no crypto assumption.** The board PI
  is variable-width (18 felts). Root-injectivity is then the *trivial* base-4 lemma of §1.2 —
  fully discharged in Lean.
- **Option B — single hash-to-8-lanes.** Keep the 8-lane digest interface (drop-in for the door
  layer) at the cost of one Poseidon2 whose collision-resistance is the residual. Still no tree.

**Recommendation:** ship **Option A** for the standalone game/light-client leaf (root-injectivity
becomes a theorem); keep **Option B** available as a thin adapter *only where a downstream layer
demands a fixed 8-felt board digest*. Either way the board is committed by ≤ 9 linear gates + at
most one permutation, n-generically.

### 1.5 Why it is n-generic by construction

The only n-dependence is the felt **count** `⌈n²/15⌉`, i.e. a `List.range (⌈n²/15⌉)` fold — exactly
the shape `AutomataflOcclusionGeneric` §2 already reasons over (`sum_map_ite`, `sum_oneHot`,
`List.range`-indexed folds). There is no board-size case split, no tree recursion, no padding-width
special case beyond "pad to 16." Genericity falls out of the same fold algebra already proven.

---

## 2. The working representation — keep n²-felt cells, pack only at the boundary

**Do not pack the working rep.** Analysis:

- Every board **read** in both descriptors is positional. The auto read and each ray step are a
  gated row×column dot product `value − Σ_y Σ_x selRow[y]·selCol[x]·board[y·n+x]` (degree 3, n²
  product terms), and occlusion reads a whole line (`LineReadsVert/Horiz` reads `(x,k)` for each
  k). These want `board[y·n+x]` to be a **single column**.
- If cells were bit-packed, every read would first have to **decompose** the enclosing felt into its
  15 cells (a range-bit gadget per felt) to index one cell. Because the reads collectively touch the
  *whole board* (the auto dot product sweeps all n² cells; ray/occlusion sweep whole lines), you
  would decompose all 9 felts back to 121 cells anyway — ending with **both** the 121 cell columns
  **and** the 9 packed felts **and** 9 unpack gates. Strictly worse than unpacked.

**Recommendation:** the working representation stays **1 felt per cell, n² columns**, range-pinned
to {0,1,2,3} (already emitted). Packing is a boundary transform: `⌈n²/15⌉` linear gates per board,
placed at the commitment leg only. "Compute unpacked, commit packed." Packing does **not** win for
the working rep, and the doc says so explicitly so the temptation is closed.

---

## 3. The n-generic proof plan — arguments, not `decide`

The occlusion **math** is already n-generic and proven; the *board read/write/eq/selection/carry/
capstone* proofs are NN = 2 `decide`-over-{0,1} and must be rebuilt as arguments over an explicit n.
`AutomataflOcclusionGeneric.lean` is the worked template for how (`interior_nil_n2` → membership
characterisation; vacuity → non-negative-sum witness extraction).

### 3.1 Carries over verbatim (n-agnostic — reuse as-is)

- **Field glue** (`AutomataflStepRefine`): `Canon`, `bin_of_gate`, `eq_of_modEq_canon`,
  `eq_of_modEq_small/win`, `forcedGe0_core`, `StepCanon`, `codeToParticle`, `gate_modEq_iff`. These
  are descriptor- and n-agnostic (mod-p denotation, canonicality, the no-wrap comparison heart).
- **One-hot machinery** (`OcclusionGeneric` §1): `OneHotAt`, `sum_map_ite`, `sum_oneHot`,
  `oneHotAt_ite` — already quantified over `n`.
- **The whole occlusion argument** (`OcclusionGeneric` §2–5): `segVal_eq`, `msumVal_eq_sum_between`,
  `msum_ge_one_iff`, `mem_interior_vert/horiz`, `occluded_vert/horiz_iff`,
  `occ_eq_occluded_vert/horiz`. Stated over `n` as a variable; the between-mask, the non-negative-sum
  decomposition, and the reference membership side are all size-free. **This is the crown jewel that
  is already done.**
- **Reference-side congruence / seam** (`Games/Automatafl.lean` §8b–8c): `raycastFuel_congr`,
  `raycast_congr`, `automatonOffset_congr`, `automatonStep_congr`, `mem_interior_*`,
  `applyMoves_cell_TT/TF/FT/FF`. All quantify over `Board` (with `size` a field). `applyMoves_cell_*`
  is a **2-element move list** — that is the *player count* (m = 2), invariant under n, not a board-
  size limitation. These carry.
- **Reference model** (`Games/Automatafl.lean`) is *already fully n-generic* (`Board.size` a field,
  `raycastFuel` fuel-seeded `size+1`, `interior` over `List.range (hi-lo-1)`). Nothing to redo.

### 3.2 Rewritten (currently NN = 2-concrete `decide` — the real work)

Redo each as a fold/argument over `List.range n` with `omega` on the index arithmetic, mirroring how
`OcclusionGeneric` replaced `interval_cases` over a 2×2 board with membership + non-negativity:

| Leg | Current NN = 2 form | n-generic replacement |
|---|---|---|
| **auto pin** (R1/A1) | `coord_of_sat` decides the auto cell over {0,1}² | one-hot `selRow/selCol` extraction via `sum_oneHot`; dot-product read `= AUTO` by `readRowcolHead` evaluated against the one-hot (reuse §3.1 one-hot algebra) |
| **board read** (`read_rowcol_gated`) | dot product decided over 4 cells | `readRowcolHead` value = `board[y·n+x]` from the two one-hots (`sum_oneHot` twice); n-generic |
| **eq-coords** (occlusion `is_vertical`, `occEq`) | `decide` over {0,1} endpoints | `mem_interior_*` + the `Between` predicate (already generic); rook-align from `validate_move` gate |
| **selection truth table** (fork/collide/survive) | `selection_of_sat` cases over 2×2 | argument over the `hasTwoDistinct` reference (`conflictResolve_pair` already generic-ish); the 2-move fork/collide disjunction is m = 2, not n-bound |
| **carries + flow-through** (R5 caterpillar) | `chainDest_a/b`, `carry_of_sat`, `ft_of_sat` decided on the 2×2 chain | `followChain` over fuel `moves.length+1 = 3` (m = 2 fixed); indices range over `n` but the chain length is bounded by move count — reuse `applyMoves_cell_*` |
| **write-mid** (R6 rewrite) | `writeCell_of_sat`, `cellAlgebra` (11/16 live cases) decided per cell over 2×2 | per-cell gate = `midCell_of_facts` cased on survive verdict × carrying sources; already structured as `applyMoves_cell_*` matches — generalise the cell quantifier from {0,1}² to `range n × range n` |
| **the four raycasts** (A2) | `raycast_{xp,xn,yp,yn}_of_sat` decide the line reads over n = 2 | induct on `raycastFuel` fuel (seeded `size+1 = n+1`); the hit one-hot + vacuum-before/in-bounds-before gates force the true first-non-vacuum cell at any n (the OcclusionGeneric non-negativity witness pattern) |
| **decide_axis** (A3) | `decideAxis_x/y_sound` — 9-case truth table, `decide` on {0,1} dists | the 9 `evaluateAxis` cases are on **particle kind × dist comparison**, not board size; keep the case structure, replace concrete-dist `decide` with `forcedGe0_core` comparisons over n-ranged dists |
| **choose_offset** (A4) | NAMED residual today | score-compare (`sgt/slt` 20-bit, n-independent) + column rule; the offset equalities are `chooseOffset_mem` (already generic). New, but n-flat |
| **step + board-update fold** (A5) | NAMED residual today | `stepTo` positional rewrite; per-cell update gate cased like write-mid; `automatonStep_congr` closes composition |

### 3.3 The one non-obvious cost — membership must stop being `by decide`

Every gate-extraction lemma today proves *"this constraint ∈ `desc.constraints`"* by `decide` over
the fold-generated list (≈ 380 nodes at n = 2). At n = 11 the list is ≈ 800–900 nodes of nontrivial
`VmConstraint2`, and `by decide` membership will blow `maxRecDepth`/time. **Replace enumerated
membership with structured indexing lemmas**: "the k-th `seg` gate sits at list offset f(n,k)",
proved once by the fold's `List.range`/`append` structure, so extraction is O(1) lookup independent
of n. This is a real, pervasive part of the rebuild (touches every `_of_sat`), and is the main
reason the port is not mechanical.

---

## 4. `descN n` — genericity as a type, not a global `def`

Today `NN : Nat := 2` is a top-level constant and every family reads it globally; genericity is
"edit the def and re-check." Make it a parameter:

```lean
def automataflResolveDescN (n : Nat) : EffectVmDescriptor2 := …   -- every family takes n
def automataflStepDescN     (n : Nat) : EffectVmDescriptor2 := …
def automataflResolveDesc := automataflResolveDescN 2             -- byte-golden UNCHANGED
def automataflStepDesc     := automataflStepDescN 2
def automataflResolveDesc11 := automataflResolveDescN 11
def automataflStepDesc11    := automataflStepDescN 11
```

Consequences:
- n-generic theorems quantify `∀ n, …` over the *actual emitted object* `descN n`, so the refinement
  is machine-checked at the parameter, not at a chosen constant. Instantiating at 11 is
  `descN 11`; at 5, `descN 5`; the n = 2 byte-pin is preserved as `descN 2` for regression.
- The pack felt-count `⌈n²/15⌉`, the `COORD_RBITS = ⌈log₂ n⌉` bit widths, the `List.range n` one-hots
  and seg folds all become functions of the argument — which they morally already are; this makes it
  enforced. Byte-pins become `#guard (descN 2) == golden` (unchanged) plus `#guard (descN 11)` shape
  pins (width/PI/constraint-count, §5).

This is a **mechanical refactor of the emitters** (thread `n` through ~30 `def`s each) that must land
*before* the n-generic proofs — the proofs need `descN n` to quantify over.

---

## 5. Budget at n = 11 (with the smart commitment)

Computed from the exact width chain (`R_WIDTH = SEL0 + 24 + 8n + commit`; verified `= 306` at n = 2):

| Metric | Target | Leg R (resolve) @ n=11 | Leg A (step) @ n=11 | Driver |
|---|---|---|---|---|
| **Width** | **< 1024** | **853** (Opt A) / 870 (Opt B) | **≈ 690** (front 418 + back ≈ 240 + commit) | 2n² board cells (242) + O(n) move/occlusion blocks |
| **Degree** | **< 8** | **≤ 4** | **≤ 4** | gated case `gate·formula` (≤ deg 4); dot product `sel·sel·board` (deg 3); cond_nonzero (deg 3). **Pack adds deg 1; hash is a lookup** |
| **Constraint count** | — | ≈ 700–900 | ≈ 700–900 | `boardRange` 2n² = 242; occlusion/move O(n)×blocks; +18 pack gates (+2 lookups if Opt B) |
| **PIs** | — | 34 (Opt A: 16 state + 18 packed) / 32 (Opt B) | same | |

Notes:
- **Width headroom is the real ceiling, and it is the board cells, not the commitment.** Opt A and
  Opt B differ by only ~17 columns; both clear 1024 at n = 11 with ~160 columns of margin. The
  commitment is *not* the width bottleneck — 2n² unpacked cells are.
- Scaling past 11: at **n = 13** Opt A = 1011 (fits), Opt B = 1028 (just over) — beyond 13, old/mid
  column sharing or a fold row is needed to stay < 1024. The **hash** stays single-permutation
  through n = 15. So for the deployed target (11) and the next size up (13), the pack + single hash
  is comfortable; width, not the commitment, is what eventually bites.
- Degree budget is met with **> 4 of margin**; the commitment consumes none of it.

---

## 6. Ordered build plan, honestly costed — and the residual

The rebuild is **large**: the two refine files are ~610 KB and ~307 combined theorems, and their
capstones are NN = 2 `decide` throughout (662 `decide` in `StepRefine`, 67 in `ResolveRefine`; many
are constraint-membership decides that also must be restructured, §3.3). The occlusion math and the
field/one-hot/congruence infra (~30 % of the theory) carry; the board read/write/eq/selection/carry/
raycast/decide/choose capstones (~70 %) are re-proven as arguments. This is a **multi-week, multi-
file effort**, not a mechanical port. Ordered:

1. **Commitment family, n-generic** *(small, self-contained, do first)*. Add `packBoard` (⌈n²/15⌉
   linear gates) + `commitBoard` (Opt A PI bindings; Opt B single `node8Lookup`) to both emitters,
   parametric in n. Prove **`pack_injective`**: `packBoard b₁ = packBoard b₂` (as felt tuples) →
   cell-wise equality, from the {0,1,2,3} range pins by base-4 positional decode (the §1.2 lemma).
   *Cost: ~1 file, days. No dependence on the capstone rebuild — dispatch immediately.*
2. **`descN n` refactor** of both emitters (§4). Thread `n`; re-pin `descN 2` to the existing
   goldens (regression); add `descN 11` shape `#guard`s. *Cost: mechanical but wide; ~2 files.*
3. **Structured membership** (§3.3): replace `by decide` extraction with `List.range`/`append`
   offset lemmas so gate extraction is n-independent. *Cost: touches every `_of_sat`; foundational
   for everything after — do before the capstones.*
4. **Leg R n-generic**: eq-coords → selection → carries/flow-through → write-mid → `resolveMid`
   capstone, reusing `OcclusionGeneric` (occlusion already done) and `applyMoves_cell_*`. Instantiate
   `resolve_sat_imp_resolveMid` at `descN 11`. *Cost: the bulk of `ResolveRefine`.*
5. **Leg A n-generic**: auto pin → four raycasts (induct on fuel) → decide_axis (9 cases, n-flat) →
   **choose_offset** and **step/board-update** (today's named residuals) → `automatonStep` capstone.
   *Cost: the bulk of `StepRefine`, plus closing the two open legs.*
6. **Whole turn at n = 11**: `resolve_step_sat_imp_applyTurn` over `descN 11`, glued by
   `applyTurn_factors` + `automatonStep_congr`. Validate with concrete 11×11 `#guard` witnesses
   (a real hnefatafl opening move, a blocked rook, a Daemon step) driving both legs.

**The seam residual reduces to root-injectivity on the new commitment** — and that is the payoff:

- Today `resolve_step_sat_imp_applyTurn` carries a **named seam hypothesis**: "Leg A's decoded old
  board agrees cell-wise with Leg R's decoded mid board," justified only informally by "both bind a
  `board_root8` of those columns." Nothing derives it.
- With **Option A (packed-as-PI)**, `board_mid_root(R) = board_old_root(A)` as PIs means the 9 mid
  packed felts equal the 9 old packed felts, and `pack_injective` (step 1, **a Lean theorem, no
  crypto**) gives cell-wise board equality. **The seam hypothesis becomes a discharged lemma.** The
  turn is unconditional.
- With **Option B (single hash)**, the residual is exactly **collision-resistance of one arity-16
  Poseidon2 call** — the same floor the rest of the system already assumes, with the pack half proven
  injective in Lean and **no Merkle-tree depth argument**. One CR call, not a tree.

Net: the naive n ≤ 2 padded leaf and the would-be 121-cell Merkle tree are both gone; the commitment
is ⌈n²/15⌉ degree-1 gates plus at most one permutation; and the whole-turn seam that is a bare
assumption today collapses to a base-4 injectivity theorem (Opt A) or a single-hash CR assumption
(Opt B), n-generically, validated at 11 × 11.
