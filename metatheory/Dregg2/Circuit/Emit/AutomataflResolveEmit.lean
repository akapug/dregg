/-
# Dregg2.Circuit.Emit.AutomataflResolveEmit — the EMIT-FROM-LEAN author of the automatafl m=2
move-adjudication (Leg R, `old → mid`) descriptor (`dregg-automatafl-resolve-n2`).

## What this file IS, and the law it closes

Law #1: ZERO Rust-authored constraints. The automatafl RESOLUTION AIR (`old → mid`, the OTHER half
of the turn from `AutomataflStepEmit`'s automaton step `mid → new`) was authored in RUST
(`dregg-automatafl/src/moves.rs`, `emit_resolution` / `build_r`) with NO Lean emit. This file is the
Lean author that moves it off Rust: the Leg R constraints are authored here as IR-v2 `VmConstraint2`
nodes, byte-pinned by an `emitVmJson2` `#guard`, on the same template `AutomataflStepEmit.lean` used
for the step half.

The SEMANTIC target this descriptor refines (Stage 2, NOT in this file) is
`Dregg2.Games.Automatafl.resolve_mid` / `applyMoves` / `conflictResolve` — the m=2 reference
resolution. This file is Stage 1: the descriptor STRUCTURE + byte-pin.

## SCOPE — Stages R1+R2 (this file): validity + occlusion, the faithful emission PREFIX of Leg R

`emit_resolution` (moves.rs) emits, IN ORDER:

  1. `validate_move(ma)` + `validate_move(mb)`  — THE VALIDITY GATES               ← THIS FILE
  2. `validate_occlusion(ma)` + `validate_occlusion(mb)`  — the masked line scans   ← THIS FILE
  3. `anz`/`bnz` source-non-vacuum bits                                             ← remaining
  4. the 4 `eq_coords` pattern bits + fork/collide/survive selection                ← remaining
  5. `carry_a`/`carry_b` (survive ∧ non-vac ∧ ¬occ)                                  ← remaining
  6. the `ft_a`/`ft_b` vacuum flow-through chain-endpoint destinations              ← remaining
  7. `write_mid_witnessed` — the one-hot board rewrite `mid == resolve_mid(old,..)` ← remaining
  8. `bind_board_roots` — the `board_root8` PI tail `[16..32)`                       ← remaining

This file authors legs (1) and (2) — `validate_move` and `validate_occlusion` for BOTH moves — the
CLEAN FAITHFUL PREFIX of the emission: the maximal initial segment allocated here, with the
remaining legs (3)–(8) continuing the column order after the occlusion blocks. The occlusion leg is
NOT a transcription of the Rust: moves.rs specialises on a compile-time `is_vertical`, which is
faithful for one move shape only; §2.2 replaces it with a WITNESSED direction bit pinned to the
actual coordinates, so the descriptor covers ANY rook move. Authoring a prefix keeps the Stage-2
refinement's reading of these columns byte-faithful.

`validate_move` (per move) is:
  * `decompose_coord_le` on each of `fx/fy/tx/ty` — the `0 ≤ coord ≤ n−1` range, at `n=2` a
    `rbits = 1` bit-decomposition per edge (lower `coord = b_lo`, upper `(n−1) − coord = b_hi`);
  * the ROOK-ALIGN gate `(fx−tx)(fy−ty) == 0`;
  * DISTINCTNESS `(fx−tx)² + (fy−ty)² ≠ 0` (a witnessed squared distance `dsq` + a `cond_nonzero`);
  * NOT-THE-AUTOMATON `frm ≠ auto`, `to ≠ auto` (auto-relative squared distances `fa`/`ta` gated
    against the WITNESSED auto position + `cond_nonzero`s);
  * the WITNESSED SOURCE READ `fp == old[n·fy + fx]` through a row×column one-hot pinned to `(fx,fy)`
    (2n selectors), so the source particle is bound to the coordinates the move claims.

## The board size and the automaton position — n = 2, auto WITNESSED from the board

Mirroring `AutomataflStepEmit`, this authors the minimal complete instance `n = 2` (`k = n² = 4`
cells). The NOT-AUTO gate reads the auto position from the OLD board via a WITNESSED `ax`/`ay`
row×column one-hot pinned where `old == AUTO` (a shared 10-column block, `autoReadConstraints`,
`§2.0`), exactly like the step gadget's auto pin — NOT the compile-time `old.auto` constant moves.rs
bakes (`let (ax, ay) = old.auto`). The auto MOVES each turn, so a baked constant is faithful for only
one board; the `fa`/`ta` gates expand `(fx−ax)² + (fy−ay)²` / `(tx−ax)² + (ty−ay)²` over the
witnessed `(ax, ay)` columns (`autoDistHead`), gating the move against wherever the automaton
actually sits. This is a deliberate FAITHFULNESS UPGRADE over the Rust spec (which this Lean author
supersedes; Rust is the debt). Zero-coefficient terms are dropped exactly as `AutomataflStepEmit`'s
`headToExpr` canonicalizes (Lean is the source of truth for the emitted form).

## The public-input ABI (Leg R, moves.rs `build_r_bound`)

```text
  [ 0.. 8)  old8   the CELL's pre-state root  (add_pi'd, opaque, fold-connected)
  [ 8..16)  mid8   the CELL's post-state root (== Leg A's old8 — the seam)
  [16..24)  board_old_root  CONSTRAINED board_root8(old)   ]  emitted by bind_board_roots,
  [24..32)  board_mid_root  CONSTRAINED board_root8(mid)   ]  a REMAINING leg (8) above
```

This VALIDITY slice exposes only the opaque door prefix `[0..16)` (16 `add_pi`s, never constrained
in `build_r` — faithful to their opaque treatment); the board-root PI tail `[16..32)` rides
`bind_board_roots`, which lands with the board rewrite (leg 8). So `piCount = 16` here, growing to
32 when the rewrite + roots land.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its full wire string + shape `#guard`s. NEW
file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.AutomataflResolveEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Constants (`reference.rs`). The board is `n×n`; the auto is a compile-time coord. -/

/-- The board dimension. `validate_move`'s families are `NN`-generic; this file emits `n = 2`. -/
def NN : Nat := 2
/-- `k = n²`, the number of board cells. -/
def KK : Nat := NN * NN
/-- The automaton particle felt code (`reference.rs::AUTO`). The NOT-AUTO gates gate the move's
`frm`/`to` against the WITNESSED auto position — the cell where `old == AUTO`, read from the board
by a row×column one-hot (`autoReadConstraints`), exactly as `AutomataflStepEmit`'s auto pin — NOT a
compile-time-baked `old.auto` constant. The auto moves each turn, so a baked constant would only be
faithful for one board; the witnessed read gates against wherever the automaton actually sits. -/
def AUTO_CODE : ℤ := 3

/-! ## §2 — The column layout (the `build_r_bound` + `emit_resolution` `Builder::alloc` order).

Columns are allocated exactly in the Rust order so the emitted var indices mirror the gadget:
old cells `[0..k)`, mid cells `[k..2k)`, the `one` pin, then a fixed 23-column block per move. -/

/-- `old[i]` — cell `i` of the source board (columns `0..k`). All source reads are over this board. -/
def old (i : Nat) : Nat := i
/-- `mid[i]` — cell `i` of the claimed resolved board (columns `k..2k`). Allocated to keep the
layout stable for the DEFERRED board-rewrite family (leg 8); unconstrained in this validity slice. -/
def mid (i : Nat) : Nat := KK + i
/-- The `one` pin (a column forced to 1; the always-on `cond_nonzero` selector). -/
def ONE : Nat := 2 * KK

/-! ### §2.0 — The witnessed automaton-position read (the faithfulness fix).

The NOT-AUTO gates read the auto position from the OLD board rather than baking `old.auto`. A shared
10-column block (allocated once, after `one`, before the moves — the auto is a single board-global
position, so both moves' `fa`/`ta` gate against it) mirrors `AutomataflStepEmit`'s front-end auto
pin: `ax`/`ay` bit-decomposed to `0..n−1`, a row×column one-hot pinned to `(ax, ay)`, and the dot
product `AUTO == Σ selRow·selCol·old` forcing `(ax, ay)` to be the cell holding the automaton. -/

/-- The witnessed automaton x/y coordinate columns. -/
def AX_C : Nat := 2 * KK + 1
def AY_C : Nat := 2 * KK + 2
/-- `decompose_coord_le` bits for `ax` / `ay` at `n = 2` (`rbits = 1`): lower then upper edge. -/
def axLo : Nat := 2 * KK + 3
def axHi : Nat := 2 * KK + 4
def ayLo : Nat := 2 * KK + 5
def ayHi : Nat := 2 * KK + 6
/-- The auto ROW one-hot (pinned to `ay`) and COLUMN one-hot (pinned to `ax`). -/
def selAutoRow (y : Nat) : Nat := 2 * KK + 7 + y
def selAutoCol (x : Nat) : Nat := 2 * KK + 7 + NN + x
/-- Width of the shared auto-read block: `ax`/`ay` (2) + coord bits (4) + `2n` one-hot selectors. -/
def AUTO_BLOCK_WIDTH : Nat := 6 + 2 * NN

/-- The first column of a move's 23-column `validate_move` block. Move A: base `2k+1+autoBlock`;
move B: that `+ 23`. (The auto-read block sits between `one` and the moves.) -/
def mvBase (which : Nat) : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + 23 * which

/-! ### §2.1 — The per-move column block, at base `b`. -/

/-- Witnessed move coordinates. -/
def cFx (b : Nat) : Nat := b + 0
def cFy (b : Nat) : Nat := b + 1
def cTx (b : Nat) : Nat := b + 2
def cTy (b : Nat) : Nat := b + 3
/-- `decompose_coord_le` bits (lower edge / upper edge) for each coordinate at `rbits = 1`. -/
def cFxLo (b : Nat) : Nat := b + 4
def cFxHi (b : Nat) : Nat := b + 5
def cFyLo (b : Nat) : Nat := b + 6
def cFyHi (b : Nat) : Nat := b + 7
def cTxLo (b : Nat) : Nat := b + 8
def cTxHi (b : Nat) : Nat := b + 9
def cTyLo (b : Nat) : Nat := b + 10
def cTyHi (b : Nat) : Nat := b + 11
/-- Distinctness squared distance + its `cond_nonzero` witnessed inverse. -/
def cDsq (b : Nat) : Nat := b + 12
def cDistinctInv (b : Nat) : Nat := b + 13
/-- The `frm ≠ auto` squared distance + inverse. -/
def cFa (b : Nat) : Nat := b + 14
def cFnaInv (b : Nat) : Nat := b + 15
/-- The `to ≠ auto` squared distance + inverse. -/
def cTa (b : Nat) : Nat := b + 16
def cTnaInv (b : Nat) : Nat := b + 17
/-- The witnessed source particle `fp == old[n·fy + fx]`. -/
def cFp (b : Nat) : Nat := b + 18
/-- The source row×column one-hot pair (pinned to `fy` / `fx`). -/
def cSelRow0 (b : Nat) : Nat := b + 19
def cSelRow1 (b : Nat) : Nat := b + 20
def cSelCol0 (b : Nat) : Nat := b + 21
def cSelCol1 (b : Nat) : Nat := b + 22

/-! ### §2.2 — The per-move OCCLUSION block (leg 2), at base `o`.

`validate_occlusion` (moves.rs) branches on `let is_vertical = m.frm.0 == m.to.0` — a COMPILE-TIME
bool — and that branch selects (i) which line the extract pulls (column-scan vs row-scan), (ii)
which endpoint one-hots feed the between-mask, and (iii) which coordinate the other-source passable
gate compares. A move's direction VARIES per turn, so a compile-time-specialised occlusion is
faithful for exactly one move shape — the same bug class as the baked `old.auto` constant §2.0
fixes. This Lean author emits a WITNESSED `is_vertical` BIT instead:

  * `iv` is pinned to the ACTUAL geometry by the `eq_scalar` construction over the witnessed
    coordinate columns: `dxsq == (fx − tx)²`, `neq == [dxsq ≥ 1]` (a `forced_ge0` range gadget),
    `iv == 1 − neq`. So `iv = 1` IFF `fx == tx` — no prover choice. Together with `validate_move`'s
    rook-align gate `(fx−tx)(fy−ty) == 0`, `iv = 0` forces `fy == ty` (a horizontal move).
  * BOTH line-extracts are emitted into the SAME `line[k]` columns, each gated:
    `line[k] == iv·(column-scan) + (1−iv)·(row-scan)`.
  * BOTH along-axis endpoint one-hots are emitted (`ety` pinned to `ty`, `etx` pinned to `tx`) and
    the between-mask reads the GATED combination `eto[j] == iv·ety[j] + (1−iv)·etx[j]`; likewise
    `efrom[j] == iv·selRow[j] + (1−iv)·selCol[j]` over `validate_move`'s source one-hots. (Pinning
    both `e_to` one-hots unconditionally and gating the SELECTION is strictly stronger than gating
    the one-hots themselves: each stays a genuine one-hot of its real coordinate.)
  * BOTH passable-mask comparisons are emitted: `eqx == [other.fx == fx]`, `eqy == [other.fy == fy]`
    (two `eq_scalar`s), and the mask gate is `og == iv·eqx + (1−iv)·eqy`, with the gated one-hot's
    along-index head `iv·other.fy + (1−iv)·other.fx`.

Costs width, buys generality: the descriptor covers ANY rook move, not one shape. -/

/-- `DIFF_RBITS` (moves.rs) — the range width for the squared-distance is-zero / `msum` threshold. -/
def RBITS : Nat := 9

/-- The first column of a move's `OCC_BLOCK_WIDTH`-column occlusion block. The occlusion blocks
follow BOTH `validate_move` blocks, exactly as `emit_resolution` orders the allocation. -/
def occBase (which : Nat) : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + 23 * 2 + 62 * which

/-- The witnessed `is_vertical` pin: `dxsq == (fx−tx)²`, its `forced_ge0` bit + range bits, and the
boolean `iv == 1 − [dxsq ≥ 1]`. -/
def cIvDsq (o : Nat) : Nat := o + 0
def cIvNeq (o : Nat) : Nat := o + 1
def ivNeqBit (o k : Nat) : Nat := o + 2 + k
def cIv (o : Nat) : Nat := o + 11
/-- The gated line-extract `line[k]`. -/
def cLine (o k : Nat) : Nat := o + 12 + k
/-- The `to`-endpoint one-hots: `ety` (pinned to `ty`, the vertical branch) and `etx` (`tx`). -/
def cEty (o j : Nat) : Nat := o + 14 + j
def cEtx (o j : Nat) : Nat := o + 16 + j
/-- The gated along-axis endpoint one-hots feeding the between-mask. -/
def cEfrom (o j : Nat) : Nat := o + 18 + j
def cEto (o j : Nat) : Nat := o + 20 + j
/-- The strictly-between mask. -/
def cSeg (o k : Nat) : Nat := o + 22 + k
/-- `eqx == [other.fx == fx]` (the vertical branch's passable comparison). -/
def cEqxDsq (o : Nat) : Nat := o + 24
def cEqxNeq (o : Nat) : Nat := o + 25
def eqxBit (o k : Nat) : Nat := o + 26 + k
def cEqx (o : Nat) : Nat := o + 35
/-- `eqy == [other.fy == fy]` (the horizontal branch's passable comparison). -/
def cEqyDsq (o : Nat) : Nat := o + 36
def cEqyNeq (o : Nat) : Nat := o + 37
def eqyBit (o k : Nat) : Nat := o + 38 + k
def cEqy (o : Nat) : Nat := o + 47
/-- The gated other-source mask: its gate `og` and its gated one-hot. -/
def cOg (o : Nat) : Nat := o + 48
def cOsrc (o j : Nat) : Nat := o + 49 + j
/-- The masked interior sum and the `occ = [msum ≥ 1]` threshold bit + its range bits. -/
def cMsum (o : Nat) : Nat := o + 51
def cOcc (o : Nat) : Nat := o + 52
def occBit (o k : Nat) : Nat := o + 53 + k
/-- Width of one occlusion block: `iv` pin (12) + line (2) + endpoint one-hots (8) + seg (2) +
passable masks (27) + `msum`/`occ` (11). -/
def OCC_BLOCK_WIDTH : Nat := 62

/-- Total main-trace width: `2k` board cells + `one` + the shared auto-read block + `23` per move
× 2 moves + one occlusion block per move. -/
def R_WIDTH : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + 23 * 2 + OCC_BLOCK_WIDTH * 2
/-- Only the opaque door prefix `[0..16)` (leg 8's board-root PI tail `[16..32)` is not in this
validity slice). -/
def R_PI_COUNT : Nat := 16

/-! ## §3 — `Head`: the `builder.rs` linear/product head, in Lean (verbatim shape from
`AutomataflStepEmit`). `headToExpr` lowers it to the `EmittedExpr` gate polynomial (zero-coeff terms
dropped for a clean gate; Lean is the source of truth). -/

/-- A linear/product head: `Σ (coeff, cols) + constant`; `cols = []` is the constant term. -/
structure Head where
  terms : List (ℤ × List Nat)
  const : ℤ

namespace Head
def zero : Head := ⟨[], 0⟩
def c (k : ℤ) : Head := ⟨[], k⟩
def lin (coeff : ℤ) (col : Nat) : Head := ⟨[(coeff, [col])], 0⟩
def addLin (h : Head) (coeff : ℤ) (col : Nat) : Head := ⟨h.terms ++ [(coeff, [col])], h.const⟩
def addProd (h : Head) (coeff : ℤ) (cols : List Nat) : Head := ⟨h.terms ++ [(coeff, cols)], h.const⟩
def addConst (h : Head) (k : ℤ) : Head := ⟨h.terms, h.const + k⟩
def scale (h : Head) (k : ℤ) : Head := ⟨h.terms.map (fun t => (t.1 * k, t.2)), h.const * k⟩
def append (h o : Head) : Head := ⟨h.terms ++ o.terms, h.const + o.const⟩
end Head

instance : Inhabited Head := ⟨Head.zero⟩

/-- The product `∏ vars` (empty product `= 1`), left-associated. -/
def varsProd : List Nat → EmittedExpr
  | []        => .const 1
  | co :: rest => rest.foldl (fun acc v => .mul acc (.var v)) (.var co)

/-- One term `coeff · ∏ cols` as an `EmittedExpr` (coeff `1` elides the multiplier). -/
def termToExpr : ℤ × List Nat → EmittedExpr
  | (coeff, [])   => .const coeff
  | (coeff, cols) => if coeff == 1 then varsProd cols else .mul (.const coeff) (varsProd cols)

/-- Lower a `Head` to the gate `EmittedExpr` (a left-folded sum; zero-coeff terms dropped). -/
def headToExpr (h : Head) : EmittedExpr :=
  let ts := (h.terms.filter (fun t => t.1 != 0)).map termToExpr
  let ts := if h.const == 0 then ts else ts ++ [.const h.const]
  match ts with
  | []       => .const 0
  | e :: rest => rest.foldl (fun acc x => .add acc x) e

/-- `x·(x−1)` — the boolean pin (`assert_binary`). -/
def gBin (co : Nat) : EmittedExpr := .mul (.var co) (.add (.var co) (.const (-1)))

/-- A per-row gate from a raw `EmittedExpr`. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A per-row gate from a `Head`. -/
def cgH (h : Head) : VmConstraint2 := .base (.gate (headToExpr h))

/-- `cond_nonzero(sel, val)` lowered as the gate `sel·(val·inv − 1) == 0` (the `AutomataflStepEmit`
lowering of `ConditionalNonzero`; a fresh witnessed inverse column `inv`). -/
def gCondNonzero (sel val inv : Nat) : EmittedExpr :=
  .mul (.var sel) (.add (.mul (.var val) (.var inv)) (.const (-1)))

/-! ## §4 — `validate_move` (moves.rs), the per-move validity gate block at base `b`. -/

/-- `decompose_coord_le(col, n−1)` at `n = 2` (`rbits = 1`): the lower edge `col = b_lo` and the
upper edge `(n−1) − col = b_hi`, each a boolean bit + its recomposition gate. -/
def decomposeConstraints (col loBit hiBit : Nat) : List VmConstraint2 :=
  [ cg (gBin loBit)
  , cgH ((Head.lin 1 col).addLin (-1) loBit)                              -- col − b_lo == 0
  , cg (gBin hiBit)
  , cgH (((Head.c ((NN : ℤ) - 1)).addLin (-1) col).addLin (-1) hiBit) ]   -- (n−1) − col − b_hi == 0

/-- A one-hot's two gates (`Builder::one_hot`): `Σ selⱼ == 1` and `Σ j·selⱼ == indexHead`. Written
for the `n = 2` pair `[sel0, sel1]` pinned to `idxCol` (a bare coordinate column). -/
def oneHotConstraints (sel0 sel1 idxCol : Nat) : List VmConstraint2 :=
  [ cg (gBin sel0)
  , cg (gBin sel1)
  , cgH (((Head.c (-1)).addLin 1 sel0).addLin 1 sel1)               -- sel0 + sel1 − 1 == 0
  , cgH ((Head.lin 1 sel1).addLin (-1) idxCol) ]                    -- (0·sel0 + 1·sel1) − idx == 0

/-- The witnessed source read `fp − Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x] == 0` at `n = 2`. -/
def sourceReadHead (b : Nat) : Head :=
  ((((Head.lin 1 (cFp b)).addProd (-1) [cSelRow0 b, cSelCol0 b, old 0]).addProd (-1)
      [cSelRow0 b, cSelCol1 b, old 1]).addProd (-1) [cSelRow1 b, cSelCol0 b, old 2]).addProd (-1)
      [cSelRow1 b, cSelCol1 b, old 3]

/-- The squared-distance definition `dsq − (fx−tx)² − (fy−ty)²`, expanded exactly as moves.rs
`validate_move`'s distinctness head. -/
def dsqHead (b : Nat) : Head :=
  ((((((Head.lin 1 (cDsq b)).addProd (-1) [cFx b, cFx b]).addProd 2 [cFx b, cTx b]).addProd (-1)
      [cTx b, cTx b]).addProd (-1) [cFy b, cFy b]).addProd 2 [cFy b, cTy b]).addProd (-1)
      [cTy b, cTy b]

/-- The auto-relative squared distance `out − (x−ax)² − (y−ay)²` for coordinate columns `(xc, yc)`
against the WITNESSED auto columns `(AX_C, AY_C)`, expanded as
`out − x² + 2·x·ax − ax² − y² + 2·y·ay − ay²` (every auto term a product of witnessed columns, not a
baked constant). -/
def autoDistHead (outCol xc yc : Nat) : Head :=
  ((((((Head.lin 1 outCol).addProd (-1) [xc, xc]).addProd 2 [xc, AX_C]).addProd (-1)
      [AX_C, AX_C]).addProd (-1) [yc, yc]).addProd 2 [yc, AY_C]).addProd (-1) [AY_C, AY_C]

/-- The AUTO pin: `AUTO == Σ_y Σ_x selAutoRow[y]·selAutoCol[x]·old[y·n+x]` — forces `(ax, ay)` (the
one-hot indices) to be the board cell holding the automaton (`AutomataflStepEmit.autoPinHead`). -/
def autoPinHead : Head :=
  (List.range NN).foldl (fun h (y : Nat) =>
    (List.range NN).foldl (fun h2 (x : Nat) =>
      h2.addProd 1 [selAutoRow y, selAutoCol x, old (y * NN + x)]) h) (Head.c (-AUTO_CODE))

/-- The shared witnessed automaton-position read: `ax`/`ay` bit-range decomposition, the row×column
one-hot pinned to `(ax, ay)`, and the `AUTO == Σ selRow·selCol·old` dot product. Emitted once, in
`AutomataflStepEmit`'s front-end order (decompose `ax`, decompose `ay`, row one-hot @ `ay`, column
one-hot @ `ax`, the auto pin). -/
def autoReadConstraints : List VmConstraint2 :=
  decomposeConstraints AX_C axLo axHi
  ++ decomposeConstraints AY_C ayLo ayHi
  ++ oneHotConstraints (selAutoRow 0) (selAutoRow 1) AY_C     -- auto row one-hot @ ay
  ++ oneHotConstraints (selAutoCol 0) (selAutoCol 1) AX_C     -- auto col one-hot @ ax
  ++ [ cgH autoPinHead ]

/-- The rook-alignment gate `(fx−tx)(fy−ty) == 0`, expanded as
`fx·fy − fx·ty − tx·fy + tx·ty`. -/
def rookAlignHead (b : Nat) : Head :=
  (((Head.zero.addProd 1 [cFx b, cFy b]).addProd (-1) [cFx b, cTy b]).addProd (-1)
      [cTx b, cFy b]).addProd 1 [cTx b, cTy b]

/-- The full `validate_move` constraint block for the move at base `b`, in emission order. -/
def validateMove (b : Nat) : List VmConstraint2 :=
  decomposeConstraints (cFx b) (cFxLo b) (cFxHi b)
  ++ decomposeConstraints (cFy b) (cFyLo b) (cFyHi b)
  ++ decomposeConstraints (cTx b) (cTxLo b) (cTxHi b)
  ++ decomposeConstraints (cTy b) (cTyLo b) (cTyHi b)
  ++ [ cgH (rookAlignHead b) ]                                       -- rook-aligned
  ++ [ cgH (dsqHead b) ]                                             -- dsq definition
  ++ [ cg (gCondNonzero ONE (cDsq b) (cDistinctInv b)) ]            -- distinct: dsq ≠ 0
  ++ [ cgH (autoDistHead (cFa b) (cFx b) (cFy b)) ]                 -- fa = |frm − auto|²
  ++ [ cg (gCondNonzero ONE (cFa b) (cFnaInv b)) ]                  -- frm ≠ auto
  ++ [ cgH (autoDistHead (cTa b) (cTx b) (cTy b)) ]                 -- ta = |to − auto|²
  ++ [ cg (gCondNonzero ONE (cTa b) (cTnaInv b)) ]                  -- to ≠ auto
  ++ oneHotConstraints (cSelRow0 b) (cSelRow1 b) (cFy b)            -- source row one-hot @ fy
  ++ oneHotConstraints (cSelCol0 b) (cSelCol1 b) (cFx b)            -- source col one-hot @ fx
  ++ [ cgH (sourceReadHead b) ]                                     -- fp == old[n·fy + fx]

/-! ## §4.5 — The `builder.rs` range primitives, in Lean (`range_nonneg` / `forced_ge0` /
`eq_scalar` / `one_hot_gated`), then `validate_occlusion` with the WITNESSED direction bit. -/

/-- `Builder::range_nonneg(head, rbits)` with bits at `bit0 ..< bit0+rbits`: each bit boolean, then
the recomposition `head − Σ 2^k·b_k == 0`. A negative/over-range head has no satisfying bits, so the
leaf is UNSAT — the genuine non-negativity proof. -/
def rangeNonnegConstraints (h : Head) (bit0 rbits : Nat) : List VmConstraint2 :=
  (List.range rbits).map (fun k => cg (gBin (bit0 + k)))
  ++ [ cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k)) h) ]

/-- `Builder::forced_ge0`'s range head `2·ib·d + ib − d − 1` (verbatim term order). -/
def forcedGe0Term (d : Head) (ib : Nat) : Head :=
  ((((d.terms.foldl (fun acc t => acc.addProd (2 * t.1) (ib :: t.2)) Head.zero).addProd
      (2 * d.const) [ib]).addLin 1 ib).append (d.scale (-1))).addConst (-1)

/-- `Builder::forced_ge0(d)` — the boolean `ib` FORCED to `[d ≥ 0]`: `ib` boolean, then
`range_nonneg(2·ib·d + ib − d − 1)`. Only the honest bit admits a non-negative term. -/
def forcedGe0Constraints (d : Head) (ib bit0 : Nat) : List VmConstraint2 :=
  cg (gBin ib) :: rangeNonnegConstraints (forcedGe0Term d ib) bit0 RBITS

/-- `eq_scalar(a, c)` — `eq == [a == c]`, pinned by an is-zero over `(a−c)²`: the witnessed
`dsq == a² − 2ac + c²`, `neq == [dsq ≥ 1]` (a `forced_ge0`), `eq == 1 − neq`. A PROVEN boolean
function of the two witnessed columns — no prover freedom. -/
def eqScalarConstraints (a c dsqCol neqCol bit0 eqCol : Nat) : List VmConstraint2 :=
  [ cgH ((((Head.lin 1 dsqCol).addProd (-1) [a, a]).addProd 2 [a, c]).addProd (-1) [c, c]) ]
  ++ forcedGe0Constraints ((Head.lin 1 dsqCol).addConst (-1)) neqCol bit0
  ++ [ cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1)) ]

/-- `Builder::one_hot_gated` at `n = 2`: selectors boolean, `Σ sel == gate`, and
`Σ j·selⱼ == gate·indexHead` (the index head multiplied THROUGH the gate, term by term). -/
def oneHotGatedConstraints (sel0 sel1 gate : Nat) (idx : Head) : List VmConstraint2 :=
  [ cg (gBin sel0)
  , cg (gBin sel1)
  , cgH (((Head.lin (-1) gate).addLin 1 sel0).addLin 1 sel1)
  , cgH ((idx.terms.foldl (fun acc t => acc.addProd (-t.1) (gate :: t.2))
            ((Head.lin 0 sel0).addLin 1 sel1)).addProd (-idx.const) [gate]) ]

/-- The WITNESSED `is_vertical` bit: `iv == [fx == tx]`, by `eq_scalar` over the move's own
witnessed coordinate columns. THIS is the pin to the real geometry — the bit cannot disagree with
the move it gates. -/
def isVerticalConstraints (b o : Nat) : List VmConstraint2 :=
  eqScalarConstraints (cFx b) (cTx b) (cIvDsq o) (cIvNeq o) (ivNeqBit o 0) (cIv o)

/-- The GATED line-extract: `line[k] == iv·(Σ_x selCol[x]·old[k·n+x]) + (1−iv)·(Σ_y selRow[y]·
old[y·n+k])` — BOTH scans emitted, the column-scan gated by `iv`, the row-scan by `1−iv`. -/
def lineHead (b o k : Nat) : Head :=
  let hv := (List.range NN).foldl (fun h x =>
    h.addProd (-1) [cIv o, cSelCol0 b + x, old (k * NN + x)]) (Head.lin 1 (cLine o k))
  (List.range NN).foldl (fun h y =>
    (h.addProd (-1) [cSelRow0 b + y, old (y * NN + k)]).addProd 1
      [cIv o, cSelRow0 b + y, old (y * NN + k)]) hv

/-- `efrom[j] == iv·selRow[j] + (1−iv)·selCol[j]` — the along-axis SOURCE one-hot, selected by the
witnessed bit from `validate_move`'s two source one-hots (vertical ⇒ the row index `fy`). -/
def efromHead (b o j : Nat) : Head :=
  (((Head.lin 1 (cEfrom o j)).addProd (-1) [cIv o, cSelRow0 b + j]).addLin (-1)
      (cSelCol0 b + j)).addProd 1 [cIv o, cSelCol0 b + j]

/-- `eto[j] == iv·ety[j] + (1−iv)·etx[j]` — the along-axis DESTINATION one-hot, selected from the
two unconditionally-pinned endpoint one-hots. -/
def etoHead (o j : Nat) : Head :=
  (((Head.lin 1 (cEto o j)).addProd (-1) [cIv o, cEty o j]).addLin (-1)
      (cEtx o j)).addProd 1 [cIv o, cEtx o j]

/-- `seg[k] == Σ_{j1<k<j2} (efrom[j1]·eto[j2] + eto[j1]·efrom[j2])` — the ORDER-INDEPENDENT
strictly-between mask (no per-position range gadget). At `n = 2` the index set is empty for every
`k`, so the family forces `seg[k] == 0`: a 2-line has no strictly-interior cell. -/
def segHead (o k : Nat) : Head :=
  (List.range k).foldl (fun h j1 =>
    ((List.range NN).filter (fun j2 => k < j2)).foldl (fun h2 j2 =>
      (h2.addProd (-1) [cEfrom o j1, cEto o j2]).addProd (-1) [cEto o j1, cEfrom o j2]) h)
    (Head.lin 1 (cSeg o k))

/-- `og == iv·eqx + (1−iv)·eqy` — the other-source passable GATE: on a vertical move the other
source lies on this line iff its `x` matches, on a horizontal one iff its `y` does. BOTH comparisons
are emitted; the witnessed bit selects. -/
def ogHead (o : Nat) : Head :=
  (((Head.lin 1 (cOg o)).addProd (-1) [cIv o, cEqx o]).addLin (-1) (cEqy o)).addProd 1
    [cIv o, cEqy o]

/-- The masked interior sum `msum == Σ_k seg[k]·(1 − osrc[k])·line[k]`, expanded as
`Σ seg·line − Σ seg·osrc·line` (moves.rs' term order). -/
def msumHead (o : Nat) : Head :=
  (List.range NN).foldl (fun h k =>
    (h.addProd (-1) [cSeg o k, cLine o k]).addProd 1 [cSeg o k, cOsrc o k, cLine o k])
    (Head.lin 1 (cMsum o))

/-- **`validate_occlusion`** for the move at base `b`, occlusion block at `o`, whose OTHER moving
source is the move at base `ob` — authored with a WITNESSED direction bit so it covers ANY rook
move, in `validate_occlusion`'s emission order (iv pin, line extract, endpoint one-hots, between
mask, passable mask, masked sum + threshold). -/
def validateOcclusion (b o ob : Nat) : List VmConstraint2 :=
  isVerticalConstraints b o
  ++ (List.range NN).map (fun k => cgH (lineHead b o k))
  ++ oneHotConstraints (cEty o 0) (cEty o 1) (cTy b)              -- e_to (vertical) @ ty
  ++ oneHotConstraints (cEtx o 0) (cEtx o 1) (cTx b)              -- e_to (horizontal) @ tx
  ++ (List.range NN).map (fun j => cgH (efromHead b o j))
  ++ (List.range NN).map (fun j => cgH (etoHead o j))
  ++ (List.range NN).map (fun k => cgH (segHead o k))
  ++ eqScalarConstraints (cFx ob) (cFx b) (cEqxDsq o) (cEqxNeq o) (eqxBit o 0) (cEqx o)
  ++ eqScalarConstraints (cFy ob) (cFy b) (cEqyDsq o) (cEqyNeq o) (eqyBit o 0) (cEqy o)
  ++ [ cgH (ogHead o) ]
  ++ oneHotGatedConstraints (cOsrc o 0) (cOsrc o 1) (cOg o)
       ((((Head.zero.addProd 1 [cIv o, cFy ob]).addLin 1 (cFx ob)).addProd (-1) [cIv o, cFx ob]))
  ++ [ cgH (msumHead o) ]
  ++ forcedGe0Constraints ((Head.lin 1 (cMsum o)).addConst (-1)) (cOcc o) (occBit o 0)

/-! ## §5 — The descriptor: the `one` pin followed by `validate_move` for both moves. -/

/-- The `one_col` pin (`Head::lin(1, one).add_const(-1)` ⇒ `one − 1 == 0`). -/
def onePin : VmConstraint2 := cgH ((Head.lin 1 ONE).addConst (-1))

/-- The flat Leg-R constraint list, in `emit_resolution`'s emission order: the `one` pin, the shared
witnessed auto-read block, `validate_move` for both moves, then `validate_occlusion` for both moves
(each with the OTHER move as its passable moving source). -/
def resolveConstraints : List VmConstraint2 :=
  onePin :: (autoReadConstraints
    ++ validateMove (mvBase 0) ++ validateMove (mvBase 1)
    ++ validateOcclusion (mvBase 0) (occBase 0) (mvBase 1)
    ++ validateOcclusion (mvBase 1) (occBase 1) (mvBase 0))

/-- **`automataflResolveDesc`** — the automatafl m=2 move-adjudication (Leg R) VALIDITY descriptor,
AUTHORED IN LEAN. Stage R1: `validate_move ×2` (the faithful emission prefix of `emit_resolution`);
the occlusion / conflict-selection / flow-through / board-rewrite / board-root-PI legs are the next
stage. -/
def automataflResolveDesc : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-resolve-n2"
  , traceWidth  := R_WIDTH
  , piCount     := R_PI_COUNT
  , tables      := []
  , constraints := resolveConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — The byte-pinned wire golden + shape pins. -/

#guard automataflResolveDesc.name == "dregg-automatafl-resolve-n2"
#guard automataflResolveDesc.traceWidth == 189
#guard automataflResolveDesc.traceWidth == R_WIDTH
#guard automataflResolveDesc.piCount == 16
#guard automataflResolveDesc.constraints.length == 226
#guard automataflResolveDesc.tables.length == 0
#guard automataflResolveDesc.hashSites.length == 0
#guard automataflResolveDesc.ranges.length == 0
#guard autoReadConstraints.length == 17
#guard (validateMove (mvBase 0)).length == 32
#guard (validateMove (mvBase 1)).length == 32
#guard (validateOcclusion (mvBase 0) (occBase 0) (mvBase 1)).length == 72
#guard (validateOcclusion (mvBase 1) (occBase 1) (mvBase 0)).length == 72
-- the occlusion blocks tile the trace tail exactly: occBase 0 == the validity width, and the last
-- allocated column (`occBit o 8`) is the final column of the trace.
#guard occBase 0 == 65
#guard occBase 1 == occBase 0 + OCC_BLOCK_WIDTH
#guard occBit (occBase 1) 8 + 1 == R_WIDTH
-- the witnessed direction bit is pinned by an eq_scalar over the move's OWN coordinate columns
#guard (isVerticalConstraints (mvBase 0) (occBase 0)).length == 13

-- THE WIRE GOLDEN (byte-pinned; captured from the emitter). Stage R1+R2: `one` + the witnessed
-- auto-read + `validate_move ×2` + `validate_occlusion ×2` (WITNESSED direction bit).
#guard emitVmJson2 automataflResolveDesc ==
  "{\"name\":\"dregg-automatafl-resolve-n2\",\"ir\":2,\"trace_width\":189,\"public_input_count\":16,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":47}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"var\",\"v\":55}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":66}}},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":67}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":68}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":69}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":70}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":71}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":72}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":73}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":74}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":75}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":77},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":78},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"var\",\"v\":82}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":83},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":40}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":41}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":79}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":81}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":81}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":80}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":82}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":82}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":87}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":88}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":89},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":90}}},\"r\":{\"t\":\"var\",\"v\":90}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":91}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":92}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":93}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":94}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":95}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":96}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":97}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":98}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":99}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":100},\"r\":{\"t\":\"var\",\"v\":90}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":101},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":107},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":107},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":108},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":108},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":102}}},\"r\":{\"t\":\"var\",\"v\":102}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":103}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":104}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":106}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":107}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":108}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":109}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":110}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":111}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":112},\"r\":{\"t\":\"var\",\"v\":102}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":100}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":112}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":112}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":115}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":76}},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":76}},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":116},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"var\",\"v\":77}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":77}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"var\",\"v\":78}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":78}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":117}}},\"r\":{\"t\":\"var\",\"v\":117}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":118}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":119}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":120}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":121}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":122}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":123}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":124}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":125}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":126}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":128}}},\"r\":{\"t\":\"var\",\"v\":128}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":129}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":130}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":131}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":132}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":133}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":134}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":135}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":136}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":137}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":128}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":140},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"var\",\"v\":142}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"var\",\"v\":144}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":145},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":63}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":146},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":64}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":141}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":143}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":143}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":142}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":144}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":144}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":149}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":150}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":151},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":152}}},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":153}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":154}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":155}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":156}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":157}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":158}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":159}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":160}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":161}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":162},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":163},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":164}}},\"r\":{\"t\":\"var\",\"v\":164}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":165}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":166}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":167}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":168}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":169}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":170}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":171}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":172}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":173}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":174},\"r\":{\"t\":\"var\",\"v\":164}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":162}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":174}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":174}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":175}},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":177}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":138}},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":138}},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":178},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"var\",\"v\":139}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":139}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"var\",\"v\":140}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"var\",\"v\":177}},\"r\":{\"t\":\"var\",\"v\":140}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":179}}},\"r\":{\"t\":\"var\",\"v\":179}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":180}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":181}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":182}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":183}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":184}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":185}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":186}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":187}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":188}}}}],\"hash_sites\":[],\"ranges\":[]}"

end Dregg2.Circuit.Emit.AutomataflResolveEmit
