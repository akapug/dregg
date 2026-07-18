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

## SCOPE — COMPLETE. All eight `emit_resolution` legs are authored here.

`emit_resolution` (moves.rs) emits, IN ORDER — every leg now Lean-authored:

  1. `validate_move(ma)` + `validate_move(mb)`  — THE VALIDITY GATES               §4
  2. `validate_occlusion(ma)` + `validate_occlusion(mb)`  — the masked line scans  §4.5
  3. `anz`/`bnz` source-non-vacuum bits                                            §4.6 leg 3
  4. the 4 `eq_coords` pattern bits + fork/collide/survive selection               §4.6 leg 4
  5. `carry_a`/`carry_b` (survive ∧ non-vac ∧ ¬occ)                                 §4.6 leg 5
  6. the `ft_a`/`ft_b` vacuum flow-through chain-endpoint destinations             §4.6 leg 6
  7. `write_mid_witnessed` — the one-hot board rewrite `mid == resolve_mid(old,..)` §4.6 leg 7
  8. `bind_board_roots` — the `board_root8` PI tail `[16..32)`                      §4.6 leg 8

The descriptor is therefore CLOSED: it does not merely gate the two moves for validity, it FORCES
the resolved board. `write_mid_witnessed` equates every `mid` cell to the one-hot rewrite of `old`
at the witnessed source and (flow-through-interpolated) destination indices, and `bind_board_roots`
publishes `board_root8(old)` and `board_root8(mid)` as CONSTRAINED public inputs — so the leaf
commits to precisely the boards it adjudicated, and Leg A's `mid8` seam has something to weld to.

## The WITNESSED discipline — two compile-time bakes converted, and the audit for the rest

This is NOT a transcription of the Rust. moves.rs specialises two gadgets on compile-time values,
each faithful for exactly ONE board / ONE move shape; both are replaced here by WITNESSED, pinned
columns:

  * **the automaton position.** moves.rs bakes `let (ax, ay) = old.auto` into the NOT-AUTO gates.
    §2.0 replaces it with an `ax`/`ay` row×column one-hot pinned where `old == AUTO`, so the gates
    range over wherever the automaton actually sits.
  * **the move direction.** moves.rs branches on `let is_vertical = m.frm.0 == m.to.0`, which
    selects the line scan, the endpoint one-hots, and the passable comparison. §2.2 replaces it
    with a witnessed `iv` bit pinned by an `eq_scalar` over the move's OWN coordinates, emits BOTH
    branches, and gates the SELECTION — covering any rook move.

Legs 3–8 were audited for the same class and need no conversion: their remaining compile-time reads
(`old.cell_at(ma.frm)`, `eq_coords`' `axv/ayv/bxv/byv`, `Placement.src_x_hot`, `dest_a_x_hot`, …)
are `Builder::alloc` WITNESS VALUES and one-hot hot-indices — the honest assignment — never
coefficients in an emitted head. Every leg-3–8 gate is already a polynomial in witnessed columns
(`fxa`, `txb`, `ft_a`, `carry_a`, …). See §2.3.

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

The door prefix `[0..16)` rides 16 bare `add_pi`s, never constrained in `build_r` — faithful to
their opaque, fold-connected treatment. The board-root tail `[16..32)` is CONSTRAINED: leg 8 emits
the two `MerkleHash8` node8 chip lookups over the actual board columns and `bind_pi`s their eight
output lanes each, so a forged root has no satisfying witness. `piCount = 32`.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its full wire string + shape `#guard`s. NEW
file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.AutomataflResolveEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleN emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Constants (`reference.rs`). The board is `n×n`; the auto is a compile-time coord. -/

/-- The board dimension. EVERY gadget family and EVERY column offset below is a function of `NN`;
this file INSTANTIATES `n = 2` (the minimal complete instance, kept so the emitted artifact stays
byte-comparable with the pinned golden). Changing this single definition re-lays the whole trace:
the coordinate bit-widths (`COORD_RBITS`), the per-move block (`MV_BLOCK_WIDTH`), the occlusion
block (`OCC_BLOCK_WIDTH`), the adjudication base (`RES0`) and the total width (`R_WIDTH`) all move
with it. -/
def NN : Nat := 2
/-- `k = n²`, the number of board cells. -/
def KK : Nat := NN * NN

/-- `decompose_coord_le`'s bit width — `ceil(log2 n)`, the number of bits needed to hold a
coordinate in `[0, n)`. `1` at `n = 2`, `4` at `n = 11`. Both edges of the range decomposition
(`coord = Σ 2^k b_k` and `(n−1) − coord = Σ 2^k b'_k`) carry this many bits. -/
def COORD_RBITS : Nat := if NN ≤ 1 then 1 else Nat.log2 (NN - 1) + 1
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
/-- `mid[i]` — cell `i` of the claimed resolved board (columns `k..2k`). FORCED cell-by-cell by
`write_mid_witnessed` (leg 7) and committed by `board_root8(mid)` (leg 8). -/
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
/-- `decompose_coord_le` bit runs for `ax` / `ay`, each `COORD_RBITS` wide, lower then upper edge
(at `n = 2`, `COORD_RBITS = 1`, so these are the single columns `2k+3 … 2k+6`). -/
def axLo : Nat := 2 * KK + 3
def axHi : Nat := 2 * KK + 3 + COORD_RBITS
def ayLo : Nat := 2 * KK + 3 + 2 * COORD_RBITS
def ayHi : Nat := 2 * KK + 3 + 3 * COORD_RBITS
/-- The auto ROW one-hot (pinned to `ay`) and COLUMN one-hot (pinned to `ax`), `n` selectors each. -/
def selAutoRow (y : Nat) : Nat := 2 * KK + 3 + 4 * COORD_RBITS + y
def selAutoCol (x : Nat) : Nat := 2 * KK + 3 + 4 * COORD_RBITS + NN + x
/-- Width of the shared auto-read block: `ax`/`ay` (2) + `4·COORD_RBITS` coord bits + `2n` one-hot
selectors. `6 + 2n` at `COORD_RBITS = 1`. -/
def AUTO_BLOCK_WIDTH : Nat := 2 + 4 * COORD_RBITS + 2 * NN

/-- Width of one `validate_move` block: 4 coordinate columns + `8·COORD_RBITS` range bits (two edges
on each of four coordinates) + `dsq`/`inv`/`fa`/`inv`/`ta`/`inv` (6) + the source particle (1) +
`2n` source one-hot selectors. `23` at `n = 2`. -/
def MV_BLOCK_WIDTH : Nat := 4 + 8 * COORD_RBITS + 6 + 1 + 2 * NN

/-- The first column of a move's `MV_BLOCK_WIDTH`-column `validate_move` block. Move A: base
`2k+1+autoBlock`; move B: that `+ MV_BLOCK_WIDTH`. (The auto-read block sits between `one` and the
moves.) -/
def mvBase (which : Nat) : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + MV_BLOCK_WIDTH * which

/-! ### §2.1 — The per-move column block, at base `b`. -/

/-- Witnessed move coordinates. -/
def cFx (b : Nat) : Nat := b + 0
def cFy (b : Nat) : Nat := b + 1
def cTx (b : Nat) : Nat := b + 2
def cTy (b : Nat) : Nat := b + 3
/-- `decompose_coord_le` bit runs (lower edge / upper edge) for each coordinate, `COORD_RBITS` wide
each, laid out `fx.lo fx.hi fy.lo fy.hi tx.lo tx.hi ty.lo ty.hi`. -/
def cFxLo (b : Nat) : Nat := b + 4
def cFxHi (b : Nat) : Nat := b + 4 + COORD_RBITS
def cFyLo (b : Nat) : Nat := b + 4 + 2 * COORD_RBITS
def cFyHi (b : Nat) : Nat := b + 4 + 3 * COORD_RBITS
def cTxLo (b : Nat) : Nat := b + 4 + 4 * COORD_RBITS
def cTxHi (b : Nat) : Nat := b + 4 + 5 * COORD_RBITS
def cTyLo (b : Nat) : Nat := b + 4 + 6 * COORD_RBITS
def cTyHi (b : Nat) : Nat := b + 4 + 7 * COORD_RBITS
/-- The first column after the coordinate range bits. -/
def mvPost (b : Nat) : Nat := b + 4 + 8 * COORD_RBITS
/-- Distinctness squared distance + its `cond_nonzero` witnessed inverse. -/
def cDsq (b : Nat) : Nat := mvPost b + 0
def cDistinctInv (b : Nat) : Nat := mvPost b + 1
/-- The `frm ≠ auto` squared distance + inverse. -/
def cFa (b : Nat) : Nat := mvPost b + 2
def cFnaInv (b : Nat) : Nat := mvPost b + 3
/-- The `to ≠ auto` squared distance + inverse. -/
def cTa (b : Nat) : Nat := mvPost b + 4
def cTnaInv (b : Nat) : Nat := mvPost b + 5
/-- The witnessed source particle `fp == old[n·fy + fx]`. -/
def cFp (b : Nat) : Nat := mvPost b + 6
/-- The source row / column one-hots (pinned to `fy` / `fx`), `n` selectors each. -/
def cSelRow (b j : Nat) : Nat := mvPost b + 7 + j
def cSelCol (b j : Nat) : Nat := mvPost b + 7 + NN + j
/-- The `n = 2` names, retained for the refinement's gate-membership fields. -/
def cSelRow0 (b : Nat) : Nat := cSelRow b 0
def cSelRow1 (b : Nat) : Nat := cSelRow b 1
def cSelCol0 (b : Nat) : Nat := cSelCol b 0
def cSelCol1 (b : Nat) : Nat := cSelCol b 1

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

/-- `DIFF_RBITS` (moves.rs) — the range width for the squared-distance is-zero / `msum` threshold.
Independent of the column LAYOUT but not of `n`: it must hold `2·(n−1)²` (the largest squared
coordinate distance) and `3n` (the largest masked interior sum). `9` bits covers both through
`n = 16`, so `n = 2` and the `n = 11` target share this width. -/
def RBITS : Nat := 9
/-- `SMALL_RBITS` (moves.rs) — the narrow range width, used by the source-non-vacuum bits (it ranges
over the particle alphabet `{0,1,2,3}` only, so it is `n`-independent). -/
def SMALL_RBITS : Nat := 5

/-- One `eq_scalar` / `forced_ge0` sub-block: `dsq`, the `neq` bit, its `RBITS` range bits, and the
`eq` bit. `12` columns at `RBITS = 9`. -/
def EQ_BLOCK_WIDTH : Nat := 3 + RBITS

/-- Width of one occlusion block: the `iv` `eq_scalar` pin (`EQ_BLOCK_WIDTH`) + six `n`-wide vectors
(`line`, `ety`, `etx`, `efrom`, `eto`, `seg`) + the two passable `eq_scalar`s (`2·EQ_BLOCK_WIDTH`) +
`og` (1) + the `n`-wide `osrc` + `msum`/`occ` and its `RBITS` range bits. `62` at `n = 2`. -/
def OCC_BLOCK_WIDTH : Nat := 3 * EQ_BLOCK_WIDTH + 7 * NN + 3 + RBITS

/-- The first column of a move's `OCC_BLOCK_WIDTH`-column occlusion block. The occlusion blocks
follow BOTH `validate_move` blocks, exactly as `emit_resolution` orders the allocation. -/
def occBase (which : Nat) : Nat :=
  2 * KK + 1 + AUTO_BLOCK_WIDTH + MV_BLOCK_WIDTH * 2 + OCC_BLOCK_WIDTH * which

/-- The witnessed `is_vertical` pin: `dxsq == (fx−tx)²`, its `forced_ge0` bit + range bits, and the
boolean `iv == 1 − [dxsq ≥ 1]`. -/
def cIvDsq (o : Nat) : Nat := o + 0
def cIvNeq (o : Nat) : Nat := o + 1
def ivNeqBit (o k : Nat) : Nat := o + 2 + k
def cIv (o : Nat) : Nat := o + 2 + RBITS
/-- The first column after the `iv` pin — the base of the six `n`-wide vectors. -/
def occVec (o : Nat) : Nat := o + EQ_BLOCK_WIDTH
/-- The gated line-extract `line[k]`. -/
def cLine (o k : Nat) : Nat := occVec o + k
/-- The `to`-endpoint one-hots: `ety` (pinned to `ty`, the vertical branch) and `etx` (`tx`). -/
def cEty (o j : Nat) : Nat := occVec o + NN + j
def cEtx (o j : Nat) : Nat := occVec o + 2 * NN + j
/-- The gated along-axis endpoint one-hots feeding the between-mask. -/
def cEfrom (o j : Nat) : Nat := occVec o + 3 * NN + j
def cEto (o j : Nat) : Nat := occVec o + 4 * NN + j
/-- The strictly-between mask. -/
def cSeg (o k : Nat) : Nat := occVec o + 5 * NN + k
/-- The base of the two passable-comparison `eq_scalar` blocks. -/
def occEq (o : Nat) : Nat := occVec o + 6 * NN
/-- `eqx == [other.fx == fx]` (the vertical branch's passable comparison). -/
def cEqxDsq (o : Nat) : Nat := occEq o + 0
def cEqxNeq (o : Nat) : Nat := occEq o + 1
def eqxBit (o k : Nat) : Nat := occEq o + 2 + k
def cEqx (o : Nat) : Nat := occEq o + 2 + RBITS
/-- `eqy == [other.fy == fy]` (the horizontal branch's passable comparison). -/
def cEqyDsq (o : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 0
def cEqyNeq (o : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 1
def eqyBit (o k : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 2 + k
def cEqy (o : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 2 + RBITS
/-- The base of the mask/threshold tail. -/
def occTail (o : Nat) : Nat := occEq o + 2 * EQ_BLOCK_WIDTH
/-- The gated other-source mask: its gate `og` and its gated one-hot. -/
def cOg (o : Nat) : Nat := occTail o + 0
def cOsrc (o j : Nat) : Nat := occTail o + 1 + j
/-- The masked interior sum and the `occ = [msum ≥ 1]` threshold bit + its range bits. -/
def cMsum (o : Nat) : Nat := occTail o + 1 + NN
def cOcc (o : Nat) : Nat := occTail o + 2 + NN
def occBit (o k : Nat) : Nat := occTail o + 3 + NN + k

/-! ### §2.3 — The ADJUDICATION columns (legs 3–8), continuing the `emit_resolution` alloc order.

Everything after the two occlusion blocks: the source-non-vacuum bits, the four `eq_coords` pattern
bits and the fork/collide/survive selection, the carries, the flow-through chain bits, the board
rewrite's one-hot endpoints, and the two `board_root8` outputs.

The WITNESSED discipline audit for these legs: `emit_resolution`'s remaining compile-time reads
(`old.cell_at(ma.frm)`, `eq_coords`' `axv/ayv/bxv/byv`, `Placement.src_x_hot`, `dest_a_x_hot`, …)
are all `Builder::alloc` WITNESS VALUES / one-hot hot-indices — the *honest assignment*, never a
baked coefficient in an emitted head. Every emitted head in legs 3–8 is already a polynomial in
witnessed columns (`fxa`, `txb`, `ft_a`, `carry_a`, …), so unlike the `old.auto` constant (§2.0) and
the `is_vertical` branch (§2.2) there is nothing here to convert: the gates already range over any
board and any move shape. -/

/-- The first adjudication column — the end of the validity+occlusion prefix. -/
def RES0 : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + MV_BLOCK_WIDTH * 2 + OCC_BLOCK_WIDTH * 2

/-- Leg 3 — `anz`/`bnz`, each a `forced_ge0(fp − 1, SMALL_RBITS)` source-non-vacuum bit. -/
def cAnz : Nat := RES0
def anzBit (k : Nat) : Nat := RES0 + 1 + k
def cBnz : Nat := RES0 + 1 + SMALL_RBITS
def bnzBit (k : Nat) : Nat := RES0 + 2 + SMALL_RBITS + k

/-- The first column after the two non-vacuum bits. -/
def NZ_WIDTH : Nat := 2 * (1 + SMALL_RBITS)

/-- Leg 4 — the four `eq_coords` blocks (`eq_ff`, `eq_tt`, `eq_ab`, `eq_ba`), `EQ_BLOCK_WIDTH`
columns each: `dsq`, the `forced_ge0` bit + its `DIFF_RBITS` range bits, and the `eq` bit. -/
def eqBase (i : Nat) : Nat := RES0 + NZ_WIDTH + EQ_BLOCK_WIDTH * i
def cEqDsq (e : Nat) : Nat := e + 0
def cEqNeq (e : Nat) : Nat := e + 1
def eqBitAt (e k : Nat) : Nat := e + 2 + k
def cEqBit (e : Nat) : Nat := e + 2 + RBITS

/-- Leg 4 (cont.) — the selection truth table: `fork`, `¬eq_ff`, the collide product chain, `surv`. -/
def SEL0 : Nat := RES0 + NZ_WIDTH + 4 * EQ_BLOCK_WIDTH
def cFork : Nat := SEL0 + 0
def cNeqFf : Nat := SEL0 + 1
def cCol1 : Nat := SEL0 + 2
def cCol2 : Nat := SEL0 + 3
def cCollide : Nat := SEL0 + 4
def cSurv : Nat := SEL0 + 5

/-- Leg 5 — the carries `survive ∧ non-vac ∧ ¬occ`, each via one product column + one gate. -/
def CAR0 : Nat := SEL0 + 6
def cSa1 : Nat := CAR0 + 0
def cCarryA : Nat := CAR0 + 1
def cSb1 : Nat := CAR0 + 2
def cCarryB : Nat := CAR0 + 3

/-- Leg 6 — the vacuum flow-through chain bits (three `not_bit`s + a 4-product chain per side). -/
def FT0 : Nat := CAR0 + 4
def cNBnz : Nat := FT0 + 0
def cNOccb : Nat := FT0 + 1
def cNEqba : Nat := FT0 + 2
def cFa1 : Nat := FT0 + 3
def cFa2 : Nat := FT0 + 4
def cFa3 : Nat := FT0 + 5
def cFtA : Nat := FT0 + 6
def cNAnz : Nat := FT0 + 7
def cNOcca : Nat := FT0 + 8
def cNEqab : Nat := FT0 + 9
def cFb1 : Nat := FT0 + 10
def cFb2 : Nat := FT0 + 11
def cFb3 : Nat := FT0 + 12
def cFtB : Nat := FT0 + 13

/-- Leg 7 — `write_mid_witnessed`'s per-piece `one_hot_rowcol` endpoints: for each of the two
pieces, a source row/column one-hot pair then a destination row/column one-hot pair (`2n` selectors
per endpoint, `8` columns per piece, in `one_hot_rowcol`'s row-then-column order). -/
def WR0 : Nat := FT0 + 14
/-- Four `n`-wide one-hots per piece: source row, source column, destination row, destination
column. `8` columns per piece at `n = 2`. -/
def WR_PIECE_WIDTH : Nat := 4 * NN
def wSrcRow (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + j
def wSrcCol (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + NN + j
def wDstRow (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + 2 * NN + j
def wDstCol (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + 3 * NN + j

/-- Leg 8 — `bind_board_roots`: the shared `mh8_zero` pad column and the two 8-felt roots. -/
def MH0 : Nat := WR0 + WR_PIECE_WIDTH * 2
def MH8_ZERO : Nat := MH0
def oldRootCols : List Nat := (List.range 8).map (MH0 + 1 + ·)
def midRootCols : List Nat := (List.range 8).map (MH0 + 9 + ·)

/-- Total main-trace width: the validity+occlusion prefix (`RES0`) followed by the adjudication
columns, ending with the two board roots. -/
def R_WIDTH : Nat := MH0 + 17
/-- The full Leg-R public-input ABI: the opaque door prefix `[0..16)` plus the two CONSTRAINED
`board_root8` roots `[16..24)` (old) and `[24..32)` (mid), bound by leg 8. -/
def R_PI_COUNT : Nat := 32

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

/-- `∏_{s∈set}(col − s)` — the membership gate (`assert_member`), left-associated, byte-identical to
`AutomataflStepEmit.memberExpr`. -/
def memberExpr (col : Nat) (set : List ℤ) : EmittedExpr :=
  match set with
  | []        => .const 1
  | s :: rest => rest.foldl (fun acc t => .mul acc (.add (.var col) (.const (-t))))
                   (.add (.var col) (.const (-s)))

/-- A per-row gate from a raw `EmittedExpr`. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A per-row gate from a `Head`. -/
def cgH (h : Head) : VmConstraint2 := .base (.gate (headToExpr h))

/-- `cond_nonzero(sel, val)` lowered as the gate `sel·(val·inv − 1) == 0` (the `AutomataflStepEmit`
lowering of `ConditionalNonzero`; a fresh witnessed inverse column `inv`). -/
def gCondNonzero (sel val inv : Nat) : EmittedExpr :=
  .mul (.var sel) (.add (.mul (.var val) (.var inv)) (.const (-1)))

/-! ### §3.1 — The `n`-generic range primitive (hoisted: `decomposeConstraints` uses it).

`Builder::range_nonneg(head, rbits)` with bits at `bit0 ..< bit0+rbits`: each bit boolean, then the
recomposition `head − Σ 2^k·b_k == 0`. A negative/over-range head has no satisfying bits, so the leaf
is UNSAT — the genuine non-negativity proof. -/
def rangeNonnegConstraints (h : Head) (bit0 rbits : Nat) : List VmConstraint2 :=
  (List.range rbits).map (fun k => cg (gBin (bit0 + k)))
  ++ [ cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k)) h) ]

/-! ## §4 — `validate_move` (moves.rs), the per-move validity gate block at base `b`. -/

/-- `decompose_coord_le(col, n−1)` — the `COORD_RBITS`-bit range decomposition of BOTH edges: the
lower edge `col = Σ 2^k b_k` and the upper edge `(n−1) − col = Σ 2^k b'_k`, each bit boolean plus its
recomposition gate. At `n = 2` (`COORD_RBITS = 1`) this is the old two-bit form verbatim; at
`n = 11` it is four bits per edge. -/
def decomposeConstraints (col loBit0 hiBit0 : Nat) : List VmConstraint2 :=
  rangeNonnegConstraints (Head.lin 1 col) loBit0 COORD_RBITS
  ++ rangeNonnegConstraints ((Head.c ((NN : ℤ) - 1)).addLin (-1) col) hiBit0 COORD_RBITS

/-- A one-hot's gates (`Builder::one_hot`), `n`-generically over a selector LIST and a general index
HEAD (the `AutomataflStepEmit.oneHotConstraints` shape): every selector boolean, `Σ selⱼ == 1`, and
`Σ j·selⱼ == idx`. The `j = 0` term carries coefficient `0` and is dropped by `headToExpr`, so at
`n = 2` this emits byte-identically to the old hand-written pair. -/
def oneHotConstraints (sels : List Nat) (idx : Head) : List VmConstraint2 :=
  sels.map (fun s => cg (gBin s))
  ++ [ cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ]
  ++ [ cgH (((sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).append
              (idx.scale (-1))) ]

/-- The one-hot pinned to a bare coordinate COLUMN — the common case. -/
def oneHotAtCol (sels : List Nat) (idxCol : Nat) : List VmConstraint2 :=
  oneHotConstraints sels (Head.lin 1 idxCol)

/-- The source row / column selector lists for the move at base `b`. -/
def selRowCols (b : Nat) : List Nat := (List.range NN).map (cSelRow b)
def selColCols (b : Nat) : List Nat := (List.range NN).map (cSelCol b)

/-- The witnessed source read `fp − Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x] == 0`, an `n×n` fold. -/
def sourceReadHead (b : Nat) : Head :=
  (List.range NN).foldl (fun h y =>
    (List.range NN).foldl (fun h2 x =>
      h2.addProd (-1) [cSelRow b y, cSelCol b x, old (y * NN + x)]) h) (Head.lin 1 (cFp b))

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
  ++ oneHotAtCol ((List.range NN).map selAutoRow) AY_C        -- auto row one-hot @ ay
  ++ oneHotAtCol ((List.range NN).map selAutoCol) AX_C        -- auto col one-hot @ ax
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
  ++ oneHotAtCol (selRowCols b) (cFy b)                             -- source row one-hot @ fy
  ++ oneHotAtCol (selColCols b) (cFx b)                             -- source col one-hot @ fx
  ++ [ cgH (sourceReadHead b) ]                                     -- fp == old[n·fy + fx]

/-! ## §4.5 — The `builder.rs` range primitives, in Lean (`range_nonneg` / `forced_ge0` /
`eq_scalar` / `one_hot_gated`), then `validate_occlusion` with the WITNESSED direction bit. -/

/-- `Builder::forced_ge0`'s range head `2·ib·d + ib − d − 1` (verbatim term order). -/
def forcedGe0Term (d : Head) (ib : Nat) : Head :=
  ((((d.terms.foldl (fun acc t => acc.addProd (2 * t.1) (ib :: t.2)) Head.zero).addProd
      (2 * d.const) [ib]).addLin 1 ib).append (d.scale (-1))).addConst (-1)

/-- `Builder::forced_ge0(d)` — the boolean `ib` FORCED to `[d ≥ 0]`: `ib` boolean, then
`range_nonneg(2·ib·d + ib − d − 1)`. Only the honest bit admits a non-negative term. -/
def forcedGe0ConstraintsN (d : Head) (ib bit0 rbits : Nat) : List VmConstraint2 :=
  cg (gBin ib) :: rangeNonnegConstraints (forcedGe0Term d ib) bit0 rbits

/-- `forced_ge0` at the default `DIFF_RBITS` width. -/
def forcedGe0Constraints (d : Head) (ib bit0 : Nat) : List VmConstraint2 :=
  forcedGe0ConstraintsN d ib bit0 RBITS

/-- `eq_scalar(a, c)` — `eq == [a == c]`, pinned by an is-zero over `(a−c)²`: the witnessed
`dsq == a² − 2ac + c²`, `neq == [dsq ≥ 1]` (a `forced_ge0`), `eq == 1 − neq`. A PROVEN boolean
function of the two witnessed columns — no prover freedom. -/
def eqScalarConstraints (a c dsqCol neqCol bit0 eqCol : Nat) : List VmConstraint2 :=
  [ cgH ((((Head.lin 1 dsqCol).addProd (-1) [a, a]).addProd 2 [a, c]).addProd (-1) [c, c]) ]
  ++ forcedGe0Constraints ((Head.lin 1 dsqCol).addConst (-1)) neqCol bit0
  ++ [ cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1)) ]

/-- `Builder::one_hot_gated`, `n`-generically: selectors boolean, `Σ sel == gate`, and
`Σ j·selⱼ == gate·indexHead` (the index head multiplied THROUGH the gate, term by term). -/
def oneHotGatedConstraints (sels : List Nat) (gate : Nat) (idx : Head) : List VmConstraint2 :=
  sels.map (fun s => cg (gBin s))
  ++ [ cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.lin (-1) gate)) ]
  ++ [ cgH ((idx.terms.foldl (fun acc t => acc.addProd (-t.1) (gate :: t.2))
              (sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).addProd
              (-idx.const) [gate]) ]

/-- The WITNESSED `is_vertical` bit: `iv == [fx == tx]`, by `eq_scalar` over the move's own
witnessed coordinate columns. THIS is the pin to the real geometry — the bit cannot disagree with
the move it gates. -/
def isVerticalConstraints (b o : Nat) : List VmConstraint2 :=
  eqScalarConstraints (cFx b) (cTx b) (cIvDsq o) (cIvNeq o) (ivNeqBit o 0) (cIv o)

/-- The GATED line-extract: `line[k] == iv·(Σ_x selCol[x]·old[k·n+x]) + (1−iv)·(Σ_y selRow[y]·
old[y·n+k])` — BOTH scans emitted, the column-scan gated by `iv`, the row-scan by `1−iv`. -/
def lineHead (b o k : Nat) : Head :=
  let hv := (List.range NN).foldl (fun h x =>
    h.addProd (-1) [cIv o, cSelCol b x, old (k * NN + x)]) (Head.lin 1 (cLine o k))
  (List.range NN).foldl (fun h y =>
    (h.addProd (-1) [cSelRow b y, old (y * NN + k)]).addProd 1
      [cIv o, cSelRow b y, old (y * NN + k)]) hv

/-- `efrom[j] == iv·selRow[j] + (1−iv)·selCol[j]` — the along-axis SOURCE one-hot, selected by the
witnessed bit from `validate_move`'s two source one-hots (vertical ⇒ the row index `fy`). -/
def efromHead (b o j : Nat) : Head :=
  (((Head.lin 1 (cEfrom o j)).addProd (-1) [cIv o, cSelRow b j]).addLin (-1)
      (cSelCol b j)).addProd 1 [cIv o, cSelCol b j]

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
  ++ oneHotAtCol ((List.range NN).map (cEty o)) (cTy b)           -- e_to (vertical) @ ty
  ++ oneHotAtCol ((List.range NN).map (cEtx o)) (cTx b)           -- e_to (horizontal) @ tx
  ++ (List.range NN).map (fun j => cgH (efromHead b o j))
  ++ (List.range NN).map (fun j => cgH (etoHead o j))
  ++ (List.range NN).map (fun k => cgH (segHead o k))
  ++ eqScalarConstraints (cFx ob) (cFx b) (cEqxDsq o) (cEqxNeq o) (eqxBit o 0) (cEqx o)
  ++ eqScalarConstraints (cFy ob) (cFy b) (cEqyDsq o) (cEqyNeq o) (eqyBit o 0) (cEqy o)
  ++ [ cgH (ogHead o) ]
  ++ oneHotGatedConstraints ((List.range NN).map (cOsrc o)) (cOg o)
       ((((Head.zero.addProd 1 [cIv o, cFy ob]).addLin 1 (cFx ob)).addProd (-1) [cIv o, cFx ob]))
  ++ [ cgH (msumHead o) ]
  ++ forcedGe0Constraints ((Head.lin 1 (cMsum o)).addConst (-1)) (cOcc o) (occBit o 0)

/-! ## §4.6 — The ADJUDICATION legs (3–8): non-vacuum bits, the pattern/selection truth table,
the carries, the flow-through chain, the board rewrite, and the board-root PI tail. -/

/-- `not_bit(col)` — a fresh column pinned to `1 − col`: `c + col − 1 == 0`. -/
def notBitPin (out col : Nat) : VmConstraint2 :=
  cgH (((Head.lin 1 out).addLin 1 col).addConst (-1))

/-- `Builder::alloc_prod(a, b)` — a fresh column pinned to the product: `−out + a·b == 0`. -/
def prodPin (out a b : Nat) : VmConstraint2 :=
  cgH ((Head.lin (-1) out).addProd 1 [a, b])

/-! ### Leg 3 — the source-non-vacuum bits `anz` / `bnz`.

`anz = [fp_a − 1 ≥ 0] = [fp_a ≠ vacuum]` (particle codes are `≥ 1`; vacuum is `0`), a `forced_ge0`
at `SMALL_RBITS` over the WITNESSED source-particle column `validate_move` already bound to
`old[n·fy + fx]`. Nothing compile-time survives into the head: the Rust's `old.cell_at(ma.frm)` is
the range gadget's witness assignment, not a coefficient. -/
def srcNonVacConstraints : List VmConstraint2 :=
  forcedGe0ConstraintsN ((Head.lin 1 (cFp (mvBase 0))).addConst (-1)) cAnz (anzBit 0) SMALL_RBITS
  ++ forcedGe0ConstraintsN ((Head.lin 1 (cFp (mvBase 1))).addConst (-1)) cBnz (bnzBit 0) SMALL_RBITS

/-! ### Leg 4 — the four `eq_coords` pattern bits + the fork/collide/survive selection. -/

/-- `eq_coords((xa,ya), (xb,yb))` — `eq == [(xa,ya) == (xb,yb)]`, the 2-D twin of `eq_scalar`: the
witnessed squared distance `dsq == (xa−xb)² + (ya−yb)²` (expanded in moves.rs' term order), the
`forced_ge0` bit `neq == [dsq ≥ 1]`, and `eq == 1 − neq`. A PROVEN boolean function of the four
witnessed coordinate columns. -/
def eqCoordsConstraints (xa ya xb yb e : Nat) : List VmConstraint2 :=
  [ cgH ((((((Head.lin 1 (cEqDsq e)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
      [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb]) ]
  ++ forcedGe0Constraints ((Head.lin 1 (cEqDsq e)).addConst (-1)) (cEqNeq e) (eqBitAt e 0)
  ++ [ cgH (((Head.lin 1 (cEqBit e)).addLin 1 (cEqNeq e)).addConst (-1)) ]

/-- The four pattern bits, in `emit_resolution`'s order:
`eq_ff = [frm_a == frm_b]` (same source), `eq_tt = [to_a == to_b]` (same destination),
`eq_ab = [to_a == frm_b]` and `eq_ba = [to_b == frm_a]` (the chain relations). -/
def patternBitConstraints : List VmConstraint2 :=
  let a := mvBase 0; let b := mvBase 1
  eqCoordsConstraints (cFx a) (cFy a) (cFx b) (cFy b) (eqBase 0)   -- eq_ff
  ++ eqCoordsConstraints (cTx a) (cTy a) (cTx b) (cTy b) (eqBase 1) -- eq_tt
  ++ eqCoordsConstraints (cTx a) (cTy a) (cFx b) (cFy b) (eqBase 2) -- eq_ab
  ++ eqCoordsConstraints (cTx b) (cTy b) (cFx a) (cFy a) (eqBase 3) -- eq_ba

/-- The `n = 2` SELECTION truth table, derived from the pattern bits and the non-vacuum bits:
`fork = eq_ff ∧ ¬eq_tt` (same source, different destination ⇒ drop both);
`collide = eq_tt ∧ ¬eq_ff ∧ anz ∧ bnz` (same destination, two distinct non-vacuum sources ⇒ drop);
`survive = ¬fork ∧ ¬collide` (symmetric at `n = 2`, expanded as the inclusion–exclusion gate
`surv − 1 + fork + collide − fork·collide == 0`). -/
def selectionConstraints : List VmConstraint2 :=
  let eqFf := cEqBit (eqBase 0); let eqTt := cEqBit (eqBase 1)
  [ cgH (((Head.lin 1 cFork).addLin (-1) eqFf).addProd 1 [eqFf, eqTt])   -- fork = eq_ff·(1−eq_tt)
  , notBitPin cNeqFf eqFf
  , prodPin cCol1 eqTt cNeqFf
  , prodPin cCol2 cCol1 cAnz
  , prodPin cCollide cCol2 cBnz
  , cgH (((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1 cCollide).addProd (-1)
      [cFork, cCollide]) ]

/-! ### Leg 5 — the carries. `carry_i = survive ∧ src_nonvac_i ∧ ¬occ_i`: the piece actually
journeys only if the turn survived adjudication, its source held a piece, and its line was clear. -/
def carryConstraints : List VmConstraint2 :=
  [ prodPin cSa1 cSurv cAnz
  , cgH (((Head.lin 1 cCarryA).addProd (-1) [cSa1]).addProd 1 [cSa1, cOcc (occBase 0)])
  , prodPin cSb1 cSurv cBnz
  , cgH (((Head.lin 1 cCarryB).addProd (-1) [cSb1]).addProd 1 [cSb1, cOcc (occBase 1)]) ]

/-! ### Leg 6 — the vacuum flow-through chain (the `m = 2` caterpillar).

A surviving carrying piece lands at its own `to` EXCEPT when it rides a square the other piece is
vacating: if A's destination IS B's source and that source is VACUUM (`¬bnz` — B's "move" is the
continuation of the chain, not a second piece), then A flows THROUGH to B's destination. The
`¬eq_ba` conjunct breaks the symmetric 2-cycle so at most one side flows through.

  `ft_a = eq_ab ∧ ¬bnz ∧ survive ∧ ¬occ_b ∧ ¬eq_ba`   ⇒  `dest_a = to_b`
  `ft_b = eq_ba ∧ ¬anz ∧ survive ∧ ¬occ_a ∧ ¬eq_ab`   ⇒  `dest_b = to_a` -/
def flowThroughConstraints : List VmConstraint2 :=
  let eqAb := cEqBit (eqBase 2); let eqBa := cEqBit (eqBase 3)
  [ notBitPin cNBnz cBnz
  , notBitPin cNOccb (cOcc (occBase 1))
  , notBitPin cNEqba eqBa
  , prodPin cFa1 eqAb cNBnz
  , prodPin cFa2 cFa1 cSurv
  , prodPin cFa3 cFa2 cNOccb
  , prodPin cFtA cFa3 cNEqba
  , notBitPin cNAnz cAnz
  , notBitPin cNOcca (cOcc (occBase 0))
  , notBitPin cNEqab eqAb
  , prodPin cFb1 eqBa cNAnz
  , prodPin cFb2 cFb1 cSurv
  , prodPin cFb3 cFb2 cNOcca
  , prodPin cFtB cFb3 cNEqab ]

/-- The flow-through destination head for piece `i`: `to_i + ft_i·(to_other − to_i)` — a linear
interpolation between the piece's own destination and the chain endpoint, over the WITNESSED
destination columns and the witnessed `ft` bit. (moves.rs' `dest_a_x_head` term order.) -/
def destHead (own other ft : Nat) : Head :=
  ((Head.lin 1 own).addProd 1 [ft, other]).addProd (-1) [ft, own]

/-! ### Leg 7 — `write_mid_witnessed`, the per-cell one-hot board rewrite. -/

/-- The carry column of piece `i`. -/
def carryCol (i : Nat) : Nat := if i == 0 then cCarryA else cCarryB
/-- The witnessed source particle of piece `i` (`validate_move`'s bound `fp`). -/
def particleCol (i : Nat) : Nat := cFp (mvBase i)

/-- `one_hot_rowcol` for both endpoints of both pieces, in `write_mid_witnessed`'s allocation order
(per piece: source row @ `fy`, source column @ `fx`, destination row @ the interpolated `dest_y`,
destination column @ `dest_x`). -/
def writeEndpointConstraints : List VmConstraint2 :=
  (List.range 2).flatMap (fun i =>
    let b := mvBase i; let ob := mvBase (1 - i); let ft := if i == 0 then cFtA else cFtB
    oneHotConstraints ((List.range NN).map (wSrcRow i)) (Head.lin 1 (cFy b))
    ++ oneHotConstraints ((List.range NN).map (wSrcCol i)) (Head.lin 1 (cFx b))
    ++ oneHotConstraints ((List.range NN).map (wDstRow i)) (destHead (cTy b) (cTy ob) ft)
    ++ oneHotConstraints ((List.range NN).map (wDstCol i)) (destHead (cTx b) (cTx ob) ft))

/-- The per-cell rewrite head. With `keep[c] = (1 − is_src[c])·(1 − land[c])`,
`mid[c] == keep[c]·old[c] + Σ_i carry_i·sel_dst_i[c]·particle_i`, expanded exactly as moves.rs:
`old − Σ_i carry_i·src_i[c]·old − Σ_i carry_i·dst_i[c]·old + Σ_i carry_i·dst_i[c]·particle_i`
plus, for `i ≠ j`, the SWAP-RESTORE term `carry_i·src_i[c]·carry_j·dst_j[c]·old` — a cell that is
BOTH a cleared source AND a landing target was subtracted twice, so it is added back once. The
`(1 − land)` factor makes a landing an OVERWRITE rather than a sum (the occlusion-aware
`apply_moves` case where a piece journeys onto an uncleared, non-journeying source).

**DEFECT #5, FIXED HERE — the SHARED-ENDPOINT inclusion–exclusion.** The per-piece sums above
double-count when the two moves share an endpoint, which happens on the IDENTICAL-MOVE turn
(`ma = mb`, both carrying) that `Automatafl.conflictResolve` explicitly does NOT treat as a
conflict. Two terms close it:

* SHARED SOURCE `A·C·old` (`A = carry_a·src_a[c]`, `C = carry_b·src_b[c]`): the old particle was
  subtracted once per piece, forcing `mid ≡ −old`, which DEFECT #4's alphabet gates then reject —
  the leaf was UNSATISFIABLE on a legal turn. Added back once, a shared source vacates exactly
  once (`mid = 0`).
* SHARED LANDING `B·D·old − B·D·particle_b`: symmetric double subtraction of `old` plus a doubled
  deposit `pa + pb`; the overlap correction leaves exactly ONE particle on the square.

Both are pure inclusion–exclusion on the SAME indicators the gate already carries, so no forged
board becomes admissible: the cell value is still pinned to a single reference-determined value
(`cellAlgebra` in `AutomataflResolveRefine` proves the pinned value IS the reference's, now over
all sixteen indicator combinations minus only the same-piece exclusions `A·B = C·D = 0`). -/
def writeCellHead (c : Nat) : Head :=
  let x := c % NN; let y := c / NN
  let base := (List.range 2).foldl (fun h i =>
    ((h.addProd (-1) [carryCol i, wSrcRow i y, wSrcCol i x, old c]).addProd (-1)
        [carryCol i, wDstRow i y, wDstCol i x, old c]).addProd 1
        [carryCol i, wDstRow i y, wDstCol i x, particleCol i]) (Head.lin 1 (old c))
  let full := (List.range 2).foldl (fun h i =>
    (List.range 2).foldl (fun h2 j =>
      if i == j then h2 else
        h2.addProd 1 [carryCol i, wSrcRow i y, wSrcCol i x,
                      carryCol j, wDstRow j y, wDstCol j x, old c]) h) base
  let ie := ((full.addProd 1 [carryCol 0, wSrcRow 0 y, wSrcCol 0 x,
                              carryCol 1, wSrcRow 1 y, wSrcCol 1 x, old c]).addProd 1
              [carryCol 0, wDstRow 0 y, wDstCol 0 x,
               carryCol 1, wDstRow 1 y, wDstCol 1 x, old c]).addProd (-1)
              [carryCol 0, wDstRow 0 y, wDstCol 0 x,
               carryCol 1, wDstRow 1 y, wDstCol 1 x, particleCol 1]
  (Head.lin 1 (mid c)).append (ie.scale (-1))

/-- **`write_mid_witnessed`** — the endpoint one-hots followed by the `k` cell equalities forcing
`mid == resolve_mid(old, [ma, mb])`. -/
def writeMidConstraints : List VmConstraint2 :=
  writeEndpointConstraints ++ (List.range KK).map (fun c => cgH (writeCellHead c))

/-! ### Leg 8 — `bind_board_roots`: the two `board_root8` `MerkleHash8` chip lookups + PI tail. -/

/-- A `MerkleHash8` node8 site as an arity-16 `Poseidon2Chip` lookup absorbing `left8 ‖ right8`,
binding all 8 output lanes — the same lowering `AutomataflStepEmit.node8Lookup` uses. At `k = 4` the
board packs into ONE zero-padded leaf, folded against a zero sibling into the root. -/
def node8Lookup (leftCols rightCols outCols : List Nat) : VmConstraint2 :=
  .lookup { table := TableId.poseidon2
          , tuple := chipLookupTupleN ((leftCols ++ rightCols).map (fun c => EmittedExpr.var c)) outCols }

/-- **`bind_board_roots`**: the `mh8_zero` pin, the OLD-board root node8 + its 8 `bind_pi`s
(`[16..24)`), then the MID-board root node8 + its 8 `bind_pi`s (`[24..32)`). The roots are
EQUALITY-CONSTRAINED to the very board columns the rewrite proves over, so a forged root is UNSAT
and the published PI is a genuine ~124-bit commitment to `old` and to `mid`. -/
def bindBoardRootsConstraints : List VmConstraint2 :=
  let zeroLeaf := List.replicate 8 MH8_ZERO
  -- At `k ≤ 8` the whole board packs into ONE zero-padded leaf. This is the ONE place the layout is
  -- not yet `n`-generic in the sense of covering `n = 11` (`k = 121`), which needs a real
  -- `board_root8` Merkle TREE rather than a single padded leaf; the padding width itself is `8 − k`.
  let leaf (cells : List Nat) : List Nat := cells ++ List.replicate (8 - KK) MH8_ZERO
  [ cgH (Head.lin 1 MH8_ZERO) ]
  ++ [ node8Lookup (leaf ((List.range KK).map old)) zeroLeaf oldRootCols ]
  ++ (List.range 8).map (fun i =>
       (.base (.piBinding VmRow.first (oldRootCols[i]!) (16 + i)) : VmConstraint2))
  ++ [ node8Lookup (leaf ((List.range KK).map mid)) zeroLeaf midRootCols ]
  ++ (List.range 8).map (fun i =>
       (.base (.piBinding VmRow.first (midRootCols[i]!) (24 + i)) : VmConstraint2))

/-! ## §5 — The descriptor: the `one` pin followed by `validate_move` for both moves. -/

/-- The `one_col` pin (`Head::lin(1, one).add_const(-1)` ⇒ `one − 1 == 0`). -/
def onePin : VmConstraint2 := cgH ((Head.lin 1 ONE).addConst (-1))

/-- **The board-cell RANGE CHECKS** (DEFECT #4, closed) — `assert_member(cell, {VAC,REP,ATT,AUTO})`
for every OLD and every MID board column, exactly as `AutomataflStepEmit.boardRangeConstraints`.

Without these the board columns are UNCONSTRAINED felts entering only the source read, the
`write_mid_witnessed` rewrite and the `board_root8` Poseidon leaf, so a witness could carry
`old[c] = 4`: the circuit's source-non-vacuum bit `anz = forced_ge0(fp − 1)` is then SATISFIED (the
cell "carries a piece") while the reference `codeToParticle 4 = vacuum` (an EMPTY cell) — the
descriptor and the reference genuinely DISAGREE on the whole window `fp ∈ [4, p)`, and the 5-bit
`SMALL_RBITS` comparison supplies no a-priori window of its own. That makes the Leg R capstone FALSE
over satisfying witnesses. These `KK` + `KK` membership gates close it, and they are what makes the
OLD-board validity envelope a THEOREM of the descriptor (`boardvalid_of_sat`) rather than an
`hvalid` hypothesis carried into the capstone. The MID columns are range-checked on the same footing
so the CLAIMED resolved board is decodable too (the refinement's conclusion is about
`boardDecode mid`). -/
def boardRangeConstraints : List VmConstraint2 :=
  ((List.range KK).map (fun c => cg (memberExpr (old c) [0, 1, 2, 3])))
  ++ ((List.range KK).map (fun c => cg (memberExpr (mid c) [0, 1, 2, 3])))

/-- The flat Leg-R constraint list, in `emit_resolution`'s emission order: the `one` pin, the shared
witnessed auto-read block, `validate_move` for both moves, then `validate_occlusion` for both moves
(each with the OTHER move as its passable moving source). -/
def resolveConstraints : List VmConstraint2 :=
  onePin :: (boardRangeConstraints
    ++ autoReadConstraints
    ++ validateMove (mvBase 0) ++ validateMove (mvBase 1)
    ++ validateOcclusion (mvBase 0) (occBase 0) (mvBase 1)
    ++ validateOcclusion (mvBase 1) (occBase 1) (mvBase 0)
    ++ srcNonVacConstraints                                      -- leg 3
    ++ patternBitConstraints ++ selectionConstraints             -- leg 4
    ++ carryConstraints                                          -- leg 5
    ++ flowThroughConstraints                                    -- leg 6
    ++ writeMidConstraints                                       -- leg 7
    ++ bindBoardRootsConstraints)                                -- leg 8

/-- **`automataflResolveDesc`** — the automatafl m=2 move-adjudication (Leg R) descriptor, AUTHORED
IN LEAN, COMPLETE: `validate_move ×2` · `validate_occlusion ×2` (witnessed direction bit) · the
source-non-vacuum bits · the four `eq_coords` pattern bits and the fork/collide/survive selection ·
the carries · the vacuum flow-through chain · `write_mid_witnessed` (the one-hot board rewrite
forcing `mid == resolve_mid(old, [ma, mb])`) · `bind_board_roots` (the two `board_root8` chip
lookups and the `[16..32)` PI tail). -/
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
#guard automataflResolveDesc.traceWidth == 306
#guard automataflResolveDesc.traceWidth == R_WIDTH
#guard automataflResolveDesc.piCount == 32
#guard automataflResolveDesc.constraints.length == 379
#guard boardRangeConstraints.length == 8
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
#guard occBit (occBase 1) 8 + 1 == RES0
-- the PARAMETRIC widths agree with the n=2 instance they replaced (the re-derivation canary: these
-- are now computed from NN / COORD_RBITS / RBITS, not written down)
#guard COORD_RBITS == 1
#guard MV_BLOCK_WIDTH == 23
#guard OCC_BLOCK_WIDTH == 62
#guard EQ_BLOCK_WIDTH == 12
#guard AUTO_BLOCK_WIDTH == 10
#guard WR_PIECE_WIDTH == 8
#guard NZ_WIDTH == 12
-- the per-move block tiles: the last source-column selector is the block's final column
#guard cSelCol (mvBase 0) (NN - 1) + 1 == mvBase 1
#guard cSelCol (mvBase 1) (NN - 1) + 1 == occBase 0
-- the coordinate bit runs tile the block without overlap
#guard cTyHi (mvBase 0) + COORD_RBITS == mvPost (mvBase 0)
-- the occlusion sub-blocks tile
#guard cIv (occBase 0) + 1 == occVec (occBase 0)
#guard cSeg (occBase 0) (NN - 1) + 1 == occEq (occBase 0)
#guard cEqy (occBase 0) + 1 == occTail (occBase 0)
#guard occBit (occBase 0) (RBITS - 1) + 1 == occBase 1
-- the adjudication sub-blocks tile
#guard bnzBit (SMALL_RBITS - 1) + 1 == eqBase 0
#guard cEqBit (eqBase 3) + 1 == SEL0
#guard wDstCol 1 (NN - 1) + 1 == MH0
-- COORD_RBITS is the real ceil(log2 n): it holds n−1 and no fewer bits would
#guard NN - 1 < 2 ^ COORD_RBITS
-- the witnessed direction bit is pinned by an eq_scalar over the move's OWN coordinate columns
#guard (isVerticalConstraints (mvBase 0) (occBase 0)).length == 13
-- the ADJUDICATION legs (3-8) tile the trace tail exactly: they start where the occlusion blocks
-- end, and the last board-root column is the final column of the trace.
#guard RES0 == 189
#guard srcNonVacConstraints.length == 14
#guard patternBitConstraints.length == 52
#guard (eqCoordsConstraints 0 1 2 3 (eqBase 0)).length == 13
#guard selectionConstraints.length == 6
#guard carryConstraints.length == 4
#guard flowThroughConstraints.length == 14
#guard writeEndpointConstraints.length == 32
#guard writeMidConstraints.length == 36
#guard bindBoardRootsConstraints.length == 19
#guard midRootCols == [298, 299, 300, 301, 302, 303, 304, 305]
#guard midRootCols.getLast! + 1 == R_WIDTH
-- the board rewrite reaches EVERY cell, and each root lookup absorbs its OWN board
#guard (List.range KK).all (fun c => mid c == KK + c)

-- THE WIRE GOLDEN (byte-pinned; captured from the emitter). Stage R1+R2: `one` + the witnessed
-- auto-read + `validate_move ×2` + `validate_occlusion ×2` (WITNESSED direction bit).
-- THE WIRE GOLDEN (byte-pinned; captured from the emitter). The COMPLETE Leg R gate set:
-- `one` + the witnessed auto-read + `validate_move` x2 + `validate_occlusion` x2 (WITNESSED
-- direction bit) + the non-vacuum bits + the pattern/selection truth table + the carries + the
-- flow-through chain + `write_mid_witnessed` + `bind_board_roots` -- 379 constraints over 306
-- columns and 32 public inputs.
#guard emitVmJson2 automataflResolveDesc ==
  "{\"name\":\"dregg-automatafl-resolve-n2\",\"ir\":2,\"trace_width\":306,\"public_input_count\":32,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":47}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"var\",\"v\":55}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":66}}},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":67}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":68}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":69}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":70}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":71}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":72}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":73}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":74}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":75}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":77},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":78},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"var\",\"v\":82}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":83},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":40}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":41}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":79}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":81}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":81}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":80}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":82}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":82}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":87}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":88}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":89},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":90}}},\"r\":{\"t\":\"var\",\"v\":90}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":91}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":92}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":93}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":94}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":95}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":96}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":97}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":98}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":99}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":100},\"r\":{\"t\":\"var\",\"v\":90}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":101},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":107},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":107},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":108},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":108},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":102}}},\"r\":{\"t\":\"var\",\"v\":102}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":103}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":104}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":106}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":107}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":108}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":109}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":110}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":111}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":112},\"r\":{\"t\":\"var\",\"v\":102}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":100}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":112}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":112}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":115}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":76}},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":76}},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":116},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"var\",\"v\":77}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":77}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"var\",\"v\":78}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":78}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":117}}},\"r\":{\"t\":\"var\",\"v\":117}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":118}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":119}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":120}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":121}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":122}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":123}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":124}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":125}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":126}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":128}}},\"r\":{\"t\":\"var\",\"v\":128}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":129}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":130}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":131}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":132}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":133}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":134}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":135}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":136}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":137}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":128}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":140},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"var\",\"v\":142}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"var\",\"v\":144}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":145},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":63}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":146},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":64}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":141}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":143}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":143}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":142}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":144}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":144}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":149}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":150}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":151},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":152}}},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":153}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":154}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":155}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":156}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":157}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":158}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":159}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":160}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":161}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":162},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":163},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":164}}},\"r\":{\"t\":\"var\",\"v\":164}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":165}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":166}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":167}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":168}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":169}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":170}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":171}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":172}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":173}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":174},\"r\":{\"t\":\"var\",\"v\":164}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":162}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":174}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":174}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":175}},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":177}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":138}},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":138}},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":178},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"var\",\"v\":139}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":139}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"var\",\"v\":140}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"var\",\"v\":177}},\"r\":{\"t\":\"var\",\"v\":140}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":179}}},\"r\":{\"t\":\"var\",\"v\":179}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":180}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":181}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":182}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":183}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":184}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":185}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":186}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":187}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":188}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":190},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":190},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":191},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":191},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":192},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":192},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":193},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":193},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":189}}},\"r\":{\"t\":\"var\",\"v\":189}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":190}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":191}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":192}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":193}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":194}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":196},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":196},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":197},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":197},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":198},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":198},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":199},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":199},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":195}}},\"r\":{\"t\":\"var\",\"v\":195}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":196}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":197}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":198}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":199}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":200}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":201},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":203},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":203},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":204},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":204},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":205},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":205},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":210},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":210},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":211},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":211},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"var\",\"v\":201}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":202}}},\"r\":{\"t\":\"var\",\"v\":202}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":201}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":203}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":204}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":205}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":206}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":207}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":208}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":209}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":210}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":211}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"var\",\"v\":202}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":213},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":216},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":216},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":217},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":217},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":218},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":218},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":219},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":219},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":220},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":220},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":222},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":222},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":223},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":223},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"var\",\"v\":213}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":214}}},\"r\":{\"t\":\"var\",\"v\":214}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":213}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":215}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":216}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":217}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":218}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":219}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":220}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":221}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":222}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":223}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":224},\"r\":{\"t\":\"var\",\"v\":214}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":225},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":228},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":228},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":229},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":229},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":230},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":230},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":231},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":231},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":232},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":232},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":234},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":234},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"var\",\"v\":225}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":226}}},\"r\":{\"t\":\"var\",\"v\":226}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":225}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":227}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":228}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":229}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":230}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":231}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":232}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":233}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":234}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":235}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"var\",\"v\":226}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":237},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":240},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":240},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":241},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":241},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":242},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":242},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":243},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":243},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":244},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":244},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":245},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":245},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":246},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":246},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"var\",\"v\":237}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":238}}},\"r\":{\"t\":\"var\",\"v\":238}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":237}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":239}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":240}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":241}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":242}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":243}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":244}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":245}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":246}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":247}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":248},\"r\":{\"t\":\"var\",\"v\":238}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":212}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"var\",\"v\":224}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":250},\"r\":{\"t\":\"var\",\"v\":212}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":251}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":224},\"r\":{\"t\":\"var\",\"v\":250}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":252}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":251},\"r\":{\"t\":\"var\",\"v\":189}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":253}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":252},\"r\":{\"t\":\"var\",\"v\":195}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":249}},\"r\":{\"t\":\"var\",\"v\":253}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"var\",\"v\":253}}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":255}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":189}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":255}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":255},\"r\":{\"t\":\"var\",\"v\":117}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":257}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":195}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":257}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":257},\"r\":{\"t\":\"var\",\"v\":179}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":259},\"r\":{\"t\":\"var\",\"v\":195}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":260},\"r\":{\"t\":\"var\",\"v\":179}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":261},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":262}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"var\",\"v\":259}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":263}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":262},\"r\":{\"t\":\"var\",\"v\":254}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":264}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":263},\"r\":{\"t\":\"var\",\"v\":260}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":265}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":264},\"r\":{\"t\":\"var\",\"v\":261}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":266},\"r\":{\"t\":\"var\",\"v\":189}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":267},\"r\":{\"t\":\"var\",\"v\":117}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":268},\"r\":{\"t\":\"var\",\"v\":236}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":269}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":248},\"r\":{\"t\":\"var\",\"v\":266}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":270}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":269},\"r\":{\"t\":\"var\",\"v\":254}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":271}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":270},\"r\":{\"t\":\"var\",\"v\":267}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":272}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":271},\"r\":{\"t\":\"var\",\"v\":268}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":273},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":273},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":274},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":274},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":273},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":274},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":275},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":275},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":276},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":276},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":275},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":276},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":279},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":279},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":280},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":280},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":279},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":280},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":281},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":281},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":282},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":282},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":281},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":282},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":283},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":283},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":284},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":284},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":283},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":284},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":287},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":287},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":288},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":288},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":287},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":288},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":44}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":289}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":290},{\"t\":\"var\",\"v\":291},{\"t\":\"var\",\"v\":292},{\"t\":\"var\",\"v\":293},{\"t\":\"var\",\"v\":294},{\"t\":\"var\",\"v\":295},{\"t\":\"var\",\"v\":296},{\"t\":\"var\",\"v\":297}]},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":290,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":291,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":292,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":293,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":294,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":295,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":296,\"pi_index\":22},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":297,\"pi_index\":23},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":289},{\"t\":\"var\",\"v\":298},{\"t\":\"var\",\"v\":299},{\"t\":\"var\",\"v\":300},{\"t\":\"var\",\"v\":301},{\"t\":\"var\",\"v\":302},{\"t\":\"var\",\"v\":303},{\"t\":\"var\",\"v\":304},{\"t\":\"var\",\"v\":305}]},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":298,\"pi_index\":24},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":299,\"pi_index\":25},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":300,\"pi_index\":26},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":301,\"pi_index\":27},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":302,\"pi_index\":28},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":303,\"pi_index\":29},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":304,\"pi_index\":30},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":305,\"pi_index\":31}],\"hash_sites\":[],\"ranges\":[]}"

end Dregg2.Circuit.Emit.AutomataflResolveEmit
