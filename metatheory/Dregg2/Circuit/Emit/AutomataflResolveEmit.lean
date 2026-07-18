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

## SCOPE — Stage R1 (this file): the VALIDITY leg, the faithful emission PREFIX of Leg R

`emit_resolution` (moves.rs) emits, IN ORDER:

  1. `validate_move(ma)` + `validate_move(mb)`  — THE VALIDITY GATES               ← THIS FILE
  2. `validate_occlusion(ma)` + `validate_occlusion(mb)`  — the masked line scans   ← remaining
  3. `anz`/`bnz` source-non-vacuum bits                                             ← remaining
  4. the 4 `eq_coords` pattern bits + fork/collide/survive selection                ← remaining
  5. `carry_a`/`carry_b` (survive ∧ non-vac ∧ ¬occ)                                  ← remaining
  6. the `ft_a`/`ft_b` vacuum flow-through chain-endpoint destinations              ← remaining
  7. `write_mid_witnessed` — the one-hot board rewrite `mid == resolve_mid(old,..)` ← remaining
  8. `bind_board_roots` — the `board_root8` PI tail `[16..32)`                       ← remaining

This file authors leg (1) — `validate_move` for BOTH moves — which is the CLEAN FAITHFUL PREFIX of
the emission: it is the maximal initial segment whose column layout matches `build_r` index-for-index
(everything after `validate_move ×2` begins with `validate_occlusion`, whose column count this slice
does not yet allocate). Authoring only a prefix keeps the Stage-2 refinement's reading of these
columns byte-faithful; the remaining legs (2)–(8) are the next stage (see the closing report).

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

/-- Total main-trace width: `2k` board cells + `one` + the shared auto-read block + `23` per move
× 2 moves. -/
def R_WIDTH : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + 23 * 2
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

/-! ## §5 — The descriptor: the `one` pin followed by `validate_move` for both moves. -/

/-- The `one_col` pin (`Head::lin(1, one).add_const(-1)` ⇒ `one − 1 == 0`). -/
def onePin : VmConstraint2 := cgH ((Head.lin 1 ONE).addConst (-1))

/-- The flat Leg-R VALIDITY constraint list, in `emit_resolution`'s emission order: the `one` pin,
the shared witnessed auto-read block, then `validate_move` for both moves. -/
def resolveConstraints : List VmConstraint2 :=
  onePin :: (autoReadConstraints ++ validateMove (mvBase 0) ++ validateMove (mvBase 1))

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
#guard automataflResolveDesc.traceWidth == 65
#guard automataflResolveDesc.traceWidth == R_WIDTH
#guard automataflResolveDesc.piCount == 16
#guard automataflResolveDesc.constraints.length == 82
#guard automataflResolveDesc.tables.length == 0
#guard automataflResolveDesc.hashSites.length == 0
#guard automataflResolveDesc.ranges.length == 0
#guard autoReadConstraints.length == 17
#guard (validateMove (mvBase 0)).length == 32
#guard (validateMove (mvBase 1)).length == 32

-- THE WIRE GOLDEN (byte-pinned; captured from the emitter). Stage R1: `one` + `validate_move ×2`.
#guard emitVmJson2 automataflResolveDesc ==
  "{\"name\":\"dregg-automatafl-resolve-n2\",\"ir\":2,\"trace_width\":65,\"public_input_count\":16,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":47}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"var\",\"v\":55}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}}}],\"hash_sites\":[],\"ranges\":[]}"

end Dregg2.Circuit.Emit.AutomataflResolveEmit
