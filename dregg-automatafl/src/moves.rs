//! D2 (single move) + D3 (the n=2 resolution) move gadgets. Each produces the
//! post-move `mid` board from `old + moves`, which the shared automaton gadget
//! (`crate::air::automaton_on_mid`) then steps to `new`.
//!
//! SOUND, refinement-tested and now WITNESSED-BOUND:
//!  - validity (MoveValid) — hard gates over the witnessed coordinate columns;
//!  - the source-particle read is indexed through the WITNESSED move coordinates
//!    (`old[n*fy+fx]` via a one-hot head over the `(fx,fy)` columns, not a
//!    compile-time constant) — a prover cannot read a cell other than the one its
//!    move claims;
//!  - the n=2 SELECTION is RE-DERIVED IN-CIRCUIT: the pattern bits
//!    `eq_ff / eq_tt / eq_ab / eq_ba` are pinned by is-zero gadgets over the
//!    witnessed coordinates, `vac_fa / vac_fb` by the witnessed source particles,
//!    and `fork / collide / survive` + the chain-endpoint destination are computed
//!    from those bits by the enumerated n=2 truth-table AS GATES (not taken from
//!    the reference). The survive bits and destination keys are therefore a proven
//!    function of `(old, moves)`;
//!  - occlusion (a COORDINATE-INDEXED masked line scan — see [`validate_occlusion`])
//!    and the board rewrite (one-hot writes at the witnessed source/dest indices,
//!    with a landing OVERWRITE so an occluded static occupant is replaced, not summed).
//!
//! C.4 REAL OCCLUSION (landed): occlusion is computed from the WITNESSED endpoints, not
//! a compile-time interior enumeration — one authenticated line-extract (reusing the C.2
//! perpendicular one-hot pulls the move's row/column into an n-vector) + a strictly-between
//! mask `seg[k]` (order-independent, from the endpoint one-hots — no per-position range
//! gadget) + a moving-source mask, summed and thresholded (`occ = [msum ≥ 1]`). This
//! matches `reference::occluded` for ANY rook move on ANY board size (the prerequisite for
//! a real 11×11 board). The concrete Lean `Refines` discharge is the long pole.

use dregg_circuit::dsl::circuit::ColumnKind;
use dregg_circuit::field::BabyBear;

use crate::air::{alloc_board_pub, automaton_on_mid};
use crate::builder::{Builder, Head, fb};
use crate::reference::{
    self as r, Board, Move, VAC, apply_moves, apply_turn, conflict_resolve, interior, move_valid,
};

const SMALL_RBITS: usize = 5;
/// Range width for the squared-distance is-zero (`2*(N-1)^2 < 2^DIFF_RBITS`; covers N ≤ 15).
const DIFF_RBITS: usize = 9;

/// A "1" column pinned to one (for `cond_nonzero` selectors that are always on).
fn one_col(b: &mut Builder) -> usize {
    let one = b.alloc("one", ColumnKind::Value, 1);
    b.assert_zero(&Head::lin(1, one).add_const(-1));
    one
}

/// A fresh boolean column pinned to `1 - col` (`col` must be boolean-valued).
fn not_bit(b: &mut Builder, tag: &str, col: usize) -> usize {
    let v = 1 - b.value(col).0 as i128;
    let c = b.alloc(tag, ColumnKind::Binary, v);
    b.assert_zero(&Head::lin(1, c).add_lin(1, col).add_const(-1));
    c
}

/// `eq = [coord(xa,ya) == coord(xb,yb)]`, pinned by an is-zero over the squared
/// distance `(xa-xb)^2 + (ya-yb)^2`. The distance column is a proven quadratic of
/// the WITNESSED coordinate columns; `[dsq != 0]` is the range-gadget-forced sign
/// bit, so `eq` is a proven function of the four coordinate columns.
#[allow(clippy::too_many_arguments)]
fn eq_coords(
    b: &mut Builder,
    tag: &str,
    xa: usize,
    ya: usize,
    xb: usize,
    yb: usize,
    axv: i32,
    ayv: i32,
    bxv: i32,
    byv: i32,
) -> usize {
    let dsq_val = ((axv - bxv) as i128).pow(2) + ((ayv - byv) as i128).pow(2);
    let dsq = b.alloc(format!("{tag}_dsq"), ColumnKind::Value, dsq_val);
    // dsq - [(xa-xb)^2 + (ya-yb)^2] == 0
    b.assert_zero(
        &Head::lin(1, dsq)
            .add_prod(-1, vec![xa, xa])
            .add_prod(2, vec![xa, xb])
            .add_prod(-1, vec![xb, xb])
            .add_prod(-1, vec![ya, ya])
            .add_prod(2, vec![ya, yb])
            .add_prod(-1, vec![yb, yb]),
    );
    // neq = [dsq >= 1] = [dsq != 0]; eq = 1 - neq (dsq is a sum of squares, so >= 0).
    let neq = b.forced_ge0(
        &format!("{tag}_neq"),
        &Head::lin(1, dsq).add_const(-1),
        dsq_val - 1,
        DIFF_RBITS,
    );
    let eq = b.alloc(
        format!("{tag}_eq"),
        ColumnKind::Binary,
        (dsq_val == 0) as i128,
    );
    b.assert_zero(&Head::lin(1, eq).add_lin(1, neq).add_const(-1));
    eq
}

/// Validate MoveValid(old, m) with hard gates (rejects an invalid move), returning the
/// witnessed coordinate columns `(fx,fy,tx,ty)`, the source-particle column `fp`, and the
/// row×column one-hots pinned to the source `(sel_row @ fy, sel_col @ fx)`. The source
/// particle is read through the WITNESSED `(fx,fy)` via those one-hots, so `fp == old[n*fy+fx]`
/// — the read is bound to the coordinates the move claims. The one-hots are RETURNED so the
/// occlusion line-extract can reuse the perpendicular one (C.2) rather than allocate a fresh
/// n²-wide read per interior cell.
#[allow(clippy::type_complexity)]
fn validate_move(
    b: &mut Builder,
    tag: &str,
    old: &Board,
    m: &Move,
    old_cols: &[usize],
    one: usize,
) -> (usize, usize, usize, usize, usize, Vec<usize>, Vec<usize>) {
    let n = old.n;
    let fx = b.alloc(format!("{tag}_fx"), ColumnKind::Value, m.frm.0 as i128);
    let fy = b.alloc(format!("{tag}_fy"), ColumnKind::Value, m.frm.1 as i128);
    let tx = b.alloc(format!("{tag}_tx"), ColumnKind::Value, m.to.0 as i128);
    let ty = b.alloc(format!("{tag}_ty"), ColumnKind::Value, m.to.1 as i128);
    // Range-pin each coord to 0..=n-1 by bit-decomposition (degree ≤ 2), not the degree-n
    // membership product — the same range, under the constraint-degree cap as the board grows.
    let mx = n as i128 - 1;
    b.decompose_coord_le(&format!("{tag}_fx"), fx, mx);
    b.decompose_coord_le(&format!("{tag}_fy"), fy, mx);
    b.decompose_coord_le(&format!("{tag}_tx"), tx, mx);
    b.decompose_coord_le(&format!("{tag}_ty"), ty, mx);
    // rook-aligned: (fx-tx)*(fy-ty) == 0
    b.assert_zero(
        &Head::zero()
            .add_prod(1, vec![fx, fy])
            .add_prod(-1, vec![fx, ty])
            .add_prod(-1, vec![tx, fy])
            .add_prod(1, vec![tx, ty]),
    );
    // distinct: (fx-tx)^2 + (fy-ty)^2 != 0
    let dsq_val = (m.frm.0 - m.to.0).pow(2) as i128 + (m.frm.1 - m.to.1).pow(2) as i128;
    let dsq = b.alloc(format!("{tag}_dsq"), ColumnKind::Value, dsq_val);
    b.assert_zero(
        &Head::lin(1, dsq)
            .add_prod(-1, vec![fx, fx])
            .add_prod(2, vec![fx, tx])
            .add_prod(-1, vec![tx, tx])
            .add_prod(-1, vec![fy, fy])
            .add_prod(2, vec![fy, ty])
            .add_prod(-1, vec![ty, ty]),
    );
    b.cond_nonzero(&format!("{tag}_distinct"), one, dsq, dsq_val);
    // frm != auto, to != auto (auto at old.auto, a compile-time coord for this board)
    let (ax, ay) = old.auto;
    let fa_val = (m.frm.0 - ax).pow(2) as i128 + (m.frm.1 - ay).pow(2) as i128;
    let fa = b.alloc(format!("{tag}_fa"), ColumnKind::Value, fa_val);
    b.assert_zero(
        &Head::lin(1, fa)
            .add_prod(-1, vec![fx, fx])
            .add_lin(2 * ax as i128, fx)
            .add_const(-(ax as i128 * ax as i128))
            .add_prod(-1, vec![fy, fy])
            .add_lin(2 * ay as i128, fy)
            .add_const(-(ay as i128 * ay as i128)),
    );
    b.cond_nonzero(&format!("{tag}_fna"), one, fa, fa_val);
    let ta_val = (m.to.0 - ax).pow(2) as i128 + (m.to.1 - ay).pow(2) as i128;
    let ta = b.alloc(format!("{tag}_ta"), ColumnKind::Value, ta_val);
    b.assert_zero(
        &Head::lin(1, ta)
            .add_prod(-1, vec![tx, tx])
            .add_lin(2 * ax as i128, tx)
            .add_const(-(ax as i128 * ax as i128))
            .add_prod(-1, vec![ty, ty])
            .add_lin(2 * ay as i128, ty)
            .add_const(-(ay as i128 * ay as i128)),
    );
    b.cond_nonzero(&format!("{tag}_tna"), one, ta, ta_val);
    // source particle: read from old at the WITNESSED source (fx,fy) via a row×column √n
    // read — `fp == old[n*fy+fx]`, the row `fy` and column `fx` each pinned by an n-wide
    // one-hot (2n selectors, not n²).
    let fp = b.alloc(
        format!("{tag}_fp_v"),
        ColumnKind::Value,
        old.cell_at(m.frm) as i128,
    );
    // Build the row×column one-hot pair pinned to the source (sel_row @ fy, sel_col @ fx)
    // ONCE, then do the read against it (so occlusion can reuse the perpendicular one-hot).
    let (sel_row, sel_col) = b.one_hot_rowcol(
        &format!("{tag}_fp"),
        n,
        m.frm.0 as usize,
        &Head::lin(1, fx),
        m.frm.1 as usize,
        &Head::lin(1, fy),
    );
    // fp - Σ_y Σ_x sel_row[y]·sel_col[x]·old[y·n+x] == 0 (the genuine source cell).
    let mut rd = Head::lin(1, fp);
    for y in 0..n {
        for x in 0..n {
            rd = rd.add_prod(-1, vec![sel_row[y], sel_col[x], old_cols[y * n + x]]);
        }
    }
    b.assert_zero(&rd);
    (fx, fy, tx, ty, fp, sel_row, sel_col)
}

/// A moving source OTHER than the move under occlusion analysis: its honest coordinate plus
/// its witnessed `(fx, fy)` columns. At m=2 exactly one such source can lie strictly interior
/// to a given move's line (that move's own source is an endpoint, excluded by the between-mask).
struct OtherSrc {
    frm: r::Coord,
    fx_col: usize,
    fy_col: usize,
}

/// `eq = [a == c]` for two witnessed scalar columns, pinned by an is-zero over `(a-c)^2`.
/// The 1-D twin of [`eq_coords`]; a proven boolean function of the two columns.
fn eq_scalar(b: &mut Builder, tag: &str, a: usize, a_val: i128, c: usize, c_val: i128) -> usize {
    let dsq_val = (a_val - c_val).pow(2);
    let dsq = b.alloc(format!("{tag}_dsq"), ColumnKind::Value, dsq_val);
    // dsq - (a-c)^2 == 0  =>  dsq - a² + 2ac - c² == 0.
    b.assert_zero(
        &Head::lin(1, dsq)
            .add_prod(-1, vec![a, a])
            .add_prod(2, vec![a, c])
            .add_prod(-1, vec![c, c]),
    );
    let neq = b.forced_ge0(
        &format!("{tag}_neq"),
        &Head::lin(1, dsq).add_const(-1),
        dsq_val - 1,
        DIFF_RBITS,
    );
    let eq = b.alloc(
        format!("{tag}_eq"),
        ColumnKind::Binary,
        (dsq_val == 0) as i128,
    );
    b.assert_zero(&Head::lin(1, eq).add_lin(1, neq).add_const(-1));
    eq
}

/// **C.4 — COORDINATE-INDEXED occlusion.** `occ = [∃ interior cell that is non-vacuum and not a
/// moving source]`, matching [`crate::reference::occluded`] for ANY rook move — computed from the
/// WITNESSED endpoints, not a compile-time interior enumeration:
///
/// 1. **Line-extract** — reuse the C.2 perpendicular one-hot (`sel_col @ fx` for a vertical move,
///    `sel_row @ fy` for a horizontal one) to pull the move's row/column into an n-vector `line[k]`
///    (each `line[k]` a degree-2 dot product of the perpendicular selector with a board row/column).
/// 2. **Between-mask** — `seg[k] = [min(from,to) < k < max(from,to)]`, built ORDER-INDEPENDENTLY
///    from the two along-axis endpoint one-hots as `pfx_from·sfx_to + pfx_to·sfx_from` (prefix/suffix
///    sums of one-hots — NO per-position range gadget; exactly one product fires). This move's own
///    source sits at an endpoint, so `seg` excludes it automatically.
/// 3. **Source-mask** — the OTHER move's source (if it lies on this line) is marked passable by a
///    gated one-hot `other_sel[k]` (gate = perp-coords-equal), so it never blocks.
/// 4. **Threshold** — `msum = Σ_k seg[k]·(1-other_sel[k])·line[k]` sums the particle codes (≥1 for
///    non-vacuum) of the interior, non-source cells; `occ = [msum ≥ 1]` (one range gadget). `occ` is
///    thus a proven function of the witnessed coordinates and the board.
#[allow(clippy::too_many_arguments)]
fn validate_occlusion(
    b: &mut Builder,
    tag: &str,
    old: &Board,
    m: &Move,
    old_cols: &[usize],
    fx: usize,
    fy: usize,
    tx: usize,
    ty: usize,
    sel_row: &[usize],
    sel_col: &[usize],
    other: Option<OtherSrc>,
) -> usize {
    let n = old.n;
    let is_vertical = m.frm.0 == m.to.0;

    // --- 1. the authenticated line-extract (reuse the perpendicular C.2 one-hot) ---
    let mut line = Vec::with_capacity(n);
    for k in 0..n {
        let lv = if is_vertical {
            old.cell_at((m.frm.0, k as i32)) as i128
        } else {
            old.cell_at((k as i32, m.frm.1)) as i128
        };
        let lc = b.alloc(format!("{tag}_line{k}"), ColumnKind::Value, lv);
        let mut rd = Head::lin(1, lc);
        if is_vertical {
            // column fx: line[k] = Σ_x sel_col[x]·old[k·n+x]
            for x in 0..n {
                rd = rd.add_prod(-1, vec![sel_col[x], old_cols[k * n + x]]);
            }
        } else {
            // row fy: line[k] = Σ_y sel_row[y]·old[y·n+k]
            for y in 0..n {
                rd = rd.add_prod(-1, vec![sel_row[y], old_cols[y * n + k]]);
            }
        }
        b.assert_zero(&rd);
        line.push(lc);
    }

    // --- 2. the along-axis endpoint one-hots (e_from reused, e_to fresh) ---
    let (from_val, to_val, e_from, e_to): (i32, i32, Vec<usize>, Vec<usize>) = if is_vertical {
        let e_to = b.one_hot(&format!("{tag}_ety"), n, m.to.1 as usize, &Head::lin(1, ty));
        (m.frm.1, m.to.1, sel_row.to_vec(), e_to)
    } else {
        let e_to = b.one_hot(&format!("{tag}_etx"), n, m.to.0 as usize, &Head::lin(1, tx));
        (m.frm.0, m.to.0, sel_col.to_vec(), e_to)
    };

    // --- 3. strictly-between mask seg[k] = [min < k < max], order-independent ---
    let lo = from_val.min(to_val);
    let hi = from_val.max(to_val);
    let mut seg = Vec::with_capacity(n);
    for k in 0..n {
        let seg_val = ((lo as usize) < k && k < (hi as usize)) as i128;
        let s = b.alloc(format!("{tag}_seg{k}"), ColumnKind::Binary, seg_val);
        // seg - Σ_{j1<k, j2>k} (e_from[j1]·e_to[j2] + e_to[j1]·e_from[j2]) == 0.
        let mut h = Head::lin(1, s);
        for j1 in 0..k {
            for j2 in (k + 1)..n {
                h = h.add_prod(-1, vec![e_from[j1], e_to[j2]]);
                h = h.add_prod(-1, vec![e_to[j1], e_from[j2]]);
            }
        }
        b.assert_zero(&h);
        seg.push(s);
    }

    // --- 4. the other-source passable mask (gated one-hot over its along-position) ---
    let other_sel: Vec<usize> = if let Some(o) = other {
        let (gate, along_col, along_hot) = if is_vertical {
            // on this column iff other.x == fx; its along-position is other.y
            let g = eq_scalar(
                b,
                &format!("{tag}_og"),
                o.fx_col,
                o.frm.0 as i128,
                fx,
                m.frm.0 as i128,
            );
            (g, o.fy_col, o.frm.1 as usize)
        } else {
            // on this row iff other.y == fy; its along-position is other.x
            let g = eq_scalar(
                b,
                &format!("{tag}_og"),
                o.fy_col,
                o.frm.1 as i128,
                fy,
                m.frm.1 as i128,
            );
            (g, o.fx_col, o.frm.0 as usize)
        };
        b.one_hot_gated(
            &format!("{tag}_osrc"),
            n,
            gate,
            along_hot,
            &Head::lin(1, along_col),
        )
    } else {
        Vec::new()
    };

    // --- 5. masked interior sum + occ = [msum >= 1] ---
    let mut msum_val: i128 = 0;
    let msum = b.alloc(format!("{tag}_msum"), ColumnKind::Value, 0);
    let mut h = Head::lin(1, msum);
    for k in 0..n {
        let sv = b.value(seg[k]).0 as i128;
        let ov = if other_sel.is_empty() {
            0
        } else {
            b.value(other_sel[k]).0 as i128
        };
        let lv = b.value(line[k]).0 as i128;
        msum_val += sv * (1 - ov) * lv;
        // msum - Σ seg·line + Σ seg·other·line == 0  (== msum - Σ seg·(1-other)·line)
        h = h.add_prod(-1, vec![seg[k], line[k]]);
        if !other_sel.is_empty() {
            h = h.add_prod(1, vec![seg[k], other_sel[k], line[k]]);
        }
    }
    b.set_value(msum, fb(msum_val));
    b.assert_zero(&h);

    // occ = [msum >= 1]  (particle codes are ≥ 1, so any interior non-source non-vacuum ⇒ occluded)
    b.forced_ge0(
        &format!("{tag}_occ"),
        &Head::lin(1, msum).add_const(-1),
        msum_val - 1,
        DIFF_RBITS,
    )
}

/// One surviving piece's placement data: its witnessed source row/column hot indices +
/// heads, its (in-circuit-derived) destination row/column hot indices + heads, its particle
/// column and carry bit. The row×column form addresses each cell by a product of two n-wide
/// one-hots (2n selectors per endpoint, not n²).
struct Placement {
    src_x_hot: usize,
    src_x_head: Head,
    src_y_hot: usize,
    src_y_head: Head,
    dest_x_hot: usize,
    dest_x_head: Head,
    dest_y_hot: usize,
    dest_y_head: Head,
    particle: usize,
    carry: usize,
}

/// Emit the board rewrite `mid` from `old` via one-hot writes at the WITNESSED source
/// and (derived) destination indices. For each cell `c`, with `keep[c] = (1-is_src[c])·(1-land[c])`:
///   `mid[c] = keep[c]·old[c] + Σ_i carry_i·sel_dst_i[c]·particle_i`
/// where `is_src[c] = Σ_i carry_i·sel_src_i[c]` (c is a journeying source) and
/// `land[c] = Σ_i carry_i·sel_dst_i[c]` (a carrying piece lands on c). The `(1-land)` factor
/// makes a landing an OVERWRITE, not a sum: it clears whatever sat at `c` in `old` — required
/// when a piece journeys onto an OCCLUDED (hence uncleared, non-journeying) source, the
/// occlusion-aware `apply_moves` overwrite the old additive rewrite got wrong (the corrected
/// oracle's constraint-462 case). On the honest path a landing cell is either vacuum (both
/// forms agree) or a swap/flow-through target that is also a cleared source (both forms agree),
/// so this strictly generalizes the previous rewrite. Validated cell-by-cell against `mid_cols`;
/// the selectors are one-hots pinned to the witnessed heads, so a wrong source/dest is UNSAT.
fn write_mid_witnessed(
    b: &mut Builder,
    n: usize,
    old_cols: &[usize],
    mid_cols: &[usize],
    pieces: Vec<Placement>,
) {
    let k = n * n;
    // Each endpoint is a row×column one-hot pair; cell (x,y) is addressed by the product
    // `sel_row[y]·sel_col[x]` — 2n selectors per endpoint instead of n².
    #[allow(clippy::type_complexity)]
    let mut sels: Vec<(Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>)> =
        Vec::with_capacity(pieces.len());
    for (i, p) in pieces.iter().enumerate() {
        let (src_row, src_col) = b.one_hot_rowcol(
            &format!("wsrc{i}"),
            n,
            p.src_x_hot,
            &p.src_x_head,
            p.src_y_hot,
            &p.src_y_head,
        );
        let (dst_row, dst_col) = b.one_hot_rowcol(
            &format!("wdst{i}"),
            n,
            p.dest_x_hot,
            &p.dest_x_head,
            p.dest_y_hot,
            &p.dest_y_head,
        );
        sels.push((src_row, src_col, dst_row, dst_col));
    }
    for c in 0..k {
        let x = c % n;
        let y = c / n;
        // expr = keep[c]·old[c] + place[c], with keep = (1-is_src)(1-land):
        //   old - is_src·old - land·old + (is_src·land)·old + Σ place.
        let mut expr = Head::lin(1, old_cols[c]);
        for (i, p) in pieces.iter().enumerate() {
            let (src_row, src_col, dst_row, dst_col) = &sels[i];
            // - is_src_i·old : clear a carried (journeying) source
            expr = expr.add_prod(-1, vec![p.carry, src_row[y], src_col[x], old_cols[c]]);
            // - land_i·old : clear on landing (OVERWRITE) — the constraint-462 fix
            expr = expr.add_prod(-1, vec![p.carry, dst_row[y], dst_col[x], old_cols[c]]);
            // + place at dest : carry·sel_dst_row·sel_dst_col·particle
            expr = expr.add_prod(1, vec![p.carry, dst_row[y], dst_col[x], p.particle]);
        }
        // + (is_src·land)·old for i≠j : restore the cell that is BOTH a cleared source AND a
        // landing target (a swap / flow-through cycle) — subtracted twice above, added back once.
        for i in 0..pieces.len() {
            for j in 0..pieces.len() {
                if i == j {
                    continue;
                }
                let (s_row, s_col, ..) = &sels[i];
                let (.., d_row, d_col) = &sels[j];
                expr = expr.add_prod(
                    1,
                    vec![
                        pieces[i].carry,
                        s_row[y],
                        s_col[x],
                        pieces[j].carry,
                        d_row[y],
                        d_col[x],
                        old_cols[c],
                    ],
                );
            }
        }
        b.assert_zero(&Head::lin(1, mid_cols[c]).append(&expr.scale(-1)));
    }
}

/// **STAGE D2** — single move: `claimed_next == apply_turn(old, [m])`.
///
/// PUBLIC INPUTS: the door's state-binding prefix `[old8 ‖ new8]` (the cell roots, add_pi'd)
/// followed by the two CONSTRAINED board-state roots (old board, claimed-next board). See
/// [`crate::air::build_d1_bound`] for the layout and semantics. The bare [`build_d2`] uses
/// placeholder door roots; this `_bound` form takes the leg's REAL roots (the fold driver).
pub fn build_d2_bound(
    old: &Board,
    m: &Move,
    claimed_next: &Board,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    let n = old.n;
    let mut b = Builder::new(format!("automatafl-d2-n{n}"));
    let old_cols = alloc_board_pub(&mut b, "old", old);
    let mid = apply_moves(
        old,
        &conflict_resolve(
            old,
            &[*m]
                .into_iter()
                .filter(|mm| move_valid(old, mm))
                .collect::<Vec<_>>(),
        ),
    );
    let mid_cols = alloc_board_pub(&mut b, "mid", &mid);
    let new_cols = alloc_board_pub(&mut b, "new", claimed_next);
    // PI[0..16): the door's state-binding prefix (cell roots; fold-connected).
    for x in old8.iter().chain(new8.iter()) {
        b.add_pi(x.0 as i128);
    }

    let one = one_col(&mut b);
    let (fx, fy, tx, ty, fp, sel_row, sel_col) =
        validate_move(&mut b, "m0", old, m, &old_cols, one);
    let srcs = vec![m.frm];
    // occlusion (coordinate-indexed; single move ⇒ no other source) + carry
    let occ_ref = interior(m.frm, m.to)
        .iter()
        .any(|&c| old.cell_at(c) != VAC && !srcs.contains(&c));
    let occ = validate_occlusion(
        &mut b, "m0", old, m, &old_cols, fx, fy, tx, ty, &sel_row, &sel_col, None,
    );
    // src non-vacuum
    let src_nz = b.forced_ge0(
        "m0_srcnz",
        &Head::lin(1, fp).add_const(-1),
        old.cell_at(m.frm) as i128 - 1,
        SMALL_RBITS,
    );
    // carries = src_nz AND NOT occ
    let carries_ref = (old.cell_at(m.frm) != VAC) && !occ_ref;
    let carry = b.alloc("m0_carry", ColumnKind::Binary, carries_ref as i128);
    b.assert_zero(
        &Head::lin(1, carry)
            .add_prod(-1, vec![src_nz])
            .add_prod(1, vec![src_nz, occ]),
    );
    // destination = to when carries (single move: dest is m.to, indexed by witnessed tx,ty).
    write_mid_witnessed(
        &mut b,
        n,
        &old_cols,
        &mid_cols,
        vec![Placement {
            src_x_hot: m.frm.0 as usize,
            src_x_head: Head::lin(1, fx),
            src_y_hot: m.frm.1 as usize,
            src_y_head: Head::lin(1, fy),
            dest_x_hot: m.to.0 as usize,
            dest_x_head: Head::lin(1, tx),
            dest_y_hot: m.to.1 as usize,
            dest_y_head: Head::lin(1, ty),
            particle: fp,
            carry,
        }],
    );

    // then the automaton steps on mid
    automaton_on_mid(&mut b, n, &mid_cols, &mid, &new_cols);
    // PI[16..32): the CONSTRAINED board-state roots (bind_pi'd app PIs).
    crate::air::bind_board_roots(&mut b, &old_cols, &new_cols);
    b
}

/// **STAGE D2** with placeholder door roots (the fast battery).
pub fn build_d2(old: &Board, m: &Move, claimed_next: &Board) -> Builder {
    let (old8, new8) = crate::air::placeholder_roots();
    build_d2_bound(old, m, claimed_next, old8, new8)
}

pub fn build_d2_honest(old: &Board, m: &Move) -> Builder {
    let next = apply_turn(old, &[*m]);
    build_d2(old, m, &next)
}

/// The honest D2 program bound to the leg's REAL cell-state roots (the fold driver).
pub fn build_d2_honest_bound(
    old: &Board,
    m: &Move,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    let next = apply_turn(old, &[*m]);
    build_d2_bound(old, m, &next, old8, new8)
}

/// **THE m=2 RESOLUTION BODY** (shared by Leg R and the monolithic D3). Emits every
/// constraint carving `mid == resolve_mid(old, [ma, mb])` over the pre-allocated `old_cols`
/// / `mid_cols`: both moves validated, the 6 pattern bits + fork/collide/survive selection
/// + each surviving piece's chain-endpoint destination RE-DERIVED IN-CIRCUIT from the
/// witnessed coordinates + source particles (no value taken from the reference resolution),
/// then the one-hot board rewrite `write_mid_witnessed`. `mid_cols` holds the CLAIMED
/// intermediate board; a forged `mid` fails the per-cell rewrite equalities (UNSAT).
fn emit_resolution(
    bld: &mut Builder,
    old: &Board,
    ma: &Move,
    mb: &Move,
    old_cols: &[usize],
    mid_cols: &[usize],
) {
    let n = old.n;
    let one = one_col(bld);

    // Validate both moves (rejects an invalid move); source reads bound to (fx,fy).
    let (fxa, fya, txa, tya, fpa, sra, sca) = validate_move(bld, "ma", old, ma, old_cols, one);
    let (fxb, fyb, txb, tyb, fpb, srb, scb) = validate_move(bld, "mb", old, mb, old_cols, one);

    // Occlusion per move (COORDINATE-INDEXED; the OTHER move's source is the passable one).
    let occa = validate_occlusion(
        bld,
        "ma",
        old,
        ma,
        old_cols,
        fxa,
        fya,
        txa,
        tya,
        &sra,
        &sca,
        Some(OtherSrc {
            frm: mb.frm,
            fx_col: fxb,
            fy_col: fyb,
        }),
    );
    let occb = validate_occlusion(
        bld,
        "mb",
        old,
        mb,
        old_cols,
        fxb,
        fyb,
        txb,
        tyb,
        &srb,
        &scb,
        Some(OtherSrc {
            frm: ma.frm,
            fx_col: fxa,
            fy_col: fya,
        }),
    );

    // Source non-vacuum bits (vac_fa = 1-anz, vac_fb = 1-bnz).
    let anz = bld.forced_ge0(
        "ma_srcnz",
        &Head::lin(1, fpa).add_const(-1),
        old.cell_at(ma.frm) as i128 - 1,
        SMALL_RBITS,
    );
    let bnz = bld.forced_ge0(
        "mb_srcnz",
        &Head::lin(1, fpb).add_const(-1),
        old.cell_at(mb.frm) as i128 - 1,
        SMALL_RBITS,
    );

    // --- the 6 pattern bits, is-zero over the WITNESSED coordinates ---
    let eq_ff = eq_coords(
        bld, "eqff", fxa, fya, fxb, fyb, ma.frm.0, ma.frm.1, mb.frm.0, mb.frm.1,
    );
    let eq_tt = eq_coords(
        bld, "eqtt", txa, tya, txb, tyb, ma.to.0, ma.to.1, mb.to.0, mb.to.1,
    );
    // eq_ab = [to_a == frm_b], eq_ba = [to_b == frm_a] (the chain relations).
    let eq_ab = eq_coords(
        bld, "eqab", txa, tya, fxb, fyb, ma.to.0, ma.to.1, mb.frm.0, mb.frm.1,
    );
    let eq_ba = eq_coords(
        bld, "eqba", txb, tyb, fxa, fya, mb.to.0, mb.to.1, ma.frm.0, ma.frm.1,
    );

    // --- the n=2 SELECTION truth table, derived from the bits ---
    // fork    = eq_ff ∧ ¬eq_tt                     (same source, different dest → drop both)
    // collide = eq_tt ∧ ¬eq_ff ∧ ¬vac_fa ∧ ¬vac_fb (same dest, two distinct non-vac srcs → drop)
    // survive = ¬fork ∧ ¬collide                   (symmetric at n=2)
    let ffv = bld.value(eq_ff).0 as i128;
    let ttv = bld.value(eq_tt).0 as i128;
    let fork_val = ffv * (1 - ttv);
    let fork_c = bld.alloc("fork", ColumnKind::Binary, fork_val);
    // fork - eq_ff + eq_ff*eq_tt == 0
    bld.assert_zero(
        &Head::lin(1, fork_c)
            .add_lin(-1, eq_ff)
            .add_prod(1, vec![eq_ff, eq_tt]),
    );
    let neq_ff = not_bit(bld, "neqff", eq_ff);
    let col1 = bld.alloc_prod("col_c1", eq_tt, neq_ff);
    let col2 = bld.alloc_prod("col_c2", col1, anz);
    let collide_c = bld.alloc_prod("collide", col2, bnz);
    let surv_val = (1 - fork_val) * (1 - bld.value(collide_c).0 as i128);
    let surv = bld.alloc("surv", ColumnKind::Binary, surv_val);
    // surv - 1 + fork + collide - fork*collide == 0
    bld.assert_zero(
        &Head::lin(1, surv)
            .add_const(-1)
            .add_lin(1, fork_c)
            .add_lin(1, collide_c)
            .add_prod(-1, vec![fork_c, collide_c]),
    );

    // carries_i = survive ∧ src_nonvac_i ∧ ¬occ_i.
    let sa1 = bld.alloc_prod("ma_c1", surv, anz);
    let carr_a_val = bld.value(sa1).0 as i128 * (1 - bld.value(occa).0 as i128);
    let carry_a = bld.alloc("ma_carry", ColumnKind::Binary, carr_a_val);
    bld.assert_zero(
        &Head::lin(1, carry_a)
            .add_prod(-1, vec![sa1])
            .add_prod(1, vec![sa1, occa]),
    );
    let sb1 = bld.alloc_prod("mb_c1", surv, bnz);
    let carr_b_val = bld.value(sb1).0 as i128 * (1 - bld.value(occb).0 as i128);
    let carry_b = bld.alloc("mb_carry", ColumnKind::Binary, carr_b_val);
    bld.assert_zero(
        &Head::lin(1, carry_b)
            .add_prod(-1, vec![sb1])
            .add_prod(1, vec![sb1, occb]),
    );

    // --- chain-endpoint destination, derived from the bits ---
    // At n=2 a surviving carrying piece lands at its own `to` EXCEPT the vacuum
    // flow-through case: when A's `to` is B's source and that source is VACUUM (so B's
    // resolved unoccluded move continues the chain), A flows THROUGH to B's dest.
    //   ft_a = eq_ab ∧ ¬vac... : eq_ab ∧ ¬bnz ∧ survive ∧ ¬occb ∧ ¬eq_ba  → dest_a = to_b
    //   ft_b = eq_ba ∧ ¬anz ∧ survive ∧ ¬occa ∧ ¬eq_ab                     → dest_b = to_a
    let n_bnz = not_bit(bld, "nbnz", bnz);
    let n_occb = not_bit(bld, "noccb", occb);
    let n_eqba = not_bit(bld, "neqba", eq_ba);
    let fa1 = bld.alloc_prod("fta1", eq_ab, n_bnz);
    let fa2 = bld.alloc_prod("fta2", fa1, surv);
    let fa3 = bld.alloc_prod("fta3", fa2, n_occb);
    let ft_a = bld.alloc_prod("ft_a", fa3, n_eqba);

    let n_anz = not_bit(bld, "nanz", anz);
    let n_occa = not_bit(bld, "nocca", occa);
    let n_eqab = not_bit(bld, "neqab", eq_ab);
    let fb1 = bld.alloc_prod("ftb1", eq_ba, n_anz);
    let fb2 = bld.alloc_prod("ftb2", fb1, surv);
    let fb3 = bld.alloc_prod("ftb3", fb2, n_occa);
    let ft_b = bld.alloc_prod("ft_b", fb3, n_eqab);

    let ft_a_val = bld.value(ft_a).0 as i128;
    let ft_b_val = bld.value(ft_b).0 as i128;
    // dest_a x-index = to_a.x + ft_a*(to_b.x - to_a.x); y-index likewise. Each a proven fn
    // of the (witnessed) coords + ft_a — the row/column split of the flow-through endpoint.
    let dest_a_x_hot = (ma.to.0 as i128 + ft_a_val * (mb.to.0 as i128 - ma.to.0 as i128)) as usize;
    let dest_a_y_hot = (ma.to.1 as i128 + ft_a_val * (mb.to.1 as i128 - ma.to.1 as i128)) as usize;
    let dest_a_x_head = Head::lin(1, txa)
        .add_prod(1, vec![ft_a, txb])
        .add_prod(-1, vec![ft_a, txa]);
    let dest_a_y_head = Head::lin(1, tya)
        .add_prod(1, vec![ft_a, tyb])
        .add_prod(-1, vec![ft_a, tya]);
    let dest_b_x_hot = (mb.to.0 as i128 + ft_b_val * (ma.to.0 as i128 - mb.to.0 as i128)) as usize;
    let dest_b_y_hot = (mb.to.1 as i128 + ft_b_val * (ma.to.1 as i128 - mb.to.1 as i128)) as usize;
    let dest_b_x_head = Head::lin(1, txb)
        .add_prod(1, vec![ft_b, txa])
        .add_prod(-1, vec![ft_b, txb]);
    let dest_b_y_head = Head::lin(1, tyb)
        .add_prod(1, vec![ft_b, tya])
        .add_prod(-1, vec![ft_b, tyb]);

    write_mid_witnessed(
        bld,
        n,
        old_cols,
        mid_cols,
        vec![
            Placement {
                src_x_hot: ma.frm.0 as usize,
                src_x_head: Head::lin(1, fxa),
                src_y_hot: ma.frm.1 as usize,
                src_y_head: Head::lin(1, fya),
                dest_x_hot: dest_a_x_hot,
                dest_x_head: dest_a_x_head,
                dest_y_hot: dest_a_y_hot,
                dest_y_head: dest_a_y_head,
                particle: fpa,
                carry: carry_a,
            },
            Placement {
                src_x_hot: mb.frm.0 as usize,
                src_x_head: Head::lin(1, fxb),
                src_y_hot: mb.frm.1 as usize,
                src_y_head: Head::lin(1, fyb),
                dest_x_hot: dest_b_x_hot,
                dest_x_head: dest_b_x_head,
                dest_y_hot: dest_b_y_hot,
                dest_y_head: dest_b_y_head,
                particle: fpb,
                carry: carry_b,
            },
        ],
    );
}

/// **STAGE D3** — the n=2 resolution: `claimed_next == apply_turn(old, [a, b])`.
/// The MONOLITH: resolution (`emit_resolution`, `old → mid`) AND the automaton
/// (`mid → new`) in one AIR. The C.5 fold-leg split ([`build_r_bound`] +
/// [`build_a_bound`]) carves these apart; this one-receipt form remains for the fast
/// self-tests / size census.
pub fn build_d3_bound(
    old: &Board,
    ma: &Move,
    mb: &Move,
    claimed_next: &Board,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    let n = old.n;
    let mut bld = Builder::new(format!("automatafl-d3-n{n}"));
    let old_cols = alloc_board_pub(&mut bld, "old", old);

    // reference resolution (drives the honest witness + the public `mid`/`new`)
    let mid = r::resolve_mid(old, &[*ma, *mb]);
    let mid_cols = alloc_board_pub(&mut bld, "mid", &mid);
    let new_cols = alloc_board_pub(&mut bld, "new", claimed_next);
    // PI[0..16): the door's state-binding prefix (cell roots; fold-connected).
    for x in old8.iter().chain(new8.iter()) {
        bld.add_pi(x.0 as i128);
    }

    emit_resolution(&mut bld, old, ma, mb, &old_cols, &mid_cols);
    automaton_on_mid(&mut bld, n, &mid_cols, &mid, &new_cols);
    // PI[16..32): the CONSTRAINED board-state roots (bind_pi'd app PIs).
    crate::air::bind_board_roots(&mut bld, &old_cols, &new_cols);
    bld
}

/// **LEG R — the resolution leg (`old → mid`).** Validity + m=2 conflict
/// (fork/collide/survive) + the 2-move chain-follow/flow-through + the board rewrite,
/// producing the resolved board `mid` from `old` and the two moves (via
/// [`emit_resolution`]). It does NOT step the automaton — that is Leg A's job.
///
/// PUBLIC INPUTS (the state-binding door ABI, exactly as D1–D3):
/// ```text
///   [ 0.. 8)  old8            the CELL's pre-state root  (add_pi'd, fold-connected)
///   [ 8..16)  mid8            the CELL's post-state root (== Leg A's old8 — the seam)
///   [16..24)  board_old_root  CONSTRAINED board_root8(old)
///   [24..32)  board_mid_root  CONSTRAINED board_root8(mid)  ← THE PUBLISHED mid_root
/// ```
/// Leg R publishes `mid_root = board_root8(mid)` as its NEW-root app PI; Leg A consumes
/// the byte-identical `board_root8(mid)` as its OLD-root app PI. Modeled as two chained
/// sub-turns on the same cell, R's post-state door prefix `mid8` welds to A's pre-state
/// prefix through the deployed cell-continuity connect (`new_root[i] == old_root[i+1]`),
/// which SEQUENCES the two legs. A forged `mid` INSIDE Leg R is a leaf conflict: `mid_cols`
/// holds the CLAIMED `mid` and the `emit_resolution` rewrite equalities reject any
/// `mid ≠ resolve_mid(old, [ma, mb])` (no satisfying leaf). The board `mid_root` published
/// here / consumed by Leg A is byte-identical on the honest path; the cross-turn connect
/// that makes a mid DISAGREEMENT between the two legs UNSAT at the fold level is the one
/// open fold-driver hook (see `tests/prove_fold.rs::fold`).
pub fn build_r_bound(
    old: &Board,
    ma: &Move,
    mb: &Move,
    claimed_mid: &Board,
    old8: [BabyBear; 8],
    mid8: [BabyBear; 8],
) -> Builder {
    let n = old.n;
    let mut bld = Builder::new(format!("automatafl-legR-n{n}"));
    let old_cols = alloc_board_pub(&mut bld, "old", old);
    let mid_cols = alloc_board_pub(&mut bld, "mid", claimed_mid);
    // PI[0..16): the door's state-binding prefix (cell roots; fold-connected). Leg R's
    // post-state prefix `mid8` is what Leg A re-exposes as its pre-state prefix.
    for x in old8.iter().chain(mid8.iter()) {
        bld.add_pi(x.0 as i128);
    }
    emit_resolution(&mut bld, old, ma, mb, &old_cols, &mid_cols);
    // PI[16..32): the CONSTRAINED board-state roots — old board, and the PUBLISHED mid_root.
    crate::air::bind_board_roots(&mut bld, &old_cols, &mid_cols);
    bld
}

/// Leg R with placeholder door roots (the fast battery).
pub fn build_r(old: &Board, ma: &Move, mb: &Move, claimed_mid: &Board) -> Builder {
    let (old8, mid8) = crate::air::placeholder_roots();
    build_r_bound(old, ma, mb, claimed_mid, old8, mid8)
}

/// The honest Leg R: `claimed_mid = resolve_mid(old, [ma, mb])` (placeholder door roots).
pub fn build_r_honest(old: &Board, ma: &Move, mb: &Move) -> Builder {
    let mid = r::resolve_mid(old, &[*ma, *mb]);
    build_r(old, ma, mb, &mid)
}

/// The honest Leg R bound to the leg's REAL cell-state roots (the fold driver).
pub fn build_r_honest_bound(
    old: &Board,
    ma: &Move,
    mb: &Move,
    old8: [BabyBear; 8],
    mid8: [BabyBear; 8],
) -> Builder {
    let mid = r::resolve_mid(old, &[*ma, *mb]);
    build_r_bound(old, ma, mb, &mid, old8, mid8)
}

/// **LEG A — the automaton leg (`mid → new`).** The existing automaton gadget on the
/// already-resolved board `mid`, producing `new = automaton_step(mid)`. Structurally this
/// is D1 with `mid` as the input board: it publishes `board_root8(mid)` as its OLD-root app
/// PI (the SAME `mid_root` Leg R published) and `board_root8(new)` as its NEW-root app PI.
/// Its door prefix is `[mid8 ‖ new8]`; `mid8` is welded to Leg R's post-state prefix by the
/// deployed continuity connect.
pub fn build_a_bound(
    mid: &Board,
    claimed_new: &Board,
    mid8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    crate::air::build_d1_bound(mid, claimed_new, mid8, new8)
}

/// Leg A with placeholder door roots (the fast battery).
pub fn build_a(mid: &Board, claimed_new: &Board) -> Builder {
    let (mid8, new8) = crate::air::placeholder_roots();
    build_a_bound(mid, claimed_new, mid8, new8)
}

/// The honest Leg A: `claimed_new = automaton_step(mid)` (placeholder door roots).
pub fn build_a_honest(mid: &Board) -> Builder {
    let new = crate::reference::automaton_step(mid);
    build_a(mid, &new)
}

/// The honest Leg A bound to the leg's REAL cell-state roots (the fold driver).
pub fn build_a_honest_bound(mid: &Board, mid8: [BabyBear; 8], new8: [BabyBear; 8]) -> Builder {
    let new = crate::reference::automaton_step(mid);
    build_a_bound(mid, &new, mid8, new8)
}

/// **STAGE D3** with placeholder door roots (the fast battery).
pub fn build_d3(old: &Board, ma: &Move, mb: &Move, claimed_next: &Board) -> Builder {
    let (old8, new8) = crate::air::placeholder_roots();
    build_d3_bound(old, ma, mb, claimed_next, old8, new8)
}

pub fn build_d3_honest(old: &Board, ma: &Move, mb: &Move) -> Builder {
    let next = apply_turn(old, &[*ma, *mb]);
    build_d3(old, ma, mb, &next)
}

/// The honest D3 program bound to the leg's REAL cell-state roots (the fold driver).
pub fn build_d3_honest_bound(
    old: &Board,
    ma: &Move,
    mb: &Move,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    let next = apply_turn(old, &[*ma, *mb]);
    build_d3_bound(old, ma, mb, &next, old8, new8)
}

/// **TEST SUPPORT — the coordinate-indexed occlusion in isolation.** Builds a standalone AIR
/// carrying [`validate_move`] + [`validate_occlusion`] for `m` (and, if `other` is given, that
/// move's source as the passable "other" — both moves must be individually valid), and returns
/// `(air_accepts, occ_bit)`. Lets the differential fuzz compare the in-circuit `occ` against
/// [`crate::reference::occluded`] directly across many rook moves and board sizes.
pub fn probe_occlusion(old: &Board, m: &Move, other: Option<&Move>) -> (bool, bool) {
    let mut b = Builder::new(format!("occ-probe-n{}", old.n));
    let old_cols = alloc_board_pub(&mut b, "old", old);
    let one = one_col(&mut b);
    let (fx, fy, tx, ty, _fp, sr, sc) = validate_move(&mut b, "m", old, m, &old_cols, one);
    let other_src = other.map(|o| {
        let (ofx, ofy, ..) = validate_move(&mut b, "o", old, o, &old_cols, one);
        OtherSrc {
            frm: o.frm,
            fx_col: ofx,
            fy_col: ofy,
        }
    });
    let occ = validate_occlusion(
        &mut b, "m", old, m, &old_cols, fx, fy, tx, ty, &sr, &sc, other_src,
    );
    (b.air_accepts(), b.value(occ) != BabyBear::ZERO)
}

// ============================================================================
// THE IN-PROOF SEALED MOVE — the commit→reveal enforced INSIDE the AIR.
//
// automatafl's two seats submit their moves SIMULTANEOUSLY and SECRETLY. In D1–D3 that
// secrecy is a host discipline (the executor's commit→reveal teeth withhold the move
// until reveal). This module makes the secrecy CRYPTOGRAPHIC and IN-PROOF, the analogue
// of `dregg-multiway-tug`'s hidden-hand: each seat's move is committed as a Poseidon2
// `hash_4_to_1([frm, to, seat, nonce])` (the `*_commit` column, bound to a published
// descriptor PI); the reveal OPENS a move in-circuit — witnessing its coordinates,
// re-deriving the flattened `(frm, to)` indices, and re-hashing them (with the revealed
// seat + nonce) through the SAME `Hash4to1` Poseidon2 chip site. The `Hash4to1`
// constraint forces `commit == hash(opened)`, so opening a move that differs from the
// committed one (a post-reveal swap) needs a Poseidon2 collision — it has NO satisfying
// leaf. The simultaneous-secret is thus enforced by the PROOF, not by host non-reveal.
// ============================================================================

/// A sealed (committed) simultaneous secret move: the seat, the move, and a per-move
/// blinding nonce. The commitment `hash_4_to_1([frm_idx, to_idx, seat, nonce])` HIDES the
/// move (the nonce blinds the tiny coordinate space) and BINDS the seat to exactly it.
#[derive(Clone, Copy, Debug)]
pub struct SealedMove {
    /// Which seat submitted this move (0 or 1) — revealed on open.
    pub seat: u32,
    /// The (secret until reveal) move.
    pub mv: Move,
    /// The blinding nonce (revealed on open to re-derive the commitment).
    pub nonce: u32,
}

impl SealedMove {
    /// The board-flattened `(frm_idx, to_idx)` at board size `n`.
    fn indices(&self, n: usize) -> (u32, u32) {
        let frm = (self.mv.frm.1 as u32) * n as u32 + self.mv.frm.0 as u32;
        let to = (self.mv.to.1 as u32) * n as u32 + self.mv.to.0 as u32;
        (frm, to)
    }

    /// The Poseidon2 commitment felt `hash_4_to_1([frm, to, seat, nonce])` — the exact
    /// hash the in-AIR `Hash4to1` chip site recomputes (so the in-circuit commit column
    /// byte-matches this host value).
    pub fn commit(&self, n: usize) -> BabyBear {
        let (frm, to) = self.indices(n);
        dregg_circuit::poseidon2::hash_4_to_1(&[
            BabyBear::new(frm),
            BabyBear::new(to),
            BabyBear::new(self.seat),
            BabyBear::new(self.nonce),
        ])
    }
}

/// Emit one seat's sealed commit + in-circuit open. `committed` drives the published PI
/// commitment; `opened` is the move actually revealed (== `committed.mv` on the honest
/// path; a DIFFERENT valid move on a forged reveal, which the `Hash4to1` rejects).
fn seal_seat(
    bld: &mut Builder,
    tag: &str,
    old_cols: &[usize],
    old: &Board,
    committed: &SealedMove,
    opened: &Move,
    one: usize,
) {
    let n = old.n;
    // The opened move is a genuine, VALIDATED automatafl move; its coordinates are the
    // witnessed columns the commitment reopens.
    let (fx, fy, tx, ty, _fp, _sr, _sc) = validate_move(bld, tag, old, opened, old_cols, one);
    // Re-derive the flattened source/dest indices from the WITNESSED coordinates.
    let of = (opened.frm.1 as i128) * n as i128 + opened.frm.0 as i128;
    let ot = (opened.to.1 as i128) * n as i128 + opened.to.0 as i128;
    let frm = bld.alloc(format!("{tag}_frm"), ColumnKind::Value, of);
    bld.assert_zero(&Head::lin(1, frm).add_lin(-(n as i128), fy).add_lin(-1, fx));
    let to = bld.alloc(format!("{tag}_to"), ColumnKind::Value, ot);
    bld.assert_zero(&Head::lin(1, to).add_lin(-(n as i128), ty).add_lin(-1, tx));
    // The revealed seat (pinned public) and the revealed blinding nonce (a witnessed
    // opening — private, learned only at reveal).
    let seat = bld.alloc(
        format!("{tag}_seat"),
        ColumnKind::Binary,
        committed.seat as i128,
    );
    bld.assert_binary(seat);
    bld.assert_zero(&Head::lin(1, seat).add_const(-(committed.seat as i128)));
    let nonce = bld.alloc(
        format!("{tag}_nonce"),
        ColumnKind::Value,
        committed.nonce as i128,
    );
    // The commit column is PINNED to the COMMITTED hash (the published PI); the `Hash4to1`
    // site forces it to equal `hash(opened frm, to, seat, nonce)`. Honest: opened ==
    // committed, so they agree. Forged: opening ≠ committed ⇒ the recomputed hash ≠ the
    // committed PI ⇒ UNSAT.
    let host = committed.commit(n);
    let commit = bld.alloc(format!("{tag}_commit"), ColumnKind::Hash, host.0 as i128);
    bld.push_hash4to1(commit, [frm, to, seat, nonce]);
    bld.bind_pi(commit);
}

/// **THE SEALED-MOVE REVEAL LEAF** — both seats' committed moves, opened in-circuit. A
/// hash-carrying (Poseidon2 `Hash4to1`) foldable custom leaf: it PROVES a committed +
/// opened pair, and a forged reveal (opening a different move than committed) has no
/// satisfying leaf. `committed_*` drives each seat's published PI commitment; `opened_*`
/// is the revealed move.
pub fn build_sealed_bound(
    old: &Board,
    committed_a: &SealedMove,
    opened_a: &Move,
    committed_b: &SealedMove,
    opened_b: &Move,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    let n = old.n;
    let mut bld = Builder::new(format!("automatafl-sealed-n{n}"));
    let old_cols = alloc_board_pub(&mut bld, "old", old);
    // PI[0..16): the door's state-binding prefix (cell roots; fold-connected).
    for x in old8.iter().chain(new8.iter()) {
        bld.add_pi(x.0 as i128);
    }
    // PI[16..24): the CONSTRAINED board root of the pre-reveal board the seals commit against.
    let old_root = bld.board_root8("boardold", &old_cols);
    for c in old_root {
        bld.bind_pi(c);
    }
    let one = one_col(&mut bld);
    // PI[24..]: each seat's in-circuit-opened Poseidon2 move commitment (bind_pi'd in seal_seat).
    seal_seat(&mut bld, "sa", &old_cols, old, committed_a, opened_a, one);
    seal_seat(&mut bld, "sb", &old_cols, old, committed_b, opened_b, one);
    bld
}

/// The sealed reveal with placeholder door roots (the fast battery).
pub fn build_sealed(
    old: &Board,
    committed_a: &SealedMove,
    opened_a: &Move,
    committed_b: &SealedMove,
    opened_b: &Move,
) -> Builder {
    let (old8, new8) = crate::air::placeholder_roots();
    build_sealed_bound(
        old,
        committed_a,
        opened_a,
        committed_b,
        opened_b,
        old8,
        new8,
    )
}

/// The honest sealed reveal: each seat opens exactly the move it committed.
pub fn build_sealed_honest(old: &Board, a: &SealedMove, b: &SealedMove) -> Builder {
    build_sealed(old, a, &a.mv, b, &b.mv)
}

/// The honest sealed reveal bound to the leg's REAL cell-state roots (the fold driver).
pub fn build_sealed_honest_bound(
    old: &Board,
    a: &SealedMove,
    b: &SealedMove,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
) -> Builder {
    build_sealed_bound(old, a, &a.mv, b, &b.mv, old8, new8)
}
