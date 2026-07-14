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
//!  - occlusion (bounded interior scan with sources passable) and the board rewrite
//!    (one-hot writes at the witnessed source/dest indices).
//!
//! LABELED RESIDUAL (unchanged): the occlusion interior scan is still enumerated
//! over the compile-time move line (the general N=11 segmented-indicator scan is
//! future work), and the concrete Lean `Refines` discharge is the long pole.

use dregg_circuit::dsl::circuit::ColumnKind;

use crate::air::{alloc_board_pub, automaton_on_mid};
use crate::builder::{Builder, Head};
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

/// Read `board[coord]` into a fresh column via an ungated one-hot read at a
/// COMPILE-TIME index (used for the interior-occlusion scan, whose cell line is
/// structurally compile-time at n=2).
fn read_cell(
    b: &mut Builder,
    tag: &str,
    board_cols: &[usize],
    n: usize,
    coord: r::Coord,
    board: &Board,
) -> usize {
    let (x, y) = coord;
    let idx = (y as usize) * n + (x as usize);
    let v = board.cell_at(coord) as i128;
    let vc = b.alloc(format!("{tag}_v"), ColumnKind::Value, v);
    let index_head = Head::c(idx as i128);
    b.one_hot_read(tag, board_cols, idx, &index_head, vc);
    vc
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
/// witnessed coordinate columns `(fx,fy,tx,ty)` and the source-particle column. The
/// source particle is read through the WITNESSED `(fx,fy)` via a one-hot index head,
/// so `fp == old[n*fy+fx]` — the read is bound to the coordinates the move claims.
fn validate_move(
    b: &mut Builder,
    tag: &str,
    old: &Board,
    m: &Move,
    old_cols: &[usize],
    one: usize,
) -> (usize, usize, usize, usize, usize) {
    let n = old.n;
    let inb: Vec<i128> = (0..n as i128).collect();
    let fx = b.alloc(format!("{tag}_fx"), ColumnKind::Value, m.frm.0 as i128);
    let fy = b.alloc(format!("{tag}_fy"), ColumnKind::Value, m.frm.1 as i128);
    let tx = b.alloc(format!("{tag}_tx"), ColumnKind::Value, m.to.0 as i128);
    let ty = b.alloc(format!("{tag}_ty"), ColumnKind::Value, m.to.1 as i128);
    b.assert_member(fx, &inb);
    b.assert_member(fy, &inb);
    b.assert_member(tx, &inb);
    b.assert_member(ty, &inb);
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
    // source particle: read from old at the WITNESSED source index n*fy+fx.
    let src_idx = (m.frm.1 as usize) * n + (m.frm.0 as usize);
    let src_head = Head::lin(n as i128, fy).add_lin(1, fx);
    let fp = b.alloc(
        format!("{tag}_fp_v"),
        ColumnKind::Value,
        old.cell_at(m.frm) as i128,
    );
    b.one_hot_read(&format!("{tag}_fp"), old_cols, src_idx, &src_head, fp);
    (fx, fy, tx, ty, fp)
}

/// Occlusion for a move: are all interior cells vacuum-or-passable-source? The
/// reference `occluded` treats moving sources as passable. We compute `occ` from the
/// reference and validate it by reading each interior cell (a bounded scan; the move
/// endpoints are compile-time coords here, so the interior line is fixed — the
/// labeled N=11 segmented-scan residual).
fn validate_occlusion(
    b: &mut Builder,
    tag: &str,
    old: &Board,
    m: &Move,
    old_cols: &[usize],
    srcs: &[r::Coord],
    occ_ref: bool,
) -> usize {
    let n = old.n;
    let interior_cells = interior(m.frm, m.to);
    // per interior cell: block bit = [cell nonvacuum AND not a moving source]
    let mut any_block = Head::zero();
    let mut block_cols = Vec::new();
    for (k, &c) in interior_cells.iter().enumerate() {
        let cv = read_cell(b, &format!("{tag}_int{k}"), old_cols, n, c, old);
        // nz = [cell != 0]
        let nz = b.forced_ge0(
            &format!("{tag}_intnz{k}"),
            &Head::lin(1, cv).add_const(-1),
            old.cell_at(c) as i128 - 1,
            SMALL_RBITS,
        );
        // is this cell a moving source? (compile-time known)
        let is_src = srcs.contains(&c);
        // block = nz AND (not is_src). is_src is compile-time; if src, block=0.
        let block_val = if is_src { 0 } else { b.value(nz).0 as i128 };
        let block = b.alloc(format!("{tag}_blk{k}"), ColumnKind::Binary, block_val);
        if is_src {
            b.assert_zero(&Head::lin(1, block));
        } else {
            b.assert_zero(&Head::lin(1, block).add_lin(-1, nz));
        }
        any_block = any_block.add_lin(1, block);
        block_cols.push(block);
    }
    // occ bit = [any block]. Validate: occ == 1 iff Σ block >= 1. Since blocks are bits
    // and at most a few, use: occ = 1 - ∏(1 - block).
    let occ = b.alloc(format!("{tag}_occ"), ColumnKind::Binary, occ_ref as i128);
    if block_cols.is_empty() {
        // no interior: never occluded
        b.assert_zero(&Head::lin(1, occ));
    } else {
        // prod = ∏ (1 - block_k); assert prod + occ - 1 == 0.
        let mut acc = None::<usize>;
        for (k, &blk) in block_cols.iter().enumerate() {
            let fval = 1 - b.value(blk).0 as i128;
            let fcol = b.alloc(format!("{tag}_f{k}"), ColumnKind::Value, fval);
            b.assert_zero(&Head::lin(1, fcol).add_lin(1, blk).add_const(-1)); // fcol = 1 - blk
            acc = Some(match acc {
                None => fcol,
                Some(a) => b.alloc_prod(&format!("{tag}_p{k}"), a, fcol),
            });
        }
        let prod = acc.unwrap();
        b.assert_zero(&Head::lin(1, prod).add_lin(1, occ).add_const(-1));
    }
    occ
}

/// One surviving piece's placement data: its witnessed source index + head, its
/// (in-circuit-derived) destination index + head, its particle column and carry bit.
struct Placement {
    src_idx: usize,
    src_head: Head,
    dest_idx: usize,
    dest_head: Head,
    particle: usize,
    carry: usize,
}

/// Emit the board rewrite `mid` from `old` via one-hot writes at the WITNESSED source
/// and (derived) destination indices. For each cell `c`:
///   `mid[c] = old[c] - Σ_i carry_i·sel_src_i[c]·old[c] + Σ_i carry_i·sel_dst_i[c]·particle_i`
/// i.e. a carried source is cleared to vacuum and its particle re-deposited at the
/// derived destination — validated cell-by-cell against the reference `mid_cols`. The
/// source/dest selectors are one-hots pinned to the witnessed index heads, so a wrong
/// source/dest has no satisfying witness.
fn write_mid_witnessed(
    b: &mut Builder,
    n: usize,
    old_cols: &[usize],
    mid_cols: &[usize],
    pieces: Vec<Placement>,
) {
    let k = n * n;
    let mut sels: Vec<(Vec<usize>, Vec<usize>)> = Vec::with_capacity(pieces.len());
    for (i, p) in pieces.iter().enumerate() {
        let sel_src = b.one_hot(&format!("wsrc{i}"), k, p.src_idx, &p.src_head);
        let sel_dst = b.one_hot(&format!("wdst{i}"), k, p.dest_idx, &p.dest_head);
        sels.push((sel_src, sel_dst));
    }
    for c in 0..k {
        let mut expr = Head::lin(1, old_cols[c]);
        for (i, p) in pieces.iter().enumerate() {
            let (ssrc, sdst) = &sels[i];
            // clear carried source: - carry * sel_src[c] * old[c]
            expr = expr.add_prod(-1, vec![p.carry, ssrc[c], old_cols[c]]);
            // place at dest: + carry * sel_dst[c] * particle
            expr = expr.add_prod(1, vec![p.carry, sdst[c], p.particle]);
        }
        b.assert_zero(&Head::lin(1, mid_cols[c]).append(&expr.scale(-1)));
    }
}

/// **STAGE D2** — single move: `claimed_next == apply_turn(old, [m])`.
pub fn build_d2(old: &Board, m: &Move, claimed_next: &Board) -> Builder {
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
    b.add_pi((old.auto.1 as i128) * n as i128 + old.auto.0 as i128);

    let one = one_col(&mut b);
    let (fx, fy, tx, ty, fp) = validate_move(&mut b, "m0", old, m, &old_cols, one);
    let srcs = vec![m.frm];
    // occlusion + carry
    let occ_ref = interior(m.frm, m.to)
        .iter()
        .any(|&c| old.cell_at(c) != VAC && !srcs.contains(&c));
    let occ = validate_occlusion(&mut b, "m0", old, m, &old_cols, &srcs, occ_ref);
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
    let src_head = Head::lin(n as i128, fy).add_lin(1, fx);
    let dest_head = Head::lin(n as i128, ty).add_lin(1, tx);
    let src_idx = (m.frm.1 as usize) * n + (m.frm.0 as usize);
    let dest_idx = (m.to.1 as usize) * n + (m.to.0 as usize);
    write_mid_witnessed(
        &mut b,
        n,
        &old_cols,
        &mid_cols,
        vec![Placement {
            src_idx,
            src_head,
            dest_idx,
            dest_head,
            particle: fp,
            carry,
        }],
    );

    // then the automaton steps on mid
    automaton_on_mid(&mut b, n, &mid_cols, &mid, &new_cols);
    let s = apply_turn(old, &[*m]);
    b.add_pi((s.auto.1 as i128) * n as i128 + s.auto.0 as i128);
    b
}

pub fn build_d2_honest(old: &Board, m: &Move) -> Builder {
    let next = apply_turn(old, &[*m]);
    build_d2(old, m, &next)
}

/// **STAGE D3** — the n=2 resolution: `claimed_next == apply_turn(old, [a, b])`.
/// The 6 pattern bits, the fork/collide/survive selection, and each surviving
/// piece's chain-endpoint destination are RE-DERIVED IN-CIRCUIT from the witnessed
/// coordinates + source particles (no value taken from the reference resolution).
pub fn build_d3(old: &Board, ma: &Move, mb: &Move, claimed_next: &Board) -> Builder {
    let n = old.n;
    let mut bld = Builder::new(format!("automatafl-d3-n{n}"));
    let old_cols = alloc_board_pub(&mut bld, "old", old);

    // reference resolution (drives the honest witness + the public `mid`/`new`)
    let valid: Vec<Move> = [*ma, *mb]
        .into_iter()
        .filter(|m| move_valid(old, m))
        .collect();
    let resolved = conflict_resolve(old, &valid);
    let mid = apply_moves(old, &resolved);
    let mid_cols = alloc_board_pub(&mut bld, "mid", &mid);
    let new_cols = alloc_board_pub(&mut bld, "new", claimed_next);
    bld.add_pi((old.auto.1 as i128) * n as i128 + old.auto.0 as i128);

    let one = one_col(&mut bld);
    let srcs = vec![ma.frm, mb.frm];

    // Validate both moves (rejects an invalid move); source reads bound to (fx,fy).
    let (fxa, fya, txa, tya, fpa) = validate_move(&mut bld, "ma", old, ma, &old_cols, one);
    let (fxb, fyb, txb, tyb, fpb) = validate_move(&mut bld, "mb", old, mb, &old_cols, one);

    // Occlusion per move (sources passable).
    let occa_ref = interior(ma.frm, ma.to)
        .iter()
        .any(|&c| old.cell_at(c) != VAC && !srcs.contains(&c));
    let occb_ref = interior(mb.frm, mb.to)
        .iter()
        .any(|&c| old.cell_at(c) != VAC && !srcs.contains(&c));
    let occa = validate_occlusion(&mut bld, "ma", old, ma, &old_cols, &srcs, occa_ref);
    let occb = validate_occlusion(&mut bld, "mb", old, mb, &old_cols, &srcs, occb_ref);

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
        &mut bld, "eqff", fxa, fya, fxb, fyb, ma.frm.0, ma.frm.1, mb.frm.0, mb.frm.1,
    );
    let eq_tt = eq_coords(
        &mut bld, "eqtt", txa, tya, txb, tyb, ma.to.0, ma.to.1, mb.to.0, mb.to.1,
    );
    // eq_ab = [to_a == frm_b], eq_ba = [to_b == frm_a] (the chain relations).
    let eq_ab = eq_coords(
        &mut bld, "eqab", txa, tya, fxb, fyb, ma.to.0, ma.to.1, mb.frm.0, mb.frm.1,
    );
    let eq_ba = eq_coords(
        &mut bld, "eqba", txb, tyb, fxa, fya, mb.to.0, mb.to.1, ma.frm.0, ma.frm.1,
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
    let neq_ff = not_bit(&mut bld, "neqff", eq_ff);
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
    let n_bnz = not_bit(&mut bld, "nbnz", bnz);
    let n_occb = not_bit(&mut bld, "noccb", occb);
    let n_eqba = not_bit(&mut bld, "neqba", eq_ba);
    let fa1 = bld.alloc_prod("fta1", eq_ab, n_bnz);
    let fa2 = bld.alloc_prod("fta2", fa1, surv);
    let fa3 = bld.alloc_prod("fta3", fa2, n_occb);
    let ft_a = bld.alloc_prod("ft_a", fa3, n_eqba);

    let n_anz = not_bit(&mut bld, "nanz", anz);
    let n_occa = not_bit(&mut bld, "nocca", occa);
    let n_eqab = not_bit(&mut bld, "neqab", eq_ab);
    let fb1 = bld.alloc_prod("ftb1", eq_ba, n_anz);
    let fb2 = bld.alloc_prod("ftb2", fb1, surv);
    let fb3 = bld.alloc_prod("ftb3", fb2, n_occa);
    let ft_b = bld.alloc_prod("ft_b", fb3, n_eqab);

    let ne = n as i128;
    let toa_idx = (ma.to.1 as usize) * n + (ma.to.0 as usize);
    let tob_idx = (mb.to.1 as usize) * n + (mb.to.0 as usize);
    let ft_a_val = bld.value(ft_a).0 as i128;
    let ft_b_val = bld.value(ft_b).0 as i128;
    // dest_a index = to_a_idx + ft_a*(to_b_idx - to_a_idx), a proven fn of the coords + ft_a.
    let dest_a_idx = (toa_idx as i128 + ft_a_val * (tob_idx as i128 - toa_idx as i128)) as usize;
    let dest_a_head = Head::lin(ne, tya)
        .add_lin(1, txa)
        .add_prod(ne, vec![ft_a, tyb])
        .add_prod(1, vec![ft_a, txb])
        .add_prod(-ne, vec![ft_a, tya])
        .add_prod(-1, vec![ft_a, txa]);
    let dest_b_idx = (tob_idx as i128 + ft_b_val * (toa_idx as i128 - tob_idx as i128)) as usize;
    let dest_b_head = Head::lin(ne, tyb)
        .add_lin(1, txb)
        .add_prod(ne, vec![ft_b, tya])
        .add_prod(1, vec![ft_b, txa])
        .add_prod(-ne, vec![ft_b, tyb])
        .add_prod(-1, vec![ft_b, txb]);

    let src_a_idx = (ma.frm.1 as usize) * n + (ma.frm.0 as usize);
    let src_b_idx = (mb.frm.1 as usize) * n + (mb.frm.0 as usize);
    let src_a_head = Head::lin(ne, fya).add_lin(1, fxa);
    let src_b_head = Head::lin(ne, fyb).add_lin(1, fxb);

    write_mid_witnessed(
        &mut bld,
        n,
        &old_cols,
        &mid_cols,
        vec![
            Placement {
                src_idx: src_a_idx,
                src_head: src_a_head,
                dest_idx: dest_a_idx,
                dest_head: dest_a_head,
                particle: fpa,
                carry: carry_a,
            },
            Placement {
                src_idx: src_b_idx,
                src_head: src_b_head,
                dest_idx: dest_b_idx,
                dest_head: dest_b_head,
                particle: fpb,
                carry: carry_b,
            },
        ],
    );

    automaton_on_mid(&mut bld, n, &mid_cols, &mid, &new_cols);
    let s = apply_turn(old, &[*ma, *mb]);
    bld.add_pi((s.auto.1 as i128) * n as i128 + s.auto.0 as i128);
    bld
}

pub fn build_d3_honest(old: &Board, ma: &Move, mb: &Move) -> Builder {
    let next = apply_turn(old, &[*ma, *mb]);
    build_d3(old, ma, mb, &next)
}
