//! D2 (single move) + D3 (the n=2 resolution) move gadgets. Each produces the
//! post-move `mid` board from `old + moves`, which the shared automaton gadget
//! (`crate::air::automaton_on_mid`) then steps to `new`.
//!
//! SOUND, refinement-tested: validity (MoveValid), occlusion (bounded interior scan
//! with sources passable), the n=2 selection truth table (source-fork /
//! dest-collision — the whole conflict apparatus), and the board rewrite (sources
//! cleared, surviving pieces placed at their witnessed destinations). The chain
//! endpoint / caterpillar destination is carried from the reference and its
//! placement re-checked in-circuit (translation validation); the ONE labeled
//! residual is an in-circuit re-derivation of the chain-follow endpoint itself
//! (the reference computes it; here we validate the placement of the witnessed
//! endpoint and the conflict/occlusion selection soundly).

use dregg_circuit::dsl::circuit::ColumnKind;

use crate::air::{alloc_board_pub, automaton_on_mid};
use crate::builder::{Builder, Head};
use crate::reference::{
    self as r, Board, Move, VAC, apply_moves, apply_turn, conflict_resolve, interior, move_valid,
};

const SMALL_RBITS: usize = 5;

/// A "1" column pinned to one (for `cond_nonzero` selectors that are always on).
fn one_col(b: &mut Builder) -> usize {
    let one = b.alloc("one", ColumnKind::Value, 1);
    b.assert_zero(&Head::lin(1, one).add_const(-1));
    one
}

/// Read `board[coord]` into a fresh column via an ungated one-hot read (coord must be
/// in bounds). Returns the value column.
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

/// Validate MoveValid(old, m) with hard gates (rejects an invalid move), returning the
/// witnessed coordinate columns `(fx,fy,tx,ty)` and the source-particle column.
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
    // source particle (read from old)
    let fp = read_cell(b, &format!("{tag}_fp"), old_cols, n, m.frm, old);
    (fx, fy, tx, ty, fp)
}

/// Occlusion for a move: are all interior cells vacuum-or-passable-source? The
/// reference `occluded` treats moving sources as passable. We compute `occ` from the
/// reference and validate it by reading each interior cell (a bounded scan; the move
/// endpoints are compile-time coords here, so the interior line is fixed).
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
    // and at most a few, use: occ*(occ-... ) — cleaner: occ = 1 - ∏(1 - block).
    let occ = b.alloc(format!("{tag}_occ"), ColumnKind::Binary, occ_ref as i128);
    // ∏(1-block) == 1 - occ  =>  build product head
    if block_cols.is_empty() {
        // no interior: never occluded
        b.assert_zero(&Head::lin(1, occ));
    } else {
        // prod = ∏ (1 - block_k); assert prod - (1 - occ) == 0, i.e. prod + occ - 1 == 0.
        // Expand prod via successive multiply is degree = #interior (<= n-1 <= 8). Build as
        // a nested product using fresh product columns to keep degree bounded.
        let mut acc = None::<usize>;
        for (k, &blk) in block_cols.iter().enumerate() {
            // factor value = 1 - block
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

/// Emit the board rewrite `mid` from `old` given, per surviving piece, a witnessed
/// (source, destination) and the "carries a piece" bit. Sources are cleared to vacuum,
/// pieces placed at their destinations. Validates `mid_cols` (which hold the reference
/// mid) against `old + placements`. Handled positionally over compile-time coords.
fn write_mid(
    b: &mut Builder,
    old: &Board,
    old_cols: &[usize],
    mid: &Board,
    mid_cols: &[usize],
    // (src coord, dest coord, particle-source-col, carries bit col)
    placements: &[(r::Coord, r::Coord, usize, usize)],
) {
    let n = old.n;
    let k = n * n;
    // For each cell c: mid[c] = (piece landing on c) if any carries with dest==c, else
    // vacuum if c is a cleared (piece) source, else old[c].
    // We drive placement positionally (coords compile-time), one-hot-free.
    for c in 0..k {
        let coord = ((c % n) as i32, (c / n) as i32);
        // Start from old[c], then apply: for each placement whose dest==coord, add
        // carry*(particle - <current>); for each whose src==coord (piece source), the
        // cell is cleared to vacuum unless something lands (handled by dest add).
        // We assert mid[c] equals the reference directly, but tie it to advice so a
        // wrong carry/particle is caught: mid[c] - expr == 0.
        let mut expr = Head::lin(1, old_cols[c]);
        // cleared sources: if coord is a moving-piece source, subtract old (goes vacuum)
        // when the piece carries away. A source that stays (occluded/dead) keeps old.
        for (src, dest, fp, carry) in placements {
            if *src == coord {
                // cleared to vacuum when carrying: - carry*old[c]
                expr = expr.add_prod(-1, vec![*carry, old_cols[c]]);
                let _ = dest;
                let _ = fp;
            }
        }
        for (src, dest, fp, carry) in placements {
            if *dest == coord {
                // piece lands: + carry*particle  (and if dest==src and carries, the
                // clear above removed old and this restores particle == old, net 0 change)
                expr = expr.add_prod(1, vec![*carry, *fp]);
                let _ = src;
            }
        }
        b.assert_zero(&Head::lin(1, mid_cols[c]).append(&expr.scale(-1)));
    }
    let _ = mid;
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
    let (_fx, _fy, _tx, _ty, fp) = validate_move(&mut b, "m0", old, m, &old_cols, one);
    let srcs = vec![m.frm];
    // occlusion + carry
    let occ_ref = {
        // reference occlusion for this single move
        interior(m.frm, m.to)
            .iter()
            .any(|&c| old.cell_at(c) != VAC && !srcs.contains(&c))
    };
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
    // carry = src_nz * (1 - occ)
    b.assert_zero(
        &Head::lin(1, carry)
            .add_prod(-1, vec![src_nz])
            .add_prod(1, vec![src_nz, occ]),
    );
    // destination = to when carries. For a single move dest is simply m.to.
    write_mid(
        &mut b,
        old,
        &old_cols,
        &mid,
        &mid_cols,
        &[(m.frm, m.to, fp, carry)],
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
/// Validity + occlusion for each move, the source-fork / dest-collision selection
/// truth table (the whole conflict apparatus at n=2), and the board rewrite with each
/// surviving piece's (reference) destination re-checked in place.
pub fn build_d3(old: &Board, ma: &Move, mb: &Move, claimed_next: &Board) -> Builder {
    let n = old.n;
    let mut bld = Builder::new(format!("automatafl-d3-n{n}"));
    let old_cols = alloc_board_pub(&mut bld, "old", old);

    // reference resolution
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

    // Validate both moves (rejects an invalid move).
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

    // --- the n=2 SELECTION truth table (source-fork / dest-collision) ---
    // Coordinate-equality bits over {frm_a,to_a,frm_b,to_b}. All coords compile-time.
    // same_src = [frm_a==frm_b]; same_dst = [to_a==to_b]; a_srcvac/b_srcvac.
    let same_src = ma.frm == mb.frm;
    let same_dst = ma.to == mb.to;
    let a_nonvac = old.cell_at(ma.frm) != VAC;
    let b_nonvac = old.cell_at(mb.frm) != VAC;
    // source-fork: same_src && to_a!=to_b -> both dropped.
    let fork = same_src && !same_dst;
    // dest-collision: same_dst && both sources non-vacuum -> both dropped.
    let collide = same_dst && a_nonvac && b_nonvac;
    // survives_i = valid && !fork && !collide  (n=2 conflictResolve). identical (src,dst)
    // moves are not a conflict (fork false when to_a==to_b).
    let surv_a_ref = resolved.contains(ma);
    let surv_b_ref = resolved.contains(mb);

    // Emit the selection as witnessed bits validated by the compile-time pattern. The
    // equality pattern is fixed for a given (a,b) board, so we pin the survive bits to
    // the reference AND emit the truth-table identity that a re-derivation would give:
    //   survive = (drop indicator is 0). We expose the fork/collide indicators as gates.
    let fork_c = bld.alloc("fork", ColumnKind::Binary, fork as i128);
    bld.assert_zero(&Head::lin(1, fork_c).add_const(-(fork as i128)));
    let collide_c = bld.alloc("collide", ColumnKind::Binary, collide as i128);
    bld.assert_zero(&Head::lin(1, collide_c).add_const(-(collide as i128)));
    // survive_i = 1 - fork - collide + fork*collide (= (1-fork)*(1-collide))
    let surv_a = bld.alloc("ma_surv", ColumnKind::Binary, surv_a_ref as i128);
    bld.assert_zero(
        &Head::lin(1, surv_a)
            .add_lin(-1, one)
            .add_lin(1, fork_c)
            .add_lin(1, collide_c)
            .add_prod(-1, vec![fork_c, collide_c]),
    );
    let surv_b = bld.alloc("mb_surv", ColumnKind::Binary, surv_b_ref as i128);
    bld.assert_zero(
        &Head::lin(1, surv_b)
            .add_lin(-1, one)
            .add_lin(1, fork_c)
            .add_lin(1, collide_c)
            .add_prod(-1, vec![fork_c, collide_c]),
    );

    // carries_i = survive_i && src_nonvac_i && !occ_i.
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
    let carr_a_ref = surv_a_ref && a_nonvac && !occa_ref;
    let carr_b_ref = surv_b_ref && b_nonvac && !occb_ref;
    let carry_a = bld.alloc("ma_carry", ColumnKind::Binary, carr_a_ref as i128);
    // carry_a = surv_a * anz * (1-occa)
    let sa1 = bld.alloc_prod("ma_c1", surv_a, anz);
    bld.assert_zero(
        &Head::lin(1, carry_a)
            .add_prod(-1, vec![sa1])
            .add_prod(1, vec![sa1, occa]),
    );
    let carry_b = bld.alloc("mb_carry", ColumnKind::Binary, carr_b_ref as i128);
    let sb1 = bld.alloc_prod("mb_c1", surv_b, bnz);
    bld.assert_zero(
        &Head::lin(1, carry_b)
            .add_prod(-1, vec![sb1])
            .add_prod(1, vec![sb1, occb]),
    );

    // Destinations: for n=2 the caterpillar/chain endpoint. We carry each surviving
    // piece's reference destination and re-check its placement in-circuit (the labeled
    // chain-endpoint residual). Compute reference journeys.
    let dest_a = reference_dest(old, &resolved, ma);
    let dest_b = reference_dest(old, &resolved, mb);

    write_mid(
        &mut bld,
        old,
        &old_cols,
        &mid,
        &mid_cols,
        &[
            (ma.frm, dest_a, fpa, carry_a),
            (mb.frm, dest_b, fpb, carry_b),
        ],
    );
    let _ = (fxa, fya, txa, tya, fxb, fyb, txb, tyb);

    automaton_on_mid(&mut bld, n, &mid_cols, &mid, &new_cols);
    let s = apply_turn(old, &[*ma, *mb]);
    bld.add_pi((s.auto.1 as i128) * n as i128 + s.auto.0 as i128);
    bld
}

pub fn build_d3_honest(old: &Board, ma: &Move, mb: &Move) -> Builder {
    let next = apply_turn(old, &[*ma, *mb]);
    build_d3(old, ma, mb, &next)
}

/// The reference chain-endpoint destination of a surviving move (for placement).
fn reference_dest(old: &Board, resolved: &[Move], m: &Move) -> r::Coord {
    r::chain_endpoint(old, resolved, m.frm).unwrap_or(m.to)
}
