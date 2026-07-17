//! **C.4 — the coordinate-indexed occlusion differential + the overwrite fix at scale.**
//!
//! Two batteries, both pinning the in-circuit resolution to the corrected reference oracle
//! (`reference::occluded` / `reference::resolve_mid`) across MANY random rook moves on real
//! board sizes — the size at which the old compile-time interior enumeration would have blown
//! past `MAX_TRACE_WIDTH` (an n²-wide read per interior cell):
//!
//!  1. `occlusion_masked_window_matches_reference` — the standalone occlusion probe
//!     (`moves::probe_occlusion`, one authenticated line-extract + strictly-between mask +
//!     source mask) computes the SAME `occ` bit as `reference::occluded` for every generated
//!     rook move (single-move AND with a passable second source on the line).
//!  2. `leg_r_air_refines_resolve_mid_fuzz` — the full Leg R AIR (`build_r_honest`) ACCEPTS the
//!     honest `old → mid` on hundreds of non-conflicting two-move pairs, including the occluded-
//!     source-overwrite (constraint-462) case, at n=11 — and every leg fits under the width cap.

use dregg_automatafl::build_r_honest;
use dregg_automatafl::moves::probe_occlusion;
use dregg_automatafl::reference::{
    self as dref, ATT, AUTO, Board, Move, REP, VAC, conflict_resolve, move_valid, occluded,
    resolve_mid,
};
use dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH;

// A tiny deterministic PRNG (SplitMix64) — hermetic, reproducible.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_add(0x9E37_79B9_7F4A_7C15))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// A random board of size `n`: an automaton at a random cell, then `density` sprinkled
/// repulsors/attractors (never on the automaton). Vacuum everywhere else.
fn random_board(rng: &mut Rng, n: usize, density: usize) -> Board {
    let mut cells = vec![VAC; n * n];
    let ax = rng.below(n);
    let ay = rng.below(n);
    cells[ay * n + ax] = AUTO;
    for _ in 0..density {
        let x = rng.below(n);
        let y = rng.below(n);
        if (x, y) == (ax, ay) {
            continue;
        }
        cells[y * n + x] = if rng.next_u64() & 1 == 0 { REP } else { ATT };
    }
    Board {
        n,
        cells,
        auto: (ax as i32, ay as i32),
        col_rule: true,
    }
}

/// A random VALID rook move on `board` (rook-aligned, distinct, in-bounds, neither endpoint the
/// automaton). Source may be vacuum or a piece — the occlusion is about the INTERIOR either way.
fn random_valid_move(rng: &mut Rng, board: &Board, who: u32) -> Move {
    let n = board.n;
    loop {
        let fx = rng.below(n);
        let fy = rng.below(n);
        let horizontal = rng.next_u64() & 1 == 0;
        let (tx, ty) = if horizontal {
            let mut tx = rng.below(n);
            if tx == fx {
                tx = (tx + 1) % n;
            }
            (tx, fy)
        } else {
            let mut ty = rng.below(n);
            if ty == fy {
                ty = (ty + 1) % n;
            }
            (fx, ty)
        };
        let m = Move {
            who,
            frm: (fx as i32, fy as i32),
            to: (tx as i32, ty as i32),
        };
        if move_valid(board, &m) {
            return m;
        }
    }
}

// ===========================================================================
// (1) The occlusion probe agrees with `reference::occluded`, bit for bit.
// ===========================================================================
#[test]
fn occlusion_masked_window_matches_reference() {
    const N: usize = 11;
    let mut rng = Rng::new(0xC4_0CC1);
    let mut occluded_seen = 0usize;
    let mut clear_seen = 0usize;
    let mut src_on_line_seen = 0usize;

    for _ in 0..6000 {
        let dens = 8 + rng.below(20);
        let board = random_board(&mut rng, N, dens);
        let m = random_valid_move(&mut rng, &board, 0);

        // --- single-move occlusion (srcs = [m.frm]) ---
        let (accepts, occ_air) = probe_occlusion(&board, &m, None);
        assert!(
            accepts,
            "occlusion probe must self-accept\n board={board:?}\n m={m:?}"
        );
        let occ_ref = occluded(&board, &[m.frm], &m);
        assert_eq!(
            occ_air, occ_ref,
            "single-move occ diverges: air={occ_air} ref={occ_ref}\n board={board:?}\n m={m:?}"
        );
        if occ_ref {
            occluded_seen += 1;
        } else {
            clear_seen += 1;
        }

        // --- with a second (passable) source on the SAME line, when we can place one ---
        // Put the other source at a random interior cell of m's line, so [k not a moving
        // source] is genuinely exercised (the reference excludes it; the AIR must too).
        if let Some(other) = other_source_on_line(&mut rng, &board, &m) {
            if move_valid(&board, &other) {
                let (acc2, occ_air2) = probe_occlusion(&board, &m, Some(&other));
                assert!(acc2, "two-source occlusion probe must self-accept");
                let occ_ref2 = occluded(&board, &[m.frm, other.frm], &m);
                assert_eq!(
                    occ_air2, occ_ref2,
                    "two-source occ diverges: air={occ_air2} ref={occ_ref2}\n board={board:?}\n m={m:?}\n other={other:?}"
                );
                // Did the other source actually sit strictly interior to m? (coverage.)
                if dref::interior(m.frm, m.to).contains(&other.frm) {
                    src_on_line_seen += 1;
                }
            }
        }
    }

    assert!(
        occluded_seen > 200 && clear_seen > 200,
        "weak coverage: occluded={occluded_seen} clear={clear_seen}"
    );
    assert!(
        src_on_line_seen > 20,
        "the passable-interior-source case was barely exercised ({src_on_line_seen})"
    );
    eprintln!(
        "occlusion differential: 6000 rook moves agreed with reference::occluded \
         (occluded {occluded_seen}, clear {clear_seen}, interior-source {src_on_line_seen})"
    );
}

/// Build a second move whose SOURCE sits at a strictly-interior cell of `m`'s line (so it is a
/// passable moving source the occlusion must skip). `None` if `m` has no interior.
fn other_source_on_line(rng: &mut Rng, board: &Board, m: &Move) -> Option<Move> {
    let interior = dref::interior(m.frm, m.to);
    if interior.is_empty() {
        return None;
    }
    let src = interior[rng.below(interior.len())];
    if src == board.auto {
        return None;
    }
    // A perpendicular escape move off the line (so `other` is itself a legal rook move).
    let n = board.n as i32;
    let (dx, dy) = if m.frm.0 == m.to.0 {
        // m is vertical → other moves horizontally off the column
        let tx = if src.0 + 1 < n { src.0 + 1 } else { src.0 - 1 };
        (tx, src.1)
    } else {
        let ty = if src.1 + 1 < n { src.1 + 1 } else { src.1 - 1 };
        (src.0, ty)
    };
    let other = Move {
        who: 1,
        frm: src,
        to: (dx, dy),
    };
    Some(other)
}

// ===========================================================================
// (2) The full Leg R AIR refines resolve_mid across many two-move pairs at n=11 —
//     the occlusion + the overwrite fix, at the real board size, under the width cap.
// ===========================================================================
#[test]
fn leg_r_air_refines_resolve_mid_fuzz() {
    const N: usize = 11;
    let mut rng = Rng::new(0x462_0FF);
    let mut checked = 0usize;
    let mut occluded_pairs = 0usize;
    let mut rewrote = 0usize;
    let mut max_width = 0usize;

    for _ in 0..500 {
        let dens = 6 + rng.below(16);
        let board = random_board(&mut rng, N, dens);
        let a = random_valid_move(&mut rng, &board, 0);
        let b = random_valid_move(&mut rng, &board, 1);
        let da = [a, b];
        // Only the non-conflicting subset — the board-for-board resolution Leg R proves.
        let valid: Vec<Move> = da
            .iter()
            .filter(|m| move_valid(&board, m))
            .copied()
            .collect();
        if valid.len() != 2 || conflict_resolve(&board, &valid).len() != 2 {
            continue;
        }
        let mid = resolve_mid(&board, &da);
        let prog = build_r_honest(&board, &a, &b);
        let w = prog.descriptor().trace_width;
        max_width = max_width.max(w);
        assert!(
            w <= MAX_TRACE_WIDTH,
            "Leg R width {w} exceeds {MAX_TRACE_WIDTH} at n={N}"
        );
        let f = prog.failing();
        assert!(
            f.is_empty(),
            "Leg R must accept honest old→mid; failing = {:?}\n board={board:?}\n a={a:?} b={b:?}",
            f
        );
        checked += 1;
        if occluded(&board, &[a.frm, b.frm], &a) || occluded(&board, &[a.frm, b.frm], &b) {
            occluded_pairs += 1;
        }
        if mid.cells != board.cells {
            rewrote += 1;
        }
    }

    assert!(
        checked > 100,
        "too few non-conflicting pairs checked ({checked})"
    );
    assert!(
        occluded_pairs > 10,
        "occlusion was barely exercised in the Leg R fuzz ({occluded_pairs})"
    );
    assert!(rewrote > 10, "the board was rarely rewritten ({rewrote})");
    assert!(
        max_width <= MAX_TRACE_WIDTH,
        "Leg R n={N} peaked at width {max_width} (> {MAX_TRACE_WIDTH})"
    );
    eprintln!(
        "Leg R n={N} refinement fuzz: {checked} honest old→mid accepted \
         (occluded pairs {occluded_pairs}, rewrites {rewrote}); peak width {max_width}"
    );
}
