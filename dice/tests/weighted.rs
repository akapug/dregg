//! E2 — the provably-fair weighted draw (`DrawStream::weighted`).
//!
//! A CDF over one `draw_bounded`: tier `i` is selected with probability
//! `weights[i] / Σ`. Re-derivable from `(seed, index)` + the committed weights, so
//! rarity is a proof anyone re-runs, not a claim.

use dregg_dice::{DrawError, DrawStream, Seed};

fn stream(tag: u8, count: u32) -> DrawStream {
    DrawStream::new(Seed::from_bytes([tag; 32]), count)
}

#[test]
fn weighted_is_deterministic_and_re_derivable() {
    let s = stream(7, 64);
    for i in 0..64 {
        // Same seed + same index + same committed weights ⇒ same tier, every time.
        let a = s.weighted(i, &[1000, 420, 150, 40, 6]).unwrap();
        let b = s.weighted(i, &[1000, 420, 150, 40, 6]).unwrap();
        assert_eq!(a, b, "weighted draw must be a pure function");
    }
}

#[test]
fn weighted_consumes_exactly_one_draw() {
    // `weighted` is a CDF over ONE draw_bounded(total): the tier it returns is exactly
    // the tier the single draw at that index falls into. This binds it to the fixed
    // transcript (draw_count unchanged).
    let s = stream(9, 32);
    let weights = [3u64, 5, 2]; // total = 10
    for i in 0..32 {
        let pick = s.draw_bounded(i, 10).unwrap();
        let expect = if pick < 3 {
            0
        } else if pick < 8 {
            1
        } else {
            2
        };
        assert_eq!(s.weighted(i, &weights).unwrap(), expect);
    }
}

#[test]
fn weighted_distribution_tracks_the_committed_weights() {
    // Over many independent indices the empirical frequencies approach the committed
    // ratios — the provably-fair property, measured (non-vacuous).
    let s = stream(11, 20_000);
    let weights = [1000u64, 420, 150, 40, 6];
    let total: u64 = weights.iter().sum();
    let mut counts = [0u64; 5];
    for i in 0..20_000 {
        counts[s.weighted(i, &weights).unwrap()] += 1;
    }
    // Commons dominate; the ordering of frequencies matches the ordering of weights.
    assert!(counts[0] > counts[1], "common should be most frequent");
    assert!(counts[1] > counts[2]);
    // Each observed frequency is within a loose tolerance of its committed probability.
    for k in 0..5 {
        let expected = 20_000.0 * (weights[k] as f64) / (total as f64);
        let got = counts[k] as f64;
        let tol = (expected * 0.5).max(30.0);
        assert!(
            (got - expected).abs() <= tol,
            "tier {k}: got {got}, expected ≈ {expected}"
        );
    }
}

#[test]
fn weighted_rare_tail_occurs_and_re_derives() {
    // A 6/1616 legendary tier is a real tail event: it DOES occur across a scan, and
    // any claimed legendary re-derives from the committed seed + weights (non-vacuous).
    let s = stream(13, 5_000);
    let weights = [1000u64, 420, 150, 40, 6];
    let legendary = (0..5_000)
        .find(|&i| s.weighted(i, &weights).unwrap() == 4)
        .expect("a legendary appears within 5000 draws");
    // Re-derivation by a verifier holding only (seed, index, committed weights).
    let reverify = DrawStream::new(Seed::from_bytes([13; 32]), 5_000);
    assert_eq!(reverify.weighted(legendary, &weights).unwrap(), 4);
}

#[test]
fn weighted_rejects_empty_and_zero_tables() {
    let s = stream(1, 4);
    assert_eq!(s.weighted(0, &[]).unwrap_err(), DrawError::ZeroBound);
    assert_eq!(s.weighted(0, &[0, 0, 0]).unwrap_err(), DrawError::ZeroBound);
}

#[test]
fn weighted_rejects_overflowing_table() {
    let s = stream(1, 4);
    let err = s.weighted(0, &[u64::MAX, u64::MAX]).unwrap_err();
    assert_eq!(err, DrawError::WeightsOverflow);
}
