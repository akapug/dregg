//! **THE BUDGET CENSUS.** Width / degree / PIs / Poseidon2 sites at each shape, measured
//! against the deployed caps (`MAX_TRACE_WIDTH = 1024`, `MAX_CONSTRAINT_DEGREE = 8`,
//! `MAX_PUBLIC_INPUTS = 64`) — the automatafl lesson taken up front rather than discovered.
//!
//! Run:
//!   cargo test -p dregg-param-compose --test size -- --nocapture

use dregg_circuit::field::BabyBear;
use dregg_param_compose::air::build;
use dregg_param_compose::field::fb;
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::{
    ComposeShape, MAX_CONSTRAINT_DEGREE, MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH,
};

fn old8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(1000 + i as i128))
}
fn new8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(2000 + i as i128))
}

/// A DENSE composition that saturates every one of the shape's bounds — so the census
/// measures the worst case a VK of this shape must carry, not a lucky sparse one.
fn saturating(shape: &ComposeShape) -> Composition {
    let roles: Vec<u64> = (0..shape.max_subjects).map(|i| 100 + i as u64).collect();
    let subjects = (0..shape.max_subjects)
        .map(|i| Subject {
            identity: 10 + 7 * i as u64,
            role: roles[i],
            params: (0..shape.max_params).map(|p| (i + p + 1) as i64).collect(),
        })
        .collect();
    let linear = (0..shape.max_linear)
        .map(|t| LinearTerm {
            role: roles[t % shape.max_subjects],
            param: t % shape.max_params,
            coeff: (t as i64 + 1) * 3,
        })
        .collect();
    let knots = (0..shape.max_knots)
        .map(|k| Knot {
            role_a: roles[k % shape.max_subjects],
            param_a: k % shape.max_params,
            role_b: roles[(k + 1) % shape.max_subjects],
            param_b: (k + 1) % shape.max_params,
            coeff: -(k as i64 + 1),
        })
        .collect();
    Composition {
        subjects,
        ruleset: Ruleset {
            id: 42,
            version: 1,
            linear,
            knots,
        },
        param_count: shape.max_params,
    }
}

fn report(tag: &str, shape: &ComposeShape) -> (usize, usize, usize) {
    let comp = saturating(shape);
    let air = build(shape, &comp, &old8(), &new8()).expect("saturating composition builds");
    assert!(
        air.builder.air_accepts(),
        "{tag}: the honest saturating witness must self-accept"
    );
    let d = air.builder.descriptor();
    let fits = if d.trace_width <= MAX_TRACE_WIDTH {
        "FITS"
    } else {
        "EXCEEDS -> SEGMENT"
    };
    eprintln!(
        "{tag:<26} w={:<5} cols/1024={:<6} deg={:<2} pis={:<3} app_pis={:<3} sites={:<4} \
         constraints={:<6} [{fits}]",
        shape.digest_felts,
        d.trace_width,
        d.max_degree,
        d.public_input_count,
        d.public_input_count - pi::APP_BASE,
        air.builder.hash_site_count(),
        d.constraints.len(),
    );
    assert!(
        d.max_degree <= MAX_CONSTRAINT_DEGREE,
        "{tag}: degree {} exceeds the deployed cap {MAX_CONSTRAINT_DEGREE}",
        d.max_degree
    );
    assert!(
        d.public_input_count <= MAX_PUBLIC_INPUTS,
        "{tag}: {} PIs exceed the deployed cap {MAX_PUBLIC_INPUTS}",
        d.public_input_count
    );
    (d.trace_width, d.max_degree, d.public_input_count)
}

/// **THE HEADLINE MEASUREMENT.** The realistic HOARDLIGHT-scale composition the task
/// names: ~8 params x ~4 subjects + ~6 knots, at the deployable W=8 binding width.
///
/// This test only MEASURES; it never asserts the width fits. Whether it does is a fact
/// about the budget, printed here and reported in the crate's honest scope.
#[test]
fn realistic_shape_census() {
    eprintln!("\n=== REALISTIC SHAPE: ~8 params x ~4 subjects + ~6 knots ===");
    let realistic = ComposeShape::new(4, 8, 8, 6);
    let (w8, _, pis8) = report("realistic W=8 (DEPLOY)", &realistic);
    let (w1, _, _) = report("realistic W=1 (INSECURE)", &realistic.with_digest_felts(1));

    eprintln!(
        "\n  binding cost: W=8 costs {} columns over W=1 ({} -> {}), i.e. {:.1}x — the price of \
         the REFUSED one-site 8-felt primitive (MerkleHash8, custom_leaf_lowering.rs:625).",
        w8 - w1,
        w1,
        w8,
        w8 as f64 / w1 as f64
    );
    eprintln!(
        "  PI budget: {pis8}/{MAX_PUBLIC_INPUTS} total, {}/48 app — the layout is CONSTANT in the \
         subject count, so growing the scene never touches it.",
        pis8 - pi::APP_BASE
    );
    if w8 > MAX_TRACE_WIDTH {
        eprintln!(
            "  VERDICT: the realistic shape EXCEEDS {MAX_TRACE_WIDTH} at the deployable width by \
             {} columns -> SEGMENTATION REQUIRED (see the crate doc's segmentation plan).",
            w8 - MAX_TRACE_WIDTH
        );
    } else {
        eprintln!(
            "  VERDICT: the realistic shape FITS {MAX_TRACE_WIDTH} at the deployable width with \
             {} columns of headroom -> ONE leaf, no segmentation.",
            MAX_TRACE_WIDTH - w8
        );
    }
}

/// **THE IDENTITY-WIDTH LEVER.** The ordering tooth's range gadgets are the AIR's single
/// biggest column cost: a `b`-bit identity namespace spends `b` range columns per subject
/// plus `b+1` per ordering comparison. This sweep is why `identity_bits` is a SHAPE field
/// rather than a constant — sizing the namespace to the realm is what decides whether the
/// realistic shape needs segmenting at all.
#[test]
fn identity_width_sweep() {
    eprintln!("\n=== IDENTITY-WIDTH SWEEP (realistic shape, W=8) ===");
    let realistic = ComposeShape::new(4, 8, 8, 6);
    for bits in [12usize, 16, 20, 24, 28] {
        let sh = realistic.with_identity_bits(bits);
        let (w, _, _) = report(
            &format!(
                "identity_bits={bits} ({:>3}M ids)",
                (1u64 << bits) / 1_000_000
            ),
            &sh,
        );
        assert!(
            sh.identity_bits_sound(),
            "the ordering tooth must stay non-vacuous"
        );
        let _ = w;
    }
}

/// A shape whose identity width would make the ordering comparison VACUOUS is REFUSED,
/// not silently built. A 31-bit namespace lets both comparison bits satisfy the range
/// gadget, so the "canonical order + duplicate rejection" tooth would look present and
/// enforce nothing — exactly the failure this check exists to make impossible.
#[test]
fn an_identity_width_that_would_go_vacuous_is_refused() {
    let sh = ComposeShape::new(4, 8, 8, 6).with_identity_bits(31);
    assert!(!sh.identity_bits_sound());
    let comp = saturating(&ComposeShape::new(4, 8, 8, 6));
    assert!(
        build(&sh, &comp, &old8(), &new8()).is_err(),
        "a shape whose ordering comparison would be VACUOUS must be refused, never built"
    );
}

/// The census across shapes: where the 1024-column wall actually is at W=8.
#[test]
fn staged_width_census() {
    eprintln!("\n=== SHAPE CENSUS (all at the deployable W=8) ===");
    report("n2 p2 l1 k1", &ComposeShape::new(2, 2, 1, 1));
    report("n3 p4 l3 k2 (leaf test)", &ComposeShape::new(3, 4, 3, 2));
    report("n4 p8 l8 k6 (realistic)", &ComposeShape::new(4, 8, 8, 6));
    report("n6 p8 l12 k10", &ComposeShape::new(6, 8, 12, 10));
    report("n8 p16 l16 k16", &ComposeShape::new(8, 16, 16, 16));
}

/// The PI layout is CONSTANT in the number of subjects — the §9.3 property. Growing the
/// scene from 2 to 8 subjects must not move a single public input slot.
#[test]
fn the_pi_layout_does_not_encode_the_subject_count() {
    let counts: Vec<usize> = (2..=8)
        .map(|n| ComposeShape::new(n, 8, 8, 6).public_input_count())
        .collect();
    assert!(
        counts.windows(2).all(|w| w[0] == w[1]),
        "the PI count must not track the subject count (that is the cul-de-sac \
         HOARDLIGHT §9.3 names): {counts:?}"
    );
    assert_eq!(
        counts[0], 53,
        "W=8 layout: 16 door + 5 scalars + 4 roots x 8"
    );
    assert!(counts[0] <= MAX_PUBLIC_INPUTS);
    assert_eq!(
        counts[0] - pi::APP_BASE,
        37,
        "37 app PIs, inside the door's 48-PI app budget"
    );
}
