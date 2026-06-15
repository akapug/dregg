//! Crate-boundary integration test: the cap gate gates the render that reaches the
//! glass, exercised through the PUBLIC `servo_render` API (the same way
//! `stage_a_render_to_glass.rs` exercises `present_frame`).
//!
//! This is the Stage-A step-4↔step-5 join (`SERVO-ON-SEL4.md §4`): a fetch through
//! the REAL `starbridge_web_surface` cap gate decides whether the SWGL render is
//! driven, and an admitted frame reaches the compositor-PD's glass through the
//! genuine T1/T2/T3 gate — all at the crate boundary, no internals. No mozjs.

#![cfg(feature = "swgl-standalone")]

use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::{cell_seed, CompositorPd, Scene, Surface};
use servo_render::{fetch_render_present, FramePresentation, PipelineOutcome};
use starbridge_web_surface::{AuthRequired, CapGatedDelegate, SurfaceCapability};

/// A one-surface scene `presenter` owns region 3 in, focused, projecting root 500.
fn scene_for(presenter: dregg_firmament::CellId) -> Scene {
    Scene {
        surfaces: vec![Surface {
            owner: presenter,
            regions: vec![3],
            content_digest: 0,
            source_state_root: 500,
            z_layer: 0,
            focus_flag: true,
        }],
    }
}

fn presentation_for(presenter: dregg_firmament::CellId) -> FramePresentation {
    FramePresentation {
        presenter,
        target_regions: vec![3],
        source_state_root: 500,
        claims_focus: true,
    }
}

/// **A cap-permitted fetch renders a real SWGL frame that reaches the glass** — and
/// **a cap-forbidden fetch puts nothing on the glass** — driven through the public
/// `fetch_render_present`, with the SAME surface cap (scoped to one origin) for both.
#[test]
fn the_cap_gate_decides_whether_a_real_frame_reaches_the_glass() {
    let presenter = cell_seed(11);
    // One surface cap, scoped to example.com. The SAME cap backs the scene surface
    // (presenter) — the genuine bind between fetch authority and surface ownership.
    let surface = SurfaceCapability::scoped(
        presenter,
        AuthRequired::Either,
        [String::from("https://example.com")],
        [],
    );
    let delegate = CapGatedDelegate::new();

    // (a) The PERMITTED origin: the frame renders and reaches the glass.
    let mut compositor = CompositorPd::boot(EmulatedKernel::new(), scene_for(presenter));
    let permitted = fetch_render_present(
        &mut compositor,
        &surface,
        &delegate,
        "https://example.com",
        (0x20, 0xC0, 0x40, 0xFF),
        &presentation_for(presenter),
    );
    assert!(permitted.reached_glass(), "a cap-permitted fetch reaches the glass");
    let digest_byte = match permitted {
        PipelineOutcome::Presented { ref frame, ref commit } => {
            assert_eq!(frame.pixel(8, 8), (0x20, 0xC0, 0x40, 0xFF), "SWGL rasterized the color");
            assert_eq!(commit.digest, frame.content_digest(), "the real pixels' digest is committed");
            (frame.content_digest() & 0xFF) as u8
        }
        other => panic!("expected Presented, got {other:?}"),
    };
    assert_eq!(
        compositor.framebuffer_snapshot()[3],
        digest_byte,
        "the cap-authorized frame composited to the glass"
    );

    // (b) A FORBIDDEN origin on a FRESH compositor: refused at the cap gate, glass blank.
    let mut compositor2 = CompositorPd::boot(EmulatedKernel::new(), scene_for(presenter));
    let forbidden = fetch_render_present(
        &mut compositor2,
        &surface,
        &delegate,
        "https://tracker.ad-network.com", // ⊄ {example.com}
        (0xFF, 0x00, 0x00, 0xFF),
        &presentation_for(presenter),
    );
    assert!(forbidden.fetch_was_refused(), "an out-of-allowlist fetch is refused at the cap gate");
    assert!(!forbidden.reached_glass(), "a cap-refused fetch puts nothing on the glass");
    assert_eq!(
        compositor2.framebuffer_snapshot()[3],
        0,
        "the glass is blank — the cap gate stopped the frame before the render"
    );
}
