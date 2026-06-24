//! Stage-A integration test: a REAL SWGL render lands on the compositor-PD's
//! glass through the genuine T1/T2/T3 gate.
//!
//! This is the §4 Stage-A pipeline (steps 2 + 5) exercised end-to-end at the
//! crate boundary: construct a `SwglRenderingContext`, drive the SWGL GL to
//! rasterize a known frame into a caller-owned RGBA8 `Vec<u8>`, then carry that
//! real frame to `CompositorPd::present()` via the seam and assert the authorized
//! tile composited the real frame's digest. No GPU, no EGL, no mozjs.

#![cfg(feature = "swgl-standalone")]

use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::{cell_seed, label_of, CompositorPd, Refusal, Scene, Surface};
use gleam::gl;
use servo_render::{
    present_frame, with_gl, FramePresentation, RenderingContext, SwglRenderingContext,
};

/// Render a `W×H` frame cleared to a known RGBA color using the SWGL CPU
/// rasterizer, returning the owned RGBA8 frame. This stands in for a WebRender
/// `Renderer::render` of a real page until the `libservo` feature wires the engine
/// — but the rasterization, the buffer ownership, and the readback are all REAL.
///
/// The whole create→draw→read sequence runs under the process-wide SWGL
/// current-context lock ([`servo_render::GL_LOCK`] via [`with_gl`]): SWGL's
/// current context is a single global (`gl.cc:898`), so these two integration
/// tests — which run in parallel threads in the same test binary — must serialize
/// their SWGL access or they stomp each other's `ctx`/framebuffer binding.
fn render_known_frame(w: u32, h: u32, rgba: (u8, u8, u8, u8)) -> servo_render::RgbaFrame {
    with_gl(|| {
        let ctx = SwglRenderingContext::new(w, h);
        ctx.make_current();
        ctx.prepare_for_rendering();
        let glh = ctx.gleam_gl_api();
        let (r, g, b, a) = rgba;
        glh.clear_color(
            r as f32 / 255.0,
            g as f32 / 255.0,
            b as f32 / 255.0,
            a as f32 / 255.0,
        );
        glh.clear(gl::COLOR_BUFFER_BIT);
        ctx.present();
        ctx.read_frame()
    })
}

#[test]
fn stage_a_real_swgl_frame_reaches_the_glass_through_the_gate() {
    // A presenter cell owning region 5, focused, projecting root 1000.
    let presenter = cell_seed(7);
    let scene = Scene {
        surfaces: vec![Surface {
            owner: presenter,
            regions: vec![5],
            content_digest: 0,
            source_state_root: 1000,
            z_layer: 0,
            focus_flag: true,
        }],
    };
    let mut compositor = CompositorPd::boot(EmulatedKernel::new(), scene);

    // Render a REAL frame (opaque teal) via SWGL into a buffer we own.
    let frame = render_known_frame(16, 16, (0x00, 0x80, 0x80, 0xFF));
    assert_eq!(frame.bytes.len(), 16 * 16 * 4, "real RGBA8, 4 bytes/pixel");
    assert_eq!(
        frame.pixel(8, 8),
        (0x00, 0x80, 0x80, 0xFF),
        "SWGL rasterized the teal"
    );
    let digest = frame.content_digest();

    // Carry it through the GENUINE compositor gate.
    let commit = present_frame(
        &mut compositor,
        &frame,
        &FramePresentation {
            presenter,
            target_regions: vec![5],
            source_state_root: 1000,
            claims_focus: true,
        },
    )
    .expect("an honest present of a real frame is admitted");

    assert_eq!(
        commit.digest, digest,
        "the real pixels' digest is on the frame log"
    );
    assert_eq!(
        commit.label,
        label_of(&presenter, 1000),
        "T2: genuine owner-binding"
    );

    // The glass (the framebuffer the compositor solely holds) shows the real
    // frame's digest byte in the authorized tile.
    let fb = compositor.framebuffer_snapshot();
    assert_eq!(
        fb[5],
        (digest & 0xFF) as u8,
        "the authorized tile composited the SWGL frame"
    );
}

#[test]
fn stage_a_gate_still_refuses_a_foreign_overpaint_of_a_real_frame() {
    let owner = cell_seed(7);
    let intruder = cell_seed(8);
    let scene = Scene {
        surfaces: vec![
            Surface {
                owner,
                regions: vec![5],
                content_digest: 0,
                source_state_root: 1000,
                z_layer: 0,
                focus_flag: true,
            },
            Surface {
                owner: intruder,
                regions: vec![6],
                content_digest: 0,
                source_state_root: 2000,
                z_layer: 0,
                focus_flag: false,
            },
        ],
    };
    let mut compositor = CompositorPd::boot(EmulatedKernel::new(), scene);

    let frame = render_known_frame(8, 8, (0xFF, 0x00, 0x00, 0xFF));
    // The intruder targets the owner's region 5 — overpaint, must be refused even
    // though the frame is real.
    let verdict = present_frame(
        &mut compositor,
        &frame,
        &FramePresentation {
            presenter: intruder,
            target_regions: vec![5],
            source_state_root: 2000,
            claims_focus: false,
        },
    );
    assert!(
        matches!(verdict, Err(Refusal::Overpaint { .. })),
        "T1 bites on a real frame"
    );
    assert_eq!(
        compositor.framebuffer_snapshot()[5],
        0,
        "the victim's tile is untouched"
    );
}
