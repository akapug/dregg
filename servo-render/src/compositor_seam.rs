//! The compositor seam — feed a SWGL `RgbaFrame` into the compositor-PD's
//! `present()` contract (`SERVO-ON-SEL4.md §3.2`, step 5 of Stage A).
//!
//! `compositor_pd.rs`'s `present(presenter, Present { .., new_digest })` carries a
//! `content_digest` (a `u64`) that, today, is a PROMISE of pixels — the honestly-
//! labeled F3 fidelity gap (`CompositorPd::FIDELITY`). This module makes the
//! promise GOOD: it hashes a REAL SWGL-rendered RGBA8 frame to the `content_digest`
//! and builds the `Present` the compositor's UNCHANGED T1/T2/T3 gate admits.
//!
//! ## What is and isn't done here (HONEST — not laundered)
//!
//! - **The bytes become real.** The `content_digest` is now `blake3(rgba8)` of an
//!   actual CPU-rasterized frame, not a stand-in. That closes **F3 (real pixels
//!   from a confined renderer)** on the host.
//! - **The gate is untouched.** We construct a genuine [`Present`] and call the
//!   genuine [`CompositorPd::present`]; the T1 non-overlap / T2 label-binding / T3
//!   focus-exclusivity teeth, the `is_attenuation` lattice, the no-amplification
//!   keystone are all the REAL dregg machinery, exactly as `BUILD-STATUS.md`
//!   promises ("only `MockSurface` is replaced"). We reinvent NONE of it.
//! - **F1/F2 remain the frontier.** Binding the *scanned-out* framebuffer to the
//!   digest (F1) and IOMMU/DMA-confining a display PD (F2) are NOT done here and
//!   are NOT claimed — they are the named hardware-trust frontier (`§3.3`). "The
//!   pixels are now real" does NOT launder "the scan-out is now attested."
//!
//! ## The seam shape
//!
//! [`present_frame`] is the one function Stage A's step 5 needs: given a rendered
//! [`RgbaFrame`], the presenter cell, its target region(s) + label binding, it
//! computes the digest and drives `present()`. The compositor then (iff the gate
//! admits) composites the authorized region into the framebuffer it SOLELY holds.

#![cfg(feature = "swgl-standalone")]

use dregg_firmament::CellId;
use dregg_firmament::{label_of, CompositorPd, FrameCommit, Present, Refusal};

use crate::swgl_context::RgbaFrame;

/// A presenter's intent to show a rendered frame: which cell is presenting, the
/// region-set it owns and targets, the state-root the content projects, and
/// whether it asserts input focus. The `content_digest` is NOT here — it is
/// derived from the real pixels by [`present_frame`], which is the whole point.
#[derive(Clone, Debug)]
pub struct FramePresentation {
    /// The cell presenting (the authority lineage the compositor reads).
    pub presenter: CellId,
    /// The region-set this frame paints (T1: must be ⊆ the presenter's owned set
    /// AND disjoint from foreign surfaces).
    pub target_regions: Vec<u32>,
    /// The cell state-root the rendered content is a projection of (T2 binds the
    /// label to this; a light client checks the content against it).
    pub source_state_root: u64,
    /// Whether this present asserts input focus (T3).
    pub claims_focus: bool,
}

/// **THE STAGE-A STEP-5 SEAM: render → hash → present → gate → blit.**
///
/// Bind a REAL SWGL-rendered [`RgbaFrame`] to the compositor-PD's `present()`:
/// compute `content_digest = blake3(rgba8)`, build the genuine [`Present`] with the
/// COMPOSITOR-COMPUTED label (`label_of(presenter, source_state_root)` — never
/// app-chosen, T2's binding discipline), and drive [`CompositorPd::present`]. The
/// compositor's unchanged T1∧T2∧T3 gate decides; on admit it composites the
/// authorized region into the framebuffer it solely holds and returns the
/// [`FrameCommit`]; on refusal nothing changes (fail-closed) and the [`Refusal`]
/// names the tooth that bit.
///
/// This is the function the deos compositor render pass calls each frame once the
/// SWGL context is rendering a real `WebView` (the `libservo` path) — and it works
/// IDENTICALLY today with the standalone SWGL frame, which is the whole de-risking
/// value of Stage A standing alone.
pub fn present_frame(
    compositor: &mut CompositorPd,
    frame: &RgbaFrame,
    presentation: &FramePresentation,
) -> Result<FrameCommit, Refusal> {
    // The bind that makes F3 real: the digest is a hash of the ACTUAL pixels.
    let content_digest = frame.content_digest();

    // The label is the COMPOSITOR's, a function of the cell's authority lineage —
    // computed here exactly as the compositor would (T2). An honest presenter
    // declares this genuine binding; the gate is what makes it load-bearing.
    let declared_label = label_of(&presentation.presenter, presentation.source_state_root);

    let present = Present {
        target: presentation.target_regions.clone(),
        source_state_root: presentation.source_state_root,
        declared_label,
        claims_focus: presentation.claims_focus,
        new_digest: content_digest,
    };

    // Drive the GENUINE compositor gate. Everything it checks is the real dregg
    // machinery; only the SOURCE of the digest changed (MockSurface stand-in → a
    // real SWGL render). The compositor composites the authorized region into the
    // framebuffer it solely holds iff every tooth admits.
    compositor.present(&presentation.presenter, present)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::emulated_kernel::EmulatedKernel;
    use dregg_firmament::{cell_seed, Scene, Surface};

    /// A one-surface scene the presenter owns region 7 in, focused, projecting
    /// root 42 with an initial digest of 0 (so any real frame advances it).
    fn one_surface_scene(presenter: CellId) -> Scene {
        Scene {
            surfaces: vec![Surface {
                owner: presenter,
                regions: vec![7],
                content_digest: 0,
                source_state_root: 42,
                z_layer: 0,
                focus_flag: true,
            }],
        }
    }

    /// **END-TO-END: a REAL SWGL frame is presented through the GENUINE compositor
    /// gate and lands in the framebuffer the compositor solely holds.**
    ///
    /// This is the Stage-A payoff wiring (step 5), exercised standalone: render a
    /// frame's worth of RGBA8 (here a small owned buffer), hash it, present it, and
    /// assert the compositor ADMITTED it (the digest is on the frame log, and the
    /// composited tile reflects the real frame's digest byte).
    #[test]
    fn real_frame_presents_through_the_compositor_gate() {
        let presenter = cell_seed(3);
        let kernel = EmulatedKernel::new();
        let mut compositor = CompositorPd::boot(kernel, one_surface_scene(presenter));

        // A real owned RGBA8 frame (the shape a SWGL render produces). Distinctive
        // bytes so the digest is non-trivial.
        let frame = RgbaFrame {
            width: 2,
            height: 1,
            bytes: vec![0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0],
        };
        let digest = frame.content_digest();

        let presentation = FramePresentation {
            presenter,
            target_regions: vec![7],
            source_state_root: 42,
            claims_focus: true,
        };

        let commit = present_frame(&mut compositor, &frame, &presentation)
            .expect("an honest present of a real frame is admitted by the gate");

        // The commit carries the REAL pixels' digest and the genuine owner-label.
        assert_eq!(
            commit.digest, digest,
            "the frame log records the real pixels' digest"
        );
        assert_eq!(
            commit.label,
            label_of(&presenter, 42),
            "T2: the genuine owner-binding"
        );
        assert_eq!(commit.regions, vec![7]);

        // The framebuffer the compositor SOLELY holds now shows the frame's digest
        // byte in region 7 (the load-bearing authority observable).
        let fb = compositor.framebuffer_snapshot();
        assert_eq!(
            fb[7],
            (digest & 0xFF) as u8,
            "the authorized tile composited the real frame"
        );
        assert_eq!(fb[0], 0, "an unrelated tile is untouched");
    }

    /// **The gate still BITES on a real frame.** A presenter targeting a region it
    /// does NOT own is refused (T1 overpaint) even though the pixels are real —
    /// proving the seam did not weaken the compositor's authority teeth.
    #[test]
    fn real_frame_overpainting_a_foreign_region_is_refused() {
        let presenter = cell_seed(3);
        let intruder = cell_seed(4);
        let kernel = EmulatedKernel::new();
        // Scene: presenter owns region 7 (focused); intruder owns region 8.
        let scene = Scene {
            surfaces: vec![
                Surface {
                    owner: presenter,
                    regions: vec![7],
                    content_digest: 0,
                    source_state_root: 42,
                    z_layer: 0,
                    focus_flag: true,
                },
                Surface {
                    owner: intruder,
                    regions: vec![8],
                    content_digest: 0,
                    source_state_root: 99,
                    z_layer: 0,
                    focus_flag: false,
                },
            ],
        };
        let mut compositor = CompositorPd::boot(kernel, scene);

        let frame = RgbaFrame {
            width: 1,
            height: 1,
            bytes: vec![0xAA, 0xBB, 0xCC, 0xDD],
        };
        // The intruder tries to paint region 7 (the presenter's) — overpaint.
        let presentation = FramePresentation {
            presenter: intruder,
            target_regions: vec![7],
            source_state_root: 99,
            claims_focus: false,
        };

        let verdict = present_frame(&mut compositor, &frame, &presentation);
        assert!(
            matches!(verdict, Err(Refusal::Overpaint { .. })),
            "a real frame cannot overpaint a foreign region — the gate bites (T1)"
        );
        // The victim's tile is untouched (fail-closed).
        let fb = compositor.framebuffer_snapshot();
        assert_eq!(fb[7], 0, "the overpaint never reached the framebuffer");
    }
}
