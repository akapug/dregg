//! **Present through the EXISTING gate.** An android [`RgbaFrame`] driven through
//! `servo-render`'s UNCHANGED `present_frame` / `CompositorPd` seam.
//!
//! This module is deliberately thin: it is the proof that the expensive half is free.
//! The android frame is handed to the SAME [`servo_render::present_frame`] the SWGL
//! webcell uses; the SAME T1 non-overlap / T2 label-binding / T3 focus teeth decide;
//! the SAME [`FrameCommit`] (carrying `blake3(rgba8)` + the owner-label) comes back.
//! The compositor cannot tell an android frame from a Servo frame — it hashes the
//! pixels and checks authority, nothing more. `servo:web :: android-runtime:android`
//! at the one seam that matters.

use dregg_firmament::{CellId, CompositorPd, FrameCommit, Refusal};
use servo_render::{present_frame, FramePresentation, RgbaFrame};

/// An android-cell's intent to show its app's frame: which cell presents, the region
/// it owns + targets, the state-root the content projects, and whether it claims
/// focus. A thin wrapper that maps straight onto [`servo_render::FramePresentation`]
/// — there is no android-specific present vocabulary, by design.
#[derive(Clone, Debug)]
pub struct AndroidPresentation {
    pub presenter: CellId,
    pub target_regions: Vec<u32>,
    pub source_state_root: u64,
    pub claims_focus: bool,
}

impl From<AndroidPresentation> for FramePresentation {
    fn from(a: AndroidPresentation) -> Self {
        FramePresentation {
            presenter: a.presenter,
            target_regions: a.target_regions,
            source_state_root: a.source_state_root,
            claims_focus: a.claims_focus,
        }
    }
}

/// **Present an android frame through the GENUINE compositor gate.** A one-line
/// delegation to [`servo_render::present_frame`] — the whole point is that no new
/// compositor code exists. The digest is `blake3(rgba8)` of the real android pixels;
/// the gate admits iff every tooth (T1/T2/T3) does; on refusal nothing changes
/// (fail-closed) and the [`Refusal`] names the tooth that bit.
pub fn present_android_frame(
    compositor: &mut CompositorPd,
    frame: &RgbaFrame,
    presentation: AndroidPresentation,
) -> Result<FrameCommit, Refusal> {
    let presentation: FramePresentation = presentation.into();
    present_frame(compositor, frame, &presentation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frame::screencap_to_rgba;
    use dregg_firmament::emulated_kernel::EmulatedKernel;
    use dregg_firmament::{cell_seed, label_of, Scene, Surface};

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

    /// **END-TO-END: a REAL captured Android frame presents through the GENUINE
    /// compositor gate.** The committed home-screen fixture is parsed to an
    /// `RgbaFrame` and presented; the gate admits an honest present and the commit
    /// carries the real android pixels' digest + the genuine owner-label. This is the
    /// android-cell's "first real rendered content" milestone — an android app's frame
    /// on the deos glass.
    #[test]
    fn real_android_frame_presents_through_the_compositor_gate() {
        let presenter = cell_seed(3);
        let kernel = EmulatedKernel::new();
        let mut compositor = CompositorPd::boot(kernel, one_surface_scene(presenter));

        // A REAL android frame (the live emulator's home screen, downscaled fixture).
        let raw = include_bytes!("../fixtures/android_home_screencap.raw");
        let frame = screencap_to_rgba(raw).expect("the real android frame converts");
        let digest = frame.content_digest();

        let commit = present_android_frame(
            &mut compositor,
            &frame,
            AndroidPresentation {
                presenter,
                target_regions: vec![7],
                source_state_root: 42,
                claims_focus: true,
            },
        )
        .expect("an honest present of a real android frame is admitted by the gate");

        assert_eq!(commit.digest, digest, "the real android pixels' digest");
        assert_eq!(commit.label, label_of(&presenter, 42), "T2: owner-binding");
        assert_eq!(commit.regions, vec![7]);

        // The framebuffer the compositor solely holds now shows the android frame.
        let fb = compositor.framebuffer_snapshot();
        assert_eq!(fb[7], (digest & 0xFF) as u8, "the android tile composited");
        assert_eq!(fb[0], 0, "an unrelated tile untouched");
    }

    /// **The gate still BITES on an android frame.** An intruder presenting a real
    /// android frame into a region it does not own is refused (T1 overpaint) — the
    /// seam did not weaken the compositor's authority teeth for android-sourced pixels.
    #[test]
    fn android_frame_overpainting_a_foreign_region_is_refused() {
        let presenter = cell_seed(3);
        let intruder = cell_seed(4);
        let kernel = EmulatedKernel::new();
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

        let raw = include_bytes!("../fixtures/android_home_screencap.raw");
        let frame = screencap_to_rgba(raw).unwrap();

        let verdict = present_android_frame(
            &mut compositor,
            &frame,
            AndroidPresentation {
                presenter: intruder,
                target_regions: vec![7], // the presenter's region — overpaint
                source_state_root: 99,
                claims_focus: false,
            },
        );

        assert!(
            matches!(verdict, Err(Refusal::Overpaint { .. })),
            "a real android frame cannot overpaint a foreign region — the gate bites (T1)"
        );
        let fb = compositor.framebuffer_snapshot();
        assert_eq!(fb[7], 0, "the overpaint never reached the framebuffer");
    }
}
