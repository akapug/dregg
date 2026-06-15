//! **The cap-gated render pipeline — Stage A's two halves, joined.**
//!
//! `docs/desktop-os-research/SERVO-ON-SEL4.md §4 Stage A` is one flow, but its
//! pieces have so far lived in two standalone crates:
//!
//! - **step 4 — the cap gate** (`starbridge-web-surface/src/delegate.rs`): a fetch
//!   / navigation a `WebView` performs is a `WebViewDelegate` callback, and the
//!   embedder's impl ([`CapGatedDelegate`]) IS the cap gate — a fetch the held
//!   [`SurfaceCapability`] does not permit is refused *at the callback*, before the
//!   engine acts (`granted ⊆ held`, the GENUINE `dregg_cell::is_attenuation`).
//! - **step 5 — the render → glass** (`compositor_seam`): a REAL SWGL frame is
//!   hashed to a `content_digest` and driven through the compositor-PD's unchanged
//!   T1/T2/T3 `present()` gate ([`present_frame`]).
//!
//! Until now nothing connected them: the render path rendered a frame with **no
//! cap mediation upstream**, and the cap gate decided fetches with **no render
//! downstream**. This module is the seam that makes the Stage-A flow whole:
//!
//! > a **cap-gated fetch** (the held surface cap) decides whether a page may load;
//! > **iff it may**, the page is rendered via SWGL and **presented through the
//! > compositor gate**; **iff it may not**, the fetch is refused *in-band* and **no
//! > frame ever reaches the glass**.
//!
//! ## What is real here (NOT a re-mock — the toy-disease guard)
//!
//! Every authority object is the GENUINE one. [`SurfaceCapability`],
//! [`CapGatedDelegate`], [`ResourceDecision`] are the REAL
//! `starbridge_web_surface` types (libservo's `WebViewDelegate` shape + the
//! firmament `Capability`); [`present_frame`] drives the REAL `dregg_firmament`
//! compositor gate. Both crates path-depend on the SAME `../sel4/dregg-firmament`,
//! so the [`CellId`] backing the surface cap and the [`CellId`] presenting to the
//! compositor are the *same type and the same value* — the cap that authorizes the
//! fetch is the cap that owns the surface the frame lands on. We wire two real
//! gates in series; we invent neither.
//!
//! ## What is still the seam (HONEST — not laundered)
//!
//! The *render itself* is still the SWGL clear-to-color stand-in for a WebRender
//! `Renderer::render` of a real `WebView` (the `libservo` feature, the mozjs long
//! pole, is not linked). So this proves **the cap gate gates the render that
//! reaches the glass** — the step-4↔step-5 join — on REAL pixels through the REAL
//! compositor, with the *page content* still synthetic. The remaining wall is
//! exactly step 3 (`libservo` + mozjs): swap the `render_color` stand-in for a real
//! `WebView` painting into the [`SwglRenderingContext`]. The gate, the cap model,
//! the present path are all unchanged when that lands.

#![cfg(feature = "swgl-standalone")]

use dregg_firmament::{CompositorPd, FrameCommit, Refusal};
use gleam::gl;
use starbridge_web_surface::{CapGatedDelegate, ResourceDecision, SurfaceCapability, WebSurfaceDelegate};

use crate::compositor_seam::{present_frame, FramePresentation};
use crate::swgl_context::{with_gl, RenderingContext, RgbaFrame, SwglRenderingContext};

/// The outcome of a cap-gated render: either the fetch was refused at the cap gate
/// (no render, nothing on the glass), the render+present was refused at the
/// compositor gate, or the frame reached the glass.
#[derive(Clone, Debug)]
pub enum PipelineOutcome {
    /// **The cap gate refused the fetch** ([`CapGatedDelegate::load_web_resource`]
    /// returned [`ResourceDecision::Intercept`]): the held surface cap does not
    /// permit `origin`. The page sees the cap-denied body, the renderer is NEVER
    /// driven, and the compositor's framebuffer is untouched. This is the in-band
    /// refusal — the whole point of the gate-in-front-of-the-render.
    FetchRefused {
        /// The cap-denied body the renderer would have received instead of the
        /// resource (the same bytes `load_web_resource`'s `Intercept` carries).
        denied_body: Vec<u8>,
    },
    /// The fetch was allowed and the frame rendered, but the **compositor gate**
    /// refused the `present()` (T1 overpaint / T2 label-spoof / T3 focus). The
    /// frame is real but it did not reach the glass — the authority teeth bit.
    PresentRefused(Refusal),
    /// The fetch was allowed, the frame rendered via SWGL, and the compositor gate
    /// ADMITTED it: the frame is on the glass. Carries the genuine [`FrameCommit`]
    /// (the real pixels' digest + the owner-binding label) and the rendered frame.
    Presented {
        /// The compositor's commit receipt for the admitted frame.
        commit: FrameCommit,
        /// The frame that reached the glass (the real SWGL RGBA8).
        frame: RgbaFrame,
    },
}

impl PipelineOutcome {
    /// Did a frame actually reach the glass?
    pub fn reached_glass(&self) -> bool {
        matches!(self, PipelineOutcome::Presented { .. })
    }

    /// Was the fetch refused at the CAP gate (vs. the compositor gate, vs.
    /// admitted)? The load-bearing "the cap stopped it before the render" check.
    pub fn fetch_was_refused(&self) -> bool {
        matches!(self, PipelineOutcome::FetchRefused { .. })
    }
}

/// **THE STAGE-A PIPELINE: cap-gated fetch → SWGL render → compositor present.**
///
/// Drive one frame of the Stage-A flow with the cap gate IN FRONT of the render:
///
/// 1. Ask the REAL cap gate whether `surface` may fetch `origin`
///    ([`CapGatedDelegate::load_web_resource`] → the genuine `granted ⊆ held`
///    allowlist check). On [`ResourceDecision::Intercept`] (cap-denied) return
///    [`PipelineOutcome::FetchRefused`] *immediately* — the SWGL renderer is never
///    driven and the compositor's framebuffer is untouched.
/// 2. On [`ResourceDecision::Continue`] (cap-permitted), render a frame via the
///    SWGL CPU rasterizer into a caller-owned RGBA8 buffer (here a clear to
///    `render_color`, the WebRender-`Renderer::render` stand-in until the
///    `libservo` feature wires a real `WebView`).
/// 3. Carry the real frame through the compositor-PD's unchanged T1/T2/T3
///    [`present_frame`] gate, returning the [`FrameCommit`] (admit) or the
///    [`Refusal`] (a present the authority teeth bite).
///
/// `presentation` names which cell presents + which regions it targets; for the
/// genuine cap model `presentation.presenter` should be the cell the `surface`'s
/// cap backs (`surface.cell()`), so the cap that authorized the fetch is the cap
/// that owns the surface the frame lands on.
pub fn fetch_render_present(
    compositor: &mut CompositorPd,
    surface: &SurfaceCapability,
    delegate: &CapGatedDelegate,
    origin: &str,
    render_color: (u8, u8, u8, u8),
    presentation: &FramePresentation,
) -> PipelineOutcome {
    // STEP 1 — the cap gate, IN FRONT of the render. The held surface cap decides;
    // a fetch it does not permit is refused here, before a single pixel is drawn.
    match delegate.load_web_resource(surface, origin) {
        ResourceDecision::Intercept { body, .. } => {
            // Cap-denied: the renderer is never driven; the glass is untouched.
            return PipelineOutcome::FetchRefused { denied_body: body };
        }
        ResourceDecision::Continue => { /* cap-permitted — render below */ }
    }

    // STEP 2 — render the (now-permitted) frame via SWGL into a buffer we own.
    // This stands in for a WebRender `Renderer::render` of a real `WebView` until
    // the `libservo` feature links the engine; the rasterization is REAL.
    let frame = render_frame(presentation_size(presentation), render_color);

    // STEP 3 — carry the real frame through the GENUINE compositor gate.
    match present_frame(compositor, &frame, presentation) {
        Ok(commit) => PipelineOutcome::Presented { commit, frame },
        Err(refusal) => PipelineOutcome::PresentRefused(refusal),
    }
}

/// The framebuffer size to render at. A small fixed tile is fine for the standalone
/// render-path proof (the compositor gate keys on the digest + the region-set, not
/// the pixel dimensions); a real `WebView` path sizes this to the surface.
fn presentation_size(_presentation: &FramePresentation) -> (u32, u32) {
    (16, 16)
}

/// Render a `w×h` frame cleared to `rgba` via the SWGL CPU rasterizer, under the
/// process-wide SWGL current-context lock. The same real render path the
/// `compositor_seam` integration test exercises — REAL RGBA8 out of the C++
/// rasterizer into a caller-owned `Vec<u8>`.
fn render_frame((w, h): (u32, u32), rgba: (u8, u8, u8, u8)) -> RgbaFrame {
    with_gl(|| {
        let ctx = SwglRenderingContext::new(w, h);
        ctx.make_current();
        ctx.prepare_for_rendering();
        let glh = ctx.gleam_gl_api();
        let (r, g, b, a) = rgba;
        glh.clear_color(r as f32 / 255.0, g as f32 / 255.0, b as f32 / 255.0, a as f32 / 255.0);
        glh.clear(gl::COLOR_BUFFER_BIT);
        ctx.present();
        ctx.read_frame()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::emulated_kernel::EmulatedKernel;
    use dregg_firmament::{cell_seed, label_of, Scene, Surface};
    use starbridge_web_surface::AuthRequired;

    /// A one-surface scene the `presenter` cell owns region 5 in, focused,
    /// projecting root 1000 (so any real frame advances its digest).
    fn one_surface_scene(presenter: dregg_firmament::CellId) -> Scene {
        Scene {
            surfaces: vec![Surface {
                owner: presenter,
                regions: vec![5],
                content_digest: 0,
                source_state_root: 1000,
                z_layer: 0,
                focus_flag: true,
            }],
        }
    }

    fn presentation_for(presenter: dregg_firmament::CellId) -> FramePresentation {
        FramePresentation {
            presenter,
            target_regions: vec![5],
            source_state_root: 1000,
            claims_focus: true,
        }
    }

    /// **THE LOAD-BEARING SEAM TEST: a fetch the cap does NOT permit is refused at
    /// the cap gate, and NO frame reaches the glass.**
    ///
    /// This is the join the whole module exists for: the cap gate sits in FRONT of
    /// the SWGL render → compositor present. A surface scoped to `example.com` tries
    /// to load `evil.com` (⊄ its fetch allowlist) — the REAL
    /// `CapGatedDelegate::load_web_resource` intercepts it, so the renderer is never
    /// driven and the compositor's framebuffer is UNTOUCHED. The refusal is in-band
    /// (the page would get the cap-denied body), exactly as a mediated effect a held
    /// cap does not permit.
    #[test]
    fn an_uncapped_fetch_is_refused_at_the_gate_and_no_frame_reaches_the_glass() {
        let presenter = cell_seed(7);
        // The surface's cap IS over `presenter` (the same cell that owns the
        // scene's surface) — the genuine bind: the fetch-authorizing cap and the
        // present-owning cap are one cell.
        let surface = SurfaceCapability::scoped(
            presenter,
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );
        let mut compositor = CompositorPd::boot(EmulatedKernel::new(), one_surface_scene(presenter));

        // The glass starts blank in region 5.
        assert_eq!(compositor.framebuffer_snapshot()[5], 0, "region 5 starts blank");

        let outcome = fetch_render_present(
            &mut compositor,
            &surface,
            &CapGatedDelegate::new(),
            "https://evil.com", // ⊄ {example.com} — the cap forbids it
            (0xFF, 0x00, 0x00, 0xFF),
            &presentation_for(presenter),
        );

        // The fetch was refused at the CAP gate (not the compositor gate).
        assert!(outcome.fetch_was_refused(), "an out-of-allowlist fetch is refused at the cap gate");
        assert!(!outcome.reached_glass(), "a cap-refused fetch puts NOTHING on the glass");
        match outcome {
            PipelineOutcome::FetchRefused { denied_body } => {
                let s = String::from_utf8(denied_body).unwrap();
                assert!(s.contains("blocked by capability"), "the page gets the cap-denied body");
            }
            other => panic!("expected FetchRefused, got {other:?}"),
        }

        // THE LOAD-BEARING ASSERTION: the renderer never ran, so the compositor's
        // framebuffer is untouched — the cap gate stopped the frame BEFORE the glass.
        assert_eq!(
            compositor.framebuffer_snapshot()[5],
            0,
            "no frame reached the glass — the cap gate refused before the render"
        );
    }

    /// **THE PAYOFF: a fetch the cap DOES permit renders a real SWGL frame that
    /// reaches the glass through the compositor gate.**
    ///
    /// The other side of the seam: a surface scoped to `example.com` loading
    /// `example.com` (∈ its allowlist) is permitted by the cap gate, so the SWGL
    /// renderer IS driven, a real RGBA8 frame is produced, and it lands on the glass
    /// through the genuine T1/T2/T3 `present()` gate — the cap-authorized cell
    /// presenting to the surface its cap backs.
    #[test]
    fn a_capped_fetch_renders_a_real_frame_that_reaches_the_glass() {
        let presenter = cell_seed(7);
        let surface = SurfaceCapability::scoped(
            presenter,
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );
        let mut compositor = CompositorPd::boot(EmulatedKernel::new(), one_surface_scene(presenter));

        let outcome = fetch_render_present(
            &mut compositor,
            &surface,
            &CapGatedDelegate::new(),
            "https://example.com", // ∈ {example.com} — the cap permits it
            (0x00, 0x80, 0x80, 0xFF), // opaque teal
            &presentation_for(presenter),
        );

        // The frame reached the glass through the genuine gate.
        assert!(outcome.reached_glass(), "a cap-permitted fetch renders and reaches the glass");
        match outcome {
            PipelineOutcome::Presented { commit, frame } => {
                // The frame is a REAL SWGL render (the teal we asked for).
                assert_eq!(frame.bytes.len(), 16 * 16 * 4, "real RGBA8, 4 bytes/pixel");
                assert_eq!(frame.pixel(8, 8), (0x00, 0x80, 0x80, 0xFF), "SWGL rasterized the teal");
                // The commit carries the real pixels' digest + the genuine owner-binding.
                assert_eq!(commit.digest, frame.content_digest(), "the real pixels' digest is committed");
                assert_eq!(commit.label, label_of(&presenter, 1000), "T2: the genuine owner-binding");
                // The glass shows the real frame's digest byte in the authorized tile.
                assert_eq!(
                    compositor.framebuffer_snapshot()[5],
                    (frame.content_digest() & 0xFF) as u8,
                    "the cap-authorized frame composited to the glass"
                );
            }
            other => panic!("expected Presented, got {other:?}"),
        }
    }

    /// **The cap gate and the compositor gate are INDEPENDENT teeth.** Even a
    /// cap-PERMITTED fetch is still subject to the compositor's authority gate: a
    /// presenter rendering a region it does not own is refused at the *compositor*
    /// gate (T1 overpaint) — the two gates compose, neither subsumes the other.
    #[test]
    fn a_capped_fetch_is_still_subject_to_the_compositor_gate() {
        let owner = cell_seed(7);
        let intruder = cell_seed(8);
        // Scene: `owner` owns region 5; `intruder` owns region 6.
        let scene = Scene {
            surfaces: vec![
                Surface { owner, regions: vec![5], content_digest: 0, source_state_root: 1000, z_layer: 0, focus_flag: true },
                Surface { owner: intruder, regions: vec![6], content_digest: 0, source_state_root: 2000, z_layer: 0, focus_flag: false },
            ],
        };
        let mut compositor = CompositorPd::boot(EmulatedKernel::new(), scene);

        // The intruder's surface cap is a WILDCARD (fetch-anything) — so the CAP
        // gate permits the fetch. The refusal must therefore come from the
        // COMPOSITOR gate (overpainting region 5, which `owner` holds), proving the
        // two gates are independent.
        let intruder_surface = SurfaceCapability::root(intruder, AuthRequired::Either);

        let outcome = fetch_render_present(
            &mut compositor,
            &intruder_surface,
            &CapGatedDelegate::new(),
            "https://anything.example", // wildcard cap permits ANY fetch
            (0xFF, 0x00, 0x00, 0xFF),
            &FramePresentation {
                presenter: intruder,
                target_regions: vec![5], // region 5 is OWNER's, not intruder's — overpaint
                source_state_root: 2000,
                claims_focus: false,
            },
        );

        // The fetch was NOT refused at the cap gate (the wildcard permitted it)...
        assert!(!outcome.fetch_was_refused(), "the wildcard cap permits the fetch");
        // ...but the frame did NOT reach the glass — the COMPOSITOR gate bit (T1).
        assert!(!outcome.reached_glass(), "the compositor gate refuses the overpaint");
        assert!(
            matches!(outcome, PipelineOutcome::PresentRefused(Refusal::Overpaint { .. })),
            "a cap-permitted fetch is still refused by the compositor's T1 overpaint tooth"
        );
        // The victim's tile is untouched (fail-closed at the compositor gate).
        assert_eq!(compositor.framebuffer_snapshot()[5], 0, "the owner's tile is untouched");
    }
}
