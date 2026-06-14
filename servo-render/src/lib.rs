//! `servo-render` — the HOST SWGL render path that IS deos's compositor render
//! pass (**Stage A** of `docs/desktop-os-research/SERVO-ON-SEL4.md`).
//!
//! # The one paragraph
//!
//! The compositor-PD (`sel4/dregg-firmament/src/compositor_pd.rs`) carries a
//! `present(region, contentDigest)` whose `contentDigest` is, today, a *promise*
//! of pixels — its honestly-labeled **F3** fidelity gap. This crate makes the
//! pixels REAL: a [`SwglRenderingContext`](swgl_context::SwglRenderingContext)
//! backed by WebRender's **SWGL** (`swgl 0.68.0` — a self-contained, CPU-only,
//! framebuffer-out software GL that `impl Gl for swgl::Context`, so it IS a
//! `gleam::gl::Gl`) renders a page into a caller-owned RGBA8 `Vec<u8>`, and
//! [`compositor_seam::present_frame`] hashes those bytes to the `content_digest`
//! the compositor's unchanged T1/T2/T3 gate admits. **No GPU, no EGL, no platform
//! surface** — "unaccelerated but real."
//!
//! # The HONEST build split (this crate's whole design)
//!
//! - **`swgl-standalone` (DEFAULT)** — depends on NOTHING but `swgl` + `gleam` (+
//!   the real `dregg-firmament` for the compositor seam). This is the de-risking
//!   core: it proves SWGL's C++17 rasterizer (clang, `gl.cc`) COMPILES on this
//!   host and produces REAL RGBA8 pixels, *independent of the libservo elephant*.
//!   The tests here exercise that.
//! - **`libservo` (OPT-IN)** — adds the real `servo` + `servo-paint-api` and wires
//!   the SWGL context into a real `WebView` (see [`webview`]). This pulls `script`
//!   → `mozjs` (the multi-GB SpiderMonkey C++ build) — the known-hard, known-walked
//!   long pole, kept behind a feature so the core builds without grinding it.
//!
//! # What closes and what doesn't (NOT laundered)
//!
//! When the SWGL frame's digest drives `present()`, **F3 (real pixels from a
//! confined renderer)** closes on the host. **F1** (binding the *scanned-out*
//! framebuffer to the digest) and **F2** (IOMMU/DMA-confining a display PD) are
//! NOT touched and NOT claimed — they are the named hardware-trust frontier
//! (`SERVO-ON-SEL4.md §3.3`). "The pixels are real" does not launder "the scan-out
//! is attested."
//!
//! # Module map
//!
//! - [`swgl_context`] — the [`SwglRenderingContext`](swgl_context::SwglRenderingContext)
//!   shim + the load-bearing "SWGL produces real RGBA8" test.
//! - [`compositor_seam`] — [`present_frame`](compositor_seam::present_frame): the
//!   render→hash→present→gate→blit step against the GENUINE compositor-PD.
//! - [`webview`] (feature `libservo`) — the real-`RenderingContext`-trait adapter
//!   over SWGL that a real `WebView` paints into.

pub mod swgl_context;

#[cfg(feature = "swgl-standalone")]
pub mod compositor_seam;

#[cfg(feature = "libservo")]
pub mod webview;

#[cfg(feature = "swgl-standalone")]
pub use swgl_context::{
    with_gl, ReadRect, RenderingContext, RgbaFrame, SwglRenderingContext, GL_LOCK,
};

#[cfg(feature = "swgl-standalone")]
pub use compositor_seam::{present_frame, FramePresentation};
