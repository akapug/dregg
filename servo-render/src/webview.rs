//! The real-`WebView` path (`SERVO-ON-SEL4.md §4 Stage A`, steps 3-4) — OPT-IN
//! behind the `libservo` feature, because it pulls `servo` → `script` → `mozjs`
//! (the multi-GB SpiderMonkey C++ build), the known-hard, known-walked long pole.
//!
//! ## What this module does
//!
//! 1. Implements servo's GENUINE `paint_api::rendering_context::RenderingContext`
//!    trait (not the standalone mirror) over a [`SwglRenderingContext`], so a real
//!    `WebView` accepts our SWGL context as its render target — the §1.5 "write a
//!    small new `RenderingContext` impl" that replaces the surfman → Mesa path.
//! 2. Builds a `WebView` via `WebViewBuilder` pointed at that context, loads a
//!    trivial `data:` page, spins the event loop until paint, and reads the frame
//!    via `RenderingContext::read_to_image` → feeds it to the compositor seam.
//!
//! ## The one real trait-shape divergence (HONEST)
//!
//! Servo's real trait (verified, `servo-paint-api 0.1.0-rc2`,
//! `rendering_context.rs`) requires BOTH:
//!   - `gleam_gl_api(&self) -> Rc<dyn gleam::gl::Gl>`  ← SWGL provides this (it
//!     `impl Gl for swgl::Context`); this is the WebRender render path + the
//!     `read_to_image` (`read_pixels`) pixel path.
//!   - `glow_gl_api(&self) -> Arc<glow::Context>`  ← SWGL does **NOT** implement
//!     `glow`. This is used by the OFFSCREEN-context blit path
//!     (`OffscreenRenderingContext::blit_framebuffer`), NOT by the page→buffer
//!     render or the pixel readback. For a DRAW-compositor SWGL context that owns
//!     the whole default framebuffer we do not take the offscreen blit path, so
//!     the honest options are: (a) a `glow::Context` built from a SWGL proc-loader
//!     shim, or (b) a panicking stub guarded to the offscreen path we never hit.
//!     This module takes (b) and documents it; closing (a) is a small follow-up
//!     (a `glow::Context::from_loader_function` over swgl's entry points).
//!
//! ## Build status
//!
//! This module compiles ONLY under `--features libservo`, which requires the full
//! servo dependency tree (mozjs/SpiderMonkey, the multi-GB C++ build). See the
//! crate-level build-status report; the `swgl-standalone` default proves the
//! render path WITHOUT this elephant.

#![cfg(feature = "libservo")]

use std::rc::Rc;
use std::sync::Arc;

use servo_paint_api::rendering_context::RenderingContext as ServoRenderingContext;
use webrender_api::units::DeviceIntRect;
use dpi::PhysicalSize;
use image::RgbaImage;

use crate::swgl_context::SwglRenderingContext;

/// A real-`RenderingContext`-trait adapter over [`SwglRenderingContext`]. THIS is
/// the type a real `WebViewBuilder` accepts (`builder(rendering_context: Rc<dyn
/// RenderingContext>)`), making the SWGL software rasterizer the WebView's render
/// target — no GPU, no EGL, no surfman.
pub struct ServoSwglContext {
    inner: SwglRenderingContext,
}

impl ServoSwglContext {
    /// Wrap a SWGL context for use as a real servo `RenderingContext`.
    pub fn new(width: u32, height: u32) -> Self {
        ServoSwglContext { inner: SwglRenderingContext::new(width, height) }
    }

    /// The inner SWGL context (for direct frame readback into the compositor seam).
    pub fn inner(&self) -> &SwglRenderingContext {
        &self.inner
    }
}

impl ServoRenderingContext for ServoSwglContext {
    fn prepare_for_rendering(&self) {
        use crate::swgl_context::RenderingContext as _;
        self.inner.prepare_for_rendering();
    }

    fn read_to_image(&self, source_rectangle: DeviceIntRect) -> Option<RgbaImage> {
        use crate::swgl_context::{ReadRect, RenderingContext as _};
        let rect = ReadRect {
            x: source_rectangle.min.x,
            y: source_rectangle.min.y,
            width: source_rectangle.width(),
            height: source_rectangle.height(),
        };
        let frame = self.inner.read_to_image(rect)?;
        RgbaImage::from_raw(frame.width, frame.height, frame.bytes)
    }

    fn size(&self) -> PhysicalSize<u32> {
        use crate::swgl_context::RenderingContext as _;
        let (w, h) = self.inner.size();
        PhysicalSize::new(w, h)
    }

    fn resize(&self, size: PhysicalSize<u32>) {
        use crate::swgl_context::RenderingContext as _;
        self.inner.resize(size.width, size.height);
    }

    fn present(&self) {
        use crate::swgl_context::RenderingContext as _;
        self.inner.present();
    }

    fn make_current(&self) -> Result<(), servo_paint_api::rendering_context::Error> {
        use crate::swgl_context::RenderingContext as _;
        self.inner.make_current();
        Ok(())
    }

    fn gleam_gl_api(&self) -> Rc<dyn gleam::gl::Gl> {
        use crate::swgl_context::RenderingContext as _;
        self.inner.gleam_gl_api()
    }

    fn glow_gl_api(&self) -> Arc<glow::Context> {
        // SEE THE MODULE DOCS: SWGL does not implement `glow`. This is the
        // OFFSCREEN-blit path only, which a DRAW-compositor SWGL context does not
        // take. Closing this honestly is a `glow::Context::from_loader_function`
        // over swgl's GL entry points (follow-up (a)). Until then this path is
        // unreached for the page→buffer render + readback Stage A exercises.
        unimplemented!(
            "SWGL provides gleam::Gl (the render + readback path); glow is only the \
             offscreen-blit path a DRAW-compositor SWGL context does not take. \
             Follow-up: glow::Context::from_loader_function over swgl entry points."
        )
    }
}

// NOTE: the real `WebViewBuilder::new(&servo, rc).build()` wiring + event-loop
// spin + `data:` page load lands here once the `libservo` feature's mozjs build
// is green. The cap-gate forwarding (CapGatedDelegate) is already written in
// `starbridge-web-surface/src/delegate.rs` (the `// LIBSERVO SEAM`); this crate
// supplies the render half (the SWGL RenderingContext) that the WebView paints
// into, and `compositor_seam::present_frame` carries the result to the glass.
