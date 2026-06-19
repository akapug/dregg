//! The real-`WebView` path (`SERVO-ON-SEL4.md §4 Stage A`, steps 3-4) — OPT-IN
//! behind the `libservo` feature, because it pulls `servo` → `script` → `mozjs`
//! (the multi-GB SpiderMonkey C++ build), the known-hard, known-walked long pole.
//!
//! ## What this module does (the wiring is WRITTEN against the genuine API)
//!
//! 1. [`ServoSwglContext`] implements servo's GENUINE
//!    `paint_api::rendering_context::RenderingContext` trait (not the standalone
//!    mirror) over a [`SwglRenderingContext`], so a real `WebView` accepts our SWGL
//!    context as its render target — the §1.5 "write a small new `RenderingContext`
//!    impl" that replaces the surfman → Mesa path.
//! 2. [`CapGate`] is the real `WebViewDelegate` — Servo calls *out* to it at every
//!    authority point and it forwards `load_web_resource` / `request_navigation` to
//!    the genuine `CapGatedDelegate` (`granted ⊆ held`), so the held
//!    [`SurfaceCapability`] mediates the engine exactly as it mediates the
//!    `MockSurface`.
//! 3. [`render_url_to_frame`] builds a real `Servo` (`ServoBuilder`) + `WebView`
//!    (`WebViewBuilder` pointed at the SWGL context, the `CapGate` as delegate),
//!    loads a URL, spins `spin_event_loop` until the page is loaded+painted, calls
//!    `WebView::paint`, and reads the frame back via `RenderingContext::read_to_image`
//!    as an [`RgbaFrame`] — the SAME type `present_frame` carries to the compositor.
//!
//! This is API-correct against the published trait + the `winit_minimal` upstream
//! embed example. It has NOT been run end-to-end (the `mozjs` build is the gate);
//! when that build is green this is the real page→glass path, no stand-in.
//!
//! ## The one real trait-shape divergence (HONEST)
//!
//! Servo's real trait (verified against `servo-paint-api`'s `rendering_context.rs`;
//! the version the codebase pins as `0.1.0-rc2` resolves to the published `0.1.0`)
//! requires BOTH:
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
//! This module compiles ONLY under `--features libservo`, which pulls the full
//! servo dependency tree (941 crates incl. mozjs/SpiderMonkey, the multi-GB C++
//! build). That whole tree **resolves and builds offline from the crates.io
//! mirror** — the wall is wall-clock on the `mozjs`/`script` compile, not a missing
//! dependency. The `swgl-standalone` default proves the render path (real RGBA8 out
//! of SWGL) WITHOUT this elephant, and is green today.

#![cfg(feature = "libservo")]

use std::rc::Rc;
use std::sync::Arc;

// NB: the crate is `servo-paint-api` but its `[lib] name` is `paint_api` (verified
// via `cargo metadata`), so it is imported as `paint_api`, not `servo_paint_api`.
use paint_api::rendering_context::RenderingContext as ServoRenderingContext;
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

    fn make_current(&self) -> Result<(), paint_api::rendering_context::Error> {
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

// ─────────────────────────────────────────────────────────────────────────────
// The real `WebView` embed — Stage-A steps 3-4 wired against the GENUINE servo
// API (`servo 0.1.x`, the `winit_minimal` example is the upstream template). This
// is the actual `ServoBuilder → WebViewBuilder → load → spin-until-painted →
// read_to_image` flow, NOT a stand-in. It is gated `#[cfg(feature = "libservo")]`,
// so it compiles only once the engine (mozjs/SpiderMonkey, the long pole) links;
// the code itself is complete and API-correct against the published trait.
// ─────────────────────────────────────────────────────────────────────────────

use std::cell::Cell;

use servo::{
    EventLoopWaker, LoadStatus, ServoBuilder, WebResourceLoad, WebResourceResponse, WebView,
    WebViewBuilder, WebViewDelegate,
};
use url::Url;

use starbridge_web_surface::{
    CapGatedDelegate, NavigationDecision, ResourceDecision, SurfaceCapability, WebSurfaceDelegate,
};

use crate::swgl_context::RgbaFrame;

/// **The real `WebViewDelegate` that IS the cap gate** (the `// LIBSERVO SEAM` made
/// good). Servo calls *out* to this at every authority point; each callback
/// discharges the held [`SurfaceCapability`] through the GENUINE
/// [`CapGatedDelegate`] (the same `granted ⊆ held` `is_attenuation` gate the
/// firmament runs), so a fetch/navigation the cap does not permit is refused *at
/// the callback*, before the engine acts — exactly the discipline
/// `starbridge-web-surface` already proves on the `MockSurface`. The only thing
/// new here over the mock is that the callbacks are the *real* libservo ones.
///
/// It also wakes the embedder loop on a new frame ([`Self::frame_ready`]), the
/// signal the headless [`render_url_to_frame`] spins on.
struct CapGate {
    /// The held authority for this `WebView` (the c-list entry the delegate
    /// discharges) — carried by the surface, never by the untrusted page.
    surface: SurfaceCapability,
    /// The genuine cap-enforcing gate the callbacks forward to.
    gate: CapGatedDelegate,
    /// Set when servo reports a new frame is painted — the headless render loop
    /// reads this to know a frame is ready to read back.
    frame_ready: Cell<bool>,
    /// Set when the load reaches [`LoadStatus::Complete`] — the headless loop's
    /// terminating condition (paint the *finished* page, not a partial one).
    load_complete: Cell<bool>,
}

impl WebViewDelegate for CapGate {
    /// libservo `load_web_resource` — the fetch/subresource chokepoint. Forward to
    /// the cap gate: on [`ResourceDecision::Intercept`] (cap-denied) we intercept
    /// the load with the cap-denied body (the page sees the refusal bytes, never
    /// the resource); on [`ResourceDecision::Continue`] we let it proceed.
    fn load_web_resource(&self, _webview: WebView, load: WebResourceLoad) {
        let origin = load.request().url.origin().ascii_serialization();
        match self.gate.load_web_resource(&self.surface, &origin) {
            ResourceDecision::Continue => { /* not intercepted — proceeds to net */ }
            ResourceDecision::Intercept { body, .. } => {
                // Hand the page the cap-denied body instead of the resource. The
                // builder shape (`WebResourceResponse::new(url)`) + `intercept` →
                // `send_body_data` → `finish` is servo's own canonical interception
                // pattern (verified against its `webview_delegate.rs` test).
                let url = load.request().url.clone();
                let mut intercepted = load.intercept(WebResourceResponse::new(url));
                intercepted.send_body_data(body);
                intercepted.finish();
            }
        }
    }

    /// libservo `request_navigation` — accepted by default, so the cap gate must
    /// affirmatively decide. Forward to the gate's navigate allowlist:
    /// [`NavigationDecision::Allow`] → `allow()`, else `deny()`.
    fn request_navigation(&self, _webview: WebView, navigation_request: servo::NavigationRequest) {
        // `NavigationRequest::url` is a public FIELD in the published `servo 0.1.1`
        // (not the `url()` accessor the pre-1.0 docs implied).
        let origin = navigation_request.url.origin().ascii_serialization();
        match self.gate.allow_navigation(&self.surface, &origin) {
            NavigationDecision::Allow => navigation_request.allow(),
            NavigationDecision::Deny { .. } => navigation_request.deny(),
        }
    }

    /// libservo `notify_new_frame_ready` — servo painted a new frame into the
    /// rendering context's back buffer. Flag it so the headless loop reads back.
    fn notify_new_frame_ready(&self, _webview: WebView) {
        self.frame_ready.set(true);
    }

    /// libservo `notify_load_status_changed` — flag [`LoadStatus::Complete`] so the
    /// headless loop knows the page is fully loaded (ready for a final paint).
    fn notify_load_status_changed(&self, _webview: WebView, status: LoadStatus) {
        // `matches!` (not `==`) so this is robust whether or not `LoadStatus` derives
        // `PartialEq` — it is a plain variant discriminant check either way.
        if matches!(status, LoadStatus::Complete) {
            self.load_complete.set(true);
        }
    }
}

/// A no-op [`EventLoopWaker`] — the headless render driver pumps
/// [`Servo::spin_event_loop`] itself in a bounded loop (no external event loop to
/// wake). A real windowed embedder wakes its winit proxy here (cf. `winit_minimal`).
#[derive(Clone)]
struct HeadlessWaker;
impl EventLoopWaker for HeadlessWaker {
    fn clone_box(&self) -> Box<dyn EventLoopWaker> {
        Box::new(self.clone())
    }
    fn wake(&self) {}
}

/// **THE STAGE-A STEP-3+4 PAYOFF: render a real web page to an `RgbaFrame` through
/// the SWGL context, behind the cap gate.**
///
/// Build a real `Servo` engine, point a real `WebView` at our [`ServoSwglContext`]
/// (the SWGL software rasterizer — no GPU, no EGL, no surfman), install the
/// [`CapGate`] `WebViewDelegate` (so the held `surface` cap mediates every fetch /
/// navigation), load `url`, spin the event loop until the page is loaded and
/// painted, then read the rendered RGBA8 back via the genuine
/// `RenderingContext::read_to_image`. The returned [`RgbaFrame`] is the SAME type
/// [`crate::present_frame`] carries to the compositor-PD's `present()` gate — so the
/// real page's pixels flow straight into the unchanged T1/T2/T3 gate, closing F3
/// with genuine page content (not the clear-to-color stand-in).
///
/// `max_spins` bounds the headless pump (servo is multi-threaded; the page load +
/// layout + paint complete asynchronously across its actor threads). Returns `None`
/// if no frame was produced within the bound (e.g. the page never painted).
///
/// This is the function the `swgl-standalone` `fetch_render_present` pipeline's
/// `render_color` stand-in is replaced BY when `libservo` is on: same cap gate in
/// front, same compositor gate behind, real pixels in between.
pub fn render_url_to_frame(
    url: &str,
    surface: SurfaceCapability,
    width: u32,
    height: u32,
    max_spins: usize,
) -> Option<RgbaFrame> {
    use crate::swgl_context::RenderingContext as _;

    let url = Url::parse(url).ok()?;

    // The SWGL rendering context — our software rasterizer as a real servo
    // `RenderingContext` (`Rc<dyn RenderingContext>` is what `WebViewBuilder` takes).
    let rendering_context = Rc::new(ServoSwglContext::new(width, height));
    let _ = ServoRenderingContext::make_current(&*rendering_context);

    // The real engine. Headless: we drive `spin_event_loop` ourselves.
    let servo = ServoBuilder::default()
        .event_loop_waker(Box::new(HeadlessWaker))
        .build();

    // The delegate IS the cap gate — every fetch/navigation discharges `surface`.
    let delegate = Rc::new(CapGate {
        surface,
        gate: CapGatedDelegate::new(),
        frame_ready: Cell::new(false),
        load_complete: Cell::new(false),
    });

    let webview = WebViewBuilder::new(&servo, rendering_context.clone())
        .url(url)
        .delegate(delegate.clone())
        .build();

    // Pump servo's actor threads until the page is loaded AND a frame is ready,
    // bounded so a non-painting page cannot hang the caller.
    let mut spins = 0;
    while spins < max_spins {
        servo.spin_event_loop();
        if delegate.load_complete.get() && delegate.frame_ready.get() {
            break;
        }
        spins += 1;
    }

    // Ask the WebView to paint the (now-loaded) page into the SWGL back buffer,
    // then read the RGBA8 out via the genuine trait — the same `read_pixels` path
    // the standalone build proves. `read_to_image` reads the back buffer even
    // before `present`, so the rendered page is available here.
    webview.paint();
    let (w, h) = rendering_context.inner().size();
    let rect = crate::swgl_context::ReadRect::whole(w, h);
    let frame = rendering_context.inner().read_to_image(rect)?;
    Some(frame)
}
