//! THE FULL GPUI COCKPIT, IN THE BROWSER.
//!
//! This boots the REAL `starbridge_v2::cockpit::Cockpit` — the same comprehensive
//! master interface the native desktop opens (the dock, the surface set, the
//! gpui-component widgets) — on the `gpui_web` backend (wasm32 + WebGPU canvas,
//! via `gpui_platform`'s wasm forwarding), driving the SAME in-browser verified
//! executor (`starbridge_v2::world::World`) the native cockpit drives. It is NOT a
//! reduced web-only view and NOT the JSON/atlas skin (`lib.rs`): one renderer, one
//! cockpit, two platforms.
//!
//! The boot path is identical in SHAPE to native `run_window` — only the platform
//! constructor differs (`single_threaded_web()` vs `application()`):
//!
//!   1. `gpui_platform::web_init()` — install the wasm panic/log hooks.
//!   2. `single_threaded_web().run(|cx| { … })` — the gpui app on `gpui_web`.
//!   3. register the cockpit fonts (Lilex + IBM Plex), then `gpui_component::init(cx)`
//!      (the widget library's global state — the cockpit's `Input`/`Button` panic
//!      without it), exactly as native boot does.
//!   4. `cx.open_window(...)` — on wasm this creates the `<canvas>`, appends it to
//!      the document body, and binds the `WgpuRenderer` (WebGPU) to it.
//!   5. mount `Cockpit::with_node(world, anchors, focus, None, None)` — the real
//!      cockpit over the live `World`; `focus_on_open` arms keyboard focus.
//!
//! See docs/deos/WEB-DEOS.md.

#![cfg(all(target_arch = "wasm32", feature = "gpui-web"))]

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{px, size, App, AppContext, Bounds, WindowBounds, WindowOptions};
use wasm_bindgen::prelude::*;

use starbridge_v2::cockpit::Cockpit;
use starbridge_v2::world;

/// THE WASM ENTRYPOINT — boot the FULL gpui cockpit in the browser.
///
/// Called from JS (after `init()`): seeds a fresh sovereign genesis image
/// (`world::demo_genesis`, the same the native cockpit boots — the four genesis
/// cells, the five demo seed turns deferred so they fill in live off the paint
/// path), boots a single-threaded web gpui application, registers the cockpit
/// fonts + the gpui-component widget globals, opens a window (which creates the
/// WebGPU canvas + appends it to the document body), and mounts the real
/// `Cockpit`. The gpui run-loop drives paints/events thereafter — every
/// affordance click is a real cap-gated turn through the verified executor in-tab.
#[wasm_bindgen]
pub fn boot_cockpit() {
    gpui_platform::web_init();

    // The genesis (at-rest) image + the deferred demo seed — exactly the native
    // `run_window` shape. `with_node` takes the seed so the cockpit seeds it in
    // LIVE (cells appear as each turn commits) off the first-paint path.
    let (world, anchors, seed) = world::demo_genesis();
    let shared = Rc::new(RefCell::new(world));

    gpui_platform::single_threaded_web().run(move |cx: &mut App| {
        // Register the cockpit's fonts. The web platform text system does not carry
        // "Lilex" (the cockpit's default) or "IBM Plex" — without them the styled
        // panels render with blank text (chrome lays out, no glyphs). Same fonts
        // the native boot + the headless bake register.
        static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
        static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");
        if let Err(e) = cx.text_system().add_fonts(vec![
            std::borrow::Cow::Borrowed(LILEX),
            std::borrow::Cow::Borrowed(IBM_PLEX),
        ]) {
            web_sys_warn(&format!("failed to register embedded UI fonts: {e}"));
        }

        // Initialize gpui-component — the real widget library (text `Input`,
        // `Button`, the shadcn-style set). This installs the theme + the global
        // state every widget reads; without it any gpui-component widget the
        // cockpit constructs panics on a missing global. One call at boot,
        // exactly as native `run_window` does.
        gpui_component::init(cx);

        let bounds = Bounds {
            origin: gpui::point(px(0.), px(0.)),
            size: size(px(1280.), px(820.)),
        };
        let mut seed = Some(seed);
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                ..Default::default()
            },
            move |window, cx| {
                let pending_seed = seed.take();
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    // The REAL cockpit over the in-browser `World`. `node_url = None`
                    // (no remote-federation panel on the web boot — the data plane is
                    // the in-tab executor); `pending_seed` lets it seed in live.
                    Cockpit::with_node(shared.clone(), anchors, focus, None, pending_seed)
                });
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                view
            },
        )
        .expect("failed to open web window");
    });
}

/// Surface a warning to the browser console (the web platform has no stderr).
fn web_sys_warn(msg: &str) {
    web_sys::console::warn_1(&JsValue::from_str(msg));
}
