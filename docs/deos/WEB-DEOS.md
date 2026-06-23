# WEB DEOS — the full gpui cockpit, in the browser

Web deos is **the same cockpit as native, rendered in a browser tab**: the real
`gpui` element-tree renderer running on the `gpui_web` platform backend (wasm32
+ WebGPU canvas), driving the **same in-browser verified executor** the native
desktop drives. It is *not* a lesser "web skin" reimplementation of the UI — it
is one renderer, one model, two platforms (native windowing vs. a browser
canvas).

This document states the architecture, the per-app backend map, the build
story, and — honestly — what the first slice proves versus the distance to full
parity.

## The two planes

A deos surface is two planes that meet at the cockpit:

- **Presentation plane** — `gpui`. The element tree, layout, the resolved
  `Scene`, paint. Native paints it through `gpui_macos`/`gpui_linux`/
  `gpui_windows` (Metal/Vulkan/D3D). The web paints the *same* `Scene` through
  `gpui_web` → `gpui_wgpu`'s `WgpuRenderer` → WebGPU on an `HtmlCanvasElement`.
- **Data plane** — the embedded verified executor (`starbridge_v2::world::World`
  over `dregg_turn::TurnExecutor`). It already compiles to wasm and runs
  in-tab today (see `starbridge-v2/web/src/lib.rs`, the `WebImage` atlas skin):
  every `act` is a real cap-gated turn through the verified executor, no server.

The whole point of web deos is to put the **native presentation plane on the
web platform over the already-wasm data plane** — so the browser tab is the full
cockpit, not a JSON viewer of it.

### Why gpui-in-browser is real (not aspirational)

The gpui fork (`emberian/zed@407a6ff`) ships a complete web backend,
`gpui_web` (`crates/gpui_web`): a full `Platform` implementation —
`WebPlatform` / `WebDispatcher` / `WebDisplay` / `WebWindow` plus events,
keyboard, and an HTTP client over `fetch`. `WebWindow::new` creates a
`<canvas>`, appends it to the document body, and binds a
`gpui_wgpu::WgpuRenderer` to it (`WgpuRenderer::new_from_canvas`); `WebPlatform::run`
asynchronously initializes the WebGPU context (`WgpuContext::new_web()`), then
runs the gpui app loop via `wasm_bindgen_futures::spawn_local`.

The boot path is *identical in shape* to native — only the platform constructor
differs:

```rust
// native (starbridge-v2/src/main.rs::run_window):
gpui_platform::application().run(|cx| { cx.open_window(opts, |_, cx| cx.new(...)) });

// web (starbridge-v2/web/src/cockpit_web.rs::boot_cockpit):
gpui_platform::web_init();
gpui_platform::single_threaded_web().run(|cx| { cx.open_window(opts, |_, cx| cx.new(...)) });
```

`gpui_platform` is the abstraction seam: `current_platform()` selects
`MacPlatform`/`WindowsPlatform`/`gpui_linux` on native and
`gpui_web::WebPlatform` under `cfg(target_family = "wasm")`. So the cockpit's
`Render` impls — pure `div().child(...)` element trees — are platform-agnostic
and run unchanged on either.

## The first slice (this change)

`starbridge-v2/web/src/cockpit_web.rs` (gated `cfg(all(wasm32, feature =
"gpui-web"))`) is a **real gpui `Render` entity** — `CockpitWeb` — booted on
`gpui_web`, driving the live `World`:

- A three-column cockpit slice (cell roster · inspector · affordances + receipt
  log), the same left-rail/center/right shape as the native cockpit, built from
  `div()` element trees — the genuine gpui renderer, not HTML.
- It reads the live image through the **same** lib surfaces the native cockpit
  uses: `reflect::reflect_cell`, `InspectAct::build`, `inspect_act::send`. A
  click on an affordance fires a **real cap-gated turn through the verified
  executor in-tab** and shows the receipt (`computrons_used`, `action_count`)
  or the in-band refusal.
- The wasm entrypoint `boot_cockpit()` (wasm-bindgen) seeds `world::demo_world`
  (the same image the native cockpit + atlas use), boots a single-threaded web
  gpui app, opens a window (creating the WebGPU canvas), and mounts the view.

**What it proves:** the gpui presentation plane renders to a browser canvas over
the in-browser verified data plane — the load-bearing path for web deos. It is a
genuine slice of the cockpit (HOME survey + inspector + act), not a separate
HTML page.

**What it is not (yet):** it is not the full `cockpit::Cockpit` (28 surfaces,
the dock/pane engine, the gpui-component widget set). See "Distance to full
parity" below — the blocker is architectural (module placement + a few
native-only widget/resource deps), not a question of whether gpui runs on the
web. It does.

## The build story

```
cd starbridge-v2/web
cargo build --target wasm32-unknown-unknown -p starbridge-web --features gpui-web
# then bundle:  wasm-bindgen / wasm-pack / trunk  (the existing atlas skin uses wasm-pack)
```

The default build (`cargo build --target wasm32-unknown-unknown -p
starbridge-web`, no features) is unchanged — it produces the gpui-free `WebImage`
atlas skin. `gpui-web` is **purely additive**: it turns on a new
`starbridge-v2/gpui-web` feature (gpui + gpui_platform, NO native sub-features)
plus the gpui crates in the web crate, and compiles in `cockpit_web`.

### The minimal feature set (what's ON / what's deliberately OFF)

The cockpit's `native-full` feature drags three native-only resource holdouts.
The new `gpui-web` feature path turns them **off**:

| Feature | native-full | gpui-web (wasm) | why |
| --- | --- | --- | --- |
| `embedded-executor` | on | **on** | the data plane — already wasm-clean (proven by the atlas skin) |
| `gpui` + `gpui_platform` | on (native platform) | **on (gpui_web)** | the presentation plane; `gpui_platform` forwards to `gpui_web` on wasm32 |
| `gpui_platform/{runtime_shaders,x11,wayland}` | on | **off** | macOS Metal / Linux X11+Wayland windowing — inert on wasm, kept out for clarity |
| `web-shell` (servo/libservo) | on | **off** | servo is native-only (C++ swgl / mozjs) — the one app with no in-browser-gpui path |
| `dev-surfaces` (deos-zed editor + deos-terminal) | on | **off** | alacritty PTY + `RealFs` are native resources (the *gpui UI* of these CAN run on web; the *backend* needs a wire — see app map) |
| `render-capture` (gpui `test-support` offscreen wgpu) | on | **off** | the native headless bake; the browser paints to a live canvas, no offscreen capture |
| `live-node` (reqwest blocking) | on | **off** | reqwest's blocking client is native; a web live-node uses `fetch`/WebSocket (future) |

So the wasm cockpit feature set is exactly: **cockpit gpui UI + embedded
executor + gpui_web**, with web-shell / dev-surfaces / render-capture / live-node
off. The data plane was already fine on wasm; `gpui_web` swaps in for the native
gpui platform; the holdouts are the native-resource backends, each addressed in
the app map below.

## Per-app backend map (the node as the web backend)

Each deos app is **gpui UI (renders in-browser today)** + a **backend wire**.
The UI half is platform-agnostic gpui and runs on `gpui_web`; the backend half
is where a native resource lives, and the web build wires it to `node/` (over
HTTP/WebSocket) or to the in-browser executor.

| App | gpui UI in-browser | Backend wire needed for web |
| --- | --- | --- |
| **Cockpit / inspectors** | ✅ today (this slice: home/inspector/affordances; the full surface set is element-tree work) | none — drives the in-browser `World` directly |
| **Terminal** (`deos_terminal::TerminalView`) | gpui grid renders on web; alacritty's PTY does not exist in a browser | PTY over a **WebSocket to `node/`** — the terminal grid stays gpui, the shell process runs node-side and streams bytes back |
| **Editor** (`deos_zed::Editor`) | gpui editor renders on web | swap `RealFs::arc()` for a **firmament-backed `Arc<dyn Fs>`** over the in-browser executor (the editor already takes `Arc<dyn Fs>` — see `editor_surface.rs`), or an `Fs` over `node/`'s file API |
| **Chat** (`deos_matrix::chat::ChatView`) | gpui chat renders on web | `matrix-rust-sdk` (`matrix-sdk 0.18`) **wasm-compiles** (it targets wasm32 with a `fetch`/IndexedDB stack); the headless `deos-matrix` core compiles to wasm and the gpui `ChatView` paints it — the cleanest fully-in-tab app after the cockpit |
| **Web-shell** (servo / libservo) | ❌ native-only | servo is a native C++/mozjs engine; there is no in-browser servo. The browser tab already *is* a web engine, so a web-deos "web-shell" surface would be a sandboxed `<iframe>`/native browsing context behind the net-cap gate, not gpui-rendered servo. This is the one app with no gpui-on-web path. |

So three of the four self-hosting apps (terminal, editor, chat) keep their gpui
UI on `gpui_web` and differ only in **where the backend resource lives** — a
node websocket (terminal), an `Fs` impl (editor), or a wasm-native SDK (chat).
Servo is the lone native-only holdout.

## Distance to full parity (honest)

The first slice renders a real cockpit slice. The gap to the *full*
`cockpit::Cockpit` in-browser is **architectural, not foundational**:

1. **`cockpit::Cockpit` is binary-private.** It lives in
   `starbridge-v2/src/main.rs` as `mod cockpit` (gated `gpui-ui`), not in the
   library, so a separate `cdylib` (the `web/` crate) cannot reach it. To render
   the *actual* `Cockpit` on web, the cockpit module (and `login`, `views`) must
   move into the library behind a gpui-gated `pub mod`, OR a wasm `cdylib`
   entrypoint must be added to the `starbridge-v2` crate itself. Either is a
   module-placement change; neither changes cockpit internals. (This slice
   deliberately did not touch the cockpit `.rs` files.)
2. **gpui-component on wasm.** The full cockpit uses `gpui-component` (text
   `Input`, `Button`, the shadcn-style widget set). The first slice uses plain
   gpui (`div()` trees) to avoid pulling that crate's dep tree onto wasm before
   it is checked. gpui-component is gpui-native UI, so it *should* build to
   wasm; the open task is to compile it for wasm32 (verify no tree-sitter /
   native-font / clipboard-native leaf is force-pulled) and call
   `gpui_component::init(cx)` at web boot exactly as native does.
3. **The native-resource backends** (terminal PTY, editor Fs, web-shell servo) —
   each needs its wire per the app map. The UI for terminal/editor/chat is
   already gpui and web-ready; the backends are the work.

None of these is "can gpui run in the browser" — that is settled (`gpui_web` is
a complete platform and this slice boots on it). The remaining work is **lift the
cockpit module to lib-reachable**, **wasm-check gpui-component**, and **wire the
three native-resource backends** (websocket / Fs / wasm-SDK), with servo noted
as the single native-only surface.

## Files

- `starbridge-v2/web/src/cockpit_web.rs` — the first-slice gpui cockpit view +
  the `boot_cockpit` wasm entrypoint.
- `starbridge-v2/web/src/lib.rs` — declares `cockpit_web` (gated) alongside the
  existing `WebImage` atlas skin.
- `starbridge-v2/web/Cargo.toml` — the `gpui-web` feature (additive; pulls gpui +
  gpui_platform + `starbridge-v2/gpui-web`).
- `starbridge-v2/Cargo.toml` — the `gpui-web` feature on the main crate (gpui +
  gpui_platform without native sub-features; web-shell/dev-surfaces/
  render-capture/live-node off).
- `starbridge-v2/web/cockpit_gpui.html` — boots the wasm bundle and calls
  `boot_cockpit()`.
