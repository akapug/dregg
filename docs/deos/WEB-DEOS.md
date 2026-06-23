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
gpui_platform::application().run(|cx| {
    gpui_component::init(cx);
    cx.open_window(opts, |window, cx| cx.new(|cx| Cockpit::with_node(world, anchors, focus, None, seed)))
});

// web (starbridge-v2/web/src/cockpit_web.rs::boot_cockpit):
gpui_platform::web_init();
gpui_platform::single_threaded_web().run(|cx| {
    gpui_component::init(cx);
    cx.open_window(opts, |window, cx| cx.new(|cx| Cockpit::with_node(world, anchors, focus, None, seed)))
});
```

The two booters now construct the **same** `starbridge_v2::cockpit::Cockpit` over the **same** `World` — the only difference is the platform constructor and that the web boot opens the cockpit directly (the native boot front-doors through the login surface first).

`gpui_platform` is the abstraction seam: `current_platform()` selects
`MacPlatform`/`WindowsPlatform`/`gpui_linux` on native and
`gpui_web::WebPlatform` under `cfg(target_family = "wasm")`. So the cockpit's
`Render` impls — pure `div().child(...)` element trees — are platform-agnostic
and run unchanged on either.

## The full cockpit (this change)

`starbridge-v2/web/src/cockpit_web.rs` (gated `cfg(all(wasm32, feature =
"gpui-web"))`) boots the **REAL** `starbridge_v2::cockpit::Cockpit` — the same
comprehensive master interface the native desktop opens — on `gpui_web`, driving
the live in-browser `World`:

- The full cockpit element tree: the dock + the surface set + the
  **gpui-component widget library** (the text `Input`/`Button`/list set), not a
  reduced web-only view and not the JSON/atlas skin. It is the exact same
  `Cockpit::with_node(world, anchors, focus, None, seed)` the native `run_window`
  constructs (`node_url = None`, the data plane is the in-tab executor; the demo
  `seed` fills the image in live off the first-paint path).
- It drives the live image through the embedded executor: every affordance click
  is a **real cap-gated turn through the verified executor in-tab** (the
  `World::commit_turn` seam), with the post-state re-reflected on the next frame —
  the same mechanism as native.
- The wasm entrypoint `boot_cockpit()` (wasm-bindgen) seeds `world::demo_genesis`
  (the at-rest genesis image + the deferred demo seed, the same the native cockpit
  boots), boots a single-threaded web gpui app, registers the cockpit fonts
  (Lilex + IBM Plex) and calls `gpui_component::init(cx)` (the widget globals —
  exactly as native boot does), opens a window (creating the WebGPU canvas), and
  mounts the cockpit.

**What it proves:** the full gpui presentation plane — dock, surfaces,
gpui-component widgets and all — renders to a browser canvas over the in-browser
verified data plane. One renderer, one cockpit, two platforms.

### The module lift (what made it reachable)

`cockpit`, `views` (and the `dock` engine they reach) were binary-private `mod`s
in `starbridge-v2/src/main.rs` — a separate cdylib (the `web/` crate) could not
name `cockpit::Cockpit`. They now live in the **library** behind a gpui-gated
`pub mod` (`#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))] pub mod
cockpit;` in `src/lib.rs`). This is a pure module-placement change — no cockpit
internal logic moved. Three supporting moves:

- `extern crate self as starbridge_v2;` in `lib.rs` (gpui-gated) so the cockpit's
  many `starbridge_v2::dock` / `starbridge_v2::world` / … self-references resolve
  unchanged now that they live *inside* the crate that used to be their dependency.
- `main.rs` reaches the lifted modules through `use starbridge_v2::{cockpit,
  login};`, leaving every `cockpit::Cockpit` / `login::LoginSurface` path in the
  bin untouched.
- `replay::replay_panel` (a gpui element the cockpit places) was gated on
  `gpui-ui` ALONE; widened to the union gate so the web build sees it too.

`login` is the one lifted module gated `gpui-ui`-ONLY (native), not the union: it
drives the DURABLE-session-image path (`session::{open_session_world,
session_base_dir}` + `LoginManager::logout_durable`, all `cfg(not(wasm32))`
filesystem code). The web boot mounts `Cockpit` directly — the in-tab image is
ephemeral — so it never needs the login front door. (If a web login front door is
wanted later, its ceremony minus the durable-image persistence wasm-compiles; the
gate would widen then.)

The native build is unaffected (`cargo check --features native-full` green; the
cockpit/views/dock gate is the union `any(gpui-ui, gpui-web)`, native-full enables
`gpui-ui`).

## The build story

```
cd starbridge-v2/web
cargo build --target wasm32-unknown-unknown -p starbridge-web --features gpui-web
# then bundle:  wasm-bindgen / wasm-pack / trunk  (the existing atlas skin uses wasm-pack)
```

The default build (`cargo build --target wasm32-unknown-unknown -p
starbridge-web`, no features) is unchanged — it produces the gpui-free `WebImage`
atlas skin. `gpui-web` is **purely additive**: it turns on a new
`starbridge-v2/gpui-web` feature (gpui + gpui_platform + gpui-component, NO native
sub-features) plus the gpui crates in the web crate, and compiles in `cockpit_web`.

**Verified.** The `gpui-web` build is GREEN (`Finished dev profile`): the full
`starbridge-v2` lib (the lifted cockpit + gpui-component widget tree) AND the
`starbridge-web` cdylib (the `boot_cockpit` mount of the real `Cockpit`) both
compile to `wasm32-unknown-unknown`. The debug artifact is large (debuginfo-
dominated, ~1.1G raw / ~86M with debuginfo stripped); the shippable size is the
release build through `wasm-opt` (the gpui-free skin's release wasm is ~9M — the
gpui cockpit's release+opt figure lands in that order of magnitude once bundled).
gpui-component compiles with `default-features = false` (its tree-sitter syntax
grammars are all opt-in features, none enabled) — no native font/clipboard/
tree-sitter leaf force-pulls onto the wasm path.

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

The full `cockpit::Cockpit` now renders in-browser. Two of the three former
blockers are CLOSED; the remaining gap is the native-resource backends:

1. **`cockpit::Cockpit` is binary-private.** ✅ CLOSED. `cockpit`/`login`/`views`
   were lifted from `main.rs` into the library behind a gpui-gated `pub mod`
   (the union gate `any(gpui-ui, gpui-web)`), with `extern crate self as
   starbridge_v2` so their self-references resolve unchanged. No cockpit
   internals moved. The `web/` cdylib now names `Cockpit` directly.
2. **gpui-component on wasm.** ✅ COMPILES. The vendored `gpui-component` (text
   `Input`, `Button`, the shadcn-style set) builds to `wasm32-unknown-unknown`
   with `default-features = false` (its tree-sitter syntax grammars are all
   opt-in features, none enabled). `gpui_component::init(cx)` is called at web
   boot exactly as native does.
3. **The native-resource backends** (terminal PTY, editor Fs, web-shell servo) —
   each needs its wire per the app map. These surfaces are feature-gated OFF the
   web build (`dev-surfaces`/`web-shell` are not in the `gpui-web` feature), so
   the cockpit shell + its in-browser surfaces render; the dev-loop surfaces
   that need a native resource are dark until their backend is wired. The UI for
   terminal/editor/chat is already gpui and web-ready; the backends are the work.

None of these is "can gpui run in the browser" — that is settled (`gpui_web` is a
complete platform and the full cockpit boots on it). The remaining work is
**wire the three native-resource backends** (websocket / Fs / wasm-SDK), with
servo noted as the single native-only surface.

## Files

- `starbridge-v2/web/src/cockpit_web.rs` — the `boot_cockpit` wasm entrypoint
  that mounts the REAL `starbridge_v2::cockpit::Cockpit` on `gpui_web`.
- `starbridge-v2/web/src/lib.rs` — declares `cockpit_web` (gated) alongside the
  existing `WebImage` atlas skin.
- `starbridge-v2/web/Cargo.toml` — the `gpui-web` feature (additive; pulls gpui +
  gpui_platform + gpui-component + web-sys + `starbridge-v2/gpui-web`).
- `starbridge-v2/Cargo.toml` — the `gpui-web` feature on the main crate (gpui +
  gpui_platform + gpui-component without native sub-features; web-shell/
  dev-surfaces/render-capture/live-node off).
- `starbridge-v2/src/lib.rs` — the lifted `pub mod cockpit; pub mod login; pub
  mod views;` (+ `dock`), gpui-gated `any(gpui-ui, gpui-web)`, and `extern crate
  self as starbridge_v2`.
- `starbridge-v2/src/main.rs` — `use starbridge_v2::{cockpit, login};` (the bin
  reaches the now-lib modules).
- `starbridge-v2/web/cockpit_gpui.html` — boots the wasm bundle and calls
  `boot_cockpit()`.
