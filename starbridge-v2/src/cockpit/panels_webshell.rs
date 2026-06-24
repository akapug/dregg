//! THE 🌐 WEB-SHELL BROWSER surface — a general `http(s)://` browser as a cockpit
//! tab, distinct from the `dregg://` web-of-cells browser ([`super::panels_web`]).
//!
//! ## What it is
//!
//! A real address bar + back / forward / reload navigation + a content tile that
//! renders a live web page. The pieces are all genuine:
//!
//!   * **URL bar** — a real gpui-component single-line text
//!     [`gpui_component::input::InputState`] (the URL bar gpui never had before this
//!     widget landed), submitting on `↵` via the
//!     [`InputEvent::PressEnter`](gpui_component::input::InputEvent) subscription.
//!   * **Navigation** — a [`Vec<String>`](Cockpit::webshell_history) history of
//!     visited URLs with a [`cursor`](Cockpit::webshell_cursor); back / forward /
//!     reload each RE-DRIVE the render of the URL at the new cursor (genuine
//!     re-fetch, not a relabel).
//!   * **The content tile** — `Go` calls
//!     [`servo_render::webview::render_url_to_frame`] (the real
//!     `ServoBuilder → WebViewBuilder → SWGL context → spin-until-painted →
//!     read_to_image` flow) and paints the returned
//!     [`RgbaFrame`](servo_render::RgbaFrame) through the SAME
//!     [`rgba_frame_to_image`] `img()` path the web-of-cells tab uses. Fail-closed:
//!     a render error / cap refusal is shown in the status line and the previous
//!     tile is KEPT — the surface never silently blanks.
//!
//! ## The cap model — the net-cap seam, named honestly
//!
//! The page's fetch + navigation ride the genuine
//! [`CapGate`](servo_render::webview) `WebViewDelegate`, which discharges a held
//! [`SurfaceCapability`](starbridge_web_surface::SurfaceCapability) through the
//! `granted ⊆ held` allowlist (`load_web_resource` / `request_navigation`): an
//! origin the surface cap does not permit is REFUSED *at the callback*, before the
//! engine acts (the page sees the cap-denied body, never the resource). This panel
//! holds a real `SurfaceCapability` over the browser's own backing cell and renders
//! through it.
//!
//! ## The net-cap socket bind (the formerly-open wire, now wired)
//!
//! Every fetch's CONNECT DECISION is routed through
//! [`servo_render::NetcapConnector`] backed by the dregg `captp`
//! [`Netlayer::dial`](dregg_captp::netlayer::Netlayer::dial) transport — the SAME
//! audited byte-frame transport the federation dials over (no ambient OS socket). An
//! origin the held [`SurfaceCapability`] does not authorize is refused AT the
//! connector before any `dial` (the socket never opens); a cap-admitted origin's
//! connection IS a real audited `NetSession`. The status line reports which of the
//! three an origin hit (dialed / refused-by-cap / unreachable), via
//! [`render_url_to_frame_netcap`](servo_render::webview::render_url_to_frame_netcap).
//!
//! HONEST DEPTH: for `http(s)` the *bytes-on-the-wire* still ride servo's internal
//! `net` (hyper) — servo forbids embedder `ProtocolHandler`s for `http`/`https`
//! (`FORBIDDEN_SCHEMES`), so replacing the byte socket needs a fork of servo's `net`
//! crate (out of one pass's reach). What IS bound, at the depth the embedder API
//! allows, is the connect/authority decision → `Netlayer::dial`: the origin's
//! reachability is the netlayer's to grant (gated by the cap), and a cap-denied origin
//! is refused at the dial doorstep. A `dregg://` (cell) fetch — not http — rides the
//! connector end-to-end with no such ceiling.
//!
//! ## Build gating
//!
//! The address bar + navigation + the whole surface chrome compile in any windowed
//! (`gpui-ui`) build. The actual page render is gated on the cockpit `web-shell`
//! feature (→ `servo-render/libservo`): with it OFF the panel still renders (URL
//! bar + nav + a "render engine not linked" note); with it ON the `Go` button
//! drives the real `render_url_to_frame`. The frame field + the render call are
//! `#[cfg(feature = "servo")]` (the `RgbaFrame` type) / `#[cfg(feature =
//! "web-shell")]` (the `render_url_to_frame` symbol).

use super::*;

use gpui_component::input::{Input, InputEvent, InputState};

impl Cockpit {
    // === lifecycle ===========================================================

    /// Seed the URL-bar text input entity on the first render (it needs a live
    /// `&mut Window` for [`InputState::new`] + the cockpit's weak handle for the
    /// Enter subscription, neither available in the constructor). Idempotent — a
    /// no-op once seeded. The `↵` (PressEnter) subscription routes straight to
    /// [`Self::webshell_go`], so the address bar behaves like a real browser's.
    pub(crate) fn ensure_webshell_input(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        // Seed the PAGE TILE's focus handle (it needs a live `Context` for
        // `cx.focus_handle()`). A click on the rendered page focuses this; while it
        // holds focus the tile's `on_key_down` routes typed characters into the live
        // WebView, so you can type into a web form / search box.
        #[cfg(feature = "web-shell")]
        if self.webshell_tile_focus.is_none() {
            self.webshell_tile_focus = Some(cx.focus_handle());
        }

        if self.webshell_input.is_none() {
            let seed = self
                .webshell_history
                .get(self.webshell_cursor)
                .cloned()
                .unwrap_or_default();
            let input = cx.new(|cx| {
                let mut st = InputState::new(window, cx).placeholder("https://… or dregg://…");
                st.set_value(seed, window, cx);
                st
            });
            // ↵ in the URL bar = Go (the path the Go button + the ⌘K palette take).
            cx.subscribe(&input, |this, _input, event: &InputEvent, cx| {
                if matches!(event, InputEvent::PressEnter { .. }) {
                    this.webshell_go(cx);
                }
            })
            .detach();
            self.webshell_input = Some(input);
        }

        // Apply any pending URL-bar value (a back/forward/programmatic nav set it):
        // `set_value` needs the live `&mut Window` we only have here, on the paint
        // path. Cleared after applying so user typing is never re-stomped.
        if let Some(url) = self.webshell_input_pending.take() {
            if let Some(input) = self.webshell_input.clone() {
                input.update(cx, |st, cx| st.set_value(url, window, cx));
            }
        }
    }

    /// The URL currently typed into the address bar (the input entity's live value),
    /// falling back to the current history entry when the input is not yet seeded
    /// (the headless path) or empty.
    fn webshell_typed_url(&self, cx: &Context<Self>) -> String {
        let typed = self
            .webshell_input
            .as_ref()
            .map(|i| i.read(cx).value().to_string())
            .unwrap_or_default();
        if typed.trim().is_empty() {
            self.webshell_history
                .get(self.webshell_cursor)
                .cloned()
                .unwrap_or_default()
        } else {
            typed.trim().to_string()
        }
    }

    // === navigation ==========================================================

    /// GO — navigate to the URL in the address bar. A `dregg://` address routes to
    /// the `WebOfCells` browser (the existing web-of-cells resolution path — that is
    /// where a cell address belongs); an `http(s)://` (or scheme-less, defaulted to
    /// `https://`) address is pushed onto the history and RENDERED here. A
    /// malformed/empty address is refused in-band (the status line), the tile kept.
    pub(crate) fn webshell_go(&mut self, cx: &mut Context<Self>) {
        let raw = self.webshell_typed_url(cx);
        let url = normalize_url(&raw);
        let Some(url) = url else {
            self.webshell_status = format!("⚠ not a navigable address: {raw:?}");
            cx.notify();
            return;
        };

        // dregg:// — a cell address. Hand it to the WEB-OF-CELLS browser (the cell
        // docuverse resolution path), not the http renderer. The web-shell is the
        // http(s):// surface; the dregg:// surface is its sibling tab.
        if url.starts_with("dregg://") {
            self.webshell_status =
                format!("dregg:// address → routed to the WEB-OF-CELLS browser ({url})");
            self.set_tab(Tab::WebOfCells, cx);
            return;
        }

        // A NEW navigation truncates the forward tail (browser semantics) + pushes.
        if self.webshell_history.get(self.webshell_cursor) != Some(&url) {
            self.webshell_history.truncate(self.webshell_cursor + 1);
            self.webshell_history.push(url.clone());
            self.webshell_cursor = self.webshell_history.len() - 1;
        }
        self.sync_webshell_input(cx);
        self.webshell_render_current(cx);
    }

    /// BACK — step to the previous URL in history + re-render it (no-op at genesis).
    pub(crate) fn webshell_back(&mut self, cx: &mut Context<Self>) {
        if self.webshell_cursor == 0 {
            self.webshell_status = "← already at the start of history".to_string();
            cx.notify();
            return;
        }
        self.webshell_cursor -= 1;
        self.sync_webshell_input(cx);
        self.webshell_render_current(cx);
    }

    /// FORWARD — step to the next URL in history + re-render it (no-op at the head).
    pub(crate) fn webshell_forward(&mut self, cx: &mut Context<Self>) {
        if self.webshell_cursor + 1 >= self.webshell_history.len() {
            self.webshell_status = "→ already at the head of history".to_string();
            cx.notify();
            return;
        }
        self.webshell_cursor += 1;
        self.sync_webshell_input(cx);
        self.webshell_render_current(cx);
    }

    /// RELOAD — re-render the current history URL (re-drive the WebView render).
    pub(crate) fn webshell_reload(&mut self, cx: &mut Context<Self>) {
        self.webshell_render_current(cx);
    }

    /// Mirror the current history URL back into the address-bar input (after a
    /// back / forward / programmatic navigation), so the bar always shows the URL
    /// being viewed. The actual `set_value` (which needs a live `&mut Window`) is
    /// deferred to the next [`Self::ensure_webshell_input`] on the paint path via
    /// the [`webshell_input_pending`](Self::webshell_input_pending) field.
    fn sync_webshell_input(&mut self, _cx: &mut Context<Self>) {
        if let Some(url) = self.webshell_history.get(self.webshell_cursor).cloned() {
            self.webshell_input_pending = Some(url);
        }
    }

    /// The held [`SurfaceCapability`] this browser renders through — a real cap over
    /// the browser's own backing cell (the cockpit's `service` anchor stands in as
    /// the surface-owning principal). `AuthRequired::Either` clears a normal fetch;
    /// the genuine `granted ⊆ held` gate inside `render_url_to_frame` discharges it
    /// at every `load_web_resource` / `request_navigation` callback.
    #[cfg(feature = "web-shell")]
    fn webshell_surface_cap(&self) -> starbridge_web_surface::SurfaceCapability {
        let owner = self.anchors[1]; // the `service` anchor — the surface principal
        starbridge_web_surface::SurfaceCapability::root(
            owner,
            starbridge_web_surface::AuthRequired::Either,
        )
    }

    /// Render the current history URL into the content tile through the real,
    /// cap-gated Servo WebView. Fail-closed: a `None` frame (no paint / cap refusal /
    /// parse failure) leaves the previous tile in place and explains itself in the
    /// status line.
    pub(crate) fn webshell_render_current(&mut self, cx: &mut Context<Self>) {
        let Some(url) = self.webshell_history.get(self.webshell_cursor).cloned() else {
            self.webshell_status = "no URL to render".to_string();
            cx.notify();
            return;
        };

        #[cfg(feature = "web-shell")]
        {
            const MAX_SPINS: usize = 4096;
            let surface = self.webshell_surface_cap();
            // THE PERSISTENT LIVE WEBVIEW: open it once (on the first navigation), then
            // NAVIGATE it on subsequent loads (a fresh `WebView` on the SAME held
            // engine — servo's options are a process `OnceCell`, so only one engine
            // exists). Holding it alive is what makes the pane interactive: the same
            // live `WebView` then takes scroll/click/key input between paints.
            //
            // Runs under the process-wide SWGL current-context lock (the global `ctx`),
            // the same serialization the headless render path uses.
            let painted = servo_render::with_gl(|| {
                let mut slot = self.webshell_live.borrow_mut();
                match slot.as_mut() {
                    // Already open — navigate the live pane to the new URL.
                    Some(live) => live.load(&url, surface, MAX_SPINS),
                    // First navigation — build the persistent engine + pane and load.
                    None => match servo_render::webview::LiveWebView::open(
                        &url,
                        surface,
                        Self::WEBSHELL_W,
                        Self::WEBSHELL_H,
                        MAX_SPINS,
                    ) {
                        Ok(live) => {
                            let ok = live.frame().is_some();
                            *slot = Some(live);
                            ok
                        }
                        // A second engine was refused (one already exists this process):
                        // the only way this fires is a logic error, surfaced honestly.
                        Err(_) => false,
                    },
                }
            });
            // Pull the live pane's current tile into the painted-tile field.
            self.sync_webshell_frame_from_live();
            // The active render backend (GPU hardware-GL, or SWGL software fallback) —
            // the runtime selection, surfaced so the operator sees whether the pane is
            // GPU-accelerated on this host.
            let backend = self
                .webshell_live
                .borrow()
                .as_ref()
                .map(|l| l.backend_label())
                .unwrap_or("SWGL (software)");
            match (painted, &self.webshell_frame) {
                (true, Some(f)) => {
                    self.webshell_status = format!(
                        "rendered {}×{} of {url} · {} bytes RGBA8 · digest {:#x} · {backend} · LIVE (scroll · click · type)",
                        f.width,
                        f.height,
                        f.bytes.len(),
                        f.content_digest(),
                    );
                }
                _ => {
                    // FAIL-CLOSED — keep the old tile, show why.
                    self.webshell_status = format!(
                        "⚠ no frame for {url} — the page did not paint within {MAX_SPINS} spins or the address is unparseable (tile kept)"
                    );
                }
            }
        }
        #[cfg(not(feature = "web-shell"))]
        {
            self.webshell_status = format!(
                "render engine not linked (build with --features web-shell to drive the real Servo WebView) · would render: {url}"
            );
        }
        cx.notify();
    }

    // === the live loop (input → re-render → repaint) =========================

    /// The web-shell content tile's device dimensions — the persistent
    /// [`LiveWebView`](servo_render::webview::LiveWebView)'s viewport AND the
    /// `img()` paint size, so the gpui pane's pixel coordinates map 1:1 onto the
    /// WebView's device points (no scale factor in the bridge).
    #[cfg(feature = "servo")]
    pub(crate) const WEBSHELL_W: u32 = 720;
    /// See [`Self::WEBSHELL_W`].
    #[cfg(feature = "servo")]
    pub(crate) const WEBSHELL_H: u32 = 460;

    /// Pull the persistent live pane's current tile into [`Self::webshell_frame`] (the
    /// field the `img()` paints). Called after a load or a live input. A no-op on the
    /// `servo`-off build / before the pane has opened.
    #[cfg(feature = "web-shell")]
    fn sync_webshell_frame_from_live(&mut self) {
        if let Some(live) = self.webshell_live.borrow().as_ref() {
            if let Some(frame) = live.frame() {
                self.webshell_frame = Some(frame.clone());
            }
        }
    }

    /// Map a WINDOW-space gpui position to the live WebView's local DEVICE point, using
    /// the tile's last-recorded window bounds ([`Self::webshell_tile_bounds`], set each
    /// frame by the tile's `canvas` overlay). Returns `None` when the point is outside
    /// the tile or the bounds have not been recorded yet (so an out-of-tile scroll is
    /// not mis-delivered into the page).
    #[cfg(feature = "web-shell")]
    fn webshell_local_point(&self, window_pos: gpui::Point<gpui::Pixels>) -> Option<(f32, f32)> {
        let bounds = self.webshell_tile_bounds.get()?;
        let lx = f32::from(window_pos.x - bounds.origin.x);
        let ly = f32::from(window_pos.y - bounds.origin.y);
        let w = f32::from(bounds.size.width);
        let h = f32::from(bounds.size.height);
        if lx < 0.0 || ly < 0.0 || lx >= w || ly >= h {
            return None;
        }
        Some((lx, ly))
    }

    /// **THE EVENT BRIDGE — deliver ONE lowered [`WebInput`] to the live pane, repaint,
    /// and notify the cockpit on change.** The tile's gpui scroll / click / move / key
    /// listeners lower their native events to a [`WebInput`] (translating window coords
    /// to the WebView's local device point via [`Self::webshell_local_point`]) and land
    /// here: the input is delivered to the persistent
    /// [`LiveWebView`](servo_render::webview::LiveWebView) (which pumps the engine +
    /// repaints), the fresh tile is pulled into [`Self::webshell_frame`], and — if the
    /// tile actually changed — `cx.notify()` repaints the `img()`. This is the live
    /// loop: scrolling / clicking / typing in the web-shell updates the cockpit pane.
    ///
    /// `pump` bounds the per-input engine spins (a scroll resolves in a handful; a click
    /// running script may want more). Runs under the SWGL current-context lock.
    #[cfg(feature = "web-shell")]
    fn webshell_apply_live_input(
        &mut self,
        input: servo_render::webview::WebInput,
        pump: usize,
        cx: &mut Context<Self>,
    ) {
        let changed = servo_render::with_gl(|| {
            let mut slot = self.webshell_live.borrow_mut();
            match slot.as_mut() {
                Some(live) if live.is_loaded() => live.apply_input(input, pump),
                _ => false,
            }
        });
        if changed {
            self.sync_webshell_frame_from_live();
            // Re-paint the tile this very frame; the digest moved, so the pixels did.
            cx.notify();
        }
    }

    /// A gpui SCROLL-WHEEL event over the tile → a live page scroll. The wheel delta is
    /// resolved to pixels (line deltas scaled by a nominal line height) and the position
    /// mapped to the tile-local device point; positive `dy` scrolls the page DOWN.
    #[cfg(feature = "web-shell")]
    pub(crate) fn webshell_live_scroll(
        &mut self,
        ev: &gpui::ScrollWheelEvent,
        cx: &mut Context<Self>,
    ) {
        let Some((x, y)) = self.webshell_local_point(ev.position) else {
            return;
        };
        // Resolve the delta to pixels (a line delta uses a nominal 16px line height —
        // the same magnitude order servo's own winit embedder uses for wheel lines).
        let delta = ev.delta.pixel_delta(gpui::px(16.));
        let (dx, dy) = (f32::from(delta.x), f32::from(delta.y));
        if dx == 0.0 && dy == 0.0 {
            return;
        }
        // gpui scroll delta is "content moves with the gesture" (scroll down ⇒ negative
        // y); the page-scroll sense `WebInput::Scroll` wants is "reveal content below ⇒
        // positive dy", so negate.
        self.webshell_apply_live_input(
            servo_render::webview::WebInput::Scroll {
                x,
                y,
                dx: -dx,
                dy: -dy,
            },
            48,
            cx,
        );
    }

    /// A gpui left-CLICK over the tile → a live page click at the tile-local point
    /// (a `mousedown`+`mouseup`, which runs the page's click handlers / follows links).
    #[cfg(feature = "web-shell")]
    pub(crate) fn webshell_live_click(
        &mut self,
        window_pos: gpui::Point<gpui::Pixels>,
        cx: &mut Context<Self>,
    ) {
        let Some((x, y)) = self.webshell_local_point(window_pos) else {
            return;
        };
        // A click may run script / start a navigation; give it more spins than a scroll.
        self.webshell_apply_live_input(servo_render::webview::WebInput::Click { x, y }, 128, cx);
    }

    /// A gpui POINTER-MOVE over the tile → a live page pointer move (drives `:hover` /
    /// cursor). Cheap pump — a hover repaint is small; many of these arrive.
    #[cfg(feature = "web-shell")]
    pub(crate) fn webshell_live_move(
        &mut self,
        ev: &gpui::MouseMoveEvent,
        cx: &mut Context<Self>,
    ) {
        let Some((x, y)) = self.webshell_local_point(ev.position) else {
            return;
        };
        self.webshell_apply_live_input(servo_render::webview::WebInput::MouseMove { x, y }, 16, cx);
    }

    /// A typed CHARACTER into the focused web-shell tile → a live page key event
    /// (a `keydown`+`keyup` for the character). Routed from the cockpit key handler
    /// when the web-shell tile holds focus.
    #[cfg(feature = "web-shell")]
    pub(crate) fn webshell_live_key(&mut self, ch: char, cx: &mut Context<Self>) {
        self.webshell_apply_live_input(servo_render::webview::WebInput::KeyChar { ch }, 96, cx);
    }

    /// A NAMED key (Enter / Backspace / an arrow / …) into the focused web-shell tile →
    /// a live page named-key event, so a web FORM can be submitted (Enter), edited
    /// (Backspace / Delete), and its caret moved (the arrows). Routed alongside
    /// [`Self::webshell_live_key`] from the tile's `on_key_down`.
    #[cfg(feature = "web-shell")]
    pub(crate) fn webshell_live_key_named(
        &mut self,
        key: servo_render::webview::NamedWebKey,
        cx: &mut Context<Self>,
    ) {
        self.webshell_apply_live_input(
            servo_render::webview::WebInput::KeyNamed { key },
            96,
            cx,
        );
    }

    /// **THE KEY ROUTE — a keystroke on the focused page tile → the live WebView.** The
    /// tile's `on_key_down` lands here while the page holds focus (a click on the page
    /// focused it). A PRINTABLE character (`key_char`, no ⌘/Ctrl held) is delivered as
    /// a [`WebInput::KeyChar`](servo_render::webview::WebInput); a NAMED editing key
    /// (Enter / Backspace / Delete / Tab / Escape / the arrows / Home / End) is
    /// delivered as a [`WebInput::KeyNamed`](servo_render::webview::WebInput) — so you
    /// can TYPE into a web form, SUBMIT it, and edit its text. A ⌘/Ctrl chord is left
    /// alone (it bubbles to the cockpit's `on_key` for ⌘K / ⌘J / nav), never sunk into
    /// the page. Returns `true` if the keystroke was delivered to the page (the tile
    /// listener then stops it propagating), `false` if it was left to bubble.
    #[cfg(feature = "web-shell")]
    pub(crate) fn webshell_tile_on_key(
        &mut self,
        ev: &gpui::KeyDownEvent,
        cx: &mut Context<Self>,
    ) -> bool {
        let ks = &ev.keystroke;
        // A ⌘/Ctrl chord is a cockpit command (⌘K / ⌘J / ⌘[ / ⌘]); never sink it into
        // the page — let it bubble to `on_key`.
        if ks.modifiers.platform || ks.modifiers.control {
            return false;
        }
        // A NAMED editing/navigation key (Enter / Backspace / arrows / …) → the page's
        // named-key path (form submit / delete / caret motion).
        if let Some(named) = servo_render::webview::NamedWebKey::from_key_name(ks.key.as_str()) {
            self.webshell_live_key_named(named, cx);
            return true;
        }
        // A printable character (the typed grapheme) → the page's character path. A
        // control char (no printable `key_char`) is not delivered.
        if let Some(ch) = ks.key_char.as_ref().and_then(|s| s.chars().next()) {
            if !ch.is_control() {
                self.webshell_live_key(ch, cx);
                return true;
            }
        }
        false
    }

    // === the live-loop bake hooks (for the headless before/after artifact) =====

    /// **BAKE HOOK** — navigate the web-shell to `url` through the persistent live
    /// WebView (the same path a typed-Enter takes), so a headless bake can show a real
    /// page in the pane. Sets the WebShell tab + history to `url`, then loads. Returns
    /// `true` if a frame painted. Used by the `--render-webshell-live` artifact bake;
    /// the windowed cockpit reaches the same render through [`Self::webshell_go`].
    #[cfg(feature = "web-shell")]
    pub fn webshell_bake_load(&mut self, url: &str, cx: &mut Context<Self>) -> bool {
        self.set_tab(Tab::WebShell, cx);
        self.webshell_history = vec![url.to_string()];
        self.webshell_cursor = 0;
        self.webshell_render_current(cx);
        self.webshell_frame.is_some()
    }

    /// **BAKE HOOK** — deliver ONE scroll-down input to the live WebView at the pane
    /// center (bypassing the window-coord mapping the gpui listeners use, since a
    /// headless bake has no real cursor), pump + repaint, and pull the fresh tile.
    /// Returns `true` if the tile changed — the "input → re-render" witness the
    /// before/after artifact captures. `dy` is CSS pixels to scroll DOWN.
    #[cfg(feature = "web-shell")]
    pub fn webshell_bake_scroll(&mut self, dy: f32, cx: &mut Context<Self>) -> bool {
        let (w, h) = (Self::WEBSHELL_W as f32, Self::WEBSHELL_H as f32);
        let changed = servo_render::with_gl(|| {
            let mut slot = self.webshell_live.borrow_mut();
            match slot.as_mut() {
                Some(live) if live.is_loaded() => live.apply_input(
                    servo_render::webview::WebInput::Scroll {
                        x: w / 2.0,
                        y: h / 2.0,
                        dx: 0.0,
                        dy,
                    },
                    256,
                ),
                _ => false,
            }
        });
        if changed {
            self.sync_webshell_frame_from_live();
            cx.notify();
        }
        changed
    }

    /// **BAKE HOOK** — deliver ONE click to the live WebView at tile-local `(x, y)`
    /// (CSS pixels), bypassing the window-coord mapping (a headless bake has no real
    /// cursor). Used to focus an in-PAGE text field before the key bake types into it.
    /// Returns `true` if the tile changed.
    #[cfg(feature = "web-shell")]
    pub fn webshell_bake_click(&mut self, x: f32, y: f32, cx: &mut Context<Self>) -> bool {
        let changed = servo_render::with_gl(|| {
            let mut slot = self.webshell_live.borrow_mut();
            match slot.as_mut() {
                Some(live) if live.is_loaded() => {
                    live.apply_input(servo_render::webview::WebInput::Click { x, y }, 256)
                }
                _ => false,
            }
        });
        if changed {
            self.sync_webshell_frame_from_live();
            cx.notify();
        }
        changed
    }

    /// **BAKE HOOK** — type ONE character into the live WebView (the same
    /// [`WebInput::KeyChar`](servo_render::webview::WebInput) the focused tile's
    /// `on_key_down` routes), pump + repaint, and pull the fresh tile. Returns `true`
    /// if the tile changed — the "a typed char changes the page" witness (e.g. the
    /// char appearing in a focused `<input>`). The headless analogue of typing into the
    /// focused page; the windowed cockpit reaches the same path through
    /// [`Self::webshell_live_key`].
    #[cfg(feature = "web-shell")]
    pub fn webshell_bake_key(&mut self, ch: char, cx: &mut Context<Self>) -> bool {
        let changed = servo_render::with_gl(|| {
            let mut slot = self.webshell_live.borrow_mut();
            match slot.as_mut() {
                Some(live) if live.is_loaded() => {
                    live.apply_input(servo_render::webview::WebInput::KeyChar { ch }, 256)
                }
                _ => false,
            }
        });
        if changed {
            self.sync_webshell_frame_from_live();
            cx.notify();
        }
        changed
    }

    /// **BAKE HOOK** — the current page-tile content digest (the hash of the tile's
    /// RGBA8 pixels), or `0` before any page paints. A layout-INDEPENDENT witness: it
    /// hashes the WebView's own rendered tile, not the cockpit window, so a key bake can
    /// assert "the page tile changed after typing" even when the tile is clipped/scaled
    /// in the windowed layout. `0` (no frame) is distinguishable from any real digest.
    #[cfg(feature = "web-shell")]
    pub fn webshell_tile_digest(&self) -> u64 {
        self.webshell_frame
            .as_ref()
            .map(|f| f.content_digest())
            .unwrap_or(0)
    }

    // === the panel ===========================================================

    /// THE 🌐 WEB-SHELL panel — the address bar + back/forward/reload + the content
    /// tile (+ the net-cap seam note).
    pub(crate) fn webshell_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let can_back = self.webshell_cursor > 0;
        let can_fwd = self.webshell_cursor + 1 < self.webshell_history.len();
        let current = self
            .webshell_history
            .get(self.webshell_cursor)
            .cloned()
            .unwrap_or_default();

        let mut col = div()
            .id("cockpit-scroll-webshell")
            .flex()
            .flex_col()
            .size_full()
            .overflow_y_scroll()
            .p_3()
            .gap_2();

        // ── header ──
        col = col.child(section_title("🌐 WEB-SHELL — a general http(s):// browser"));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A real Servo WebView render of a live web page, behind the net-cap \
                     allowlist (granted ⊆ held). dregg:// addresses route to the \
                     WEB-OF-CELLS browser.",
        ));

        // ── the navigation toolbar: ← → ⟳ + the URL bar + Go ──
        let mut toolbar = div().flex().items_center().gap_1().mt_1();

        toolbar = toolbar.child(nav_button(
            cx,
            "←",
            "webshell-back",
            if can_back {
                theme::accent()
            } else {
                theme::muted()
            },
            Cockpit::webshell_back,
        ));
        toolbar = toolbar.child(nav_button(
            cx,
            "→",
            "webshell-forward",
            if can_fwd {
                theme::accent()
            } else {
                theme::muted()
            },
            Cockpit::webshell_forward,
        ));
        toolbar = toolbar.child(nav_button(
            cx,
            "⟳",
            "webshell-reload",
            theme::accent(),
            Cockpit::webshell_reload,
        ));

        // The URL BAR — the real gpui-component text input (Enter-to-go is wired in
        // `ensure_webshell_input`). When not yet seeded (first frame / headless) show
        // the current URL as a static field so the bar is never blank.
        if let Some(input) = self.webshell_input.as_ref() {
            toolbar = toolbar.child(div().flex_1().child(Input::new(input)));
        } else {
            toolbar = toolbar.child(
                div()
                    .flex_1()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .text_sm()
                    .text_color(theme::text())
                    .child(SharedString::from(current.clone())),
            );
        }

        toolbar = toolbar.child(nav_button(
            cx,
            "Go",
            "webshell-go",
            theme::good(),
            Cockpit::webshell_go,
        ));
        col = col.child(toolbar);

        // ── the loading / status line ──
        let status_color = if self.webshell_status.starts_with('⚠') {
            theme::warn()
        } else if self.webshell_status.starts_with("rendered") {
            theme::good()
        } else {
            theme::muted()
        };
        col = col.child(
            div()
                .mt_1()
                .px_2()
                .py_1()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(status_color)
                .child(SharedString::from(self.webshell_status.clone())),
        );

        // ── the content tile (with the live event bridge) ──
        col = col.child(self.webshell_tile(cx));

        // ── the cap model / net-cap seam note ──
        col = col.child(
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::accent())
                        .child("THE CAP MODEL"),
                )
                .child(
                    div()
                        .mt_0p5()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(
                            "Every fetch + navigation rides the CapGate WebViewDelegate: \
                             the held SurfaceCapability is discharged through the \
                             granted ⊆ held allowlist at each load_web_resource / \
                             request_navigation callback — a non-permitted origin is \
                             refused AT the callback (the page sees the cap-denied body, \
                             never the resource).",
                        ),
                )
                .child(
                    div()
                        .mt_1()
                        .text_xs()
                        .text_color(theme::good())
                        .child(
                            "NET-CAP SOCKET (wired): every fetch's connect decision routes \
                             through the dregg captp Netlayer::dial connector — a cap-denied \
                             origin is REFUSED at the socket (dial never called), a cap-admitted \
                             origin opens a real audited NetSession. The status line above reports \
                             dialed / refused-by-cap / unreachable.",
                        ),
                )
                .child(
                    div()
                        .mt_0p5()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(
                            "Depth (honest): for http(s) the bytes-on-the-wire still ride servo's \
                             internal hyper (it forbids embedder ProtocolHandlers for http/https); \
                             the CONNECT DECISION + reachability is the netlayer's, gated by the cap. \
                             A dregg:// (cell) fetch rides the connector end-to-end.",
                        ),
                ),
        );

        col
    }

    /// The content tile — the rendered page frame painted through the same `img()`
    /// path the web-of-cells tab uses, or a "no page yet / engine not linked"
    /// placeholder. Fail-closed: a kept frame stays painted even after a failing
    /// navigation (the status line carries the error).
    ///
    /// LIVE (feature `web-shell`): the painted tile carries the gpui→`apply_input`
    /// EVENT BRIDGE — scroll-wheel / left-click / pointer-move listeners on the tile
    /// container lower to a [`WebInput`](servo_render::webview::WebInput) and drive the
    /// persistent live `WebView` ([`Self::webshell_apply_live_input`]), so the pane
    /// scrolls / clicks LIVE. A transparent `canvas` overlay records the tile's
    /// window-space bounds each frame ([`Self::webshell_tile_bounds`]) so the listeners
    /// can map window coords → the WebView's local device point.
    fn webshell_tile(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        // `cx` drives the live event bridge (feature `web-shell`); in a `servo`-only or
        // engine-off build the tile is non-interactive, so `cx` is unused there.
        #[cfg(not(feature = "web-shell"))]
        let _ = &cx;
        #[cfg(feature = "servo")]
        if let Some(frame) = self.webshell_frame.as_ref() {
            let (fw, fh) = (frame.width as f32, frame.height as f32);
            // The bounds-recording overlay: a transparent `canvas` sized to the tile,
            // absolutely positioned over it; its prepaint records the tile's
            // window-space bounds into `webshell_tile_bounds` for the coordinate map.
            // (Feature-gated to `web-shell`: only the live build needs the mapping.)
            #[cfg(feature = "web-shell")]
            let bounds_recorder = {
                let handle = cx.entity().downgrade();
                gpui::canvas(
                    move |bounds, _window, cx| {
                        if let Some(this) = handle.upgrade() {
                            this.read(cx).webshell_tile_bounds.set(Some(bounds));
                        }
                    },
                    |_bounds, _state, _window, _cx| {},
                )
                .absolute()
                .top_0()
                .left_0()
                .w(gpui::px(fw))
                .h(gpui::px(fh))
            };

            // The painted image, with the LIVE event bridge on its container.
            // `mut` only used under `web-shell` (the listeners); harmless otherwise.
            #[cfg_attr(not(feature = "web-shell"), allow(unused_mut))]
            let mut tile_box = div()
                .id("webshell-live-tile")
                .relative()
                .w(gpui::px(fw))
                .h(gpui::px(fh))
                .child(
                    gpui::img(rgba_frame_to_image(frame))
                        .w(gpui::px(fw))
                        .h(gpui::px(fh)),
                );

            #[cfg(feature = "web-shell")]
            {
                tile_box = tile_box
                    .cursor_pointer()
                    .child(bounds_recorder)
                    // SCROLL — the live page scroll (the headline interaction).
                    .on_scroll_wheel(cx.listener(|this, ev: &gpui::ScrollWheelEvent, _w, cx| {
                        this.webshell_live_scroll(ev, cx);
                    }))
                    // MOVE — pointer move (drives :hover / cursor). Bounded pump.
                    .on_mouse_move(cx.listener(|this, ev: &gpui::MouseMoveEvent, _w, cx| {
                        this.webshell_live_move(ev, cx);
                    }));

                // FOCUS + KEYS: make the tile focusable on its own handle so it can
                // TAKE KEYBOARD INPUT. A click both (a) focuses the tile — so typed
                // keys route here, not to the URL bar — and (b) clicks the live page.
                // While focused, `on_key_down` routes each keystroke into the WebView
                // (`webshell_tile_on_key`): type into a web form, submit it with Enter.
                // A 2px ring (transparent → accent on focus) shows when the page has
                // the keyboard. `track_focus`/`focus(..)` need the seeded handle.
                if let Some(focus) = self.webshell_tile_focus.clone() {
                    let focus_for_click = focus.clone();
                    tile_box = tile_box
                        .track_focus(&focus)
                        // A 2px focus ring: transparent at rest, accent when the page
                        // holds the keyboard (the `focus(..)` style applies on focus).
                        .border_2()
                        .border_color(gpui::transparent_black())
                        .focus(|s| s.border_color(theme::accent()))
                        // CLICK — focus the tile (so keys route to the page), THEN
                        // deliver the live page click (mousedown+up; runs handlers /
                        // links). `window` (was `_w`) is needed to move focus.
                        .on_mouse_down(
                            gpui::MouseButton::Left,
                            cx.listener(move |this, ev: &gpui::MouseDownEvent, window, cx| {
                                focus_for_click.focus(window, cx);
                                this.webshell_live_click(ev.position, cx);
                            }),
                        )
                        // KEY — route the keystroke into the live WebView while the
                        // tile holds focus. A delivered key is stopped here (it does
                        // not also bubble to the cockpit's `on_key`); a ⌘/Ctrl chord
                        // is left to bubble (so ⌘K / ⌘J / nav still work).
                        .on_key_down(cx.listener(
                            |this, ev: &gpui::KeyDownEvent, window, cx| {
                                if this.webshell_tile_on_key(ev, cx) {
                                    cx.stop_propagation();
                                    window.prevent_default();
                                }
                            },
                        ));
                } else {
                    // Handle not yet seeded (the very first paint): the click still
                    // drives the live page; the focus/key wire arrives next frame once
                    // `ensure_webshell_input` has seeded the tile focus handle.
                    tile_box = tile_box.on_mouse_down(
                        gpui::MouseButton::Left,
                        cx.listener(|this, ev: &gpui::MouseDownEvent, _w, cx| {
                            this.webshell_live_click(ev.position, cx);
                        }),
                    );
                }
            }

            return div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::good())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::good())
                        .child("PAGE — LIVE cap-gated Servo WebView · click to focus, then TYPE into the page · scroll · click → re-render (SWGL → glass)"),
                )
                .child(tile_box)
                .into_any_element();
        }

        // No frame yet (or `servo` off): a placeholder tile that names the state.
        div()
            .mt_2()
            .p_4()
            .rounded_md()
            .border_1()
            .border_color(theme::border())
            .bg(theme::panel())
            .flex()
            .items_center()
            .justify_center()
            .h(gpui::px(200.))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(self.webshell_tile_placeholder()),
            )
            .into_any_element()
    }

    /// The placeholder text when there is no rendered frame to paint.
    fn webshell_tile_placeholder(&self) -> SharedString {
        #[cfg(feature = "web-shell")]
        {
            SharedString::from("no page rendered yet — type an http(s):// address and press ↵ Go")
        }
        #[cfg(not(feature = "web-shell"))]
        {
            SharedString::from(
                "the real WebView render engine is not linked in this build — build with \
                 --features web-shell (→ servo-render/libservo) to render live pages here",
            )
        }
    }
}

/// Normalize a raw address-bar string into a navigable URL. A `dregg://`,
/// `http://`, or `https://` URL passes through; a scheme-less, dot-bearing token
/// (e.g. `example.com`) is defaulted to `https://`; anything else (an empty or
/// space-laden non-URL) is rejected (`None`) — surfaced in-band, never silently
/// navigated.
fn normalize_url(raw: &str) -> Option<String> {
    let t = raw.trim();
    if t.is_empty() {
        return None;
    }
    if t.starts_with("dregg://") || t.starts_with("http://") || t.starts_with("https://") {
        return Some(t.to_string());
    }
    // A bare host (`example.com`, `a.b/c`) — default to https. Reject a token with
    // no dot and no slash (it is not a host), and anything with whitespace.
    if t.contains(char::is_whitespace) {
        return None;
    }
    if t.contains('.') {
        return Some(format!("https://{t}"));
    }
    None
}

/// A web-shell toolbar button (← → ⟳ Go) — a small kit `Button` running a
/// `&mut Cockpit` nav method. Mirrors [`shell_button`], with a caller-supplied
/// stable element id (the labels are glyphs, not unique strings).
fn nav_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    id: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    button_variant(
        Button::new(SharedString::from(id.to_string())).label(label.to_string()),
        color,
    )
    .small()
    .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
        handler(this, cx);
    }))
}

#[cfg(test)]
mod tests {
    use super::normalize_url;

    #[test]
    fn normalize_passes_through_full_urls() {
        assert_eq!(
            normalize_url("https://example.com").as_deref(),
            Some("https://example.com")
        );
        assert_eq!(
            normalize_url("http://a.b/c").as_deref(),
            Some("http://a.b/c")
        );
        assert_eq!(
            normalize_url("dregg://cell/0").as_deref(),
            Some("dregg://cell/0")
        );
    }

    #[test]
    fn normalize_defaults_bare_hosts_to_https() {
        assert_eq!(
            normalize_url("example.com").as_deref(),
            Some("https://example.com")
        );
        assert_eq!(normalize_url("  a.b/c  ").as_deref(), Some("https://a.b/c"));
    }

    #[test]
    fn normalize_rejects_non_urls() {
        assert_eq!(normalize_url(""), None);
        assert_eq!(normalize_url("   "), None);
        assert_eq!(normalize_url("not a url"), None); // whitespace
        assert_eq!(normalize_url("noscheme"), None); // no dot, no scheme
    }
}
