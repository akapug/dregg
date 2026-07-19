//! # `descent_play` — THE DESCENT, mounted on a served page (backlog H1, "the real win").
//!
//! `GET /descent/play` is the flagship's **playable web front door**: a strict-CSP page that mounts
//! the ALREADY-BUILT `<dregg-descent>` thin-view ([`extension/src/elements/dregg-descent.ts`]) over
//! the ALREADY-BUILT wasm [`DescentWorld`](../../../wasm/src/bindings_descent.rs), wired to an
//! **in-page** [`DescentEngine`] — the SAME client the browser extension runs, minus the
//! `chrome.runtime` transport hop (routed in-page to the engine here, exactly as
//! `extension/tests/dregg-descent/fixture.html` + its harness do). A stranger with a plain URL plays
//! a real, beacon-seeded, permadeath run in the tab: gate room → cap-gated verified moves →
//! permadeath, private (the moves never leave the device) and replay-verifiable.
//!
//! Until this page, every web/Telegram "Play The Descent" CTA landed on `/descent` — the no-cheat
//! *leaderboard*, not a game (`docs/DESCENT-EXCELLENCE-BACKLOG-2026-07-18.md` §H1). The playable
//! surface existed but was reachable only inside the extension. This mounts it on a served page.
//!
//! ## What this module is — pure surface plumbing (NOT a game re-authoring)
//!
//! The game RULES / AIR / `daily_scene` move-math live in the Lean terminal + `spween-dregg` +
//! `dreggnet-offerings`, compiled into the wasm `DescentWorld`. This module writes **none** of that.
//! It serves: (1) an HTML shell in the site's own [`STYLE`](crate::STYLE)/[`topbar`](crate::topbar)/
//! [`FOOTER`](crate::FOOTER) chrome, with a strict Content-Security-Policy; (2) a same-origin
//! bootstrap module ([`PLAY_APP_JS`]) that constructs the engine, sets the port factory, and
//! registers the element; (3) same-origin routes for the vendored client bundle + wasm.
//!
//! ## Security posture — the `/tg/link` review's discipline (`docs/TG-LINK-SECURITY-REVIEW-2026-07-18.md`)
//!
//! Every script the page loads is **same-origin** (the bootstrap, the client bundle, the wasm glue),
//! so [`PLAY_CSP`] can be strict: `script-src 'self' 'wasm-unsafe-eval'` (the `'wasm-unsafe-eval'` is
//! the one concession WebAssembly instantiation needs — NOT `'unsafe-eval'`, NOT `'unsafe-inline'`
//! for scripts), `connect-src 'self'` (the glue fetches the `.wasm` same-origin), and no CDN. This
//! closes the "a CDN/MITM serves attacker JS" hole exactly as the link-page review did — the whole
//! point of serving the wasm bundle from our own origin, never `esm.sh` / a public wasm CDN.
//!
//! ## HONEST GAP — two vendored artifacts, no build step in `dreggnet-web`
//!
//! `dreggnet-web` has **no JS/TS build pipeline and no wasm-pack step** (the same reality
//! [`crate::discord_activity`] names for its vendored SDK bundle). Mounting the *real* client needs
//! two artifacts BUILT ELSEWHERE and dropped into the descent-play asset dir
//! ([`play_asset_dir`], default `dreggnet-web/assets/descent/`, override `DESCENT_PLAY_ASSET_DIR`):
//!
//! 1. **`client.js`** — the element + engine + port, bundled to an ESM:
//!    `esbuild extension/src/descent-play-entry.ts --bundle --format=esm --target=es2022 \`
//!    `  --outfile=dreggnet-web/assets/descent/client.js`
//!    (the entry re-exports `DescentEngine` / `defaultResolveDescent` / `setDescentPortFactory` /
//!    `registerDescentElement` — the exact four [`PLAY_APP_JS`] imports).
//! 2. **`dregg_wasm.js` + `dregg_wasm_bg.wasm`** — the wasm `DescentWorld`, `--target web`:
//!    `wasm-pack build wasm --target web --out-dir pkg --release` then copy `pkg/dregg_wasm.js`
//!    and `pkg/dregg_wasm_bg.wasm` into the same asset dir. (`wasm/pkg/` already holds a fresh
//!    `--target web` build — this is a copy, not a new toolchain.)
//!
//! Until an artifact lands, its route serves an honest placeholder (JS) / `503` (wasm) and the page
//! renders a "not vendored yet" notice — the shell, the routes, and the mount glue are all real and
//! light up the moment the two artifacts are dropped in. No code change converges it.

use std::path::PathBuf;

use axum::{
    Router,
    http::{StatusCode, header},
    response::{Html, IntoResponse, Response},
    routing::get,
};

/// The strict Content-Security-Policy for the play page. `'wasm-unsafe-eval'` is the single
/// concession WebAssembly instantiation requires (it is NOT `'unsafe-eval'` and does NOT loosen JS
/// eval); everything the page loads is same-origin, so scripts get no `'unsafe-inline'` and there is
/// no CDN origin. `connect-src 'self'` is what the wasm glue's same-origin `fetch` of the `.wasm`
/// blob needs; `style-src 'unsafe-inline'` covers the site `<style>` + the element's closed-shadow
/// stylesheet (DOM `<style>` text, not a script).
const PLAY_CSP: &str = "default-src 'none'; \
    script-src 'self' 'wasm-unsafe-eval'; \
    style-src 'unsafe-inline'; \
    connect-src 'self'; \
    img-src 'self' data:; \
    font-src 'self'; \
    base-uri 'none'; object-src 'none'; form-action 'none'; \
    frame-ancestors 'none'";

/// The `text/javascript` content-type every served module carries (same string the sibling
/// same-origin-asset routes use).
const JS_CT: &str = "text/javascript; charset=utf-8";

/// The canonical descent day URI the served element opens. `defaultResolveDescent` derives a
/// STABLE, byte-identical day from a well-formed `dregg://descent/b3_<hex>` addr (the same
/// deterministic stand-in the fixture + poll/doc/story engines use), so this page opens a real,
/// fully-playable Descent run without a network fetch. The production seam that swaps this for
/// TODAY's live drand round (`DescentWorld.fromBeacon`) is `defaultResolveDescent`'s documented
/// beacon-client path — a follow-up, orthogonal to this mount.
const DEFAULT_DAY_URI: &str = "dregg://descent/b3_de5ce0";

/// **Build the playable-Descent router.** Additive + state-free — merge it onto the same app as
/// [`descent_router`](crate::descent_router) / [`router`](crate::router). Serves:
/// - `GET /descent/play` — the strict-CSP page shell that mounts `<dregg-descent>`;
/// - `GET /descent/play/static/app.js` — the same-origin bootstrap ([`PLAY_APP_JS`]);
/// - `GET /descent/play/static/client.js` — the vendored element+engine bundle (or a placeholder);
/// - `GET /descent/play/static/dregg_wasm.js` — the vendored wasm glue (or a placeholder);
/// - `GET /descent/play/static/dregg_wasm_bg.wasm` — the vendored wasm blob (or an honest `503`).
pub fn descent_play_router() -> Router {
    Router::new()
        .route("/descent/play", get(get_descent_play))
        .route("/descent/play/static/app.js", get(get_play_app_js))
        .route("/descent/play/static/client.js", get(get_play_client_js))
        .route(
            "/descent/play/static/dregg_wasm.js",
            get(get_play_wasm_glue),
        )
        .route(
            "/descent/play/static/dregg_wasm_bg.wasm",
            get(get_play_wasm_blob),
        )
}

/// `GET /descent/play` — the play page shell (static HTML; the strict CSP header is the point). The
/// `<dregg-descent>` element upgrades + boots against the in-page engine [`PLAY_APP_JS`] wires; a
/// fallback board link inside it is what shows before the module runs (or if the run fails closed).
async fn get_descent_play() -> Response {
    (
        [(header::CONTENT_SECURITY_POLICY, PLAY_CSP)],
        Html(shell_page()),
    )
        .into_response()
}

/// `GET /descent/play/static/app.js` — the bootstrap module, served SAME-ORIGIN so the strict CSP
/// forbids inline script (a CDN swap / XSS of the mount glue has no foothold).
async fn get_play_app_js() -> impl IntoResponse {
    ([(header::CONTENT_TYPE, JS_CT)], PLAY_APP_JS)
}

/// `GET /descent/play/static/client.js` — the vendored element+engine+port ESM bundle. Absent →
/// [`CLIENT_PLACEHOLDER_JS`] (a valid module that defines none of the four exports), so the
/// bootstrap detects it and shows an honest notice. See the module-level "HONEST GAP".
async fn get_play_client_js() -> Response {
    match read_play_asset("client.js") {
        Some(bytes) => ([(header::CONTENT_TYPE, JS_CT)], bytes).into_response(),
        None => ([(header::CONTENT_TYPE, JS_CT)], CLIENT_PLACEHOLDER_JS).into_response(),
    }
}

/// `GET /descent/play/static/dregg_wasm.js` — the vendored wasm glue (`wasm-pack --target web`).
/// Absent → [`WASM_GLUE_PLACEHOLDER_JS`] (its default `init` throws), so the bootstrap degrades to
/// an honest notice. Its default init fetches `dregg_wasm_bg.wasm` relative to THIS url, i.e.
/// `/descent/play/static/dregg_wasm_bg.wasm` (the same-origin blob route below).
async fn get_play_wasm_glue() -> Response {
    match read_play_asset("dregg_wasm.js") {
        Some(bytes) => ([(header::CONTENT_TYPE, JS_CT)], bytes).into_response(),
        None => ([(header::CONTENT_TYPE, JS_CT)], WASM_GLUE_PLACEHOLDER_JS).into_response(),
    }
}

/// `GET /descent/play/static/dregg_wasm_bg.wasm` — the vendored wasm blob, served
/// `application/wasm` (so `WebAssembly.instantiateStreaming` accepts it). Absent → an honest `503`
/// naming the `wasm-pack` step, never a broken `200`.
///
/// NOTE: this reads the (large) blob from disk per request via `std::fs`. That is fine for the demo
/// server + a low-traffic play page; a production deployment should front the `static/` prefix with
/// a caching static file server (as `site/` already serves `pkg/`), which this route's fixed paths
/// make a drop-in.
async fn get_play_wasm_blob() -> Response {
    match read_play_asset("dregg_wasm_bg.wasm") {
        Some(bytes) => ([(header::CONTENT_TYPE, "application/wasm")], bytes).into_response(),
        None => (
            StatusCode::SERVICE_UNAVAILABLE,
            [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
            "The Descent WebAssembly bundle (dregg_wasm_bg.wasm) is not vendored on this deployment.\n\
             Build it with `wasm-pack build wasm --target web` and copy pkg/dregg_wasm_bg.wasm into\n\
             the descent-play asset dir (default dreggnet-web/assets/descent/, override\n\
             DESCENT_PLAY_ASSET_DIR). See dreggnet-web/src/descent_play.rs.",
        )
            .into_response(),
    }
}

/// The directory the vendored play artifacts (`client.js`, `dregg_wasm.js`, `dregg_wasm_bg.wasm`)
/// are read from: `DESCENT_PLAY_ASSET_DIR` when set + non-empty, else the in-crate default
/// `dreggnet-web/assets/descent/`.
fn play_asset_dir() -> PathBuf {
    match std::env::var("DESCENT_PLAY_ASSET_DIR") {
        Ok(dir) if !dir.trim().is_empty() => PathBuf::from(dir.trim()),
        _ => PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/assets/descent")),
    }
}

/// Read a vendored play asset by its fixed basename (never user input — each route passes a literal,
/// so there is no path-traversal surface). `None` when the artifact has not been vendored yet.
fn read_play_asset(name: &str) -> Option<Vec<u8>> {
    let mut path = play_asset_dir();
    path.push(name);
    std::fs::read(path).ok()
}

/// **The play page** — the site's own chrome ([`STYLE`](crate::STYLE) / [`topbar`](crate::topbar) /
/// [`FOOTER`](crate::FOOTER)) so this reads as the SAME product, with a strict-CSP-clean body: no
/// inline script (the affordance-enhance script that `document()` injects is deliberately omitted —
/// the descent element drives its own closed shadow, and an inline script would violate the CSP),
/// just the mount root and the same-origin bootstrap module. The `<dregg-descent>` carries a
/// board-link as fallback content (shown pre-boot / on a fail-closed run).
fn shell_page() -> String {
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <meta name=\"color-scheme\" content=\"dark\">\
         <title>Play The Descent — DreggNet Cloud</title>{style}</head><body>{topbar}\
         <main class=\"session\">\
         <p class=\"prose\">The Descent — played in your browser</p>\
         <p class=\"prose\">A beacon-seeded, permadeath run, played right here in the tab. Every move \
         is one cap-gated verified turn on the in-tab executor; the run stays private (the moves \
         never leave your device) and a stranger can replay the whole receipt chain. Reach the \
         drowned king&#39;s hoard, or fall to the warden.</p>\
         <div id=\"descent-play-root\">\
         <dregg-descent id=\"descent-run\" src=\"{day}\">\
         <a class=\"btn btn-ghost\" href=\"/descent\">See today&#39;s no-cheat board \
         <span class=\"arr\" aria-hidden=\"true\">&rarr;</span></a>\
         </dregg-descent>\
         </div>\
         <noscript><p class=\"notice refused\" role=\"status\">The Descent plays in-tab with \
         JavaScript + WebAssembly. With scripting off, see the \
         <a href=\"/descent\">no-cheat board</a> instead.</p></noscript>\
         </main>{footer}\
         <script type=\"module\" src=\"/descent/play/static/app.js\"></script>\
         </body></html>",
        style = crate::STYLE,
        topbar = crate::topbar("descent"),
        day = DEFAULT_DAY_URI,
        footer = crate::FOOTER,
    )
}

/// **The bootstrap module** (`/descent/play/static/app.js`) — the whole mount, in one same-origin
/// ES module. It imports the vendored client bundle + wasm glue, instantiates the wasm, builds one
/// in-page [`DescentEngine`] over the real wasm `DescentWorld`, routes the descent port to it, and
/// registers the element AFTER the port factory is set (the element reads the factory at upgrade
/// time). This is the ONLY thing the extension does differently: there the port is a `chrome.runtime`
/// hop to a background engine; here the SAME engine is wired directly, exactly as the fixture does.
/// Missing/placeholder artifacts degrade to an honest, styled notice — never a broken authorize.
const PLAY_APP_JS: &str = r##"// THE DESCENT, mounted on a served page. Wires the REAL <dregg-descent> thin-view over the REAL
// wasm DescentWorld through an in-page DescentEngine (dreggnet-web/src/descent_play.rs).
const root = document.getElementById("descent-play-root");

function notice(msg) {
  const p = document.createElement("p");
  p.className = "notice refused";
  p.setAttribute("role", "status");
  p.textContent = msg;
  if (root) root.replaceChildren(p);
}

async function boot() {
  // (1) The element + engine + port bundle (esbuild of extension/src/descent-play-entry.ts).
  let client;
  try {
    client = await import("/descent/play/static/client.js");
  } catch (e) {
    notice("Could not load The Descent web client: " + (e && e.message ? e.message : e));
    return;
  }
  if (!client || typeof client.DescentEngine !== "function" ||
      typeof client.setDescentPortFactory !== "function" ||
      typeof client.registerDescentElement !== "function" ||
      typeof client.defaultResolveDescent !== "function") {
    notice("The Descent web client is not built into this deployment yet — the game cannot start. " +
      "(Vendor the esbuild bundle at /descent/play/static/client.js; see descent_play.rs.)");
    return;
  }

  // (2) The wasm DescentWorld (wasm-pack --target web). Its default export is the async init; with
  //     no argument it fetches dregg_wasm_bg.wasm relative to its own url (same-origin, this route).
  let wasm;
  try {
    wasm = await import("/descent/play/static/dregg_wasm.js");
    await wasm.default();
  } catch (e) {
    notice("The Descent WebAssembly bundle is not built into this deployment yet — the game cannot " +
      "start. (Vendor wasm-pack --target web output at /descent/play/static/; see descent_play.rs.)");
    return;
  }
  const DescentWorld = wasm.DescentWorld;
  if (typeof DescentWorld !== "function") {
    notice("The Descent WebAssembly bundle did not export DescentWorld — cannot start the game.");
    return;
  }

  const { DescentEngine, defaultResolveDescent, setDescentPortFactory, registerDescentElement } = client;

  // (3) One engine owns the real wasm world per day. Play + verify are the FREE, PRIVATE, in-tab
  //     tier; settle (the opt-in publish-to-leaderboard hook) is left unwired here, so a run stays
  //     private and the element's publish button degrades to its honest "opt-in named hook" note.
  const engine = new DescentEngine({
    DescentWorld: DescentWorld,
    resolveDescent: defaultResolveDescent,
    settle: null,
  });

  // (4) Route the descent port in-page to the engine. The element's default transport is a
  //     chrome.runtime hop to a background engine; on a plain page there is no extension, so the
  //     SAME engine is wired directly — the ONLY shimmed piece, exactly as the fixture harness does.
  //     Set BEFORE registering: the element reads the factory when it upgrades.
  setDescentPortFactory(function () {
    return { request: function (req) { return engine.handle(req, location.origin); } };
  });

  // (5) Register the element; the parser-created <dregg-descent src=...> upgrades and boots against
  //     the in-page engine — opening today's day, rendering the gate room + its moves, and running
  //     the whole private, replay-verifiable run in the tab.
  registerDescentElement();
}

boot().catch(function (e) {
  notice("Could not start The Descent: " + (e && e.message ? e.message : e));
});
"##;

/// The placeholder served for `client.js` until the real esbuild bundle is vendored (mirrors
/// [`crate::discord_activity`]'s SDK placeholder). A valid ES module that defines NONE of the four
/// exports [`PLAY_APP_JS`] needs, so the bootstrap detects it and shows the honest notice.
const CLIENT_PLACEHOLDER_JS: &str = r##"// PLACEHOLDER — the Descent web client bundle is NOT vendored on this build.
// Build it once and drop it in the descent-play asset dir (default dreggnet-web/assets/descent/):
//   esbuild extension/src/descent-play-entry.ts --bundle --format=esm --target=es2022 \
//     --outfile=dreggnet-web/assets/descent/client.js
// It must export: DescentEngine, defaultResolveDescent, setDescentPortFactory, registerDescentElement.
export const __DESCENT_CLIENT_PLACEHOLDER = true;
console.warn("dregg: /descent/play/static/client.js placeholder — vendor the esbuild bundle (see descent_play.rs).");
"##;

/// The placeholder served for `dregg_wasm.js` until the real `wasm-pack --target web` glue is
/// vendored. Its default `init` throws, so the bootstrap's try/catch degrades to an honest notice.
const WASM_GLUE_PLACEHOLDER_JS: &str = r##"// PLACEHOLDER — the wasm `--target web` glue is NOT vendored on this build.
// Build + copy into the descent-play asset dir (default dreggnet-web/assets/descent/):
//   wasm-pack build wasm --target web --out-dir pkg --release
//   cp wasm/pkg/dregg_wasm.js wasm/pkg/dregg_wasm_bg.wasm dreggnet-web/assets/descent/
export default async function () {
  throw new Error("dregg_wasm.js placeholder — the wasm bundle is not vendored (see descent_play.rs).");
}
export const __DESCENT_WASM_PLACEHOLDER = true;
"##;

#[cfg(test)]
mod tests {
    use axum::response::IntoResponse;

    #[tokio::test]
    async fn the_play_page_ships_a_strict_wasm_csp_and_mounts_the_element() {
        let resp = super::get_descent_play().await;
        let csp = resp
            .headers()
            .get("content-security-policy")
            .expect("CSP header present")
            .to_str()
            .unwrap();
        // Strict, same-origin scripts + the one WebAssembly concession — never unsafe-inline/eval.
        assert!(
            csp.contains("script-src 'self' 'wasm-unsafe-eval'"),
            "wasm CSP"
        );
        assert!(
            !csp.contains("'unsafe-inline'") || !csp.contains("script-src 'self' 'unsafe-inline'")
        );
        assert!(!csp.contains("'unsafe-eval'") || csp.contains("'wasm-unsafe-eval'"));
        assert!(csp.contains("connect-src 'self'"), "same-origin wasm fetch");

        let html = super::shell_page();
        assert!(html.contains("<dregg-descent"), "the element is mounted");
        assert!(
            html.contains(super::DEFAULT_DAY_URI),
            "opens a concrete day"
        );
        assert!(
            html.contains("/descent/play/static/app.js"),
            "same-origin bootstrap module"
        );
        // No CDN / external script origin (the /tg/link discipline).
        assert!(!html.contains("esm.sh") && !html.contains("https://cdn"));
        // Same product chrome + a board-link fallback for the pre-boot / no-JS reader.
        assert!(html.contains("href=\"/descent\""), "board fallback link");
    }

    #[tokio::test]
    async fn the_bootstrap_wires_the_real_engine_and_element() {
        use axum::body::to_bytes;
        let resp = super::get_play_app_js().await.into_response();
        assert_eq!(
            resp.headers().get("content-type").unwrap(),
            "text/javascript; charset=utf-8"
        );
        let body = to_bytes(resp.into_body(), 1 << 20).await.unwrap();
        let js = std::str::from_utf8(&body).unwrap();
        // The four real client symbols + the in-page port wire (not chrome.runtime).
        for needle in [
            "DescentEngine",
            "defaultResolveDescent",
            "setDescentPortFactory",
            "registerDescentElement",
            "engine.handle(req, location.origin)",
            "/descent/play/static/client.js",
            "/descent/play/static/dregg_wasm.js",
        ] {
            assert!(js.contains(needle), "bootstrap references {needle}");
        }
    }

    #[tokio::test]
    async fn an_unvendored_wasm_blob_fails_closed_with_an_honest_503() {
        // With no vendored asset dir on the test box, the blob route is an honest 503 (never a
        // broken 200), and the client/glue routes serve detectable placeholders.
        // SAFETY: single-threaded set of a process env for this scoped assertion.
        unsafe {
            std::env::set_var(
                "DESCENT_PLAY_ASSET_DIR",
                "/nonexistent/dregg-descent-play-assets",
            );
        }
        let blob = super::get_play_wasm_blob().await;
        assert_eq!(blob.status(), axum::http::StatusCode::SERVICE_UNAVAILABLE);

        let client = super::get_play_client_js().await;
        assert_eq!(client.status(), axum::http::StatusCode::OK);
        let cbody = axum::body::to_bytes(client.into_body(), 1 << 16)
            .await
            .unwrap();
        assert!(
            std::str::from_utf8(&cbody)
                .unwrap()
                .contains("__DESCENT_CLIENT_PLACEHOLDER")
        );
        unsafe {
            std::env::remove_var("DESCENT_PLAY_ASSET_DIR");
        }
    }
}
