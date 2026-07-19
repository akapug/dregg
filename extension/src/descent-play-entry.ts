/**
 * Web-served bundle entry for THE DESCENT played on a plain page (dreggnet-web's
 * `GET /descent/play`, served at `/descent/play/static/client.js`).
 *
 * It re-exports EXACTLY the four symbols the served bootstrap (`dreggnet-web/src/descent_play.rs`,
 * `PLAY_APP_JS`) imports, so the mount is the REAL client — the same `<dregg-descent>` thin-view
 * + `DescentEngine` + descent port the browser extension runs — with no re-authoring. The page
 * wires an in-page `DescentEngine` over the wasm `DescentWorld` and routes the port to it, the
 * only difference from the extension being the transport hop (no `chrome.runtime` on a plain page).
 *
 * Build (dreggnet-web has no JS build step; run this once and vendor the output):
 *   esbuild extension/src/descent-play-entry.ts --bundle --format=esm --target=es2022 \
 *     --outfile=dreggnet-web/assets/descent/client.js
 *
 * This file is NOT one of the extension's `build.mjs` entryPoints (background/content/page/popup),
 * so it never enters the extension bundle — it exists solely to give the served page a clean ESM.
 */
export { DescentEngine, defaultResolveDescent } from "./port";
export { setDescentPortFactory, registerDescentElement } from "./elements/dregg-descent";
