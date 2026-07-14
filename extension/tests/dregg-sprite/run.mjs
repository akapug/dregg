// Fixture test for the in-house sprite, painted in-tab (`<dregg-sprite>`).
//
// Serves a static page carrying <dregg-sprite> elements, loads it in a real (headless)
// Chromium via Playwright, and asserts the whole paint path (docs/CONTENT-AND-ASSET-SPEC.md;
// dreggnet-sprite/src/lib.rs; wasm/src/bindings_sprite.rs):
//   - the element upgrades → a CLOSED shadow root (the page cannot read it);
//   - it paints a well-formed <svg> for its (kind, asset) and reflects [rendered] + [kind];
//   - DETERMINISM: two elements with the SAME (kind, asset) paint the BYTE-IDENTICAL SVG;
//   - a DIFFERENT asset id paints a different sprite; the two KINDS (gear/card) differ;
//   - a malformed asset id FAILS CLOSED — no render, [error], no shadow art.
//
// The engine + element are the shipping code path; only the transport hop is shimmed, and
// the wasm renderer is stood in by an in-memory DETERMINISTIC one (see harness.ts).
//
// Run:  node --test tests/dregg-sprite/run.mjs

import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const MIME = {
  ".js": "text/javascript; charset=utf-8",
  ".html": "text/html; charset=utf-8",
};

async function buildHarness() {
  const out = await esbuild.build({
    entryPoints: [path.join(__dirname, "harness.ts")],
    bundle: true,
    format: "iife",
    platform: "browser",
    target: ["es2022"],
    write: false,
  });
  return out.outputFiles[0].text;
}

async function startServer(harnessJs) {
  const fixture = await readFile(path.join(__dirname, "fixture.html"), "utf8");
  const server = http.createServer((req, res) => {
    const url = req.url.split("?")[0];
    const send = (body, type) => {
      res.writeHead(200, { "content-type": type });
      res.end(body);
    };
    if (url === "/" || url === "/fixture.html") return send(fixture, MIME[".html"]);
    if (url === "/harness.js") return send(harnessJs, MIME[".js"]);
    res.writeHead(404);
    res.end("not found");
  });
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  const { port } = server.address();
  return { server, base: `http://127.0.0.1:${port}` };
}

// Browser-side snapshot: read the closed-shadow registry (test-only) + reflected attributes
// for one <dregg-sprite>. `svg` is the painted SVG's outerHTML (the byte-stable render).
const SNAPSHOT = `
window.__snap = function snap(id) {
  const el = document.getElementById(id);
  const roots = window.__dreggSpriteRoots;
  const root = roots && roots.get(el);
  const svgEl = root ? root.querySelector('.art svg') : null;
  return {
    kind: el.getAttribute("kind"),
    asset: el.getAttribute("asset"),
    rendered: el.hasAttribute("rendered"),
    error: el.hasAttribute("error"),
    rarity: el.getAttribute("rarity"),
    pageSeesShadow: el.shadowRoot !== null,            // closed ⇒ always false
    hasShadow: !!root,
    hasSvg: !!svgEl,
    svg: svgEl ? svgEl.outerHTML : null,
    caption: root ? (root.querySelector(".cap")?.textContent || "").trim() : null,
  };
};
`;

test("dregg-sprite: paints a deterministic SVG in a closed shadow (same asset ⇒ byte-identical; different id / kind differ; bad input fails closed)", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push(String(e)));
    await page.addInitScript(SNAPSHOT);
    await page.goto(`${base}/fixture.html`);

    // Boot: engine + element wired.
    await page.waitForFunction(() => window.__DREGG_READY === true || window.__DREGG_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__DREGG_ERROR || null);
    assert.equal(bootErr, null, `harness boot error: ${bootErr}`);

    // The four valid sprites settle [rendered]; the bad one settles [error].
    await page.waitForFunction(
      () => {
        const els = [...document.querySelectorAll("dregg-sprite")];
        return els.length === 5 && els.every((el) => el.hasAttribute("rendered") || el.hasAttribute("error"));
      },
      null,
      { timeout: 15000 },
    );

    // ── gearA: a well-formed <svg> painted into a CLOSED shadow, [rendered] reflected.
    const gearA = await page.evaluate(() => window.__snap("gearA"));
    assert.equal(gearA.pageSeesShadow, false, "closed shadow hides the render from the page");
    assert.equal(gearA.hasShadow, true, "the closed shadow was attached (test registry)");
    assert.equal(gearA.rendered, true, "[rendered] reflected");
    assert.equal(gearA.error, false, "no [error] on a valid sprite");
    assert.equal(gearA.kind, "gear", "[kind] reflected");
    assert.equal(gearA.hasSvg, true, "an <svg> was painted");
    assert.match(gearA.svg, /^<svg[\s>]/, "the painted art is an SVG root");
    assert.ok(gearA.rarity, "a [rarity] was reflected from the trait vector");
    assert.match(gearA.caption, /gear/i, "the caption names the kind");

    // ── DETERMINISM: gearAdup (same kind + asset) paints the BYTE-IDENTICAL SVG.
    const gearAdup = await page.evaluate(() => window.__snap("gearAdup"));
    assert.equal(gearAdup.svg, gearA.svg, "same (kind, asset) ⇒ byte-identical painted SVG");
    assert.equal(gearAdup.rarity, gearA.rarity, "same asset ⇒ same derived rarity");

    // ── A DIFFERENT asset id ⇒ a different sprite.
    const gearB = await page.evaluate(() => window.__snap("gearB"));
    assert.equal(gearB.rendered, true, "the different-asset gear also renders");
    assert.notEqual(gearB.svg, gearA.svg, "a different asset id ⇒ a different sprite");

    // ── The two KINDS differ for the SAME asset id.
    const cardA = await page.evaluate(() => window.__snap("cardA"));
    assert.equal(cardA.rendered, true, "the card renders");
    assert.equal(cardA.kind, "card", "[kind] reflects card");
    assert.notEqual(cardA.svg, gearA.svg, "gear and card of the same asset are distinct sprites");
    assert.match(cardA.svg, /data-kind="card"/, "the card SVG carries its kind");

    // ── FAIL-CLOSED: the malformed asset id renders NOTHING (no shadow art, [error]).
    const bad = await page.evaluate(() => window.__snap("badSprite"));
    assert.equal(bad.rendered, false, "a malformed asset never renders");
    assert.equal(bad.error, true, "[error] reflected on the fail-closed element");
    assert.equal(bad.pageSeesShadow, false, "no shadow visible to the page");
    assert.equal(bad.hasShadow, false, "no shadow art was attached on fail-closed");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
