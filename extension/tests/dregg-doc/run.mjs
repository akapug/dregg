// Fixture test for the verifiable-document authoring path (`<dregg-doc>`).
//
// Serves a static page carrying a <dregg-doc> on a document that ALREADY holds a
// first-class CONFLICT, loads it in a real (headless) Chromium via Playwright,
// and asserts the whole authoring path — the north star (a person authors a
// verifiable document a stranger can check):
//   - the element upgrades → CLOSED shadow (the page cannot read it);
//   - the CONFLICT renders BOTH alternatives, attributed, side by side — NEITHER
//     hidden (conflict-as-first-class-state);
//   - a click resolves ONE alternative and PUBLISHES a real verified turn (routed
//     through consent) → a receipt is produced;
//   - the committed heap_root MATCHES substrate_commit of the resolved doc
//     (`boundaryMatchesProjection` — the equality the receipt bound at limb 28);
//   - an INDEPENDENT LIGHT-CLIENT check re-verifies that heap_root;
//   - consent is load-bearing: deny it → the publish is refused, nothing committed,
//     and the conflict is STILL shown (both alternatives);
//   - a malformed addr FAILS CLOSED (original link + warning, no render).
//
// The engine runs the REAL wasm DocCollabWorld; the element uses its real closed
// shadow + message transport. Only the transport hop + consent are shimmed
// in-page (see harness.ts).
//
// Run:  node --test tests/dregg-doc/run.mjs

import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const EXT_ROOT = path.resolve(__dirname, "..", "..");

const MIME = {
  ".js": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
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
  const glue = await readFile(path.join(EXT_ROOT, "dregg_wasm.js"), "utf8");
  const wasm = await readFile(path.join(EXT_ROOT, "dregg_wasm_bg.wasm"));

  const server = http.createServer((req, res) => {
    const url = req.url.split("?")[0];
    const send = (body, type) => {
      res.writeHead(200, { "content-type": type });
      res.end(body);
    };
    if (url === "/" || url === "/fixture.html") return send(fixture, MIME[".html"]);
    if (url === "/harness.js") return send(harnessJs, MIME[".js"]);
    if (url === "/dregg_wasm.js") return send(glue, MIME[".js"]);
    if (url === "/dregg_wasm_bg.wasm") return send(wasm, MIME[".wasm"]);
    res.writeHead(404);
    res.end("not found");
  });
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  const { port } = server.address();
  return { server, base: `http://127.0.0.1:${port}` };
}

// Browser-side snapshot: read the closed-shadow registry (test-only) + reflected
// attributes for one <dregg-doc>.
const SNAPSHOT = `
window.__snap = function snap(id) {
  const el = document.getElementById(id);
  const roots = window.__dreggDocRoots;
  const root = roots && roots.get(el);
  return {
    src: el.getAttribute("src"),
    trust: el.getAttribute("trust"),
    verified: el.hasAttribute("verified"),
    error: el.hasAttribute("error"),
    conflict: el.hasAttribute("conflict"),
    alternatives: el.getAttribute("alternatives"),
    receipts: el.getAttribute("receipts"),
    commitment: el.getAttribute("commitment"),
    substrateMatches: el.hasAttribute("substrate-matches"),
    publishRefused: el.hasAttribute("publish-refused"),
    pageSeesShadow: el.shadowRoot !== null,            // closed ⇒ always false
    hasFallbackLink: !!el.querySelector('a[href^="https://dregg.net/d/doc/"]'),
    hasWarning: !!el.querySelector(".dregg-fallback-warning"),
    doc: root ? (root.querySelector(".doc")?.textContent || "").trim() : null,
    docHtml: root ? (root.querySelector(".doc")?.innerHTML || "") : null,
    badge: root ? (root.querySelector(".badge")?.textContent || "").trim() : null,
    note: root ? (root.querySelector(".note")?.textContent || "").trim() : null,
    resolveButtons: root ? root.querySelectorAll('.deos-button[data-turn="resolve"]').length : null,
  };
};
`;

test("dregg-doc: conflict shows both alternatives → resolve → publish → heap_root==substrate_commit → light-client re-verifies; consent load-bearing; fail-closed", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push(String(e)));
    await page.addInitScript(SNAPSHOT);
    await page.goto(`${base}/fixture.html`);

    // Boot: wasm loaded, engine + element wired.
    await page.waitForFunction(() => window.__DREGG_READY === true || window.__DREGG_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__DREGG_ERROR || null);
    assert.equal(bootErr, null, `harness boot error: ${bootErr}`);

    // Both elements settle a trust state (verified or error).
    await page.waitForFunction(
      () => {
        const els = [...document.querySelectorAll("dregg-doc")];
        return els.length === 2 && els.every((el) => el.hasAttribute("verified") || el.hasAttribute("error"));
      },
      null,
      { timeout: 15000 },
    );

    // ── THE VALID DOCUMENT: verified, and it arrives carrying a CONFLICT.
    let doc = await page.evaluate(() => window.__snap("doc"));
    assert.equal(doc.pageSeesShadow, false, "closed shadow hides the render from the page");
    assert.equal(doc.verified, true, "[verified] reflected");
    assert.equal(doc.error, false, "no [error]");
    assert.equal(doc.trust, "extension", "trust=extension");
    assert.match(doc.badge, /verified by your cipherclerk/, "honest badge");
    assert.equal(doc.conflict, true, "the document carries a first-class conflict");

    // ── CONFLICT AS FIRST-CLASS STATE: BOTH alternatives render, attributed,
    //    NEITHER hidden. (alice + bob authored concurrently.)
    assert.equal(doc.alternatives, "2", "two live alternatives");
    assert.match(doc.doc, /alice/i, "alice's alternative is attributed");
    assert.match(doc.doc, /bob/i, "bob's alternative is attributed");
    assert.match(doc.doc, /independent patches commute/i, "alice's text renders");
    assert.match(doc.doc, /categorical pushout/i, "bob's text renders — NEITHER alternative is hidden");
    assert.ok(doc.resolveButtons >= 1, "a resolution affordance per choice is rendered");

    const commitmentBefore = doc.commitment;
    const receiptsBefore = Number(doc.receipts);
    assert.ok(commitmentBefore && /^[0-9a-f]+$/i.test(commitmentBefore), "the pre-publish heap_root is a hex commitment");

    // ── DENY CONSENT: the publish is refused, nothing commits, conflict STILL shown.
    await page.evaluate(() => (window.__DREGG_CONSENT = false));
    await page.evaluate(() => {
      window.__dreggDocRoots.get(document.getElementById("doc")).querySelector('.deos-button[data-turn="resolve"]').click();
    });
    await page.waitForFunction(() => document.getElementById("doc").hasAttribute("publish-refused"), null, { timeout: 15000 });
    doc = await page.evaluate(() => window.__snap("doc"));
    assert.equal(doc.publishRefused, true, "publish refused when consent denied");
    assert.match(doc.note, /refused/i, "refusal surfaced in the view");
    assert.equal(doc.conflict, true, "conflict STILL shown after a denied publish (not hidden)");
    assert.equal(doc.commitment, commitmentBefore, "no boundary move when consent denied");
    assert.equal(Number(doc.receipts), receiptsBefore, "no receipt when consent denied");

    // ── APPROVE CONSENT + RESOLVE + PUBLISH: a real verified turn.
    await page.evaluate(() => (window.__DREGG_CONSENT = true));
    await page.evaluate(() => {
      window.__dreggDocRoots.get(document.getElementById("doc")).querySelector('.deos-button[data-turn="resolve"]').click();
    });
    await page.waitForFunction(
      () => {
        const el = document.getElementById("doc");
        return !el.hasAttribute("conflict") && el.hasAttribute("substrate-matches");
      },
      null,
      { timeout: 15000 },
    );
    doc = await page.evaluate(() => window.__snap("doc"));

    // The conflict collapsed to the published, resolved reading.
    assert.equal(doc.conflict, false, "conflict resolved (collapsed) after publish");
    assert.equal(doc.publishRefused, false, "publish not refused with consent");
    assert.equal(doc.verified, true, "still verified after publish");

    // A RECEIPT was produced (the audit tape grew: genesis publish + this publish).
    const receiptsAfter = Number(doc.receipts);
    assert.ok(receiptsAfter > receiptsBefore, `a receipt was produced (${receiptsBefore} → ${receiptsAfter})`);

    // The committed heap_root MOVED to the resolved document's commitment...
    assert.notEqual(doc.commitment, commitmentBefore, "the umem boundary (heap_root) moved to the resolved document");
    assert.ok(/^[0-9a-f]+$/i.test(doc.commitment), "the new heap_root is a hex commitment");

    // ...and it MATCHES substrate_commit of the resolved doc (the equality the
    // receipt bound at limb 28 — an independent recompute of substrate_commit
    // equals the committed heap_root).
    assert.equal(doc.substrateMatches, true, "committed heap_root == substrate_commit(resolved)");

    // ── THE STRANGER'S CHECK: an INDEPENDENT light-client re-verify of that
    //    heap_root (recomputes substrate_commit from the graph off the render path).
    const lc = await page.evaluate((uri) => window.__dreggLightClientVerify(uri), "dregg://doc/b3_d0cface");
    assert.equal(lc.ok, true, "light-client verify ran");
    assert.equal(lc.verified, true, "light client re-verifies the committed heap_root");
    assert.equal(lc.commitment, doc.commitment, "the light-client-verified heap_root IS the published commitment");
    assert.equal(Number(lc.receiptCount), receiptsAfter, "the light client sees the same receipt tape");

    // ── FAIL-CLOSED: the malformed addr rendered NOTHING; link + warning kept.
    const bad = await page.evaluate(() => window.__snap("baddoc"));
    assert.equal(bad.verified, false, "bad: not verified");
    assert.equal(bad.error, true, "bad: [error] set");
    assert.equal(bad.trust, "none", "bad: trust=none");
    assert.equal(bad.doc, null, "bad: NOTHING rendered (no shadow)");
    assert.ok(bad.hasFallbackLink, "bad: original link kept as fallback");
    assert.ok(bad.hasWarning, "bad: visible warning shown");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
