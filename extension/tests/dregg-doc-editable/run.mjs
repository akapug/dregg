// Fixture test for the FREE-TEXT authoring path (`<dregg-doc editable>`).
//
// Serves a static page carrying a <dregg-doc editable> over a real DocTextWorld,
// loads it in a real (headless) Chromium via Playwright, and asserts the whole
// free-text authoring path — the north star (a person authors a verifiable
// document a stranger can check) for FREE TEXT, not just picking an alternative:
//   - the element upgrades → CLOSED shadow with a contenteditable prose region
//     (the page cannot read it);
//   - typing a replacement ("brown" → "RED") produces a MINIMAL patch — 1 atom
//     added + 1 tombstoned (the surrounding words KEPT by their atom ids), NOT a
//     four-token rewrite;
//   - THE KEYED RECONCILER preserves the caret across the repaint (the cursor ends
//     right after "RED", never reset to the start);
//   - a "publish" affordance commits the accumulated edits as a real verified turn
//     (routed through consent) → a receipt lands; the committed heap_root MATCHES
//     substrate_commit of the edited doc (`boundaryMatchesProjection`);
//   - an INDEPENDENT LIGHT-CLIENT check re-verifies that heap_root;
//   - consent is load-bearing: deny it → the publish is refused, nothing committed;
//   - a malformed addr FAILS CLOSED (original link + warning, no editable render).
//
// The engine runs the REAL wasm DocTextWorld; the element uses its real closed
// shadow + message transport. Only the transport hop + consent are shimmed
// in-page (see harness.ts).
//
// Run:  node --test tests/dregg-doc-editable/run.mjs

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

// Browser-side helpers over the closed-shadow registry (test-only).
const SNAPSHOT = `
window.__editableOf = function(id) {
  const el = document.getElementById(id);
  const root = window.__dreggDocRoots && window.__dreggDocRoots.get(el);
  return root ? root.querySelector(".doc-edit") : null;
};
window.__selOf = function(root) {
  return (root.getSelection ? root.getSelection() : document.getSelection());
};
window.__snap = function snap(id) {
  const el = document.getElementById(id);
  const roots = window.__dreggDocRoots;
  const root = roots && roots.get(el);
  const editable = root ? root.querySelector(".doc-edit") : null;
  return {
    src: el.getAttribute("src"),
    trust: el.getAttribute("trust"),
    verified: el.hasAttribute("verified"),
    error: el.hasAttribute("error"),
    dirty: el.hasAttribute("dirty"),
    atomsAdded: el.getAttribute("atoms-added"),
    atomsTombstoned: el.getAttribute("atoms-tombstoned"),
    receipts: el.getAttribute("receipts"),
    commitment: el.getAttribute("commitment"),
    substrateMatches: el.hasAttribute("substrate-matches"),
    publishRefused: el.hasAttribute("publish-refused"),
    pageSeesShadow: el.shadowRoot !== null,            // closed ⇒ always false
    hasFallbackLink: !!el.querySelector('a[href^="https://dregg.net/d/doc/"]'),
    hasWarning: !!el.querySelector(".dregg-fallback-warning"),
    text: editable ? (editable.textContent || "") : null,
    badge: root ? (root.querySelector(".badge")?.textContent || "").trim() : null,
    note: root ? (root.querySelector(".note")?.textContent || "").trim() : null,
    patchinfo: root ? (root.querySelector(".patchinfo")?.textContent || "").trim() : null,
    hasEditable: !!editable,
    publishButtons: root ? root.querySelectorAll('button[data-turn="publish-text"]').length : null,
  };
};
// Set a selection over [start,end) of the editable's single text node (closed-shadow scoped).
window.__selectRange = function(id, start, end) {
  const el = document.getElementById(id);
  const root = window.__dreggDocRoots.get(el);
  const editable = root.querySelector(".doc-edit");
  editable.focus();
  const node = editable.firstChild;
  const sel = window.__selOf(root);
  const range = document.createRange();
  range.setStart(node, start);
  range.setEnd(node, end);
  sel.removeAllRanges();
  sel.addRange(range);
  return editable.textContent;
};
// Read the caret's character offset within the editable (the keyed-reconciler probe).
window.__caret = function(id) {
  const el = document.getElementById(id);
  const root = window.__dreggDocRoots.get(el);
  const editable = root.querySelector(".doc-edit");
  const sel = window.__selOf(root);
  if (!sel || sel.rangeCount === 0) return null;
  const range = sel.getRangeAt(0);
  if (!editable.contains(range.startContainer) && range.startContainer !== editable) return null;
  const pre = range.cloneRange();
  pre.selectNodeContents(editable);
  pre.setEnd(range.startContainer, range.startOffset);
  return pre.toString().length;
};
window.__clickPublish = function(id) {
  const el = document.getElementById(id);
  const root = window.__dreggDocRoots.get(el);
  root.querySelector('button[data-turn="publish-text"]').click();
};
`;

test("dregg-doc editable: type → minimal patch → caret preserved → publish-through-consent → light-client verify; deny → no publish; fail-closed", async () => {
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

    // ── THE VALID DOCUMENT: verified, editable, seeded prose in the CLOSED shadow.
    let doc = await page.evaluate(() => window.__snap("doc"));
    assert.equal(doc.pageSeesShadow, false, "closed shadow hides the editable from the page");
    assert.equal(doc.verified, true, "[verified] reflected (genesis seed published)");
    assert.equal(doc.error, false, "no [error]");
    assert.equal(doc.trust, "extension", "trust=extension");
    assert.match(doc.badge, /verified by your cipherclerk/, "honest badge");
    assert.equal(doc.hasEditable, true, "a contenteditable prose region is rendered");
    assert.equal(doc.publishButtons, 1, "a publish affordance is rendered");
    assert.equal(doc.text, "the quick brown fox", "the seed prose is shown");
    assert.equal(doc.dirty, false, "no unpublished edits at load");

    const commitmentSeed = doc.commitment;
    const receiptsSeed = Number(doc.receipts);
    assert.ok(commitmentSeed && /^[0-9a-f]+$/i.test(commitmentSeed), "the seed heap_root is a hex commitment");
    assert.equal(receiptsSeed, 1, "the genesis seed published as one verified turn");

    // ── TYPE A FREE-TEXT EDIT: select "brown" and type "RED" (a real keyboard, so
    //    real input events → the reconciler runs). "the quick " is 10 chars; "brown"
    //    occupies [10,15).
    await page.evaluate(() => window.__selectRange("doc", 10, 15));
    await page.keyboard.type("RED", { delay: 60 });
    await page.waitForFunction(
      () => window.__editableOf("doc")?.textContent === "the quick RED fox",
      null,
      { timeout: 15000 },
    );

    doc = await page.evaluate(() => window.__snap("doc"));
    assert.equal(doc.text, "the quick RED fox", "the edit applied — the prose now reads 'RED'");

    // ── MINIMAL PATCH (NOT A REWRITE): the LAST edit added exactly ONE atom and
    //    tombstoned exactly ONE — the surrounding words kept their atom ids. A
    //    full rewrite of a four-token doc would show four adds.
    assert.equal(doc.atomsAdded, "1", "one atom added (minimal, not a rewrite)");
    assert.equal(doc.atomsTombstoned, "1", "one atom tombstoned (minimal, not a rewrite)");
    assert.match(doc.patchinfo, /minimal patch, not a rewrite/i, "the minimal-patch summary is surfaced");
    assert.equal(doc.dirty, true, "the edit is unpublished (dirty) — the boundary lags until publish");

    // ── THE KEYED RECONCILER: the caret survived the repaint. After typing "RED"
    //    the cursor sits right after it (offset 13 = len("the quick RED")), NOT reset
    //    to 0 by the repaint.
    const caret = await page.evaluate(() => window.__caret("doc"));
    assert.equal(caret, 13, "the caret is preserved across the repaint (right after 'RED', not reset to 0)");

    // The committed boundary has NOT moved yet (the edit is not a verified turn until publish).
    assert.equal(doc.commitment, commitmentSeed, "the umem boundary still binds the seed until publish");
    assert.equal(Number(doc.receipts), receiptsSeed, "no new receipt for an unpublished edit");

    // ── DENY CONSENT: the publish is refused, nothing commits.
    await page.evaluate(() => (window.__DREGG_CONSENT = false));
    await page.evaluate(() => window.__clickPublish("doc"));
    await page.waitForFunction(() => document.getElementById("doc").hasAttribute("publish-refused"), null, { timeout: 15000 });
    doc = await page.evaluate(() => window.__snap("doc"));
    assert.equal(doc.publishRefused, true, "publish refused when consent denied");
    assert.match(doc.note, /refused/i, "refusal surfaced in the view");
    assert.equal(doc.commitment, commitmentSeed, "no boundary move when consent denied");
    assert.equal(Number(doc.receipts), receiptsSeed, "no receipt when consent denied");
    assert.equal(doc.dirty, true, "the edit is still unpublished after a denied publish");

    // ── APPROVE CONSENT + PUBLISH: a real verified turn commits the edits.
    await page.evaluate(() => (window.__DREGG_CONSENT = true));
    await page.evaluate(() => window.__clickPublish("doc"));
    await page.waitForFunction(
      () => {
        const el = document.getElementById("doc");
        return el.hasAttribute("substrate-matches") && !el.hasAttribute("dirty");
      },
      null,
      { timeout: 15000 },
    );
    doc = await page.evaluate(() => window.__snap("doc"));

    assert.equal(doc.publishRefused, false, "publish not refused with consent");
    assert.equal(doc.verified, true, "still verified after publish");
    assert.equal(doc.dirty, false, "no unpublished edits after publish");

    // A RECEIPT was produced (genesis seed publish + this edit publish).
    const receiptsAfter = Number(doc.receipts);
    assert.ok(receiptsAfter > receiptsSeed, `a receipt was produced (${receiptsSeed} → ${receiptsAfter})`);

    // The committed heap_root MOVED to the edited document's commitment...
    assert.notEqual(doc.commitment, commitmentSeed, "the umem boundary (heap_root) moved to the edited document");
    assert.ok(/^[0-9a-f]+$/i.test(doc.commitment), "the new heap_root is a hex commitment");

    // ...and it MATCHES substrate_commit of the edited doc (the equality the receipt bound).
    assert.equal(doc.substrateMatches, true, "committed heap_root == substrate_commit(edited)");

    // ── THE STRANGER'S CHECK: an INDEPENDENT light-client re-verify of that heap_root.
    const lc = await page.evaluate((uri) => window.__dreggTextLightClientVerify(uri), "dregg://doctext/b3_ed17ab1e");
    assert.equal(lc.ok, true, "light-client verify ran");
    assert.equal(lc.verified, true, "light client re-verifies the committed heap_root");
    assert.equal(lc.commitment, doc.commitment, "the light-client-verified heap_root IS the published commitment");
    assert.equal(Number(lc.receiptCount), receiptsAfter, "the light client sees the same receipt tape");

    // ── FAIL-CLOSED: the malformed addr rendered NO editable region; link + warning kept.
    const bad = await page.evaluate(() => window.__snap("baddoc"));
    assert.equal(bad.verified, false, "bad: not verified");
    assert.equal(bad.error, true, "bad: [error] set");
    assert.equal(bad.trust, "none", "bad: trust=none");
    assert.equal(bad.hasEditable, false, "bad: NO editable region rendered (no shadow)");
    assert.ok(bad.hasFallbackLink, "bad: original link kept as fallback");
    assert.ok(bad.hasWarning, "bad: visible warning shown");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
