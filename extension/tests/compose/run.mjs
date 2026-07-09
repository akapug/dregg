// Fixture test for the composition delivery layer — `<dregg-embed>` (whole child
// cell, recursive) and `<dregg-transclude>` (value quote).
//
// Serves a static page with author-placed <dregg-embed>/<dregg-transclude> tags,
// loads it in a real (headless) Chromium via Playwright, and asserts:
//   - the recursive fold: an embed of a cell that itself embeds a grandchild
//     renders as NESTED closed shadow roots;
//   - DARKENING WITHHOLDS BYTES: an out-of-cap child renders only its citation,
//     and the withheld bytes are NOT anywhere in the shadow;
//   - a CYCLE is a first-class STATE (not a hang / stack overflow);
//   - UNRESOLVED / UNBOUND states render (unbound HEALS on rebind + refresh);
//   - a PINNED embed renders, marked frozen;
//   - a TRANSCLUDE shows a VERIFIED value snapshot, and FAILS CLOSED on a bad quote;
//   - every render is a CLOSED shadow the page cannot read.
//
// Run:  node --test tests/compose/run.mjs

import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

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
    if (url === "/" || url === "/fixture.html") {
      res.writeHead(200, { "content-type": "text/html; charset=utf-8" });
      return res.end(fixture);
    }
    if (url === "/harness.js") {
      res.writeHead(200, { "content-type": "text/javascript; charset=utf-8" });
      return res.end(harnessJs);
    }
    res.writeHead(404);
    res.end("not found");
  });
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  const { port } = server.address();
  return { server, base: `http://127.0.0.1:${port}` };
}

// Browser-side: drill through the closed-shadow registry into a nested tree.
// Installed as an init script so `drill` is a global across every evaluate call.
const DRILL = `
window.drill = function drill(el) {
  const roots = window.__dreggComposeRoots;
  const root = roots && roots.get(el);
  const node = {
    tag: el.tagName.toLowerCase(),
    src: el.getAttribute("src"),
    state: el.getAttribute("state"),
    verified: el.hasAttribute("verified"),
    error: el.hasAttribute("error"),
    readonly: el.hasAttribute("readonly"),
    trust: el.getAttribute("trust"),
    pageSeesShadow: el.shadowRoot !== null,   // closed ⇒ always false
    html: root ? root.innerHTML : null,        // full shadow html (test-only read)
    text: root ? (root.textContent || "") : null,
    children: [],
  };
  if (root) {
    for (const c of root.querySelectorAll("dregg-embed, dregg-transclude")) {
      // Only DIRECT descendants of THIS shadow (not deeper ones re-listed).
      if ((roots.get(c)) && c.getRootNode() === root) node.children.push(drill(c));
    }
  }
  return node;
};
`;

test("composition: recursive embed, darkening withholds bytes, cycle-is-a-state, transclude verified+fail-closed", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push(String(e)));
    await page.addInitScript(DRILL);
    await page.goto(`${base}/fixture.html`);

    await page.waitForFunction(() => window.__DREGG_READY === true || window.__DREGG_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__DREGG_ERROR || null);
    assert.equal(bootErr, null, `harness boot error: ${bootErr}`);

    // Wait until the top-level elements have settled a state, AND the recursive /
    // cyclic subtrees have reached their leaves (nested embeds resolved).
    await page.waitForFunction(
      () => {
        const need = ["root", "secret", "cyclic", "gone", "named", "pinned", "quote", "badquote"];
        for (const id of need) {
          const el = document.getElementById(id);
          if (!el || !el.getAttribute("state")) return false;
        }
        // recursion reached the leaf, and the cycle reached its cycle-leaf.
        const roots = window.__dreggComposeRoots;
        const rootLeaf = roots.get(document.getElementById("root"))?.querySelector("dregg-embed");
        if (!rootLeaf || !rootLeaf.getAttribute("state")) return false;
        const b = roots.get(document.getElementById("cyclic"))?.querySelector("dregg-embed");
        const a2 = b && roots.get(b)?.querySelector("dregg-embed");
        if (!a2 || a2.getAttribute("state") !== "cycle") return false;
        return true;
      },
      null,
      { timeout: 15000 },
    );

    const tree = await page.evaluate(() => {
      const ids = ["root", "secret", "cyclic", "gone", "named", "pinned", "quote", "badquote"];
      const out = {};
      for (const id of ids) out[id] = drill(document.getElementById(id));
      return out;
    });

    const allNodes = [];
    const collect = (n) => { allNodes.push(n); n.children.forEach(collect); };
    Object.values(tree).forEach(collect);

    // ── THE SPLIT: no thin view is readable by the page (closed shadow).
    for (const n of allNodes) assert.equal(n.pageSeesShadow, false, `${n.src}: closed shadow hides render from page`);

    // ── RECURSION: root rendered → nested leaf embed rendered (nested shadows).
    const root = tree.root;
    assert.equal(root.state, "rendered", "root cell rendered");
    assert.equal(root.verified, true, "root reflects [verified]");
    assert.match(root.text, /SEARCHABLE_ROOT/, "root prose rendered");
    assert.equal(root.children.length, 1, "root shadow holds exactly one nested embed");
    const leaf = root.children[0];
    assert.equal(leaf.src, "dregg://cell/b3_leaf", "the nested embed points at the grandchild");
    assert.equal(leaf.state, "rendered", "grandchild rendered (recursive fold)");
    assert.match(leaf.text, /LEAFBYTES-grandchild/, "grandchild bytes rendered in ITS OWN shadow");
    // The grandchild bytes live only in the grandchild's shadow — the recursion
    // is genuine nested membranes, not a flattened single render.
    assert.doesNotMatch(root.html.replace(leaf.html, ""), /LEAFBYTES-grandchild/, "grandchild bytes are in the nested shadow, not the parent's");

    // ── DARKENING WITHHOLDS BYTES: citation shown, secret bytes NOWHERE.
    const secret = tree.secret;
    assert.equal(secret.state, "darkened", "out-of-cap child darkens");
    assert.equal(secret.verified, false, "darkened is not verified");
    assert.match(secret.text, /dregg:\/\/cell\/b3_secret/, "darkened keeps the citation/provenance");
    assert.doesNotMatch(secret.html, /SECRETBYTES/, "DARKENING WITHHOLDS BYTES: the withheld bytes are not in the shadow");
    // Belt-and-braces: the bytes are nowhere in the whole page either.
    const pageHtml = await page.evaluate(() => document.documentElement.outerHTML);
    assert.doesNotMatch(pageHtml, /SECRETBYTES/, "withheld bytes never reached the page at all");

    // ── CYCLE is a first-class STATE (we got here ⇒ no hang / stack overflow).
    const cyclic = tree.cyclic;
    assert.equal(cyclic.state, "rendered", "b3_a rendered");
    const b = cyclic.children[0];
    assert.equal(b.state, "rendered", "b3_b rendered");
    const a2 = b.children[0];
    assert.equal(a2.state, "cycle", "the loop back to b3_a is a CYCLE state");
    assert.match(a2.text, /cycle/i, "cycle surfaced honestly");
    assert.equal(a2.children.length, 0, "the cycle does not recurse further (terminates)");

    // ── UNRESOLVED: a real failure, surfaced with the link + [error].
    const gone = tree.gone;
    assert.equal(gone.state, "unresolved", "a missing cell is unresolved");
    assert.equal(gone.error, true, "unresolved sets [error]");
    assert.match(gone.text, /dregg:\/\/cell\/b3_missing/, "unresolved shows the dregg:// link");

    // ── PINNED: a frozen citation still renders, marked pinned.
    const pinned = tree.pinned;
    assert.equal(pinned.state, "rendered", "a pinned embed renders");
    assert.match(pinned.text, /pinned/i, "pinned is marked frozen in the citation");

    // ── UNBOUND → HEAL: unbound now, rendered after a rebind + refresh.
    const named = tree.named;
    assert.equal(named.state, "unbound", "a name binding to nothing is unbound");
    assert.equal(named.error, false, "unbound is a state, not an error");
    await page.evaluate(() => {
      window.__DREGG_HEAL_NAME();
      document.getElementById("named").refresh();
    });
    await page.waitForFunction(() => document.getElementById("named").getAttribute("state") === "rendered", null, { timeout: 10000 });
    const healed = await page.evaluate(() => drill(document.getElementById("named")));
    assert.equal(healed.state, "rendered", "unbound HEALS on rebind");
    assert.match(healed.text, /NOWBOUND-hero-figure/, "the rebound cell renders");

    // ── TRANSCLUDE: a VERIFIED value snapshot (not live, not editable).
    const quote = tree.quote;
    assert.equal(quote.tag, "dregg-transclude", "quote is a transclude");
    assert.equal(quote.state, "quoted", "verified quote rendered");
    assert.equal(quote.verified, true, "quote reflects [verified]");
    assert.equal(quote.readonly, true, "a quote is UNEDITABLE ([readonly])");
    assert.match(quote.text, /QUOTED-VALUE-snapshot-ok/, "the quoted value bytes are shown");
    assert.match(quote.text, /r_deadbeef/, "the citation/receipt provenance travels with the quote");
    assert.equal(quote.children.length, 0, "a value quote is not a subtree (no recursion)");

    // ── TRANSCLUDE FAIL-CLOSED: an unverifiable quote is never shown.
    const badquote = tree.badquote;
    assert.equal(badquote.state, "failed", "an unverifiable quote fails closed");
    assert.equal(badquote.verified, false, "a bad quote is not verified");
    assert.equal(badquote.error, true, "a bad quote sets [error]");
    assert.doesNotMatch(badquote.html, /BADQUOTE-should-never-render/, "the unverified bytes are NEVER shown");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
