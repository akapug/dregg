// Fixture test for the verifiable choose-your-own-adventure (`<dregg-story>`).
//
// Serves a static page carrying <dregg-story> elements, loads it in a real
// (headless) Chromium via Playwright, and asserts the whole play path — the north
// star (a reader picks a choice as a verified turn; a stranger replays the receipt
// chain):
//   - the element upgrades → CLOSED shadow (the page cannot read it);
//   - READ + VERIFY are the FREE tier: passage 1's prose renders + a replay-verified
//     badge, with NO custody needed;
//   - the choices render as buttons (a GATED choice is shown but disabled);
//   - a GATED/unavailable choice is REFUSED (fail-closed, no advance, no prompt);
//   - DENY consent → the choice is refused, nothing advances (custody is load-bearing);
//   - APPROVE consent → the story advances to passage 2 (receiptCount grows, the
//     commitment moves), and on to the ending (a 3-passage traversal);
//   - the STRANGER'S CHECK: an independent light-client REPLAYS the receipt chain true;
//   - a READ-ONLY story (no custody) still renders + verifies, but choosing degrades
//     to the honest "connect your cipherclerk to play" note;
//   - a malformed addr FAILS CLOSED (original link + warning, no render).
//
// The engine + element are the shipping code path; only the transport hop + consent
// are shimmed, and the wasm StoryWorld is stood in by an in-memory one (see harness.ts).
//
// Run:  node --test tests/dregg-story/run.mjs

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

// Browser-side snapshot: read the closed-shadow registry (test-only) + reflected
// attributes for one <dregg-story>.
const SNAPSHOT = `
window.__snap = function snap(id) {
  const el = document.getElementById(id);
  const roots = window.__dreggStoryRoots;
  const root = roots && roots.get(el);
  const buttons = root ? [...root.querySelectorAll('button[data-choice]')] : [];
  return {
    src: el.getAttribute("src"),
    trust: el.getAttribute("trust"),
    verified: el.hasAttribute("verified"),
    error: el.hasAttribute("error"),
    passage: el.getAttribute("passage"),
    readonly: el.hasAttribute("readonly"),
    receipts: el.getAttribute("receipts"),
    commitment: el.getAttribute("commitment"),
    choiceRefused: el.hasAttribute("choice-refused"),
    pageSeesShadow: el.shadowRoot !== null,            // closed ⇒ always false
    hasFallbackLink: !!el.querySelector('a[href^="https://dregg.net/d/story/"]'),
    hasWarning: !!el.querySelector(".dregg-fallback-warning"),
    prose: root ? (root.querySelector(".passage")?.textContent || "").trim() : null,
    badge: root ? (root.querySelector(".badge")?.textContent || "").trim() : null,
    note: root ? (root.querySelector(".note")?.textContent || "").trim() : null,
    roNote: root ? (root.querySelector(".readonly-note")?.textContent || "").trim() : null,
    choiceCount: buttons.length,
    choiceTexts: buttons.map((b) => b.textContent),
    enabledChoices: buttons.filter((b) => !b.disabled).length,
    gatedDisabled: buttons.filter((b) => b.classList.contains("gated")).every((b) => b.disabled),
  };
};
window.__clickChoice = function (id, index) {
  const root = window.__dreggStoryRoots.get(document.getElementById(id));
  const btn = root.querySelector('button[data-choice="' + index + '"]');
  btn.disabled = false;   // bypass the DOM gate to prove the ENGINE also refuses
  btn.click();
};
`;

test("dregg-story: render → choose → advance → stranger-replays; gated refused; consent load-bearing; read-only degrade; fail-closed", async () => {
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

    // All three elements settle a trust state (verified or error).
    await page.waitForFunction(
      () => {
        const els = [...document.querySelectorAll("dregg-story")];
        return els.length === 3 && els.every((el) => el.hasAttribute("verified") || el.hasAttribute("error"));
      },
      null,
      { timeout: 15000 },
    );

    // ── READ + VERIFY (the FREE tier): passage 1 renders, verified, replay badge.
    let s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.pageSeesShadow, false, "closed shadow hides the render from the page");
    assert.equal(s.verified, true, "[verified] reflected");
    assert.equal(s.error, false, "no [error]");
    assert.equal(s.trust, "extension", "trust=extension");
    assert.equal(s.passage, "the-fork", "[passage] reflects the genesis passage");
    assert.match(s.prose, /fork in the drifting mist/i, "passage 1 prose renders");
    assert.match(s.badge, /replay-verified/i, "honest replay-verified badge (READ+VERIFY free tier)");

    // The choices render; the GATED choice is SHOWN but disabled.
    assert.equal(s.choiceCount, 2, "both choices render (a gated one is not hidden)");
    assert.equal(s.enabledChoices, 1, "only the available choice is takeable");
    assert.equal(s.gatedDisabled, true, "the gated choice is shown but disabled");
    assert.equal(s.readonly, false, "playable story is not read-only");

    const commitmentBefore = s.commitment;
    const receiptsBefore = Number(s.receipts);
    assert.equal(receiptsBefore, 0, "no receipts before any choice");
    assert.ok(commitmentBefore && /^[0-9a-f]+$/i.test(commitmentBefore), "the genesis commitment is hex");

    // ── GATED CHOICE REFUSED: the ENGINE fails closed on the locked gate (index 1),
    //    without prompting, and nothing advances.
    const gated = await page.evaluate((uri) => window.__dreggStoryChoose(uri, 1), "dregg://story/b3_a11ce0");
    assert.equal(gated.refused, true, "gated choice refused by the engine");
    assert.match(gated.reason, /gated|unavailable/i, "refusal names the gating");
    assert.equal(gated.passage, "the-fork", "gated refusal did not advance the passage");
    assert.equal(Number(gated.receiptCount), receiptsBefore, "gated refusal produced no receipt");
    assert.equal(gated.commitment, commitmentBefore, "gated refusal did not move the commitment");

    // ── DENY CONSENT: choosing the AVAILABLE path is refused; nothing advances.
    await page.evaluate(() => (window.__DREGG_CONSENT = false));
    await page.evaluate(() => window.__clickChoice("story", 0));
    await page.waitForFunction(() => document.getElementById("story").hasAttribute("choice-refused"), null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.choiceRefused, true, "choice refused when consent denied");
    assert.match(s.note, /refused/i, "refusal surfaced in the view");
    assert.equal(s.passage, "the-fork", "no advance when consent denied");
    assert.equal(s.commitment, commitmentBefore, "no commitment move when consent denied");
    assert.equal(Number(s.receipts), receiptsBefore, "no receipt when consent denied");

    // ── APPROVE CONSENT + CHOOSE: a real verified turn → passage 2.
    await page.evaluate(() => (window.__DREGG_CONSENT = true));
    await page.evaluate(() => window.__clickChoice("story", 0));
    await page.waitForFunction(() => document.getElementById("story").getAttribute("passage") === "the-bright-path", null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.choiceRefused, false, "not refused with consent");
    assert.equal(s.verified, true, "still verified after the turn");
    assert.equal(s.passage, "the-bright-path", "advanced to passage 2");
    assert.match(s.prose, /lantern-lit hollow/i, "passage 2 prose renders");
    const receiptsAfter = Number(s.receipts);
    assert.ok(receiptsAfter > receiptsBefore, `a receipt was produced (${receiptsBefore} → ${receiptsAfter})`);
    assert.notEqual(s.commitment, commitmentBefore, "the story commitment moved");
    assert.ok(/^[0-9a-f]+$/i.test(s.commitment), "the new commitment is hex");

    // ── THE STRANGER'S CHECK: an INDEPENDENT light-client REPLAYS the receipt chain.
    const lc = await page.evaluate((uri) => window.__dreggStoryVerify(uri), "dregg://story/b3_a11ce0");
    assert.equal(lc.ok, true, "light-client verify ran");
    assert.equal(lc.verified, true, "the stranger's replay verifies the receipt chain");
    assert.equal(lc.commitment, s.commitment, "the replayed commitment IS the current one");
    assert.equal(Number(lc.receiptCount), receiptsAfter, "the stranger sees the same receipt tape");

    // ── ADVANCE AGAIN → the ending (a full 3-passage traversal).
    await page.evaluate(() => window.__clickChoice("story", 0));
    await page.waitForFunction(() => document.getElementById("story").getAttribute("passage") === "the-tower", null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.passage, "the-tower", "reached the ending passage");
    assert.equal(s.choiceCount, 0, "the ending offers no choices");
    assert.equal(Number(s.receipts), receiptsAfter + 1, "the receipt tape grew again");
    assert.equal(s.verified, true, "the finished story still verifies");

    // ── READ-ONLY story: renders + verifies (free tier), but choosing degrades to
    //    the honest note; the choice button is disabled (no custody).
    const ro = await page.evaluate(() => window.__snap("roStory"));
    assert.equal(ro.verified, true, "read-only story still verifies (READ+VERIFY free)");
    assert.match(ro.badge, /replay-verified/i, "read-only story shows the replay-verified badge");
    assert.match(ro.prose, /fork in the drifting mist/i, "read-only story renders its prose");
    assert.equal(ro.readonly, true, "[readonly] reflected when no custody");
    assert.equal(ro.enabledChoices, 0, "no choice is takeable without custody");
    assert.match(ro.roNote, /connect your cipherclerk/i, "honest read-only note shown");

    // ── FAIL-CLOSED: the malformed addr rendered NOTHING; link + warning kept.
    const bad = await page.evaluate(() => window.__snap("badStory"));
    assert.equal(bad.verified, false, "bad: not verified");
    assert.equal(bad.error, true, "bad: [error] set");
    assert.equal(bad.trust, "none", "bad: trust=none");
    assert.equal(bad.prose, null, "bad: NOTHING rendered (no shadow)");
    assert.ok(bad.hasFallbackLink, "bad: original link kept as fallback");
    assert.ok(bad.hasWarning, "bad: visible warning shown");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
