// Fixture test for the COLLECTIVE choose-your-own-adventure
// (`<dregg-story collective>`) — the killer mode: the crowd votes each branch,
// the winner advances, in a browser tab.
//
// Serves a static page carrying <dregg-story collective> elements, loads it in a
// real (headless) Chromium via Playwright, and asserts the whole crowd-play path:
//   - the element upgrades → CLOSED shadow (the page cannot read it);
//   - READ + the TALLY are the FREE tier: passage 1's prose + a replay-verified
//     badge + the branch options at zero tally, with NO custody needed;
//   - openBranch shows 2 options + a zero tally;
//   - a VOTE is a CUSTODY WRITE: 3 distinct voters cast (each consent-gated, each
//     recorded under its own stable voter id); the tally updates;
//   - a DOUBLE vote by one voter is REFUSED (one vote per voter, fail-closed);
//   - a DENIED-consent vote is REFUSED, nothing counted (custody is load-bearing);
//   - a NO-CUSTODY viewer can READ + watch the tally but CANNOT vote (honest degrade);
//   - CLOSE → the winner advances as a real verified turn (receiptCount grows, the
//     commitment moves), and the element re-renders the NEW passage's branch;
//   - the STRANGER'S CHECK: an independent light-client REPLAYS the receipt chain true;
//   - a malformed addr FAILS CLOSED (original link + warning, no render).
//
// The engine + element are the shipping code path; only the transport hop, consent,
// and the voter identity are shimmed, and the wasm collective StoryWorld is stood in
// by an in-memory one (see harness.ts).
//
// Run:  node --test tests/dregg-story-collective/run.mjs

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
// attributes for one <dregg-story collective>.
const SNAPSHOT = `
window.__snap = function snap(id) {
  const el = document.getElementById(id);
  const roots = window.__dreggStoryRoots;
  const root = roots && roots.get(el);
  const opts = root ? [...root.querySelectorAll('button[data-vote]')] : [];
  const closeBtn = root ? root.querySelector('button[data-close]') : null;
  return {
    trust: el.getAttribute("trust"),
    verified: el.hasAttribute("verified"),
    error: el.hasAttribute("error"),
    passage: el.getAttribute("passage"),
    voting: el.hasAttribute("voting"),
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
    tally: root ? (root.querySelector(".tally")?.textContent || "").trim() : null,
    yourVote: root ? (root.querySelector(".yourvote")?.textContent || "").trim() : null,
    ending: root ? (root.querySelector(".ending")?.textContent || "").trim() : null,
    optCount: opts.length,
    optLabels: opts.map((b) => (b.querySelector(".opt-label")?.textContent || "")),
    optCounts: opts.map((b) => Number(b.querySelector(".opt-count")?.textContent || "0")),
    enabledOpts: opts.filter((b) => !b.disabled).length,
    closeDisabled: closeBtn ? closeBtn.disabled : null,
    closeHidden: closeBtn ? (closeBtn.style.display === "none") : null,
  };
};
window.__clickVote = function (id, choiceIndex) {
  const root = window.__dreggStoryRoots.get(document.getElementById(id));
  const btn = root.querySelector('button[data-vote][data-choice="' + choiceIndex + '"]');
  btn.disabled = false;   // bypass the DOM gate to prove the ENGINE also gates
  btn.click();
};
window.__clickClose = function (id) {
  const root = window.__dreggStoryRoots.get(document.getElementById(id));
  const btn = root.querySelector('button[data-close]');
  btn.disabled = false;
  btn.click();
};
`;

test("dregg-story collective: openBranch → crowd votes → tally → close → winner advances → stranger-replays; double-vote refused; consent load-bearing; no-custody read-only; fail-closed", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push(String(e)));
    await page.addInitScript(SNAPSHOT);
    await page.goto(`${base}/fixture.html`);

    const URI = "dregg://story/b3_c011ec";
    const RO_URI = "dregg://story/b3_b0b0b0";

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

    await page.evaluate(() => (window.__DREGG_CONSENT = true));

    // ── READ + TALLY (the FREE tier): passage 1 renders, verified, replay badge,
    //    2 options at ZERO tally.
    let s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.pageSeesShadow, false, "closed shadow hides the render from the page");
    assert.equal(s.verified, true, "[verified] reflected");
    assert.equal(s.error, false, "no [error]");
    assert.equal(s.trust, "extension", "trust=extension");
    assert.equal(s.passage, "the-fork", "[passage] reflects the genesis passage");
    assert.match(s.prose, /fork in the drifting mist/i, "passage 1 prose renders (free READ)");
    assert.match(s.badge, /replay-verified/i, "honest replay-verified badge (READ+tally free tier)");
    assert.equal(s.voting, true, "[voting] reflected at a live branch");
    assert.equal(s.readonly, false, "playable collective story is not read-only");
    assert.equal(s.optCount, 2, "the branch offers 2 options");
    assert.deepEqual(s.optCounts, [0, 0], "zero tally before any vote");
    assert.equal(s.enabledOpts, 2, "both options are votable (custody held)");
    assert.equal(s.closeDisabled, true, "close is disabled with no votes cast");
    const commitmentBefore = s.commitment;
    const receiptsBefore = Number(s.receipts);
    assert.equal(receiptsBefore, 0, "no receipts before any close");
    assert.ok(commitmentBefore && /^[0-9a-f]+$/i.test(commitmentBefore), "the genesis commitment is hex");

    // openBranch (the free tier, directly): 2 options + a zero tally.
    const open0 = await page.evaluate((uri) => window.__dreggStoryOpen(uri), URI);
    assert.equal(open0.ok, true, "openBranch ok");
    assert.equal(open0.options.length, 2, "openBranch shows 2 options");
    assert.equal(open0.total, 0, "openBranch zero tally");
    assert.equal(open0.custody, true, "openBranch reports custody");

    // ── THE CROWD VOTES (each a consent-gated custody write, recorded under a stable
    //    voter id). Two crowd members via the direct engine hook.
    const v1 = await page.evaluate(async (uri) => {
      window.__DREGG_VOTER = "voterB";
      return window.__dreggStoryVote(uri, 0);
    }, URI);
    assert.equal(v1.refused, false, "voterB's vote accepted");
    assert.equal(v1.voter, "voterB", "vote recorded under voterB's stable id");
    assert.equal(v1.tally[0].count, 1, "option 0 now has 1 vote");

    const v2 = await page.evaluate(async (uri) => {
      window.__DREGG_VOTER = "voterC";
      return window.__dreggStoryVote(uri, 1);
    }, URI);
    assert.equal(v2.refused, false, "voterC's vote accepted");
    assert.equal(v2.tally[1].count, 1, "option 1 now has 1 vote");

    // ── DOUBLE VOTE REFUSED: voterB tries again → one vote per voter, fail-closed.
    const dup = await page.evaluate(async (uri) => {
      window.__DREGG_VOTER = "voterB";
      return window.__dreggStoryVote(uri, 0);
    }, URI);
    assert.equal(dup.refused, true, "voterB's second vote refused (one vote per voter)");
    assert.match(dup.reason, /already voted/i, "refusal names the double-vote");
    assert.equal(dup.tally[0].count, 1, "the double vote did not inflate the tally");

    // ── DENY CONSENT (element path): a 4th voter is refused; nothing counted. The
    //    element still shows the crowd's tally (READ is free) — proving 1/1 so far.
    await page.evaluate(() => {
      window.__DREGG_CONSENT = false;
      window.__DREGG_VOTER = "voterD";
    });
    await page.evaluate(() => window.__clickVote("story", 1));
    await page.waitForFunction(() => document.getElementById("story").hasAttribute("choice-refused"), null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.choiceRefused, true, "vote refused when consent denied");
    assert.match(s.note, /refused/i, "refusal surfaced in the view");
    assert.deepEqual(s.optCounts, [1, 1], "denied vote counted nothing; the element sees the crowd's 1/1 tally");
    assert.equal(s.yourVote, "", "no 'your vote' recorded on a denied vote");

    // ── APPROVE + the ELEMENT'S OWN vote (voterA) → option 0 wins the round.
    await page.evaluate(() => {
      window.__DREGG_CONSENT = true;
      window.__DREGG_VOTER = "voterA";
    });
    await page.evaluate(() => window.__clickVote("story", 0));
    await page.waitForFunction(
      () => {
        const root = window.__dreggStoryRoots.get(document.getElementById("story"));
        const b = root && root.querySelector('button[data-vote][data-choice="0"] .opt-count');
        return b && b.textContent === "2";
      },
      null,
      { timeout: 15000 },
    );
    s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.choiceRefused, false, "not refused with consent");
    assert.deepEqual(s.optCounts, [2, 1], "the tally updated: option 0 leads 2–1");
    assert.match(s.yourVote, /Take the bright path/i, "'your vote' highlighted");
    assert.match(s.tally, /3 votes cast/i, "the running total shows 3 votes");
    assert.equal(s.closeDisabled, false, "close is enabled once votes are in");
    assert.equal(s.verified, true, "still verified through the voting");
    assert.equal(Number(s.receipts), receiptsBefore, "voting alone produces no receipt (pre-finalization tally)");
    assert.equal(s.commitment, commitmentBefore, "voting alone does not move the commitment");

    // ── NO-CUSTODY viewer: READ + tally free, but VOTING degrades honestly.
    const ro = await page.evaluate(() => window.__snap("roStory"));
    assert.equal(ro.verified, true, "read-only collective story still verifies (READ+tally free)");
    assert.match(ro.badge, /replay-verified/i, "read-only story shows the replay-verified badge");
    assert.match(ro.prose, /fork in the drifting mist/i, "read-only story renders its prose");
    assert.equal(ro.optCount, 2, "read-only story shows the branch options (READ)");
    assert.equal(ro.readonly, true, "[readonly] reflected when no custody");
    assert.equal(ro.enabledOpts, 0, "no option is votable without custody");
    assert.equal(ro.closeDisabled, true, "no close without custody");
    assert.match(ro.roNote, /connect your cipherclerk/i, "honest read-only note shown");
    const roVote = await page.evaluate((uri) => window.__dreggStoryVote(uri, 0), RO_URI);
    assert.equal(roVote.refused, true, "a no-custody vote fails closed at the engine");
    assert.match(roVote.reason, /no custody/i, "refusal names the missing custody");

    // ── CLOSE THE BRANCH (element): the winner advances as ONE verified turn.
    await page.evaluate(() => window.__clickClose("story"));
    await page.waitForFunction(() => document.getElementById("story").getAttribute("passage") === "the-bright-path", null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("story"));
    assert.equal(s.passage, "the-bright-path", "the winning choice advanced the story");
    assert.match(s.note, /the crowd chose "Take the bright path"/i, "the winner is announced honestly");
    assert.match(s.prose, /lantern-lit hollow/i, "the NEW passage's prose renders");
    assert.equal(s.optCount, 1, "the new passage's branch renders");
    assert.match(s.optLabels[0], /Push on to the tower/i, "the new branch option renders");
    assert.deepEqual(s.optCounts, [0], "the new round starts at zero tally");
    assert.equal(s.yourVote, "", "'your vote' cleared for the new round");
    const receiptsAfter = Number(s.receipts);
    assert.ok(receiptsAfter > receiptsBefore, `a receipt was produced (${receiptsBefore} → ${receiptsAfter})`);
    assert.notEqual(s.commitment, commitmentBefore, "the story commitment moved on close");
    assert.ok(/^[0-9a-f]+$/i.test(s.commitment), "the new commitment is hex");
    assert.equal(s.verified, true, "still verified after the advance");

    // ── THE STRANGER'S CHECK: an INDEPENDENT light-client REPLAYS the receipt chain.
    const lc = await page.evaluate((uri) => window.__dreggStoryVerify(uri), URI);
    assert.equal(lc.ok, true, "light-client verify ran");
    assert.equal(lc.verified, true, "the stranger's replay verifies the receipt chain");
    assert.equal(lc.commitment, s.commitment, "the replayed commitment IS the current one");
    assert.equal(Number(lc.receiptCount), receiptsAfter, "the stranger sees the same receipt tape");

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
