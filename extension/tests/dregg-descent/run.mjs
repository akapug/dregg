// Fixture test for The Descent, played in-tab (`<dregg-descent>`).
//
// Serves a static page carrying <dregg-descent> elements, loads it in a real
// (headless) Chromium via Playwright, and asserts the whole play path — the north
// star ("EVERY MOVE IS A RECEIPT": a move press is a verified turn on the in-tab
// executor; a stranger replays the receipt chain):
//   - the element upgrades → CLOSED shadow (the page cannot read it);
//   - OPEN + VERIFY are the FREE, PRIVATE tier: today's room prose renders, the run
//     state (hp/depth/warden) shows, a replay-verified badge shows, NO custody needed;
//   - the moves render as buttons (a GATED move — press-past a standing warden — is
//     shown but disabled);
//   - a GATED move is REFUSED in-band by the executor (fail-closed, no advance);
//   - a MOVE PRESS advances the in-tab run: the state updates (hp drops, turns grow,
//     the commitment moves), the whole thing staying verified;
//   - a CAREFUL run is driven to the hoard → WON, and the STRANGER'S CHECK replays true;
//   - a RECKLESS run DIES at the warden → the loss is an honest, replay-verifiable record;
//   - SETTLE degrades to the honest "opt-in named hook" note (the run stays private);
//   - a malformed addr FAILS CLOSED (original link + warning, no render).
//
// The engine + element are the shipping code path; only the transport hop is shimmed,
// and the wasm DescentWorld is stood in by an in-memory one (see harness.ts).
//
// Run:  node --test tests/dregg-descent/run.mjs

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
// attributes for one <dregg-descent>.
const SNAPSHOT = `
window.__snap = function snap(id) {
  const el = document.getElementById(id);
  const roots = window.__dreggDescentRoots;
  const root = roots && roots.get(el);
  const moves = root ? [...root.querySelectorAll('button[data-move]')] : [];
  return {
    src: el.getAttribute("src"),
    trust: el.getAttribute("trust"),
    verified: el.hasAttribute("verified"),
    error: el.hasAttribute("error"),
    room: el.getAttribute("room"),
    hp: el.getAttribute("hp"),
    depth: el.getAttribute("depth"),
    turns: el.getAttribute("turns"),
    won: el.hasAttribute("won"),
    dead: el.hasAttribute("dead"),
    ended: el.hasAttribute("ended"),
    commitment: el.getAttribute("commitment"),
    moveRefused: el.hasAttribute("move-refused"),
    published: el.hasAttribute("published"),
    pageSeesShadow: el.shadowRoot !== null,            // closed ⇒ always false
    hasFallbackLink: !!el.querySelector('a[href^="https://dregg.net/d/descent/"]'),
    hasWarning: !!el.querySelector(".dregg-fallback-warning"),
    title: root ? (root.querySelector(".title")?.textContent || "").trim() : null,
    prose: root ? (root.querySelector(".prose")?.textContent || "").trim() : null,
    status: root ? (root.querySelector(".status")?.textContent || "").trim() : null,
    badge: root ? (root.querySelector(".badge")?.textContent || "").trim() : null,
    note: root ? (root.querySelector(".note")?.textContent || "").trim() : null,
    settleNote: root ? (root.querySelector(".settle-note")?.textContent || "").trim() : null,
    moveCount: moves.length,
    moveTexts: moves.map((b) => b.textContent),
    enabledMoves: moves.filter((b) => !b.disabled).length,
    gatedDisabled: moves.filter((b) => b.classList.contains("gated")).every((b) => b.disabled),
  };
};
// Click a move by index (bypassing the DOM gate to prove the ENGINE also refuses).
window.__clickMove = function (id, index) {
  const root = window.__dreggDescentRoots.get(document.getElementById(id));
  const btn = root.querySelector('button[data-move="' + index + '"]');
  btn.disabled = false;
  btn.click();
};
// Click the first ENABLED move (a valid winning line: measured strikes drop the warden,
// then press past, take the key, seize the hoard).
window.__clickFirstEnabled = function (id) {
  const root = window.__dreggDescentRoots.get(document.getElementById(id));
  const btn = [...root.querySelectorAll('button[data-move]')].find((b) => !b.disabled);
  if (btn) { btn.click(); return Number(btn.getAttribute('data-move')); }
  return -1;
};
window.__clickAction = function (id, kind) {
  const root = window.__dreggDescentRoots.get(document.getElementById(id));
  root.querySelector('button[data-' + kind + ']').click();
};
`;

test("dregg-descent: open → play a move → advance in-tab → win → stranger-replays; gated refused; reckless dies; settle named-hook; fail-closed", async () => {
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

    // Both elements settle a trust state (verified or error).
    await page.waitForFunction(
      () => {
        const els = [...document.querySelectorAll("dregg-descent")];
        return els.length === 2 && els.every((el) => el.hasAttribute("verified") || el.hasAttribute("error"));
      },
      null,
      { timeout: 15000 },
    );

    // ── OPEN + VERIFY (the FREE, PRIVATE tier): today's room renders, verified, badge.
    let s = await page.evaluate(() => window.__snap("descent"));
    assert.equal(s.pageSeesShadow, false, "closed shadow hides the render from the page");
    assert.equal(s.verified, true, "[verified] reflected");
    assert.equal(s.error, false, "no [error]");
    assert.equal(s.trust, "extension", "trust=extension");
    assert.equal(s.room, "gate", "[room] reflects the opening gate");
    assert.match(s.title, /The Sunken Descent/i, "the day's beacon-drawn title renders");
    assert.match(s.prose, /iron warden bars the sunken gate/i, "the gate prose renders");
    assert.match(s.badge, /replay-verified/i, "honest replay-verified badge (PLAY+VERIFY free tier)");
    assert.match(s.status, /alive/i, "the run opens alive");

    // The moves render; the GATED move (press past a standing warden) is shown but disabled.
    assert.equal(s.moveCount, 4, "all gate moves render (a gated one is not hidden)");
    assert.ok(s.enabledMoves >= 1 && s.enabledMoves < 4, "only the available moves are takeable");
    assert.equal(s.gatedDisabled, true, "the gated move is shown but disabled");

    const commitmentBefore = s.commitment;
    const hpBefore = Number(s.hp);
    assert.equal(Number(s.turns), 1, "the genesis turn is committed at open");
    assert.equal(hpBefore, 50, "the gate opens at full HP");
    assert.ok(commitmentBefore && /^[0-9a-f]+$/i.test(commitmentBefore), "the genesis commitment is hex");

    // ── GATED MOVE REFUSED: the ENGINE fails closed in-band on "press past" (index 2)
    //    while the warden still stands — nothing advances.
    const gated = await page.evaluate((uri) => window.__dreggDescentAdvance(uri, 2), "dregg://descent/b3_de5ce0");
    assert.equal(gated.refused, true, "gated move refused by the executor");
    assert.match(gated.reason, /gated|unavailable/i, "refusal names the gating");
    assert.equal(gated.room, "gate", "gated refusal did not leave the gate");
    assert.equal(gated.commitment, commitmentBefore, "gated refusal did not move the commitment");

    // ── A MOVE PRESS ADVANCES THE IN-TAB RUN: measured strike (index 0) — a verified turn.
    await page.evaluate(() => window.__clickMove("descent", 0));
    await page.waitForFunction(() => Number(document.getElementById("descent").getAttribute("turns")) >= 2, null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("descent"));
    assert.equal(s.moveRefused, false, "the measured strike was not refused");
    assert.equal(s.verified, true, "still verified after the turn");
    assert.ok(Number(s.hp) < hpBefore, `hp dropped from the blow (${hpBefore} → ${s.hp})`);
    assert.ok(Number(s.turns) >= 2, "a real verified turn accrued");
    assert.notEqual(s.commitment, commitmentBefore, "the run commitment moved");
    assert.ok(/^[0-9a-f]+$/i.test(s.commitment), "the new commitment is hex");

    // ── THE STRANGER'S CHECK: an INDEPENDENT light-client REPLAYS the receipt chain.
    const lc = await page.evaluate((uri) => window.__dreggDescentVerify(uri), "dregg://descent/b3_de5ce0");
    assert.equal(lc.ok, true, "light-client verify ran");
    assert.equal(lc.verified, true, "the stranger's replay verifies the run");
    assert.equal(lc.commitment, s.commitment, "the replayed commitment IS the current one");

    // ── DRIVE THE CAREFUL RUN TO THE HOARD: click the first enabled move until the run
    //    ends (measured strikes drop the warden, press past, take the key, seize the hoard).
    for (let i = 0; i < 12; i++) {
      const ended = await page.evaluate(() => document.getElementById("descent").hasAttribute("ended"));
      if (ended) break;
      const before = await page.evaluate(() => document.getElementById("descent").getAttribute("commitment"));
      const clicked = await page.evaluate(() => window.__clickFirstEnabled("descent"));
      assert.ok(clicked >= 0, "an enabled move was available mid-run");
      await page.waitForFunction(
        (b) => {
          const el = document.getElementById("descent");
          return el.getAttribute("commitment") !== b || el.hasAttribute("ended");
        },
        before,
        { timeout: 15000 },
      );
    }

    s = await page.evaluate(() => window.__snap("descent"));
    assert.equal(s.won, true, "reached the hoard — a won run");
    assert.equal(s.dead, false, "a winner did not perish");
    assert.equal(s.ended, true, "the run ended");
    assert.ok(Number(s.depth) > 0, "the run pressed deeper");
    assert.match(s.status, /hoard is seized|won/i, "the win is surfaced in the status");

    // The WON run replays true against a fresh, identically-seeded day.
    const lcWin = await page.evaluate((uri) => window.__dreggDescentVerify(uri), "dregg://descent/b3_de5ce0");
    assert.equal(lcWin.verified, true, "the won run re-verifies by replay");

    // ── SETTLE degrades to the honest opt-in named-hook note (the run stays PRIVATE).
    await page.evaluate(() => window.__clickAction("descent", "settle"));
    await page.waitForFunction(() => {
      const root = window.__dreggDescentRoots.get(document.getElementById("descent"));
      return (root.querySelector(".settle-note")?.textContent || "").length > 0;
    }, null, { timeout: 15000 });
    s = await page.evaluate(() => window.__snap("descent"));
    assert.equal(s.published, false, "the run was NOT published (no settle provider wired)");
    assert.match(s.settleNote, /private|named hook|opt-in/i, "settle degrades to the honest named-hook note");

    // ── RECKLESS DEATH: a fresh element would be needed for a full replay; drive the
    //    death path directly through the engine to prove a LOST run is an honest,
    //    replay-verifiable record. Reckless all-out (1) → hp to the brink → fall (3).
    const deathUri = "dregg://descent/b3_deadb0";
    const opened = await page.evaluate((uri) => window.__dreggDescentOpen(uri), deathUri);
    assert.equal(opened.ok, true, "the death-path day opens");
    assert.equal(opened.verified, true, "a freshly-opened day replays trivially");
    let r = await page.evaluate((uri) => window.__dreggDescentAdvance(uri, 1), deathUri); // reckless
    assert.equal(r.refused, false, "the reckless opener commits");
    assert.ok(r.state.hp <= 20, `at the brink after the reckless blow (hp=${r.state.hp})`);
    // The fall-to-defeat move is now available (its gate is hp<=20).
    r = await page.evaluate((uri) => window.__dreggDescentAdvance(uri, 3), deathUri); // fall
    assert.equal(r.refused, false, "the fall commits");
    assert.equal(r.state.dead, true, "the downed flag is set — a permadeath loss");
    // Close the defeat room.
    r = await page.evaluate((uri) => window.__dreggDescentAdvance(uri, 0), deathUri);
    assert.equal(r.state.ended, true, "the run is over — lost");
    assert.equal(r.state.won, false, "a lost run did not reach the hoard");
    const lcDeath = await page.evaluate((uri) => window.__dreggDescentVerify(uri), deathUri);
    assert.equal(lcDeath.verified, true, "the lost run re-verifies by replay");

    // ── FAIL-CLOSED: the malformed-addr descent renders NOTHING (fallback link + warning).
    const bad = await page.evaluate(() => window.__snap("badDescent"));
    assert.equal(bad.verified, false, "a malformed addr never verifies");
    assert.equal(bad.error, true, "[error] reflected on the fail-closed element");
    assert.equal(bad.pageSeesShadow, false, "no shadow was attached on fail-closed");
    assert.equal(bad.hasFallbackLink, true, "the original link is preserved");
    assert.equal(bad.hasWarning, true, "an honest could-not-verify warning is shown");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
