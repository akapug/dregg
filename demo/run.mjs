// THE DRIVEN RUN — the bar: it worked, shown.
//
// Loads the demo in a real (headless) Chromium via Playwright, waits for the crowd
// auto-play to reach an ending + the verify badge, ASSERTS the story advanced through
// ≥2 collective branches (the passage changed and the receipt count grew each round)
// AND that verify() replays true, then CAPTURES a screenshot of the played-out story +
// a per-round transcript.
//
//   node demo/run.mjs
//
// Fail-closed: a spween syntax error in the scene surfaces as a StoryWorld::new failure
// (the page reports it, and this run fails loudly with the parser message).

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import path from "node:path";
import { makeServer } from "./serve.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");

// Playwright lives under extension/tests/node_modules; resolve it from there.
const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");

const OUT = path.join(__dirname, "run");

async function main() {
  await mkdir(OUT, { recursive: true });
  const { server, base } = await makeServer(0);
  const browser = await chromium.launch({ headless: true });
  const pageErrors = [];
  try {
    const page = await browser.newPage({ viewport: { width: 900, height: 1400 }, deviceScaleFactor: 2 });
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/`, { waitUntil: "load" });

    // Boot: either the element settles verified, or the page reports a fail-closed error
    // (e.g. a spween syntax error from StoryWorld::new).
    await page.waitForFunction(
      () => {
        const el = document.getElementById("commons");
        return (el && (el.hasAttribute("verified") || el.hasAttribute("error"))) || !!window.__DEMO_ERROR;
      },
      null,
      { timeout: 40000 },
    );

    const bootErr = await page.evaluate(() => window.__DEMO_ERROR || null);
    if (bootErr) {
      throw new Error(
        `the demo failed to boot (fail-closed). Most likely a spween scene error:\n    ${bootErr}`,
      );
    }
    const verifiedAtBoot = await page.evaluate(() => document.getElementById("commons").hasAttribute("verified"));
    assert.equal(verifiedAtBoot, true, "the story must resolve + replay-verify at load");

    // Wait for the crowd auto-play to run to the ending + the stranger's replay.
    await page.waitForFunction(() => window.__DEMO_DONE === true, null, { timeout: 90000 });

    // ── read the results ──
    const log = await page.evaluate(() => window.__DEMO_LOG || []);
    const verified = await page.evaluate(() => window.__DEMO_VERIFIED === true);
    const receipts = await page.evaluate(() => Number(window.__DEMO_RECEIPTS || 0));
    const finalPassage = await page.evaluate(() => document.getElementById("commons").getAttribute("passage"));
    const badge = await page.evaluate(() => (document.getElementById("verifyBadge")?.textContent || "").trim());

    // ── ASSERT the crowd co-authored the story ──
    assert.ok(log.length >= 2, `the story advanced through ≥2 collective branches (got ${log.length})`);
    for (const r of log) {
      const cast = r.options.reduce((a, o) => a + o.count, 0);
      assert.ok(cast > 0, `round ${r.round} at "${r.passage}" recorded real ballots (got ${cast})`);
      assert.ok(
        r.receiptsAfter > r.receiptsBefore,
        `round ${r.round}: closing advanced the winner as a verified turn ` +
          `(receipts ${r.receiptsBefore} → ${r.receiptsAfter})`,
      );
      assert.notEqual(
        r.newPassage,
        r.passage,
        `round ${r.round}: the winning branch changed the passage ("${r.passage}" → "${r.newPassage}")`,
      );
    }
    // Monotone receipt tape across the whole play.
    for (let i = 1; i < log.length; i++) {
      assert.ok(log[i].receiptsBefore >= log[i - 1].receiptsAfter, "the receipt tape only grows");
    }
    assert.equal(verified, true, "the stranger's replay re-verifies the whole receipt chain");
    assert.match(badge, /nothing was rewritten/i, "the verify badge announces the payoff");

    // ── CAPTURE ── (let the badge's fade-in transition settle first)
    await page.waitForFunction(
      () => {
        const b = document.getElementById("verifyBadge");
        return b && getComputedStyle(b).opacity === "1";
      },
      null,
      { timeout: 5000 },
    ).catch(() => {});
    await page.waitForTimeout(300);
    await page.screenshot({ path: path.join(OUT, "screenshot.png"), fullPage: true });

    const transcript = renderTranscript({ base, log, verified, receipts, finalPassage, badge });
    await writeFile(path.join(OUT, "transcript.txt"), transcript, "utf8");

    if (pageErrors.length) {
      // Surface but do not necessarily fail on benign console noise; a real pageerror is caught above by assertions.
      console.warn("page console/errors:\n  " + pageErrors.join("\n  "));
    }

    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "screenshot.png")}`);
    console.log(`  transcript → ${path.join(OUT, "transcript.txt")}\n`);
    console.log("  ✓ THE COMMONS RAN: real wasm StoryWorld, " + log.length + " crowd-voted branches, verify() true.\n");
  } finally {
    await browser.close();
    server.close();
  }
}

function renderTranscript({ base, log, verified, receipts, finalPassage, badge }) {
  const L = [];
  L.push("THE COMMONS — a crowd authors a verifiable story");
  L.push("driven run · real wasm StoryWorld · the-commons.scene");
  L.push("served at " + base);
  L.push("=".repeat(64));
  L.push("");
  for (const r of log) {
    L.push(`ROUND ${r.round} — passage "${r.passage}"`);
    L.push("  the assembly votes:");
    for (const o of r.options) {
      const bar = "█".repeat(o.count) + "·".repeat(Math.max(0, 7 - o.count));
      L.push(`    ${bar}  ${String(o.count).padStart(2)}  ${o.label}`);
    }
    L.push(`  → the crowd chose: "${r.winner}"`);
    L.push(`  → advanced to "${r.newPassage}"  ·  receipts ${r.receiptsBefore} → ${r.receiptsAfter}`);
    L.push(`  → commitment ${(r.commitment || "").slice(0, 16)}…`);
    L.push("");
  }
  L.push("-".repeat(64));
  L.push(`ending passage : ${finalPassage}`);
  L.push(`receipt tape   : ${receipts} verified turns (genesis + one per branch)`);
  L.push(`stranger replay: ${verified ? "VERIFIED — nothing was rewritten" : "FAILED"}`);
  L.push(`badge          : ${badge}`);
  L.push("");
  return L.join("\n");
}

main().catch((e) => {
  console.error("\n  ✗ RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
