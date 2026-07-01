// Playwright capture of portal.dregg.studio (served locally by serve.mjs).
//
// Captures the REAL served portal's painted surfaces + short videos:
//   1. hero    — "Don't trust the server / Verify it yourself" + the dregg_wasm
//                recursive-STARK verifier panel (its trust-first idle state).
//   2. network — the living-network view: hub-and-spoke graph over the cell set,
//                the cell grid (balance / nonce / caps), the trust chip.
//   3. cell    — the cell inspector: the recursive FOLD theatre (t0 t1 t2 -> root)
//                + the field table ("the server's claim") the light client binds.
//
// HONESTY: the in-tab recursive-STARK verifier is REAL wasm, but its proof-
// GENERATION step (produce_external_history_envelope) traps under THIS sandbox's
// headless-chromium (build 1223) — it completes only in a full desktop browser.
// So this captures the portal's trust-first UI, NOT a green "Verified" end-state
// (which we do not fabricate). For the network + cell shots we abort /pkg/** so
// the verifier can't block the main thread. See demo/surfaces/SURFACES.md.
//
// Run: node demo/surfaces/capture.mjs   (needs serve.mjs on BASE; CHROME_PATH set)
import { chromium } from "playwright";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { mkdirSync } from "node:fs";

const here = dirname(fileURLToPath(import.meta.url));
const OUT = join(here, "out");
const VIDEO = join(OUT, "video");
const SHOTS = join(OUT, "shots");
mkdirSync(VIDEO, { recursive: true });
mkdirSync(SHOTS, { recursive: true });

const BASE = process.env.BASE || "http://localhost:8787";
const VP = { width: 1280, height: 800 };
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function run() {
  const launchOpts = { args: ["--force-color-profile=srgb"] };
  if (process.env.CHROME_PATH) launchOpts.executablePath = process.env.CHROME_PATH;
  const browser = await chromium.launch(launchOpts);
  const mkctx = () => browser.newContext({
    viewport: VP, deviceScaleFactor: 2,
    recordVideo: { dir: VIDEO, size: VP }, reducedMotion: "no-preference",
  });

  // ---- 1. hero: the trust-first verifier panel (pre auto-run) ----------------
  {
    const ctx = await mkctx();
    const page = await ctx.newPage();
    await page.goto(BASE + "/", { waitUntil: "load" });
    // the engine auto-runs at ~1.4s; grab the clean idle panel before that.
    await sleep(950);
    await page.screenshot({ path: join(SHOTS, "01-hero.png"), animations: "disabled", timeout: 20000 });
    await sleep(400);
    await ctx.close();
    const v = await page.video(); if (v) await v.saveAs(join(VIDEO, "hero.webm"));
  }

  // ---- 2. living network (abort /pkg so the verifier can't block) ------------
  {
    const ctx = await mkctx();
    const page = await ctx.newPage();
    await page.route("**/pkg/**", (r) => r.abort());
    await page.goto(BASE + "/", { waitUntil: "load" });
    await page.waitForSelector(".cell", { timeout: 8000 }).catch(() => {});
    await sleep(700);
    await page.evaluate(() => document.getElementById("network").scrollIntoView({ behavior: "instant", block: "start" }));
    await sleep(1500);
    await page.screenshot({ path: join(SHOTS, "02-network.png"), animations: "disabled", timeout: 20000 });
    await sleep(400);
    await ctx.close();
    const v = await page.video(); if (v) await v.saveAs(join(VIDEO, "network.webm"));
  }

  // ---- 3. cell inspector: fold theatre + field table (abort /pkg) ------------
  {
    const ctx = await mkctx();
    const page = await ctx.newPage();
    await page.route("**/pkg/**", (r) => r.abort());
    const id = "1c9e7d5b3a1f0e8c6a4b2d0f8e6c4a2b1093f7d5b3a1e9c7f5d3b1a9e7c5d3f1";
    await page.goto(BASE + "/cell.html?id=" + id, { waitUntil: "load" });
    await page.waitForSelector(".turnblk", { timeout: 8000 }).catch(() => {});
    await sleep(1400); // let the fold theatre slide in + fields fill
    // The verifier can't run under this sandbox (see header) so the banner shows
    // "attestation check failed to run". We frame the inspector's STRUCTURE — the
    // recursive fold theatre + the field table ("the server's claim") — by
    // removing the verdict banner rather than fabricating a result. Honest: these
    // are the real painted surfaces the light client binds when it runs.
    await page.evaluate(() => { const b = document.getElementById("banner"); if (b) b.remove(); });
    await sleep(200);
    await page.screenshot({ path: join(SHOTS, "03-cell-fold.png"), animations: "disabled", timeout: 20000 });
    await page.screenshot({ path: join(SHOTS, "04-cell-fields.png"), fullPage: true, animations: "disabled", timeout: 20000 });
    await sleep(400);
    await ctx.close();
    const v = await page.video(); if (v) await v.saveAs(join(VIDEO, "cell.webm"));
  }

  await browser.close();
  console.log("captured -> " + OUT);
}
run().catch((e) => { console.error(e); process.exit(1); });
