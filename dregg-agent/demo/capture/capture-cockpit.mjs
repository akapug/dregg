// Capture the STAR surface: the DreggNet web cockpit (dreggnet-attach).
// Drives the real flow in a headless chromium and records it to out/cockpit.webm:
//   goal -> reason->act->observe stream (signed receipts accumulating) ->
//   budget gauge draws down + the exfiltrate probe cap-refused ("no money moved")
//   -> VERIFY (the proof held) -> the tamper self-demo (flip one line -> shatters)
//   -> a tiny-budget run so the ceiling visibly BITES (over-budget refusals).
//
// HONEST: the receipt-chain verify + the tamper are REAL (re-witnessed in-browser,
// no host trusted). The tool verdicts are canned/demo-labelled by the server
// itself ("demo verdict (canned — not re-witnessed)"); this capture does not
// dress them up as live-witnessed. The brain is the scripted demo planner (the
// live Hermes brain is the reviewed-go swap) — labelled on-screen.

import { chromium } from 'playwright-core';
import { VIEW, sleep, caption, reveal } from './lib.mjs';

const URL = process.env.ATTACH_URL || 'http://127.0.0.1:8100';
const OUT = process.env.OUT_DIR || './out';

const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({
  viewport: VIEW,
  recordVideo: { dir: OUT, size: VIEW },
  deviceScaleFactor: 2,
});
const page = await context.newPage();
page.setDefaultTimeout(30000);

await page.goto(URL, { waitUntil: 'domcontentloaded' });
await sleep(600);

// ── cold open ─────────────────────────────────────────────────────────────
await caption(page,
  'The web COCKPIT &mdash; <b>a hosted brain you own, and can prove</b>',
  'dreggnet-attach, served locally. Signed in as your cap-account (dev subject).');
await reveal(page, 'header', 900);
await sleep(1400);

// ── the goal box: click a suggested goal (the zero-to-wow onramp) ───────────
await caption(page,
  'Give your agent a <b>goal</b> + a budget + a cap bundle',
  'Every tool-call is cap-gated, metered against the budget, and sealed into a receipt chain.');
await reveal(page, '#goalbox', 700);
await page.locator('.chip', { hasText: 'run tests + verify deploy' }).click();
await sleep(1200);
await page.locator('#drive').click();

// ── the reason -> act -> observe stream ─────────────────────────────────────
await page.waitForSelector('#live:not([hidden])');
await caption(page,
  'reason &rarr; act &rarr; observe &mdash; <b>signed receipts accumulate</b>',
  'think / act / observe per step; #seq &middot; signed &middot; &larr;prev. Tool verdicts are demo-labelled (canned), not live-witnessed.');
// let the paced feed render (cards arrive ~340ms apart) + the refusal land.
await page.waitForSelector('.stepcard.refused', { timeout: 20000 });
await sleep(700);
await caption(page,
  'The out-of-bundle <b>exfiltrate</b> probe is <b>refused</b>',
  'The cap-gate held in-band: "no effect — no money moved." The teeth bite every run.');
await reveal(page, '.stepcard.refused', 700);
await sleep(1600);

// ── the budget gauge ────────────────────────────────────────────────────────
await caption(page,
  'The <b>budget gauge</b> &mdash; un-drawn headroom is authority never exercised',
  'Bounded by construction: the spend can never cross the ceiling you funded.');
await reveal(page, '.gauge', 700);
await sleep(1600);

// ── VERIFY: re-witness, then the tamper self-demo ──────────────────────────
await page.waitForSelector('#verify-live:not([disabled])', { timeout: 20000 });
await caption(page,
  'Click <b>VERIFY</b> &mdash; re-witness the proof in your own browser',
  'This leg is REAL: the signed receipt chain is replayed offline, no host trusted.');
await reveal(page, '.verify-zone', 500);
await page.locator('#verify-live').click();

await page.waitForFunction(
  () => /the proof held/i.test(document.getElementById('proof-held')?.textContent || ''),
  null, { timeout: 20000 });
await caption(page,
  '<b>&#10003; the proof held</b> &mdash; the chain is unbroken, the spend inside its box',
  'Re-witnessed in-browser. No trust in the host.');
await reveal(page, '#proof-held', 700);
await sleep(1800);

await page.waitForSelector('#proof-tampered:not([hidden])', { timeout: 20000 });
await caption(page,
  '<b>&#10007; flip ONE line &mdash; it shatters</b> (BadSignature)',
  'Same chain, one sealed line changed, re-witnessed: a forged result cannot survive.');
await reveal(page, '#proof-tampered', 700);
await sleep(2600);

// ── a tiny budget so the ceiling visibly BITES ─────────────────────────────
await page.evaluate(() => window.scrollTo({ top: 0, behavior: 'smooth' }));
await sleep(700);
await caption(page,
  'Now a <b>tiny budget</b> &mdash; watch the ceiling bite',
  'Fund only a sliver; the over-budget spends are refused before any money moves.');
await page.locator('.chip', { hasText: 'tiny budget' }).click();
await sleep(1000);
await page.locator('#drive').click();
await page.waitForSelector('#live:not([hidden])');
await page.waitForSelector('.stepcard.refused', { timeout: 20000 });
await reveal(page, '.gauge', 700);
await caption(page,
  'The gauge slams full &mdash; <b>&#10007; refused, no money moved</b>',
  'A hard budget ceiling: the extra work is contained, not charged.');
await sleep(2400);

const vid = page.video();
await page.close();
await context.close();
if (vid) await vid.saveAs(`${OUT}/cockpit.webm`);
await browser.close();
console.error('cockpit: recorded to', `${OUT}/cockpit.webm`);
