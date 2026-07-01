// Capture the supporting panes: the signed-in CONSOLE ("my stuff", cap-scoped)
// and the public STATUS page ("is the cloud up?" — the federation panel), plus
// the public LANDING front door for the close. Each is the REAL server-rendered
// surface (dreggnet-console over its deterministic fixtures; dreggnet-status in
// STATUS_DEMO; dreggnet-landing). Recorded locally; fixture/demo data is a real
// render, not a live-cloud claim.

import { chromium } from 'playwright-core';
import { VIEW, sleep, caption } from './lib.mjs';

const OUT = process.env.OUT_DIR || './out';
const CONSOLE_URL = process.env.CONSOLE_URL || 'http://127.0.0.1:8101';
const STATUS_URL = process.env.STATUS_URL || 'http://127.0.0.1:8102';
const LANDING_URL = process.env.LANDING_URL || 'http://127.0.0.1:8103';

async function slowScroll(page, ms = 3200) {
  await page.evaluate(async (ms) => {
    const h = document.body.scrollHeight - window.innerHeight;
    if (h <= 0) return;
    const steps = 60, dt = ms / steps;
    for (let i = 0; i <= steps; i++) {
      window.scrollTo(0, Math.round((h * i) / steps));
      await new Promise((r) => setTimeout(r, dt));
    }
  }, ms);
}

async function grab(name, url, title, note) {
  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({
    viewport: VIEW, recordVideo: { dir: OUT, size: VIEW }, deviceScaleFactor: 2,
  });
  const page = await context.newPage();
  page.setDefaultTimeout(30000);
  await page.goto(url, { waitUntil: 'networkidle' }).catch(() => {});
  await sleep(900);
  await caption(page, title, note);
  await sleep(1600);
  await slowScroll(page);
  await sleep(1200);
  const vid = page.video();
  await page.close();
  await context.close();
  if (vid) await vid.saveAs(`${OUT}/${name}.webm`);
  await browser.close();
  console.error(`${name}: recorded to ${OUT}/${name}.webm (${url})`);
}

await grab('console', CONSOLE_URL,
  'The <b>CONSOLE</b> &mdash; "my stuff", cap-scoped to you',
  'Sites, servers, agents, budget, receipts &mdash; narrowed to the signed-in subject. Fixture data, real render.');

await grab('status', STATUS_URL,
  'The <b>STATUS</b> page &mdash; is the cloud up?',
  'The public health + federation panel. STATUS_DEMO fixture (honest devnet posture; no live-n=5 claim).');

await grab('landing', LANDING_URL,
  '<b>DreggNet</b> &mdash; the verifiable agent cloud',
  'The public front door. Served locally for the recording.');

console.error('panes: done');
