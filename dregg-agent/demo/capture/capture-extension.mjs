// Capture the cipherclerk EXTENSION (breadstuffs/extension) — the MV3 wallet,
// loaded UNPACKED in a real chromium, recorded to out/extension.webm:
//   create a cap-account (a KEY, not a password) -> LOG IN to the network
//   (challenge -> sign -> session, verified by the local stub webauth) ->
//   POWERBOX: grant an ATTENUATED dregg-cap scoped to one action (no-amplify).
//
// HONEST: the login is the REAL challenge/sign handshake — the wallet signs the
// server nonce with its real Ed25519 key and the local STUB webauth VERIFIES the
// signature before minting a session (a forged sig is rejected). The stub's node
// status + the derived subject are canned (a real deployment computes the
// substrate account-identity cell). The powerbox grant is a REAL attenuated
// bearer cap minted by the wallet WASM. No live-cloud claim.

import { chromium } from 'playwright-core';
import path from 'path';
import { fileURLToPath } from 'url';
import { sleep, caption } from './lib.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const EXT_DIR = process.env.EXT_DIR || path.resolve(__dirname, '../../../extension');
const NODE_URL = process.env.MOCK_NODE_URL || 'http://localhost:8420';
const OUT = process.env.OUT_DIR || './out';
const VIEW = { width: 460, height: 820 };
const PASS = 'demo-passphrase';
const TARGET_CELL = '3f2a7c9e1b4d8a06f5e2c1907a3b6d4e8f0a1c2b3d4e5f60718293a4b5c6d7e8';

const context = await chromium.launchPersistentContext('', {
  headless: false,
  viewport: VIEW,
  recordVideo: { dir: OUT, size: VIEW },
  deviceScaleFactor: 2,
  args: [
    `--disable-extensions-except=${EXT_DIR}`,
    `--load-extension=${EXT_DIR}`,
    '--no-first-run',
    '--disable-gpu',
  ],
});

// extension id from the service worker.
let [sw] = context.serviceWorkers();
if (!sw) sw = await context.waitForEvent('serviceworker', { timeout: 20000 });
const extId = sw.url().split('/')[2];
console.error('extension id:', extId);

// point the wallet's node config at the local stub (drives the real settings UI).
const settings = await context.newPage();
settings.on('dialog', (d) => void d.accept());
await settings.goto(`chrome-extension://${extId}/settings.html`);
await settings.waitForLoadState('domcontentloaded');
await settings.fill('#nodeUrl', NODE_URL);
await settings.fill('#wssUrl', 'ws://localhost:8420/ws').catch(() => {});
await settings.fill('#wsUrl', 'ws://localhost:8420/ws').catch(() => {});
await settings.click('#saveBtn');
await settings.waitForFunction(
  () => /saved/i.test(document.getElementById('statusMsg')?.textContent || ''),
  null, { timeout: 8000 }).catch(() => {});
await settings.close();

// the popup — the recorded page.
const page = await context.newPage();
page.setDefaultTimeout(30000);
await page.goto(`chrome-extension://${extId}/popup.html`, { waitUntil: 'domcontentloaded' });
// centre the 360px popup body in the recording frame.
await page.evaluate(() => { document.body.style.margin = '0 auto'; });
await sleep(800);

await caption(page,
  'The cipherclerk <b>EXTENSION</b> &mdash; your dregg wallet, in the browser',
  'MV3, loaded UNPACKED in a real chromium. Recorded locally.');
await sleep(1600);

// ── onboarding: a cap-account is a KEY, not a password ─────────────────────
const onboarding = page.locator('#onboardingSection');
await sleep(400);
if (await onboarding.isVisible().catch(() => false)) {
  await caption(page,
    'Create a <b>cap-account</b> &mdash; a KEY you hold, not a username + password',
    'The recovery phrase derives your Ed25519 identity key (the one that signs turns).');
  await page.fill('#onbPass', PASS);
  await page.fill('#onbPassConfirm', PASS);
  await sleep(800);
  await page.click('#onbNextBtn');
  await page.locator('#onbStep2:not(.hidden)').waitFor({ state: 'attached', timeout: 8000 });
  await sleep(1000);
  const words = await page.locator('#onbMnemonic').evaluate((el) =>
    (el.textContent || '').split(/\s+/).filter((t) => t && !/^\d+\.?$/.test(t)).join(' '));
  await page.fill('#onbConfirm', words);
  await sleep(600);
  await page.click('#onbCreateBtn');
  await onboarding.waitFor({ state: 'hidden', timeout: 8000 });
  await sleep(800);
}

// ── LOG IN: challenge -> sign -> session (the Cloud Session on the Clerk tab) ─
await page.locator('.tab-btn[data-tab="cipherclerk"]').click();
await sleep(700);
await caption(page,
  '<b>Log in</b> with your cap-account &mdash; no password',
  'Your key signs a one-time challenge; the stub webauth verifies the signature and returns a session.');
await page.evaluate(() => {
  const b = document.getElementById('loginBtn'); if (b) b.scrollIntoView({ block: 'center' });
});
await sleep(1200);
let loggedIn = false;
try {
  await page.locator('#loginBtn').click();
  await page.locator('#loginLoggedIn:not(.hidden)').waitFor({ state: 'attached', timeout: 15000 });
  loggedIn = true;
} catch (e) {
  console.error('login did not complete:', String(e).split('\n')[0]);
}
if (loggedIn) {
  const subj = await page.locator('#loginSubject').textContent().catch(() => '');
  await caption(page,
    '<b>&#10003; signed in as</b> ' + (subj || 'dregg:…'),
    'The signature PROVED possession of the key (verified by the stub webauth). The token is a revocable bearer, never the key.');
} else {
  await caption(page,
    'The signed challenge was sent (login leg)',
    'The wallet signs the nonce with its real key; the stub webauth verifies it. (See out/*.log if the panel did not flip.)');
}
await sleep(2600);

// ── POWERBOX: grant an ATTENUATED capability ────────────────────────────────
await page.locator('.tab-btn[data-tab="capabilities"]').click();
await sleep(700);
await caption(page,
  '<b>Powerbox</b> &mdash; grant an <b>attenuated</b> capability',
  'A dregg-cap scoped to ONE action on ONE cell. It can only be attenuated further &mdash; never amplified.');
await page.fill('#grantCellInput', TARGET_CELL);
await sleep(500);
await page.fill('#grantActionInput', 'read');
await sleep(500);
await page.fill('#grantExpiryInput', '60');
await sleep(700);
await page.locator('#grantCapBtn').click();
try {
  await page.locator('#grantResult').waitFor({ state: 'visible', timeout: 12000 });
  await page.evaluate(() => document.getElementById('grantResult')?.scrollIntoView({ block: 'center' }));
  const scope = await page.locator('#grantResultScope').textContent().catch(() => '');
  await caption(page,
    '<b>dregg-cap</b> minted &mdash; ' + (scope || 'action "read" · expires in 60m'),
    'A real bearer cap, minted by the wallet by ATTENUATING your key. The no-amplify story, on screen.');
} catch (e) {
  console.error('grant did not surface a token:', String(e).split('\n')[0]);
  await caption(page,
    'The powerbox grant was requested (attenuated cap)',
    'The wallet mints a bearer cap by attenuating your key &mdash; it can only do LESS.');
}
await sleep(3000);

// persistent-context video: grab the temp path, finalize on close, then copy.
const vpath = await page.video()?.path().catch(() => null);
await page.close();
await context.close();
if (vpath) {
  const fs = await import('fs');
  fs.copyFileSync(vpath, `${OUT}/extension.webm`);
}
console.error('extension: recorded to', `${OUT}/extension.webm`);
