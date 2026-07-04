#!/usr/bin/env node
// Drive the SERVED live reflective-inspector page in headless Chrome over the DevTools
// Protocol (CDP) — the same way the counter proof was driven. PROVES the browser-native
// reflective cockpit surface end-to-end:
//
//   1. launch headless Chrome with --remote-debugging-port, navigate to the inspector page;
//   2. wait for the in-tab `InspectorWorld` to boot (window.__deosCard bound);
//   3. read the bound rows (state[0..2]) + the receipt count off the LIVE in-tab ledger;
//   4. CLICK the `add` affordance button → a REAL cap-gated verified turn in the tab;
//   5. assert the bound state[1] row re-painted (42 → 43) and the receipt count advanced;
//   6. click `tick` → assert state[0] advances independently.
//
// No npm deps: uses node's built-in fetch + WebSocket (node ≥ 22). Chrome is found via
// $CHROME or the macOS default. The page must already be SERVED (run serve-deos-card.sh
// --no-serve, then `python3 -m http.server` from the dist dir, OR pass a URL).
//
//   node scripts/drive-deos-inspector.mjs [http://localhost:8000/inspector.html]

import { spawn } from 'node:child_process';
import { mkdtempSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const URL = process.argv[2] || 'http://localhost:8000/inspector.html';
const CHROME =
  process.env.CHROME ||
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const DEBUG_PORT = 9333;

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function cdpTargets() {
  const res = await fetch(`http://127.0.0.1:${DEBUG_PORT}/json`);
  return res.json();
}

// A tiny CDP client over the page's WebSocket debugger URL.
class CDP {
  constructor(ws) {
    this.ws = ws;
    this.id = 0;
    this.pending = new Map();
    ws.addEventListener('message', (ev) => {
      const msg = JSON.parse(ev.data);
      if (msg.id && this.pending.has(msg.id)) {
        const { resolve, reject } = this.pending.get(msg.id);
        this.pending.delete(msg.id);
        if (msg.error) reject(new Error(JSON.stringify(msg.error)));
        else resolve(msg.result);
      }
    });
  }
  send(method, params = {}) {
    const id = ++this.id;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.ws.send(JSON.stringify({ id, method, params }));
    });
  }
  // Evaluate an expression in the page, awaiting promises, returning the JSON value.
  async eval(expr) {
    const r = await this.send('Runtime.evaluate', {
      expression: expr,
      awaitPromise: true,
      returnByValue: true,
    });
    if (r.exceptionDetails) {
      throw new Error('page eval threw: ' + JSON.stringify(r.exceptionDetails));
    }
    return r.result.value;
  }
}

function assert(cond, msg) {
  if (!cond) {
    console.error('FAIL:', msg);
    process.exit(1);
  }
  console.log('  ok:', msg);
}

async function main() {
  const userDir = mkdtempSync(join(tmpdir(), 'deos-chrome-'));
  const chrome = spawn(
    CHROME,
    [
      '--headless=new',
      `--remote-debugging-port=${DEBUG_PORT}`,
      `--user-data-dir=${userDir}`,
      '--no-first-run',
      '--no-default-browser-check',
      '--disable-gpu',
      URL,
    ],
    { stdio: 'ignore' },
  );

  let cleanup = () => {
    try {
      chrome.kill('SIGKILL');
    } catch {}
  };
  process.on('exit', cleanup);

  try {
    // Wait for the debugger endpoint + a page target.
    let target = null;
    for (let i = 0; i < 50; i++) {
      try {
        const targets = await cdpTargets();
        target = targets.find((t) => t.type === 'page' && t.webSocketDebuggerUrl);
        if (target) break;
      } catch {}
      await sleep(200);
    }
    assert(target, `Chrome devtools page target reachable (navigated to ${URL})`);

    const ws = new WebSocket(target.webSocketDebuggerUrl);
    await new Promise((res, rej) => {
      ws.addEventListener('open', res);
      ws.addEventListener('error', rej);
    });
    const cdp = new CDP(ws);
    await cdp.send('Runtime.enable');

    // 1. Wait for the in-tab InspectorWorld to boot (window.__deosCard bound + readable).
    let booted = false;
    for (let i = 0; i < 80; i++) {
      const ready = await cdp.eval(
        `(() => { const c = window.__deosCard; return !!(c && typeof c.read === 'function' && typeof c.fire === 'function'); })()`,
      );
      if (ready) {
        booted = true;
        break;
      }
      await sleep(250);
    }
    assert(booted, 'the in-tab InspectorWorld booted (window.__deosCard bound, real verified executor)');

    // 2. Read the bound rows + receipts off the LIVE in-tab ledger (the witnessed reads).
    const before = await cdp.eval(
      `(() => { const c = window.__deosCard; return { s0: Number(c.read(0)), s1: Number(c.read(1)), s2: Number(c.read(2)), receipts: c.receiptCount(), cell: c.cellId() }; })()`,
    );
    console.log('  in-tab ledger (before):', JSON.stringify(before));
    assert(before.s0 === 7 && before.s1 === 42 && before.s2 === 100, 'the three bound slots read their seeds (7, 42, 100)');
    assert(before.receipts === 3, 'three seed turns committed (receipts = 3)');
    assert(before.cell && before.cell.length > 0, 'the focused cell has a real id');

    // 3. The rendered `add` button shows the seeded value in its bound row before the click.
    const rowBefore = await cdp.eval(
      `document.querySelector('.deos-bind[data-slot="1"]').textContent`,
    );
    assert(/42$/.test(rowBefore), `the state[1] Bind row paints 42 before the click (got "${rowBefore}")`);

    // 4. CLICK the `add` affordance button → a REAL cap-gated verified turn in the tab.
    await cdp.eval(
      `document.querySelector('.deos-button[data-turn="add"]').click()`,
    );
    await sleep(300); // let the turn commit + the DOM re-paint

    // 5. Assert the bound row re-painted (42 → 43) and the receipt count advanced.
    const after = await cdp.eval(
      `(() => { const c = window.__deosCard; return { s0: Number(c.read(0)), s1: Number(c.read(1)), s2: Number(c.read(2)), receipts: c.receiptCount() }; })()`,
    );
    console.log('  in-tab ledger (after add):', JSON.stringify(after));
    assert(after.s1 === 43, 'the `add` click fired a real verified turn: state[1] 42 → 43');
    assert(after.s0 === 7 && after.s2 === 100, 'the untouched slots are unchanged');
    assert(after.receipts === 4, 'exactly one more verified turn committed (receipts 3 → 4)');

    const rowAfter = await cdp.eval(
      `document.querySelector('.deos-bind[data-slot="1"]').textContent`,
    );
    assert(/43$/.test(rowAfter), `the state[1] Bind row RE-PAINTED to 43 (got "${rowAfter}")`);

    // 6. A different affordance advances a different slot — the loop is durable + per-slot.
    await cdp.eval(`document.querySelector('.deos-button[data-turn="tick"]').click()`);
    await sleep(300);
    const after2 = await cdp.eval(
      `(() => { const c = window.__deosCard; return { s0: Number(c.read(0)), receipts: c.receiptCount() }; })()`,
    );
    console.log('  in-tab ledger (after tick):', JSON.stringify(after2));
    assert(after2.s0 === 8, 'the `tick` click advanced state[0] 7 → 8 (independent slot)');
    assert(after2.receipts === 5, 'five verified turns on the in-tab audit tape');

    console.log('\nPASS: the reflective-inspector card renders + fires real verified turns in a browser TAB.');
  } finally {
    cleanup();
  }
}

main().catch((e) => {
  console.error('driver error:', e);
  process.exit(1);
});
