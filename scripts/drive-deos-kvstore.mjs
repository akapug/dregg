#!/usr/bin/env node
// Drive the SERVED live KV-STORE SERVICE-CELL page in headless Chrome over the DevTools
// Protocol (CDP). PROVES that a SERVICE CELL — a cell publishing a typed `InterfaceDescriptor`
// (put · delete · get) whose method calls route through the verified DFA before they desugar to
// ordinary `SetField` effects — renders AND fires real cap-gated verified turns in a browser
// TAB, through the SAME `ViewNode` IR the native cockpit renders:
//
//   1. launch headless Chrome with --remote-debugging-port, navigate to the kvstore page;
//   2. wait for the in-tab `KvStoreWorld` to boot (window.__deosCard bound);
//   3. assert the rendered DOM carries a version Bind (slot 0) + a `.deos-table` of register
//      rows, each with a `put` and a `del` button (the published-interface affordances);
//   4. read the store version + register values + receipt count off the LIVE ledger;
//   5. CLICK `put` on reg 2 → a REAL verified turn ROUTED through the interface; assert reg 2
//      bumped (20→21), the monotone version advanced, and receipts +1;
//   6. CLICK `del` on reg 1 → reg 1 cleared (10→0), the version advanced again, receipts +1;
//   7. call `card.tryRollback(2)` → assert it is REFUSED (the store program's `Monotonic`
//      version constraint bites on the verified commit path — the guarantee, in the tab);
//   8. call `card.tryGet(1)` → assert it names the `Serviced` OFE seam (the router refuses to
//      desugar a read to a turn — honest, not faked);
//   9. capture a screenshot of the painted store to the given path.
//
// No npm deps: node's built-in fetch + WebSocket (node >= 22). Chrome via $CHROME or the macOS
// default. The page must already be SERVED (file:// is CORS-blocked).
//
//   node scripts/drive-deos-kvstore.mjs [http://localhost:8000/kvstore.html] [screenshot.png]

import { spawn } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const URL = process.argv[2] || 'http://localhost:8000/kvstore.html';
const SHOT = process.argv[3] || join(process.cwd(), 'deos-kvstore.png');
const CHROME =
  process.env.CHROME || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const DEBUG_PORT = 9335;

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function cdpTargets() {
  const res = await fetch(`http://127.0.0.1:${DEBUG_PORT}/json`);
  return res.json();
}

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
      '--force-device-scale-factor=2',
      '--window-size=560,520',
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
    await cdp.send('Page.enable');

    // 1. Wait for the in-tab KvStoreWorld to boot.
    let booted = false;
    for (let i = 0; i < 80; i++) {
      const ready = await cdp.eval(
        `(() => { const c = window.__deosCard; return !!(c && typeof c.fire === 'function' && typeof c.version === 'function' && typeof c.tryRollback === 'function'); })()`,
      );
      if (ready) {
        booted = true;
        break;
      }
      await sleep(250);
    }
    assert(booted, 'the in-tab KvStoreWorld booted (window.__deosCard bound, real verified service cell)');

    // 2. The rendered DOM carries the published-interface surface.
    const layout = await cdp.eval(
      `(() => ({
        version_binds: document.querySelectorAll('.deos-bind[data-slot="0"]').length,
        tables: document.querySelectorAll('.deos-table').length,
        reg_rows: document.querySelectorAll('.deos-table .deos-row').length,
        puts: document.querySelectorAll('.deos-button[data-turn="put"]').length,
        dels: document.querySelectorAll('.deos-button[data-turn="delete"]').length,
      }))()`,
    );
    console.log('  rendered layout:', JSON.stringify(layout));
    assert(layout.version_binds === 1, 'the store renders the version Bind (slot 0)');
    assert(layout.tables === 1 && layout.reg_rows === 4, 'a Table of four register Rows');
    assert(layout.puts === 4 && layout.dels === 4, 'each register Row carries put + del affordances');

    // 3. Read the store off the LIVE in-tab ledger.
    const before = await cdp.eval(
      `(() => { const c = window.__deosCard; return { version: Number(c.version()), r1: Number(c.read(1)), r2: Number(c.read(2)), r3: Number(c.read(3)), r4: Number(c.read(4)), receipts: c.receiptCount(), cell: c.cellId() }; })()`,
    );
    console.log('  in-tab store (before):', JSON.stringify(before));
    assert(before.r1 === 10 && before.r2 === 20 && before.r3 === 30 && before.r4 === 40, 'registers read their seeds (10/20/30/40)');
    assert(before.version === 4, 'four seed puts bumped the monotone version to 4');
    // receipts = 1 store-cell mint (a real factory turn) + 4 seed puts.
    assert(before.receipts === 5, 'the store mint + four seed turns committed (receipts = 5)');
    assert(before.cell && before.cell.length > 0, 'the store cell has a real id');

    // 4. CLICK `put` on reg 2 → a REAL verified turn routed through the interface.
    await cdp.eval(
      `document.querySelector('.deos-button[data-turn="put"][data-arg="2"]').click()`,
    );
    await sleep(300);
    const afterPut = await cdp.eval(
      `(() => { const c = window.__deosCard; return { version: Number(c.version()), r2: Number(c.read(2)), receipts: c.receiptCount() }; })()`,
    );
    console.log('  in-tab store (after put reg2):', JSON.stringify(afterPut));
    assert(afterPut.r2 === 21, 'the put click fired a real routed verified turn: reg 2 bumped 20 → 21');
    assert(afterPut.version === 5, 'the monotone store version advanced 4 → 5');
    assert(afterPut.receipts === 6, 'exactly one more verified turn committed (5 → 6)');
    const r2Row = await cdp.eval(`document.querySelector('.deos-bind[data-slot="2"]').textContent`);
    assert(/^21$/.test(r2Row.trim()), `reg 2 Bind row RE-PAINTED to 21 (got "${r2Row}")`);

    // 5. CLICK `del` on reg 1 → cleared, version advances again.
    await cdp.eval(
      `document.querySelector('.deos-button[data-turn="delete"][data-arg="1"]').click()`,
    );
    await sleep(300);
    const afterDel = await cdp.eval(
      `(() => { const c = window.__deosCard; return { version: Number(c.version()), r1: Number(c.read(1)), r2: Number(c.read(2)), receipts: c.receiptCount() }; })()`,
    );
    console.log('  in-tab store (after del reg1):', JSON.stringify(afterDel));
    assert(afterDel.r1 === 0, 'the del click fired a real routed verified turn: reg 1 cleared 10 → 0');
    assert(afterDel.r2 === 21, 'reg 2 held its committed 21 (independent register)');
    assert(afterDel.version === 6, 'the monotone version advanced 5 → 6');
    assert(afterDel.receipts === 7, 'seven verified turns on the in-tab audit tape');

    // 6. The verified guarantee BITES in the tab: a rollback is REFUSED.
    const rollback = await cdp.eval(`JSON.parse(window.__deosCard.tryRollback(2))`);
    console.log('  tryRollback(2):', JSON.stringify(rollback));
    assert(rollback.refused === true, 'a put that LOWERS the version is REFUSED — the Monotonic guarantee bites in-tab');
    const afterRollback = await cdp.eval(`Number(window.__deosCard.version())`);
    assert(afterRollback === 6, 'the refused rollback left the version unchanged (still 6)');

    // 7. `get` is a NAMED SEAM, not a faked write.
    const getSeam = await cdp.eval(`window.__deosCard.tryGet(1)`);
    console.log('  tryGet(1):', JSON.stringify(getSeam));
    assert(/Serviced/.test(getSeam) && /OFE/.test(getSeam), 'get is named as the Serviced OFE seam (router refuses to desugar a read)');

    // 8. Capture a screenshot of the painted store.
    const shot = await cdp.send('Page.captureScreenshot', { format: 'png' });
    writeFileSync(SHOT, Buffer.from(shot.data, 'base64'));
    console.log('  screenshot:', SHOT);

    console.log('\nPASS: the KV-store SERVICE CELL (published interface · routed methods · Monotonic guarantee) renders + fires real verified turns in a browser TAB.');
  } finally {
    cleanup();
  }
}

main().catch((e) => {
  console.error('driver error:', e);
  process.exit(1);
});
