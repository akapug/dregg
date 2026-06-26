#!/usr/bin/env node
// Drive the SERVED live DOCUMENT-COLLABORATION page in headless Chrome over the DevTools
// Protocol (CDP). PROVES the Pijul/conflicts-as-objects flow — fork → diverge → stitch → a
// first-class conflict held off-heap → resolve → publish to the umem-heap — runs NODE-LESS in a
// browser TAB over an in-tab verified executor, firing REAL cap-gated verified turns:
//
//   1. launch headless Chrome with --remote-debugging-port, navigate to the doc-collab page;
//   2. wait for the in-tab `DocCollabWorld` to boot (window.__deosDoc bound) — the doc-cell's
//      base document is already published to its umem-heap (the FORK), leaving a receipt;
//   3. assert the PUBLISHED state: no conflict, a real umem boundary (heap_root), >= 1 receipt,
//      and a `stitch` affordance rendered; capture the base boundary;
//   4. CLICK `stitch` → the pushout: assert a first-class CONFLICT now renders (a ConflictView of
//      TWO alternatives attributed to alice/bob side-by-side + resolution buttons), held OFF-heap
//      (the committed umem boundary is UNCHANGED, receipts unchanged);
//   5. CLICK a resolution button (keep-both / order) → a REAL verified turn: assert the conflict
//      collapsed, the merged document PUBLISHED (the umem boundary MOVED, receipts +1, the
//      boundary still equals the canonical projection), and both authors' lines are in the doc;
//   6. capture a screenshot of the published document to the given path (default: deos-doccollab.png).
//
// No npm deps: node's built-in fetch + WebSocket (node >= 22). Chrome via $CHROME or the macOS
// default. The page must already be SERVED (file:// is CORS-blocked).
//
//   node scripts/drive-deos-doccollab.mjs [http://localhost:8000/doccollab.html] [screenshot.png]

import { spawn } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const URL = process.argv[2] || 'http://localhost:8000/doccollab.html';
const SHOT = process.argv[3] || join(process.cwd(), 'deos-doccollab.png');
const CHROME =
  process.env.CHROME || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const DEBUG_PORT = 9336;

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
      '--window-size=620,560',
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

    // 1. Wait for the in-tab DocCollabWorld to boot.
    let booted = false;
    for (let i = 0; i < 80; i++) {
      const ready = await cdp.eval(
        `(() => { const c = window.__deosDoc; return !!(c && typeof c.fire === 'function' && typeof c.viewHtml === 'function' && typeof c.hasConflict === 'function'); })()`,
      );
      if (ready) {
        booted = true;
        break;
      }
      await sleep(250);
    }
    assert(booted, 'the in-tab DocCollabWorld booted (window.__deosDoc bound, real verified executor)');

    // 2. The PUBLISHED base state (the fork): no conflict, a real umem boundary, a seed receipt.
    const before = await cdp.eval(
      `(() => { const c = window.__deosDoc; return {
        conflict: c.hasConflict(),
        receipts: c.receiptCount(),
        boundary: c.commitmentHex(),
        cell: c.cellId(),
        matches: c.boundaryMatchesProjection(),
        hasStitch: !!document.querySelector('.deos-button[data-turn="stitch"]'),
      }; })()`,
    );
    console.log('  published base:', JSON.stringify(before));
    assert(before.conflict === false, 'the base document is published, no conflict yet');
    assert(before.receipts >= 1, 'the base publish left a real verified-turn receipt');
    assert(before.boundary && before.boundary.length === 64 && !/^0+$/.test(before.boundary),
      'the doc-cell carries a real umem boundary (heap_root) — the committed commitment');
    assert(before.matches, 'the committed umem boundary equals the canonical document projection');
    assert(before.hasStitch, 'the published surface offers the `stitch` affordance');

    // 3. CLICK `stitch` → the categorical pushout surfaces a first-class conflict (held off-heap).
    await cdp.eval(`document.querySelector('.deos-button[data-turn="stitch"]').click()`);
    await sleep(300);
    const stitched = await cdp.eval(
      `(() => { const c = window.__deosDoc; return {
        conflict: c.hasConflict(),
        receipts: c.receiptCount(),
        boundary: c.commitmentHex(),
        alternatives: c.alternativesJson(),
        resolveButtons: document.querySelectorAll('.deos-button[data-turn="resolve"]').length,
        columns: document.querySelectorAll('#deos-doc-root .deos-row .deos-vstack').length,
      }; })()`,
    );
    console.log('  after stitch:', JSON.stringify(stitched));
    assert(stitched.conflict === true, 'the stitch surfaced a first-class CONFLICT (the antichain)');
    assert(stitched.boundary === before.boundary,
      'the conflict is HELD OFF-HEAP: the committed umem boundary is UNCHANGED');
    assert(stitched.receipts === before.receipts,
      'no publish happened on stitch: the receipt tape is unchanged');
    assert(stitched.resolveButtons >= 2, 'the ConflictView offers resolution buttons (keep-each / order)');
    assert(stitched.columns === 2, 'the two alternatives render side-by-side (two attributed columns)');
    const alts = JSON.parse(stitched.alternatives);
    const authors = alts.map((a) => a.author).sort();
    console.log('  alternatives:', JSON.stringify(alts));
    assert(authors.join(',') === 'alice,bob', 'the two alternatives are attributed to alice and bob');

    // 4. CLICK a resolution that KEEPS BOTH (order) → a REAL verified turn publishing the merge.
    const clicked = await cdp.eval(
      `(() => {
        const btns = [...document.querySelectorAll('.deos-button[data-turn="resolve"]')];
        const order = btns.find((b) => /keep both/i.test(b.textContent)) || btns[0];
        const label = order.textContent;
        order.click();
        return label;
      })()`,
    );
    console.log('  resolved via:', JSON.stringify(clicked));
    await sleep(300);
    const after = await cdp.eval(
      `(() => { const c = window.__deosDoc; return {
        conflict: c.hasConflict(),
        receipts: c.receiptCount(),
        boundary: c.commitmentHex(),
        matches: c.boundaryMatchesProjection(),
        text: c.publishedText(),
      }; })()`,
    );
    console.log('  after resolve+publish:', JSON.stringify(after));
    assert(after.conflict === false, 'the resolution collapsed the conflict');
    assert(after.receipts === before.receipts + 1,
      'exactly one more verified turn committed — the merged document PUBLISHED');
    assert(after.boundary !== before.boundary,
      'the umem boundary (heap_root) MOVED — the resolved document is the new committed commitment');
    assert(after.matches, 'the new umem boundary still equals the canonical projection (anti-forge invariant holds)');
    assert(/Alice/.test(after.text) && /Bob/.test(after.text),
      'the "keep both" (order) resolution published BOTH authors\' lines');

    // 5. Capture a screenshot of the published document.
    const shot = await cdp.send('Page.captureScreenshot', { format: 'png' });
    writeFileSync(SHOT, Buffer.from(shot.data, 'base64'));
    console.log('  screenshot:', SHOT);

    console.log('\nPASS: fork → diverge → stitch → a first-class conflict held off-heap → resolve → published to the umem-heap as a real verified turn, in a browser TAB, node-less.');
  } finally {
    cleanup();
  }
}

main().catch((e) => {
  console.error('driver error:', e);
  process.exit(1);
});
