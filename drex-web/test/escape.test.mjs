// escape.test.mjs — drex-web builds markup only through html.mjs, which escapes
// every interpolated value that is not itself an `html` result.
// Run: node --test drex-web/test/
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { esc, html, setHtml } from '../html.mjs';

const ROOT = fileURLToPath(new URL('../', import.meta.url));
// drex-viz renders SVG from the local fhegg_clear run over a fixed book (no node or
// chain input); its builders return markup strings and are not converted here.
const EXEMPT = new Set(['drex-viz.html', 'drex-viz.js']);

test('esc neutralises every markup-significant character', () => {
  assert.equal(esc(`<img src=x onerror="a()">'\`&`), '&lt;img src=x onerror=&quot;a()&quot;&gt;&#39;&#96;&amp;');
  assert.equal(esc(undefined), '');
});

test('a node-relayed turn hash and error cannot open a tag', () => {
  const r = { turnHash: '<img src=x onerror=alert(1)>', error: '</div><script>x()</script>' };
  const out = String(html`<span class="v hash mono">${r.turnHash}</span><div class="d">${r.error}</div>`);
  assert.ok(!/<img|<script|<\/div><script/.test(out), out);
  const steps = [{ h: 'settle', d: r.error }].map((s) => html`<div class="h">${s.h}</div>${s.d ? html`<div class="d">${s.d}</div>` : ''}`);
  assert.equal(String(html`${steps}`), '<div class="h">settle</div><div class="d">&lt;/div&gt;&lt;script&gt;x()&lt;/script&gt;</div>');
});

test('setHtml refuses a raw string', () => {
  const el = { innerHTML: '' };
  assert.throws(() => setHtml(el, '<b>x</b>'), TypeError);
  assert.equal(el.innerHTML, '');
});

test('no drex-web source writes innerHTML except through setHtml', () => {
  const offenders = [];
  for (const d of readdirSync(ROOT, { withFileTypes: true })) {
    if (!d.isFile() || !/\.(html|js|mjs)$/.test(d.name) || EXEMPT.has(d.name)) continue;
    readFileSync(join(ROOT, d.name), 'utf8').split('\n').forEach((line, i) => {
      const isSetHtml = d.name === 'html.mjs' && line.trim() === 'el.innerHTML = h.s;';
      if (/(innerHTML|outerHTML)\s*[+]?=|insertAdjacentHTML|document\.write/.test(line) && !isSetHtml) offenders.push(`${d.name}:${i + 1}`);
    });
  }
  assert.deepEqual(offenders, []);
});
