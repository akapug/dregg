// escape.test.mjs — the launchpad pages build markup only through app.js's
// `html` tag, which escapes every interpolated value that is not itself an
// `html` result. Run: node --test test/
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { esc, html, setHtml, SafeHtml, chip, phaseBadge } from '../public/js/app.js';

const PUBLIC = fileURLToPath(new URL('../public/', import.meta.url));
const XSS = `<img src=x onerror="alert(1)">'\`&`;

test('esc neutralises every markup-significant character', () => {
  assert.equal(esc(XSS), '&lt;img src=x onerror=&quot;alert(1)&quot;&gt;&#39;&#96;&amp;');
  assert.equal(esc(null), '');
  assert.equal(esc(undefined), '');
  assert.equal(esc(42), '42');
});

test('a creator-chosen token name and symbol cannot open a tag in the title', () => {
  const L = { name: XSS, symbol: '<script>steal()</script>', id: '7', phase: '<b>Cleared</b>' };
  const out = String(html`${L.name || 'launch'} <span class="tick">$${L.symbol || ''}</span> · #${L.id} ${phaseBadge(L.phase)}`);
  assert.ok(!out.includes('<img'), out);
  assert.ok(!out.includes('<script'), out);
  assert.ok(!out.includes('<b>'), out);
  assert.ok(out.includes('<span class="tick">$&lt;script&gt;'), out);
  assert.ok(out.includes('<span class="badge ">&lt;b&gt;Cleared&lt;/b&gt;</span>'), out);
});

test('nested html results and arrays pass through; plain strings inside them do not', () => {
  const rows = ['<i>a</i>', '<i>b</i>'].map((x) => html`<li>${x}</li>`);
  assert.equal(String(html`<ul>${rows}</ul>`), '<ul><li>&lt;i&gt;a&lt;/i&gt;</li><li>&lt;i&gt;b&lt;/i&gt;</li></ul>');
  assert.equal(String(html`${chip('PROVED')}`), '<span class="chip PROVED">PROVED</span>');
  assert.equal(String(html`${chip('"><x')}`), '<span class="chip &quot;&gt;&lt;x">&quot;&gt;&lt;x</span>');
});

test('setHtml refuses a raw string', () => {
  const el = { innerHTML: '' };
  assert.throws(() => setHtml(el, '<img src=x>'), TypeError);
  assert.equal(el.innerHTML, '');
  setHtml(el, html`<p>${XSS}</p>`);
  assert.ok(el.innerHTML.startsWith('<p>&lt;img'));
  assert.ok(html`` instanceof SafeHtml);
});

function sources(dir) {
  return readdirSync(dir, { withFileTypes: true }).flatMap((d) => {
    const p = join(dir, d.name);
    if (d.isDirectory()) return d.name === 'vendor' ? [] : sources(p);
    return /\.(html|js|mjs)$/.test(d.name) ? [p] : [];
  });
}

test('no page writes innerHTML except through setHtml, and no inline handler interpolates', () => {
  const offenders = [];
  for (const f of sources(PUBLIC)) {
    const lines = readFileSync(f, 'utf8').split('\n');
    lines.forEach((line, i) => {
      const where = `${f.slice(PUBLIC.length)}:${i + 1}`;
      const isSetHtml = f.endsWith(join('js', 'app.js')) && line.trim() === 'el.innerHTML = h.s;';
      if (/(innerHTML|outerHTML)\s*[+]?=|insertAdjacentHTML|document\.write/.test(line) && !isSetHtml) offenders.push(where);
      if (/\son[a-z]+="[^"]*\$\{/.test(line)) offenders.push(where + ' (inline handler)');
    });
  }
  assert.deepEqual(offenders, []);
});
