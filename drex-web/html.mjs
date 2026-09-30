// html.mjs — the only way drex-web builds markup. Strings relayed from the live
// node (turn hash, finality, operator, error text) and from the solver/prover
// subprocesses are not ours, so every interpolated value is escaped unless it is
// itself an `html` result (a `SafeHtml`); arrays are joined element-wise under
// the same rule; `setHtml` refuses anything else. No module assigns innerHTML
// directly (test/escape.test.mjs enforces it). launchpad-web/public/js/app.js
// carries the same helper: the two apps are served from separate roots.
export class SafeHtml {
  constructor(s) { this.s = s; }
  toString() { return this.s; }
}
const ESC = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;', '`': '&#96;' };
export const esc = (v) => String(v ?? '').replace(/[&<>"'`]/g, (c) => ESC[c]);
const frag = (v) => v instanceof SafeHtml ? v.s : Array.isArray(v) ? v.map(frag).join('') : esc(v);
export function html(strings, ...vals) {
  let out = strings[0];
  vals.forEach((v, i) => { out += frag(v) + strings[i + 1]; });
  return new SafeHtml(out);
}
export function setHtml(el, h) {
  if (!(h instanceof SafeHtml)) throw new TypeError('setHtml: markup must be built with html``');
  el.innerHTML = h.s;
}
