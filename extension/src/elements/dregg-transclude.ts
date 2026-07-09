/**
 * `<dregg-transclude src="dregg://cell/field">` — a VALUE QUOTE (the Xanadu
 * quote). DOC-CELL-COMPOSITION.md §1, DREGG-DOCUMENT-FOUNDATION.md §1.3.
 *
 * This is the load-bearing DISTINCTION from `<dregg-embed>`: a transclude imports
 * a *value* — a SNAPSHOT of the bytes a source cell committed at a cited,
 * FINALIZED receipt. It never rots, never updates, and is UNEDITABLE — that is
 * the whole point (a citation of an immutable past, not a live cell). It has NO
 * pin (a value is already frozen), NO turn affordances (you cannot edit a quote),
 * and NO recursion (it is a value, not a subtree).
 *
 * It FAILS CLOSED: an unverifiable quote is never shown as a value — the anchored
 * verifier's `verified === false` renders NOTHING but an honest warning.
 *
 * Like `<dregg-embed>` it reuses `DreggElement` (closed shadow) and overrides the
 * boot flow to speak the composition port's `resolveValue`.
 */

import { DreggElement } from "./dregg-poll";
import type { ResolveValueResponse } from "../port";
import { getCellPort, escapeHtml, exposeRootForTest, COMPOSE_STYLE } from "./cell-port";
import type { CellPort } from "../port";

export class DreggTransclude extends DreggElement {
  private cell: CellPort = getCellPort();

  static get observedAttributes(): string[] {
    return ["src"];
  }

  attributeChangedCallback(name: string, prev: string | null, next: string | null): void {
    if (!this.booted || prev === next) return;
    if (name === "src") void this.boot();
  }

  protected async boot(): Promise<void> {
    this.booted = true;
    const uri = this.src;
    if (!uri) return this.failQuote("no source");

    let resp: ResolveValueResponse;
    try {
      resp = (await this.cell.request({ op: "resolveValue", uri })) as ResolveValueResponse;
    } catch (e) {
      return this.failQuote(String((e as Error)?.message ?? e));
    }
    // Fail CLOSED on a bad quote — an unverifiable value is never rendered.
    if (!resp || !resp.ok || !resp.verified) {
      return this.failQuote(resp?.error || "the quote could not be verified");
    }
    this.paintQuote(uri, resp);
  }

  /** Abstract on the base (poll flow); the transclude never uses it. */
  protected async renderVerified(): Promise<void> {
    /* unused — transclude overrides boot() and speaks the composition port. */
  }

  /** A verified value snapshot: the quoted bytes + a provenance/citation badge.
   * NOT live, NOT editable — a static quote. */
  private paintQuote(uri: string, resp: ResolveValueResponse): void {
    const prov = resp.provenance;
    const cellUri = prov?.cell || uri;
    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = COMPOSE_STYLE;
    const wrap = document.createElement("div");
    wrap.className = "quote";
    wrap.setAttribute("role", "figure");
    // The quoted bytes are a VALUE snapshot — rendered as text (never re-parsed
    // as live markup: a quote is inert, it cannot smuggle affordances).
    const q = document.createElement("blockquote");
    q.className = "child";
    q.style.cssText = "margin:0;font-style:italic;";
    q.textContent = resp.bytes ?? "";
    const cite = document.createElement("div");
    cite.className = "cite";
    cite.innerHTML =
      `<span>❝ verified snapshot of</span> ` +
      `<a href="${escapeHtml(cellUri)}" rel="noopener">${escapeHtml(cellUri)}</a>` +
      (prov?.receipt ? ` <span>@ ${escapeHtml(prov.receipt)}</span>` : "") +
      (prov?.author ? ` <span class="who">by ${escapeHtml(prov.author)}</span>` : "");
    wrap.appendChild(q);
    wrap.appendChild(cite);
    root.replaceChildren(style, wrap);

    this.reflectTrust(resp.tier, true);
    this.setAttribute("state", "quoted");
    this.setAttribute("readonly", "");
    this.removeAttribute("error");
    exposeRootForTest(this, root);
  }

  /** Fail closed: render nothing verified; set [error]; keep any light-DOM
   * fallback; show an honest warning. A bad quote is NEVER shown as a value. */
  private failQuote(reason: string): void {
    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = COMPOSE_STYLE;
    const box = document.createElement("div");
    box.className = "state unresolved";
    box.innerHTML =
      `<span class="label">⚠ quote not shown — could not verify</span>` +
      ` <span class="why">(${escapeHtml(reason)})</span>`;
    root.replaceChildren(style, box);

    this.removeAttribute("verified");
    this.removeAttribute("readonly");
    this.setAttribute("state", "failed");
    this.setAttribute("trust", "none");
    this.setAttribute("error", "");
    exposeRootForTest(this, root);
  }
}
