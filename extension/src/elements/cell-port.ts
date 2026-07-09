/**
 * The shared plumbing for the composition thin views (`<dregg-embed>` and
 * `<dregg-transclude>`): the transport hop to the CellEngine, the pin/ancestor
 * parsing, and the closed-shadow test-exposure registry.
 *
 * This mirrors `dregg-poll.ts`'s port split exactly — the element is a VIEW, the
 * engine (background) owns wasm/keys/caps — but speaks the composition protocol
 * (`dregg:cell`) instead of the poll protocol (`dregg:poll`). Nothing here
 * touches wasm or a key; it only marshals `{ resolveCell | resolveValue }`
 * requests and reads back tiered responses.
 */

import { canonicalUri, type CellPort, type CellPortRequest, type CellPortResponse, type Pin } from "../port";

/** The port factory the composition elements use to reach the engine.
 * Overridable for tests (the fixture routes it in-page to a real CellEngine). */
export type CellPortFactory = () => CellPort;
let cellPortFactory: CellPortFactory | null = null;
export function setCellPortFactory(f: CellPortFactory): void {
  cellPortFactory = f;
}

/** The default transport: a `chrome.runtime` message hop to the background
 * CellEngine. The router wraps handler results as `{ id, result }` | `{ error }`. */
function chromeMessagePort(): CellPort {
  return {
    async request(req: CellPortRequest): Promise<CellPortResponse> {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:cell", ...req });
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as CellPortResponse;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return {
          ok: false,
          state: "unresolved",
          tier: "none",
          error: String((resp as { error: unknown }).error),
        } as CellPortResponse;
      }
      return resp as CellPortResponse;
    },
  };
}

export function getCellPort(): CellPort {
  return (cellPortFactory ?? chromeMessagePort)();
}

/** Parse the `pin` attribute: `pin="live"` (default) | `pin="at:<receipt>"`. */
export function parsePin(el: HTMLElement): Pin {
  const raw = (el.getAttribute("pin") || "live").trim();
  if (!raw || raw === "live") return { kind: "live" };
  const m = /^at:(.+)$/.exec(raw);
  if (m) return { kind: "at", receipt: m[1].trim() };
  return { kind: "live" };
}

/**
 * Walk OUT through the closed shadow boundaries collecting the canonical uris of
 * the ancestor `<dregg-embed>`s. The composition tree IS the DOM: a nested embed
 * lives inside its parent's (closed) shadow root, so `getRootNode()` returns that
 * root even from inside a closed shadow, and `.host` is the parent embed. This is
 * how the ENGINE learns the ancestor chain to decide a cycle — the element never
 * decides trust, it only reports the shape it sits in.
 */
export function ancestorChain(el: HTMLElement): string[] {
  const chain: string[] = [];
  let node: Node = el;
  for (let hops = 0; hops < 64; hops++) {
    const root = node.getRootNode();
    if (!(root instanceof ShadowRoot)) break; // reached the top-level document
    const host = root.host as HTMLElement | null;
    if (!host) break;
    if (host.tagName === "DREGG-EMBED") {
      const raw = host.getAttribute("data-canonical") || host.getAttribute("src") || "";
      const canon = canonicalUri(raw) ?? raw;
      if (canon) chain.unshift(canon); // outermost first
    }
    node = host;
  }
  return chain;
}

/** HTML-escape for the citation/provenance text we author (never engine html). */
export function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

/** Test hook (never populated in production): expose a closed root so the
 * harness can read/assert it. Gated on an explicit global flag, exactly like
 * `<dregg-poll>`'s `__dreggPollRoots`. */
export function exposeRootForTest(el: Element, root: ShadowRoot): void {
  if ((globalThis as unknown as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
    const reg = ((globalThis as unknown as { __dreggComposeRoots?: WeakMap<Element, ShadowRoot> }).__dreggComposeRoots ??=
      new WeakMap());
    reg.set(el, root);
  }
}

/** The shared styles for both composition views — the frame, the citation badge,
 * and the four non-rendered states (darkened / unresolved / cycle / unbound). */
export const COMPOSE_STYLE = `
:host { display: block; font-family: system-ui, sans-serif; }
:host([hidden]) { display: none; }
.embed { border: 1px solid #cdbff2; border-left: 3px solid #7c6cf0; border-radius: 8px; padding: 8px 10px; margin: 4px 0; background: #fbfaff; color: #1c1830; }
.quote { border: 1px solid #cdbff2; border-left: 3px solid #2f7d32; border-radius: 8px; padding: 8px 10px; margin: 4px 0; background: #f7fbf7; color: #1c1830; }
.child { font-size: 14px; }
.cite { font-size: 11px; color: #5a5470; margin-top: 6px; display: flex; flex-wrap: wrap; gap: 6px; align-items: baseline; }
.cite a { color: #4030a0; }
.cite .who { color: #2f7d32; }
.state { font-size: 12px; padding: 6px 8px; border-radius: 6px; }
.state.darkened { background: #efeaf7; color: #4a4460; border: 1px dashed #b7a9e0; }
.state.unresolved { background: #fdeeec; color: #b02a37; border: 1px solid #f0b7b0; }
.state.cycle { background: #fff6e6; color: #8a5a00; border: 1px solid #f0d29a; }
.state.unbound { background: #eef2fb; color: #3a4a7a; border: 1px solid #b7c4e6; }
.state .label { font-weight: 600; }
.state .lnk { display: block; margin-top: 4px; font-size: 11px; }
.state .lnk a { color: #4030a0; }
`;
