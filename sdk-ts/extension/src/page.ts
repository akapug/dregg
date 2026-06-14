/**
 * `window.dregg` — the page-side provider the extension injects into every page.
 *
 * This runs in the PAGE's world and holds NO key material. It can only describe
 * a turn (verbs, as JSON) and receive a receipt; the signing key lives in the
 * extension's background worker and never crosses this boundary. The shape
 * mirrors `@dregg/sdk`'s two-noun door so a dapp author writes the same kind of
 * code whether they import the SDK or call this provider:
 *
 *   const id = await window.dregg.identity();        // public cell id (no key)
 *   const receipt = await window.dregg.turn({        // describe a turn …
 *     effects: [{ kind: "transfer", toHex, amount: 100 }],
 *   });                                              // … extension+user approve, sign, submit
 *
 * `turn()` resolves with a `Receipt` view ONLY after the user approves the
 * faithful reading of exactly these effects in the extension popup. A declined
 * turn rejects; the key is never exposed and no signature is produced for the
 * page.
 */

import type { IdentityView, ProviderRequest, ProviderResponse, ReceiptView, TurnRequestSpec } from "./protocol";

const nonce = document.currentScript?.getAttribute("data-dregg-nonce") ?? "";

let counter = 0;
const pending = new Map<string, { resolve: (r: ProviderResponse) => void }>();

window.addEventListener(`dregg:response:${nonce}`, (event: Event): void => {
  const resp = (event as CustomEvent).detail as ProviderResponse | undefined;
  if (!resp || !resp.id) return;
  const p = pending.get(resp.id);
  if (p) {
    pending.delete(resp.id);
    p.resolve(resp);
  }
});

function request(type: ProviderRequest["type"], spec?: TurnRequestSpec): Promise<ProviderResponse> {
  const id = `${Date.now()}-${counter++}`;
  return new Promise((resolve) => {
    pending.set(id, { resolve });
    window.dispatchEvent(new CustomEvent(`dregg:request:${nonce}`, { detail: { type, id, spec } }));
  });
}

async function unwrap<T>(p: Promise<ProviderResponse>): Promise<T> {
  const r = await p;
  if (!r.ok) throw new Error(r.error);
  return r.result as T;
}

/** The injected provider — the page's view of the front door. */
const provider = {
  /** Is the extension present + unlocked (a quick availability probe). */
  async isConnected(): Promise<boolean> {
    try {
      const r = await unwrap<{ connected: boolean }>(request("dregg:isConnected"));
      return r.connected === true;
    } catch {
      return false;
    }
  },

  /** The signing identity HINT — public cell id + public key. NEVER the key. */
  identity(): Promise<IdentityView> {
    return unwrap<IdentityView>(request("dregg:identity"));
  },

  /**
   * Describe a turn and request the user sign+submit it. Resolves with the
   * committed `Receipt` view, or rejects if the user declines. The page never
   * holds the key and never sees a signature; the extension mediates.
   */
  turn(spec: TurnRequestSpec): Promise<ReceiptView> {
    return unwrap<ReceiptView>(request("dregg:turn", spec));
  },
};

declare global {
  interface Window {
    dregg?: typeof provider;
  }
}

// Define once; a second injection (e.g. SPA navigation) is a no-op.
if (!window.dregg) {
  Object.defineProperty(window, "dregg", { value: Object.freeze(provider), configurable: false, writable: false });
}
