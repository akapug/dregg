/**
 * The content script — the trusted-path bridge between the page's
 * `window.dregg` provider and the background service-worker that holds the key.
 *
 * It runs in the extension's isolated world (the page cannot read it), injects
 * `page.js` (which defines `window.dregg`), and relays the narrow provider
 * protocol over:
 *
 *   - a per-injection nonce-scoped CustomEvent channel to the page (a page
 *     cannot guess the nonce, so it cannot spoof the content script's replies);
 *   - a long-lived `chrome.runtime` port to the background.
 *
 * It stamps the VERIFIED page origin (`window.location.origin`, read here in the
 * isolated world — not from page-supplied data) on every forwarded request, so
 * the background always knows who is asking. Restricted methods (`dregg:turn`)
 * are still fully gated by the user's approval popup in the background; the
 * origin stamp is for the reading and any future per-origin allowlist.
 */

import type { ProviderMethod, ProviderRequest, ProviderResponse } from "./protocol";
import { RESTRICTED_METHODS, UNRESTRICTED_METHODS } from "./protocol";

// A fresh nonce per injection: the page learns it only via the data attribute on
// the injected script tag, scoping the event channel to this content script.
const NONCE = crypto.randomUUID();

// Inject the page provider, handing it the nonce.
const script = document.createElement("script");
script.src = chrome.runtime.getURL("dist/page.js");
script.dataset.dreggNonce = NONCE;
(document.head || document.documentElement).appendChild(script);
script.onload = (): void => script.remove();

// One long-lived port to the background; reconnect lazily if the worker sleeps.
let port: chrome.runtime.Port | undefined;
const inflight = new Map<string, (r: ProviderResponse) => void>();

function connect(): chrome.runtime.Port {
  const p = chrome.runtime.connect({ name: "dregg" });
  p.onMessage.addListener((resp: ProviderResponse) => {
    const cb = inflight.get(resp.id);
    if (cb) {
      inflight.delete(resp.id);
      cb(resp);
    }
  });
  p.onDisconnect.addListener(() => {
    port = undefined;
    // Fail any inflight requests so the page promise rejects rather than hangs.
    for (const [id, cb] of inflight) cb({ id, ok: false, error: "extension worker disconnected" });
    inflight.clear();
  });
  return p;
}

function send(req: ProviderRequest, origin: string): Promise<ProviderResponse> {
  if (!port) port = connect();
  return new Promise((resolve) => {
    inflight.set(req.id, resolve);
    (port as chrome.runtime.Port).postMessage({ ...req, _origin: origin });
  });
}

// Page -> content-script: a provider request on the nonce-scoped channel.
window.addEventListener(`dregg:request:${NONCE}`, (async (event: Event): Promise<void> => {
  const detail = (event as CustomEvent).detail as ProviderRequest | undefined;
  if (!detail || !detail.type || !detail.id) return;
  const method = detail.type as ProviderMethod;
  const origin = window.location.origin;

  const reply = (resp: ProviderResponse): void => {
    window.dispatchEvent(new CustomEvent(`dregg:response:${NONCE}`, { detail: resp }));
  };

  // Only known methods cross the boundary; the user-approval gate for restricted
  // methods lives in the background popup (not bypassable from here).
  if (!UNRESTRICTED_METHODS.has(method) && !RESTRICTED_METHODS.has(method)) {
    reply({ id: detail.id, ok: false, error: `method "${method}" is not available from a page` });
    return;
  }

  try {
    reply(await send(detail, origin));
  } catch (e) {
    reply({ id: detail.id, ok: false, error: e instanceof Error ? e.message : String(e) });
  }
}) as EventListener);
