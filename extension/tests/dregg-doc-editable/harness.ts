/**
 * In-page test harness for the FREE-TEXT authoring path (`<dregg-doc editable>`).
 *
 * It wires the REAL modules — the `<dregg-doc editable>` thin view (closed shadow,
 * contenteditable, keyed reconciler), the `DocTextEngine` over the REAL wasm
 * `DocTextWorld` (the actual `Doc::edit` token-LCS diff → minimal patch + the
 * umem-heap publish turn) — and routes the free-text port in-page to the engine.
 * Everything security- and correctness-relevant — closed shadow, engine-owns-wasm,
 * minimal-patch (not rewrite), caret-preserving repaint, consent-gated publish, the
 * real verified turn, the light-client re-verify, fail-closed — is the shipping code
 * path. The ONLY things shimmed are the transport hop (routed in-page to the engine)
 * and consent (auto-approve, flippable via `window.__DREGG_CONSENT`).
 */
import { DocTextEngine, defaultResolveDocText } from "../../src/port";
import { setDocTextPortFactory, registerDocElement } from "../../src/elements/dregg-doc";

declare const window: any;

(async () => {
  // Let the element register its closed root in a test registry (gated hook).
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  const wb = window.wasm_bindgen;
  await wb("/dregg_wasm_bg.wasm");
  const DocTextWorld = wb.DocTextWorld;

  const engine = new DocTextEngine({
    DocTextWorld,
    // The valid doc-cell is seeded with "the quick brown fox"; a malformed addr
    // fails closed (defaultResolveDocText returns null → the element warns).
    resolveDocText: (uri: string) => defaultResolveDocText(uri),
    // Consent stands in for the confirm-intent chrome; default approve.
    consent: async () => window.__DREGG_CONSENT !== false,
  });

  // Route the free-text port in-page directly to the engine (the REAL element uses
  // this factory to reach what is, in production, the background DocTextEngine).
  setDocTextPortFactory(() => ({
    async request(req: any) {
      return engine.handle(req, location.origin);
    },
  }));

  // THE STRANGER'S CHECK: an INDEPENDENT light-client re-verify. `verifyText`
  // recomputes `substrate_commit(published)` and confirms it equals the committed
  // `heap_root` the receipt bound — driven off the render path.
  window.__dreggTextLightClientVerify = (uri: string) => engine.handle({ op: "verifyText", uri });

  registerDocElement();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
