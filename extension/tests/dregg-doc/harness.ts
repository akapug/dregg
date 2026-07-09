/**
 * In-page test harness for the verifiable-document authoring path (`<dregg-doc>`).
 *
 * It wires the REAL modules — the `<dregg-doc>` thin view (closed shadow), the
 * `DocEngine` over the REAL wasm `DocCollabWorld` (the actual patch-theory +
 * umem-heap doc world) — and routes the document port in-page to the engine.
 * Everything security- and correctness-relevant — closed shadow, engine-owns-wasm,
 * conflict-as-first-class-state (both alternatives), consent-gated publish, the
 * real verified turn, the light-client re-verify, fail-closed — is the shipping
 * code path. The ONLY things shimmed are the transport hop (routed in-page to the
 * engine) and consent (auto-approve, flippable via `window.__DREGG_CONSENT`).
 *
 * The loaded document `dregg://doc/b3_d0cface` arrives ALREADY carrying a
 * first-class conflict (the resolver asks the engine to surface the divergence),
 * so the element's first render is the ConflictView — both alternatives, attributed.
 */
import { DocEngine, defaultResolveDoc } from "../../src/port";
import { setDocPortFactory, registerDocElement } from "../../src/elements/dregg-doc";

declare const window: any;

(async () => {
  // Let the element register its closed root in a test registry (gated hook).
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  const wb = window.wasm_bindgen;
  await wb("/dregg_wasm_bg.wasm");
  const DocWorld = wb.DocCollabWorld;

  const engine = new DocEngine({
    DocWorld,
    // The valid document arrives carrying a conflict (stitch: true); a malformed
    // addr still fails closed (defaultResolveDoc returns null → the element warns).
    resolveDoc: (uri: string) => {
      const spec = defaultResolveDoc(uri);
      return spec ? { ...spec, stitch: true } : null;
    },
    // Consent stands in for the confirm-intent chrome; default approve.
    consent: async () => window.__DREGG_CONSENT !== false,
  });

  // Route the document port in-page directly to the engine (the REAL element uses
  // this factory to reach what is, in production, the background DocEngine).
  setDocPortFactory(() => ({
    async request(req: any) {
      return engine.handle(req, location.origin);
    },
  }));

  // THE STRANGER'S CHECK: an INDEPENDENT light-client re-verify. `verify`
  // recomputes `substrate_commit(published)` from the document graph and confirms
  // it equals the committed `heap_root` the receipt bound — the "a stranger checks
  // the receipt chain" property, driven off the render path.
  window.__dreggLightClientVerify = (uri: string) => engine.handle({ op: "verify", uri });

  registerDocElement();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
