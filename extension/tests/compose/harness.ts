/**
 * In-page test harness for the composition delivery layer (`<dregg-embed>` +
 * `<dregg-transclude>`).
 *
 * It wires the REAL modules — the `DreggEmbed`/`DreggTransclude` thin views
 * (closed shadow), the `CellEngine` over an in-memory `MapWebOfCells` (the
 * standalone netlayer+membrane stand-in, exactly as `defaultResolveObject` is for
 * polls) — and routes the composition port in-page to the engine. Everything
 * security- and correctness-relevant — closed shadow, engine-owns-the-bytes
 * (darkening withholds), the five states, recursion via nested custom-element
 * upgrade, fail-closed transclude — is the shipping code path.
 *
 * The web-of-cells the fixture composes:
 *   b3_root   → prose + a nested <dregg-embed src=…b3_leaf>   (RECURSION)
 *   b3_leaf   → "LEAFBYTES-…"                                 (the grandchild)
 *   b3_secret → inCap:false, html "SECRETBYTES-…"             (DARKENED: withheld)
 *   b3_a ↔ b3_b → each embeds the other                       (CYCLE)
 *   b3_name   → initially UNBOUND, healed to a cell on refresh (UNBOUND→heal)
 *   b3_quote/body   → a VERIFIED value quote                   (transclude ok)
 *   b3_bad/body     → an UNVERIFIED value quote                (transclude fail-closed)
 */
import { CellEngine, MapWebOfCells } from "../../src/port";
import { setCellPortFactory } from "../../src/elements/cell-port";
import { registerCompositionElements } from "../../src/elements/dregg-embed";

declare const window: any;

(async () => {
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  const web = new MapWebOfCells();
  web
    .setCell("dregg://cell/b3_root", {
      html: `<p>root prose — SEARCHABLE_ROOT</p><dregg-embed src="dregg://cell/b3_leaf"></dregg-embed>`,
      provenance: { cell: "dregg://cell/b3_root", author: "alice" },
      inCap: true,
    })
    .setCell("dregg://cell/b3_leaf", {
      html: `<span>LEAFBYTES-grandchild</span>`,
      provenance: { cell: "dregg://cell/b3_leaf", author: "bob" },
      inCap: true,
    })
    .setCell("dregg://cell/b3_secret", {
      // The engine MUST withhold these bytes on an out-of-cap child.
      html: `<span>SECRETBYTES-should-never-reach-the-page</span>`,
      provenance: { cell: "dregg://cell/b3_secret", author: "carol" },
      inCap: false,
    })
    .setCell("dregg://cell/b3_a", {
      html: `<span>A body</span><dregg-embed src="dregg://cell/b3_b"></dregg-embed>`,
      provenance: { cell: "dregg://cell/b3_a" },
      inCap: true,
    })
    .setCell("dregg://cell/b3_b", {
      html: `<span>B body</span><dregg-embed src="dregg://cell/b3_a"></dregg-embed>`,
      provenance: { cell: "dregg://cell/b3_b" },
      inCap: true,
    })
    .setUnbound("dregg://cell/b3_name")
    .setValue("dregg://cell/b3_quote/body", {
      bytes: "QUOTED-VALUE-snapshot-ok",
      provenance: { cell: "dregg://cell/b3_quote", receipt: "r_deadbeef", author: "dave" },
      verified: true,
    })
    .setValue("dregg://cell/b3_bad/body", {
      bytes: "BADQUOTE-should-never-render",
      provenance: { cell: "dregg://cell/b3_bad", receipt: "r_forged" },
      verified: false, // the anchored verifier refuses → fail closed
    });

  const engine = new CellEngine({ resolveCell: web.resolveCell, resolveValue: web.resolveValue });

  // Route the composition port in-page directly to the engine (the REAL element
  // uses this factory to reach what is, in production, the background CellEngine).
  setCellPortFactory(() => ({
    async request(req: any) {
      return engine.handle(req);
    },
  }));

  // Expose the heal control (the rebind that turns b3_name from unbound → a cell).
  window.__DREGG_HEAL_NAME = () => {
    web.setCell("dregg://cell/b3_name", {
      html: `<span>NOWBOUND-hero-figure</span>`,
      provenance: { cell: "dregg://cell/b3_name", author: "eve" },
      inCap: true,
    });
  };

  registerCompositionElements();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
