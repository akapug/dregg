/**
 * In-page test harness for the in-house sprite, painted in-tab (`<dregg-sprite>`).
 *
 * It wires the REAL modules — the `<dregg-sprite>` thin view (closed shadow) and the
 * `SpriteEngine` — and routes the sprite port in-page to the engine. Everything
 * security- and correctness-relevant — the closed shadow, the engine-authored SVG, the
 * DETERMINISM (same asset ⇒ the byte-identical sprite), and fail-closed on a bad input — is
 * the shipping code path. The ONLY thing shimmed is the transport hop (routed in-page to
 * the engine).
 *
 * The real renderer is the wasm `dreggnet-sprite` getter (`spriteSvg` / `traitsJson`,
 * wasm/src/bindings_sprite.rs), proven deterministic by its native `cargo test`. This
 * fixture stands in an in-memory DETERMINISTIC renderer implementing the exact surface
 * (`spriteSvg(kind, asset)` / `traitsJson(kind, asset)`, both pure, both throwing on a bad
 * kind / non-hex / wrong-length id) — exactly as the dregg-descent fixture stands in a
 * `DescentWorld` — so the element test does not block on a wasm build. The stand-in is a
 * pure function of `(kind, asset)`, so it exercises the very property the element must
 * carry across the port: same asset ⇒ the byte-identical painted SVG; a different id ⇒ a
 * different sprite; the two kinds differ.
 */
import { SpriteEngine, type SpriteRenderer } from "../../src/port";
import { setSpritePortFactory, registerSpriteElement } from "../../src/elements/dregg-sprite";

declare const window: any;

// ── The in-memory DETERMINISTIC stand-in renderer ────────────────────────────

const RARITY_NAMES = ["common", "uncommon", "rare", "epic", "legendary"];

/** A tiny FNV-1a over the input — deterministic (a pure function of the bytes). */
function fnv1a(s: string): number {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
  }
  return h >>> 0;
}

function parseKind(kind: string): "gear" | "card" {
  const k = kind.toLowerCase();
  if (k !== "gear" && k !== "card") throw new Error(`unknown sprite kind ${JSON.stringify(kind)}`);
  return k;
}

function parseAsset(asset: string): string {
  const hex = asset.startsWith("0x") ? asset.slice(2) : asset;
  if (hex.length !== 64) throw new Error(`asset id must be 32 bytes (64 hex chars), got ${hex.length}`);
  if (!/^[0-9a-fA-F]+$/.test(hex)) throw new Error("asset id is not valid hex");
  return hex.toLowerCase();
}

/** A deterministic stand-in for the wasm renderer: a pure function of `(kind, asset)`. */
const standInRenderer: SpriteRenderer = {
  spriteSvg(kind: string, asset: string): string {
    const k = parseKind(kind);
    const hex = parseAsset(asset);
    const seed = fnv1a(k + ":" + hex);
    const hue = seed % 360;
    const tier = seed % 5;
    // A composed, well-formed SVG — deterministic in (kind, asset). The kind selects the
    // silhouette, the seed drives the hue + a couple of shapes, so a different id ⇒ a
    // different sprite and the two kinds differ.
    const bg = `hsl(${hue} 60% 92%)`;
    const fg = `hsl(${hue} 70% 40%)`;
    const shape =
      k === "gear"
        ? `<path d="M64 14 L72 70 L59 80 L56 70 Z" fill="${fg}"/><rect x="40" y="80" width="48" height="8" fill="${fg}"/>`
        : `<circle cx="64" cy="60" r="28" fill="${fg}"/><rect x="20" y="20" width="88" height="88" fill="none" stroke="${fg}" stroke-width="4"/>`;
    return (
      `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 128 128" data-kind="${k}" data-asset="${hex.slice(0, 8)}" data-tier="${tier}">` +
      `<rect width="128" height="128" fill="${bg}"/>${shape}</svg>`
    );
  },
  traitsJson(kind: string, asset: string): string {
    const k = parseKind(kind);
    const hex = parseAsset(asset);
    const seed = fnv1a(k + ":" + hex);
    const tier = seed % 5;
    return JSON.stringify({
      kind: k,
      rarity: { name: RARITY_NAMES[tier], tier },
      fingerprint: (seed >>> 0).toString(16).padStart(8, "0"),
      axes: k === "gear" ? { blade: seed % 4, gem: (seed >> 3) % 6 } : { emblem: seed % 6, pips: 2 + (seed % 5) },
    });
  },
};

// ── wire the engine + element ────────────────────────────────────────────────

(async () => {
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  const engine = new SpriteEngine({ renderer: standInRenderer });

  // Route the sprite port in-page directly to the engine (the REAL element uses this
  // factory to reach what is, in production, the background SpriteEngine driving the wasm).
  setSpritePortFactory(() => ({
    async request(req: any) {
      return engine.handle(req);
    },
  }));

  registerSpriteElement();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
