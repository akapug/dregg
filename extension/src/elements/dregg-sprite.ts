/**
 * `<dregg-sprite kind="gear" asset="<hex>">` — THE IN-HOUSE SPRITE, PAINTED IN THE TAB.
 *
 * The deterministic generative `content-addressed asset → SVG` renderer
 * (`dreggnet-sprite/src/lib.rs`, exposed as the wasm getter `spriteSvg`,
 * `wasm/src/bindings_sprite.rs`) made VISIBLE: the element takes an asset id + a kind, asks
 * the sprite port for the SVG, and paints it into its CLOSED shadow root. The whole point is
 * DETERMINISM — **the same asset id ⇒ the byte-identical sprite** a stranger re-renders off
 * the same content address, and a different id ⇒ a different sprite.
 *
 * It is a THIN VIEW, exactly like `<dregg-poll>` / `<dregg-descent>`:
 *  - the render surface is a **closed** shadow root (`attachShadow({mode:"closed"})`), the
 *    handle kept in a module-private `WeakMap` — a hostile page cannot read or rewrite the art;
 *  - the SVG is engine-authored (from the deterministic renderer, NOT the page), so it is
 *    safe to inject — it is exactly what the renderer produced for `(kind, asset)`;
 *  - an unrenderable input (a bad kind / non-hex / wrong-length id) FAILS CLOSED: it renders
 *    NOTHING and reflects `[error]`, never a fake sprite.
 *
 * Unlike the poll/story/descent views there is NO trust tier, NO key, NO custody: a sprite is
 * a pure function of public data, so there is nothing to "verify by a signature" — the honest
 * claim is only that this SVG is the deterministic render of this asset id, re-derivable by
 * anyone. The element reflects `[kind] [asset] [rendered]` (+ `[rarity]` from the trait
 * vector) so the page and a11y tools can read what was painted; these are public facts.
 */

import { DreggElement } from "./dregg-poll";
import type {
  SpritePort,
  SpritePortRequest,
  SpritePortResponse,
  SpriteRenderResponse,
  SpriteTraitsResponse,
  SpriteKind,
} from "../port";

/** The port factory the element uses to reach the engine. Overridable for tests
 *  (the fixture routes it in-page to a `SpriteEngine` over a deterministic renderer). */
export type SpritePortFactory = () => SpritePort;
let spritePortFactory: SpritePortFactory | null = null;
export function setSpritePortFactory(f: SpritePortFactory): void {
  spritePortFactory = f;
}

/** The default transport: a `chrome.runtime` message hop to the background SpriteEngine
 *  (which drives the wasm `spriteSvg`). The router wraps results as `{ result }` | `{ error }`. */
function chromeMessagePort(): SpritePort {
  return {
    async request(req: SpritePortRequest): Promise<SpritePortResponse> {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:sprite", ...req });
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as SpritePortResponse;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return { ok: false, error: String((resp as { error: unknown }).error) } as SpriteRenderResponse;
      }
      return resp as SpritePortResponse;
    },
  };
}

function getSpritePort(): SpritePort {
  return (spritePortFactory ?? chromeMessagePort)();
}

const STYLE = `
:host { display: inline-block; line-height: 0; }
.wrap { border: 1px solid #7c6cf0; border-radius: 10px; padding: 6px; background: #faf9ff; display: inline-block; }
.art { display: block; width: var(--dregg-sprite-size, 128px); height: var(--dregg-sprite-size, 128px); }
.art svg { display: block; width: 100%; height: 100%; }
.cap { font-family: system-ui, sans-serif; font-size: 10px; color: #6a5acd; text-align: center; margin-top: 4px; line-height: 1.2; text-transform: capitalize; }
.cap:empty { display: none; }
`;

// The closed shadow roots — off-instance so nothing on the element (reachable by the page)
// exposes them. Keyed weakly by element.
const CLOSED_ROOTS = new WeakMap<DreggSprite, ShadowRoot>();

const VALID_KINDS = new Set<string>(["gear", "card"]);

/** `<dregg-sprite>` — the in-house deterministic sprite, painted in a closed shadow. */
export class DreggSprite extends DreggElement {
  private sprite: SpritePort = getSpritePort();

  static get observedAttributes(): string[] {
    return ["asset", "kind"];
  }

  get asset(): string {
    return this.getAttribute("asset") || "";
  }

  get kind(): SpriteKind {
    const k = (this.getAttribute("kind") || "gear").toLowerCase();
    return (VALID_KINDS.has(k) ? k : "gear") as SpriteKind;
  }

  /** Override the poll boot: fetch the deterministic SVG for `(kind, asset)` and paint it. */
  protected async boot(): Promise<void> {
    this.booted = true;
    const asset = this.asset;
    if (!asset) return this.failClosedSprite("no asset id");
    const kind = this.kind;

    let resp: SpriteRenderResponse;
    try {
      resp = (await this.sprite.request({ op: "renderSprite", kind, asset })) as SpriteRenderResponse;
    } catch (e) {
      return this.failClosedSprite(String((e as Error)?.message ?? e));
    }
    if (!resp || !resp.ok || !resp.svg) {
      return this.failClosedSprite(resp?.error || "could not render the sprite");
    }
    this.paint(kind, asset, resp.svg);

    // Best-effort trait vector for the caption + a reflected [rarity] (never load-bearing —
    // a traits miss leaves the sprite painted and simply omits the caption/attribute).
    try {
      const t = (await this.sprite.request({ op: "spriteTraits", kind, asset })) as SpriteTraitsResponse;
      if (t.ok && t.traitsJson) this.applyTraits(t.traitsJson);
    } catch {
      /* the sprite is already painted; the caption is decorative. */
    }
  }

  /** Abstract on the base (poll flow); the sprite overrides boot(). */
  protected async renderVerified(): Promise<void> {
    /* unused — the sprite overrides boot() and speaks the sprite port. */
  }

  /** Attach the closed shadow and paint the engine-authored SVG. Reflects `[kind] [asset]
   *  [rendered]`. Same `(kind, asset)` ⇒ the identical painted SVG (deterministic). */
  private paint(kind: SpriteKind, asset: string, svg: string): void {
    const root = this.attachClosed();
    const style = document.createElement("style");
    style.textContent = STYLE;
    const wrap = document.createElement("div");
    wrap.className = "wrap";
    const art = document.createElement("div");
    art.className = "art";
    art.setAttribute("role", "img");
    art.setAttribute("aria-label", `${kind} sprite ${asset.slice(0, 8)}`);
    // The SVG is exactly what the deterministic renderer produced for (kind, asset) — safe
    // to inject (engine-authored, not the page). Same input ⇒ byte-identical string.
    art.innerHTML = svg;
    const cap = document.createElement("div");
    cap.className = "cap";
    wrap.replaceChildren(art, cap);
    root.replaceChildren(style, wrap);

    this.setAttribute("kind", kind);
    this.setAttribute("asset", asset);
    this.setAttribute("rendered", "");
    this.removeAttribute("error");

    exposeRootForTest(this, root);
  }

  /** Fill the caption + reflect `[rarity]` from the derived trait vector (decorative). */
  private applyTraits(traitsJson: string): void {
    let traits: { rarity?: { name?: string } } | null = null;
    try {
      traits = JSON.parse(traitsJson);
    } catch {
      return;
    }
    const rarity = traits?.rarity?.name;
    const root = CLOSED_ROOTS.get(this);
    if (rarity && root) {
      this.setAttribute("rarity", rarity);
      const cap = root.querySelector(".cap") as HTMLElement | null;
      if (cap) cap.textContent = `${rarity} ${this.kind}`;
    }
  }

  /** Fail-closed: render NOTHING (no shadow art), reflect `[error]`, drop `[rendered]`. A
   *  sprite has no external link to fall back to — the honest state is simply "not rendered". */
  private failClosedSprite(reason: string): void {
    this.removeAttribute("rendered");
    this.removeAttribute("rarity");
    this.setAttribute("error", "");
    this.setAttribute("title", `dregg: could not render this sprite (${reason})`);
  }

  /** Attach (once) a closed shadow root, kept off-instance (the page can't reach it). */
  private attachClosed(): ShadowRoot {
    let root = CLOSED_ROOTS.get(this);
    if (!root) {
      root = this.attachShadow({ mode: "closed" });
      CLOSED_ROOTS.set(this, root);
    }
    return root;
  }
}

/** Test hook (never populated in production): expose the closed root so the harness can
 *  read it. Gated on an explicit global flag, exactly like `<dregg-descent>`'s
 *  `__dreggDescentRoots`. */
function exposeRootForTest(el: Element, root: ShadowRoot): void {
  if ((globalThis as unknown as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
    const reg = ((globalThis as unknown as { __dreggSpriteRoots?: WeakMap<Element, ShadowRoot> }).__dreggSpriteRoots ??=
      new WeakMap());
    reg.set(el, root);
  }
}

/** Register the `<dregg-sprite>` custom element (idempotent). Call from the content script. */
export function registerSpriteElement(): void {
  if (typeof customElements === "undefined" || customElements === null) return; // null in Chromium isolated worlds
  if (!customElements.get("dregg-sprite")) customElements.define("dregg-sprite", DreggSprite);
}
