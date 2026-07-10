/**
 * `<dregg-story src="dregg://story/…">` — THE VERIFIABLE CHOOSE-YOUR-OWN-ADVENTURE.
 * A reader reads a passage, picks a choice (a REAL verified turn), the story
 * advances, and a stranger can replay the whole receipt chain.
 * docs/MEGASPEC-worlds-ide-and-the-verified-web.md §4.
 *
 * The two-tier split is the whole point (§4.3):
 *  - READ + VERIFY are the FREE, trustless tier — the story's prose renders and
 *    a "✓ replay-verified" badge is shown with NO extension and NO custody (a bare
 *    browser can SEE and re-check the receipt chain).
 *  - CHOOSING is a CUSTODY WRITE — a choice is a real verified turn, so it routes
 *    through the un-overlayable confirm-intent consent BEFORE it advances. Absent
 *    custody, the choices degrade to read-only with an honest note (never a fake).
 *
 * It is a THIN VIEW, exactly like `<dregg-doc>` / `<dregg-poll>`: a **closed**
 * shadow root (the page cannot read or rewrite the render), NO wasm, NO keys, NO
 * story graph — every fact comes back tiered through the port from the background
 * `StoryEngine`. It REUSES `DreggElement` (closed shadow, trust reflection,
 * fail-closed) but overrides the boot flow to speak the story port. An
 * unresolvable/bad scene renders NOTHING (fallback link + warning). It NEVER hides
 * its trust tier — a reflected `trust=…` + a visible badge always say who checked.
 */

import { DreggElement } from "./dregg-poll";
import type {
  StoryPort,
  StoryPortRequest,
  StoryPortResponse,
  StoryResolveResponse,
  StoryRenderResponse,
  StoryChooseResponse,
  StoryVerifyResponse,
  StoryChoice,
  TrustTier,
} from "../port";

/** The port factory the element uses to reach the engine. Overridable for tests
 *  (the fixture routes it in-page to a `StoryEngine` over an in-memory StoryWorld). */
export type StoryPortFactory = () => StoryPort;
let storyPortFactory: StoryPortFactory | null = null;
export function setStoryPortFactory(f: StoryPortFactory): void {
  storyPortFactory = f;
}

/** The default transport: a `chrome.runtime` message hop to the background
 *  StoryEngine. The router wraps handler results as `{ id, result }` | `{ error }`. */
function chromeMessagePort(): StoryPort {
  return {
    async request(req: StoryPortRequest): Promise<StoryPortResponse> {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:story", ...req });
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as StoryPortResponse;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return { ok: false, tier: "none", verified: false, error: String((resp as { error: unknown }).error) } as StoryPortResponse;
      }
      return resp as StoryPortResponse;
    },
  };
}

function getStoryPort(): StoryPort {
  return (storyPortFactory ?? chromeMessagePort)();
}

// The badge surfaces BOTH the trust tier (who checked) AND the story-specific
// semantic (the whole receipt chain replays). A tier is never hidden.
const BADGE: Record<TrustTier, string> = {
  extension: "✓ replay-verified by your cipherclerk",
  sdk: "✓ replay-verified in this page",
  server: "✓ replay-verified by dregg.net (trust the origin)",
  none: "⚠ unverified — original link shown",
};

const STYLE = `
:host { display: block; font-family: system-ui, sans-serif; }
.wrap { border: 1px solid #7c6cf0; border-radius: 10px; padding: 12px 14px; background: #faf9ff; color: #1c1830; max-width: 42em; }
.title { font-weight: 600; font-size: 13px; margin-bottom: 8px; color: #4030a0; }
.passage { font-size: 15px; line-height: 1.55; white-space: pre-wrap; }
.choices { display: flex; flex-direction: column; gap: 8px; margin-top: 12px; }
.choices button { font: inherit; font-size: 14px; padding: 7px 12px; border: 1px solid #7c6cf0; border-radius: 8px; background: #fff; color: #4030a0; cursor: pointer; text-align: left; }
.choices button:hover:not(:disabled) { background: #7c6cf0; color: #fff; }
.choices button:disabled { opacity: .55; cursor: default; }
.choices button.gated::after { content: " 🔒"; }
.readonly-note { font-size: 12px; color: #8a5a00; margin-top: 10px; }
.readonly-note:empty { display: none; }
.note { font-size: 12px; color: #b02a37; margin-top: 8px; }
.note:empty { display: none; }
.badge { font-size: 11px; margin-top: 12px; color: #2f7d32; }
.badge.none { color: #b02a37; }
.ending { font-size: 12px; color: #4030a0; margin-top: 12px; font-style: italic; }
.ending:empty { display: none; }
:host([readonly]) .wrap { border-style: dashed; }
`;

// The closed shadow roots — off-instance so nothing on the element (reachable by
// the page) exposes them. Keyed weakly by element.
const CLOSED_ROOTS = new WeakMap<DreggStory, ShadowRoot>();

/** `<dregg-story>` — a verifiable choose-your-own-adventure surface. */
export class DreggStory extends DreggElement {
  private story: StoryPort = getStoryPort();
  private uri = "";
  private wired = false;
  private custody = false;

  /** Override the poll boot: resolve the story → render the passage + choices. */
  protected async boot(): Promise<void> {
    this.booted = true;
    const uri = this.src;
    if (!uri) return this.failClosed("no source");
    this.uri = uri;

    let resolved: StoryResolveResponse;
    try {
      resolved = (await this.story.request({ op: "resolveStory", uri })) as StoryResolveResponse;
    } catch (e) {
      return this.failClosed(String((e as Error)?.message ?? e));
    }
    if (!resolved || !resolved.ok || !resolved.verified) {
      return this.failClosed(resolved?.error || "could not verify");
    }
    await this.paintInitial(resolved);
  }

  /** Abstract on the base (poll flow); the story overrides boot(). */
  protected async renderVerified(): Promise<void> {
    /* unused — the story overrides boot() and speaks the story port. */
  }

  /** Build the shell, wire the (single, delegated) click handler on the closed
   *  root, and paint the first passage's prose + its choices. */
  private async paintInitial(resolved: StoryResolveResponse): Promise<void> {
    const render = (await this.story.request({ op: "renderStory", uri: this.uri })) as StoryRenderResponse;
    if (!render.ok) return this.failClosed(render.error || "render failed");

    this.custody = !!(render.custody ?? resolved.custody);

    const root = this.attachClosed();
    const style = document.createElement("style");
    style.textContent = STYLE;
    const wrap = document.createElement("div");
    wrap.className = "wrap";
    wrap.innerHTML =
      `<div class="title">Story — ${escapeHtml(resolved.object?.addr || "")}</div>` +
      `<div class="passage"></div>` +
      `<div class="choices"></div>` +
      `<div class="ending" aria-live="polite"></div>` +
      `<div class="readonly-note" aria-live="polite"></div>` +
      `<div class="note" aria-live="polite"></div>` +
      `<div class="badge"></div>`;
    root.replaceChildren(style, wrap);

    this.injectPassage(root, render);

    // The click wire is bound to the CLOSED root — the page cannot inject choices;
    // only the buttons this element rendered carry a turn.
    if (!this.wired) {
      root.addEventListener("click", (ev) => void this.onShadowClick(ev));
      this.wired = true;
    }

    this.reflectTrust(resolved.tier, true);
    this.setAttribute("receipts", String(resolved.receiptCount ?? 0));
    if (resolved.commitment) this.setAttribute("commitment", resolved.commitment);
    this.paintBadge(root, resolved.tier, true);

    exposeRootForTest(this, root);
  }

  private async onShadowClick(ev: Event): Promise<void> {
    const target = ev.target as HTMLElement | null;
    const btn = target?.closest?.("button[data-choice]") as HTMLElement | null;
    if (!btn || (btn as HTMLButtonElement).disabled) return;
    const index = Number(btn.getAttribute("data-choice") || "0");
    const root = this.closed();
    if (!root) return;
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "";
    this.freeze(root, true);

    let resp: StoryChooseResponse;
    try {
      resp = (await this.story.request({ op: "chooseChoice", uri: this.uri, index })) as StoryChooseResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      this.freeze(root, false);
      return;
    }

    if (resp.refused) {
      // Surface the refusal honestly (gated / consent denied / no custody).
      note.textContent = `⚠ choice refused: ${resp.reason || "refused"}`;
      this.setAttribute("choice-refused", "");
      this.freeze(root, false);
      return;
    }
    this.removeAttribute("choice-refused");

    // Advanced: re-render the NEW passage from the engine (never from the page)
    // and re-verify the badge (the stranger's replay check). injectPassage rebuilds
    // the buttons with their correct takeable state, so no unfreeze is needed.
    await this.repaint(root);
  }

  /** Freeze/thaw the choice row while a turn (and its consent) is in flight. On
   *  thaw a choice is takeable iff it is available (not gated) AND we hold custody. */
  private freeze(root: ShadowRoot, frozen: boolean): void {
    (root.querySelectorAll("button[data-choice]") as NodeListOf<HTMLButtonElement>).forEach((b) => {
      b.disabled = frozen || b.classList.contains("gated") || !this.custody;
    });
  }

  /** Re-render from the engine + re-verify the badge. */
  private async repaint(root: ShadowRoot): Promise<void> {
    const render = (await this.story.request({ op: "renderStory", uri: this.uri })) as StoryRenderResponse;
    if (render.ok) {
      this.custody = !!render.custody;
      this.injectPassage(root, render);
    }

    const verify = (await this.story.request({ op: "verifyStory", uri: this.uri })) as StoryVerifyResponse;
    this.reflectTrust(verify.tier, verify.verified);
    if (!verify.verified) {
      this.removeAttribute("verified");
      this.setAttribute("error", "");
    }
    if (verify.commitment) this.setAttribute("commitment", verify.commitment);
    if (typeof verify.receiptCount === "number") this.setAttribute("receipts", String(verify.receiptCount));
    this.paintBadge(root, verify.tier, verify.verified);
  }

  /** Inject the current passage: its prose, its choices as buttons (a gated choice
   *  is shown but disabled), and — when there is no custody — the honest read-only
   *  degrade note. Reflects `[passage]` and `[readonly]`. */
  private injectPassage(root: ShadowRoot, render: StoryRenderResponse): void {
    const passageEl = root.querySelector(".passage") as HTMLElement;
    passageEl.textContent = render.prose ?? "";
    if (render.passage) this.setAttribute("passage", render.passage);

    const choicesEl = root.querySelector(".choices") as HTMLElement;
    const choices: StoryChoice[] = render.choices ?? [];
    choicesEl.replaceChildren();
    for (const c of choices) {
      const b = document.createElement("button");
      b.type = "button";
      b.dataset.choice = String(c.index);
      b.textContent = c.text;
      // READ shows every choice; CHOOSE needs both availability AND custody.
      const takeable = c.available && this.custody;
      b.disabled = !takeable;
      if (!c.available) b.classList.add("gated");
      choicesEl.appendChild(b);
    }

    const ending = root.querySelector(".ending") as HTMLElement;
    ending.textContent = choices.length === 0 ? "— the end —" : "";

    const roNote = root.querySelector(".readonly-note") as HTMLElement;
    if (!this.custody && choices.length > 0) {
      this.setAttribute("readonly", "");
      roNote.textContent = "connect your cipherclerk to play (reading + verifying is free)";
    } else {
      this.removeAttribute("readonly");
      roNote.textContent = "";
    }
  }

  private paintBadge(root: ShadowRoot, tier: TrustTier, verified: boolean): void {
    const badge = root.querySelector(".badge") as HTMLElement;
    if (!badge) return;
    const shown: TrustTier = verified ? tier : "none";
    badge.textContent = BADGE[shown];
    badge.classList.toggle("none", shown === "none");
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

  private closed(): ShadowRoot | undefined {
    return CLOSED_ROOTS.get(this);
  }
}

function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

/** Test hook (never populated in production): expose the closed root so the
 *  harness can drive/read it. Gated on an explicit global flag, exactly like
 *  `<dregg-poll>`'s `__dreggPollRoots` and `<dregg-doc>`'s `__dreggDocRoots`. */
function exposeRootForTest(el: Element, root: ShadowRoot): void {
  if ((globalThis as unknown as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
    const reg = ((globalThis as unknown as { __dreggStoryRoots?: WeakMap<Element, ShadowRoot> }).__dreggStoryRoots ??=
      new WeakMap());
    reg.set(el, root);
  }
}

/** Register the `<dregg-story>` custom element (idempotent). Call from the content script. */
export function registerStoryElement(): void {
  if (typeof customElements === "undefined") return;
  if (!customElements.get("dregg-story")) customElements.define("dregg-story", DreggStory);
}
