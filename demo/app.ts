/**
 * THE COMMONS — the page-SDK demo wiring.
 *
 * A self-contained page (NO extension runtime) that:
 *  1. loads the real wasm-bindgen `StoryWorld` (the collective spween CYOA world);
 *  2. fetches `stories/the-commons.scene` and compiles a REAL `StoryWorld(scene)`;
 *  3. injects a page-side collective `StoryEngine` over it via `setStoryPortFactory`;
 *  4. registers + mounts `<dregg-story collective>` — the exact shipping element;
 *  5. auto-plays a simulated crowd voting each branch (each vote a custody-signed,
 *     consent-gated verified turn on the real `CollectiveChoiceEngine`), advances the
 *     winner, on to an ending, then replays `verify()` — "nothing was rewritten".
 *
 * The element, the `StoryEngine`, and the wasm `StoryWorld` are the shipping code path.
 * The ONLY things "shimmed" for a browser tab are the transport hop (routed in-page to
 * the engine), the consent chrome (auto-approve, but VISIBLY shown so the custody write
 * is legible), and the voter identity (a simulated crowd of named villagers + you).
 */

import {
  StoryEngine,
  defaultResolveStory,
  type StoryWorldLike,
  type CollectiveStoryWorldLike,
} from "../extension/src/port";
import { setStoryPortFactory, registerStoryElement } from "../extension/src/elements/dregg-story";

declare const window: any;

// ── the wasm `StoryWorld` constructor (real spween collective CYOA world) ────────
interface WasmStoryWorld {
  new (sceneSource: string): {
    currentPassage(): string;
    passageProse(): string;
    choicesJson(): string;
    advance(index: number): string;
    verify(): boolean;
    commitmentHex(): string;
    receiptCount(): number;
    isEnded(): boolean;
    setElectorate(csv: string): void;
    electorateJson(): string;
    openBranchPoll(): string;
    castVote(voter: string, optionIndex: number): string;
    branchTally(): string;
    closeBranchPoll(): string;
    hasOpenPoll(): boolean;
  };
}

// ── the eligible crowd — the real `CollectiveChoiceEngine` gates ballots to this
//    declared electorate (holding a ballot cap IS eligibility). Seven founding
//    villagers plus you (so ember's own click is an eligible vote). ────────────────
const VILLAGERS = ["Miren", "Tomas", "Sela", "Odd", "Brisa", "Cael", "Wend"] as const;
const YOU = "you";
const ROSTER = [...VILLAGERS, YOU];

const STORY_URI = "dregg://story/b3_c0117ec";

/** Fill the page banner that makes a custody write LEGIBLE (the confirm-intent
 *  chrome an extension would pop; here we show it inline and auto-approve). */
function showSigning(who: string, what: string): void {
  const el = document.getElementById("signing");
  if (!el) return;
  el.innerHTML = `<span class="pen">✍</span> <b>${escapeHtml(who)}</b> is signing a turn — <span class="what">${escapeHtml(what)}</span>`;
  el.classList.add("live");
}
function clearSigning(): void {
  const el = document.getElementById("signing");
  if (!el) return;
  el.classList.remove("live");
  el.textContent = "";
}
const sleep = (ms: number) => new Promise<void>((r) => setTimeout(r, ms));

/**
 * The page-side collective world: a THIN, honest adapter over the real wasm
 * `StoryWorld`. It delegates every method to the wasm — EXCEPT `openBranchPoll`,
 * which it makes IDEMPOTENT: the shipping element re-reads the open branch on every
 * refresh (after each vote), but the wasm `open_branch_poll` OPENS A FRESH poll each
 * call (a new `CollectiveChoiceEngine`, discarding the round's ballots). So the
 * adapter opens a real wasm poll only when none is open, and returns the cached
 * descriptor while a poll is live — the ballots the crowd casts are preserved and the
 * tally the element shows is the real engine's tally. Nothing else is intercepted.
 */
class CommonsWorld implements CollectiveStoryWorldLike {
  private real: InstanceType<WasmStoryWorld>;
  private cachedOpen: string | null = null;

  constructor() {
    const Ctor: WasmStoryWorld = window.__COMMONS_STORYWORLD;
    if (!Ctor) throw new Error("wasm StoryWorld constructor not initialized");
    // FAIL-CLOSED: an unparseable scene throws here (the JsError from the parser),
    // and the whole boot fails closed (the element shows the fallback + warning).
    this.real = new Ctor(window.__COMMONS_SCENE);
    // Declare the eligible crowd once (persists on the world; each freshly-opened
    // poll admits exactly these voters' ballots).
    this.real.setElectorate(ROSTER.join(","));
  }

  currentPassage(): string { return this.real.currentPassage(); }
  passageProse(): string { return this.real.passageProse(); }
  choicesJson(): string { return this.real.choicesJson(); }
  advance(index: number): string { return this.real.advance(index); }
  verify(): boolean { return this.real.verify(); }
  commitmentHex(): string { return this.real.commitmentHex(); }
  receiptCount(): number { return this.real.receiptCount(); }

  openBranchPoll(): string {
    // Idempotent: open a real wasm poll only when none is live (so a re-read after a
    // vote does not wipe the round's ballots). When ended, the wasm returns an error
    // JSON here — pass it straight through (the element renders "— the end —").
    if (!this.real.hasOpenPoll()) {
      this.cachedOpen = this.real.openBranchPoll();
    }
    return this.cachedOpen ?? this.real.openBranchPoll();
  }
  castVote(voter: string, optionIndex: number): string {
    return this.real.castVote(voter, optionIndex);
  }
  branchTally(): string { return this.real.branchTally(); }
  closeBranchPoll(): string {
    const r = this.real.closeBranchPoll();
    this.cachedOpen = null; // the poll is consumed; a fresh passage re-opens one
    return r;
  }
  // Feature-probe method the engine's `asCollective` looks for is satisfied by the
  // four collective methods above; `hasOpenPoll` is not part of the interface but
  // kept for parity / potential callers.
  hasOpenPoll(): boolean { return this.real.hasOpenPoll(); }
}

/** The shared engine — the page holds it to run the stranger's replay directly. */
let ENGINE: StoryEngine;

/** Boot: init wasm, fetch the scene, wire the engine + element. */
async function boot(): Promise<void> {
  const status = document.getElementById("status")!;
  try {
    status.textContent = "loading the verifiable world…";

    // 1) The scene source (a real spween `.scene`).
    const sceneResp = await fetch("stories/the-commons.scene");
    if (!sceneResp.ok) throw new Error(`could not fetch the scene (${sceneResp.status})`);
    window.__COMMONS_SCENE = await sceneResp.text();

    // 2) The real wasm `StoryWorld` (the collective spween CYOA world).
    await window.wasm_bindgen("dregg_wasm_bg.wasm");
    if (!window.wasm_bindgen.StoryWorld) {
      throw new Error("the wasm bundle has no StoryWorld export — rebuild extension/dregg_wasm.js");
    }
    window.__COMMONS_STORYWORLD = window.wasm_bindgen.StoryWorld;

    // 3) The page-side collective engine over the real world. `consent` stands in for
    //    the un-overlayable confirm-intent chrome (auto-approve, VISIBLY shown so the
    //    custody write is legible); `voterIdentity` yields the current caster's stable
    //    id (a named villager during the crowd auto-play, or "you" for ember's click).
    ENGINE = new StoryEngine({
      StoryWorld: CommonsWorld as unknown as { new (): StoryWorldLike },
      resolveStory: defaultResolveStory,
      consent: async (req) => {
        const who = String(window.__DEMO_VOTER || YOU);
        // A short, VISIBLE "signing" beat — the custody write, made legible.
        showSigning(who, humanizeIntent(req.explanation));
        await sleep(220);
        clearSigning();
        return true;
      },
      voterIdentity: () => String(window.__DEMO_VOTER || YOU),
    });

    // 4) Route the element's story port in-page to the engine (the transport hop).
    setStoryPortFactory(() => ({
      async request(req: any) {
        return ENGINE.handle(req, location.origin);
      },
    }));

    // Expose the closed shadow root so the page can DRIVE the shipping element's own
    // vote/close buttons (the crowd auto-play clicks them, flipping the voter id — the
    // exact element→engine→wasm path a real click takes). This is the element's
    // provided test seam; every vote it drives is a real verified turn.
    window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

    // 5) Register + let the in-DOM <dregg-story collective> upgrade and boot.
    window.__DEMO_VOTER = YOU;
    registerStoryElement();

    status.textContent = "the real story loaded — watch the crowd decide";
    // Wait for the element to settle verified, then start the crowd.
    await whenElementReady();
    void autoplay();
  } catch (e) {
    status.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
    window.__DEMO_ERROR = String((e as Error)?.message ?? e);
  }
}

/** Turn the engine's faithful (verbose) consent explanation into a short human line. */
function humanizeIntent(explanation: string): string {
  const vote = /vote for "([^"]+)"/.exec(explanation);
  if (vote) return `casting a ballot for “${vote[1]}”`;
  if (/Close the branch poll/.test(explanation)) return "closing the branch — advancing the winner";
  return "committing one verified turn";
}

// ── driving the shipping element (closed-shadow buttons) ─────────────────────────

function storyEl(): HTMLElement {
  return document.getElementById("commons") as HTMLElement;
}
function storyRoot(): ShadowRoot | undefined {
  const roots = window.__dreggStoryRoots as WeakMap<Element, ShadowRoot> | undefined;
  return roots?.get(storyEl());
}
function voteButtons(): HTMLButtonElement[] {
  const root = storyRoot();
  return root ? [...root.querySelectorAll<HTMLButtonElement>("button[data-vote]")] : [];
}
function optionState(): { choiceIndex: number; label: string; count: number }[] {
  return voteButtons().map((b) => ({
    choiceIndex: Number(b.getAttribute("data-choice") || "0"),
    label: (b.querySelector(".opt-label")?.textContent || "").trim(),
    count: Number(b.querySelector(".opt-count")?.textContent || "0"),
  }));
}
function totalVotes(): number {
  return optionState().reduce((a, o) => a + o.count, 0);
}

async function whenElementReady(timeoutMs = 20000): Promise<void> {
  const start = Date.now();
  for (;;) {
    const el = storyEl();
    if (el.hasAttribute("verified") && voteButtons().length > 0) return;
    if (el.hasAttribute("error")) throw new Error("the story failed to verify (scene did not compile?)");
    if (Date.now() - start > timeoutMs) throw new Error("timed out waiting for the story element");
    await sleep(60);
  }
}

async function waitUntil(pred: () => boolean, timeoutMs = 15000): Promise<void> {
  const start = Date.now();
  while (!pred()) {
    if (Date.now() - start > timeoutMs) return;
    await sleep(50);
  }
}

/** One villager casts one ballot for `choiceIndex` by clicking the element's own
 *  vote button (flipping the current voter id so the engine records it under that
 *  villager's stable id). Returns when the element has repainted the new tally. */
async function crowdVote(voter: string, choiceIndex: number): Promise<boolean> {
  const before = totalVotes();
  window.__DEMO_VOTER = voter;
  const btn = voteButtons().find((b) => Number(b.getAttribute("data-choice")) === choiceIndex);
  if (!btn) return false;
  btn.disabled = false; // the element re-enables on repaint; ensure the click lands
  btn.click();
  await waitUntil(() => totalVotes() > before || storyEl().hasAttribute("choice-refused"), 8000);
  window.__DEMO_VOTER = YOU; // restore — ember's own clicks vote as "you"
  return totalVotes() > before;
}

/** Close the open branch → advance the winner as one verified turn. Waits for the
 *  passage to change (or the ending). */
async function closeBranch(): Promise<void> {
  const root = storyRoot();
  if (!root) return;
  const passageBefore = storyEl().getAttribute("passage");
  const closeBtn = root.querySelector<HTMLButtonElement>("button[data-close]");
  if (!closeBtn) return;
  window.__DEMO_VOTER = YOU;
  closeBtn.disabled = false;
  closeBtn.click();
  await waitUntil(
    () => storyEl().getAttribute("passage") !== passageBefore || isEnded(),
    12000,
  );
}

function isEnded(): boolean {
  const root = storyRoot();
  const ending = root?.querySelector(".ending")?.textContent || "";
  return /the end/i.test(ending) || voteButtons().length === 0;
}

/** A deterministic, story-steering ballot distribution: the crowd gives one option a
 *  clear plurality, the rest split — the REAL engine resolves the argmax through its
 *  quorum gate. (Chosen so the tale reaches the "open, verifiable" ending.) */
function planRound(nOptions: number): { winner: number; assignment: number[] } {
  const winner = nOptions >= 3 ? 1 : 0; // 3-way → "by the water"; 2-way → the open choice
  const assignment: number[] = [];
  // Give the winner the majority; scatter a few dissenting ballots for realism.
  for (let i = 0; i < VILLAGERS.length; i++) {
    if (i < Math.ceil(VILLAGERS.length * 0.6)) assignment.push(winner);
    else assignment.push((winner + 1 + (i % Math.max(1, nOptions - 1))) % nOptions);
  }
  return { winner, assignment };
}

// ── the auto-play: watch the crowd co-author the story ───────────────────────────

let PAUSED = false;
window.__demoTogglePause = () => {
  PAUSED = !PAUSED;
  const b = document.getElementById("pauseBtn");
  if (b) b.textContent = PAUSED ? "▶ resume the crowd" : "⏸ pause (vote yourself)";
  return PAUSED;
};

async function autoplay(): Promise<void> {
  window.__DEMO_LOG = [];
  const status = document.getElementById("status")!;
  let round = 0;
  const MAX_ROUNDS = 8;

  while (!isEnded() && round < MAX_ROUNDS) {
    round++;
    const passage = storyEl().getAttribute("passage") || "";
    const opts = optionState();
    if (opts.length === 0) break;

    status.textContent = `round ${round}: the assembly votes at “${passage}”`;
    const plan = planRound(opts.length);

    // Stagger the crowd's ballots so the tally visibly grows.
    for (let i = 0; i < VILLAGERS.length; i++) {
      while (PAUSED) await sleep(150);
      await crowdVote(VILLAGERS[i], plan.assignment[i]);
      await sleep(180);
    }

    // Record the round for the transcript (post-crowd, pre-close tally).
    const tally = optionState().map((o) => ({ label: o.label, count: o.count }));
    const receiptsBefore = Number(storyEl().getAttribute("receipts") || "0");

    // Let ember linger if they paused to add their own vote.
    while (PAUSED) await sleep(150);

    status.textContent = `round ${round}: closing the branch — the winner advances`;
    await closeBranch();

    const receiptsAfter = Number(storyEl().getAttribute("receipts") || "0");
    const winnerLabel = tally.reduce((a, b) => (b.count > a.count ? b : a), tally[0])?.label || "";
    window.__DEMO_LOG.push({
      round,
      passage,
      options: tally,
      winner: winnerLabel,
      receiptsBefore,
      receiptsAfter,
      newPassage: storyEl().getAttribute("passage") || "",
      commitment: storyEl().getAttribute("commitment") || "",
    });
    renderChain();
    await sleep(400);
  }

  // The stranger's replay: independently re-verify the whole receipt chain.
  const verify = (await ENGINE.handle({ op: "verifyStory", uri: STORY_URI })) as any;
  window.__DEMO_VERIFIED = !!verify.verified;
  window.__DEMO_RECEIPTS = Number(verify.receiptCount || 0);
  window.__DEMO_DONE = true;

  const status2 = document.getElementById("status")!;
  status2.textContent = "the story reached its ending.";
  const badge = document.getElementById("verifyBadge")!;
  if (verify.verified) {
    badge.className = "verify ok";
    badge.textContent = "✓ receipt chain verified — nothing was rewritten.";
  } else {
    badge.className = "verify bad";
    badge.textContent = "⚠ the receipt chain did not replay.";
  }
  renderChain();
}

/** The receipt-chain indicator: a growing chain of committed turns + the moving
 *  commitment (read from the element's reflected public attributes). */
function renderChain(): void {
  const el = document.getElementById("chain");
  if (!el) return;
  const receipts = Number(storyEl().getAttribute("receipts") || "0");
  const commitment = storyEl().getAttribute("commitment") || "";
  const links = Array.from({ length: receipts }, (_, i) =>
    `<span class="link" title="verified turn ${i + 1}">●</span>`,
  ).join('<span class="rope">—</span>');
  el.innerHTML =
    `<div class="chain-links">${links || '<span class="link empty">○</span>'}</div>` +
    `<div class="chain-meta">${receipts} verified turn${receipts === 1 ? "" : "s"} · commitment ` +
    `<code>${escapeHtml(commitment.slice(0, 12) || "—")}…</code></div>`;
}

function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", () => void boot());
} else {
  void boot();
}
