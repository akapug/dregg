/**
 * In-page test harness for the verifiable choose-your-own-adventure (`<dregg-story>`).
 *
 * It wires the REAL modules — the `<dregg-story>` thin view (closed shadow) and the
 * `StoryEngine` — and routes the story port in-page to the engine. Everything
 * security- and correctness-relevant — closed shadow, engine-owns-the-world,
 * READ/VERIFY as the free tier, CHOOSE as a custody-gated verified turn, fail-closed
 * on a gated choice, the stranger's receipt-chain replay — is the shipping code
 * path. The ONLY things shimmed are the transport hop (routed in-page to the engine)
 * and consent (auto-approve, flippable via `window.__DREGG_CONSENT`).
 *
 * The wasm `StoryWorld` is built by a PARALLEL lane; this fixture drives an
 * in-memory STAND-IN `StoryWorld` implementing the exact storyworld contract
 * (`currentPassage/passageProse/choicesJson/advance/verify/commitmentHex/receiptCount`),
 * exactly as the dregg-doc fixtures drive a stand-in — so it does not block on wasm.
 */
import {
  StoryEngine,
  defaultResolveStory,
  type StoryWorldLike,
} from "../../src/port";
import { setStoryPortFactory, registerStoryElement } from "../../src/elements/dregg-story";

declare const window: any;

// ── The in-memory STAND-IN StoryWorld ───────────────────────────────────────
// A 3-passage story. Every choice is a receipt; `verify()` replays the whole
// chain from genesis (the stranger's check); `commitmentHex()` moves each advance.
// A gated choice (the locked gate at the fork) FAILS CLOSED — `advance` refuses it
// and the boundary does not move.

interface RawChoice {
  index: number;
  text: string;
  available: boolean;
}
interface Passage {
  name: string;
  prose: string;
  choices: RawChoice[];
}

const GENESIS = "the-fork";
const PASSAGES: Record<string, Passage> = {
  "the-fork": {
    name: "the-fork",
    prose:
      "You stand at a fork in the drifting mist. To the left, a bright path hums with lantern-light. Ahead, an iron gate hangs locked and cold.",
    choices: [
      { index: 0, text: "Take the bright path", available: true },
      { index: 1, text: "Force the locked gate", available: false }, // gated
    ],
  },
  "the-bright-path": {
    name: "the-bright-path",
    prose:
      "The bright path opens onto a lantern-lit hollow. A slender tower rises from its centre, its door ajar and waiting.",
    choices: [{ index: 0, text: "Push on to the tower", available: true }],
  },
  "the-tower": {
    name: "the-tower",
    prose: "The tower door swings wide. Inside, your own receipt-chain glows on the wall — every choice, replayable.",
    choices: [], // the end
  },
};
const TRANSITIONS: Record<string, Record<number, string>> = {
  "the-fork": { 0: "the-bright-path" },
  "the-bright-path": { 0: "the-tower" },
  "the-tower": {},
};

/** A tiny FNV-1a hex hash — deterministic, moves as the receipt tape grows. */
function fnv1aHex(s: string): string {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
  }
  return ("00000000" + h.toString(16)).slice(-8);
}

class StandInStoryWorld implements StoryWorldLike {
  private passage = GENESIS;
  private receipts: { from: string; index: number; to: string }[] = [];

  currentPassage(): string {
    return this.passage;
  }
  passageProse(): string {
    return PASSAGES[this.passage].prose;
  }
  choicesJson(): string {
    return JSON.stringify(PASSAGES[this.passage].choices);
  }
  advance(index: number): string {
    const fail = (error: string) =>
      JSON.stringify({ ok: false, error, passage: this.passage, receiptCount: this.receipts.length, commitmentHex: this.commitmentHex() });
    const p = PASSAGES[this.passage];
    const choice = p.choices.find((c) => c.index === index);
    // FAIL CLOSED: a gated / unknown choice never moves the boundary.
    if (!choice) return fail("no such choice");
    if (!choice.available) return fail("choice gated/unavailable");
    const to = TRANSITIONS[this.passage]?.[index];
    if (to === undefined) return fail("no transition");
    this.receipts.push({ from: this.passage, index, to });
    this.passage = to;
    return JSON.stringify({ ok: true, passage: this.passage, receiptCount: this.receipts.length, commitmentHex: this.commitmentHex() });
  }
  /** Replay the receipt chain from genesis — every transition must have been a
   *  legal, available choice, and the walk must land on the current passage. */
  verify(): boolean {
    let cur = GENESIS;
    for (const r of this.receipts) {
      if (r.from !== cur) return false;
      const c = PASSAGES[cur]?.choices.find((ch) => ch.index === r.index);
      if (!c || !c.available) return false;
      if (TRANSITIONS[cur]?.[r.index] !== r.to) return false;
      cur = r.to;
    }
    return cur === this.passage;
  }
  commitmentHex(): string {
    return fnv1aHex(JSON.stringify({ passage: this.passage, receipts: this.receipts }));
  }
  receiptCount(): number {
    return this.receipts.length;
  }
}

// ── wire the engine(s) + element ─────────────────────────────────────────────

(async () => {
  // Let the element register its closed root in a test registry (gated hook).
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  // The PLAYABLE story: custody wired (consent stands in for the confirm-intent
  // chrome; default approve, flippable via window.__DREGG_CONSENT).
  const engineFull = new StoryEngine({
    StoryWorld: StandInStoryWorld,
    resolveStory: defaultResolveStory,
    consent: async () => window.__DREGG_CONSENT !== false,
  });

  // The READ-ONLY story: NO custody provider — READ + VERIFY still work (the free,
  // trustless tier); choosing degrades to the honest "connect your cipherclerk" note.
  const engineReadOnly = new StoryEngine({
    StoryWorld: StandInStoryWorld,
    resolveStory: defaultResolveStory,
    consent: null,
  });

  const pick = (uri: string) => (uri && uri.indexOf("b0b0b0") !== -1 ? engineReadOnly : engineFull);

  // Route the story port in-page directly to the engine (the REAL element uses this
  // factory to reach what is, in production, the background StoryEngine).
  setStoryPortFactory(() => ({
    async request(req: any) {
      return pick(req.uri).handle(req, location.origin);
    },
  }));

  // THE STRANGER'S CHECK: an INDEPENDENT light-client replay of the receipt chain.
  window.__dreggStoryVerify = (uri: string) => pick(uri).handle({ op: "verifyStory", uri });
  // Drive the engine's choose directly (used to prove a GATED choice is refused —
  // the element also renders that choice as a disabled button).
  window.__dreggStoryChoose = (uri: string, index: number) => pick(uri).handle({ op: "chooseChoice", uri, index });

  registerStoryElement();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
