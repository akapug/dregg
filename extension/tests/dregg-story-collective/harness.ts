/**
 * In-page test harness for the COLLECTIVE choose-your-own-adventure
 * (`<dregg-story collective>`) — the killer mode: the crowd votes each branch,
 * the winner advances, in a browser tab.
 *
 * It wires the REAL modules — the `<dregg-story>` thin view (closed shadow) and the
 * `StoryEngine` collective methods — and routes the story port in-page to the engine.
 * Everything security- and correctness-relevant — closed shadow, engine-owns-the-world,
 * READ/tally as the FREE tier, a VOTE as a custody-gated verified turn recorded under
 * the voter's stable public key, one-vote-per-voter fail-closed, CLOSE advancing the
 * winner as a real verified turn, the stranger's receipt-chain replay — is the shipping
 * code path. The ONLY things shimmed are the transport hop (routed in-page to the engine),
 * consent (auto-approve, flippable via `window.__DREGG_CONSENT`), and the voter identity
 * (flippable via `window.__DREGG_VOTER` — a stand-in for the custody provider's public key,
 * so the fixture can simulate a CROWD of distinct voters).
 *
 * The wasm collective `StoryWorld` is built by a PARALLEL lane; this fixture drives an
 * in-memory STAND-IN implementing the EXACT collective contract
 * (`openBranchPoll/castVote/branchTally/closeBranchPoll`, over the base
 * `currentPassage/passageProse/advance/verify/commitmentHex/receiptCount`), exactly as
 * the dregg-story/poll fixtures drive a stand-in — so it does not block on wasm.
 */
import {
  StoryEngine,
  defaultResolveStory,
  type CollectiveStoryWorldLike,
} from "../../src/port";
import { setStoryPortFactory, registerStoryElement } from "../../src/elements/dregg-story";

declare const window: any;

// ── The in-memory STAND-IN collective StoryWorld ─────────────────────────────
// A branching story. At each choice passage the crowd votes (one vote per voter,
// fail-closed on a double-vote). Closing tallies, picks the winner (ties resolved
// by lowest index, reported honestly), and ADVANCES as a receipt — `verify()`
// replays the whole chain (the stranger's check); `commitmentHex()` moves on close.

interface RawChoice {
  index: number;
  text: string;
}
interface Passage {
  name: string;
  prose: string;
  options: RawChoice[]; // the branch the crowd votes on ([] ⇒ an ending)
}

const GENESIS = "the-fork";
const PASSAGES: Record<string, Passage> = {
  "the-fork": {
    name: "the-fork",
    prose:
      "You stand at a fork in the drifting mist. The crowd must decide: left, a bright path humming with lantern-light; or down, a dark stair spiralling into the earth.",
    options: [
      { index: 0, text: "Take the bright path" },
      { index: 1, text: "Descend the dark stair" },
    ],
  },
  "the-bright-path": {
    name: "the-bright-path",
    prose:
      "The bright path opens onto a lantern-lit hollow. A slender tower rises from its centre, its door ajar and waiting.",
    options: [{ index: 0, text: "Push on to the tower" }],
  },
  "the-dark-stair": {
    name: "the-dark-stair",
    prose: "The dark stair ends at a still black pool that mirrors nothing at all.",
    options: [{ index: 0, text: "Wade across" }],
  },
  "the-tower": {
    name: "the-tower",
    prose:
      "The tower door swings wide. Inside, the crowd's own receipt-chain glows on the wall — every branch, every vote, replayable.",
    options: [], // the end
  },
};
const TRANSITIONS: Record<string, Record<number, string>> = {
  "the-fork": { 0: "the-bright-path", 1: "the-dark-stair" },
  "the-bright-path": { 0: "the-tower" },
  "the-dark-stair": { 0: "the-tower" },
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

class CollectiveStandInStoryWorld implements CollectiveStoryWorldLike {
  private passage = GENESIS;
  private round = 0;
  private receipts: { from: string; index: number; to: string; round: number }[] = [];
  /** voter id → the option (choiceIndex) they voted for THIS round; one vote per voter. */
  private votes = new Map<string, number>();

  private opts(): RawChoice[] {
    return PASSAGES[this.passage].options;
  }
  private counts(): { label: string; count: number }[] {
    const opts = this.opts();
    const rows = opts.map((o) => ({ label: o.text, count: 0 }));
    for (const [, chosen] of this.votes) {
      const i = opts.findIndex((o) => o.index === chosen);
      if (i >= 0) rows[i].count++;
    }
    return rows;
  }

  // ── base StoryWorld surface ──
  currentPassage(): string {
    return this.passage;
  }
  passageProse(): string {
    return PASSAGES[this.passage].prose;
  }
  choicesJson(): string {
    // Single-player parity view (every branch option, all available).
    return JSON.stringify(this.opts().map((o) => ({ index: o.index, text: o.text, available: true })));
  }
  advance(index: number): string {
    // Direct single-player advance (kept for interface parity; the collective path
    // advances through closeBranchPoll). Fail-closed on an illegal move.
    const fail = (error: string) =>
      JSON.stringify({ ok: false, error, passage: this.passage, receiptCount: this.receipts.length, commitmentHex: this.commitmentHex() });
    const to = TRANSITIONS[this.passage]?.[index];
    if (to === undefined) return fail("no transition");
    this.receipts.push({ from: this.passage, index, to, round: this.round });
    this.passage = to;
    this.round++;
    this.votes.clear();
    return JSON.stringify({ ok: true, passage: this.passage, receiptCount: this.receipts.length, commitmentHex: this.commitmentHex() });
  }
  verify(): boolean {
    let cur = GENESIS;
    for (const r of this.receipts) {
      if (r.from !== cur) return false;
      const to = TRANSITIONS[cur]?.[r.index];
      if (to === undefined || to !== r.to) return false;
      cur = r.to;
    }
    return cur === this.passage;
  }
  commitmentHex(): string {
    // Moves on CLOSE (passage + receipts change); a vote alone does NOT move it
    // (votes are the pre-finalization tally, not the committed boundary).
    return fnv1aHex(JSON.stringify({ passage: this.passage, receipts: this.receipts }));
  }
  receiptCount(): number {
    return this.receipts.length;
  }

  // ── the COLLECTIVE contract ──
  openBranchPoll(): string {
    return JSON.stringify({
      passage: this.passage,
      round: this.round,
      options: this.opts().map((o) => ({ choiceIndex: o.index, label: o.text })),
    });
  }
  branchTally(): string {
    return JSON.stringify(this.counts());
  }
  castVote(voter: string, optionIndex: number): string {
    const ok = this.opts().some((o) => o.index === optionIndex);
    if (!ok) return JSON.stringify({ ok: false, error: "no such option", tally: this.counts() });
    // ONE vote per voter, fail-closed (the nullifier analogue).
    if (this.votes.has(voter)) return JSON.stringify({ ok: false, error: "already voted (one vote per voter)", tally: this.counts() });
    this.votes.set(voter, optionIndex);
    return JSON.stringify({ ok: true, tally: this.counts() });
  }
  closeBranchPoll(): string {
    const opts = this.opts();
    if (opts.length === 0) return JSON.stringify({ ok: false, error: "no branch to close (ending)" });
    const rows = opts.map((o) => {
      let n = 0;
      for (const [, v] of this.votes) if (v === o.index) n++;
      return { choice: o.index, label: o.text, count: n };
    });
    const total = rows.reduce((a, r) => a + r.count, 0);
    if (total === 0) return JSON.stringify({ ok: false, error: "no votes cast" });
    const max = Math.max(...rows.map((r) => r.count));
    const top = rows.filter((r) => r.count === max);
    const tie = top.length > 1;
    const winner = top.reduce((a, b) => (a.choice <= b.choice ? a : b)); // lowest index
    const to = TRANSITIONS[this.passage]?.[winner.choice];
    if (to === undefined) return JSON.stringify({ ok: false, error: "no transition" });
    this.receipts.push({ from: this.passage, index: winner.choice, to, round: this.round });
    this.passage = to;
    this.round++;
    this.votes.clear();
    return JSON.stringify({
      ok: true,
      winningChoice: winner.choice,
      winningLabel: winner.label,
      tie,
      tally: rows.map((r) => ({ label: r.label, count: r.count })),
      passage: this.passage,
      receiptCount: this.receipts.length,
      commitmentHex: this.commitmentHex(),
    });
  }
}

// ── wire the engine(s) + element ─────────────────────────────────────────────

(async () => {
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  // The COLLECTIVE story: custody wired. consent stands in for confirm-intent
  // (default approve, flippable via window.__DREGG_CONSENT); voterIdentity stands in
  // for the custody provider's public key (flippable via window.__DREGG_VOTER — so
  // the fixture can simulate a crowd of distinct voters).
  const engineFull = new StoryEngine({
    StoryWorld: CollectiveStandInStoryWorld,
    resolveStory: defaultResolveStory,
    consent: async () => window.__DREGG_CONSENT !== false,
    voterIdentity: () => (window.__DREGG_VOTER ? String(window.__DREGG_VOTER) : null),
  });

  // The READ-ONLY collective story: NO custody. READ + tally still work (the free,
  // trustless tier); voting/closing degrade to the honest "connect your cipherclerk" note.
  const engineReadOnly = new StoryEngine({
    StoryWorld: CollectiveStandInStoryWorld,
    resolveStory: defaultResolveStory,
    consent: null,
    voterIdentity: null,
  });

  const pick = (uri: string) => (uri && uri.indexOf("b0b0b0") !== -1 ? engineReadOnly : engineFull);

  setStoryPortFactory(() => ({
    async request(req: any) {
      return pick(req.uri).handle(req, location.origin);
    },
  }));

  // Direct engine hooks (drive the crowd / the stranger's replay from the test).
  window.__dreggStoryVerify = (uri: string) => pick(uri).handle({ op: "verifyStory", uri });
  window.__dreggStoryOpen = (uri: string) => pick(uri).handle({ op: "openBranch", uri });
  window.__dreggStoryTally = (uri: string) => pick(uri).handle({ op: "branchTally", uri });
  window.__dreggStoryVote = (uri: string, optionIndex: number) => pick(uri).handle({ op: "castBranchVote", uri, optionIndex });
  window.__dreggStoryClose = (uri: string) => pick(uri).handle({ op: "closeBranch", uri });

  registerStoryElement();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
