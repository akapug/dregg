/**
 * In-page test harness for The Descent, played in-tab (`<dregg-descent>`).
 *
 * It wires the REAL modules — the `<dregg-descent>` thin view (closed shadow) and the
 * `DescentEngine` — and routes the descent port in-page to the engine. Everything
 * security- and correctness-relevant — closed shadow, engine-owns-the-world, PLAY +
 * VERIFY as the free, PRIVATE, in-tab tier, a move press as a real cap-gated verified
 * turn, fail-closed in-band on a gated move, the stranger's replay, and the OPT-IN
 * settle as a named hook — is the shipping code path. The ONLY thing shimmed is the
 * transport hop (routed in-page to the engine).
 *
 * The wasm `DescentWorld` is in the shipped wasm32 bundle (wasm/src/bindings_descent.rs);
 * this fixture drives an in-memory STAND-IN `DescentWorld` implementing the exact surface
 * (`title/seedHex/currentRoom/roomProse/movesJson/advance/stateJson/commitmentHex/verify`),
 * exactly as the dregg-story fixture drives a stand-in StoryWorld — so it does not block
 * on a wasm build. The stand-in models the same shape as the real day: a warden gate
 * (measured / reckless / press-past / fall-to-defeat), a key room, and the hoard, with an
 * HP-brink death route — so a CAREFUL run WINS and a RECKLESS run DIES, both replay-true.
 */
import {
  DescentEngine,
  defaultResolveDescent,
  type DescentWorldLike,
} from "../../src/port";
import { setDescentPortFactory, registerDescentElement } from "../../src/elements/dregg-descent";

declare const window: any;

// ── The in-memory STAND-IN DescentWorld ──────────────────────────────────────

const HOARD_GOLD = 100;
const HP_START = 50;

interface RunState {
  room: string;
  hp: number;
  wardenHp: number;
  depth: number;
  gold: number;
  downed: number;
}

/** A tiny FNV-1a hex hash — deterministic, moves as the receipt tape grows. */
function fnv1aHex(s: string): string {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
  }
  return ("00000000" + h.toString(16)).slice(-8);
}

class StandInDescentWorld implements DescentWorldLike {
  private st: RunState;
  private readonly wardenStart: number;
  private readonly seed: string;
  private readonly titleStr: string;
  private receipts: number[] = [];

  constructor(epochHex: string) {
    // The day is a pure function of the committed epoch (as the real beacon-drawn day
    // is): the warden HP and title are drawn from the epoch bytes.
    const firstByte = parseInt(epochHex.slice(0, 2) || "2d", 16) || 45;
    this.wardenStart = 45 + (firstByte % 16); // 45..=60
    this.seed = "b3d_" + epochHex.slice(0, 24);
    this.titleStr = "The Sunken Descent #" + epochHex.slice(0, 4);
    this.st = this.genesis();
  }

  private genesis(): RunState {
    return { room: "gate", hp: HP_START, wardenHp: this.wardenStart, depth: 0, gold: 0, downed: 0 };
  }

  // ── metadata ──
  title(): string {
    return this.titleStr;
  }
  seedHex(): string {
    return this.seed;
  }

  // ── room + moves ──
  currentRoom(): string {
    return this.st.room;
  }
  roomProse(): string {
    return PROSE[this.st.room] ?? "";
  }
  movesJson(): string {
    return JSON.stringify(this.movesFor(this.st));
  }

  /** The gate-computed moves at a state (a gated move is SHOWN but not `available`). */
  private movesFor(s: RunState): { index: number; text: string; available: boolean }[] {
    switch (s.room) {
      case "gate":
        return [
          { index: 0, text: "Measured strike at the warden", available: s.wardenHp > 0 },
          { index: 1, text: "Reckless all-out blow", available: s.wardenHp > 0 },
          { index: 2, text: "Press past the felled warden", available: s.wardenHp <= 0 },
          { index: 3, text: "Fall to the warden's blow", available: s.hp <= 20 },
        ];
      case "keyroom":
        return [{ index: 0, text: "Take the iron key", available: true }];
      case "hoard":
        return [{ index: 0, text: "Seize the hoard", available: true }];
      case "downed":
        return [{ index: 0, text: "Close your eyes", available: true }];
      default:
        return []; // ended
    }
  }

  // ── advance: one verified turn (fail-closed in-band on a gated/invalid move) ──
  advance(index: number): string {
    return this.step(this.st, index, true);
  }

  /** Apply move `index` to `s` (mutating iff `commit`). Returns the state JSON with
   *  `ok` set — `ok:false` (nothing changed) on a gated / out-of-range / ended move. */
  private step(s: RunState, index: number, commit: boolean): string {
    const fail = (error: string) => JSON.stringify({ ...this.stateObj(s), ok: false, error });
    const move = this.movesFor(s).find((m) => m.index === index);
    if (!move) return fail("no such move");
    if (!move.available) return fail("move gated/unavailable");

    // Effects (the stand-in scene's gate-checked transitions).
    if (s.room === "gate") {
      if (index === 0) {
        s.wardenHp = Math.max(0, s.wardenHp - 15);
        s.hp = Math.max(0, s.hp - 5);
      } else if (index === 1) {
        s.wardenHp = Math.max(0, s.wardenHp - 25);
        s.hp = Math.max(0, s.hp - 30);
      } else if (index === 2) {
        s.room = "keyroom";
        s.depth += 1;
      } else if (index === 3) {
        s.room = "downed";
        s.downed = 1;
      }
    } else if (s.room === "keyroom") {
      s.room = "hoard";
      s.depth += 1;
    } else if (s.room === "hoard") {
      s.gold = HOARD_GOLD;
      s.room = ""; // won → ended
    } else if (s.room === "downed") {
      s.room = ""; // lost → ended
    }

    if (commit) this.receipts.push(index);
    return JSON.stringify({ ...this.stateObj(s), ok: true });
  }

  // ── state ──
  stateJson(): string {
    return JSON.stringify(this.stateObj(this.st));
  }
  private stateObj(s: RunState): Record<string, unknown> {
    const ended = s.room === "";
    const won = ended && s.gold === HOARD_GOLD;
    const dead = s.downed === 1;
    return {
      room: s.room,
      hp: s.hp,
      wardenHp: s.wardenHp,
      depth: s.depth,
      gold: s.gold,
      downed: s.downed,
      alive: !dead,
      dead,
      won,
      ended,
      turns: 1 + this.receipts.length, // genesis + one per committed move
      commitmentHex: this.commitmentHex(),
    };
  }
  commitmentHex(): string {
    return fnv1aHex(JSON.stringify({ st: this.st, receipts: this.receipts }));
  }

  /** Replay the recorded moves against a FRESH, identically-seeded day and confirm the
   *  exact committed state reproduces — the stranger's check. Every recorded move must
   *  have been available at that point (a forged/ineligible move breaks the replay). */
  verify(): boolean {
    const fresh = this.genesis();
    for (const idx of this.receipts) {
      const out = JSON.parse(this.step(fresh, idx, false));
      if (!out.ok) return false;
    }
    return JSON.stringify(fresh) === JSON.stringify(this.st);
  }
}

const PROSE: Record<string, string> = {
  gate: "An iron warden bars the sunken gate, its blade weeping rust. The stair beyond descends into dark.",
  keyroom: "The felled warden slumps aside. On a broken plinth rests a single iron key, cold to the touch.",
  hoard: "The last door groans open. Gold spills from a drowned king's hoard, glittering in your lantern-light.",
  downed: "Your knees strike the stone. The warden's shadow falls across you, and the dark closes in.",
};

// ── wire the engine + element ────────────────────────────────────────────────

(async () => {
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  // The PLAYABLE descent: play + verify are the free, private, in-tab tier. The settle
  // hook is left null (the opt-in publish is a named seam) — so `settleDescent` degrades
  // to the honest "opt-in named hook" note and the run stays private.
  const engine = new DescentEngine({
    DescentWorld: StandInDescentWorld,
    resolveDescent: defaultResolveDescent,
    settle: null,
  });

  // Route the descent port in-page directly to the engine (the REAL element uses this
  // factory to reach what is, in production, the background DescentEngine).
  setDescentPortFactory(() => ({
    async request(req: any) {
      return engine.handle(req, location.origin);
    },
  }));

  // Drive the engine directly (used to prove a GATED move is refused in-band, and the
  // stranger's replay-verify).
  window.__dreggDescentOpen = (uri: string) => engine.handle({ op: "openDescent", uri });
  window.__dreggDescentAdvance = (uri: string, index: number) => engine.handle({ op: "advanceMove", uri, index });
  window.__dreggDescentVerify = (uri: string) => engine.handle({ op: "verifyDescent", uri });
  window.__dreggDescentSettle = (uri: string) => engine.handle({ op: "settleDescent", uri });

  registerDescentElement();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});
