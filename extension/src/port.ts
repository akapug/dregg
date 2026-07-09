/**
 * THE QUIET-UPGRADE PORT — the capability-shaped protocol between the in-page
 * thin view (`<dregg-poll>`) and the in-extension engine (this module, run in
 * the background/service-worker context where wasm is allowed).
 *
 * The split (DREGG-QUIET-UPGRADE.md §3) is load-bearing: NOTHING in this file
 * touches the page. It owns the wasm world, the netlayer resolve, the verify,
 * and it delegates custody consent to an injected callback that (in the
 * extension) opens the un-overlayable `confirm-intent` chrome. The element
 * never sees a key, a witness, or the wasm — only these responses, each of
 * which carries an explicit trust tier.
 *
 * This module is dependency-free (no `chrome`, no wasm import): the background
 * constructs a `PollEngine` with the real `PollWorld` constructor + a real
 * consent callback; a test constructs it with the same wasm world + an
 * auto-consent callback. Both drive the IDENTICAL engine over the IDENTICAL
 * message protocol.
 */

// ── trust tiers (§5) — never hidden, always on the wire ─────────────────────
export type TrustTier = "extension" | "sdk" | "server" | "none";

// ── the port request/response protocol (§3) ─────────────────────────────────
export type PollPortRequest =
  | { op: "resolve"; uri: string }
  | { op: "render"; uri: string }
  | { op: "fire"; uri: string; turn: string; arg: number }
  | { op: "verify"; uri: string };

export interface ResolveResponse {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  /** The content-addressed object's public shape (never secret state). */
  object?: { kind: string; addr: string; optionCount: number; quorum: number };
  receiptCount?: number;
  error?: string;
}

export interface RenderResponse {
  ok: boolean;
  tier: TrustTier;
  /** The world's in-wasm `render_html()` — a live tally fragment. */
  html?: string;
  optionCount?: number;
  error?: string;
}

export interface FireResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the turn was refused (below-quorum, double-vote, denied consent). */
  refused?: boolean;
  reason?: string;
  verified?: boolean;
  receiptCount?: number;
  /** Re-read total across options (public tally). */
  total?: number;
  error?: string;
}

export interface VerifyResponse {
  ok: boolean;
  tier: TrustTier;
  verified: boolean;
  receiptCount?: number;
  total?: number;
  error?: string;
}

export type PollPortResponse = ResolveResponse | RenderResponse | FireResponse | VerifyResponse;

/** The transport the element holds — a request/response channel to the engine. */
export interface PollPort {
  request(req: PollPortRequest): Promise<PollPortResponse>;
}

// ── the wasm world surface this engine needs (a structural subset) ──────────
export interface PollWorldLike {
  optionCount(): number;
  read(option: number): number;
  total(): number;
  verified(): boolean;
  receiptCount(): number;
  renderHtml(): string;
  castAs(voter: number, option: number): number;
}
export interface PollWorldCtor {
  // `quorumM` is a wasm `u64` → wasm-bindgen expects a BigInt at the boundary.
  new (numOptions: number, quorumM: bigint): PollWorldLike;
}

/** A turn the engine wants custody consent for, described in human terms. */
export interface ConsentRequest {
  /** A faithful, human reading of exactly what the turn does. */
  explanation: string;
  /** A stable id for the turn (bound in the confirm-intent chrome). */
  turnId: string;
  origin?: string;
}
export type ConsentFn = (req: ConsentRequest) => Promise<boolean>;

/** The public, content-addressed poll spec a resolve yields (netlayer stand-in). */
export interface PollSpec {
  kind: string;
  addr: string;
  numOptions: number;
  quorumM: number;
}
/** Resolve a canonical uri to a poll spec, or `null` (fail-closed). May be async. */
export type ResolveObjectFn = (uri: string) => PollSpec | null | Promise<PollSpec | null>;

export interface PollEngineDeps {
  PollWorld: PollWorldCtor;
  /** The netlayer resolve (content-addr → object). */
  resolveObject: ResolveObjectFn;
  /** Custody consent — opens `confirm-intent` chrome in the extension. */
  consent: ConsentFn;
}

// ── uri grammar (§1) ────────────────────────────────────────────────────────
// Canonical: dregg://poll/<addr>[?q]   Mirror: https://dregg.net/d/poll/<addr>[?q]
// The detector matches loosely (any token); the engine validates STRICTLY —
// a well-formed content-addr is `b3_<hex>`. A token that matches the detector
// but not this is fail-closed here (never rendered as verified).
const CANONICAL_RE = /^dregg:\/\/([a-z0-9]+)\/([^?#\s]+)(?:[?#].*)?$/i;
const MIRROR_RE = /^https?:\/\/dregg\.net\/d\/([a-z0-9]+)\/([^?#\s]+)(?:[?#].*)?$/i;
const VALID_ADDR_RE = /^b3_[0-9a-f]{6,}$/i;

/** Parse either uri form to `{ kind, addr }`, or `null` if it is not a dregg-thing. */
export function parseDreggUri(uri: string): { kind: string; addr: string } | null {
  const s = uri.trim();
  const m = CANONICAL_RE.exec(s) || MIRROR_RE.exec(s);
  if (!m) return null;
  return { kind: m[1].toLowerCase(), addr: m[2] };
}

/** The canonical key for a dregg-thing (both uri forms map to the same key). */
export function canonicalUri(uri: string): string | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  return `dregg://${parsed.kind}/${parsed.addr}`;
}

/** A stable content-addressing stand-in: derive poll config from the addr bytes.
 *
 * The REAL netlayer (build order §4) fetches the content-addressed object and
 * checks `addr == blake3(object)`. Until that lands, we derive a deterministic
 * `(numOptions, quorumM)` from the addr so a well-formed `b3_<hex>` upgrades to
 * a stable poll, and a malformed token fails closed. This is honest about the
 * gap: verification of the *tally* is real (in-wasm light-client recompute);
 * the addr↔object binding is the deferred netlayer tooth. */
export function defaultResolveObject(uri: string): PollSpec | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  if (parsed.kind !== "poll") return null;
  if (!VALID_ADDR_RE.test(parsed.addr)) return null; // fail-closed on a bad addr
  // FNV-1a over the hex tail → a stable, addr-pinned poll shape.
  let h = 0x811c9dc5;
  const tail = parsed.addr.slice(3);
  for (let i = 0; i < tail.length; i++) {
    h ^= tail.charCodeAt(i);
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  const numOptions = 2 + (h % 4); // 2..=5
  const quorumM = 1 + ((h >>> 8) % 3); // 1..=3
  return { kind: "poll", addr: parsed.addr, numOptions, quorumM };
}

/** The viewer's own ballot index — one ballot per resolved poll, so a second
 * click is a genuine double-vote the nullifier refuses (not a fresh voter). */
const VIEWER_VOTER = 0;

/**
 * THE ENGINE. Owns one `PollWorld` per resolved uri; every response is tiered.
 * Runs only in the extension (background) context. Never returns secret state.
 */
export class PollEngine {
  private worlds = new Map<string, PollWorldLike>();
  private specs = new Map<string, PollSpec>();

  constructor(private deps: PollEngineDeps) {}

  async handle(req: PollPortRequest, origin?: string): Promise<PollPortResponse> {
    try {
      switch (req.op) {
        case "resolve":
          return await this.resolve(req.uri);
        case "render":
          return this.render(req.uri);
        case "verify":
          return this.verify(req.uri);
        case "fire":
          return await this.fire(req.uri, req.turn, req.arg, origin);
        default:
          return { ok: false, tier: "none", error: "unknown op" } as ResolveResponse;
      }
    } catch (e) {
      return { ok: false, tier: "none", verified: false, error: String((e as Error)?.message ?? e) };
    }
  }

  private async world(uri: string): Promise<PollWorldLike | null> {
    const key = canonicalUri(uri);
    if (!key) return null;
    const existing = this.worlds.get(key);
    if (existing) return existing;
    const spec = await this.deps.resolveObject(key);
    if (!spec) return null;
    const w = new this.deps.PollWorld(spec.numOptions, BigInt(spec.quorumM));
    this.worlds.set(key, w);
    this.specs.set(key, spec);
    return w;
  }

  private async resolve(uri: string): Promise<ResolveResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, verified: false, tier: "none", error: "not a dregg-thing" };
    const w = await this.world(key);
    if (!w) return { ok: false, verified: false, tier: "none", error: "could not resolve object" };
    const spec = this.specs.get(key)!;
    // The in-wasm self-verify: executor tally == light-client recompute.
    const verified = w.verified();
    return {
      ok: true,
      verified,
      tier: verified ? "extension" : "none",
      object: { kind: spec.kind, addr: spec.addr, optionCount: w.optionCount(), quorum: spec.quorumM },
      receiptCount: w.receiptCount(),
    };
  }

  private render(uri: string): RenderResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", error: "not resolved" };
    // Never render an unverified board as if verified (§6 fail-closed).
    if (!w.verified()) return { ok: false, tier: "none", error: "unverified" };
    return { ok: true, tier: "extension", html: w.renderHtml(), optionCount: w.optionCount() };
  }

  private verify(uri: string): VerifyResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", verified: false, error: "not resolved" };
    const verified = w.verified();
    return {
      ok: true,
      tier: verified ? "extension" : "none",
      verified,
      receiptCount: w.receiptCount(),
      total: Number(w.total()),
    };
  }

  private async fire(uri: string, turn: string, arg: number, origin?: string): Promise<FireResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    if (turn !== "cast") return { ok: false, tier: "none", error: `unknown turn: ${turn}` };
    const spec = this.specs.get(key)!;
    if (!Number.isInteger(arg) || arg < 0 || arg >= w.optionCount()) {
      return { ok: false, tier: "none", error: "option out of range" };
    }

    // Custody consent (§3, §4.5) — the un-overlayable confirm-intent chrome.
    // Every cast is a real turn, so every cast asks. Consent BEFORE any commit.
    const approved = await this.deps.consent({
      explanation:
        `Cast your ballot for option ${arg} in poll ${spec.addr}. ` +
        `This commits one verified vote (one ballot, one vote) to the tally.`,
      turnId: `${key}#cast:${arg}`,
      origin,
    });
    if (!approved) {
      return { ok: true, tier: "extension", refused: true, reason: "consent denied", verified: w.verified(), total: Number(w.total()) };
    }

    // The real cap-gated verified turn: this viewer's own ballot. A second cast
    // is refused by the nullifier / WriteOnce(VOTE) — surfaced, not swallowed.
    try {
      w.castAs(VIEWER_VOTER, arg);
    } catch (e) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: String((e as Error)?.message ?? e),
        verified: w.verified(),
        receiptCount: w.receiptCount(),
        total: Number(w.total()),
      };
    }
    return {
      ok: true,
      tier: "extension",
      refused: false,
      verified: w.verified(),
      receiptCount: w.receiptCount(),
      total: Number(w.total()),
    };
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// THE COMPOSITION PORT — `<dregg-embed>` (a whole child CELL) and
// `<dregg-transclude>` (a value QUOTE). DOC-CELL-COMPOSITION.md §1/§2.3,
// DREGG-DOCUMENT-FOUNDATION.md §1.1–1.5, DREGG-WEB-SPEC.md pillar 5.
//
// The SAME split as the poll port: the ENGINE (background, wasm-side) resolves +
// verifies + renders + makes the trust/cap decision; the element is a thin,
// closed-shadow VIEW. No wasm, no keys, no cap-lattice ever reaches the page —
// only these tiered responses. The two operators are DISTINCT (§1):
//
//   resolveCell  — `<dregg-embed>`  — a whole child cell. LIVE by default
//                  (re-resolves to the child's tip) OR pinned to a receipt. Its
//                  own membrane boundary → its own shadow root. This is Op::Embed.
//   resolveValue — `<dregg-transclude>` — a VALUE quote: a snapshot of a
//                  finalized receipt. Never rots, never updates, UNEDITABLE.
//                  (The Xanadu quote.) Fail-CLOSED if it cannot be verified.
// ═══════════════════════════════════════════════════════════════════════════

/** The five resolution states of an embedded child cell (§2.3). The renderer
 * NEVER forges and NEVER panics — each is a first-class *state* of the output. */
export type CellResolution = "rendered" | "darkened" | "unresolved" | "cycle" | "unbound";

/** `Pin::Live` re-resolves to the child's tip every render; `Pin::At(receipt)`
 * freezes an immutable child receipt — a citation that never rots (§2.2). */
export type Pin = { kind: "live" } | { kind: "at"; receipt: string };

/** The public provenance/citation an embed or a quote carries. ALWAYS survives —
 * even a darkened embed keeps its citation (the membrane withholds only bytes). */
export interface Provenance {
  /** which cell (canonical `dregg://` uri). */
  cell: string;
  /** who owns/authored it (public), if known. */
  author?: string;
  /** the cited/pinned receipt (a pinned embed or a value quote). */
  receipt?: string;
  /** how it resolved: live tip vs a frozen receipt. */
  pin?: "live" | "at";
}

// ── the composition request/response protocol ───────────────────────────────
export type CellPortRequest =
  | { op: "resolveCell"; uri: string; pin?: Pin; ancestors?: string[] }
  | { op: "resolveValue"; uri: string };

export interface ResolveCellResponse {
  ok: boolean;
  /** which of the five states this child resolved to. */
  state: CellResolution;
  tier: TrustTier;
  /** the child's rendered HTML — PRESENT ONLY when `state === "rendered"`.
   *  It may itself contain nested `<dregg-*>` tags → the fold is RECURSIVE.
   *  On `darkened` the engine WITHHOLDS the bytes: this is `undefined` (the
   *  membrane projection — provenance survives, bytes never leave the engine). */
  html?: string;
  /** the citation/provenance — present for every non-error state, darkened too. */
  provenance?: Provenance;
  /** the canonical uri (for the light-DOM fallback link on a failed resolve). */
  canonical?: string;
  /** a human reason for a non-rendered state (unresolved/cycle/unbound). */
  reason?: string;
  error?: string;
}

export interface ResolveValueResponse {
  ok: boolean;
  /** the anchored quote verifier's verdict. `false` ⇒ the element fails closed. */
  verified: boolean;
  tier: TrustTier;
  /** the quoted, engine-rendered bytes — PRESENT ONLY when `verified`. */
  bytes?: string;
  provenance?: Provenance;
  error?: string;
}

export type CellPortResponse = ResolveCellResponse | ResolveValueResponse;

/** The transport a composition element holds — a channel to the CellEngine. */
export interface CellPort {
  request(req: CellPortRequest): Promise<CellPortResponse>;
}

// ── the resolver seam (the netlayer + membrane stand-in) ────────────────────
/** A child cell the netlayer fetched + the membrane projected for this viewer. */
export interface ResolvedCell {
  /** the child's rendered HTML (may embed grandchildren as nested `<dregg-*>`). */
  html: string;
  provenance: Provenance;
  /** the viewer's caps reach it. `false` ⇒ the ENGINE darkens (withholds html). */
  inCap: boolean;
}
/** A whole-cell lookup: found (with the projected cell) or not (why). */
export type CellLookup =
  | { found: true; cell: ResolvedCell }
  | { found: false; reason: "unbound" | "unresolved" };
/** Resolve a canonical cell uri (honoring the pin) to a lookup. May be async. */
export type ResolveCellFn = (uri: string, pin: Pin) => CellLookup | Promise<CellLookup>;

/** A finalized value quote: the bytes a source cell committed at a cited receipt. */
export interface ValueQuote {
  bytes: string;
  provenance: Provenance;
  /** the anchored verifier's verdict over the cited receipt. */
  verified: boolean;
}
/** Resolve a value uri to a quote, or `null` (unresolvable → fail-closed). */
export type ResolveValueFn = (uri: string) => ValueQuote | null | Promise<ValueQuote | null>;

export interface CellEngineDeps {
  resolveCell: ResolveCellFn;
  resolveValue: ResolveValueFn;
}

/**
 * THE COMPOSITION ENGINE. Runs only in the extension (background) context. It
 * makes the CAP/TRUST decision (darkening is engine-side — the bytes never leave
 * here on an out-of-cap child) and the CYCLE decision (the element supplies its
 * DOM ancestor chain — the composition tree IS the DOM — and the engine checks
 * membership). Every response is tiered; it never returns secret state and never
 * forges a child it could not resolve.
 */
export class CellEngine {
  constructor(private deps: CellEngineDeps) {}

  async handle(req: CellPortRequest): Promise<CellPortResponse> {
    try {
      switch (req.op) {
        case "resolveCell":
          return await this.resolveCell(req.uri, req.pin ?? { kind: "live" }, req.ancestors ?? []);
        case "resolveValue":
          return await this.resolveValue(req.uri);
        default:
          return { ok: false, state: "unresolved", tier: "none", error: "unknown op" } as ResolveCellResponse;
      }
    } catch (e) {
      return { ok: false, state: "unresolved", tier: "none", error: String((e as Error)?.message ?? e) };
    }
  }

  /** `<dregg-embed>`: resolve a whole child cell to one of the five states. */
  private async resolveCell(uri: string, pin: Pin, ancestors: string[]): Promise<ResolveCellResponse> {
    const canonical = canonicalUri(uri);
    if (!canonical) {
      return { ok: false, state: "unresolved", tier: "none", canonical: uri, reason: "not a dregg-thing" };
    }
    // CYCLE (§7): the target already sits above us in the composition tree.
    // A cycle is a first-class STATE, never a hang / stack overflow.
    if (ancestors.includes(canonical)) {
      return {
        ok: true,
        state: "cycle",
        tier: "extension",
        canonical,
        provenance: { cell: canonical, pin: pin.kind === "at" ? "at" : "live" },
        reason: "embedding this cell here would loop",
      };
    }
    const lookup = await this.deps.resolveCell(canonical, pin);
    if (!lookup.found) {
      // UNBOUND: a Name that binds to nothing (heals on rebind).
      // UNRESOLVED: a cell that could not be fetched at all (surfaced, not swallowed).
      return {
        ok: true,
        state: lookup.reason,
        tier: "extension",
        canonical,
        provenance: { cell: canonical },
        reason: lookup.reason === "unbound" ? "the name binds to nothing" : "the child could not be fetched",
      };
    }
    const cell = lookup.cell;
    const prov: Provenance = { ...cell.provenance, pin: pin.kind === "at" ? "at" : "live" };
    if (!cell.inCap) {
      // DARKENED — the membrane projection. Provenance survives; the bytes are
      // WITHHELD (html is undefined — they never leave the engine). §2.2.2.
      return { ok: true, state: "darkened", tier: "extension", canonical, provenance: prov, reason: "out of cap" };
    }
    // RENDERED — the child (its html may nest more `<dregg-*>` → the recursion).
    return { ok: true, state: "rendered", tier: "extension", canonical, html: cell.html, provenance: prov };
  }

  /** `<dregg-transclude>`: resolve a VALUE quote. Fail-CLOSED if unverifiable. */
  private async resolveValue(uri: string): Promise<ResolveValueResponse> {
    const canonical = canonicalUri(uri) ?? uri.trim();
    const quote = await this.deps.resolveValue(canonical);
    if (!quote) {
      return { ok: false, verified: false, tier: "none", error: "quote could not be resolved" };
    }
    if (!quote.verified) {
      // The anchored verifier refused — a bad quote is NEVER shown as a value.
      return { ok: false, verified: false, tier: "none", provenance: quote.provenance, error: "quote failed to verify" };
    }
    return { ok: true, verified: true, tier: "extension", bytes: quote.bytes, provenance: quote.provenance };
  }
}

/**
 * A dependency-free, in-memory web-of-cells (the netlayer + nameservice + value
 * store stand-in). The REAL substrate resolver (`WebOfCells::fetch` +
 * `Membrane::project` + the anchored `verify_anchored`) is named wiring; this is
 * the standalone analogue the fixture drives, exactly as `defaultResolveObject`
 * is for polls. A cell absent from the map is `unresolved`; a name explicitly
 * bound to nothing is `unbound`; `inCap: false` darkens; a value quote whose
 * `verified` is false fails closed.
 */
export class MapWebOfCells {
  private cells = new Map<string, ResolvedCell>();
  private unbound = new Set<string>();
  private values = new Map<string, ValueQuote>();

  setCell(uri: string, cell: ResolvedCell): this {
    const key = canonicalUri(uri) ?? uri;
    this.cells.set(key, cell);
    this.unbound.delete(key);
    return this;
  }
  /** Mark a name as currently bound to nothing (→ `unbound`; a later `setCell` heals it). */
  setUnbound(uri: string): this {
    const key = canonicalUri(uri) ?? uri;
    this.unbound.add(key);
    this.cells.delete(key);
    return this;
  }
  setValue(uri: string, quote: ValueQuote): this {
    this.values.set(canonicalUri(uri) ?? uri, quote);
    return this;
  }

  resolveCell: ResolveCellFn = (uri) => {
    const key = canonicalUri(uri) ?? uri;
    const cell = this.cells.get(key);
    if (cell) return { found: true, cell };
    if (this.unbound.has(key)) return { found: false, reason: "unbound" };
    return { found: false, reason: "unresolved" };
  };

  resolveValue: ResolveValueFn = (uri) => {
    return this.values.get(canonicalUri(uri) ?? uri) ?? null;
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// THE DOCUMENT-AUTHORING PORT — `<dregg-doc>` (a verifiable document surface).
// DREGG-DOCUMENT-FOUNDATION.md (conflicts-as-objects), wasm/src/bindings_doc.rs
// (`DocCollabWorld`). This is the culminating authoring path: a person authors a
// verifiable document a STRANGER can check — fork → diverge → stitch → a
// first-class CONFLICT (both live alternatives, side by side, attributed) →
// resolve (pick an alternative) → PUBLISH as a real cap-gated verified turn whose
// receipt commits the resealed umem `heap_root` (limb 28).
//
// The SAME split as the poll/composition ports: the ENGINE (background, wasm-side)
// owns the `DocCollabWorld`, the resolve, the render, the resolution, and the
// verified-turn publish — and routes the publish through the un-overlayable
// confirm-intent consent. The element is a thin, closed-shadow VIEW: no wasm, no
// keys, no doc graph ever reaches the page — only these tiered responses. A
// CONFLICT is NEVER silently resolved or hidden here: the engine renders BOTH
// alternatives (its `viewHtml` ConflictView) and only a consented publish
// collapses it.
// ═══════════════════════════════════════════════════════════════════════════

/** The `DocCollabWorld` wasm surface this engine needs (a structural subset of
 *  `wasm/src/bindings_doc.rs`'s `#[wasm_bindgen]` methods). */
export interface DocWorldLike {
  /** The doc-cell's id (hex) — the document's sovereignty boundary. */
  cellId(): string;
  /** The document's commitment: the committed umem-heap boundary `heap_root` (hex). */
  commitmentHex(): string;
  /** The audit-tape length (one receipt per published boundary, incl. genesis). */
  receiptCount(): number;
  /** True iff a stitched merge is currently carrying an unresolved conflict. */
  hasConflict(): boolean;
  /** The light-client invariant: committed `heap_root == substrate_commit(published)`. */
  boundaryMatchesProjection(): boolean;
  /** The pending conflict's alternatives as JSON: `[{author, text}]`. */
  alternativesJson(): string;
  /** The current published document's rendered text (the resolved reading). */
  publishedText(): string;
  /** The document view-tree JSON (`{kind, props, children}`). */
  viewTreeJson(): string;
  /** The rendered HTML fragment (the ConflictView when a conflict is held). */
  viewHtml(): string;
  /** The affordance wire: `stitch` (diverge+merge) | `resolve` (collapse+publish). */
  fire(turn: string, arg: number): void;
}
export interface DocWorldCtor {
  new (): DocWorldLike;
}

/** One live alternative in a conflict — attributed, NEVER hidden. */
export interface DocAlternative {
  author: string;
  text: string;
}

// ── the document request/response protocol ──────────────────────────────────
export type DocPortRequest =
  | { op: "resolveDoc"; uri: string }
  | { op: "renderDoc"; uri: string }
  | { op: "stitch"; uri: string }
  | { op: "resolveConflict"; uri: string; choice: number }
  | { op: "publish"; uri: string }
  | { op: "verify"; uri: string };

export interface DocResolveResponse {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  /** The document's public shape (never the graph itself). */
  object?: { kind: string; addr: string; cellId: string };
  /** True when the document currently carries a first-class conflict. */
  hasConflict?: boolean;
  /** Both live alternatives (attributed) — present whenever a conflict is held. */
  alternatives?: DocAlternative[];
  /** The committed umem boundary `heap_root` (hex). */
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export interface DocRenderResponse {
  ok: boolean;
  tier: TrustTier;
  /** The engine's `viewHtml()` — the ConflictView (both alternatives side by side,
   *  attributed, + a resolution button per choice) OR the clean published doc. */
  html?: string;
  hasConflict?: boolean;
  alternatives?: DocAlternative[];
  error?: string;
}

export interface DocConflictResponse {
  ok: boolean;
  tier: TrustTier;
  /** True once an alternative is STAGED (picked). The conflict is STILL shown —
   *  it collapses only on a consented publish, so nothing is hidden by picking. */
  staged?: boolean;
  choice?: number;
  hasConflict?: boolean;
  error?: string;
}

export interface DocPublishResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the publish turn was refused (consent denied / bad choice). */
  refused?: boolean;
  reason?: string;
  verified?: boolean;
  hasConflict?: boolean;
  receiptCount?: number;
  /** The NEW committed umem boundary `heap_root` (hex) after the publish turn. */
  commitment?: string;
  /** The light-client witness: the committed `heap_root` EQUALS the independent
   *  recompute of `substrate_commit(published)` — a stranger can re-check it. */
  substrateMatches?: boolean;
  error?: string;
}

export interface DocVerifyResponse {
  ok: boolean;
  tier: TrustTier;
  verified: boolean;
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export type DocPortResponse =
  | DocResolveResponse
  | DocRenderResponse
  | DocConflictResponse
  | DocPublishResponse
  | DocVerifyResponse;

/** The transport the `<dregg-doc>` element holds — a channel to the DocEngine. */
export interface DocPort {
  request(req: DocPortRequest): Promise<DocPortResponse>;
}

/** The public document spec a resolve yields (netlayer stand-in). `stitch` asks
 *  the engine to surface the demo divergence so the loaded document ALREADY
 *  carries a first-class conflict (the authoring case the fixture exercises). */
export interface DocSpec {
  kind: string;
  addr: string;
  stitch?: boolean;
}
/** Resolve a canonical doc uri to a spec, or `null` (fail-closed). May be async. */
export type ResolveDocFn = (uri: string) => DocSpec | null | Promise<DocSpec | null>;

export interface DocEngineDeps {
  DocWorld: DocWorldCtor;
  /** The netlayer resolve (content-addr → document spec). */
  resolveDoc: ResolveDocFn;
  /** Custody consent — opens `confirm-intent` chrome in the extension for a publish. */
  consent: ConsentFn;
}

/** The default (test/stand-in) doc resolver: validate the `dregg://doc/<addr>`
 *  content-address and yield a fresh document. The REAL netlayer fetches the
 *  content-addressed document and checks `addr == blake3(document)`; this is the
 *  standalone analogue (exactly as `defaultResolveObject` is for polls). A fresh
 *  document carries no conflict — the authoring divergence is surfaced explicitly
 *  (`stitch`); a malformed addr fails closed. */
export function defaultResolveDoc(uri: string): DocSpec | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  if (parsed.kind !== "doc") return null;
  if (!VALID_ADDR_RE.test(parsed.addr)) return null; // fail-closed on a bad addr
  return { kind: "doc", addr: parsed.addr, stitch: false };
}

/**
 * THE DOCUMENT ENGINE. Owns one `DocCollabWorld` per resolved uri; every response
 * is tiered. Runs only in the extension (background) context. It renders the
 * document (a ConflictView holds BOTH alternatives — never hidden), stages a
 * resolution pick, and PUBLISHES (a real cap-gated verified turn — reseal the
 * umem `heap_root`, commit `SetField(20)+IncrementNonce`) ONLY after the injected
 * consent approves the faithful reading. Never returns the doc graph itself.
 */
export class DocEngine {
  private worlds = new Map<string, DocWorldLike>();
  private specs = new Map<string, DocSpec>();
  /** The staged resolution pick per doc — set by `resolveConflict`, consumed by
   *  `publish`. Staging does NOT collapse the conflict; the publish does. */
  private staged = new Map<string, number>();

  constructor(private deps: DocEngineDeps) {}

  async handle(req: DocPortRequest, origin?: string): Promise<DocPortResponse> {
    try {
      switch (req.op) {
        case "resolveDoc":
          return await this.resolve(req.uri);
        case "renderDoc":
          return this.render(req.uri);
        case "stitch":
          return await this.stitch(req.uri);
        case "resolveConflict":
          return this.resolveConflict(req.uri, req.choice);
        case "publish":
          return await this.publish(req.uri, origin);
        case "verify":
          return this.verify(req.uri);
        default:
          return { ok: false, tier: "none", verified: false, error: "unknown op" } as DocResolveResponse;
      }
    } catch (e) {
      return { ok: false, tier: "none", verified: false, error: String((e as Error)?.message ?? e) };
    }
  }

  private async world(uri: string): Promise<DocWorldLike | null> {
    const key = canonicalUri(uri);
    if (!key) return null;
    const existing = this.worlds.get(key);
    if (existing) return existing;
    const spec = await this.deps.resolveDoc(key);
    if (!spec) return null;
    const w = new this.deps.DocWorld();
    // Surface the authoring divergence so the loaded document carries a first-class
    // conflict (the case the authoring path is FOR). A fresh document has none.
    if (spec.stitch) w.fire("stitch", 0);
    this.worlds.set(key, w);
    this.specs.set(key, spec);
    return w;
  }

  /** Parse the wasm's `[{author, text}]` alternatives — both alternatives always
   *  travel together (the anti-forge tooth binds them into `substrate_commit`). */
  private alternatives(w: DocWorldLike): DocAlternative[] {
    try {
      const rows = JSON.parse(w.alternativesJson());
      if (!Array.isArray(rows)) return [];
      return rows.map((r) => ({ author: String(r.author ?? ""), text: String(r.text ?? "") }));
    } catch {
      return [];
    }
  }

  private async resolve(uri: string): Promise<DocResolveResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, verified: false, tier: "none", error: "not a dregg-thing" };
    const w = await this.world(key);
    if (!w) return { ok: false, verified: false, tier: "none", error: "could not resolve document" };
    const spec = this.specs.get(key)!;
    // The light-client invariant: the committed boundary equals the canonical
    // projection of the published reading (the membership/anti-forge guarantee).
    const verified = w.boundaryMatchesProjection();
    return {
      ok: true,
      verified,
      tier: verified ? "extension" : "none",
      object: { kind: spec.kind, addr: spec.addr, cellId: w.cellId() },
      hasConflict: w.hasConflict(),
      alternatives: this.alternatives(w),
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }

  private render(uri: string): DocRenderResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", error: "not resolved" };
    // Never render a document whose boundary does not match its projection (§6).
    if (!w.boundaryMatchesProjection()) return { ok: false, tier: "none", error: "unverified" };
    return {
      ok: true,
      tier: "extension",
      html: w.viewHtml(),
      hasConflict: w.hasConflict(),
      alternatives: this.alternatives(w),
    };
  }

  /** STITCH — surface a concurrent divergence (the pushout) as a first-class
   *  conflict, held off-heap (the committed boundary does not move). */
  private async stitch(uri: string): Promise<DocConflictResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    try {
      w.fire("stitch", 0);
    } catch (e) {
      return { ok: false, tier: "none", error: String((e as Error)?.message ?? e) };
    }
    return { ok: true, tier: "extension", hasConflict: w.hasConflict() };
  }

  /** RESOLVE-CONFLICT — STAGE the pick of an alternative. The conflict is STILL
   *  shown (both alternatives) until a consented publish collapses it; picking
   *  never hides an alternative. */
  private resolveConflict(uri: string, choice: number): DocConflictResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    if (!w.hasConflict()) return { ok: false, tier: "none", error: "no conflict to resolve" };
    if (!Number.isInteger(choice) || choice < 0) return { ok: false, tier: "none", error: "invalid choice" };
    this.staged.set(key, choice);
    return { ok: true, tier: "extension", staged: true, choice, hasConflict: w.hasConflict() };
  }

  /** PUBLISH — the real cap-gated verified turn. Consent BEFORE any commit (the
   *  faithful reading of the publish turn, in un-overlayable chrome). On approval,
   *  `fire("resolve", choice)` collapses the conflict, reseals the umem `heap_root`
   *  to `substrate_commit(resolved)`, and commits `SetField(20)+IncrementNonce`;
   *  the receipt witnesses the new boundary at limb 28. */
  private async publish(uri: string, origin?: string): Promise<DocPublishResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    if (!w.hasConflict()) return { ok: false, tier: "none", error: "nothing to publish (no held conflict)" };
    if (!this.staged.has(key)) return { ok: false, tier: "none", error: "pick an alternative first" };
    const choice = this.staged.get(key)!;
    const spec = this.specs.get(key)!;
    const chosen = this.alternatives(w)[choice]?.author ?? `choice ${choice}`;

    // Custody consent (the load-bearing property): the faithful reading the page
    // cannot overlay or clickjack. Every publish is a real turn, so every publish asks.
    const approved = await this.deps.consent({
      explanation:
        `Publish the resolved document ${spec.addr} to the umem-heap. ` +
        `You are keeping the alternative by ${chosen} and committing ONE verified turn ` +
        `that binds the new document commitment (heap_root) into the receipt (limb 28).`,
      turnId: `${key}#publish:${choice}`,
      origin,
    });
    if (!approved) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: "consent denied",
        verified: w.boundaryMatchesProjection(),
        hasConflict: w.hasConflict(),
        commitment: w.commitmentHex(),
        receiptCount: w.receiptCount(),
      };
    }

    // The real verified turn: resolve + publish (reseal heap_root, commit turn).
    try {
      w.fire("resolve", choice);
    } catch (e) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: String((e as Error)?.message ?? e),
        verified: w.boundaryMatchesProjection(),
        hasConflict: w.hasConflict(),
        commitment: w.commitmentHex(),
        receiptCount: w.receiptCount(),
      };
    }
    this.staged.delete(key);
    const substrateMatches = w.boundaryMatchesProjection();
    return {
      ok: true,
      tier: "extension",
      refused: false,
      verified: substrateMatches,
      hasConflict: w.hasConflict(),
      receiptCount: w.receiptCount(),
      commitment: w.commitmentHex(),
      substrateMatches,
    };
  }

  /** VERIFY — the LIGHT-CLIENT check a stranger runs: independently recompute
   *  `substrate_commit(published)` and confirm it equals the committed `heap_root`
   *  the receipt bound. This is the "a stranger checks the receipt chain" property. */
  private verify(uri: string): DocVerifyResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", verified: false, error: "not resolved" };
    const verified = w.boundaryMatchesProjection();
    return {
      ok: true,
      tier: verified ? "extension" : "none",
      verified,
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }
}
