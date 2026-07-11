/**
 * THE COLLECTIVE DUNGEON — a CROWD steers one shared party through the attested dungeon by VOTE.
 *
 * This unites the two halves of the project: collective fiction (the crowd co-authors the next
 * move) + the AI dungeon (a local model narrates, the WORLD resolves). Each turn: OPEN a vote
 * round over the candidate actions, the seated party CASTS ballots (one write-once ballot each),
 * CLOSE it — and the winning action is resolved through the SAME /game/act path (the model narrates,
 * resolve_action decides, a verified turn lands). The crowd DECIDES; the world still RESOLVES:
 * a voted-for locked exit is still refused (no receipt), and the party must vote again.
 *
 * HONEST SCOPE: the vote is a simple MAJORITY vote among the seated party (one write-once ballot
 * per voter per round, plurality winner, ties broken by lowest optionId) — NOT a quorum
 * certificate. What is load-bearing is unchanged: the world resolution, the cap gate, the chain.
 *
 * The page speaks ONLY the service contract over fetch:
 *   GET /game/state · GET /party/options · POST /party/open · POST /party/vote {voter,optionId}
 *   · GET /party/tally · POST /party/close · GET /game/verify · POST /game/reset
 */

declare const window: any;

interface RoomView { id: string; name: string; description: string }
interface GameState {
  world: string; worldName: string; room: RoomView; inventory: string[];
  objective: string; status: "playing" | "won" | "lost";
  receiptCount: number; commitmentHex: string; narratorKind: string;
}
interface Ballot { id: number; command: string; label: string }
interface TallyRow extends Ballot { count: number }
interface OpenResp { ok: boolean; roundId: number; options: Ballot[]; state: GameState; reason?: string }
interface VoteResp { ok: boolean; voter?: string; optionId?: number; refused?: string; reason?: string; tally?: { tally: TallyRow[]; totalVotes: number } }
interface CloseResp {
  ok: boolean; roundId?: number; winner?: TallyRow; tie?: boolean; tieBreak?: string;
  tally?: { tally: TallyRow[]; totalVotes: number };
  resolved?: { ok: boolean; narration: string; outcome: "landed" | "refused"; reason?: string; actionLabel?: string; state: GameState };
  refused?: string; reason?: string;
}

const $ = (id: string) => document.getElementById(id)!;
async function jget<T>(url: string): Promise<T> {
  const r = await fetch(url, { headers: { accept: "application/json" } });
  return (await r.json()) as T;
}
async function jpost<T>(url: string, body?: unknown): Promise<T> {
  const r = await fetch(url, { method: "POST", headers: { "content-type": "application/json" }, body: body === undefined ? "{}" : JSON.stringify(body) });
  return (await r.json()) as T;
}
function short(hex: string): string { return hex && hex.length > 12 ? `${hex.slice(0, 8)}…${hex.slice(-6)}` : hex || "—"; }
function escapeHtml(s: string): string { return String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]!)); }

// ── the seated party — five named adventurers who co-author the shared party's path ──
const SEATS = ["Bramwen", "Corvin", "Della", "Ferro", "Wisp"];

let currentRound: { id: number; options: Ballot[] } | null = null;
// A local mirror of who has voted for what this round (the authoritative tally comes from the
// service; this only drives the seat chips + the "next unvoted seat" the click-to-cast uses).
let seatVote: Record<string, number> = {};

// ── narratorKind, HONESTLY ─────────────────────────────────────────────────────
function renderNarratorKind(kind: string) {
  const el = $("narratorKind");
  if (kind && kind.startsWith("model:")) {
    el.className = "narrator model";
    el.innerHTML = `🧠 narrated by a real local model <code>${escapeHtml(kind.slice("model:".length))}</code> — the crowd decides the move; the <b>world</b> resolves it.`;
  } else {
    el.className = "narrator";
    el.innerHTML = "🎭 <b>deterministic scripted narrator</b> (ollama unreachable) — the vote, the world resolution, and the receipt rail are <b>real</b>. Start the game service (hosted Claude Haiku 4.5, or a local ollama) for live narration.";
  }
}

// ── the room ──────────────────────────────────────────────────────────────────
function renderRoom(s: GameState) {
  $("roomName").textContent = s.room.name;
  $("roomDesc").textContent = s.room.description;
  $("objectiveText").textContent = s.objective;
  $("nowPlaying").textContent = s.worldName || "…";
  const inv = $("inventory");
  inv.innerHTML = s.inventory.length
    ? s.inventory.map((i) => `<span class="held">${escapeHtml(i.replace(/_/g, " "))}</span>`).join("")
    : '<span class="empty">— empty-handed —</span>';
}

// ── the seated party chips ──────────────────────────────────────────────────────
function labelForOption(id: number): string {
  const o = currentRound?.options.find((x) => x.id === id);
  return o ? o.command : `option ${id}`;
}
function renderSeats() {
  const el = $("seats");
  el.innerHTML = SEATS.map((name) => {
    const voted = Object.prototype.hasOwnProperty.call(seatVote, name);
    const cls = voted ? "seat voted" : "seat";
    const choice = voted ? `<span class="seat-choice">→ ${escapeHtml(labelForOption(seatVote[name]))}</span>` : `<span class="seat-choice waiting">…undecided</span>`;
    return `<div class="${cls}"><span class="seat-name">${escapeHtml(name)}</span>${choice}</div>`;
  }).join("");
  const voted = Object.keys(seatVote).length;
  $("seatSummary").textContent = currentRound
    ? `${voted} of ${SEATS.length} adventurers have cast a ballot`
    : "no vote in progress";
}

// ── the ballot + live tally ─────────────────────────────────────────────────────
function renderBallot(rows: TallyRow[] | null) {
  const el = $("ballot");
  if (!currentRound) {
    el.innerHTML = '<p class="empty">No vote in progress. Open a round to put the party\'s next move to the crowd.</p>';
    updateProgress();
    return;
  }
  const opts = currentRound.options;
  const counts: Record<number, number> = {};
  let total = 0;
  if (rows) for (const r of rows) { counts[r.id] = r.count; total += r.count; }
  // The current front-runner (plurality; a tie resolves to the lowest optionId, as the service does).
  let leadId = -1, leadCount = 0;
  for (const o of opts) { const c = counts[o.id] || 0; if (c > leadCount) { leadCount = c; leadId = o.id; } }
  el.innerHTML = opts.map((o) => {
    const c = counts[o.id] || 0;
    const pct = total > 0 ? Math.round((c / total) * 100) : 0;
    const locked = /barred/i.test(o.label);
    const leading = o.id === leadId && leadCount > 0;
    const aria = `Vote to ${o.command}${locked ? " (a barred exit)" : ""} — ${c} vote${c === 1 ? "" : "s"}${leading ? ", currently the front-runner" : ""}`;
    return `<button class="opt ${locked ? "locked" : ""} ${leading ? "leading" : ""}" data-opt="${o.id}" type="button" aria-label="${escapeHtml(aria)}">` +
      `<span class="opt-top"><span class="opt-label">${escapeHtml(o.label)}${leading ? ' <span class="opt-lead-tag">front-runner</span>' : ""}</span>` +
      `<span class="opt-count">${c} vote${c === 1 ? "" : "s"}${total > 0 ? `<span class="opt-pct">${pct}%</span>` : ""}</span></span>` +
      `<span class="opt-cmd"><code>${escapeHtml(o.command)}</code></span>` +
      `<span class="opt-bar"><span class="opt-fill" style="width:${pct}%"></span></span>` +
      `</button>`;
  }).join("");
  el.querySelectorAll<HTMLButtonElement>("button.opt").forEach((b) => {
    b.addEventListener("click", () => castNextSeat(Number(b.dataset.opt)));
  });
  updateProgress();
}

// ── round-state pill + the "how many have voted" progress bar ──
function updateProgress() {
  const fill = document.querySelector<HTMLElement>("#turnProgress .tp-fill");
  if (!fill) return;
  const voted = Object.keys(seatVote).length;
  fill.style.width = (currentRound ? Math.round((voted / SEATS.length) * 100) : 0) + "%";
}
type RoundStateKind = "idle" | "open" | "resolving" | "landed" | "refused";
function setRoundState(kind: RoundStateKind, text: string) {
  const el = document.getElementById("roundState");
  if (!el) return;
  el.className = "round-state" + (kind === "idle" ? "" : " " + kind);
  const t = el.querySelector(".rs-text");
  if (t) t.textContent = text; else el.textContent = text;
}

// ── the receipt rail ─────────────────────────────────────────────────────────
function renderChain(count: number, commitmentHex: string) {
  const links = $("chainLinks");
  const parts: string[] = [];
  for (let i = 0; i < Math.max(count, 0); i++) { if (i) parts.push('<span class="rope">—</span>'); parts.push("✓"); }
  links.innerHTML = parts.join("") || '<span class="empty">— no turns yet —</span>';
  $("chainMeta").innerHTML = `<b>${count}</b> voted move${count === 1 ? "" : "s"} landed as verified turns · running commitment <code>${short(commitmentHex)}</code>`;
}
async function renderVerifyBadge(): Promise<boolean> {
  const badge = $("verifyBadge");
  try {
    const { verified, receiptCount } = await jget<{ verified: boolean; receiptCount: number }>("/game/verify");
    badge.className = verified ? "verify ok" : "verify bad";
    badge.textContent = verified
      ? `✓ the whole ledger re-verifies as a hash chain — ${receiptCount} voted turn${receiptCount === 1 ? "" : "s"}, each authentic, injection-free, prev-linked`
      : "✗ the ledger failed to re-verify";
    return verified;
  } catch (e) {
    badge.className = "verify bad";
    badge.textContent = "✗ verify unreachable: " + String((e as any)?.message ?? e);
    return false;
  }
}

// ── the chronicle (per resolved turn) ────────────────────────────────────────
interface ChronRow { round: number; winner: string; tie: boolean; outcome: string; narration: string; reason?: string }
const chronicle: ChronRow[] = [];
function renderChronicle() {
  const el = $("chronicle");
  if (!chronicle.length) { el.innerHTML = '<p class="empty">The party stands at the threshold. Open the first vote.</p>'; return; }
  el.innerHTML = chronicle.map((e) => {
    const refused = e.outcome === "refused";
    return `<div class="entry ${refused ? "refused" : "landed"}">` +
      `<div class="cmd">round #${e.round} · the party voted <b>${escapeHtml(e.winner)}</b>${e.tie ? ' <span class="tie">(tie → lowest optionId)</span>' : ""}</div>` +
      (e.narration ? `<div class="prose">${escapeHtml(e.narration)}</div>` : "") +
      (refused
        ? `<div class="verdict">⛔ the WORLD refused it — ${escapeHtml(e.reason || "the world disposed")}<span class="sub"> (no receipt — the room did not move; the party must vote again)</span></div>`
        : `<div class="verdict">✓ landed — a verified turn; the dungeon advances</div>`) +
      `</div>`;
  }).join("");
  const last = el.querySelector<HTMLElement>(".entry:last-child");
  if (last && chronicle.length) last.classList.add("flash");
  el.scrollTop = el.scrollHeight;
}

// ── the win / lose banner ────────────────────────────────────────────────────
function renderBanner(status: string) {
  const b = $("banner");
  if (status === "won") {
    b.className = "banner show won";
    $("bannerTitle").textContent = "★ The party escapes into the light.";
    $("bannerBody").textContent = "The crowd steered them through, one voted turn at a time. Every step is a verified turn on the receipt rail — replay it and the chain holds.";
  } else if (status === "lost") {
    b.className = "banner show lost";
    $("bannerTitle").textContent = "☠ The dungeon keeps the party.";
    $("bannerBody").textContent = "The crowd led them into the dark. Restart to try a different path.";
  } else {
    b.className = "banner"; $("bannerTitle").textContent = ""; $("bannerBody").textContent = "";
  }
}

// ── the vote lifecycle ──────────────────────────────────────────────────────
let busy = false;
function setBusy(on: boolean) {
  for (const id of ["openBtn", "closeBtn", "autoBtn", "resetBtn"]) {
    const el = document.getElementById(id) as any; if (el) el.disabled = on;
  }
}
function setPhase() {
  const open = !!currentRound;
  ($("openBtn") as any).disabled = open || busy;
  ($("closeBtn") as any).disabled = !open || busy || Object.keys(seatVote).length === 0;
  ($("autoBtn") as any).disabled = !open || busy;
}

async function refreshState() {
  const s = await jget<GameState>("/game/state");
  renderNarratorKind(s.narratorKind || "scripted");
  renderRoom(s);
  renderChain(s.receiptCount, s.commitmentHex);
  renderBanner(s.status);
  await renderVerifyBadge();
  return s;
}

async function openVote(): Promise<OpenResp> {
  if (busy) throw new Error("busy");
  busy = true; setBusy(true);
  try {
    const resp = await jpost<OpenResp>("/party/open");
    if (!resp.ok) { throw new Error(resp.reason || "could not open a round"); }
    currentRound = { id: resp.roundId, options: resp.options };
    seatVote = {};
    renderRoom(resp.state);
    renderSeats();
    renderBallot(null);
    setRoundState("open", `round #${resp.roundId} open — awaiting ballots`);
    $("phaseHint").textContent = `Round #${resp.roundId} is open. Each adventurer casts one ballot; then close the vote and the world resolves the winner.`;
    return resp;
  } finally { busy = false; setBusy(false); setPhase(); }
}

async function castVote(voter: string, optionId: number): Promise<VoteResp> {
  const resp = await jpost<VoteResp>("/party/vote", { voter, optionId });
  if (resp.ok) {
    seatVote[voter] = optionId;
  }
  renderSeats();
  renderBallot(resp.tally ? resp.tally.tally : null);
  if (currentRound) {
    const voted = Object.keys(seatVote).length;
    setRoundState("open", voted >= SEATS.length
      ? `round #${currentRound.id} · all ${SEATS.length} voted — close to resolve`
      : `round #${currentRound.id} · ${voted}/${SEATS.length} voted`);
  }
  setPhase();
  return resp;
}

// Click-to-cast: the clicked option receives the ballot of the next still-undecided seat.
async function castNextSeat(optionId: number) {
  if (!currentRound) return;
  const next = SEATS.find((s) => !Object.prototype.hasOwnProperty.call(seatVote, s));
  if (!next) { $("phaseHint").textContent = "Every adventurer has voted. Close the vote to resolve the party's choice."; return; }
  await castVote(next, optionId).catch((e) => console.error(e));
  if (Object.keys(seatVote).length === SEATS.length) {
    $("phaseHint").textContent = "Every adventurer has voted. Close the vote — the world resolves the winner.";
  }
}

// Cast a ballot for every still-undecided seat, spread across the options (a quick crowd).
async function autoFill() {
  if (!currentRound || busy) return;
  busy = true; setBusy(true);
  try {
    const opts = currentRound.options;
    let i = 0;
    for (const s of SEATS) {
      if (Object.prototype.hasOwnProperty.call(seatVote, s)) continue;
      // Bias the crowd toward the first (usually a legal) option, but spread a little.
      const pick = opts[(i % 2 === 0 ? 0 : (i % opts.length))].id;
      i++;
      await castVote(s, pick);
    }
  } finally { busy = false; setBusy(false); setPhase(); }
}

async function closeVote(): Promise<CloseResp> {
  if (busy || !currentRound) throw new Error("no open round");
  busy = true; setBusy(true);
  const roundId = currentRound.id;
  setRoundState("resolving", `round #${roundId} — the world resolves the winner…`);
  try {
    const resp = await jpost<CloseResp>("/party/close");
    if (!resp.ok) { throw new Error(resp.reason || "could not close the round"); }
    const r = resp.resolved!;
    chronicle.push({
      round: roundId,
      winner: resp.winner ? resp.winner.command : "(none)",
      tie: !!resp.tie,
      outcome: r.outcome,
      narration: r.narration,
      reason: r.reason,
    });
    currentRound = null;
    seatVote = {};
    $("narrationText").textContent = r.narration || "(the dungeon master says nothing)";
    renderRoom(r.state);
    renderSeats();
    renderBallot(null);
    renderChronicle();
    renderChain(r.state.receiptCount, r.state.commitmentHex);
    renderBanner(r.state.status);
    await renderVerifyBadge();
    if (r.outcome === "refused") {
      setRoundState("refused", `round #${roundId} — the world REFUSED it (no receipt)`);
      $("phaseHint").textContent = `The world REFUSED the party's choice (${escapeHtml(r.reason || "barred")}). No receipt — open another vote and choose again.`;
    } else {
      setRoundState("landed", `round #${roundId} — landed as verified turn #${r.state.receiptCount}`);
      $("phaseHint").textContent = "The world resolved the party's choice. Open the next vote to press on.";
    }
    return resp;
  } finally { busy = false; setBusy(false); setPhase(); }
}

async function reset(world?: string): Promise<GameState> {
  const body = world ? { world } : {};
  const { state } = await jpost<{ ok: boolean; state: GameState }>("/game/reset", body);
  currentRound = null; seatVote = {}; chronicle.length = 0;
  $("narrationText").textContent = `The party gathers at the threshold of ${state.worldName || "the dungeon"}. Open the first vote.`;
  renderNarratorKind(state.narratorKind || "scripted");
  renderRoom(state);
  renderSeats();
  renderBallot(null);
  renderChronicle();
  renderChain(state.receiptCount, state.commitmentHex);
  renderBanner(state.status);
  await renderVerifyBadge();
  setRoundState("idle", "no vote in progress");
  setPhase();
  return state;
}

// ── boot ─────────────────────────────────────────────────────────────────────
async function boot() {
  try {
    await refreshState();
    renderSeats();
    renderBallot(null);
    renderChronicle();
    setRoundState("idle", "no vote in progress");
    $("openBtn").addEventListener("click", () => openVote().catch((e) => console.error(e)));
    $("closeBtn").addEventListener("click", () => closeVote().catch((e) => console.error(e)));
    $("autoBtn").addEventListener("click", () => autoFill().catch((e) => console.error(e)));
    $("resetBtn").addEventListener("click", () => reset().catch((e) => console.error(e)));
    setPhase();
    window.__PARTY_READY = true;
  } catch (e) {
    window.__PARTY_ERROR = String((e as any)?.stack ?? e);
    const badge = $("verifyBadge");
    badge.className = "verify bad";
    badge.textContent = "✗ could not reach the /party service: " + String((e as any)?.message ?? e);
  }
}

// Driver hooks (the same service contract the buttons take).
window.__partyReset = (world?: string) => reset(world);
window.__partyState = () => jget<GameState>("/game/state");
window.__partyOptions = () => jget("/party/options");
window.__partyOpen = () => openVote();
window.__partyVote = (voter: string, optionId: number) => castVote(voter, optionId);
window.__partyVoteRaw = (voter: string, optionId: number) => jpost("/party/vote", { voter, optionId });
window.__partyTally = () => jget("/party/tally");
window.__partyClose = () => closeVote();

boot();
