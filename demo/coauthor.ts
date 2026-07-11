/**
 * THE COMMONS FORGE — a CROWD co-authors ONE shared dungeon draft by quorum-certified VOTE.
 *
 * The "collectivity" heart: the crowd PROPOSES bounded, typed edits to a server-held shared draft;
 * the seated co-authors QUORUM-VOTE on the real collective-choice engine; and the VALIDATOR
 * (parse_dungeon) DISPOSES — a certified edit that would break the world is refused and rolled back
 * even though it won the vote. The draft grows over time and stays PLAYABLE at every step.
 *
 * The page speaks ONLY the service contract over fetch:
 *   GET /coauthor/draft · GET /coauthor/proposals · POST /coauthor/propose {editType,...}
 *   · POST /coauthor/open · POST /coauthor/vote {voter,optionId} · GET /coauthor/tally
 *   · POST /coauthor/close · POST /coauthor/reset
 *
 * The draft's room graph is drawn with the SHARED `roommap.ts` visualizer (the same one /vault and
 * /forge use). It exposes `window.__co*` hooks so `run-coauthor.mjs` can drive it headless.
 */

import { renderRoomMap, type MapRoom } from "./roommap";

declare const window: any;

interface MapExitView { name: string; to: string; toName: string; locked: boolean; gateReason: string | null }
interface DraftView {
  name: string; source: string; sourceHash: string; start: string;
  objective: { room: string; holding: string; text: string };
  roomCount: number; map: (MapRoom & { exits: MapExitView[] })[]; plays: boolean;
  history: HistoryEntry[]; appliedCount: number; voteModel: string;
}
interface EditView { type: string; [k: string]: unknown }
interface Proposal { proposalId: number; optionId: number | null; kind: string; summary: string; proposer: string; edit: EditView }
interface Quorum { threshold: number; ballotsCast: number; met: boolean; electorateSize: number }
interface TallyRow { optionId: number; proposalId: number; kind: string; summary: string; count: number }
interface RoundView { roundId: number; open: boolean; question: string; totalVotes: number; tally: TallyRow[]; quorum: Quorum }
interface ProposalsView { proposals: Proposal[]; round: RoundView | null; voteModel: string; quorum: { threshold: number; electorateSize: number; seats: string[] }; editTypes: string[] }
interface Cert {
  kind: string; question: string; quorumThreshold: number; ballotsCast: number; quorumMet: boolean;
  winner?: { summary: string; kind: string }; winnerTally: number; lightClientAgrees: boolean;
  electorate: { size: number; seats: string[]; commitmentHex: string };
  real: string; productionGap: string; disposedBy: string;
}
interface HistoryEntry {
  seq: number; roundId: number; summary: string; kind: string; disposition: string;
  refuseStage: string | null; reason: string | null; sourceHash: string; cert: Cert;
}
interface CloseResp {
  ok: boolean; refused?: string; reason?: string; roundId?: number; quorumCertified?: boolean;
  cert?: Cert; winner?: { kind: string; summary: string; edit: EditView };
  disposition?: { applied: boolean; outcome: string; stage: string | null; reason: string | null; note: string };
  historySeq?: number; draft?: DraftView; quorum?: Quorum;
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
function esc(s: string): string { return String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]!)); }

const SEATS = ["Ansel", "Briar", "Cyra", "Doon", "Elowen"];

let lastDraft: DraftView | null = null;
let lastProposals: ProposalsView | null = null;
// A local mirror of who cast for what this round (drives the seat chips + click-to-cast).
let seatVote: Record<string, number> = {};

// ── the edit-proposal form: fields per edit kind ────────────────────────────────
const FIELD_DEFS: Record<string, { key: string; label: string; ph: string }[]> = {
  AddRoom: [
    { key: "id", label: "room id", ph: "hall" },
    { key: "name", label: "display name", ph: "The Long Hall" },
    { key: "description", label: "description", ph: "A long echoing hall of cold stone." },
  ],
  AddExit: [
    { key: "from", label: "from room", ph: "threshold" },
    { key: "dir", label: "direction", ph: "north" },
    { key: "to", label: "to room", ph: "hall" },
    { key: "gateItem", label: "gate item (optional)", ph: "" },
  ],
  PlaceItem: [
    { key: "room", label: "room", ph: "hall" },
    { key: "item", label: "item", ph: "torch" },
  ],
  SetObjective: [
    { key: "room", label: "objective room", ph: "hall" },
    { key: "holding", label: "win item", ph: "torch" },
  ],
};

function renderFields() {
  const type = ($("editType") as HTMLSelectElement).value;
  const defs = FIELD_DEFS[type] || [];
  $("editFields").innerHTML = defs
    .map(
      (d) =>
        `<div class="field"><label for="f_${d.key}">${esc(d.label)}</label>` +
        `<input type="text" id="f_${d.key}" data-key="${d.key}" placeholder="${esc(d.ph)}" autocomplete="off" /></div>`
    )
    .join("");
}

function collectEdit(): Record<string, unknown> {
  const type = ($("editType") as HTMLSelectElement).value;
  const out: Record<string, unknown> = { editType: type, proposer: "you" };
  for (const inp of Array.from($("editFields").querySelectorAll("input[data-key]"))) {
    const el = inp as HTMLInputElement;
    const key = el.dataset.key!;
    const val = el.value.trim();
    if (key === "gateItem") {
      if (val) out.gate = { item: val };
    } else {
      out[key] = val;
    }
  }
  return out;
}

// ── rendering ───────────────────────────────────────────────────────────────────
function renderDraft(d: DraftView) {
  lastDraft = d;
  $("objectiveText").textContent = d.objective.text;
  $("roomCount").textContent = String(d.roomCount);
  const plays = $("playsBadge");
  plays.textContent = d.plays ? "✓ plays" : "✗ broken";
  plays.className = "plays " + (d.plays ? "ok" : "bad");
  $("sourceHash").textContent = short(d.sourceHash);
  $("appliedCount").textContent = String(d.appliedCount);
  ($("sourceText") as HTMLElement).textContent = d.source;
  // The room graph, drawn with the shared visualizer. All rooms are "known" (the crowd authored
  // them); the start room reads as "you are here".
  renderRoomMap($("draftMap"), d.map as unknown as MapRoom[], { allKnown: true, currentRoomId: d.start });
  renderHistory(d.history);
}

function renderHistory(hist: HistoryEntry[]) {
  const box = $("history");
  if (!hist.length) {
    box.innerHTML = `<div class="empty">no edits yet — propose one and put it to a vote.</div>`;
    return;
  }
  box.innerHTML = hist
    .slice()
    .reverse()
    .map((h) => {
      const applied = h.disposition === "applied";
      const verdict = applied
        ? `applied <span class="sub">— sound; the draft grew (source ${short(h.sourceHash)})</span>`
        : `refused by the validator <span class="sub">(${esc(h.refuseStage || "validate")}) — ${esc(h.reason || "")}</span>`;
      const light = h.cert?.lightClientAgrees ? "light-client ✓" : "light-client ✗";
      return (
        `<div class="hist ${applied ? "applied" : "refused"}">` +
        `<div class="hist-top"><span class="hist-summary">${esc(h.summary)}</span><span class="hist-seq">#${h.seq} · round ${h.roundId}</span></div>` +
        `<div class="hist-verdict">${verdict}</div>` +
        `<div class="hist-cert">quorum-certified: ${h.cert?.winnerTally ?? "?"} vote(s), quorum ${h.cert?.quorumMet ? "met" : "not met"} · ${light}</div>` +
        `</div>`
      );
    })
    .join("");
}

function renderSeats() {
  $("seats").innerHTML = SEATS.map((s) => {
    const voted = seatVote[s] !== undefined;
    const choice = voted ? `option ${seatVote[s]}` : "waiting…";
    return (
      `<div class="seat ${voted ? "voted" : ""}"><span class="seat-name">${esc(s)}</span>` +
      `<span class="seat-choice ${voted ? "" : "waiting"}">${esc(choice)}</span></div>`
    );
  }).join("");
}

function renderPool(pv: ProposalsView, tally?: RoundView | null) {
  lastProposals = pv;
  const round = tally || pv.round;
  const counts: Record<number, number> = {};
  let leadOpt = -1;
  let leadCount = -1;
  if (round) {
    for (const row of round.tally) {
      counts[row.optionId] = row.count;
      if (row.count > leadCount) { leadCount = row.count; leadOpt = row.optionId; }
    }
  }
  const pool = $("pool");
  if (!pv.proposals.length && !round) {
    pool.innerHTML = `<div class="empty">no proposals yet — add a bounded edit above.</div>`;
  } else {
    // When a round is open, show its frozen slate (with tallies); else the pending pool.
    const items = round
      ? round.tally.map((row) => ({ optionId: row.optionId, summary: row.summary, kind: row.kind, count: row.count, proposer: "" }))
      : pv.proposals.map((p) => ({ optionId: p.optionId, summary: p.summary, kind: p.kind, count: 0, proposer: p.proposer }));
    const total = round ? round.tally.reduce((a, r) => a + r.count, 0) : 0;
    pool.innerHTML = items
      .map((it) => {
        const oid = it.optionId;
        const c = oid !== null && oid !== undefined ? (counts[oid] ?? it.count) : 0;
        const pct = total > 0 ? Math.round((c / total) * 100) : 0;
        const leading = round && oid === leadOpt && leadCount > 0;
        const clickable = round && oid !== null && oid !== undefined;
        return (
          `<div class="prop ${leading ? "leading" : ""}" ${clickable ? `data-opt="${oid}" role="button" tabindex="0"` : ""}>` +
          `<div class="prop-top"><span class="prop-summary">${esc(it.summary)}</span>` +
          `<span class="prop-count">${round ? `${c} vote${c === 1 ? "" : "s"}` : ""}<span class="prop-lead-tag"> · leading</span></span></div>` +
          `<div><span class="prop-kind">${esc(it.kind)}</span>${it.proposer ? ` <span class="prop-by">proposed by ${esc(it.proposer)}</span>` : ""}</div>` +
          (round ? `<span class="prop-bar"><span class="prop-fill" style="width:${pct}%"></span></span>` : "") +
          `</div>`
        );
      })
      .join("");
    // Wire click-to-cast for the next un-voted seat.
    for (const el of Array.from(pool.querySelectorAll("[data-opt]"))) {
      const oid = Number((el as HTMLElement).dataset.opt);
      const cast = () => castNextSeat(oid);
      el.addEventListener("click", cast);
      el.addEventListener("keydown", (e) => { if ((e as KeyboardEvent).key === "Enter" || (e as KeyboardEvent).key === " ") { e.preventDefault(); cast(); } });
    }
  }
  renderQuorum(round);
}

function renderQuorum(round: RoundView | null | undefined) {
  const el = $("quorumLine");
  if (!round) {
    el.className = "quorum-line";
    el.innerHTML = `<span class="q-label">quorum</span><span class="q-text">no vote in progress</span>`;
    return;
  }
  const q = round.quorum;
  const pct = Math.min(100, Math.round((q.ballotsCast / q.threshold) * 100));
  el.className = "quorum-line" + (q.met ? " met" : "");
  el.innerHTML =
    `<span class="q-label">quorum</span>` +
    `<span class="q-text"><b>${q.ballotsCast}</b> / <b>${q.threshold}</b> ballots ${q.met ? "· MET — a close will certify" : `· ${q.threshold - q.ballotsCast} more to certify`}</span>` +
    `<span class="q-bar"><span class="q-fill" style="width:${pct}%"></span></span>`;
}

function renderCert(cert: Cert, applied: boolean) {
  const el = $("certPanel");
  const seatList = cert.electorate.seats.join(", ");
  el.className = "cert-panel show";
  el.innerHTML =
    `<div class="cert-badge">✔ quorum certificate — ${applied ? "applied" : "certified, but the validator refused it"}</div>` +
    `<div class="cert-facts">` +
    `<div><span class="cf-k">winning edit</span><span class="cf-v"><code>${esc(cert.winner?.summary || "—")}</code></span></div>` +
    `<div><span class="cf-k">tally</span><span class="cf-v"><b>${cert.winnerTally}</b> of ${cert.ballotsCast} ballots · quorum ${cert.quorumThreshold} · ${cert.quorumMet ? "MET" : "not met"}</span></div>` +
    `<div><span class="cf-k">light client</span><span class="cf-v">${cert.lightClientAgrees ? "replay of the cast log recomputes the same board ✓" : "✗"}</span></div>` +
    `<div><span class="cf-k">electorate</span><span class="cf-v">${cert.electorate.size} seats [${esc(seatList)}] · commitment <code>${short(cert.electorate.commitmentHex)}</code></span></div>` +
    `</div>` +
    `<p class="cert-honest"><b>The certificate governs which edit won — the validator disposes.</b> ${esc(cert.disposedBy)} <b>Real:</b> ${esc(cert.real)} <b>Gap:</b> ${esc(cert.productionGap)}</p>`;
}

function showBanner(applied: boolean, title: string, body: string) {
  const b = $("banner");
  b.className = "banner show " + (applied ? "applied" : "refused");
  $("bannerTitle").textContent = title;
  ($("bannerBody") as HTMLElement).innerHTML = body;
}
function hideBanner() { $("banner").className = "banner"; }

// ── actions ─────────────────────────────────────────────────────────────────────
async function refresh(): Promise<DraftView> {
  const [d, p] = await Promise.all([jget<DraftView>("/coauthor/draft"), jget<ProposalsView>("/coauthor/proposals")]);
  ($("voteModel") as HTMLElement).innerHTML = `🗳 <code>${esc(d.voteModel)}</code>`;
  renderDraft(d);
  renderPool(p);
  renderSeats();
  return d;
}

async function doPropose(edit?: Record<string, unknown>) {
  const body = edit || collectEdit();
  const r = await jpost<any>("/coauthor/propose", body);
  if (r.ok) {
    $("proposeHint").textContent = `added: ${r.proposal.summary} (pool: ${r.poolSize})`;
    for (const inp of Array.from($("editFields").querySelectorAll("input[data-key]"))) (inp as HTMLInputElement).value = "";
  } else {
    $("proposeHint").textContent = `refused: ${r.reason || r.error || "bad edit"}`;
  }
  const p = await jget<ProposalsView>("/coauthor/proposals");
  renderPool(p);
  return r;
}

async function doOpen() {
  hideBanner();
  $("certPanel").className = "cert-panel";
  seatVote = {};
  const r = await jpost<any>("/coauthor/open");
  const p = await jget<ProposalsView>("/coauthor/proposals");
  renderPool(p);
  renderSeats();
  return r;
}

async function doVote(voter: string, optionId: number) {
  const r = await jpost<any>("/coauthor/vote", { voter, optionId });
  if (r.ok) seatVote[voter] = optionId;
  const t = await jget<RoundView>("/coauthor/tally");
  if (lastProposals) renderPool(lastProposals, t.open ? t : null);
  renderSeats();
  return r;
}

async function castNextSeat(optionId: number) {
  const next = SEATS.find((s) => seatVote[s] === undefined);
  if (!next) return;
  await doVote(next, optionId);
}

async function doClose(): Promise<CloseResp> {
  const r = await jpost<CloseResp>("/coauthor/close");
  if (r.ok && r.disposition) {
    const d = r.disposition;
    if (d.applied) {
      showBanner(true, "✔ edit applied", `The crowd certified <b>${esc(r.winner?.summary || "")}</b> and the validator accepted it — the draft grew and still plays.`);
    } else {
      showBanner(false, "✗ refused by the validator", `The crowd certified <b>${esc(r.winner?.summary || "")}</b>, but the validator refused it (${esc(d.stage || "validate")}): <code>${esc(d.reason || "")}</code>. The draft is unchanged — the crowd proposes, the validator disposes.`);
    }
    if (r.cert) renderCert(r.cert, d.applied);
    if (r.draft) { renderDraft(r.draft); }
  } else if (r.refused === "below-quorum") {
    showBanner(false, "below quorum", `Only ${r.quorum?.ballotsCast ?? "?"} of ${r.quorum?.threshold ?? "?"} ballots — the quorum gate refused the decision-turn. Gather more votes.`);
  } else {
    $("proposeHint").textContent = r.reason || "close refused";
  }
  seatVote = {};
  const p = await jget<ProposalsView>("/coauthor/proposals");
  renderPool(p);
  renderSeats();
  return r;
}

async function doReset(): Promise<DraftView> {
  const r = await jpost<any>("/coauthor/reset");
  hideBanner();
  $("certPanel").className = "cert-panel";
  seatVote = {};
  await refresh();
  return r.draft as DraftView;
}

// ── boot + test hooks ─────────────────────────────────────────────────────────
function wire() {
  ($("editType") as HTMLSelectElement).addEventListener("change", renderFields);
  $("proposeBtn").addEventListener("click", () => doPropose());
  $("openBtn").addEventListener("click", () => doOpen());
  $("closeBtn").addEventListener("click", () => doClose());
  $("resetBtn").addEventListener("click", () => doReset());
  $("autoBtn").addEventListener("click", async () => {
    // Let the remaining seats vote for the current leader (or option 0).
    const t = await jget<RoundView>("/coauthor/tally");
    if (!t.open) return;
    let lead = 0, best = -1;
    for (const row of t.tally) if (row.count > best) { best = row.count; lead = row.optionId; }
    for (const s of SEATS) if (seatVote[s] === undefined) await doVote(s, lead);
  });
  renderFields();

  // window hooks for the headless driver (run-coauthor.mjs).
  window.__coRefresh = () => refresh();
  window.__coState = () => lastDraft;
  window.__coDraft = () => jget<DraftView>("/coauthor/draft");
  window.__coProposals = () => jget<ProposalsView>("/coauthor/proposals");
  window.__coPropose = (edit: Record<string, unknown>) => doPropose(edit);
  window.__coOpen = () => doOpen();
  window.__coVote = (voter: string, optionId: number) => doVote(voter, optionId);
  window.__coTally = () => jget<RoundView>("/coauthor/tally");
  window.__coClose = () => doClose();
  window.__coReset = () => doReset();
  // A DOM probe for the driver: how many room nodes the map currently shows.
  window.__coMapNodeCount = () => $("draftMap").querySelectorAll(".rm-node").length;
}

async function boot() {
  wire();
  try {
    await refresh();
    window.__COAUTHOR_READY = true;
  } catch (e: any) {
    window.__COAUTHOR_ERROR = String(e?.message || e);
    ($("voteModel") as HTMLElement).textContent = `could not reach the co-authoring service: ${window.__COAUTHOR_ERROR}`;
  }
}

boot();
