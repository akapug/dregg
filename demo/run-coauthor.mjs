// THE DRIVEN RUN — THE COMMONS FORGE: a crowd co-authors ONE shared dungeon draft by VOTE.
//
// Spawns the native attested-dm dungeon-service, serves the co-author page against it (serve.mjs
// proxying /coauthor/* + /game/*), loads it headless, and CO-AUTHORS the shared draft through the
// page's own affordances (propose → open → vote → close → the validator disposes), ASSERTING the
// INVARIANTS against the service's own responses (never fabricated):
//
//   A. THE SEED DRAFT — the shared draft starts minimal (one start room + an obtainable objective)
//      and PLAYS. The room-map shows one node.
//   B. SUB-QUORUM — a proposed AddRoom with only ONE ballot (below the M=3 quorum) is REFUSED at
//      close (below-quorum): the decision-turn is refused by the polis AffineLe gate, the draft does
//      NOT grow, nothing is applied. A duplicate ballot from the same seat is refused (already-voted).
//   C. QUORUM → APPLIED — the same round gathers two more ballots (≥ quorum). Close → the
//      QUORUM-CERTIFIED winning edit is handed to the validator, ACCEPTED, and the draft grows: a new
//      room, a fresh source, appliedCount++, and the map RE-RENDERS (the node count grows). The close
//      carries a QUORUM CERTIFICATE (quorum met, light-client agrees, full electorate).
//   D. THE VALIDATOR DISPOSES (the non-vacuous teeth) — the crowd proposes a BREAKING edit (AddExit
//      from a real room to a NONEXISTENT room). The whole roster votes for it (quorum met, cert
//      issued) — yet the validator (parse_dungeon) REFUSES it and rolls it back: the draft is
//      UNCHANGED (same room count, same source hash), the refusal names the dangling room, and the
//      history records the refusal. The crowd certified a choice; the world disposed.
//   E. THE GROWN DRAFT PLAYS — the crowd votes in a valid AddExit; the draft grows again. Its rendered
//      .dungeon source is loaded into a real GameSession (/game/author), a move into the co-authored
//      room LANDS (/game/act), and /game/verify re-verifies the ledger as a hash chain.
//   The edit HISTORY is append-only + quorum-certified throughout (applied AND refused entries).
//
// The vote runs on the REAL collective-choice engine (WriteOnce ballots + Monotonic tally + the
// polis AffineLe quorum gate) — quorum-certified over DEMO identities (each seat's key is
// blake3(name); a production deployment adds real custody keys + persistence). We assert the draft
// transitions / dispositions / certs / receipt counts (the INVARIANTS), from the service's responses.
//
// Captures demo/run/coauthor.png + coauthor.txt.

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import net from "node:net";
import path from "node:path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");
const OUT = path.join(__dirname, "run");
const SERVICE_BIN = path.join(REPO, "target", "debug", "dungeon-service");

const SEATS = ["Ansel", "Briar", "Cyra", "Doon", "Elowen"];

function waitPortOpen(port, host = "127.0.0.1", timeoutMs = 60000) {
  const start = Date.now();
  return new Promise((resolve, reject) => {
    const tick = () => {
      const s = net.connect(port, host);
      s.once("connect", () => { s.destroy(); resolve(); });
      s.once("error", () => {
        s.destroy();
        if (Date.now() - start > timeoutMs) reject(new Error(`service did not open ${host}:${port} within ${timeoutMs}ms`));
        else setTimeout(tick, 400);
      });
    };
    tick();
  });
}

const optIdForKind = (opts, kind) => {
  const o = opts.find((x) => x.kind === kind);
  assert.ok(o, `an option of kind "${kind}" is on the slate (got: ${opts.map((x) => x.kind).join(", ")})`);
  return o.optionId;
};

async function main() {
  await mkdir(OUT, { recursive: true });

  const SERVICE_PORT = 8793;
  const svc = spawn(SERVICE_BIN, [], {
    env: { ...process.env, DREGG_NARRATOR: process.env.DREGG_NARRATOR || "scripted", DUNGEON_BIND: `127.0.0.1:${SERVICE_PORT}` },
    stdio: ["ignore", "pipe", "pipe"],
  });
  const svcLog = [];
  svc.stdout.on("data", (d) => svcLog.push(String(d)));
  svc.stderr.on("data", (d) => svcLog.push(String(d)));
  svc.on("exit", (code) => { if (code) svcLog.push(`\n[service exited ${code}]`); });

  let server, browser;
  const steps = [];
  try {
    await waitPortOpen(SERVICE_PORT);
    await new Promise((r) => setTimeout(r, 400));

    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = server.address ? `http://127.0.0.1:${server.address().port}` : null;

    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1120, height: 2400 }, deviceScaleFactor: 2 });
    const pageErrors = [];
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/coauthor`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__COAUTHOR_READY === true || !!window.__COAUTHOR_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__COAUTHOR_ERROR || null);
    if (bootErr) throw new Error(`the co-author page failed to boot (could not reach /coauthor):\n    ${bootErr}`);

    // ── A. THE SEED DRAFT — minimal + playable, one node on the map ──
    const seed = await page.evaluate(() => window.__coReset());
    assert.equal(seed.roomCount, 1, "the seed draft has exactly one room");
    assert.equal(seed.plays, true, "the seed draft parses + validates (playable)");
    assert.equal(seed.appliedCount, 0, "no edits applied yet");
    const seedNodes = await page.evaluate(() => window.__coMapNodeCount());
    assert.equal(seedNodes, 1, "the room-map draws one node for the seed");
    const seedHash = seed.sourceHash;
    steps.push({ step: "A seed", roomCount: seed.roomCount, plays: seed.plays, nodes: seedNodes });

    // ── B. SUB-QUORUM — propose AddRoom, one ballot, close → below-quorum, NOT applied ──
    const propHall = await page.evaluate(() => window.__coPropose({ editType: "AddRoom", id: "hall", name: "The Long Hall", description: "A long echoing hall of cold grey stone." }));
    assert.equal(propHall.ok, true, "the AddRoom proposal was accepted into the pool");
    let open = await page.evaluate(() => window.__coOpen());
    assert.equal(open.ok, true, "a round opened over the pending proposals");
    const roundB = open.roundId;
    const hallOpt = optIdForKind(open.options, "AddRoom");

    const v1 = await page.evaluate(([voter, id]) => window.__coVote(voter, id), [SEATS[0], hallOpt]);
    assert.equal(v1.ok, true, `${SEATS[0]} cast a ballot`);
    // A duplicate ballot from the same seat is refused (write-once).
    const dup = await page.evaluate(([voter, id]) => window.__coVote(voter, id), [SEATS[0], hallOpt]);
    assert.equal(dup.ok, false, "a repeat ballot from the same seat is refused");
    assert.equal(dup.refused, "already-voted", `the refusal is tagged already-voted (got ${dup.refused})`);
    // A non-seated voter is refused (eligibility).
    const outsider = await page.evaluate(([voter, id]) => window.__coVote(voter, id), ["Nobody", hallOpt]);
    assert.equal(outsider.refused, "not-seated", `a non-roster voter is refused not-seated (got ${outsider.refused})`);

    let tally = await page.evaluate(() => window.__coTally());
    assert.equal(tally.quorum.met, false, "one ballot is below the M=3 quorum");
    let close = await page.evaluate(() => window.__coClose());
    assert.equal(close.ok, false, "a sub-quorum close is refused (not prematurely resolved)");
    assert.equal(close.refused, "below-quorum", `the refusal is tagged below-quorum (got ${close.refused})`);
    let draft = await page.evaluate(() => window.__coDraft());
    assert.equal(draft.roomCount, 1, "a sub-quorum round did NOT grow the draft");
    assert.equal(draft.appliedCount, 0, "nothing was applied below quorum");
    assert.equal(draft.sourceHash, seedHash, "the draft source is unchanged (the AffineLe gate refused the decision-turn)");
    steps.push({ step: "B sub-quorum", ballots: tally.quorum.ballotsCast, refused: close.refused, roomCount: draft.roomCount });

    // ── C. QUORUM → APPLIED — two more ballots on the SAME round, close → applied, draft grows ──
    await page.evaluate(([voter, id]) => window.__coVote(voter, id), [SEATS[1], hallOpt]);
    await page.evaluate(([voter, id]) => window.__coVote(voter, id), [SEATS[2], hallOpt]);
    tally = await page.evaluate(() => window.__coTally());
    assert.equal(tally.quorum.met, true, "three ballots meet the quorum");
    close = await page.evaluate(() => window.__coClose());
    assert.equal(close.ok, true, "the quorum-met round closed");
    assert.equal(close.quorumCertified, true, "the resolved round is quorum-certified");
    assert.ok(close.cert && close.cert.kind === "quorum-certificate", "the close carries a quorum certificate");
    assert.equal(close.cert.quorumMet, true, "the certificate records quorum met");
    assert.equal(close.cert.lightClientAgrees, true, "an independent light-client replay recomputes the same board");
    assert.equal(close.cert.electorate.size, SEATS.length, `the cert names the full ${SEATS.length}-seat electorate`);
    assert.equal(close.disposition.applied, true, "the validator ACCEPTED the sound edit");
    assert.equal(close.draft.roomCount, 2, "the draft grew by one room (the co-authored hall)");
    assert.equal(close.draft.appliedCount, 1, "one edit is now applied");
    assert.equal(close.draft.plays, true, "the grown draft still plays");
    assert.notEqual(close.draft.sourceHash, seedHash, "the draft source changed");
    // The map RE-RENDERS with the new room.
    const grownNodes = await page.evaluate(() => window.__coMapNodeCount());
    assert.equal(grownNodes, 2, "the room-map re-rendered with two nodes");
    const afterApplyHash = close.draft.sourceHash;
    steps.push({ step: "C applied", winner: close.winner.summary, roomCount: close.draft.roomCount, nodes: grownNodes, cert: true });

    // ── D. THE VALIDATOR DISPOSES — a BREAKING certified edit refused despite the vote ──
    const propDangling = await page.evaluate(() => window.__coPropose({ editType: "AddExit", from: "threshold", dir: "west", to: "nowhere" }));
    assert.equal(propDangling.ok, true, "the (breaking) AddExit proposal was accepted into the pool (it is well-TYPED)");
    open = await page.evaluate(() => window.__coOpen());
    const roundD = open.roundId;
    const danglingOpt = optIdForKind(open.options, "AddExit");
    for (const s of SEATS) {
      await page.evaluate(([voter, id]) => window.__coVote(voter, id), [s, danglingOpt]);
    }
    tally = await page.evaluate(() => window.__coTally());
    assert.equal(tally.quorum.met, true, "the whole roster voted — quorum is met");
    close = await page.evaluate(() => window.__coClose());
    assert.equal(close.ok, true, "the round closed (a decision was certified)");
    // THE CERTIFICATE IS REAL — the crowd DID certify this edit.
    assert.equal(close.quorumCertified, true, "the breaking edit was quorum-CERTIFIED (the vote passed)");
    assert.equal(close.cert.quorumMet, true, "the certificate records quorum met");
    assert.match(close.winner.summary, /AddExit/, "the certified winner is the AddExit edit");
    // THE VALIDATOR DISPOSED — refused + rolled back, DESPITE the passing vote (the non-vacuous teeth).
    assert.equal(close.disposition.applied, false, "the VALIDATOR refused the certified edit (not applied)");
    assert.equal(close.disposition.outcome, "refused", "the disposition is a refusal");
    assert.equal(close.disposition.stage, "validate", "refused by the fail-closed VALIDATOR (parse_dungeon)");
    assert.match(close.disposition.reason || "", /nowhere|unknown room/i, `the refusal names the dangling target (got "${close.disposition.reason}")`);
    // ROLLBACK — the draft is UNCHANGED even though the edit won the vote.
    assert.equal(close.draft.roomCount, 2, "the draft did NOT grow — the breaking edit was rolled back");
    assert.equal(close.draft.appliedCount, 1, "still exactly one applied edit (the refusal did not apply)");
    assert.equal(close.draft.sourceHash, afterApplyHash, "the draft source is UNCHANGED despite the passing vote");
    // The refusal is recorded honestly in the append-only history.
    const histRefused = close.draft.history.find((h) => h.disposition === "refused");
    assert.ok(histRefused, "the append-only history records the refused edit");
    assert.equal(histRefused.refuseStage, "validate", "the history entry marks it a validator refusal");
    steps.push({ step: "D refused", winner: close.winner.summary, quorumMet: close.cert.quorumMet, applied: close.disposition.applied, reason: close.disposition.reason, roomCount: close.draft.roomCount });

    // ── E. THE GROWN DRAFT PLAYS — vote in a VALID exit, then open + move + verify ──
    await page.evaluate(() => window.__coPropose({ editType: "AddExit", from: "threshold", dir: "north", to: "hall" }));
    open = await page.evaluate(() => window.__coOpen());
    const roundE = open.roundId;
    const exitOpt = optIdForKind(open.options, "AddExit");
    for (const s of SEATS.slice(0, 3)) {
      await page.evaluate(([voter, id]) => window.__coVote(voter, id), [s, exitOpt]);
    }
    close = await page.evaluate(() => window.__coClose());
    assert.equal(close.disposition.applied, true, "the valid AddExit was applied");
    assert.equal(close.draft.plays, true, "the twice-grown draft still plays");
    const grownSource = close.draft.source;
    assert.match(grownSource, /exit north -> hall/, "the rendered source carries the co-authored exit");

    // Load the co-authored draft into a REAL GameSession over the same /game path, and PLAY it.
    const authored = await page.evaluate(async (src) => await (await fetch("/game/author", { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ source: src }) })).json(), grownSource);
    assert.equal(authored.ok, true, "the co-authored draft opens a real GameSession (parse + validate)");
    assert.equal(authored.state.room.id, "threshold", "the session starts at the draft's start room");
    const moved = await page.evaluate(async () => await (await fetch("/game/act", { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ command: "go north" }) })).json());
    assert.equal(moved.outcome, "landed", `a move into the co-authored room LANDS (got ${moved.outcome})`);
    assert.equal(moved.state.room.id, "hall", "the move advanced into the crowd-authored hall");
    assert.equal(moved.state.receiptCount, 1, "the landed move grew the receipt rail to one verified turn");
    const gverify = await page.evaluate(async () => await (await fetch("/game/verify")).json());
    assert.equal(gverify.verified, true, "the co-authored dungeon's ledger re-verifies as a hash chain");
    steps.push({ step: "E plays", exit: "threshold -north-> hall", moveOutcome: moved.outcome, room: moved.state.room.id, verified: gverify.verified });

    // Screenshot the co-author page.
    await page.waitForTimeout(300);
    await page.screenshot({ path: path.join(OUT, "coauthor.png"), fullPage: true });

    const finalDraft = await page.evaluate(() => window.__coDraft());
    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    const transcript = renderTranscript({ base, steps, finalDraft });
    await writeFile(path.join(OUT, "coauthor.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "coauthor.png")}`);
    console.log(`  transcript → ${path.join(OUT, "coauthor.txt")}\n`);
    console.log("  ✓ THE COMMONS FORGE RAN: a crowd co-authored one shared draft by QUORUM-CERTIFIED vote — a sub-quorum edit refused by the gate, a certified edit APPLIED (the draft grew + the map re-rendered), a certified BREAKING edit REFUSED and rolled back by the validator despite the vote, and the grown draft PLAYS. The crowd proposes; the validator disposes.\n");
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, steps, finalDraft }) {
  const L = [];
  L.push("THE COMMONS FORGE — a crowd co-authors one shared dungeon draft by VOTE");
  L.push(`driven run · attested-dm /coauthor contract · quorum-certified collective co-authoring`);
  L.push("served at " + base + "/coauthor");
  L.push("=".repeat(78));
  L.push("");
  L.push("The crowd PROPOSES a bounded, typed edit; the seated co-authors QUORUM-VOTE on the real");
  L.push("collective-choice engine (WriteOnce ballots + Monotonic tally + the polis AffineLe quorum");
  L.push("gate, M=3 of 5); and the VALIDATOR (parse_dungeon) DISPOSES the certified edit — a sound");
  L.push("edit grows the draft, a breaking one is refused and rolled back DESPITE the passing vote.");
  L.push("");
  for (const s of steps) {
    L.push("-".repeat(78));
    if (s.step === "A seed") {
      L.push(`[A] SEED DRAFT — ${s.roomCount} room · plays: ${s.plays} · map nodes: ${s.nodes}`);
    } else if (s.step === "B sub-quorum") {
      L.push(`[B] SUB-QUORUM — ${s.ballots} ballot < M=3 → close REFUSED (${s.refused}); the draft did not grow (still ${s.roomCount} room). A duplicate ballot + a non-seated voter were refused too.`);
    } else if (s.step === "C applied") {
      L.push(`[C] QUORUM → APPLIED — quorum met, certified winner: ${s.winner}`);
      L.push(`    the validator ACCEPTED it → the draft grew to ${s.roomCount} rooms; the map re-rendered (${s.nodes} nodes). A quorum certificate was emitted.`);
    } else if (s.step === "D refused") {
      L.push(`[D] THE VALIDATOR DISPOSES — certified winner: ${s.winner} · quorum met: ${s.quorumMet}`);
      L.push(`    yet the validator REFUSED it: ${s.reason}`);
      L.push(`    the draft is UNCHANGED (still ${s.roomCount} rooms) — the crowd certified a choice; the world disposed. (non-vacuous)`);
    } else if (s.step === "E plays") {
      L.push(`[E] THE GROWN DRAFT PLAYS — voted in ${s.exit}; loaded into a real GameSession → a move ${s.moveOutcome} into ${s.room}; /game/verify = ${s.verified}`);
    }
  }
  L.push("=".repeat(78));
  L.push(`RESULT: the co-authored draft has ${finalDraft.roomCount} rooms · ${finalDraft.appliedCount} certified edits applied · plays: ${finalDraft.plays}`);
  L.push(`append-only history: ${finalDraft.history.length} disposed rounds (applied + validator-refused), each with its quorum certificate.`);
  L.push("The crowd proposed every edit. The quorum certified the winner. The validator disposed —");
  L.push("a voted-for broken world was refused and rolled back. The draft grew, and stays playable.");
  L.push("");
  return L.join("\n");
}

main().catch((e) => {
  console.error("\n  ✗ COMMONS FORGE RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
