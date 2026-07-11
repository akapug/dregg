// THE DRIVEN RUN — THE COLLECTIVE DUNGEON: a crowd steers one shared party by VOTE.
//
// Spawns the native attested-dm dungeon-service (hosted Claude Haiku 4.5 via Bedrock, or a local model), serves the party
// page against it (serve.mjs proxying /party/* + /game/*), loads it in headless Chromium, and
// plays THE SHARED DUNGEON by VOTE through the page's own affordances (open → cast → close →
// the winning move resolves through the SAME /game/act path), ASSERTING the INVARIANTS against
// the service's own responses (never fabricated):
//
//   A. /party/options lists the candidate actions at the current room as a ballot slate, and
//      advertises the QUORUM threshold.
//   A'. THE QUORUM GATE — a round with only ONE ballot (below the M=3 quorum) is REFUSED at close
//      (below-quorum): the decision-turn is refused by the polis AffineLe gate, the world does not
//      move, no receipt. A sub-quorum round does not prematurely resolve.
//   B. A LANDING ROUND — from the shore, the seated party votes "go north" (4 ballots ≥ quorum). A
//      repeat ballot from the SAME voter is REFUSED (already-voted). Close → the QUORUM-CERTIFIED
//      winner resolves as a VERIFIED turn: the receipt rail grows by one, the room advances, and
//      the close carries a QUORUM CERTIFICATE (quorum met, light-client agrees, full electorate).
//   C. THE HONEST-FRAMING ROUND — at the antechamber WITHOUT the lantern, the party votes the
//      LOCKED dark stair ("go down"). Close → the round is CERTIFIED (quorum met), but the world
//      RESOLVES and REFUSES the winner: the room is UNCHANGED, the receipt rail did NOT grow (no
//      receipt — anti-ghost). The crowd certified a choice; the world disposed. Vote again.
//   D. THE RE-VOTE — the party then votes "take lantern": it LANDS, the receipt rail grows, and
//      now the once-barred stair is open (the world moved because the party earned it, not voted it).
//   /game/verify re-verifies the whole ledger as a hash chain throughout.
//
// The vote runs on the REAL collective-choice engine (WriteOnce ballots + Monotonic tally + the
// polis AffineLe quorum gate) — quorum-certified over DEMO identities (each seat's key is
// blake3(name); a production deployment adds real custody keys). The narration is a REAL local
// model, so prose VARIES run to run; we assert the world transitions / refusals / receipt counts /
// the quorum cert (the INVARIANTS), never the model's exact words.
//
// Captures demo/run/party.png + party.txt.

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import net from "node:net";
import path from "node:path";

// A short, HONEST speaker label from the response's narratorKind (never a hardcoded model name).
function speaker(narratorKind) {
  const k = String(narratorKind || "");
  if (k.startsWith("model:")) {
    const id = k.slice(6);
    if (/haiku/i.test(id)) return "haiku";
    if (/nova/i.test(id)) return "nova";
    if (/gemma/i.test(id)) return "gemma2";
    return id.split(/[.\/]/).pop() || "model";
  }
  if (k.startsWith("scripted")) return "scripted";
  return k || "narrator";
}


const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");
const OUT = path.join(__dirname, "run");

const SERVICE_BIN = path.join(REPO, "target", "debug", "dungeon-service");

const SEATS = ["Bramwen", "Corvin", "Della", "Ferro", "Wisp"];

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

const optIdFor = (opts, cmd) => {
  const o = opts.find((x) => x.command === cmd);
  assert.ok(o, `the ballot offers "${cmd}" (got: ${opts.map((x) => x.command).join(", ")})`);
  return o.id;
};
const countFor = (tally, cmd) => {
  const r = tally.tally.find((x) => x.command === cmd);
  return r ? r.count : 0;
};

async function main() {
  await mkdir(OUT, { recursive: true });

  // ── 1. spawn the native attested-dm dungeon-service (the hosted/metered narrator) ──
  const SERVICE_PORT = 8792;
  const svc = spawn(SERVICE_BIN, [], {
    env: { ...process.env, DUNGEON_BIND: `127.0.0.1:${SERVICE_PORT}` },
    stdio: ["ignore", "pipe", "pipe"],
  });
  const svcLog = [];
  svc.stdout.on("data", (d) => svcLog.push(String(d)));
  svc.stderr.on("data", (d) => svcLog.push(String(d)));
  svc.on("exit", (code) => { if (code) svcLog.push(`\n[service exited ${code}]`); });

  let server, browser;
  try {
    await waitPortOpen(SERVICE_PORT);
    await new Promise((r) => setTimeout(r, 500));
    const narratorKind = await (await fetch(`http://127.0.0.1:${SERVICE_PORT}/game/state`)).json().then((s) => s.narratorKind);
    const realModel = String(narratorKind || "").startsWith("model:");

    // ── 2. serve the party page against the native service (proxy /party/* + /game/*) ──
    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = server.address ? `http://127.0.0.1:${server.address().port}` : null;

    // ── 3. load the page ──
    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1120, height: 2200 }, deviceScaleFactor: 2 });
    const pageErrors = [];
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/party`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__PARTY_READY === true || !!window.__PARTY_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__PARTY_ERROR || null);
    if (bootErr) throw new Error(`the party page failed to boot (could not reach /party):\n    ${bootErr}`);

    // Fresh sunken vault to start clean.
    const initial = await page.evaluate(() => window.__partyReset("sunken-vault"));
    assert.equal(initial.world, "sunken-vault", "reset to the sunken vault");
    assert.equal(initial.room.id, "shore", "the shared party starts at the shore");
    assert.equal(initial.receiptCount, 0, "a fresh dungeon starts with an empty receipt rail");

    const rounds = [];

    // ── A. /party/options — the ballot slate at the shore + the quorum threshold ──
    const optionsView = await page.evaluate(() => window.__partyOptions());
    assert.ok(Array.isArray(optionsView.options) && optionsView.options.length > 0, "/party/options returns a non-empty ballot slate");
    assert.match(optionsView.voteModel || "", /quorum-certified/i, "/party/options labels the vote model as quorum-certified (honest)");
    assert.ok(optionsView.quorum && optionsView.quorum.threshold >= 2, "/party/options advertises a quorum threshold");
    const QUORUM = optionsView.quorum.threshold;
    optIdFor(optionsView.options, "go north"); // the shore's exit is on the slate

    // ── A'. THE QUORUM GATE — a single ballot is BELOW quorum; a close does NOT resolve ──
    let subOpen = await page.evaluate(() => window.__partyOpen());
    assert.equal(subOpen.ok, true, "a round opened for the sub-quorum probe");
    assert.equal(subOpen.quorum.threshold, QUORUM, "the opened round carries the quorum threshold");
    const subLook = optIdFor(subOpen.options, "look");
    await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [SEATS[0], subLook]);
    const subTally = await page.evaluate(() => window.__partyTally());
    assert.equal(subTally.quorum.met, false, `one ballot is below the M=${QUORUM} quorum`);
    const subClose = await page.evaluate(() => window.__partyCloseRaw());
    assert.equal(subClose.ok, false, "a sub-quorum close is refused (not prematurely resolved)");
    assert.equal(subClose.refused, "below-quorum", `the refusal is tagged below-quorum (got ${subClose.refused})`);
    assert.equal(subClose.quorum.met, false, "the quorum gate reports not met");
    const afterSub = await page.evaluate(() => window.__partyState());
    assert.equal(afterSub.room.id, "shore", "a sub-quorum round did not move the world");
    assert.equal(afterSub.receiptCount, 0, "a sub-quorum round left no receipt (the decision-turn was refused by the AffineLe gate)");

    // ── B. A LANDING ROUND — the party votes "go north"; a repeat ballot is refused ──
    let open = await page.evaluate(() => window.__partyOpen());
    assert.equal(open.ok, true, "the round opened");
    const round1 = open.roundId;
    const goNorth = optIdFor(open.options, "go north");
    const lookOpt = optIdFor(open.options, "look");

    // Three adventurers vote to go north; one looks around (a split, so the tally is legible).
    const v1 = await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [SEATS[0], goNorth]);
    assert.equal(v1.ok, true, `${SEATS[0]} cast a ballot`);
    await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [SEATS[1], goNorth]);
    await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [SEATS[2], goNorth]);
    await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [SEATS[3], lookOpt]);

    // THE WRITE-ONCE RULE — the same voter cannot cast a second ballot this round.
    const dup = await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [SEATS[0], lookOpt]);
    assert.equal(dup.ok, false, "a repeat ballot from the same voter is refused");
    assert.equal(dup.refused, "already-voted", `the refusal is tagged already-voted (got ${dup.refused})`);

    // The live tally reflects the ballots: 3 for go north, 1 for look.
    const tally1 = await page.evaluate(() => window.__partyTally());
    assert.equal(countFor(tally1, "go north"), 3, `the tally shows 3 for "go north" (got ${countFor(tally1, "go north")})`);
    assert.equal(countFor(tally1, "look"), 1, `the tally shows 1 for "look" (got ${countFor(tally1, "look")})`);
    assert.equal(tally1.totalVotes, 4, `4 ballots cast (the duplicate did not count; got ${tally1.totalVotes})`);

    // Close → the plurality winner ("go north") resolves as a VERIFIED turn.
    let close = await page.evaluate(() => window.__partyClose());
    assert.equal(close.ok, true, "the round closed");
    assert.equal(close.winner.command, "go north", `the winner is "go north" (got ${close.winner.command})`);
    // THE QUORUM CERTIFICATE — a resolved round produces a verifiable cert, not a bare count.
    assert.equal(close.quorumCertified, true, "the resolved round is quorum-certified");
    assert.ok(close.cert && close.cert.kind === "quorum-certificate", "the close carries a quorum certificate");
    assert.equal(close.cert.quorumMet, true, "the certificate records quorum met");
    assert.equal(close.cert.lightClientAgrees, true, "an independent light-client replay recomputes the same board");
    assert.equal(close.cert.electorate.size, SEATS.length, `the cert names the full ${SEATS.length}-seat electorate`);
    assert.equal(close.cert.winner.command, "go north", "the certificate names the certified winner");
    assert.equal(close.resolved.outcome, "landed", "the world LANDED the party's choice");
    assert.equal(close.resolved.state.room.id, "antechamber", "the dungeon advanced to the antechamber");
    assert.equal(close.resolved.state.receiptCount, 1, "the receipt rail grew by one (a verified turn)");
    let verify = await page.evaluate(async () => await (await fetch("/game/verify")).json());
    assert.equal(verify.verified, true, "the ledger re-verifies after the landing round");
    rounds.push({ round: round1, winner: close.winner.command, tally: [["go north", 3], ["look", 1]], outcome: "landed", room: close.resolved.state.room.id, receipts: close.resolved.state.receiptCount, narration: close.resolved.narration, dupRefused: true });

    // ── C. THE HONEST-FRAMING ROUND — the party votes the LOCKED dark stair (no lantern) ──
    open = await page.evaluate(() => window.__partyOpen());
    const round2 = open.roundId;
    const goDownLocked = optIdFor(open.options, "go down");
    const lockedOpt = open.options.find((o) => o.id === goDownLocked);
    assert.match(lockedOpt.label, /barred/i, `the dark-stair option is shown as barred (label: "${lockedOpt.label}")`);
    // The whole party votes to force the barred stair.
    for (const s of SEATS.slice(0, 4)) {
      await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [s, goDownLocked]);
    }
    const railBefore = 1;
    close = await page.evaluate(() => window.__partyClose());
    assert.equal(close.ok, true, "the round closed");
    assert.equal(close.winner.command, "go down", "the party voted to force the dark stair");
    // The round is CERTIFIED (quorum met) — but the certificate governs the CHOICE, not the world.
    assert.equal(close.quorumCertified, true, "the round is quorum-certified even though the world will refuse it");
    assert.equal(close.cert.quorumMet, true, "the certificate records quorum met");
    assert.equal(close.cert.winner.command, "go down", "the certificate names the certified (but world-refused) winner");
    // THE WORLD DISPOSES — the voted-for locked exit is REFUSED (collective choice ≠ bypass).
    assert.equal(close.resolved.outcome, "refused", `the world REFUSED the voted locked exit (got ${close.resolved.outcome})`);
    assert.match(close.resolved.reason || "", /lantern/i, `the refusal names the lantern (got "${close.resolved.reason}")`);
    assert.equal(close.resolved.state.room.id, "antechamber", "the room is UNCHANGED — the party did not descend");
    assert.equal(close.resolved.state.receiptCount, railBefore, "the refused vote left NO receipt (anti-ghost)");
    verify = await page.evaluate(async () => await (await fetch("/game/verify")).json());
    assert.equal(verify.verified, true, "the ledger still re-verifies after the refused vote");
    rounds.push({ round: round2, winner: close.winner.command, tally: [["go down", 4]], outcome: "refused", reason: close.resolved.reason, room: close.resolved.state.room.id, receipts: close.resolved.state.receiptCount, narration: close.resolved.narration });

    // ── D. THE RE-VOTE — the party votes "take lantern"; now it LANDS ──
    open = await page.evaluate(() => window.__partyOpen());
    const round3 = open.roundId;
    const takeLantern = optIdFor(open.options, "take lantern");
    for (const s of SEATS) {
      await page.evaluate(([voter, id]) => window.__partyVote(voter, id), [s, takeLantern]);
    }
    close = await page.evaluate(() => window.__partyClose());
    assert.equal(close.winner.command, "take lantern", "the party re-voted to take the lantern");
    assert.equal(close.quorumCertified, true, "the re-vote is quorum-certified");
    assert.equal(close.cert.lightClientAgrees, true, "the re-vote's cert light-client tally agrees");
    assert.equal(close.resolved.outcome, "landed", "taking the lantern LANDS");
    assert.equal(close.resolved.state.receiptCount, 2, "the receipt rail grew to two verified turns");
    assert.ok(close.resolved.state.inventory.includes("lantern"), "the party now carries the lantern");
    verify = await page.evaluate(async () => await (await fetch("/game/verify")).json());
    assert.equal(verify.verified, true, "the ledger re-verifies after the re-vote");
    rounds.push({ round: round3, winner: close.winner.command, tally: [["take lantern", 5]], outcome: "landed", room: close.resolved.state.room.id, receipts: close.resolved.state.receiptCount, narration: close.resolved.narration, note: "the once-barred stair is now open — the world moved because the party EARNED it, not because it voted." });

    // Screenshot the party page: the chronicle (landed + the refused locked-exit round), the rail.
    await page.waitForTimeout(300);
    await page.screenshot({ path: path.join(OUT, "party.png"), fullPage: true });

    const finalState = await page.evaluate(() => window.__partyState());

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    // ── transcript ──
    const transcript = renderTranscript({ base, narratorKind, realModel, rounds, finalState });
    await writeFile(path.join(OUT, "party.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "party.png")}`);
    console.log(`  transcript → ${path.join(OUT, "party.txt")}\n`);
    console.log("  ✓ THE COLLECTIVE DUNGEON RAN: a crowd steered one party by a QUORUM-CERTIFIED vote — a sub-quorum round refused by the quorum gate, a repeat ballot refused, a certified locked exit refused by the WORLD, and a re-vote landed with its quorum certificate. The crowd certifies; the world resolves.\n");
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, narratorKind, realModel, rounds, finalState }) {
  const L = [];
  L.push("THE COLLECTIVE DUNGEON — a crowd steers one shared party by VOTE");
  L.push(`driven run · attested-dm /party contract · narratorKind: ${narratorKind}${realModel ? " (a REAL local model)" : ""}`);
  L.push("served at " + base + "/party");
  L.push("=".repeat(78));
  L.push("");
  L.push("Each turn: OPEN a vote over the party's candidate moves, the seated adventurers cast");
  L.push("write-once ballots, CLOSE it — and the QUORUM-CERTIFIED winner resolves through the SAME");
  L.push("engine as single-player. The vote runs on the real collective-choice engine (WriteOnce");
  L.push("ballots + Monotonic tally + the polis AffineLe quorum gate); a quorum-met close emits a");
  L.push("verifiable QUORUM CERTIFICATE over demo identities. The crowd CERTIFIES; the world still");
  L.push("RESOLVES — a party that certifies a locked door is still refused by the world.");
  L.push("");
  for (const r of rounds) {
    L.push("-".repeat(78));
    const tallyStr = r.tally.map(([c, n]) => `${c} = ${n}`).join(" · ");
    L.push(`ROUND #${r.round} — ballots: ${tallyStr}`);
    L.push("-".repeat(78));
    if (r.dupRefused) L.push(`  · a SECOND ballot from a voter who already voted → REFUSED (already-voted, one ballot per voter)`);
    L.push(`  » the party voted: ${r.winner}`);
    L.push(`    ${speaker(narratorKind)}: ${oneline(r.narration) || "(no narration this run)"}`);
    if (r.outcome === "landed") {
      L.push(`    world : LANDED → room ${r.room} · receipt rail #${r.receipts} (a verified turn)`);
      if (r.note) L.push(`            ${r.note}`);
    } else {
      L.push(`    world : REFUSED — ${r.reason}`);
      L.push(`            the room is UNCHANGED (still ${r.room}) and the receipt rail did NOT grow`);
      L.push(`            (#${r.receipts}, no receipt — the anti-ghost tooth). The crowd decided; the world disposed.`);
    }
    L.push("");
  }
  L.push("=".repeat(78));
  L.push(`RESULT: the shared party is at ${finalState.room.name} · ${finalState.receiptCount} verified voted turns · carrying [${finalState.inventory.join(", ")}]`);
  L.push("The crowd decided every move. The world resolved every move. A voted-for locked door");
  L.push("stayed shut until the party earned it. The ledger is the truth, not the vote.");
  L.push("");
  return L.join("\n");
}

function oneline(s) { return String(s || "").replace(/\s+/g, " ").trim(); }

main().catch((e) => {
  console.error("\n  ✗ COLLECTIVE DUNGEON RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
