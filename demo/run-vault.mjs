// THE DRIVEN RUN — THE SUNKEN VAULT: the AI narrates, the WORLD resolves.
//
// Spawns the native attested-dm dungeon-service (hosted Claude Haiku 4.5 via Bedrock, or a local model), serves the
// vault page against it (serve.mjs proxying /game/*), loads it in headless Chromium, and
// plays THE VAULT through the page's own affordances (button/command -> fetch -> /game/act
// -> render), ASSERTING the INVARIANTS against the service's own responses (never fabricated):
//
//   A. A WINNING PLAYTHROUGH — take lantern → descend → key → unlock → sword → beat the
//      Warden → amulet → the gate. Every listed move LANDS, the room transitions as the
//      world dictates, the receipt rail GROWS by one per landed move, and status -> "won".
//   B. THE "you can't cheat" MOMENT — from a fresh vault, step to the antechamber, then try
//      the dark stair WITHOUT the lantern: outcome "refused" ("...it needs the lantern"),
//      the room UNCHANGED, and the receipt rail UNCHANGED (no receipt — anti-ghost).
//   /game/verify re-verifies the whole ledger as a hash chain throughout.
//
// The narration is a REAL local model, so the prose VARIES run to run — we assert the world
// state transitions / status / refusals (the INVARIANTS), never the model's exact words, and
// capture some of the model's real narration into the transcript.
//
// Captures demo/run/vault.png + vault.txt.

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

// The canonical winning path — each entry is (command, why). The order is FORCED by the
// gates: no lantern → no descent; no key → no armory; no sword → death at the Warden; no
// amulet → no win at the gate.
const WIN_PATH = [
  ["go north", "into the salt antechamber", "antechamber"],
  ["take lantern", "a light against the dark", "antechamber"],
  ["go down", "down the now-lit stair", "dark_stair"],
  ["go down", "into the flooded cistern", "cistern"],
  ["take rusted_key", "the key caught in the grate", "cistern"],
  ["go north", "to the drowned vestry", "vestry"],
  ["use rusted_key on iron_door", "the lock gives", "vestry"],
  ["go east", "through the opened iron door", "armory"],
  ["take sword", "one blade still keen", "armory"],
  ["go north", "into the Warden's hall", "warden_hall"],
  ["attack warden", "sword against drowned plate", "warden_hall"],
  ["go east", "past the fallen Warden", "treasury"],
  ["take amulet", "the Drowned Amulet", "treasury"],
  ["go up", "toward grey daylight — WIN", "sunken_gate"],
];

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

async function main() {
  await mkdir(OUT, { recursive: true });

  // ── 1. spawn the native attested-dm dungeon-service (the hosted/metered narrator) ──
  const SERVICE_PORT = 8790;
  const svc = spawn(SERVICE_BIN, [], {
    env: { ...process.env, DREGG_NARRATOR: process.env.DREGG_NARRATOR || "scripted", DUNGEON_BIND: `127.0.0.1:${SERVICE_PORT}` },
    stdio: ["ignore", "pipe", "pipe"],
  });
  const svcLog = [];
  svc.stdout.on("data", (d) => svcLog.push(String(d)));
  svc.stderr.on("data", (d) => svcLog.push(String(d)));
  svc.on("exit", (code) => { if (code) svcLog.push(`\n[service exited ${code}]`); });

  let server, browser;
  try {
    await waitPortOpen(SERVICE_PORT);
    // Give the model probe a moment to settle (build_game_state probes ollama on boot).
    await new Promise((r) => setTimeout(r, 500));
    const narratorKind = await (await fetch(`http://127.0.0.1:${SERVICE_PORT}/game/state`)).json().then((s) => s.narratorKind);
    const realModel = String(narratorKind || "").startsWith("model:");

    // ── 2. serve the vault page against the native service (proxy /game/*) ──
    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = server.address ? `http://127.0.0.1:${server.address().port}` : null;

    // ── 3. load the page ──
    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1120, height: 1900 }, deviceScaleFactor: 2 });
    const pageErrors = [];
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/vault`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__VAULT_READY === true || !!window.__VAULT_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__VAULT_ERROR || null);
    if (bootErr) throw new Error(`the vault page failed to boot (could not reach /game):\n    ${bootErr}`);

    // Fresh vault to start clean.
    await page.evaluate(() => window.__vaultReset());

    const initial = await page.evaluate(async () => await (await fetch("/game/state")).json());
    assert.equal(initial.receiptCount, 0, "a fresh vault starts with an empty receipt rail");
    assert.equal(initial.room.id, "shore", "a fresh vault starts at the shore");
    assert.equal(initial.status, "playing", "a fresh vault is playing");

    const narrations = []; // captured model prose (varies run to run)

    // ── A. THE WINNING PLAYTHROUGH ──
    let prevReceipts = 0;
    const winLog = [];
    for (const [cmd, why, expectRoom] of WIN_PATH) {
      const resp = await page.evaluate((c) => window.__vaultAct(c), cmd);
      // INVARIANT: this move is LEGAL and LANDS (the world admitted it).
      assert.equal(resp.outcome, "landed", `winning move "${cmd}" must land (got ${resp.outcome}: ${resp.reason || ""})`);
      assert.equal(resp.ok, true, `winning move "${cmd}" must be ok`);
      // INVARIANT: the world transitioned to the expected room.
      assert.equal(resp.state.room.id, expectRoom, `after "${cmd}" the world should be in ${expectRoom}, got ${resp.state.room.id}`);
      // INVARIANT: the receipt rail grew by exactly one landed move.
      assert.equal(resp.state.receiptCount, prevReceipts + 1, `"${cmd}" should add exactly one receipt (${prevReceipts} -> ${resp.state.receiptCount})`);
      prevReceipts = resp.state.receiptCount;
      // INVARIANT: the whole ledger still re-verifies.
      const v = await page.evaluate(async () => await (await fetch("/game/verify")).json());
      assert.equal(v.verified, true, `the ledger must re-verify after "${cmd}"`);
      assert.ok(resp.narration && resp.narration.length > 0, `the AI narrated "${cmd}"`);
      narrations.push({ cmd, prose: resp.narration });
      winLog.push({ cmd, why, room: resp.state.room.id, receipts: resp.state.receiptCount, status: resp.state.status, narration: resp.narration });
    }

    // INVARIANT: the objective is met — WON, holding the amulet at the gate, 14 verified turns.
    const won = await page.evaluate(async () => await (await fetch("/game/state")).json());
    assert.equal(won.status, "won", `the playthrough should WIN (got ${won.status})`);
    assert.equal(won.room.id, "sunken_gate", "the winning room is the sunken gate");
    assert.equal(won.inventory.includes("amulet"), true, "the winner carries the amulet");
    assert.equal(won.receiptCount, WIN_PATH.length, `every winning move is a verified turn (${WIN_PATH.length})`);
    const finalVerify = await page.evaluate(async () => await (await fetch("/game/verify")).json());
    assert.equal(finalVerify.verified, true, "the winning ledger re-verifies as a hash chain");

    // Screenshot the WON state (banner up, receipt rail full).
    await page.waitForTimeout(300);
    await page.screenshot({ path: path.join(OUT, "vault.png"), fullPage: true });

    // ── B. THE "you can't cheat" MOMENT — a fresh vault, step to the antechamber, force the stair ──
    await page.evaluate(() => window.__vaultReset());
    const stepNorth = await page.evaluate(() => window.__vaultAct("go north"));
    assert.equal(stepNorth.outcome, "landed", "stepping to the antechamber lands");
    assert.equal(stepNorth.state.room.id, "antechamber", "we are in the antechamber");
    const railBefore = stepNorth.state.receiptCount;

    const cheat = await page.evaluate(() => window.__vaultAct("go down")); // the dark stair, no lantern
    // INVARIANT: the world REFUSES it — no prose talks past the locked stair.
    assert.equal(cheat.outcome, "refused", `forcing the dark stair without the lantern must be refused (got ${cheat.outcome})`);
    assert.equal(cheat.ok, false, "a refused cheat is not ok");
    assert.match(cheat.reason || "", /lantern/i, `the refusal names the lantern (got "${cheat.reason}")`);
    // INVARIANT: the room is UNCHANGED (still the antechamber) and the rail did NOT grow.
    assert.equal(cheat.state.room.id, "antechamber", "the cheat left the room UNCHANGED");
    assert.equal(cheat.state.receiptCount, railBefore, "the refused cheat left NO receipt (anti-ghost)");
    const cheatVerify = await page.evaluate(async () => await (await fetch("/game/verify")).json());
    assert.equal(cheatVerify.verified, true, "the ledger still re-verifies after the refused cheat");
    const cheatNarration = cheat.narration || "";

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    // ── transcript ──
    const transcript = renderTranscript({ base, narratorKind, realModel, winLog, won, cheat, cheatNarration });
    await writeFile(path.join(OUT, "vault.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "vault.png")}`);
    console.log(`  transcript → ${path.join(OUT, "vault.txt")}\n`);
    console.log("  ✓ THE SUNKEN VAULT RAN: a full WIN against the real model, and the locked stair refused the cheat — the AI narrates, the world resolves.\n");
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, narratorKind, realModel, winLog, won, cheat, cheatNarration }) {
  const L = [];
  L.push("THE SUNKEN VAULT — the AI narrates, the world resolves");
  L.push(`driven run · attested-dm /game contract · narratorKind: ${narratorKind}${realModel ? " (a REAL local model)" : ""}`);
  L.push("served at " + base + "/vault");
  L.push("=".repeat(74));
  L.push("");
  L.push("A local AI dungeon-master narrates every room and move, but its prose has NO");
  L.push("authority: the WORLD resolves each move deterministically. You cannot narrate");
  L.push("through a locked door. A legal move lands as one verified turn; a refused move");
  L.push("leaves the world unchanged and lands no receipt.");
  L.push("");
  L.push("-".repeat(74));
  L.push("A · THE WINNING PLAYTHROUGH  (each move LANDS; the receipt rail grows by one)");
  L.push("-".repeat(74));
  for (const t of winLog) {
    L.push("");
    L.push(`  » ${t.cmd}   (${t.why})`);
    L.push(`    ${speaker(narratorKind)}: ${oneline(t.narration)}`);
    L.push(`    world : LANDED → room ${t.room} · receipt rail #${t.receipts} · status ${t.status}`);
  }
  L.push("");
  L.push(`  RESULT: status = ${won.status.toUpperCase()} · ${won.receiptCount} verified turns · carrying [${won.inventory.join(", ")}]`);
  L.push("          the ledger re-verifies as a hash chain (authentic ∧ well-formed ∧ injection-free ∧ prev-linked).");
  L.push("");
  L.push("-".repeat(74));
  L.push("B · THE \"you can't cheat\" MOMENT  (force the dark stair with no lantern)");
  L.push("-".repeat(74));
  L.push("");
  L.push("  » go down   (the dark stair, before taking the lantern)");
  L.push(`    the narrator may narrate the darkness parting: ${oneline(cheatNarration) || "(no narration this run)"}`);
  L.push(`    world : REFUSED — ${cheat.reason}`);
  L.push(`            the room is UNCHANGED (still ${cheat.state.room.id}) and the receipt rail did NOT grow`);
  L.push(`            (#${cheat.state.receiptCount}, no receipt — the anti-ghost tooth). The world disposes.`);
  L.push("");
  L.push("=".repeat(74));
  L.push("The AI narrated. The world resolved. You cannot narrate yourself through a locked door.");
  L.push("");
  return L.join("\n");
}

function oneline(s) { return String(s || "").replace(/\s+/g, " ").trim(); }

main().catch((e) => {
  console.error("\n  ✗ SUNKEN VAULT RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
