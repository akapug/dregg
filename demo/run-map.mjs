// THE DRIVEN RUN — THE ROOM MAP + LIVE VALIDATION.
//
// Spawns the native attested-dm dungeon-service, serves the vault + forge pages against it
// (serve.mjs proxying /game/*), loads them in headless Chromium, and drives the two new surfaces
// through the SERVICE'S OWN responses (never fabricated):
//
//   1. GET /game/map — the current world's room graph [{id,name,exits:[{to,locked}]}]: a non-empty
//      array of rooms, each exit carrying a destination + a boolean lock, at least one BARRED edge
//      in the sunken vault (a gate not yet satisfied).
//   2. POST /game/validate — pure lint, NO session opened:
//        · a CLEAN .dungeon      → {stage:"clean"}
//        · a SEMANTICALLY broken  → {stage:"validate", issues:[…] with lines}
//        · a SYNTAX broken        → {stage:"parse", line}
//      and it does NOT disturb the live world (state before == state after).
//   3. /vault — the SVG room map renders (room nodes present), the current room is highlighted,
//      and moving marks a room visited (the visited set grows).
//   4. /forge — authoring a world draws its map (room nodes present); typing a SYNTAX-broken source
//      surfaces a LIVE error marker in the gutter (.glm-err) + a lint verdict, all BEFORE ▶ Play.
//
// Captures demo/run/map.png (the vault map on screen, a couple rooms in) + map.txt.

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

// A CLEAN minimal world (parses + validates with no errors) → /game/validate {stage:"clean"}.
const CLEAN = `name: The Test Warren
start: den
objective: reach exit_room holding key
room den "The Den"
  A snug earthen den.
  items: key
  exit north -> exit_room
room exit_room "The Way Out"
  Daylight ahead.
  exit south -> den
`;

// A SYNTAX-broken world: an exit with no destination after \`->\` → /game/validate {stage:"parse", line}.
const SYNTAX_BROKEN = `name: Syntax Trap
start: room_a
objective: reach room_b holding key
room room_a "Room A"
  A bare stone room.
  exit north ->
room room_b "Room B"
  items: key
  exit south -> room_a
`;

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

  const SERVICE_PORT = 8793;
  const svc = spawn(SERVICE_BIN, [], {
    env: { ...process.env, DUNGEON_BIND: `127.0.0.1:${SERVICE_PORT}` },
    stdio: ["ignore", "pipe", "pipe"],
  });
  const svcLog = [];
  svc.stdout.on("data", (d) => svcLog.push(String(d)));
  svc.stderr.on("data", (d) => svcLog.push(String(d)));
  svc.on("exit", (code) => { if (code) svcLog.push(`\n[service exited ${code}]`); });

  let server, browser;
  const svcUrl = `http://127.0.0.1:${SERVICE_PORT}`;
  const T = [];
  try {
    await waitPortOpen(SERVICE_PORT);
    await new Promise((r) => setTimeout(r, 500));

    const narratorKind = await (await fetch(`${svcUrl}/game/state`)).json().then((s) => s.narratorKind);

    // ── 1. GET /game/map on a freshly-reset sunken vault ──────────────────────────────
    await fetch(`${svcUrl}/game/reset`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ world: "sunken-vault" }) });
    const mapRooms = await (await fetch(`${svcUrl}/game/map`)).json();
    assert.ok(Array.isArray(mapRooms) && mapRooms.length >= 4, `/game/map returns a room graph (got ${Array.isArray(mapRooms) ? mapRooms.length : "non-array"})`);
    for (const r of mapRooms) {
      assert.ok(typeof r.id === "string" && r.id.length > 0, "each room has an id");
      assert.ok(typeof r.name === "string" && r.name.length > 0, "each room has a name");
      assert.ok(Array.isArray(r.exits), "each room carries an exits array");
      for (const e of r.exits) {
        assert.ok(typeof e.to === "string", "each exit names a destination room id");
        assert.equal(typeof e.locked, "boolean", "each exit carries a boolean `locked`");
      }
    }
    const lockedEdges = mapRooms.flatMap((r) => r.exits.filter((e) => e.locked));
    assert.ok(lockedEdges.length >= 1, `the sunken vault map has at least one BARRED edge (got ${lockedEdges.length})`);
    assert.ok(lockedEdges.every((e) => typeof e.gateReason === "string" && e.gateReason.length > 0), "a barred edge carries a legible gate reason");
    T.push(`MAP       /game/map → ${mapRooms.length} rooms, ${mapRooms.reduce((n, r) => n + r.exits.length, 0)} exits, ${lockedEdges.length} barred (e.g. "${lockedEdges[0].gateReason}")`);

    // ── 2. POST /game/validate — clean / validate / parse, WITHOUT disturbing the live world ──
    const stateBefore = await (await fetch(`${svcUrl}/game/state`)).json();

    const clean = await (await fetch(`${svcUrl}/game/validate`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ source: CLEAN }) })).json();
    assert.equal(clean.ok, true, "a clean world lints ok");
    assert.equal(clean.stage, "clean", `a clean world → stage "clean" (got ${clean.stage})`);
    assert.equal((clean.issues || []).filter((i) => i.severity === "error").length, 0, "a clean world has no errors");

    // (the semantic-broken world lints after the page server is up, so we can fetch broken.dungeon)

    const syntax = await (await fetch(`${svcUrl}/game/validate`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ source: SYNTAX_BROKEN }) })).json();
    assert.equal(syntax.ok, false, "a syntax-broken world does NOT lint ok");
    assert.equal(syntax.stage, "parse", `a syntax-broken world → stage "parse" (got ${syntax.stage})`);
    assert.ok(Number.isInteger(syntax.line) && syntax.line > 0, `the parse error is line-pinned (got line ${syntax.line})`);

    const stateAfter = await (await fetch(`${svcUrl}/game/state`)).json();
    assert.equal(stateAfter.room.id, stateBefore.room.id, "/game/validate did NOT change the live world's room (pure lint)");
    assert.equal(stateAfter.receiptCount, stateBefore.receiptCount, "/game/validate did NOT touch the receipt ledger");
    T.push(`VALIDATE  clean → stage="clean" · syntax-broken → stage="parse" line ${syntax.line} · live world UNTOUCHED`);

    // ── serve the pages against the native service ──
    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = `http://127.0.0.1:${server.address().port}`;

    // the SEMANTIC-broken committed world (broken.dungeon) → stage "validate" with issues+lines
    const brokenDungeon = await (await fetch(`${base}/dungeons/broken.dungeon`)).text();
    const validate = await (await fetch(`${svcUrl}/game/validate`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ source: brokenDungeon }) })).json();
    assert.equal(validate.ok, false, "the semantic-broken world does NOT lint ok");
    assert.equal(validate.stage, "validate", `the semantic-broken world → stage "validate" (got ${validate.stage})`);
    const vErrs = (validate.issues || []).filter((i) => i.severity === "error");
    assert.ok(vErrs.length >= 2, `every validation error is reported (got ${vErrs.length})`);
    assert.ok(vErrs.some((i) => i.line > 0), "at least one validation issue is line-pinned");
    T.push(`VALIDATE  broken.dungeon → stage="validate" · ${vErrs.length} errors (line-pinned) · no session opened`);

    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1200, height: 2200 }, deviceScaleFactor: 2 });
    const pageErrors = [];
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    // ── 3. /vault — the SVG room map renders; moving marks a room visited ──────────────
    await page.goto(`${base}/vault`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__VAULT_READY === true || !!window.__VAULT_ERROR, null, { timeout: 30000 });
    const vErr = await page.evaluate(() => window.__VAULT_ERROR || null);
    if (vErr) throw new Error(`the vault page failed to boot: ${vErr}`);
    await page.evaluate(() => window.__vaultReset("sunken-vault"));
    await page.waitForFunction(() => document.querySelectorAll("#roomMap .rm-node").length > 0, null, { timeout: 15000 });

    const vaultMap = await page.evaluate(() => ({
      nodes: document.querySelectorAll("#roomMap svg .rm-node").length,
      edges: document.querySelectorAll("#roomMap svg .rm-edge").length,
      lockedEdges: document.querySelectorAll("#roomMap svg .rm-edge.locked").length,
      current: document.querySelectorAll("#roomMap svg .rm-node.current").length,
      svg: !!document.querySelector("#roomMap svg.roommap-svg"),
    }));
    assert.equal(vaultMap.svg, true, "the vault renders an inline SVG room map");
    assert.ok(vaultMap.nodes >= 4, `the vault map has room nodes (got ${vaultMap.nodes})`);
    assert.equal(vaultMap.current, 1, "exactly one room is highlighted as current");
    assert.ok(vaultMap.lockedEdges >= 1, `a barred exit is drawn distinctly on the map (got ${vaultMap.lockedEdges})`);

    const visitedBefore = await page.evaluate(() => window.__vaultVisited().length);
    // walk into the vault so the visited set grows (shore → antechamber, take the lantern, then the
    // now-lit dark stair down): the map's barred stair edge opens as the gate is satisfied.
    await page.evaluate(() => window.__vaultAct("go north"));
    await page.evaluate(() => window.__vaultAct("take lantern"));
    await page.evaluate(() => window.__vaultAct("go down"));
    const visitedAfter = await page.evaluate(() => window.__vaultVisited().length);
    assert.ok(visitedAfter > visitedBefore, `moving marks a new room visited (${visitedBefore} → ${visitedAfter})`);
    const visitedNodes = await page.evaluate(() => document.querySelectorAll("#roomMap svg .rm-node.visited").length);
    assert.ok(visitedNodes >= 1, `a visited room reads distinctly on the map (got ${visitedNodes})`);
    T.push(`VAULT     SVG map: ${vaultMap.nodes} nodes, ${vaultMap.edges} edges (${vaultMap.lockedEdges} barred) · current highlighted · visited ${visitedBefore}→${visitedAfter}`);

    // Capture the map on screen (the vault map region, a couple rooms in).
    await page.waitForTimeout(250);
    const mapEl = await page.$("#roomMap");
    if (mapEl) await mapEl.screenshot({ path: path.join(OUT, "map.png") });
    else await page.screenshot({ path: path.join(OUT, "map.png"), fullPage: true });

    // ── 4. /forge — authoring draws the map; typing broken source surfaces a LIVE marker ──
    await page.goto(`${base}/forge`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__FORGE_READY === true, null, { timeout: 45000 });
    const fBoot = await page.evaluate(() => window.__FORGE_ERROR || null);
    if (fBoot) throw new Error(`the forge page failed to boot: ${fBoot}`);

    // the starter authored on boot → its map is drawn
    await page.evaluate(() => window.__forgePlay());
    await page.waitForFunction(() => document.querySelectorAll("#roomMap .rm-node").length > 0, null, { timeout: 15000 });
    const forgeMap = await page.evaluate(() => ({
      nodes: document.querySelectorAll("#roomMap svg .rm-node").length,
      svg: !!document.querySelector("#roomMap svg.roommap-svg"),
    }));
    assert.equal(forgeMap.svg, true, "the forge renders an inline SVG map of the authored world");
    assert.ok(forgeMap.nodes >= 4, `the authored world's map has room nodes (got ${forgeMap.nodes})`);

    // typing a SYNTAX-broken source → a live gutter marker + a lint verdict (before ▶ Play)
    await page.evaluate((src) => window.__forgeLintNow(src), SYNTAX_BROKEN);
    const lintState = await page.evaluate(() => window.__forgeLintState());
    assert.ok(lintState && lintState.stage === "parse", `live-lint flags the syntax error (stage ${lintState && lintState.stage})`);
    assert.ok(lintState.errors >= 1, "live-lint reports at least one error");
    const gutterErr = await page.evaluate(() => document.querySelectorAll(".gutter span.glm-err").length);
    assert.ok(gutterErr >= 1, `a live error marker appears in the gutter (got ${gutterErr})`);
    const lintPanel = await page.evaluate(() => (document.getElementById("lint")?.textContent || "").trim());
    assert.ok(/error/i.test(lintPanel), "the live-lint panel names the error");

    // and a CLEAN source clears the markers as you type
    await page.evaluate((src) => window.__forgeLintNow(src), CLEAN);
    const cleanState = await page.evaluate(() => window.__forgeLintState());
    assert.equal(cleanState.stage, "clean", "a clean source lints clean live");
    const gutterErrAfter = await page.evaluate(() => document.querySelectorAll(".gutter span.glm-err").length);
    assert.equal(gutterErrAfter, 0, "the gutter error marker clears when the source is fixed");
    T.push(`FORGE     authored-world map: ${forgeMap.nodes} nodes · live-lint: syntax-broken → gutter ●error + stage="parse"; fixed → clean`);

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    const transcript = renderTranscript({ base, narratorKind, T });
    await writeFile(path.join(OUT, "map.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "map.png")}`);
    console.log(`  transcript → ${path.join(OUT, "map.txt")}\n`);
    console.log("  ✓ THE ROOM MAP + LIVE VALIDATION RAN: /game/map returns the room graph; /game/validate lints clean/validate/parse without touching the world; the SVG map renders on /vault + /forge; typing a broken source surfaces a live gutter marker.\n");
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, narratorKind, T }) {
  const L = [];
  L.push("THE ROOM MAP + LIVE VALIDATION — the play + forge surfaces, driven");
  L.push(`driven run · attested-dm /game/map + /game/validate · narratorKind: ${narratorKind}`);
  L.push("served at " + base + "/vault  and  " + base + "/forge");
  L.push("=".repeat(76));
  L.push("");
  L.push("A room-map visualizer (inline SVG, no libs) draws the dungeon's room graph on both the play");
  L.push("surface (your position + visited rooms) and the forge (the shape of the world you authored,");
  L.push("a disconnected room flagged). Live validation lints the .dungeon source as you type — a");
  L.push("gutter marker + a panel — so you see problems BEFORE ▶ Play (which stays authoritative).");
  L.push("");
  L.push("-".repeat(76));
  L.push("THE DRIVEN CHECKS");
  L.push("-".repeat(76));
  for (const line of T) L.push("  " + line);
  L.push("");
  L.push("=".repeat(76));
  L.push("The map is an aid; the service is the authority. /game/validate opens no session, changes");
  L.push("no state — ▶ Play remains the fail-closed compile that mounts a world.");
  L.push("");
  return L.join("\n");
}

main().catch((e) => {
  console.error("\n  ✗ MAP RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
