// THE DRIVEN RUN — THE REAL dungeon-on-dregg ENGINE over HTTP.
//
// Spawns the native `real-dungeon-service` (the committed real game — The Warden's Keep —
// on spween-dregg's REAL WorldCell/executor; NO attested-dm), then DRIVES it over the wire
// with plain fetch, ASSERTING the invariants against the service's own responses:
//
//   A. A WINNING PLAYTHROUGH — trade blows → press on → claim the crown → descend →
//      cast the ward → seize the hoard. Every move LANDS as a real TurnReceipt returned
//      over the wire (turnHash/preStateHash/postStateHash printed), the committed-move
//      count grows by one per landed move, and the run reaches a real WIN (gold 500, ended).
//   B. /session/verify returns verified:true — a fresh, identically-seeded keep is re-driven
//      through the recorded choices (verify_by_replay) and the receipt chain links.
//   C. THE "you can't cheat" MOMENT (a fresh session) — after the Red Hand claims the crown,
//      the rival Blue-Hand claim on the SAME crown is REFUSED by the real executor (a WriteOnce
//      StateConstraint tooth), and NOTHING commits (anti-ghost: relic_owner still Red).
//
// HONEST SCOPE (printed): verification is O(N) verify_by_replay + chain-linkage, NOT the
// succinct light client. A refused move is anti-ghost on the world cell but advances the
// agent's receipt chain (anti-replay), so the illegal demo runs in a SEPARATE session from
// the verified winning run.
//
// Writes demo/run/real-dungeon.txt.

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import net from "node:net";
import path from "node:path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const OUT = path.join(__dirname, "run");
const BIN = path.join(REPO, "target", "debug", "real-dungeon-service");

const lines = [];
const say = (s = "") => {
  lines.push(s);
  console.log(s);
};

function freePort() {
  return new Promise((res, rej) => {
    const srv = net.createServer();
    srv.on("error", rej);
    srv.listen(0, "127.0.0.1", () => {
      const p = srv.address().port;
      srv.close(() => res(p));
    });
  });
}

async function waitListening(port, ms = 8000) {
  const deadline = Date.now() + ms;
  while (Date.now() < deadline) {
    const ok = await new Promise((res) => {
      const s = net.connect(port, "127.0.0.1");
      s.on("connect", () => { s.destroy(); res(true); });
      s.on("error", () => res(false));
    });
    if (ok) return;
    await new Promise((r) => setTimeout(r, 100));
  }
  throw new Error("service did not start listening");
}

async function main() {
  await mkdir(OUT, { recursive: true });
  const PORT = await freePort();
  const BASE = `http://127.0.0.1:${PORT}`;

  say("── spawning the REAL dungeon-on-dregg service (The Warden's Keep, real WorldCell) ──");
  const child = spawn(BIN, [], {
    env: { ...process.env, REAL_DUNGEON_BIND: `127.0.0.1:${PORT}` },
    stdio: ["ignore", "pipe", "pipe"],
  });
  child.stderr.on("data", (d) => process.stderr.write(`[svc] ${d}`));

  const j = async (pathname, body) =>
    (await fetch(BASE + pathname, body
      ? { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify(body) }
      : {})).json();

  try {
    await waitListening(PORT);

    // ── PHASE 1 — play to a WIN, every move a real TurnReceipt over the wire ──
    say("\n── PHASE 1 · play The Warden's Keep to a WIN (each move a real executor turn) ──");
    let start = await j("/session/start", { seed: 70 });
    say(`  started · room=${start.state.room} · hp=${start.state.vars.hp} · cell=${start.state.cellId}…`);

    // The winning line (indices are the keep's choice coordinates; the order is forced by teeth).
    const WIN = [
      [0, "trade blows with the warden", "FieldGte hp floor"],
      [1, "press on into the hall", "(ungated)"],
      [0, "claim the crown for the Red Hand", "WriteOnce loot"],
      [2, "descend the collapsing stair", "Monotonic ratchet"],
      [0, "cast the sealing ward", "FieldLteField budget"],
      [2, "seize the hoard", "(ungated → END)"],
    ];

    let committed = 0;
    for (const [idx, label, tooth] of WIN) {
      const moves = await j("/session/moves");
      const legal = (moves.moves || []).some((m) => m.index === idx);
      assert.ok(legal, `move ${idx} (${label}) is listed at room ${moves.room}`);
      const r = await j("/session/move", { index: idx });
      assert.equal(r.ok, true, `move ${idx} (${label}) commits: ${r.reason || ""}`);
      committed += 1;
      assert.equal(r.state.committedMoves, committed, "committed-move count grows by one");
      say(`  ✔ ${label}  [tooth: ${tooth}]`);
      say(`      turn ${r.receipt.turnHash.slice(0, 24)}…  pre ${r.receipt.preStateHash.slice(0, 16)}… post ${r.receipt.postStateHash.slice(0, 16)}…`);
    }

    const st = await j("/session/state");
    say(`  ⇒ state: room=${st.room} · ended=${st.ended} · won=${st.won} · gold=${st.vars.gold} · depth=${st.vars.depth} · relic_owner=${st.vars.relic_owner}`);
    assert.equal(st.won, true, "the keep is cleared (a real WIN: gold 500, scene ended)");

    // ── PHASE 1b — /session/verify returns true (replay + chain-linkage) ──
    const v = await j("/session/verify");
    say(`\n── verify (O(N) replay + chain-linkage) ──`);
    say(`  verified=${v.verified} · replayOk=${v.replayOk} · chainLinks=${v.chainLinks}`);
    say(`  ${v.chainNote}`);
    assert.equal(v.verified, true, "the winning run verifies (replay reproduces + chain links)");
    assert.equal(v.replayOk, true, "verify_by_replay reproduced every committed state");

    // ── PHASE 2 — an illegal move over the wire is a REAL executor refusal (anti-ghost) ──
    say("\n── PHASE 2 · an illegal move is a REAL executor refusal (fresh session, anti-ghost) ──");
    await j("/session/start", { seed: 70 });
    await j("/session/move", { index: 1 }); // gatehall -> hall
    const red = await j("/session/move", { index: 0 }); // Red claims the crown
    assert.equal(red.ok, true, "the Red Hand's first claim commits (WriteOnce 0→1)");
    say(`  ✔ Red claims the crown  ·  relic_owner=${red.state.vars.relic_owner}  ·  turn ${red.receipt.turnHash.slice(0, 24)}…`);
    const blue = await j("/session/move", { index: 1 }); // Blue claims the SAME crown → refused
    assert.equal(blue.ok, false, "the rival Blue-Hand claim does not commit");
    assert.equal(blue.refused, true, "it is a real executor refusal");
    assert.equal(blue.state.vars.relic_owner, 1, "anti-ghost: the crown still belongs to Red");
    say(`  ✗ Blue claims the SAME crown → REFUSED by the executor`);
    say(`      reason: ${blue.reason}`);
    say(`      anti-ghost: relic_owner still ${blue.state.vars.relic_owner} (unchanged, nothing committed)`);

    say("\n── Honest scope ──");
    say(`  ${v.scope}`);
    say(`  A production deploy still needs: player auth + per-identity sessions (this is one`);
    say(`  in-memory session behind a mutex), durable ledger/receipt persistence (state is`);
    say(`  process memory), and real hosting/TLS (a plain local HTTP/1.1 loop).`);
    say("\nALL ASSERTIONS PASSED — the REAL dungeon-on-dregg engine is deployed, played to a WIN over HTTP");
    say("(real receipts returned), an illegal move refused by the real executor, and /verify true.");

    await writeFile(path.join(OUT, "real-dungeon.txt"), lines.join("\n") + "\n");
  } finally {
    child.kill("SIGKILL");
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
