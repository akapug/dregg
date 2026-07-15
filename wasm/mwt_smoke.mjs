// On-device (wasm) smoke for multiway-tug proving: drive the REAL exported
// #[wasm_bindgen] entry points through the JS boundary under node — prove a played
// card's Poseidon2 membership IN WASM, confirm it binds the committed hand root, and
// verify it. This is the exact call a browser makes. Run: node mwt_smoke.mjs
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const wasm = require("./pkg-mwt/dregg_wasm.js");

const HAND = "[[0,1001],[1,1002],[3,1003],[7,1004],[12,1005],[18,1006]]";

function assert(cond, msg) {
  if (!cond) { console.error("SMOKE FAIL:", msg); process.exit(1); }
}

let anyProof = null;
for (const card of [0n, 7n, 18n]) {
  const t0 = Date.now();
  const out = wasm.proveTugPlayOnDevice(HAND, card);
  const dt = Date.now() - t0;
  assert(out && out.proof_json, `card ${card}: a proof envelope came back`);
  assert(out.root_matches_committed === true, `card ${card}: bound root == committed HandTree root`);
  assert(out.proof_size_bytes > 0, `card ${card}: non-empty proof blob`);
  const v = wasm.verifyTugPlayOnDevice(out.proof_json);
  assert(v.valid === true, `card ${card}: on-device proof VERIFIES (err=${v.error})`);
  console.log(
    `PASS card=${card}: prove ${dt}ms, verify ${Math.round(v.verification_time_ms)}ms, ` +
    `leaf=${out.leaf}, root=${out.root}, rows=${out.trace_rows}, size=${out.proof_size_bytes}B, ` +
    `root_matches_committed=${out.root_matches_committed}`);
  anyProof = out.proof_json;
}

// NEGATIVE: a card not in the hand yields no on-device proof (fail-closed).
let threw = false;
try { wasm.proveTugPlayOnDevice(HAND, 99n); } catch (_) { threw = true; }
assert(threw, "a card not in the hand must fail closed (no proof)");
console.log("PASS negative: a fabricated card (99) fails closed in wasm");

console.log("MULTIWAY-TUG ON-DEVICE (WASM) SMOKE: OK — the browser generated the match's per-play membership proofs client-side and they verify.");
