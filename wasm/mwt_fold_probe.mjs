// HONEST BOUNDARY PROBE: attempt the FULL recursive fold on-device (wasm) and measure
// where it hits the wasm32 limit (memory / time). foldTugMatchOnDevice runs the whole
// Phase-3 recursion fold (prove_turn_chain_recursive) — heavy even natively. This records
// the failure mode (OOM vs slow) in the browser's 32-bit address space, single-threaded.
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const wasm = require("./pkg-mwt/dregg_wasm.js");
const HAND = "[[0,1001],[1,1002],[3,1003],[7,1004],[12,1005],[18,1006]]";

console.log("FOLD PROBE: calling foldTugMatchOnDevice(HAND, 0, 1) in wasm...");
const t0 = Date.now();
try {
  const out = wasm.foldTugMatchOnDevice(HAND, 0n, 1n);
  const dt = Date.now() - t0;
  console.log(`FOLD PROBE OK in ${dt}ms: num_turns=${out.num_turns}, accepts=${out.lightclient_accepts}, bytes=${out.proof_size_bytes}`);
} catch (e) {
  const dt = Date.now() - t0;
  console.log(`FOLD PROBE HIT WASM LIMIT after ${dt}ms: ${e && e.name}: ${e && e.message}`);
}
