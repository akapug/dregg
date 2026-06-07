# POC — the REAL verified Lean executor runs in a browser

`index.html` + `drive-headless.mjs` prove that `execFullForestG`
(`@[export] dregg_exec_full_forest_auth`, the PROVED gated complete-turn
executor) runs **in an actual browser engine**, not just under Node:

```
node web/spike/poc/drive-headless.mjs
```

This serves `web/spike` and drives **real headless Chrome** over the DevTools
protocol (no puppeteer/npm). Observed:

```
[poc] status: Lean runtime booted in 237 ms. Running turns…
[poc] turn ① post-state: …"bal":[[0,0,70],[1,0,35]]…,"loglen":1,"ok":1   (COMMIT, conserved)
[poc] turn ② post-state: …"bal":[[0,0,100],[1,0,5]]…,"loglen":0,"ok":0    (ROLLBACK, unchanged)
[poc] verdict: PASS
```

Prereq: `web/spike/out-web/dregg.{mjs,wasm}` (the ES6 browser-shape build,
produced by `build-executor-wasm.sh` + the browser-variant link; ~41 MB wasm).
These are reproducible build artifacts (gitignored).

## Why the wasm is ~41 MB (the bloat, measured)

`Dregg2.Exec.FFI`'s transitive **import** closure is **8,757 modules — 8,099
of them Mathlib, incl. 342 `Mathlib.Tactic.*`** (the whole tactic/elaborator
framework). Lean runs every imported module's `initialize_` at boot, so that
code stays live regardless of `--gc-sections` (init-reachable ≠ compile-time-
only). 16,577 of the linked symbols are `Mathlib.CategoryTheory.*` alone —
pure proof scaffolding from `Dregg2.Core`'s monoidal-category imports, with
zero runtime relevance to a balance transfer.

The tactic imports (`Mathlib.Tactic`, `.Ring`, `.Tauto` in `Exec.Kernel`,
`CryptoKernel`, `Tactics`, `Core`, …) are **proof-time only** — the executor
never invokes `ring`/`tauto` at runtime. They are in the closure because the
runtime defs and the proofs live in the SAME modules.

## The size ladder (module-closure measured)

| Variant | module closure | tactic modules | est. wasm |
|---|---|---|---|
| current FFI | 8,757 | 342 | ~41 MB (measured) |
| trim Dregg2-level tactic imports (state still `Finset`) | ~1,754 | 216 | est. ~10–15 MB |
| runtime state uses `List`/`HashSet` not mathlib `Finset` | ~12 | 0 | **~1–2 MB** (tiny regime, measured for tiny.wasm) |

The hard floor for *touching mathlib `Finset` at all* is ~1,754 modules /
~216 tactic modules — mathlib's own `Finset.Basic` imports tactics at the top.
Single-digit-MB requires moving the **runtime** state representation off
mathlib `Finset` (keep `Finset` in the spec/proofs via a refinement); that's a
real refactor, not a link flag.
