# libdregg_lean.a — what the megabytes are, and the real shrink levers

Measured 2026-07-10 on nextop (Darwin-arm64, lean v4.30.0, mathlib pin
`1c2b90b…`), during the HEAD recut of the seed.

## Where the size lives (the Jul-07 4450-member / 195 MB seed)

| family | MB | members | note |
|---|---|---|---|
| Mathlib | 111.0 | 3058 | the import cone, mostly `__const` + `__text` |
| Dregg2 | 38.0 | 1107 | the executor slice |
| archive symbol index | 16.3 | 1 | proportional, unavoidable |
| Aesop | 14.3 | 135 | elaboration-time-only |
| Batteries | 6.1 | 78 | |
| ProofWidgets | 4.7 | 14 | biggest single object = PenroseDiagram (2.7 MB, 97% `__const` embedded assets) |
| Qq / Plausible / ImportGraph / LeanSearchClient | 4.4 | 41 | all elaboration-time-only |

Facts that kill the easy ideas:
- **Zero debug fat.** `strip -S` on the biggest objects is a no-op — leanc
  objects are `__const` data + code. No flag shrinks this.
- **Reachability-GC saves only ~20%.** The node build's GC'd working copy
  keeps 103/111 MB of Mathlib and **all 135 Aesop objects** — Lean module
  initializers chain through the import graph, so linking any Mathlib module
  keeps its whole import cone alive. Meanwhile Dregg2 GCs 38 MB → 7 MB
  (135/1107 objects reachable from the FFI exports). **The executor is ~7 MB
  riding a ~140 MB import cone.**
- The **distribution** form was already fine: zstd -19 ≈ 8-9× (195 MB → 21 MB).

## Why the fresh raw recut got BIGGER (295 MB, 9906 members)

`seed-dregg2-closure.sh` archives every `.c` under every warm IR root — and a
`lake exe cache get` materializes IR for ALL of mathlib, not just the FFI
import closure. ~5000 of the 8647 dependency objects in the raw cut are
modules the FFI never imports. The Jul-07 195 MB seed was closure-based
(dep-complete base + splice), not archive-everything. **Named fix: make the
script closure-aware** — enumerate the FFI import closure (the modules `lake
build Dregg2.Exec.FFI` actually elaborates) and archive only those. That alone
returns to ~195 MB and the build.rs closure-completion covers any stragglers
on warm trees.

## The real lever: the source import cone

Only **11 of 114** `Dregg2/Exec/*.lean` modules import Mathlib directly:
- `import Mathlib.Tactic` (the full umbrella): **one file**, RecordCircuit —
  **fixed 2026-07-10**: its proofs need only `ring` + `norm_num`; swapping to
  the two specific imports collapsed its build closure **2943 → 788 jobs**.
- `Mathlib.Tactic.Ring` ×6, `Mathlib.Algebra.BigOperators…` ×6,
  `Mathlib.Data.Finset…` ×3, `Mathlib.Data.Fintype.Basic` ×1 — and Mathlib is
  **proof-only in 9 of the 11 files** (only Caps.lean and NullifierCell.lean
  use Finset in defs).

So the structural shrink is the standard proof-split: move the theorems of
those 9 files into `Dregg2.Proofs.*` modules (which import Mathlib AND the
Exec module), leaving the Exec runtime slice with zero Mathlib imports except
the Finset-computational pair. Estimated effect: the compiled FFI closure
drops from "most of mathlib" to the Finset/algebra cone; combined with the
closure-aware seed script, the seed should land well under 100 MB, and a
further Finset→own-finmap refactor in Caps/NullifierCell would take the cone
out entirely (~tens of MB seed, mostly Dregg2 itself). Days-scale, mechanical,
zero proof loss — each split file re-proves against the same defs.

Also fixed in this pass: the script's `ls`/`ar *.o` globs blew ARG_MAX at
9906 objects (Darwin) — now find/xargs-batched, and the archive is written to
`.a.new` + atomically renamed so a concurrent `cargo build` can never copy a
torn seed.
