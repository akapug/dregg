# BLOCKER: workspace-wide `cargo test` link failure — stale Lean archive init-cascade (2026-07-19)

**Impact:** `cargo test` cannot LINK for any crate pulling `dregg-lean-ffi` (dreggnet-telegram,
dreggnet-web, dreggnet-council, dreggnet-names, dreggnet-hermes, discord-bot, ...).
`cargo check --all-targets` is clean and **`--release` links fine — deploys are unaffected.**
Only test EXECUTION is blocked.

## Exact diagnosis (after 6 attempts + a control)
The spliced Lean archive's init-cascade references modules that **no longer exist**:
- `_initialize_Dregg2_Metatheory_Dynamics_Production`
- `_initialize_Dregg2_Metatheory_EpistemicDial`

Neither has a `.o` in `metatheory/.lake/build/ir/`, and neither has a `.lean` source at those
paths. The archive was built when those modules existed; the in-flight `metatheory/Dregg2/**`
work has since RENAMED or REMOVED them, so the archive's cascade dangles.

Earlier (superseded) readings, recorded so nobody re-chases them:
- NOT `ConstructiveKnowledge` — its `.o` IS present (debug and release).
- NOT (only) the archive GC pruning a reachable member — the archive was rebuilt to its full
  315 MB and the failure persisted, with a DIFFERENT missing-symbol set.
- Earlier runs showed missing `ProofWidgets_*` / `Mathlib_Tactic_Widget_*` inits; those cleared
  with the full rebuild, leaving the two Dregg2 modules above.

## Controls run
- Untouched `dreggnet-compute` / `driven.rs` fail IDENTICALLY -> tree-wide, not any lane's change.
- `cargo test -p collective-choice --no-run` links fine -> specific to lean-ffi-linking binaries.
- `DREGG_LEAN_FFI_NO_ARCHIVE_GC=1` now genuinely takes effect (see the rerun-if-env-changed fix,
  commit 188a454a9) and does NOT fix it — the archive content, not the GC, is the problem.

## The fix (owner: whoever owns metatheory/Dregg2)
A `lake build` over the settled metatheory tree, then re-splice the archive, so the cascade
matches the modules that actually exist. Cannot be done from outside that lane while its tree is
mid-rename / possibly non-compiling.

## Consequence to remember
Several commits from 2026-07-19 are **type-checked, not observed passing** (each says so in its
message): the telegram hidden-hand fix, the weighted-council restore, names+hermes label fix.
They need one clean `cargo test` run once the metatheory build settles.
