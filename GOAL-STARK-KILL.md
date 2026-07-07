# GOAL — STARK-KILL: re-derive the hand-rolled Rust STARK engine + its ~45 AIRs from Lean

*(This goal's trail. The repo's `GOAL.md` belongs to the storage-in-lean lane — do NOT
touch it. Full plan: `docs/deos/LEGACY-STARK-DELETION-SCOPE.md`.)*

## The mission
Kill `circuit/src/stark.rs` (the O(n²) hand engine) + ~45 hand-authored Rust AIRs by
EMITTING every circuit from Lean as a byte-pinned `EffectVmDescriptor2` on the p3 IR2
prover (law #1). Then climb the semantic ladder as high as it goes — Rung 1 (functional
refinement) AND Rung 2 (semantic no-forgery) for EVERY family, Rung 3 (fold → light-client
verifiable) where there's a consumer, and beyond (cross-circuit composition + assurance-case
apex). Done = engine + AIRs deleted, every survivor Lean-emitted + Rung-1&2-proven.

## Current thrust
Rung 1 across all 20 families (whole-descriptor `Satisfied2 ⟺ genuine semantic relation`),
+ opening Rung 2 on DFA (the first target). Verify-before-commit; non-vacuous or reject.

## Next 3 moves
1. Harvest the Rung-1 resume swarm (`w2hvgi0r4`) on completion → build-verify each Refine
   on my tree, commit only adversarially-CONFIRMED non-vacuous bridges.
2. DFA Rung-2 pathfinder — close `hterm` (the terminal-step) via `route_commitment_binds_trace`
   → unconditional `Satisfied2 → final = classify`. Establishes the Rung-2 pattern.
3. Fan out Rung-2 across all families using DFA Rung-2 as the template; then Phase 2b
   (rewire consumers + delete hand AIRs, theorem-backed) for the done families.

## Done-log
- Rung 0 (emit + real-prover gate) landed for all 20 families — `9c440d208` (+ merkle
  pathfinder `d7d3348fa`). Verified on my tree: 20 emit modules build, 21 gate tests pass.
- Rung 1 DFA bridge landed — `DfaRoutingRefine.lean` (`dfaRouting_refines_classify` +
  unconditional `dfaRouting_genuine_prefix`). Adversarially CONFIRMED non-vacuous,
  axiom-clean. Honest PARTIAL: `hterm` terminal-step = the first Rung-2 target.
- Scope doc + refinement ladder committed — `6716a3dcb`.
- Rung-1 swarm (other 20 families) resumed after a session-limit zombie — `w2hvgi0r4`
  (8 emits cached, remainder + all verifies re-running).
