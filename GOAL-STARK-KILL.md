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
Rung 1 nearly complete (17/20 families landed + committed). BLOCKED on the API session
limit (resets ~02:40 ET 07-07) for the last stragglers + Rung 2. Verify-before-commit.

## Next 3 moves (fire when the limit resets)
1. Resume `wf_1ee0382f-94a` for the 4 Rung-1 stragglers: refine temporal + garbled (died
   mid-emit), refute multi_step + presentation (emit green, verify died). Harvest + commit
   CONFIRMED.
2. Re-fire the DFA Rung-2 pathfinder (`wf_9717841d-cf1`, BLOCKED = its lone agent hit the
   limit, not a real block) — close `hterm` via `route_commitment_binds_trace`.
3. Fan out Rung-2 across all families using DFA Rung-2 as template; then Phase 2b
   (theorem-backed hand-AIR deletion) for the done families.

## Done-log
- Rung 0 (emit + real-prover gate) landed for all 20 families — `9c440d208` (+ merkle
  pathfinder `d7d3348fa`). Verified on my tree: 20 emit modules build, 21 gate tests pass.
- Rung 1 DFA bridge landed — `DfaRoutingRefine.lean` (`dfaRouting_refines_classify` +
  unconditional `dfaRouting_genuine_prefix`). Adversarially CONFIRMED non-vacuous,
  axiom-clean. Honest PARTIAL: `hterm` terminal-step = the first Rung-2 target.
- Scope doc + refinement ladder committed — `6716a3dcb`.
- Rung-1 swarm (other 20 families) resumed after a session-limit zombie — `w2hvgi0r4`
  (8 emits cached, remainder + all verifies re-running).
- Rung 1 — 16 whole-descriptor bridges landed + committed (verified on my tree, lake 3024
  jobs, adversarially CONFIRMED, non-vacuous, axiom-clean; bridge_action reaches IFF).
  13 GREEN + 3 honest PARTIAL (membership/note_spending/non_revocation residuals = Rung-2
  targets). Total Rung 1 = 17/20 (incl DFA). HELD unverified: multi_step + presentation
  (refute died on limit); temporal + garbled (refine died) — resume when limit resets.
