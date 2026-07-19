# ROADMAP — Assurance-Perimeter Closure (living tracker)

The multi-swarm-cycle execution tracker for closing the witness-generation perimeter. **DESIGN** (the
architecture + the verdicts) = `docs/DESIGN-assurance-perimeter-closure.md`. **INVENTORY** (what was
trusted-Rust) = memory `project-witness-gen-assurance-perimeter`. This file = *where we are*, updated each
cycle. Orthogonal axis: the FRI floor (`project-fri-soundness-reality`, 57 calc bits) — never laundered by
this work.

## Mission (the invariant we are driving to)
Every consensus-visible value is EITHER constrained by a proven-**COMPLETE** AIR (`air_accepts ⟺ spec`, in
the honest shape below) OR a single Lean implementation Rust calls into. The receipt carries a **proof**, not
a trusted key. **Nothing trusted, nothing duplicated.**

## Standing discipline (the rules that keep re-earning themselves)
- **GREENFIELD** — nothing is deployed. NO cutover / migration / flag-day / byte-identical / compat theater
  (`feedback-no-greenfield-migration-theater`). Build the right object, DELETE the debt.
- **The honest `⟺` shape** (from the non-rev template, `209d543e5`): NOT a per-trace `Satisfied2 ↔ spec`
  (degenerates vacuous when ordering is lookup-enforced). It is **accept-SET ↔ spec** + **∀-soundness ∧
  ∃-completeness**, all trust folded into ONE named carrier bundle. Canary both directions.
- **CI-wire every exemplar** — a proof the default `Dregg2` build never compiles is a green nobody runs
  (`776381e52` wired the first two). Import into the root aggregator.
- **AIR is Lean-authored** (law #1). Rust computes witnesses / calls in; the CONSTRAINT is Lean.
- **VERIFY AGAINST THE DEPLOYED DESCRIPTOR, not a study face** ([[feedback-reality-gate-first-not-internal-consistency]]). The audit/crux mis-classified cap (#4) as underconstrained by reading a SUPERSEDED `*Refine`/study module — the LIVE registry entry (`attenuateVmDescriptor2R24 = attenuateV3`) already forced the genuine `writesTo8`. Every value's status is confirmed against the deployed registry entry + its apex wiring (`Rfix _`, `ClosureFanoutGenuine`), NOT a `*Refine` peer. A lane that REFUSES to build a mirror + reports the deployed reality is the discipline HOLDING (cap lane, `c8f443e37`).

## Status board — the 11 perimeter values
| # | value | class | status |
|---|---|---|---|
| — | `⟺` TEMPLATE (non-rev) | technique | ✅ `209d543e5` — the reusable schema + honest-shape finding; CI-wired |
| 8 | non-revocation | technique | ✅ (the template IS non-rev); residual: fold spine decode further |
| 2 | state commitment (transfer) | technique | ✅ FLAGSHIP `c68c4f5a9` — `transferDescriptor_commit_iff`; CI-wired. TAIL: generalize to ALL effect tags; make `wire_commit` the chained commitment + delete BLAKE3 `ledger.root()` |
| 5 | heap-root | ARCHITECTURE | ✅ `f7dd79db2` — genuine `Heap.set` forced, prepend-digest DELETED, MapOps carrier verified |
| 3 | receipt `TurnExecuted` | trust→proof | 🔶 resolver `26d3b1615` + migration `b4ac7ef23` (all 4 features → `TurnProven`, proof threaded onto the receipt) committed; coherence build VERIFYING (a `service_promise` test-panic being resolved — lands when all 4 features genuinely resolve green). Blocked on its own test-fix, not churn. |
| 4 | cap-root | ~~ARCHITECTURE~~ **ALREADY CLOSED** | ✅ the DEPLOYED `attenuateV3` already forces the faithful 8-felt sorted-tree write `writesTo8` (`CapOpenEmit.effCapOpenWriteV3_forces_write8`, §11 keystone, `#assert_axioms`-clean, apex-wired via `Rfix 12` / `ClosureFanoutGenuine` CLASS A) — **STRONGER than heap** (full ~124-bit vs heap's lane-0 scalar). The audit/crux "prepend / free CAP_DIGEST_NEW" read a SUPERSEDED study face, not the deployed descriptor. Doc corrected `c8f443e37`. The cap lane correctly REFUSED to build the requested scalar splice (would be a weaker re-authored mirror — reality-gate held). RESIDUALS (tracked, NOT soundness gaps): (a) delete the superseded prepend/free-digest code across ~15 cap-family modules (own multi-session cutover + adversarial audit); (b) a `Satisfied2`-only forged-root canary needs the sorted-tree functional property from the trace (discharge the `SpineCommits` decode) + closes the arity-7 leaf other-field encoding residual. |
| 6 | note-spend | structural | ✅ `cb2567872` (on origin) — `noteSpendFresh_accepts_iff` (full `⟺`: `NoteFreshAccepts ↔ nf∉nulls`), `gapOpen_complete` forward gap-construction, canaried both directions, `#assert_axioms`-clean. `NullifierTreeEncodes` kept as the honest Rust-accumulator-boundary residual (named). |
| — | garbled-eval | technique | ✅ `ba38e878b` (on origin) — `garbled_accepts_iff` (`AirAccepts ↔ CanonInstance`) + `garbled_bridge` (∀-soundness ∧ ∃-completeness); `honestG_satisfied2` generalizes the single witness parametrically; `GarbledCarriers` bundle (canon+hash), both canaries. Also CI-wired the previously `lake env`-only Rung-1/2 garbled chain. |
| 1 | ledger root | trusted-Rust | ⏳ folds into #2 tail (`cells_root` = Lean-authored sorted-Poseidon2 fold, bound at the boundary) |
| 9 | `system_roots_digest` | trusted-Rust | ⏳ later — small; make it an AIR-bound or Lean-authored value |
| 10 | effect state-transition | Lean-authored | ✅ deployed `produce_via_lean` (covered set); residual: the root (#2) + wasm/unmapped fallback |

## Cycles
- **Cycle 1 — DONE.** template · heap hole · state-commit flagship · CI-wiring · receipt resolver (held).
- **Cycle 2 — PROOFS DONE, integration finishing.** ✅ note-spend `cb2567872` · garbled `ba38e878b` · cap
  found-already-closed `c8f443e37`. 🔶 #3 migration `b4ac7ef23` verifying its own service_promise test-fix.
  ⚠ full-tree `Dregg2` CI-confirm blocked by co-tenant heap8 WIP (`MapMerkleRoot` deps mid-refactor) — origin is
  clean, both `⟺` bridges green standalone; the CI-wiring lands when the tree quiesces.
- **Cycle 3.** generalize transfer `⟺` to all effect tags; `cells_root` Phase-E; make `wire_commit` the anchor +
  delete BLAKE3 root; discharge `hcanon` field-faithfulness; the ~31-bit 8-felt-lane thread (heap/nullifier).
- **Apex (post-A).** recursive-proof-default (grow inner AIR to real `EffectVmAir`, force `NEW_COMMIT` in-circuit,
  then recurse). THEN the FRI floor campaign (`FriLdtExtractV3`, an adversary object) — separate.

## Cross-crate arcs (the multi-session pieces — plan before firing)
1. **Receipt proof-threading (#3):** commit pipeline PRODUCES the rotated STARK → ATTACH to `TurnReceipt`/
   `ConditionProof` at construction → 4 features migrate to `TurnProven`+`EffectVmProof` → land `26d3b1615`.
   Touches: node commit pipeline, sdk receipt type, turn/conditional, the 4 feature crates + tests.
2. **State-commit anchor cutover (#2 tail):** `wire_commit` becomes the chained commitment in `execute.rs`;
   delete BLAKE3 `ledger.root()`. Greenfield = a code change, NOT a migration. Touches: cell/ledger, turn/executor,
   node, light-client read paths.
3. **All-effect-tag `⟺`:** generalize `transferDescriptor_commit_iff` from transfer to every effect (the rotated
   descriptor covers them; the per-family completeness proofs do not exist). Pure Lean, but broad.

## Update protocol
Each cycle: flip the status cells, add the commit hashes, move finished arcs out of "in flight". Keep it terse.
This is the thread across the rolling window — the design doc explains WHY, this says WHERE WE ARE.
