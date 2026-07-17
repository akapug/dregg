# DISCARD-CANDIDATES

Ancient-strata docs that are **safe to discard** — fully harvested into `HARVEST-KEEPERS.md` AND
genuinely superseded. The discard itself is ember's call; this is a conservative recommendation.
Every keeper from these files is preserved with provenance in `HARVEST-KEEPERS.md`, so dropping the
source loses nothing.

**Conservative bar:** a file is listed ONLY if (a) everything forward-looking was extracted, AND
(b) it's genuinely stale/superseded/research-narrative. Partly-current files are NOT listed (they
appear under "DO NOT DISCARD" below with what's still live).

---

## ⚠ TOP-PRIORITY (actively misleading — likely to send an agent down a wrong path NOW)

None of the read files is a confidently-stated FALSE claim about the current architecture. The
closest hazards are handled by note, not discard:

- **`.docs-history-noclaude/rebuild/metatheory/_RUST-LEAN-DIVERGENCE-LEDGER.md`** — NOT a discard candidate, but **stale-as-frozen-snapshot**: it is a GENERATED artifact whose committed corpus is older than `_SWAP-COMPLETE-STATUS.md` (recent CellUnseal/escrow/obligation projections shift the GAP/AGREE counts). Treat the table as a stale cache; regenerate via `turn/tests/rust_lean_divergence_finder.rs` before trusting any divergence claim. (The header already says the table records the eligibility map only when Lean isn't linked.) Keep the file; regenerate, don't read-frozen.
- The general hazard ember named (a stale obligation/gapmap table read as current state) is mitigated by the keeper note: the live coverage docs (`_SWAP-COMPLETE-STATUS`, `_SILVER-COVERAGE-LEDGER`, `_EXECUTOR-COMPLETENESS-GAPMAP`) are SNAPSHOTS — verify counts vs HEAD, never act on a frozen "GAP" without re-checking the code.

---

## SAFE TO DISCARD — research-survey narrative (durable ideas harvested)

The `INTENT-REFS-*` files are literature-survey passes whose *forward-looking distillate* (the build
ladder, the corrected overclaims, the key citations + "why it matters to dregg") is now captured in
`HARVEST-KEEPERS.md`. The remaining body is per-paper narrative + refuted-claim history that git
retains. The actual Lean build specs live in `PHASE-2-INTENT-SPEC.md` and `INTENT-AS-CO-RECEIPT.md`
(also harvested). Discard-safe:

- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-centers.md` — monoidal/Drinfeld-center survey. WHY: build ladder + the two ⚠ corrections (Predicate⊣Witness is NOT the monoidal adjoint; AMM-as-center is a pun) harvested. Harvested into HARVEST-KEEPERS.
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-fairness.md` — justness/van-Glabbeek survey. WHY: the justness decision + `Proof/Fairness.lean` plan + the four citations harvested. Harvested into HARVEST-KEEPERS.
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-linear.md` — linear-logic/session-types survey. WHY: the three recommendations (conservation-as-monoid-hom, frame layer, session cut) + the linearity thesis harvested. Harvested into HARVEST-KEEPERS.
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-optics.md` — coend/optics/open-games survey. WHY: the coend-reuse verdict + lens-for-auction de-risk harvested. Harvested into HARVEST-KEEPERS.
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-resources.md` — resource-theory/cospan survey. WHY: the decorated-cospan SMC (highest-leverage artifact) + two-layer-split correction + catalysis/Petri insights harvested. Harvested into HARVEST-KEEPERS.
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-tensor-categories.md` — hyperdoctrine/escrow-monad survey. WHY: `escrowMonadHom`, Lawvere K1–K8, and the refuted overclaims harvested. Harvested into HARVEST-KEEPERS. (The `_INDEX` itself rates this "MOSTLY-STALE — value is in filtering what doesn't work.")
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-time.md` — causal-vs-frame time survey. WHY: the `Deadline` sum type + commit-wait bridge + the causal-set/Spanner/clock-sync insights harvested. Harvested into HARVEST-KEEPERS.
- `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-web3.md` — intent-centric SOTA survey. WHY: the 4-rung DeFi benchmark + "what dregg adds" + the Aequitas/Themis/Condorcet honesty boundary harvested. Harvested into HARVEST-KEEPERS.

## SAFE TO DISCARD — superseded web-surface reviews (`docs-old/`)

These review surfaces (explorer / playground / studio / starbridge-v1) are superseded by the deos
desktop / starbridge-v2 cockpit. Surface-specific chrome is dead; the transcending product/UX
insights are harvested.

- `docs/docs-old/REVIEW-playground.md` — FULLY STALE. WHY: playground-specific cruft (dead WebSocket scaffold, stale discovery.json schema, orphaned ci-results) on a surface with no network integration; nothing transcends. Harvested (nothing of lasting value beyond one open question, captured).
- `docs/docs-old/REVIEW-explorer.md` — MOSTLY STALE. WHY: surface superseded; the two transcending findings (`/api/receipts/{hash}/witnesses` + `/api/events` polls, client-side finality verify) harvested. Harvested into HARVEST-KEEPERS.
- `docs/docs-old/REVIEW-studio-starbridge.md` — MOSTLY STALE. WHY: surface renamed → cockpit; the one live finding (`/api/events` poll) + witness-fetch open question harvested. Harvested into HARVEST-KEEPERS.
- `docs/docs-old/_FRONTEND-OVERHAUL-PLAN.md` — SUPERSEDED BLUEPRINT. WHY: a coherent product vision (task-first Author/Simulate/Observe shell, foreground verified guarantees, kill playground-as-surface, verified-guarantee badges, client-side finality) — fully harvested as keepers; the diagnosis transcends the dead surfaces but the deos cockpit epoch is the realized successor. Discard-safe ONLY after confirming the keepers landed; the UX principles are now in HARVEST-KEEPERS.

## SAFE TO DISCARD — superseded / fully-actioned design audits

- `.docs-history-noclaude/rebuild/metatheory/_RUST-CIRCUIT-CONSOLIDATION.md` — DATED audit (per `_INDEX`). WHY: verdict "do NOT delete the manual Rust AIRs (Lean emits digest-equality, the Poseidon2 producing the digest lives in Rust); only Rust-vs-Rust consolidation is safe" is the durable insight (harvested). The DELETE-1/2 audits ran (both BLOCKED on caller migration, not deletable); DELETE-3/4 criteria set but unrun. The reasoning is preserved; the action is suspended. Harvested into HARVEST-KEEPERS. (Mild caution: if anyone revisits Rust circuit consolidation, re-derive from current code, not this snapshot.)

---

## DO NOT DISCARD (partly-current or still-live reference — listed so they're not swept by mistake)

**Still-current reference ledgers** (read-before-claiming docs; harvest took only forward bits):
`_CRYPTO-HYPOTHESIS-LEDGER.md`, `_CIRCUIT-ASSURANCE-PER-EFFECT.md`, `_THREAT-MODEL.md`,
`CONSISTENCY-SURFACE.md`, `_PROOF-INTEGRITY-LEDGER.md`, `_AUTHORIZATION-COMPLETE.md`,
`_VACUITY-SWEEP.md`, `_WHAT-IS-DREGG.md`, `_DREGG-ONTOLOGY-AND-PRODUCT.md`,
`EXTERNAL-LEAN-REFERENCES.md`, `_INDEX.md` (the navigation map).

**Live design / worklist docs** (the design is the live plan; the worklist tracks open work):
`_IR-EXTENSION-DESIGN.md`, `_RECORD-LAYER-UPGRADE.md`, `_EMITTER-AMPLIFICATION-WORKLIST.md`,
`DESIGN-lookups-plonky3-perf.md`, `DESIGN-recursion-aggregation-private-joint-turns.md`,
`DESIGN-EFFECT-HANDLER-ALGEBRA.md`, `_POLICY-LANGUAGES-REFRESH.md` (the de-stodgying stages D0–D9),
`TITANIUM-PHASE.md`, `APP-THEOREM-SUITE.md`, `PHASE-2-INTENT-SPEC.md`, `INTENT-AS-CO-RECEIPT.md`.

**Live coverage SNAPSHOTS** (current as of ~2026-06-08; verify counts vs HEAD, don't act on a frozen
GAP — these are the docs whose staleness most risks misleading an agent, but they're not discardable
because they're the only map of remaining work):
`_SWAP-COMPLETE-STATUS.md`, `_SILVER-COVERAGE-LEDGER.md`, `_EXECUTOR-COMPLETENESS-GAPMAP.md`,
`_DREGG-DREGGRS-MANIFEST.md`, `_DREGG1-DREGG2-UNIFICATION-LEDGER.md`, `_METATHEORY-GLUE-AUDIT.md`,
`AUTHORITY-DIVERGENCE-FINDING.md` (decision-pending: the `notify` enrichment), `_RUST-LEAN-DIVERGENCE-LEDGER.md` (regenerate, don't trust frozen).

**Live federation / consensus / UC design** (the verified-distributed lane blueprint):
`_FEDERATION-SSB-DESIGN.md`, `_FEDERATION-SSB-ORIENTATION.md`, `_CAPTP-ORIENTATION.md`,
`CONSENSUS-GROUNDING.md`, `UC-CARRIER-GAME-MAP.md`, `PHASE-UC-TRANSPORT.md`, `_POLIS-SUBSTRATE.md`,
`_PRODUCT-POLIS-ASSESSMENT.md`.

**Out of this harvest's WRITE scope** (READ-only flag for ember): there is a SECOND, even more
ancient `docs/rebuild/` at the REPO ROOT (`breadstuffs/docs/rebuild/` — the foundations/spine/
candidate essays: `01-spine-*.md`, `cand-*.md`, `FOUNDATIONS-*.md`, `DREGG4-*.md`, `OPEN-PROBLEMS.md`,
`GLOSSARY.md`, …). It was NOT harvested here (outside `metatheory/docs/`). It is a strong candidate
for a follow-up harvest pass — flag it before any discard there.
