# Docs Cleanup Plan

_Generated 2026-06-06 from 98 per-file triage dispositions. Goal: replace the
`.md` sprawl with a clean, non-misleading structure that holds only
current/useful info; archive implemented designs to `docs-old/` so they stop
misleading future readers/agents._

## TL;DR

There are ~100 markdown design docs split across **two** trees
(`/docs/rebuild/` and `/metatheory/docs/rebuild/`) plus a few top-level READMEs
and per-app READMEs. The corpus is ~40% live (KEEP/REFORM), ~30% implemented
(ARCHIVE), ~10% stale-no-salvage (DISCARD), with the rest being operational
runbooks that stay put.

The plan:
1. **Consolidate** all design docs under `metatheory/docs/` (that is where the
   live HANDOFF/CLAIMS/INTENT spine already lives and where agents look). The
   old `/docs/rebuild/` tree becomes empty.
2. **Five authoritative living docs** at the top of `metatheory/docs/`:
   `ARCHITECTURE.md`, `STATUS.md`, `ROADMAP.md`, plus directories `live/`
   (open designs), `reference/` (vocabulary + lit maps), `audits/` (honesty
   ledgers).
3. **Archive** the ~28 implemented/historical designs to `docs-old/`.
4. **Discard** a small set of stale candidate-selection siblings with no salvage.
5. **Refresh** the few drifted file:line / sorry-count / FFI-drop-in claims that
   the dispositions flagged as load-bearing-but-stale.

Operational runbooks (`deploy/aws`, `docker/*`, top-level `README/STATUS`, per-app
READMEs, retired-section READMEs) are correct and stay where they are — they are
not part of the design sprawl.

---

## 1. Proposed NEW directory structure

```
metatheory/docs/
├── ARCHITECTURE.md          ← THE canonical architecture (merge dregg2.md + DREGG2-FOUNDATIONS)
├── STATUS.md                ← ground-truth "what is proved / open right now" (= CLAIMS.md, kept at metatheory/CLAIMS.md; this is a pointer + the HANDOFF "where we are" snapshot)
├── ROADMAP.md               ← merged SUCCESSOR-ROADMAP + ROADMAP + IMPLEMENTATION-ROADMAP + HANDOFF tracks
├── GLOSSARY.md              ← project vocabulary (kept)
├── HANDOFF.md               ← rolling master handoff (= newest HANDOFF; older ones archived)
│
├── live/                    ← NOT-YET-BUILT plans + open research (never bury these)
│   ├── swap/                ← the dregg1→dregg2 cutover
│   │   ├── SWAP-READINESS.md
│   │   ├── DREGG1-TO-DREGG2.md
│   │   ├── GAP-MAP.md              (= DREGG2-GAP-MAP, open fills only)
│   │   ├── EFFECT-FIDELITY-LEDGER.md
│   │   ├── EFFECT-ISA-DESIGN.md
│   │   ├── EFFECT-HANDLER-ALGEBRA.md   (= DESIGN-EFFECT-HANDLER-ALGEBRA, R1-R12 table)
│   │   ├── APPS-READINESS.md
│   │   ├── PHASE-STEPCOMPLETE-AUDIT.md
│   │   └── PHASE-DISTRIBUTED-CONFORMANCE.md
│   ├── circuit-crypto/      ← the live soundness pillars (#3/#4)
│   │   ├── PHASE-CRYPTOKERNEL.md
│   │   ├── PHASE-CRYPTO-TCB.md
│   │   ├── PHASE-BRIDGE.md
│   │   ├── DESIGN-recursion-aggregation-private-joint-turns.md
│   │   ├── DESIGN-lookups-plonky3-perf.md
│   │   └── study-mina-relink.md
│   ├── intent/              ← Track A design north-star + phase-3 monoidal
│   │   ├── INTENT-AS-CO-RECEIPT.md
│   │   ├── PHASE-2-INTENT-SPEC.md
│   │   ├── INTENT-REFS-centers.md
│   │   └── INTENT-REFS-tensor-categories.md
│   ├── coordination/        ← consensus / I-confluence / justness open gates
│   │   ├── study-consensus.md
│   │   ├── DRIFT-STABILITY-SPECTRUM.md
│   │   └── study-gc.md            (open gc.rs unified-lace migration)
│   ├── apps/
│   │   ├── APP-THEOREM-SUITE.md
│   │   ├── RIGHT-OF-WAY-EPIC.md
│   │   └── DEVNET-COMPOSITION.md  (stays at Dregg2/Apps/, see note)
│   ├── research/            ← genuine open-research register (not engineering)
│   │   ├── OPEN-PROBLEMS.md
│   │   ├── PHASE-PROBABILISTIC-COINDUCTIVE.md
│   │   ├── SHEAF-OF-VERIFIERS.md
│   │   ├── SHEAF-GROUND-dregg.md
│   │   ├── HANDLER-TRANSFORMER-CONJECTURE.md
│   │   └── PHASE-UC-TRANSPORT.md
│   └── dregg4/              ← forward vision menus (clearly future)
│       ├── DREGG4-HYPERSYSTEM.md
│       ├── DREGG4-OS-ENDGAME.md
│       ├── DREGG4-CRYPTO-MENU.md
│       └── DREGG4-CROSS-POLLINATION.md
│
├── audits/                  ← standing honesty ledgers / anti-hype tripwires
│   ├── FAITHFULNESS-AUDIT.md       (ExecRights:=Unit tripwire)
│   ├── FAITHFULNESS-AUDIT-CORE.md  (de-vacuification targets)
│   ├── CONSISTENCY-SURFACE.md      (TCB carrier map)
│   ├── COVERAGE-AUTHORITY.md       (post-#94 re-grounded matrix)
│   ├── COVERAGE-DISTRIBUTED.md     (BFT-vs-CordialMiners mismatch)
│   ├── GROUND-AUTH-ATTESTATION.md  (narrow residual gaps)
│   ├── GROUND-STORAGE-PROGRAMS.md  (WAL/Merkle carry-forward)
│   ├── EFFECT-FIDELITY-LEDGER.md   (also linked from live/swap)
│   └── gaps-2-distributed.md       (deliberately-out-of-core scope map)
│       (gaps-1-substrate.md → reform into this or archive; see notes)
│
├── reference/              ← vocabulary, lit maps, durable categorical maps
│   ├── CONSTRUCTIVE-KNOWLEDGE.md   (conceptual spine; kept at metatheory/ root + linked)
│   ├── FOUNDATIONS-coalgebra.md
│   ├── FOUNDATIONS-modal-dials.md
│   ├── FOUNDATIONS-effect-comodel-lens.md
│   ├── FOUNDATIONS-verify-find-logic.md
│   ├── EXTERNAL-LEAN-REFERENCES.md (adopt/avoid column only)
│   ├── SHEAF-LIT-epistemic.md
│   ├── SHEAF-LIT-networks.md
│   ├── HANDLER-TRANSFORMER-LIT.md
│   ├── INTENT-REFS-optics.md
│   ├── INTENT-REFS-resources.md
│   ├── INTENT-REFS-linear.md
│   ├── INTENT-REFS-time.md
│   ├── INTENT-REFS-web3.md
│   └── INTENT-REFS-fairness.md
│
└── CLAUDETHOUGHT.md         ← ember's keepsake vision essay (kept verbatim)
```

Top-level repo `README.md` / `STATUS.md` / `HATCHERY.md` and `metatheory/README.md`
/ `metatheory/CLAIMS.md` / `metatheory/CONSTRUCTIVE-KNOWLEDGE.md` stay in their
current locations (they are the discovery entry points). `ARCHITECTURE.md`/
`ROADMAP.md`/`STATUS.md` inside `metatheory/docs/` are the consolidated design
docs; the root-level files are the short on-ramps that point into them.

**Justification:** the dispositions show the live material clusters into exactly
five concerns — (a) the SWAP cutover, (b) circuit/crypto soundness, (c) Intent
Track A, (d) coordination/consensus, (e) genuine open research / dregg4 vision —
plus a stable set of (f) honesty audits and (g) reference/vocabulary. The
`live/` subtree keeps every not-yet-built plan visible and grouped by the work
it gates; `audits/` keeps the anti-hype tripwires together; `reference/` holds
the durable maps that don't rot.

---

## 2. KEEP map (live docs → new home)

Format: `current path → new path` (REFORM = edit before/after move).

### Authoritative living docs (merge/promote)
- `docs/rebuild/dregg2.md` + `docs/rebuild/DREGG2-FOUNDATIONS.md`
  → **`metatheory/docs/ARCHITECTURE.md`** (REFORM: merge the consolidated
  architecture narrative; trim the implemented parts of dregg2 §1–6 to a status
  note; keep the unbuilt §7 circuit-PI surface; **drop DREGG2-FOUNDATIONS'
  stale "exactly THREE sorrys" headline** — Circuit/* has ~18; fix capital-M
  paths → `Dregg2/`).
- `docs/rebuild/SUCCESSOR-ROADMAP.md` + `docs/rebuild/ROADMAP.md` +
  `docs/rebuild/IMPLEMENTATION-ROADMAP.md`
  → **`metatheory/docs/ROADMAP.md`** (REFORM: SUCCESSOR is the spine — north-star
  toy→real table + 4 phases; fold ROADMAP's still-unbuilt Phase-2 circuit spine +
  anti-brick + recursion-trait plan and collapse its done metatheory-discharge
  section; **read IMPLEMENTATION-ROADMAP against current code before trusting any
  "done" markers** — it was not opened in the triage pass).
- `metatheory/docs/rebuild/HANDOFF-2026-06-06.md`
  → **`metatheory/docs/HANDOFF.md`** (newest handoff becomes the rolling master;
  carries reading order + non-negotiable discipline list. The 2026-06-03 one is
  superseded → archive).
- `docs/rebuild/GLOSSARY.md` → **`metatheory/docs/GLOSSARY.md`** (KEEP; fix the
  few drifted file:line cites — `sound_of_step_complete` lives in
  `Exec/Cell.lean` + `Spec/JointViaHyper.lean`, not `Boundary.lean`).
- `docs/rebuild/CLAUDETHOUGHT.md` → **`metatheory/docs/CLAUDETHOUGHT.md`** (KEEP
  verbatim — ember keepsake).

### live/swap/
- `docs/rebuild/SWAP-READINESS.md` → `live/swap/SWAP-READINESS.md` (REFORM: strip
  the multi-entry `execFullTurn`/`dregg_exec_full_turn` body superseded by the
  D1 one-entry consolidation → `dregg_exec_full_forest_auth`; KEEP the staged-
  rewrite framing + 5 deletion gates + "differential = kernel-vs-NEW-Rust never
  vs buggy dregg1").
- `docs/rebuild/DREGG1-TO-DREGG2.md` → `live/swap/DREGG1-TO-DREGG2.md` (KEEP crate-
  fate table; fix capital-M path cites).
- `metatheory/docs/rebuild/DREGG2-GAP-MAP.md` → `live/swap/GAP-MAP.md` (REFORM:
  strip the two RESOLVED frontier items — FILL J codec is GREEN, #138 forest-
  delegation IMPLEMENTED — and the long resolved-FILL prose; KEEP the still-open
  fills 4/5/7/8 as the swap-gap tracker).
- `metatheory/docs/rebuild/EFFECT-ISA-DESIGN.md` → `live/swap/EFFECT-ISA-DESIGN.md`
  (REFORM: the forest-delegation gap-note has itself drifted — `execFullChildrenA`
  now routes an edge; KEEP the "is this the right orthogonal effect basis / ~6
  shapes wearing ~50 names" ISA question).
- `metatheory/docs/rebuild/DESIGN-EFFECT-HANDLER-ALGEBRA.md` →
  `live/swap/EFFECT-HANDLER-ALGEBRA.md` (REFORM: scaffold landed but FullActionA
  migration did NOT happen; KEEP the re-verified R1-R12 hole table + convention→
  type premise; discard the stale "build RED gated on codec #136" framing — codec
  is green).
- `docs/rebuild/APPS-READINESS.md` → `live/swap/APPS-READINESS.md` (KEEP: the
  record-domain FFI wiring gap — SetField/EmitEvent — is still open).
- `docs/rebuild/PHASE-STEPCOMPLETE-AUDIT.md` → `live/swap/PHASE-STEPCOMPLETE-AUDIT.md`
  (KEEP the 4-conjunct replacement-coverage checklist).
- `docs/rebuild/PHASE-DISTRIBUTED-CONFORMANCE.md` →
  `live/swap/PHASE-DISTRIBUTED-CONFORMANCE.md` (REFORM: mark the C1 row CLOSED —
  `validate_handoff` now enforces granted⊄held; KEEP B1/C2 open gaps).
- `metatheory/docs/rebuild/EFFECT-FIDELITY-LEDGER.md` →
  `live/swap/EFFECT-FIDELITY-LEDGER.md` (KEEP; also referenced from audits/).

### live/circuit-crypto/
- `docs/rebuild/PHASE-CRYPTOKERNEL.md` (KEEP: live spec for #3/#4 — verify=no-law
  central hole).
- `docs/rebuild/PHASE-CRYPTO-TCB.md` (KEEP: §8 swap-readiness map).
- `docs/rebuild/PHASE-BRIDGE.md` (KEEP: 4-guarantee bridge theorem-shape table).
- `metatheory/docs/rebuild/DESIGN-recursion-aggregation-private-joint-turns.md`
  (KEEP — not in dispositions but is the active recursion/aggregation design;
  pairs with study-mina-relink).
- `metatheory/docs/rebuild/DESIGN-lookups-plonky3-perf.md` (KEEP — not in
  dispositions; live perf-design per the proof-system reorientation memory).
- `docs/rebuild/study-mina-relink.md` → `live/circuit-crypto/study-mina-relink.md`
  (REFORM: KEEP the JointTurn≡Zkapp_command mapping + per-cell-vs-global-commit
  divergence; the Mina-side OCaml cites are into `~/dev/mina`, unverified here).

### live/intent/
- `metatheory/docs/rebuild/INTENT-AS-CO-RECEIPT.md` (KEEP — Track A design
  north-star, HANDOFF's #2 reading).
- `metatheory/docs/rebuild/PHASE-2-INTENT-SPEC.md` (KEEP — not in dispositions;
  the active Phase-2 intent spec).
- `metatheory/docs/rebuild/INTENT-REFS-centers.md` (KEEP — Phase-3 monoidal
  upgrade ref, Centers.lean partially realizes it).
- `metatheory/docs/rebuild/INTENT-REFS-tensor-categories.md` (KEEP — L0-L4 stack +
  the critique-verified corrections that prevent re-attempting a Frobenius weld).

### live/coordination/
- `docs/rebuild/study-consensus.md` (KEEP: the 3 prose-contracts-to-make-real-gates
  + the BEC Thm-3.1 live risk).
- `docs/rebuild/DRIFT-STABILITY-SPECTRUM.md` (REFORM → KEEP just the two-windows
  kernel: TOCTOU equalizer SOLVED vs composition-window drift colimit OPEN).
- `docs/rebuild/study-gc.md` (REFORM → KEEP the open `gc.rs` unified-lace
  FederationId→StrandId migration; shed the lit-survey).

### live/apps/
- `metatheory/docs/rebuild/APP-THEOREM-SUITE.md` (KEEP: the anti-sprawl app
  discipline for Track I).
- `docs/rebuild/RIGHT-OF-WAY-EPIC.md` (KEEP: maintained doc for a live shipped
  demo cluster + honesty ledger).
- `metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md` → **stays at
  `Dregg2/Apps/DEVNET-COMPOSITION.md`** (REFORM: strike the two ALREADY-FALSE
  blockers — `docker/devnet-config` DOES exist, mandate apps DO have pages; KEEP
  the genesis apps.json wiring gap + P1-P4 PR sequence). Lives beside the code it
  maps; link it from `live/apps/`.

### live/research/
- `docs/rebuild/OPEN-PROBLEMS.md` (KEEP: update #7 for the admits_sound landing;
  rest is the don't-mistake-research-for-engineering guardrail).
- `docs/rebuild/PHASE-PROBABILISTIC-COINDUCTIVE.md` (KEEP: 3 deep open problems +
  infra inventory).
- `docs/rebuild/SHEAF-OF-VERIFIERS.md` (KEEP: ember's standing original direction).
- `docs/rebuild/SHEAF-GROUND-dregg.md` (REFORM → KEEP the row-by-row REAL/PARTIAL/
  POETRY map + the one OPEN first theorem; shed lit-survey bulk).
- `docs/rebuild/HANDLER-TRANSFORMER-CONJECTURE.md` (KEEP: live research grounded in
  5 proved facets).
- `metatheory/docs/rebuild/PHASE-UC-TRANSPORT.md` (KEEP — not in dispositions; UC
  transport per the reorientation memory's UC-security pursuit).

### live/dregg4/
- `docs/rebuild/DREGG4-HYPERSYSTEM.md` (KEEP forward vision).
- `docs/rebuild/DREGG4-OS-ENDGAME.md` (REFORM → one-page distillation of the
  "local theorem + one networked dial ⇒ OS feature" framing).
- `docs/rebuild/DREGG4-CRYPTO-MENU.md` (KEEP: curated crypto backlog).
- `docs/rebuild/DREGG4-CROSS-POLLINATION.md` (REFORM → KEEP only the genuinely-
  unbuilt frontier items; shed the now-landed cells).

### audits/
- `docs/rebuild/FAITHFULNESS-AUDIT.md` (KEEP: ExecRights:=Unit tripwire — STILL TRUE).
- `docs/rebuild/FAITHFULNESS-AUDIT-CORE.md` (REFORM: drop the now-fixed Privacy
  graph-tier target; KEEP Pacemaker/Synchronizer/Later:=id de-vacuification targets).
- `metatheory/docs/rebuild/CONSISTENCY-SURFACE.md` (KEEP: canonical "what do we
  assume" TCB map).
- `docs/rebuild/COVERAGE-AUTHORITY.md` (REFORM: cut the stale pre-#94 prose; KEEP
  the post-#94 re-grounding receipts).
- `docs/rebuild/COVERAGE-DISTRIBUTED.md` (REFORM → KEEP the one BFT-vs-Cordial-
  Miners mismatch verdict).
- `docs/rebuild/GROUND-AUTH-ATTESTATION.md` (KEEP the narrow residual: base
  Credential all-or-nothing, ring/chameleon unbuilt).
- `docs/rebuild/GROUND-STORAGE-PROGRAMS.md` (KEEP: WAL/Merkle carry-forward + the
  74-vs-16 StateConstraint gap).
- `docs/rebuild/gaps-2-distributed.md` (KEEP: out-of-core scope map).

### reference/
- `docs/rebuild/FOUNDATIONS-coalgebra.md` (KEEP §10 REAL/DECORATIVE/ASPIRATIONAL
  table; fix the phi_functorial-is-sorry drift → now PROVED-under-NonDegenerate).
- `docs/rebuild/FOUNDATIONS-modal-dials.md` (KEEP §10 table + named open theorems;
  same phi_functorial fix).
- `docs/rebuild/FOUNDATIONS-effect-comodel-lens.md` (KEEP the REAL/DECORATIVE/
  ASPIRATIONAL tagging discipline).
- `docs/rebuild/FOUNDATIONS-verify-find-logic.md` (KEEP the two false-slogan
  corrections).
- `metatheory/docs/rebuild/EXTERNAL-LEAN-REFERENCES.md` (REFORM → KEEP the
  adopt/avoid TCB-hygiene column; the build-ourselves column is now historical).
- `docs/rebuild/SHEAF-LIT-epistemic.md` (KEEP: cross-paper synthesis + H⁰=iff /
  H¹=sound-not-complete verdict + named next theorem).
- `docs/rebuild/SHEAF-LIT-networks.md` (REFORM → KEEP mapping + reading list; shed
  lit-survey bulk).
- `metatheory/docs/rebuild/HANDLER-TRANSFORMER-LIT.md` (REFORM → focused research
  note: the central conjecture + curated paper list).
- `metatheory/docs/rebuild/INTENT-REFS-{optics,resources,linear,time,web3,fairness}.md`
  (KEEP all six as the Intent reference maps — optics/resources/time acted-on,
  web3/linear/fairness durable rationale).

### Stay-put (NOT moved — discovery on-ramps + operational + per-app)
- `README.md`, `STATUS.md`, `HATCHERY.md` (repo root) — KEEP.
- `metatheory/README.md` (REFORM: recount or drop the "exactly 3 sorry" headline —
  Circuit/* has ~18; defer the count to CLAIMS.md).
- `metatheory/CLAIMS.md`, `metatheory/CONSTRUCTIVE-KNOWLEDGE.md` — KEEP.
- `deploy/aws/README.md`, `docker/README.md`, `docker/devnet-config/README.md`,
  `dregg-lean-ffi/README.md` (REFORM: `Metatheory.Exec.FFI` → `Dregg2.Exec.FFI`),
  `site/playground/sections/_retired/README.md`,
  `starbridge-apps/compartment-workflow-mandate/README.md` (REFORM: strike stale
  "no pages/"), `starbridge-apps/storage-gateway-mandate/README.md` — all KEEP.

---

## 3. ARCHIVE list (git-mv to docs-old/ — implemented, historical only)

These designs LANDED; keep them only as historical rationale so they stop
reading as live plans.

- `docs/rebuild/00-synthesis.md` (synthesis that produced dregg2.md; conclusions
  materialized) — preserve a 1-paragraph distillation in ARCHITECTURE's preamble.
- `docs/rebuild/01-spine-capability.md` — **REFORM-then-ARCHIVE**: extract the
  CDT≡strand-log thesis into ARCHITECTURE/CDT note (only partially realized), then
  archive the spine-exploration body. (Disposition said reform; the realized part
  is what survives, the exploration is historical.)
- `docs/rebuild/03-spine-proof.md` (superseded spine exploration).
- `docs/rebuild/cand-B-witness-pca.md` (README-marked SUPERSEDED, folded into dregg2).
- `docs/rebuild/cand-C-cap-distributed.md` (superseded candidate; preserve the
  permission-survives/authority-does-not distinction in ARCHITECTURE).
- `docs/rebuild/study-category.md` (materialized into Categorical.lean).
- `docs/rebuild/study-choreography.md` (IS the Coordination.lean spec, cited by #).
- `docs/rebuild/PHASE-SHIFT.md` (#1 move done; preserve trust-partition table).
- `docs/rebuild/PHASE-CONSTRUCTION.md` — **REFORM-then-ARCHIVE**: premise stale
  (toy kernel grown past it); extract the 3-strategy refinement partition +
  Spec⊒Exec⊒Rust tower + risk taxonomy into ROADMAP, then archive.
- `docs/rebuild/PHASE-METAPROGRAMMING.md` (mostly absorbed; preserve the
  #assert_axioms_all/codegen nugget into HATCHERY.md).
- `docs/rebuild/PHASE-DISTRIBUTED-ADVERSARY.md` (4 OPENs closed; own header says
  SUPERSEDED).
- `docs/rebuild/PHASE-EXTRACTION.md` (export exists; preserve the fuzzer-gap note).
- `docs/rebuild/PHASE-PROOF-CARRYING.md` (ProofForest.lean built as specced).
- `docs/rebuild/PHASE-VCG-WP.md` (WP.lean + WPCatalog.lean built).
- `docs/rebuild/FOUNDATIONS-authority-cdt-camera.md` (faithful as-built map).
- `docs/rebuild/FOUNDATIONS-limits-tensor-simplicial.md` (as-built; flag its stale
  zero-sorry claim in the archive note).
- `docs/rebuild/ZERO-SORRY-VERDICT.md` (dated point-in-time audit; preserve the
  teeth-test CI discipline note in CLAIMS.md).
- `docs/rebuild/dregg2-multicell-privacy.md` (§5 deltas built — JointTurn /
  CellUpgrade / Privacy).
- `metatheory/docs/rebuild/FEATURE-BUILD-BRIEFING.md` (recommendations executed;
  stale 51-effect count; Hatchery inventory duplicated in HANDOFF §1).
- `metatheory/docs/rebuild/HANDOFF-2026-06-03.md` (superseded by 2026-06-06).
- `docs-old/STARBRIDGE-DEVNET.md` (ALREADY in docs-old; genesis/status/CORS
  fixes landed — leave it, listed for completeness).

**Candidate siblings NOT in dispositions (verify then archive — all part of the
May-29 candidate-selection round that dregg2.md/00-synthesis superseded):**
- `docs/rebuild/cand-A-vat-coalgebra.md`
- `docs/rebuild/cand-D-choreography.md`
- `docs/rebuild/02-spine-cell.md`
- `docs/rebuild/CARRY-FORWARD-SYNTHESIS.md` (likely synthesis sibling)

---

## 4. DISCARD list (delete outright — stale/misleading, no salvage)

Lean strongly toward archive over delete (history is cheap), so this list is
deliberately tiny. Only docs whose every useful idea is already captured
elsewhere AND that actively mislead:

- `docs/rebuild/REORIENT.md` — disposition says REFORM, but its salvage (metatheory
  IS dregg2, trust-code-over-markdown, traps) is fully duplicated by HANDOFF's
  discipline section + CONSTRUCTIVE-KNOWLEDGE, and its STALE/LIVE pointer lists +
  "FFI-drop-in" framing are actively wrong vs the swap-as-rewrite understanding.
  **Recommend: extract nothing new, DELETE** (or archive if any doubt). Flagged
  in §5 for maintainer confirmation since the disposition wanted reform.
- `docs/rebuild/README.md` — index for the OLD `/docs/rebuild/` tree which this
  plan empties; its taxonomy is reborn as the new `metatheory/docs/` layout.
  **DELETE after the move** (the new tree's top-level docs are self-indexing).

Everything else either lands somewhere live or is archived. No other file in the
dispositions had "no salvage."

---

## 5. UNSURE — maintainer please decide

- **Two-tree consolidation.** I propose collapsing `/docs/rebuild/` INTO
  `metatheory/docs/`. If you'd rather keep design docs at the repo-root `/docs/`
  level (above the Lean project), say so and I'll mirror the same `live/audits/
  reference` layout there instead.
- **`docs/rebuild/REORIENT.md`** — disposition was REFORM; I lean DELETE because
  its content is fully duplicated and its FFI-drop-in framing is misleading.
  Confirm delete vs a thin reform.
- **`docs/rebuild/gaps-1-substrate.md`** — disposition REFORM. The still-open
  substrate list (multi-target codegen/settlement + bulk privacy cryptosystem) is
  real, but it overlaps `gaps-2-distributed.md`. Fold into one `audits/gaps.md`,
  or keep separate? I lean fold.
- **`docs/rebuild/01-spine-capability.md` / `PHASE-CONSTRUCTION.md`** — I marked
  these REFORM-then-ARCHIVE (extract the live thesis, archive the body). If you'd
  rather keep them whole in `live/`, they have a real unrealized kernel (CDT≡
  strand-log; refinement-partition taxonomy).
- **Files not in the 98 dispositions** (need a quick read before final placement):
  `metatheory/docs/rebuild/REVIEW-{explorer,playground,studio-starbridge}.md`
  (site/UI reviews — probably stale-or-operational, candidate archive),
  `docs/rebuild/{DREGG4-UNIFICATION,STARBRIDGE-LEAN-REIMAGINING,WHOLESALE-SWAP-LEDGER,
  COVERAGE-APPS,DOWNSTREAM-READINESS}.md`, and
  `metatheory/docs/rebuild/_RECOVERED-DESIGNS-2026-06-02.json` (a recovery index —
  likely archive once its pointers are folded into HANDOFF).
- **`IMPLEMENTATION-ROADMAP.md`** — defaulted to KEEP-LIVE (merge into ROADMAP) but
  was never opened in the triage. Confirm its "done" markers against current code
  before merging, per its own disposition.

---

## Execution order (when you green-light)

1. `git mv` the ARCHIVE set → `docs-old/` (extract the few preserve-nuggets first).
2. Create `metatheory/docs/{live,audits,reference}/...` and `git mv` the KEEP set in.
3. Merge the three roadmaps → `ROADMAP.md`; merge dregg2+FOUNDATIONS →
   `ARCHITECTURE.md`; promote newest HANDOFF → `HANDOFF.md`.
4. Apply the REFORM edits (stale headcounts, drifted file:line, capital-M paths,
   closed-row updates, FFI module rename) — these are the load-bearing
   de-misleading fixes.
5. Delete the DISCARD set.
6. Resolve §5 UNSURE items.

Never bury a not-yet-built plan: everything in `live/` is unbuilt-or-partial and
stays visible.
