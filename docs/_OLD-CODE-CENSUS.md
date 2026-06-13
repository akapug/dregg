# OLD-CODE CENSUS — dregg heritage cleanup

Date: 2026-06-13. Scope: whole repo at `/Users/ember/dev/breadstuffs`.
Method: workspace-member map (root `Cargo.toml`) + whole-tree reference greps
(`rg`, `cargo metadata`, `git ls-files`). Heritage lineage: pyana → dregg1 → dregg2.

**Verification discipline applied:** every deletion below has grep-confirmed ZERO
live build references (no workspace membership, no path-dep, no script/CI use).
`cargo metadata --no-deps` resolves green after deletion (exit 0). No code inside
the off-limits active crates was touched.

---

## SUMMARY COUNTS

| Category | Count | Action |
|---|---|---|
| DEAD (safe-deleted) | 3 items (apps/ tree = 60 files, benches/summary.rs, 3 root logs) | DELETED |
| SUPERSEDED (parallel) | 2 (`apps/`→`starbridge-apps/` [deleted]; `ts-sdk.archived/`→`sdk-ts/`) | 1 deleted, 1 needs-review |
| STALE-DOCS archives | 3 dirs (`docs-old/` 79, `old-docs/` 43, `docs-history/` 10 tracked files) | NEEDS-REVIEW (deliberate history) |
| LEGACY-HERITAGE | `gen_kimchi.rs` (still wired), gitignored scratch dirs | KEEP / note |
| NEEDS-REVIEW | see ranked plan below | main-loop decision |

**Verdict: GREEN** — the unambiguous accidental cruft is gone (stray superseded
app tree, orphan bench file, stale root logs) and a ranked prune plan exists for
the deliberate-history archives and the off-limits-crate items.

---

## SAFE-DELETIONS PERFORMED (this run)

### 1. `apps/` — SUPERSEDED app tree (DELETED, 60 tracked files)
- **Evidence of death:** package names `dregg-bounty-board` / `dregg-gallery` /
  `dregg-privacy-voting` / `compute-exchange`. NONE are in the workspace
  `members` list. NO `path = ".../apps/<x>"` dependency exists anywhere
  (`rg 'path = "(\.\./)*apps/' --glob Cargo.toml` → empty). Last modified
  2026-05-26 (vs `starbridge-apps/` lib.rs at 2026-06-10).
- **Replacement named:** `starbridge-apps/` (package names `starbridge-*`, the
  workspace members the `node`/`discord-bot` crates path-depend on). The
  migration is documented in `preflight/src/checks/apps.rs:3-5`
  ("The old `apps/gallery` and `apps/identity` checks were retired in the
  `apps/ → starbridge-apps/` migration") and landed in commit `90b34bbfa`.
- **`apps/lending`, `apps/orderbook`, `apps/stablecoin`** contained only
  gitignored `CLAUDIT.md` scratch files (no code).
- **Only residual reference:** `scripts/no-unchecked-auth.sh` allowlists
  `apps/gallery/src/artwork.rs`, `apps/gallery/src/settlement.rs`,
  `apps/bounty-board/src/payment.rs`. The script iterates `git ls-files '*.rs'`,
  so the now-deleted paths simply never appear → no breakage; those 3 allowlist
  lines are now dead and can be tidied (cosmetic follow-up, not load-bearing).
- Comment-only mentions in `cell/src/ring_closure.rs:32` and
  `discord-bot/src/main.rs:10` (doc comments, not code references).

### 2. `benches/summary.rs` + empty `benches/` dir (DELETED)
- **Evidence:** the file's own header says
  `cargo run -p dregg-bench-summary` — but `dregg-bench-summary` is NOT a
  workspace member and `benches/` has no `Cargo.toml`. Root `Cargo.toml` has no
  `[[bench]]` pointing at it (only `[profile.bench]`). Zero references
  (`rg 'benches/summary'` → empty). The live perf summary is `perf/` crate
  (`perf-summary` bin → `src/bin/perf_summary.rs`).

### 3. Root stale build/test logs (DELETED, 3 tracked files)
- `nextest.log` (74 KB, captured `cargo`/nextest output, 2026-05-26),
  `test_results.txt` (798 KB, captured warnings dump),
  `houyhnhnm.total.txt` (275 KB, scraped "Houyhnhnm Computing" web page — research
  scratch behind the `docs-old/HOUYHNHNM-*.md` comparison study).
- **Evidence:** referenced only by stale archive docs
  (`docs-old/`, `old-docs/2026-05-26/*-AUDIT.md`); NOT referenced by
  `paper/`, `paper2/`, `site/`, `scripts/`, or `.github/`.

---

## DEAD / ORPHAN (not deleted — judgment / off-limits / gitignored)

### `Metatheory/Dynamics/Production.lean` — ORPHAN Lean module — NEEDS-REVIEW
- Zero importers: `grep -r "Dynamics.Production"` hits only the file's own
  header. Not imported by `metatheory/Dregg2.lean` nor any other `.lean`.
- **Not deleted:** metatheory is the active "jam"; a single un-imported module is
  likely live-WIP, not heritage. Main-loop decision.

### Gitignored scratch/build dirs (NOT tracked — left as-is)
- `target-swaplane/` (stray cargo target dir from the swap lane; `.gitignore` has
  `/target-swaplane`), `web/` (3.7 GB Lean checkout scratch; `.gitignore` `/web`),
  `states/` + `spec/states/` (TLA+ TLC model-checker output dumps; `.gitignore`
  `states/` and `spec/states`), `site/pkg/`, `sdk-ts/dist/`.
- These are already gitignored build/scratch — not tracked cruft. Safe to `rm`
  locally anytime but they carry no repo weight. Listed for completeness.

---

## SUPERSEDED / PARALLEL (census — needs deliberate action)

### `ts-sdk.archived/` → `sdk-ts/` — NEEDS-REVIEW (likely SAFE-DELETE)
- Self-tombstoned: `ts-sdk.archived/README.md` line 1 = "ts-sdk — ARCHIVED
  2026-05-25 … superseded by `../sdk-ts/` (`@dregg/sdk`)". The live TS SDK is
  `sdk-ts/`.
- Zero code references. **Weak live reference:** `site/src/learn/developers/
  typescript-sdk.html:29` mentions the directory NAME in prose ("…has been
  archived as `ts-sdk.archived/`") — not a hyperlink, just historical text.
- **Verdict NEEDS-REVIEW** (not auto-deleted): the only thing keeping it is that
  prose mention. Deleting it + dropping the site-prose sentence is a clean
  follow-up. Includes a committed `node_modules/` — deleting reclaims real space.

### `gen_kimchi.rs` (dregg-dsl) — KEEP (still wired)
- Despite the "kimchi deleted" note (which concerned the *circuit* kimchi
  backend), `dregg-dsl/src/gen_kimchi.rs` (250 lines) is STILL imported and
  called: `dregg-dsl/src/lib.rs:22` (`mod gen_kimchi;`), `:66`, `:128`
  (`gen_kimchi::generate_kimchi(&ir)`). A live DSL codegen target → KEEP.
  (Possible future heritage review if the kimchi DSL backend is retired, but it
  is referenced today.)

---

## STALE-DOCS ARCHIVES (census — NEEDS-REVIEW, deliberate history kept)

These are **deliberately-preserved** history directories with explicit
"not-authoritative" disclaimers, not accidental cruft. Per the "when in doubt do
not delete" rule and "do not delete memory files," they are left for an
ember-decision rather than mass-pruned. None are referenced by code/CI/README.

| Dir | Tracked files | Self-declared status | Verdict |
|---|---|---|---|
| `docs-old/` | 79 | `README.md`: "archived design & audit notes (NOT authoritative)… Do not treat anything here as current ground truth" | NEEDS-REVIEW (deliberate archive) |
| `old-docs/` | 43 | dated `2026-05-26/` snapshots of design drafts | NEEDS-REVIEW |
| `docs-history/` | 10 | design graveyard (STAGE-3/7 plans, feasibility studies) | NEEDS-REVIEW |
| `.docs-history-noclaude/` | ~38 | historical decision record; prior audits explicitly say KEEP | KEEP |
| `plans/` | ~35 | mix of completed + aspirational designs; `wire/src/lib.rs` cites `plans/unified-lace-propagation.md` | KEEP (some live cross-refs) |

`docs/`, `docs/rebuild/`, `audits/` = LIVE-KEEP (current docs + active soundness
ledger). `pdfs/` and `paper`/`paper2`/`site` = LIVE.

**pyana references:** only `docs/rebuild/cand-D-choreography.md` (comparative
design note) and `metatheory/docs/rebuild/_RECOVERED-DESIGNS-2026-06-02.json`
(recovery artifact). Both are intentional historical comparisons, not stale code.
No source file uses the old name.

---

## OFF-LIMITS CRATES — CENSUS ONLY (no deletions made)

Per brief, these active crates were censused but NOT pruned. No large dead/parallel
blocks found inside them in this pass; notable items:

- `node/`, `turn/`, `cell/`, `circuit/`, `sdk/`, `coord/` etc.: all live
  workspace members with healthy reference counts; no orphan modules surfaced in
  the reference sweep. (A deeper per-module dead-code pass is a separate lane.)
- `dregg-discharge-gateway` (workspace member, NOT off-limits): has 0 in-workspace
  dependents — but it is a **standalone bin+lib service**
  (`[[bin]] discharge-gateway` + `[lib] discharge_gateway_service`), so leaf-ness
  is by design, NOT death. KEEP.
- Standalone (excluded-from-workspace) crates `pg-dregg/`, `dregg-tui/`,
  `starbridge-v2/`, `chain/`, `wasm/`, `sdk-py/`: all intentionally separate
  workspaces (feature-unification / dep-conflict / toolchain isolation), each
  documented in its own `Cargo.toml` header. All LIVE.

---

## RANKED NEEDS-REVIEW PRUNE PLAN (deliberate main-loop action)

1. **`ts-sdk.archived/` (DELETE candidate, HIGH confidence)** — self-tombstoned,
   superseded by `sdk-ts/`, only a site-prose mention blocks it. Delete the dir +
   the one sentence in `site/src/learn/developers/typescript-sdk.html:29`.
   Reclaims a committed `node_modules/`.
2. **Doc archives `docs-old/` + `old-docs/` + `docs-history/`** (~132 files) —
   deliberate non-authoritative history. Decide: keep as cold history vs prune.
   Zero code/CI/README references; safe to delete whenever ember wants the
   history gone. (Left intact this pass — deliberate archive, not accidental.)
3. **`Metatheory/Dynamics/Production.lean`** — confirm it is abandoned WIP (zero
   importers) vs intended future import, then delete or wire it in.
4. **`scripts/no-unchecked-auth.sh` allowlist tidy** — remove the now-dead
   `apps/gallery/*` and `apps/bounty-board/*` lines (cosmetic; script unaffected).
5. **Gitignored scratch (`target-swaplane/`, local `web/`, `states/`)** — `rm`
   locally to declutter the working tree; no repo impact (already untracked).
6. **`plans/` triage** — mark completed designs vs aspirational integrations
   (evm/mina/midnight bridges); keep code-grounded reviews. Lower priority.
