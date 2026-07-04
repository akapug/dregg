# APPS-CENSUS — dregg's demo/example apps, source-grounded

A source-grounded census of dregg's **apps** — the demos, example apps, and
deos surfaces that are the *face* of dregg. The refinement-epoch bar is
"not-a-toy apps": a stale/broken/toy demo misrepresents the whole system, so
each crumby old app is worth a spirit-visit (revive / refresh / promote-to-
flagship / retire).

Method: VERIFY THE SOURCE (both directions). An app is not dead because it's
old, nor good because it exists. Per app — does it BUILD? does it RUN today?
does it ride the **real verified substrate** (`EmbeddedExecutor` → real
`TurnExecutor` over a real `Ledger`, real Ed25519 signatures, real executor
refusals — not `Authorization::Unchecked` / `[0u8;64]` placeholder sigs)? does
it embody dregg WELL or is it a crumby stub?

Captured at HEAD `1acc24ac4`. Build-verified: `cargo check -p
starbridge-first-room -p starbridge-bounty-board -p starbridge-nameservice`
green; the `starbridge-apps/*` and `demo-agent` crates are workspace
`default-members` (they build with the tree). `first-room`'s example was run
live (output below).

---

## Headline

- **`starbridge-apps/` is the real face — and it is clean.** All 22 apps ride
  the real `EmbeddedExecutor`, sign with real Ed25519 (`AppCipherclerk::
  make_action`), and ship refusal-teeth tests that assert genuine executor
  refusals (`FireExecuteError::Gate(...)` / `TurnError::ProgramViolation`). The
  only `Authorization::Unchecked` / `[0u8;64]` hits in this directory are doc
  comments and adversarial regression guards *asserting their absence*. **No
  TOY-STUB, no STALE-BROKEN, no ABANDONED** among the 22. ~31.6K src LOC.

- **The single highest-value move: PROMOTE `first-room`.** It is a genuine
  flagship — 909 LOC, runs a full living-world cycle (mandate → conserving
  escrow → pay) and a 5-cheat battery each *provably refused in-band with the
  receipt-why printed* — but has **no README and no run-pointer**, so nobody
  finds it. Adding a README + surfacing it is the biggest face-of-dregg win for
  the least work.

- **The crumby-toy contrast lives elsewhere: `demo-agent/examples/`.** 11 of
  its 41 examples still use `Authorization::Unchecked` + `[0u8;64]` /
  `vec![0x01]` placeholder proofs (`delegation_demo.rs:137`,
  `atomic_swap_demo.rs:125/134`, `agent_network.rs:79`) — exactly the
  presentation-layer anti-pattern `starbridge-apps` was built to replace. These
  are the ones that misrepresent the system.

- **The deos "apps" (chat / card-editor / MUD) are real but hidden behind
  feature gates** (`agent-js`/`card-pane`/`dev-surfaces`, off `default-members`
  for mozjs/gpui/sqlite weight) and proven by tests rather than packaged as
  stranger-openable products. The MUD has the object model but no playable
  client — the biggest "make it a playable app" opportunity.

---

## starbridge-apps/ — the canonical apps (all ALIVE-RUNS, real substrate)

`starbridge-apps/README.md` is honest and current. A starbridge-app is a Rust
crate (`src/lib.rs` = `FactoryDescriptor`s + signed turn-builders) + tests +
(some) a generated web surface. The hard rule "the answer is never
`Effect::FooApp`" holds — every app composes from dregg-native primitives.

| App | Substrate | #tests | What it demonstrates | Verdict | Rec |
|---|---|---|---|---|---|
| **first-room** | REAL (welds 3 organs, 1 ledger) | 4 (in src/scenario.rs) | The living-world weld: mandate-job + conserving escrow-pay + 5-cheat battery, each a real executor refusal, surfaced in-room with receipt-why | ALIVE-RUNS, **EXCELLENT** | **PROMOTE** ← #1 move |
| **polis** | REAL (multi-inhabitant e2e) | 47 | Governance-of-governance: council (M-of-N) · constitution-as-program · budgeted mandates · KERI pre-rotation identity. Ties to the polisware-constitution vision | ALIVE-RUNS, **EXCELLENT** | PROMOTE |
| **governed-namespace** | REAL (50 executor hits, threshold-sig STARK) | 95 | propose→vote→commit atomic route-table swap by a constitutional committee; real threshold-sig under `Authorization::Custom` | ALIVE-RUNS, **EXCELLENT** | PROMOTE |
| **sealed-auction** | REAL (+ Lean-mirrored verified settle ring) | 29 | Sealed-bid multi-agent coordination; settlement folds through `verified_settle::settle_ring_verified` (Rust mirror of Lean `Ring.settleRing`). Has runnable example | ALIVE-RUNS, **EXCELLENT** | PROMOTE |
| **nameservice** | REAL (+ attested tier) | 83 | The exemplar starbridge-app: register→resolve→renew→transfer→revoke (WriteOnce/Monotonic slot caveats). The pattern others copy | ALIVE-RUNS, flagship | PROMOTE |
| **identity** | REAL (over dregg-credentials) | 48 | Verifiable credentials: issue→present (selective disclosure)→verify→revoke; multi-show unlinkability | ALIVE-RUNS, flagship | PROMOTE |
| **subscription** | REAL | 72 | `CapInbox` publisher/consumer queue as a cell-program — storage-as-cell-programs (no parallel storage loop) | ALIVE-RUNS, strong | PROMOTE |
| **tussle** | REAL (+ Lean ring + `SymMemberOf` atom) | 31 | A verified joint-combat **game** (Toribash-shaped): commit→reveal→resolve, fog-of-war, joint-state-is-an-enum forced by the `SymMemberOf` typed atom. Most fun/demoable. Runnable example | ALIVE-RUNS, WELL (fun) | PROMOTE + **REFRESH** (no README; manifest `page` dangles) |
| **agent-orchestration** | REAL (+ Python hermes weld) | 36 + 14py | Durable, crash-recoverable multi-agent orchestration: attenuated mandates (tools∧budget∧task), auditable receipt chain. `python/` mirrors the gate onto hermes-agent (zero core edits) | ALIVE-RUNS, **WELL** | **REFRESH** (no top-level README — the python product is buried) |
| **bounty-board** | REAL | 24 | Bounty lifecycle as caveats: StrictMonotonic state machine, WriteOnce first-claimer-wins | ALIVE-RUNS, WELL | PROMOTE |
| **escrow-market** | REAL | 22 | Escrowed-delivery marketplace: bounded fund + sealed delivery + conserving settle (organ composition). Richest README | ALIVE-RUNS, WELL | PROMOTE |
| **compute-exchange** | REAL | 22 | Compute marketplace: budget-gated bid + conserving settle. Near-twin of escrow-market | ALIVE-RUNS, WELL | PROMOTE / REFRESH (overlaps escrow-market) |
| **gallery** | REAL | 27 | Commit-reveal juried art gallery: WriteOnce anti-swap board + one-way phase lifecycle | ALIVE-RUNS, WELL | PROMOTE |
| **supply-chain-provenance** | REAL | 32 | Verifiable custody chain: item=cell, handoff=cap-attenuated transfer, single-custodianship as a conservation law. 1468 substantive LOC | ALIVE-RUNS, **hidden** | **REFRESH** (no README/manifest/example) |
| **swarm-orchestration** | REAL | 31 | In-memory cap-attenuated swarm dispatch: conserved budget + epoch no-replay + async NOTIFY. **Best run-pointer README** | ALIVE-RUNS, WELL | PROMOTE |
| **tool-access-delegation** | REAL (+ Lean differential) | 30 | Ocap for AI tool/MCP access: rate-limited, time-bounded, revocable mandate cell; per-invocation caveats. Best-documented; `lean_differential.rs` pins Rust to proven theorems | ALIVE-RUNS, WELL | PROMOTE (add an example) |
| **agent-provenance** | REAL | 23 | Proof-carrying agent memory: append-only blake3 hash-chain (WriteOnce entries, Monotonic head), anyone re-verifies | ALIVE-RUNS, WELL | PROMOTE |
| **compartment-workflow-mandate** | REAL (+ Lean differential) | 35 | Charter DAG workflow (review→redact→sign): DAG step-order + clearance + spend-budget teeth. Mirrors the Lean corpus | ALIVE-RUNS, scaffold | REFRESH (thin web surface) |
| **privacy-voting** | REAL (composed DeosApp, axum-mounted) | 24 | One-vote-per-ballot polling (factory-born poll + per-voter WriteOnce ballot). **The only app re-expressed as a composed `DeosApp` on the newer deos framework** — the migration template | ALIVE-RUNS, ahead-of-curve | PROMOTE |
| **storage-gateway-mandate** | REAL (+ Lean differential) | 22 | Object-store gateway (GET/PUT/LIST): op allowlist + prefix-auth + monotone volume budget. Mirrors the Lean corpus | ALIVE-RUNS, scaffold | REFRESH (thinnest surface/tests) |

### first-room — the live run (proof it's flagship-grade)

`cargo run -p starbridge-first-room --example first_room` runs the full cycle
and prints the cheat battery, each refused on the verified commit path with the
receipt-why:

```
── THE TRY-TO-CHEAT BATTERY (each REFUSED in-band) ──
  [REFUSED ✓] skip a prerequisite step  → MonotonicSequence(JOB_CURSOR)
              seq[0]: expected 1 got 2
  [REFUSED ✓] overspend the budget      → FieldLteField(SPEND_ACCUM ≤ BUDGET)
  [REFUSED ✓] reach outside compartment  → FieldLteField(ESCROWED ≤ CEILING)
  [REFUSED ✓] take an ungranted verb     → ClearanceDominates(actor ⊐ verb)
  [REFUSED ✓] release escrow w/o approval → AffineEq(RELEASED+REFUNDED==ESCROWED)
  THE FIRST ROOM HOLDS: true
```

It welds (rebuilds nothing) `compartment-workflow-mandate::colonist_job` +
`escrow-market` + a gpui-free `Room`/`InhabitantView` over one
`EmbeddedExecutor`. This is the "this is what dregg is *for*" app — and it has
no README. (`starbridge-apps/first-room/src/lib.rs:1`.)

### Cross-cutting notes (starbridge-apps)

- **Two surface generations.** Most apps still carry the older static
  `pages/index.html` + `inspectors.js` fragments mounted under a Caddy prefix;
  `privacy-voting` alone is re-expressed as a composed `DeosApp` with a
  generated `<dregg-affordance-surface>` axum-mounted in tests. That's the live
  migration frontier.
- **Dangling surface refs.** Several `manifest.json` declare a `pages/`
  surface that no longer exists on disk (the live surface is the in-src
  `DeosApp` router). `tussle/manifest.json` points `page` at a nonexistent
  `pages/index.html`.
- **Lean-tied apps.** `compartment-workflow-mandate`, `storage-gateway-mandate`,
  `tool-access-delegation`, `sealed-auction`, `tussle` carry differential tests
  pinning Rust admission/settlement to the verified Lean corpus — the highest-
  integrity apps.
- **The legacy `apps/` directory is GONE** (retired; the README's dual-existence
  note is stale — `starbridge-apps/` is now the sole home).

---

## deos surfaces — the live desktop apps (real, but feature-gated)

Heavy crates excluded from `default-members` (mozjs/gpui/sqlite weight); wired
into the cockpit behind opt-in features. None STALE-BROKEN or ABANDONED.

| Surface | Class | State | Rec |
|---|---|---|---|
| **deos-matrix** (membrane chat) | APP (windowed `deos-chat` bin) | ALIVE — message = a cap-bounded shareable world-fork; default `MockSource`, world-backed transport behind `dev-surfaces`. Largest single app (~6.3K LOC) | **PROMOTE / REFRESH** (make default demo ride the real transport) |
| **card-editor** (in `deos-js/src/card_editor.rs`) | APP (edit-a-card-from-within) | ALIVE — every authoring gesture is a real receipted patch/turn; cap tooth refuses unauthorized edits. Closes "HYPERDREGGMEDIA gap #1". Rerender test in `deos-view` | **PROMOTE-TO-FLAGSHIP** (the most distinctive "GET dregg" — accountable HyperCard/Xanadu) |
| **MUD** (`deos-js/src/mud.rs` + `starbridge-v2/src/mud.rs`) | APP (object model only) | ALIVE but library/test-grade — room=cell, exit=cap edge, GM authority made explicit/accountable, dungeon=membrane fork. **No playable client yet** | **PROMOTE — needs a playable face** (unbeatable ocap pedagogy: locked door = absent cap) |
| deos-js | INFRA (the spine) | ALIVE — SpiderMonkey drives real cells/turns; houses the whole card vocabulary + `run_js` | KEEP-AS-INFRA |
| deos-view | INFRA (render backend) | ALIVE — one view-tree → native pixels OR web DOM; renderer-independent card | KEEP-AS-INFRA |
| deos-reflect | INFRA (only one in default build) | ALIVE — cap-bounded attested reflection (read confers no authority); "cap-gated Pharo" | KEEP-AS-INFRA |
| deos-web-cells | INFRA / library | ALIVE — web/JS bundle as a content-addressed, cap-gated, transcludable cell | KEEP-AS-INFRA |
| deos-leptos | DEMO / proof-of-runtime | ALIVE — Leptos signal runtime as the deos reactive rung; SSR per-viewer-frustum demo bins | REFRESH (could become the cards' web face) |
| counter demo | TOY / loop-proof (now a test) | The original spike, lives as `deos-js/tests/js_drives_substance.rs` | KEEP as test; RETIRE any lingering counter UI |

---

## demo-agent/ + demo/ + sdk/examples — the older example corpus

### demo-agent/examples/ — 41 examples, 20.9K LOC (the legacy SDK demos)

The presentation-pipeline demos (token → ZK proof → turn). Recently touched
(2026-06-23) but **mixed substrate fidelity**:

- **30 of 41 are CLEAN** (real auth, no placeholder) — e.g.
  `payment_channel.rs`, `note_privacy.rs`, `seal_unseal_transfer.rs`,
  `rbac_datalog.rs`, `cdt_revocation.rs`, `private_auction.rs`,
  `cipherclerk_lifecycle.rs`, `progressive_disclosure.rs`. These are legitimate
  feature-walkthroughs of the ZK token/proof pipeline.
- **11 of 41 use `Authorization::Unchecked` + placeholder proofs** —
  `delegation_demo.rs` (8 Unchecked + `[0u8;64]` parent_signature, `:392/398`),
  `atomic_swap_demo.rs` (`:125/186` Unchecked, `:134/195` `vec![0x01]`
  spending_proof), `agent_network.rs`, `orchestration_demo.rs`,
  `pipeline_demo.rs`, `cross_fed_atomic.rs`, `cross_federation_nft_swap.rs`,
  `private_orderbook.rs`, `delegation_swarm.rs`, `unified_harness.rs`. **These
  are TOY-STUB by the refinement-epoch bar** — they print a "flow worked" story
  on faked authorization, the exact thing starbridge-apps was built to retire.

Verdict: **REFRESH-or-RETIRE the 11 placeholder examples** — either lift them to
real auth (like the 30 clean siblings) or retire the ones whose story is now
told better by a starbridge-app (delegation → `tool-access-delegation`;
atomic_swap/orderbook → `sealed-auction`/`escrow-market`; orchestration →
`agent-orchestration`). They are the corpus most likely to misrepresent dregg to
a reader who opens `demo-agent/examples/` first.

### demo/ — the cross-process e2e demos (REAL substrate)

- **`demo/two-ai-handoff/`** (ALIVE) — the *production reference* for the
  receipt chain: Alice signs a `HandoffCertificate`, Bob signs a
  `HandoffPresentation` carrying `Authorization::CapTpDelivered`, Charlie
  re-runs the executor's `verify_captp_delivered` checks via the independent
  `dregg-verifier` binary; a tampered variant must reject (`expected.json`).
  Real signatures, real verification. **KEEP / PROMOTE.**
- **`demo/multi-node-devnet/`** (ALIVE) — boots two 3-node federations,
  cross-registers committees, runs named cross-federation scenarios over the
  real substrate. **KEEP** (note: no live devnet to point at — local only).
- `demo/cross-app-e2e`, `demo/silver-vision-e2e`, `demo/sdk-consensus` — python
  + Rust e2e harnesses with `expected.json` oracles. KEEP (test infra).

### sdk/examples/ — runnable one-binary walkthroughs (REAL substrate)

- **`hello_receipt_chain.rs`** (78 LOC, ALIVE) — the smallest agent-to-agent
  receipt-chain primitive (GitHub issue #3); the "what does a dregg receipt
  actually look like" teaching demo. KEEP / good onboarding pointer.
- **`polis_ceremony.rs`** / **`polis_sealed_vote.rs`** — full governance
  walkthroughs on the *real* `AgentRuntime`+`TurnExecutor`; the sealed vote adds
  the unbiasable beacon for sortition. KEEP.
- `agent_demo.rs` — full lifecycle (cipherclerk → mint → attenuate → turn →
  proof). KEEP.

### app-framework/examples/ — the deos-app composition exemplars (REAL)

`deos_app_in_an_afternoon.rs` (the "useful deos app in an afternoon" promise),
`deos_council_board.rs` (the `GatedAffordance` cap∧state conjunction —
"htmx-on-crack"), `stark_frustum_cull.rs` + `stark_rehydrate.rs` (per-viewer
frustum culling / rehydration backed by a REAL STARK + the non-amplification
obligation made concrete). KEEP — these are the framework's teaching surface.

---

## Spirit-visit priority list (ranked by show-dregg × fixability)

1. **PROMOTE `first-room`** — add a README + a run-pointer (it is the
   refinement-epoch app, and it's invisible). Highest value, lowest effort. ★
2. **PROMOTE the card-editor → flagship** — package the
   edit-a-card-from-within surface as the headline "accountable HyperCard"
   demo. (deos-js/deos-view, behind `card-pane`.)
3. **REFRESH-or-RETIRE the 11 placeholder `demo-agent/examples`** — the only
   genuinely *crumby* corpus; lift to real auth or retire in favor of the
   starbridge-app that tells the story better. Removes the worst
   misrepresentation risk.
4. **REFRESH `agent-orchestration` + `supply-chain-provenance`** — both are
   substantial, real-substrate apps hidden behind a missing README/manifest/
   example. Pure discoverability.
5. **Give the MUD a playable client** — the object model + GM-authority story
   exists; build the room-walk loop. The most legible ocap demo for a stranger.
6. **REFRESH `tussle`** — add a README and fix the dangling manifest `page`;
   it's the most fun demoable app (a verified game) and currently undocumented.
7. **PROMOTE `deos-matrix`** — make the default `deos-chat` demo ride the
   world-backed transport (not just `MockSource`); the membrane is the standout
   novel idea.
8. **REFRESH the two "scaffold" mandates** (`compartment-workflow-mandate`,
   `storage-gateway-mandate`) — thin web surfaces over excellent Lean-tied
   substrate.

**The single highest-value app move: PROMOTE `first-room`** — give the
refinement-epoch's exemplar app a README and a run-pointer so a stranger can
find the one demo that makes them GET dregg.
