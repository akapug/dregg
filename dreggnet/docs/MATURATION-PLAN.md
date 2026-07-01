# MATURATION PLAN — the DreggNet + dregg master roadmap

The single prioritized roadmap for **maturing, stabilizing, measuring, optimizing,
and deploying** DreggNet (the orchestration/hosting plane) + dregg (the AGPL
substrate). It synthesizes the four under-wired catalogs + the red-team pass into
one accountable burn-down across five axes, and — critically — marks which work an
**overnight autonomous `/goal` can safely do unattended** versus which needs
ember's reviewed go.

This is a DESIGN doc: it sequences and classifies, it does not itself build. The
lanes draw from it; nothing here is a claim that the work is done.

> **How an overnight `/goal` uses this.** Read §6 (the autonomy classification)
> first — it is the spec for a reliable all-night run. Pick the next OPEN item
> from the **SAFE-AUTONOMOUS-TONIGHT** set (§6.1), do it green-gated and
> reversible, commit it, update HORIZONLOG + this plan's status column, and move
> to the next. Never touch a **REVIEWED-GO** item (§6.2) without ember in the
> loop. The discipline: *build + prove + test + stage* freely; *flip + deploy +
> re-roll* only with a human.

Dated 2026-06-29. Grounded to HEAD across both repos. Status columns are
point-in-time — verify CODE vs HEAD before relying on a row.

---

## 0. Companion docs (read these; this plan references, it does not duplicate)

| Doc | What it is | Axis it feeds |
|---|---|---|
| `docs/RED-TEAM-FINDINGS.md` | the adversarial security pass (criticals + HOLDS) | Stabilize (§1) |
| `docs/UNDER-WIRED-parity.md` | executor↔Lean under-enforcement catalog | Stabilize (§1), Burn-down (§5) |
| `docs/UNDER-WIRED-circuit.md` | deployed-VK / light-client gaps (G1–G9) | Burn-down (§5), VK epoch |
| `docs/UNDER-WIRED-features.md` | built-but-not-live census (#1–#32) | Burn-down (§5) |
| `docs/NAMED-RUNGS.md` | the accountable named-rung burn-down (rows 1–32) | Burn-down (§5) |
| `breadstuffs/docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` | **the VK-EPOCH-DESIGN lane** — the soundness core for the capacity/satisfaction welds + the flag-day shape | Burn-down (§5) |
| `breadstuffs/docs/PERF-CHARACTERIZATION.md` | **the WORKLOAD/measure plan** — bench inventory + the WIDE/VERTICAL/FEDERATION scaling plan + targets | Measure (§3), Optimize (§4) |
| `breadstuffs/metatheory/docs/CELL-PROGRAM-LANGUAGE.md`, `docs/deos/{DERIVATIVE-MATCHING-DESIGN,DOCUMENT-LANGUAGE}.md` | **the LANGUAGE-EXEC strands** — cell-program grammar, derivative matching, the document language | Burn-down (§5) |
| `docs/{MONITORING,OPERATING,GO-REAL,TESTING,COMPUTE-TIERS,ORCHESTRATION-LOOP}.md` | the operate-it / run-it / measure-it runbooks | Deploy (§2), Measure (§3) |
| `runbooks/{UPGRADE,DEPLOY,FEDERATION,INCIDENT-RESPONSE,DISASTER-RECOVERY,SECRETS,KEY-MANAGEMENT,COMMITTEE-CHANGE,NODE-OPS,...}.md` | the operator runbooks | Deploy (§2) |
| `breadstuffs/HORIZONLOG.md` (OPEN-BURN-DOWN, ~L6375) | the standing-practice live log | all |

> Note on the three "landing in parallel" siblings the brief names: **VK-EPOCH-DESIGN**
> is `VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`; **WORKLOAD-TEST-PLAN** is
> `PERF-CHARACTERIZATION.md`; **LANGUAGE-EXEC-PLAN** is presently distributed across
> the three language strands above (no single standalone file yet). This plan cites
> them; it does not restate their internals.

---

## 1. STABILIZE — make it solid

The "no known soft underbelly" list. Most red-team CRITICALs are already FIXED
(CAP-1, CAP-FACET-1, SBX-1/2/3, GW-4a, LEASE-1a, LEASE-3, F1, BR-1/2/3); the
residue below is the HIGH-tier trust-anchoring, the parity tail, the fail-open
startup gate, and the soak/flake hygiene that earns the word "stable."

### 1.1 The HIGH red-team residuals (live, code-side — SAFE to do tonight)

| ID | Fix (code + test, green-gated, reversible) | Effort | Autonomy |
|---|---|---|---|
| **LC-1** | web/light consumer must hold the committee keys + gate on `is_valid(known_keys)`; `has_quorum`/count-only must never be an acceptance gate (`starbridge-web-surface/src/web_of_cells.rs`) | S–M | SAFE |
| **LC-2** | pass the trusted committee to `verify_finalized_history`; count only signers in the set; anchor `participant_count` (`lightclient/src/lib.rs`) | M | SAFE |
| **LC-3** | wire a finality gate into the production wasm light client (legs 1+2 only today); rides LC-2's fix (`wasm/src/bindings_lightclient.rs`) | M | SAFE |
| **NODE-1** | anchor recovery's "expected" root to the federation-signed attested root (verify a quorum sig over `(height, ledger_root)`), not the self-stored unsigned redb root (`node/src/state.rs`, `persist/src/commit_log.rs`) | M | SAFE |
| **NODE-2** | persist a signed monotonic high-water mark; refuse a store below it (anti-rollback on boot) | M | SAFE |
| **MESH-2** | auth the node read API (`/api/cells`, `/api/cell`, `/api/receipts/*`, `/checkpoint/latest` are plain GETs today) — bearer or tailnet identity on reads. The bind-scoping half (`0.0.0.0`→`127.0.0.1`/overlay, drop `ports:` for `expose:`) is a **compose edit = deploy config** (REVIEWED-GO, §2) | S (code) | SAFE (code) / REVIEWED (compose) |
| **GW-1 / GW-2** | app-layer auth on the gateway machines API (`/v1/apps/{app}/…`); bind the lessee to the authenticated principal not the URL segment; close the `*.dregg.works`/`www` fall-through (`gateway/src/http.rs`, `webapp/src/hosting.rs`) | M | SAFE (code) |
| **F2** | back admission bonds with a verified locked-cell commitment (`admission.rs`) | M | SAFE |
| **WALLET-3** | move `dregg:subscribe` behind per-origin approval; don't deliver `receipt`/`activity` to unapproved origins | S | SAFE |
| **WALLET-4** | add the `walletExists()` guard + replace-confirmation to `recoverFromMnemonic` | S | SAFE |
| **LEASE-1b/1c/1d/2** | single authoritative balance with atomic reserve→decrement before dispatch; control-plane bounds the charge `min(reported, budget)`; global instance dedup; fuel-meter wasmi | M | SAFE |
| **LC-4 / LC-5 / F3–F5 / GW-1b / LEASE-4b / MESH-1/3** | the MED/LOW tail (full 8-felt finality anchor, real BLS in `is_valid`, dealer/MAC hardening, rotate committed bcrypt to a secret mount, checked i64 in the budget gate, ephemeral preauth keys) | S–M each | SAFE (code) / REVIEWED (the secret-mount + key-rotation deploy halves) |

### 1.2 The parity residuals (executor↔Lean — SAFE)

- **#1 CAP-FACET-1 — DONE-SINCE** (the direct cross-cell path now enforces the cap
  facet; `rejection_parity` green). Verify it stays pinned.
- **#2 xsort tie-break theorem** — make Rust `xsort` *be* the `(round,id)`
  comparator (predecessors always have a strictly smaller round, so the Kahn
  machinery is unnecessary), compare **ordered** sequences in the live differential
  (not sorted multisets), or discharge `xsort_kahn = xsortBy` as a Lean theorem.
  Closes the only honest-node *state*-fork window. SAFE (comparator + test low; the
  theorem is Lean-only).
- **#6/#7 the fail-open-when-Lean-unlinked startup hard-check** — add a startup
  hard-check that **refuses to serve turns / refuses to claim verified
  production+consensus** when the Lean archive is absent (`lean_available()` false),
  rather than degrading to Rust-only with a per-turn `warn!`. This is what keeps
  CAP-FACET-1's mitigation and the xsort dormancy real. SAFE (a config/startup gate,
  reversible; it only ever *refuses*, never relaxes).
- **#3/#4/#5 producer covered-set** — promote the covered-set root-agreement to a
  discharged Lean theorem **or** add a halt-on-divergence switch (today it installs
  Lean's root and logs); extend the producer differential to the 7 uncovered effect
  families + the note set. SAFE (theorem is Lean; the halt switch is a config gate).
- **#26 Rust executor agent-lifecycle admission gate** — reject
  `agent_cell.is_terminal()` at admission (both entries ~`execute.rs` L382/L1436);
  the spec already rejects via `cellLifecycleCanAuthor`. SAFE, small. *(Caution
  named in NAMED-RUNGS: don't touch untested Migrated-agent flows blindly.)*

### 1.3 Sustained-finality soak + nonce/round hygiene (SAFE to observe + pin)

There is no single "sustained-finality phase" doc; the property is the composition
of IVC #1 (whole-chain ordered binding, machine-proven), settlement soundness
(wired + green), monotone nonce (inexpressible non-monotone vector), and the live
n=2 BFT committee finalizing. The stabilize work is to **earn the word "sustained"
empirically**: a long soak of the live committee with `dregg_block_height` rising,
`dregg_validator_votes_total{voter}` advancing for both members,
`dregg_consensus_differential_divergence_total == 0`, and the τ-prefix shifts
absorbed by the identity cursor. SAFE to run + capture; any flake found becomes a
pinned regression test. (Round-production cadence + nonce monotonicity are already
enforced in code — the soak is verification, not new build.)

### 1.4 Known-flaky / gated-lane hygiene (SAFE)

`make test` is the offline-green gauntlet; the gated lanes (`test-pg`,
`test-verify`, `test-net`) skip cleanly. Stabilize work: stand up the Postgres lane
in CI (a service container, not a skip), de-`#[ignore]` the durable-resume-pg tests
behind it, and harden any test that depends on timing/network. SAFE.

### 1.5 The accumulated-fix redeploy (the bridge to §2)

Several landed fixes are **code-complete but not yet on the live edge** — they
take effect only on a redeploy: **GW-4a** (the `/api/op` ownership gate, bot is
live on the edge), the CAP/LEASE fixes in the node image, the genesis-baseline
recovery fix (`1a61dc16d`, NAMED-RUNGS #21). Shipping them is a **REVIEWED-GO**
deploy (§2) — the autonomous run prepares the image/binaries and the upgrade
script; the human runs the swap.

---

## 2. DEPLOY / AUTOMATE — turn the hand-cranking into a pipeline

The manual redeploy is the single biggest ops drag. Today (per `OPERATING.md`,
`runbooks/{UPGRADE,DEPLOY}.md`): build **off-box** (Mac `cargo zigbuild` for
gateway/cli/ops/webauth; persvati native for the node image — it links
`libdregg_lean.a` and **cannot** be cross-compiled — and the bot), ship via
`docker save|gzip|scp|docker load` + rsync, then on-box `docker compose up -d`
one service at a time in the order **postgres → node → gateway → bot → ops**. CI
(`.github/workflows/ci.yml`) runs four jobs — macOS service-stack `cargo test`,
Linux gateway `cargo build`, `fmt` (hard gate), `clippy` (advisory) — and **does
no deploy, no image bake, no registry, no multi-node test, no rolling-upgrade
validation**.

The phased pipeline (build the automation tonight; gate the prod-touching flips):

| Phase | Goal | Concrete work | Autonomy |
|---|---|---|---|
| **P1 — repeatable deploy script** | one command, no surprises | `deploy/staging/deploy.sh` already does build+ship+up; harden it into `deploy-edge.sh {build,ship,up,upgrade,verify}` covering all four pieces + a post-deploy smoke (`curl /health /status \| jq .dag_height`; cross-node faucet transfer) | SAFE to **author + dry-run**; the live `ship/up` is REVIEWED-GO |
| **P2 — image registry** | versioned, rollback-able artifacts | push `dregg-node` + `dregg-bot` to GHCR on a successful persvati build, tag by `git` short-sha; `.env` pulls by tag; rollback = prior tag (replaces `docker save/load`) | SAFE to author the workflow; enabling the push is REVIEWED-GO (registry creds) |
| **P3 — multi-node CI** | prove federation in CI | a `docker compose`/Kind harness that stands up an n=2 committee, validates finality over the mesh, runs `control/tests/go_real_loop.rs` + `bridge/tests/windowed_verified_read.rs` against **live** nodes (not stubs); gate on multi-node finality + verified-read success | SAFE (CI authoring + local validation) |
| **P4 — orchestrated rolling upgrade** | encode `UPGRADE.md` so a human can't fumble the order | `deploy-edge.sh upgrade <tag>` enforces postgres→node→gateway→bot→ops, graceful SIGTERM + `stop_grace_period`, waits each healthcheck, greps for STORE-INTEGRITY, keeps the prior tag for rollback; one-node-at-a-time committee discipline + Lean-archive-consistency assertion | SAFE to author; the live run is REVIEWED-GO |
| **P5 — bootstrap + secrets automation** | kill the manual key steps | webauth `dregg-authctl keygen`+`mint` as a first-boot entrypoint (if root pubkey empty); headscale ephemeral+single-use preauth keys (MESH-1) via a rotation cron; a `reroll-federation.sh` that signs/distributes a new `genesis.json` in quorum order | SAFE to author scripts; **running any rotation / committee re-roll is REVIEWED-GO** |
| **P6 — prod hardening** | staged rollout + auto-verify | canary a new node image on one homelab box, soak, then roll the edge; corruption alerter → INCIDENT-RESPONSE trigger; reboot-resiliency test in CI (hard-stop a node container, assert it recovers + finalizes within `start_period` + replay) | SAFE to author; the canary/prod rollout is REVIEWED-GO |

Cross-cutting deploy items already named: **node-image** (NAMED-RUNGS #4 — the
Lean-on-Linux builder, gates the staging end-to-end), **dregg-web-auth live
rewire** (deployed in parallel with basic-auth, fail-closed, break-glass token;
the switch to cap-only is a coordinated REVIEWED-GO), **`dregg.works` DNS+Caddy
live deploy** (NAMED-RUNGS #16, REVIEWED-GO — public surface), **private GitHub
remote** (NAMED-RUNGS #10 — `origin` now exists; ensure `dev` is pushed, SAFE).

---

## 3. MEASURE / BENCHMARK — characterize the cloud

Reference `PERF-CHARACTERIZATION.md` for the full inventory + plan + targets; this
section sequences it and ties it to the live o11y.

### 3.1 What the cloud must measure (the metric set)

Latency, throughput, cost-per-unit-work, tail under load, across:
**finality latency (end-to-end)**, **turn throughput at saturation**, **lease
lifecycle latency (open→fund→run→meter→reap) + leases/sec**, **per-cap-tier
workload latency (wasmi/wasmtime/native-CPython)**, **proof gen + verify time +
aggregate/fold throughput**, **gateway/webapp req/sec end-to-end**, **durable
checkpoint/resume cost**, **resource use per lease (CPU/mem/net)**, and the
**economy** (metered units, settlement). The kernel/proof floor is already
benched (`dregg-perf`'s 16 criterion benches + the per-crate suites); the
**DreggNet service layer has ZERO benches** — the largest gap.

### 3.2 The benchmark harness (SAFE to build tonight)

Execution order from `PERF-CHARACTERIZATION.md` §5, all SAFE (build + run on a dev
box / persvati, capture baselines, commit artifacts; reversible, no prod effect):

1. **DreggNet service-layer micro-benches** — `bridge` lease lifecycle, `durable`
   checkpoint/resume, `gateway`/`webapp` req/sec, per-tier workload latency
   (zero coverage today; highest value).
2. **The macro/throughput load-gen harness** — drives N concurrent
   leases/workloads/agents (the pay→lease→run→meter→reap loop; promote
   `perf/src/bin/orchestration_demo.rs`); reports throughput + p50/p99/p99.9 tail
   (reuse the `net/transport profile.rs` JSON/remote shape for the four-9s
   envelope).
3. **WIDE sweeps** — populated-ledger commitment (1→10³→10⁶ cells: does the
   sparse-Merkle + cap-root cache keep commitment O(touched)?), N-concurrent
   leases, per-tier saturation; instrument the named contention points (ledger
   `root()`, nullifier set, scheduler, gateway accept loop, durable append,
   cap-floor scan).
4. **VERTICAL saturation + flamegraphs** — confirm the predicted bottleneck per
   workload class (prover is the prime suspect at ~21,000× the executor); commit
   the flamegraph as an artifact per axis (profiled, not inferred).
5. **FULL baselines on persvati** — the existing `dregg-perf` suite only has a
   SMOKE baseline (`smoke-2026-06-22-m2max`); capture FULL on real hardware.
6. **FEDERATION** — modeled analytically now (per-node × N − gossip overhead);
   real multi-node bench DEFERRED to the fleet (REVIEWED-GO when the fleet exists).

### 3.3 The o11y completion (SAFE — config + code, reversible)

The Grafana stack exists (`deploy/observability/`: 9 dashboards — consensus,
protocol, compute, economy, bridge, security, cloud-health, hosts, cloud — plus
Prometheus rules `dreggnet.rules.yml` and node_exporter ×3). The native
`dregg_*` families are real (finality latency, divergence, validator votes,
blocklace depth/frontier, mempool pending, receipt-chain length, proof verify
duration). Named-remaining, all SAFE:

- **Dashboard panels:** an aggregated **turn-throughput** panel; a **per-tier
  proof-latency** breakdown; **end-to-end finality** (local decision → committed),
  not just first-vote→quorum; **per-lease settlement latency**; **per-tier
  workload latency** + **leases/sec**; a **per-resource cost** breakdown (compute
  vs storage vs network) beyond the aggregate `total_units_spent`.
- **Metric wiring:** `dregg_sandbox_denials_total` is registered but stays 0 — the
  deny-by-default lives in the exec plane (no Prometheus surface yet); wire it.
  Wire the **bridge-relayer status** source (`OPS_BRIDGE_URL`) so conservation /
  double-mint move from *un-observed* to *observed* (today they read un-observed,
  never a false all-clear — keep that property).
- **Alert tuning:** finality-latency has no alert (panel only) — add a
  threshold; revisit `HeightNotAdvancing` 30m (idle chains legitimately stall),
  `TurnRejectSpike` >20/10m, `PostgresConnectionPressure` ≥85%, `BackendDown` 5m.

---

## 4. OPTIMIZE — once measured, not before

Targets named by `PERF-CHARACTERIZATION.md` §4; the discipline is **measure →
flamegraph → confirm bottleneck → optimize that one thing**. Design the approach,
do not pre-optimize.

| Target | The lever (design, not a commitment) | Gate |
|---|---|---|
| **Heavy Lean build** | the node image's `libdregg_lean.a` is the long pole (the ~190MB libLean.a elaborator tail named in memory); the strip 179MB→75MB closure work is the source-split lane. Bounded build (`taskset -c 0-5 -j6` + earlyoom) is the operational mitigation today | measure build time/mem on persvati |
| **Proof time** | full prove ~147 ms/turn vs ~8 µs execute (~21,000×). Lever: admit interactively (~µs symbolic), prove **asynchronously** off the hot path, aggregate via recursion fold so a node sustains *prove-throughput ≥ admit-rate*, not per-turn proving. Confirm proving is never the latency a user feels | the macro harness + the async-proof histogram |
| **Gossip / sync efficiency** | the bounded gossip-stream + receiver backpressure already landed (`923becc66`); measure per-node bandwidth/CPU to converge vs federation size + churn (the FEDERATION axis) | fleet bench (REVIEWED-GO) |
| **Compute cold-start** | wasmtime Cranelift cold vs the `InstancePool` pre-pooled path (`bench_wasm_instantiate` shows the payoff); native-CPython subprocess spawn dominates short workloads | per-tier saturation sweep |
| **Commitment O(touched)** | confirm incremental commitment + sparse-Merkle + cap-root cache keep `Ledger::root()` cost in touched-cells, not total-cells, as the ledger grows | the populated-ledger WIDE sweep |

All of §4 is **SAFE to investigate + prototype** (bench, profile, draft an
optimization behind a flag, prove byte-identical); a change that **alters the
deployed VK or the wire** is REVIEWED-GO.

---

## 5. THE UNIFIED UNDER-WIRED BURN-DOWN (the four catalogs, deduped)

One prioritized master list. `DONE-SINCE` = closed since the catalog pass;
`OPEN` = live work; the **VK-epoch cluster** is the single biggest payoff and the
deliberately-gated, be-thoughtful zone (design + prove + stage freely; **flip with
ember**).

### 5.1 Tier A — small, high-value, SAFE (do these first, unattended)

| Item | Source | Status | Autonomy |
|---|---|---|---|
| CAP-FACET-1 direct-path facet gate | parity #1, red-team | **DONE-SINCE** | — |
| F1 voter-id dedup | red-team | **DONE-SINCE** | — |
| BR-1/2/3 bridge escrow-binding + non-vacuous conservation + RAM-mint demotion | red-team | **DONE-SINCE** (latent; pre-relayer) | — |
| SBX-1/2/3 wasmtime default-deny + fail-closed preopen | red-team, features #8/#9 | **DONE-SINCE** | — |
| LEASE-1a funded-lease gate + LEASE-3 durable settle ledger | red-team | **DONE-SINCE** | — |
| GW-4a `/api/op` ownership gate | red-team | **DONE-SINCE** (needs redeploy, §1.5) | — |
| #26 agent-lifecycle admission gate | NAMED-RUNGS, parity | OPEN | SAFE |
| #6/#7 fail-open startup hard-check | parity | OPEN | SAFE |
| #2 xsort `(round,id)` comparator + ordered differential | parity | OPEN | SAFE |
| LC-1/2/3 committee-anchoring | red-team | OPEN | SAFE |
| NODE-1/2 recovery root + anti-rollback | red-team | OPEN | SAFE |
| GW-1/2, F2, WALLET-3/4, LEASE-1b/c/d/2 | red-team | OPEN | SAFE (code) |
| #21 genesis-baseline recovery rollout | NAMED-RUNGS | OPEN | code DONE (`1a61dc16d`); rollout = REVIEWED-GO |

### 5.2 Tier B — medium, the live-money + verified-read enablers

| Item | Source | Status | Autonomy |
|---|---|---|---|
| **#12 pg-dregg proof-gate S3 flip** (one circuit line unblocks #11/#13/#18) | features | OPEN | the flip is VK-adjacent → REVIEWED-GO; the surrounding S1/S2 are SAFE |
| **#1–#3 wire the M2 privacy effects** (shielded transfer / multi-asset pool / ZK attestations) | features | OPEN | the Effect + executor admission gate + tests are SAFE; the **in-circuit witness / new selector = VK-affecting = REVIEWED-GO** |
| **#15 real `MeterTick` → Payable** (one Postgres txn = duroxide checkpoint + lease charge) | features | OPEN | SAFE (code + test over `pg-dregg`) |
| **#7 / #19 `dregg-verify` RPC transport** (the light-client receipt-log fetch) | NAMED-RUNGS, features | OPEN | the transport + decode are SAFE; **flipping `dregg-verify` ON as the deployed default = AGPL-derivative + workspace-lock = REVIEWED-GO** |
| #5/#17 Solana mainnet-real (geyser inclusion proofs) + mainnet relayer wire | NAMED-RUNGS | OPEN | the verifier is SAFE; deploying a live mainnet relayer = REVIEWED-GO |
| #6/#18 owned native/interpreter engine (Caged tier) + args threading; #14 owned microVM engine guest plane | NAMED-RUNGS, features #8 | OPEN | SAFE (code, hardware-gated tests skip cleanly) |
| #20–#22 the distributed loop (mesh overlay + deploy `dreggnet-provider` + persvati) | features | OPEN | code SAFE; **the fleet deploy + the live-edge operator step = REVIEWED-GO** |

### 5.3 Tier C — the VK epoch (the gated flag-day; DESIGN+PROVE+STAGE safe, FLIP reviewed)

The single coordinated rotation/VK epoch — batch it, design it once, flip it once,
**with ember**. Per `VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` + UNDER-WIRED-circuit
G1–G7 + NAMED-RUNGS 1/2/3/12/22/23.

| Item | Source | Status | The flip vs the staging |
|---|---|---|---|
| **G1 bridge foreign-proof binding** (fold built `bridge_action_air` into effect_vm + IVC) | circuit G1 | OPEN — highest soundness-value (real money), a *localizable* weld not a flag-day | the weld build is SAFE; the deployed-VK emit is REVIEWED-GO |
| **#23 umem VK epoch** (commit wide-welded VK + flip default + `umem_witness_enabled`) | NAMED-RUNGS, circuit G4 | OPEN — the domain-2 burn-down (one welded mint + resolve `OodEvaluationMismatch`) is the precursor | precursor + proofs SAFE; **the flip = REVIEWED-GO** |
| **#1/#2/#3 Gentian / capacity satisfaction welds** (tags 17/18/19 + the limb-24 layout flag-day) | NAMED-RUNGS, circuit G5/G7 | OPEN — keystones proven + Rust shadow green; the dedicated floor-digest limb + range-check + multi-limb-product gadgets + row-locality fix remain | gadget build + Lean SAFE; **the registry-wide flag-day = REVIEWED-GO** |
| **#22 Custom/proofBind VK weld** (gate `True→boundAt`, 4→8-felt lift) | NAMED-RUNGS, circuit G2 | OPEN — Lean half closed (`CustomApex`); deployed-VK epoch only | rides the same epoch — REVIEWED-GO |
| **G3 sovereign inner-transition proof** (sentinel-zero VK binding) | circuit G3 | OPEN — small, removes a sentinel-zero | the recursive verifier is SAFE; the bind = REVIEWED-GO |
| **#12 CommitBindsMMR Gap B** (weld `mroot` into the EPOCH commitment) | NAMED-RUNGS | OPEN — closes the trusted-root TOFU seam | rides the VK epoch — REVIEWED-GO |
| #6 G6 epoch-stamp write-forcing | circuit G6 | OPEN — low severity (commitment already binds) | descriptor cutover — REVIEWED-GO |

**SUPERSEDED / DONE-SINCE (do not re-climb):** #30 attenuate recompute (routing
would downgrade), #31 RefreshDelegation (12th WState field), #32
`∀ e, descriptorRefines` (assembled; residual = the terminal FRI/Poseidon2-CR
crypto floor, by-design).

### 5.4 Tier D — language-exec + the long tail

The LANGUAGE-EXEC strands (`CELL-PROGRAM-LANGUAGE.md` grammar atoms — 3 landed;
`DERIVATIVE-MATCHING-DESIGN.md` — Brzozowski Stage 3 landed, Stage 5 open research;
`DOCUMENT-LANGUAGE.md` — the patch-theory document core) plus the features long
tail (#23/#24/#25 conditional/pending/remote-eventual node wiring, #26 EVM
settlement, #27 deos-hermes live agent, #28–#31 cockpit/deos wiring, #32 the
owned interpreter/native engines). All SAFE (code + proof + test, no prod/VK
effect) except where a new selector or a live deploy is involved. Decision of
record (HORIZONLOG 2026-06-28): **NEVER language-as-wasm** — the stronger langs
want real owned CPython/Node engines, which are fail-closed seams today (the
owned engine is future work); only the owned wasmi `Sandboxed` tier genuinely
runs.

---

## 6. THE AUTONOMY SPEC — SAFE-AUTONOMOUS-TONIGHT vs REVIEWED-GO

The reliable-overnight-`/goal` contract. The dividing line: **reversibility + blast
radius**. If a step is green-gated, locally reversible (a `git revert`/flag flip
undoes it), and has no outward or money/key/consensus effect, it is SAFE. If it is
hard to reverse or reaches the live network, it is REVIEWED-GO.

### 6.1 SAFE-AUTONOMOUS-TONIGHT (do these unattended, green-gated, commit + log)

- **Lean proofs** — any `#assert_axioms`-clean theorem work: the xsort theorem
  (#2), the producer covered-set root-agreement (#3), the capacity-satisfaction
  rungs, the VK-epoch keystones. Pure substrate; no deploy.
- **Rust executor / library fixes with tests** — §1.1 (LC-1/2/3, NODE-1/2 code
  half, GW-1/2, F2, WALLET-3/4, LEASE-1b/c/d/2, the MED/LOW code tail), §1.2
  (#26, #6/#7 startup hard-check, the xsort comparator, the producer halt switch).
  Each lands with its regression test; the lib suites stay green.
- **Wiring built-but-not-live features at the executor/library layer** — the M2
  privacy Effects + admission gates (#1–#3), `MeterTick`→Payable (#15), the
  `dregg-verify` RPC transport + decode (#7/#19), the owned native/interpreter
  engine (Caged tier) + args (#6/#18), the owned microVM engine guest plane
  (#14), the conditional/pending node wiring
  (#23/#24/#25) — the *code + tests*, NOT the deployed-VK flip or the live deploy.
- **VK-epoch DESIGN + PROVE + BUILD + STAGE** — the gadgets, the staged
  descriptors, the Lean apexes, the domain-2 burn-down precursor (resolve the
  `OodEvaluationMismatch`), the producer that emits the welded trace. Everything
  **up to but not including** committing the VK + flipping the deployed default.
- **The benchmark + measure axes (§3)** — build every service-layer bench, the
  load-gen harness, the WIDE/VERTICAL sweeps, capture FULL baselines on a dev box /
  persvati, commit flamegraphs.
- **The o11y completion (§3.3)** — new Grafana panels, new/tuned Prometheus alert
  rules, wiring the sandbox-denial + bridge-relayer metric sources. Config + code,
  reversible.
- **Authoring the deploy automation (§2 P1–P6)** — write `deploy-edge.sh`, the CI
  workflows (image bake, multi-node CI, orchestrated upgrade), the bootstrap +
  rotation scripts; **dry-run + local-validate** them. Do not point them at prod.
- **Optimization investigation (§4)** — bench, flamegraph, prototype an
  optimization behind a flag, prove byte-identical. No wire/VK change.
- **Docs + HORIZONLOG + this plan's status columns** — keep the record current in
  the same breath as the work.
- **Repo hygiene** — push `dev` to the now-existing `origin` (NAMED-RUNGS #10);
  green CI.

### 6.2 REVIEWED-GO (needs ember's reviewed go — do NOT do unattended)

- **The VK flip** — committing the wide-welded / capacity / custom / umem VK and
  flipping the deployed default off the bare rotated + per-map leg. The whole VK
  epoch's *flag-day*. (Per memory's be-thoughtful scar: a kernel/effect/commitment
  change from thin context is exactly the forbidden move.)
- **Live-prod / staging deploys** — any `ship`/`docker compose up` against the
  edge or persvati, the redeploy of the accumulated fixes (§1.5), the node-image
  swap. Outward-facing; money + keys are live.
- **Genesis / committee / federation changes** — committee re-roll, `federation_id`
  change, `node.key` rotation, adding a committee member. Coordinated, breaks the id.
- **The live-edge operator step** — unlock the node + export its bearer + mint a
  funded execution-lease (NAMED-RUNGS #13). Money-moving.
- **Enabling auto-deploy-to-prod** — flipping any CI step from "build/test" to
  "ship to the live box," and pushing images to a real registry with creds.
- **`dregg-verify` ON as the deployed default** — an AGPL-derivative-work +
  workspace-lock decision (license/legal, not just code).
- **Bridge relayer / webhook DEPLOY** — the BR fixes are in; standing up a live
  relayer or webhook server (and the mainnet geyser path) is the gate.
- **Public-surface changes** — `dregg.works` DNS + Caddy live deploy, the Discord
  bot token go-live, the webauth switch to cap-only (drop basic-auth), any
  secret/key rotation run.
- **Anything that finalizes irreversibly on the live chain** — a real on-chain
  turn the network commits.

### 6.3 The nightly `/goal` loop recipe

```
loop until morning:
  1. orient: REORIENT → HORIZONLOG OPEN-BURN-DOWN → this plan §5 + §6.1
  2. pick the next OPEN item from §6.1 (prefer Tier A small/high-value, then the
     measure/o11y/automation-authoring lanes, then VK-epoch design+prove+stage)
  3. do it green-gated + reversible; land its regression test
  4. verify: targeted suite + `cargo fmt`; trust lane logs, no full-suite reruns
  5. commit (explicit paths, gpgsign-off ok when unattended); update HORIZONLOG +
     this plan's status column in the same commit-set
  6. if blocked by a REVIEWED-GO gate → write the design/stage to the doc, leave a
     crisp "ready for ember: <one line>" note, move to the next SAFE item
  never: flip a VK, ship to prod, re-roll the committee, move money, rotate a key
```

---

## 7. The one-paragraph through-line

The criticals are closed; the residue is HIGH-tier trust-anchoring (light-client /
node-recovery / mesh / gateway auth) + the parity tail (xsort theorem, the
fail-open startup hard-check, the agent-lifecycle gate) — all SAFE to land
tonight. The biggest ops drag is the manual redeploy; the cure is a phased
pipeline whose *authoring* is SAFE and whose *prod-touching flips* are REVIEWED-GO.
Measurement's micro-floor is complete and the Grafana stack is live; the gap is the
DreggNet service-layer benches + the macro load-gen harness + a handful of named
panels — all SAFE. Optimization waits on measurement. The under-wired burn-down
deduplicates to a small SAFE Tier-A, a money/verified-read Tier-B, the
deliberately-gated **VK epoch** (design+prove+stage freely, **flip with ember**),
and the language/long-tail. The reliable all-night run lives entirely inside §6.1
and never crosses into §6.2.
