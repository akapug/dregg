# Under-wired features — built but not live

A skeptic's census of machinery that EXISTS (a crate, tests, a demo, a proof)
but is NOT exercised by the live running path: behind a feature flag, never
called from a deployed binary, a stub/demo dressed as real, or proven-in-a-lib
without integration. Spans both repos — `dregg` (`breadstuffs`, AGPL core) and
`DreggNet` (the orchestration/hosting plane).

The rule of the census: *"there is a crate/test for X" is NOT "X runs live."*
It is honest in both directions — the genuinely-live surfaces are named too
([What IS live](#what-is-genuinely-live)).

## Classification legend

| tag | meaning |
|-----|---------|
| **LIVE** | called from a real deployed binary / executor / app path |
| **FLAG-GATED** | fully built + tested, switched off by a cargo `feature` (often a deliberate license/size/hardware gate) |
| **DEMO-STUB** | a stub / in-process twin / simulated path standing in for the real thing (honestly labelled in-code) |
| **LIB-ONLY** | complete + tested as a library, zero call sites in any binary/daemon |
| **DESIGNED** | spec / doc / scaffold only; no working implementation |

Effort: **S** = <1 day · **M** = 1–5 days · **L** = 1–2 weeks.

---

## Summary table

| # | Feature | Repo | Class | Value | Effort | The one gap |
|---|---------|------|-------|-------|--------|-------------|
| 1 | Shielded transfer prover (M2-a) | dregg | LIB-ONLY | high | M | no Effect variant / executor admission gate |
| 2 | Multi-asset shielded pool (M2-b) | dregg | LIB-ONLY | high | M | same as #1 |
| 3 | ZK attestations / membership-disclosure (M2-d) | dregg | LIB-ONLY | high | M–H | same as #1 |
| 4 | General shielded transition (M2-c) | dregg | DESIGNED | high | L | comment-only spec |
| 5 | Oblivious transfer (Chou-Orlandi) | dregg | LIB-ONLY | low* | M | no 2PC consumer |
| 6 | "Garbled-circuit" sealed auction | dregg | LIVE (no GC) | — | — | misnamed: BLAKE3 commit-reveal, no garbling |
| 7 | Private-voting secret tally | dregg | LIVE ballots / DESIGNED tally | med | H | tally is plaintext+monotone, no ZK |
| 8 | Firecracker microVM tier | DreggNet | FLAG-GATED, guest-plane DEAD | high | M | VM boots, `call()` errors — vsock guest wire + image build + jailer-as-standard |
| 9 | Caged native+seccomp+landlock tier | DreggNet | FLAG-GATED (off) | med | S | `--features caged`; Linux-only enforcement |
| 10 | SBX / dregg-bridge cap-aware seam | dregg | LIB-ONLY | med | M | no binary routes exec→sandbox through it |
| 11 | pg-dregg (dregg-in-Postgres) | dregg | LIB-ONLY, workspace-excluded | high | M–L | no daemon imports it |
| 12 | pg-dregg proof-gate circuit-link (S3) | dregg | DESIGNED+BUILT 90% | high | M | one circuit flip; attests nothing until then |
| 13 | node `pg-mirror-live` writer | dregg | FLAG-GATED + env-coupled | med | S | feature + `DREGG_PG_MIRROR_URL`; blocked on #12 |
| 14 | Durable Postgres store (duroxide-pg) | DreggNet | FLAG-GATED (off), `#[ignore]` test | med | S | default is on-disk SQLite (single-host) |
| 15 | Real `MeterTick` → dregg Payable | DreggNet | DEMO-STUB (in-process ledger) | high | M | meter ticks an in-process counter, not a chain charge |
| 16 | Storage / bucket service | DreggNet | LIB-ONLY | med | M | no gateway HTTP handler mounted |
| 17 | WebApp metered router (`LeasedRouter`) | DreggNet | LIB-ONLY (Router live, leased not) | med | M | gateway serves unmetered `Router` |
| 18 | Web-hosting on-chain publish write | DreggNet | DEMO-STUB (in-process `content_root`) | high | M | `SiteRegistry` is the data plane; real cell write is the `dregg-verify` flip |
| 19 | `dregg-verify` verified on-chain read | DreggNet | FLAG-GATED (off, AGPL) | high | L | default build is Apache-pure; needs workspace patch unification + a live node with data |
| 20 | Mesh dispatch (two-node WireGuard) | DreggNet | DEMO-STUB (`StubMesh` Unimplemented) | high | L | overlay handshake never brought up |
| 21 | `dreggnet-provider` autonomous loop | DreggNet | DESIGNED (real loop, not deployed) | high | L | not in the fleet; gated on operator lease-mint step |
| 22 | Persvati compute backend (`:8021`) | DreggNet | DESIGNED | high | L | hardware not provisioned |
| 23 | ConditionalBatch / ConditionalTurn | dregg | FLAG-GATED (HTTP API, no executor wire) | med | M | resolves over HTTP pool; no node→executor advance |
| 24 | PendingTurnRegistry (async coord) | dregg | LIB-ONLY | med | M–H | zero node wiring |
| 25 | Remote (cross-fed) EventualRef | dregg | DESIGNED (local LIVE) | med | M | `federation_id` field exists, executor never fetches remote receipt |
| 26 | EVM settlement (chain/, SP1) | dregg | DESIGNED+TESTED (mock) | med | M | mock-only; no live deploy / real prover in CI |
| 27 | deos-hermes confined agent | dregg | DEMO-STUB (Rust stand-in) | med | M | the jailed agent body is a stand-in, not live `hermes acp` |
| 28 | `AgentDockView` run_js | dregg | LIB-ONLY | med | S | proven in tests, not wired into the cockpit surface |
| 29 | starbridge-v2 `process-pd` | dregg | FLAG-GATED, half-built | med | M | surface→child-PD re-home not in live migrate path |
| 30 | starbridge-v2 `live-brain`/`agent-js`/`card-pane` | dregg | FLAG-GATED (off, size) | high | S | built + render-tested; off-default to avoid mozjs weight |
| 31 | node `deos-host` headless runner | dregg | FLAG-GATED (off, size) | med | S | opt-in to avoid SpiderMonkey in default build |
| 32 | upstream-track langs | DreggNet | DESIGNED | low | L | Zig/Crystal/Nim/etc. exit "not yet linked" |

\* low *today* — it is the missing foundation for any future 2PC.

---

## Per-cluster detail

### Privacy / ZK (dregg `circuit-prove`)

The M2 privacy stack is the sharpest "built-but-orphaned" cluster: the circuit
implementations are complete, both-polarity-tested, and use real hiding
uni-STARKs and Poseidon2 commitments — **no simulations, no stubs**. They simply
have **zero call sites in the executor**. They are a *cryptographic library*
awaiting an *Effect-vocabulary integration*.

- **#1 Shielded transfer (M2-a)** — `circuit-prove/src/shielded/transfer.rs`
  (`prove_shielded_transfer`, `verify_stark_side`, hidden membership + nullifiers
  + Pedersen value commitments). Called only from
  `circuit-prove/tests/shielded_transfer_m2a.rs`. No turn action type, no
  executor admission gate, no `Turn` field for the proof. **Gap:** define a
  shielded-transfer Effect, serialize the proof into the action, wire
  `verify_stark_side` into the executor. **The gap is plumbing, not crypto.**
- **#2 Multi-asset pool (M2-b)** — `circuit-prove/src/shielded/pool.rs`. Lifts
  the asset type into a hidden scalar (fixes M2-a's plaintext asset leak). Same
  wiring status as #1.
- **#3 ZK attestations (M2-d)** — `circuit-prove/src/shielded/attest.rs`. A real
  `Predicate` algebra (`Threshold`/`Positive`/`Membership`/`Equality`) over a
  Poseidon2 commitment, with a sound 30-bit range gadget on BabyBear ("prove
  age ≥ 18 / balance > 0 / membership without leaking the set"). Tested only.
  Poseidon2 is used correctly throughout — **no non-CR-hash gate was found**;
  the "membership-disclosure gated off for a weak hash" concern does not apply
  here. **Gap:** an attestation Effect + admission gate.
- **#4 General shielded transition (M2-c)** — `shielded/mod.rs` comment only.
  DESIGNED.
- **#5 Oblivious transfer** — `cell-crypto/src/oblivious_transfer.rs`, a full
  Chou-Orlandi 1-of-2 + 1-of-N, fully tested, **used nowhere** outside its own
  tests. The missing 2PC foundation; low value until a garbled-circuit consumer
  exists.
- **#6 "Garbled-circuit" sealed auction** — `starbridge-apps/sealed-auction`.
  **Honest correction:** there are *no* garbled circuits and *no* 2PC. It is a
  BLAKE3 sealed-commitment + plaintext-reveal auction with anti-front-running
  enforced by executor `WriteOnce`/`Monotonic` state constraints. Secure and
  LIVE, but cryptographically simple — the OT in #5 is not used by it.
- **#7 Private-voting tally** — `starbridge-apps/privacy-voting`. Ballot cells
  are genuinely unlinkable (derived from pubkey + blinding token) and one-vote
  enforcement is real (`WriteOnce`). But the **tally is plaintext** arithmetic
  protected only by `Monotonic` slots — there is no ZK proof of tally
  consistency. The crate's own doc says a production tier "would additionally
  blind the choice and prove tally consistency in zero knowledge." So: ballot
  privacy LIVE; secret tally DESIGNED.

### Compute tiers (DreggNet `exec` → the owned sandbox)

Only the base wasm tier is genuinely **LIVE**: `CapTier::Sandboxed` runs on an
**owned, vendored pure-Rust `wasmi` interpreter** (zero unsafe, no external
submodule), and it really executes — the `add(40,2)=42` dogfood runs here, with
real metering. It emits the provider label `dreggnet-wasmi`. **Every stronger
tier is an honest, fail-closed seam today** (`ExecError::NotWired` /
`TierNotServed`) — never a fake run, never a silent downgrade. Wiring an owned
engine for each is future work:

- **#8 Firecracker microVM** — `CapTier::MicroVm` is a **fail-closed seam**: it
  refuses cleanly (`dreggnet-microvm (seam)`) rather than executing. The owned
  microVM engine (guest plane, vsock+JSON wire, kernel/rootfs image build, jailer
  chroot+cgroup) is future work. No workload runs inside a microVM today; the
  tier honestly reports it is not served.
- **#9 Caged (native + seccomp + Landlock)** — `CapTier::Caged` is a
  **fail-closed seam** (`dreggnet-native (seam)`): it refuses generic host
  binaries / shebang scripts rather than running them. The owned native engine
  (seccomp + Landlock enforcement) is future work.
- **#10 SBX / dregg-bridge cap-aware seam** — the dregg-cap-aware boundary
  between `exec` and the owned sandbox is a **LIB-ONLY** seam: no binary routes
  execution through it live yet.

(The `JitSandboxed`/JIT wasm tier and the native `python`/`node` interpreter
langs are likewise fail-closed seams today — an owned engine for each is future
work. Do not read these as "live": only the base `Sandboxed` wasmi tier runs.)

### Durable settlement & Postgres (both repos)

The honest shape: **durable execution is LIVE on single-host SQLite**;
**Postgres-grade durability and the real chain charge are the named next rungs.**

- **#11 pg-dregg** — `breadstuffs/pg-dregg`, the dregg-in-Postgres verified
  store. **Excluded from the workspace** and imported by **no** daemon — used
  only in its own tests/examples/benches. It is the reference implementation of
  the verified durable spine, not yet a backing store for any live service.
- **#12 pg-dregg proof-gate circuit-link** — S1 (WholeChainProof serde) and S2
  (the turn-proof producer) are built; **S3 — the circuit flip** that turns the
  tier-c attest from a fail-closed stub into a real verifier — is the one
  remaining line. Until S3, the shadow-attest path *attests nothing* (the safe
  direction). This is the load-bearing blocker under #11/#13/#18.
- **#13 node `pg-mirror-live`** — full pg-mirror module with an in-memory sink
  that is load-bearing and tested; the live Postgres writer (`pg_live::PgSink`)
  only activates with both the `pg-mirror-live` feature AND
  `DREGG_PG_MIRROR_URL` set, and is downstream of the #12 proof-gate.
- **#14 Durable Postgres store (duroxide-pg)** — `DreggNet/durable`'s `pg`
  feature: an in-process Postgres `Provider` + a meter outbox over a shared
  sqlx pool, tested behind an `#[ignore]` + `DATABASE_URL` gate. The default and
  only-live store is **on-disk SQLite** — WAL-durable across process restart on
  one host, NOT across host loss. Swapping in duroxide-pg changes no workflow
  line; it is the multi-region durability boundary, un-flipped.
- **#15 Real `MeterTick` → dregg Payable** — *the* durable-settlement seam. The
  `MeterTick` activity currently increments an **in-process ledger counter**
  (`dreggnet_durable::metrics`), not a real dregg `Payable` charge. The
  "transactional twin" (work + meter committed together-or-not) is real *within
  duroxide's history*, but the meter side is not yet a chain transfer. Making
  `MeterTick` a `Payable` against `pg-dregg` (one Postgres txn = the duroxide
  checkpoint + the lease charge) is the bridge rung. **Note:** the node-facing
  *settlement* path (`NodeApiSettlement` → `Effect::Transfer` per period, with a
  fsync'd dedup ledger `DurableSettleLedger`) IS real and wired in
  `dreggnet-provider` — but that binary isn't deployed (#21). The in-process
  `ConservingLedger` is an honestly-labelled twin, not a disguised stub.

### DreggNet services — gateway / storage / webapp / bridge

The **gateway is production-ready and LIVE** (httpe on `:8080` in staging, real
machines API, lease validation through the bridge gate, static minisite serving).
The libraries beneath it are mostly complete-but-unmounted:

- **#16 Storage / buckets** — `DreggNet/storage` is a complete, tamper-tested
  trustless object store (`BucketRegistry`, `StorageCap`, Poseidon2
  `content_root`, `verify_opening`). **No gateway HTTP handler is mounted** —
  `storage/lib.rs` says outright "neither is wired live here." LIB-ONLY.
- **#17 WebApp metered router** — `Router` (route → sandbox handler) is tested
  and the gateway serves it, but **unmetered**; the `LeasedRouter` (metered
  against a funded lease + durable) is not deployed. Multi-app-per-gateway is "a
  later rung." Hosting is wired; metered routing is not.
- **#18 Web-hosting on-chain publish** — a site IS a cell, and the
  publish→serve round-trip over real TCP is tested and the gateway's
  `SiteHostHandler` resolves by `Host`. **But the publish writes an in-process
  `SiteRegistry`** — the computed `content_root` is the *stand-in* for the
  cell's committed heap root. The real `Effect::Write` to a dregg node (witnessed
  as a receipt) is the deliberate `dregg-verify` flip (#19). DEMO-STUB on the
  on-chain dimension; the serving is real.
- **#19 `dregg-verify` verified on-chain read** — the AGPL boundary feature
  (`bridge`/`control`/`storage`), **off by default to keep the build
  Apache-pure**. When on, `DreggNodeFeed` reads funded leases from a node's
  receipt log via light-client whole-log attestation (`VerifiedNodeLeaseSource`),
  with the `CommitBindsMMR` trusted-root hardening. Flipping it needs
  workspace-level patch unification (ark-serialize/lockstitch) AND a live node
  carrying data — today's recovered edge node has an empty receipt log, so the
  loop boots, reads nothing, and idles. The wiring is proven to the
  point-of-having-data against local stub nodes.

### Orchestration / mesh / deployment (DreggNet `control`)

LIVE: the `LocalProvider` + `Scheduler` + CLI (`lease open` → `run` →
in-process fulfillment), with JSON lease-state persistence. The autonomous,
distributed half is designed but not deployed:

- **#20 Mesh dispatch** — `TailscaleMesh` + `post_fulfill` + `health_check` are
  built and tested with loopback stubs, but the live two-node WireGuard handshake
  is never brought up: `StubMesh` returns `ProviderError::Unimplemented` naming
  the exact `POST /fulfill` that *would* run. DEMO-STUB pending the overlay.
- **#21 `dreggnet-provider` autonomous loop** — the real daemon (read funded
  leases → schedule → dispatch over mesh → meter → settle a real `Transfer` per
  period → reap, with the `DurableSettleLedger` dedup) is **fully coded** but
  **not in the staging fleet**, and its live end-to-end is gated on a one-time
  operator step (unlock the node, mint a funded execution-lease).
- **#22 Persvati compute backend** — the `:8021` bridge agent that answers
  `POST /fulfill`; designed in `deploy/PERSVATI-BACKEND.md`, hardware not yet
  provisioned.

### Promises / partial-turn / reactor (dregg)

A pleasant surprise: most of this cluster is **LIVE**, not spec-only.

- **LIVE — guarded holes (Promise/Notify/React):** real Effect variants
  (`turn/src/action.rs:1341–1386`) dispatched by the executor
  (`apply_promise`/`apply_notify`/`apply_react`), with one-shot linearity
  enforced by the same note-nullifier double-spend gate and a ~3300-line
  forge-detector suite. Sound and integrated.
- **LIVE — `PipelinedSend` + `EventualRef`:** an Effect variant with a real
  executor dispatch and topological multipass resolution (local pipelining).
- **LIVE — CapTP promise pipelining:** `captp/src/pipeline.rs` is actively used
  by `node`'s channels / handoff / mailbox-crank paths.
- **LIVE — Reactor / app-framework:** `app-framework/src/reactor.rs`'s
  filter→react→cap-gate→Action desugaring is genuinely driven by the
  **discord-bot** (`bot_reactor.rs`, started from `main.rs`), which fires a
  custodial turn in response to a real on-chain command-cell receipt.
- **#23 ConditionalTurn (ConditionalBatch-as-Effect):** NOT an Effect variant —
  it is a separate Turn wrapper submitted to the node over `POST
  /conditional/{submit,resolve}` with full STARK verification. **Gap:** the
  node's conditional pool does not advance a *resolved* conditional into the
  executor queue (no per-block timeout sweep / resolved→execute edge shown).
  FLAG-GATED via the HTTP API, not closed-loop.
- **#24 PendingTurnRegistry:** `turn/src/pending.rs` — a complete async
  coordination registry (submit/resolve/cascade/timeout, full test suite) with
  **zero node wiring**. LIB-ONLY.
- **#25 Remote EventualRef:** the `federation_id` field exists on `EventualRef`,
  but the executor never fetches a remote federation's receipt — cross-fed
  pipelining is DESIGNED while local is LIVE.

### Long tail (both repos)

- **#26 EVM settlement** — `breadstuffs/chain` (SP1 guest STARK verifier,
  alloy on-chain scaffold, proof serialization) is **mock-mode complete and
  tested** but the crate's own README calls it a "structural scaffold … not yet
  deployed to a live chain." Real SP1 proving and Base Sepolia/Mainnet
  deployment are unwired.
- **#27 deos-hermes confined agent** — the cap-confined PD launch +
  sandbox-probe verdict are real, but the **agent body inside the jail is a
  deliberate Rust stand-in**, not the live `hermes acp` venv. DEMO-STUB by
  design (it proves the confinement, not the agent).
- **#28 `AgentDockView` run_js** — proven in `deos-hermes` tests
  (`hermes_runs_js`, `hermes_authors_card_via_run_js`) but not wired into the
  live cockpit surface. LIB-ONLY, small gap.
- **#29 starbridge-v2 `process-pd`** — OS-sandboxed child-PD infrastructure
  (fork/socketpair/LSM) is half-built and tested in isolation; the
  surface→child-PD re-home is not integrated into the live cockpit migrate path.
- **#30 starbridge-v2 `live-brain` / `agent-js` / `card-pane`** — all three are
  fully built and render-capture-tested, **off the default desktop build** to
  avoid the multi-GB mozjs/SpiderMonkey weight. FLAG-GATED, no correctness gap.
- **#31 node `deos-host`** — a headless JS-program runner against the node's
  ledger, off-default to keep SpiderMonkey out of the standard build.
- **#32 upstream-track languages** — Zig/Crystal/Nim and other langs
  exit `78` "not yet linked"; per-language owned engines are future work
  (fail-closed seams today).

---

## What IS genuinely live

So the census is honest in both directions:

- **dregg kernel & effects** — Transfer / SetField / cap grant-revoke / notes
  (NoteSpend/Create) / nonce / CreateCell, and the promise cluster
  (Promise/Notify/React, PipelinedSend) are all real Effect variants with real
  executor dispatch and forge-detector tests.
- **Reactor** — driven live by the discord-bot against a real on-chain
  command cell.
- **CapTP pipelining** — used by the node's channels/handoff/mailbox paths.
- **DreggNet gateway** — httpe `:8080` in staging, machines API, static
  minisite serving, lease-gated.
- **Compute** — the base `Sandboxed` wasm tier genuinely executes and meters on
  the owned, vendored pure-Rust `wasmi` interpreter (the `add(40,2)=42` dogfood
  runs here, `dreggnet-wasmi`). Every stronger tier (JIT, Caged/native, MicroVm,
  python/node) is a fail-closed seam today — an owned engine for each is future work.
- **Durable execution** — real metered workloads as duroxide orchestrations,
  per-step metering, crash-resume proven on on-disk SQLite (single host).
- **Settlement** — `NodeApiSettlement` posts real conserving `Transfer` turns
  with a fsync'd exactly-once dedup ledger (live in the `dreggnet-provider`
  binary; that binary just isn't deployed in the fleet yet).
- **~24 starbridge-apps** — nameservice, identity, subscription,
  governed-namespace, escrow-market, compute-exchange, agent/swarm-orchestration,
  execution-lease, bounty-board, privacy-voting (ballots), kvstore, gallery,
  agent-provenance, first-room … each with a passing `cargo test` proving its
  admission gates fire through the embedded executor. They run against the
  embedded/local executor; "live against a deployed fleet node" is the
  unwired dimension, not the app logic.

## Priority read (by value × tractability)

1. **#12 pg-dregg proof-gate S3 flip** (one circuit line) unblocks #11/#13/#18
   real verified durable state — the highest leverage small move.
2. **#15 real `MeterTick` → Payable** + **#19 `dregg-verify` flip** turn the
   metered/hosted demos into genuinely on-chain-settled, verified services.
3. **#1–#3 wire the M2 privacy effects** — a complete, sound crypto library is
   one Effect-vocabulary integration away from shippable shielded transfers and
   ZK attestations.
4. **#20–#22 the distributed loop** (mesh overlay + deploy `dreggnet-provider` +
   persvati) is the largest-effort, highest-value lift to a real autonomous
   metered fleet — gated mostly on deployment/ops, not code.
5. **#8 firecracker guest plane** — make the strong-isolation tier actually run
   workloads (vsock wire + image build), not just boot-and-refuse.
