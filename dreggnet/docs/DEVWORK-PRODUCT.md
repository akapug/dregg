# DEVWORK-PRODUCT — the prioritized product dev-work list

A grounded, read-the-code sweep (HEAD, 2026-06-30) of DreggNet's **product /
featureset surfaces** — hosting, auto-deploy, custom domains, storage, the
persistent-server control plane, the compute tiers, the inner host-API, the
sandstorm bridge, the durable layer, hosting-billing, the lease bridge / fiat
rail, and the admin portal. For each surface it names the genuine dev work:
what's **half-built / stubbed**, what **needs deepening** (v1 → robust), the **DX
gaps** (rough edges for a real user/dev), the **missing features** ("this should
obviously exist"), and the **integration seams**.

This doc is the *product-feature* lens. It is **complementary** to, not a
restatement of, the three honesty catalogs — where an item is already cataloged
there, this doc cross-refs and does not re-derive:

- `docs/STAND-INS-CENSUS.md` — what's faked that needs to be real.
- `docs/UNDER-WIRED-features.md` — built-but-not-live.
- `docs/UNDER-WIRED-{circuit,parity}.md` — executor/Lean-vs-circuit gaps.

**The honest headline.** DreggNet's spines are genuinely built and tested — the
control-plane orchestration (place→provision→fulfill→reap), per-period lease
metering (exactly-once across restart), the persistent-server lifecycle, all
compute tiers (only the microVM *guest plane* is unbuilt), the host-API
cap-gate/meter/receipt, the conserving settlement model, the deploy
clone→build→publish workflow, and the read-only ops aggregation are real. The
product gaps are mostly (a) **portable cores not yet mounted in the gateway**
(storage, the leased router), (b) **DX polish a stranger hits in the first hour**
(no `--dry-run`, no build logs, opaque budgets, `--owner` ignores login), and (c)
**"obviously should exist" web-platform features** (path params, request bodies,
HTTPS, rollback, env/secrets). The deliberate stand-ins (FNV-for-Poseidon2,
StubMesh, MockDns, LocalProvider default) are honestly named and behind clean
seams; they are tracked in STAND-INS-CENSUS and only cross-ref'd here.

**Effort:** S = <1 day · M = 1–5 days · L = 1–2 weeks.
**Disposition:** safe-autonomous (no live deploy / real money / external service
/ hardware / AGPL-flip to touch) · reviewed-go (one of those gates applies) ·
needs-a-decision (a product/design choice precedes the code).

---

## TOP 10 — highest leverage to do next (ranked)

Ranked by value × tractability, favoring *real-impl-already-near* + *safe-
autonomous* + *unblocks-other-work* first.

| # | Item | Surface | file:line | Effort | Value | Disposition |
|---|------|---------|-----------|--------|-------|-------------|
| 1 | **Mount the storage core in the gateway** (`PUT/GET/DELETE /<bucket>/<key>` → the tested `BucketRegistry`; the sibling `gateway/src/storage.rs` does not exist) | storage | `storage/src/lib.rs:46-52`; `gateway/src/` (no `storage.rs`) | M | high | safe-autonomous |
| 2 | **`dregg-cloud deploy --dry-run`** (run detect+build-plan, print the plan + would-publish name, no clone/build/publish) — the single biggest deploy-DX win | deploy/CLI | `cli/src/main.rs:106-125`; `dregg-deploy/src/plan.rs:178-208` | M | high | safe-autonomous |
| 3 | **Capture & surface build/workload output on failure** (today a failed `npm run build` or lapsed workload shows only an exit code / "lapsed" label — no stderr) | deploy/CLI | `dregg-deploy/src/build.rs:74-78`; `cli/src/main.rs:844-845` | M | high | safe-autonomous |
| 4 | **`--owner` should default to the logged-in identity** (after `dregg-cloud login`, deploy/domains still default `owner="operator"`) | CLI | `cli/src/main.rs:120,138` | S | high | safe-autonomous |
| 5 | **Path parameters in the router** (`/users/{id}`); today only whole-path `match_route` — blocks any REST app | webapp | `webapp/src/router.rs:50-61`; `webapp/src/lib.rs:97` | M | high | needs-a-decision |
| 6 | **Request body → handler ABI** (handlers are zero-arg `run`; the body is parsed but never passed) — blocks POST/PUT apps | webapp | `webapp/src/lib.rs:98-101`; `webapp/src/http.rs` | M | high | reviewed-go (polyana host-import) |
| 7 | **Rate-limit publish + domain-verify** (a cap holder can republish / re-verify unbounded → DOS the bandwidth meter / DNS resolver) | hosting/domains | `webapp/src/hosting.rs:589-623`; `dregg-domains/src/lib.rs` (verify) | S | high | safe-autonomous |
| 8 | **Rate-card API + free-tier flag** (pricing is hardcoded Rust; no endpoint to read it, no config switch between `free()` and real pricing) | billing | `control/src/hosting_meter.rs:68-110` | S | high | safe-autonomous |
| 9 | **Persistent-server health probe** (`ServerFleet::health` returns `!is_running` — no real TCP/heartbeat probe; ingress can't gate on liveness) | control/servers | `control/src/server.rs:1104-1120` | M | high | reviewed-go (network IO) |
| 10 | **Wire `invoke` to the real ToolGateway** (the host-API spine — cap-gate/meter/receipt — is real; only the *target resolution* is a caller-registered service map) | exec host-API | `exec/src/host_api.rs:60-70,440-458` | M | high | reviewed-go (AGPL seam) |

The cluster #1–#4 + #7–#8 are **safe-autonomous and individually small**: a
focused push there makes DreggNet meaningfully more usable by a stranger without
touching money, hardware, or the AGPL core. #5/#6 are the two web-platform
features that gate "real apps." #9/#10 are the highest-value spine completions.

---

## HOSTING — static minisites (`webapp/`, `gateway/`)

**Solid:** the publish→serve round-trip over real TCP; the cap-gated
`SiteRegistry`; the order-independent content commitment (a single changed byte
moves the root); `cert_ok()` decision logic; bandwidth accounting.

### Half-built / stubbed
- **FNV-1a content root stands in for Poseidon2** — `webapp/src/hosting.rs:763-790`.
  Order-independent and correct as a binding; the real on-chain Poseidon2 heap
  root rides the `dregg-verify` flip. *Cross-ref STAND-INS #4.* Effort S to swap
  once the node-write lands; safe-autonomous.
- **Caddy on-demand-TLS `ask` endpoint not served** — `gateway/src/hosting.rs:114-135`
  has `cert_ok()`, but no `GET /internal/site-exists?domain=…` route in
  `gateway/src/main.rs`. Effort M, high value (no cert mints without it),
  needs-a-decision (deploy/ops lane owns the Caddyfile).

### Needs deepening
- **No publish rate-limit** — `webapp/src/hosting.rs:589-623`. Unbounded
  republish can DOS the shared bandwidth meter. Effort S, high. *(Top-10 #7.)*
- **No cache-invalidation signal on republish** — `webapp/src/hosting.rs:195-197`.
  New `content_root` = new cell, but no edge/CDN purge hook. Effort M, med.
- **No publish audit metadata** — `webapp/src/hosting.rs:269-288`. `PublishReceipt`
  lacks timestamp/source. Effort S, med, safe-autonomous (add optional field).

### DX gaps
- **No `--dry-run` for `dreggnet-host`** — `webapp/src/bin/dreggnet-host.rs:44-103`.
  Effort S, med.
- **No rollback / version history** — `webapp/src/hosting.rs:606,621` (publish
  replaces the cell; old content discarded). Effort M, med, reviewed-go.
- **No per-site bandwidth-budget surface** — `webapp/src/hosting.rs:364-513`
  (`BandwidthMeter` has the methods; no CLI/API to set/read a budget). Effort M,
  high, needs-a-decision (billing UX).

### Missing features (web-platform table-stakes)
- **HTTPS provisioning** (wildcard DNS-01 or on-demand HTTP-01) — `docs/WEB-HOSTING.md:93-162`,
  no serving-side code. Effort M, **critical**, needs-a-decision (deploy/ops).
- **Cache-Control / ETag / Last-Modified** — `webapp/src/http.rs:98-105`
  (response is status+type+body only). Effort S, med, safe-autonomous.
- **Redirects (301/302)**, **custom 404/50x pages**, **CORS headers** — all
  `webapp/src/hosting.rs:201-216` / `http.rs:98-105`. Each Effort S,
  safe-autonomous; redirects+CORS med value, error pages low.
- **Compression (gzip/brotli)** in the portable binary — `webapp/src/http.rs`.
  Effort M, med (delegated to Caddy at the edge), reviewed-go.

### Integration seams
- **On-chain `Effect::Write` for a published site** — `webapp/src/hosting.rs:46,191-197`.
  The in-process registry is the data plane; the witnessed cell write is the
  `dregg-verify` flip. *Cross-ref STAND-INS #4 / UNDER-WIRED #18.* Effort L, high,
  needs-a-decision.

---

## WEBAPP DYNAMIC API — the leased router (`webapp/router.rs`, `gateway/webapp.rs`)

**Solid:** `Router::serve` route-match + polyana handler run + render; 402 on
over-budget; on-disk SQLite durability across restart (single-host).

### Half-built / stubbed
- **`LeasedRouter` built but the gateway serves the unmetered `Router`** —
  *Cross-ref UNDER-WIRED #17.* Effort M, med.
- **Per-request store is single-host SQLite** — `webapp/src/router.rs:151,189`.
  Multi-host = the Postgres store rung. Effort L, high, needs-a-decision.

### Missing features
- **Path parameters** — `webapp/src/router.rs:50-61`; `lib.rs:97`. Whole-path
  match only. Effort M, **high**, needs-a-decision. *(Top-10 #5.)*
- **Request body → handler** — `webapp/src/lib.rs:98-101`. Zero-arg handlers;
  body parsed but not threaded. Effort M, **high**, reviewed-go (polyana
  host-import ABI). *(Top-10 #6.)*
- **Streaming responses** (`http.rs:98-105`, buffered `Vec<u8>`), **middleware
  pipeline** (`router.rs:54-62`), **per-route rate-limit / 429** — each Effort
  M, med/high, reviewed-go.
- **OpenAPI/schema export** — `webapp/src/spec.rs`. Effort M, low, safe-autonomous.

### DX gaps
- **No app-author SDK** (only the demo builders in `webapp/src/assemble.rs`) —
  Effort M, high, needs-a-decision.
- **No local `app test` / validation before deploy** — Effort M/S, med/low,
  safe-autonomous.
- **No per-route metrics / request context** — `gateway/src/main.rs:203`;
  `webapp/src/router.rs:84-100`. Effort S/M, med, reviewed-go.

---

## CUSTOM DOMAINS (`dregg-domains/`, `gateway/hosting.rs`)

**Solid:** the `DnsResolver` trait seam; `LiveDns` real worker
(`dregg-domains/src/live.rs:65-128`); the TXT/CNAME challenge model; cap-gated
binding.

### Half-built / stubbed
- **`MockDns` in tests; no production resolver in the cert path** — *Cross-ref
  STAND-INS #6.* `LiveDns` exists but `cert_ok` is only reachable once the Caddy
  `ask` endpoint is wired (above). Effort S (resolver), high, reviewed-go.

### Needs deepening / missing
- **No verify rate-limit** — `dregg-domains/src/lib.rs` (verify). Spammable DNS
  lookups. Effort S, high. *(Top-10 #7.)*
- **No TTL cache on verified bindings** — `gateway/src/hosting.rs:124-130`
  (re-verifies every `cert_ok`). Effort S, low, reviewed-go.
- **No unbind / rebind** — `dregg-domains/src/lib.rs` (only `bind`). Effort S,
  med, safe-autonomous.
- **No challenge-instruction rendering / status command** — `dregg-domains/src/lib.rs:129-143`.
  Effort S/M, low/med, safe-autonomous.
- **No cert auto-renewal lifecycle** — Effort M, low, needs-a-decision.

---

## STORAGE SERVICE (`storage/`)

**Solid:** the cell model, cap-gate + attenuation, content-address + content-root
commitments, receipts, metering, and the self-verifying `verify_opening` read —
all tested in-crate.

### Half-built / stubbed — the one blocking gap
- **No gateway mount** — `storage/src/lib.rs:46-52` names a sibling storage mount;
  `gateway/src/storage.rs` **does not exist** and no `PUT/GET/DELETE` routes are
  in `gateway/src/main.rs`. The whole tested core is unreachable. Effort M,
  **critical**, safe-autonomous. *(Top-10 #1.)*
- **FNV leaf/root stands in for Poseidon2** — `storage/src/object.rs`,
  `storage/src/bucket.rs`. *Cross-ref STAND-INS #5.* Rides the node-write flip.

### Needs deepening / missing (S3-shaped expectations)
- **Concurrent put = silent last-write-wins** (`storage/src/registry.rs:144+`) —
  add etag/version + compare-and-set. Effort M, med, reviewed-go.
- **No lifecycle/TTL, no soft-delete, no access log** (`storage/src/{bucket,registry,meter}.rs`)
  — each Effort M, med/high, reviewed-go.
- **Signed URLs** (temporary capless read), **versioning**, **multipart upload**,
  **object/bucket metadata + CORS** — `storage/src/{registry,object,bucket,cap}.rs`.
  Signed-URLs high value (Effort M, needs-a-decision); multipart needed for large
  files (Effort L, reviewed-go); metadata/CORS Effort S, safe-autonomous.
- **No `dreggnet-store` CLI / bulk import** — no `storage/src/bin/`. Effort M,
  med, safe-autonomous.

---

## AUTO-DEPLOY (`dregg-deploy/`)

**Solid:** the crash-resumable, metered clone→detect→build→publish durable
workflow; the deny-default build sandbox; symlink refusal at build + publish.

### Half-built / stubbed
- **Detection is a 3-heuristic** — `dregg-deploy/src/plan.rs:178-208` (Dockerfile
  → Server, `package.json` build script → Command, `index.html` → Static; else an
  honest error). No Python/Go/Rust/Hugo/Next/Vite/etc. Effort M, high,
  safe-autonomous (harden the matcher).
- **Publish lands in the in-process `SiteRegistry`** — `dregg-deploy/src/workflow.rs:156`;
  `cli/src/main.rs:914`. Live `*.example.com` serving is the gateway-mount rung.
  Effort L, high, reviewed-go.
- **Compute build path uses repo-declared lang/source only** —
  `dregg-deploy/src/build.rs:80-91`. Runtime-supplied workloads are bridge-side
  future work. Effort M, high, reviewed-go.

### Needs deepening
- **Build failure surfaces only command+exit code** — `dregg-deploy/src/build.rs:74-78`.
  Capture stderr/output snippet + which step. Effort M, high, safe-autonomous.
  *(Top-10 #3.)*
- **Silent output-dir fallback** (`dist`/`build`/`out`/`public`) —
  `dregg-deploy/src/build.rs:129-134`. Warn which was used. Effort S, med.
- **Loose manifest validation** (unknown `dregg.toml` keys ignored; no version) —
  `dregg-deploy/src/plan.rs:222-256`. Effort S, low, safe-autonomous.

### Missing features
- **`--dry-run`** — *(Top-10 #2.)* Effort M, high, safe-autonomous.
- **Build-only / publish-only stages; `deploy resume <id>`** (the durable store
  supports resume — `workflow.rs:507-519` — but the CLI doesn't expose it) —
  Effort M, med, safe-autonomous.
- **Rollback / deploy history** — Effort L/M, high/med, needs-a-decision.
- **Env vars / secrets injection** (build runs in a cleared env —
  `sandbox.rs:103-118`) — Effort L, high, needs-a-decision.
- **Preview deploys, monorepo `--root`, pre/post hooks, framework `--init`
  scaffold** — each Effort M, med/high, mostly needs-a-decision (`--init` is
  safe-autonomous).
- **Live build logs / progress** — `cli/src/main.rs:922-934` (silent wait).
  Effort L, med, safe-autonomous.

---

## THE CLI (`cli/src/main.rs`)

**Solid:** a coherent command set (`lease`/`run`/`status`/`deploy`/`login`/
`domains`/`ls`/`logs`/`destroy`), cross-invocation JSON state, cap-tier enum.

### Half-built (bridge-side, reviewed-go)
- **`run --lang` only accepts `wat`; workload program hardcoded; lease `funded`
  is a mock flag** — `cli/src/main.rs:761,791-792` and the bridge. *Cross-ref
  STAND-INS #8/#11, GO-REAL.* Effort M each, high, reviewed-go.

### DX gaps (mostly safe-autonomous polish)
- **`--owner` ignores the logged-in identity** — `cli/src/main.rs:120,138`.
  Effort S, high. *(Top-10 #4.)*
- **Opaque budget units; no `dregg estimate`** — `cli/src/main.rs:122-124`.
  Effort S/M, high.
- **`destroy` has no confirmation/`--force`** — `cli/src/main.rs:684-730`.
  Effort S, low (safety).
- **No config file (`.dreggnetrc`), no `--json`, no `--quiet`** — Effort S/M,
  med.
- **Workload failure prints only "lapsed", no diagnostics** —
  `cli/src/main.rs:824-846`. Effort M, high. *(folds into Top-10 #3.)*
- **Lease+run vs deploy are two unconnected paradigms** (can't `deploy` onto a
  pre-funded lease) — `cli/src/main.rs:83-125`. Effort M, high, needs-a-decision.
- **Wallet-bound vs minted account split is confusing** — `cli/src/main.rs:479-492`.
  Effort S, med, needs-a-decision.

### Missing
- **Team / org support** (everything is one cap-account), **multi-region /
  canary**, **deploy analytics** — each Effort L, med/low, needs-a-decision.

---

## PERSISTENT SERVERS + CONTROL PLANE (`control/`)

**Solid:** the server lifecycle state machine + durable `ServerStore` (crash
survival, exactly-once uptime metering across reload — `control/src/server.rs:72-85,505-650`);
the scheduler place→provision→fulfill→reap with lease-gated admission
(`scheduler.rs:140-200`); the orchestrator daemon loop with round-robin pick +
health cadence + failover (`orchestrator.rs`); `NodeApiSettlement` exactly-once
`Transfer` per period.

### Half-built / stubbed
- **`ServerFleet::health` is a stub** (`control/src/server.rs:1104-1120`,
  returns `!is_running` — no TCP/heartbeat probe). Effort M, high, reviewed-go.
  *(Top-10 #9.)*
- **No gateway→server ingress routing** — `gateway/src/route.rs` has no machine
  ingress handler; persistent servers exist but requests aren't routed to them.
  Effort M, high, needs-a-decision.
- **StubMesh / Ec2 stubbed API / LocalProvider default** — *Cross-ref STAND-INS
  #3/#10/#11.* Deliberate dev defaults + the live-fleet deploy rung.

### Needs deepening
- **Scheduling is round-robin only** (`fleet.rs:285-310`) — no bin-packing,
  fairness, per-tenant quota, or placement constraints. Effort M, med/high,
  safe-autonomous.
- **No crash recovery for persistent workloads / no restart policy** (backoff,
  max-restarts) — `server.rs:200-210`. Effort M, high, safe-autonomous.
- **No graceful drain / shutdown** (stop is immediate; no in-flight drain) —
  `fleet.rs:280-310`, `server.rs`. Effort S/M, med, safe-autonomous.
- **Daemon loses workload tracking on restart** (in-memory registry;
  `dreggnet-provider.rs:150-170`). Effort M, high, safe-autonomous.
- **No autoscaling** (registry read-only per tick). Effort L, high, reviewed-go.
- **Mesh hardening**: keep-alive/heartbeat, key rotation, partition handling,
  multi-cloud provider impls (only Local + EC2) — `mesh.rs`, `provider.rs`,
  `ec2.rs`. Effort M/L, med, mixed.

### DX gaps
- **No fleet/server operator CLI** (`fleet add/remove/drain/health`,
  `server start/stop/restart/scale/logs`) — backends are config-only. Effort M,
  high, safe-autonomous.
- **No mesh troubleshooting tooling** (latency/loss/reachability). Effort M, med.

---

## COMPUTE TIERS + INNER HOST-API (`exec/`)

**Solid:** wasmi + wasmtime (fuel + WASI-P2) tiers on every platform; Caged
(seccomp+Landlock, Linux); microVM VM lifecycle (spawn/boot/teardown/jailer); GPU
routing with clean refusal. Host-API cap-gate (`gate_effect_set`), metering,
conserving value ledger, chained receipts, cell read/write — all real
(`exec/src/host_api.rs:440-585`).

### Half-built / stubbed
- **microVM guest plane dead** (`exec/src/lib.rs:95-110`; boots, `call()` errors
  — vsock+JSON guest wire unbuilt). *Cross-ref STAND-INS #2 / UNDER-WIRED #8.*
  Effort M, high, reviewed-go (KVM).
- **`invoke` resolves a caller-registered service map** — `exec/src/host_api.rs:60-70,440-458`.
  The cap-gate/meter/receipt are the REAL surface; only target resolution is the
  in-process realization (the real target is the breadstuffs ToolGateway).
  *Cross-ref STAND-INS #1.* Effort M, high, reviewed-go. *(Top-10 #10.)*
- **Host-call wire only for native Python/Node tiers** (`host_api.rs:622-650`;
  wasm/microVM carry it in a later rung). Effort L, high, reviewed-go.

### Needs deepening / missing
- **`transfer` and `subturn` deferred** (`host_api.rs:430-436`) — the
  value-moving / nested-turn host calls; semantics (nested failure/rollback)
  unspecified. Effort M, high, reviewed-go.
- **No per-call rate limit, no per-service value quota, no typed service
  schemas, no service versioning, synchronous handlers only** — `host_api.rs`
  (`ServiceFn` is a sync closure). Effort S–M each, low/med, mixed.
- **Resource metering uncalibrated** (wasmi no fuel; native = wall-clock
  timeout) — `exec/src/lib.rs:305-310`. Effort M, med, safe-autonomous.
- **Caged native tier is shebang-scripts-only** (ELF a later rung) —
  `exec/src/lib.rs:68-73`. Effort M, med, reviewed-go.
- **No workload-author host-API docs/examples** — Effort S/M, med,
  safe-autonomous.

---

## SANDSTORM BRIDGE (`sandstorm-bridge/`)

**Solid (as a design prototype):** the grain=cell / powerbox=cap / SturdyRef
model with real HMAC-SHA256 ownership seals (`powerbox.rs:42-99`); the network
confinement policy; the resource-lease quota math; the `.spk` archive
(magic/xz/Ed25519). *The whole crate is an honestly-named prototype — cross-ref
STAND-INS #12.*

### Half-built / stubbed
- **`.spk` manifest is a JSON projection of the capnp schema** —
  `sandstorm-bridge/src/manifest.rs:14`, `spk.rs:37-44`. Real capnp codec is the
  swap. Effort M, high, reviewed-go (needs a real `.spk` sample + differential
  test).
- **`Umem` heap is an in-memory `BTreeMap`** — `cell.rs:27`, `lib.rs:17`
  (commit→data_root correct; weld to real umem/durable is mechanical). Effort L,
  high, safe-autonomous.
- **CPU/memory/egress are policy-only** (only uptime is actually charged;
  syscall/socket interception lives in exec) — `limits.rs:242-250`, `net.rs:114-120`.
  Effort S/M, high, reviewed-go.

### Needs deepening / missing / seams
- **No real crash/restart durability test** (lifecycle is in-process) —
  `grain.rs:199-205`. Effort M, high, reviewed-go.
- **No grain copy/migrate** (Sandstorm's `transferGrain`) — `grain.rs`. Effort M,
  high, needs-a-decision.
- **No `.spk` inspector / cap-audit trail** — Effort M, med, safe-autonomous.
- **Seams (reviewed-go):** `.spk`→`dregg-deploy` ingest; powerbox→cipherclerk
  delegation witness; grain→funded-lease admission — all owned by the bridge
  orchestrator / breadstuffs weld.

---

## DURABLE LAYER (`durable/`)

**Solid:** duroxide orchestration + on-disk SQLite (WAL-safe, single-host);
in-process crash-resume test; the conserving ledger with exactly-once
`(lease, period)` dedup (`settle.rs`); the verified blake3-chained settlement
twin (`verified.rs`).

### Half-built / stubbed
- **SQLite → Postgres (`duroxide-pg`) is a feature swap, not a stub** —
  `durable/src/lib.rs:89-96` (multi-host = a different store; honest boundary).
  *Cross-ref UNDER-WIRED #14.* Effort L, high, safe-autonomous (mechanical).
- **`MeterTick` is an in-process counter, not a `Payable` charge** —
  `durable/src/lib.rs:108-112`. The named single seam. *Cross-ref STAND-INS #7.*
  Effort M, high, reviewed-go (rides pg-dregg S3).
- **`VerifiedConservingStore` Poseidon2 root + on-chain `Payable` are S3-gated** —
  `durable/src/verified.rs:65-73`. Effort S once S3 flips, high, needs-a-decision.

### Needs deepening / DX / missing
- **No real multi-process restart test** (in-process teardown only) —
  `lib.rs:131-142`. Effort M, high, reviewed-go.
- **No cross-lease dedup test** (key is compound + safe, just unproven at scale)
  — `settle.rs:14-28`. Effort S, med, safe-autonomous.
- **No workflow progress surface; no meter-outbox operator view** — `lib.rs`.
  Effort M, med/high, mixed (likely control-plane).
- **No meter soft-limits / over-budget hooks** (hard-fail only) — `lib.rs:84-87`.
  Effort M, med, needs-a-decision.

---

## HOSTING-BILLING / METERING (`control/hosting_meter.rs`, `control/settle_ledger.rs`)

**Solid:** the price-list + charge model (publish/uptime/bandwidth/cert/build),
`ceil_div` rounding, and the per-period conserving settlement, all tested end to
end (charge → lapse → over-budget refusal).

### Half-built / stubbed
- **Bandwidth counter integrated but the gateway→meter→charge flow is unproven** —
  `hosting_meter.rs:19-42`; no end-to-end test of bytes flowing from serve to
  charge. Effort M, high, reviewed-go.
- **Free-tier is hardcoded `free()` in tests; no prod switch** —
  `hosting_meter.rs:101-110`. Effort S, med, safe-autonomous. *(Top-10 #8.)*
- **`cert_units_per_issue` priced but no cert provisioner wired** —
  `hosting_meter.rs:77`. Effort M, med, needs-a-decision.

### Needs deepening / missing
- **Integer-only rounding; no financial-precision model** (rounding accumulates
  at scale; no $↔unit policy) — `hosting_meter.rs:114-127`. Effort M, high,
  needs-a-decision.
- **Bandwidth roll-up period undefined / not config** — `settle_ledger.rs`.
  Effort M, high, reviewed-go.
- **No rate-card API / pricing transparency** — `hosting_meter.rs:68-80`. Effort
  S, high, safe-autonomous. *(Top-10 #8.)*
- **No billing dashboard, no quotas/alerts, no usage export, no multi-tenant
  isolation test** — Effort S–M, med/high, mixed (quotas/alerts high).

---

## LEASE BRIDGE + FIAT RAIL (`bridge/`, `gateway/funding.rs`, `demo/stripe-receiver/`)

**Solid:** the watch→fulfill→reap loop + durable metering; the fail-closed
funding gate (`gateway/src/funding.rs:99-141` — `AttestedFunding::empty()` admits
nothing, `from_verified_source` is the LEASE-1a verified wire); the
stripe-receiver's *real* breadstuffs HMAC verify + replay-window + consume-once +
`Effect::Mint`.

### Half-built / stubbed
- **`MockFeed` / `Lease` mock are the dev source; verified read is feature-gated**
  — `bridge/src/watch.rs:254-282`, `bridge/src/lib.rs:142-170`. *Cross-ref
  STAND-INS #8/#9.* The transport that fetches receipt-log records from a live
  node is the remaining step (`dregg_verify.rs:69-76`). Effort M, high,
  reviewed-go.
- **Cap-grade admission is an enum check, not the real `gate_effect_set`** —
  `bridge/src/lib.rs:258-289`. Effort S, high, safe-autonomous (swap when
  polyana-dregg-bridge is available).
- **Stripe receiver is a single-process demo** — `demo/stripe-receiver/src/main.rs`
  (real crypto, no HA/persistence/dedup-across-instances). Effort L, med,
  needs-a-decision (on-ramp topology).

### Needs deepening / missing
- **No refund→burn / chargeback handling** (`charge.refunded`,
  `charge.dispute.created`) — `demo/stripe-receiver/`. Effort M, high,
  needs-a-decision.
- **No fiat→credit ledger view** (payment X → credit for lessee Y); no webhook
  delivery observability / dead-letter. Effort M, high, mixed.
- **No lease provisioning ceremony / lifecycle observability** (no "fund this
  lessee for X compute" flow; no budget-utilization view). Effort M, high,
  mixed.

---

## ADMIN PORTAL (`ops/`)

**Solid:** read-only aggregation across node / gateway / Postgres meter / bridge
relayer / Docker logs, all defensive (failures degrade to `None`, never a false
all-clear) — `ops/src/aggregate.rs`, `pg.rs`, `bridge.rs`, `docker.rs`.

### Half-built / needs deepening
- **Observability only — no control actions** (no restart/pause/fund/cancel; any
  action means SSH) — `ops/`. Effort M/L, high, needs-a-decision.
- **Coarse authz** (Caddy forward-auth + a binary `OPS_REQUIRE_CAP`; no RBAC
  tiers) — `ops/src/main.rs:94-98,242-263`. Effort M, med, needs-a-decision.
- **No admin audit trail** (who did what, when) — Effort M, med,
  safe-autonomous.
- **Hard-coded alert thresholds; logs capped at 2000 lines** —
  `ops/src/bridge.rs:487-541`, `main.rs:352-378`. Effort S/M, low/med,
  safe-autonomous.

### Missing
- **MTTR tooling on a PAGE** (restart/logs/config from the dashboard), **bulk
  export / scheduled reports**, **economy conservation audit** (total minted vs
  charged), **TLS on the alert webhook sink** — Effort S–M, med, mixed.

---

## Cross-cutting

- **Per-resource metrics** — `gateway/src/main.rs:203` (per-gateway only; no
  per-site/bucket/app labels). Blocks accurate billing + observability. Effort M,
  high, reviewed-go.
- **The `dregg-verify` AGPL flip** underlies the on-chain dimension of hosting,
  storage, lease-read, and metering (*Cross-ref UNDER-WIRED #19*). A deliberate
  license-isolation boundary; the verified read paths are built behind it.
- **Exactly-once across restarts** is solid at the metering layer
  (`NodeApiSettlement`, durable dedup) but **not** yet for daemon workload
  tracking or pre-fulfillment lease dedup (control-plane in-memory state) —
  worth an explicit pass before a live fleet.

---

## What is genuinely solid (no immediate work)

- The control-plane scheduler/orchestrator core (place→provision→fulfill→reap,
  lease-gated, lapse handling).
- Per-period lease metering, exactly-once across restart (`NodeApiSettlement` +
  the conserving ledger + `(lease, period)` dedup).
- All compute-tier *sandboxes* (wasmi / wasmtime / Caged) and the microVM *VM
  lifecycle*; clean hardware-gated refusals (no fake successes).
- The host-API cap-gate / meter / conserving-ledger / receipt spine.
- The deploy clone→build→publish durable workflow + its deny-default build
  sandbox + symlink refusal.
- The fail-closed funding gate (LEASE-1a) and the stripe-receiver's real
  verify+mint crypto.
- The ops read-only aggregation (defensive, no false all-clears).
- The receipt protocol (prev-hash-chained, ed25519, seq-bound).
