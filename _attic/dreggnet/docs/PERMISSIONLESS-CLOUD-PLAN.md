# The permissionless verifiable cloud — surpassing Liftoff

The plan for the headline FEATURESET pillar (`docs/OVERNIGHT-GOAL.md` §2): build
DreggNet into THE permissionless cloud — bigger and better than Liftoff
(`@liftoffday`) — and lean hard into the structural differentiators Liftoff
*cannot* match. This document is the what-is gap analysis + the buildable,
prioritized plan an autonomous run executes.

The one-line thesis: **Liftoff is a KYC-free host you trust; DreggNet is a
permissionless host you verify.** Same developer convenience (push → live, pay in
token, no gatekeepers), but the served bytes, the compute, and the bill are all
re-witnessable against a committed cell — the host *cannot* lie about what it
served or what it charged. That is a different category, not a better Liftoff.

---

## 1. Liftoff — what it is

`liftoff.day` / `@liftoffday` markets itself as the KYC-free hosting layer for
crypto: "launch a token with a real website on Solana." The offering, as pitched:

- **Hosting the whole stack, no gatekeepers** — websites, servers, SSL certs,
  automatic deployments, custom domains. No ID, no credit card, no approval queue.
  "You ship, we host."
- **The chain is your account** — a wallet, not a signup form, is your identity.
- **Pay in `$LIFTOFF`** — the platform token is the unit of account for hosting.
- **A launchpad twist** — it couples a token launch to a real hosted site
  (Solana launchpad lineage), so a project ships its coin and its web presence
  together.

What it is, structurally: **a centralized hosting operator with a crypto
front-door.** The blockchain is the *payment and identity rail*; the hosting
itself is ordinary trusted infrastructure. You still trust Liftoff's servers to
serve the bytes you uploaded, to run the code you deployed, and to bill you
honestly. There is no disclosed mechanism by which a visitor or a tenant
cryptographically *verifies* what was served or what was charged.

Adjacent prior art, for calibration (all centralized-trust or storage-only):

| project | what it is | trust model |
|---|---|---|
| **Liftoff** | KYC-free hosting + Solana launchpad, pay-in-token | trust the host |
| **Fleek** | Git push → deploy to IPFS/Filecoin; great DX | trust the gateway / pin |
| **Akash / Spheron** | decentralized compute marketplaces (cheap VMs/containers) | trust the provider node |
| **Arweave / AR.IO** | permanent storage + verifiable gateways | content-addressed storage; no compute |

The unoccupied seat: a host with Fleek's push-to-deploy DX, Akash's real compute,
Arweave's content-verifiability — **and** per-request, per-charge, light-client
verifiability of the *operated* result. That seat is DreggNet's.

---

## 2. Gap analysis — Liftoff feature × DreggNet status

Status is graded against HEAD of this repo. LIVE = code-proven here; PARTIAL =
core wired, a named seam open; GAP = not built yet. File paths are the grounding.

| Liftoff feature | DreggNet status | Where / the seam |
|---|---|---|
| **Static websites** | **LIVE** | `webapp/src/hosting.rs` `SiteCell` (site = cell), cap-gated publish + `PublishReceipt`, served by `gateway/src/hosting.rs` `SiteHostHandler` over `<name>.dregg.works`. |
| **SSL certs** | **PARTIAL** | Wildcard `*.dregg.works` TLS via Caddy DNS-01 is specced (`docs/WEB-HOSTING.md` §3) but owned by the `deploy/` lane; per-(custom)-domain cert issuance is unbuilt. |
| **Custom domains (BYO)** | **GAP** | Only `<name>.dregg.works` subdomains. No BYO-domain binding, DNS-verification, or per-domain cert automation. |
| **Auto-deploy (git push → build → host)** | **GAP** | The keystone DX feature. No git clone, no build step, no publish pipeline. Today: publish a *pre-built* directory via `dreggnet-host`. |
| **Persistent servers** (long-running instances) | **PARTIAL** | Fly-compatible machines API is LIVE for CRUD + lease-gated admission (`gateway/src/route.rs`, `types.rs`), but machine records are in-memory + request-scoped; no durable long-running server process. |
| **The deploy CLI / ship→host DX** | **PARTIAL** | `dregg-cloud lease/run/status` is operator-facing (`cli/src/main.rs`), `wat`-only. No `dregg-cloud deploy` app-developer onramp. |
| **Pay-in-token** | **PARTIAL → LIVE rail** | The lease economy is real: meter per step, budget-gate, exactly-once settlement as a real `Transfer` (`control/src/{orchestrator,settle_ledger,node_api}.rs`, `durable/`). *Hosting itself* is not yet metered/billed — compute is subsidized in the early era. |
| **No-KYC / chain-as-account** | **LIVE (surpasses)** | `webauth/` cap-auth: a wallet-held `dga1_` credential, ed25519 caveat-chain, attenuable, offline-verifiable. Not just "no KYC" — *fine-grained attenuable delegation*. |

Supporting LIVE capabilities Liftoff has no equivalent of: **object storage**
(`storage/`, trustless `verified_get`), **durable execution** (`durable/`,
crash-resume exactly-once), **agent-served web APIs** (`webapp/router.rs`,
`LeasedRouter` → `402`), the **service catalog** (`docs/SERVICES.md`, 13 services
on one cell-shaped template).

**The five things to build** (the GAP/PARTIAL rows, in §3): auto-deploy-from-git,
custom domains, persistent servers, the `dregg-cloud deploy` DX, metered-`$DREGG`
hosting billing.

---

## 3. The five features — design

Each is designed to reuse the most already built (the `docs/SERVICES.md` "least
new substrate first" rule): a new feature is a thin weld over the site cell, the
lease economy, the durable layer, and the machines API — not a new engine.

### 3.1 Auto-deploy-from-git — the keystone DX

The flow Liftoff sells as "you ship, we host," made verifiable: a git repo →
build → publish a site/server cell → live, every step receipted.

```
  dregg-cloud deploy <git-url|.>                    (one command)
    │
    ▼  ① CLONE       — fetch the repo at a pinned commit (the source commitment)
    ▼  ② DETECT      — framework heuristic → a BuildPlan (static | node | …)
    ▼  ③ BUILD       — run the build in an owned-sandbox tier (Caged/MicroVm — fail-closed seams today), cap-bounded,
    │                   metered against a deploy-lease; output = a dist/ tree
    ▼  ④ PUBLISH     — SiteRegistry::publish(dist) → a SiteCell + PublishReceipt
    │                   (OR register a server machine, for a server target — §3.3)
    ▼  ⑤ LIVE        — served at <name>.dregg.works (or the bound custom domain)
```

Design decisions:

- **The build IS a durable workflow.** Model the pipeline as a `dreggnet-durable`
  orchestration whose activities are `Clone`, `Build`, `Publish` — so a deploy is
  crash-resumable, exactly-once, and metered the same way compute leases are. A
  build that crashes mid-way resumes from its last checkpoint; the deploy receipt
  is the durable history. This is a direct reuse of `durable/`.
- **The build runs in a sandbox tier.** A `BuildPlan` carries a `cap_tier`; an
  arbitrary repo build (untrusted code) routes to `Caged` (Linux seccomp+Landlock)
  or `MicroVm` (Firecracker) via the existing `exec/` tier map — never the bare
  host. Static-only builds (no build step, just publish a directory) need no tier.
- **Framework detection** is a small, explicit heuristic crate (`dregg-deploy`
  core): `index.html` at root → static; `package.json` with a `build` script →
  node build → publish the configured output dir; a `Dockerfile`/server entry →
  the server target (§3.3). Detection is overridable by a `dregg.toml` in the repo.
- **The source commitment.** The cloned commit hash is recorded in the
  `PublishReceipt`, so "this site was built from *that* commit" is provable —
  reproducibility Liftoff cannot offer.

New crate: `dregg-deploy` (the build-plan + orchestration), driven by the CLI
(§3.4). Reuses `dreggnet-durable`, `dreggnet-exec`, `dreggnet-webapp::hosting`.

**Tonight-safe subset:** the `BuildPlan` model + framework detection + the
clone/build/publish durable orchestration + the static and node paths, run
locally end-to-end (clone a local/file repo → build in the wasm/Caged tier →
publish a SiteCell → serve over local TCP), fully tested. **Reviewed-go:** a
public webhook receiver (push-triggered auto-deploy from a hosted git provider)
and any live go-live — guardrail: "enabling auto-deploy/CI-deploy" is REVIEWED-GO.

### 3.2 Custom domains — BYO-domain → a dregg-hosted site

Bind an owner's own domain (`shop.example.com`) to a published site cell, with
verification, DNS guidance, and automatic certs.

```
  dregg-cloud domains add shop.example.com --site blog
    │
    ▼  ① BIND        — a DomainBinding cell { domain, site_cell, owner } (cap-gated)
    ▼  ② CHALLENGE   — emit a DNS TXT challenge (_dregg-verify.shop.example.com = nonce)
    │                   OR a CNAME target (shop.example.com → blog.dregg.works)
    ▼  ③ VERIFY      — poll DNS until the TXT/CNAME proves control → mark verified
    ▼  ④ CERT        — gateway answers Caddy on-demand-TLS `ask` for verified domains;
    │                   Caddy mints a per-domain cert over ACME HTTP-01
    ▼  ⑤ ROUTE       — gateway Host resolution extended: custom Host → bound site cell
```

Design decisions:

- **A `DomainBinding` is a cell**, cap-gated and receipted, exactly like a site:
  the binding `domain → site_cell` is committed and re-witnessable (this is the
  `docs/SERVICES.md` row 8 nameservice shape, turned outward).
- **Verification is a challenge cell.** The TXT-nonce (or CNAME) proof of control
  is the standard ACME-style challenge; the *binding* records the verified flag +
  the verifying turn, so "who proved control of this domain, when" is provable.
- **Certs reuse the on-demand-TLS `ask` hook** already named in
  `docs/WEB-HOSTING.md` §3: extend the gateway's `/internal/site-exists` endpoint
  to also answer for *verified custom domains*, so Caddy only mints a cert for a
  domain a tenant has proven they control (rate-limit-safe, no DNS-plugin needed).
- **Gateway routing** extends `site_name_from_host` (`gateway/src/hosting.rs`) with
  a `host → site_cell` map keyed on bound custom domains, beside the
  `<name>.dregg.works` subdomain path.

**Tonight-safe subset:** the `DomainBinding` cell + cap-gate + receipt, the
challenge/verify state machine (TXT + CNAME), the gateway custom-Host resolution,
and the extended `ask` endpoint logic — all in-process and tested (a fake DNS
resolver drives the verify path). **Reviewed-go:** pointing real DNS / issuing
real public certs (the live `deploy/` Caddy edit + a real domain).

### 3.3 Persistent servers — the fly.io-machines model, real

Today a "machine" is request-scoped: created, runs a workload, reaped. Liftoff
sells long-running server instances. Make a machine a genuine durable, metered,
cap-bounded long-running server.

```
  POST /v1/apps/{app}/machines  { config, server: { entry, port } }
    │                            (or: dregg-cloud deploy . --server)
    ▼  ① ADMIT       — lease-gated (existing bridge gate, refuse unfunded/over-grade)
    ▼  ② LAUNCH      — fulfill the record as a LONG-RUNNING owned-sandbox workload (a server
    │                   entrypoint that stays up), as a durable workflow → crash-resume
    ▼  ③ INGRESS     — gateway routes the app's data-plane traffic to the machine
    │                   (over the wireguard mesh on a real fleet; in-process locally)
    ▼  ④ METER       — per-period (wall-clock uptime) StandingObligation tick → settle
    ▼  ⑤ LIFECYCLE   — start/stop/reap; a lapsed lease reaps the server
```

Design decisions:

- **Persistence = the durable layer + a persistent store.** A server machine is a
  long-lived `dreggnet-durable` workflow; its record lives in a persistent store
  (the named `duroxide-pg` rung), so machines survive a control-plane restart
  (today they vanish — in-memory `HashMap`). The create→fulfill seam (the named
  rung) is the wire from "record admitted" to "durable server launched."
- **A server workload shape.** Generalize the fixed 2-step demo workflow to a
  long-running entrypoint (an owned sandbox workload that serves, rather than computes a
  value and exits) with a health probe — the gateway ingress routes to it.
- **Metering is per-period uptime, not per-step.** Reuse `StandingObligation`: a
  server bills per wall-clock period (the rent model already in
  `node_api.rs`'s `RENT_SLOT`/`PERIOD_SLOT`), and a lapsed lease reaps the server
  — the same "no run beyond what the lease authorizes" invariant, applied to
  uptime.
- **Ingress over the mesh.** The `control/src/mesh.rs` WireGuard plane already
  reaches a fleet node; the gateway proxies a machine's app traffic to its ingress
  over the overlay (live two-node handshake is the deploy rung).

**Tonight-safe subset:** the persistent-server workload shape + the create→fulfill
durable launch seam + per-period uptime metering + lifecycle (start/stop/reap) +
a persistent machine record (SQLite store), proven in-process / over LocalProvider
end-to-end. **Reviewed-go:** the live fleet boot (Hetzner/persvati, real KVM
Firecracker, the two-node mesh handshake).

### 3.4 The `dregg-cloud deploy` CLI — the ship→host onramp

The single app-developer front door. Today's CLI is operator-facing
(`lease/run/status`); add the developer verbs that drive §3.1–§3.3.

```
  dregg-cloud login                 # bind a wallet-held cap credential as the account (webauth)
  dregg-cloud deploy ./site         # build (if needed) + publish a site cell → live URL
  dregg-cloud deploy <git-url>      # clone + build + publish (the auto-deploy flow, §3.1)
  dregg-cloud deploy . --server     # build + launch a persistent server machine (§3.3)
  dregg-cloud domains add <domain>  # bind + verify a custom domain (§3.2)
  dregg-cloud ls / dregg-cloud logs / dregg-cloud destroy
```

Design decisions:

- **`deploy` is the verb.** It detects the target (static / node / server) and
  drives the right §3.1–§3.3 orchestration, prints the live URL + the receipt, and
  records the deploy in the local state store (the existing `cli` registry shape).
- **`login` binds the cap account.** Reuse `webauth`'s `dga1_` credential: the CLI
  holds an attenuable credential from the wallet — the chain-as-account, but
  *delegable* (a CI runner gets a deploy-only attenuation, not the root key).
- **Keep the operator CLI.** `lease/run/status` stay; `deploy/login/domains/ls/
  logs/destroy` are the new developer surface over the same control plane.

**Tonight-safe subset:** the new CLI verbs wired to the §3.1–§3.3 orchestrations,
all driving the local/in-process path, with e2e tests (extend `cli/tests/e2e.rs`).
**Reviewed-go:** anything that publishes to the live public edge.

### 3.5 Metered-`$DREGG` hosting billing

The lease economy already meters + settles compute. Extend it into a hosting
billing rail so every hosting resource is a metered, receipted, `$DREGG`-settled
charge — the same exactly-once rail (`control/src/settle_ledger.rs`), new meters.

| resource | meter | settles as |
|---|---|---|
| **site publish** | per-publish + per-MB stored | a `Payable` charge on the publish turn |
| **bandwidth** | per-GB served (the gateway counts bytes per site cell) | a per-period roll-up charge |
| **server uptime** | per wall-clock period (§3.3) | a `StandingObligation` tick |
| **cert** | per issued/renewed cert (§3.2) | a per-issuance charge |
| **deploy build** | per build-minute in the sandbox (§3.1) | metered on the build workflow |

Design decisions:

- **One meter shape, many resources.** Each resource is a `Pricing` over a funded
  account, refused before the operation commits if over budget — the exact
  `storage/src/meter.rs` pattern, generalized. A hosting account is a funded
  `execution-lease` cell; the bill is the sum of metered turns against it.
- **Bandwidth is the new counter.** The gateway already serves per-site; add a
  per-site byte counter that rolls into a per-period charge (the only genuinely
  new metering surface — everything else reuses an existing meter).
- **Settlement reuses the durable ledger.** Every hosting charge goes through the
  same exactly-once `settle_ledger` + `NodeApiSettlement` real-`Transfer` path, so
  a billing tick is as crash-safe and re-witnessable as a compute tick.

**Tonight-safe subset:** the hosting-meter model (the per-resource `Pricing` + the
bandwidth byte-counter + the charge-before-commit gate) wired to the lease/Payable
rail in-process, tested (publish/serve/uptime charge the funded account; over-
budget is refused). **Reviewed-go:** charging real money on the live edge (the
early era is subsidized; flipping real billing on is an ember decision).

---

## 4. The SURPASS — structural differentiators

These are not features to catch up on; they are the category gap. Build the
featureset above *on top of* these, and DreggNet is not a better Liftoff — it is a
host you verify instead of trust. Each is already real or near in this repo.

- **Verifiable hosting (the headline).** A site IS a cell carrying a `content_root`
  commitment (`webapp/src/hosting.rs`); the served bytes re-witness against it. The
  visitor's browser can re-verify, with no trust in the server, that what it was
  served is the genuine published cell — the `deos-view` trustless cell projection
  (breadstuffs, AGPL) the portal already uses. *Liftoff you trust; dregg you verify.*
  The host cannot tamper with a byte without the visitor catching it.
- **Verifiable billing.** Every charge is a receipted, exactly-once, conserving
  `Transfer` (`control/src/settle_ledger.rs`) — the bill is re-witnessable, not a
  number on a dashboard. The host cannot overcharge.
- **Private compute.** The M2 shielded-transfer rail (breadstuffs) means a tenant's
  values + payments can be confidential while still verified — ZK hosting Liftoff
  has no analog of.
- **Durable / receipted execution.** Every workload is crash-resumable and
  exactly-once-metered (`durable/`); every run leaves a receipt. A deploy, a
  request, a server period — each is a durable, witnessed transition.
- **Agent-native.** Host an *agent*, not just a site: agent-served web APIs
  (`webapp/router.rs`), BYO-key Hermes loops, and agent coordination over the
  intent ring / branch-stitch. The cloud built for autonomous software.
- **Attenuable cap-accounts.** "No KYC" is the floor; the real differentiator is
  the `webauth` cap credential — an attenuable, offline-verifiable `dga1_` token. A
  tenant delegates a *deploy-only*, *one-site*, *time-boxed* sub-capability to a CI
  runner or a teammate without sharing the root key. The cipherclerk wallet is the
  account; delegation is fine-grained and revocable.

---

## 5. The buildable plan — prioritized, dependency-ordered

The dependency order (foundation → keystone → fan-out):

```
  ① hosting-billing meter model (§3.5)   ── the rail every feature bills on
        │
  ② dregg-deploy core + CLI verbs (§3.4) ── the onramp every feature is driven by
        │
        ├─ ③ auto-deploy-from-git (§3.1)  ── the keystone DX (build → publish workflow)
        ├─ ④ custom domains (§3.2)         ── the DomainBinding cell + gateway routing
        └─ ⑤ persistent servers (§3.3)     ── the create→fulfill durable launch seam
```

Rationale: the **meter model (①)** is the floor every other feature charges
against, so it comes first (and it is a near-pure reuse of `storage/src/meter.rs`).
The **deploy core + CLI (②)** is the shared driver. Then the three product
features **(③④⑤)** fan out in parallel — each a disjoint new crate/module, so a
swarm can build them concurrently without shared-manifest clobber.

### Priority worklist (highest value first)

1. **`dregg-deploy` core + the build durable workflow (③).** The keystone DX. New
   crate: `BuildPlan` + framework detection + the `Clone/Build/Publish` durable
   orchestration. Static + node paths, local end-to-end. *Highest value — it is the
   one feature that makes DreggNet feel like Liftoff's "you ship, we host."*
2. **The hosting-billing meter model (①).** The bandwidth byte-counter + the
   per-resource `Pricing` + charge-before-commit, wired to the lease/Payable rail.
3. **The `dregg-cloud deploy` CLI verbs (②).** `login`/`deploy`/`domains`/`ls`/`logs`/
   `destroy` over the control plane, e2e-tested.
4. **Custom domains (④).** The `DomainBinding` cell + challenge/verify + gateway
   custom-Host routing + the on-demand-TLS `ask` extension.
5. **Persistent servers (⑤).** The long-running server workload shape + the
   create→fulfill durable launch seam + per-period uptime metering + a persistent
   machine store.
6. **Wire the differentiators outward.** The trustless-serving wrap on hosted
   sites (the `content_root` → `deos-view` re-witness path), and the
   verifiable-billing receipt surfaced per charge — the §4 headline made tangible.

### The safe-autonomous-tonight subset vs reviewed-go

Per `docs/OVERNIGHT-GOAL.md` guardrails: build + prove + test + stage; reversible;
green-gated. Live go-lives and anything outward-facing or hard-to-reverse stop and
queue to `MORNING-REVIEW.md`.

**SAFE-AUTONOMOUS (build it tonight):**

- All five features' **code + models + orchestrations + tests**, driven through
  the **local / in-process / LocalProvider** path — the same path the existing
  crates prove themselves on (publish→serve over local TCP, durable workflow over
  on-disk SQLite, lease-gated admission, in-process metering).
- The `dregg-deploy` crate (clone/build/publish workflow, static + node), the
  hosting-meter model, the new CLI verbs, the `DomainBinding` cell + verify state
  machine (fake-DNS-driven), the persistent-server workload shape + launch seam +
  uptime meter + persistent store.
- Cross-build green for Linux (`cargo zigbuild`) where the gateway is touched; the
  full `make test` gauntlet green before each commit.

**REVIEWED-GO (stop + queue, never autonomous):**

- A **public push-triggered webhook** auto-deploy receiver (a hosted-git
  integration) — "enabling auto-deploy/CI-deploy" is explicitly REVIEWED-GO.
- **Real DNS / real public cert issuance** for custom domains (the live `deploy/`
  Caddy edit, a real domain pointed at the edge).
- The **live fleet boot** for persistent servers (Hetzner/persvati, real KVM
  Firecracker, the two-node mesh handshake) — beyond the n4 devnet.
- **Charging real money** on the live edge (flip real hosting billing on) — the
  early era is subsidized; this is an ember decision.
- Any **public/store go-live** of the new developer CLI or the verifiable-hosting
  front door.

The dividing line is exactly the project's standing rule: the *code* and the
*verified local proof* are safe-autonomous; the *operated reality on the public
edge* is reviewed-go. Tonight the run builds the whole featureset to green and
stages it; the morning queue holds the go-lives.

---

## 6. Positioning

**Liftoff is a KYC-free host you trust; DreggNet is a permissionless host you
verify** — same push-to-deploy, pay-in-token, no-gatekeepers DX, but the served
bytes, the compute, and the bill are each re-witnessable against a committed cell,
so the host *cannot* lie. Not a better Liftoff — a different category.
