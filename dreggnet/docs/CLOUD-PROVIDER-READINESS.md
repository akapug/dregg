# Cloud-Provider Readiness — the "we're about to be a real cloud" gap map

A grounded (read-the-code, HEAD 2026-06-30) audit of DreggNet against the **full
cloud-provider capability surface** (AWS / GCP / fly.io / Vercel / Cloudflare /
Akash). The lens is blunt: *this is about to be a real, permissionless,
KYC-free cloud — what cloud-provider things have we NOT?*

The honest headline: **the compute/verifiability spine is genuinely strong, the
operator-facing plane is strong, and the customer-facing + abuse/legal/quota
plane is nearly empty.** DreggNet can *run and bill verified workloads*; it
cannot yet *responsibly open its doors to the public*, because the things that
keep a KYC-free cloud from being shut down or sued — an AUP, a takedown path, an
account-suspension switch, per-identity rate limits, a legal entity — do not
exist in the repo at all.

This doc is complementary to the existing honesty catalogs and reuses their
grounding rather than re-deriving it:
`docs/PERMISSIONLESS-CLOUD-PLAN.md` (the Liftoff featureset closure),
`docs/DEVWORK-PRODUCT.md` (the product dev-work list),
`docs/RED-TEAM-FINDINGS-2.md` (the adversarial isolation pass),
`docs/STAND-INS-CENSUS.md` / `docs/UNDER-WIRED-features.md` (the stand-ins).
Where an item is cataloged there, this doc cross-refs.

Grading: **HAVE** = code-proven here (file:line). **PARTIAL** = core wired, a
named seam open. **LACK** = not built. Criticality: **BLOCKER** = a responsible
public open-door is unsafe/illegal without it; **IMPORTANT** = expected of a real
cloud, painful to launch without; **NICE** = maturity. Effort: S <1d · M 1–5d ·
L 1–2wk · XL multi-week.

---

## 0. The permissionless-cloud existential risks (read this first)

A KYC-free, wallet-as-account, (early-era) subsidized cloud that **hosts arbitrary
static sites and runs arbitrary code** is, by construction, a magnet for phishing,
malware C2, spam relays, crypto-miners, DDoS-source workloads, and illegal content.
What separates a serious operator from a liability is **not** the compute sandbox
(ours is good — see below); it is the **content-layer + legal-layer controls** that
let the operator say "no", remove, suspend, and answer a subpoena. Those are
**absent from the repo today.** Each of these is, on its own, capable of getting
the cloud shut down by an upstream (Hetzner/registrar/Stripe/Cloudflare) or sued.

### E-1 — No Acceptable Use Policy / ToS / Privacy Policy / DMCA notice (BLOCKER)
`find` for `*tos* *terms* *acceptable*use* *privacy* *aup* *dmca*` across the repo
returns **nothing**. There is no legal entity named, no abuse contact, no
`security.txt`, no DMCA designated-agent notice, no data-processing/privacy
statement. Consequences that bite immediately on a public open:
- No contractual basis to remove a tenant's content or terminate them — every
  takedown becomes an ad-hoc decision with no policy to point to.
- No DMCA §512 safe harbor (US) → the operator is directly liable for hosted
  infringement instead of shielded by notice-and-takedown.
- No NCMEC/CSAM reporting posture — a legal *obligation*, not optional, the moment
  you host user content. Missing it is a criminal-exposure item.
- No GDPR/CCPA privacy basis while `storage/` holds user bytes and `webauth`/
  console process identity — and storage has **no delete/TTL/erasure path**
  (see S-7), so a data-subject deletion request is currently unanswerable.
- Stripe (the live fiat rail, `demo/stripe-receiver/`) requires an AUP + business
  identity; a KYC-free passthrough to anonymous compute risks the account.
- **Effort:** legal docs S–M (writing), but **gating** — nothing else ships
  responsibly to the public without them. This is the #1 blocker.

### E-2 — No content moderation / takedown / abuse-report pipeline (BLOCKER)
`rg` for `abuse|moderat|takedown|dmca|phishing|report.*abuse` finds **no code**
outside the gateway's slow-loris hardening comment (`gateway/src/main.rs:36`).
There is no abuse-report endpoint, no content scanning (no SafeBrowsing/known-bad
hash check on published sites, no malware scan on uploads), no takedown workflow,
and no de-publish/de-route control surfaced anywhere.
- A published site is `webapp/src/hosting.rs::SiteRegistry` + a `<name>.dregg.works`
  route in `gateway/src/hosting.rs`; nothing can *unpublish* it operationally
  except deleting the in-process cell. There is `cli ... destroy` for the *owner*,
  but no *operator* takedown of someone else's content.
- **The verifiability pitch cuts against this and must be reconciled.** The
  headline ("the host *cannot* tamper with a byte") is about *integrity*, not
  *availability*: takedown is de-publish / de-route / suspend, which is fully
  compatible — but the repo has no such operator control today.
- **Effort:** M for an abuse-report intake + a de-publish/de-route operator
  action; L for any automated scanning. BLOCKER for the manual-takedown minimum.

### E-3 — No operator account-suspension / kill-switch (BLOCKER)
The only revocation in the product layer is `sandstorm-bridge/src/net.rs:108`
(`revoke_outbound`, grain network re-confinement) and lease *lapse* (compute is
reaped when a lease runs dry, `control/src/hosting_meter.rs:521`). There is **no
"suspend this subject across all their resources"** control: a tenant's sites,
servers, domains, and buckets cannot be frozen by an operator in one action. The
ops dashboard is **read-only by design** — "no control actions; any action means
SSH" (`docs/DEVWORK-PRODUCT.md`, ADMIN PORTAL). Cap revocation exists in the
substrate but is not wired to a DreggNet operator-suspend flow. Without this, the
response to a live-abuse incident is manual SSH surgery, not a button.
- **Effort:** M (a subject→resources freeze that de-routes/halts; the cap-revoke
  primitive exists to build on). BLOCKER.

### E-4 — Sybil-free-of-charge + no per-identity rate limits (BLOCKER, economic)
Wallet = account (`console/src/scope.rs:4-16`), accounts are free to mint, and the
early era is **subsidized** (`HostingPricing::free()`, `control/src/hosting_meter.rs:99`).
The only abuse-limiter that bites is the funded-lease economic gate — and in a
free/subsidized era it does not bite. Meanwhile:
- The gateway has **connection-level** hardening only (slow-loris timeouts,
  body-size `413`, connection-concurrency cap — `gateway/src/main.rs:36-50`), but
  **no per-identity / per-IP request rate limiting** at the HTTP edge.
- Publish and domain-verify are **unbounded** (`docs/DEVWORK-PRODUCT.md` Top-10 #7:
  "a cap holder can republish / re-verify unbounded → DOS the bandwidth meter / DNS
  resolver"); `webapp/src/hosting.rs:589` has no publish rate-limit.
- Net: a free account can spray publishes, burn the bandwidth meter, hammer the DNS
  resolver, and mint unlimited sibling accounts. The compute *sandbox* is bounded
  (good), but the *surface* is open.
- **Effort:** S–M for per-identity publish/verify rate-limits + a gateway edge
  limiter; the deeper Sybil answer is a real (non-free) price floor or a
  proof-of-work/stake on account creation (needs-a-decision). BLOCKER to open
  doors without it.

### E-5 — No egress abuse control / monitoring on the run path (IMPORTANT→BLOCKER)
Compute *isolation* is strong (E-isolation note below), but a perfectly-sandboxed
workload can still be **used to attack others**: outbound DDoS, spam relay, crypto
mining, scraping, port-scanning. `sandstorm-bridge/src/net.rs` has an outbound
confinement *policy* primitive, and the build sandbox uses an empty netns
(`docs/RED-TEAM-FINDINGS-2.md` D-1 fix), but there is **no egress allow/deny policy,
rate cap, or anomaly monitoring on the general `exec/` run path**, and no abuse
detection (a miner pegging CPU is "paid usage" today). An upstream sees DreggNet
IPs attacking the internet and null-routes the fleet. **Effort:** M (egress policy
+ basic outbound-rate/anomaly signal). IMPORTANT, trending BLOCKER at any scale.

### What is genuinely strong on the abuse front (do not re-solve)
The **compute-isolation** red-team pass (`docs/RED-TEAM-FINDINGS-2.md`) is real and
fixed: D-1 build runs in a deny-default sandbox (`env_clear`+allowlist, empty
netns, `RLIMIT_*`, `no_new_privs`); D-2 path-traversal/symlink-exfil refused;
D-3 fork-bomb/grandchild-reap bounded; SRV-1 persistent-server admission now reads
the **real funded balance** (not a self-asserted bool) + per-lessee/global quota +
sweep; PB-1/H-1 powerbox forgery closed with host-sealed HMAC. So **host RCE,
tenant-to-tenant escape, and resource-exhaustion-of-the-host are bounded.** The
existential gap is **content + legal + identity-economics**, not sandbox escape.

> **Bottom line on §0:** DreggNet is technically safe to *run* an untrusted
> workload, and dangerously unprepared to *be the named operator* of a public
> KYC-free host. The five items above are the difference between "a verifiable
> cloud" and "a verifiable cloud that survives contact with the public internet."

---

## 1. The capability gap map (by domain)

### Compute
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| WASM sandbox (wasmi + wasmtime/JIT, fuel) | **HAVE** | `exec/src/lib.rs:235-285,552-675` | — |
| Native cage (seccomp+Landlock, Linux) | **HAVE** | `exec/src/lib.rs:251-256` (shebang-scripts; ELF a later rung) | — |
| Firecracker microVM (KVM, jailed/direct) | **PARTIAL** | `exec/src/lib.rs:840-930` boots; **guest plane dead** — `call()` errors, vsock+JSON wire unbuilt (`exec/src/lib.rs:95-110`, STAND-INS #2) | IMPORTANT · M (reviewed-go, KVM) |
| Cap-tier map (sandbox grade ← lease grade) | **HAVE** | `exec/src/lib.rs:235-285` (`CapTier`) | — |
| Functions / FaaS (one-shot lease) | **HAVE** | `control/src/scheduler.rs:140-200` | — |
| Execution models (cron/streaming/escrow/agent) | **HAVE** | `exec/src/model.rs` (`::cron/::streaming/::escrow_bonded`) | — |
| Persistent long-running servers | **HAVE (core)** | `control/src/server.rs:72-85,505-650` durable lifecycle + uptime meter; **no gateway→server ingress routing**, **health is a stub** (`server.rs:1104`) | IMPORTANT · M |
| Fly-machines-compatible API (CRUD) | **HAVE** | `gateway/src/route.rs`, `gateway/src/types.rs`, `gateway/src/gateway.rs:133-143` | — |
| GPU | **PARTIAL** | tier + probe + clean refusal wired (`exec/src/lib.rs:267-285,1023-1096`); no live passthrough provider | NICE · L (hw-gated) |
| Containers (Docker/OCI orchestration) | **LACK** | Firecracker only; no OCI scheduler | NICE · L |
| Autoscaling | **LACK** | fleet registry is read-only per tick; round-robin only (`control/src/fleet.rs`) | IMPORTANT · L |

### Storage & data services
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| Object storage (buckets) + trustless `verified_get` | **HAVE (core)** | `storage/src/bucket.rs:60`, `registry.rs:225`; **not mounted in the gateway** (no `gateway/src/storage.rs`, DEVWORK Top-10 #1) | IMPORTANT · M |
| Object durability | **PARTIAL** | `BucketRegistry` is **in-memory** (`storage/src/registry.rs:42`), lost on restart; on-chain write rides `dregg-verify` flip | BLOCKER · L (see R-1) |
| Lifecycle / TTL / versioning / soft-delete / signed-URLs | **LACK** | none in `storage/` | IMPORTANT (TTL/erasure tie to E-1 privacy) · M |
| Backups / snapshots | **LACK** | durability via durable-layer checkpoints, not snapshots | IMPORTANT · M |
| Managed DB-as-a-service (Postgres) | **PARTIAL** | durable layer can ride `duroxide-pg` (`durable/src/lib.rs:307`); **not a tenant-facing DB product** | IMPORTANT · L |
| KV / database service | **PARTIAL (near)** | kvstore cell in breadstuffs; thin wrap pending (SERVICES.md #2) | NICE · M |
| Redis / cache | **LACK** | — | NICE · M |
| Message queues / pub-sub | **LACK** | SERVICES.md #3/#4 roadmap | NICE · M |
| Secrets / KMS | **LACK** | SERVICES.md #7 roadmap; build env is cleared, no secret injection | IMPORTANT · M |
| Search | **LACK** | — | NICE · L |
| IPFS pin/fetch (content-addressed) | **HAVE (core)** | `dregg-ipfs/src/{client,bridge}.rs`; on-chain write reviewed-go | — |

### Networking
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| Private overlay (WireGuard / Tailscale mesh) | **HAVE** | `control/src/mesh.rs` (`100.64.0.0/10`, Tailscale + self-managed) | — |
| Per-workload dispatch over overlay | **HAVE** | `control/src/mesh.rs`, `gateway/src/gateway.rs:25-75` | — |
| Load balancing | **PARTIAL** | round-robin + capacity tracking only (`control/src/fleet.rs`); no weighted/least-loaded | IMPORTANT · M |
| Gateway→persistent-server ingress routing | **LACK** | `gateway/src/route.rs` has no machine-ingress handler | IMPORTANT · M |
| Edge HTTP hardening (slow-loris/413/conn-cap) | **HAVE** | `gateway/src/main.rs:36-50` | — |
| Per-identity / per-IP rate limiting (edge) | **LACK** | see E-4 | BLOCKER · S–M |
| DDoS protection / WAF | **LACK** (relies on upstream Caddy/Cloudflare, unconfigured) | — | IMPORTANT · M |
| CDN / edge caching | **LACK** | no cache layer, no `Cache-Control`/`ETag` (DEVWORK) | IMPORTANT · M |

### Identity / IAM
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| Account = wallet-held cap (`dga1_` ed25519 caveat-chain) | **HAVE (surpasses)** | `webauth/src/cred.rs:42-117`, `console/src/scope.rs:4-16` | — |
| Attenuable, offline-verifiable delegation | **HAVE (surpasses)** | `webauth/src/grant.rs:48-61`, `exec/src/meter.rs:185-212` | — |
| Organizations / teams / sub-accounts | **LACK** | scope is single-subject only (`console/src/scope.rs:5-16`); "everything is one cap-account" (DEVWORK CLI) | IMPORTANT · L |
| Roles / RBAC | **PARTIAL** | flat cap vocabulary (`ops-admin`/`grafana-view`/`gateway-admin`, `webauth/src/grant.rs:21-46`); no role hierarchy | IMPORTANT · M |
| Service accounts | **LACK** | delegation-via-attenuation only; no distinct type | NICE · M |
| API keys / programmatic tokens | **PARTIAL** | credential-only (`dga1_` via `Authorization: Bearer`, `webauth/src/server.rs:56-85`); no key-mint/rotate/revoke UX | IMPORTANT · M |

### Billing
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| Usage metering (per-resource) | **HAVE** | `control/src/hosting_meter.rs:66-128`, `exec/src/meter.rs` | — |
| Exactly-once settlement (WAL dedup + on-chain memo) | **HAVE** | `control/src/settle_ledger.rs:52-213`, `node_api.rs:27` | — |
| $DREGG token + Stripe fiat on-ramp | **HAVE** | `demo/stripe-receiver/`, `runbooks/STRIPE-SETUP.md` | — |
| Spending limits / budget caps | **HAVE** | `exec/src/budget.rs:348-433`, `hosting_meter.rs:315` | — |
| Free tier (subsidy) | **HAVE** | `HostingPricing::free()` `control/src/hosting_meter.rs:99` (note E-4) | — |
| Cost estimation (pre-check) | **HAVE (lib)** | `hosting_meter.rs:114-127`; **no `dregg estimate` CLI** (DEVWORK) | NICE · S |
| Verifiable per-charge receipt | **HAVE (differentiator)** | `settle_ledger.rs`, conserving `Transfer` | — |
| INVOICES (a generated bill document) | **HAVE (lib) · console wiring pending** | the `billing` crate produces verifiable invoices with a receipt-trace: `Invoice` + `LineItem` + `SealedInvoice` + `invoices_for` (`billing/src/invoice.rs:77,289,327`), and `Invoice::verify_against_receipts` re-witnesses each line back to its `UsageReceipt`s, proven to equal the ledger balance (`billing/src/lib.rs:122-184`). Remaining: wire it into the console read plane (`/api/billing` returns empty until a `BillingSource` is bound — see FAKEOUTS-cloud M4) and add PDF/delivery | IMPORTANT · S |
| Refunds / disputes / chargebacks | **PARTIAL** | documented manual workflow, **not wired** (`runbooks/STRIPE-OPS.md` §2; no `charge.refunded`→burn relayer) | IMPORTANT · M |
| Rate-card API / pricing transparency | **LACK** | pricing hardcoded in Rust, no endpoint (DEVWORK Top-10 #8) | IMPORTANT · S |
| Low-balance alert (proactive notice) | **PARTIAL** | lapse *stops serving* (`hosting_meter.rs:521`) but no advance email/push warning | IMPORTANT · M |

### Observability
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| Metrics (Prometheus + Grafana) | **HAVE (operator)** | `gateway/src/metrics.rs:113-160`; 9 dashboards `deploy/observability/grafana/` | — |
| Health checks | **HAVE** | `gateway/src/status.rs:228-262` | — |
| Alerting | **HAVE (operator-only)** | `docs/MONITORING.md` §3; ops `/api/alerts` | — |
| Per-tenant runtime **log** aggregation / tail / search | **LACK** | `dregg-cloud logs` prints **cached local metadata**, not a tail (`cli/src/main.rs:1272-1304`); real log-tail is **operator-only** Docker tailing (`ops/src/docker.rs:113`) | BLOCKER · M |
| Distributed traces (customer) | **PARTIAL (internal)** | owned sandbox spans, not exposed | NICE · M |
| Per-tenant / per-resource status surface | **PARTIAL** | console models exist but use **fixtures**, live aggregation deferred (`console/src/source.rs`) | IMPORTANT · M |
| Public **status page** (customer uptime/incidents) | **LACK** | gateway `/` is operator-informational; portal is a cell viewer | IMPORTANT · M |

### DNS / domains
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| `<name>.dregg.works` subdomain serving | **HAVE** | `gateway/src/hosting.rs` (`SiteHostHandler`) | — |
| Custom-domain BYO bind + TXT/CNAME verify | **HAVE (core, hardened)** | `dregg-domains/src/{lib,live}.rs`; DOM-1/DOM-2 fixed (real `LiveDns`, owner-checked `DomainCap`) | — |
| Per-custom-domain cert (on-demand TLS) | **PARTIAL** | `cert_ok()` logic exists, **`ask` endpoint not served**, no cert provisioner wired (`gateway/src/hosting.rs:114`, DEVWORK) | IMPORTANT · M (reviewed-go) |
| Wildcard `*.dregg.works` TLS | **PARTIAL** | specced (Caddy DNS-01, `docs/WEB-HOSTING.md`), owned by deploy lane | IMPORTANT · M |
| DNS zones / records as a product | **LACK** | nameservice cell in breadstuffs (SERVICES.md #8 near) | NICE · M |

### Reliability / DR
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| BFT federation (n-of-m), fail-closed store | **HAVE** | `runbooks/{FEDERATION,INCIDENT-RESPONSE}.md`; store-integrity fail-closed | — |
| Disaster-recovery runbook + re-sync | **HAVE** | `runbooks/DISASTER-RECOVERY.md` | — |
| **Durable data plane** (survives restart/host-loss) | **PARTIAL→LACK** | metering/settlement durable (`settle_ledger.rs`, on-disk SQLite); but **sites, buckets, machine/mesh registries, daemon workload tracking are in-memory** (`storage/registry.rs:42`, gateway/control HashMaps) | BLOCKER · L (the Postgres-store rung) |
| Multi-region / AZ | **LACK** | single-region; per-tenant store is single-host SQLite (`webapp/src/router.rs:151`) | IMPORTANT · L |
| SLA / uptime commitment | **LACK** | no SLA doc | NICE · S |
| Incident response / runbooks (operator) | **HAVE** | `runbooks/INCIDENT-RESPONSE.md` + 18 runbooks | — |

### Operations
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| Public status page | **LACK** | (see Observability) | IMPORTANT · M |
| Quotas / limits (server-count) | **PARTIAL** | per-lessee/global live-server quota (`control/src/server.rs:557`, SRV-1); **no quotas on publishes/buckets/bandwidth-spray/accounts** | BLOCKER · M (see E-4) |
| Rate-limiting (edge, per-identity) | **LACK** | see E-4 | BLOCKER · S–M |
| **Abuse prevention / content moderation / takedown** | **LACK** | see E-2 | BLOCKER · M–L |
| Account suspension / kill-switch | **LACK** | see E-3 | BLOCKER · M |
| Operator control actions (restart/pause/fund/cancel) | **LACK** | ops dashboard read-only; "any action means SSH" (DEVWORK) | IMPORTANT · M |
| Admin authz (RBAC tiers) + audit trail | **PARTIAL** | binary `OPS_REQUIRE_CAP`, no RBAC tiers, no admin audit trail (DEVWORK) | IMPORTANT · M |

### Developer experience
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| CLI (`dregg-cloud` — login/deploy/domains/ls/logs/destroy/lease/run/agent/model) | **HAVE** | `cli/src/main.rs:110-235` | — |
| SDK (Python/TS/Rust) | **HAVE (referenced)** | `pip install dregg`, `@dregg/sdk`, `dregg-sdk` | — |
| Onboarding / quickstarts | **HAVE** | `docs/{GETTING-STARTED,DEVELOPERS,USING-DREGGNET}.md` + Discord `/start` | — |
| Auto-deploy from git (clone→build→publish, durable) | **HAVE (core, hardened)** | `dregg-deploy/`; publish lands in-process, live edge is the gateway-mount rung | IMPORTANT · M |
| Customer console ("my stuff", cap-scoped) | **PARTIAL** | `console/` models real; uses **fixtures**, live source deferred | IMPORTANT · M |
| API docs (OpenAPI/spec) | **PARTIAL** | inline route docs; no formal spec | NICE · M |
| Build logs / `--dry-run` / rollback / env-secrets | **LACK** | DEVWORK Top-10 #2/#3; no secret injection | IMPORTANT · M |
| Templates / marketplace (Sandstorm) | **PARTIAL (framework)** | `sandstorm-bridge/` framework; no app catalog | NICE · L |

### Business / legal
| Capability | Status | Grounding | Crit · Effort |
|---|---|---|---|
| ToS / AUP / Privacy / DMCA / abuse contact | **LACK** | none in repo (see E-1) | BLOCKER · S–M |
| Named legal entity / support channel | **LACK** | not in repo | BLOCKER · S |
| Data-subject erasure (GDPR/CCPA) path | **LACK** | no storage delete/TTL (S-7) | BLOCKER · M |

---

## 2. The ranked master list

### Launch-blockers (cannot responsibly open KYC-free doors without these)
1. **Legal/policy pack — ToS + AUP + Privacy + DMCA agent + abuse contact + named
   entity** (E-1). Gates everything else; without it, upstreams/Stripe pull the
   plug and the operator is personally liable. *S–M, but first.*
2. **Abuse-report intake + operator takedown (de-publish / de-route)** (E-2). *M.*
3. **Operator account-suspension / kill-switch** across a subject's resources
   (E-3), built on the substrate cap-revoke. *M.*
4. **Durable data plane** — flip sites / buckets / machine + mesh registries /
   daemon workload tracking off in-memory `HashMap` onto the Postgres store rung
   (R-1). Today a control-plane restart loses published sites and live machines.
   *L.* (Metering/settlement are already durable — this is the data, not the money.)
5. **Per-identity rate-limiting + publish/verify caps + a real anti-Sybil price
   floor** (E-4) — close the free-spray surface before doors open. *S–M + a
   pricing decision.*
6. **Per-tenant runtime logs (tail/search)** (LOG gap). A cloud you cannot debug
   on is not a cloud a customer will trust their workload to; today they get
   cached step-outputs, not logs. *M.*
7. **Egress abuse control on the run path** (E-5) — outbound policy + basic
   anomaly signal, so a tenant can't turn DreggNet IPs into an attack/mining
   source and get the fleet null-routed. *M.*

### Important (a real cloud is expected to have these; painful to launch without)
8. **Public status page** + live per-tenant resource status (wire the console off
   fixtures). *M each.*
9. **Invoices + refund/dispute→burn wiring + rate-card API.** *M / M / S.*
10. **Gateway mounts** that unlock built cores: storage `PUT/GET/DELETE`, the
    leased router, gateway→persistent-server ingress, the on-demand-TLS `ask`
    endpoint. Each is "tested core, not reachable from the edge." *M each.*
11. **Secrets/KMS + build-time env injection.** *M.*
12. **Teams/orgs + RBAC tiers + API-key mint/rotate/revoke UX** — the cap model is
    powerful but presents as single-wallet; real customers need shared accounts.
    *L / M / M.*
13. **Operator control actions** in the ops plane (suspend/restart/fund/cancel
    without SSH) + admin RBAC + audit trail. *M.*
14. **CDN/cache + `Cache-Control`/`ETag`; load-balancing beyond round-robin;
    backups/snapshots; multi-region.** *M–L.*
15. **Build logs / `--dry-run` / rollback / deploy history.** *M.*

### Nice-to-have (maturity)
16. Managed DB / Redis / queues / pub-sub / search as tenant products.
17. Containers/OCI, autoscaling, GPU live boot.
18. Object lifecycle/versioning/signed-URLs/multipart; storage CLI.
19. Distributed traces for customers; OpenAPI; app marketplace/catalog.
20. SLA document; cost-estimation CLI; DNS-zones-as-a-product.

---

## 3. Minimum to responsibly open the doors

The smallest set that turns "a verifiable cloud demo" into "a KYC-free cloud that
survives the public internet and an upstream's abuse desk." Everything here is a
**launch-blocker**; the ordering is dependency- and risk-first.

1. **Ship the legal/policy pack** (E-1): a named operating entity, ToS, an
   **Acceptable Use Policy** with prohibited-content/conduct, a **DMCA designated
   agent + notice-and-takedown**, a Privacy Policy, a published **abuse@ contact +
   `security.txt`**, and a CSAM-reporting posture. *Nothing else opens safely
   first.*
2. **Build the enforcement arm the policy points to** (E-2 + E-3): an abuse-report
   intake, an **operator de-publish/de-route takedown**, and a **subject-level
   suspension kill-switch** (reuse the substrate cap-revoke). A policy with no
   button is theater.
3. **Close the free-spray + Sybil surface** (E-4): per-identity publish/verify
   rate-limits, a gateway edge limiter, and **a real price floor or PoW/stake on
   account creation** — so abuse costs the abuser something. Decide the
   subsidy-era economics deliberately before opening.
4. **Add egress control + outbound-anomaly signal** (E-5) so tenants can't weaponize
   the fleet's IPs.
5. **Make the data plane durable** (R-1): published sites, buckets, and the
   machine/mesh/daemon registries must survive a restart before real tenants
   depend on them. (The money rail already is.)
6. **Give tenants logs + a status page** (LOG + status): runtime log tail/search
   for a workload, and a public uptime page — the two things a developer checks
   first when something breaks.

Items 1–3 are the genuinely **existential** ones: they are what stand between
DreggNet and being shut down by Hetzner/Stripe/a registrar or named in a lawsuit
on day one. The technical isolation is already strong; the operator-readiness is
the work.

> **Reviewed-go reminder.** Per the repo's standing guardrails, the *code* for all
> of the above is safe-autonomous to build and prove locally; **flipping any of it
> onto the live public edge — real takedown authority, real account suspension,
> real billing, real rate-limits on the production gateway — is reviewed-go and an
> ember decision.** This doc is the map, not a go-live.
