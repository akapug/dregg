# The Liftoff surpass matrix — surpass them on every axis

The scorecard for the headline featureset pillar (`docs/OVERNIGHT-GOAL.md` §2,
`docs/PERMISSIONLESS-CLOUD-PLAN.md`): a flat, honest, axis-by-axis comparison of
DreggNet against Liftoff (`@liftoffday` / `liftoff.day`) and the adjacent
permissionless-cloud landscape (Akash, Fleek, Spheron, Arweave/AR.IO) and the
web2 bar (Cloudflare, fly.io, Vercel). The point of this document is **not** to
list wins — it is to **find every axis where we are not yet ahead and name the
concrete plan to close it**, so the autonomous run has a target.

The one-line thesis (unchanged): **Liftoff is a KYC-free host you trust; DreggNet
is a permissionless host you verify.** Same push-to-deploy / pay-in-token /
no-gatekeepers DX, but the served bytes, the compute, and the bill are each
re-witnessable against a committed cell, so the host *cannot* lie. That is a
different category, not a better Liftoff — and the structural axes in §2 are ones
a centralized trusted host **cannot** match no matter how much it polishes.

Status grading (against HEAD of this repo, 2026-06-29):

- **LIVE** — code-proven here, with tests; runs on the local / in-process path the
  existing crates prove themselves on.
- **v1 / PARTIAL** — core wired, one named seam open (a deploy-lane edit, an AGPL
  flip, a stand-in to replace).
- **GAP** — not built yet; the plan is named.

> Honesty caveat that colours the whole matrix: almost everything LIVE here is
> proven on the **local / in-process / LocalProvider path**, not on a live public
> edge. The live `dregg.works` edge, real cert issuance, the on-chain `Effect::Write`
> that replaces the FNV `content_root` stand-in, and real $DREGG billing are all
> **reviewed-go** (`docs/OVERNIGHT-GOAL.md` guardrails) and several are not yet
> operating (`docs/GO-REAL.md`: the recovered edge node's receipt log is empty and
> its submit endpoint is operator-locked). Where an axis is "LIVE" but its public
> operation is gated, the row says so. This is the difference between *built +
> proven* and *operated on the public edge*; we surpass on the former, and the
> latter is the reviewed-go go-live queue, not new code.

---

## 1. The axis-by-axis matrix — Liftoff feature × DreggNet status × how we surpass

| Axis | Liftoff's offering | DreggNet status | How we surpass (or the gap + plan) |
|---|---|---|---|
| **Static websites** | Host a site, no gatekeepers | **LIVE** (`webapp/src/hosting.rs` `SiteCell`, cap-gated publish + `PublishReceipt`; served by `gateway/src/hosting.rs`; round-trip tested over real TCP, `webapp/tests/site_publish_serve.rs`) | A site **IS a cell** carrying a `content_root` commitment → trustless serving (§2): the visitor re-witnesses the served bytes. *Seam:* `content_root` is an FNV-1a stand-in (`hosting.rs:180`) until the `dregg-verify` on-chain `Effect::Write` flip lands the real Poseidon2 heap root. |
| **SSL / TLS** | Automatic SSL certs | **v1** (wildcard `*.dregg.works` via Caddy DNS-01 is specced, `docs/WEB-HOSTING.md` §3; the on-demand-TLS `ask` hook is designed) | Match on wildcard; surpass via the **verified `ask` endpoint** (Caddy only mints a cert for a cell a tenant has cap-proven they own). *Gap:* per-custom-domain cert automation is unbuilt; live cert issuance is reviewed-go (deploy lane). |
| **Custom domains (BYO)** | Bind your own domain | **v1 → GAP** (`dregg-domains/` crate exists: `DomainBinding` cell + TXT/CNAME challenge state machine; **`MockDns` stand-in**, no live resolver — `dregg-domains/src/lib.rs:237`) | A `DomainBinding` is a **cap-gated receipted cell** → "who proved control of this domain, when" is provable. *Gap to close:* a real `DnsResolver` (hickory/trust-dns) replacing `MockDns` (effort S) + the live cert mint (reviewed-go). |
| **Auto-deploy (git push → build → host)** | "You ship, we host" — the keystone DX | **GAP** (no clone/build/publish pipeline today; publish is a *pre-built* directory via `dreggnet-host`) | **The build IS a durable workflow** (`dregg-deploy` core over `durable/`): crash-resumable, exactly-once-metered, and the **cloned commit hash is recorded in the receipt** → "built from *that* commit" is provable (reproducibility Liftoff can't offer). *Gap to close:* build `dregg-deploy` (BuildPlan + framework detect + Clone/Build/Publish), static+node paths local e2e (safe-autonomous); the public push-webhook is reviewed-go. |
| **Persistent servers** | Long-running instances | **PARTIAL** (fly-compatible machines API CRUD + lease-gated admission LIVE: `gateway/src/route.rs`, `types.rs`; but records are in-memory + request-scoped — no durable long-running process; create→fulfill seam deferred) | A server = a **long-lived durable workflow** metered per-period uptime (`StandingObligation`), reaped on lease lapse → **you pay only while it's awake** (Sandstorm-style sleep). *Gap to close:* the persistent-server workload shape + create→fulfill durable launch seam + a persistent machine store (SQLite/duroxide-pg); live fleet boot reviewed-go. |
| **The deploy CLI / ship→host DX** | One-command deploy | **PARTIAL** (`dregg-cloud lease/run/status` is operator-facing, `wat`-only; SDKs published — `@dregg/sdk` npm, `dregg` pip; gateway speaks the fly machines API) | `dregg-cloud login` binds an **attenuable cap account** (a CI runner gets a deploy-only sub-cap, not the root key). *Gap to close:* the `dregg-cloud deploy / domains / ls / logs / destroy` developer verbs over the same control plane (safe-autonomous, e2e-tested). |
| **Pay-in-token / billing** | Pay hosting in `$LIFTOFF` | **PARTIAL → LIVE rail** (the lease economy is real: meter per step, budget-gate, exactly-once settlement as a real conserving `Transfer` — `control/src/{orchestrator,settle_ledger,node_api}.rs`, `durable/`; *hosting itself* is not yet metered — compute is subsidized in the early era) | **Verifiable billing** (§2): every charge is a re-witnessable conserving `Transfer`, not a dashboard number — the host **cannot overcharge**. *Gap to close:* the hosting-meter model (per-publish/MB/GB/uptime/cert/build-minute `Pricing` + the bandwidth byte-counter), wired to the lease/Payable rail; flipping real money on is an ember decision (reviewed-go). |
| **No-KYC / chain-as-account** | Wallet = account, no ID | **LIVE (surpasses)** (`webauth/` cap-auth: a wallet-held `dga1_` credential, ed25519 caveat-chain, attenuable, offline-verifiable) | Not just "no KYC" — **fine-grained attenuable, revocable, offline-verifiable delegation**. The wallet is the account *and* you can hand a teammate/CI a strictly-attenuated sub-capability. |
| **Object storage** | (none disclosed) | **LIVE** (`storage/`, cap-gated `create/put/get/list/delete`, trustless `verified_get` + pure `verify_opening`) | Trustless reads: a flipped byte or forged root is caught client-side. *Seam:* the leaf hash is an FNV-1a stand-in for Poseidon2 until the same on-chain flip as hosting (`storage/src/object.rs:47`). |
| **Databases** | (none disclosed) | **v1 / near** (KV = the kvstore register-file cell pattern, a thin managed wrap over the pg-dregg verified store — `docs/SERVICES.md` row 2) | A verified KV/DB: committed register state + replayable receipts over the proof-attested pg-dregg store. *Gap:* the managed surface + metering is the new bit; a relational/SQL product is roadmap. |
| **Functions / FaaS** | (none disclosed) | **LIVE (compute) / v1 (front door)** (the wasm tier `dreggnet-exec` → the owned wasmi sandbox runs handlers at the lease's `Sandboxed` cap-tier; exposed as the agent-web-app router `webapp/`) | Handlers run at exactly the cap-grade the lease authorizes; output rides a receipt. *Gap:* the standalone "deploy a function" packaging front door. |
| **Compute / servers (real)** | Trusted servers | **LIVE (owned wasmi tier) / SEAM (stronger tiers) / PARTIAL (fleet)** (durable metered compute: the `Sandboxed` tier genuinely runs on the owned, vendored pure-Rust `wasmi` interpreter on every platform; every stronger tier — `JitSandboxed`/JIT, `Caged`/native+python+node, `MicroVm`/Firecracker, `Gpu` — is an honest **fail-closed seam** today (`ExecError::NotWired`/`TierNotServed`), never a fake run — `docs/COMPUTE-TIERS.md`) | **Durable, receipted, cap-tiered, privacy-capable** compute; crash-resume exactly-once. *Gap:* wiring an owned engine for each stronger tier (`exec/src/lib.rs`) + a real multi-node fleet (today a 2→5 node devnet); both reviewed-go (owned-engine work / fleet). |
| **App catalog** | One site per launch | **v1 (Sandstorm integration)** (`sandstorm-bridge/` prototype: `.spk` manifest parser, grain=cell lifecycle, powerbox=cap ceremony, 13 tests) | **Hundreds of cap-secured self-hostable apps** (Etherpad/Wekan/Gitea/…), each a verifiable metered grain; the powerbox becomes *provable* (§2). *Gap to close:* the `.spk` reader (Ed25519+XZ+capnp unpack), the descriptor↔Pred bridge, the http-bridge shim; executing real catalog code is reviewed-go. |
| **Scheduled / cron** | (none disclosed) | **v1 / near** (the durable runtime exists; the timer-trigger cell + period-fire loop is the new bit — `docs/SERVICES.md` row 5) | Each run is a durable, crash-resumable, exactly-once-metered workflow. |
| **Pub/sub · queues · secrets · naming · identity** | (none disclosed) | **roadmap / near** (reactor+SSE, conditional-batch cq, cipherclerk, nameservice, credential-ZK — `docs/SERVICES.md` rows 3,4,7,8,9) | Each is the *same cell-shaped template*, paid + verified; naming is already consumed by hosting's `<name>.dregg.works`. |
| **Light-client verifiable receipts** | (none — structurally impossible) | **LIVE** (`portal.dregg.studio` read-only v1: in-tab wasm/recursive-STARK light client re-verifies a cell's committed history) | See §2 — this is the category gap. |
| **Token launch / launchpad** | Couples a Solana token launch to a hosted site | **substrate-LIVE, no product** ($DREGG / per-asset-well supply model, provable `Effect::Mint`/`Burn` exist in breadstuffs; no "launch a coin + a site together" product) | *Gap (optional):* a launchpad product is not built and may not be wanted — but the substrate (an issuer-cell asset-well + cap-gated mint) is *stronger* than an SPL mint. See §3. |

**Supporting LIVE capabilities Liftoff has no equivalent of:** durable execution
(`durable/`, crash-resume exactly-once), agent-served web APIs (`webapp/router.rs`,
`LeasedRouter` → `402`), agent coordination (branch/stitch settlement-sound merge),
the 13-service catalog on one cell-shaped template (`docs/SERVICES.md`).

### 1b. The adjacent landscape — match-or-beat

| Project | What it is | What it offers we should match-or-beat | DreggNet posture |
|---|---|---|---|
| **Liftoff** | KYC-free host + Solana launchpad, pay-in-token | sites/SSL/domains/auto-deploy/servers, wallet-as-account, token-coupled launch | match the DX (§3 closure list); surpass on verifiability (§2) |
| **Fleek** | Git → IPFS/Filecoin + an edge network; great DX | **push-to-deploy DX**, edge functions, gateway delivery | match the DX (auto-deploy-from-git is the keystone gap); surpass on *operated* verifiability (IPFS verifies storage, not the served operation) |
| **Akash / Spheron** | Decentralized compute marketplaces; **GPU mainnet** (~334 GPU units Q1'26), Console no-CLI deploy, templates | **cheap real VMs/containers + GPU**, a polished deploy Console, ~85% cost claims | match on cap-tiered compute; **behind on GPU + fleet scale + a no-CLI Console** (§3); surpass on durable/receipted/metered-verifiably |
| **Arweave / AR.IO** | Permanent storage + verifiable gateways; **pay-once-store-~200yr** endowment; **ArNS** naming | **permanent storage with a one-time fee**, censorship-resistant naming, content-addressed verifiable reads | content-addressed verifiable reads — *match*; **behind on a permanent-storage endowment model** (we meter storage per-period; §3); surpass on *compute* (Arweave has none) |
| **Cloudflare / fly.io / Vercel** | The web2 bar | **polished DX, preview deploys, global edge/CDN/PoPs, mature scale, dashboards, instant rollbacks** | **behind across the board on polish + scale + edge** (§3); surpass only on the verifiability category, not on maturity |

---

## 2. The dregg-unique axes — what Liftoff (and every trusted host) structurally cannot match

These are not features to catch up on; they are the category gap. A centralized
trusted host cannot offer them *by construction*, because they require the served
state, the delegation, and the bill to be committed and re-witnessable.

- **Verifiable tamper-proof hosting (the headline).** A site IS a cell carrying a
  `content_root` commitment (`webapp/src/hosting.rs`); the served bytes re-witness
  against it via the `deos-view::render_trustless_cell_document` trustless
  projection the portal already uses. The visitor's browser re-verifies, trusting
  no server, that what it was served is the genuine published cell. **The host
  cannot tamper with a byte without the visitor catching it.** *Liftoff you trust;
  dregg you verify.* (Seam: the real Poseidon2 commit lands with the on-chain flip.)
- **Verifiable billing.** Every charge is a receipted, exactly-once, conserving
  `Transfer` (`control/src/settle_ledger.rs`) — the bill is re-witnessable, not a
  number on a dashboard. **The host cannot overcharge.**
- **Private compute.** The M2 shielded-transfer rail (breadstuffs) means a tenant's
  values + payments can be confidential while still verified — ZK hosting Liftoff
  has no analog of. (Seam: M2 effects are complete crypto awaiting executor call
  sites — `docs/STAND-INS-CENSUS.md` #17.)
- **Durable / receipted execution.** Every workload is crash-resumable and
  exactly-once-metered (`durable/`); a deploy, a request, a server period each
  leaves a receipt — a durable, witnessed transition, not a fire-and-forget run.
- **Agent-native.** Host an *agent*, not just a site: agent-served web APIs,
  BYO-key Hermes loops, agent coordination over the intent ring / branch-stitch.
  The cloud built for autonomous software — a grain is a cell, so an agent can spin
  one up, hold its cap, attenuate a sub-cap to a teammate, and coordinate.
- **Attenuable cap-accounts.** "No KYC" is the floor; the differentiator is the
  `webauth` `dga1_` cap credential — attenuable, offline-verifiable, revocable. A
  tenant delegates a *deploy-only*, *one-site*, *time-boxed* sub-capability without
  sharing the root key.
- **Provable capability delegation (the powerbox-on-dregg).** The first
  delegation UI where a third party can witness, trusting no one, that an app holds
  exactly the authority it was granted and no more — confused-deputy immunity *with
  a proof* (`docs/SANDSTORM-INTEGRATION-PLAN.md` §4).
- **The whole thing on a light-client-unfoolable rail.** `verifyBatch accept ⟹ ∃
  genuine kernel transition` — the served reality is anchored to a finalized
  committee checkpoint (`docs/GO-REAL.md`, `CommitBindsMMR`), not to the operator's
  word.

---

## 3. HONEST — where Liftoff or the landscape is AHEAD, and the plan to close it

This is the point of the document. Naming a win is cheap; naming where we are
behind and the concrete leapfrog is the work.

### 3.1 Polished, frictionless DX — Liftoff / Fleek / Vercel are AHEAD

**The gap:** Liftoff sells "you ship, we host" as a single frictionless step;
Fleek and Vercel have years-polished `git push → live` with preview deploys,
build logs, instant rollbacks, and a dashboard. DreggNet today has an
**operator-facing** CLI (`lease/run/status`, `wat`-only) and a pre-built-directory
publish — there is **no `dregg-cloud deploy`, no git clone/build pipeline** (the keystone
DX gap, GAP in §1).

**The plan to close + leapfrog:** build `dregg-deploy` (the BuildPlan + framework
detection + the Clone/Build/Publish **durable** orchestration) and the `dregg
deploy / login / domains / ls / logs / destroy` developer verbs (safe-autonomous,
local e2e). The leapfrog over Fleek/Vercel: our build is a **crash-resumable,
exactly-once-metered, receipted durable workflow** whose **source commit is bound
into the publish receipt** — reproducible-by-construction, not a best-effort log.
Match the polish, beat it on provenance. (`docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.1,
§3.4.)

### 3.2 Mature scale, global edge, CDN — Cloudflare / fly / Vercel are AHEAD

**The gap:** a global anycast edge, hundreds of PoPs, instant cache invalidation,
mature autoscaling, five-nines operation. DreggNet runs a **2-node devnet heading
to 5** (`docs/DEVELOPERS.md` §6), serving is single-edge (the recovered
`34.224.208.52` box), and the live public edge is **not yet operating** — the
node's receipt log is empty and submit is operator-locked (`docs/GO-REAL.md`).

**The plan to close:** this is an *operational* gap, not a code gap, and most of it
is reviewed-go (live fleet boot, real edge). The near-term honest move is **scale
to the 5-node federation for real fault tolerance + sustained finality**
(`docs/OVERNIGHT-GOAL.md` §3) and the **WireGuard mesh two-node handshake**
(`control/src/mesh.rs`, `StubMesh` → `WireguardMesh`, `docs/STAND-INS-CENSUS.md`
#10). We will **not** out-scale Cloudflare soon; the honest positioning is that we
trade raw edge maturity for a verifiability property they can't offer (§2), and
close the operational gap incrementally on real hardware (reviewed-go).

### 3.3 GPU + heavy compute marketplace — Akash is AHEAD

**The gap:** Akash has a live GPU mainnet (~334 GPU units Q1'26), Starcluster, and
a deep provider marketplace; Spheron similar. DreggNet's compute genuinely runs
only the `Sandboxed` wasm tier (the owned wasmi interpreter); every stronger tier
(`Caged`/native, `MicroVm`/Firecracker, `Gpu`) is a **fail-closed seam** today
(`docs/STAND-INS-CENSUS.md` #2), and there is no GPU tier.

**The plan to close:** wire an **owned microVM engine** for `MicroVm` (guest
wire + kernel/rootfs image + jailer — reviewed-go, KVM hardware) to make it a real
VM tier, and an owned native/python/node engine for `Caged`; add a **GPU cap-tier**
to the `CapTier` map (`exec/src/lib.rs`, `docs/COMPUTE-TIERS.md`) as a later rung.
The leapfrog: even a smaller fleet is
**durable + receipted + cap-tiered + privacy-capable** — an Akash workload is a
trusted VM; a DreggNet workload is a witnessed, exactly-once-metered transition.
Match the tiers over time; surpass on verifiability + agent-nativeness now.

### 3.4 Permanent storage endowment — Arweave / AR.IO is AHEAD

**The gap:** Arweave's pay-once-store-~200-years endowment + ArNS naming is a model
we don't have — DreggNet meters storage **per-period** (`StandingObligation`), so a
lapsed lease eventually reaps the cell. For "publish once, persist forever" content
this is strictly behind.

**The plan to close:** offer a **prepaid-endowment storage option** — a one-time
funded `Account` whose periodic storage charge is drawn from the principal at a
rate that targets a long horizon (the meter already exists; the endowment is a
funding *policy* over it, not a new engine). The leapfrog: unlike Arweave's
opaque-miner model, the endowment draw-down is a **re-witnessable conserving
charge** and the content is a **verifiable cell**, not just content-addressed
storage. Match permanence; surpass on verifiable billing + the cell model.

### 3.5 The verifiable-hosting headline is not yet wired to the real node

**The gap (the most important honesty):** the §2 headline ("you verify the served
bytes") is **proven in design and locally**, but the `content_root` is an **FNV-1a
stand-in** (`webapp/src/hosting.rs:180`, `storage/src/object.rs:47`), not the real
Poseidon2 committed umem heap root. The trustless re-witness checks the *identical
bytes-bind-to-root property*, but against a stand-in commitment until the on-chain
`Effect::Write` flip lands (`docs/STAND-INS-CENSUS.md` #4/#5, the `dregg-verify`
AGPL flip + a live node).

**The plan to close:** the on-chain write (publish turn → `Effect::Write` to the
content cell → committed Poseidon2 heap root, witnessed as a receipt) is the
deliberate flip-on step on `bridge/src/dregg_verify.rs`'s surface (reviewed-go:
AGPL link-isolation + a live node). Until then, the property is real, the
commitment carrier is a stand-in — and the doc says so rather than overclaiming.

### 3.6 Token launch / launchpad — Liftoff couples it; we don't (optional)

**The gap:** Liftoff's distinguishing twist is shipping a Solana **token + a hosted
site together**. DreggNet has the supply substrate ($DREGG, per-asset-well
`Effect::Mint`/`Burn`, issuer-cell identity) but **no launchpad product**.

**The plan (only if wanted):** a "launch a verifiable asset-well + its site" flow
is a thin SDK/app-layer composition over the existing mint + hosting primitives —
*not* a kernel change. The asset-well is structurally stronger than an SPL mint
(cap-gated, conserving, supply-modelled). Flagged as a **deliberate non-priority**:
it is a market-positioning feature, not a verifiability one; build only on request.

### 3.7 Honest scorecard summary

| Axis | Who's ahead today | After the §3 closure plan |
|---|---|---|
| Verifiable hosting / billing / delegation | **DreggNet** (structural) | DreggNet (real commit wired) |
| No-KYC / attenuable accounts | **DreggNet** | DreggNet |
| Durable / receipted / private / agent-native compute | **DreggNet** | DreggNet |
| App catalog (cap-secured, verifiable) | **DreggNet** (Sandstorm path) | DreggNet |
| Auto-deploy-from-git DX | **Liftoff / Fleek / Vercel** | DreggNet (durable + provenance) |
| Polished DX / dashboards / preview deploys | **Vercel / Fleek** | parity + provenance edge |
| Custom domains + live certs | **Liftoff / everyone** | DreggNet (verified `ask`) |
| Persistent servers (operated) | **Liftoff / fly** | parity (pay-only-while-awake edge) |
| Global edge / CDN / mature scale | **Cloudflare / fly / Vercel** | still behind (operational, reviewed-go) |
| GPU + heavy compute marketplace | **Akash / Spheron** | partial (MicroVm + GPU tier later) |
| Permanent storage endowment | **Arweave / AR.IO** | parity (prepaid endowment policy) |
| Token launch / launchpad | **Liftoff** | optional (substrate stronger; product unbuilt) |

We are ahead, by construction, on every **verifiability** axis. We are behind on
**operated maturity** (edge scale, polished DX, GPU fleet, live operation) and on
two product axes (permanent-storage model, launchpad). The closure plan makes us
*parity-or-ahead* on every feature axis except raw edge scale, where the honest
position is "we trade scale for verifiability and close the operational gap on real
hardware incrementally."

---

## 4. Positioning + the prioritized surpass-gap closure list

**Positioning:** *Liftoff is a KYC-free host you trust; DreggNet is a permissionless
host you verify* — same push-to-deploy, pay-in-token, no-gatekeepers DX, but the
served bytes, the compute, and the bill are each re-witnessable against a committed
cell, and you get an attenuable cap-account, durable receipted compute, private
compute, and a catalog of hundreds of cap-secured verifiable apps. Not a better
Liftoff — a different category.

**The prioritized closure list** (highest surpass-value first; safe-autonomous
unless marked). The dependency order: the billing meter is the floor, the deploy
core is the shared driver, then the product features fan out, then the
differentiators are wired outward.

1. **`dregg-deploy` core + the build durable workflow** (closes §3.1, the keystone
   DX gap). BuildPlan + framework detection + Clone/Build/Publish durable
   orchestration; static + node paths, local e2e. *The one feature that makes
   DreggNet feel like Liftoff's "you ship, we host" — with reproducible provenance.*
2. **The hosting-billing meter model** (closes the §1 billing PARTIAL). Per-resource
   `Pricing` + the bandwidth byte-counter + charge-before-commit, on the lease/Payable
   rail. The floor every other feature bills against.
3. **The `dregg-cloud deploy / login / domains / ls / logs / destroy` CLI verbs** (closes
   §3.1 DX). The developer onramp over the same control plane, e2e-tested.
4. **Custom domains — replace `MockDns` with a real `DnsResolver`** (closes §3, the
   custom-domain GAP). The `DomainBinding` cell is built; a hickory/trust-dns
   resolver + the verified `ask` endpoint logic (live cert mint is reviewed-go).
5. **Persistent servers — the create→fulfill durable launch seam** (closes §1 PARTIAL).
   The long-running server workload shape + per-period uptime metering + a persistent
   machine store (live fleet boot reviewed-go).
6. **Sandstorm catalog ingest** (extends the app-catalog lead). The `.spk` reader
   (Ed25519+XZ+capnp) + the descriptor↔Pred bridge + the http-bridge shim (executing
   real catalog code is reviewed-go).
7. **Wire the differentiators outward** (makes §2 tangible). The trustless-serving
   wrap on hosted sites (the `content_root` → `deos-view` re-witness), and the
   verifiable-billing receipt surfaced per charge.
8. **The prepaid-endowment storage policy** (closes §3.4). A funding policy over the
   existing meter — pay-once, long-horizon, verifiable draw-down.
9. **(Reviewed-go / operational, not new code)** the on-chain `Effect::Write` flip
   for the real Poseidon2 `content_root` (§3.5), the 5-node federation + WireGuard
   mesh (§3.2), the Firecracker guest plane + a GPU cap-tier (§3.3), and the live
   public edge / real cert issuance / real $DREGG billing — all gated by the
   `docs/OVERNIGHT-GOAL.md` reviewed-go guardrails.

The dividing line is the project standard: items 1–8 are *code + verified local
proof* (safe-autonomous tonight); item 9 is *operated reality on the public edge*
(reviewed-go, ember's go). Build 1–8 to green and the matrix in §3.7 moves DreggNet
to parity-or-ahead on every feature axis, with the verifiability axes (§2) ahead by
construction the whole time.

---

*Dated 2026-06-29. Status graded against HEAD; verify any specific file:line or
LIVE/PARTIAL/GAP claim against the tree before relying on it. Liftoff's offering is
characterized from `liftoff.day`'s public pitch ("launch a token with a real
website on Solana" — KYC-free hosting: sites/servers/SSL/auto-deploy/custom-domains,
pay-in-`$LIFTOFF`, wallet-as-account) and the project's prior research; their X
(`@liftoffday`) and deeper marketing were not machine-readable at write time, so
treat their roadmap as approximate and re-verify before any outward claim.*
