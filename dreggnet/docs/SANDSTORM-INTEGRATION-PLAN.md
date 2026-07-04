# Sandstorm.io × DreggNet — the native integration plan

The make-it-sing featureset for DreggNet Cloud (`docs/OVERNIGHT-GOAL.md` §2,
`docs/PERMISSIONLESS-CLOUD-PLAN.md`). This document is the research + the
dregg-native design + the buildable plan.

The one-line thesis: **a Sandstorm grain and a dregg cell are the same object,
and Sandstorm's powerbox and dregg's capabilities are the same security
discipline — so the integration is not a port, it is a *welding of two halves of
one idea*.** Sandstorm built the object-capability runtime (grains, the
powerbox, per-object sandboxing) and the app ecosystem; dregg adds the half
Sandstorm never had: **the delegation and the served bytes are *witnessed*** —
a light client can verify what an app holds, what it served, and what it
charged, trusting neither the host nor the app. The result is a different
category: *hundreds of cap-secured, self-hostable apps you verify instead of
trust, metered in $DREGG.*

> Companion artifacts: the executable design prototype lives at
> `../sandstorm-bridge/` (a detached crate — `cargo test` green, 13 tests:
> the `.spk` manifest parser, the grain=cell lifecycle, the powerbox=cap grant
> ceremony). The deep Sandstorm research backing this plan is captured inline in
> §1; sources are footnoted there.

---

## 1. What Sandstorm is (research digest)

Sandstorm's defining move: **containerize objects, not services.** Docker/k8s
wrap a *service* (one Etherpad daemon serving every document); Sandstorm wraps
each *logical object* — one document, one board, one repo, one mailbox — in its
own isolated container, the **grain**, bundling that instance's frontend *and*
its database. Everything else follows from that decision.

### 1.1 Grains
A grain = a sandboxed instance of an app + that instance's private data. Private
to its creator by default; shared only by an explicit capability grant. Lifecycle
(orchestrated by the C++ `backend.capnp` on behalf of the Meteor shell; one
dedicated **supervisor** process per grain):

- **create / open** — `startGrain(...)` spins the grain's process tree up *on
  demand* when a user navigates to it, returns a `Supervisor` capability.
- **wake / keep-alive** — the front-end calls `Supervisor.keepAlive` ≥ once/min.
- **sleep** — the supervisor arms a 90 s `ITIMER_REAL`; with no keepalive and no
  background wake-lock it logs "Grain no longer in use; shutting down" and exits.
  An idle grain self-terminates within ~90 s, freeing all resources.
- **backup / restore** — `backupGrain` emits a ZIP; `restoreGrain` unpacks it.
- **delete / transfer** — `deleteGrain`, `transferGrain` (reassign ownership).

**Isolation** (the kernel features directly, not via LXC/Docker): the supervisor
`unshare()`s user/mount/IPC/UTS/PID **and network** namespaces, then *forbids the
app from creating further namespaces* (neutralizing the unprivileged-userns CVE
class). Root FS = a **read-only** bind-mount of the `.spk` app image (shared
across grains) + a **read-write** bind-mount of the grain's `/var` data. No
overlayfs, no `/proc`, no `/sys`; only `/dev/{null,zero,urandom}`.
`PR_SET_NO_NEW_PRIVS` + a **seccomp-bpf** syscall allowlist (blocks `ptrace`,
`keyctl`, `bpf`, `mount`, further seccomp, …). The supervisor `chroot`s away from
the app FS and SIGKILLs the app if it exits — no orphans.

### 1.2 The powerbox (capability delegation)
A new grain is *totally confined* — no network, no ambient FS, no DNS. The only
way it reaches anything outside itself is a Cap'n Proto capability the user
*explicitly handed it through the powerbox*. The powerbox makes
**designation = authorization**: choosing which object to share *is* the grant.

- **Request by *type*, not instance.** The grain `postMessage`s the shell with
  `powerboxRequest { query, saveLabel }`; `query` is a list of
  `PowerboxDescriptor`s (each = `tags: List(Tag{id: UInt64 type-id, value:
  AnyPointer})` + `MatchQuality`). The grain asks for "any object implementing
  this calendar API"; the user picks the concrete grain. This kills lock-in and
  fuses consent with selection.
- **Trusted picker.** System UI (outside the requesting grain) lists every
  capability the user holds that matches; the grain only ever receives the one
  the user designates — all others stay hidden.
- **Claim → live → durable.** The grant is a session-scoped **claim token** →
  `claimRequest()` → a **LiveRef** (in-RAM, connection-lifetime) → `save()` → a
  **SturdyRef** (durable, sealed to its owner so a leaked token is inert) →
  `restore()` (token → fresh LiveRef on a later connection) → `drop()` (revoke
  forever). Only the *token* crosses the persistence boundary.
- **Cross-grain + drivers.** The provider can be *any* grain implementing the
  interface, including a **driver grain** that exposes an external resource as a
  capability (the HTTP/API driver — the only sanctioned network path; the email
  driver; etc.). Permissions/roles are declared in `ViewInfo`
  (`permissions` + `roleDefinitions`); the platform computes the permission set
  per request and hands the app `X-Sandstorm-Permissions: edit,admin` — the app
  never sees raw identities.

### 1.3 Cap'n Proto
A capnp `interface` reference *is* a capability — passable, returnable,
embeddable, and **unforgeable** (IDs are connection-scoped; you can't mint one
you weren't given). Promise pipelining ("time-traveling RPC") returns a promise
immediately and lets you call methods on a not-yet-existent result, collapsing
chained calls to one round trip — lineage: E's **CapTP**. RPC level **L2 =
persistent capabilities** = `Persistent(SturdyRef, Owner)` in `persistent.capnp`,
with `SaveParams.sealFor: Owner`. Cap'n Proto is maintained by Kenton Varda at
Cloudflare and underpins `workerd`.

### 1.4 App packaging (`.spk`)
Binary: magic prefix + **XZ**-compressed payload = a capnp `Signature {
publicKey, signature }` (libsodium **Ed25519**) + an `Archive` (`List(File)` —
the whole chroot tree). **The app ID *is* the Ed25519 public key**, base32-encoded
(`0123456789acdefghjkmnpqrstuvwxyz`) — no CA; the key is the global identity, and
all packages signed with it are releases of one app. Tooling: `spk`
(`init`/`dev`/`pack`/`publish`; `dev` traces file access to build the minimal
file list) and the recommended **`vagrant-spk`** (runs Sandstorm in a VM while
you edit on the host). Manifest (`sandstorm-pkgdef.capnp` → `Manifest`):
`appTitle`, `appVersion` (UInt32, drives auto-update), `appMarketingVersion`,
`actions: List(Action)` (the "New X" buttons; each an `Action{ input, command,
nounPhrase }`), `continueCommand` (restart an existing grain), `metadata`
(icons/categories/author/license), `bridgeConfig` (for http-bridge apps:
`viewInfo`, `apiPath`, `powerboxApis`). The market is `apps.sandstorm.io`,
keyed by App ID; authorship proven by PGP-signing the app-ID statement.

### 1.5 The runtime
A self-containerizing bundle: a **Meteor** (Node) shell + **MongoDB** (shell
metadata: users, grains, tokens) + the **C++ backend** (the "container
scheduler") + per-grain supervisor/app processes. A grain is served in a
sandboxed `<iframe>` under a **random per-session hostname** (CSRF/XSS defense);
the app's only outside connection is a single Cap'n Proto socket on **FD #3**.
**`WebSession`** (`web-session.capnp`) maps HTTP onto a typed capnp interface
(`get`/`post`/WebDAV/WebSocket; whitelisted headers; a `Response` union). Most
apps don't speak capnp, so **`sandstorm-http-bridge`** is the grain entry-point:
it owns FD #3, implements `WebSession`, and proxies HTTP-over-RPC to a normal
HTTP server on `localhost:8000` inside the sandbox — injecting
`X-Sandstorm-User-Id` / `-Username` / `-Permissions` / `-Session-Id`. **This is
the key fact for the integration: the vast majority of catalog apps are just a
chroot running an ordinary HTTP server on :8000, fronted by the bridge.**

### 1.6 URL / domain model
A mandatory **wildcard host** (`WILDCARD_HOST=*.example.com`, sharing a parent
domain with `BASE_URL`); a fresh random unguessable subdomain per grain session.
External API access via a per-token `-api` host with `Authorization: Bearer`.
**Offer templates** let an app show a user an API token *without ever reading it*
(the shell substitutes `$API_TOKEN`/`$API_HOST` inside an iframe it controls).
Self-hosters get free wildcard DNS + Let's Encrypt TLS via **sandcats.io**.

### 1.7 Current state (honest)
**Alive but dormant-leaning.** Survived its company (Sandstorm Development Group;
hosted "Oasis" shut down 2019). On **2024-01-14** Kenton Varda handed governance
to the community (Open Source Collective) at **sandstorm.org**; he is no longer
maintainer (he leads Cloudflare Workers / `workerd` / Cap'n Proto). Maintained by
a thin volunteer bench (Jacob "ocdtrekkie" Weisz). **Last tag v0.308,
2023-08-06** — ~3 years with no tagged release; commits trickle (docs/deps,
latest observed 2026-05). Stuck on **MongoDB 2.6** (the long-standing upgrade
blocker). `curl https://install.sandstorm.io | bash` still works; the app market
is up. **Sandstorm is Apache-2.0.** Verdict: mechanically runnable and a great
*reference oracle + app source*, but you would be betting on a frozen-at-2023
platform with an aging Mongo and few maintainers. **This is exactly why the
dregg-native path (run the apps, not the platform) is the right primary bet.**

*Sources: sandstorm.io/how-it-works, docs.sandstorm.io (using/developing/
administering), sandstorm.io/news/{2014-08-13-sandbox-security,
2014-12-15-capnproto-0.5, 2024-01-14-move-to-sandstorm-org}, sandstorm.org/about,
capnproto.org/rpc.html, the `*.capnp` schemas in sandstorm-io/sandstorm.*

---

## 2. The deep alignment — why this is one object

| Sandstorm concept | dregg / DreggNet concept | Where it already exists |
|---|---|---|
| **grain** (object container: one document, frontend+DB) | **cell** (one sovereign object + its umem heap) | breadstuffs `cell/`, `turn/src/umem.rs` |
| grain private data (`/var`, RW) | the cell's **umem heap**, committed → a `content_root`/`data_root` | `webapp/src/hosting.rs` (SiteCell), umem |
| grain backup (ZIP) | the committed cell image — content-addressed **and re-witnessable** | deos-view trustless render |
| supervisor jail (ns + seccomp + ro-image/rw-var) | the **`Caged`** (seccomp-bpf + Landlock) / **`MicroVm`** (Firecracker) tier | `exec/src/lib.rs` `CapTier`, `docs/COMPUTE-TIERS.md` |
| grain runs on demand / idle-shutdown | a **lease**-funded workload; **durable** checkpoint; **umem** resume | `bridge/`, `durable/`, `service_economy.rs` |
| **powerbox** (trusted picker, designate=authorize) | the **CapDesk powerbox** (trusted UI mints an attenuated cap) | **breadstuffs `starbridge-v2/src/powerbox.rs`** (already built) |
| capnp capability (unforgeable interface ref) | a dregg **`CapabilityRef`** + its `EffectMask`/facets | `cell/src/facet.rs` |
| **SturdyRef** (persistent, sealed to owner) | a persisted attenuable **`dga1_…` / `HeldToken`** (caveat-chain re-verified) | `webauth/src/cred.rs`, `sdk/src/cipherclerk.rs` |
| cross-grain delegation / driver grain | the **membrane** forwarder (compose/forward authority) | `cell/src/membrane.rs` |
| `ViewInfo` permissions + roles | **named cap attenuations** (`Pred::AnyOf` facet sets) | `webauth/src/grant.rs` |
| `X-Sandstorm-Permissions` header | the cap's facets, derived per request from the held cap | (new shim — §5.B) |
| `sandstorm-http-bridge` (HTTP↔capnp, identity headers) | the **gateway** + a dregg bridge shim (HTTP↔workload, cap-derived headers) | `gateway/`, `webapp/router.rs` |
| `.spk` Ed25519-signed app image; App ID = pubkey | a signed app image; App ID = **issuer key** of the app's asset-well | breadstuffs issuer-cell identity model |
| confined foreign app as an object | the **android-cell** (foreign app, cap-bounded, receipted gates) | breadstuffs `android-cell/` |

The two crucial finds that de-risk the whole effort:

1. **dregg already has a powerbox.** `breadstuffs/starbridge-v2/src/powerbox.rs`
   is a CapDesk-modeled trusted-designation flow: a confined app-cell *requests* a
   cap it lacks; the trusted UI filters the picker to the principal's own held
   caps; the user designates; the UI mints a **strictly attenuating** cap into the
   app's c-list via a *real* `Effect::GrantCapability` turn, leaving a
   `TurnReceipt`. It is the Sandstorm powerbox, *already verifiable*. The integration
   work is the Cap'n Proto descriptor ↔ dregg-`Pred` translation, not the ceremony.

2. **dregg already runs foreign apps as cap-bounded cells.** `android-cell/`
   confines a whole foreign Android app behind receipted permission/storage/intent
   gates — the exact "a grain is a foreign app cell whose authority is visible and
   handed over by turns" pattern, proven on a much harder target than a chroot.

---

## 3. Grain = dregg cell + workload

A grain becomes a **`GrainCell`** (prototyped in `sandstorm-bridge/src/grain.rs`):
the grain's identity + ownership is a `CellId` + its holder cap; the grain's
private data is the cell's **umem heap** (committed → a `data_root`); the running
app is a **cap-bounded compute workload** at a `Caged`/`MicroVm` tier, admitted
and metered against a funded dregg **lease**.

The lifecycle maps onto machinery DreggNet already has:

| Sandstorm | dregg-native realization |
|---|---|
| **create** (`startGrain isNew`) | mint a fresh cell (the grain's umem heap); run the manifest **action** command once under a deploy-lease to initialize → `Running` |
| **open / wake** (`continueCommand`, keepAlive) | resume the workload from the last umem checkpoint under a funded lease → `Running`. `keepAlive` ↦ the lease's liveness tick |
| **sleep** (90 s idle shutdown) | checkpoint the umem heap (`durable/`), release the lease, reap the workload → `Sleeping`. A sleeping grain costs only storage |
| **backup** (ZIP) | the committed cell image *is* the backup — content-addressed and re-witnessable (no separate export) |
| **delete / transfer** | tombstone / re-own the cell (committed history persists) |

The economic invariant is the same one DreggNet already enforces: **a workload
only runs under a funded lease** (`bridge/src/lib.rs::Lease::funded`; "no run
beyond what the lease authorizes"). The prototype encodes this — `wake(false)`
(unfunded) refuses to start the grain, and uptime is metered only while
`Running`. The lifecycle reuses, with *no new engine*: `bridge/` (lease admission),
`durable/` (checkpoint/resume), umem (the passable witnessed image),
`webapp/src/hosting.rs` (the cell-as-served-object shape).

**Idle-shutdown → sleep is a direct economic win.** Sandstorm sleeps idle grains
to free RAM on one box; DreggNet sleeps idle grains to *stop the meter* — a
sleeping grain bills only storage, so a user can hold hundreds of grains and pay
compute only for the ones they're using. This is the cost model Liftoff (a
trusted always-on host) structurally cannot offer cheaply.

---

## 4. Powerbox = dregg caps (THE keystone)

This is where dregg makes Sandstorm's security **provable, not merely enforced.**

### 4.1 The mapping
A Sandstorm powerbox grant is a Cap'n Proto reference handed to a grain; the
supervisor enforces that the grain holds only what it was given. A dregg cap grant
is a strictly-attenuating `Effect::GrantCapability` turn that leaves a receipt —
so the *same* delegation becomes a fact a **light client can witness**: "user A
delegated cap C (facets {view}) over grain G to app B" is verifiable to a third
party who trusts neither host nor app. Sandstorm: *trust the supervisor.* dregg:
*verify the receipt.*

| Sandstorm | dregg |
|---|---|
| `LiveRef` (in-session) | a live `CapabilityRef` in a cell's c-list |
| **`SturdyRef`** (persistent, `sealFor: Owner`) | a persisted `dga1_…` / `HeldToken` whose **caveat-chain re-verifies on every use** (`cipherclerk.rs` `DelegationBinding`) — and is bound to the delegatee key, i.e. *sealed to its owner*: a leaked token is inert, exactly as `sealFor` intends |
| `save()` / `restore()` / `drop()` | persist the encoded token / re-verify it to a live cap / revoke (the cap-revocation path) |
| powerbox **request** (`PowerboxDescriptor` query) | a `PowerboxRequest` — the facets an app lacks (prototype: `powerbox.rs`) |
| descriptor **tag algebra** (`id` + `value`, MatchQuality) | a **`Pred`** over the cap's target + facets (breadstuffs' one boolean-matching algebra; `Pred::AnyOf` for facet sets) — the descriptor *is* a predicate, and dregg already has the proven `Pred` to evaluate it |
| the trusted **picker** | the **cipherclerk** / CapDesk picker: filter to the principal's *own* held caps (`Powerbox::present`) |
| **grant** (designation) | `PowerboxGrant::mint` → a strictly-attenuating `Effect::GrantCapability` turn (prototype enforces `granted ⊆ held`, refuses amplification in-band) |
| `ViewInfo` roles (viewer/editor/admin) | named attenuations: `editor = {view,edit}`, `viewer = {view}` — a role *is* a facet subset |
| `X-Sandstorm-Permissions` header | the held cap's facets, rendered into the request the bridge shim hands the app |
| cross-grain delegation / driver grain | the **membrane** forwarder: compose two held authorities into a guarded facet C requiring both — the "this app may reach that grain's API" weld, witnessed |

### 4.2 The bridge to build (`SturdyRef ↔ dregg cap`)
1. **Descriptor → Pred.** Parse a `PowerboxDescriptor` (tag `id` = the capnp
   interface type-id = the *kind* of resource; `value` = metadata/null-wildcard;
   `MatchQuality`) into a dregg `Pred` over `(target_kind, facets)`. The picker
   then filters the principal's held caps by `Pred` satisfaction — the same
   intersection Sandstorm does, but over dregg's proven matching algebra.
2. **Grant → turn.** The user's designation drives `Powerbox::grant` →
   `Effect::GrantCapability`, attenuated to exactly the designated facets. The
   `TurnReceipt` is the witnessed SturdyRef-mint.
3. **SturdyRef persistence.** `save()` returns the encoded `dga1_…` token bound to
   the delegatee key (the `sealFor` owner-seal). `restore()` re-verifies the
   caveat-chain → a live cap. `drop()` routes the revocation.
4. **The cipherclerk *is* the powerbox picker.** The browser extension / discord
   cipherclerk already does **authorization-first** rendering ("transfer 5
   computrons…", UNKNOWN-marked if unreadable) bound to the canonical turn hash.
   A powerbox grant is exactly this ceremony with a cap-grant turn — the human
   sees, in plain language, *what authority they are about to hand which app*,
   before any signature. This is a strictly better consent UI than Sandstorm's
   picker: it is **legible and witnessed**, not just trusted.

### 4.3 Why this is the headline
Sandstorm proved that designation=authority is *usable* at app scale. dregg adds
that it is *verifiable*. The powerbox-on-dregg is the first capability-delegation
UI where a third party can check, after the fact and trusting no one, that an app
holds exactly the authority it was granted and no more — the confused-deputy
immunity Sandstorm gives you *plus* a proof you can hand to an auditor.

---

## 5. Sandbox = a DreggNet compute tier

The Sandstorm supervisor jail (namespaces + seccomp-bpf + ro-app-image /
rw-grain-var, no further namespaces, no `/proc`) maps onto DreggNet's existing
isolation tiers (`docs/COMPUTE-TIERS.md`, `exec/src/lib.rs`):

- **`Caged`** (native + **seccomp-bpf** + **Landlock**) is the faithful analog of
  the supervisor — shared host kernel, syscall + filesystem allowlist. An
  http-bridge web app (a chroot serving HTTP on :8000) routes here. The
  prototype's `grain_spec()` does exactly this routing.
- **`MicroVm`** (Firecracker, its own guest kernel behind KVM) is *strictly
  stronger* than Sandstorm's shared-kernel supervisor — the route for raw /
  native-capnp apps and for any tenant who wants VM-grade isolation.
- **Never weaker.** A grain never routes to an in-process wasm tier; that would
  be a silent isolation *downgrade* below what Sandstorm assumes. The prototype's
  `SandboxTier` deliberately omits the wasm tiers, and `dreggnet-exec`'s
  `check_floor` rule (no silent downgrade, enforcement surfaced in `Output`) is
  the production backstop. **SBX deny-default + per-tenant isolation** are the
  same posture Sandstorm starts from (a new grain reaches *nothing*).

The read-only-app-image / read-write-grain-var split maps cleanly: the `.spk`
chroot is the immutable workload image (content-addressed, shared across grains
of the same app); the grain's `/var` is the cell's umem heap (per-grain,
committed). Per-grain network confinement (Sandstorm's net-namespace, no
outbound) = the dregg cap rule that a workload reaches the network only through a
**Network cap** (already threaded into the Caged tier via `instantiate_with_caps`
— `docs/COMPUTE-TIERS.md`): the *only* sanctioned outbound is a powerbox-granted
driver capability, exactly as Sandstorm requires.

---

## 6. Metered in $DREGG + verifiable serving

### 6.1 Metering
Every grain resource is a metered, receipted, $DREGG-settled charge on the same
exactly-once rail the lease economy already runs (`control/src/settle_ledger.rs`,
`storage/src/meter.rs::Pricing`, `StandingObligation`):

| resource | meter | settles as |
|---|---|---|
| grain **uptime** | per wall-clock period while `Running` (the prototype's `meter_period`) | a `StandingObligation` tick (the rent model) |
| grain **storage** | per-MB of the cell's umem heap, while `Sleeping` or `Running` | a per-period roll-up charge |
| **compute** inside the grain | per durable step / per request | the existing per-step lease meter |
| grain **bandwidth** | per-GB served by the gateway for this grain | a per-period roll-up (the new byte-counter, shared with §3.5 of the cloud plan) |
| **powerbox grant** | per grant (optional) | a `Payable` on the `Effect::GrantCapability` turn |

A lapsed lease reaps the grain (sleep → eventually delete), exactly the
"no run beyond what the lease authorizes" invariant applied to a long-running
object. **Verifiable billing:** every charge is a re-witnessable conserving
`Transfer`, not a dashboard number — the host cannot overcharge.

### 6.2 Verifiable serving (the differentiator)
A grain's HTTP session is served through the gateway (`gateway/src/hosting.rs`
`SiteHostHandler` shape, generalized from static to a live workload's responses),
under the `<name>.example.com` wildcard (the dregg analog of Sandstorm's
wildcard host + per-session hostname). Because the grain's data *is* a cell
carrying a `data_root` commitment, the served output can be wrapped
**trustlessly**: the visitor's browser re-witnesses that what it was served binds
to the committed grain cell (the `deos-view::render_trustless_cell_document`
projection the portal already uses). **The host cannot tamper with a grain's
served bytes without the visitor catching it** — a property no Sandstorm host,
and certainly no Liftoff host, offers.

The Sandstorm **offer-template** trick (show a user an API token the app never
reads) maps onto dregg's cipherclerk: an API/sharing token is a cap, minted and
displayed by the trusted clerk, never handled by the app — and now witnessed.

---

## 7. The app catalog — two approaches, assessed

The prize: run the hundreds of `.spk` apps (Etherpad, Wekan, Rocket.Chat, GitWeb,
Davros, TinyTinyRSS, Radicale, WordPress, Gitea, …) on dregg → an instant
self-hostable catalog, each app a cap-secured, metered, verifiable dregg grain.

### Approach A — run the real Sandstorm runtime as a DreggNet compute backend
Stand up an unmodified Sandstorm server (or just its backend+supervisor) inside a
DreggNet `MicroVm` node; bridge the grain's `/var` to a dregg cell (commit the
heap) and the powerbox to dregg caps (mirror each grant as a witnessed turn).

- **Pros:** instant 100% `.spk` compatibility, including native-capnp apps and the
  full powerbox-driver ecosystem; Sandstorm is the reference oracle for behavior;
  fastest path to "it runs Etherpad today."
- **Cons:** heavy and frozen (the Meteor shell + **MongoDB 2.6** + C++ backend, a
  2023-era platform with a thin maintainer bench); the verifiability is *bolted
  on* — the grain data lives in the supervisor's `/var`, and dregg can only commit
  a *snapshot* of it, not witness the transitions; the powerbox enforcement stays
  in the supervisor, so dregg mirrors grants rather than *being* the authority. The
  trust story is weaker (you still trust the Sandstorm supervisor).

### Approach B — adopt the grain/spk model dregg-native (recommended primary)
Run the `.spk` *app image* directly as a DreggNet workload, providing dregg's own
runtime for the grain contract — **because the contract is simple.** The vast
majority of catalog apps are http-bridge apps: a chroot running an ordinary HTTP
server on `localhost:8000`, fronted by `sandstorm-http-bridge`. dregg supplies:

- the **chroot as the Caged/MicroVm workload image** (the `.spk` archive
  unpacked, read-only, content-addressed);
- a **dregg http-bridge shim** — own the workload's ingress, serve the grain
  session over the gateway, and inject `X-Sandstorm-{User-Id,Username,
  Permissions,Session-Id}` *derived from the holder's dregg cap* (the cap's
  facets → the `Permissions` header). This is a small, well-specified shim (the
  `WebSession` HTTP-verb surface) over `gateway/` + `webapp/router.rs`;
- the **grain `/var` = the cell umem heap** (native commitment, real
  verifiability — the transitions are witnessed, not just snapshotted);
- the **powerbox = the dregg powerbox** (§4) — dregg *is* the authority.

- **Pros:** native verifiability (grain data + delegations + served bytes all
  witnessed); our metering; no MongoDB/Meteer/frozen-platform baggage; the
  powerbox is provable, not mirrored; runs the same unmodified app images. This is
  the make-it-sing path.
- **Cons:** more to build (the `.spk` unpack+verify, the http-bridge shim, the
  descriptor→Pred matcher); native-capnp apps (a small minority) and full driver
  grains are a later rung — until then they fall back to Approach A.

### Recommendation — staged hybrid, B-primary
1. **Lead with B for http-bridge apps** (the bulk of the catalog): `.spk` →
   verify the Ed25519 signature (App ID = the key) → unpack the chroot as a
   `Caged`/`MicroVm` workload image → run behind the dregg http-bridge shim →
   grain `/var` = a cell. This is where the verifiability and the differentiation
   live. Most of Etherpad/Wekan/GitWeb/Davros/TinyTinyRSS are reachable this way.
2. **Keep A as a compatibility fallback + oracle:** a real Sandstorm instance
   (on an operator's homelab — §10) for native-capnp apps, the driver ecosystem, and as
   the behavioral reference the B shim is differential-tested against.
3. **Catalog ingest reuses `dregg-deploy`** (the new crate from
   `docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.1): an `.spk` is just another
   `BuildPlan` source (`detect: spk`), so "install a Sandstorm app" rides the same
   clone→verify→publish durable, receipted pipeline as "deploy a git repo." The
   App ID (the signing key) is the source commitment.

---

## 8. The SURPASS framing

Liftoff hosts your one site on infrastructure you trust, pay-in-token. DreggNet ×
Sandstorm hosts **hundreds of cap-secured, self-hostable apps** where:

- **every app is an object you verify, not a service you trust** — the grain's
  data, its served bytes, and its bill are each re-witnessable against a committed
  cell; the host cannot lie about what it served or charged;
- **cross-app capability delegation is provable** — the powerbox-on-dregg is the
  first delegation UI where a light client can witness exactly what authority each
  app holds (confused-deputy immunity *with a proof*);
- **you pay only for what's awake** — idle grains sleep and bill only storage, a
  cost model an always-on trusted host can't match;
- **it's agent-native** — a grain is a cell, so an agent can spin one up, hold its
  cap, attenuate a sub-cap to a teammate, and coordinate over the intent ring;
- **it inherits a real app ecosystem** — Sandstorm already solved "package and
  isolate a web app as an object"; dregg makes that ecosystem verifiable.

Not a better Liftoff, and not a revived Sandstorm — a third category:
**a verifiable, metered, agent-native object-capability cloud with Sandstorm's
app catalog and dregg's proofs.**

---

## 9. The buildable plan

Dependency order (each item a disjoint new crate/module — swarm-safe; the shared
`gateway`/`Cargo.toml` edits stay with the main loop in quiet windows):

```
  ① sandstorm-bridge core (manifest parse + grain-cell + powerbox map)   [PROTOTYPED]
        │
        ├─ ② .spk reader  — Ed25519-verify + XZ + capnp Archive unpack → workload image
        ├─ ③ powerbox descriptor↔Pred matcher + the SturdyRef(dga1_)↔cap bridge
        │       (welds onto breadstuffs starbridge-v2/powerbox.rs + cipherclerk)
        ├─ ④ the dregg http-bridge shim — WebSession surface over gateway,
        │       cap-derived X-Sandstorm-Permissions, grain /var = cell umem
        └─ ⑤ catalog ingest via dregg-deploy (`detect: spk`) + grain lifecycle
                wired to bridge/durable (lease admission, checkpoint, sleep/wake)
```

### Priority worklist (highest value first)
1. **`sandstorm-bridge` core** — *done as the prototype* (`../sandstorm-bridge/`):
   the manifest parser, the grain=cell lifecycle state machine, the powerbox=cap
   grant ceremony, all green. Promote it from a detached spike to a wired crate.
2. **The `.spk` reader (②).** Ed25519 signature verify (App ID = the key), XZ
   decompress, capnp `Archive` unpack → a content-addressed workload image. The
   manifest decode swaps the prototype's JSON projection for a real capnp read.
3. **The powerbox descriptor↔Pred bridge (③).** The keystone weld: parse
   `PowerboxDescriptor` → `Pred`; route the grant through breadstuffs'
   `starbridge-v2/src/powerbox.rs` (`Effect::GrantCapability` + receipt);
   persist/restore the SturdyRef as a `dga1_…` token (cipherclerk).
4. **The dregg http-bridge shim (④).** The `WebSession` HTTP surface over the
   gateway; cap-facets → `X-Sandstorm-Permissions`; grain `/var` ↔ cell umem.
5. **Catalog ingest + lifecycle (⑤).** `.spk` as a `dregg-deploy` source; the
   grain lifecycle wired to `bridge/` (admission) + `durable/` (checkpoint) +
   the uptime/storage meters.

### Safe-autonomous-tonight subset vs reviewed-go
**SAFE-AUTONOMOUS (build + prove + test + stage; reversible; green-gated):**
- The `sandstorm-bridge` core — **delivered** (`../sandstorm-bridge/`, 13 tests).
- The `.spk` reader (signature-verify + unpack), tested against a few real public
  `.spk`s fetched read-only (or fixtures) — local, no execution of the app.
- The descriptor↔Pred matcher + the SturdyRef↔cap mapping as pure, tested code
  welded onto the existing breadstuffs powerbox/cipherclerk surfaces (no VK, no
  new effect — `Effect::GrantCapability` already exists).
- The http-bridge shim's `WebSession`→HTTP translation as a tested library type
  (the gateway mount + cap-derived headers), driven in-process / over local TCP
  the way `webapp`/`storage` prove themselves.
- The grain lifecycle wired to the in-process lease/durable/meter path
  (LocalProvider), end-to-end: install a fixture `.spk` → create a grain cell →
  wake under a funded lease → serve a request → meter → sleep (checkpoint) → wake.

**REVIEWED-GO (stop + queue to `MORNING-REVIEW.md`):**
- **Actually executing a downloaded `.spk` app** on a live tier (untrusted
  third-party code in `Caged`/`MicroVm`) beyond local fixtures — a real
  sandbox-escape surface; needs the Firecracker boot + jailer (the hardware-gated
  `MicroVm` rung) and a review.
- Running a **real Sandstorm instance in prod** / pointing the live catalog at it
  (Approach A) — and any public go-live of the app catalog.
- The **live `example.com` wildcard serving** of grains (the `deploy/` Caddy +
  cert lane).
- Charging **real $DREGG** for grain uptime/storage (the early era is subsidized).

The dividing line is the project standard: the *code + verified local proof* is
safe-autonomous; *executing untrusted catalog code* and *operated public reality*
are reviewed-go.

---

## 10. What an operator should set up (homelab)

A real Sandstorm instance is wanted as the **reference oracle + app source** the
dregg-native shim (Approach B) is differential-tested against, and as the
Approach-A fallback host. Concretely, on the operator's homelab:

1. **Install Sandstorm** on a Linux box (KVM-capable — the homelab has it):
   `curl https://install.sandstorm.io | bash` (the GPG-verified installer still
   works). Accept the defaults; note it lands on the 2023 v0.308 line.
2. **Set the wildcard host + TLS**: configure `BASE_URL` + `WILDCARD_HOST` on a
   subdomain the operator controls (or use the free **sandcats.io** dynamic DNS + the
   built-in **Let's Encrypt** path, on since 2020). The wildcard host is mandatory
   — Sandstorm won't serve grains without it.
3. **Install ~5 representative apps from `apps.sandstorm.io`** spanning the shapes
   we map first: **Etherpad** (collab editor, http-bridge), **Wekan** (kanban),
   **GitWeb or Gitea** (git host), **Davros** (file storage / WebDAV — exercises
   the non-GET `WebSession` verbs), **TinyTinyRSS** (RSS). Create one grain of
   each and confirm it serves.
4. **Expose the instance to me on the mesh** (read-only is fine): the **base URL**,
   one **grain session URL**, and one **API token** (`-api` host + Bearer) per
   app, so the dregg http-bridge shim can be tested against real `WebSession`
   traffic and real `X-Sandstorm-Permissions` headers.
5. **Hand over a few `.spk` files** (the actual packages for the 5 apps above —
   downloadable from the market or via `spk` ) so the `.spk` reader (②) and the
   manifest decode can be tested against genuine signed packages, not fixtures.
6. **Optionally**: `vagrant-spk`/`spk dev` set up on the box, so we can observe the
   bridge contract live (FD #3, the `:8000` localhost server, the identity-header
   injection) while building the dregg shim.

That gives us: a behavioral oracle for the shim, real signed `.spk`s for the
reader, real `WebSession`/permission traffic to differential-test against, and an
Approach-A fallback host for the native-capnp apps — everything the dregg-native
build needs to be verified against the real thing.

---

## 11. Status

- **Research:** complete (§1) — grains, powerbox, capnp, `.spk`, runtime, URL
  model, and an honest current-state read (frozen-at-2023, community-maintained,
  Apache-2.0, MongoDB-2.6-blocked; Varda → Cloudflare/`workerd`/Cap'n Proto).
- **Design:** complete (§2–§8) — the grain=cell, powerbox=verifiable-cap,
  sandbox=tier, metered, verifiable-serving, catalog (B-primary hybrid), surpass.
- **Prototype:** delivered + green (`../sandstorm-bridge/`, 13 tests) — the
  manifest parser, the grain lifecycle, the powerbox grant ceremony.
- **Next:** the `.spk` reader (②) and the descriptor↔Pred / SturdyRef↔cap bridge
  (③) are the safe-autonomous follow-ons; executing real catalog code and any
  live serving are reviewed-go.

*Dated 2026-06-29. Verify file paths against HEAD before relying on a specific
line.*
