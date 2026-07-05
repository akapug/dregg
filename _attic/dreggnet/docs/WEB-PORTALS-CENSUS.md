# DreggNet — the web-portals census

*Ember asked: "how many web portals do we have anyway?"* — here is the honest,
code-grounded count. Scope: `DreggNet/` (excluding `circuit/` + `metatheory/`)
plus the relevant `breadstuffs/` web bits the cloud actually serves. Each surface
is read from source, not from memory.

## TL;DR — the count

There is **no single number** that isn't slightly dishonest, because "web portal"
spans three different things. The honest breakdown:

- **~8 human-facing web UIs / portals** (a person opens these in a browser).
- **~10 machine-facing HTTP service surfaces** (APIs/webhooks/data-planes — web,
  but not "a portal you click around").
- **~4 rendering engines / libraries** that *power* the UIs above (not portals
  themselves, but they're where the HTML comes from).

If ember wants the one-liner: **about 8 portals, ~18 web-facing surfaces total.**
And there is real overlap (three different "host a static site" code paths; two
cipherclerk extension builds; the portal's data is served by the *Discord bot*).

The honest headline: the **one polished, public, human portal is
`portal.dregg.studio`** (the live-network viewer + trustless verify + drive
layer). Everything else is either an operator tool (ops, Grafana), an auth gate
(webauth login), a wallet (the extension), a control-plane API (gateway/node), or
a developer/demo surface. Several are stubs or prototypes — flagged below.

---

## The table

| # | Surface | What it is / does | State | Audience | Tech |
|---|---------|-------------------|-------|----------|------|
| **HUMAN-FACING PORTALS / UIs** |
| 1 | **`portal.dregg.studio`** (`breadstuffs/portal/` + baked by `deos-view/examples/portal_bake.rs`; served by Caddy from `/srv/portal`) | The public read-mostly portal: cell graph (SVG), live cells list, **per-cell trustless verify in your own browser** (recursive-STARK wasm light client), and a **drive layer** (`drive.html` — connect wallet, publish a minisite, open a lease, fire a transfer). | **Live (v1, read + drive).** Read-only + the drive rung landed; footer still says "drive-actions are the next rung" in the static index. | End-user / visitor | Static HTML/CSS + `portal.js` (vanilla) + `@dregg/sdk/browser` + wasm light client (`portal/dist/pkg`) |
| 2 | **`cell.html`** (the trustless cell-view) (`deos-view/src/web.rs` → `render_trustless_cell_document`) | Renders one cell's deos card wrapped in a light-client **trust banner that verifies the STARK aggregate in-tab**. The "verify UI." Part of the portal. | **Live.** The keystone verify surface. | End-user / visitor | Static HTML baked from the deos `ViewNode` web renderer + wasm |
| 3 | **ops dashboard** `dreggnet-ops` (`ops/`, `:8090`, `ops.dreggnet.fg-goose.online`) | The operator's single pane of glass: all-activity feed, status tables (leases/machines/federation/consensus), **History tab** (faceted "what happened" ledger), log tailing (Docker Engine API), whole-cloud health rollup, **coin-bridge observability**, and a **Grafana cross-link** in the header. | **Live.** Real aggregator (degrades gracefully per-source). | Operator | Single self-contained HTML page (`render.rs`) + JSON APIs; pure-std thread-per-conn HTTP server |
| 4 | **gateway landing page** (`gateway/src/status.rs`, `:8080` `GET /`) | The friendly front door a human/probe sees at the gateway root: "alive, N machines, federation healthy, see portal." Plus `/status` JSON + `/healthz`. | **Live.** Small but real. | Operator / visitor | Server-rendered HTML string + JSON |
| 5 | **webauth login page** (`webauth/src/server.rs`, `:8099`, `/.dregg-auth/*`) | The forward-auth login: paste / wallet-sign a `dga1_…` dregg credential → session cookie → admit. Gates ops/Grafana/gateway-admin by **capability** (no passwords). | **Code-proven; live-edge rewire is a deploy step.** The `forward_auth` blocks are wired in the Caddyfile; break-glass override still recommended on. | Operator (logging in) | Server-rendered HTML login form; pure-std HTTP server |
| 6 | **Grafana** (`deploy/observability/grafana/`, `:3000`, `grafana.dreggnet.fg-goose.online`) | The deep time-series observability: **9 provisioned dashboards** (hosts, protocol, consensus, compute, economy, cloud, cloud-health, bridge, security), Prometheus datasource, alertmanager, blackbox/json/thermal exporters. | **Live (provisioned).** Real dashboards + rules. | Operator | Grafana (provisioned JSON dashboards) behind webauth `grafana-view` cap |
| 7 | **Dragon's Egg Cipherclerk** browser extension (`breadstuffs/extension/`) | The **wallet + trusted-picker cap-grant ceremony**: `confirm-intent.html`, `disclosure-picker.html`, `origin-permission.html` — the user designates a capability, the extension signs the turn, injects `window.dregg`. The cap-auth web flow. | **Built** (Chrome + Firefox manifests, BIP39, wasm). Maturity unverified here; this is the real wallet. | End-user | MV3 browser extension (HTML ceremony pages + wasm) |
| 8 | **sdk-ts extension** (`breadstuffs/sdk-ts/extension/`) | A **second** extension build from the TS SDK: `popup.html` + `example-dapp.html` — the SDK's reference wallet + a demo dApp. | **Example / reference.** Overlaps #7. | Developer | MV3 extension + example page |
| **MACHINE-FACING HTTP SERVICE SURFACES** |
| 9 | **gateway machines API** (`gateway/src/lib.rs`, `/v1/apps/{app}/machines`) | Fly-Machines-API-compatible control plane: create/list/status/stop/start/destroy a durable workload; each create → a dregg execution-lease. | **Live (real routing + lease-gate).** | Developer (fly client) | JSON HTTP over `httpe`/Elide |
| 10 | **gateway storage handler** (`gateway/src/storage.rs`, `/storage/<bucket>/<key>`) | S3-ish object store on the verified rail: cap-gated metered PUT/GET/DELETE/list + public trustless read (`?opening`). | **Live; on-chain `Effect::Write` is the named flip-on.** | Developer | JSON / bytes HTTP |
| 11 | **gateway SiteHostHandler** (`gateway/src/hosting.rs`, `*.dregg.works`) | The edge static-minisite data plane: resolve `Host: <name>` → published `SiteCell` → serve bytes. | **Live (in-process registry; on-chain write is the flip-on).** | End-user (visitor) / developer (publisher) | Static serving over `httpe` |
| 12 | **gateway WebAppHandler** (`gateway/src/webapp.rs`) | Edge data plane for **agent-served web APIs**: routes inbound HTTP → the leased sandbox handler. | **Live (single-app; per-host mux is a later rung).** | Developer / end-user | HTTP → owned wasmi sandbox |
| 13 | **`webapp` portable serve binaries** (`webapp/src/bin/dreggnet-{host,serve}.rs`, `serve.rs`) | The **standalone / any-host** version of static + dynamic serving (the `dregg deploy --serve` round-trip) + the `.well-known/dregg-receipt.json` trustless read. | **Live.** Overlaps the gateway handlers (#11/#12). | Developer | pure-std TCP serving loop |
| 14 | **dregg node read API** (`breadstuffs/node/src/api.rs`, `:8420`; `ws.rs`) | The node's localhost Axum read API the **browser-extension cipherclerk talks to** + SSE + websocket. The data backbone everything reads from. | **Live.** | Developer / wallet | Axum + SSE + WS |
| 15 | **discord-bot HTTP surface** (`breadstuffs/discord-bot/src/http_server.rs`, `:8080`) | The bot as a first-class dregg peer: `/api/cells`, `/api/cell/<id>`, `/api/receipts/recent`, `/api/federations`, `/observability/stream` (SSE). **This is what actually backs `portal.dregg.studio`'s `/api/*` + `/observability/*`** (per the Caddyfile) and the `/admin*` surface. | **Live (production-grade module).** | Developer / portal backend | Axum 0.8 + SSE, rate-limit + CORS |
| 16 | **discord deos surface** (`breadstuffs/discord-bot/src/deos_surface.rs`) | Discord *as* the web-of-cells front: affordances → buttons (per-viewer attenuated), transclusion → embeds, `dregg://` links + what-links-here. The "web surface" is Discord's interaction model. | **Live weld over real primitives (with a named seam).** | End-user (Discord) | Discord interactions (buttons/embeds) |
| 17 | **discharge-gateway** (`breadstuffs/discharge-gateway/`) | Macaroon third-party-caveat discharge service: `POST /discharge`, `GET /conditions`, `GET /health`. | **Built.** | Developer / service | Axum JSON |
| 18 | **stripe-receiver** (`demo/stripe-receiver/`, `:4242` `/webhook`) | A real Stripe webhook endpoint running the genuine `stripe_mirror` verify+mint path — the on-camera "a real Stripe event funds the agent" demo. | **Demo (local-only, on-camera).** | Operator (demo) | pure HTTP webhook |
| 19 | **dregg-domains** (`dregg-domains/`) | BYO custom domains: ACME-style proof-of-control (`_dregg-verify` TXT / CNAME) → gateway `Host` → site cell + cert. Drives the Caddy `on_demand_tls ask` hook. | **Built (control-plane; library, not a UI).** | Developer | Library + DNS/HTTP routing |
| **POWERING ENGINES / LIBRARIES (not portals themselves)** |
| 20 | **deos-view web renderer** (`deos-view/src/web.rs`) | Walks the deos `ViewNode` tree → HTML (the same tree the native gpui cockpit renders). The engine behind #1/#2 and the cockpit's web projection. | **Live.** | (infra) | gpui-free Rust → HTML string |
| 21 | **deos-web-cells** (`deos-web-cells/`) | Web-of-cells: transclusion, rehydrate, cascade, surface-capture — the docuverse web primitive. | **Built / prototype.** | (infra) | Rust |
| 22 | **deos-leptos** (`deos-leptos/`) | Prototype: the Leptos signal-graph as the deos reactive-affordance web runtime (server-render → per-island hydrate = frustum rehydration). | **Working prototype (ember's hypothesis, confirmed).** | (infra / R&D) | Leptos (Rust full-stack) |
| 23 | **wasm light client** (`breadstuffs/wasm/`) | The in-browser verify engine + `DreggRuntime` playground (mint/attenuate/STARK/Datalog/full runtime sim). Powers the portal's in-tab verify. | **Live (powers the portal) + playground.** | End-user / developer | Rust→wasm |

`dregg-deploy/` (auto-deploy-from-git) and `dregg-ipfs/` (IPFS CID bridge) are
web-*adjacent* (they feed hosting) but are CLI/library, not surfaces — noted for
completeness, not counted.

---

## What's missing / rough / half-built (gaps)

- **The drive layer is the youngest rung.** `portal.dregg.studio` is real and live
  for *reading + verifying*, and the drive UI (`drive.html` / `drive-ui.mjs`) is
  written, but the static portal index still advertises drive-actions as "the next
  rung." This is the gap between "see the network" and "use the network in the
  browser" — and it's the single highest-value place to finish.
- **webauth is code-proven but not yet the live default.** The cap-based
  forward-auth + login page exist and are tested; the Caddyfile `forward_auth`
  blocks are wired, but the honest scope note says keep break-glass on until the
  cap flow is exercised in production. Until then, the edge is still partly on the
  old gate.
- **Storage / hosting carry an honest in-process seam.** The data planes (#10/#11)
  serve real cap-gated, receipted bytes, but the leaf/root are FNV stand-ins for
  the committed Poseidon2 umem root and the on-chain `Effect::Write` is the named
  flip-on. The *property* is right; the on-chain witness is the deliberate next step.
- **Several catalog services are roadmap, not shipped** (`docs/SERVICES.md`):
  pub/sub, queues, secrets/KMS-as-a-service, identity-as-a-service are designed but
  not surfaced. No web front door for them yet.
- **No unified "console."** There is no single authenticated developer console that
  ties identity + machines + storage + hosting + billing into one signed-in
  experience. Today that's split across the gateway API (#9–12), the ops dashboard
  (operator-only), and the portal (public read). A *customer*-facing console is a
  gap.
- **The gateway landing page is a one-screen stub** (real, but minimal) — fine as a
  front door, not a product surface.
- **stripe-receiver is a demo**, not a billing portal.
- **deos-leptos / deos-web-cells are prototypes** — promising (the Leptos-as-deos
  runtime is confirmed) but not a shipped product surface.

## Overlaps — what's doing the same job (candidates to merge)

- **Three "host a static site" code paths.** `gateway/src/hosting.rs`
  (`SiteHostHandler`, edge), `webapp/src/{hosting,serve}.rs` (`dreggnet-host` /
  `dreggnet-serve`, portable/standalone), and the `webapp` data plane. They share
  the `SiteRegistry` model but are three serving loops. The portable binaries are
  the dev/round-trip path; the gateway is the edge path — but the duplication of the
  serving loop is real. **Candidate: one serving core, two front-ends.**
- **Two cipherclerk browser extensions** (`extension/` = Dragon's Egg, the real
  wallet; `sdk-ts/extension/` = the SDK reference build). These should converge or
  the SDK one should be explicitly "example only."
- **The portal's data is served by the Discord bot.** `portal.dregg.studio`'s
  `/api/*` and `/observability/*` proxy to `dreggnet-discord-bot:8080` (Caddyfile),
  while the node *also* exposes `/api/cells` etc. (`node/src/api.rs`). Two read
  APIs of nearly the same shape (`CellStateView`). **Candidate: the portal should
  read the node directly (or the bot's read surface should be a thin, named proxy),
  not couple the public portal to the Discord bot's lifecycle.**
- **Three observability surfaces.** The ops dashboard's history/health tiles,
  Grafana, and the `/observability/stream` SSE all show "what's happening." Ops
  cross-links to Grafana (good), but the boundary (live tiles vs deep time-series
  vs raw stream) could be stated once.
- **deos-view web renderer vs the portal's hand-written `portal.js`.** The cell
  cards come from the proven deos renderer; the live shell is vanilla JS. Fine, but
  worth knowing the portal is *half* proven-renderer, *half* bespoke glue.

## The highest-value web-surface work (synthesis)

1. **Finish + foreground the portal drive layer.** The portal is the one public,
   polished, human surface and it already reads+verifies the live network. Making
   "connect wallet → publish a site / open a lease / fire a transfer → verify it
   in-tab" the *front-and-center* flow (and updating the static index that still
   calls it "the next rung") turns a viewer into a usable product. This is the
   single best lever.
2. **Land webauth as the live default + retire the old gate.** Cap-based login is
   the dregg-native auth story and it's already code-proven; exercising it in
   production (and dropping break-glass) makes every operator surface coherent.
3. **Decouple the public portal from the Discord bot** by pointing `/api/*` at the
   node's read API (or a named gateway read surface), so the marketing/portal
   surface doesn't depend on a chat bot being up.
4. **Build the customer console** (the missing surface): one signed-in page over
   identity + machines + storage + hosting + billing — the thing that turns the
   federated APIs into a product a stranger can self-serve. This is the biggest net-
   new opportunity and the natural home for the roadmap catalog services.
5. **Collapse the three static-hosting serving loops** into one core to kill the
   duplication before more divergence accrues.

---
*Grounded against `DreggNet@dev` and `breadstuffs` at census time. Surfaces marked
"live" are reachable + real per their module docs; "built" = code-complete, edge/
prod wiring may be a deploy step; "prototype/demo/stub" say exactly that.*
