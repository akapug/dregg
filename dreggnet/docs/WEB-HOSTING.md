# Web hosting — minisites on `example.com`

DreggNet hosts static minisites on the verified rail: **a site is a dregg cell.**
An agent or user publishes static web content (HTML/CSS/JS, images — a whole
`index.html` + assets) under a name, and it is served at `<name>.example.com`.
Publishing is a cap-gated, receipted turn, so *who published what* is provable;
serving is read-only and public.

This is the static sibling of the agent-served web API (`docs/AGENT-WEB-APPS.md`):
that capability serves an agent's *dynamic* routes → polyana handlers; this one
serves *static* content out of a published cell.

```text
  PUBLISH (cap-gated, receipted)              SERVE (read-only, public)
  ────────────────────────────               ─────────────────────────
  PublishCap  site-host/<name>               GET https://<name>.example.com/
    └─ SiteRegistry::publish ─▶ SiteCell       └─ Caddy (wildcard TLS)
         { name, owner, content_root,              └─ gateway  SiteHostHandler
           content: path → Asset }                      └─ SiteRegistry::resolve
       + PublishReceipt                                      host → cell → asset
       (who published what, at which root)                   bytes + content-type
```

## A site is a cell (the model)

A hosted minisite is a `SiteCell` (`webapp/src/hosting.rs`):

| field          | meaning                                                            |
|----------------|-------------------------------------------------------------------|
| `name`         | the route name — the subdomain label served at `<name>.example.com` |
| `owner`        | the publishing cell/agent (the cap holder) — provable in the receipt |
| `content_root` | a deterministic commitment to the content (the cell's umem heap root on a real node) |
| `content`      | the served assets: a `path → Asset` map (`Asset` = bytes + content-type) |

On a real dregg node this is a cap-bounded cell whose committed umem heap holds
these fields. Publishing writes that cell; the served bytes bind to `content_root`,
which is what makes trustless serving possible (below).

## The publish flow

Publishing is gated by a `site-host/<name>` capability held by the owner. The cap
is bound to BOTH the holder and the site name, so it can only be exercised to
publish the one site it names — the turn's cap-attenuation. A publish that clears
the gate writes the cell and returns a `PublishReceipt { seq, name, owner,
content_root, asset_count }` — the verifiable record of who published what.

Three ways to drive it:

- **CLI / binary** — `dreggnet-host` (`webapp/src/bin/dreggnet-host.rs`) reads a
  directory of static files, publishes it as a site cell, and serves it:
  ```sh
  dreggnet-host --dir ./site --name blog --owner agent:ember --port 8080
  # by Host (what example.com routes):
  curl -s -H 'Host: blog.example.com' http://localhost:8080/
  # no-DNS local fallbacks:
  curl -s -H 'Host: blog' http://localhost:8080/style.css   # bare-label Host
  curl -s http://localhost:8080/blog/                       # /<name>/… path prefix
  ```
- **API / library** — build a `SiteContent`, call `SiteRegistry::publish(&cap,
  name, content)`, get a `PublishReceipt`. The registry is the data plane the
  gateway resolves against.
- **SDK / agent (later)** — a discord-bot or portal flow that takes content + a
  name and drives the same `publish`. The cap a real agent presents is the dregg
  `site-host/<name>` capability granted to it.

## Serving on the gateway

The gateway resolves an inbound request's `Host` to a published site cell and
serves its content read-only:

- `gateway/src/hosting.rs` — `SiteHostHandler`, the `httpe` handler over a shared
  `Arc<SiteRegistry>`. It reads the `Host` header, resolves `<name>.example.com`
  → the site cell (`SiteRegistry::resolve`), and serves the requested path's asset
  with its correct content-type. An unknown host or path is a `404`.
- Standard static-host path conventions apply: `/` and a trailing-slash directory
  serve `index.html`; content-types are inferred from the file extension
  (`content_type_for`).
- The portable `dreggnet-host` binary is the any-host serving path (std TCP,
  cross-platform); the `httpe` `SiteHostHandler` is the Linux production mount —
  the same split the dynamic webapp `Router`/`dreggnet-serve` already use.

Host resolution (`site_name_from_host`): `<name>.example.com[:port]` → `name`;
the bare apex `example.com` and `www.example.com` resolve to nothing (no per-site
landing); a bare single label (`blog`, `blog:8080`) is taken as the name for
no-DNS local testing.

> **Subdomain, not path-prefix.** Sites are served at `<name>.example.com`, not
> `example.com/<name>`. Subdomain isolation is cleaner: each site gets its own
> origin (separate cookie/storage/CORS scope), and a wildcard proxy rule routes
> them all without per-site Caddy edits. (The `dreggnet-host` binary additionally
> accepts a `/<name>/…` path prefix purely as a no-DNS local convenience.)

## `example.com` routing — DNS + Caddy (design; deferred to the deploy lane)

The edge box (`<EDGE_HOST>`) runs Caddy as the only public door; it terminates
TLS and reverse-proxies to `gateway:8080` (see `deploy/staging/Caddyfile`). Web
hosting needs two additions, **to be wired by whoever owns `deploy/`** — this doc
is the spec, the live `Caddyfile` is intentionally NOT edited here.

### 1. DNS — a wildcard record

```
*.example.com.   A   <EDGE_HOST>      ; (or CNAME → the edge name)
example.com.     A   <EDGE_HOST>      ; apex (optional: a landing page)
```

A wildcard `*.example.com` so any published `<name>.example.com` reaches the edge
without a per-site DNS change.

### 2. Caddy — a wildcard host block

Add a block that matches `*.example.com` and proxies to the gateway, which does
the per-site resolution by `Host`:

```caddy
# *.example.com — published minisite cells, served by the gateway's SiteHostHandler.
# NO basic-auth: a published public site is served to anyone (the publish was the
# cap-gated step; reads are free). The gateway resolves the Host to the site cell.
*.example.com {
	encode gzip
	reverse_proxy gateway:8080
}
```

### 3. Wildcard TLS — the one real requirement

A wildcard host needs a wildcard certificate, which Let's Encrypt only issues over
the **DNS-01** challenge (HTTP-01 cannot satisfy `*.example.com`). Two options:

- **Wildcard cert via DNS-01 (recommended).** Configure Caddy with the DNS
  provider plugin for wherever `example.com` is hosted and issue `*.example.com`:
  ```caddy
  *.example.com {
  	tls {
  		dns <provider> {env.DNS_API_TOKEN}
  	}
  	encode gzip
  	reverse_proxy gateway:8080
  }
  ```
  This needs a Caddy build with the DNS-provider module and an API token in the
  environment. One cert covers every site.
- **On-demand TLS (per-name certs, HTTP-01).** Caddy issues a cert per concrete
  hostname on first request:
  ```caddy
  {
  	on_demand_tls {
  		# ask the gateway whether <name> is a published site before issuing
  		ask http://gateway:8080/internal/site-exists
  	}
  }
  https:// {
  	tls {
  		on_demand
  	}
  	reverse_proxy gateway:8080
  }
  ```
  This avoids a DNS plugin but issues a cert per site (rate-limit aware) and wants
  an `ask` endpoint so Caddy only mints certs for real sites — a small gateway
  route to add when this option is chosen. DNS-01 wildcard is simpler and is the
  recommended path.

## What is code-proven vs the live-deploy step

**Code-proven now** (`cargo test -p dreggnet-webapp`, green):

- The cell model, cap-gate (a `site-host/<name>` cap only authorizes its named
  site — a wrong cap is refused), the deterministic `content_root`, and the
  receipt.
- The host→site resolver and read-only static serving with correct content-types.
- The **publish→serve round-trip over real TCP** (`webapp/tests/site_publish_serve.rs`):
  publish a minisite (`index.html` + `style.css`) → stand up a local gateway over
  the registry → `GET` both routes over a real socket → assert the served bytes
  and content-types, plus unknown-site and unknown-path `404`s.
- The gateway adoption (`gateway/src/hosting.rs::SiteHostHandler`) — serving a
  published cell by `Host`, with its content-type preserved — built and tested via
  the cross-target Linux build (`cargo zigbuild --target x86_64-unknown-linux-gnu
  -p dreggnet-gateway`).

**Deferred — the live `example.com` deploy** (owned by the `deploy/` lane):

- The DNS wildcard `*.example.com → <EDGE_HOST>` and the Caddy wildcard host
  block + wildcard TLS (DNS-01 cert, or on-demand) specified above. The live
  `Caddyfile` is not edited here.
- Mounting `SiteHostHandler` in the gateway serving binary's connection loop
  (`gateway/src/main.rs`) — today the handler is a library type with tests, the
  same state `WebAppHandler` is in. Wiring it (and a shared registry the publish
  side writes) is the mount step, alongside the Caddy wildcard.

**The on-chain write (the dregg-verify lane):** committing the `SiteCell` to a real
dregg node — the publish turn as an `Effect::Write` to the content cell, witnessed
as a dregg receipt — lands on the same surface `dreggnet-bridge`'s `dregg_verify`
module names (`witness_receipt` / `query_shadow_attest_whole_log`). The in-process
`SiteRegistry` is the data plane; the `content_root` computed here is the
stand-in for the cell's committed heap root. That wire is the deliberate flip-on
step (default-off, AGPL isolation — see `bridge/src/dregg_verify.rs`).

## Trustless serving — the docuverse tie-in

Because a site IS a cell carrying a `content_root` commitment, the same content
can be served **trustlessly**: the cell's content wrapped so the visitor's browser
re-witnesses that the served bytes match the committed cell state (per-asset
openings against the heap root), re-witnessing nothing itself. This is exactly the
projection `deos-view::render_trustless_cell_document` performs for any dregg cell —
the same renderer the public portal (`portal.example.com`) already uses to serve
trustless cell cards (light-client verify in the tab).

That renderer lives in the breadstuffs `deos-view` workspace (AGPL, separate). The
hosting layer here carries the `content_root` commitment it needs and the cell
shape it renders; the plain serving above is the public read path, and the
trustless wrap is the verify-in-tab upgrade over the same site cell. So a minisite
on `example.com` is not just *served* — it can be *proven* to be the genuine
published cell, the docuverse property applied to ordinary web content.
