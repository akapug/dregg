# HTTPE-TIDY-PLAN — tidying the gateway's HTTP engine for production

The DreggNet gateway (`dreggnet-gateway`) is the public-facing serving layer:
it serves the fly-compatible machines API, the `*.example.com` static minisites
(the permissionless-hosting surface), and the friendly root/status/health
surfaces. This document assesses the HTTP engine the gateway is built on (the
bundled Elide `net/httpe` stack), names the production-readiness gaps, and lays
out a concrete, prioritized tidy-up — split into a **safe-autonomous-tonight**
subset (code cleanup + tests + hardening, no deployed-behavior change) and a
**reviewed-go** subset (anything touching the public wire behavior or the
dependency surface).

The single most important finding up front, because it reframes everything
below:

> **The gateway links the entire `httpe` engine but uses only ~6 of its small
> value types.** The real serving loop in `gateway/src/main.rs` is hand-rolled
> on `std::net::TcpListener` + thread-per-connection. The Elide CQ engine
> (compio/io_uring event loop, H1/H2/H3, middleware, ACME, reverse proxy, JVM
> FFI, the EAP license timebomb) is compiled and linked in, but **never
> started**. The gateway pays the full cost of a heavyweight, proprietary,
> Linux-only engine with a large git-fork closure to borrow `Method`,
> `StatusCode`, `ResponseWriter`, `Handler`, `Request`, and `HandlerResult`.

That coupling is the center of gravity for the tidy-up.

---

## 1. The current state — what httpe IS and how the gateway uses it

### 1.1 What `httpe` is

`net/httpe` (crate `elidehttp`, lib name `elidehttp`) is the full Elide HTTP
engine, vendored from an internal Elide HTTP-engine source tree. It is a single
sophisticated crate covering, per `net/httpe/src/lib.rs`:

- **The CQ engine** (`cq/`, `pub(crate)`) — a compio/io_uring + ntex event loop;
  H1/H2/H3 server *and* client, headless CQ for `elide run`, zero-downtime
  upgrade / connection migration, signal-driven graceful shutdown.
- **Protocols** — `protocol/{h2,h3,ws}` (HTTP/2 + HPACK, HTTP/3 + QPACK,
  WebSocket).
- **Middleware** (`middleware/`) — `rate_limit`, `slowloris`, `connection_limit`,
  `cors`, `acl`, `ip_filter`, `jwt_auth`, `basic_auth`, `auth_request`,
  `compress`, `security_headers`, `tailscale_auth`, `stick_table`, …
- **Reverse/forward proxy + L4** (`proxy/`, `l4/`), **CGI** (`cgi/`), **static
  files + autoindex** (`routing/`), **cache** (`cache/`), **sessions/cookies**,
  **ACME auto-TLS** (re-exported as `auto_tls`/`on_demand_tls`/`auto_https`),
  **a native HTTP client**, and a **JVM FFI bridge** (`ffi/`).
- A **premium-feature licensing layer** (`PremiumFeature`, `PremiumFeatureGuard`,
  the `EAP_BUILD_UNIX_TS` / `EAP_TTL_DAYS` atomics) — an EAP "timebomb" the CQ
  periodic job consults to decide whether to abort, plus per-feature gating
  (ReverseProxy / AutoHttps / Grpc / Tailscale / WebRtc / SocksProxy are
  "premium").

The crate carries an Elide proprietary copyright header. Per `ARCHITECTURE.md`,
the `net/` crates are ember's own work as research director at Elide, vendored
and used here by right; this was part of why DreggNet could not yet be open-sourced (the Elide net stack has since been ejected; DreggNet is AGPL-3.0). It
requires `#![feature(linkage)]` (nightly) and the `--cfg reqwest_unstable`
rustflag (set in `.cargo/config.toml`).

The performance story is real: the patched forks give it scatter-gather writes
(ntex `elide/scatter-gather-write`), zero-copy unbuffered plaintext TLS (rustls
`elide/zero-copy-plaintext`), and io_uring completion IO (compio fork). **None
of this is on the gateway's serving path** — see 1.2.

### 1.2 How the gateway actually uses it

The gateway's library handlers (`gateway/src/{http,hosting,webapp}.rs`) implement
`elidehttp::handler::Handler` and write responses through
`elidehttp::response::ResponseWriter`. But the **runnable server**
(`gateway/src/main.rs`) does **not** mount them in an httpe server. It:

1. Binds a `std::net::TcpListener` and spawns **one thread per connection**
   (`std::thread::spawn`), unbounded.
2. Hand-parses the request: reads to the `\r\n\r\n` header terminator, parses the
   request line, `Content-Length`, and `Host` with ad-hoc
   `String::from_utf8_lossy` scans (`parse_content_length`, `parse_header`).
3. Routes by `Host`: `<name>.example.com` → `SiteHostHandler`; the Caddy
   on-demand-TLS `ask` probe (`GET /internal/site-exists?domain=…`) → a
   site-existence check; everything else → the machines route table
   (`MachinesHandler::dispatch_async`, which blocks on a shared tokio runtime for
   the create→dispatch path).
4. Writes the response into a fixed `RESPONSE_BUF_BYTES = 256 KiB` buffer via the
   slice-backed `ResponseWriter`, writes it to the socket, and **closes** (no
   keep-alive).

So the **only** httpe surface the gateway depends on is the small value
vocabulary: `Method`, `StatusCode`, `ResponseWriter` (the `&mut [u8]` slice
variant), `Handler`, `Request`, `HandlerResult`, and `response::content_type`
constants. The route table, the lease gate, the site registry, and the TCP loop
are all DreggNet's own code. TLS, ACME, HTTP/2-3, compression, rate-limiting,
and connection limits are all handled **by Caddy at the edge**, not by httpe.

### 1.3 What builds vs what's excluded / the build ladder

- **Workspace members (green):** the full net closure is in the workspace —
  `net/httpe`, `transport`, `tailscale`, `wireguard`, `iocoreo`, `pki`, plus the
  vendored local Elide deps (`base bindings builder core dns foreign-gai macros
  native-dispatch nodeapi rpc sys jvm-stubs`). `ARCHITECTURE.md`'s "net crate
  status" table marks them all green.
- **`jvm-stubs`** force-links the JVM extern symbols so the engine links without a
  real JVM (`#[cfg(test)] extern crate jvm_stubs`); the JVM FFI is present but
  inert for DreggNet's use.
- **Excluded:** only `polyana` (its own Apache-2.0 workspace, referenced as a
  submodule, never absorbed).
- **`net/builder/build.rs`** skips the monorepo `make setup` / GraalVM gate
  (dev-ergonomics; nothing in the net stack links the GraalVM engine);
  `net/rpc/build.rs` resolves its capnp schema dir relative to the crate.
- The **service stack** (`dreggnet-cli/durable/exec/bridge/control/webapp/ops`,
  the `make build` set) is the always-green, cross-platform offline path and does
  **not** pull the httpe closure. `httpe` only enters the build through
  `dreggnet-gateway`. `ops` and `webauth` are explicitly noted as "pure-std HTTP,
  cross-builds trivially" — the gateway is the lone Linux-only service, *because
  of httpe*.

### 1.4 The cross-build constraint

The gateway is **Linux-only**: `net/nodeapi` (and parts of `net/transport`) use
Linux-only socket primitives (`SOCK_NONBLOCK`, io_uring). From macOS it is
cross-built with `cargo zigbuild --target x86_64-unknown-linux-gnu -p
dreggnet-gateway` (zig supplies the C cross-toolchain for
`aws-lc-rs`/`boringtun`/`zstd-sys`). On a native Linux host plain `cargo build`
works. **This constraint is inherited entirely from httpe** — none of the
gateway's own code (`std::net` + tokio + serde) needs Linux primitives.

### 1.5 The fork-dependency weight

The root `[patch.crates-io]` reconstitutes the Elide fork set (Cargo does not
inherit patches across path/git deps, so the bundled crates' `{ workspace = true
}` references must be satisfied here). The httpe-required forks:

| Fork | Pinning | Notes |
|---|---|---|
| `rustls` `elide/zero-copy-plaintext` | **branch** | zero-copy unbuffered plaintext, secret injection, 0-RTT |
| `ntex` + 15 sibling crates `elide/scatter-gather-write` | **branch** | scatter-gather write + `Bytes::from_owner` |
| `compio` ×11 (`compio-buf/driver/net/runtime/…`) | rev `6a97636…` | io_uring driver custom commit |
| `hickory-proto` / `hickory-resolver` `compio` | **branch** | DNS over the compio loop |
| `jni` rev `52526ed…`, `java_native`, `keygen-rs` `compio` | rev / branch | JVM bridge + licensing |

The reproducibility hazard: the **branch-pinned** git deps (rustls, the 16 ntex
crates, hickory) are **not reproducible** — the branch can advance, and any
lockfile regeneration (`cargo update`, a fresh `Cargo.lock`) pulls different
source. `Cargo.lock` pins exact commits, so *existing* checkouts build
reproducibly, but a lock refresh is a supply-chain landmine. The rev-pinned deps
(compio, jni) are stable. This is the maintenance reality of carrying a bundled
upstream engine: the closure is large, proprietary, nightly-only, and partly
pinned to moving branches.

### 1.6 The honest state summary

| Aspect | State |
|---|---|
| httpe as an engine | **Sophisticated and real** — but bundled, proprietary, nightly-only, Linux-only, with a moving-branch fork closure and an EAP timebomb |
| The gateway's use of httpe | **~6 thin types only**; the engine is linked but never started |
| The gateway's actual server | **Hand-rolled** `std::net` thread-per-connection loop — simple, correct at control-plane scale, but missing production hardening |
| TLS / ACME / H2 / rate-limit | **All at Caddy**, not httpe |
| Cross-build | Linux-only, **purely because of the httpe link** |

---

## 2. The tidy-up needs for production permissionless hosting

### 2.1 Robustness (the hand-rolled loop)

`serve_connection` (`gateway/src/main.rs`) has several gaps that matter on a
public surface, even behind Caddy:

- **No socket timeouts.** Neither the header-read loop nor the body-read loop
  sets `set_read_timeout`/`set_write_timeout`. A peer that opens a connection and
  dribbles bytes (or never finishes the body) **holds a thread forever** —
  classic slow-loris. `MAX_HEADER_BYTES` (64 KiB) bounds header *size* but not
  *time*.
- **No body-size cap.** `content_length` is trusted: the body `Vec` is grown up to
  the declared `Content-Length` with no ceiling. A large declared length drives
  unbounded read + allocation.
- **Unbounded connection concurrency.** Thread-per-connection with no cap, pool,
  or semaphore. Many simultaneous connections spawn unbounded threads — a trivial
  resource-exhaustion vector.
- **Response truncation bug (real correctness defect).** The slice-backed
  `ResponseWriter::body` writes `min(data.len, remaining)` and only emits a
  `tracing` warning (`"truncated write, buffer full"`) on overflow — which the
  gateway does not subscribe to. With a fixed `RESPONSE_BUF_BYTES = 256 KiB`, any
  static asset larger than ~256 KiB (minus headers) served through
  `SiteHostHandler` is **silently truncated**, while `Content-Length` still
  declares the full size — so the client hangs on a short read. For permissionless
  static hosting (images, JS bundles, full pages) this is a live data-corruption
  bug, not a theoretical one.
- **No chunked transfer-encoding handling.** Only `Content-Length` is read; a
  chunked request body is mis-read. Caddy normalizes to `Content-Length` when
  proxying, so the deployed path is safe, but a direct hit is brittle and silent.
- **Header re-parsing.** `parse_content_length` and `parse_header` each
  re-`from_utf8_lossy` and re-scan the whole header block; minor, but it is
  duplicated work and duplicated logic.
- **Errors go to `eprintln!` only** — no structured signal (see 2.7).

### 2.2 TLS / cert handling (the on-demand / wildcard flow)

TLS is **entirely Caddy's** (`deploy/staging/Caddyfile`): Caddy terminates TLS
and reverse-proxies plain HTTP to `gateway:8080`. For `*.example.com` it uses
**on-demand TLS** — a per-name Let's Encrypt cert minted over HTTP-01 on first
request, gated by the gateway's `GET /internal/site-exists?domain=…` `ask`
endpoint so only published sites mint certs (rate-limit hygiene). This is a clean
division of labor and the gateway's role (the `ask` endpoint) is solid.

Gaps for production permissionless hosting (ties to the permissionless-cloud
plan):

- **Per-name on-demand certs don't scale to a large or hostile site population.**
  Let's Encrypt rate limits (certs/registered-domain/week) bite when many sites
  are published, and an attacker who can publish names can drive issuance churn.
  The documented stronger option is a **DNS-01 wildcard** `*.example.com` (one
  cert, no per-name issuance) — deferred only because it needs a Caddy
  DNS-provider plugin + an API token for the `example.com` zone.
- **Custom user domains** (a user's own `example.com` → their site) are the real
  permissionless-hosting frontier; they require the on-demand path *plus* a
  domain-ownership check in the `ask` endpoint (today it only checks site
  existence, not who may bind which hostname).
- **The `/internal/site-exists` endpoint is unauthenticated** and reachable on
  `:8080` from anything that can reach the gateway. It is meant to be Caddy-only;
  it should be bound to the internal interface / firewalled, or documented as
  must-be-internal.

### 2.3 Routing / site resolution (scalability)

- Host-based site resolution (`SiteRegistry::resolve`, shared `Arc`) and the
  machines route table (`route::parse`) are clean and well-tested.
- **The site registry is loaded once at boot** from `/srv/sites`
  (`load_sites`). A new publish on disk is **not** visible until restart. The
  "a publish becomes visible immediately" property holds only for in-process
  `SiteRegistry::publish` calls, not the disk boot-load. Permissionless hosting at
  scale wants **live ingestion** (a publish API or a dir-watch) and the registry
  is **in-memory only** — all site assets are held in RAM, so memory grows with
  (site count × content size). That is the hosting scalability ceiling to name.

### 2.4 Performance

- The httpe zero-copy / scatter-gather / io_uring forks are **unused** by the
  gateway. The gateway's loop copies freely (Vec body, `from_utf8_lossy` header
  parse, a fresh 256 KiB response buffer per connection).
- **No keep-alive:** one request per TCP connection, then close. Caddy↔gateway
  re-establishes a connection per request, paying TCP + 256 KiB-alloc + loop
  setup each time. HTTP/1.1 persistent connections to Caddy would cut that.
- **No HTTP/2 or /3 to clients** — fine, Caddy speaks H2/H3 to the public; the
  Caddy↔gateway hop is H1 and that is the right altitude.
- Fine at control-plane / operator scale today; the per-connection 256 KiB
  allocation + thread-per-connection model is the ceiling if hosting traffic
  grows.

### 2.5 Cross-build

The gateway is Linux-only **only because it links httpe**. Its own code is
`std::net` + tokio + serde + the DreggNet service crates — all portable. If the
httpe dependency were reduced to the thin type vocabulary (owned natively), the
gateway would build and test natively on macOS like `ops`/`webauth`, and the
`cargo zigbuild` Linux-pin would become a deploy choice rather than a hard
constraint. Today the only path is the zigbuild cross-compile or a native-Linux
build.

### 2.6 Fork maintenance

As in 1.5: the branch-pinned forks (rustls, ntex ×16, hickory) are **not
reproducible across a lock refresh**. For a production service this is the
highest-leverage supply-chain fix: pin every `third-party` git dep by `rev=`
(not `branch=`) or vendor them, so a `cargo update` cannot silently change the
engine. The rev-pinned ones (compio, jni) already meet this bar. Separately, the
EAP timebomb + premium-feature gating live in the linked code; the gateway never
starts the CQ engine so they never arm, but they are a latent liability that
*decoupling removes entirely*.

### 2.7 Observability

The gateway has **essentially no per-request o11y**: errors go to `eprintln!`;
there is no request counter, status-code breakdown, latency histogram, byte
counter, or tracing span. DreggNet has a full Prometheus/Grafana stack
(`deploy/observability`, `docs/MONITORING.md`, node-metrics). `tracing` is
already in the httpe closure but the gateway emits nothing into it. For a public
surface this is a real gap — there is no way to see request rate, error rate, or
tail latency on the hosting/machines surface.

### 2.8 Production hardening (the public-internet surface)

- **No rate-limiting / per-IP caps** at the gateway for the public
  `*.example.com` surface. Caddy could add `rate_limit` (needs a plugin; not
  configured). The unbounded thread-per-connection model is the DoS vector (2.1).
- The operator surfaces (machines API, ops, grafana) are well-gated by the
  `webauth` dregg-capability `forward_auth` at Caddy — that part is solid. The
  **public hosting** surface is the unhardened one.

---

## 3. The cleanup / completion steps (prioritized)

Two tracks. **Track A (safe-autonomous-tonight)** is code cleanup, tests, and
hardening that does **not** change deployed public wire behavior — it only
rejects abusive/malformed traffic and fixes a latent corruption bug. **Track B
(reviewed-go)** changes public-facing behavior or the dependency surface and
wants ember's sign-off.

### Track A — safe autonomous tonight (hardening + cleanup + tests)

Ordered by dependency; all are confined to `gateway/src/main.rs` (+ small
shared-helper extraction) and tests.

1. **A1 — Fix the response-truncation bug (correctness, do first).**
   Detect when a handler's response would exceed `RESPONSE_BUF_BYTES` and grow
   the buffer to fit the actual response (size it from the resolved asset /
   serialized body), or stream the body to the socket in chunks. At minimum,
   never emit a `Content-Length` larger than the bytes actually written. Add a
   test: publish + serve a >256 KiB asset and assert a byte-identical round-trip.
   *Why first:* it is a live data-corruption bug on the hosting surface and is
   independent of everything else.

2. **A2 — Socket timeouts (slow-loris).** Set `set_read_timeout` +
   `set_write_timeout` on each accepted stream; treat a timeout as a clean close
   (optionally a `408`). Bound total header-read and body-read wall-time.
   Test: a dribbling/never-finishing client is dropped within the deadline.

3. **A3 — Body-size cap.** Reject `Content-Length` above a configurable max
   (default e.g. a few MiB for create bodies; a larger, separate cap for publish
   if publish ever moves onto this path) with `413 Payload Too Large` before
   reading the body. Test: oversized declared length → 413, no allocation blowup.

4. **A4 — Connection-concurrency cap.** Bound in-flight connection threads with a
   semaphore (or a fixed worker pool); excess connections wait or are rejected.
   Test: N+1 concurrent connections do not spawn unbounded threads.

5. **A5 — Explicit chunked handling.** Detect `Transfer-Encoding: chunked` and
   either decode it or reject with a clear `411`/`400`, instead of silently
   mis-reading. Test: a chunked body is handled deterministically.

6. **A6 — Per-request observability.** Add atomic counters (requests, errors, by
   status class, by surface: machines / hosting / ask) and a latency measure;
   expose them on `/status` (or a `/metrics` Prometheus endpoint) and add
   `tracing` spans around `serve_connection`. Additive, no behavior change.
   Wire into `docs/MONITORING.md` / the observability stack.

7. **A7 — Code cleanup.** Factor the duplicated `map_method` / `map_status` /
   `write` helpers shared between `hosting.rs` and `webapp.rs` into one place;
   collapse the duplicated header re-parse (`parse_content_length` +
   `parse_header` + `from_utf8_lossy`) into a single header-block parse pass.
   Document `/internal/site-exists` as internal-only (recommend binding/firewall).

### Track B — reviewed-go (changes public behavior or the dependency surface)

8. **B1 — Decouple the gateway from the httpe engine (the keystone).** Own the
   ~6 thin types (`Method`, `StatusCode`, `ResponseWriter`, `Handler`, `Request`,
   `HandlerResult`, `content_type`) in a small `gateway-http` module/crate and
   drop the `httpe` dependency from `dreggnet-gateway`. Payoff: removes the
   Linux-only constraint, the proprietary-engine + EAP-timebomb + premium-gating
   liability, and the heavy moving-branch fork closure from the gateway's build;
   the gateway becomes pure-std + tokio + serde and builds/tests natively on macOS
   like `ops`/`webauth`; build time drops sharply. Behavior-identical (the types
   are tiny and the server is already DreggNet's own), but it is a real
   dependency-surface change → ember reviews. *All of Track A is independent of
   this and survives the decouple unchanged.*

   *Counter-option to weigh, not recommended:* lean **into** httpe and actually
   run its CQ server (real H1/H2/H3, its `rate_limit`/`slowloris`/
   `connection_limit` middleware, its ACME). Rejected because Caddy already does
   TLS/ACME/H2/rate-limiting at the edge, several of those httpe features are
   "premium"/EAP-gated, and it deepens the proprietary + Linux-only + fork
   coupling rather than reducing it. If a future need arises (e.g. dropping
   Caddy), revisit — but that is a strategic decision, not a tidy-up.

9. **B2 — Keep-alive between Caddy and the gateway.** HTTP/1.1 persistent
   connections to cut per-request TCP + alloc cost. Changes the wire behavior;
   measure first.

10. **B3 — DNS-01 wildcard cert for `*.example.com`.** Replace on-demand per-name
    issuance with a single wildcard cert (Caddy DNS-provider plugin + a
    `example.com`-zone API token). Removes the Let's Encrypt rate-limit /
    issuance-churn exposure. A deploy/Caddy + secret change; ties to the
    permissionless-cloud plan. Keep the on-demand `ask` path for **custom user
    domains** and extend the `ask` to check domain-ownership, not just site
    existence.

11. **B4 — Live site-registry ingestion + memory ceiling.** A publish API or a
    dir-watch so a new site is served without a gateway restart, and a plan for
    the in-RAM asset ceiling (spill large/cold assets to the storage service /
    content-addressed store rather than holding every asset in memory). Changes
    the hosting data plane.

12. **B5 — Pin every `third-party` git dep by `rev=`.** Convert the
    branch-pinned forks (rustls, the 16 ntex crates, hickory) to exact `rev=`
    pins (or vendor them) so a lock refresh cannot silently change the engine.
    Touches the workspace `[patch]` set and may shift resolved code → re-lock
    deliberately and review. (Largely moot for the gateway *if B1 lands*, but
    still relevant to the rest of the `net/` stack — `transport`, `tailscale`,
    `wireguard`, `pki` — which keeps the closure.)

13. **B6 — Public-surface rate-limiting.** Per-IP / per-name request caps on the
    public `*.example.com` surface (Caddy `rate_limit` plugin at the edge, or a
    gateway-side limiter). Public behavior change.

### Dependency order (the through-line)

```
A1 (truncation fix)  ─┐
A2 (timeouts)         ├─ robustness floor, autonomous, all independent
A3 (body cap)         │
A4 (conn cap)         │
A5 (chunked)          │
A6 (o11y)             ├─ informs everything; autonomous
A7 (cleanup)          ─┘
        │
        ▼
B1 (decouple from httpe)   ← keystone; Track A survives it unchanged
        │
        ├─ B2 keep-alive          (perf, measure)
        ├─ B3 DNS-01 wildcard     (deploy + permissionless-cloud)
        ├─ B4 live ingestion      (hosting data plane)
        ├─ B5 rev-pin forks       (mostly the rest of net/ after B1)
        └─ B6 edge rate-limit     (public hardening)
```

The safe-autonomous-tonight subset is **A1–A7**: it fixes a live data-corruption
bug, closes the slow-loris / body-size / connection-exhaustion holes, adds the
missing observability, and tidies the duplicated helper code — all without
changing what a well-behaved client sees on the wire, and all surviving the
later `httpe` decouple (B1) untouched.
