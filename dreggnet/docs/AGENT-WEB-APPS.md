# Agent-served web apps

DreggNet's headline vision is **fully agentic web-facing apps**: an agent
autonomously assembles a web API and DreggNet runs + serves it. An agent
declares a set of HTTP routes, each bound to a sandbox workload handler;
DreggNet routes each inbound request to its handler, **runs the handler on the
owned wasmi sandbox** under a dregg execution-lease, and serves the response.

This is the `dreggnet-webapp` crate.

```
   agent assembles                 DreggNet runs + serves
   ───────────────                 ──────────────────────
   WebApp { routes: [              inbound HTTP ─▶ Router::serve
     GET /add   ─▶ handler,                          │ match the route
     GET /hello ─▶ handler,                          │ Handler::build_source
   ] }                                               ▼
                                    dreggnet_exec::run_workload  (owned wasmi sandbox)
                                                     │ Output { values }
                                                     ▼
                                    ResponseSpec::render ─▶ WebResponse
```

## Declaring an app

A `WebApp` is plain `serde` data — an agent can produce it as a JSON document or
with the `assemble` builders. A route binds a method + exact path to a `Handler`
(a sandbox workload) and a `ResponseSpec` (how to render the handler's result).

A handler is either:

- **static** — a fixed WAT module exporting `run` (a constant or a fixed
  computation), or
- **templated** — a WAT module with `{{param}}` placeholders filled from the
  request query. Each placeholder value is **validated as an integer** before
  substitution, so a templated handler cannot be turned into a WAT-injection
  vector by a crafted query value.

The two bundled demo handlers (`assemble::demo_app`):

| route | handler | proof |
|---|---|---|
| `GET /hello` | static: computes `21 * 2` in the wasm sandbox | greets with the sandbox-computed value |
| `GET /add?a=&b=` | templated: `i64.add` of `a` + `b` in the sandbox | returns `{"result": a+b}` |

## Serving it

### Portable (any host): `dreggnet-serve`

A std-sockets serving binary that serves an assembled app over HTTP on any
platform (the wasm tiers run on macOS + Linux):

```sh
dreggnet-serve --port 8787
curl -s localhost:8787/hello
#   hello from an agent-served endpoint — the owned wasmi sandbox computed 42
curl -s 'localhost:8787/add?a=40&b=2'
#   {"result":42}          (the addition genuinely runs in the wasm sandbox)
```

With `--lease-budget N`, the app is served through a `LeasedRouter` metered
against a funded dregg execution-lease (1 unit/request). Once the budget is
spent, further requests get `402 Payment Required` — the handler never runs, so
no unpaid work is served:

```sh
dreggnet-serve --port 8787 --lease-budget 2
# two requests served, the third:
#   {"error":"execution-lease exhausted: request charge 1 would reach 3 > budget 2"}
```

### The fly gateway (Linux): `dreggnet-gateway`

The Linux-only `httpe` gateway adopts the same `Router` via
`gateway::WebAppHandler` (`gateway/src/webapp.rs`), so a served app's data-plane
traffic is routed to its sandbox handlers through the production gateway. The
fly-machines API (`MachinesHandler`) is the control plane; `WebAppHandler` is
the data plane.

## Metering against a lease

`LeasedRouter` meters each served request against a funded dregg `Lease`,
validated through the bridge's **real** gate
(`dreggnet_bridge::workflow_input_for_lease`) when the router is built. The
charge is gated **before** the handler runs — the same "no work beyond what the
lease authorizes" invariant the durable bridge enforces per step, here enforced
per request.

## What is real vs. a later rung (honest)

- **Real:** an agent declares a `WebApp` (data); `Router::serve` matches a
  request, builds the handler's concrete workload (filling templated params,
  integer-validated), runs it on the owned wasmi sandbox, and renders the response; the metered
  `LeasedRouter`; the portable `dreggnet-serve` HTTP server; the gateway
  `WebAppHandler` (cross-compiles for Linux).
- **Path patterns** — routes match an *exact* path; `/users/{id}` params are a
  later rung. Per-request inputs reach a handler via the query string.
- **Request body → handler** — the handler entrypoint is the sandbox's zero-arg
  `run`; request data reaches the handler via templated query params, not the
  body. A richer handler ABI (request bytes in, response bytes out) waits on an
  owned-sandbox host-import shape for it.
- **Per-request durability** — `LeasedRouter` meters over the real `Lease` gate
  but runs each request through the direct exec path, not a full durable
  per-request `dreggnet_durable` workflow (crash-resume of an in-flight
  request). That is the next rung — it reuses `dreggnet_durable` once that
  orchestration accepts an arbitrary handler spec.
