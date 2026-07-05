# Running DreggNet locally (Docker, incl. on a Mac)

DreggNet is a Linux serving stack (the `net/` gateway uses epoll/io_uring; parts
of `durable`/`exec` compile and run only on Linux). The way to run and demo it on
a macOS host is Docker Desktop — the container is Linux, so the Linux-only path
runs unchanged.

This runbook brings up the runnable demo on any machine with Docker.

## What runs today

| Piece | Status | Notes |
|---|---|---|
| `dregg-cloud` CLI (operator face) | **runs** | the wasmi-tier exec demo path: drives control → bridge → durable → exec → the owned wasmi sandbox; genuinely runs a metered, durable, sandboxed workload |
| owned wasmi sandbox (`Sandboxed` tier) | **runs** | the `add(40,2)=42` / `*2=84` workflow executes in the owned pure-Rust `wasmi` interpreter (provider `dreggnet-wasmi`, zero `unsafe`, in-crate). Every stronger tier (JIT/`Caged`/`MicroVm`/GPU) is an honest fail-closed seam (`ExecError::TierNotServed` / `NotWired`) — never a fake run, never a silent downgrade |
| `postgres` | **runs** | the durable `pg` store + meter outbox boundary; where `pg-dregg` composes the lease/meter/checkpoint in one txn |
| durable store (bundled SQLite) | **runs** | the default CLI demo path; crash-exact resume over an on-disk DB |
| durable `pg` store | **opt-in** | same workflow, Postgres-backed checkpoints; its resume test is `DATABASE_URL`-gated |
| `dreggnet-gateway` (httpe machines API) | **runs** | a serving binary binds :8080 and serves the fly-compatible machines API; see "The gateway" below |

## Prerequisites

- Docker Desktop (or any Docker Engine) with Compose v2.
- A plain checkout of the repository — nothing to init. Compute is **owned and
  in-crate**: the `exec` crate depends on the pure-Rust `wasmi` interpreter from
  crates.io (no external submodule, no path-dep to fetch).

## Bring it up

```sh
docker compose up -d --build      # postgres + the dreggnet container
docker compose ps                 # both healthy/running
```

The first build is heavy: it installs the pinned nightly toolchain
(`nightly-2026-03-24`), compiles the owned wasmi sandbox and the durable
stack, and vendors OpenSSL from source. BuildKit cache mounts make rebuilds fast.

## The end-to-end demo (one command)

```sh
docker compose run --rm dreggnet dreggnet-demo
```

This opens a funded lease, runs a metered durable sandboxed workload, and prints
the lifecycle + meter. Expected output includes:

```
==> dregg-cloud lease open --cap-tier sandboxed --budget 100
lease opened: <id>

==> dregg-cloud run --lease <id> --lang wat --source workload.wat
... add(40, 2) = 42 ...
... *2 = 84 ...

==> dregg-cloud status
... running/completed + meter ...
```

## Driving the CLI yourself

The `dreggnet` container idles (the operator CLI is not a daemon), so exec into it:

```sh
# 1) open + fund a (mock) execution-lease
docker compose exec dreggnet \
  dregg-cloud lease open --cap-tier sandboxed --budget 100
# -> "lease opened: <LEASE_ID>"

# 2) declare a trivial WAT workload and run it as a metered durable workflow
docker compose exec dreggnet sh -c \
  'printf "(module (func (export \"run\") (result i32) (i32.const 42)))\n" > /var/lib/dreggnet/w.wat'
docker compose exec dreggnet \
  dregg-cloud run --lease <LEASE_ID> --lang wat --source /var/lib/dreggnet/w.wat

# 3) see the lifecycle + meter
docker compose exec dreggnet dregg-cloud status
```

An over-budget lease (e.g. `--budget 1` against a multi-step workflow) lapses
mid-fulfillment and is auto-reaped — no machine is left running for unpayable
work. That is the bridge's honest invariant.

## Postgres

The `postgres` service is wired and reachable:

```sh
docker compose exec postgres psql -U dreggnet -d dreggnet -c '\l'
# or from the host (port 5432 is published):
#   psql postgres://dreggnet:dreggnet@localhost:5432/dreggnet -c 'select 1'
```

`DATABASE_URL=postgres://dreggnet:dreggnet@postgres:5432/dreggnet` is exported
into the `dreggnet` container. The **default** CLI demo uses the bundled SQLite
durable store and does not need Postgres; Postgres is the multi-host durability
boundary and the place the `pg`-gated durable resume test runs. To exercise it,
build/run the durable crate with the `pg` feature against this `DATABASE_URL`
from a cargo-capable environment (the build stage, or the host via
`cargo zigbuild`):

```sh
DATABASE_URL=postgres://dreggnet:dreggnet@localhost:5432/dreggnet \
  cargo test -p dreggnet-durable --features pg -- --ignored
```

## The gateway — the fly-compatible machines API (`dreggnet-gateway`)

The fly.io-compatible **machines API** is a running service. The
`dreggnet-gateway` binary binds a TCP listener (`--port`, default `8080`) and
serves the `MachinesHandler` route table over a small HTTP/1.1 loop: each
request's line + headers + body are read off the socket, dispatched through the
**real** route table + the bridge's lease-gate, and a fly-shaped JSON response
written back.

Bring it up (its own compose service; the build pulls the heavy Linux-only Elide
`net/` closure — forked ntex/compio/rustls + capnp codegen — so the first build
is slow):

```sh
docker compose up -d --build dreggnet-gateway
docker compose ps                 # the gateway is running, :8080 published
```

Then drive it with `curl` from the host:

```sh
# create a machine (the body is decoded for real; the lease runs through the
# bridge's real gate before any machine is recorded)
curl -s -X POST http://localhost:8080/v1/apps/demo/machines \
  -H 'content-type: application/json' \
  -d '{"name":"w1","config":{"guest":{"cpus":1,"memory_mb":256}}}'
# -> {"id":"...","name":"w1","state":"created",...}

# list machines for the app
curl -s http://localhost:8080/v1/apps/demo/machines

# status of one machine (use the id from create)
curl -s http://localhost:8080/v1/apps/demo/machines/<ID>

# stop / start / destroy
curl -s -X POST   http://localhost:8080/v1/apps/demo/machines/<ID>/stop
curl -s -X POST   http://localhost:8080/v1/apps/demo/machines/<ID>/start
curl -s -X DELETE http://localhost:8080/v1/apps/demo/machines/<ID>
```

### What is live vs. deferred

- **Live + real:** `create`, `list`, `status`, `stop`, `start`, `delete`. A
  `create` decodes the JSON body, maps it onto a dregg execution-lease, and runs
  it through the bridge's **real** validation gate
  (`dreggnet_bridge::workflow_input_for_lease`) before recording the machine. A
  lease the bridge refuses (unfunded / ill-formed / grade-below-floor) yields a
  4xx and **no** machine record — no unpaid work is provisioned.
- **Deferred (the create→fulfill seam):** `create` *admits* the machine (records
  it as `created`), mirroring fly's create→start split. The durable launch is
  `MachineGateway::fulfill` (the real `dreggnet_bridge::fulfill`), which is
  `async`; the `httpe` `Handler` surface this server speaks is synchronous, so
  the durable workload launch is driven by a control loop, not the request path.
  The lifecycle endpoints transition the record today.

You can also run the binary directly from a cargo-capable Linux environment (or
cross-build it from macOS):

```sh
cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-gateway   # lib + bin
# on Linux:
dreggnet-gateway --port 8080
```

## Tearing down

```sh
docker compose down            # stop + remove containers
docker compose down -v         # also drop the postgres + state volumes
```
