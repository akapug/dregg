# Testing DreggNet — one command

A developer or operator validates the whole repo with one command:

```sh
make test
```

This runs the **default offline-green gauntlet**: no network, no Postgres, no live
node, no AWS. The env-gated lanes (Postgres, a live dregg node, the Linux network
stack) are reported as **SKIPPED** — never failed — when their prerequisites are
absent. `make test` is a thin entry over `scripts/test.sh`.

The toolchain is pinned by `rust-toolchain.toml` (`nightly-2026-03-24`, edition
2024) — `rustup` selects it automatically.

## Targets

| Target | What it runs |
|---|---|
| `make test` | the full gauntlet — the service stack (unit + integration + e2e) plus any gated lane whose env is present |
| `make test-fast` | the quick unit subset — `cargo test --lib` on the service crates (no integration/e2e) |
| `make lint` | `cargo fmt --all -- --check` (hard gate) + `cargo clippy … -D warnings` (advisory) |
| `make build` | build the service stack + its binaries (macOS/Linux portable) |
| `make test-pg` | the Postgres durable-resume lane (gated — needs `DATABASE_URL`) |
| `make test-verify` | the verified on-chain read lane (gated — needs `DREGGNET_LIVE_NODE`, AGPL `dregg-verify`) |
| `make test-net` | the Linux gateway + `net/` stack (Linux only) |
| `make build-gateway` | cross-build the Linux-only `httpe` gateway from any host (`cargo-zigbuild`) |
| `make help` | list targets |

## The default offline path (what `make test` always runs)

The **service stack** — the crates that build and test on both macOS and Linux:

```
dreggnet-cli  dreggnet-durable  dreggnet-exec  dreggnet-bridge
dreggnet-control  dreggnet-webapp  dreggnet-ops
```

These carry the e2e / integration suites: the CLI demo end-to-end (`cli/tests/e2e.rs`),
the autonomous orchestration loop (`control/tests/{orchestration_loop,go_real_loop}.rs`),
durable crash-resume on the bundled SQLite store (`durable/tests/durable_resume.rs`),
the lease→durable workflow and the lease watcher
(`bridge/tests/{lease_drives_durable_workflow,lease_watcher}.rs`), and the static-site
publish→serve round-trip + durable-request resume
(`webapp/tests/{site_publish_serve,durable_request_resume,durable_request_real_restart}.rs`).

`dreggnet-exec` runs the owned, vendored pure-Rust `wasmi` sandbox for the `Sandboxed`
wasm tier — it genuinely executes everywhere (zero `unsafe`, no external submodule; the
`add(40,2)=42` dogfood runs here). Every stronger tier — `JitSandboxed`/JIT, `Caged`/native,
`MicroVm`/Firecracker, `Gpu`, and the python/node interpreter langs — is an honest,
fail-closed seam today (`ExecError::NotWired` / `TierNotServed`): never a fake run, never a
silent downgrade. Wiring an owned engine for each stronger tier is future work — see
`docs/COMPUTE-TIERS.md`.

This is the same crate set CI tests on its macOS service-stack job (`.github/workflows/ci.yml`).

## The gated lanes (opt-in, skipped cleanly by default)

Each lane needs an external resource. `scripts/test.sh` detects the env var and
either runs the lane or prints a one-line SKIP telling you how to enable it.

### Postgres durable resume — `make test-pg`

Three `#[ignore]` tests in `durable/tests/durable_resume_pg.rs` exercise the
Postgres-backed durable store (exactly-once meter outbox across a crash, the
over-budget pre-charge failure, per-(lease,period) idempotency). Needs the `pg`
feature and a live Postgres:

```sh
DATABASE_URL=postgres://dreggnet:dreggnet@localhost:5432/dreggnet make test-pg
```

`docker compose up -d postgres` (see `docs/RUN-LOCALLY.md`) stands one up locally.

### Verified on-chain read — `make test-verify`

`bridge/tests/verified_read_live.rs` reads funded execution-leases from a live
dregg node's receipt log and asserts a tamper is rejected. It needs the
**off-by-default `dregg-verify` feature** (turning it on makes the build a
derivative of AGPL-3.0 dregg code — the deliberate flip-on step;
`docs/ORCHESTRATION-LOOP.md`, `bridge/Cargo.toml`) and a reachable node:

```sh
DREGGNET_LIVE_NODE=127.0.0.1:18420 make test-verify
```

### The Linux gateway + net stack — `make test-net`

The `httpe` gateway and the `net/` stack (transport, tailscale, wireguard, dns,
pki — the vendored Elide closure) use Linux io_uring/epoll and Linux-only socket
primitives, so they build and test on **Linux only**. CI builds the gateway on its
Linux job (`cargo build -p httpe -p dreggnet-gateway`). From a macOS dev box,
cross-build the gateway with `make build-gateway` (`cargo-zigbuild`).

Some net tests have their own further gates: the Tailscale e2e
(`HEADSCALE_URL` / `TS_AUTH_KEY` / `E2E_SCENARIO`) skips silently without a live
Headscale; the `dns` integration tests are `#[ignore]` (network-dependent); the
loom model-checking tests want `--test-threads=1`.

### Solana / AWS

The Solana bridge is devnet/oracle-attested (no default test reaches devnet), and
the `ec2` provider backend needs real AWS credentials (`docs/SELF-HOST.md`) — both
are configured + buildable offline; exercising them live is a deploy-lane step,
not part of `make test`.

## CI

`.github/workflows/ci.yml` runs four jobs on the pinned toolchain: **service-stack**
(`cargo test` over the seven service crates, macOS), **gateway-linux**
(`cargo build -p httpe -p dreggnet-gateway`, Linux), **fmt** (`cargo fmt --all --
--check`, a hard gate), and **clippy** (`-D warnings`, advisory /
continue-on-error). `make test` + `make lint` reproduce the testable part locally.

## What "green" means

`make test` exits non-zero only if the default offline path fails. A skipped gated
lane is reported but does not fail the run — it is gated, not broken. To validate a
gated lane, provide its env and run its target.
