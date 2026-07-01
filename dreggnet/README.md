# DreggNet — the verifiable agent cloud

DreggNet is the **operated service layer** that runs real agent workloads on real
metal and settles them against the public, formally-verified **dregg** substrate.
dregg says *what was promised, paid, and owed* — verifiably. DreggNet *delivers
it*: it schedules the workload, serves it, meters it, and bills for it, with every
charge traceable back to a signed, re-witnessable receipt.

This repository is **AGPL-3.0-only** (see `LICENSE`). It builds on the public
substrate at **`github.com/emberian/dregg`** (also AGPL-3.0); DreggNet depends on
dregg, and nothing in dregg depends on DreggNet (clean open-core hygiene).

## Honest status — read this first

DreggNet is an **early, real, multi-operator devnet**, not a turnkey production
cloud. What is true today, stated without overclaiming:

- **The serving layer is real and links zero proprietary code.** An earlier build
  vendored a proprietary `net/*` stack; it has been fully **ejected** (see
  `docs/ELIDE-NET-EJECTION.md`). The gateway runs on the owned, pure-`std`
  `dreggnet-http` vocabulary; the mesh runs on the owned `control::wg` engine over
  `boringtun` (Cloudflare, BSD-3-Clause). DreggNet now links **no** proprietary
  network code.
- **The service crates build and test** on macOS and Linux (`cli`, `exec`,
  `bridge`, `control`, `webapp`, `durable`, `gateway`, and friends). The
  `dreggnet-gateway` (a Fly-machines-compatible API server) builds and runs on
  Linux (the deploy target).
- **A dregg node runs, but is *silently unverified* on a fresh clone.** The
  verified, Lean-linked node needs a host-native Lean archive (the "seed"). Without
  it, `cargo build -p dregg-node` compiles **marshal-only** — it runs and commits
  turns, but with the un-verified Rust executor, not the verified producer. To get
  a genuinely verified node, build with `DREGG_REQUIRE_LEAN=1` (a fail-loud gate)
  and provide the Lean seed. See `docs/SELF-HOST-READINESS.md` for the exact trap
  and the recipe.
- **Finality is being hardened.** A small federation runs; sustained multi-node
  finality is under active hardening, not a settled guarantee.
- **The cloud is not one-command self-hostable, by design.** Provider backends
  (bare-metal/EC2 provisioning, the scheduler, settlement) reach live infrastructure
  behind their own operator config and credentials. The public tree ships those
  configs as **templates** (hostnames/IPs/keys are placeholders like `<EDGE_HOST>`,
  `<NODE_TAILNET_IP>`, `example.com` — fill your own).

The honest one-liner: **dregg's half is verifiable; DreggNet's half is the
operated, paid reality — and neither claim outruns the other.**

For the grounded maturity picture, read: `docs/SELF-HOST-READINESS.md`,
`docs/DEPLOY-READINESS.md`, `docs/CLOUD-PROVIDER-READINESS.md`, the `docs/FAKEOUTS-*.md`
(what looks done but isn't), and the `docs/TEST-RIGOR-*.md` (how thoroughly each
surface is actually tested).

## What composes here

- **the substrate dependency** — the verified ocap core (kernel, value layer,
  intent ring, Payable, the execution-*lease*) lives in the public `emberian/dregg`
  repo (AGPL-3.0). DreggNet path-/git-depends on it.
- **polyana** (`polyana/`, a git submodule → `akapug/polyana`, Apache-2.0; co-developed
  with an external contributor) — the real polyglot execution engine (many language families; sandbox
  tiers from `wasmtime`/`v8`/`graal` up to `native+seccomp+landlock`/`firecracker`;
  durable replay; capability gates at every boundary). It is a **separate
  workspace**, referenced never absorbed; it is **not vendored into this tree** —
  initialize it as a submodule to build the `polyana`-feature paths.
- **the serving + transport layer** — DreggNet-owned, AGPL-clean:
  - `http/` (`dreggnet-http`) — the clean-room, pure-`std` HTTP/1.1 value vocabulary.
  - `control/src/wg.rs` — the owned userspace WireGuard config/engine over `boringtun`.
  - `net/conformance-kit` — the DreggNet-authored conformance/perf kit (the only
    surviving crate under `net/`; self-contained, no proprietary code).
- **the bridge** (`bridge/`) — fulfills a dregg `execution-lease` by running the
  workload on polyana through the durable layer, metered and charged against the
  lease budget.
- **the control plane** (`control/`) — the orchestrator/provider/trust-rail:
  provisioning, scheduler + fleet lifecycle, settlement ledger, and the
  wireguard/tailscale mesh + node API.
- **the gateway** (`gateway/`) — the live product host: `dreggnet-gateway`, a
  runnable Fly-machines-compatible API server serving the route table + lease gate.

## The flow (an agent rents durable execution)

1. An agent opens a paid `execution-lease` on **dregg** (verified, settled via Payable).
2. **DreggNet** sees the funded lease and schedules a **polyana** workload on the
   fleet at the sandbox tier the cap-grade demands, networked over the mesh.
3. The workload runs durably (polyana checkpoint/replay); the agent's state is a
   passable, witnessed image.
4. Metering ticks the lease on dregg; payment settles through Payable. Non-payment
   lapses the lease and the container is reaped.
5. The agent reaches its workload through `dreggnet-gateway` over the mesh.

## Build & run (honest quickstart)

Prerequisites: the pinned Rust toolchain (`rust-toolchain.toml`), and the public
**dregg** substrate available where the manifests expect it. Some crates path-dep
a sibling checkout (`../breadstuffs` → the `emberian/dregg` clone); others git-dep
`emberian/dregg` directly. Clone the substrate alongside this repo, or adjust the
paths, before building.

```sh
# service crates (build + test on macOS/Linux):
cargo build -p dreggnet-cli -p dreggnet-gateway -p dreggnet-control

# the gateway is the deploy target (Linux):
cargo run -p dreggnet-gateway

# a local dregg node — NOTE: marshal-only (UNVERIFIED) without the Lean seed:
cargo build -p dregg-node
# for a genuinely verified node, provide the Lean seed and:
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release
```

The staging templates under `deploy/staging/` (docker-compose, Caddyfile, `.env.example`)
are the operator starting point — every hostname/IP/credential is a placeholder to
fill. See `docs/DEPLOY-READINESS.md` and `runbooks/` for the ordered plan.

## Layout

`docs/` is the working design + audit corpus (grounded status, critiques, plans).
`runbooks/` is the operator playbook set. `deploy/` holds the (templated) staging +
observability configs. The remaining top-level directories are the workspace crates
described above.

## License

AGPL-3.0-only. See `LICENSE`. Copyright (C) 2026 ember arlynx.
