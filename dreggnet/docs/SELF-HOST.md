# Self-hosting a DreggNet provider

DreggNet is **not a monolith**. The substrate (dregg: the execution-lease cell,
the meter, the `Payable` settlement rail) is open and verifiable; the *operated
infrastructure* — the machines that actually run durable workloads — is the
product, and **anyone can operate it**. You run your own provider against your
own dregg cells, your own machines, and your own gateway. Federated providers,
one open lease/meter/pay protocol between them: the moat is the network, not the
code.

This guide is the unit a stranger runs to host their own provider:
`dreggnet-provider` (a binary in `dreggnet-control`) plus a `ProviderConfig`.

```
   your dregg cells          your machines              your ingress
   ───────────────           ─────────────              ────────────
   funded execution-leases ─▶ dreggnet-provider ────────▶ dreggnet-gateway
     (a dregg node, or         (LocalProvider /             (the fly-machines API)
      mock for dev)             Ec2Provider)         ─────▶ dreggnet-serve
                                  │                          (agent-served web apps)
                                  ▼
                                the bridge → durable polyana workload, metered
```

## What a provider is

A provider is a [`VmProvider`](../control/src/provider.rs): it rents machines,
places a funded lease on one, runs the lease as a durable, metered polyana
workload (via the bridge), and reaps the machine when the lease lapses. Two
backends ship today:

| backend | what it is | status |
|---|---|---|
| `local` | runs workloads in-process on **this** host via the bridge | real, end-to-end |
| `ec2`   | rents AWS EC2 instances (shells the `aws` CLI) | real argv + JSON parse; needs AWS creds |

There is deliberately **no Hetzner provider** — your fleet is your choice.

## The config

`dreggnet-provider` is configured by a TOML file (`--config path`) overlaid with
`DREGGNET_*` environment variables. Every field has a default, so an empty
config is a valid (mock-cells, local-backend) provider.

```toml
# dreggnet-provider.toml — see docs/dreggnet-provider.example.toml
name         = "my-provider"     # the lease-owner / EC2 tag
region       = "home-lab"        # the placement region tag
asset        = "USD"             # the asset leases are denominated in
gateway_bind = "0.0.0.0:8080"    # where this provider's gateway binds

[cells]                          # WHERE funded execution-leases are read from
kind = "mock"                    # in-process leases (dev; no node needed)
# kind     = "dregg_node"        # or: read leases from a dregg node's receipt log
# node_url = "https://my-node:9090"

[backend]                        # WHAT machines this provider rents
kind = "local"                   # run workloads in-process via the bridge
# kind   = "ec2"                 # or: rent AWS EC2 instances
# ami_id = "ami-0abc…"
# owner  = "me"
```

### Environment overrides

A deployment can be configured without editing a file:

| env var | overrides |
|---|---|
| `DREGGNET_NAME` | the provider name |
| `DREGGNET_REGION` | the placement region |
| `DREGGNET_GATEWAY_BIND` | the gateway bind address |
| `DREGGNET_ASSET` | the lease asset tag |
| `DREGGNET_NODE_URL` | flips `cells` to a live dregg node at this URL |
| `DREGGNET_BACKEND` | `local` or `ec2` (EC2 also reads `DREGGNET_EC2_AMI`) |

## Run it

```sh
# default: mock cells, local backend — runs a demo lease end-to-end on this host
dreggnet-provider

# your config
dreggnet-provider --config dreggnet-provider.toml

# env-only (no file): read leases from your node, place in your region
DREGGNET_NODE_URL=https://my-node:9090 DREGGNET_REGION=home-lab dreggnet-provider
```

With a **local** backend and **mock** cells, the entrypoint runs a demo lease
through the provider to prove the wiring on your host — it provisions a machine,
runs the metered durable polyana workload (`add(40,2)=42`, `*2=84`), and reaps:

```
dreggnet-provider: resolved plan
  name         : dreggnet-provider
  region       : local
  cells        : mock (in-process leases)
  backend      : local
dreggnet-provider: built `local` provider
  provisioned machine <id> (local)
  workload completed on polyana: step1=42 step2=84 meter_units=2
  reaped machine <id>
dreggnet-provider: demo OK — the configured provider ran a metered, sandboxed workload.
```

With a real backend (EC2) or a real cells source (a dregg node), it resolves the
plan and stops at the deployment step rather than spending money or requiring a
live node.

## Reading leases from your own dregg cells (the `dregg-verify` lane)

`cells.kind = "dregg_node"` points the provider at a dregg node's receipt log.
The decode — funded execution-lease grants → `Lease` (lessee / cap-grade /
budget) — is real and lives in `dreggnet_bridge::dregg_verify`
(`DreggNodeFeed`), behind the bridge's off-by-default `dregg-verify` feature.

That feature is off by default for a license reason: pulling in the dregg tree
(AGPL-3.0-or-later) is what makes a build a derivative work, so the default
build stays AGPL-clean with zero dregg git in the lock. Flipping it on is the
documented two-part step in `bridge/Cargo.toml` (the local dep + a root
`[patch.crates-io]` reconciliation). The **named next step** is the live
light-client RPC that fetches the log records the decode consumes.

## Serving (the gateway + agent-served web apps)

A provider's ingress is two surfaces, both over the (Linux-only) `httpe`
gateway or the portable `dreggnet-serve` binary:

- **The fly-machines API** (`dreggnet-gateway`) — the control plane: create /
  inspect / reap durable workloads. See `docs/RUN-LOCALLY.md`.
- **Agent-served web apps** (`dreggnet-webapp`) — the data plane: an agent
  declares HTTP routes bound to polyana handlers, and the provider runs each
  inbound request's handler on polyana and serves the response. See
  `docs/AGENT-WEB-APPS.md`.

## What is real vs. the named next step

- **Real:** the `ProviderConfig` (file + env), `build_provider()` for both
  backends, the `local` end-to-end demo (provision → metered durable polyana
  workload → reap), the `ec2` argv + JSON parse.
- **Named next step:** the live lease-watch run loop against a real dregg node
  (the `dregg-verify` light-client RPC), and EC2 provisioning against real AWS
  credentials. The provider is configured + buildable for both today; wiring the
  live loop is the deployment rung.
