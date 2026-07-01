# Early-era compute — running leases on DreggNet's own resources

This is the user-facing shape of DreggNet compute: how someone gets work executed
on the network, what hardware backs it today, and how it surfaces to them. It is
the product view of the machinery in `deploy/COMPUTE-BACKEND.md` (the backend) and
`control/src/mesh.rs` (the dispatch path).

The one-line model: **a user opens a funded lease; the control plane dispatches it
over the private overlay to a compute node; the node runs it as a real durable
metered workflow; the metered result comes back.** No node runs work the lease did
not authorize, and no result is claimed beyond what the lease budget paid for.

## What "early-era compute" means

Early-era = the offering is live but small, and budgets are generous. A user does
not bring their own cluster and does not pay per second up front: they get a
subsidized budget (free / generous initial allocation) and run real workloads on
hardware DreggNet already operates. The aim is to let people *actually run things*
on the network now, while the resource pool is one home box plus the edge — and to
have the same path scale cleanly as more hardware joins.

## How a user gets compute

1. **Open a lease.** A funded execution-lease names the lessee, the cap-grade (the
   isolation tier the work runs at — `sandboxed` / `caged` / `microvm`), the asset
   its budget is denominated in, the total `budget_units`, and the `per_period_units`
   charged per durable step. In the early era this lease is created with a
   subsidized budget (see *Budgets* below).
2. **Dispatch.** The control plane (`dreggnet-control`) decides which node runs it
   and reaches that node over the private overlay — it does **not** require the node
   to expose any public port. It establishes the link, health-checks the node, then
   issues a real `POST <overlay-addr>:8021/fulfill` carrying the lease
   (`dispatch_lease_over_mesh`, `control/src/mesh.rs`).
3. **Run.** The node's bridge agent (`deploy/node-agent`) runs the lease as a
   **real durable polyana workflow** (`dreggnet_bridge::fulfill`): each step runs in
   the polyana sandbox at the lease's tier, and a `MeterTick` charges
   `per_period_units` against the budget. Because the meter ticks are durable
   history, a crash resumes *within the same budget* — exactly-once metering, no
   double-charge.
4. **Meter back.** The metered result returns to the caller
   (`{ step1, step2, outputs, meter_units }`). If a tick would exceed the budget the
   workflow fails and the lease lapses — surfaced as a lapse the scheduler reaps, with
   no fabricated result.

The budget gate is the whole safety story: an unfunded lease starts no workflow, an
over-budget tick stops the workflow, and the dispatch path maps a refusal
(`HTTP 4xx` from the agent) to a `WorkloadLapsed` rather than inventing output.

## The resource pool

| node | role | capacity | cost |
| --- | --- | --- | --- |
| **node-a** (primary) | home Linux box, runs the bridge agent + polyana | a multi-core Linux box | ~free at the margin (home power, owned hardware) |
| **edge** (AWS, `<EDGE_HOST>`) | thin door: stable IP, TLS, headscale mesh control + DERP, orchestration front | one small always-on t3-class box | the only recurring cloud spend; does not grow with load |
| **homelab** (later) | additional compute backends — BIG machines | lots of CPU / RAM / disk | ~free at the margin (owned hardware) |

The economic point is that cloud spend is pinned to one small edge box, and
everything that scales with load — lease execution and STARK proving — runs on
hardware that is already owned. node-a is the engine room; the edge is a thin
door.

## How it surfaces

- **The Fly-compatible machines API** (`gateway/`): a `POST .../machines` create
  maps to a lease, runs it through the bridge's real validation gate
  (`workflow_input_for_lease`), and — when the gateway is dispatch-configured
  (`DREGGNET_DISPATCH=tailscale`, the live edge default) — **dispatches that lease
  over the overlay to the compute node** (`dispatch_lease_over_mesh` → node-a's
  `:8021/fulfill`) so the created machine RUNS a real durable metered workload. The
  machine record reflects the outcome: `started` with the real `meter_units` + step
  outputs under a `dregg` field, or `failed` with the lapse reason (an over-budget /
  refused lease — no work claimed). Without dispatch configured the create fulfills
  the lease in-process (single-box / dev). The gateway root (`GET /`) is a friendly
  status landing page (name · machine count · federation health · portal pointer);
  `GET /status` / `GET /healthz` are its JSON forms. This is the programmatic front.
- **The Discord bot** (`breadstuffs/discord-bot`, deployed as
  `dreggnet-discord-bot`): the community front door. A user opens a lease and runs
  work from Discord; the command maps to the same lease→dispatch→run→meter flow and
  the metered result comes back in-channel. It is wired and token-gated (live the
  moment a real `DISCORD_TOKEN` is set — see `deploy/staging/MINI-DEVNET.md`).
- **The portal / CLI** (`cli/`, `webapp/`): the same lease vocabulary
  (`dreggnet-control` re-exports `Lease` / `CapGrade` / `DurableOutput`) drives a
  lease and reads back its metered result.

Whatever the surface, the lease/run flow lands on **real node-a compute** over the
overlay — the same `:8021/fulfill` contract end to end.

## Budgets (early era)

Early-era leases are created with generous / free initial budgets so people can run
real work without friction. The budget is still a real meter: it bounds and meters
the run (so a runaway workload lapses rather than consuming the box), it is just
subsidized rather than billed. As the offering matures, the same `budget_units` /
`per_period_units` become the billing knob without any change to the execution path.

## The scale path — node-a now, homelab later

The dispatch path is backend-agnostic in exactly the way that makes scaling a
matter of adding nodes, not rewriting the plane:

- **Now:** one compute backend — node-a at `100.64.0.2:8021` on the headscale
  overlay, the edge at `100.64.0.1`. The control plane dispatches to it over the
  tailnet (`TailscaleMesh`, `control/src/mesh.rs`).
- **Later (homelab):** each homelab machine — the BIG-CHUNGUS boxes, lots of
  RAM/CPU/disk — joins the same headscale overlay (`deploy/FABRIC-JOIN.md`) and runs
  the **same** `node-agent` on `:8021`. It registers a mesh node; the control
  plane gains another `MeshNode` to dispatch to. Nothing about the lease, the
  `/fulfill` contract, or the metering changes — a new backend is one more overlay
  address speaking the same protocol.
- The scheduler picks among nodes by cap-tier / size / load; the heavy, scale-with-
  load work (lease execution, STARK proving) fans out across the home/homelab fleet
  while the edge stays a thin, fixed-cost door.

## Live status (2026-06-28)

- **Dispatch path closed + proven through the control plane.**
  `dispatch_lease_over_mesh` issues the real `POST /fulfill` (it no longer returns
  an `Unimplemented` plan). Backends: `TailscaleMesh` (the live overlay backend the
  edge↔node-a deploy uses), `WireguardMesh` (Linux, self-managed tunnel), and
  `StubMesh` (tests / macOS dev host).
- **Proven live, edge→node-a, via the control plane (not raw curl):** from the
  edge (`100.64.0.1`), a funded lease dispatched through `dreggnet-control` over the
  headscale overlay ran on node-a's cores and returned the metered result
  (`step1=42, step2=84, meter_units=2`); an under-budget lease came back as a lapse
  (`HTTP 402` → `WorkloadLapsed`), no work claimed. (Driven with the
  `dispatch_over_tailscale` example built for `x86_64-unknown-linux-gnu`, run on the
  edge against `100.64.0.2:8021`.)
- **Remaining drive steps (named):** wire the gateway/Discord-bot/portal create
  flow to call `dispatch_lease_over_mesh` for the chosen node (the dispatch primitive
  is ready; the surfaces still run leases via the in-process / gateway path); and
  register homelab nodes as additional `MeshNode` backends when that hardware joins.
