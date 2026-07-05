# GO-REAL — the live verified orchestration loop

DreggNet's control plane runs as a real daemon (`dreggnet-provider`) that reads
funded execution-leases off a live dregg node, dispatches them onto a compute
fleet, meters the work, and settles each metered period as a real conserving
`Transfer` turn back to the node. This note is what the daemon does when pointed
at a real node, the trust model of its lease read, and the one operator step the
live edge proof needs.

## Running the daemon against a node

A `dregg_node` cells source switches the daemon from the offline demo to the real
loop:

```sh
# Light-client-VERIFIED read (links the dregg verified core; AGPL — operator infra):
DREGGNET_NODE_URL=http://my-node:8420 \
DREGGNET_NODE_BEARER=<operator-bearer-from-unlock> \
DREGGNET_COMPUTE_NAME=node-a DREGGNET_COMPUTE_ADDR=100.64.0.2 \
DREGGNET_COMPUTE_PAYABLE=<64-hex-cell-id> \
  cargo run -p dreggnet-control --features dregg-verify --bin dreggnet-provider
```

or in `dreggnet-provider.toml`:

```toml
[cells]
kind = "dregg_node"
node_url = "http://my-node:8420"

[[compute]]
name = "node-a"
overlay_addr = "100.64.0.2"
agent_port = 8021
payable_cell = "0707…07"      # 64-hex cell id the metered work settles into
capacity = 4

# Optional: pin the verified read's trusted root to a finalized checkpoint.
[trusted_root]
height = 1024                  # the finalized checkpoint height
len = 5120                     # the root-pinned receipt-log length at that checkpoint
mmr_root = "1913…56"          # the finalized checkpoint's committed receipt-index MMR root
min_qc_votes = 3              # the federation quorum size that makes it finalized
```

When `DreggNode` is configured the daemon constructs the real seams and runs
`Orchestrator::run_until_shutdown` on them (ctrl-c to stop):

- **lease read** — `VerifiedNodeLeaseSource` (feature `dregg-verify`): a
  light-client-verified on-chain read. Without the feature it falls back to
  `NodeApiLeaseSource` (the node's cell API, trusted), so the binary builds and
  runs either way; the feature is the verified upgrade.
- **settlement** — `NodeApiSettlement`: one conserving `Effect::Transfer` per
  metered period, lessee cell → the backend's payable cell, exactly-once per
  `(lease, period)`, submitted to `POST /api/turns/submit`.
- **compute fleet** — the `[[compute]]` backends, dispatched over the mesh.

The mock demo stays behind the default `mock` cells + `local` backend.

## The verified read (light-client unfoolable, fail-closed)

`bridge/src/dregg_verify.rs` verifies the node's receipt log before any lease is
trusted:

- `verified_leases_from_range` — a single whole-log range with its non-omission
  certificate, verified against the trusted root and row-recomputed (fail-closed).
- `verified_leases_windowed` — the **long-chain** read: the node caps one
  `/api/receipts/index/range` at 1024 rows, so a longer log is read as contiguous
  windows that TILE `[0, len-1]`. Each window's non-omission certificate verifies
  against the same whole-log MMR root; the windows must be gap-free and reach the
  root-pinned head, so a dropped window / omitted tail is rejected. The union is
  provably the whole genuine log with nothing omitted.

A forged / truncated / root-mismatched log yields no leases.

## Trusted-root hardening — `CommitBindsMMR`

The verifier checks the log against a *trusted root* it takes as a parameter. On
its own that root is whatever the node serves at `/api/receipts/index/root` — a
compromised / forking node can serve a self-consistent forged root (TOFU).

`TrustedRoot::CheckpointBound(CheckpointAnchor)` closes that seam: the trusted
root is pinned to a **finalized checkpoint** (a federation-quorum-certified
state). Before a verified read trusts the anchored root, it confirms via
`/checkpoint/latest` that the node still recognizes the finalized anchor:

1. the latest checkpoint is **finalized** — its QC vote count meets the anchor's
   `min_qc_votes` threshold;
2. the node has **not rolled back** below the anchor — its latest checkpoint
   height is `>= anchor.height` (a fork that rewinds finalized history is
   rejected);
3. the verified read's root **equals** the anchor's committed MMR root (the
   binding — `commit_pins_mmr`).

This is the DreggNet-side instantiation of the proven `CommitBindsMMR`
(`metatheory/Dregg2/Lightclient/MMR.lean` §6; `docs/deos/COMMIT-BINDS-MMR.md`).

**Provenance of the anchor's `mmr_root` (honest):** `CommitBindsMMR` Gap B —
welding `mroot` into the EPOCH commitment so a checkpoint *carries* the
receipt-index root — is VK-affecting and gated to the rotation epoch, so today's
`/checkpoint/latest` does not yet expose the MMR root field. Until it does, the
anchor's `(height, len, mmr_root)` is established out-of-band from a finalized
checkpoint (the operator channel / TOFU the design names), and the code enforces
the binding equality + the finality + the no-rollback checks against it. When Gap
B lands, the only change is the *provenance* of `mmr_root` — read it from the
verified checkpoint instead of the operator — a caller-side change in
`VerifiedNodeLeaseSource::read_verified_leases`.

## Live-edge proof status

The recovered edge node (`<EDGE_HOST>:8420`) is reachable read-only but its
receipt log is **empty** (`/api/receipts/index/root` → `len: 0`), it has no
program-bearing execution-lease cells, no finalized checkpoint, and its submit
endpoint is **operator-locked**. The daemon, pointed at it, boots the real loop,
reads (finds nothing), and idles — the wiring is proven against the live node up
to the point of having data.

The full live end-to-end (read a verified lease → schedule → dispatch → meter →
settle a real `Transfer` → reap) is gated on the **operator step**:

1. **unlock** the node and export its bearer token (`DREGGNET_NODE_BEARER`);
2. **mint** a real funded execution-lease grant via the lease factory (the
   signed-envelope / `execution-lease` factory path).

Until then the loop is proven on a local node: the integration tests
`control/tests/go_real_loop.rs` (read a real lease over the node-API wire →
dispatch + meter on a backend → settle real `Transfer` turns), plus
`control/tests/trusted_root_anchor.rs` (the `CommitBindsMMR` binding) and
`bridge/tests/windowed_verified_read.rs` (the long-chain windowed read), all run
against local stub nodes speaking the exact wire.
