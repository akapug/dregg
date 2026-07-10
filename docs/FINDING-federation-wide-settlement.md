# FINDING: federation-wide lease settlement needs the lease-program discharge, not a plain operator Transfer

Established 2026-07-10 while trying to make the demo lease's rent settle on every
replica. Surfaced *because* the orchestrator was made loud (it had been silent).

## The mechanism

DreggNet's provider settles metered rent with
`bridge/src/node_client.rs::submit_transfer` — a plain `Transfer { from: lease,
to: provider }` submitted to `POST /api/turns/submit`. The node signs every
thin-path turn as its **own operator cell** (confused-deputy hardening) and
executes it. A `Transfer` moving value *from* a cell requires that cell's
authorization: the operator can authorize a transfer from the lease **only if the
operator owns the lease**.

So the loop settles iff the lease cell is operator-owned. It was — until the demo
seed was made federation-wide (lease owned by a key derived from `federation_id`
so every replica seeds the identical cell). Then:
- the lease's owner key is not the operator → the operator-signed Transfer from it
  is refused `invalid authorization: hybrid: Ed25519 (classical) signature half
  failed`;
- and this broke the *single-node* loop too, which had settled only because the
  lease was operator-owned.

## The tension (why it's not a quick fix)

For a settlement to REPLICATE across the federation, both the `from` (lease) and
`to` (provider) cells must be federation-wide (identical on every replica) AND the
turn must be authorizable. A plain operator-signed Transfer can only move value
from an **operator-owned** cell, which is **per-node**. Federation-wide lease +
operator Transfer are mutually exclusive.

## The correct design

Rent is not the operator's value to move by fiat — it is the lease paying its
obligation, which the lease cell's PROGRAM (`starbridge-apps/execution-lease`
`lease_cell_program`) exists to enforce. The app already provides the mechanism:
the `pay` / `advance` discharge operations (`advance_effects`, the metered
discharge), which the executor re-enforces against the lease invariants and which
operate on the lease **without** requiring the caller to own it. Routing DreggNet's
metered settlement through the lease program's discharge (instead of a plain
Transfer) is what lets a federation-wide lease's rent settle on every replica.

That is a real integration step (DreggNet's `NodeApiSettlement` would submit a
lease-discharge turn, and the thin `/api/turns/submit` vocabulary would need to
carry it), not a drive-by.

## Current state (chosen for tonight)

- **Lease: operator-owned (per-node).** Restores the proven settlement loop
  (operator signs the Transfer from its own lease). Node-local.
- **Provider (rent beneficiary): federation-wide** — a real Ed25519 key derived
  from `federation_id`, seeded identically on every replica, so the metered
  Transfer credits a cell they all hold. (A raw blake3 digest is not a valid
  Ed25519 point and is refused; the key must be a real point.)

Net: a node-1 settlement moves value from node-1's lease to the shared provider.
It applies on node-1; it does not replicate (the other replicas lack node-1's
lease). Full federation-wide settlement waits on the discharge-path integration
above.
