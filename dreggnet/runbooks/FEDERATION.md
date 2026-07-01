# FEDERATION — the consensus model + how to add an operator

The consensus backbone is a fixed **committee** of `dregg-node` validators that
gossip a shared blocklace (Cordial-Miners) DAG over the headscale overlay and
finalize turns by BFT quorum. This runbook is the operator-facing model: the two
ways the network grows (lace-merge and committee-union), the intentional
rust/lean finality mix, and the concrete steps to fold in a new operator.

Deeper specs: `deploy/FEDERATION.md` (the original consensus doc),
`deploy/FABRIC-JOIN.md` (the overlay join). The substrate proofs live in
`~/dev/breadstuffs`.

## Live state (2 of 5)

**Federation id:** `<FEDERATION_ID>`
(committee = {edge, node-a}, epoch 0, threshold 2).

| node | overlay | public key |
|---|---|---|
| edge (node-0) | `100.64.0.1` | `<NODE0_PUBKEY>` |
| node-a (node-1) | `100.64.0.2` | `<NODE1_PUBKEY>` |

Both run `--federation-mode full` (BFT quorum, not solo), peered over the overlay
(`peer_count: 1` each). The `federation_id` is a commitment to the committee —
`blake3_derive(len || sorted_pubkeys || epoch)` — so every node derives it
identically from `genesis.json`, and **adding members changes the id** (which is
exactly why growing the committee is a coordinated act, not a unilateral one).

> Note: the **solo** edge node the Discord bot points at has a *different*
> `FEDERATION_ID` (`<FEDERATION_ID_PREFIX>…` = `blake3(<EDGE_NODE_PUBKEY_PREFIX>…)`) because at n=1 the
> committee is just that one key. The bot's `FEDERATION_ID` must match whatever
> node it submits to; the bot logs the correct value at startup. See SECRETS.md.

### Quorum table

Threshold is the strict blocklace supermajority `⌊2n/3⌋ + 1 = n − ⌊(n−1)/3⌋`;
BFT tolerance is `f = n − threshold` (the Rust `federation::quorum_threshold` /
`compute_bft_threshold`, `federation/src/epoch.rs`):

| n | threshold | f | meaning |
|---|---|---|---|
| 1 | 1 | 0 | solo, no consensus |
| **2** | **2** | **0** | both must be online + honest (today) |
| 4 | 3 | 1 | survives one fault |
| **5** | **4** | **1** | survives one down/Byzantine node (target) |

At n=2, `f=0`: a *real* federation (two independent boxes, full BFT, signed
quorum) but **no fault tolerance** — both must be up for the chain to progress.
The load-bearing fact for "resists attackers" is not the count but that the extra
nodes are **independently operated** (a homelab operator's), so no single party holds
`n − f` keys.

## (a) Lace-merge — disjoint cell sets union for free

The blocklace is a **proven CRDT**. Two chains over *disjoint* cell sets merge
into one lace by set-union of their blocks — associative, commutative, idempotent
— with **no consensus round** needed, because disjoint cells cannot conflict.
This is the I-confluent fragment: state unions are free.

Grounded in:
- `~/dev/breadstuffs/turn/src/conflict.rs::disjoint_cells_no_conflict` (the test
  that two turns touching disjoint cells never conflict).
- `~/dev/breadstuffs/blocklace/src/lib.rs::causal_past_union` (the lace union
  primitive; `causal_past_union_equals_per_block_union` proves it equals the
  per-block union — the merge law in code).
- Lean: `metatheory/Dregg2/Distributed/LaceMerge.lean`,
  `metatheory/Dregg2/Confluence/CRDT.lean` (the merge-law proofs).

**Operationally:** when a node rejoins or a new node catches up, it pulls the
finalized DAG from the quorum and **unions** it into its lace — there is no
re-genesis and no global lock. A catch-up node re-derives the exact finalized
state by replaying the merged DAG (`node/src/catchup.rs`,
`node/src/blocklace_sync.rs`; convergence proven in
`metatheory/Dregg2/Distributed/CatchupConverges.lean`). This is what makes the
NODE-OPS.md recovery (wipe `dregg.redb`, restart, re-sync) sound.

## (b) Committee-union — epoch transitions add/remove validators

Changing **who** is in the committee is an **epoch transition**
(`federation/src/epoch.rs`), and the chain continues across it — **no
re-genesis**:

- `propose_epoch_transition(current_config, joins, leaves)` → computes the new
  member set, recomputes the threshold, and builds an `EpochTransition`
  (`from_epoch`/`to_epoch = current+1`, the added/removed validators). The
  attestation QC is a placeholder the proposer fills after collecting votes.
- `verify_epoch_transition(transition, old_config)` → **attestation-gated**:
  checks the epoch numbers are sequential, the QC carries **≥ old threshold**
  votes, and each vote's Ed25519 signature verifies against an *old-epoch*
  member key, and the new threshold is correct for the resulting member count.
- `apply_epoch_transition(config, transition)` → advances the epoch, swaps the
  member set, advances `epoch_start_height`, and sets the new threshold.

So a new validator is admitted **only** with a supermajority attestation from the
*current* committee — you can't unilaterally join. The chain's height keeps
advancing; only the validator set + threshold + `federation_id` change at the
epoch boundary.

> **Honest state:** the static committee re-roll (below) is the recommended,
> auditable path to the 5-quorum today. The dynamic join path
> (`MembershipAction::Join` over gossip + the epoch rotation above, gated by
> `--auto-approve-joins`) exists in the node but is **not yet exercised
> end-to-end on the live nodes** — wiring + exercising it is a named TODO.

## (c) The rust/lean finality mix is intentional

Finality has two impls that **cross-check each other** — this is by design, not
redundancy:

- **Rust is the real finality.** `dregg_blocklace::ordering::tau` computes the
  finalized total order over the lace (round computation → final-leader selection
  → `tauOrder`). `node/src/blocklace_sync.rs::poll_finalized_blocks` serves the
  not-yet-executed blocks to the executor in that order.
- **Lean shadows it.** `node/src/finality_gate.rs` wire-encodes the same
  `(wavelength, participants, lace)` and calls the verified Lean rule
  (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean::tauOrder`) via the FFI
  export `dregg_blocklace_finalize`. The theorem
  `gate_admits_iff_verified_finalizes` proves the gate admits a block **iff** the
  verified rule finalizes it — so gating on it *is* gating on the verified order.

The gate is controlled by **`DREGG_FINALITY_GATE` (default ON)** with two
fail-modes that matter operationally:

- **No Lean archive in the build (rust-only node):** the gate **fails OPEN** to
  the un-gated Rust order with a **loud warning + a divergence record**. The live
  path is never broken — a node without the verified archive keeps running — but
  the operator is told the verified gate is not active.
- **Archive present and the rules disagree** on a `(creator, seq)`: the gate
  **REFUSES** that block (it is not sliced to the executor) and records the
  divergence. **The verified rule wins.** A divergence is a **bug signal** —
  investigate it.

This means a consensus member can be run **lean-shadowed** (full verified gate,
needs the Lean archive in the image — the default `dregg-node:staging` build) or
**rust-only** (fast build, no Lean link — `--features dregg-sdk/no-lean-link`
style); both finalize, and a divergence between them is exactly the cross-check
we want. **Goal:** every consensus member runs lean-shadowed so a divergence is
caught everywhere, not just where the archive happens to be linked. (TODO.)

## How to add an operator

Two steps — the overlay and the committee.

1. **Merge their lace (overlay + catch-up).** Get their box on the mesh and stand
   up their node pointed at a live bootstrap peer; it pulls + unions the finalized
   DAG. This is the OPERATOR-ONBOARDING.md + NODE-OPS.md path. Disjoint cells
   need no coordination (lace-merge, above).

2. **Epoch-transition their validators into the committee.** For a devnet the
   simplest auditable path is a **static committee re-roll** (not the dynamic
   join):

   ```sh
   # generate a fresh 5-member genesis (all keys + the new federation_id):
   docker run --rm -v "$PWD/out:/out" dregg-node:staging \
     genesis --validators 5 --output /out
   #   → node-0..4.key  +  genesis.json (validators[] = all 5 pubkeys)
   #   prints the new 5-member federation_id with threshold 4
   ```

   Or assemble the committee from each operator's `GET :8420/api/node/identity`
   public key by hand. Then:

   - Put the **same** `genesis.json` on every node's data dir; give each its own
     `node.key`. (The committee — and thus `federation_id` — is now identical
     across all five.)
   - Start each node `--federation-mode full --federation-peers <edge>:9420`
     (one live bootstrap peer is enough; gossip-of-peers fills in the mesh).
     `--node-index`/`--federation-size` are documentation only — the committee
     comes entirely from `genesis.json`.
   - **Verify:** each `/status` shows `federation_mode: full`, `peer_count ≥ 1`,
     the new 5-member `federation_id`, and they converge to the same `dag_height`.
     Quorum is now 4-of-5 (`f=1`).

### Verify cross-node finality (the proof we ran 2026-06-28)

A turn submitted on **one** node finalizes and appears on the **other** with an
identical state commitment:

```sh
# on the edge — submit a faucet transfer:
curl -s -X POST http://localhost:8420/api/faucet \
  -H 'content-type: application/json' \
  -d '{"to":"aaaa...aaaa","amount":100}'
#   → turn_hash = 42dea554c67818a919a173757be0faf9590bd6027a0adb563dbdeaf4bb57046a

# the blocklace gossips the block to node-a; BOTH sign finalization votes
# (threshold 2 — both required). Then read the recipient cell on BOTH nodes:
curl -s http://100.64.0.1:8420/api/cell/aaaa...aaaa   # edge
curl -s http://100.64.0.2:8420/api/cell/aaaa...aaaa   # node-a
#   → balance: 100, identical state_commitment
#     ea4321e41be41501af0deeab2988ed4b6733acd3862984e6b93e18bb2161ea70
#   node-a's /api/receipts carries the same turn_hash, finality: "final"
```

node-a never received the faucet HTTP call — the recipient cell was provisioned
there purely from the finalized turn data by the same deterministic executor.
That is the cross-node-deterministic-finality property.

## See also

- OPERATOR-ONBOARDING.md — the new-operator path (steps 1 + role pick).
- NODE-OPS.md — deploy/restart/recover a node.
- MESH.md — the overlay join + headscale.
- `deploy/FEDERATION.md` — the original consensus spec.
</content>
