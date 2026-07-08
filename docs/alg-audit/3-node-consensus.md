# Alg-Complexity Audit — node/ consensus runtime

Read-only sweep of `node/src/**` (blocklace_sync, execution_cursor, catchup, api,
state, finality_gate, finalization_votes, prove_pool, strand_admission_gate,
gossip). Hunt: `Vec`-scan-where-`HashMap`-belongs, nested growth loops,
recompute-where-cache-belongs, big-structure clone-per-call, collect-then-scan.

**Scope excludes the KNOWN primary** — the per-poll finality-gate/tau-order FFI
rebuild in `blocklace_sync::poll_finalized_blocks` and `build_ordering_blocklace`
(owned by the throughput lane). Everything below is a DIFFERENT derp.

Good news first — the parts that are already right:
- `ExecutionCursor` (execution_cursor.rs): executed set is a `HashSet<BlockId>`;
  `pending`/`mark_executed`/`is_executed` are all O(1)/O(order). Sound.
- `finalization_votes.rs`: `committee` is `HashSet<[u8;32]>`, votes are
  `HashMap`-keyed, `record`/`quorum` group by root via `HashMap`. Clean.
- `state.rs::sync_receipt_index` is incremental (`chain[have..]`), not a rescan.
  `witnessed_receipt_count` is a `HashMap` lookup. `Ledger` is
  `HashMap<CellId, Cell>` (per `audits/AUDIT-cell.md`), so `ledger.get/len` are O(1).
- `execute_finalized_turn` (the consensus commit path) clones only the ACTOR cell
  (gated on proving), never the whole ledger. Good.
- `get_receipts` / `receipt_infos_from_chain` are bounded by `.rev().take(limit)`.

---

## Ranked findings (complexity × frequency × what-grows)

### 1. Per-request full-ledger deep clone on every turn-submit / faucet path
`api.rs` — `post_submit_turn:2994`, `post_submit_signed_turn:3300` **+** `3350`,
`post_submit_encrypted_turn:3823`, `post_faucet:6846` **+** `6881`.

```rust
let pre_ledger = s.ledger.clone();      // rollback snapshot of the WHOLE ledger
...
let mut scratch  = s.ledger.clone();    // (submit-signed & faucet) a SECOND full clone
```

- **Complexity:** O(cells) deep clone per request (each `Cell` deep-copies its
  capability `Vec`, fields, program). `post_submit_signed_turn` and `post_faucet`
  clone the entire ledger **twice** per request (`pre_ledger` for rollback +
  `scratch` for receipt-only ingress execution).
- **Hot path?** YES — this is the per-turn external ingress (`/turns/submit`,
  `/turns/submit-signed`, `/turns/submit-encrypted`, faucet). Every user turn pays it.
- **What grows:** the ledger cell count (unbounded over the deployment's lifetime).
- **FIX:** the clone exists only to roll back on the rare `append_receipt` failure.
  Replace the whole-ledger snapshot with a **touched-cell journal**: capture the
  pre-images of the (few) cells a turn mutates and restore only those on failure
  (the executor already knows the touched set). Kills an O(cells) alloc on the
  hottest path and drops the `scratch` clones to a provisioning delta. This is the
  single highest-leverage fix in the file.

### 2. Catch-up `apply_with_buffering` rebuilds the full lace keyset per block
`catchup.rs` — `present_set(lace)` at `258–260`, called inside the drain loop at
`276`, `283`, `313`.

```rust
fn present_set(lace: &Blocklace) -> HashSet<BlockId> {
    lace.iter().map(|(id, _)| *id).collect()          // O(N) over the WHOLE lace
}
...
while let Some(block) = queue.pop_front() {
    ...
    let present = present_set(lace);                  // rebuilt EVERY iteration
    let released = buffer.ready_after(block_id, &present);
```

- **Complexity:** O(B·N) — a batch of B blocks rebuilds the N-block keyset once
  per block. Both grow together precisely on the sync path (catch-up = many blocks
  arriving while the lace is already large ⇒ quadratic in history).
- **Hot path?** Catch-up / gossip-push ingest (bursty, but exactly when N is large).
- **What grows:** the lace N and the incoming batch B.
- **FIX:** maintain `present` as a single `HashSet<BlockId>` seeded once before the
  loop, `insert(block_id)` after each successful `receive_block`. O(N + B) instead
  of O(B·N). Bonus: `ready_after` clones its `present` arg into `now_present`
  (`169`) but **never reads `now_present`** for membership (it only `insert`s into
  it, `192`) — the whole `present` argument to `ready_after` is dead; drop it and
  the clone with it.

### 3. `get_starbridge_receipts` filter-scans the entire receipt chain per request
`api.rs:2350–2365`.

```rust
let chain = s.cclerk.receipt_chain();
let receipts = chain.iter().enumerate().rev()
    .filter(|(_, r)| cell.as_ref().is_none_or(|want|
        hex_encode(&r.agent.0).eq_ignore_ascii_case(want)) && ... )   // per-receipt String alloc
    .take(limit)
```

- **Complexity:** O(history). `.take(limit)` only short-circuits after `limit`
  MATCHES — a query filtered by `cell`/`turn_hash`/`effects_hash` that matches
  fewer than `limit` receipts walks the **whole** chain. Each visited receipt does
  3× `hex_encode` (heap `String` allocation) purely to compare.
- **Hot path?** Per-request explorer/starbridge endpoint; unauthenticated.
- **What grows:** the receipt chain (grows with every committed turn, forever).
- **FIX:** (a) compare on raw bytes — hex-decode the query params ONCE, match
  `r.agent.0 == want_bytes` — instead of hex-encoding every receipt per request;
  (b) for the common `cell=`/`turn_hash=` filters, add a secondary index
  (`HashMap<CellId, Vec<usize>>` / `HashMap<[u8;32], usize>`) maintained alongside
  `sync_receipt_index`, so a filtered query is O(matches) not O(history).

### 4. `poll_finalized_blocks` clones the whole DAG 2–3× per poll (distinct from the FFI rebuild)
`blocklace_sync.rs` — `962` (snapshot), `1101` (`lace_ffi` for tau-order FFI),
`1270` (`lace_ffi` for the gate FFI).

```rust
let lace = { let guard = self.lace.read().await; (*guard).clone() };   // 962
...
let lace_ffi = lace.clone();                                            // 1101
...
let lace_ffi = lace.clone();                                            // 1270 (fallback belt)
```

- **Complexity:** O(N) memory each; up to 3 full-DAG clones per finality poll
  (snapshot + one per `spawn_blocking` FFI). This is the ALLOCATION cost, separate
  from the known FFI COMPUTE rebuild the throughput lane owns.
- **Hot path?** Per finality poll (debounced ~150ms, fires on every produced/received block).
- **What grows:** the lace N.
- **FIX:** the snapshot at `962` is deliberate (release the read lock). But it can
  be an `Arc<Blocklace>` snapshot instead of a deep clone, and the two `lace_ffi`
  clones can move the same `Arc` into each `spawn_blocking` (the FFI only reads it)
  rather than deep-cloning again — cuts 2–3 O(N) deep clones per poll to zero-copy
  `Arc` bumps. Also `cursor.observe_order` does `self.last_order = ordered.to_vec()`
  every poll (O(order) clone) — acceptable given the soundness role, noted for
  completeness.

### 5. `wave_open` scans the whole lace per production cadence
`blocklace_sync.rs:3404` (inside the cadence's `wave_open` check).

```rust
lace.iter().any(|(id, block)| {
    ...
    match (tip_round, lace.round_of(id)) { ... }     // round_of per element
})
```

- **Complexity:** O(lace) scan (short-circuits on the first genuinely-open turn),
  with a `lace.round_of(id)` per visited block. If `round_of` is not O(1) this
  compounds.
- **Hot path?** Read on the block-production cadence (`wave_open`), separate from
  the finality executor.
- **What grows:** the lace (specifically the un-executed / near-tip region walked
  before the short-circuit).
- **FIX:** track a small set of "open near-tip" block ids incrementally as blocks
  are produced/executed, or bound the scan to the last `2*wavelength` rounds via a
  round-indexed structure, instead of `lace.iter()` over the full DAG each cadence.

---

## Minor / noted, not ranked
- `api.rs::get_all_cells` (`3974`) returns EVERY ledger cell in one unbounded
  response (`s.ledger.iter().map(...).collect()`) — O(cells) work + unbounded
  response size. Not quadratic, but wants a page/limit like the receipt endpoints.
- `api.rs::get_cell` (`3959/3963`) does `s.ledger.get(&cell_id)` twice (found +
  balance). O(1) each (HashMap), so cosmetic — fold to one lookup.
- `catchup.rs::unmet_roots` (`144`) is O(orphans × avg-preds) but bounded by the
  buffer size, not history. Fine.

## Top-5 summary
1. Per-request **full-ledger clone** on every turn-submit/faucet (`api.rs`
   2994/3300/3350/3823/6846/6881) — O(cells)/request, some paths 2×. Journal the
   touched cells.
2. **Catch-up `present_set` rebuild per block** (`catchup.rs:276/283/313`) —
   O(B·N). Maintain `present` incrementally; drop the dead `ready_after` clone.
3. **`get_starbridge_receipts` full-chain filter scan** (`api.rs:2350`) —
   O(history)/request + per-receipt `hex_encode`. Raw-byte compare + secondary index.
4. **`poll_finalized_blocks` 2–3× full-DAG deep clones per poll**
   (`blocklace_sync.rs:962/1101/1270`) — O(N) allocs/poll. `Arc` the snapshot.
5. **`wave_open` full-lace scan per production cadence**
   (`blocklace_sync.rs:3404`) — O(lace)/cadence. Round-index the near-tip window.
