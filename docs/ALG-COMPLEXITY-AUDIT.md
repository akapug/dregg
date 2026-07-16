# ALG-COMPLEXITY AUDIT — master board

Systematic 6-lane sweep of the whole tree for the `tauOrderFast`-class derp:
**`List`/`Vec` linear-scan where a `HashMap`/`HashSet` belongs, or recompute where a cache belongs,
on an input that grows with the chain / ledger / history.** Per-lane detail: `docs/alg-audit/{1..6}-*.md`
(the sweep-time record); the statuses on this board are checked against HEAD.

Verdict: the codebase is *architected* against the worst trap (per-turn work is scoped to the turn's
touched-cell set — `build_pre_ledger`, `execute_finalized_turn`, the exec FFI wire are all O(turn)).
The sweep caught a cluster of **history-growing membership gates** and **per-turn full-ledger clones**.
Most rows are closed; each row below says how (or names what stays open).

## RANK (severity = complexity × frequency × what-grows)

### 🔴 Tier 1 — live commit path, grows unboundedly
| # | derp | file:line | complexity | grows with | status |
|---|------|-----------|-----------|-----------|--------|
| 1 | Nullifier double-spend gate `nf ∈ k.nullifiers` | `RecordKernel.lean:433` | O(\|nullifiers\|)/spend | **all history** | ✅ CLOSED — by a stronger mechanism than the HashSet-twin this board proposed: the **sorted-Merkle nullifier accumulator**. The kernel carries `nullifierRoot` (the Poseidon2 sorted-tree root), and the deployed `noteSpendVmDescriptor2R24` **forces** freshness (gate test `deployed_notespend_wide_bracket_double_spend_rejected`). |
| 2 | Credential-revocation gate `revoked.contains` | `FullForestAuth.lean:481`(+500,648) | O(\|revoked\|)/action | **all history** | ⚠ **OPEN** — the gate still List-scans `s.kernel.revoked`; the accumulator treatment (#1's) is the shape of the fix |
| 3 | Producer full-ledger `template.clone()` | `exec-lean/src/lean_apply.rs:1148` | O(N_cells)/turn | ledger | ⚠ **OPEN** — touched-cell delta still wanted |
| 4 | api full-ledger clone ×2 per submit/faucet | `node/src/api.rs:3183` | O(N_cells)/turn | ledger | ✅ CLOSED for submit/faucet — an O(touched) per-turn undo journal (`ledger.begin_restore_point()`) replaces the whole-ledger clone there; ⚠ one live full-ledger `ledger.clone()` remains in `post_evaluate_proposal` (`node/src/api.rs:6471`, `dregg_coord::Participant::new(…, s.ledger.clone())` on every `/turn/atomic/evaluate` request); the other surviving clones are test-only |

### 🟠 Tier 2 — hot path, quadratic-per-call
| # | derp | file:line | complexity | grows | status |
|---|------|-----------|-----------|-------|--------|
| 5 | `has_equivocation_in_past` unmemoized (Rust `tau` dominant term) | `blocklace/src/ordering.rs:165` | O(waves·P·N²)/poll | DAG | ✅ CLOSED — the visible-equivocator formulation: precomputed once per `tau`, no per-observer causal-past rebuild |
| 6 | Pubkey ledger scan in bearer-cap auth | `cell/src/ledger.rs:566` | O(N_cells)/bearer-turn | ledger | ✅ CLOSED — `Ledger::pubkey_index` reverse index; `cell_by_pubkey` is O(1) |
| 7 | DSL Lookup re-scans lookup table per trace row | `circuit/src/dsl/circuit.rs:43` | O(rows·entries)/prove (2^16) | table | ✅ CLOSED — `LookupIndex`: O(1) membership, built once, consulted by the per-row prover/verifier loop |
| 8 | coord budget `debits: Vec` as anti-replay set | `coord/src/budget.rs:96` | O(n²)/session | session debits | ✅ CLOSED — `debit_set: HashSet<DebitDigest>` membership twin beside the Vec, rebuilt from `debits` on deserialize |
| 9 | Catch-up `present_set(lace)` rebuilt per block | `node/src/catchup.rs:258` | O(B·N) sync | DAG | ✅ CLOSED — `apply_with_buffering` seeds one `present: HashSet<BlockId>`, insert-on-accept |
| 10 | Linear `position` on SORTED `sorted_leaves` | `circuit/src/heap_root.rs:315` · `cap_root.rs:521` | O(n)→O(log n) | heap | ✅ CLOSED — `position_of` is a `binary_search_by`; range lookups use `partition_point` |
| 11 | `get_starbridge_receipts` full-chain scan | `node/src/api.rs:2475` | O(history)/request | receipts | ⚠ **OPEN** — every request still filters the whole receipt chain (hex-encoding each row to compare); wants a raw-byte compare + an agent/turn_hash index |
| 12 | `poll_finalized_blocks` clones whole DAG per poll | `node/src/blocklace_sync.rs:969` | O(N) alloc/poll | DAG | ✅ RESOLVED BY DESIGN — the poll deliberately snapshots the lace and releases the read lock (documented in-code: holding it across the O(history) FFI starved the producer's `lace.write()`), and the cross-poll fingerprint cache (`last_order_fingerprint`/`last_lean_order`, `:268`) skips the FFI entirely when the lace is unchanged |

### 🟡 Tier 3 — storage Merkle full-recompute-per-op
| # | derp | file:line | status |
|---|------|-----------|--------|
| 13 | `BlindedQueue::commit` dual-Merkle rebuild | `storage/src/blinded.rs:365` | ⚠ **OPEN** — `recompute_root` still rebuilds both trees from every leaf per commit; route through an incremental MMR (`bucket_commitment.rs` has one) |
| 14 | `MerkleQueue::recompute_root` per enq/deq | `storage/src/queue.rs:565` | ✅ CLOSED for enqueue — the incremental `append_reseal` fast path is O(log m) (`:589`); the dequeue full re-fold is documented in-code as irreducible for the front-drop window shape (advancing `head` re-indexes every pending leaf) |
| 15 | umem `lay` whole-heap boundary root per write | `dregg-umem/src/lib.rs:181` | ✅ CLOSED — `set_heap` is the O(log n) incremental heap-tree path |

### 🟢 Tier 4 — Lean model code (denotational; `@[implemented_by]` twins, off live path today)
StrandAdmission O(committee²) live-but-rare; distinctApprovers, HistoryAggregation.logRoot (MMR),
DirectoryLaws Dir, EpochReconfig, Polis Datalog `fire` (governance) — all `List`-model mirrors of
deployed Map/MMR structures. Fix the `tauOrderFast` way (`@[implemented_by]`, proofs untouched) when
they reach the live path or scale demands.

### CHECKED & CLEARED (sweep is legible)
per-turn exec (touched-scoped), execute_finalized_turn (actor-cell only), ExecutionCursor/finalization_votes
(HashSet), sync_receipt_index (incremental), cipherclerk (O(1) append), the `dregg-dfa` router (lazy
determinization + cached flat table), descriptor_ir2 trace (irreducible O(rows·constraints)), governance
tally (HashSet). Restart recovery = checkpoint + touched overlay (not full replay).

## REMAINING (the open rows)
- **#2 revocation gate** (`FullForestAuth.lean:481`): O(\|revoked\|) List scan on every gated action —
  the accumulator mechanism that closed #1 is the template (state-twin + seed rebuild, so needs-design).
- **#3 producer ledger clone** (`exec-lean/src/lean_apply.rs:1148`): O(N_cells) per turn — touched-cell delta.
- **#11 starbridge receipts scan** (`node/src/api.rs:2475`): O(history) per request — index by agent/turn_hash.
- **#13 BlindedQueue commit** (`storage/src/blinded.rs:365`): full dual-tree rebuild — incremental MMR.
