# starbridge-agent-provenance

**Proof-carrying agent provenance — a verifiable, append-only, tamper-evident memory for AI agents.**

An AI agent posts its claims, tool-calls, and outputs to a capability-gated cell that is an
**append-only blake3 hash chain**. Each entry is a `WriteOnce` slot — once a record is
committed it can never be silently overwritten — and the head cursor is `Monotonic` — the
log only ever grows, never re-orders or rewinds. **Any party can recompute the chain from
the published claims and verify it link-for-link**; a single tampered or dropped entry
breaks the recomputation. This is a verifiable agent scratchpad: a memory you can audit.

Built from dregg primitives only — `FactoryDescriptor`, `Effect::SetField` /
`Effect::EmitEvent`, `Authorization::Signature`, Lane-G `StateConstraint` caveats. No
domain-specific provenance `Effect`, no `Authorization::Unchecked`, no placeholder
signatures. Routes through the **real verified executor** via `EmbeddedExecutor`.

## The hash chain

```
entry_0 = blake3(GENESIS_PREV || claim_0)
entry_1 = blake3(entry_0      || claim_1)
entry_i = blake3(entry_{i-1}  || claim_i)
```

Each `entry_i` is committed into a `WriteOnce` slot; `HEAD` advances `Monotonic`. The
chain commits to the *order* and *content* of every claim. To verify, a third party takes
the published `claims[]` and the committed `entry[]` digests and recomputes
`verify_chain(claims, committed)` — re-deriving each link and checking it matches.

| Slot | Constant     | Caveat       | What it guarantees |
|:---:|--------------|--------------|--------------------|
| `2` | `HEAD_SLOT`    | `Monotonic`  | the log index only grows — no re-order, no rewind |
| `3` | `TIP_SLOT`     | (cursor)     | the current chain tip digest |
| `4+`| `entry_i`      | `WriteOnce`  | each committed provenance record freezes forever (tamper-evidence) |

## Lean companion

`metatheory/Dregg2/Apps/AgentProvenanceGated.lean` proves the **same** invariants on the
verified gated executor (`execFullForestG`): append-only (`WriteOnce` no-overwrite),
`Monotonic`-no-rewind, faithful read-back, the receipt-log audit trail, the verifiable
hash chain, and balance-conservation. The Rust crate is the executable surface of that
proof.

## What this crate exports

```rust
provenance_factory_descriptor() -> FactoryDescriptor
provenance_cell_program()       -> CellProgram
factory_descriptors()           -> Vec<FactoryDescriptor>

build_append_action(cclerk,       log_cell, i, prev, claim)   // append entry_i
build_advance_head_action(cclerk, log_cell, new_head)

// off-chain verification helpers (no ledger needed)
link_hash(prev, claim)          -> FieldElement
entry_digests(claims)           -> Vec<FieldElement>
verify_chain(claims, committed) -> bool          // ← the audit any third party runs
claim_digest(bytes)             -> FieldElement

register(ctx: &StarbridgeAppContext) -> [u8; 32]
```

## Running it against a node

```rust
let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32]);
let exec = EmbeddedExecutor::new(&cclerk, "default");
exec.deploy_factory(provenance_factory_descriptor());

// birth a log cell, grant the owner cap, then append a chain:
let mut prev = GENESIS_PREV;
for (i, claim) in claims.iter().enumerate() {
    exec.submit_action(&cclerk, build_append_action(&cclerk, log, i, &prev, claim))?;
    prev = link_hash(&prev, claim);
}
// overwriting a committed entry is REFUSED by WriteOnce — tamper-evidence.

// later, any auditor recomputes:
assert!(verify_chain(&claims, &committed_digests_read_off_the_ledger));
```

The `examples/provenance_demo.rs` binary runs this end to end against an embedded node, and
`src/lib.rs::tests::factory_born_log_appends_chain_rejects_overwrite_and_verifies` is the
self-contained test: birth → 3-entry chain → tamper-refused → chain verifies.

```sh
cargo test -p starbridge-agent-provenance
cargo run  -p starbridge-agent-provenance --example provenance_demo
```

## See also

- `metatheory/Dregg2/Apps/AgentProvenanceGated.lean` — the verified companion.
- `../nameservice/README.md` — the anchor starbridge-app and exemplar.
- `../../HORIZONLOG.md` — `APPS-POLISH`: userspace-verify integration (a published
  `verify_chain` checker as a `dregg-userspace-verify` predicate).
