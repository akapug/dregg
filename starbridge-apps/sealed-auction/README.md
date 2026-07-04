# starbridge-sealed-auction

**Sealed-bid, front-running-proof multi-agent coordination — settled through the verified executor.**

Several agents compete for a single award — a compute slot, a task assignment, a contract —
by submitting **sealed** (hashed) bids during a COMMIT phase, then REVEALING them. Because a
commitment binds `(bidder, value, nonce)` under blake3, no agent can peek at, copy, or
front-run another's bid before the reveal. The winning bid then **settles atomically**
through the verified per-asset executor: the award is all-or-nothing and value-neutral.

This is the executable surface of `metatheory/Dregg2/Intent/SealedAuction.lean`, which
**proves** the guarantees this crate enforces. It is the Rust image of the same
commit-reveal state machine.

## The guarantees, proven in Lean

| Lean keystone | What it guarantees |
|---|---|
| `reveal_binds_committed`        | a sealed commitment opens to **exactly** its bid (collision-resistance) — no peeking-then-switching |
| `reveal_requires_reveal_phase`  | no reveal binds before the commit phase closes |
| `uncommitted_cannot_open`/`_win`| a party that never committed can never reveal, hence never settle |
| `settle_atomic`                 | the award is all-or-nothing — a leg failure aborts the whole settlement |
| `settle_conserves`              | the award is value-neutral — no asset is minted or burned |
| `winner_was_committed`          | the award binds back to a real prior commitment |

## Routing through the VERIFIED executor — not a Rust shadow

Settlement does **not** re-implement ledger arithmetic. `Auction::settle` builds the award
**ring** — leg 1: the winner pays its bid to the seller; leg 2: the seller's slot cell
delivers the task-token to the winner — and folds it through
`dregg_intent::verified_settle::settle_ring_verified`, the Rust mirror of the Lean
`Ring.settleRing` / `SealedAuction.settle`. That fold runs the verified per-asset
transition `recKExecAsset` for **every** leg (and, under the intent crate's
`verified-settle` feature, cross-checks each leg against the **real Lean FFI export**). A
leg that fails its gate aborts the whole award (atomicity); a committed award provably
conserves every asset (conservation). The coordination is settled by the verified
executor, not by a Rust-only path.

## The sealed commitment

```
seal(bid) = BLAKE3_derive_key("dregg-sealed-auction bid v1", bidder || sign || |value| || nonce)
```

— the same construction as the running `intent::commit_reveal_fulfillment`, and the Rust
image of the Lean `SealedAuction.sealOf`. The nonce blinds the commitment so even a
low-entropy `value` is hidden. Collision-resistance is the assumption the binding rests on
(proved non-vacuously in Lean against the reference `Blake3Kernel`).

## What this crate exports

```rust
struct Bid { bidder, value, nonce }   Bid::seal() -> [u8; 32]
enum Phase { Commit, Reveal, Settled }
struct Auction { .. }
    Auction::new(seller, slot, asset, slot_asset)
    .commit(seal)              // COMMIT phase only; reveals rejected
    .seal_commit_phase()       // close commits, open reveals
    .reveal(bid)               // REVEAL phase only; binds iff the seal opens
    .winner() -> Option<Bid>   // first-price: highest revealed valid bid
    .award_ring(winner) -> Vec<VerifiedLeg>
    .settle(ledger) -> Result<.., VerifiedSettleError>   // verified per-asset fold
fund_ledger(rows) -> VerifiedLedger
```

## Running it

```rust
use starbridge_sealed_auction::*;

let mut a = Auction::new(seller, slot, asset, slot_asset);
a.commit(Bid::new(alice, 100, 0xAA).seal())?;   // sealed — value hidden
a.commit(Bid::new(bob,    80, 0xBB).seal())?;
a.seal_commit_phase();                            // no late commits past here
a.reveal(Bid::new(alice, 100, 0xAA))?;            // binds: the seal opens to this bid
a.reveal(Bid::new(bob,    80, 0xBB))?;
let mut ledger = fund_ledger(&[(alice, asset, 100), (seller, slot_asset, 1)]);
a.settle(&mut ledger)?;                            // verified, atomic, conserving
```

```sh
cargo test -p starbridge-sealed-auction
```

The suite (`src/tests.rs`) covers: a sealed bid hides its value; a reveal that doesn't open
its seal is rejected; an uncommitted party cannot win; settlement conserves value and is
atomic.

## See also

- `metatheory/Dregg2/Intent/SealedAuction.lean` — the verified development this mirrors.
- `../../intent/src/verified_settle.rs` — the verified per-asset settle fold.
- `../../HORIZONLOG.md` — `APPS-POLISH`: a factory-born *commitment-board cell* (so the
  commit phase itself is on-ledger with a `WriteOnce`/`Monotonic`-gated commit set) is a
  named follow-up; today the commit/reveal phase machine is in-process and only the award
  settlement is on the verified executor.
