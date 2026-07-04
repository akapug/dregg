# starbridge-escrow-market

**A sealed-escrow atomic-swap marketplace — the app's escrow IS the protocol-proven
`SealedEscrow` capacity.** Two mutually-distrustful parties exchange value with **no trusted
intermediary**: "I give you X iff you give me Y." Each party locks a conforming *leg* of the
trade into the escrow cell's committed heap; the swap **settles atomically** only when both
legs are present; and until then each party may **reclaim** its own leg. No party can ever
walk away holding the counterparty's leg without a genuine own deposit, and no leg is
claimable twice. This is a real *witnessed movable asset*, not decorative slot arithmetic.

```
open(terms) ──depositₐ──┐
                        ├── settle (atomic 2-of-2) ──▶ A↔B value crossed
            ──deposit_b──┘
                        └── reclaim (half-open defence) ──▶ depositor made whole
```

- **open**    — seal the swap terms into the escrow commitment (who locks what on each side).
- **deposit** — a party locks its conforming leg; value leaves its wallet into custody, the
  commitment moves (a light client SEES value enter). A non-conforming leg is refused.
- **settle**  — the exchange completes atomically: both legs cross to their counterparties in
  one step (no half-open trade), value conserved per asset.
- **reclaim** — before settlement, a depositor pulls its own leg back and is made whole; the
  leg is one-shot (a reclaimed leg can never then be settled, and vice-versa).

The genuine core is `SealedEscrowMarket` (`src/lib.rs`), driving the proven
`dregg_cell::escrow_sealed` capacity (imaged by the Lean rung
`metatheory/Dregg2/Deos/SealedEscrow.lean`). The forge-rejecting verification core
(`EscrowState::check_claim` / `settlement`) refuses every attack: a non-conforming deposit, a
claim without a conforming own deposit, an over-claim, and a one-shot replay.

```sh
cargo test -p starbridge-escrow-market   # tests/atomic_swap.rs is the flagship
```

`tests/atomic_swap.rs` proves: witnessed deposit (commitment moves), atomic settlement,
per-asset conservation across the whole run, and the half-open-trade attack defeated by
reclaim. The `EscrowVault` (`Payable`) face receives value and settles it onward through the
shared interface, so per-asset `Σδ=0` holds across app boundaries (bounty→escrow→payee,
`tests/cross_app_value_flow.rs`). The `service::EscrowService` publishes the typed
`open`/`deposit`/`settle`/`reclaim`/`view` interface and drives the capacity; the `card`
module ships the renderer-independent UI.

---

## Legacy compat surface (RETAINED, demoted)

The constructs below are a **pre-existing slot-caveat "delivery lifecycle"**
(`list → fund → ship → settle`) RETAINED at the crate root because out-of-scope dependents
(`starbridge-first-room`, `starbridge-v2`) import them. They are **no longer the app's
headline escrow** — they model bounded *scalar fields*, not a movable witnessed asset. The
genuine escrow is the `SealedEscrowMarket` above.

```
LISTED ──fund──▶ FUNDED ──ship──▶ SHIPPED ──settle──▶ SETTLED
```

### Four organs, one cell program (legacy)

Each guarantee the night's organs provide is composed here as a slot caveat the verified
executor enforces:

| Organ      | The organ's guarantee                          | How this cell enforces it | Scope |
|------------|------------------------------------------------|---------------------------|-------|
| **TRUSTLINE**  | a draw never exceeds the credit line       | `FieldLteField { ESCROWED ≤ CEILING }` — the escrow is a bounded line; the buyer cannot escrow past the listing's ceiling | every turn |
| **MAILBOX**    | sealed delivery, bound exactly once        | `WriteOnce(DELIVERY_HASH)` — the seller commits the sealed-goods digest once; tamper-evident, no swap-after-ship | every turn |
| **FLASHWELL**  | atomic, conserving settlement (post ≥ pre) | no-mint `AffineLe { RELEASED + REFUNDED ≤ ESCROWED }` (every turn) **and** no-burn `AffineEq { RELEASED + REFUNDED = ESCROWED }` (settle) — the payout neither mints nor burns | see note |
| **LIFECYCLE**  | one-way state machine                       | `StrictMonotonic(STATE)` — `LISTED→FUNDED→SHIPPED→SETTLED`; no regress, no replay, no double-settle | every turn |

> **The flashwell invariant, honestly split.** The executor installs the descriptor's flat
> `state_constraints` and re-checks them *unconditionally* on every turn
> (`turn/src/executor/apply.rs::apply_create_cell_from_factory` installs
> `CellProgram::Predicate(state_constraints)`). The **no-mint** half
> (`RELEASED + REFUNDED ≤ ESCROWED`) is universally true — `0 ≤ escrow` before settle,
> equality at settle — so it is an executor-enforced invariant: **no party can ever extract
> more than was escrowed.** The exact **no-burn** equality (all escrow is paid out) would be
> false at `fund` time (`0 < escrow`), so it is scoped to the `settle` case of the canonical
> `child_program_vk` recipe (`escrow_cell_program`) and upheld by `build_settle_action`,
> which always emits a balanced split. Both halves are exercised by tests: a value-minting
> settle is refused by the `AffineLe`; a value-burning settle is refused by the `AffineEq`.

Built from dregg primitives only — `FactoryDescriptor`, `Effect::SetField` /
`Effect::EmitEvent`, `Authorization::Signature` from `AppCipherclerk::make_action`, Lane-G
`StateConstraint` slot caveats. No domain-specific escrow `Effect`, no
`Authorization::Unchecked`, no placeholder signatures.

## Cell schema

| Slot | Constant            | Caveat                          | Meaning |
|:---:|---------------------|---------------------------------|---------|
| `2` | `SELLER_HASH_SLOT`    | `WriteOnce`                     | the seller, bound at listing |
| `3` | `BUYER_HASH_SLOT`     | `WriteOnce`                     | the buyer, bound at funding |
| `4` | `CEILING_SLOT`        | `WriteOnce`                     | the escrow ceiling (the trustline `line`) |
| `5` | `ESCROWED_SLOT`       | `WriteOnce`, `≤ CEILING`        | the amount escrowed (the trustline `drawn`) |
| `6` | `DELIVERY_HASH_SLOT`  | `WriteOnce`                     | the sealed-delivery digest (the mailbox commitment) |
| `7` | `RELEASED_SLOT`       | `WriteOnce`, `+REFUND ≤/= ESC`  | funds released to the seller |
| `8` | `REFUNDED_SLOT`       | `WriteOnce`, `+RELEASE ≤/= ESC` | funds refunded to the buyer |
| `9` | `STATE_SLOT`          | `StrictMonotonic`               | the one-way lifecycle |

## What this crate exports

```rust
escrow_factory_descriptor() -> FactoryDescriptor   // constructor-transparency contract
escrow_cell_program()       -> CellProgram         // the canonical child-program recipe (Cases)
factory_descriptors()       -> Vec<FactoryDescriptor>

build_list_action(cclerk,   escrow, seller, ceiling)
build_fund_action(cclerk,   escrow, buyer, amount)
build_ship_action(cclerk,   escrow, &sealed_delivery_digest)
build_settle_action(cclerk, escrow, released, refunded)   // released + refunded == escrowed

sealed_delivery_digest(payload) -> FieldElement   // blake3 of the encrypted goods
register(ctx: &StarbridgeAppContext) -> [u8; 32]
```

## Running it against a node

```rust
use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, CellMode};
use starbridge_escrow_market::*;

let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32]);
let exec = EmbeddedExecutor::new(&cclerk, "default");
exec.deploy_factory(escrow_factory_descriptor());
// … birth an escrow cell from the factory, grant the owner cap …

exec.submit_action(&cclerk, build_list_action(&cclerk, escrow, "acme-corp", 1000))?;
exec.submit_action(&cclerk, build_fund_action(&cclerk, escrow, "buyer-bob", 800))?;   // ≤ 1000 ✓
let goods = sealed_delivery_digest(b"the-goods-ciphertext");
exec.submit_action(&cclerk, build_ship_action(&cclerk, escrow, &goods))?;
exec.submit_action(&cclerk, build_settle_action(&cclerk, escrow, 800, 0))?;           // release all
```

`tests/factory_birth.rs` is the runnable, self-contained version of exactly this — birth →
full deal → every organ tooth refusing its attack (funding over the ceiling, overwriting the
sealed delivery, minting at settle, double-settling).

```sh
cargo test -p starbridge-escrow-market
```

## Tests

| Test | Surface | What it pins |
|---|---|---|
| `src/lib.rs::tests::*` | `Cases` program via `evaluate_with_meta` | descriptor shape, all four organ caveats, default-deny on unknown methods, no-mint vs no-burn |
| `tests/factory_birth.rs::factory_born_escrow_runs_the_whole_deal` | **the real executor** | birth → `list → fund → ship → settle`, all ACCEPTED; post-state reads back |
| `tests/factory_birth.rs::..._refuses_funding_over_ceiling` | **the real executor** | TRUSTLINE: escrow over the ceiling REFUSED |
| `tests/factory_birth.rs::..._refuses_minting_tampering_and_double_settle` | **the real executor** | MAILBOX delivery-swap, FLASHWELL minting, LIFECYCLE double-settle all REFUSED |

## Userspace-verify integration (HORIZONLOG)

The settlement-conservation property (`released + refunded == escrowed`, and the headline
"no party extracts more than was escrowed") is the natural first customer for the
`dregg-userspace-verify` toolkit another lane is building: the escrow's conservation
predicate, lifted to a published userspace checker, would let any third party verify a
closed deal's conservation from its receipts without re-running the executor. The
integration point is `escrow_cell_program`'s settle case (the `AffineEq`/`AffineLe` pair).
Tracked in `../../HORIZONLOG.md` (`APPS-POLISH`). This crate does **not** depend on
`dregg-userspace-verify` compiling yet.

## See also

- `sdk/src/trustline.rs`, `sdk/src/mailbox.rs`, `sdk/src/flashwell.rs` — the SDK organ
  surfaces whose semantics this cell composes.
- `../nameservice/README.md` — the anchor starbridge-app and paint-by-numbers exemplar.
- `../bounty-board/` — the single-resource escrow lifecycle; escrow-market is the
  two-party, organ-composed generalization.
