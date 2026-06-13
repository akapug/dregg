# starbridge-escrow-market

**An escrowed-delivery marketplace — one verified cell that composes the guarantees of four
organs.** This is the app that shows dregg is not a toy: a buyer and seller who don't trust
each other transact a good with **no escrow agent and no off-chain coordinator**. The escrow
*is* a factory-born cell whose installed `CellProgram` is the rules, re-checked by the
verified executor on every turn.

```
LISTED ──fund──▶ FUNDED ──ship──▶ SHIPPED ──settle──▶ SETTLED
```

- **list**   — the seller opens a listing: writes the escrow `CEILING` and `SELLER_HASH`.
- **fund**   — the buyer escrows `amount ≤ CEILING`, binds `BUYER_HASH`.
- **ship**   — the seller commits the **sealed-delivery digest** (the encrypted goods /
  turn-intent) into `DELIVERY_HASH`.
- **settle** — the deal closes: funds **release** to the seller and any remainder
  **refunds** the buyer, atomically and value-neutrally.

## Four organs, one cell program

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
