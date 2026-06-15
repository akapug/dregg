# starbridge-compute-exchange

**A compute marketplace — one verified cell that escrows a budget, gates a bid, and settles
conservingly.** A requester needs work done; a provider has spare compute. They transact a
job neither trusts the other over, with **no escrow agent and no off-chain coordinator**. The
job *is* a factory-born cell whose installed `CellProgram` is the rules, re-checked by the
verified executor on every turn.

```
POSTED ──bid──▶ BID ──settle──▶ SETTLED
```

- **post**   — the requester opens a job: writes the escrowed `BUDGET`, `REQUESTER_HASH`, and a
  sealed `SPEC_HASH` (the job description).
- **bid**    — a provider bids `price ≤ BUDGET`, binds `PROVIDER_HASH`.
- **settle** — the deal closes: the accepted price is **paid** to the provider and any
  remainder **refunds** the requester, atomically and value-neutrally.

## Four guarantees, one cell program

Each guarantee is a slot caveat the verified executor enforces:

| Guarantee   | What it bounds                                | How this cell enforces it | Scope |
|-------------|-----------------------------------------------|---------------------------|-------|
| **BUDGET**  | a bid never exceeds the escrowed budget       | `FieldLteField { BID ≤ BUDGET }` — the accepted price is a bounded draw (the AffineLe budget gate); a provider cannot bid past the job's budget | every turn |
| **ACCEPTED**| the accepted price, bound exactly once        | `WriteOnce(BID)` — the requester accepts a price once; no silent renegotiation after acceptance | every turn |
| **FLASHWELL**| atomic, conserving settlement                | no-mint `AffineLe { PAID + REFUNDED ≤ BUDGET }` (every turn) **and** no-burn `AffineEq { PAID + REFUNDED = BUDGET }` (settle) — the payout neither mints nor burns | see note |
| **LIFECYCLE**| one-way state machine                         | `StrictMonotonic(STATE)` — `POSTED→BID→SETTLED`; no regress, no replay, no double-settle | every turn |

> **The conservation invariant, honestly split.** The executor installs the descriptor's flat
> `state_constraints` and re-checks them *unconditionally* on every turn. The **no-mint** half
> (`PAID + REFUNDED ≤ BUDGET`) is universally true — `0 ≤ budget` before settle, equality at
> settle — so it is an executor-enforced invariant: **no party can ever extract more than was
> budgeted.** The exact **no-burn** equality (all the budget is accounted for) would be false at
> `bid` time, so it is scoped to the `settle` case of the canonical `child_program_vk` recipe
> (`job_cell_program`) and upheld by the settle fire, which reads live `BID` + `BUDGET` and pays
> the provider in full (`PAID := BID`, `REFUNDED := BUDGET − BID`). A value-minting settle is
> refused by the `AffineLe`; a value-burning settle is refused by the `AffineEq`.

Built from dregg primitives only — `FactoryDescriptor`, `Effect::SetField` /
`Effect::EmitEvent`, `Authorization::Signature` from `AppCipherclerk::make_action`, and Lane-G
`StateConstraint` slot caveats. No domain-specific compute `Effect`, no
`Authorization::Unchecked`, no `[0u8; 64]` placeholder signatures.

## The deos-native surface

The whole interaction is one composed `DeosApp` (`job_app`), shipping from `src/lib.rs`. The
rights ladder `Signature ⊂ Either ⊂ None` **is** the observer ⊂ provider ⊂ requester roster:

- `view_job` — cap-only, `Signature` (an observer / auditor reads the job state);
- `bid` — gated (cap∧state), `Either` — a `POSTED` precondition; the fire submits the full bid
  turn, the executor re-enforcing the BUDGET gate;
- `settle` — gated (cap∧state), `None`/root — a `BID` precondition; the fire reads live
  `BID` + `BUDGET` and pays the provider in full, the executor re-enforcing FLASHWELL
  conservation.

The job cell is published into the web-of-cells as a `dregg://` sturdyref (a provider or
auditor on another federation reacquires the job across the membrane), and is discoverable
under `compute` / `marketplace`.

**The seam is closed.** The deos fire is two-tempo: a cap∧state precondition gate decides the
button in-band (nothing submitted on a miss — anti-ghost), then the full multi-effect turn is
submitted and the executor re-enforces the installed program. So an over-budget bid
(`FieldLteField`), a value-conjuring settle (`AffineEq`/`AffineLe`), and a non-advancing state
(`StrictMonotonic`, strict) are all **real executor refusals in the fire path** —
`tests/deos_seam.rs` proves each, with both polarities (the honest turn commits; the hostile
turn is refused and commits nothing). `tests/factory_birth.rs` proves the same teeth bite on a
factory-born cell.

## Run the tests

```
cargo test -p starbridge-compute-exchange
```
