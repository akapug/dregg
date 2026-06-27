# starbridge-first-room

**THE FIRST ROOM of the living world — a composition exemplar that WELDS other apps' organs into one runnable, cargo-testable scenario.**

dregg read as a WORLD: a persistent place whose inhabitants — human or agent — act ONLY through a
mandate proven safe-forever. This crate stands up the first room end to end by **welding organs that
already landed** (it rebuilds none of them): a colonist does its mandated job step-by-step, finishes,
is paid from a conserving escrow — then a try-to-cheat battery, each cheat REFUSED in-band by the real
executor and rendered in-room with the receipt-why.

## This is a COMPOSITION EXEMPLAR, not a four-axis app

The modern starbridge-app template has four axes — a verified core (`FactoryDescriptor` +
`CellProgram`), a deos surface (`DeosApp`), a service cell (`invoke()`), and a deos-view card. Most
apps own all four because they define a primitive. **first-room owns none of the first three, by
design**: it has no verified primitive of its own. Its "core" is the *composition* of other apps'
cores, driven through ONE shared `EmbeddedExecutor`:

| Organ welded | From | What it contributes |
|---|---|---|
| the COLONIST'S JOB (DAG `gather→make→hand-off`, no-skip · clearance · spend-budget) | `starbridge-compartment-workflow-mandate` | the inhabitant's mandate it provably can't exceed |
| the ESCROW ECONOMY (`list→fund→ship→settle`, `released + refunded == escrowed`) | `starbridge-escrow-market` | the pay-for-work loop (a conserving transfer) |
| the ROOM + INHABITANT model | this crate (`src/room.rs`, gpui-free mirror of `starbridge-v2/src/room.rs`) | a place that renders each inhabitant's mandate, genuine actions, and in-room refusals |

Forcing a `FactoryDescriptor` or a service interface onto first-room would FAKE a primitive it doesn't
have and DUPLICATE the organs' own service/affordance surfaces — a degrading mismatch. So the honest
shape is: **a documented composition exemplar that ships the one modern-app axis that genuinely fits —
the renderer-independent CARD.**

## The mapping (ember's vision)

- a cell = an ENTITY (the inhabitant, the room, the escrow item);
- a turn = an ACTION (cap-gated + receipted) — every step here is a real signed turn;
- the held workflow-mandate = the colonist's JOB it provably can't exceed;
- the escrow settle = the pay-for-work ECONOMY (a conserving transfer);
- DAVID'S DOOR — the gateway (`starbridge-storage-gateway-mandate`) is where a *buildr* agent walks IN
  as a new inhabitant: it births a job cell under the gateway's physics and advances it with the same
  three legs (see `scenario::davids_door`).

## The scenario (`src/scenario.rs`)

`run_first_room()` runs the full cycle through ONE real executor and returns a `Transcript`:

1. the payer LISTS + FUNDS the escrow (the reward, drawn from a conserved pool, `escrowed ≤ ceiling`);
2. the inhabitant DOES ITS MANDATED JOB step-by-step (`gather → make → hand-off`, each a receipted
   turn the executor admits IFF the three legs pass);
3. the job FINISHES → the payer SHIPS + SETTLES → the escrow RELEASES → the inhabitant is PAID (a
   conserving transfer: `released == escrowed`).

Then THE HEADLINE — a try-to-cheat battery, EACH refused in-band by the real executor and rendered
in-room with the receipt-why:

| Cheat | Tooth that refuses it |
|---|---|
| (a) skip a prerequisite step | `MonotonicSequence(JOB_CURSOR)` |
| (b) overspend the budget | `FieldLteField(SPEND_ACCUM ≤ BUDGET)` |
| (c) reach outside its compartment (fund over the ceiling) | `FieldLteField(ESCROWED ≤ CEILING)` |
| (d) take a verb it wasn't granted (a hauler crafting) | `ClearanceDominates(actor ⊐ verb)` |
| (e) release the escrow without approval (a conjuring settle) | `AffineEq(RELEASED + REFUNDED == ESCROWED)` |

Each cheat is driven through `EmbeddedExecutor::submit_action` exactly as the honest steps are, so a
refusal is a REAL executor rejection (anti-ghost: it advanced no chain, produced no receipt), and the
refusal must cite its tooth (the both-polarity / non-vacuity discipline).

## The CARD axis (`src/card.rs`) — the one modern-app surface that fits

The composed room as a renderer-independent `deos.ui.*` view-tree: a `vstack` of a room header and one
nested section per inhabitant (its held mandate, its GENUINE receipted actions tagged `genuine`, and
its in-room REFUSALS tagged `refusal` — the anti-ghost tooth made visible, the two styled distinctly).
Pure `serde_json` (no dependency on the `deos-view` renderer crate, which pulls the mozjs + gpui
elephants). The SAME tree renders three ways via `deos-view` — native gpui pixels, a browser-loadable
HTML document, and a discord embed.

```rust
let t = starbridge_first_room::run_first_room();
let card_json = starbridge_first_room::room_card_json(&t.room.render()); // the welded room as deos.ui.* JSON
```

There are NO action buttons on this card: the room is a read-only COMPOSED VIEW; the actions live on
the organs' own service/affordance surfaces.

## What this crate exports

```rust
// the runnable scenario
run_first_room() -> Transcript        // the honest cycle + the try-to-cheat battery, one executor
davids_door() -> String               // the gateway-entry seam note
Transcript / CheatClass / CheatOutcome / JobStepRecord

// the room model
Room / RoomView / InhabitantView / InRoomRefusal

// the CARD axis
card::room_card_value(&RoomView) / card::room_card_json(&RoomView) / card::card_for_room(&Room)
```

## Tests

```sh
cargo test -p starbridge-first-room
```

| Test | What it pins |
|---|---|
| `scenario::tests::the_first_room_holds_end_to_end` | THE guarantee: job done + paid in full + conserving + every cheat provably refused |
| `scenario::tests::the_honest_cycle_earns_and_is_paid` | three genuine receipted job steps; spend tracks the DAG; paid the full conserved reward |
| `scenario::tests::every_cheat_is_provably_refused` | each of the five cheat classes refused in-band on its expected tooth |
| `scenario::tests::the_room_renders_the_inhabitant_and_the_refusals` | the room, felt: mandate + genuine actions + the five in-room refusals |
| `card::tests::*` | the composed room renders to a well-formed `deos.ui.*` tree; genuine actions + refusals tagged distinctly; the real welded scenario room renders its five refusals |

## See also

- `../compartment-workflow-mandate/` — the colonist-job organ (the mandate law + the job instance).
- `../escrow-market/` — the escrow-economy organ (`list→fund→ship→settle`, conserving).
- `../storage-gateway-mandate/` — DAVID'S DOOR (the gateway physics that scopes an agent's entry).
- `../bounty-board/` — the reference 4-axis template (for apps that DO own a primitive).
- `../../docs/deos/DEOS-APPS.md` — the deos app model.
