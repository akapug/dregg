# starbridge-supply-chain-provenance

**Single-custodianship as a conservation law, enforced by the verified executor — plus a derived-cell + attested-query showcase.**

An ITEM is a factory-born sovereign cell. A custody HANDOFF is a cap-attenuated
transfer that moves the sole custodianship forward, strictly advances a
provenance epoch, and appends a tamper-evident receipt link. The PROVENANCE is
the on-cell hash chain (`link_i = blake3(prev ‖ event)`), which a third party
PROVES by re-derivation. A FORGED handoff — a party claiming custody it does not
hold — is REFUSED by the verified executor on two teeth: the cap-graph (no
custody cap reaching the item) and the actor-bound register
(`AnyOf[Immutable, SenderInSlot]`).

This crate follows **the unified starbridge-app template** — the four axes every
modern deos app demonstrates — and adds a fifth, the **derived-cell /
attested-query** showcase: a provenance summary is a derived view `f(events)`,
made unforgeable to a light client by two grounded dregg capabilities.

## The axes (the template + the showcase)

| Axis | What it is | Where | Test |
|---|---|---|---|
| **1. Verified core** | a `FactoryDescriptor` + `CellProgram` whose slot-caveats ARE the custody policy; the executor refuses any illegal turn | `src/lib.rs` | `src/lib.rs::tests` |
| **2. deos surface** | the custody lifecycle composed as a `DeosApp` — per-viewer projection, cap∧state gated fires, web-of-cells publish, manifest | `src/lib.rs` (`item_app`, `register_deos`) | `tests/deos_seam.rs`, `tests/reexpress_deos_app.rs` |
| **3. Service cell** | a typed `InterfaceDescriptor` driven through the `invoke()` front door — the lifecycle as named methods (cells-as-service-objects) | `src/service.rs` | `tests/service.rs` |
| **4. deos-view card** | the UI as a renderer-independent `deos.ui.*` view-tree (native gpui / web HTML / discord — one piece of data) | `src/card.rs` | `src/card.rs::tests` |
| **5. Derived-cell + attested-query** | a provenance summary as a derived view `f(events)`, grounded on `dregg_cell::derived` and `dregg_query` | `src/derived.rs` | `src/derived.rs::tests` |

These compose: the SAME `item_program()` backs axes 1–4, so the same custody
caveats bite whether a turn arrives as a raw `build_*_action`, a gated `DeosApp`
fire, or an `invoke()` method call. Soundness lives in the verified core (axis 1);
axes 2–4 are faces onto it; axis 5 certifies VIEWS over its committed history.

## Axis 1 — custody as caveats (not asserted)

Each item lives in a sovereign cell whose policy is its installed `CellProgram`:

| Slot | Constant | Caveat | What it guarantees |
|:---:|---|---|---|
| `0` | `CUSTODIAN_SLOT` | `AnyOf[Immutable, SenderInSlot]` | the **actor-bound baton** — the custodian may change only in a turn SIGNED BY the incoming holder (a stolen-baton flip is refused) |
| `1` | `EPOCH_SLOT` | `StrictMonotonic` | **no replay** — every handoff strictly advances the provenance epoch |
| `2` | `HEAD_SLOT` | `Monotonic` | **append-only** — the custody chain cannot be rewound (no truncate-then-fork) |
| `3` | `TIP_SLOT` | — | the latest committed custody-link digest (the chain tip a verifier reads first) |
| `4+i` | `LINK_BASE + i` | `WriteOnce` | **frozen links** — a committed custody receipt is tamper-evident forever |

These mirror the verified Lean developments (`AgentOrchestrationBudget`,
`AgentProvenanceGated`, `AgentOrchestration`) — no new Lean module is added. The
provenance chain is PROVED by re-derivation: `verify_chain(handoffs, committed)`
recomputes the honest chain and rejects a tampered, reordered, forged, or dropped
handoff. Single-custodianship is conservation: `custody_chain_is_connected`
witnesses that custody is a single connected path with no fork and no gap.

## Axis 2 — the deos surface (`item_app` / `register_deos`)

The lifecycle composed as a `DeosApp`: `view_provenance` is a cap-only read;
`accept_custody` and `mint_item` are **gated** affordances carrying a live-state
precondition (the item is minted / not-yet-minted), so a custodian sees
`accept_custody` LIT only after the mint (the htmx tooth). The fire is a real
verified turn the executor re-enforces the full custody program on. `grant_custody`
carries the real `Effect::GrantCapability` (the `derive_no_amplify` cap handoff).
See `tests/deos_seam.rs` and `tests/reexpress_deos_app.rs`.

## Axis 3 — the service cell (`invoke()`, `src/service.rs`)

The custody lifecycle as a first-class typed interface, driven through the
`invoke()` front door (no `Effect::Invoke`, no kernel change; a method desugars to
the ordinary verified effects it names, routed by the SAME verified DFA router the
protocol uses):

| method | semantics | auth | desugars to |
|---|---|---|---|
| `mint()` | Replayable | `Signature` | `SetField(CUSTODIAN=signer, EPOCH=1, link_0, HEAD=1, TIP)` |
| `handoff(from, prev, epoch, i)` | Replayable | `Signature` | `SetField(CUSTODIAN=signer, EPOCH, link_i, HEAD, TIP)` |
| `view()` | **Serviced** | `None` | — (the named OFE seam: a read, not a turn) |

```rust
use starbridge_supply_chain_provenance::service::ProvenanceService;
use dregg_app_framework::InvokeAuthority;

let svc = ProvenanceService::new(item_cell);
let turn = svc.mint(&cclerk, InvokeAuthority::Signature)?; // routed + cap-gated + signed
executor.submit_turn(&turn)?;                              // the executor re-enforces the program
```

The cap-gate bites twice (at the front door AND the executor); a replayed `mint`
(or a stale `handoff`) is an executor refusal (`StrictMonotonic(EPOCH)`); `view`
refuses to desugar (it names the serviced seam honestly). Register the interface
with `service::register_interface(&mut registry, cell)` so the Service Explorer
resolves the real `Signature`/`Serviced` shape.

## Axis 4 — the deos-view card (`src/card.rs`)

The app's UI as a renderer-independent `deos.ui.*` view-tree: a `vstack` of a
header, a live `bind` on `EPOCH_SLOT` (the handoff counter, re-read off the
ledger), and one `button` per service method carrying its `onClick = {turn, arg}`
(the button `turn` names ARE the service method symbols). The card is pure
`serde_json` data (no dependency on the `deos-view` renderer crate, which pulls the
mozjs + gpui elephants and is a standalone excluded workspace).

```rust
let card_json = starbridge_supply_chain_provenance::card::provenance_card_json();
```

## Axis 5 — derived-cell + attested-query (`src/derived.rs`)

A provenance SUMMARY is a derived view: `summary = f(events)`. The custody history
determines, by a pure function, the item's current custodian, handoff count,
epoch, and chain tip. This module wires the two grounded dregg capabilities that
make such a summary unforgeable to a light client.

- **The projection function** — `derived::summarize(&[Handoff]) -> ProvenanceSummary`
  is the pure `f(events)` derived-view shape.
- **The derived-cell** (grounded on `dregg_cell::derived`) — a **shipment-manifest**
  cell is derived over a roster of item source cells; its committed value IS the
  item count (`Aggregate::Count`), bound into its commitment. A forged manifest
  (over-counts) or a stale one (the roster changed, the manifest did not re-derive)
  fails `verify_shipment_manifest`. This is the executor image of the proven Lean
  rung `metatheory/Dregg2/Deos/DerivedCell.lean` (`bind_verifies`,
  `forged_value_rejected`, `stale_rejected`, `claim_bound_in_root`).
- **The attested-query** (grounded on `dregg_query`) — the item's custody handoffs
  are receipt rows; `derived::attested_custody_log` builds the receipt-log MMR over
  them, opens the whole prefix, and evaluates a `field(item, CUSTODIAN, …)` query to
  produce an `AttestedAnswer` carrying a **non-omission certificate**.
  `verify_attested_custody_log` checks it against the trusted root and re-derives the
  rows, so a verifying answer is provably computed from EXACTLY the committed handoff
  range — a COMPLETENESS certificate over the cell's provenance events. A tampered or
  omitted handoff breaks it. This is the Rust embodiment of
  `metatheory/Dregg2/Lightclient/MMR.lean`'s `server_cannot_omit_position`.

```rust
use starbridge_supply_chain_provenance::derived::{attested_custody_log, verify_attested_custody_log};

let (root, answer) = attested_custody_log(&item, &handoffs);
verify_attested_custody_log(&answer, &root)?; // "these are ALL the custodians, none omitted"
```

## What this crate exports

```rust
// Axis 1 — verified core
item_factory_descriptor() -> FactoryDescriptor
item_program()            -> CellProgram
build_mint_action / build_handoff_action / build_forged_handoff_action
verify_chain / custody_chain_is_connected
register(ctx: &StarbridgeAppContext) -> [u8; 32]   // mount factory + inspector + deos surface

// Axis 2 — deos surface
item_app(cclerk, executor) -> DeosApp
register_deos(ctx) -> DeosApp                       // seed + mount the composed surface
fire_mint / fire_accept_custody

// Axis 3 — service cell
service::ProvenanceService                          // .mint / .handoff / .view
service::interface_descriptor() / service::register_interface(...)

// Axis 4 — deos-view card
card::provenance_card_value() -> serde_json::Value
card::provenance_card_json()  -> String

// Axis 5 — derived-cell + attested-query
derived::summarize(...) -> ProvenanceSummary
derived::bind_shipment_manifest / verify_shipment_manifest        // grounded dregg_cell::derived
derived::attested_custody_log / verify_attested_custody_log       // grounded dregg_query
```

## Tests

```sh
cargo test -p starbridge-supply-chain-provenance
```

| Test | Surface | What it pins |
|---|---|---|
| `src/lib.rs::tests::*` | `CellProgram::evaluate` directly | descriptor shape + every custody caveat + the chain verifier in isolation |
| `src/service.rs::tests` | the `invoke()` builder | typed interface shape + front-door refusals |
| `src/card.rs::tests` | the view-tree | the card is a well-formed `deos.ui.*` tree whose buttons carry the service methods |
| `src/derived.rs::tests` | the grounded primitives | the projection summary, the derived-cell forge/stale rejection, the attested-query completeness certificate (tamper / omission break it) |
| `tests/service.rs` | **the real executor** | the lifecycle through `invoke()`: authorized commit, front-door cap-gate, executor re-enforcement, serviced seam |
| `tests/deos_seam.rs` | **the real executor** | the gated fires + the fire→full-`CellProgram` seam |
| `tests/reexpress_deos_app.rs` | the axum surface | per-viewer projection, web-of-cells publish, rehydration, manifest |

## See also

- `../bounty-board/` — the reference template for the four axes.
- `../../cell/src/derived.rs`, `../../metatheory/Dregg2/Deos/DerivedCell.lean` — the grounded derived-cell primitive and its Lean rung.
- `../../dregg-query/` — the attested-query crate; `../../metatheory/Dregg2/Lightclient/MMR.lean` — the non-omission proof.
- `../../deos-view/` — the card renderers (native / web / discord); `docs/reference/deos-view.md`.
