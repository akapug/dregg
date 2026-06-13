# starbridge-polis — the governance layer

**Governance cells whose `StateConstraint` programs ARE the enforced state machines:**
M-of-N councils, constitution-as-program, forward-certified amendments, budgeted worker
mandates, and KERI-shaped pre-rotation identities — all as factory-born cells the verified
executor re-evaluates on every turn that touches them.

The polis layer follows the settlement-blueprint pattern (`cell/src/blueprint.rs`): per-
charter content-addressed `FactoryDescriptor`s whose `state_constraints` are installed for
life on the born cell. Turn-builders live in `dregg_sdk::polis`; end-to-end teeth on the
**real `TurnExecutor`** live in `sdk/tests/polis_governance_e2e.rs` and
`sdk/tests/polis_orchestration_e2e.rs`.

## The four organs of a polis

### `council` — M-of-N council with forward-certified amendments

A `CouncilCharter { members, threshold }` content-addresses to a `FactoryDescriptor`. The
council cell enforces an `M-of-N` approval gate: a proposal stages a hash + the membership
commitment; an amendment commits only when `threshold` distinct members have approved. The
amendment is **forward-certified** — the new membership is committed before it takes effect,
so a light client following the receipt log can verify the council's correct evolution.

```rust
council::CouncilCharter::new(members, threshold)
council::council_factory_descriptor(&charter) -> Result<FactoryDescriptor>
council::inspect_council(&charter, &fields)   -> CouncilStatus
```

### `constitution` — constitution-as-program

A `ConstitutionParams` pins the rules a governed cell must obey for life. The constitution
**is** the cell program — amendments are themselves gated by the constitution's amendment
clause.

### `mandate` — budgeted agent-orchestration worker mandates

A `WorkerMandate` scopes an agent worker to a commitment over a tool set
(`tool_scope_commitment(&tools)`), a budget, and a deadline. The worker cell's caveats meter
every action against the budget — the orchestration analogue of `tool-access-delegation`,
at the governance layer.

### `identity` — KERI-shaped pre-rotation

An `IdentityCharter` installs a key-event log: every key-state event commits to the digest
of the **next, unexposed** key set (`next_keys_digest`). A rotation must **exhibit** the
preimage of the pre-committed digest — so a thief holding the *current* keys still cannot
rotate the identity. This is the offline-signing / key-recovery substrate.

```rust
identity::IdentityCharter { devices, recovery, cooling_window, .. }
identity::key_set_commitment(&keys)    -> FieldElement
identity::next_keys_digest(&commit)    -> FieldElement
identity::identity_factory_descriptor(&charter) -> Result<FactoryDescriptor>
identity::inspect_identity(&charter, &fields)   -> IdentityStatus
```

## Why this is the keystone app

Every other starbridge-app governs a *single* resource (a name, a bounty, a subscription).
Polis governs the **governance itself**: who may change the rules, with what threshold,
under what constitution, with what key-rotation discipline. The constitution-as-program
stance means the rules are not enforced by an off-chain coordinator — they are the cell's
installed `CellProgram`, re-checked by the verified executor every turn.

## Running it against a node

The executor-path teeth live in the SDK e2e suites (they exercise the real `TurnExecutor`,
not `program.evaluate` in isolation):

```sh
cargo test -p starbridge-polis                       # charter validation, caveat shapes, inspectors
cargo test -p dregg-sdk --test polis_governance_e2e  # council propose → vote → commit on the executor
cargo test -p dregg-sdk --test polis_orchestration_e2e  # worker mandate metering on the executor
```

`dregg_sdk::polis` exposes the turn-builders (`propose`, `approve`, `commit_amendment`,
`rotate_identity`, …) that produce real signed actions.

## See also

- `cell/src/blueprint.rs` — the frozen settlement-blueprint reference pattern.
- `../nameservice/README.md` — the single-resource exemplar; polis is the governance-of-
  governance generalization.
- `metatheory/Dregg2/Apps/PreRotation.lean` — the verified pre-rotation companion for the
  `identity` organ.
- `../../HORIZONLOG.md` — `APPS-POLISH`: a factory-birth executor test *in this crate* (the
  e2e teeth currently live in `sdk/tests/`, not co-located) is a named follow-up.
