# DreggDL — a CapDL-inspired polyglot deployment description

*Design + scoping doc. Status: schema sketch + consumption design, not
implementation. Cites the actual tree as of 2026-06-13.*

## 0. The inspiration: CapDL

seL4's **CapDL** (Capability Distribution Language) is a single declarative
description of a whole system's capability layout: every component, every
kernel object (CNodes, TCBs, endpoints, frames), and every capability one
component holds to another. A **loader** (`capdl-loader`) reads the spec and
*instantiates* exactly that object-and-capability graph at boot. The
description is the source of truth; the running system is its image. Because
the cap graph is written down, it is **auditable** and **reproducible** — you
can read the whole authority structure of the system off one file.

dregg has the analogous object: cells are the objects, c-lists +
capabilities are the authority graph, factories are the constructors, and the
federation is the topology. Today there is **no single description** of a
dregg deployment — you assemble it imperatively by calling SDK builders in
some language. This doc designs **DreggDL**: write the dregg capability layout
*once*, declaratively, and have the Rust / TS / Python SDKs all instantiate
it. That is the unification of the polyglot DX.

## 1. The current state (why this is needed)

A deployment today is a *script* in one language, e.g. (Rust):

```rust
let factory_vk = runtime.deploy_factory(descriptor);            // sdk/src/runtime.rs:368
let plan = create_escrow_cell(&terms, owner, token, op, fund)?; // sdk/src/factories.rs:270
runtime.execute(plan.create_effects)?;                          // sdk/src/runtime.rs:651
runtime.execute_on(plan.cell_id, grant_effects)?;               // sdk/src/runtime.rs:703
```

The same deployment in TS (`sdk-ts/src/turns.ts`,
`runtime.turn().grant(...).sign()`) and Python (`sdk-py/src/lib.rs`,
`turn.grant(...).sign().submit()`) is *re-expressed* imperatively, builder by
builder. There is no artifact that says "this deployment IS these cells with
these grants under this factory on this federation." The pieces that *would*
serialize already exist:

- **`FactoryDescriptor`** is already `Serialize + Deserialize`
  (`cell/src/factory.rs:277`) and content-addressed by BLAKE3
  (`FactoryDescriptor::hash`, line 315). It carries `factory_vk`,
  `child_program_vk`, `allowed_cap_templates`, `field_constraints`,
  `state_constraints` (the perpetual slot caveats), `default_mode`,
  `creation_budget`. **This is already the declarative "constructor
  contract."**
- **`FactoryCreationParams`** (`cell/src/factory.rs:666`) — `mode`,
  `program_vk`, `initial_fields: Vec<(u32,u64)>`, `initial_caps:
  Vec<CapGrant>`, `owner_pubkey`.
- The **effects** are a closed, serializable vocabulary:
  `Effect::CreateCellFromFactory { factory_vk, owner_pubkey, token_id, params
  }` (`turn/src/action.rs:963`) and `Effect::GrantCapability { from, to, cap:
  CapabilityRef }` (`turn/src/action.rs:814`).
- **`FederationId(pub [u8;32])`** (`types/src/lib.rs:207`) is the topology
  anchor; all three SDKs already bind turns to it at signing time (Rust
  `set_local_federation_id`, TS `nodeClient.federationId()`, Python
  `Identity.turn(node_url, federation_id=...)`).

DreggDL is the document that *names these pieces together* and the thin
per-SDK consumer that lowers it to exactly these effects.

## 2. The schema sketch (DreggDL v0)

One file (TOML shown; JSON/YAML equivalent — the canonical form is a serde
struct, the text is a surface), declaring a deployment as four sections:
**federation**, **factories**, **cells**, **grants**.

```toml
# dregg.deploy.toml — one declarative dregg deployment

[federation]
id        = "b3:1f0a…"          # FederationId (hex of [u8;32]), or "auto" to
                                # derive blake3(operator_pubkey) from the node
node      = "https://node.example"   # ingress endpoint (TS/Py); "in-process" (Rust)

# A factory = a serialized FactoryDescriptor. Referenced by `ref`, identified
# on-chain by its content-address (factory_vk / descriptor hash).
[[factory]]
ref               = "escrow"
default_mode      = "hosted"          # CellMode
child_program_vk  = "vk:9c2…"         # the program installed on children
creation_budget   = 100
  [[factory.state_constraint]]        # the perpetual slot caveats (StateConstraint)
  kind  = "write_once"
  slot  = 3
  [[factory.state_constraint]]
  kind  = "monotonic"
  slot  = 5
  [[factory.allowed_cap_template]]    # CapTemplate — the most this factory may grant
  permissions = "signature"
  target      = "self"

# A cell = a CreateCellFromFactory instantiation.
[[cell]]
name         = "deal-001"
factory      = "escrow"               # -> factory.ref
owner_pubkey = "ed:4a7…"
token_id     = "tok:00…"
mode         = "hosted"
initial_fields = [ {slot = 1, value = 0}, {slot = 3, value = 42} ]
# value funded into the cell is a `transfer`, declared in [[grant]]/[[fund]] flows

# A grant = an Effect::GrantCapability edge in the authority graph.
[[grant]]
from        = "deal-001"              # CellId by name (or hex)
to          = "operator"             # the operator agent cell
permissions = "signature"
target      = "deal-001"             # the cell the cap reaches (self-grant = adopt)
expires_at  = 0                       # 0 = no expiry
```

Notes on the schema design:

- **Names, not raw ids, are the ergonomic layer.** `factory = "escrow"`,
  `to = "operator"`. The consumer resolves names → content-addresses /
  CellIds in a single pass, so the human writes a graph, the loader resolves
  it. (CapDL does the same: objects get symbolic names in the spec.)
- **The factory section IS a `FactoryDescriptor`** in surface form. Because
  `FactoryDescriptor` already round-trips serde, DreggDL's factory parser is
  thin — it builds the same struct the SDK already deploys, then takes its
  `.hash()` as the `factory_vk` reference. *Nothing new is invented; the
  schema is a friendly skin over the existing serialized type.*
- **The grant section is the authority graph.** Each `[[grant]]` is one
  `Effect::GrantCapability` edge. Reading all `[[grant]]` rows off the file
  *is* reading the whole dregg cap graph of the deployment — the CapDL
  property.
- **Federation = topology.** v0 is single-federation (one `[federation]`).
  Multi-federation / federation-of-federations topology is a v1 extension:
  multiple `[federation]` blocks plus `[[bridge]]` edges describing CapTP
  sturdyref grants across them (the `captp/` machinery already does
  cross-federation grants — the schema would name them).

## 3. How each SDK consumes it

The DreggDL document lowers to an **ordered list of effects** (factory
deploys, then `CreateCellFromFactory`, then `Transfer` funding, then
`GrantCapability`), grouped into turns in dependency order (a cell must be
born before it is granted from). Every SDK already has these verbs; the
consumer is a *lowering pass*, per language:

| Step | DreggDL section | Rust SDK | TS SDK | Python SDK |
|---|---|---|---|---|
| deploy factory | `[[factory]]` | `runtime.deploy_factory(desc)` (`sdk/src/runtime.rs:368`) | implicit at create (factory_vk content-addressed) | implicit at create |
| birth cell | `[[cell]]` | `Effect::CreateCellFromFactory` via `runtime.execute(...)` | `runtime.turn().createCellFromFactory(vk, params)` (`sdk-ts/src/turns.ts`) | `turn.create_cell_from_factory(...)` (`sdk-py/src/lib.rs`) |
| fund | transfer | `Effect::Transfer` via `execute` | `runtime.turn().transfer(to, amt)` | `turn.transfer(to, amt)` |
| grant | `[[grant]]` | `Effect::GrantCapability` via `execute_on` (`:703`) | `runtime.turn().grant(to, target, perms)` | `turn.grant(to, target, perms)` |
| bind topology | `[federation]` | `set_local_federation_id` (`:337`) | `new NodeClient(url, {federationId})` | `Identity.turn(url, federation_id=…)` |

The shared substrate that makes this clean:

- **One wire format.** All three SDKs submit a postcard `SignedTurn`
  envelope, Ed25519-signed over the federation-bound message, to the node's
  `POST /api/turns/submit-signed` (TS/Py) or the in-process executor (Rust).
  So the *lowering* of DreggDL is language-specific, but the *output* (signed
  turns) is identical bytes regardless of which SDK lowered it. A DreggDL
  deployed from Python and the same DreggDL deployed from Rust produce the
  same on-chain effects.
- **One descriptor type.** `FactoryDescriptor` is the Rust core type; TS and
  Python build the same content-addressed descriptor (their `program.
  descriptor(constraints)` surfaces return `{factory_vk, child_program_vk,
  constraints}`). DreggDL's factory parser produces that descriptor; the
  content-address (`factory_vk`) is the cross-language join key.

**Recommended implementation shape:** a single Rust crate, `dregg-deploy`
(or `dregg-dl`), that owns (a) the serde schema structs, (b) the
parser/validator, (c) the lowering to `Vec<Effect>` grouped into turns. Rust
SDK calls it directly. TS and Python get it **for free over the existing FFI
seams**: the Python SDK is already a PyO3 binding (`sdk-py/src/lib.rs`) and
the TS SDK already has a wasm path (`sdk-ts/src/wasm.ts`) — `dregg-deploy`'s
"parse DreggDL → emit ordered turns" is a pure function, ideal to expose
through both. This means the *parser and lowering live once, in verified-
adjacent Rust*, and the three SDKs are thin language bindings around it —
which is exactly the polyglot-DX unification ember wants: write the schema
once, the loader logic exists once, every language drives it.

## 4. Mapping to the real birth/grant turns

The lowering is not a new execution path — it produces exactly the turn
shapes the executor already gates. Concretely, for the escrow example, the
DreggDL above lowers to the same sequence `sdk/src/factories.rs` already
documents (create → fund → adopt → open):

1. `[[factory]] escrow` → build `FactoryDescriptor`, `deploy_factory` →
   `factory_vk`.
2. `[[cell]] deal-001` → `Effect::CreateCellFromFactory { factory_vk,
   owner_pubkey, token_id, params: FactoryCreationParams { mode,
   initial_fields, owner_pubkey, .. } }` — born all-zero with the factory's
   `state_constraints` installed for life (the executor re-evaluates them on
   every touching turn — `turn/src/executor/execute_tree.rs`, per the
   factories.rs module doc).
3. fund → `Effect::Transfer` of `value + ADOPT_TURN_FEE` into the cell.
4. `[[grant]] deal-001 → operator (self)` → `Effect::GrantCapability { from:
   deal-001, to: operator, cap }` — the one-time adopt self-grant
   (`sdk/src/factories.rs` step 5), the in-band form of the node's operator
   grant.

The safety is **not** in DreggDL and not in the SDK lowering — it is in the
`CellProgram` the factory installs, which the executor enforces on every
turn (factories.rs: "A caller who bypasses this module and hand-writes a turn
… faces the same program gate"). DreggDL is a *convenience and an audit
artifact*, never a trust boundary. A malformed DreggDL produces turns the
executor rejects; it cannot produce an unsafe deployment that the executor
would accept.

## 5. The synthesis — reproducible + verifiable deployments

This is where DreggDL pays off the CapDL philosophy and joins the existing
toolkit:

**Reproducible.** A DreggDL file + the factory descriptors it names + the
node's federation id fully determine the deployment's effect sequence. Re-run
it from any SDK in any language and you get byte-identical signed turns
(modulo the signing key). The deployment becomes a checked-in artifact, not a
tribal-knowledge script.

**Verifiable — and we already have the checker.** `dregg-userspace-verify`
(`dregg-userspace-verify/src/lib.rs`) is a *static, pre-submission* assurance
toolkit: it reads a constructed-but-not-submitted `CallForest` and checks the
artifact-decidable guarantees — `check_conservation` (B: per-asset moves net
to zero), `check_no_amplification` (A: in-forest grant edges are attenuations,
not amplifications), `check_wellformed` (no `Authorization::Unchecked` outside
genesis, references resolve), `check_ring_balance`. Its `boundary.rs` is the
honest static/dynamic line (`STATIC_CHECKABLE` vs `DYNAMIC_ONLY`).

The synthesis: **a DreggDL document lowers to a `CallForest`, and that forest
is exactly what `dregg-userspace-verify` checks.** So:

> **DreggDL + dregg-userspace-verify = a checkable deployment spec.**

Before any turn is submitted, the deployment author runs the static checks
over the lowered forest and gets a `Verdict` that, on failure, names the
precise locus (which cell, which grant edge, which asset). The grant graph
declared in `[[grant]]` is checked for non-amplification *as a graph*; the
funding transfers are checked for conservation; the structure is checked for
well-formedness — all *before* spending gas, all from the DreggDL artifact
alone. This is precisely CapDL's "you can audit the whole authority structure
off one file," made executable: the file is DreggDL, the audit is
`dregg-userspace-verify`, and the honest static/dynamic boundary
(`boundary.rs`) keeps us from claiming the static check stands in for the
executor or the proof (the *holding* half of A, freshness, integrity, and the
state commitment still need the live executor / receipt — `boundary.rs`
`DYNAMIC_ONLY`).

And at the seL4 layer (SEL4-EMBEDDING.md §6): a bootable dregg image can carry
*two* checkable layout specs — a CapDL spec for the component caps, a DreggDL
spec for the cell caps — making the deployment reproducible and auditable at
both the kernel and the protocol layer. Capabilities, and the descriptions of
them, all the way down.

## 6. First-step lanes

1. **`dregg-deploy` crate skeleton**: serde schema structs (federation /
   factory / cell / grant), a TOML+JSON parser, name-resolution pass, and the
   `lower(&Deployment) -> CallForest` function. Reuses `FactoryDescriptor`,
   `FactoryCreationParams`, `Effect`, `CapabilityRef`, `FederationId`
   verbatim — no new on-chain types.
2. **Wire it to `dregg-userspace-verify`**: `deploy check dregg.deploy.toml`
   lowers + runs the four static checks, prints the verdict with loci.
3. **Round-trip test**: lower the same DreggDL from the Rust path and (via the
   PyO3 / wasm seam) the Python/TS paths; assert byte-identical signed turns.
4. **`dregg-deploy apply`**: lower → submit through whichever SDK's node
   client, returning the receipt chain. The escrow example in
   `sdk/src/factories.rs` is the reference deployment to reproduce as a
   DreggDL file first.
