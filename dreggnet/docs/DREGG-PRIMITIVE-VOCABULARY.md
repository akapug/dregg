# The dregg primitive vocabulary — the complete toolbox

*The foundation document for a non-myopic DreggNet Cloud. This is the grounded
catalog of everything the dregg substrate (`~/dev/breadstuffs`) actually offers as
a primitive — what each IS (cited to `file:line` / theorem), what it ENABLES, and
**what real-world cloud resource it becomes when extended outward**. Read this to
stop asking "can dregg host a static site" and start asking "what is the full set
of resources a verifiable ocap substrate can sell."*

Dated 2026-06-30. Every claim is grounded to a `file:line` in `breadstuffs` or a
`Module.decl` in `metatheory/`. Status labels are the repo's own discipline —
verify against HEAD before betting on a specific line.

---

## How to read this

**The one-sentence through-line of the whole substrate** (from
`metatheory/.../MEMORY.md` and `docs/OVERVIEW.md`): *a turn is the exercise of an
attenuable proof-carrying token over owned state, leaving a verifiable receipt* —
and *a light client holding one root knows every transition in the whole history
was authorized, conservative, fresh, and correctly committed, re-executing
nothing.* Macaroons/biscuits → biscuit's Datalog became the derivation circuit →
the cell/turn/receipt model.

**Status legend** (honest grading, matching the repo):

- **⬛ PROVEN+DEPLOYED** — a Lean theorem (`#assert_axioms`-clean, footprint ⊆
  `{propext, Classical.choice, Quot.sound}`) *and* running Rust the executor
  enforces.
- **🟦 DEPLOYED** — running Rust, executor-enforced and tested; the in-circuit /
  light-client witness may be a *named seam* (the executor tooth is real and
  load-bearing today; the circuit tooth is its named shadow).
- **🟨 DESIGNED** — a spec/design exists; partially built or behind a named gate
  (e.g. a VK epoch).
- **⬜ ASPIRATIONAL** — a vision reachable *from* a named primitive; not built.

**The cloud-mapping column is the point.** dregg was not built as a cloud — it was
built as a verified ocap kernel. The mapping below is the synthesis: every kernel
primitive has a latent real-world-resource reading, and the union of those readings
is the actual product surface of a verifiable cloud nobody else can assemble.

---

## 0. The five meta-primitives (the spine everything rides)

These are not "a resource" so much as the substrate's atoms — but the cloud reading
of each is the foundation of the rest.

### 0.1 The Cell — the four-substance sovereign object ⬛

**IS:** "an isolated agent execution context" (`cell/src/cell.rs:249`) bundling four
disciplines the kernel verbs are the structural rules of
(`metatheory/Dregg2/Substrate/VerbRegistry.lean:72`): **value** (linear, `Σδ=0`),
**authority** (non-forgeable, attenuable, epoch-revocable), **evidence** (monotone
nullifier/commitment ledgers), **state** (guarded-mutable under a `Pred`). Identity
is content-addressed: `id == BLAKE3(public_key ‖ token_id)` under
`"dregg-cell-id-v1"` (`types/src/lib.rs:701`). Everything authority-bearing folds
into one canonical commitment `compute_canonical_state_commitment`
(`cell/src/commitment.rs:204`) — omit any field and two distinct authorities could
share a commitment.

**ENABLES:** one object that is *simultaneously* a unit of state, a unit of account,
and a unit of authority — and whose entire content is bound by one 32-byte root a
light client can check.

**CLOUD RESOURCE → the universal account / tenant / object.** A cell is the
DreggNet primitive behind *every* sellable thing: a hosted site, a database row, an
agent, a grain, a domain, a user account — each is a cell. "The unit of compute, the
unit of account, and the unit of authority are the same verified object"
(`DreggNet/docs/VISION.md §5`). The Sandstorm grain = a cell; the cap-account =
a cell.

### 0.2 The Turn — the atomic provisioning/action ⬛

**IS:** "the atomic unit of agent execution" (`turn/src/turn.rs:258`): a
`CallForest` of `Action`s, executed all-or-nothing with journaled rollback
(`turn/src/journal.rs:1`), each action gated by the kernel before commit. "The call
forest IS the transaction" (`turn/src/lib.rs:71`); authorization flows parent→child
by capability delegation. The verified Lean twin is `execFullForestG`
(`metatheory/Dregg2/Exec/FullForestAuth.lean:530`) with conservation /
non-amplification / unauthorized-fails theorems.

**ENABLES:** any state change is a transaction with cryptographic admission; a failed
turn still pays its fee and bumps its nonce (DoS-resistant,
`turn/src/executor/execute.rs:465`).

**CLOUD RESOURCE → the provisioning operation / API call / billable action.** Every
"do something on the cloud" — deploy, write, transfer, grant, scale — is a turn.
Because a turn is atomic and journaled, a multi-resource provisioning step
(create-cell + grant-cap + fund) either fully lands or fully rolls back: cloud
operations get database-transaction semantics for free.

### 0.3 The Receipt — the verifiable audit record / persistence ⬛

**IS:** a turn's verifiable witness binding the whole post-state; tampering a field
the effect did not legitimately write makes the turn unprovable (the *anti-ghost*
property, `docs/OVERVIEW.md`). `receipt_hash` (domain `dregg-receipt-v3`) binds
every field including disclosure bits `was_encrypted`/`was_burn` and the
`consumed_capabilities` witnesses, so a malicious executor cannot strip or forge
them (`turn/src/turn.rs:921`). **The receipt chain IS the persistence layer**
(`turn/src/turn.rs:6`): "the database is the cache, the receipt chain is the truth."

**ENABLES:** an append-only, self-chaining, offline-verifiable history; state is
recoverable by replay; every action leaves a provable trace.

**CLOUD RESOURCE → the audit log / billing record / event stream.** A receipt is
simultaneously the audit entry ("who did what, provably"), the billing line
(`computrons_used`), and the event payload streamed over `GET /api/events/stream`
(`node/src/events.rs:141`, the node's "nervous system"). A tenant downloads a
receipt chain and re-verifies the operator's entire conduct.

### 0.4 The Capability — the grant of real authority ⬛

**IS:** a directed edge "this cell can produce a witness the kernel accepts for
authority over that one," carrying attenuated rights. *You hold a capability iff you
can produce its witness* — never merely be named in a table; authority is
**production under non-forgeability** (`metatheory/CONSTRUCTIVE-KNOWLEDGE.md:18`,
`docs/reference/lean-authority.md`). The c-list `CapabilitySet`
(`cell/src/capability.rs:202`) commits to an openable sorted-Poseidon2 Merkle root
shared byte-identically with the circuit. Authority moves only *down* the
attenuation lattice (`is_attenuation(held, granted)`, `cell/src/capability.rs:741`).

**ENABLES:** unforgeable, attenuable, revocable, offline-witnessable delegation —
the confused-deputy-immune alternative to API keys and ACLs.

**CLOUD RESOURCE → the grant of real compute/network/storage/GPU/tool access.** A
cap is the DreggNet "lease," "API key replacement," and "IAM role" in one: a tenant
hands a CI runner a *deploy-only, one-site, time-boxed* sub-capability without
sharing the root key, and a third party witnesses exactly what was delegated
(`DreggNet/docs/VISION.md §1.3`, the `dga1_` cap-account). The firmament (§2.6)
makes a cap dispatch to a *real seL4 kernel object*, a turn, or a window
identically.

### 0.5 The Light Client — the trustless verifier ⬛

**IS:** verify ONE succinct whole-history aggregate (`WholeChainProof`) and obtain
the verdict, re-witnessing nothing (`lightclient/src/lib.rs:168`). The apex
`lightclient_unfoolable` (`metatheory/Dregg2/Circuit/CircuitSoundness.lean:453`):
`verifyBatch accept ⟹ ∃ genuine kernel transition`, `#assert_axioms`-clean. The
only open carriers are the *standard crypto floor* (FRI/STARK soundness +
Poseidon2-CR) — no dregg-specific gap.

**ENABLES:** a holder of one root knows the *entire* history was authorized,
conservative, fresh, and correctly committed — with no secrets, no replay, no trust
in any operator.

**CLOUD RESOURCE → "verify the operated result, not just the storage."** This is the
property no centralized host can offer *by construction*: a served byte, a compute
step, and a billing charge each re-witness against a committed cell anchored to a
finalized committee checkpoint (`DreggNet/docs/VISION.md §1.1`). The host cannot lie
about what it served or charged.

---

## 1. State & Memory primitives — "live persistent state"

### 1.1 The 16 fixed fields + the unbounded fields map ⬛

**IS:** `CellState.fields: [FieldElement; 16]` — the fixed user slots, like Mina's
`app_state` (`cell/src/state.rs:101`) — "unsqueezed" into an unbounded
`key → FieldElement` map (`fields_map`/`fields_root`, `cell/src/state.rs:773`) whose
root is an *openable* sorted-Poseidon2 Merkle root a light client can open
(`compute_fields_root`, `cell/src/state.rs:380`). Per-slot progressive disclosure:
`Public` / `Committed` (only `BLAKE3(value‖nonce)` public) / `SelectivelyDisclosable`
(`cell/src/state.rs:74`).

**ENABLES:** structured, selectively-private, commitment-bound record state.

**CLOUD RESOURCE → a row / document / key-value record with field-level privacy.**
The kvstore exemplar (`starbridge-apps/kvstore`) is exactly this: a verified
key-value register store. A DreggNet "database" is cells whose fields are the columns,
each independently public-or-committed.

### 1.2 Universal memory (umem) — the witnessed key→value store ⬛

**IS:** "a witnessed key→value store whose committed root is its boundary"
(`docs/reference/umem.md`, `turn/src/umem.rs`): a `(domain, key) → value` address
space + a Blum memory-checking trace + a sorted-Poseidon2 boundary root. Six domains
(`turn/src/umem.rs:99`): `Registers`(transient), `Heap`(per-cell record state, yes),
`Caps`(authority, yes), `Nullifiers`(insert-only, yes), `Index`(receipt MMR, yes),
`Working`(service scratch, transient). The keystone
`boundary_init_root_derived`/`_bound` (`UniversalMemory.lean:463,475`,
`#assert_axioms`-clean) pins a umem's init image to a committed root supplied as a
public input *and refuses a tampered declared heap* — "a umem is a value you hand off
and resume; the receiver inherits the producer's pin." `universal_memory_sound`
(`:197`) proves ONE balance certifies every domain projection — disjoint slices
cannot alias.

**ENABLES:** a portable, witnessed, composable, checkpointable memory primitive that
can be handed between parties and resumed; per-cell heaps, transient scratch,
nested umem-refs (`UVal::UmemRef`, `umem.rs:324`).

**CLOUD RESOURCE → live persistent state / a "database" / an attachable volume.** A
umem is the DreggNet *durable disk* — a portable committed heap a workload mounts,
snapshots, and hands off. Per-cell heap umem (Stage A, `PerCellUmem.lean`) is the
backing of "documents ride the heap" (`DocHeapCell`, a sovereign document bound by
one committed umem root). The `Working` domain is *RAM/scratch* — never enters the
commitment. Composable umem-refs are *mounted sub-volumes*.

### 1.3 The heap map + the eight kernel system-roots ⬛

**IS:** `heap_map`/`heap_root` is a `(collection_id, key) → FieldElement` map, the
Rust shadow of Lean `Substrate.Heap.root` (`cell/src/state.rs:409`).
`system_roots: [FieldElement; 8]` is the kernel-owned side-table roots (escrow,
queue, refcount, sturdyref, delegation, nullifier, commit, sealed-boxes) — a disjoint
namespace a `set_field` can *never* reach (`cell/src/state.rs:46`). The reuse base
`Heap.root_binds_get` (`metatheory/Dregg2/Substrate/Heap.lean:435`) — equal roots
open to equal values — backs five house capacities.

**ENABLES:** unbounded structured collections inside one cell with a single committed
root; kernel side-tables that cannot be forged from userspace.

**CLOUD RESOURCE → tables/collections inside an object; the system metadata plane.**
The heap is "indexes / nested collections"; the system-roots are the cloud control
plane the tenant can read but not write.

### 1.4 Notes & nullifiers — consume-once private state ⬛

**IS:** a `Note` (`cell/src/note.rs:44`) is a "consume-once cell with private state":
a committed `(owner, fields[8], randomness, nonce)`; spending = revealing its
`Nullifier`, creating = adding a `NoteCommitment`. Nullifiers are derived from
note-intrinsic data only (no tree position) so double-spend protection works *across
federation boundaries* (`cell/src/note.rs:10`). The `NullifierSet`
(`cell/src/nullifier_set.rs`) is an append-only set with Merkle membership +
adjacent-neighbor non-membership proofs.

**ENABLES:** linear, one-shot, privacy-preserving, federation-portable assets and
tokens; the same nullifier gate guards promise-holes, conditional turns, consent.

**CLOUD RESOURCE → bearer assets / one-time tokens / single-use vouchers / coupons.**
A note is a portable bearer instrument; the nullifier is the "this voucher was
redeemed, everywhere" gate. Bridged notes (`BridgeMint`) are cross-cloud value
transfer.

### 1.5 Continuations — suspendable/resumable running state ⬛

**IS:** "a continuation = a passable umem" (`turn/src/continuation.rs:1`): the
intermediate `UProjection` reached so far + the remaining `UmemOp` tail. A suspended
turn resumes *into the running ledger* rather than re-executing from pre-state
(`turn/src/continuation_resume.rs`); the guarantee
`resume(suspend(pre, ops)) == fold(pre, all_ops)`. The mid-forest checkpoint
(`yield_point`) is landed.

**ENABLES:** capture exactly where a computation paused, with accumulated state, hand
it off, resume from THAT point.

**CLOUD RESOURCE → forkable/snapshottable/migratable running workloads; "pay only
while awake."** This is the engine behind the Sandstorm "grain sleeps when idle,
checkpoints to its umem heap, releases the lease" cost model
(`DreggNet/docs/VISION.md §1.6`). A continuation is a *paused container image* you
can serialize, ship to another node, and resume — process migration with a witness.

### 1.6 Time-travel via the boundary ⬛

**IS:** the cockpit TIME scrubber restores a past image by an O(1) `reify_ledger`
inverse fold over a captured umem boundary (*the boundary IS the state*) instead of
genesis replay, held to anti-substitution (the reified ledger must reproduce the
recorded root tooth, else `RootMismatch`, fail-closed) — `turn/tests/umem_time_travel.rs`.

**ENABLES:** O(1) restore to any committed past state; fail-closed against tampering.

**CLOUD RESOURCE → point-in-time snapshots / instant rollback / "undo" for a live
workload.** A tenant scrubs a database/agent back to any committed instant — verifiably
the genuine past state, not a forgery.

---

## 2. Authority & Capability primitives — "grants of real resource"

### 2.1 The attenuation lattice (`AuthRequired`) ⬛

**IS:** the order on which narrowing is defined (`cell/src/permissions.rs:5`):
`None < {Signature, Proof} < Either`, `Impossible` most restrictive, `Custom{vk_hash}`
app-defined and comparable only to identical `Custom`. `attenuate_in_place` narrows
permissions, effect-mask facet, and expiry without changing slot identity and refuses
to widen on any axis (`cell/src/capability.rs:594`). The Lean keystone `attenuate_le`
(`CredentialAttenuation.lean:302`) proves the attenuated clearance is `≼` the parent
across *all axes simultaneously*; `amplification_impossible` (`:341`).

**ENABLES:** a single, proven, multi-axis "can only narrow" algebra for every grant.

**CLOUD RESOURCE → scoped/down-graded sub-grants; the IAM policy lattice.** Hand a
sub-agent a budget-and-cap that is provably a subset of yours; the *facet* (effect
mask) scopes *which operations* the grant exposes — a read-only DB cap, a deploy-only
cap, a one-method service cap.

### 2.2 Macaroons & biscuits — bearer auth tokens ⬛

**IS:** macaroons (`macaroon/`) are HMAC-SHA256 bearer tokens whose caveats can only
be appended (attenuation), with XChaCha20 third-party caveats and discharge
(`macaroon/src/macaroon.rs`). Biscuits are the public-key, *offline-attenuable*
analogue (`BiscuitGraph.lean`, `biscuit_narrows`). The wire form is `em2_`-prefixed
base64url; the Lean `CaveatChain.chain_unforgeable` reduces forgery to an HMAC break.
The convergence arrow `CaveatCapBridge.chainGateG_implies_capAuthorityG`
(`CaveatCapBridge.lean:168`) proves the macaroon narrowing forces the kernel cap gate
— one authority, four renderings.

**ENABLES:** off-chain, attenuable, third-party-dischargeable authorization tokens
that converge on the same kernel gate.

**CLOUD RESOURCE → the attenuable cap-account / shareable access token / OAuth-without-a-server.**
The `webauth` `dga1_` account is this: "no KYC, wallet = account," but the account is
an *attenuable, offline-verifiable, revocable* credential. The discharge gateway
(`macaroon/src/discharge_gateway.rs`) is a paywall/rate-limit/proof-required service.

### 2.3 Factories — transparent constructors / templates 🟦

**IS:** "EROS-style Object Factories" (`cell/src/factory.rs`): a `CellProgram` that
constrains what new cells it can create; the `FactoryDescriptor` IS the constructor
transparency — anyone can inspect exactly what caps/programs/state it installs. Fired
by `Effect::CreateCellFromFactory` (`turn/src/action.rs:1218`). Same VK in sovereign,
hosted, federated mode.

**ENABLES:** deployable, inspectable, parameterized cell templates whose installed
`CellProgram` is re-checked by the verified executor on every later turn.

**CLOUD RESOURCE → resource templates / "deploy from image" / Terraform modules / a
verifiable app catalog.** A factory is a DreggNet *blueprint*: "spin up a new
escrow-market / nameservice / vault cell from this audited template." The
`escrow-market` app is a single factory-born cell whose program IS the rules
(`starbridge-apps/escrow-market`).

### 2.4 The firmament — one cap across distance (local seL4 / turn / window) ⬛

**IS:** the cap-gradation bridge (`sel4/dregg-firmament/`): an app holds ONE
`Capability{target, rights}` and invokes/attenuates/delegates it identically whether
the target is `Local`(a CNode slot, n=1, a syscall), `Distributed`(a dregg cell, a
turn), `Surface`(a cell rendered as a window), or `HostPd`(a confined child process)
(`sel4/dregg-firmament/src/lib.rs:251`). `Bounds` carries honest distance bounds
(revocation_immediate, commit_synchronous, n); the `n=1` collapse recovers strong
local. Lean `CapGradation` proves `no_amplification`, `verbs_independent_of_n`,
`distributed_collapses_at_one`. `NotifyCap` makes async-signal a held, attenuable
authority (`NotifyAuthority.lean`).

**ENABLES:** one authority abstraction spanning a syscall, a network turn, a window,
and a sandboxed process — with the same `granted ⊆ held` gate at each.

**CLOUD RESOURCE → unified access control across the whole stack (kernel object ↔
network resource ↔ UI surface ↔ sandboxed process).** The firmament is why a DreggNet
"window," "remote object," and "OS handle" are the same grantable thing. The
`process-pd`/`process-pd-sandbox` backings (`process_kernel.rs`, Seatbelt/seccomp/
Landlock) are *real OS sandbox confinement* — the compute-tier enforcement plane.

---

## 3. Value & Economic primitives — "real economic relationships"

### 3.1 Signed-balance value + per-asset conservation (`Σδ=0`) ⬛

**IS:** `balance: i64` is **signed** — issuer wells carry `−supply` so the reachable
total is zero (`cell/src/state.rs:127`); sign discipline is by verb. The conservation
law is parametric over any commutative monoid `Bal`
(`metatheory/Dregg2/Spec/Conservation.lean`): `conservedInDomain dom deltas := Σ = 0`,
four domains conserve *independently* (`multi_domain_independent`, no "pay gas with
notes" attack), and `committed_iff_cleartext` carries it onto Pedersen commitments.
Six linearity colors (`LinearityClass`) decide per-effect which law applies; the
exhaustive `Effect::linearity` match has no default arm.

**ENABLES:** value that moves but never copies or vanishes; supply that is provably
bounded; private balances that still conserve.

**CLOUD RESOURCE → the unit of account / currency / metered credits.** This is the
billing substrate: `$DREGG` (or any asset) is a `token_id` domain; every charge is a
conserving move. "No other cloud makes the unit of compute also a unit of account"
(`DreggNet/docs/VISION.md §1.2`).

### 3.2 Transfer / Mint / Burn — the value verbs ⬛

**IS:** `Effect::Transfer{from,to,amount}` (Conservative), `Effect::Mint{target,slot,
amount}` (cap-gated supply entry, debits the issuer well, Generative),
`Effect::Burn{target,slot,amount}` (provable supply reduction, sets the receipt's
`was_burn` flag, Annihilative) (`turn/src/action.rs:1029,1342,1373`). Mint/burn must
*disclose* the broken delta in the receipt (`disclosed_non_conservation`).

**ENABLES:** payment, supply issuance, and provable destruction with mandatory
disclosure.

**CLOUD RESOURCE → billing settlement / credit top-up / credit expiry.** The lease
economy "settles each charge as a real conserving `Effect::Transfer` — exactly-once,
crash-safe, re-witnessable" (`DreggNet/docs/VISION.md §0`). Mint = provision credits;
Burn = expire them.

### 3.3 `Payable` — the cross-app value-flow standard 🟦

**IS:** "the dregg standard interface for cross-app VALUE FLOW" (`dregg-payable/`):
`pay(asset,amount,to)` / `balance(asset)`, ERC-20-shaped but built on the kernel's
`Σδ=0` layer. It is a *userspace* `InterfaceDescriptor`, not a new effect — `pay`
routes through the verified DFA router and desugars to one `Effect::Transfer`. One
source of truth, two callers: app `bounty.pay(...)` *and* the SDK's metered
tool-gateway charge.

**ENABLES:** a uniform "this cell can be paid / can pay" interface conserved across
the app boundary.

**CLOUD RESOURCE → the payments API / metered-billing rail / inter-service payment.**
`Payable` is DreggNet's Stripe-equivalent — a workload pays for its own next period,
and a tool call charges through the same conserving route.

### 3.4 Shielded transfer — confidential value ⬛/🟦

**IS:** a `ShieldedTransferPayload` (`turn/src/action.rs:996`) spends hidden input
notes and mints hidden outputs with value+owner blind, leaving only nullifiers,
output commitments, per-output Bulletproof range proofs (the inflation gate), and a
Pedersen conservation proof bound to the Fiat-Shamir transcript. The privacy payoff
theorem `committed_iff_cleartext` is proven; the range-obligation anti-inflation rib
is the named `RangeObligation` discharged by the circuit.

**ENABLES:** transfers whose amounts and parties are private yet provably conserved
and in-range.

**CLOUD RESOURCE → confidential payments / private billing / ZK-metered workloads.**
"A tenant's values, payments, and (eventually) compute can be private AND verified —
ZK hosting with no analog elsewhere" (`DreggNet/docs/VISION.md §4`).

### 3.5 The house capacities — six proven economic relationships ⬛

Six relationship-shaped capacities, each a *use of an existing proven base* (the
cap-lattice `attenuate_subset` (`metatheory/Dregg2/Exec/Caps.lean:124`) or the
committed-heap-root `Heap.root_binds_get` (`Substrate/Heap.lean:435`)), each with a
kernel-clean Lean rung + a Rust forge-detector (`invariant_matches_lean_rung`). All
**DEPLOYED**; the in-circuit (light-client) weld per capacity is the named VK-affecting
follow-up (`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`).

| Capacity | IS (one line) | Lean theorem | Rust | Cloud resource |
|---|---|---|---|---|
| **Membrane** | reshare A→B→C confers ⊆ what A held; refuses amplification | `reshare_chain_attenuates` `Membrane.lean:100` | `cell/src/membrane.rs:667` | **shared/multiplayer resource access** — invite someone into a confined fork of your world |
| **Derived** | a materialized-view cell's committed value = `f(sources)` | `DerivedCell.lean:168,235` | `cell/src/derived.rs:640` | **materialized views / cached computed columns / triggers** |
| **Sealed escrow** | atomic 2-of-2 swap, all-or-nothing, exactly once | `SealedEscrow.lean:185,303` | `cell/src/escrow_sealed.rs:1015` | **escrow / atomic swap / conditional payment / marketplace settlement** |
| **Standing obligation** | a recurring duty discharged exactly once per period, never early/skipped | `StandingObligation.lean:208,317` | `cell/src/obligation_standing.rs:1079` | **subscriptions / metered recurring billing / SLA meters** |
| **Share-vault** | minted shares = `d·S/T`; holders never diluted; ERC-4626 inflation attack rejected | `deposit_no_dilution` `Vault.lean:187,279` | `cell/src/vault.rs:1325` | **pooled funds / staking pools / shared treasuries / cap tables** |
| **Hatchery** | a user-defined KIND's invariant is enforced *forever*, attestation is real | `attested_enforces_forever` `Hatchery.lean:291` | `sdk/src/hatchery_mint.rs:635` | **verifiable smart-contract / "deploy a contract with a forever guarantee"** |

**The hatchery is special:** it IS the userspace verification product — an app author
declares an invariant in a structured shape and gets a machine-checked "holds forever,
against any adversary" theorem in the axiom-clean TCB, *no hand proof*
(`HATCHERY.md §0`, riding `livingCellA_carries`). Cloud reading: **a smart-contract
platform where the contract's safety is a theorem, not an audit.**

### 3.6 Replenishing budget / allowance — the rate-bounded meter 🟨

**IS:** a funded budget that meters *actual* consumption against a rate ceiling that
refills lazily — a runaway agent is *rate-bounded by construction*, not by a watchdog
(`DreggNet/docs/REPLENISHING-BUDGET.md`, the seL4-MCS shape over
`cell/src/allowance.rs`; the `Stingray` budget gate in the executor,
`turn/src/executor/mod.rs`). The Stingray split makes N children of one cap settle
without contending the parent.

**ENABLES:** spend authority that cannot run away; sub-agent budget delegation.

**CLOUD RESOURCE → the spend cap / rate limit / quota that an autonomous agent
physically cannot exceed.** This is the linchpin of the Verifiable Agent Cloud: "give
an agent $X and a cap; it is rate-bounded by construction."

---

## 4. Execution & Effect primitives — "the action vocabulary"

### 4.1 The 32 effects — the complete ledger-mutation vocabulary 🟦/⬛

**IS:** `Effect` (`turn/src/action.rs:1021`) is the closed enum of "what changes in
the ledger" — 32 variants, every one assigned a `LinearityClass` by an exhaustive
match. The roster: **state** (`SetField`, `IncrementNonce`, `EmitEvent`, `SetProgram`);
**value** (`Transfer`, `Mint`, `Burn`); **authority** (`GrantCapability`,
`RevokeCapability`, `AttenuateCapability`, `ExerciseViaCapability`); **lifecycle**
(`CreateCell`, `CreateCellFromFactory`, `CellSeal`, `CellUnseal`, `CellDestroy`,
`MakeSovereign`, `ReceiptArchive`, `SetPermissions`, `SetVerificationKey`);
**delegation** (`SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`);
**notes/cross-fed** (`NoteSpend`, `NoteCreate`, `BridgeMint`); **pipelining**
(`Introduce`, `PipelinedSend`); **refusal** (`Refusal`); **reactive**
(`Promise`, `Notify`, `React`).

**ENABLES:** a fixed, exhaustively-classified, light-client-witnessed action set —
new behaviors compose from these primitives, never a bespoke `Effect::FooApp`
(`starbridge-apps/README.md`: "the answer is never `Effect::FooApp`").

**CLOUD RESOURCE → the complete operations API.** This is the entire instruction set
a DreggNet workload can execute against the ledger; userspace richness is achieved by
*composition* (interfaces, programs, factories), keeping the verified TCB fixed.

### 4.2 The call forest + journal — atomic multi-resource transactions ⬛

**IS:** the `CallForest` of `CallTree`s is a Merkle transaction; the `LedgerJournal`
undo-log gives all-or-nothing atomicity without cloning the ledger (rollback even
removes inserted nullifiers so a rolled-back spend is re-spendable,
`turn/src/journal.rs:293`). Authorization flows parent→child by cap delegation.

**ENABLES:** compose many cross-cell effects into one atomic, journaled, authorized
unit.

**CLOUD RESOURCE → multi-resource atomic provisioning / saga with rollback.** Deploy
a site + bind a domain + fund the lease as ONE turn that fully commits or fully
unwinds.

### 4.3 `CellProgram` + `StateConstraint` — the on-object rule engine 🟦

**IS:** a cell carries a `CellProgram` (`cell/src/program/`) of typed
`StateConstraint`s (`FieldEquals`, `FieldLte`, `FieldLteField`, `SumEquals`,
`WriteOnce`, `Immutable`, `Monotonic`, `StrictMonotonic`, `BoundedBy`, `FieldDelta`,
…, `cell/src/program/types.rs:915`) and `TransitionGuard`s (`MethodIs`) re-checked by
the verified executor on *every* turn. A factory-born cell installs these as its
program. `Effect::SetProgram` lands a runtime re-program as an ordered turn.

**ENABLES:** declarative, executor-enforced invariants on an object's state evolution
— without a new effect or VK.

**CLOUD RESOURCE → schema constraints / business rules / row-level validation / a
state machine.** The `escrow-market` `LISTED→FUNDED→SHIPPED→SETTLED` lifecycle is a
`StrictMonotonic` constraint; a bounded credit line is `FieldLteField`. This is the
"stored procedure / DB constraint / workflow state machine" plane.

### 4.4 `Refusal` — provable non-action ⬛

**IS:** the categorical dual of acting — *evidence of absence*
(`turn/src/action.rs:1271`): a structural artifact that the prover did NOT take
`offered_action_commitment` within a window, verified via the
`WitnessedPredicateRegistry` (receipt-chain scan, bloom non-membership, or a custom
non-action AIR). Bumps the target nonce, records the refusal + reason.

**ENABLES:** non-repudiable, auditable rejection — "I received an order; I declined;
here is the proof I declined."

**CLOUD RESOURCE → auditable SLA / compliance attestation / proof-of-decline.** A
DreggNet service can prove it *did not* do something within a window (HFT-style
non-fill, "did not bid above X," compliance) — silence becomes a first-class on-chain
artifact.

### 4.5 Conditional / STARK-gated turns — proof-gated execution ⬛

**IS:** a `ConditionalTurn` (`turn/src/conditional.rs`) does not execute until a proof
satisfying its `ProofCondition` (`HashPreimage`, `RemoteProof` against an attested
foreign root, `LocalProof`, `TurnExecuted`) is presented before a timeout; otherwise
it expires with no state change. A reservation deposit is refunded on resolution,
burned on timeout. Generalizes an HTLC to *any provable statement*. Realizes
cross-federation atomicity.

**ENABLES:** "execute iff this proof arrives by height H" — escrowed, atomic,
cross-system conditional execution.

**CLOUD RESOURCE → conditional/escrowed provisioning / cross-chain atomic swap /
deferred trigger.** A workload that runs only when a payment proof / oracle proof /
peer's receipt lands.

### 4.6 Joint turns — N-cell atomic coordination ⬛

**IS:** the N-cell atomic joint turn (`turn/src/atomic.rs`, Lean `EntangledJoint`):
`jointApplyAll_dichotomy` — only full commit or untouched input, no partial;
`jointApplyAll_all_authorized` + `jointApplyAll_caps_frame` — authority cannot be
amplified by *coordinating* N turns; `jointApplyAll_conserves`. Holds at n>1 across
machines.

**ENABLES:** atomic coordination across multiple sovereign objects/parties with no
amplification.

**CLOUD RESOURCE → distributed transactions / atomic multi-party deals / cross-tenant
coordinated provisioning.**

---

## 5. Async / Reactive / Coordination primitives — "event-driven services"

### 5.1 Promises & CapTP pipelining — async eventual resources ⬛

**IS:** a pipelined send targets a promise that has *not yet resolved*; it is queued,
delivered (or cascaded broken) when the promise settles (`captp/src/pipeline.rs`).
The security invariant: *pipelining is a latency optimization, not an authority
bypass* — every delivered send is re-checked by the same verified executor
(`CapTPPipeline.drainAll_preserves_caps`, `break_freezes_state`,
`pipelining_preserves_seam`). `EventualRef` names a value a pending turn will produce
(`turn/src/eventual.rs`). Cross-federation via `CrossFedPipelineBridge`.

**ENABLES:** call a result before it exists; chain dependent calls without round-trips;
break-propagation; all without granting authority you don't hold.

**CLOUD RESOURCE → async/eventual resources / futures / promise-pipelined RPC across
regions.** A workload references a peer's not-yet-computed result and pipelines work
onto it — latency hidden, authority bounded. Cross-federation pipelining is
multi-region RPC.

### 5.2 Guarded holes — predicated late-fill ⬛

**IS:** a `GuardedHole{field,actor,target,guard}` fixes the *shape* eagerly; only the
*value* arrives late (`GuardedHole.lean:37`). `holeFill_binds_in_circuit` proves a
successful fill binds BOTH its δ and its guard (every caveat discharged, fail-closed);
`holeFill_rejects_guard_violation` is the negative tooth. The *strong* hole (an
undetermined-δ in a conservation/authority position) is deliberately inexpressible —
safe by inexpressibility.

**ENABLES:** a promise-shaped slot whose late value must satisfy a predicate to commit.

**CLOUD RESOURCE → deferred/placeholder resources with admission control.** A
provisioning slot reserved now, filled later only if the late value passes its guard.

### 5.3 The Reactor — reactive/event-driven services 🟦

**IS:** "the reactive twin of `invoke()`" (`app-framework/src/reactor.rs:1`): it
WATCHES a cell and, when an on-chain op it cares about commits, REACTS by emitting its
own turn — event-driven, not poke-driven. `filter() -> ReceiptFilter` (what it
watches) + `react(observed) -> Option<ReactionPlan>` (how it reacts); same
`InvokeAuthority` cap-gate as `invoke()`. The discord-bot is the **deployed**
exemplar: the desktop submits a real turn to an on-chain *command cell*, the bot
watches and reacts with a genuine turn (`discord-bot/src/bot_reactor.rs`, 4 tests,
live in `main.rs`).

**ENABLES:** on-chain triggers — a cell reacts to receipts on another cell, with the
reaction cap-gated and receipted.

**CLOUD RESOURCE → serverless functions / webhooks / event-driven workers /
database triggers.** A Reactor is a DreggNet *Lambda*: "when this cell changes, run
this cap-gated turn." The command-cell → reactor pattern replaces HTTP webhooks with
on-chain, verifiable triggers.

### 5.4 Affordances + `invoke()` + service interfaces — the typed service front door 🟦

**IS:** an affordance (`app-framework/src/affordance.rs`) is a *cap-gated effect
template* — "the button is a cap-gated `Effect`, and who may press it is decided by
held capabilities, not a session cookie." `authorized_for` IS the real
`is_attenuation`. `GatedAffordance` adds a live-state condition (cap ∧ state). A cell
publishes an `InterfaceDescriptor` (`cell/src/interface.rs:215`) of typed `MethodSig`s
(`Replayable` vs `Serviced`); `invoke()` (`app-framework/src/invoke.rs`) resolves the
descriptor, routes the method through the verified DFA router, cap-gates, and desugars
to ordinary effects — **no `Effect::Invoke`**, the kernel keeps seeing only effects it
enforces. The Service Explorer is the Postman-like surface.

**ENABLES:** cells as typed service objects with discoverable, cap-gated, verified
methods — and reactive twins.

**CLOUD RESOURCE → microservices / RPC endpoints / the API gateway.** A cell IS a
service; its `InterfaceDescriptor` is its OpenAPI schema; `invoke()` is the typed
client; affordances are the cap-gated UI buttons ("htmx on crack"). The node's
`/api/server/{cell}/affordances` is the public service-discovery endpoint.

---

## 6. Distributed / Multiplayer / Merge primitives — "collaborative resources"

### 6.1 The merge runtime — offchain collaborative state ⬛(laws)/🟨(circuit seam)

**IS:** "the I-confluent offchain merge/write runtime" (`dregg-merge/`): two parties
each hold their own copy of a cell, apply I-confluent ops *offchain with no
coordination*, then merge via a deterministic commutative-associative-idempotent CvRDT
`join` that converges regardless of order, *no consensus*. The confluence gate
`classify_merge` (`gate.rs`, the Rust face of `Confluence.lean`/`SemanticConvergence.lean`)
refuses the free merge for a bounded-resource invariant or a non-monotone op,
returning `Escalation::MustSettle` (settle at the boundary). Every free merge emits a
re-witnessable `MergeReceipt`. CRDT laws + the dichotomy are machine-checked
(axiom-clean, both polarities); the Lean⟷Rust in-circuit refinement is a *named seam*
for the circuit swarm.

**ENABLES:** coordination-free, partition-tolerant collaborative editing that settles
on-chain only at a real boundary (lease-close, dispute, revocation).

**CLOUD RESOURCE → collaborative/multiplayer state / CRDT documents / offline-first
sync / "globally distributed without serializing on a chain."** This is
`DreggNet/docs/VISION.md` Bet #2 — "the largest unclaimed superpower in the building":
providers/agents coordinate offchain at memory speed and anchor only when authority
crosses a boundary. A Google-Docs-style collaborative resource, verifiable.

### 6.2 Branch-and-stitch + settlement soundness — forkable multiplayer worlds ⬛

**IS:** distributed time-travel as an event-structure config lattice + RCCS
reversibility; the **Settlement Soundness theorem** is proven+axiom-clean
(`metatheory/Metatheory/SettlementSoundness.lean:153`, and the deployed compose
`Dregg2/Circuit/SettlementSoundness.lean:210`): authority must be *live at
settlement*, not branch time; a leaked-then-revoked cap cannot settle
(`leaked_then_revoked_cannot_settle`). Wired into production `stitch_pair` and LIVE
branch-and-stitch multiplayer (node-less browser fork→stitch→resolve). The document
language is the same event-structure object in VC clothes (Pijul-shaped,
conflicts-as-objects, `dregg-doc`).

**ENABLES:** fork a world/document, drive it independently, stitch divergent branches
with conflicts surfaced as first-class objects — and a settlement that fail-closes on
revoked authority.

**CLOUD RESOURCE → forkable workspaces / branch-per-feature environments / multiplayer
sessions / conflict-aware collaborative documents.** "Each coordination turn a
receipted, settlement-sound merge" (`DreggNet/docs/VISION.md §2`).

### 6.3 The membrane / shared-fork — "invite someone to my computer" ⬛/🟦

**IS:** `shared_fork.rs` hands another principal a *confined fork* of my world whose
cap-subgraph is graduated into EMBEDDED / STUDYREF(read-only) / NETWORKBOUNDARY(consent
gate) tiers. `MembraneFrustum` is a serializable, travel-able cap-bounded cell subgraph
(genuine cells, the same codec the image root commits over) with an anti-substitution
`frustum_root` tooth and fail-closed `rehydrate`. Backed by `Membrane.lean`
(`reshare_chain_attenuates`). `distributed_card` joins two principals on *different
instances* co-driving one card via a `dregg_doc` pushout.

**ENABLES:** share a bounded, confined, travel-able slice of your state with graduated
consent — and co-edit across machines.

**CLOUD RESOURCE → secure resource sharing / guest access / cross-org collaboration /
read-replicas with consent-gated writes.** The membrane is the "share this folder /
invite a collaborator / hand a contractor a scoped view" primitive — provably confined.

### 6.4 The revocation model + federation/consensus ⬛

**IS:** revocation is the *one* non-monotone operation (`Revocation.lean`):
`eventual_bounded_revocation` (revoked at origin m at τ ⟹ not honored by any node past
`τ + delay m n`); `immediate_revocation` at n=1. Finality is real
(`BlocklaceFinality.lean` twins `blocklace/src/ordering.rs::tau`); `QuorumThreshold`
= `2n/3+1`; `two_quorums_share_honest`. `FinalityCert` + `has_quorum` give the light
client its third leg (`lightclient/src/lib.rs:288`). `EpochReconfig`, `CellMigration`
(no double-existence), `ThresholdDecrypt` (t-of-n) round it out.

**ENABLES:** instant (n=1) or bounded (n>1) revocation; Byzantine-fault-tolerant
finality; cross-federation cell migration with no double-spend.

**CLOUD RESOURCE → instant access revocation / multi-operator federation / the
permissionless provider network.** "Two operators verify the same history
independently — a federation does not need a common ledger to agree"
(`DreggNet/docs/VISION.md §1.4`). Revoke an agent's authority and it darkens the
instant the revoke returns.

---

## 7. Verification & Proof primitives — "the trust dial"

### 7.1 The verification-mode lattice — the fidelity ladder 🟦

**IS:** dregg does NOT always prove (`project-verification-mode-lattice`): a fidelity
ladder — `WitnessMode::Symbolic` (deferred, snappy, `turn/src/collapse.rs:99`) →
`Full` (commitments materialized, publishable) → `WitnessBundle` (ship witness data,
verify by *re-execution / AIR-satisfaction*) → recursive proof (the buff light-client
rung, O(1) verify) → aggregated (cross-chain IVC fold). **Proving is OFF the commit
path** (`node/src/prove_pool.rs`: the executor is the soundness boundary; Full proofs
are an additive attestation layer).

**ENABLES:** pick the trust/cost/latency rung per consumer — private+snappy locally,
fully-proven publicly, recursively-folded for a light client.

**CLOUD RESOURCE → tiered trust/SLA / "verification as a service knob."** A tenant
chooses: cheap symbolic locally, full proof for a published artifact, recursive proof
for a counterparty who re-witnesses nothing. The proof distribution layer (per-node
prove pool, PG submit queue, bilateral aggregation) is the "proof CDN" greenfield.

### 7.2 The descriptor circuit + IVC whole-history fold ⬛

**IS:** a turn's execution becomes a STARK (`dregg-circuit` verify floor /
`dregg-circuit-prove` heavy surface); turns fold into one succinct constant-size
recursive whole-chain aggregate (`ivc_turn_chain.rs`, the temporal tooth: turn N's
post-root must be N+1's pre-root); a light client verifies only the root, cost
independent of K. **Lean is the source of truth** — each `circuit/descriptors/*.json`
is emitted from `Dregg2/Circuit/Emit/`, and "Rust authors NO constraints"
(`circuit/src/descriptor_ir2.rs:53`). The witnessed-predicate registry
(`Predicate.lean`, seven built-in kinds + `custom(vk)`) routes verification by kind,
fail-closed.

**ENABLES:** succinct, constant-size proof of an entire history; pluggable verified
predicates.

**CLOUD RESOURCE → the "proof of everything it did" artifact.** This is the
downloadable receipt-chain proof of the Verifiable Agent Cloud — a developer hands an
agent a budget and gets back "a proof of everything it did and a hard bound on
everything it could do" (`DreggNet/docs/VISION.md §2`).

### 7.3 The DSL — one constraint, eight backends 🟦

**IS:** `#[dregg_caveat]`/`#[dregg_effect]`/`#[dregg_circuit]` compile one constraint
into eight backends — Rust oracle, AIR, Datalog, Kimchi, Plonky3, compile-time STARK,
Midnight ZKIR, SP1 guest (`dregg-dsl/`); five form a cross-checked agreement set with
the Rust evaluator as oracle (`dregg-dsl-differential`).

**ENABLES:** author a verified predicate once, get it across every proof system; the
substrate's portability layer.

**CLOUD RESOURCE → cross-platform / cross-chain verified logic / "write once, prove
anywhere."** A constraint authored for a DreggNet cell also emits a Midnight ZKIR
program and an SP1 guest — the bridge to other verifiable platforms.

---

## 8. Persistence, Recovery & Hosting primitives — "durable infrastructure"

### 8.1 The receipt chain + redb commit log — crash-safe durability ⬛/🟦

**IS:** the receipt chain IS persistence (§0.3); the node's ONE durable store is redb
(`dregg-persist`), with a single-transaction `commit_finalized_turn` writing record +
cursor + index atomically, so across an arbitrary crash there is no torn state, no
lost finalized turn, no double-apply (`persist/src/commit_log.rs:29`). The
`recover = checkpoint ⊕ overlay` model is verified (`CrashRecovery.recover_eq_replay`,
order/cut-independent). `recover_to_last_consistent` salvages a torn image.
Forever-digests are restart-durable anti-replay.

**ENABLES:** crash-consistent durable state recoverable from the canonical stream;
fast startup from checkpoints; provable recovery.

**CLOUD RESOURCE → durable storage / crash-resume execution / the managed database.**
DreggNet's `durable/` crash-resume execution rides this; the "database is the cache,
the receipt chain is the truth" is the managed-storage guarantee.

### 8.2 Sovereign mode — client-held state, server-held commitment ⬛

**IS:** `CellMode::Sovereign` (the default) — the federation stores only a 32-byte
state commitment and the agent provides full state each turn; the proof-carrying
sovereign fast path does ZERO state interpretation, just verifies the STARK and
updates one commitment (`turn/src/executor/execute.rs:493`). `MakeSovereign` migrates
a hosted cell.

**ENABLES:** the operator holds no plaintext, only a commitment; the client is the
source of truth and proves transitions.

**CLOUD RESOURCE → client-side / zero-knowledge hosting / "the host stores a hash."**
A maximally-trust-minimized tier: the operator cannot read or lose your data because
it only holds your commitment.

### 8.3 The deos-host + node API — the served runtime 🟦

**IS:** the node (`dregg-node`) serves a localhost HTTP/WS API (turn submit ingress,
receipt SSE stream, affordance discovery) and can host a headless userspace deos-js
"private server" — a JS program holding state in real cells and offering cap-gated
affordances clients fire (`node/src/deos_host.rs`). `mud_client`/`shared_world` are
playable engines; the cockpit is just one client. The Lean shadow makes the verified
Lean executor authoritative on covered turns (`node/src/executor_setup.rs:120`).

**ENABLES:** a running, served, multi-tenant world where every fired affordance is a
verified turn.

**CLOUD RESOURCE → the application server / PaaS runtime / hosted multiplayer
backend.** The deos-host is DreggNet's "deploy a server and clients connect" —
`shared_world` (two identities co-inhabiting one world) is the multiplayer backend
rung.

---

## 9. Interface & OS primitives — "the inhabited cloud"

### 9.1 Surfaces + the verified compositor — windows as caps ⬛

**IS:** a surface is a window; authority over it is a real firmament capability
(`starbridge-v2/src/surface.rs`). The compositor enforces three scene-authority teeth
(`compositor.rs`, Lean `Dregg2.Apps.Compositor`): T1 non-overlap (`granted ⊆ held` at
the pixel layer), T2 label-binding (the shell computes the label, never the app), T3
focus-exclusivity. `present` commits IFF every tooth admits — output integrity *is*
unfoolability one hop out (`output_integrity_eq_unfoolability_on_scene`).

**ENABLES:** a UI where the human at the glass cannot be fooled — no overpaint, no
label-spoof, no focus-steal.

**CLOUD RESOURCE → trustless remote desktop / verifiable UI / the rendered surface as
a grantable resource.** A "window" is a cap over a cell; sharing a window is a narrowed
cap (`Shell::share` refuses widening). The deos cockpit served as a DreggNet surface
is "the cloud you do not just deploy to, but inhabit" (`DreggNet/docs/VISION.md §4`).

### 9.2 Sessions / login = receiving your root capability ⬛

**IS:** "login = receiving your root capability · a session = the cap-tree you hold ·
logout = revoking it" (`starbridge-v2/src/session.rs:11`). A session is not an object
kept in sync with the ledger — it IS a c-list. Each step is a real receipted turn;
logout revokes each slot (synchronous+transitive at n=1). Sessions are durable.

**ENABLES:** auth with no session store, no token DB — the session is the capability
tree.

**CLOUD RESOURCE → identity / SSO / session management with instant revocation.** No
session database to breach; revoke and the whole cap-tree darkens instantly.

### 9.3 Sandstorm grain = cell, powerbox = cap 🟨

**IS:** the Sandstorm-grains-as-cells prototype (`DreggNet/sandstorm-bridge/`,
`docs/SANDSTORM-INTEGRATION-PLAN.md`): a grain = a cell, the powerbox = a provable cap
delegation, the sandbox = a DreggNet compute tier. Prototype green (manifest parser +
grain lifecycle + powerbox ceremony); the `.spk` reader + descriptor↔`Pred` matcher +
http-bridge shim is the build.

**ENABLES:** run hundreds of existing `.spk` apps (Etherpad, Wekan, Gitea, …)
dregg-native, metered, served trustlessly, with provable cross-app delegation.

**CLOUD RESOURCE → the verifiable app store / app marketplace.** "An agent-native
object-capability cloud with Sandstorm's app catalog and dregg's proofs" — and where
*agents acquire tools* (a catalog app is a cap an agent is granted through the same
provable powerbox) (`DreggNet/docs/VISION.md §3`).

---

## 10. The consolidated toolbox → cloud-resource map

| dregg primitive | Cloud resource it becomes | Status |
|---|---|---|
| Cell (4 substances) | universal account / tenant / object | ⬛ |
| Turn | provisioning operation / API call / billable action | ⬛ |
| Receipt + chain | audit log / billing record / event stream / persistence | ⬛ |
| Capability | grant of compute/network/GPU/storage/tool access | ⬛ |
| Light client | "verify the operated result, not just storage" | ⬛ |
| 16 fields / fields-map | row / document / KV record (field-level privacy) | ⬛ |
| umem (witnessed heap) | live persistent state / database / attachable volume | ⬛ |
| heap map / system roots | tables-in-object / control plane | ⬛ |
| Notes / nullifiers | bearer assets / one-time tokens / vouchers | ⬛ |
| Continuations | forkable/snapshottable/migratable workloads; pay-while-awake | ⬛ |
| Time-travel boundary | point-in-time snapshot / instant rollback | 🟦 |
| Attenuation lattice + facets | scoped sub-grants / IAM policy | ⬛ |
| Macaroons / biscuits | attenuable cap-account / access token | ⬛ |
| Factories | resource templates / "deploy from image" / app catalog | 🟦 |
| Firmament cap-gradation | unified access control across the stack | ⬛ |
| Process-PD sandbox | real OS sandbox / compute-tier enforcement | 🟦 |
| Signed balance + Σδ=0 | unit of account / currency / metered credits | ⬛ |
| Transfer / Mint / Burn | billing settlement / top-up / expiry | ⬛ |
| Payable | payments API / metered billing rail | 🟦 |
| Shielded transfer | confidential payments / ZK-metered workloads | ⬛/🟦 |
| Sealed escrow | escrow / atomic swap / marketplace settlement | ⬛ |
| Standing obligation | subscriptions / recurring billing / SLA meter | ⬛ |
| Share-vault | pooled funds / staking / shared treasury / cap table | ⬛ |
| Derived cell | materialized view / cached column / trigger | ⬛ |
| Hatchery | verifiable smart contract ("forever guarantee") | ⬛ |
| Replenishing budget | spend cap / rate limit an agent can't exceed | 🟨 |
| 32 effects | the complete operations API | 🟦/⬛ |
| Call forest + journal | atomic multi-resource provisioning / saga | ⬛ |
| CellProgram / StateConstraint | schema constraints / business rules / state machine | 🟦 |
| Refusal | auditable SLA / compliance / proof-of-decline | ⬛ |
| Conditional / STARK-gated turn | conditional provisioning / atomic swap / trigger | ⬛ |
| Joint turn | distributed transaction / multi-party atomic deal | ⬛ |
| Promises / CapTP pipelining | async/eventual resources / futures / cross-region RPC | ⬛ |
| Guarded holes | deferred resources with admission control | ⬛ |
| Reactor | serverless functions / webhooks / DB triggers | 🟦 |
| Affordances / invoke / interfaces | microservices / RPC / API gateway | 🟦 |
| Merge runtime | collaborative/multiplayer state / CRDT docs / offline-first | ⬛/🟨 |
| Branch-and-stitch + settlement | forkable workspaces / branch envs / multiplayer | ⬛ |
| Membrane / shared-fork | secure resource sharing / guest access / read-replica | ⬛/🟦 |
| Revocation + federation | instant revocation / multi-operator network | ⬛ |
| Verification-mode lattice | tiered trust/SLA / verification-as-a-knob | 🟦 |
| Descriptor circuit + IVC | "proof of everything it did" | ⬛ |
| DSL (8 backends) | cross-platform verified logic / prove-anywhere | 🟦 |
| Receipt chain + redb | durable storage / crash-resume / managed DB | ⬛/🟦 |
| Sovereign mode | client-side / ZK hosting ("host stores a hash") | ⬛ |
| deos-host + node API | application server / PaaS / multiplayer backend | 🟦 |
| Surfaces + compositor | trustless remote desktop / verifiable UI | ⬛ |
| Sessions / login-as-cap | identity / SSO / instant-revoke sessions | ⬛ |
| Sandstorm grain=cell | verifiable app store / marketplace | 🟨 |

---

## 11. The non-myopic reading — what this toolbox actually is

The myopic reading of dregg is "a verified blockchain that can host a static site."
The toolbox above says something larger: **dregg supplies, as proven or deployed
primitives, the entire vocabulary of a cloud** — accounts, objects, databases,
volumes, snapshots, currencies, billing, payments, escrow, subscriptions, pooled
funds, IAM, access tokens, sandboxes, the operations API, atomic transactions,
serverless triggers, microservices, async RPC, collaborative documents, multiplayer
sessions, federation, identity, remote desktop, and an app store — **with one property
none of them have elsewhere: every one re-witnesses against a committed root on a
light-client-unfoolable rail, so the host cannot lie about what it stored, served,
charged, or authorized.**

The three things that are uniquely dregg's, that no other cloud can assemble
(`DreggNet/docs/VISION.md`):

1. **The unit of compute, account, and authority are the same verified object** — a
   workload transacts, pays, holds caps, and proves it stayed in its box.
2. **Coordination is mostly-offchain** (the merge runtime) — globally distributed
   without serializing on a chain, anchoring only when authority crosses a boundary.
3. **Authority is bounded and audited cryptographically and inline** — the Verifiable
   Agent Cloud: give an agent a budget and a cap, get a proof of everything it did and
   a hard bound on everything it could do.

Every entry above names the primitive it stands on. Build the cloud from the whole
toolbox, not the corner of it.

---

*Foundation document. Read for the SHAPE; verify `file:line` / theorem / LIVE-status
against HEAD before betting on a specific primitive. The grounded what-is for the
substrate is `breadstuffs/docs/reference/`; the proof inventory is
`breadstuffs/metatheory/CLAIMS.md`; the operated-layer vision is
`DreggNet/docs/VISION.md`.*
