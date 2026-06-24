# Orphaned-Capabilities Census — the weld-target map

A whole-tree honest census (read-only) of capabilities that are **built + tested
(some proven) but NOT reached by production/live code** — the orphans the swarm
should weld next. The discipline throughout: **verify the source.** For each
candidate the test is concrete — does PRODUCTION/LIVE code reach it, or only its
own `#[cfg(test)]` / a demo / a parallel Lean tower?

Three classes:

- **ALIVE-WIRED** — a live `Effect`/executor/circuit path, a live node service, a
  served endpoint, the live refinement chain (`metatheory/Dregg2.lean`), or a
  shipping binary (cli/node/starbridge-v2/wasm) reaches it in non-test code.
- **ORPHANED** — built + tested (maybe proven), but the ONLY things reaching it
  are its own tests, `lib.rs` re-exports, a demo, an SDK-API surface no live
  binary drives, or a parallel proof tower the live root never imports. *This is
  the weld target.*
- **ASPIRATIONAL-SKETCH** — a stub / named-open gap. Honestly NOT an orphan; do
  not inflate it into one.

The tree root is `/Users/ember/dev/breadstuffs` (the Rust workspace). The Lean
trunk lives under `metatheory/`. Paths below are relative to the tree root unless
noted.

> Already-named orphans (NOT re-counted here): Intent's coarse disconnections,
> the DA/Reed-Solomon mesh with 0 callers, the node god-struct, branch-and-stitch
> over docs-not-turns, the un-turn-as-doc-merge. This census surfaces the ones
> **not yet named**.

---

## Headline

**~38 genuinely-orphaned capabilities** across six clusters (excluding the
already-named ones), plus a clean line drawn under what is NOT an orphan (most of
`turn/`, the lightclient verify core, the seL4 5-PD assembly, sdk/captp/coord/
bridge/blocklace which live binaries DO reach).

### Top weld targets (ranked by value × smallness-of-stitch)

1. **Lean `Polis` + `Metatheory.DreggPolis`/`PolisNonConfusion` welds** — 66+23
   files, **0 sorry**, kernel-clean, fully proven — but the live root
   `metatheory/Dregg2.lean` never imports them. The two weld modules ALREADY
   bridge to real dregg theorems; they are just not pulled into the root. **Weld
   = 2 `import` lines** to pull the constitution + non-confusion floor into the
   CI-enforced live chain. Highest soundness-per-keystroke in the tree.
   *(metatheory/Polis/, metatheory/Metatheory/)*

2. **cell/ `vault.rs` + `escrow_sealed.rs` + `obligation_standing.rs` +
   `derived.rs` + `membrane.rs` (the house prototypes)** — each is a complete,
   forge-tested capability (timelock vault, atomic 2-of-2 escrow, recurring
   obligation, relational/derived cells, authority-meet membrane) reachable only
   from its own `#[cfg(test)]` + a `cell/src/lib.rs` re-export. **Weld each = one
   `Effect` variant + one executor `apply_*` arm + (for soundness) one circuit
   descriptor.** These are the highest *wonder*-per-weld — they make an agent
   able to LIVE inside dregg (own money over time, escrow, standing duties).

3. **Federation crypto floors orphaned from live consensus: `threshold.rs`
   (BLS QC), `vrf.rs` (sortition), `beacon.rs` (randomness beacon).** Live node
   finality uses **Ed25519 distinct-signer quorum** (`finalization_votes.rs`),
   NOT threshold BLS; the BLS/VRF/beacon path is reached only by an
   **unexercised `sdk/` API surface** (`hints_onboarding`, `sealed_governance`,
   `beacon_cell`) that no live binary drives. **Weld = wire the QC verify into
   the finality gate / wire sortition into jury selection.** Medium stitch, high
   soundness payoff (constant-size BFT certs instead of O(n) signer sets).

4. **seL4 `net-client` (the signed-turn TCP ingress).** Compiles, DHCP-acquires,
   Ed25519-verifies a `SignedTurn` envelope on TCP:5555 — but is **not a PD in
   the `dregg.system` assembly**: no Microkit channel connects NIC→client→
   executor. The 5-PD assembly already drives net-driver + executor; net-client
   is the missing ingress hop. **Weld = add a 6th PD + 2 channels to the .system
   file.** Small stitch; turns the booting firmament into a network-reachable OS.

5. **intent/ `lowering.rs` + `bond.rs` (the trustless settlement back-half).**
   The encrypted-intent endpoint IS served (`node/api.rs:4438`
   `submit_encrypted` → `TrustlessIntentEngine`), but the engine's
   challenge-window + bond-slashing + four-layer lowering (Intent→EffectPlan→
   SealedTurn→Turn) are exercised only by intent's own tests — the live API
   handler accepts the intent but never drives the lowering/bond path to a real
   executor turn. **Weld = call the lowering pipeline from the live handler.**

---

## Cluster 1 — `cell/src/*.rs` (the "house" prototypes + more)

The 2026-06-22 memory said the 8 Track-2 "capacities" are Rust sketches with
smoke tests, NOT wired (only reactive `Effect::{Promise,Notify,React}` is live).
**Verified STILL TRUE at HEAD**, and the disconnection is WIDER than the named 4:
**11 cell modules** are reached only by their own tests + `cell/src/lib.rs`
re-exports.

| Module | Class | file | what it DOES | live caller | smallest weld |
|---|---|---|---|---|---|
| `vault.rs` | **ORPHANED** | cell/src/vault.rs | timelock vault: value locked until release condition, claim-once | none (tests + lib.rs only) | `Effect::VaultClaim` + executor arm + timelock/condition circuit descriptor (~M) |
| `escrow_sealed.rs` | **ORPHANED** | cell/src/escrow_sealed.rs | atomic 2-of-2 value swap; one-shot settle, replay-rejected | none | `Effect::EscrowSettle` + apply arm + settlement-proof descriptor (~M) |
| `obligation_standing.rs` | **ORPHANED** | cell/src/obligation_standing.rs | "owe AMOUNT every PERIOD to BENEFICIARY"; one-shot per-period cursor | none | `Effect::ObligationDischarge` + apply arm + per-period nonce gate (~M) |
| `derived.rs` | **ORPHANED** | cell/src/derived.rs | relational cell: committed value MUST equal f(sources) (Sum/Count/FilteredSum) | none | `Effect::VerifyDerived` + derivation-proof verify in executor (~M) |
| `membrane.rs` | **ORPHANED** | cell/src/membrane.rs | authority composes UPWARD through a meet; require-both, non-amp tooth | none | `Effect::ComposeMembrane` + apply arm (~M) |
| `allowance.rs` | **ORPHANED** | cell/src/allowance.rs | rate-limited per-epoch spending ceiling | none | `Effect::SpendAllowance` + per-epoch ceiling gate (~S) |
| `blueprint.rs` | **ORPHANED** | cell/src/blueprint.rs | settlement-cell blueprints (bridge/escrow/obligation) UTXO-style factory templates | demos only | `Effect::DeployBlueprint` + factory instantiation (~L; underlies vault/escrow) |
| `custom_effect.rs` | **ORPHANED** | cell/src/custom_effect.rs | per-app custom-effect verifier registry | none (registry built only in tests) | wire `CustomEffectRegistry` into executor + `Effect::Custom` dispatch (~M) |
| `ring_closure.rs` | **ORPHANED** | cell/src/ring_closure.rs | ring-closure (coequalizer) attestation; N-party transfer binding | none | wire `RingClosureAttestation` into the transfer coequalizer proof path (~M) |
| `unilateral.rs` | **ORPHANED** | cell/src/unilateral.rs | 1-arity self-binding attestation (γ.2 sibling of bilateral) | none | wire into `bilateral_schedule` / reactive peer-exchange (~S) |
| `vk_v2.rs` | **ORPHANED** | cell/src/vk_v2.rs | layered VK commitment (program/predicate/effect verifier hashes) | none (setup/offline only) | bind `vk_v2` commitment into `SetProgram`/`SetVerificationKey` authorization (~S) |

**ALIVE-WIRED (the live cell spine, for contrast):** capability, facet, factory,
lifecycle, ledger, migration, note, nullifier_set, permissions, preconditions,
predicate, program/, delegation, revocation_channel — every one dispatched from
the live `turn/` executor (`turn/src/executor/apply.rs`).

> The honest pattern: these 11 are **PROTOTYPES that captured the invariant + the
> forge-shape** (memory's correct framing). They are not debt to prune — they are
> the design input for the verified-integration version. The weld is a
> Lean-effect + descriptor + apex rung, not a Rust rewrite.

---

## Cluster 2 — `intent/src/*.rs`

The live intent spine IS served: `node/api.rs` drives `validation`, `trustless`
(`submit_encrypted` at :4438), `pir`, `sse`, `fulfillment`, `matcher` (wasm),
`delay_pool` (`node/state.rs:325`), `verified_gate`/`verified_settle` (via
`exec-lean`). Orphaned beyond the already-named coarse disconnections:

| Module | Class | file | what it DOES | live caller | smallest weld |
|---|---|---|---|---|---|
| `lowering.rs` | **ORPHANED** | intent/src/lowering.rs | 4-layer tower Intent→EffectPlan→SealedTurn→Turn | only `trustless.rs` internal; trustless's live API path never reaches the lowering/executor leg | call `seal_plan_uniform` from the live `submit_encrypted` handler (~M) |
| `bond.rs` | **ORPHANED** | intent/src/bond.rs | solver bond escrow + slashing (BoundedBy slot invariant) | only `trustless.rs` error-catching; never triggered by the node | drive bond-lock/slash from the live challenge-window (~M) |
| `state_machine.rs` | **ORPHANED** | intent/src/state_machine.rs | canonical intent lifecycle schema (Pending→…→Settled/Expired) | none (zero imports) | enforce transitions in a cell-program slot-caveat (~M; waits on slot-caveat layer) |
| `gossip_filter.rs` | **ORPHANED** | intent/src/gossip_filter.rs | DFA-mediated gossip topic filtering | none (zero imports) | wire `GossipTopicFilter` into `node/gossip.rs` broadcast (~S) |
| `predicate.rs` | **ORPHANED** | intent/src/predicate.rs | intent-layer adapters to WitnessedPredicate (ResourceDfa/Temporal) | only `solver.rs:170`; solver itself is test-only-reached | reach `solver` from a live matching handler (~M) |
| `agent_mandate.rs` | **ORPHANED (test-only)** | intent/src/agent_mandate.rs | Lean-differential delegation-chain / caveat trees | only `intent/tests/agent_mandate_lean_differential.rs` | a differential — keep as test, or lift to a live mandate effect (~M) |

---

## Cluster 3 — `turn/src/*.rs` (advanced effects + the un-turn)

**Every live `Effect` variant in `turn/src/action.rs` IS dispatched** by the
executor (`turn/src/executor/apply.rs` `apply_effect` exhaustive match) — there
are **no orphaned live Effects.** The orphans here are *carriers/algebras built
beside the executor that the executor never enters*, and utilities only tests
construct. (A sub-agent over-generously labelled these "ALIVE-UTILITY" — the
honest test is "does live non-test code outside `turn/` reach it?")

| Module | Class | file | what it DOES | live caller (verified) | smallest weld |
|---|---|---|---|---|---|
| `reversible.rs` | **PARTIAL** | turn/src/reversible.rs | un-turn / RCCS inverse algebra (`Effect::invert`, ReversibleHistory) | **cockpit-alive**: `starbridge-v2/src/history_lens.rs`, `time_travel.rs` drive `Inversion`/undo as a UI feature — but **NO live `Effect` triggers a reverse turn in the protocol**; the inverse is a UI/audit algebra, not a kernel verb | to make reversal a *protocol* capability: an `Effect::Reverse` the executor + circuit witness (~L). As a cockpit feature it is already alive. |
| `presence_discharge.rs` | **ORPHANED** | turn/src/presence_discharge.rs | presence-attestation discharge for caveats | none outside turn/ (tests only) | wire `PresenceCaveat` into the live caveat-verification gate (~M) |
| `cross_fed_cite.rs` | **ORPHANED** | turn/src/cross_fed_cite.rs | cross-federation receipt citation utility | none outside turn/ (tests only) | call from the federation receipt-lift path (~S) |
| `binding_proof.rs` | **ORPHANED** | turn/src/binding_proof.rs | Effect-VM binding-proof structures (effect dependency) | constructed empty (`effect_binding_proofs: Vec::new()`) in starbridge/teasting — never populated | populate + verify binding proofs for proof-carrying sovereign effects (~M) |
| `script.rs` | **PARTIAL** | turn/src/script.rs | recorded turn-sequence macros (Tier-1) | **cockpit-alive**: `starbridge-v2/src/cockpit/nav.rs:383` records a macro | Tier-2 (Custom-VK compilation of a script) is the orphaned half (~M) |
| `composer.rs` | **ORPHANED** | turn/src/composer.rs | offline multi-party turn composition builder | demo-agent only | reach from a live multi-party signing flow (~M) |
| `encrypted.rs` | **ASPIRATIONAL** | turn/src/encrypted.rs | privacy-preserving turn ordering; `TurnValidityProof` | structure built; validity-proof verify gated off (`#[cfg(feature="prover")]`) | enable prover-side validity verify (~M) — NOT an orphan, a feature-gated gap |
| `witnessed_receipt.rs` | **ALIVE** | turn/src/witnessed_receipt.rs | witnessed receipt chains | `verifier/src/bilateral_pair.rs:45` (live) | — |

**ALIVE-WIRED:** eventual/conditional/pending (the reactive `Promise/Notify/
React` substrate — executor dispatches all three), journal, rotation_witness,
umem, collapse, economics, budget_gate, fast_path, bilateral_schedule,
aggregate_bilateral_prover (all reached by executor/circuit/node).

---

## Cluster 4 — federation crypto floors + node "organ services"

### Federation crypto floors

Live node finality uses **Ed25519 distinct-signer quorum**
(`node/src/finalization_votes.rs` — `supermajority(n)` distinct signers), NOT
threshold BLS. The BLS/VRF/beacon floors are real + tested but reached only by an
**`sdk/` API surface no live binary drives**:

| Capability | Class | file | what it DOES | reached by | smallest weld |
|---|---|---|---|---|---|
| `threshold.rs` (BLS QC) | **ORPHANED** | federation/src/threshold.rs | weighted-threshold BLS12-381 quorum certs (constant-size) | `sdk/hints_onboarding`, `dfa/federation_verifier` — NOT node finality | wire `FederationCommittee::verify_quorum` into the finality gate, replacing the O(n) Ed25519 signer set (~M) |
| `vrf.rs` | **ORPHANED** | federation/src/vrf.rs | RFC-9381 ECVRF sortition for jury selection | `sdk/identity` (comment only) | wire `sortition_select` into the beacon jury draw (~M) |
| `beacon.rs` | **ORPHANED** | federation/src/beacon.rs | threshold-BLS randomness beacon + deterministic jury | `sdk/sealed_governance`, `sdk/beacon_cell` (sdk-only, no live driver) | instantiate `BeaconCommittee` from a DKG output + call `beacon_at` in a live lottery (~M) |
| `threshold_decrypt.rs` | **ORPHANED** | federation/src/threshold_decrypt.rs | Shamir t-of-n threshold decryption (GF(256)) | tests only — NOTE: `intent/trustless` has its OWN threshold-encrypt that IS served via `submit_encrypted`; this federation copy is the orphan | DKG-distributed epoch keys + wire into validator decryption-share path (~L) |
| `dkg.rs` / `dkg_ceremony.rs` | **ORPHANED** | federation/src/dkg.rs | Feldman/JF-DKG + proactive resharing | `node/dkg_service` routes exist but the dealer/ceremony flow is never triggered | activate the DKG ceremony endpoint + enable dealer role in genesis (~L) |
| `*_diff.rs` (bls_quorum, epoch, checkpoint_prune, threshold_decrypt) | **TEST-ONLY DIFFERENTIAL** | federation/src/*_diff.rs | Lean-model ⟺ Rust forge-detectors | `#[cfg(test)]` only | by design test-only — NOT a weld target (the byte-identity-differential lesson: a round-trip, not a live capability) |

**ALIVE (live consensus/court stack):** court, admission, revocation, epoch,
checkpoint, cross_fed_bundle, solo — all driven by node startup
(`node/src/executor_setup.rs`, `node/src/state.rs`, `node/src/main.rs`).

### Node organ services — CORRECTION to a prior read

A prior pass claimed channels/trustline/storage/dkg services are "never spawned."
**That is wrong.** Verified at HEAD:

- They ARE instantiated as live `NodeState` fields
  (`node/src/state.rs:361–378`, built at :673–1023 in NON-test construction).
- Their routes ARE merged into the live router
  (`node/src/api.rs:1762–1775`: `trustline_service::routes()`,
  `channels_service::routes()`, `equivocation_court_service::routes()`,
  `dkg_service::routes()`).

So channels / trustline / storage_gateway / equivocation-court are **ALIVE
(served HTTP endpoints over live registries)**. The genuine gap is narrower: the
**DKG ceremony has routes + a registry but no dealer/round flow ever runs**
(orphaned *behavior* inside an alive service), and several services lack a
background crank (request-driven only). `prove_pool` (spawned `main.rs:538`) and
`relay_service` (opt-in daemon `main.rs:1106`) are alive background tasks.

---

## Cluster 5 — Lean parallel towers (`metatheory/Polis/`, `metatheory/Metatheory/`)

The live soundness root `metatheory/Dregg2.lean` imports the privacy layer
(`Dregg2.Privacy` line 30, `Dregg2.PrivacyKernel` line 38, `Dregg2.Privacy.
Metadata` line 39) and the live settlement keystone
(`Dregg2.Circuit.SettlementSoundness` line 659). **The privacy layer is
ALIVE-WIRED** (consumed at the Lean level by the cell-execution refinement).

Two whole `lean_lib` targets BUILD (`lakefile.toml` `defaultTargets =
["Dregg2","Metatheory","Polis"]`) but the `Dregg2` library **never imports
them** — they are **ORPHANED PROVEN TOWERS**, kernel-clean, **0 sorry**:

| Tower | Class | location | what it PROVES | imported by live root? | weld |
|---|---|---|---|---|---|
| `Polis/*` (66 files, 0 sorry) | **ORPHANED-TOWER** | metatheory/Polis/ | the constitution-as-theorem: `polis_safety` (∀ opaque controller), least-restrictive envelope, amendment non-regression, the sandbox governor games | NO | — (a proof artifact; the welds below pull it in) |
| `Metatheory.DreggPolis` | **ORPHANED-TOWER (bridge ready)** | metatheory/Polis/DreggPolis.lean | instantiates Polis on REAL dregg substrate (EpistemicDial law + `Authority.Auth` 8 l4v rights) | NO — but it imports Dregg2 components | **add `import Metatheory.DreggPolis` to Dregg2.lean (1 line)** |
| `Metatheory.PolisNonConfusion` | **ORPHANED-TOWER (bridge ready)** | metatheory/Polis/PolisNonConfusion.lean | pins 5 already-deployed non-amplification theorems as a constitutional floor | NO — but it re-pins live Dregg2 theorems | **add `import Metatheory.PolisNonConfusion` to Dregg2.lean (1 line)** |
| `Metatheory.SettlementSoundness` | **ORPHANED-TOWER** | metatheory/Metatheory/SettlementSoundness.lean | authority-live-at-settlement (a parallel study; the LIVE keystone is the separate `Dregg2.Circuit.SettlementSoundness`) | NO | pin `BindsLiveAuthority` onto the live settlement verifier, or reconcile with the wired `Dregg2.Circuit` version (~M) |
| `Metatheory.{SafetyGame,ReachGame,EnergyGame}` | **ORPHANED-TOWER** | metatheory/Metatheory/ | viability kernel / reachability attractor / graded budget games | NO | instantiate `EnergyGame` on a real gated-spending app (~M) |
| `Metatheory.{CommonSecret,ResharingChain}` | **ORPHANED-TOWER** | metatheory/Metatheory/ | threshold distributed knowledge / forward-secure committee secrets (D-side KERI dual) | NO | needs a deployment vehicle (a cell-stored-secret app) — closer to aspirational |
| `Metatheory.KeyLeak` | **ORPHANED-TOWER** | metatheory/Metatheory/KeyLeak.lean | leaked-key attacker as opaque controller; blast-radius = attenuation-closure | NO | wire as a threat-model module bridging Revocation + Polis (~M) |

> Honest note: these are **NOT aspirational** — they typecheck, 0 sorry,
> kernel-clean. They are disconnected proof artifacts. The `DreggPolis` /
> `PolisNonConfusion` welds are a **2-line import** to make the constitution +
> non-confusion floor part of the CI-enforced live chain — the single
> highest-leverage stitch in the tree.

---

## Cluster 6 — seL4 / firmament (`sel4/`) + lightclient

### seL4 — the 5-PD assembly is ALIVE; specific PDs are boots-but-not-driven

The `make run-assembly` 5-PD firmament (net-driver + verifier-stark + executor +
persist + rbg-dir) genuinely boots and is driven: real STARK verify with
anti-ghost teeth, NIC up, interactive graphics (`deos-tutorial`, `deos-image`
keyboard-IRQ-driven). The verified executor (`executor-microkit-pd`) embeds the
proved `dregg_exec_full_forest_auth` and self-stages a demo turn. Orphans:

| Capability | Class | file | what it does / why orphaned | smallest weld |
|---|---|---|---|---|
| `net-client` (signed-turn TCP ingress) | **BUILT-NOT-DRIVEN** | sel4/dregg-pd/net-client/src/main.rs | compiles, DHCP, Ed25519-verifies a `SignedTurn` on TCP:5555 — but is NOT a PD in `dregg.system`; no channel connects NIC→client→executor | add a 6th PD + 2 Microkit channels to the .system file (~S) |
| `persist-stub` → real persist | **BUILT-NOT-DRIVEN** | sel4/dregg-pd/persist-stub/src/main.rs | holds the storage seat (cap proven live) but persists nothing — awaits the block-device cap | wire storage-device cap + redb-on-bare-block (~M) |
| `executor-pd` (Lean-ELF status heart) | **ASPIRATIONAL** | sel4/dregg-pd/executor-pd/src/main.rs | the real Lean-ELF executor PD; BLOCKED: leanrt/leancpp ship Mach-O-only, won't cross-compile to aarch64-musl. `executor-stub`/`executor-microkit-pd` occupy the seat | port the Lean ELF runtime (the named wall) (~L) |
| `render-pd` (lavapipe) | **BUILT-NOT-DRIVEN** | sel4/render-pd/src/main.rs | boots, creates a lavapipe VkInstance in-VM; W→X JIT path wired — stalls one rung past device creation (`__clone` returns -ENOSYS, no real TCB) | implement `__clone` in sel4-musl (service TCB creation) (~M) |

### lightclient — the verify core is ALIVE; the trust-anchor distribution is the gap

| Capability | Class | file | status | weld |
|---|---|---|---|---|
| `verify_history` / `verify_finalized_history` / `fold_and_attest` | **ALIVE-WIRED** | lightclient/src/lib.rs | served via `sdk/src/lib.rs` re-export, wasm bindings (`wasm/src/bindings_lightclient.rs`), and the demo binary; recursive-STARK verify, VK-anchor pin, quorum check; non-vacuous tests with rejection teeth | — |
| RecursionVk trust-anchor **distribution** | **ASPIRATIONAL** | lightclient/src/lib.rs:33–42 (named) | verify functions exist; there is NO production genesis/checkpoint channel that ships the anchor to a light client (tests self-anchor) | build the anchor-distribution harness (node-side config / anchor server) (~M) |
| leaf-public re-exposure (fork follow-ups a+b) | **ASPIRATIONAL** | lightclient/src/lib.rs:49–52 (Lean names it) | a named in-band-pinning gap, mitigated by anchoring + tamper-rejection tests | pull the circuit fork lever threading `table_public_inputs` (~M) |

---

## What is NOT an orphan (line drawn honestly)

To avoid inflation:

- **sdk/, captp, coord, bridge, blocklace** — all reached by live node binaries
  (`node/src/` references each in non-test code; sdk has 94 node references).
- **The whole live cell spine + every live `Effect`** — dispatched by the
  executor.
- **The lightclient verify core, the privacy Lean layer, the live
  `Dregg2.Circuit.SettlementSoundness`** — wired.
- **The seL4 5-PD assembly + interactive graphics** — driven.
- **The `*_diff.rs` Lean differentials** — correctly test-only by design (a
  round-trip witness, not a live capability; the byte-identity lesson).
- **node organ services (channels/trustline/storage/court)** — ALIVE (registries
  in NodeState, routes merged); only the DKG ceremony *behavior* is orphaned.
- **`encrypted.rs`, the lightclient anchor + fork levers, the Lean
  CommonSecret/ResharingChain** — ASPIRATIONAL/named-gaps, not orphans.

---

## Prioritized weld queue (value × smallness)

| # | Weld | size | payoff |
|---|---|---|---|
| 1 | 2-line `import` of `Metatheory.DreggPolis` + `PolisNonConfusion` into `Dregg2.lean` | XS | constitution + non-confusion floor become CI-enforced live theorems |
| 2 | seL4 `net-client` → add 6th PD + 2 channels to `dregg.system` | S | the booting firmament becomes network-reachable (signed turns over TCP) |
| 3 | cell `allowance` / `vault` → `Effect` + apply arm (+ descriptor) | S–M | an agent can hold rate-limited + timelocked money inside dregg |
| 4 | cell `escrow_sealed` / `obligation_standing` / `derived` / `membrane` → effect+arm+descriptor | M each | atomic swap, standing duties, derived views, authority membranes — the house |
| 5 | federation `threshold` BLS QC → wire into the finality gate | M | constant-size BFT certs replace the O(n) Ed25519 signer set |
| 6 | intent `lowering`+`bond` → drive from the live `submit_encrypted` handler | M | the trustless settlement back-half goes live end-to-end |
| 7 | federation `vrf`+`beacon` → wire sortition + beacon into jury selection | M | verifiable randomness / jury draws become live |
| 8 | seL4 `render-pd` `__clone`, `persist` block cap, `executor-pd` Lean-ELF | M–L | graphics / durable storage / verified-compute heart complete the firmament |

Every row is a **wire**, not a **build** — the capability already exists and is
tested; the stitch is to make the living protocol reach it.
