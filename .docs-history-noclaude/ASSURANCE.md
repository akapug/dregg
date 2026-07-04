# dregg ASSURANCE — the authoritative assurance specification

This is the single document a reviewer reads to know **exactly what dregg
guarantees, under what assumptions, and what is staged rather than cut over.**
It is the rigorous companion to [EVALUATION.md](EVALUATION.md) (the "should I
trust it" human page): where EVALUATION.md explains the case in prose for a
newcomer, this file is the precise contract — every guarantee in exact terms,
the exact crypto floor by carrier name, the deployment-correspondence at
file:line, and the proof discipline that keeps it honest.

The **machine-checked anchor** is
[`metatheory/Dregg2/AssuranceCase.lean`](../metatheory/Dregg2/AssuranceCase.lean):
the five guarantees as theorem-DAGs, each apex `#assert_axioms`-clean. This
document and that file are kept in lockstep — if they disagree, the Lean file
wins (it is checked; prose is not).

---

## 1. The five guarantees (precise terms)

dregg states its case as five top-level guarantees to a light client. Each is a
theorem (or a thin aggregation of theorems) in `AssuranceCase.lean`.

### A — Authority
*Every state change is justified by an unforgeable, non-amplified, fresh token
chain: no effect confers more authority than was held.*

- The headline is over the REAL `List Auth` attenuation lattice: an
  introduction's conferred capability is a genuine non-amplifying SUBSET of the
  held capability (`introduce_non_amplifying`), AND the predicate DISCRIMINATES —
  a grant conferring authority the holder lacks is rejected
  (`amplifying_grant_rejected`). The gate is two-valued, not `:= True`.
- Every authority-conferring mouth is covered individually (introduce, delegate
  with attenuation, attenuate/refresh, revoke, exercise, setPermissions, stored
  caps in slots, cell birth) and PRODUCTION authority (mint) is gated on holding
  the issuer cell's capability — a constructive production law, never a
  recipient-shaped grant. There is no other cap-conferring constructor; the wire
  enum is reconciled against `Substrate.VerbRegistry.classify`, exhaustive by the
  compiler.
- The WHO leg (`credentialValid`) is the §3/§4 floor carrier (ed25519/HMAC),
  entering as a typeclass portal; the gate's soundness is conditional on it, as
  stated.

Apex: `AssuranceCase.authority_guarantee`. Running-entry instance: see §4.

### B — Conservation
*Per asset, the resource sum is identically ZERO — on every reachable state.*

Under the value unification `AssetId := CellId`, every asset IS its issuer cell;
the issuer's own balance row (the WELL) carries −supply, and mint/burn/bridgeMint
are ordinary moves against the negative-capable well. No verb moves any asset's
sum (`ledgerDeltaAsset_eq_zero` — the per-verb delta family vanishes
identically). So the guarantee is `∀ a, Σ_c bal c a = 0` on every state
reachable from a value-empty genesis — exactness, unconditionally, with NO
zero-net side condition and NO disclosed-non-conservation exemption.

Apex: `AssuranceCase.conservation_guarantee` (the reachable-zero invariant) +
`conservation_guarantee_step` (the per-move face: Σ invariant per asset, no
cross-asset leakage). Floor: NONE beyond integer arithmetic.

### C — Integrity
*A receipt binds the WHOLE post-state; a tampered input is rejected.*

The state commitment is determined by, and recovers, EVERY state field, so a turn
that tampers a field the effect did not legitimately touch is rejected (the
"anti-ghost" property). Three legs:

- **The receipt binds.** `argus_commits_to_one_receipt` — a committed Argus term
  commits exactly one receipt, determined by the post-state; the circuit-side and
  executor-side receipts AGREE (`argus_circuit_executor_receipts_agree`).
- **The commitment binds the whole state, with teeth.**
  `CommitmentCrossBind.runnable_binds_same_system_roots` (equal seam roots ⇒ equal
  full state) + `chC_bad_not_bridge` (a field-dropping commitment is NOT a
  faithful bridge — the binding is non-vacuous).
- **The executor IS a memory program** (the universal-map bridge, landed). The
  total projection `uproj` of the executor's post-state — all 17 kernel fields +
  the receipt log onto ONE domain-tagged address space — EQUALS the fold of the
  verb's emitted Blum trace over the pre-state projection
  (`gwrite/move/create_is_memory_program`, against the live executable steps).
  This makes "binds the whole post-state" a constructive fact: every field has a
  universal address; nothing is left off the address space.

Apex aggregation: `AssuranceCase.integrity_guarantee_memory_program` (over the
live `recCexec` move). The substantive cross-bind apex is re-pinned under the
heading (its long frame signature is not restated). Floor: Poseidon2-CR.

### D — Freshness
*No replay / double-spend; a committed spend's nullifier was fresh; revocation at
finality.*

- **In the term, not an out-of-band side table.** If the noteSpend term commits,
  the spent nullifier was NOT already in the set (`noteSpendStmt_no_double_spend`);
  a second spend of the same nullifier fails closed (`noteSpendStmt_then_reject`);
  a present nullifier is rejected (`noteSpendStmt_replay_rejected` — two-valued).
- **Whole-set freshness with a circuit gate.** `NonMembership.nonmembership_sound`/
  `_complete` — `nf ∉ set` is a sorted-tree non-membership opening, not "in-memory
  only".
- **Revocation is consensus-bound.** `Liveness.revocation_needs_consensus` —
  immediate AT finality, the negative-lifecycle dual of consensus-free GC.
- **Stored caps cannot outlive revocation.** The R7 retrieval-epoch rule
  (`CapSlotFactory.{stored_cap_only_fresh_if_epoch_unrevoked, revoke_stales_stored_cap,
  store_then_revoke_refused}`) covers the entire surviving storage surface (the
  seal/swiss/sturdyref verb family is gone from the kernel post-F3).

Apex: `AssuranceCase.freshness_guarantee`. Floor: Poseidon2-CR + PostGSTProgress
(for revocation-at-finality).

### E — Unfoolability
*A light client verifying a Q-chain learns A–D for the WHOLE history while
re-witnessing nothing; a tampered aggregate cannot bind.*

Checking ONLY `verify agg.root` ⇒ every turn executed correctly, correctly
ordered, the final root a genuine fold
(`RecursiveAggregation.light_client_verifies_whole_history`); the whole attested
history conserves (`attested_history_conserves`); a reordered chain forces
`ChainBound = False` so no verifying aggregate exists
(`tampered_aggregate_cannot_bind`, `leaf_pairing_defeats_swap`). The IVC fold
model (`HistoryAggregation.wellformed_attests_whole_history`) and the Argus-strand
realization (`Argus.Aggregate.argus_strand_light_client`) close the loop on the
executable term IR.

Apex (heading anchor): `AssuranceCase.unfoolability_guarantee`; the substantive
apex + anti-ghost teeth are re-pinned under the heading. Floor: FRI/STARK
soundness + Poseidon2-CR + ed25519 + PostGSTProgress.

---

## 2. The crypto floor (the entire trust boundary)

The guarantees are unconditional in the Lean-kernel sense *modulo* a small,
explicit set of cryptographic assumptions. **Every one enters as a typed `Prop`
hypothesis / typeclass field — never as an `axiom`** (so it does not appear in
`collectAxioms`; the kernel triple `{propext, Classical.choice, Quot.sound}` is
the only thing the apexes rest on beyond these). This is the system's complete
trust boundary; nothing else is load-bearing.

| # | Assumption | Named carrier(s) | Used by |
|---|---|---|---|
| 1 | Poseidon2-permutation collision-resistance | `Circuit.Poseidon2Binding.Poseidon2SpongeCR`; reduced into `Crypto.SpongeReduction`, `recStateCommit`/`cellCommit`/`stateCommit` injectivity portals, `Lightclient.MMR.mroot_binds_position`, `Apps.QueueRoot.RootCR` / `LenBindCR`, `Apps.PreRotation.KeySetCR` | C, D, E (and the MMR receipt-index discharge) |
| 2 | BLAKE3 collision-resistance | `Crypto.CommitmentBinding.Blake3Kernel` / `Blake3Commitment` | out-of-circuit content/transcript hash |
| 3 | ed25519 EUF-CMA | `CryptoKernel.verify` / `Credential.verify` (the `AuthPortal`) | A (turn/strand signatures) |
| 4 | HMAC (PRF/MAC) unforgeability | `Authority.CaveatChain.MacKernel` | A (macaroon caveat-chain tags) |
| 5 | AEAD confidentiality+integrity | the seal/disclosure payload portals | sealed values, channel ciphertext |
| 6 | discrete-log hardness | `Crypto.Pedersen` | committed values (Pedersen) |
| 7 | FRI / STARK soundness | `Circuit.RecursiveAggregation.EngineSound.recursive_sound` (the ONE recursion obligation) | E (a verifying proof attests its statement) |
| 8 | BLS aggregate-signature unforgeability | `Distributed.BlsQuorumCert` (quorum certs) | finality certs, the multi-node path |
| 9 | post-GST synchrony | `World.gst_liveness` / `PostGSTProgress` (DLS88/HotStuff pacemaker) | D (revocation-at-finality), E (finalized chains) |

There is **no trusted executor, no out-of-band "this turn was authorized"
premise, and no post-state field left uncommitted.** Per-leg ZK floor: each Argus
effect's circuit term rests on item 1 (in-circuit openings) plus, where it spends,
item 7 (the proof attests its statement).

---

## 3. Deployment correspondence — where the running node sits vs the theorems

The guarantees are kernel-unconditional modulo §2. Between the verified surface
and the deployed node there are exactly the seams below. **A seam the case does
not name is a seam the case launders** — so each is stated with its location and
its honest status. The authoritative copy is the "Named boundary seams" and "THE
ROTATION correspondence" sections of `AssuranceCase.lean`.

### 3a. The running entry — A∧B∧C hold over what the node actually runs
The node's state producer is the verified Lean `execFullForestG` (the body behind
the `dregg_exec_full_forest_auth` FFI; `dregg-lean-ffi/`). `running_entry_sound`
proves, in ONE statement over THAT function: conservation (W1-strengthened, no
zero-net hypothesis), no amplification on every delegation edge, and per-node
credential+caveat attestation — with fail-closed teeth
(`execFullForestG_unauthorized_fails`). The proofs are about the running system
because the running system calls the proved function.

### 3b. Conservation deployment caveats — DISCHARGED (this epoch)
The two conservation caveats that genesis seeding and legacy fees previously
punched are **closed on the deployed chain** (they rode the commitment `v5 → v6`
bump):

- **Signed wells.** `dregg_cell::CellState.balance` is `i64`, encoded at every
  commitment/wire boundary as the biased two-limb LE encoding (`balance_limbs` /
  `encode_balance_le`), matching the Lean kernel that already ran signed wells.
- **Genesis is issuer-moves.** `node::genesis::GenesisMove` replays from an issuer
  well seeded `−total_issued`; no balance is conjured (`node/src/genesis.rs`).
- **Fees are moves, not burns.** `TurnExecutor::fee_well_cell` /
  `set_fee_well_cell` route the fee remainder to a fee well starting at zero
  (`turn/src/executor/finalize.rs`, "fees as moves").

So guarantee B holds over the deployed chain, not only the abstract kernel.

### 3c. The three host-side seams (named, not Lean hypotheses)
1. **The prover partition.** The Lean-emitted descriptor prover
   (`EffectVmDescriptorAir`) is the default for the 17 graduated turn shapes
   (`sdk/src/full_turn_proof.rs::CUTOVER_READY_SELECTORS`). Every other shape falls
   back — LOGGED, never silent — to the hand-written AIR
   (`circuit/src/effect_vm_p3_full_air.rs`), which enforces the same PI bindings
   and is adversarially tested but is NOT Lean-derived: for non-graduated shapes,
   circuit⟺kernel agreement is test-attested, not theorem-attested. The graduation
   lane empties the fallback set.
2. **Host-fed admission inputs** (`turn/src/lean_shadow.rs::ShadowHostCtx`):
   `block_height`, the migration `frozen` set, the agent's `stored_head`, the silo
   `budget`, `intro_lifetime`. The theorems say: IF these are the node's true
   values THEN admission is decided correctly and fail-closed. Their fidelity is a
   host obligation outside the Lean statement — engineering-shaped, not
   cryptography-shaped. A host lying to itself harms only admission, never the A–C
   invariants (proven over whatever state the executor actually runs on).
3. **Producer coverage.** By default the verified executor is authoritative for
   the swap-safe covered set (`lean_shadow::producer_root_agreeing_effects`);
   shapes outside it run on the legacy Rust executor with the Lean verdict as a
   differential/veto. The honest partition (mappable = root-agreeing ∪ root-gap)
   burns down toward total coverage.

### 3d. Staged, not cut over — THE ROTATION
The rotation (the descriptor IR-v2 flag-day, `docs/EPOCH-DESIGN.md` /
`docs/ROTATION-CUTOVER.md`) is the one VK/commitment epoch that lands the
remaining circuit relayout together: registers 8→16, the `heap_root` register +
PI v3, the RESERVED-column deletion + selector compaction, the IR-v2 regeneration.
The IR-v2 interpreter is authored and feature-gated (`recursion`); it does NOT yet
sit on the live proving path (which still rides the v1 registry). What this means
for assurance **today**:

- **The heap is kernel-bound and scheme-pinned, but not yet circuit-committed.**
  A heap write is attested by the kernel theorems
  (`heapStepGuardedW_honest`, `heapRoot_binds_write`) against the deployed
  `circuit::heap_root` scheme, not yet by the per-turn proof. The gadget forces
  the address/leaf images in-row; the deployed EffectVM row does not yet carry a
  `heap_root` register of its own (Phase-E lane).
- **The executor-state bridge is LANDED** (`Exec.UniversalBridge`): `uproj` +
  `gwrite/move/create_is_memory_program` are the verified surface the rotation will
  bind in-circuit per turn. The receipt-index domain rides the same MMR
  (`index_boundary_mroot_derived`), which is exactly the index that already
  DISCHARGES the §149 Receipt PI-binding hypothesis (`argus_published_index_pins_receipt`).

The full rotation rider list is the HORIZONLOG "Rides THE ROTATION" section.

### 3e. Low-severity residuals (named)
- The MCP gateway binds biscuit-cap temporal caveats to attested height
  (`node/src/mcp.rs`) but consults NO revocation registry for MCP-issued caps; an
  MCP cap dies by expiry caveat, not explicit revocation, until a revocation feed
  is wired. Outside guarantee D's statement.
- The EffectVM layout still carries the F3-retired field-seal `RESERVED` column;
  no live verb can set a sealed bit (selectors pinned to zero), but it is not
  absorbed into the in-circuit state commitment. Deleted at the rotation relayout.

---

## 4. The proof discipline — the LIVING assurance mechanism (the #93 answer)

dregg's assurance is not a one-time audit; it is enforced continuously by a
discipline that runs on every change. **This is the recommended successor to the
"build a proof-audit harness" question (#93): the discipline below IS the harness,
and it is already running.**

Three mechanisms, layered:

1. **`#assert_axioms` (per-keystone kernel hygiene).** Every keystone the corpus
   advertises is pinned to the kernel triple `{propext, Classical.choice,
   Quot.sound}` plus the §2 carriers (which, entering as typeclass parameters /
   hypotheses, do not appear in `collectAxioms`). The five guarantee apexes and
   their direct-DAG keystones are pinned in `AssuranceCase.lean`; the comprehensive
   corpus-wide net (~190 pins) lives in `Dregg2.Claims`. A keystone that silently
   acquires an open hole or an `axiom` fails its pin — the build goes red.

2. **Non-vacuity, both polarities.** A guarantee proved over a `:= True`
   predicate is broken even if it type-checks. So every load-bearing predicate is
   shown to DISCRIMINATE: the teeth theorems witness the FALSE side
   (`amplifying_grant_rejected`, `chC_bad_not_bridge`, `noteSpendStmt_replay_rejected`,
   `IssuerMove.recKMintAsset_breaks_exact`, …), and concrete `#guard`s exercise both
   the satisfied and the refused case (e.g. the universal-bridge three-verb run is
   `#guard`-folded address-by-address; a tampered MMR root does NOT open). A
   predicate that cannot be made false is not a guarantee.

3. **The Convergence gauntlet.** Periodic whole-tree convergence rounds catch what
   narrow per-module verification structurally cannot — feature unification,
   cross-crate match-arm coverage, the textual whole-corpus proof-hole grep
   (the metatheory hygiene script in `scripts/`, named for the hole-token it forbids), and the Rust↔Lean differential harnesses
   that pin the deployed code against the model.

Recommendation (HORIZONLOG "Decisions pending"): **declare this triple the
proof-audit successor and close #93.** A separate bespoke audit harness would
duplicate `#assert_axioms` (kernel hygiene), `#guard`/teeth (non-vacuity), and the
gauntlet (whole-tree coherence) — the three things a proof audit checks — while
adding a second surface to keep in sync. The discipline is checked by `lake build`
on every change; an audit document is not.

---

## 5. Reading order

- **This file** — the precise contract (what / under what / staged-what).
- [`AssuranceCase.lean`](../metatheory/Dregg2/AssuranceCase.lean) — the
  machine-checked anchor: five guarantee DAGs, each apex `#assert_axioms`-clean.
  If prose and Lean disagree, the Lean wins.
- [`Dregg2.Claims`](../metatheory/Dregg2/Claims.lean) — the corpus-wide
  per-keystone CI pin-net (~190 pins), subordinate to `AssuranceCase`.
- [EVALUATION.md](EVALUATION.md) — the human "should I trust it" page + the
  first-ten-minutes path.
- [HORIZONLOG.md](../HORIZONLOG.md) — the live burn-down of every named follow-up
  (the rotation riders, the graduation lane, the producer-coverage burn-down).
