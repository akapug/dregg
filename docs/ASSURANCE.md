# dregg ASSURANCE — the authoritative assurance specification

This is the single document a reviewer reads to know **exactly what dregg
guarantees, under what assumptions, and what is staged rather than cut over.** It
is the precise contract: every guarantee in exact terms, the crypto floor by
carrier name, the deployment-correspondence seams, and the proof discipline that
keeps it honest. The human "should I trust it" companion is
[docs/TRUST-LEVELS.md](TRUST-LEVELS.md) and the newcomer path is
[docs/OVERVIEW.md](OVERVIEW.md).

The **machine-checked anchor** is
[`AssuranceCase.lean`](../metatheory/Dregg2/AssuranceCase.lean): the five
guarantees as theorem-DAGs, each apex `#assert_axioms`-clean. This document and
that file are kept in lockstep — if they disagree, the Lean file wins (it is
checked; prose is not).

---

## 1. The five guarantees (precise terms)

dregg states its case as five top-level guarantees to a light client. Each is a
theorem (or a thin aggregation of theorems) in `AssuranceCase.lean`.

### A — Authority
*Every state change is justified by an unforgeable, non-amplified, fresh token
chain: no effect confers more authority than was held.*

The headline is over the real `List Auth` attenuation lattice: an introduction's
conferred capability is a genuine non-amplifying SUBSET of the held capability
(`introduce_non_amplifying`), and the predicate DISCRIMINATES — a grant conferring
authority the holder lacks is rejected (`amplifying_grant_rejected`). Every
authority-conferring mouth is covered individually (introduce, delegate with
attenuation, attenuate/refresh, revoke, exercise, setPermissions, stored caps in
slots, cell birth), and production authority (mint) is gated on holding the issuer
cell's capability. The WHO leg (`credentialValid`) is the §2 floor carrier
(ed25519/HMAC), entering as a typeclass portal.

Apex: `AssuranceCase.authority_guarantee`.

### B — Conservation
*Per asset, the resource sum is identically ZERO — on every reachable state.*

Under the value unification `AssetId := CellId`, every asset IS its issuer cell;
the issuer's own balance row (the WELL) carries −supply, and mint/burn/bridgeMint
are ordinary moves against the negative-capable well. No verb moves any asset's sum
(`ledgerDeltaAsset_eq_zero`). So the guarantee is `∀ a, Σ_c bal c a = 0` on every
state reachable from a value-empty genesis — exactness, unconditionally, with no
zero-net side condition and no disclosed-non-conservation exemption.

Apex: `AssuranceCase.conservation_guarantee` + `conservation_guarantee_step`.
Floor: none beyond integer arithmetic.

### C — Integrity
*A receipt binds the WHOLE post-state; a tampered input is rejected.*

The state commitment is determined by, and recovers, every state field, so a turn
that tampers a field the effect did not legitimately touch is rejected (the
"anti-ghost" property). The receipt binds (`argus_commits_to_one_receipt`; the
circuit-side and executor-side receipts agree,
`argus_circuit_executor_receipts_agree`); the commitment binds the whole state with
teeth (`runnable_binds_same_system_roots` + `chC_bad_not_bridge`, so a
field-dropping commitment is not a faithful bridge); and the executor IS a memory
program — the total projection of the post-state (all kernel fields + the receipt
log onto one domain-tagged address space) equals the fold of the verb's emitted
trace over the pre-state projection (`Exec.UniversalBridge`).

Apex: `AssuranceCase.integrity_guarantee_memory_program`. Floor: Poseidon2-CR.

### D — Freshness
*No replay / double-spend; a committed spend's nullifier was fresh; revocation at
finality.*

If the noteSpend term commits, the spent nullifier was NOT already in the set
(`noteSpendStmt_no_double_spend`); a replay fails closed
(`noteSpendStmt_replay_rejected`, two-valued). Whole-set freshness is a sorted-tree
non-membership opening (`NonMembership.nonmembership_sound` / `_complete`), not
"in-memory only". Revocation is consensus-bound
(`Liveness.revocation_needs_consensus`) — immediate at finality — and stored caps
cannot outlive revocation (the retrieval-epoch rule on `CapSlotFactory`).

Apex: `AssuranceCase.freshness_guarantee`. Floor: Poseidon2-CR + post-GST progress.

### E — Unfoolability
*A light client verifying a Q-chain learns A–D for the WHOLE history while
re-witnessing nothing; a tampered aggregate cannot bind.*

Checking ONLY `verify agg.root` ⇒ every turn executed correctly, correctly ordered,
the final root a genuine fold
(`RecursiveAggregation.light_client_verifies_whole_history`); the whole attested
history conserves (`attested_history_conserves`); a reordered chain forces
`ChainBound = False` so no verifying aggregate exists
(`tampered_aggregate_cannot_bind`, `leaf_pairing_defeats_swap`).

Apex: `AssuranceCase.unfoolability_guarantee`. Floor: FRI/STARK soundness +
Poseidon2-CR + ed25519 + post-GST progress.

---

## 2. The crypto floor (the entire trust boundary)

The guarantees are unconditional in the Lean-kernel sense *modulo* a small,
explicit set of cryptographic assumptions. **Every one enters as a typed `Prop`
hypothesis / typeclass field — never as an `axiom`** (so it does not appear in
`collectAxioms`; the kernel triple `{propext, Classical.choice, Quot.sound}` is the
only thing the apexes rest on beyond these). This is the system's complete trust
boundary; nothing else is load-bearing.

| # | Assumption | Named carrier | Used by |
|---|---|---|---|
| 1 | Poseidon2-permutation collision-resistance | `Circuit.Poseidon2Binding.Poseidon2SpongeCR` | C, D, E |
| 2 | BLAKE3 collision-resistance | `Crypto.CommitmentBinding.Blake3Kernel` | out-of-circuit content/transcript hash |
| 3 | ed25519 EUF-CMA | `CryptoKernel.verify` (the `AuthPortal`) | A (turn/strand signatures) |
| 4 | HMAC (PRF/MAC) unforgeability | `Authority.CaveatChain.MacKernel` | A (macaroon caveat-chain tags) |
| 5 | AEAD confidentiality + integrity | the seal/disclosure payload portals | sealed values, channel ciphertext |
| 6 | discrete-log hardness | `Crypto.Pedersen` | committed values (Pedersen) |
| 7 | FRI / STARK soundness | `Circuit.RecursiveAggregation.EngineSound.recursive_sound` | E (a verifying proof attests its statement) |
| 8 | BLS aggregate-signature unforgeability | `Distributed.BlsQuorumCert` | finality certs, the multi-node path |
| 9 | post-GST synchrony | `World.gst_liveness` / `PostGSTProgress` | D (revocation-at-finality), E (finalized chains) |

There is **no trusted executor, no out-of-band "this turn was authorized" premise,
and no post-state field left uncommitted.**

---

## 3. Deployment correspondence — where the running node sits vs the theorems

The guarantees are kernel-unconditional modulo §2. Between the verified surface and
the deployed node there are exactly the seams below. **A seam the case does not
name is a seam the case launders** — so each is stated with its location and its
honest status. The authoritative copy is the "Named boundary seams" section of
`AssuranceCase.lean`.

### 3a. The running entry — A∧B∧C hold over what the node actually runs
The node's state producer is the verified Lean `execFullForestG` (the body behind
the `dregg_exec_full_forest_auth` FFI in `dregg-lean-ffi/`). `running_entry_sound`
proves, in one statement over that function: conservation (no zero-net hypothesis),
no amplification on every delegation edge, and per-node credential + caveat
attestation — with fail-closed teeth (`execFullForestG_unauthorized_fails`). The
proofs are about the running system because the running system calls the proved
function.

### 3b. Conservation deployment — DISCHARGED
The conservation caveats that genesis seeding and legacy fees previously punched are
closed on the deployed chain: balances are signed wells (`i64`, biased two-limb LE
at every commitment/wire boundary); genesis is issuer-moves from a well seeded
`−total_issued` (`node/src/genesis.rs`); and fees are moves to a fee well starting
at zero, not burns (`turn/src/executor/finalize.rs`). Guarantee B holds over the
deployed chain, not only the abstract kernel.

### 3c. The three host-side seams (named, not Lean hypotheses)
1. **The prover partition.** The Lean-emitted descriptor prover is the default for
   the graduated turn shapes (`sdk/src/full_turn_proof.rs`). Every other shape falls
   back — logged, never silent — to the hand-written AIR (`circuit/src/effect_vm/air.rs`),
   which enforces the same PI bindings and is adversarially tested but is not
   Lean-derived: for non-graduated shapes, circuit⟺kernel agreement is
   test-attested, not theorem-attested. The graduation lane empties the fallback set.
2. **Host-fed admission inputs** (`exec-lean/src/lean_shadow.rs`): block height, the
   migration frozen set, the agent's stored head, the silo budget, intro lifetime.
   The theorems say: IF these are the node's true values THEN admission is decided
   correctly and fail-closed. Their fidelity is a host obligation outside the Lean
   statement — engineering-shaped, not cryptography-shaped. A host lying to itself
   harms only admission, never the A–C invariants.
3. **Producer coverage.** By default the verified executor is authoritative for the
   swap-safe covered set; shapes outside it run on the legacy Rust executor with the
   Lean verdict as a differential/veto. The honest partition burns down toward total
   coverage.

### 3d. Staged, not cut over — THE ROTATION
The rotation is the one VK/commitment epoch that lands the remaining circuit
relayout together: registers 8→16, the `heap_root` register + PI v3, the
RESERVED-column deletion + selector compaction, the IR-v2 regeneration. The IR-v2
interpreter is authored and feature-gated; it does not yet sit on the live proving
path. What this means today: the heap is kernel-bound and scheme-pinned
(`heapRoot_binds_write`) but not yet per-turn circuit-committed, and the
executor-state bridge is landed (`Exec.UniversalBridge`) as the verified surface the
rotation binds in-circuit per turn. The full rider list is the HORIZONLOG "Rides THE
ROTATION" section.

### 3e. Low-severity residuals (named)
- The MCP gateway (`node/src/mcp/mod.rs`) binds biscuit-cap temporal caveats to
  attested height but consults no revocation registry for MCP-issued caps; such a
  cap dies by expiry caveat, not explicit revocation, until a revocation feed is
  wired. Outside guarantee D's statement.
- The EffectVM layout still carries the retired field-seal RESERVED column; no live
  verb can set a sealed bit (selectors pinned to zero), but it is not absorbed into
  the in-circuit state commitment. Deleted at the rotation relayout.

---

## 4. The proof discipline — the living assurance mechanism

dregg's assurance is not a one-time audit; it is enforced continuously by a
discipline that runs on every change. Three mechanisms, layered:

1. **`#assert_axioms` (per-keystone kernel hygiene).** Every keystone is pinned to
   the kernel triple `{propext, Classical.choice, Quot.sound}` plus the §2 carriers
   (which, entering as typeclass parameters, do not appear in `collectAxioms`). The
   five guarantee apexes are pinned in `AssuranceCase.lean`; the corpus-wide net
   lives in [`Dregg2.Claims`](../metatheory/Dregg2/Claims.lean). A keystone that
   silently acquires an open hole or an `axiom` fails its pin — the build goes red.

2. **Non-vacuity, both polarities.** A guarantee proved over a `:= True` predicate
   is broken even if it type-checks. So every load-bearing predicate is shown to
   DISCRIMINATE: the teeth theorems witness the FALSE side
   (`amplifying_grant_rejected`, `chC_bad_not_bridge`, `noteSpendStmt_replay_rejected`,
   …), and concrete `#guard`s exercise both the satisfied and the refused case. A
   predicate that cannot be made false is not a guarantee.

3. **The convergence gauntlet.** Periodic whole-tree convergence rounds catch what
   narrow per-module verification structurally cannot — feature unification,
   cross-crate match-arm coverage, the whole-corpus proof-hole grep, and the
   Rust↔Lean differential harnesses that pin the deployed code against the model.

The discipline is checked by `lake build` on every change; an audit document is not.

---

## 5. Reading order

- **This file** — the precise contract (what / under what / staged-what).
- [`AssuranceCase.lean`](../metatheory/Dregg2/AssuranceCase.lean) — the
  machine-checked anchor: five guarantee DAGs, each apex `#assert_axioms`-clean.
  If prose and Lean disagree, the Lean wins.
- [`Dregg2.Claims`](../metatheory/Dregg2/Claims.lean) — the corpus-wide
  per-keystone CI pin-net, subordinate to `AssuranceCase`.
- [docs/TRUST-LEVELS.md](TRUST-LEVELS.md) — the human "should I trust it" page.
- [HORIZONLOG.md](../HORIZONLOG.md) — the live burn-down of every named follow-up.
