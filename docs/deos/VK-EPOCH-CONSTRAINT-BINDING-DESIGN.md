# Constraint-binding: making a declared capacity caveat un-omittable

This is the design for the **soundness core** of the three house-capacity in-circuit welds
(`SettleEscrow`/`DischargeObligation`/`VaultDeposit`, tags 17/18/19). The §6 weld rungs
(`SealedEscrow.lean`, `StandingObligation.lean`, `Vault.lean`) and their Rust shadows
(`circuit/src/effect_vm/verify.rs` tag arms) prove that **if** a capacity manifest entry is
present, its re-evaluation **forces** the capacity invariant (atomicity / on-schedule / no-dilution).
This document closes the gap they leave: **that the entry must be present at all.**

## 1. The gap — the manifest is prover-chosen

The slot-caveat manifest rides public inputs; `verify_slot_caveat_manifest` iterates the prover-
published `count` entries and re-evaluates each. That is the **satisfaction** half: every entry that
IS present must hold. But the producer (`project_slot_caveat_manifest`) and the count are chosen by
the prover, so a forger settling a half-open escrow simply **omits** the tag-17 entry (publishes
`count = 0`, or a manifest with no tag-17 entry). The verifier then has nothing to re-evaluate and
accepts. The §6 gate is **prover-optional** — present it and it bites; drop it and it is silent. This
is the load-bearing soundness gap.

Two further facts about the current state (verified against HEAD):

* `verify_full_turn_bound` (`sdk/src/full_turn_proof.rs`, the real light-client path) has **zero**
  caveat-manifest references — the off-AIR manifest is not consulted on the live verify path at all.
* The off-AIR `SlotCaveatEntry` manifest lives in the **full v1** effect-vm PI layout
  (`>= pi::BASE_COUNT`); the live **rotated** leg (38/39/wide PIs) does **not** carry it. The
  AIR-bound `RotatedCaveatManifest` (`trace_rotated.rs`) is a separate vehicle.

## 2. The mechanism — the declaration is already committed

The fix binds each cell's **declared constraint-set** into the cell's **committed state**, so the
verifier knows what to require and a forger cannot omit. The keystone observation is that **this
binding already exists**:

`cell/src/commitment.rs::compute_authority_digest_felt` folds `cell.program` — and a `Predicate` /
`Cases` program carries the cell's `state_constraints` — into a single felt
(`postcard::to_allocvec(constraints)` absorbed under a domain prefix, hashed by Poseidon2
`hash_bytes`). That felt is `record_digest` = `pre[24]` = the `B_AUTHORITY_DIGEST` limb of the
rotated pre-limbs (`compute_rotated_pre_limbs`), which is absorbed into the **~124-bit wide
commitment** a light client binds in `verify_full_turn_bound` (the leg's last-16-PI 8-felt
before/after anchor).

So the declared capacity caveats are **already** part of the committed cell state, at ~124-bit
faithfulness — exactly the way the cap-reshape crown's `capability_root` binds the c-list. No new
committed limb is needed; the declaration is bound today.

## 3. The verifier check — re-derive required, demand coverage

Given the committed declaration, the verifier:

1. **Re-derives** the required capacity tags from the declared `state_constraints`
   (`dregg_turn::executor::required_capacity_caveat_tags` → `[17]` for `SettleEscrow`, `[18]` for
   `DischargeObligation`, `[19]` for `VaultDeposit`; the Rust twin of the Lean `requiredTags`). Only
   the **joint** capacity gates impose a coverage floor — the per-slot caveats are independently
   re-evaluated when present and a missing one is simply not bound (no omission attack).
2. **Demands coverage** — `dregg_circuit::effect_vm::verify_slot_caveat_coverage(pi, required_tags)`
   asserts every required tag appears in some published manifest entry. Omission ⟹ a required tag
   absent ⟹ reject.
3. **Re-evaluates satisfaction** — `verify_slot_caveat_manifest` (unchanged) asserts every present
   entry's gate holds.

Coverage (every required entry present) + satisfaction (every present entry holds) = the declared
gate is **omission-proof**.

The forger cannot escape by presenting an **alternate declaration** (e.g. one requiring nothing): to
do so it must publish a declaration whose authority digest matches the committed one, and the
authority digest's collision-resistance then forces the **same** required tags. This is exactly the
Lean `DeclCommitBinds` floor, the analog of `Poseidon2SpongeCR`.

### The proven soundness core (Lean)

`metatheory/Dregg2/Deos/ConstraintBinding.lean`, `#assert_all_clean` (8 keystones):

| Theorem | What it proves |
|---|---|
| `omission_rejected` | a manifest with no entry for a required tag is REJECTED (the omission tooth) |
| `unsatisfied_rejected` | a present-but-failing entry (hollow verdict) is REJECTED |
| `honest_accepts` | a covered, satisfied manifest ACCEPTS (non-vacuity) |
| **`omission_caught_under_binding`** | **the soundness core** — under `DeclCommitBinds`, a turn whose committed declaration requires `t` is rejected if the manifest omits `t`, WHATEVER declaration the prover presents (matching the committed commitment) |
| `hollow_declaration_impossible` | the empty-declaration dodge contradicts the binding floor |
| `honest_settle_covers` / `partial_settle_not_covered` | the escrow BRIDGE — the abstract `satisfied` bit IS the §6 `SealedEscrow.SettleGate`, reusing its proven `settle_passes_gate` / `partial_settle_rejected` teeth |
| `escrow_omission_rejected` | the concrete tag-17 instance |

Both-polarity `#guard`s compute on the reference sponge: an honest settle is covered; the empty
manifest, a wrong-tag manifest, and a hollow (failing-gate) entry are all rejected.

## 4. VK impact — NONE for the soundness core; the carrier is the named epoch

The constraint-binding **soundness core is NOT VK-affecting**:

* The declaration binding already exists (the authority digest in the ~124-bit commit — no AIR
  change).
* The manifest rides public inputs and the coverage + satisfaction checks are **off-AIR** verifier
  code (`verify_slot_caveat_coverage` is a pure PI scan). The AIR constraint polynomials — hence the
  VK bytes — are byte-identical.

What IS VK-adjacent is the **carrier** (§1, fact 2): for a **pure light client** (commitments only),
the off-AIR manifest must ride the leg the light client actually binds — the rotated/wide leg — and
be tied to committed state in-AIR. Getting the manifest (or the per-slot field-view openings) onto
the rotated/wide leg with PI bindings is a new descriptor boundary = **new VK bytes**. That is the
named, gated VK epoch.

## 5. Staged wiring (built this pass, deployed default NOT flipped)

* **Lean** — `ConstraintBinding.lean`, the proven soundness core (§3), imported into `Dregg2.Deos`.
* **Circuit** — `verify_slot_caveat_coverage` (`circuit/src/effect_vm/verify.rs`), the omission-proof
  coverage primitive, exported alongside `verify_slot_caveat_manifest`. Tests:
  `circuit/tests/caveat_coverage.rs` (omission rejected, wrong-tag rejected, hollow-entry rejected,
  honest accepted, multi-tag coverage).
* **Executor** — `required_capacity_caveat_tags` (`turn/src/executor/mod.rs`), the required-tag
  re-derivation beside `project_slot_caveat_manifest`. Test:
  `turn/tests/required_caveat_tags.rs` (the omission-proof round-trip — the same declaration projects
  its entry and yields its required tag; coverage rejects a dropped entry).
* **SDK** — `CaveatCoverageExpectation` + `verify_full_turn_bound_with_caveat_coverage`
  (`sdk/src/full_turn_proof.rs`), the STAGED verifier beside the deployed `verify_full_turn_bound`.
  `expected_caveat_coverage = None` is byte-identical to the deployed path (nothing flips);
  `Some(cov)` runs every deployed check, then demands coverage + satisfaction of the manifest. It is
  **fail-closed**: a turn with no manifest-bearing leg has every required tag absent and is rejected.

The deployed `verify_full_turn_bound` and the deployed default (no cell declares a capacity caveat)
are unchanged.

## 6. The true distance to "genuinely light-client-witnessed"

* **DONE (this pass):** the soundness core. A verifier that holds (or re-derives from authoritative
  pre/post state) the declared constraint-set + the bound state field views — the same posture as the
  deployed cap-membership expectation (`verify_full_turn_bound` step 9, where the caller re-derives
  `cap_root`/leaf from trusted data) — now **rejects omission**. The gate is no longer
  prover-optional. Proven in Lean, exercised in Rust.
* **REMAINING (the named, gated VK epoch):**
  1. **Carrier** — put the off-AIR manifest (or the field-view openings) on the rotated/wide leg PI,
     bound in-AIR, so a **pure** light client (commitments only, no state opening) witnesses
     coverage without trusting a caller-supplied field view. This is VK-affecting (new descriptor
     boundary) and must be built STAGED beside the deployed descriptor.
  2. **Authority-digest opening** — bind the caller-supplied `required_tags` to the committed
     declaration in-proof: open the witnessed `state_constraints` against the `B_AUTHORITY_DIGEST`
     limb the wide commit carries (recompute `compute_authority_digest_felt`, check equality), so the
     required-tag set is provably the committed one, not caller-asserted. The Lean `DeclCommitBinds`
     floor is the spec; this is its in-proof realization.
  3. **Flip** — the lockstep verifier-code + descriptor epoch: ship the upgraded verifier and the
     staged carrier descriptor to all consumers, then allow capacity cells to declare the caveat and
     route the live path through `verify_full_turn_bound_with_caveat_coverage`. Coordinates with the
     temporal-caveat and umem VK epochs (one upgrade window).

Until (1)+(2)+(3), the staged path is light-client-witnessed **for a verifier with the committed-
state opening** (the cap-membership posture), not yet for a pure commitments-only light client. That
is the honest scope: the soundness CORE — omission is caught, not prover-optional — is built and
proven; the carrier that extends it to a pure light client is the named remaining VK epoch.
