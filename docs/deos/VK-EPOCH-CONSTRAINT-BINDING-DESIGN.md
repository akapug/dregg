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
be tied to committed state in-AIR.

### Correction (verified against HEAD): the manifest carrier is ALREADY in the deployed VK

The rotated caveat carrier — the `RotCaveatManifest` (29 felts) chained by `caveatCommit` to a
published caveat-commit PI — is **already in the deployed AIR** of every R=24 cohort descriptor.
`circuit/descriptors/rotation-v3-staged-registry.tsv`'s `transferVmDescriptor2R24` (the avail-hardened
`-gentian-deployed-bare-refuse` member: `public_input_count:50`, trace width 1702) carries the manifest,
chained by poseidon2 lookups to the caveat-commit column, pinned `pi_index 45` at col 714
(`trace_rotated.rs:716`, "PI 45: caveat commit").
The Lean binding keystone `EffectVmEmitRotationCaveat.caveatCommit_binds` proves equal caveat commits
force equal manifests under the ONE `Poseidon2SpongeCR` floor. So a pure light client that binds the
caveat-commit PI (part of the ~124-bit wide commit) witnesses the **exact** manifest; a forger cannot
publish a different (omitting) one without moving PI 45.

Consequently, **porting the capacity manifest (tags 17/18/19) onto this carrier is NOT VK-affecting**:
the carrier columns + the `caveatCommit` → PI binding already exist; the tag values are data on
existing columns, not new constraint polynomials. The §4 framing above ("a new descriptor boundary =
new VK bytes") over-stated the carrier's cost — the manifest-binding leg is already deployed.

The genuinely-VK-affecting remainder is **narrower** than "the carrier" and is the §6 tail.

## 5. Staged wiring (built; deployed default NOT flipped)

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

### The CARRIER staging (Piece 1 — NOT VK-affecting, NOT flipped)

The capacity manifest now rides the **AIR-bound rotated carrier**, not just the unbound off-AIR
full-v1 PI leg the deployed coverage check reads:

* **Lean** — `metatheory/Dregg2/Deos/CapacityCarrier.lean`, `#assert_all_clean` (5 keystones). It
  bridges `RotCaveatManifest` → `ConstraintBinding.Manifest` (`toConstraintManifest`) and proves:
  - `carrier_manifest_forced` / `carrier_coverage_forced` — two manifests with the same caveat
    commit project to the same coverage manifest (via `caveatCommit_binds`); coverage rides the
    commit, not the prover's choice.
  - **`carrier_omission_impossible`** — the sharp tooth: there is NO manifest a forger can publish
    that both matches the committed caveat commit of an honest covering manifest AND omits a required
    tag. This is the upgrade from "verifier HOLDS the committed manifest opening" (the soundness
    core's posture) to a **pure light client** binding PI 45 — the manifest it checks IS forced.
  - **`carrier_omission_caught_pure_lightclient`** — composed with `DeclCommitBinds`: both bindings
    (caveat commit forces the manifest; authority-digest forces the required tags) discharge the
    cap-membership posture. `escrow_carrier_omission_impossible` is the concrete tag-17 instance.
  - Non-vacuity `#guard`s: an omitting (`count = 0`) manifest does not cover tag 17, and dropping the
    entry MOVES the reference-sponge `caveatCommit` (a pure light client detects it).
* **Circuit producer** — `slot_caveats_to_rotated_manifest` (`trace_rotated.rs`): projects the off-AIR
  `SlotCaveatEntry` capacity entries onto the rotated carrier (registers domain, `slot_index` → felt
  key, params preserved); refuses an over-width manifest (no silent truncation = no dropped gate).
* **Circuit verifier** — `verify_rotated_caveat_coverage` (`verify.rs`): the bound-leg twin of
  `verify_slot_caveat_coverage`, demanding every required tag is present in the rotated manifest the
  wide commit forces. Tests: `circuit/tests/capacity_carrier.rs` (7 — faithful projection, honest
  accept, omission/wrong-tag/multi-tag rejection, over-width fail-closed).

STAGED: nothing on the live wire calls these (no deployed cell declares a capacity caveat); the
deployed empty-manifest default and the deployed descriptors/VK are byte-identical (descriptor-drift
guards green).

### The SATISFACTION staging (Piece 2 — VK-AFFECTING; the emit landed, the flip did not)

The genuinely-VK-affecting half — the SATISFACTION weld — now has its soundness rung PROVEN and its
in-AIR constraint polynomials BUILT (staged beside the deployed descriptor, NOT yet emitted into a
committed VK):

* **Lean** — `metatheory/Dregg2/Deos/CapacitySatisfaction.lean`, `#assert_all_clean` (6 keystones).
  It models the rotated state block as its limb vector, the field-slot read `fieldAt b k = b[4 + k]`
  (the `r3..r10 ↔ fields[0..8]` weld), and the block `stateCommit` as the sponge over the limbs (the
  chained `wireCommitR` digest the wide commit absorbs, under the ONE `Poseidon2SpongeCR` floor). It
  proves:
  - `fieldAt_bound_in_commit` — equal state commits ⟹ equal field-at-slot (REUSE of
    `Poseidon2SpongeCR`; the field-level analog of `Heap.root_binds_get`).
  - `SettleFieldGate` — the EXACT shape of the deployed `verify.rs` `SETTLE_ESCROW` arm (both legs
    `Deposited` before, both `Consumed` after), now read from the rotated BEFORE/AFTER field columns;
    `partial_settle_field_rejected` / `phantom_settle_field_rejected` are the negative teeth.
  - **`satisfaction_witnessed`** — the SATISFACTION keystone: equal before/after state commits ⟹ the
    same gate verdict. So a forger cannot pass the in-AIR gate over FAKE field columns while the
    genuine committed state fails it. This is the in-AIR analog of `SealedEscrow.settle_gate_root_bound`,
    over the FIELD columns the weld touches and the state-commit the wide commit DIRECTLY absorbs
    (vs the heap root the caller had to hold).
  - **`capacity_witnessed_pure_lightclient`** — the composed keystone: coverage (Piece 1, the carrier
    `carrier_manifest_forced`) ∧ satisfaction (Piece 2) — a pure light client binding the caveat
    commit + the before/after state commits witnesses BOTH that the entry is present AND that the gate
    held over the committed state, WITHOUT any caller-held opening. The cap-membership posture is fully
    discharged in proof.
* **Circuit** — `circuit/src/effect_vm/satisfaction_weld.rs`: `settle_escrow_satisfaction_gates`
  builds the FOUR `VmConstraint::Gate` constraints `sel · (col − const) == 0` over the rotated
  BEFORE/AFTER field columns (`before_field_col` / `after_field_col` = `{BEFORE,AFTER}_BASE + 4 + slot`),
  selector-gated. Tests (`cargo test effect_vm::satisfaction_weld`, faithful `eval_lean_expr`): honest
  settle satisfies every gate; a partial settle and a phantom settle are UNSAT; selector-0 makes the
  gates inert (no false reject off a declared capacity turn).

STAGED — the welded descriptors ARE emitted into `rotation-v3-staged-registry.tsv` (see §6), but
nothing routes them onto the live verify path and no consumer holds their committed VKs. So
SATISFACTION is **not light-client-witnessed in production** — only a verifier holding the
committed-state opening witnesses it (the cap-membership posture). What remains is the §6 deploy
flip.

## 6. The true distance to "genuinely light-client-witnessed"

* **DONE — the soundness core.** A verifier that holds (or re-derives from authoritative
  pre/post state) the declared constraint-set + the bound state field views — the same posture as the
  deployed cap-membership expectation (`verify_full_turn_bound` step 9, where the caller re-derives
  `cap_root`/leaf from trusted data) — now **rejects omission**. The gate is no longer
  prover-optional. Proven in Lean, exercised in Rust.
* **DONE — Piece 1, the CARRIER (§5):** the capacity manifest rides the AIR-bound rotated
  carrier; omission on the bound leg is **impossible** (`carrier_omission_impossible`), proven for a
  pure light client binding PI 45. This discharges the COVERAGE half (the omission tooth) for a pure
  light client: it no longer needs to be handed the manifest opening — the wide commit forces it.
  NOT VK-affecting (the carrier binding is already deployed; see the §4 correction).

* **DONE — Piece 2, the SATISFACTION SOUNDNESS + CONSTRAINTS (§5):** the in-AIR
  gate-satisfaction weld's soundness rung is PROVEN (`CapacitySatisfaction.lean`,
  `satisfaction_witnessed` + the composed `capacity_witnessed_pure_lightclient`,
  `#assert_all_clean`) and its in-AIR `VmConstraint::Gate` polynomials are BUILT + tested
  (`satisfaction_weld.rs`). This establishes that welding the gate's slot reads to the rotated
  BEFORE/AFTER field columns carries pure-light-client satisfaction. It is STAGED — NOT yet in a
  committed VK and NOT flipped, so satisfaction is **not light-client-witnessed in production yet**.

* **DONE — the tags 18/19 SATISFACTION SOUNDNESS rungs:** `CapacitySatisfaction.lean`
  carries the discharge (tag 18) and vault (tag 19) field-column satisfaction keystones beside the
  escrow one: `discharge_satisfaction_witnessed` / `vault_satisfaction_witnessed` (equal before/after
  state commits ⟹ the SAME full gate verdict — inequalities included — by REUSE of
  `fieldAt_bound_in_commit`), their teeth (`discharge_{early,cursor_not_advanced,wrong_amount}_field_rejected`;
  `vault_{inflation_attack,dilution,no_deposit}_field_rejected`), and the composed
  `{discharge,vault}_capacity_witnessed_pure_lightclient`. `#assert_all_clean`, 16 keystones, lake green.
  This proves the soundness the in-AIR weld carries for all three tags; the in-AIR constraint
  builders and their registry emits are the LANDED items below.

* **LANDED (the former "two blockers" — both discharged; `docs/deos/VK-EPOCH-PLAN-2026-07-05.md`
  §9 records the closures and supersedes this section's earlier terminal-blocker framing):**

  * **The escrow welded-descriptor machinery.** `metatheory/Dregg2/Deos/SettleEscrowSatDescriptor.lean`
    defines `settleEscrowSatVmDescriptor2R24` = `graduateV1 (rotateV3 settle-base)` + the four
    selector-gated satisfaction gates over the rotated FIELD columns + the selector PI pin, with the
    REFINEMENT rung `settleEscrowSatV3_forces_settle_gate` + partial/phantom UNSAT teeth,
    `#assert_all_clean`; it is EMITTED into `rotation-v3-staged-registry.tsv`. The capacity-selector
    column is real (`satisfaction_weld.rs` `ESCROW_SEL_COL = PARAM_BASE+2`, pinned to PI 46), the
    emitted gate bodies match the Rust builder byte-for-byte, and the wide graduation
    (`SettleEscrowSatWideDescriptor.lean`, `#assert_all_clean`, 9 keystones) proves the
    satisfaction-gate field columns lie inside the BEFORE/AFTER limbs the deployed wide carriers
    absorb (`beforeFieldCol_absorbed` / `afterFieldCol_absorbed` composed with
    `rotV3Wide_binds_published` under `Poseidon2WideCR`) — a pure light client binding the wide
    commit binds those columns.

  * **The `sel = 0` dodge — DISCHARGED in proof.** Not by an in-AIR authority-digest recompute (the
    path this section originally specced as item 2) but by the caveat-manifest-column decode
    (`metatheory/Dregg2/Deos/CarrierBoundFloorGadget.lean`): the required-capacity floor decodes
    in-AIR from the caveat type-tag columns the committed manifest binds at PI 45
    (`caveatCommit_binds`), so a declared cell cannot present an unforced selector. This removes the
    caller-asserted `required_tags` input by a route cheaper than the digest recompute.

  * **The bare-descriptor dodge — CLOSED in the deployed cohort bytes.** Every cohort row in
    `circuit/descriptors/rotation-v3-staged-registry.tsv` carries the
    `-gentian-deployed-bare-refuse` weld (the per-tag floor-decode + `floor == 0`-refuse gates;
    cohort trace widths off base `GRAD_ROT_WIDTH = 1647` (`trace_rotated.rs:138`): 1692 for the 32
    standard graduated members, 1702/1700 for the avail-hardened transfer/burn members, 1668/1664
    for the two distinct-geometry V1Face members), and the anti-launder tooth
    `bare_floor_refuse_weld::deployed_cohort_bytes_carry_the_refuse`
    (`circuit/src/effect_vm/bare_floor_refuse_weld.rs`) parses the committed TSV and asserts all 36
    cohort rows carry it. Soundness: `BareCohortFloorRefuseDeployed.lean`
    (`declared_{escrow,discharge,vault}_unsat_deployed` — a declared-capacity turn routed through a
    bare cohort member is UNSAT); completeness: a non-declaring cell decodes `floor = 0` and the
    refuse is inert.

  * **Tags 18/19 in-AIR gates — BUILT, honoring the non-equality shapes this section demanded.**
    `circuit/src/effect_vm/discharge_weld.rs` builds the due-ness range check as a `DUE_BITS = 28`
    bit-decomposition (wrap-to-small dodge excluded) with the G5 free-param binding CLOSED:
    `PERIOD_COL`/`AMOUNT_COL` are gated equal to the committed caveat params and `CLOCK_COL` to the
    published block height (PI 44) — no producer-free scalars. `vault_weld.rs` builds the
    no-dilution product inequality `Tb·m ≤ Sb·d` as an overflow-safe multi-limb schoolbook product
    with witnessed carries (the products exceed the ~31-bit field). Both descriptors are Lean-emitted
    (`DischargeSatDescriptor.lean` / `VaultSatDescriptor.lean`) and present as staged-registry rows
    (`dischargeSatVmDescriptor2R24`, `vaultSatVmDescriptor2R24`, beside the escrow row).

  * **Real STARK prove/verify exercises run against the emitted descriptors.**
    `circuit/tests/settle_escrow_weld_prove.rs` (tag 17) and
    `circuit/tests/gentian_discharge_vault_prove.rs` (tags 18/19): honest discharge/vault settles
    PROVE + VERIFY through the genuine rotated producer + the production aux-fills; the six
    gate-mechanic forge arms (early discharge / cursor-not-advanced / wrong-amount; zero-mint /
    dilution / no-deposit) and the three free-param-bind forge arms are REFUSED.

* **REMAINING — the ember-gated deploy flip (the one deploy caveat).** The deployed light-client
  entry is still `verify_full_turn_bound`; `verify_full_turn_bound_with_caveat_coverage`
  (`sdk/src/full_turn_proof.rs:5461`) is its staged sibling, and the declaration-keyed prover
  routing (`rotated_descriptor_name_for_declared_{capacity,escrow,discharge,vault}`,
  `circuit/src/effect_vm/trace_rotated.rs`) is built but not the deployed default. Taking the flip
  is the lockstep verifier-code + VK-redistribution window: route the live verify path through the
  coverage verifier reading the **rotated** leg (`verify_rotated_caveat_coverage`), admit the welded
  satisfaction descriptors under committed VKs, re-genesis + redistribute light-client VKs, then
  allow capacity cells to declare the caveat. Precedent: the umem flip — every producer built +
  loud-probe-validated STAGED, the flip itself a registry-default flip, fail-closed, no coverage
  narrowing.

The honest scope at HEAD: COVERAGE (omission caught) is pure-light-client-witnessed via the deployed
carrier, and the two forger dodges this section once named terminal (`sel = 0`, the bare route) are
closed in proof and in the deployed cohort bytes. SATISFACTION is proven sound, its in-AIR
constraints are built and emitted for all three tags, and real STARKs exercise them — but until the
deploy flip routes the live path and commits the welded VKs to consumers, production satisfaction is
witnessed only by a verifier holding the committed-state opening (the cap-membership posture), not
by a pure light client.
