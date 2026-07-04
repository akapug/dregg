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
`circuit/descriptors/rotation-v3-staged-registry.tsv`'s `transferVmDescriptor2R24` (`public_input_count:46`)
carries the manifest at cols 287.., chained by poseidon2 lookups to col 328, pinned `pi_index 45`.
The Lean binding keystone `EffectVmEmitRotationCaveat.caveatCommit_binds` proves equal caveat commits
force equal manifests under the ONE `Poseidon2SpongeCR` floor. So a pure light client that binds the
caveat-commit PI (part of the ~124-bit wide commit) witnesses the **exact** manifest; a forger cannot
publish a different (omitting) one without moving PI 45.

Consequently, **porting the capacity manifest (tags 17/18/19) onto this carrier is NOT VK-affecting**:
the carrier columns + the `caveatCommit` → PI binding already exist; the tag values are data on
existing columns, not new constraint polynomials. The §4 framing above ("a new descriptor boundary =
new VK bytes") over-stated the carrier's cost — the manifest-binding leg is already deployed.

The genuinely-VK-affecting remainder is **narrower** than "the carrier" and is the §6 tail.

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

### The CARRIER staging (Piece 1, built this pass — NOT VK-affecting, NOT flipped)

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

### The SATISFACTION staging (Piece 2, built this pass — VK-AFFECTING, NOT emitted/flipped)

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

STAGED — these constraint polynomials are NOT yet emitted into a committed welded descriptor / VK and
NOT routed onto any live path. So SATISFACTION is **not light-client-witnessed yet** — only a verifier
holding the committed-state opening witnesses it (the cap-membership posture). What remains is §6
item 1's tail: emit the staged `settleEscrowSatVmDescriptor2R24` (its Lean emit keystone), commit its
VK beside the deployed, and flip. The deployed descriptors/VK are byte-identical this pass
(descriptor-drift guards green).

## 6. The true distance to "genuinely light-client-witnessed"

* **DONE (this pass):** the soundness core. A verifier that holds (or re-derives from authoritative
  pre/post state) the declared constraint-set + the bound state field views — the same posture as the
  deployed cap-membership expectation (`verify_full_turn_bound` step 9, where the caller re-derives
  `cap_root`/leaf from trusted data) — now **rejects omission**. The gate is no longer
  prover-optional. Proven in Lean, exercised in Rust.
* **DONE (this pass — Piece 1, the CARRIER, §5):** the capacity manifest rides the AIR-bound rotated
  carrier; omission on the bound leg is **impossible** (`carrier_omission_impossible`), proven for a
  pure light client binding PI 45. This discharges the COVERAGE half (the omission tooth) for a pure
  light client: it no longer needs to be handed the manifest opening — the wide commit forces it.
  NOT VK-affecting (the carrier binding is already deployed; see the §4 correction).

* **DONE (this pass — Piece 2, the SATISFACTION SOUNDNESS + CONSTRAINTS, §5):** the in-AIR
  gate-satisfaction weld's soundness rung is PROVEN (`CapacitySatisfaction.lean`,
  `satisfaction_witnessed` + the composed `capacity_witnessed_pure_lightclient`,
  `#assert_all_clean`) and its in-AIR `VmConstraint::Gate` polynomials are BUILT + tested
  (`satisfaction_weld.rs`). This establishes that welding the gate's slot reads to the rotated
  BEFORE/AFTER field columns carries pure-light-client satisfaction. It is STAGED — NOT yet in a
  committed VK and NOT flipped, so satisfaction is **not light-client-witnessed in production yet**.

* **DONE (2026-06-28 — the tags 18/19 SATISFACTION SOUNDNESS rungs):** `CapacitySatisfaction.lean`
  now carries the discharge (tag 18) and vault (tag 19) field-column satisfaction keystones beside the
  escrow one: `discharge_satisfaction_witnessed` / `vault_satisfaction_witnessed` (equal before/after
  state commits ⟹ the SAME full gate verdict — inequalities included — by REUSE of
  `fieldAt_bound_in_commit`), their teeth (`discharge_{early,cursor_not_advanced,wrong_amount}_field_rejected`;
  `vault_{inflation_attack,dilution,no_deposit}_field_rejected`), and the composed
  `{discharge,vault}_capacity_witnessed_pure_lightclient`. `#assert_all_clean`, 16 keystones, lake green.
  This proves the soundness an in-AIR weld WOULD carry for all three tags. It is NOT the in-AIR
  constraint and NOT a VK bump (see the blockers below).

* **REMAINING (the genuinely-VK-affecting tail — the FLIP is NOT yet soundly takeable; two
  independent, verified blockers):**

  * **BLOCKER 1 — the emit/selector/exerciser MACHINERY (now BUILT this pass — the GENTIAN
    INITIATIVE); the producer/VK/routing tail REMAINS.** What was named-only is now real:
    - **The welded emit keystone EXISTS** — `metatheory/Dregg2/Deos/SettleEscrowSatDescriptor.lean`
      defines `settleEscrowSatVmDescriptor2R24` = `graduateV1 (rotateV3 settle-base)` + the four
      selector-gated satisfaction gates over the rotated FIELD columns + the selector PI pin, with the
      REFINEMENT rung `settleEscrowSatV3_forces_settle_gate` (a satisfying trace on a selector-on
      non-last row FORCES both legs Deposited-before/Consumed-after) + partial/phantom UNSAT teeth,
      `#assert_all_clean`. It is EMITTED into `rotation-v3-staged-registry.tsv` (the 58th member;
      deployed rows byte-identical, FP re-pinned, drift + Rust descriptor-validation + wide-parity +
      resolver-cohort gates all green).
    - **The capacity-selector column is REAL** — `satisfaction_weld.rs` `ESCROW_SEL_COL = PARAM_BASE+2
      = 70` (pinned to PI 46) replaces the `SEL = 320` placeholder; the emitted descriptor's four
      welded gate bodies match the Rust builder byte-for-byte and bite (honest accept / forged reject).
    - **A capacity-caveat-bearing EXERCISER exists** — `circuit/tests/settle_escrow_capacity_weld.rs`:
      a declared escrow caveat (tag 17, legs 0/1) is COVERAGE-bound on the rotated carrier (can't be
      omitted) AND the EMITTED welded descriptor's gates accept the honest settle / reject the
      forged (SATISFACTION) = the full capacity witness for a declared turn, at the descriptor's
      CONSTRAINT-eval level.
    What REMAINS (the genuine umem-flip-scale tail; `da0c47dd6` was "the 13th attempt"): a PRODUCER
    emitting a SATISFYING rotated trace for the welded descriptor (the field-override + commit-
    recompute surgery the fee/nullifier producers do, now for the two leg field limbs of a
    zero-amount settle-carrier) → a full STARK **prove/verify** against a **committed VK**; binding
    the selector to the committed declaration in-AIR (§6 item 2, so a forger cannot dodge by setting
    the selector 0); and the prover/verify-path routing. The teeth bite in-PROOF today at the LEAN
    refinement level + the EMITTED-descriptor constraint-eval level, NOT yet a full STARK prove.

    **SUB-GAP (1) — "1-felt V3, not WIDE" — CLOSED at the proof level (2026-06-28, the GENTIAN
    FULCRUM).** The GENTIAN verifier lane (`b63f75da3`) named the first structural blocker precisely:
    `settleEscrowSatVmDescriptor2R24` was a 1-felt V3 staged member, so its satisfaction-gate field
    columns were NOT absorbed into the ~124-bit wide commit a pure light client binds.
    `metatheory/Dregg2/Deos/SettleEscrowSatWideDescriptor.lean` (`#assert_all_clean`, 9 keystones,
    lake green, wired into `Dregg2.Deos`) graduates the welded descriptor to the WIDE form:
    `settleEscrowSatVmDescriptor2R24Wide = wideAppend (graduateV1 (rotateV3 settle-base)) bb (bb+51)`
    + the four satisfaction gates + the selector PI pin (the EXACT graduation `EmitWideRegistryProbe.lean`
    applies to every cohort member; `piCount = 63` = 46 rotated + 16 wide commit anchors + the selector
    at PI 62). The V3 refinement (`settleEscrowWide_forces_settle_gate`) + partial/phantom UNSAT teeth
    carry verbatim over the wide form (the gate bodies are byte-identical). The **GRADUATION keystone**
    (`beforeFieldCol_absorbed` / `afterFieldCol_absorbed`) proves the satisfaction-gate field columns
    `bb + 4 + k` / `bb + 51 + 4 + k` (k ≤ 7) lie INSIDE the 37 pre-iroot BEFORE/AFTER limbs the wide
    carriers consume (`bb = (settleEscrowV1Base _ _).traceWidth = EFFECT_VM_WIDTH`, by `rfl`); the
    deployed `EffectVmEmitRotationWide.rotV3Wide_binds_published` (equal published 8-felt commits ⟹
    equal limbs, under `Poseidon2WideCR`) then carries the binding — so a pure light client binding the
    wide commit binds those columns, exactly the `CapacitySatisfaction.fieldAt_bound_in_commit` chain
    over the DEPLOYED wide carriers. STAGED — this is a Lean definition (the source of truth); NOTHING
    is emitted into the deployed wide registry / VK and nothing routes through it. The producer +
    committed VK + live admission (sub-gap above) and the in-AIR selector forcing (§6 item 2 below)
    remain; **the flip is NOT taken** — the selector forcing is the terminal blocker (a pure light
    client cannot force `sel = 1` from the committed digest without the in-AIR authority-digest
    recompute, so a forger would dodge by `sel = 0` or by the bare wide transfer route).

  * **BLOCKER 2 — tags 18/19 in-AIR gates are NOT a mirror of the escrow EQUALITY template.** The
    escrow gate is pure status-code equality (`sel·(col − const) == 0`), the whole gate. The discharge
    gate adds a DUE-NESS INEQUALITY (`due_block ≤ clock`) — a range-check aux column, not an equality
    gate — plus additive equalities over per-cell manifest-param columns (`period`/`amount`, not
    constants). The vault gate is ENTIRELY inequalities: two strict positivities and the no-dilution
    PRODUCT inequality `Tb·m ≤ Sb·d`, whose products exceed the ~31-bit BabyBear field (the off-AIR arm
    uses u128) — an overflow-safe multi-limb comparison gadget. Emitting an equality-only weld for
    18/19 and flipping would DROP the early-discharge / inflation-attack / dilution disciplines from
    what a pure light client witnesses — i.e. ACCEPT FORGERIES. So the sound order is: (a) build +
    validate the escrow welded descriptor + selector + producer + VK + routing (the proven template);
    (b) build the range-checked / product in-AIR gates for tags 18/19; (c) only then flip.

  * Until (a)+(b)+(c), SATISFACTION is **not light-client-witnessed in production** — only a verifier
    holding the committed-state opening witnesses it (the cap-membership posture). The earlier framing
    below ("emit the staged `settleEscrowSatVmDescriptor2R24`") understated this: the descriptor, its
    selector column, its producer, and its VK do not yet exist.
  2. **In-AIR coverage-forcing from the authority digest** — bind the required-tag floor to the
     committed declaration **in-proof**: open the witnessed `state_constraints` against the
     `B_AUTHORITY_DIGEST` r23 limb the wide commit carries (recompute `compute_authority_digest_felt`,
     check equality, force the manifest to carry the re-derived required tags). This removes the last
     caller-asserted input (`required_tags`). The Lean `DeclCommitBinds` floor is the spec; this is its
     in-proof realization. New constraint = **new VK bytes**, STAGED.
  3. **Flip** — the lockstep verifier-code + descriptor epoch: ship the upgraded verifier and the
     staged (1)+(2) descriptors to all consumers, route the live path through
     `verify_full_turn_bound_with_caveat_coverage` reading the **rotated** leg
     (`verify_rotated_caveat_coverage`) instead of the off-AIR v1 leg, then allow capacity cells to
     declare the caveat. Coordinates with the temporal-caveat and umem VK epochs (one upgrade window).
     Precedent: the umem flip (`da0c47dd6`) — every producer built + loud-probe-validated STAGED, the
     flip a pure registry-default flip, PI-count-preserving, fail-closed, no coverage narrowing.

The honest scope after this pass: COVERAGE (omission caught) is pure-light-client-witnessed via the
deployed carrier. SATISFACTION is now **proven sound + its in-AIR constraints built** (Piece 2,
`CapacitySatisfaction.lean` + `satisfaction_weld.rs`) — but it is witnessed only **for a verifier with
the committed-state opening** (the cap-membership posture) until (1) emits the welded descriptor +
commits its VK + flips; it is **NOT light-client-witnessed in production until that flip**. The
required-tag floor is caller-asserted until (2) binds it in-proof. (1)+(2)+(3) are the remaining gated
VK epoch — (1) is now reduced from "design + soundness + constraints" to "emit the descriptor + commit
the VK + flip" for the proven escrow template, then replicate for tags 18/19.
