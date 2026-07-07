# GENTIAN deployed-registry VERIFY — is the capacity-floor refuse live on the deployed light-client path?

Audit date: 2026-07-06. Repo `/Users/ember/dev/breadstuffs` @ `main` (HEAD `2630964ae`, the gentian
liveness commit). Grounded at file:line at HEAD.

## The question

The flag-day welded a three-block **capacity-floor refuse** (escrow tag 17 / discharge 18 / vault 19)
onto the bare rotated cohort so a **declared-capacity dodge** (a cell that DECLARES an escrow/discharge/
vault obligation and settles via a plain BARE cohort leg instead of its satisfaction member) is UNSAT
under the bare descriptor. The soundness keystone is
`metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3Refused.lean` (`v3RegistryRefused`, widening
`traceWidth` 1581→1626 + 39 refuse gates) with `BareCohortFloorRefuseDeployed.declared_capacity_unsat_deployed`.

The meta-review flagged a **registry mismatch**: that refuse is emitted onto the **V3 1-felt** registry
(`rotation-v3-staged-registry.tsv`), but the DEPLOYED light-client verify path resolves the **WIDE /
WELDED** registries. If the descriptor the deployed LC actually verifies a capacity turn against does not
carry the refuse, the flip is not live on the deployed path.

## VERDICT (2026-07-06): CLOSED on the deployed light-client path (option a — the wide VK epoch).

**The bare-descriptor dodge is now UNSAT on the deployed default registries.** The capacity-floor refuse
was lifted to ride the **WIDE + WELDED** bare cohort (the registries `verify_effect_vm_rotated_with_cutover`
actually resolves), not only the V3 1-felt cohort. The deployed forge
`sdk/tests/gentian_deployed_registry_dodge_forge.rs` now goes **ACCEPTED → REJECTED**: a cell that
DECLARES the escrow capacity (tag 17) and settles via a plain bare-cohort `Burn` is rejected by
`verify_effect_vm_rotated_with_cutover` ("verified under NO cohort descriptor"), while a NON-declaring
normal turn still verifies (completeness/liveness preserved).

The original finding (below) stands as the record of WHY it was open; the closure is option (a).

### The closure (option a — assessed sound + smaller; grounded + built)

- **Why (a) over (b):** the deployed SDK verify (`verify_effect_vm_rotated_with_cutover`) only sees the
  proof's PUBLIC INPUTS, and the declared capacity is folded into the `caveatCommit` hash PI (PI 45), a
  digest — the verifier cannot read the declared tag at the Rust layer. A discriminator (b) would need the
  tag exposed as a raw committed PI (itself a wide emit change), so it is NOT smaller. (a) makes the WIDE
  bare descriptor itself in-circuit-UNSAT for a declared-capacity trace, reusing the fully-built refuse
  machinery — the forge rejects because no deployed descriptor accepts.
- **Lean:** `Dregg2.Deos.BareCohortFloorRefuseWide.gentianWideBareRefuse` places the three decode+refuse
  blocks at aux columns PAST the wide member's own width (past the two 13×8 wide carriers), reading the
  SAME deployed caveat tag columns `ebDep = 643/650/657/664` (which `wideAppend` preserves). Soundness
  `declared_capacity_unsat_wide` reuses the column-parametric `declared_tag_unsat_at`; the append-only peel
  `satisfied2_of_gentianWideBareRefuse` lifts every wide value/faithfulness rung. `#assert_all_clean`.
- **Emit:** `EmitWideRegistryProbe.lean` + `EmitWideUMemWeldRegistryProbe.lean` map `gentianWideBareRefuse`
  over exactly the 36 bare cohort members (mirroring V3's `v3RegistryRefused ++ drop 36`); regenerated into
  `WIDE_REGISTRY_STAGED_TSV` / `WIDE_UMEM_WELD_REGISTRY_TSV` (FPs re-pinned). The forge burn route
  (`burnVmDescriptor2R24`) widened 2493 → 2541.
- **Rust producer:** `fill_refuse_aux` derives the aux base for a wide/welded member as
  `trace_width − 3·REFUSE_STRIDE` (past its own width); a non-declaring cell decodes `floor = 0` (inert,
  no false reject), a declared cell decodes `floor = 1` (UNSAT under the `floor == 0` gate).

### Original finding (the record of why it was open): NOT LIVE on the deployed path.

The capacity-floor refuse and the three satisfaction members lived **only** on the V3 1-felt registry.
The deployed light-client verify (both the SDK wire verifier and the executor cohort verify) resolves the
**WIDE** registry first, then the **WELDED** registry, and falls back to V3 **only** for `CapOpen`
members that lack a wide twin. A bare-cohort leg for a declared-capacity cell therefore bound its **WIDE**
member — which carried **neither the refuse nor the satisfaction gate** — and was accepted.

## Ground truth (grep + file:line)

### 1. The refuse + the satisfaction members are V3-ONLY

- `circuit/descriptors/rotation-v3-staged-registry.tsv`: 36 members at `trace_width:1626` (the
  refuse-widened bare cohort); the string `gentian-deployed-bare-refuse` appears **only** in this file
  (grep across `circuit/descriptors/` returns this file alone); `floor`/`refuse` selector strings: **72**
  occurrences. The three satisfaction members `settleEscrowSatVmDescriptor2R24` /
  `dischargeSatVmDescriptor2R24` / `vaultSatVmDescriptor2R24` are present here (width 1581).
- `circuit/descriptors/rotation-wide-registry-staged.tsv` and
  `rotation-wide-umem-welded-registry-staged.tsv`: `floor`/`refuse` occurrences: **0** each; the three
  satisfaction members: **absent** (0 hits) from both. Their `trace_width` band is 2465–2965 — a
  different emit entirely from the 1626 refuse cohort.
- Per-effect widths (the bare-cohort `transfer` / `burn` member): V3 `transferVmDescriptor2R24` =
  `trace_width 1626` (refuse-welded); WIDE = `2495`; WELDED = `2502`. V3 `burnVmDescriptor2R24` = `1626`;
  WIDE = `2493`. The wide/welded twins carry **no** `floor` gate.

### 2. The deployed light-client verify resolves WIDE/WELDED, not V3

- SDK wire verifier `sdk/src/full_turn_proof.rs::verify_effect_vm_rotated_with_cutover` (:4249): iterates
  `WIDE_REGISTRY_STAGED_TSV` first (:4313), extends with `WIDE_UMEM_WELD_REGISTRY_TSV` (:4324), and only
  if `bound.is_empty()` falls back to `V3_STAGED_REGISTRY_TSV` (:4326) — filtered to
  `name.contains("CapOpen") && !cap_open_key_has_wide_twin(name)` (:4334). The satisfaction members are
  NOT `CapOpen` names, and the refuse-welded bare transfer/burn is not `CapOpen` either, so neither can
  ever be surfaced by the fallback; and the fallback never fires for a bare leg (a wide member accepts, so
  `bound` is non-empty).
- Executor cohort verify `turn/src/executor/proof_verify.rs::verify_one_cohort_run` (:614): resolves the
  cohort member `name` from the EFFECT-keyed `rotated_descriptor_name_for_effect(lead)` (:677), i.e. a
  settle-as-transfer resolves `name = "transferVmDescriptor2R24"` — the declaration-keyed
  `rotated_descriptor_name_for_declared_capacity` the gentian commit added is NEVER called here. It parses
  that `name` from `WIDE_REGISTRY_STAGED_TSV` (:684) and the welded twin from
  `WIDE_UMEM_WELD_REGISTRY_TSV` (:734); `require_welded` (:1219) DROPS the bare wide member in favour of
  the welded twin for a single-cohort sovereign turn. The caveat manifest it reconstructs is
  `transfer_caveat_manifest()` (:755), which declares NO capacity tag — so the declared capacity is not
  even reconstructed on this path. V3 is never read on this path. (The V3 registry is only referenced in
  this file inside a comment, :981.)
- Non-test reads of `V3_STAGED_REGISTRY_TSV` are producers / aggregation / the SDK fallback, not a
  primary capacity-turn verify (grep over `--include=*.rs`, excluding tests).

### 3. The gentian LIVENESS test does NOT exercise the deployed resolution

`circuit/tests/gentian_deployed_capacity_liveness.rs` proves + verifies each satisfaction member by
parsing it **directly** from `V3_STAGED_REGISTRY_TSV` (`deployed_member`, :135) and calling
`verify_vm_descriptor2` on that exact descriptor (`accepts`, :153). That is a unit-level check of the V3
member in isolation — it never routes through `verify_effect_vm_rotated_with_cutover` /
`verify_one_cohort_run`, i.e. never through the WIDE-first resolution the deployed light client uses. So
the liveness test proves the V3 satisfaction member *can* accept an honest turn; it does **not** show the
deployed LC ever *selects* that member. The routing helper
`rotated_descriptor_name_for_declared_capacity` (`circuit/src/effect_vm/trace_rotated.rs`, added by
`2630964ae`) names the V3 satisfaction member, but nothing on the deployed verify path consults it, and no
WIDE/WELDED satisfaction member exists for a producer to emit or the LC to bind.

## The forge (the decider)

`sdk/tests/gentian_deployed_registry_dodge_forge.rs` —
`declared_capacity_dodge_verifies_through_deployed_lightclient`. It:

1. Builds a cell whose caveat manifest **declares** the escrow capacity obligation (tag 17, folded into
   the committed `caveatCommit` PI) and settles it via a plain bare-cohort leg (a value-draining `Burn`;
   the Lean refuse theorem `declared_capacity_unsat_deployed` is stated for ANY bare member).
2. Produces the **WIDE** bare leg (`burnVmDescriptor2R24`, width 2493 — the deployed producer's default),
   a real batch STARK.
3. Drives the serialized proof through the ACTUAL deployed entry
   `dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover`.

RESULT (post-flip, real batch STARK, `1 passed` in ~3.5s): <!-- FORGE_RESULT -->the deployed LC
**REJECTS** the declared-capacity bare leg. The deployed WIDE + WELDED `burnVmDescriptor2R24` now carry
the capacity-floor refuse (widened 2493 → 2541, marker `...-gentian-deployed-bare-refuse`). The honest
producer path is UNSAT under the refuse-welded member (`floor = 1` for the declared escrow → the
`floor == 0` gate has no satisfying assignment), and even a genuine PRE-FLIP bare-dodge STARK (the exact
artifact an old producer would emit) binds **NO** deployed cohort descriptor
("rotated effect-vm proof verified under NO cohort descriptor"). A NON-declaring normal wide burn still
proves + verifies through `verify_effect_vm_rotated_with_cutover` (completeness/liveness preserved). The
flip is LIVE on the deployed light-client path.<!-- /FORGE_RESULT -->

## What is now true

- The gentian soundness flip is live **on the deployed WIDE / WELDED registries** — a declared-capacity
  turn is UNSAT under every welded wide/welded bare cohort member (`declared_capacity_unsat_wide`), and the
  deployed forge REJECTS the bare-descriptor dodge through `verify_effect_vm_rotated_with_cutover`.
- Completeness/liveness is preserved: a non-declaring normal turn still verifies through the deployed LC
  (the refuse decodes `floor = 0`, inert).

## Named remaining lanes (burn-down, not parking)

1. **Carrier-regression sweep (in progress).** The 36 cohort wide members widened +48, so test consumers
   that derive teeth columns as `trace_width − N` (the `#[ignore]`d deployed-tooth STARK tests — sovereign
   `width−32` digest base, transfer/mint `width−2` teeth) or hardcode cohort widths must use
   `trace_width − 3·REFUSE_STRIDE − N` and fill the refuse aux (`fill_refuse_aux`, floor=0). PRODUCTION is
   unaffected (the producer teeth-fill riders use fixed absolute bases; only tests assumed teeth-at-the-end).
   Done: `effect_vm_wide_roundtrip` (8/8), `sovereign_binding_deployed_tooth`, `membership_binding_deployed_tooth`,
   and (2026-07-06, CP6c) `bridge` / `dsl` / `deco`. All three bind the WIDE bare transfer member
   (`transferVmDescriptor2R24`, `2495 → 2543` after the `-gentian-deployed-bare-refuse` weld) via a plain
   transfer leg whose teeth were derived end-relative (`trace_width − 2`); fixed to
   `trace_width − 48 − 2` + `fill_refuse_aux` (floor=0), mirroring sovereign/membership. VALIDATED under the
   widened registry with real recursion folds: `bridge` 2/2 (398s), `deco` 2/2 (402s), `dsl` 3/3 (372s) —
   both the honest-accepts (liveness) AND the forged-reject (the tooth still BITES) poles pass. Cheap arms
   green (2/2/3). PRODUCTION unaffected (the fix touches only the teeth base the tests assume; the producer
   riders use fixed absolute bases). Core canaries confirmed no regression: the deployed forge still
   REJECTS (closure intact), 3/3 honest capacity settles verify (liveness), `effect_vm_wide_roundtrip` 8/8.
   Remaining: `factory` / `hatchery`, `wide_new_members_cover`, the sdk wide gauntlet, and the
   `vk_epoch_*_light_client_binding` cohort-width pins.
2. **Honest declared-capacity SETTLE via a wide satisfaction member (liveness, net-new).** A wide/welded
   satisfaction descriptor exists (`SettleEscrowSatWideDescriptor.settleEscrowSatVmDescriptor2R24Wide`) but
   is NOT emitted into the deployed registry, and no producer routes an honest declared-capacity settle to
   it, so an honest escrow/discharge/vault SETTLE does not yet verify through the deployed path (it never
   did — this is a net-new deployed capability, not a regression). Emitting the three wide satisfaction
   twins + the producer routing (`rotated_descriptor_name_for_declared_capacity`) is the liveness half.
3. **WELDED-route forge.** The welded twin is emitted with the refuse (the executor `require_welded` path),
   but there is not yet a dedicated forge driving a declared-capacity WELDED bare leg through
   `verify_one_cohort_run`.
