# RESEARCH — the §3.EPOCH descriptor cutover (delegation-epoch openable committed limb)

Read-only scoping report. Goal: give the delegation-epoch state a dedicated openable
committed limb so the descriptor gate can WRITE-FORCE the revoke/spawn/refresh epoch
writes in-circuit, closing the three named residuals (`RevokeDelegationEpochResidual`,
`SpawnEpochStampResidual`, `RefreshEpochStampResidual`).

**Headline correction to the campaign premise (verified against source, not docs):** the
prompt's framing — "today those fields fold ONLY into the opaque authority-digest limb 24
(`record_digest`)" — is **only partly true**. The state in question is TWO distinct kernel
maps, and they are bound DIFFERENTLY:

- **`delegationEpoch : CellId → Nat`** (the parent's epoch *counter*) — ALREADY has a
  dedicated openable committed limb: rotated **limb 30** (`pre[30]`,
  `cell/src/commitment.rs:928`). It is *bound and openable* but NOT *write-forced* (no gate,
  no `B_EPOCH` symbolic constant on the Lean side).
- **`delegationEpochAt : CellId → Nat`** (the per-child snapshot *stamp*) — has **NO
  dedicated limb at all**; it folds ONLY into `record_digest` (limb 24) via the delegation
  snapshot bytes (`cell/src/commitment.rs:816-832`).

All THREE named residuals are about the **stamp** (`delegationEpochAt`) — the spawn/refresh
ones exclusively, the revoke one mostly (it also touches the parent counter on limb 30 and the
child `delegations` snapshot in record_digest). So the real cutover target is a `delegationEpochAt`
openable limb (a NEW limb), reusing limb 30's binding for the parent counter where applicable.

---

## (1) WHAT EXISTS IN SOURCE NOW

### 1a. The committed-block limb layout (the rotated v9 commitment)

`circuit/src/effect_vm/cell_state.rs` carries the *legacy v1* 4-felt tree
(`compute_commitment`, lines 128-140: `hash_4_to_1` over balance/nonce/fields/cap_root with
`record_digest` as the 4th root input). That is the OLD lossy form; the LIVE light-client
commitment is the **rotated v9** block, built in `cell/src/commitment.rs::compute_rotated_pre_limbs`
(lines 888-943). The 37 pre-iroot limbs (`V9_NUM_PRE_LIMBS = 37`, line 658):

| limb | content | source line | Lean const |
|------|---------|-------------|------------|
| 0 | cells_root | `:898` | — |
| 1..3 | balance_lo / nonce / balance_hi (r0/r1/r2) | `:902-904` | welded |
| 4..11 | fields[0..7] (r3..r10) | `:905-908` | welded |
| 12..23 | app-register headroom (r11..r22, zero for kernel turn) | `:909` | — |
| **24** | **record_digest / authority digest (r23)** | `:916` | `B_RECORD_DIGEST = 24` |
| 25 | cap_root | `:919` | `B_CAP_ROOT = 25` |
| 26 | nullifier_root | `:921` | `B_NULLIFIER_ROOT_OFF = 26` |
| 27 | commitments_root | `:923` | `B_COMMITMENTS_ROOT = 27` |
| 28 | heap_root | `:925` | — |
| 29 | lifecycle (opaque felt) | `:927` | `B_LIFECYCLE = 29` |
| **30** | **`delegation_epoch & 0x7FFF_FFFF`** | **`:928`** | **(NONE — no `B_EPOCH`)** |
| 31 | committed_height | `:929` | `B_COMMITTED_HEIGHT = 31` |
| 32 | lifecycle_disc (raw u8) | `:932` | `B_DISC = 32` |
| 33 | perms_digest | `:935` | `B_PERMS = 33` |
| 34 | vk_digest | `:936` | `B_VK = 34` |
| 35 | mode | `:940` | `B_MODE = 35` |
| 36 | fields_root | `:941` | `B_FIELDS_ROOT = 36` |

The Lean limb-index constants live in `Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:134-181`.
Block geometry: `B_SPAN = 51` (line 134) = 37 pre-iroot limbs + iroot(`B_IROOT = 37`) +
state_commit(`B_STATE_COMMIT = 38`) + 12 chain-carrier intermediate sites (39..50).
`AFTER_BLOCK_OFF = 51` (line 2126): the AFTER block sits at `traceWidth + 51 + off`.
`preLimbsAt_length = 37` (line 198-199). **Note: limb 30 has NO `B_EPOCH` symbolic constant**
— the Lean welds/frame never name it; it is a freely-witnessed limb the anti-ghost keystone
binds (exactly as r23 was before the WAVE-1/2/3 splits).

### 1b. The perms/vk/mode/disc/fields-root forcing TEMPLATE

Three force shapes exist, all appended CONSTRAINTS over a `rotateV3WithRecordPin` base
(`graduable` and the keystones compose verbatim because v1 columns/sites/ranges are untouched):

1. **Scalar selector-gated WELD-to-declared-param** (`permsVKWeldGate`,
   `EffectVmEmitRotationV3.lean:2746-2775`). `permsVKWeldGate sel afterCol paramCol =
   sel·(loc afterCol − loc paramCol)`. On the active row (`sel=1`) forces the AFTER sub-limb
   EQUAL to an in-circuit declared-param column (PI-anchored via `effects_hash`). Used for
   setPerms (limb 33) / setVK (limb 34). Forcing theorem `permsVKWeldGate_forces` (`:2749`);
   `rotateV3WithPermsVKGate` (`:2773`).

2. **Scalar selector-gated FORCE-to-CONSTANT** (`discForceGate` /
   `rotateV3WithDiscGate`, `:2664-2715`). Forces the AFTER limb to a *constant* `afterC`
   (used by makeSovereign → mode limb 35 forced to `Sovereign(1)`, and the lifecycle disc
   transitions on limb 32). Forcing theorem `rotateV3WithDiscGate_forces_after` (`:2697`);
   negative tooth `..._rejects_wrong_after` (`:2709`).

3. **MAP-OP WRITE gate** for an OPENABLE map root (`refusalFieldsWriteOp` /
   `refusalFieldsWriteV3`, `:3405-3425`). A `MapOp{guard, root, key, value, newRoot, op:=.write}`
   forces the AFTER `fields_root` (limb 36) to be the genuine sorted write of `(key→value)`
   into the BEFORE root — used when the limb is itself a sorted-Poseidon2 *map root*. Forcing
   theorem `refusalFieldsWriteV3_forces_write` (`:3433`).

The "frozen authority" continuity weld (`rotateV3FrozenAuthority`, `:2147-2155`) freezes
AFTER==BEFORE for limbs **24, 29, 33, 34, 35, 36** on value effects — note it does **NOT**
include limb 30 (epoch) or 31 (height). So epoch limb 30 is *unconstrained* on value rows
(height is held by its PI binding instead).

### 1c. The confirmed epoch-residual state (verified, not trusted)

Each residual was read in source and is genuinely un-forced:

- **`RevokeDelegationEpochResidual`** — `Dregg2/Circuit/EffectRefinement.lean:804-814`. Three
  clauses: parent `delegationEpoch +1`, child `delegations := []`, child `delegationEpochAt := 0`.
  The §14.EPOCH comment (`:789-802`) and the cap-family §3.EPOCH comment
  (`RotatedKernelRefinementCapFamily.lean:569-630`) both state plainly: the parent bump rides
  limb 30 and the child clears ride record_digest (limb 24); both are *bound* but the descriptor
  carries **no `writesTo delegation_epoch_before (parent_epoch+1) delegation_epoch_after` map-op**
  — it is a NAMED decode residual carried as data, conjoined onto `revokeCircuitStep`.
- **`SpawnEpochStampResidual`** — `EffectRefinement.lean:344-349`:
  `s'.kernel.delegationEpochAt = spawnEpochAtMap s.kernel actor child` (child stamped with the
  spawner's CURRENT epoch). The deployed `spawnE` descriptor FREEZES `delegationEpochAt`
  (`:326-331`); the stamp is the residual.
- **`RefreshEpochStampResidual`** — `EffectRefinementBatch2.lean:294-299`:
  `s'.kernel.delegationEpochAt = refreshEpochAtMap s.kernel child` (re-stamp to parent's current
  epoch). The deployed `refreshDelegationE` binds the frozen face (`:284-292`); the stamp is the
  residual.

### 1d. The deployed TSV rows — CONFIRMED no epoch write-forcing map_op

Parsed `circuit/descriptors/rotation-wide-registry-staged.tsv` directly (3 tab fields:
name / descriptor-id / JSON). The deployed rows for the three effects:

| row | trace_width | map_op lookups | what those map_ops are |
|-----|-------------|----------------|------------------------|
| `revokeVmDescriptor2R24` | 817 | 0 | — |
| `spawnVmDescriptor2R24` | 817 | 2 | cap-tree create (cap_root), NOT epoch |
| `refreshVmDescriptor2R24` | 817 | 0 | — |
| `revokeDelegationWriteCapOpenVmDescriptor2R24` | 1027 | 2 | cap-edge REMOVE (cap_root), NOT epoch |
| `spawnWriteCapOpenVmDescriptor2R24` | 1027 | 4 | cap-tree create + key pin, NOT epoch |
| `refreshDelegationWriteCapOpenVmDescriptor2R24` | 1027 | 2 | snapshot write (cap_root), NOT epoch |

**Confirmed: NONE of these rows carries a map_op or weld targeting limb 30 (epoch) or any
stamp limb.** The map_ops present are all cap-tree (`cap_root` limb 25) reshape ops. The prior
descriptor-cutover-CHECK agent's claim is accurate.

### 1e. Partial epoch-limb infrastructure already built?

`grep` for `epochAt.*limb`, `B_EPOCH`, `B_EPOCH_AT`, `epochStampLimb`, `delegation_epoch_at.*limb`
across `metatheory/Dregg2`, `cell/src`, `circuit/src`: **zero hits.** No partial infrastructure
exists. Limb 30 is the closest thing — an *openable but un-named, un-forced* parent-epoch limb.

---

## (2) THE GAP (precisely)

1. **`delegationEpochAt` (the child stamp) has no openable limb.** It lives only inside
   `record_digest` (limb 24) via the delegation snapshot serialization
   (`commitment.rs:816-832`). A light client cannot OPEN it, so the descriptor cannot
   FORCE a stamp write against it. This is the gap for all three residuals' stamp clauses.

2. **`delegationEpoch` (limb 30, parent counter) is openable but un-forced.** It has a
   dedicated limb that a light client CAN open, but no `B_EPOCH` constant and no force gate, so
   the revoke `+1` bump is bound-but-not-forced (a prover could witness an AFTER limb 30 that is
   NOT `before+1` on a revoke row and the descriptor would accept). This is the revoke residual's
   `epochStepParent` clause.

3. **The child `delegations := []` snapshot clear (revoke)** rides record_digest too, but that is
   a *cap/snapshot* concern, not strictly epoch geometry; it is forced today through the cap-tree
   remove map-op on limb 25 (`RevokeCapsTreeEncodes`) — only the stamp/counter legs are open.

So the cutover needs: **(a) a NEW openable stamp limb for `delegationEpochAt`**, and **(b) a
`B_EPOCH` name + force gate on the EXISTING limb 30** for the parent counter.

---

## (3) THE DESIGN

### 3a. The new limb: `B_EPOCH_AT` (stamp), reuse limb 30 as `B_EPOCH` (counter)

The epoch state is a **scalar** at the rotated-commitment level (the active cell's epoch as
one felt, `delegation_epoch & 0x7FFF_FFFF`), NOT a sorted-map root — so the **scalar
force-gate templates (§1b shapes 1 & 2) apply, NOT the map-op write gate**. This is materially
simpler than the cap-tree reshape: a `colEq`/weld/disc-style gate, no `map_ops` table op, no CR
machinery.

- **Limb 30 → `B_EPOCH = 30`** (Lean): add the symbolic constant + a `#guard B_EPOCH == 30`.
  Rust already emits it (`pre[30]`); no Rust producer change for the counter.
- **New limb 37 → `B_EPOCH_AT = 37`** (the stamp), making `V9_NUM_PRE_LIMBS 37→38`,
  `B_IROOT 37→38`, `B_STATE_COMMIT 38→39`, `B_SPAN 51→52`, `AFTER_BLOCK_OFF 51→52`. Rust:
  `pre[37] = BabyBear::new((cell.state.delegation_epoch_at(active) & 0x7FFF_FFFF) as u32)`.
  **Caveat:** `delegationEpochAt` is a `CellId → Nat` MAP. The rotated commitment commits ONE
  cell per row. So the stamp limb commits the **active cell's own stamp**. For revoke (which
  resets the CHILD's stamp, not the active/parent's) and spawn (stamps the CHILD at birth) the
  forced write is on the **child's row**, not the parent's — the multi-cell choreography already
  used for cap-edge writes (the child cell rotates its own block). This needs confirmation that
  each affected cell rotates its own block in these turns (the cap-family decode already assumes
  this for the snapshot writes — `RevokeCapsTreeEncodes` operates on the child block).

### 3b. The per-effect force gates (the simpler scalar shapes)

- **Revoke** (parent row): force AFTER limb 30 `= BEFORE limb 30 + 1` — an additive force gate
  `sel·(loc afterEpoch − loc beforeEpoch − 1) = 0` (a trivial variant of `discForceGate`, a
  constant *delta* rather than a constant *value*). (Child row): force AFTER `B_EPOCH_AT` to the
  constant `0` (a `discForceGate`-style force-to-constant).
- **Spawn** (child row): force AFTER `B_EPOCH_AT` `=` the parent's current epoch — a
  `permsVKWeldGate`-style weld to a declared-param column carrying `spawnEpochAtMap`'s value
  (the spawner's `delegationEpoch`, light-client-recomputable from the spawn params + parent's
  committed limb 30).
- **Refresh** (child row): force AFTER `B_EPOCH_AT` `=` parent's current epoch — same weld shape
  as spawn (`refreshEpochAtMap`).

All three are appended CONSTRAINTS over the existing `rotateV3WithRecordPin`/cap-write base;
selector-gated so pad rows vanish; each gets a forcing theorem (`..._forces`) + a negative tooth
(`..._rejects_wrong`) mirroring the perms/disc pattern exactly.

---

## (4) PHASED PLAN (staged-additive)

This is the SAME flag-day shape WAVE-1/2/3 already executed (NUM_PRE_LIMBS 35→37 for
disc/perms/vk/mode/fields_root). Re-run that play for the epoch limb.

**Phase 0 (FIRST CONCRETE STEP — additive, no VK cutover yet):** in
`EffectVmEmitRotationV3.lean`, add `def B_EPOCH : Nat := 30` + `#guard B_EPOCH == 30` (names the
already-deployed limb; zero geometry change, zero VK change). This is a pure naming refactor that
makes limb 30 addressable for the subsequent force gates and is independently committable/green.

**Phase 1 (add the stamp limb — geometry/VK change, staged-additive):** bump
`V9_NUM_PRE_LIMBS 37→38` (`cell/src/commitment.rs:658`), add `pre[37] = …delegation_epoch_at…`
(the active cell's stamp) in `compute_rotated_pre_limbs`, shift `B_IROOT/B_STATE_COMMIT/B_SPAN/
AFTER_BLOCK_OFF` (+1 / +1 / 51→52 / 51→52) in Lean, update `preLimbsAt_length 37→38` and the
chain-walk site count (the `chunk31` group structure: 38 limbs = 4-head + 11×3 body + 1 leftover,
so re-check the body-group arithmetic — the WAVE-3 comment at `:122-125` notes 37 = 4 + 11×3 with
NO leftover; 38 reintroduces an arity-2 leftover, mirroring the pre-WAVE-2 state). Prove the
commitment-binding keystone lifts (it is length-generic). **At this phase the limb is committed
but still frozen-or-free; no force gate yet** — the residuals still stand but the limb exists.

**Phase 2 (emit the force descriptors + prove forcing):** define `epochCounterForceGate` (revoke
parent +1), `epochStampForceGate` (revoke child →0, spawn/refresh child →declared param), append
to the revoke/spawn/refresh V3 bases, prove `..._forces` + `..._rejects_wrong`. Prove
`revokeDelegation_descriptorRefines` / spawn / refresh now FORCE the epoch clauses (replace the
named-residual conjunct with a forced-from-gate derivation in
`RotatedKernelRefinementCapFamily.lean` and `EffectRefinement{,Batch2}.lean`).

**Phase 3 (re-emit + re-pin + cutover):** re-emit the TSV
(`rotation-wide-registry-staged.tsv`) with the new limb + gates (the emit path is the
`EmitWideRegistryProbe.lean` / wide-registry emitter), re-pin the FP/golden differential
(the `fields_root_key_felt_matches_lean`-style differential for the new rows), re-point the apex
(`CircuitSoundnessAssembled.lean` — the `revokeDelegationFullCircuitStep` /`spawnFullCircuitStep`/
`refreshDelegationFullCircuitStep` now derive the epoch clauses from the gate, dropping the named
residual conjunct), drop the three `*EpochResidual` defs (or keep as proved lemmas).

---

## (5) RISKS (quantified)

- **VK-affecting: YES, moderate.** Phase 1 grows the per-block geometry `B_SPAN 51→52`
  (+1 limb/block × BEFORE+AFTER = +2 columns, plus the iroot/state_commit/chain-carrier shifts
  and the appendix span `2·B_SPAN + C_SPAN`). The deployed staged rows are `trace_width = 817`
  (base) / `1027` (cap-open). The added limb plus its force gate adds a small bounded number of
  columns + a handful of constraints per epoch row — same magnitude as the WAVE-3 mode/fields-root
  flag-day (35→37 = +2 limbs). All three epoch effects share the SAME limb geometry, so it is ONE
  geometry change covering all three. **The VK changes for the revoke/spawn/refresh rows only**
  (and any row that re-chains through the widened block — i.e. the whole registry re-pins, as in
  WAVE-3). FP/golden re-pin required.
- **One shared limb serves all three:** YES for the STAMP (`B_EPOCH_AT`) — all three write the
  child's `delegationEpochAt` and differ only in the forced value (0 / spawn-map / refresh-map),
  which is a per-effect gate, not a per-effect limb. The parent COUNTER force (revoke only) reuses
  the existing limb 30. So: ONE new limb + ONE shared `B_EPOCH` naming + THREE small per-effect
  gates.
- **Multi-cell choreography risk (the real subtlety):** revoke/spawn reset/stamp the CHILD's
  stamp while the parent's counter moves on the parent. The stamp limb commits the *active cell's*
  stamp, so the child must rotate its OWN block for the force to bind the right cell. The cap-family
  decode already rotates the child block for the snapshot clear (`RevokeCapsTreeEncodes`), so the
  hook exists — but Phase 2 must confirm the stamp gate fires on the correct (child) block, not the
  parent's. This is the one place to get wrong.
- **Blast radius:** the rotated refinement layer is broad — `RotatedKernelRefinementCapFamily.lean`
  (the §3.EPOCH structure + `revokeDelegation_descriptorRefines`/`_execFullA`), the three
  `*FullCircuitStep` defs + `*_circuit_refines_spec` theorems in `EffectRefinement{,Batch2}.lean`,
  and the apex assembly `CircuitSoundnessAssembled.lean`. The geometry shift (B_SPAN/offsets)
  touches every keystone that reads block offsets, but those are length/offset-generic (the
  WAVE-3 cutover proved this), so the blast is "re-pin the offsets + the FP", not "re-prove the
  cryptographic core". `RotatedKernelRefinementMisc.lean` and the closure files (`ClosureAll.lean`)
  also reference these residuals and re-thread.

---

## (6) VERDICT

**Tractable, and notably EASIER than the cap-reshape cutovers** — because the epoch state is a
**scalar** limb, not a sorted-map root. It uses the cheap scalar force-gate templates
(`permsVKWeldGate` / `discForceGate`), NOT the `map_ops`/CR write machinery. Half the work is
already done: limb 30 (the parent counter) is ALREADY a deployed openable committed limb; it just
lacks a symbolic name and a force gate.

**Size: medium.** ~1 new limb (the `delegationEpochAt` stamp), ~3 small per-effect force gates +
their forcing/rejection teeth, the geometry shift (B_SPAN 51→52), and the registry re-pin + FP +
apex re-point. This is a direct re-run of the WAVE-3 mode/fields-root flag-day, which is a proven,
bounded play in this codebase.

**VK-cost: one geometry cutover** (the whole staged registry re-pins, as every flag-day did) — a
single deploy, not three. Ember-gated only insofar as any VK-affecting change is; per the
"don't over-ember-gate" directive, drive it to green + commit.

**The one genuinely-new wrinkle** vs the prior waves: the multi-cell choreography (the stamp is
the CHILD's, the counter the PARENT's, written on different blocks of the same turn). The cap-family
decode already rotates the child block, so the hook exists — Phase 2 must pin the gate to the right
block. That is the single thing to verify carefully, not a blocker.

**Recommended first concrete step:** Phase 0 — add `def B_EPOCH : Nat := 30` + its `#guard` in
`EffectVmEmitRotationV3.lean`. Zero geometry/VK change, independently green, and it converts limb 30
from an anonymous freely-witnessed limb into the named, addressable target the revoke counter-force
gate needs. It also makes the codebase honestly reflect that the parent epoch counter is ALREADY
openable — closing the documentation gap the campaign premise revealed.
