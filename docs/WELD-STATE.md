# WELD-STATE — the grounded carrier-deployment / universal-fold weld map

*Grounded to git HEAD `956b8be93` (working tree clean; `origin/main` at `53a3b4336`,
local main ahead by 2). Written 2026-07-01. This is a READ-ONLY census: what is
built-and-committed vs what is the-emit-not-yet-run, so we weld the RIGHT thing.*

*EXTENDED 2026-07-02 at HEAD `bae447985` (14 commits past `956b8be93`): §1f (the
CAP-WRITE FAMILY CLOSE — landed since this map was written), plus inline
`[@bae447985]` corrections where the newer HEAD moved a line or sharpened a claim.
Everything marked `[@bae447985]` is re-verified against that HEAD; full grounding
in `docs/reference/faithful-commitment.md`.*

> Reconcile-first note. The two topic memories (`project-carrier-deployment-architecture.md`,
> `project-universal-fold-buff-lightclient.md`) are dated 2026-06-30/07-01 and their
> commit hashes are UNRELIABLE against HEAD — e.g. the memory calls `356f55b68` "the
> INSERT-shaped keystone accumInsert_writesTo8 + apex Rfix," but git shows `356f55b68`
> is a notecreate negative-tooth test commit. The memory prose describes branch states
> that got re-ordered on merge. Everything below is verified against the code at HEAD,
> not the memory.

---

## 0. TL;DR — the two-sentence state

The **faithful-state-commitment VK-epoch is DONE and on main**: all six committed roots
(cap · heap · fields · nullifier · commitments · cells) are deployed faithful 8-felt at
v11 geometry, `#assert_axioms`-clean, the accumulator-insert `noteSpend` residual closed.
The **carrier universal-fold mechanism is BUILT for all 7 carriers but DEPLOYED for only
one** (custom): the leaf + binding-node + negative-tooth + Lean refutation are committed
for every carrier, but the *third edge* (teeth == committed-authority in the deployed AIR)
+ the deployed-path wiring exist ONLY for custom. **The big bang is NOT fireable as one
shot yet** — the per-carrier Step-1 teeth-emit (the security-critical acceptance gate) and
the witness-socket generalization are unbuilt for the other six.

---

## 1. What the VK-epoch just landed + what it UNBLOCKED

The epoch that "just finished" is the **faithful state commitment** (the v9→v10→v11
geometry campaign). It widened the DEPLOYED per-cell state commitment from ~31-bit folds
to faithful 8-felt Merkle roots. This was the *precondition* the carrier bang was blocked
on: memory `project-carrier-deployment-architecture.md` §BLOCKER — "ANCHOR carriers to
FAITHFUL committed forms ONLY — never a 31-bit fold." Now the anchors are faithful.

### 1a. Geometry at HEAD (verified)

| Const | Value at HEAD | Location |
|---|---|---|
| `NUM_PRE_LIMBS` | **88** (v11) | `circuit/src/effect_vm/trace_rotated.rs:90` |
| `V9_NUM_PRE_LIMBS` | **88** | `cell/src/commitment.rs:702` |
| `B_SPAN` | **119** | `circuit/src/effect_vm/trace_rotated.rs:97` |
| `CAP_OPEN_SPAN` | **329** | `trace_rotated.rs:2273` |
| `WIDE_WIDTH` | `GRAD_ROT_WIDTH + 480` | `trace_rotated.rs:3341` `[@bae447985]` |

Path: `37 (v9) → 67 (v10, +8-felt state) → 88 (v11, +21 accumulator-8-felt lanes 67..87)`;
`B_SPAN 51 → 91 → 119`. (Two stale prose comments still say "67" / "37" —
`effect_vm_descriptors.rs:1961`, `effect_vm_rotation_flip.rs:58` — dead comments, not live
consts.)

### 1b. The six roots — all deployed faithful 8-felt

Each root is pinned by `rfl` in the apex registry `v3RegistryHeap`
(`metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean`), forcing a faithful 8-felt
write/insert (never the lane-0 squeeze):

| Root | After-spine descriptor | Shape | Apex pin |
|---|---|---|---|
| cap_root | `effCapOpenWriteV3` (`CapOpenEmit.lean:585`) — `[@bae447985]` now ONE of THREE shapes; the full cap-write family (insert/remove/update, all 8 effects) is §1f | update / insert / remove | `Rfix 12` + the §1f family pins |
| heap_root | `effHeapWriteV3` (`HeapOpenEmit`) | update-at-key | `Rfix 56`, pos 45 |
| fields_root | `effFieldsWriteV3` (`FieldsOpenEmit`) | update-at-key | `Rfix 39`, pos 55 |
| nullifier_root | `effAccumInsertV3` (`some SEL_NOTE_SPEND`) | sorted-INSERT | `Rfix 27`, pos 56 |
| commitments_root | `effAccumInsertV3` (`none`) | sorted-INSERT | `Rfix 28`, pos 57 |
| cells_root | `effAccumInsertV3` (`none`) | sorted-INSERT | `Rfix 17`, pos 58 |

The three update-at-key roots share the cap-open after-spine template; the three
accumulators use the INSERT-shaped keystone (non-membership + splice) —
`AccumulatorInsertEmit.lean` + `SortedTreeNonMembershipHeap8.lean`.

### 1c. The noteSpend residual — CLOSED at HEAD

The `a52c2f6cb` gap ("noteSpend value-col gap") was: the deployed `valueCol = NOTE_VALUE_LO`
is per-row economically constrained (must be 0 on padding), irreconcilable with
`effAccumInsertV3`'s UNCONDITIONAL per-row VALUE-bind. **Closed by `e1a0ebaf5`**
(`feat(accum8 noteSpend): selector-gate the insert KEY/VALUE binds`): the KEY/VALUE binds
became `sel·(leaf−col)=0` — active on the firing row, vacuous on padding; MEMBERSHIP +
rootPin welds stay unconditional. noteSpend passes `some SEL_NOTE_SPEND`; noteCreate /
createCell pass `none` (byte-identical, no drift). All three insert families PROVE+VERIFY;
`effect_vm_wide_roundtrip.rs` has no `#[ignore]`.

### 1d. Degraded-felt gate + the one remaining residual

`.ast-grep/rules/faithful-commitment-felt.yml` is LIVE on main with **two** rules:
`degraded-felt-commitment` (`fold_bytes32_to_bb`) and `replicated-felt-commitment`
(`[$X; 8]` replicate); `scripts/check-no-degraded-felt.sh` + a `ci.yml` job enforce it over
`commitment.rs` / `rotation_witness.rs` / `trace_rotated.rs`.

**One genuine open, explicitly allowlisted (NOT a root):** the flat per-record field limbs
`fields[0..7]` still fold 32B→1 felt (~31-bit) — `cell/src/commitment.rs:990`,
`turn/src/rotation_witness.rs:360` (`// ast-grep-ignore … residual`). The pre_limbs 67..87
are "zero-filled until producer-welded." `[@bae447985]` precision: that zero-fill is the
TWO FLAT-RECORD TWINS ONLY (`cell/src/commitment.rs` `compute_rotated_pre_limbs` +
`turn/src/rotation_witness.rs`, per the const comments at `commitment.rs:702` /
`rotation_witness.rs:67`); the CIRCUIT TRACE producers DO fill genuine
`CanonicalHeapTree8::root8()` into the accumulator lanes (nullifier 26‖67..73
`trace_rotated.rs:1094-1110`, commitments 27‖74..80 `:1272-1287`, cells 0‖81..87
`:1192-1207` — commit `cbaf7b05b`). Also `[@a1a627d4d+]` CORRECTION: the whole-image STATE_COMMIT digest flag-day
ALREADY FIRED (`9e5a83935`, 2026-06-19) — `compute_canonical_state_commitment_v9_felt8`
(`commitment.rs:1219`) IS the deployed end-to-end 8-felt binding (producer/executor/LC);
the earlier "staged" reading here quoted a stale header comment (since fixed). The one
load-bearing ~31-bit LC surface left is the `transferCapOpenTB` 1-felt V3-registry
fallback (`full_turn_proof.rs:4285-4295`, the sole cap-open key without a wide twin) —
the transferCapOpenTB wide-twin grind is its named close. This is the `fields[0..7]` / flat-mem grind, a
named follow-up — it is NOT one of the six Merkle roots and does NOT block the carrier bang
(carriers anchor to the roots, not the flat field limbs). But it IS a ~31-bit surface still
standing; flag it as the standing crumb.

### 1e. What this UNBLOCKS

Carriers may now anchor their teeth to FAITHFUL 8-felt committed forms (the six roots)
instead of the 31-bit folds the memory's §BLOCKER forbade. `[@wave-1 7c4257824]`
CORRECTION for factory: the six ROOTS are faithful, but the cells_root LEAF CONTENTS are
still 1-felt `(key, key)` and col 69 holds the owner-key fold, NOT child_vk — so factory
gained no usable anchor from this epoch (see §3 factory row + §5 item 9); the DEEPEST
carriers can anchor to faithful roots.
The MerkleHash/node8 primitive the campaign forged (arity-16 node8, `CHIP_RATE 16` —
`[@bae447985]` the const lives in `circuit/src/descriptor_ir2.rs:279`) is the
shared hash gadget the hash-heavy carrier family (custom-routing, dsl, membership path,
cap-crown Hash3Cap) needs — it now exists.

### 1f. `[@bae447985]` THE CAP-WRITE FAMILY CLOSE — landed since this map was written

Commits `48d981698..bae447985` (the 14 past `956b8be93`). **All 8 cap-writing effects
now ride SHAPE-MATCHED keystones** — the update-at-key `effCapOpenWriteV3` (§1b) grew an
INSERT and a REMOVE twin, and every cap-write was rewrapped:

| shape | keystone | effects (wrapper → Rfix pin) |
|---|---|---|
| INSERT ×4 | `effCapInsertV3` (`CapOpenEmit.lean:661`; `capInsert_writesTo8` `CapInsertEmit.lean:123` — genuine non-membership bracket + spliced membership) | delegate (`Rfix 1`, pos 46) · introduce (`Rfix 10`, 47) · delegateAtten (`Rfix 11`, 48) · spawn (`Rfix 19`, 52) |
| REMOVE ×2 | `effCapRemoveV3` (`CapOpenEmit.lean:680`; `capRemove_writesTo8` `CapRemoveEmit.lean:120` — tombstone ZERO-fold) | revoke/revokeDelegation (`Rfix 2`/`Rfix 14`, pos 49) · revokeCapability (deployed route — but see the seam below) |
| UPDATE ×2 | `effCapOpenWriteV3` (`CapOpenEmit.lean:585`; §11/§12 `:1747-1990`) | attenuate (`Rfix 12`) · refreshDelegation (`Rfix 55`, pos 50) |

**Root cause (why this was a LIVENESS break):** the heap-8-felt migration made the
witness heaps `CanonicalHeapTree8`, which made every scalar arity-2 cap map-op
**shape-UNSAT for an HONEST prover** (`sdk/src/full_turn_proof.rs:7111`; commit
`48d981698` names the shape gap: `writesTo8` was UPDATE-at-key only, but
delegate/insert/revoke *change the cap key-set* — no shared before/after path). The gap
sat unexercised while the SDK test suite carried 7 `E0308` compile breaks lagging the
same migration (`5ea008aab` — "the big-bang `--tests` check was truncated by a
disk-full moment"). The arity-2 map-op `_forces_write` theorems were deleted as
shape-UNSAT (`6a7283580`); the registries were regenerated + FP-re-pinned
(`824c2963e`, `136de6281`, `bae447985`) — registry length stays 59 (the wrappers were
REWRAPPED in place, not appended).

Rust: `CanonicalCapTree::{insert_witness,remove_witness}` (`circuit/src/cap_root.rs:768`,
`:818`) + the three-shape router `build_effect_vm_cap_open_leg`
(`sdk/src/full_turn_proof.rs:2845`: `:2898` update / `:2915` insert / `:2936` remove).
Teeth: witness unit teeth `cap_root.rs:1015-1556` (`bd5a6e5b5`); prove+verify leg tests
per effect + the no-silent-forge REMOVE tooth `full_turn_proof.rs:7124` (`c2d9feabd`,
`bae447985`). Apex: the `Rfix` pins above are `#assert_axioms`-clean
(`CircuitSoundnessAssembled.lean:761-767`).

**One honest seam:** `Rfix 24` (revokeCapability) still pins the authority-only
`revokeCapabilityCapOpenV3` (`CircuitSoundnessAssembled.lean:525`), while the deployed
prover proves the REMOVE write wrapper whenever the node supplies the c-list witness
(named empty-c-list fallback — `full_turn_proof.rs:2331-2352`, "named, not a silent
forge"). The Lean write wrapper + `ClosureAll` rung exist
(`revokeCapabilityWriteCapOpenV3` `CapOpenEmit.lean:716`;
`revokeCapability_closedLog_capOpenSat` `ClosureAll.lean:971`); moving the `Rfix 24`
pin is the open apex-registry step.

Also landed in the same span: the portable relative mathlib path restored
(`metatheory/lakefile.toml:10` → `../../../src/mathlib4`, commit `d3c16c7f1`).

**What this means for the carrier map below:** nothing in §2–§6 regresses; the
cap-write close is a §1-family (faithful-commitment) completion. The cap-root anchor
carriers weld to is now written by ALL 8 cap-writes through circuit-forced keystones —
strictly better anchoring for the third-edge builds.

---

## 2. Carrier universal-fold mechanism — built vs deployed (per-carrier)

All 7 carriers have leaf + binding-node + negative-tooth + Lean refutation COMMITTED as
reusable primitives. Corpus is sorry-free; `#assert_axioms` present in every refute file.
**Only `custom` is flipped to the positive floor proof AND wired into the deployed
aggregation path.** The other six are staged library primitives + refutations — NOT on the
deployed light-client fold.

| carrier | leaf | binding node | negative tooth | refute (BackingAttack) | BindingFromFold (positive)? | deployed-wired? |
|---|---|---|---|---|---|---|
| **custom** | `custom_leaf_adapter.rs:994/1179` | `joint_turn_recursive.rs:591` | `joint_turn_recursive.rs:1174` + integration `tests/custom_binding_deployed_tooth.rs`, `custom_binding_production_path.rs` | — (superseded) | **YES** `CustomBindingFromFold.lean` (7 pins) | **YES** (buff-in-production) |
| bridge | `bridge_leaf_adapter.rs:170/227` | `joint_turn_recursive.rs:797` | `bridge_leaf_adapter.rs:353` + `tests/bridge_binding_mechanism.rs` | `BridgeBackingAttack.lean` (7) | no | no |
| sovereign | `sovereign_leaf_adapter.rs:181/221` | `joint_turn_recursive.rs:898` | `sovereign_leaf_adapter.rs:375` | `SovereignBackingAttack.lean` (10) | no | no |
| factory | `factory_leaf_adapter.rs:177/214` | `factory_leaf_adapter.rs:338` | `factory_leaf_adapter.rs:468/590` | `FactoryBackingAttack.lean` (12) | no | no |
| hatchery | `hatchery_leaf_adapter.rs:176/214` | `hatchery_leaf_adapter.rs:343` | `hatchery_leaf_adapter.rs:477/595` | `HatcheryBackingAttack.lean` (8) | no | no |
| membership | `membership_leaf_adapter.rs:197/235` | `membership_leaf_adapter.rs:431` | `membership_leaf_adapter.rs:574` + `tests/membership_binding_mechanism.rs` | `MembershipBackingAttack.lean` (8) | no | no |
| dsl (Dfa) | `dsl_leaf_adapter.rs:112` — REUSES `prove_custom_leaf_with_commitment` | `dsl_leaf_adapter.rs:141` — REUSES `prove_custom_binding_node_segmented` | `dsl_leaf_adapter.rs:321` | `DslBackingAttack.lean` (7) | no | no |

Provenance: bridge/sovereign landed `aa34a6244`; factory/hatchery/membership `9cade93a2`;
dsl `02ef3cdd7`; `CustomBindingFromFold` `fa496cfa7`.

### Shared plumbing (the big-bang integration layer)

- **`prove_descriptor_leaf_dual_expose_at`** (`ivc_turn_chain.rs:1526`) — **GENERALIZED,
  done.** Parametric `(claim_pi_lo, claim_len)`; the old hardcoded `_dual_expose`
  (`:1481`, `CUSTOM_COMMIT_PI_LO=46`) is now a convenience wrapper. Step-3 of the uniform
  build is ready for every carrier.
- **`prove_chain_core_rotated`** (`circuit-prove/src/ivc_turn_chain.rs:2818`) — **only the
  custom arm is wired** (`match &leg.custom_witness`, `:2886`). No bridge/sovereign/
  factory/hatchery/membership/dsl witness arm exists. Step-5 done for custom only.
- **Witness socket** — **NOT generalized.** `RotatedParticipantLeg`
  (`joint_turn_aggregation.rs:6`) still carries a single `pub custom_witness:
  Option<CustomWitnessBundle>` (`:125`). No `carrier_witness: Option<CarrierWitness>` enum
  exists in the tree. Step-2 done for custom only.

### The other staged big-bang inputs

- **G5 capacity satisfaction (17/18/19)** — welds BUILT: `circuit/src/effect_vm/
  discharge_weld.rs`, `vault_weld.rs`, tests `discharge_obligation_air_teeth.rs`,
  `settle_escrow_capacity_weld.rs`, `gentian_carrier_floor_prove.rs`; Lean
  `metatheory/Dregg2/Deos/CapacitySatisfaction.lean`. (Note: the escrow floor's v11
  geometry drift was the LAST commit `956b8be93` — `settleEscrow` AFTER-gate cols
  v10→v11, `B_SPAN 51→119`.) Staged; the emit+producer-fill is part of the bang.
- **flat-mem boundary** — `satisfied2_init_root` + the `whole_image_fold_bound_mem_
  forged_minit_refuses` tooth built (memory §ALSO BUILT); the per-effect `setFieldDyn` VK
  weld is the bang piece. This overlaps the `fields[0..7]` residual (§1d).
- **The apex** (`lightclient_unfoolable` + assembled/forest/closure) is
  `#assert_axioms`-clean at HEAD (`docs/reference/lean-circuit.md`; pins at
  `CircuitSoundnessAssembled.lean:752-775`).

---

## 3. THE FAIL-OPEN LAW / THIRD-EDGE status per carrier

The load-bearing law (memory §"THE LOAD-BEARING LAW"): the *connect* alone is VACUOUS —
the leaf re-proves whatever tuple the prover hands it; the binding node enforces
`leg.teeth == leaf.tuple`, but a forger fills both with arbitrary `T`. Soundness needs the
**THIRD EDGE**: `leg.teeth == committed-authority`, enforced IN THE DEPLOYED AIR (a
PiBinding/gate tying the emitted PI to a committed-state limb). This is Step-1 of the
uniform build — the security-critical acceptance gate. Steps 2–5 without it = a vacuous
binding.

**The BackingAttack refutations ARE the proof that the third edge is currently ABSENT for
the six non-custom carriers** — each `*BackingAttack.lean` exhibits a forged input the
deployed proof accepts but a re-executor rejects (vacuous-as-deployed-LC). That is by
design: the campaign refutes its own green first, then repairs.

| carrier | depth | authority committed today? | third edge (in-AIR teeth==committed) | Step-1 remaining |
|---|---|---|---|---|
| **custom** | — | yes (PI 46–49 deployed) | **PRESENT** | none — buff-in-production. (NB: the deeper per-turn `proofBind True→boundAt` in-AIR flip + 4→8-felt lift is a SEPARATE deployed VK epoch, still pending — `docs/reference/lean-circuit.md` §Custom, `CustomApex.lean`. The recursion-tree fold is what's buffed.) |
| **factory** | SHALLOW→**BLOCKED-ON-WIDENING** | `[@wave-1 7c4257824]` CORRECTED: child_vk is NOT committed at HEAD in ANY in-AIR form, at any width. Rotated PI 38 carries the born cell's vm KEY = `hash_to_bb(owner_pubkey)` under the MISNOMER `child_vk_derived` (`turn/src/executor/effect_vm_bridge.rs:131-139`); the actual installed authority `effective_vk` (`apply.rs:2376-2421`) never reaches the VmEffect at all; the cells leaf is `(key, key)` with 1-felt contents (`trace_rotated.rs:1167-1189` — 8-felt-ness is in the DIGESTS only, `HeapLeaf` = 1-felt addr + 1-felt value); params carry no vk limbs (factory uses param0/param1 only, both ~31-bit `fold_bytes32_to_bb` folds); the born cell's state block is off-row, bound only via byte-domain blake3 `effects_hash` (Lean `EffectVmEmitCreateCellFromFactory.lean` §RT) | absent | the third edge CANNOT be built until a faithful committed carrier of child_vk EXISTS — a WIDENING epoch first (§5 item 9: three routes + blast radii). Do NOT expose unanchored witness-column teeth (6 free param cols exist — using them = the vacuous connect). Derivation (child_vk=Poseidon2(factory_vk‖params)) = named off-AIR. |
| **dsl** | SHALLOW | Witnessed{Dfa} `⇒ None` — commits NOTHING (`mod.rs:462`) | absent | Layer A (non-VK): split out of None → tag-20 manifest entry riding caveatCommit→PI 45. Layer B (VK): `dfaPiExposure`. Reduces to Poseidon2-CR. |
| **membership** | SHALLOW | authorized_root committed as pointer (PI 45) + value (fields_root); sender as OWNER_CELL_ID | absent | expose (sender_leaf, authorized_root) PIs. RECOMMENDED: redefine membership leaf domain to 4-felt OWNER_CELL_ID → sender tie is a plain connect (no in-AIR Poseidon2 re-derive). Merkle path stays off-AIR (named). |
| **hatchery-invariant** | SHALLOW | invariant_digest === child_program_vk === FACTORY's child_vk | absent | RIDES factory's CreateCellFromFactory leg + one extra connect to a re-proved contract-attestation leaf. SHARES factory teeth. |
| **bridge** | **DEEPEST** | the 26-limb tuple is ENTIRELY uncommitted; mint_hash read in ZERO constraints | absent | ⚑ folding `bridge_action_air` is UNSOUND (prover-chosen tuple, no Merkle/key). SOUND path: re-prove the REAL foreign note_spend STARK as a foldable G2 leaf (`note_spend_leaf_adapter.rs`, new), recompute mint_hash in-circuit, connect to a newly-exposed mint_hash PI on `mintV3`. Double-mint = orthogonal re-exec nullifier guard. |
| **hatchery-contract** | **DEEPEST** | contract_hash stored-only (SDK `MintedKind.hpres`), off-VK, read by zero constraints | absent | NEW on-VK binding: add contract_hash[8] teeth on FactoryDescriptor + its hash. (The invariant half is shallow, rides factory.) |
| **sovereign** | **DEEPEST** | owner key IS committed (BLAKE3 leaf `commitment.rs:209` + v9 r23 + content-addressed CellId) → `KEY_COMMIT=Poseidon2(pubkey)` is sound; teeth are prover-free PiSlot self-pins | **partial** — the 4-felt `SOVEREIGN_WITNESS_KEY_COMMIT` teeth columns exist (`columns.rs:274`, `air.rs:190`) but are prover-free self-pins; the inner transition-proof VK is sentinel-zero (`pi.rs:240`, STAGED) | P1 (non-VK): socket + producer fill the dead-zero teeth (`cipherclerk::prove_sovereign_turn_rotated` has `before_cell.public_key()`) + sovereign arm. P2 (VK, load-bearing): named rotated pubkey limb + `IS_SOVEREIGN_CELL`-gated in-AIR `Poseidon2(pubkey_limb)==teeth` → forged key UNSAT. Ed25519 stays off-AIR (verified `authorize.rs:889`). |

"committed-in-state ≠ grounded-in-fold" (sovereign: pubkey IS committed but teeth are
prover-free self-pins → needs the grounding hash-site).

### `[@wave-2]` BANG WAVE (sovereign) — the third edge is BLOCKED-ON-WIDENING (stop-condition)

Grounded at HEAD `746435722`. The sovereign third edge was ATTEMPTED and the
stop-condition fired — the SECOND carrier after factory to hit a widening wall (this
supersedes this row's earlier "partial, P1-then-P2 is a per-carrier wave" reading).

**What is real (verified in-source):** the owner pubkey IS committed and the teeth
columns DO exist — that part of the anchor is sound:
- `KEY_COMMIT` teeth cols exist: `columns.rs:274-277` (aux 23..26) + PI pins
  `air.rs:189` / `pi.rs:240`; leaf + binding node + refutation all committed
  (`sovereign_leaf_adapter.rs`, `joint_turn_recursive.rs:900`,
  `SovereignBackingAttack.lean`).
- The pubkey is committed into the FAITHFUL ~124-bit 8-felt authority digest
  (`compute_authority_digest_8` = `blake3(authority_residue_bytes)` where
  `authority_residue_bytes` absorbs `cell.public_key`, `commitment.rs:849`) and into the
  whole-state BLAKE3 commitment (`:209`). Both are genuinely faithful (not 31-bit).

**Why the FAITHFUL third edge is NOT buildable at HEAD (the wall):** P2 requires an
in-AIR gate `Poseidon2(pubkey_limb) == teeth` anchored to a FAITHFUL COMMITTED pubkey.
But the owner pubkey enters felt-commitment form **only through BLAKE3 folds**
(`commitment.rs:209/849/1850` — verified: those are the *only* sites) — it is NOT carried
as a Poseidon2/AIR-reconstructable committed column anywhere in the rotated trace
(`grep pubkey circuit/src/effect_vm/trace_rotated.rs` = 0 hits). The teeth today are
row-0 self-pins (aux == PI boundary, `trace.rs:1005-1014`), off-AIR recomputed by the
executor (`proof_verify.rs:2548 pubkey_to_witness_key_commit`); the fold's binding node
`connect`s leg.teeth == leaf.key_commit (both prover-controlled — the vacuous connect the
fail-open law forbids). To make the teeth non-forgeable in-AIR you need the pubkey as a
committed AIR-reconstructable form, and there are exactly two routes, both bigger than a
per-carrier wave:
  - **(a) geometry widening** — surface the pubkey as named rotated pre-limbs feeding
    `compute_rotated_pre_limbs` → `wireCommitR` → `state_commit`. `V9_NUM_PRE_LIMBS` is
    fully allocated at 88 (limbs 67..87 are the accumulator-8-felt completion, §1d — no
    free/reserved slot), so this GROWS the vector = a v12 geometry epoch: ALL rotated VKs
    move, keystone re-grounds, registry-wide regen + `Rfix` re-pins, devnet re-genesis.
    The direct mirror of factory's §5 item-9 route (a).
  - **(b) in-AIR Ed25519** — verify the owner signature over `(key_commit, sequence,
    anchor, new)` in-circuit, forcing `key_commit` to a verifying key. This is the NAMED
    TERMINAL crypto seam the leaf docstring (`sovereign_leaf_adapter.rs:50-59`), the
    binding-node seams (`joint_turn_recursive.rs:895`), and `SovereignBackingAttack.lean`
    §C all already name as off-AIR. Not a per-carrier wave.

Recomputing the committed BLAKE3 authority digest in-AIR from pubkey felts (to bind teeth
to the existing faithful anchor without widening) is terminal-infeasible — BLAKE3 is not
AIR-friendly (the reason it is the named off-AIR seam).

**Decision:** do NOT run P1 in isolation. P1 (fill the dead-zero teeth + set
`is_sovereign_cell = 1` + the sovereign witness arm) changes deployed sovereign-proof PI
VALUES with ZERO soundness benefit absent P2, and wiring the fold + flipping
`SovereignBackingAttack → SovereignBindingFromFold` on P1 alone would LAUNDER VACUITY
(the connect stays forger-controlled). The `SovereignBackingAttack.lean` refutation
STANDS (correct at HEAD). The sovereign third edge is blocked behind an ember-decision on
route (a) vs (b), exactly like factory. hatchery-contract/bridge (the other DEEPEST) are
unaffected by this finding.

---

## 4. THE BIG BANG — is it fireable now? NO. Here's the exact remaining emit.

The memory says "every mechanism built; the bang is purely the emit+regen+flip." That is
TRUE for **custom** and TRUE for the faithful-commitment anchors. It is **NOT yet true**
for the other six carriers' third-edge teeth, nor for the witness-socket generalization.
The bang as one coordinated regen is **NOT fire-able** until those Step-1/Step-2/Step-5
pieces land per carrier.

### What IS ready to fire (built + committed)
- Faithful 8-felt anchors (the six roots) — the precondition. DONE.
- The node8 hash primitive (arity-16, `CHIP_RATE 16`) — the shared hash gadget. DONE.
- `prove_descriptor_leaf_dual_expose_at` — parametric Step-3. DONE.
- All 7 carrier leaves + binding nodes + negative teeth + Lean BackingAttack refutations. DONE.
- Custom: third edge + deployed wiring + `CustomBindingFromFold` positive. DONE (production).
- G5 17/18/19 satisfaction welds + flat-mem boundary anchor. STAGED.
- The apex `#assert_axioms`-clean at current VKs. DONE.

### What must be BUILT before the bang (the actual remaining emit, ordered)
Per carrier (the uniform 5-step build; Steps 3 is done shared, so per carrier = 1,2,4,5):
1. **Step-1 teeth-emit + THE THIRD EDGE** (per carrier, security-critical): on the
   carrier's deployed descriptor add the `PiBinding{First}` publishing the authority tuple
   at TAIL slots `[CARRIER_PI_LO..]` AND the in-AIR gate tying each emitted PI to its
   FAITHFUL committed-state anchor. Bump that descriptor's `public_input_count` only
   (per-descriptor, no ripple to the other 56). This is where the six are UNBUILT.
2. **Step-2 witness socket**: generalize `custom_witness: Option<CustomWitnessBundle>` →
   `carrier_witness: Option<CarrierWitness>` enum on `RotatedParticipantLeg`
   (`joint_turn_aggregation.rs:125`); per-carrier `from_bound_*` projection, fail-closed
   None off-wire. ONE shared restructure (clobber hazard — main-loop owned).
3. **Step-4 leaf + connect**: reuse the built leaf/node adapters. Zero new mechanism.
4. **Step-5 wire + tooth + flip refute→positive**: add the match arm in
   `prove_chain_core_rotated` (THE shared edit, clobber hazard); add a deployed-path fold
   tooth (twin of `custom_binding_deployed_tooth.rs`); flip `*BackingAttack.lean` →
   `*BindingFromFold.lean` positive.

Then, and ONLY then, the coordinated finale:
5. **ONE descriptor regen** exposing every carrier's tuple PIs + emit G5 17/18/19 + the
   flat-mem per-effect weld → **fill the producers** → **ONE apex re-verify**
   (`lightclient_unfoolable` + 5 AssuranceCase guarantees + `deployed_system_secure_grounded`
   clean under the new VKs) → **flip** the whole cluster (deployed default rotates once,
   gated human-go, + devnet re-genesis since commitment VALUES shift).

**Blast radius** (memory §BLAST RADIUS): per-descriptor `public_input_count` (no global
count); append at TAIL `[CARRIER_PI_LO..]`; never touch the shared `[0..46)` prefix. Each
carrier touches only {its bare + wide + welded descriptor} + 3 registry fingerprints.

---

## 5. NOT-FIRE-ABLE-YET — the honest list

1. **The one-shot big bang** — not fireable. Six carriers lack Step-1 (the third edge),
   Step-2 (witness socket), Step-5 (deployed wiring + positive flip). Firing a regen now
   would ship 2–5 without the tie = **vacuous binding** for those six (the exact fail-open
   the law forbids).
2. **The witness-socket generalization** (`CarrierWitness` enum) is unbuilt — a
   prerequisite for wiring any non-custom carrier into `prove_chain_core_rotated`.
3. **The two DEEPEST NEW bindings** are genuine multi-step builds, not emits:
   - bridge: the `note_spend_leaf_adapter.rs` G2 backing leaf (re-prove the real
     note-spend STARK) — folding `bridge_action_air` is UNSOUND, do not shortcut.
   - hatchery-contract: the new on-VK `contract_hash[8]` teeth.
4. **The Merkle-PATH / Hash* in-AIR re-verification** remains the single named TERMINAL
   off-AIR seam for the hash-heavy family (membership path, dsl routing, custom routing
   programs) until the node8 lane-witnessing chain is extended to chain a full Merkle path
   (the node8 primitive exists but `custom_leaf_adapter` still REFUSES chained Hash*/
   MerkleHash). This is the highest-leverage single build after the third edges.
5. **The `fields[0..7]` flat-record ~31-bit residual** (§1d) — allowlisted, self-deleting
   when fields-welded; not a root, does not block carriers, but is a standing ~31-bit
   surface to close.
6. **Custom's deeper per-turn `proofBind True→boundAt` + 4→8-felt lift** — a separate
   gated VK epoch (`CustomApex.lean`, `docs/reference/lean-circuit.md` §Custom). The
   recursion-tree fold is buffed; this in-AIR per-turn gate is a distinct deployment.
7. `[@bae447985]` **The revokeCapability `Rfix 24` apex pin** (§1f seam) — the deployed
   prover rides the REMOVE keystone; the apex registry pin still names the
   authority-only leg. One re-pin + re-verify, small and named.
8. `[@bae447985]` **The whole-image 8-felt STATE_COMMIT digest flag-day** (§1d
   precision) — component roots are faithful; the final 1-felt digest squeeze → 8-felt
   chip-chain cut (`commitment.rs:1219`) is the deliberately-gated separate epoch.
9. `[@wave-1 7c4257824]` **The factory child_vk COMMITTED-CARRIER widening** — the
   BANG-WAVE-1 stop-condition finding (supersedes this map's earlier "child_vk committed
   at PI 38" claim, which was WRONG at HEAD — see the corrected §3 factory row). The
   faithful anchor does not exist and every widening route is bigger than a per-carrier
   wave; pick ONE deliberately:
   - **(a) geometry widening (the true perms/vk pattern):** +8 pre-limbs carrying the
     born child's vk8 on factory rows (`NUM_PRE_LIMBS` 88→96, `B_SPAN` bump = v12
     geometry) — ALL rotated descriptors' VKs move, keystone re-grounds, registry-wide
     regen + Rfix re-pins. The v10→v11-scale campaign; the semantically cleanest anchor
     (the turn's own commitment binds what it birthed).
   - **(b) cells-leaf preimage extension:** factory's inserted leaf digests
     `chip_absorb(addr ‖ value ‖ child_vk[0..8))` instead of arity-2 — descriptor
     blast radius is factory-family-only, BUT forks the shared `HeapLeaf`/`digest8`
     (heap_root.rs, all accumulators) + needs a mixed-arity Lean sorted-insert keystone
     variant + is a cells_root record-SEMANTICS decision (factory-born records bind
     their birth authority; createCell-born stay `(key,key)`) — an ember-decision.
   - **(c) caveat-manifest tag entry:** child_vk8 as a tagged manifest entry riding the
     in-AIR chip-chained caveatCommit→PI 45 — the same pattern as dsl Layer A (wave 3);
     needs manifest-capacity + verifier-twin grounding; converges the factory lane onto
     the dsl/membership lane.
   ALSO under this item: the `child_vk_derived` MISNOMER (`effect_vm_bridge.rs:138`
   lowers `hash_to_bb(owner_pubkey)`) — whichever route lands must either rename the
   field to what it is (the born cell's vm key) or make it carry what it says; today it
   is neither, and the kernel key is `CellId::derive_raw(owner_pubkey, token_id)` (owner
   AND token) while the vm key folds owner_pubkey alone — a second named divergence.
   hatchery-invariant (which RIDES the factory teeth) is blocked behind the same item.
10. `[@wave-2]` **The sovereign third-edge WIDENING** — the BANG-WAVE (sovereign)
    stop-condition finding (§3 sovereign row `[@wave-2]` block). Unlike factory, the owner
    key IS committed faithfully (~124-bit 8-felt BLAKE3 authority digest), but ONLY through
    BLAKE3 folds (`commitment.rs:209/849`) — never as an AIR-reconstructable Poseidon2 limb.
    So P2's in-AIR `Poseidon2(pubkey_limb)==teeth` gate has no faithful anchor to bind, and
    surfacing one is a bigger epoch: (a) a v12 geometry widening adding the pubkey to the
    rotated pre-limbs (`V9_NUM_PRE_LIMBS` full at 88, no free slot — all rotated VKs move +
    registry regen + devnet re-genesis), or (b) in-AIR Ed25519 (the named terminal seam).
    P1 in isolation is forbidden (deployed-PI churn with no soundness gain; flipping the
    refutation on P1 alone launders vacuity). Blocked behind an ember-decision on route
    (a) vs (b). The `SovereignBackingAttack.lean` refutation STANDS.

---

## 6. THE SAFE ORDERED NEXT WELD-STEP (what to fire, how not to make it vacuous)

**Do NOT fire a descriptor regen / VK flip yet.** The safe next weld is a per-carrier
BUILD, not the bang. Recommended order (shallow-first — cheapest, exercises the shared
template, de-risks the socket before the DEEPEST binds):

1. **Build the `CarrierWitness` enum socket ONCE** (Step-2, main-loop owned — shared-file
   clobber hazard on `joint_turn_aggregation.rs`). Generalize `custom_witness` →
   `carrier_witness`, keeping custom as the first variant so nothing regresses.
   Fail-closed `None` off-wire (re-exec rung, never fabricated).

2. **FACTORY third edge first** (SHALLOW, and hatchery-invariant rides it):
   `[@wave-1 7c4257824]` **ATTEMPTED AND STOPPED — the stop-condition fired.** The
   instruction below assumed child_vk is committed 1-felt at PI 38; grounding showed it
   is not committed AT ALL (corrected §3 factory row) and every widening route is a
   bigger epoch (§5 item 9). The factory third edge is BLOCKED behind that widening
   decision; do not re-run this step until one of the §5-item-9 routes is chosen and
   landed. The rest of the guidance stands for THAT day: expose the faithful **8-felt**
   child_vk teeth gated against the landed committed carrier. ⚑ **Anti-vacuity guidance:
   DO NOT anchor the tooth at the 31-bit fold** (memory's "factory fold8 gate I almost
   shipped anchored child_vk to the 31-bit col69 = a single linear equation = fake") —
   and equally DO NOT expose unanchored witness-column teeth. The third edge must gate
   against the faithful committed form. Add the deployed-path fold tooth (twin of
   `custom_binding_deployed_tooth.rs`) — honest-accept + forged→UNSAT through
   `prove_turn_chain_recursive → verify_turn_chain_recursive` — and flip
   `FactoryBackingAttack.lean → FactoryBindingFromFold.lean`.

3. **membership + dsl** (SHALLOW, share the caveat-manifest pattern): membership via the
   4-felt OWNER_CELL_ID leaf-domain redefinition (plain connect, no in-AIR Poseidon2);
   dsl Layer A (non-VK manifest) then Layer B (dfaPiExposure).

4. **sovereign P1 then P2**: `[@wave-2]` **ATTEMPTED AND STOPPED — the stop-condition
   fired** (§3 sovereign row, the `[@wave-2]` block). P1 (non-VK) fills the dead-zero
   KEY_COMMIT teeth from `before_cell.public_key()` + adds the sovereign arm; P2 (VK)
   welds the `IS_SOVEREIGN_CELL`-gated in-AIR `Poseidon2(pubkey_limb)==teeth`. But P2's
   faithful anchor does not exist at HEAD: the owner pubkey is committed only via BLAKE3
   folds (`commitment.rs:209/849`), never as an AIR-reconstructable Poseidon2 limb, so the
   in-AIR gate needs either (a) a v12 geometry widening surfacing the pubkey as a rotated
   pre-limb (no free slot — `V9_NUM_PRE_LIMBS` full at 88) or (b) in-AIR Ed25519 (the
   named terminal seam) — both bigger than a per-carrier wave. Do NOT run P1 alone
   (changes deployed PI values with no soundness gain; flipping the refutation on P1 alone
   launders vacuity). Blocked behind an ember-decision on route (a) vs (b), like factory.
   Ed25519 stays off-AIR.

5. **bridge + hatchery-contract** (DEEPEST, own lanes): bridge = the `note_spend_leaf_
   adapter.rs` G2 backing leaf + mint_hash-in-circuit + `mintV3` PI expose (NEVER fold
   `bridge_action_air`); hatchery-contract = the `contract_hash[8]` teeth on
   FactoryDescriptor.

6. **THEN the coordinated bang** (§4 step 5): one regen + producer fill + one apex
   re-verify + gated flip + devnet re-genesis.

**The anti-vacuity discipline for EVERY step** (the whole point): a carrier is only truly
folded when the THIRD EDGE is present — `leg.teeth == committed-authority` enforced in the
DEPLOYED AIR against a FAITHFUL (8-felt, not 31-bit) committed anchor. The negative tooth
must bite through the real `prove_turn_chain_recursive → verify_turn_chain_recursive` path
(honest-accept AND forged→UNSAT), not just a unit-level `forged_*_does_not_fold`. Prove
each load-bearing spec non-vacuous (true AND false) before flipping its BackingAttack to
BindingFromFold. The BackingAttack is not deleted until its positive replacement bites.

---

## Partition (to avoid clobber, per memory §IMPLEMENTATION SWARM PARTITION)
factory + hatchery share the CreateCellFromFactory leg (one lane). dsl + membership share
the caveat-manifest pattern (one lane). bridge = own (note_spend leaf). sovereign = own (P1
non-VK first, then P2). The `prove_chain_core_rotated` match arm + the `CarrierWitness`
socket = ONE integration-lane edit (main loop owns — shared-file clobber hazard).
