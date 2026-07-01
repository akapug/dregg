# The coordinated VK-EPOCH — design

A single, deliberate regeneration of the deployed circuit verifying-key (VK) / descriptor
registry that closes a converging cluster of **light-client-witness** gaps **at once**.

Status: **DESIGN**. This is the blueprint; execution is a later autonomous run. The
distinguishing property of a VK epoch over an ordinary weld is that it changes the
**deployed default** verification artifact — every descriptor fingerprint, every VK byte,
the wide registry, and the Lean closure apex that re-verifies clean. It is the
"be-extremely-thoughtful" zone (memory: *be-thoughtful-not-trigger-happy*, *named seam is
not a hole*, *we do not name — we ship*). It is designed here for **soundness first** and a
**staged, additive-then-flip** rollout, with the flip itself reserved as a reviewed human
go.

Companion grounding:
`docs/UNDER-WIRED-circuit.md` (the G-series catalog),
`breadstuffs/docs/deos/{BRIDGE-ARCHITECTURE-SOUNDNESS, VK-EPOCH-CONSTRAINT-BINDING-DESIGN,
IN-AIR-AUTHORITY-DIGEST-GADGET}.md`,
`breadstuffs/metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`,
`breadstuffs/HORIZONLOG.md` (the named VK residuals).

---

## 0. Scope — what converges on this epoch

| Gap | One-line | Pure-LC foolable today? | VK-flip shape |
|---|---|---|---|
| **G1** | Bridge foreign-proof binding (`BridgeMint`) — only the balance credit is in the VK; the foreign note-spend STARK + nullifier consume-once are executor-only | **Yes** (a mint's backing) | localizable bridge-member weld + recursive sub-proof verify |
| **G2** | `Effect::Custom` `proofBind` gate is in-AIR vacuous (`True`); 4-felt (~62-bit) commitment | **Yes** (that the bound sub-proof verifies) | flip `True`→`boundAt` + 4→8-felt lift on the custom member |
| **G4** | umem / WIDE effect-family weld — welded registry built + admitted, but the producer default emits the **bare** leg; the weld is gated on an `Option` witness | partial (the umem boundary, not kernel state) | additive, **PI-count-preserving** registry-default flip |
| **G5** | Capacity satisfaction (escrow/discharge/vault, tags 17/18/19) — coverage deployed, **satisfaction staged and not yet sound as shaped** (row-locality) | would-be-yes if declared; dead-by-default | registry-wide **flag-day** + row-locality fix + selector forcing + 18/19 inequality gadgets |
| **MEMBERSHIP** | Epoch-transition committee-evolution witness — consensus advances the committee live, but a pure LC does not yet witness the validator-set sequence in the VK | no for the *consensus* replayer; yes for a pure LC | VK-affecting circuit weld binding committee evolution into the EffectVM |

These are bundled into **one** epoch because they share the same mechanism: the
descriptor-set changes ⟹ every member's fingerprint changes ⟹ the registry/VK
regenerates ⟹ the closure apex `lightclient_unfoolable` + the five `AssuranceCase`
guarantees must re-verify `#assert_axioms`-clean under the new VK. Doing them piecemeal
would pay the apex-reverify + full-gauntlet-reprove + devnet-regenesis cost N times and
risk N partially-overlapping VKs in flight. One window, one VK, one apex re-verify.

**Out of this epoch (named, deliberately):** G3 (sovereign inner transition proof,
sentinel-zero VK binding — a small independent recursive-verify stand-up), G6 (epoch-stamp
write-forcing — a moving-face descriptor cutover on an already-binding commitment), G7
(the broad predicate-caveat program, tags 1–16, of which G5 is the pilot), G8 (in-AIR
Ed25519 — by design off-circuit), G9 (house-capacity prototypes — DEMO, neither side
enforces). G3/G6 can ride the *same upgrade window* opportunistically but are not the
load-bearing cluster and are not gated on the G5 precondition.

---

## 1. The shared epoch mechanics (the invariant every gap must respect)

A VK epoch is **one rotation of the deployed verification artifact**. The pipeline:

```
descriptor (Lean emit = source of truth: EffectVmEmit* → v3Registry,
            EffectVmEmitRotationV3.lean:55)
  → Rust descriptor builder (byte-for-byte twin; effect_vm_descriptors.rs)
  → registry TSV row (key ∥ name ∥ JSON IR)                    circuit/descriptors/*.tsv
  → fingerprint  (SHA-256 of the descriptor JSON, effect_vm_descriptors.rs:1460-1540,
                  fingerprint_for_name :1433; a change anywhere in trace_width /
                  constraint set / PI layout / chip tables MOVES the fingerprint. NB: the
                  fingerprint is a cache-freshness pin; the REAL drift guard is
                  scripts/check-descriptor-drift.sh — regenerate from Lean + diff)
  → VK  (the verifier's pinned descriptor set, resolved at verify time by name→registry row)
  → verify path  (turn/src/executor/proof_verify.rs:614-703 verify_one_cohort_run resolves
                  the descriptor from the registry — line 640 selects WIDE_REGISTRY_STAGED_TSV
                  vs WIDE_UMEM_WELD_REGISTRY_TSV; sdk/src/full_turn_proof.rs binds the
                  8-felt wide before/after anchors)
```

**The apex is parametric over the registry, so the re-verify is BOUNDED.**
`lightclient_unfoolable` (`CircuitSoundness.lean:453`) takes `Registry := EffectIdx →
EffectVmDescriptor2` as an **abstract parameter**; the deployed instantiation is `Rfix`
(`CircuitSoundnessAssembled.lean:102-323`, the live `v3RegistryHeap` keyed by
`actionTagToPos`). Re-verifying "clean under a new VK" means: **(i)** re-instantiate at the
new `Rfix` — every `Rfix_*` correspondence is a `rfl` **stability marker** that *survives
untouched if a tag still maps to the same position*; **(ii)** re-discharge the per-effect
`descriptorRefines S hash (Rfix e) (kstepAll e)` rung **only for descriptors that actually
changed** (`CircuitSoundnessAssembled.lean:430` `EffectDecodeBridge`; the closed whole-turn
form `ClosureForest.lean:144` `lightclient_unfoolable_circuit_sound_turn` with its
per-step `<e>_closedLog` rungs); **(iii)** if any limb *encoding/offset* changes, update the
`CommitSurface` / limb offsets and re-apply `recStateCommit_binds_kernel`. Everything else —
authority non-amplification, conservation arithmetic, freshness, the unfoolability/FRI
carriers — is **descriptor-agnostic** and re-verifies by re-elaboration with no proof edits.
So the apex re-verify cost scales with **how many descriptors the epoch changes**, not with
the whole proof corpus, and `deployed_system_secure` (`AssuranceCase.lean:850-941`, the
composed A∧B∧C∧D∧E) re-verifies by substituting the new `Rfix` + the changed per-effect
family.

Today the deployed wide leg is **62 public inputs, trace_width 817** (the R=24 cohort,
`rotation-wide-registry-staged.tsv`, ~57 members); the bare rotation-v3 leg is 46 PIs /
width 609 (`rotation-v3-staged-registry.tsv`, ~57–58 members). The umem-welded twin is
**62 PIs preserved, width 824** (`rotation-wide-umem-welded-registry-staged.tsv`, ~54
members) — additive in width (+7), identical in PI count.

**The five invariants of a sound epoch:**

1. **The 8-felt / ~124-bit faithful commitment is preserved.** No member may regress the
   wide before/after anchor below 8 felts. (This is why G2's 4→8-felt lift rides the epoch
   — `docs/FAITHFUL-STATE-COMMITMENT.md`; memory: *don't launder a load-bearing
   insecurity*.) New columns a weld absorbs must lie **inside** the pre-iroot limbs the
   wide carriers consume (the `beforeFieldCol_absorbed` / `afterFieldCol_absorbed`
   pattern), so the existing `rotV3Wide_binds_published` chain binds them — otherwise the
   weld is "1-felt V3, columns not absorbed" and a pure LC does not bind it.

2. **Additive-then-flip.** Every welded descriptor is first emitted **beside** the bare
   leg (a new staged registry / a new member), the deployed default **unflipped**, the
   descriptor-drift / wide-parity / resolver-cohort gates **green** (deployed rows
   byte-identical). The flip is a separate, later, reviewed step.

3. **Fail-closed.** A turn that does not carry the new witness/aux must be **rejected**
   under the new default once flipped — never silently accepted on a legacy path. (For
   features that are dead-by-default, "rejected" is vacuously satisfied until a cell uses
   them.)

4. **One apex re-verify.** After the descriptor set changes, the Lean closure apex
   `lightclient_unfoolable` (`CircuitSoundness.lean:453`), the assembled/forest capstones
   (`CircuitSoundnessAssembled.lean`, `ClosureForest.lean`), and the five `AssuranceCase`
   guarantees (A–E + `deployed_system_secure`) must all re-verify **`#assert_axioms`-clean
   under the new VK** — no new axioms, no `sorry`, the same standard-crypto carriers (FRI /
   STARK soundness, Poseidon2-CR, `DeployedFaithful`) and no dregg-specific open.

5. **No coverage narrowing.** A flip may only *add* what a pure LC witnesses; it may never
   drop a guarantee a re-executing validator enforces today (the precedent: the umem flip
   `da0c47dd6` — a pure registry-default flip, PI-count-preserving, fail-closed, no
   coverage narrowing).

The autonomous run owns invariants 1–4 in the **build+prove** phase; invariant 5 and the
actual default-flip are the reviewed human go.

---

## 2. The G5 ROW-LOCALITY PRECONDITION (do this FIRST)

This is the gating fix. G5 cannot be soundly flipped — and the whole epoch should not flip
the capacity members — until the row-locality defect is repaired, because as shaped today
**the honest escrow-declared settle is UNSATISFIABLE**, so the forged teeth have no
baseline to bite against.

### The defect (empirical, real `--release` STARK, `circuit/tests/gentian_carrier_floor_prove.rs`, 2026-06-29)

Two coupled bugs, both rooted in a **single-row Lean rung** (`envAt t i`, a non-last row)
that never modeled the **multi-row carry-forward** interaction nor the **last-row PI**
binding:

- **(i) Selector row-locality mismatch.** `satisfaction_weld` makes `ESCROW_SEL_COL`
  producer-controlled: `= 1` on the *settle row only*, `= 0` on carry-forward padding rows.
  But `carrier_floor_weld`'s selector-force gate is **every-row** and decodes the floor
  from the uniformly-`fill_caveat`'d type-tag columns ⟹ it forces `sel = 1` on **every**
  row. On a carry-forward padding row (status `Consumed`, continuity `next.before ==
  local.after`): `sel = 0` makes the carrier gate bite *and* `sel = 1` makes the base
  satisfaction gate bite ⟹ the honest escrow-declared settle is **unsatisfiable**
  (`OodEvaluationMismatch`). Only the no-escrow direction (selector inert ⟹ proves) is
  confirmed sound (the no-false-reject control, a 181 KiB BatchProof).

- **(ii) Decode/commit decoupling.** The committed caveat PI (PI 45) is pinned to the
  **last row**, while the decode gates are **every-row with no cross-row caveat-uniformity
  gate**. So the floor decode is decoupled from the committed caveat — a prover could light
  the decode on the settle row while committing a no-escrow manifest to PI 45.

### The fix (any one of three for biteability; the design prefers the first + a uniformity gate for soundness)

1. **Gate the carrier decode by the settle-row-only capacity selector** so the carrier
   force-gate is **inert on carry-forward rows** — i.e. multiply the every-row selector-force
   constraint by a settle-row indicator already in the trace, matching `satisfaction_weld`'s
   row-locality. This makes the honest settle satisfiable again (kills bug (i)).

2. **Force the caveat manifest uniform across rows in-AIR** (a cross-row transition gate
   `caveat_cols[next] == caveat_cols[local]`), which couples the every-row decode to the
   last-row-pinned PI 45 (kills bug (ii)).

3. **Read the decode from the same LAST row PI 45 binds** (move the decode to the boundary
   row), which collapses (i) and (ii) together by construction.

**Recommended:** fix **(1)** for satisfiability + add the **(2)** uniformity gate for the
decode↔commit coupling. (1) alone removes the false-reject; (2) closes the decoupling so a
forger cannot light the settle-row decode while committing a no-escrow PI 45. Reading from
the last row (3) is the cleanest single change but requires the satisfaction gates to also
read boundary-row field columns — verify that the wide carriers absorb the *boundary*-row
limbs (they do: the before/after anchors are the boundary state) before choosing (3).

### Where it lands (staged, no VK change yet)

- **Lean:** extend `CarrierBoundFloorGadget.lean` (and the `CapacitySatisfaction` /
  `SettleEscrowSatWideDescriptor` rungs) from the single-row `envAt t i` model to a
  **two-row / boundary-row** model: a settle-row-gated force constraint + a caveat-uniformity
  transition constraint, re-proving `gentian_selector_forced_carrier` /
  `_settle_forced_carrier` so that (a) an honest escrow settle is **satisfiable** (a positive
  `#guard` / a real prove) and (b) the forged sel=0 / partial / phantom / wrong-floor teeth
  bite **on a satisfiable baseline**.
- **Rust:** gate `carrier_floor_weld.rs`'s force constraint by the settle-row selector;
  add the caveat-uniformity transition gate; re-run `gentian_carrier_floor_prove.rs` and
  require **all four** to be green *with* the honest-settle positive control now proving.
- **Bind the decode to the deployed columns.** As a sibling correction (HORIZONLOG GENTIAN
  carrier-bound-floor): the Lean emit currently reads **free headroom** columns
  (`CARRIER_BASE = EFFECT_VM_WIDTH+200`), while the Rust shadow reads the **deployed**
  caveat-tag columns (291/298/305/312). The artifact must decode from the **deployed
  caveat-commit-bound columns** so the floor tooth bites via the real PI-45 commit
  (`hbind` realized in the artifact, not assumed as a hypothesis). Base the carrier
  descriptor on the **narrow** `settleEscrowSatVmDescriptor2R24`, which DOES carry the
  deployed caveat carrier and a genuine `caveatCommit → PI 45` via its real producer
  `generate_rotated_settle_escrow_trace`, then graduate to wide.

**This precondition is purely staged Lean+Rust+test work — fully safe-autonomous, no VK
change.** It is the prerequisite that makes the G5 satisfaction gates *real* teeth rather
than vacuous ones. Until it is green (honest settle satisfiable AND forged teeth bite in a
real STARK), the G5 leg of the epoch must not be emitted into a committed VK.

---

## 3. Per-gap design

For each gap: **(W)** what the VK must additionally witness · **(D)** the descriptor change
· **(P)** the producer change · **(L)** the Lean emit change · **(R)** the registry / wide-twin
· **(T)** the soundness theorem to (re)prove.

### G1 — Bridge foreign-proof binding (`BridgeMint`)

Today: `apply_bridge_mint` (`turn/src/executor/apply.rs:1411-1558`) verifies the foreign
note-spend STARK + federation roots + inserts the consume-once `lock_nullifier` into the
committed set; the per-turn trace body credits only `value_lo` (byte-identical to a plain
`Effect::Mint`). The full-fidelity `bridge_action_air.rs` exists as a **standalone sidecar**
(18 green teeth), and Lean `Crypto/Bridge.lean` proves it sound+complete (`#assert_axioms`-clean
under the named `extractable` carrier) — but it is **not folded into the deployed effect-vm
VK**. The concurrent-relayer double-mint hole is independently **closed** in committed state
(`bridge_ledger.rs::bridge_mint_against_lock`, `bridge/tests/committed_double_mint.rs`, 4 green).

- **(W)** That a valid foreign note-spend with the bound `(nullifier[8], recipient[8],
  dest_federation[8], amount[lo,hi])` existed (the **backing**), and that the nullifier was
  **consumed exactly once** (the in-proof double-mint gate).
- **(D)** Fold the `bridge_action_air` boundary into the `mintVmDescriptor2R24` bridge-mint
  member: new PI slots + boundary constraints binding `(nullifier, recipient,
  dest_federation, amount)`. For the **backing-existence** half, the foreign note-spend STARK
  must be **recursively verified in-AIR** — the same machinery as G2's `proofBind` flip — and
  the committed `note_nullifiers` membership/insertion surfaced into the per-turn commitment.
- **(P)** The bridge-mint producer threads the foreign-spend witness + fills the new boundary
  aux columns + (backing half) the recursive sub-proof bytes + the nullifier-membership aux.
- **(L)** `EffectVmEmitBridgeMint` changes: lift its **HONEST BOUNDARY** ("the inbound-value
  attestation is NOT internalized in-circuit") to a genuine in-AIR boundary; `mintV3` /
  the wide twin re-emit.
- **(R)** Re-emit the bridge-mint member in `rotation-v3-staged-registry.tsv` + the wide
  registry; fingerprint moves; every producer fills the new aux.
- **(T)** Re-prove the bridge boundary teeth against the *deployed* descriptor (today
  `Crypto/Bridge.lean` proves the relation, not that the deployed effect-vm constraint runs
  it); then the apex (§1.4).
- **Staging:** **(a)** emit the full-fidelity boundary **additively + staged** beside the bare
  `mintVmDescriptor2R24`, gated on a witness (sound for a witness-holding verifier, no
  default change), prove teeth in Lean+Rust. **(b)** flip (parameter binding becomes a pure-LC
  truth). **(c)** recursive foreign-spend verify (the G2-shaped lift) for backing-existence +
  nullifier-consume surfacing. **Note (a)+(b) bind only the *parameters*** — full
  backing-existence needs (c), which is the same recursive-verify primitive as G2 and should
  share it. **Effort: medium-large** ((a)+(b) medium; (c) large, shared with G2).
- **Also fix the doc imprecision** `BRIDGE-ARCHITECTURE-SOUNDNESS.md:40` ("IS in-circuit and
  nullifier-gated") in the same breath (memory: *rise to meet the claim*) — already corrected
  per HORIZONLOG; re-verify.

### G2 — `Effect::Custom` proofBind gate

Today: the in-AIR `proofBind` op is `| .proofBind _ => True` (`DescriptorIR2.lean:570`,
Rust `descriptor_ir2.rs:1299`) — the **only** AIR op kind with no in-circuit realization. The
bound sub-proof is verified **off-AIR** by `circuit-prove/src/custom_proof_bind.rs`
(`verify_proof_bind`, a recursive STARK verify, generic over `CellProgram`). The commitment
column is **4-felt / ~62-bit**. Lean `CustomApex.lean` discharges the binding under a
**staged** verifier (`VmConstraint2.holdsAtStaged` flips `proofBind` `True → boundAt` under a
named `EngineBinding E` carrier), `#assert_axioms`-clean — but the deployed gate is `True`.

- **(W)** That the bound custom sub-proof **verifies** (program-correctness recursion folded
  into the per-turn AIR, not the external engine), at the 8-felt commitment floor.
- **(D)** Flip the deployed `proofBind` gate from `True` to the genuine recursive-verify
  constraint (`boundAt`); lift `custom_proof_commitment` 4→8 felts and re-pin the column.
  This is the **shared recursive-verify primitive** G1's backing half also needs.
- **(P)** The custom producer fills the recursive sub-proof witness + the widened 8-felt
  commitment columns; the IVC fold (`ivc_turn_chain.rs`) stays per-turn (the custom proof
  rides the per-turn `Effect::Custom` ProofBind, **not** folded into the whole-chain IVC —
  that further generic-foreign-leaf fold is explicitly **out of scope**).
- **(L)** Promote `CustomApex.holdsAtStaged` to the deployed `holdsAt`; the `EngineBinding`
  carrier becomes the deployed recursion carrier.
- **(R)** Re-emit the custom member; the 4→8 lift + recursive constraint move the fingerprint.
- **(T)** `CustomApex` re-verify under the deployed (no longer staged) gate; the 8-felt
  commitment non-collision; the apex.
- **Effort: medium-large** (the recursive-verify constraint is the hard, shared piece).

### G4 — umem / WIDE effect-family weld

Today: the welded registry `rotation-wide-umem-welded-registry-staged.tsv` (~54 members,
62 PIs **preserved**, width 824) is **additively admitted beside** the bare wide leg, but the
producer default emits the **bare** leg: the weld is gated on an `Option<UmemWeldWitness>`
(`sdk/src/full_turn_proof.rs:210`; dispatch `cipherclerk.rs:5801-5874` on
`umem_weld_staged_enabled` — *the presence of this witness IS the opt-in; when `None` the
byte-identical bare wide leg runs; no VK is committed*). The verifier admits **both** but
requires **neither** (`proof_verify.rs` — *admits BOTH the welded and the bare wide proof*).
The umem witness lane is on by default executor-side (Blum trace) and all five revolutions
are `#assert_axioms`-clean (`docs/reference/umem.md`). The weld is **PI-count-preserving**
(`EmitWideUMemWeldRegistryProbe.lean`).

- **(W)** The umem **boundary** (per-cell heaps, working memory, umem-refs, checkpoints) bound
  into the deployed wide commit (today only executor-witnessed).
- **(D)** No new constraint *kind* — the welded descriptor already exists. The change is to
  make the welded form the **sole accepted** form (drop the bare-leg admission).
- **(P)** Make every producer **thread the umem witness** (drop the bare `None` default) —
  `umem_witness: Option<UmemWeldWitness>` becomes always-`Some`.
- **(L)** The emit headers that claim `umem_witness_enabled` "defaults false"
  (`effect_vm_descriptors.rs:1227`, `EffectVmEmitUMemCohort.lean:54`, `executor/mod.rs:915`)
  are **stale prose** — all three `TurnExecutor` constructors already set it `true`
  (`executor/mod.rs:995,1056,1099`); that flag controls Blum-trace materialization, not
  descriptor/VK selection. The real flip is the producer-default + verifier-admission change.
  Re-emit `EmitWideUMemWeldRegistryProbe` as the deployed wide registry.
- **(R)** `rotation-wide-umem-welded-registry-staged.tsv` becomes the deployed wide registry
  (rename off `-staged`); the bare wide registry is retired from admission.
- **(T)** The PI-count-preservation probe (`EmitWideUMemWeldRegistryProbe.lean:13-18`); the
  apex under the welded registry. This is the **cleanest flip** (additive, PI-preserving,
  fail-closed) — the model for the others.
- **Effort: large** (the gated epoch coordination), but **low novelty** (no new gadget).

### G5 — Capacity satisfaction (escrow / discharge / vault, tags 17/18/19)

Today: **COVERAGE is deployed** for a pure LC — the capacity manifest rides the AIR-bound
rotated caveat carrier (`caveatCommit → PI 45`), `carrier_omission_impossible`
(`CapacityCarrier.lean`) makes omission of a present required entry impossible (already in
the R=24 cohort VK; **not** VK-affecting). **SATISFACTION is staged and NOT yet sound as
shaped.** Three blockers, all named and verified:

- **Row-locality** — the §2 **precondition**; must land first.
- **The GENTIAN selector-forcing core** — built and proven (`InAirAuthorityDigestGadget.lean`,
  `gentian_selector_forced_discharged` / `gentian_settle_forced_discharged`,
  `#assert_all_clean` under only `ChipTableSound` + `FloorDigestBinds`; Rust
  `authority_digest_weld.rs`). The remaining **artifact** distance: bind the gadget's
  authority-digest read to a column the deployed commit actually forces. The deployed limb 24
  (`B_AUTHORITY_DIGEST` = `compute_authority_digest_felt`, a **byte-domain** hash) ≠
  `hash_many(floor)`, and limb 24 is **load-bearing** (the v1 OLD_COMMIT root + record-pin
  surfaces) so it cannot be reinterpreted. The sound realization is a **new dedicated
  felt-domain floor-digest limb** written into one of the **unconstrained headroom limbs**
  (pre-limb offsets 12..23, genuinely free + absorbed into the wide commit) **PLUS the
  per-effect floor-digest binding welds** (the `perms_digest`/`vk_digest` pattern: force-to-
  `hash_many(floor)` at creation / caveat-mutating effects + frozen pass-through +
  anti-ghost teeth) — without those binding welds the headroom limb is forger-choosable at
  the writing effect (the binding gap). *Alternative that sidesteps the binding welds:*
  decode the floor **directly from the already-coverage-bound caveat manifest columns**
  (291/…) rather than from a digest limb — preferred, as it reuses the deployed PI-45 binding
  and avoids a create/authority-cohort flag-day.
- **The bare-descriptor flag-day** — there is **no `SettleEscrow` Effect variant**; escrow
  settlement is a `dregg_cell::StateConstraint` checked at `turn/src/executor/mod.rs:371/593`,
  so it rides a **normal** effect whose honest proof verifies under the **bare wide
  descriptor**. A pure LC (no opt-in) cannot reject a forged settle on the bare path unless
  the decode+force gates live on **every deployed normal wide member** — the genuine
  **registry-wide flag-day** (every fingerprint changes, every producer fills the decode aux,
  the full gauntlet re-proves, the apex re-verifies).
- **Tags 18/19 need new gadgets**, not the escrow equality template: discharge (18) carries a
  **due-ness inequality** (`due_block ≤ clock` — a range-check aux column) + per-cell param
  equalities; vault (19) is **entirely inequalities** incl. the no-dilution **product**
  `Tb·m ≤ Sb·d`, which overflows the ~31-bit BabyBear field (off-AIR uses u128) — needing an
  **overflow-safe multi-limb comparison gadget**. Emitting an equality-only weld for 18/19 and
  flipping would DROP the early-discharge / inflation-attack / dilution disciplines — i.e.
  accept forgeries. Satisfaction soundness rungs for all three (`CapacitySatisfaction.lean`,
  16 keystones, `#assert_all_clean`) are proven; the in-AIR inequality **gadgets** are not.

Per the W/D/P/L/R/T template, for the **escrow (tag 17)** template (the proven pilot):

- **(W)** That a declared escrow capacity's settle gate (`Deposited`-before / `Consumed`-after
  on both legs) held **over the committed state**, **un-dodgeably** (the selector forced from
  the committed declaration), for a pure LC.
- **(D)** On **every deployed normal wide member**: the four selector-gated satisfaction
  equality gates (`satisfaction_weld.rs`) + the GENTIAN selector-forcing gadget
  (`authority_digest_weld.rs`: recompute-bind, decode, selector-force) reading the
  coverage-bound caveat columns + the row-locality fix. Wide form
  (`settleEscrowSatVmDescriptor2R24Wide`) so the field columns absorb into the 8-felt commit.
- **(P)** A satisfying **wide producer** fills the selector + decode-witness + is-zero + chip
  rows + the field-override-and-commit-recompute surgery (the fee/nullifier-producer pattern,
  for the two leg field limbs of a zero-amount settle-carrier).
- **(L)** Emit `settleEscrowSatVmDescriptor2R24Wide` + the gentian gates into the deployed
  cohort; re-prove `settleEscrowWide_forces_settle_gate`,
  `gentian_settle_forced_discharged`, the partial/phantom UNSAT teeth, against the deployed
  (not staged) descriptor.
- **(R)** Registry-wide: the decode+force gates on every normal wide member ⟹ every
  fingerprint moves.
- **(T)** `CapacitySatisfaction.satisfaction_witnessed` +
  `capacity_witnessed_pure_lightclient`; `InAirAuthorityDigestGadget.gentian_*_discharged`;
  the row-locality re-proofs; then **tags 18/19** with their inequality gadgets; then the apex.
- **Sound order:** (a) escrow welded descriptor + selector + producer + VK + routing (the
  proven template) with the row-locality fix; (b) the range-checked / product in-AIR gates for
  18/19; (c) only then flip. **Effort: large** (registry-wide flag-day + row-locality +
  selector forcing artifact + 18/19 inequality gadgets).

### MEMBERSHIP — epoch-transition committee-evolution witness

Today: validator add/remove/rotate is a **live on-chain op** (`finalization_votes.rs::reconfigure`,
`blocklace_sync.rs::apply_committee_change`), gate-proven by `MembershipSafety.lean` + spec
twin `EpochReconfig.lean::epoch_handoff_no_gap`. A light client following the chain verifies
the committee evolution by **replaying the finalized membership blocks** (each ratified by the
prior committee's quorum — the ARGUS correct-evolution property at the **consensus** layer).
The residual: binding that evolution **into the EffectVM / VK** so a **pure** LC (not a
re-executing/replaying validator) witnesses the validator-set **sequence**.

**Greenfield note (verified in metatheory).** The committee/epoch machinery that exists
today is **consensus-layer and orthogonal to the VK**:
`Dregg2/Distributed/EpochReconfig.lean` (`quorumThreshold`, `applyDelta`, `validDelta`,
`epoch_handoff_no_gap:52`, `verified_needs_old_quorum:39`, `quorums_intersect:110`) +
`MembershipSafety.lean` prove the **reconfiguration is safe** but live entirely at the
consensus layer. There is **no VK-indexed committee structure** in the circuit — VK epochs
are *assumed*, not proved, against the committee. So this leg is genuinely **greenfield
in-circuit**: it needs a new emit module + a new soundness theorem, not the re-use of an
existing weld.

- **(W)** The committee-evolution sequence: that each finalized membership change was ratified
  by the prior committee's quorum (a chain of `committee_epoch → committee_epoch+1` transitions
  bound into the per-turn / aggregate commitment) — the ARGUS correct-evolution property lifted
  from the consensus replayer into the per-turn AIR.
- **(D)** A new EffectVM weld (HOUSE-CAPACITIES-WELD-PLAN shape) binding the committee-change
  effect's pre/post committee digest + the quorum-ratification witness into the wide commit.
- **(P)** The membership-change producer fills the committee digest + quorum-signature
  aux (note: in-AIR signature verification is expensive — likely a **digest-of-quorum-attestation**
  carrier rather than full in-AIR Ed25519, mirroring G8's by-design boundary).
- **(L)** A new emit module (e.g. `EffectVmEmitCommitteeChange`) + a Lean witness twin of
  `MembershipSafety` / `EpochReconfig` bound to the commitment.
- **(R)** A new committee-change member in the registry; fingerprint moves.
- **(T)** A committee-evolution soundness theorem (the ARGUS correct-evolution property
  **in-circuit**) + the apex.
- **Dependency / blocker:** the **RECEIPT-IDENTITY** residual (HORIZONLOG epoch-transition (1))
  — `federation_id == derive(known_keys, committee_epoch)` is pinned by the discord-bot,
  Midnight bridge, and the executor signing domain (the **off-limits** bot/bridge lanes).
  Advancing the receipt identity live needs a stable `chain_id` (genesis root) those consumers
  pin instead. **The in-circuit membership witness is sound to build+stage independent of the
  receipt-identity migration, but flipping the deployed default interacts with it** — so the
  membership leg is the **most coupled** to off-limits lanes and should be the **last to flip**
  (or deferred to a follow-on window). **Effort: medium-large** (new weld + the receipt-identity
  coupling is the risk, not the gadget).

---

## 4. Coordinated mechanics — one VK, one apex re-verify

The five legs are **not** five VK rotations. They are **one** descriptor-set delta applied
together:

1. **Assemble the descriptor delta** (all legs that pass their preconditions): G4 (producer
   default flip + admission), G2 (proofBind flip + 4→8 lift), G5 (registry-wide decode+force
   + row-locality fix + selector forcing + 18/19 gadgets), G1 (bridge boundary + shared
   recursive verify), MEMBERSHIP (committee-change weld). Each is first **staged additively**
   (a new `-staged` registry / new members) with the deployed default unflipped.

2. **Regenerate once.** When the staged deltas are all green, the registry/VK regenerates a
   single time: every member's fingerprint changes, the wide registry becomes the welded
   registry, the verify path resolves the new descriptors.

3. **Re-verify the apex once.** `lightclient_unfoolable` + `CircuitSoundnessAssembled` +
   `ClosureForest` + the five `AssuranceCase` guarantees (A–E) + `deployed_system_secure` all
   re-verify `#assert_axioms`-clean **under the new VK** — no new axioms, the same
   standard-crypto carriers. Because the apex is structured over the **descriptor family**
   (not a hardcoded fingerprint), the re-verify is a re-elaboration of the same proofs against
   the changed `EffectVmEmit*` emissions — the proofs follow the emit modules they import.

4. **Re-prove the full gauntlet once** (all per-effect STARKs, descriptor-drift, wide-parity,
   resolver-cohort, the per-gap teeth in real `--release` STARKs).

5. **Flip the deployed default once** (the reviewed human go) — the wide registry, the
   verify-path admission, the producer defaults, all move together; the devnet re-genesis (G5
   value-only headroom-limb writes shift each cell's commitment value) happens in the same
   window.

**Why together:** every leg pays the apex-reverify + full-gauntlet-reprove + (for the
value-shifting legs) devnet-regenesis cost. Doing them in one window pays it once and avoids N
overlapping in-flight VKs. The **precedent** is the umem flip (`da0c47dd6`): every producer
built + loud-probe-validated staged, the flip a pure registry-default flip,
PI-count-preserving, fail-closed, no coverage narrowing.

---

## 5. Staged rollout — the additive-then-flip discipline

Three phases. **Phases (a) and (b) are safe-autonomous; phase (c) is the reviewed human go.**

### Phase (a) — BUILD STAGED  [SAFE-AUTONOMOUS]

For each leg, build the welded descriptors + producer + the Lean welds **admitted additively
beside** the bare legs, the deployed default **UNflipped**:

- G5 **row-locality precondition first** (§2) — the gate for the whole capacity leg.
- New `*-staged` registries / new members; deployed rows **byte-identical**.
- The `Option`-witness / opt-in gating that makes the bare path the default (the umem
  `umem_witness: None`, the capacity `expected_caveat_coverage: None`, the bridge witness-gated
  boundary) — so nothing on the live wire changes.
- The producer fills the new columns/aux **only when the witness is present**.
- Each leg's `EffectVmEmit*` change emitted to a staged registry, Rust descriptor twin
  byte-for-byte.

**Safe because:** the deployed default VK is unchanged, descriptor-drift / wide-parity /
resolver-cohort gates stay green, a pure LC's guarantees are unchanged, and a re-executing
validator already enforces everything. This is exactly the posture every gap is in **today** —
phase (a) extends it leg-by-leg without flipping.

### Phase (b) — PROVE STAGED  [SAFE-AUTONOMOUS]

- `lake build` green; the closure apex + five guarantees `#assert_axioms`-clean **under the
  staged emit** (re-elaborated against the changed emit modules, still beside the deployed).
- The per-gap **teeth bite in real `--release` STARKs**: honest accepts, forged refuses, on a
  **satisfiable baseline** (the row-locality positive control is the keystone here — an honest
  escrow settle must *prove*, not just "no false reject").
- All gauntlets green (the full per-effect suite, the bench/regression suites).
- **Descriptor-drift** green (deployed VK byte-identical), wide-parity green, resolver-cohort
  green.
- A **dry-run regeneration** of the new VK + apex re-verify performed **in a staged
  artifact**, not committed over the deployed — proving the flip *would* be clean.

**Safe because:** still nothing flipped; this is build+prove+measure. Memory: *empirical
validation > paper-green* — the real-STARK teeth + the honest-settle positive control are the
acceptance bar, not green CI alone.

### Phase (c) — THE GATED FLIP  [REVIEWED HUMAN GO]

Only after (a)+(b) are green for **every leg that is to flip**:

- Commit the new welded VK as the **sole accepted** form; flip the producer defaults; retire
  the bare-leg admission; route the live verify path through the welded descriptors.
- The devnet **re-genesis** (the value-shifting legs move each cell's commitment value).
- Re-verify the apex **over the committed VK** one final time.
- Migrate / coordinate the **off-limits-adjacent** consumers (the MEMBERSHIP leg's
  receipt-identity / `chain_id` migration touches the bot/bridge pins) — this is the part that
  most needs a human in the loop and may be **split into a follow-on window**.

**Why (c) is reviewed, not autonomous:** it changes the deployed truth a stranger's light
client trusts; it triggers a devnet re-genesis; the MEMBERSHIP leg touches the pinned
`federation_id` consumers (off-limits lanes). It is a deliberate flag-day, not a trigger-pull
(memory: *be-thoughtful-not-trigger-happy*).

**The split, explicitly:**

| Phase | What | Who |
|---|---|---|
| (a) build staged | welded descriptors + producers + Lean welds, additive, default unflipped | **autonomous** |
| (b) prove staged | apex clean, real-STARK teeth bite on a satisfiable baseline, gauntlets + drift green, dry-run regen | **autonomous** |
| (c) flip | commit welded VK, flip defaults, re-genesis, migrate pinned consumers, final apex over committed VK | **reviewed human go** |

An overnight run can take the epoch **all the way through (a) and (b) for G4, G2, G5, G1, and
stage MEMBERSHIP**, leaving a single green, reviewable, dry-run-regenerated artifact and a
one-paragraph "flip readiness" report — and **stop before (c)**.

---

## 6. Rollout order, risks, rollback, proof/test plan, effort

### Order (by soundness-value × tractability × coupling)

1. **G5 row-locality precondition** (§2) — gates the whole capacity leg; pure staged
   Lean+Rust+test, no VK. **Do first.**
2. **G4 umem** — the cleanest flip (additive, PI-preserving, fail-closed, no new gadget); the
   model the others follow. Stage first among the VK-affecting legs.
3. **G2 custom proofBind** — builds the **shared recursive-verify primitive** + the 4→8-felt
   lift that G1's backing half reuses. Stage before G1's recursion leg.
4. **G5 satisfaction** — escrow template (selector forcing artifact + decode-from-deployed-
   columns + the row-locality fix) → then tags 18/19 inequality gadgets. Registry-wide.
5. **G1 bridge** — (a)+(b) parameter boundary (localizable); (c) shares G2's recursion for
   backing-existence + the nullifier-consume surfacing.
6. **MEMBERSHIP** — stage the in-circuit committee-evolution weld; **flip last / defer** (the
   receipt-identity `chain_id` migration touches off-limits bot/bridge pins).

### Risks

- **R1 — G5 over-flip (accept forgeries).** Emitting an equality-only weld for tags 18/19, or
  flipping with the row-locality defect, makes the honest path unsatisfiable or drops the
  inequality disciplines. **Mitigation:** the §2 precondition + the sound-order (escrow proven
  template → 18/19 gadgets → flip); the real-STARK positive control as the acceptance bar.
- **R2 — Faithful-commitment regression.** G2's 4→8 lift or any new column must not regress the
  8-felt floor or land outside the absorbed pre-iroot limbs. **Mitigation:** the
  `beforeFieldCol_absorbed` discipline; the descriptor-drift + faithful-commit checks.
- **R3 — Apex non-reverify.** A descriptor change that breaks `lightclient_unfoolable` or a
  guarantee. **Mitigation:** the dry-run regen + apex re-verify in phase (b), staged, before any
  commit.
- **R4 — MEMBERSHIP / receipt-identity coupling.** Flipping the committee-evolution witness
  interacts with the pinned `federation_id` consumers (off-limits lanes). **Mitigation:** stage
  it but flip last / in a follow-on window after the `chain_id` migration; never touch the
  bot/bridge lanes autonomously.
- **R5 — Devnet re-genesis surprise.** The value-shifting legs (G5 headroom-limb writes) change
  each cell's commitment value. **Mitigation:** re-genesis is part of the reviewed (c) window,
  not autonomous; the base-layout VK stays byte-identical (value-only, not width).
- **R6 — Shared-tree clobber.** All staging happens in one working tree across parallel agents.
  **Mitigation (memory: *swarm shared-tree clobber*):** main loop owns shared-manifest edits
  (registry TSVs, `Dregg2.lean`, `lib.rs`); agents draft disjoint new descriptor/weld files;
  no `git stash`, no worktrees.

### Rollback

- **Phases (a)/(b):** nothing deployed changed — rollback is dropping the staged registries /
  reverting the WIP commit. The deployed VK was never touched.
- **Phase (c):** the flip is a single registry-default + verify-admission + producer-default
  change. Rollback = revert that commit and re-genesis back — but because (c) is reviewed and
  the dry-run regen already proved cleanliness, the flip should not need rollback. Keep the bare
  registries in-tree (not deleted) for one epoch as the rollback target. **Never** ship stale
  artifacts as a "rollback" (memory: *green or bust*) — rollback is a clean revert, not a
  last-good fallback.

### Proof / test plan (the acceptance bar for an autonomous (a)+(b) run)

- `lake build` green; closure apex + 5 guarantees `#assert_axioms`-clean under the staged emit.
- Per-gap teeth in **real `--release` STARKs**: honest accepts on a **satisfiable baseline**
  (the G5 honest-settle positive control is mandatory), forged refuses (sel=0 dodge, wrong
  floor, wrong digest, partial/phantom settle, omitted coverage, unverified sub-proof, forged
  bridge backing).
- The **named staged-but-not-flipped guard gates** stay green through (a)/(b) (deployed VK
  byte-identical) — these are the precise tripwires the autonomous run must not break:
  `rotation_layout_matches_lean()` (`effect_vm_descriptors.rs:1668`, the hard Rust↔Lean layout
  pin), `wide_registry_parses_and_is_name_stable()` (`:2416`, wide repoint stability + transfer
  row 0 byte-identical), `wide_umem_weld_registry_parity_and_no_narrowing()` (`:2500`, the
  Lean-emit == Rust `weld_umem_into_wide_descriptor` ONE-CIRCUIT invariant + piCount unchanged
  + traceWidth = host+7), `v3_staged_descriptors_parse_and_cover_all_limbs()` (`:1714`, every
  limb absorbed once), `resolvers_cover_exactly_the_rotated_registry()`
  (`trace_rotated.rs:3930`, every effect→descriptor resolver reaches a member). Plus
  `scripts/check-descriptor-drift.sh` (regenerate from Lean + diff = zero) — the real drift
  guard, not the SHA pin.
- Full per-effect gauntlet + regression suites green.
- A **dry-run VK regeneration + apex re-verify** in a staged artifact (proving (c) would be
  clean) — the deliverable that makes (c) a one-step reviewed go.

### Effort per gap

| Gap | (a)+(b) staged build+prove | (c) flip | Notes |
|---|---|---|---|
| G5 row-locality precondition | **small-medium** | n/a (no VK) | pure Lean+Rust+test; gates G5 |
| G4 umem | **medium** | small | clean model flip; no new gadget |
| G2 custom proofBind | **medium-large** | medium | builds the shared recursive-verify primitive |
| G5 satisfaction (17 → 18/19) | **large** | medium | registry-wide; selector forcing artifact + inequality gadgets |
| G1 bridge | **medium** (params) + **large** (backing, shares G2) | medium | (c) backing reuses G2 recursion |
| MEMBERSHIP | **medium-large** | medium-large + coupling | flip last / defer; receipt-identity migration |

**One sentence.** The deployed VK already binds kernel-state unfoolability, conservation,
authority non-amplification, freshness, integrity, settlement, the memory buses, and capacity
**coverage** for a pure light client; this epoch additively stages — then, in a single reviewed
flag-day, flips — the **bridge foreign-proof binding**, the **custom/sovereign recursive verify
+ 8-felt lift**, the **umem WIDE weld**, the **capacity satisfaction** welds (gated behind the
row-locality fix), and the **committee-evolution witness**, regenerating one VK and
re-verifying one apex clean — with the build+prove safe for an overnight run and the flip
reserved as a human go.
