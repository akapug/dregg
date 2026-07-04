# Under-wired circuit / VK / light-client gaps — a skeptic's census

Pass date: **2026-06-29**. Scope: a read-only sweep across the breadstuffs workspace
(circuit / effect_vm / metatheory / docs) for the pattern

> the **executor / re-executing validator ENFORCES** something, but the
> **deployed circuit / VK / pure light client does NOT yet witness** it.

A re-executing validator (one that re-runs the turn through the Rust kernel) is safe
against every gap below. The exposure is a **pure light client** — one that verifies
only the deployed per-turn STARK / aggregate VK and runs nothing else. Where a gap
lets such a client be fooled, that is called out; where it is merely "not yet a
deployed truth" for a latent / opt-in / dead-by-default feature, that is called out too.

Companion to `docs/RED-TEAM-FINDINGS.md` (the adversarial pass) — this one is narrower
and structural: it asks, per subsystem, *what does the deployed VK fail to bind?*

Method: each entry was verified against HEAD source (registry-default-selection code,
the deployed AIR ops, the Lean `#assert_axioms` state), not doc prose. Honest both ways
— what IS a deployed light-client truth is stated as such, and no gap is manufactured.

## Classification key

| label | meaning |
|---|---|
| **DEPLOYED-TRUTH** | the deployed default circuit / VK DOES bind it; a pure light client witnesses it today |
| **STAGED-VK** | the in-AIR / descriptor weld is BUILT (often Lean-proven), but not committed into the deployed VK and not flipped as default; a (often registry-wide) VK epoch remains. Sound today only for a re-executing validator or a verifier holding the state/declaration opening (the "cap-membership posture") |
| **EXECUTOR-ONLY-CIRCUIT-NAMED** | enforced executor-side in Rust; the circuit binding is named / sidecar-built but NOT wired into the per-turn VK; a pure light client cannot witness it |
| **DEMO** | a prototype wired on NEITHER side in production (orphaned) — an honest negative, not a soundness gap |

---

## Summary table (ranked by soundness-value)

| # | Gap | Class | Pure LC foolable? | Live / latent | VK-flip shape | Effort |
|---|---|---|---|---|---|---|
| G1 | **Bridge foreign-proof binding** (`BridgeMint`) | EXECUTOR-ONLY-CIRCUIT-NAMED | **Yes** — backing of a bridge mint | latent (no running relayer on `main`); money primitive | localizable weld (`bridge_action_air`→`effect_vm`) + IVC fold | medium-large |
| G2 | **`Effect::Custom` proofBind gate** | EXECUTOR-ONLY / STAGED-VK | **Yes** — that the bound sub-proof verifies | live surface, opt-in cells | VK-affecting (flip `True`→`boundAt`) + 4→8-felt lift | medium-large |
| G3 | **Sovereign inner transition proof (Phase 2)** | STAGED (incomplete) | **Yes** — VK binding is sentinel-zero | latent | bind the recursive VK + verifier follow-up | medium |
| G4 | **umem / WIDE effect-family weld** | STAGED-VK | partial — the umem *boundary*, not kernel state | latent (umem apps are cockpit/prototype) | additive, PI-preserving registry-default flip | large (gated epoch) |
| G5 | **Capacity satisfaction welds** (escrow/discharge/vault, tags 17/18/19) | STAGED-VK | would-be-yes if declared; dead-by-default | latent (no deployed cell declares a capacity caveat) | registry-wide flag-day + row-locality fix + 18/19 inequality gadgets | large |
| G6 | **Epoch-stamp write-forcing** (revoke/spawn/refresh delegation epoch) | STAGED-VK | no (commitment binds the field) | live | moving-face descriptor cutover (already-binding commit) | medium |
| G7 | **Predicate-caveat satisfaction** (tags 1–16, the off-AIR manifest) | STAGED-VK | cap-membership posture | latent | per-tag in-AIR weld (G5 is the joint-gate instance) | large |
| G8 | **Sovereign witness Ed25519 signature + sequence** | EXECUTOR-ONLY (by design) | yes for the bare STARK; by-design off-circuit | live | not cheaply in-AIR (256-bit sig) | n/a (design choice) |
| G9 | **House-capacity prototypes** (vault/allowance/membrane/derived/ring_closure) | DEMO | n/a (neither side enforces) | not wired | — | honest negative |

---

## What IS already a deployed light-client truth (do not manufacture gaps)

The bulk of the protocol's guarantees are bound by the deployed VK and witnessed by a
pure light client. The under-wired set above is a **bounded, named** remainder, not the
norm.

- **Single-transition + whole-turn unfoolability.** `lightclient_unfoolable` and the
  assembled / forest capstones (`CircuitSoundness.lean:453`,
  `CircuitSoundnessAssembled.lean:440`, `ClosureForest.lean:144`) are `#assert_axioms`-clean:
  an accepted batch decodes to a genuine kernel transition whose endpoints are the
  published 8-felt (~124-bit) commitments. The per-effect refinement family is discharged
  for the enumerated effects (`ClosureAll.lean`, dominant CLASS-A: the write is forced from
  a deployed `Satisfied2` descriptor, not a modelled gate).
- **The deployed wide leg.** A pure light client binds the **WIDE 8-felt** before/after
  anchors (`sdk/src/full_turn_proof.rs:347-348`); `verify_one_cohort_run` resolves its
  descriptor from `WIDE_REGISTRY_STAGED_TSV` (`turn/src/executor/proof_verify.rs:684`).
  Despite the `-staged` filename, the wide registry IS the deployed wire descriptor; the
  ~124-bit faithful commit is preserved.
- **Memory / universal-memory discipline.** The `memOp` / `umemOp` AIR ops are row-local
  `True` but their content rides real in-circuit LogUp buses (`BUS_MEM_*` / `BUS_UMEM_*`)
  in the deployed descriptor — fail-closed, not holes (class 2,
  `docs/deos/EFFECTVM-AIR-VERIFICATION-CENSUS.md`).
- **Authority / conservation / freshness / integrity / settlement.** The five
  `AssuranceCase.lean` guarantees (A–E) and `deployed_system_secure` (`:886`) bind the
  same committed forest; the cap-reshape crown (in-circuit non-amplification + production
  authority), `settlement_soundness`, `no_replay`, and the integrity memory-program apex
  are all `#assert_axioms`-clean and bound to the deployed commitment.
- **Capacity COVERAGE carrier.** The rotated caveat carrier (`caveatCommit`→PI 45) is
  ALREADY in the deployed R=24 cohort VK; `carrier_omission_impossible`
  (`CapacityCarrier.lean`) proves a pure light client binding PI 45 cannot have a manifest
  entry omitted. (The *satisfaction* of the entry, and the *which-tags-required* floor,
  are the staged half — see G5.)

The trusted off-AIR surfaces below are all **scrupulously named in-code** (Lean comments,
`pi.rs` / `trace.rs` doc-comments, the census doc). None is a laundered overclaim. The
single doc imprecision found is flagged under G1.

---

## Per-gap detail

### G1 — Bridge foreign-proof binding (`BridgeMint`) — EXECUTOR-ONLY-CIRCUIT-NAMED

**Executor enforces.** `apply_bridge_mint` (`turn/src/executor/apply.rs:1411-1558`)
verifies the foreign note-spend STARK (`verify_note_spend_dsl_full`, `:1512-1521`),
pinning `(nullifier, root, value_lo, value_hi, asset, dest)` against the proof's embedded
PI; `verify_portable_note` checks the federation roots (`:1524-1529`, the
cross-federation-replay close); inserts into the committed `bridged_nullifiers`
sparse-Merkle set for double-bridge protection (`:1539-1555`).

**Circuit does NOT witness.** `BridgeMint` is in the effect-vm enum
(`circuit/src/effect_vm/effect.rs:250`) but its per-turn trace body
(`trace.rs:707-719`) **only credits balance by `value_lo` — byte-identical to a plain
`Effect::Mint`**. `mint_hash` is a single carried felt, *claimed* to bind the foreign
spend but never verified in-AIR. The full-fidelity `bridge_action_air`
(`circuit/src/bridge_action_air.rs:31-75`) — binding `nullifier[8] + recipient[8] +
destination_federation[8] + amount` with tamper tests — **exists but is a standalone
sidecar**, NOT wired into `effect_vm` / the IVC / the deployed per-turn VK. The in-tree
comment names the gap exactly: `bridge/src/verifier.rs:29-33` — *"Moving the binding
into AIR (circuit `bridge_action_air` + effect_vm) is the Golden lift, BLOCKED ON HUMAN
… The current Silver posture (executor cross-checks only) is load-bearing."*

**Soundness impact.** **A pure light client CAN be fooled about a bridge mint's
backing**: it sees a balance credit of `value_lo` under the bridge-mint selector but has
no in-circuit witness that a valid foreign spend (with the bound nullifier/recipient)
ever existed; the committed `bridged_nullifiers` replay gate is likewise executor-side,
outside the per-turn VK view. The separate **Solana mirror path** is weaker still (plain
`Effect::Mint` + off-circuit Rust attestation, plus a documented concurrent-relayer
double-mint hole, `docs/deos/BRIDGE-ARCHITECTURE-SOUNDNESS.md` §3).

Lean proves `bridge_action_air` *as a relation* is sound+complete (`Crypto/Bridge.lean`,
`#assert_axioms`-clean under a named `extractable` carrier) — i.e. "IF this AIR verifies,
it certifies open+threshold" — but does NOT establish that the deployed `effect_vm`
constraint runs that AIR.

**Doc imprecision to fix:** `BRIDGE-ARCHITECTURE-SOUNDNESS.md:40` says the
cross-federation `Effect::BridgeMint` "IS in-circuit and nullifier-gated." Imprecise vs
HEAD — the nullifier gating and foreign-proof verification are executor-side; only the
balance credit is in the VK.

**Value:** highest — real money ($DREGG / the bridge), and the gap is a clean
"localizable weld" (fold the already-built `bridge_action_air` into the effect-vm
descriptor) rather than a registry-wide flag-day. **Effort:** medium-large.

### G2 — `Effect::Custom` proofBind gate — EXECUTOR-ONLY / STAGED-VK

**Verifier enforces (off-AIR).** The bound custom sub-proof is verified by the Rust
`verify_proof_bind` (`circuit-prove/src/custom_proof_bind.rs`, a recursive STARK verify).

**Circuit does NOT witness.** The in-AIR `proofBind` op is `| .proofBind _ => True`
(`metatheory/Dregg2/Circuit/DescriptorIR2.lean:570`; Rust bounds-only,
`descriptor_ir2.rs:1299`) — **the only AIR op kind with no in-circuit realization at all**
(no bus, no polynomial). The commitment column is **4-felt / ~62-bit**
(`custom_proof_bind.rs:61-70`), below the 8-felt / ~124-bit faithful-commitment floor.

**Lean status.** `Dregg2.Circuit.CustomApex` discharges the binding *under a staged
in-AIR verifier* (`VmConstraint2.holdsAtStaged` flips the `proofBind` gate `True →
ProofBind.boundAt`) and a named `EngineBinding` recursion carrier, `#assert_axioms`-clean
(`docs/reference/lean-circuit.md:196-244`). But the **deployed** gate is still `True`.

**Soundness impact.** A light client running only the aggregate EffectVM STARK does NOT
witness that the bound custom sub-proof verifies — it must additionally run
`verify_proof_bind` (or trust the federation verifier). The 4-felt commitment is also a
sub-floor collision surface. **Value:** medium (first-class app-defined proofs).
**Effort:** medium-large — flipping the gate is VK-affecting (re-emit the effect-vm
descriptor) and the 4→8-felt lift + column re-pin is the same gated epoch, coordinated
with the umem flip (G4).

### G3 — Sovereign inner transition proof (Phase 2) — STAGED (incomplete)

**Off-AIR + not even bound today.** `SOVEREIGN_TRANSITION_PROOF_{VK_HASH,COMMITMENT}` +
`HAS_TRANSITION_PROOF` (`circuit/src/effect_vm/pi.rs:240-250`) are recursively verified
off-AIR (`proof_verify.rs:2485`), and the **VK binding is sentinel-zero today**
(`proof_verify.rs:2483-2485`) — the recursive verifier is named as "a follow-up."

**Soundness impact.** For a sovereign cell carrying an inner transition proof, the
deployed path binds *nothing* about that inner proof's VK (sentinel-zero) — a genuine
STAGED gap, not merely off-AIR-but-checked. **Value:** scales with sovereign-cell usage
(today latent). **Effort:** medium (stand up the recursive verifier + bind the VK).

### G4 — umem / WIDE effect-family weld VK epoch — STAGED-VK

**Executor witnesses.** The umem witness lane is on by default (materializes the Blum
umem trace); all five "revolutions" are executor-witnessed + Lean-`#assert_axioms`-clean
(`docs/reference/umem.md`).

**Circuit: STAGED, not flipped** (confirmed from registry-default-selection code, not
prose). The WIDE+umem welded registry
(`circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv`, 54 members) is
**additively admitted beside** the bare wide leg, but:
- the producer default emits the **bare** leg — the weld is gated on an `Option` witness:
  `sdk/src/full_turn_proof.rs:206-210`, `umem_witness: Option<UmemWeldWitness>`; *"the
  PRESENCE of this witness IS the opt-in; when `None` (the deployed default) the
  byte-identical bare wide leg runs; no VK is committed."*
- the verifier admits both but requires neither: `proof_verify.rs:704-716` *"admits BOTH
  the welded proof AND the bare wide proof … the deployed default prover stays bare."*
- the welded form is **8-felt/~124-bit-preserving** (PI-count unchanged,
  `EmitWideUMemWeldRegistryProbe.lean:13-18`) — the flip is "clean," but **not taken**.

**The VK EPOCH** = (a) make every producer thread the umem witness (drop the bare
default) and (b) commit the welded VK as the **sole** accepted form. Not taken at HEAD.

**Soundness impact.** The umem *boundary* (per-cell heaps, working memory, umem-refs,
checkpoints) is NOT light-client-witnessed in the deployed VK — only executor-witnessed.
The deployed wide leg still witnesses kernel state. Of the five revolutions: time-travel
and continuations are executor-level (`turn/tests/umem_time_travel.rs`,
`turn/src/continuation*.rs`); checkpointable-runtime's **kernel-effect surface is
unbuilt design** (Stage B, `UMEM-STAGE-B-DESIGN.md`); agent-memory-as-portable-umem is a
prototype, not load-bearing (`umem.md:107`). **Value:** high (the umem epoch is a
headline) but the applications are latent. **Effort:** large (the gated epoch).

*Stale-prose note:* several headers claim `umem_witness_enabled` "defaults false"
(`effect_vm_descriptors.rs:1227`, `EffectVmEmitUMemCohort.lean:54`,
`executor/mod.rs:915`), but all three `TurnExecutor` constructors set it `true`
(`executor/mod.rs:995,1056,1099`). This flag only controls internal Blum-trace
materialization, NOT descriptor/VK selection — it does not move the staged conclusion,
but the prose is stale vs HEAD.

### G5 — Capacity satisfaction welds (escrow/discharge/vault, tags 17/18/19) — STAGED-VK

**Executor enforces (when declared).** `SettleEscrow` / `DischargeObligation` /
`VaultDeposit` are `dregg_cell::StateConstraint`s checked by the executor's post-state
evaluator (referenced at `turn/src/executor/mod.rs:371,395,424,593`). **Dead-by-default:
no deployed cell declares a capacity caveat** (the manifest projection + required-tag
re-derivation are themselves staged, `mod.rs:585-587`).

**Two halves, two states.**
- **COVERAGE — DEPLOYED for a pure LC (but latent).** The capacity manifest rides the
  deployed rotated caveat carrier (`caveatCommit`→PI 45); `carrier_omission_impossible`
  (`CapacityCarrier.lean`) makes omission of a present required entry impossible. NOT
  VK-affecting (the carrier was already deployed).
- **SATISFACTION — STAGED-VK, and NOT yet sound as shaped.** The in-AIR gates are built
  (`circuit/src/effect_vm/satisfaction_weld.rs`), proven sound
  (`CapacitySatisfaction.lean`, `satisfaction_witnessed`,
  `capacity_witnessed_pure_lightclient`, `#assert_all_clean`), and graduated to the wide
  form (`SettleEscrowSatWideDescriptor.lean`, the GENTIAN FULCRUM, closing the
  "1-felt-V3-columns-not-absorbed" sub-gap at the proof level). But it is **NOT emitted
  into a committed VK and NOT routed onto any live path.** Three independent blockers
  (per HORIZONLOG + `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6):
  1. **The bare-descriptor flag-day.** There is no `SettleEscrow` *Effect* variant —
     escrow settlement rides a *normal* effect whose honest proof verifies under the
     **bare wide descriptor**. A pure light client cannot reject a forged settle on the
     bare path unless the decode+force gates live on *every deployed normal wide member*
     — a registry-wide VK flag-day (every fingerprint changes, every producer fills the
     decode aux, the full gauntlet re-proves, the Lean apex re-verifies). This is the
     genuine VK epoch, not a one-descriptor delta.
  2. **`hbind` not realized in the artifact.** The selector-forcing gadget
     (`carrier_floor_weld.rs`) reads the floor from the deployed caveat-tag columns
     291/298/305/312, but the Lean keystone `gentian_selector_forced_carrier`
     (`CarrierBoundFloorGadget.lean:310`) discharges the limb only *conditionally* on a
     hypothesis `hbind` (the gadget manifest's `caveatCommit` equals the committed one),
     and the Lean reads FREE-HEADROOM columns (`CARRIER_BASE = EFFECT_VM_WIDTH+200`), not
     the deployed bound columns. As emitted, the forged-floor tooth would NOT bite in a
     real STARK.
  3. **Row-locality (the `10ac36c54` empirical finding, a real `--release` STARK).**
     `satisfaction_weld` makes the capacity selector settle-row-only; `carrier_floor_weld`'s
     selector-force gate is every-row and decodes the floor from uniformly-filled caveat
     columns → forces `sel=1` on carry-forward padding rows → **the honest escrow-declared
     settle becomes UNSATISFIABLE** (`OodEvaluationMismatch`), so the forged teeth have no
     baseline. Separately, PI 45 is pinned to the last row while the decode gates are
     every-row with no cross-row uniformity gate → the floor decode is decoupled from the
     committed caveat. The single-row Lean rung never modeled the multi-row carry-forward
     interaction nor the last-row PI binding. Only the no-false-reject direction (no-escrow
     ⇒ selector inert ⇒ verifies) is confirmed in a real proof.

  Additionally, **tags 18/19 need new gadgets**, not the escrow equality template:
  discharge carries a due-ness *inequality* (range-check aux column); vault is entirely
  inequalities including a *product* (`Tb·m ≤ Sb·d`) that overflows the ~31-bit BabyBear
  field (off-AIR uses u128) — an overflow-safe multi-limb comparison gadget. Emitting an
  equality-only weld for 18/19 and flipping would DROP the early-discharge /
  inflation-attack / dilution disciplines — i.e. accept forgeries.

**Soundness impact.** SATISFACTION is **not light-client-witnessed in production**; sound
today only for a verifier holding the committed-state opening (cap-membership posture).
Because the feature is dead-by-default, this is "not yet a deployed truth" for a latent
primitive, not a live exploit — and the flip was correctly NOT taken (taking it as
currently shaped would be unsound). **Value:** the house-capacity primitives (escrow /
on-schedule duty / no-dilution vault). **Effort:** large (registry-wide epoch +
row-locality fix + 18/19 inequality gadgets).

### G6 — Epoch-stamp write-forcing residuals — STAGED-VK

`RevokeDelegationEpochResidual` / `SpawnEpochStampResidual` / `RefreshEpochStampResidual`
(`Circuit.EffectRefinement` / `EffectRefinementBatch2`, named fail-closed `Prop`s;
`metatheory/CLAIMS.md` real-debt list). For these three epoch/snapshot moves the deployed
commitment **binds** the `delegationEpochAt` field (it folds into `record_digest`), the
hostile-witness extractor forces the gate, and the executor performs the move — **but the
frozen v1-face descriptor commitment-binds the stamp rather than WRITE-GATE-forcing it.**

**Soundness impact.** Low — the commitment binds the field value (no free-forge), so a
pure light client binding the commit does bind the epoch stamp; what is residual is the
in-AIR *write-gate forcing* of its correct derivation. The faithful refinement is proven
against the residual (`spawn_full_circuit_refines_spec`); the closure is the moving-face
descriptor cutover (§3.EPOCH) — per-effect descriptor + verifier-anchor work on an
already-binding commitment, NOT a commitment change. (The extraction lane itself is
fully closed: `CircuitOpenFronts.countOpenFronts = 0`, 32/32 effects.) **Effort:** medium.

### G7 — Predicate-caveat satisfaction (tags 1–16) — STAGED-VK

The general surface G5 is the joint-gate instance of. A cell's declared
`state_constraints` (field-equality, monotonic, the temporal atoms tags 13–16 —
`RateBound`/`UntilEvent`/`SinceEvent`/`ChallengeWindow`, the predicate caveats tags 1–12)
are executor-enforced; their light-client surfacing is the **off-AIR** SlotCaveatEntry
manifest re-evaluated by `verify_slot_caveat_manifest` against the bound state views — the
cap-membership posture, not the bare per-turn AIR. Per-slot caveats impose no coverage
floor (only the joint capacity gates do), so a forger could omit a per-slot entry; a
verifier re-deriving the required set from the committed authority digest closes this, but
that in-AIR coverage-forcing (§6 item 2 of the VK-epoch doc) is **caller-asserted, not
in-proof**. **Soundness impact:** the rich predicate-caveat language is not yet
pure-light-client-witnessed; latent (few/no live cells declare these). **Effort:** large
(per-tag in-AIR welds — the same class of work as G5).

### G8 — Sovereign witness Ed25519 signature + sequence — EXECUTOR-ONLY (by design)

The AIR carries only a 4-felt key digest + sequence (`pi.rs:223-235`); the Ed25519
signature is verified off-AIR (`turn/src/executor/authorize.rs:889`), replay via an
off-AIR monotonic chain-walk. **By design** the signature binds the full 256-bit key
off-circuit (`pi.rs:217-222`). A bare-STARK light client does not witness the signature
and must run sig-verify (or trust a federation verifier that does). This is an explicit,
scrupulously-named design choice (in-AIR Ed25519 is expensive), not an oversight — listed
for completeness. **Effort:** n/a (would require an in-circuit signature gadget; out of
scope).

### G9 — House-capacity prototypes — DEMO (honest negative)

`cell/src/{vault,allowance,membrane,derived,ring_closure,obligation_standing,
escrow_sealed}.rs` are orphaned prototypes with **zero live callers** (verified in
`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`). They are NOT an
executor-enforces-but-circuit-doesn't gap — the executor doesn't enforce them in
production either. `escrow_sealed` is *superseded* by the live blueprint factory route
(`sdk/src/trustline.rs:159`, proved Lean twins, PASS falsification probe). `vault` /
`allowance` are weldable as blueprint descriptors over the existing constraint vocabulary
with **no new effect and no VK change** (they would ride `CreateCellFromFactory` +
`Transfer` + `SetField`). `membrane` / `derived` / `ring_closure` would be VK-affecting if
welded but are not enforced on either side today. Recorded so they are not mistaken for
soundness gaps.

---

## Recommended sequence (by soundness-value × tractability)

1. **G1 (bridge)** — highest soundness-value (real money), and a *localizable* weld
   (fold the built `bridge_action_air` into `effect_vm` + the IVC), not a flag-day. Fix
   the `BRIDGE-ARCHITECTURE-SOUNDNESS.md:40` over-statement in the same breath. Also
   address the Solana-path concurrent-relayer double-mint independently.
2. **G3 (sovereign transition proof)** — small, removes a sentinel-zero binding.
3. **G2 (custom proofBind) + G4 (umem) + G5 (capacity)** — the coordinated gated VK
   epoch. G2's 4→8-felt lift and G4's welded-VK commit share the epoch window; G5's
   satisfaction flip additionally needs the row-locality fix and the 18/19 inequality
   gadgets before it is sound to take.
4. **G6 (epoch stamps)** — low severity (commitment already binds); a descriptor cutover.
5. **G7 (predicate caveats)** — the broad in-AIR caveat-satisfaction program; G5 is its
   pilot.

G8 (sovereign signature) and G9 (house prototypes) are by-design / not-a-gap.

**One sentence:** the deployed VK already binds kernel-state unfoolability, conservation,
authority non-amplification, freshness, integrity, settlement, and the memory buses for a
pure light client; the genuine under-wired remainder is the **bridge foreign-proof**
(executor-only, money), the **custom / sovereign-transition recursion** (off-AIR /
sentinel-zero), and the **umem + capacity-caveat satisfaction** welds (built and largely
proven, but parked behind a deliberately-gated VK epoch — with the capacity satisfaction
flip not yet sound as shaped).
