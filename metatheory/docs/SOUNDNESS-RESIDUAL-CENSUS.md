# SOUNDNESS-RESIDUAL CENSUS

A source-grounded, READ-ONLY, **adversarial** census of the genuine remaining soundness items
in the dregg apex / circuit / executor. Verified against HEAD (`34950c586`) — **no
doc/memory/HORIZONLOG/header-comment label trusted; the comment claiming "closed" was
re-checked against the definition it names.**

## The reframing this census applies (the whole point)

**"60–80% built" is NOT reassurance — it is a warning.** It means someone built the
scaffolding / happy-path, then hit the HARD part and did not carry it home. The unfinished
20–40% is *where the soundness actually lives*, and it is unfinished precisely because it is
the dangerous part. So for every "it's a theorem / already bound / GAP closed" claim, this
census finds the **EXACT unfinished 20–40%** and treats THAT as the residual.

The two danger-shapes hunted here:

1. **CARRIED HYPOTHESIS that is not an irreducible crypto floor.** A binding/force/decode the
   "theorem" RESTS ON but that is ASSUMED rather than proven. (E.g. `NmRowEncodes`: the
   non-membership gate is "sound" only *given* that the prover's `(lo,hi)` columns decode to
   genuine adjacent committed leaves — and that binding is the un-carried-home part.)
2. **COMMITMENT-BOUND but not GATE-FORCED.** "The commitment binds X" (folds X into
   `record_digest`) is scaffolding (60–80%). "The deployed gate FORCES X into the commitment so
   a prover cannot publish a forged X" is the dangerous 20–40%. Bound ≠ forced.

Irreducible crypto floors (StarkSound / Poseidon2-CR / ed25519 / the prover's own
trace-commitment) are fine — named and moved past. Everything else that the unfoolability claim
rests on is a *real soundness item* and is ranked by **danger**, not by "percent done."

---

## HEADLINE: which carried hypotheses are NOT irreducible crypto floors

Of everything the apex's unfoolability rests on, the carried hypotheses split as:

**Irreducible crypto floors (fine):** `StarkSound`, `Poseidon2SpongeCR` + the S_live
CR-set (`compressInjective`/`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/
`logHashInjective`), and `WitnessDecodes` (the prover's commitment to the kernels behind its
own published roots — a §8 prover obligation). These are the TCB.

**Dangerous (assumed-but-provable) — THE REAL SOUNDNESS ITEMS, ranked by danger:**

| rank | the EXACT unfinished 20–40% | where | danger |
|------|------------------------------|-------|--------|
| ~~**D1**~~ **CLOSED** | `NmRowEncodes` was carried as a hyp; it is now **DISCHARGED** against the deployed sorted-tree adjacency opening. `NoteSpend.lean §8¾` proves `adjacent_gives_gapInterval : Adjacent ⟹ GapInterval` over a sorted spine, so `nmRowEncodes_of_adjacency` derives the gap decode from the adjacency constraint (no assumption); `circuit_gate_meets_executor_guard_forced` concludes `nf ∉ nullifiers` with no `NmRowEncodes` hyp; `wide_bracket_forge_rejected` makes the non-consecutive forge uninhabited. Deployed verifier `turn/src/executor/membership_verifier.rs::verify_nullifier_nonmembership` runs the adjacency AIR + strict bracket; mutation-confirm `notespend_wide_bracket_double_spend_rejected`. | `NoteSpend.lean:524,741` + §8¾; `membership_verifier.rs::verify_nullifier_nonmembership` | **CLOSED.** The wide-bracket double-spend forgery is rejected by the deployed gate (Lean force = theorem; Rust force = the adjacency STARK). Remaining = wire `verify_nullifier_nonmembership` into the effect-descriptor emit so the noteSpend row REQUIRES the proof (currently the deployed gate exists + is mutation-confirmed; the descriptor-emit call site is the named flag-day, item D1-wire below). |
| **D2** | heap SPLICE is **bound-not-forced**: `heapsSplice` (the `heaps := heapWriteHeapsMap` sorted-tree `Heap.set`) is a CARRIED decode hypothesis (`heapWriteEncodes.heapsSplice`); the sorted-tree leaf-update recompute is the explicit **PHASE-E residual**. The committed heap-tree root is NOT gate-forced to the spliced heap. | `RotatedKernelRefinementExercise.lean:218,231` (PHASE-E); §3 header `:197-206` | **HIGH.** The header of `CircuitSoundnessAssembled.lean:265` claims "GAP-2 close / Rfix 56 = heapWriteV3 LIVE" but `heapWriteV3 := graduateV1 (rotateV3 heapWriteVmDescriptor)` is the BASE descriptor with FREE `newRoot`; the recompute-force is in a *separate* FIX refinement, and the splice itself is unforced. A prover could publish a heap-root advance not matching the heap content. |
| ~~**D3**~~ **CLOSED** | epoch/snapshot stamps (×3): `RevokeDelegationEpochResidual` (closed `6c501fa4d` via `epochBumpGate`) / `SpawnEpochStampResidual` / `RefreshEpochStampResidual` — now ALL forced. The spawn/refresh `delegationEpochAt` birth/freshness stamp is a CROSS-CELL relation (`child.delegationEpochAt = parent.delegationEpoch`) that the deployed SINGLE-CELL rotated row CANNOT reach (the parent's `B_EPOCH` is not a column of the child's row), and the turn layer chains effects by `state_commit`-PI equality, NOT a cross-row constraint system — so the "limb 37→38 + cross-row turn gate" is structurally unreachable (no transfer-conservation cross-ROW gate exists to mirror; conservation is carried WITHIN one effect's whole-kernel transition). The genuine forcing layer is the ABSTRACT per-effect descriptor (`spawnE`/`refreshDelegationE`, `view = chainView` over the whole kernel): `delegationEpochAt` is promoted from the framed `restFrame` into a forced PRODUCT `funcComponent` `(delegations, delegationEpochAt)` bound to `(spawnDelegationsMap, spawnEpochAtMap)` / `(refreshDelegationsMap, refreshEpochAtMap)` — the maps read `before.delegationEpoch parent`, so the injective product digest FORCES the stamp = parent_epoch (the SAME mechanism `delegations`/the DELEG system-root already use). VK-FREE (no new committed limb; drift PASS). | `EffectRefinement.lean` §5 (`spawn_circuit_refines_spec` ⟹ `SpawnFullSpec`); `EffectRefinementBatch2.lean` (`refreshDelegation_circuit_refines_spec` ⟹ `RefreshDelegationFullSpec` + `refreshDelegation_full_sat_rejects_stale_stamp`) | **CLOSED.** The stamp is gate-forced at the descriptor (Lean theorem); a stale-stamp forge violates the product `postClause` and is UNSAT (`refreshDelegation_full_sat_rejects_stale_stamp`). `#assert_axioms`-clean, non-vacuity-toothed. |
| **D4** | handler `hinner` carried hyp: `handler_refines_execFullA_exercise` carries the inner-fold-reaches-same-kernel as an un-discharged `∃ s₁, execInnerA … = some s₁ ∧ s₁.kernel = s'.kernel`; AND spawn/factory metadata (cap-handoff/factory-install writes) UNVERIFIED by the handler refinement. | `HandlerExecutor.lean:1199-1205` (`hinner`); `HandlerOpenFronts.lean:53-72` | **MEDIUM.** Handler-executor lane only (the *circuit* spawn cap-handoff IS forced — see "carried home"). The facet-mask leg is genuinely closed (no shortcut term: `innerFacetsAdmittedA`, `HandlerExecutor.lean:1222`). |

**Bottom line of the headline:** four carried hypotheses are NOT crypto floors. **D1 is the
single real soundness item that matters most** — it is the only one whose un-carried-home part
permits a concrete forgery, and its forcing object already exists in Rust, so the residual is
*integration*, not invention. D2/D3 are bound-but-not-forced gate residuals (the dangerous
distinction made literal). D4 is a handler-lane refinement gap.

**Does the apex rest on anything NON-floor-NON-proven that would be a real concern?** The
published apex `lightclient_unfoolable_circuit_sound` itself carries only floors +
`ClosedWitness` (built from genuine readouts). But the *per-effect descriptors it ranges over*
(`Rfix`) include heapWrite and the epoch-stamp effects whose internal refinements carry D2/D3 as
named-but-unforced residuals. So the apex's GLOBAL unfoolability is floor-clean, but its
PER-EFFECT faithfulness for heapWrite and the three epoch moves is bound-not-forced — that is the
honest concern, not a clean bill.

---

## What WAS carried home (verified in source — the "done" claims that survived adversarial re-check)

These are the items where I assumed "done hides the hard part" and source proved the hard part
WAS carried home. Recorded so the census is not just a list of fears.

- **The apex re-point to WIDE cap-open IS carried home** (refutes the "apex still narrow" worry).
  Verified: the published apex is keyed at `vkOfRegistry Rfix` (`ClosureFinal.lean:172`), and
  `Rfix` ranges over `v3RegistryHeap`, which routes the cap tags to the WRITE-FORCING wide
  descriptors — `Rfix 1 = delegateWriteCapOpenV3 := rfl`, `Rfix 19 = spawnWriteCapOpenV3 := rfl`,
  `Rfix 16 = exerciseCapOpenV3 := rfl`, `Rfix 12 = attenuateCapOpenEffV3 := rfl`
  (`CircuitSoundnessAssembled.lean:317,351,297,288`). The §9 "flip is next phase" is DONE: the
  deployed apex proves over the wide cap-open it runs, not an authority-only twin.
- **The cap-open appendix genuinely FORCES** (not authority-read-only). `delegateWriteCapOpenV3`
  is the cap-WRITE rotation base + cells grow-gate INSERT + cap-tree handoff INSERT
  (`CapOpenEmit.lean:542-548`); `effCapOpenV3_satisfiedEff` rebuilds the depth-16 membership
  `SatisfiedEff` per row (`:301`). The cap handoff for spawn IS forced (guarantee A).
- **The handler facet-mask leg is genuine** (no P2 whnf-shortcut term). `exercise_r4_facet_mask`
  proves `execFullA`'s `exerciseA` enforces `innerFacetsAdmittedA` and the handler tags real
  `requiredFacetA` (`ExerciseInnerTurn.lean:63`, `HandlerExecutor.lean:1222`) — the two gates are
  the SAME check, by a real `simp`-proof, not a decide-shortcut.
- **Authority §6 whole-history closure** is a real proof (`Spec/Authority.lean:456`, all 4
  induction cases, `#assert_axioms :569`). The inline `:434` "OPEN" comment is STALE.
- **CircuitOpenFronts adversarial-extractor registry = 0** (`openFronts = []`,
  `CircuitOpenFronts.lean:88`). 32/32 effects' hostile-witness extraction closed with anti-ghost
  teeth — verified the list is literally empty.

---

## Full residual table (every candidate, with the EXACT unfinished part as the key column)

| # | residual | EXACT unfinished 20–40% (the danger) | class | size | file:line |
|---|----------|--------------------------------------|-------|------|-----------|
| **D1** | noteSpend non-membership / no-double-spend | **`NmRowEncodes` carried decode** — the deployed descriptor does not bind `(lo,hi)` to the committed nullifier root; the forge-rejecting adjacency AIR (`circuit/src/membership_adjacency_air.rs`, built + `forge_nonconsecutive_wide_bracket_is_rejected`) is NOT referenced from `effect_vm_descriptors.rs`/`non_membership.rs`. | **DANGEROUS-ASSUMED** | medium (Rust wire) + small-med (Lean discharge `NmRowEncodes`) | `NoteSpend.lean:524,741,751-779` |
| **D2** | heapWrite full-state | **heap SPLICE bound-not-forced** — `heapsSplice` carried; sorted-tree leaf-update = PHASE-E residual; `heapWriteV3` is the FREE-`newRoot` base (`graduateV1(rotateV3 heapWriteVmDescriptor)`), recompute-force in a *separate* refinement; header "GAP-2 close" overstates. | **DANGEROUS-BOUND-NOT-FORCED** | medium, VK-affecting (wire recompute+splice into the live row) | `RotatedKernelRefinementExercise.lean:197-206,218,231,344`; cf. header `CircuitSoundnessAssembled.lean:265` |
| **D3** | spawn / revokeDelegation / refreshDelegation epoch stamps | **commitment-BOUND (limbs 30+24) but not WRITE-GATE-FORCED** — the v1 frozen-`cap_root` face binds the epoch field into `record_digest` but the move rides OFF-ROW; carried as fail-closed `*EpochResidual` Props. | **DANGEROUS-BOUND-NOT-FORCED** | medium, VK-affecting (moving-face V3 cutover) | `EffectRefinement.lean:797,804,344`; `EffectRefinementBatch2.lean:294` |
| **D4** | handler exercise + spawn/factory metadata | **`hinner` un-discharged hyp** (inner fold reaches same kernel) + spawn cap-handoff/factory-install writes UNVERIFIED by handler refinement (maps to born-empty `createCellH`). Circuit lane is fine; handler-executor lane is the gap. | **DANGEROUS-ASSUMED (handler lane)** | medium (Exec-executor change) | `HandlerExecutor.lean:1199-1205`; `HandlerOpenFronts.lean:53-72` |
| **D5** | #139 settlement rest-hash wire | **circuit-emit conformance**: the deployed `RH` encoder's preimage must include the `revocation_channel` (#139) MDB root; Lean carries it as the `RestHashIffFrame` floor. | NAMED-RESIDUAL (Rust conformance; NOT a Lean gap) | medium (Rust wire conformance) | `SettlementSoundness.lean:49-57` |
| F1 | StarkSound (p3 batch-STARK extraction) | — | IRREDUCIBLE FLOOR | — | `CircuitSoundness.lean:455` |
| F2 | Poseidon2SpongeCR + S_live CR-set | — | IRREDUCIBLE FLOOR | — | `CircuitSoundness.lean:455`; `ClosureSurface.lean:120` |
| F3 | WitnessDecodes + per-effect `<effect>Encodes` column-decode | — (the prover's commitment to the kernels/columns behind its own published roots) | IRREDUCIBLE FLOOR (§8 prover obligation) | — | `CircuitSoundness.lean:446`; realizable via `closedWitness_of_readouts` `ClosureFinal.lean:202` |
| S1 | Authority §6 whole-history closure | — proven; `:434` "OPEN" comment STALE | STALE-LABEL / DONE | (fix comment) | `Spec/Authority.lean:456,569` |
| S2 | forest confinement §9.CONFINE | — theorem proven under precondition; executor-gate version = cross-target routing (defense-in-depth, not a hole) | STALE-LABEL / NOT-A-GAP | — | `FullForest.lean:555-584,613` |
| S3 | CircuitOpenFronts | — `countOpenFronts = 0`, all 32 effects | DONE | — | `CircuitOpenFronts.lean:88,135` |
| S4 | CLAIMS.md §OPEN (Refine sim diagram + CM-liveness) | — abstraction-completeness + distributed-LIVENESS, not light-client soundness; Byzantine SAFETY proven | NOT A SOUNDNESS GAP | — | `CLAIMS.md:99,152-157` |

---

## Per-item adversarial notes (verify-source)

### D1 — CLOSED (was the only residual with a concrete forgery)
`NmRowEncodes` (`NoteSpend.lean:524`) WAS the carried decode the gate's soundness rested on:
`nonMemberGate_sound`/`circuit_gate_meets_executor_guard` (`:741`) concluded `nf ∉ nullifiers`
ONLY GIVEN `henc : NmRowEncodes c env xs nf`. The forge that left open was concrete and documented:
without an adjacency force, `lo=0x00…, hi=0xFF…` (non-consecutive) brackets any candidate, forging
non-membership for a present nullifier → a double-spend.

**Now discharged (`NoteSpend.lean §8¾`).** The deployed descriptor FORCES the sorted-tree
neighbor-adjacency constraint (`circuit/src/membership_adjacency_air.rs`, AIR
`dregg-membership-adjacency-v1` — in-circuit Merkle index reconstruction enforcing
`idx_upper == idx_lower + 1`). The Lean shadow of that constraint is
`Crypto.NonMembership.Adjacent`, and §8¾ proves the bridge:

  * `adjacent_gives_gapInterval : Sorted xs → Adjacent xs lo hi → GapInterval lo hi xs` —
    consecutive committed leaves have an empty open gap (the contrapositive of
    `sorted_gap_excludes`);
  * `nmRowEncodes_of_adjacency` — `NmRowEncodes` is DERIVED from the forced adjacency, not assumed;
  * `circuit_gate_meets_executor_guard_forced` — concludes `nf ∉ k.nullifiers` carrying NO
    `NmRowEncodes` hypothesis (only the wire-forced `NmRowAdjacencyForced`);
  * `wide_bracket_forge_rejected` — a non-consecutive `(lo,hi)` cannot satisfy `Adjacent`, so the
    forced-soundness lane is uninhabited (the Lean shadow of
    `forge_nonconsecutive_wide_bracket_is_rejected`).

All five are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). On the deployed
side, `turn/src/executor/membership_verifier.rs::verify_nullifier_nonmembership` composes the strict
bracket (`lo < nullifier < hi` over the leaf-felt domain) with `CircuitNeighborAdjacencyVerifier`
(the adjacency STARK). Mutation-confirm at the DEPLOYED verifier (not just the unit AIR):
`notespend_wide_bracket_double_spend_rejected` (the wide bracket is refused on the adjacency leg,
incl. a replay of a genuine consecutive proof under wide-bracket PIs),
`notespend_nonmembership_consecutive_accepts`, `notespend_nullifier_outside_bracket_rejected`.

**Remaining (D1-wire, a named flag-day — NOT a Lean gap):** wire the `verify_nullifier_nonmembership`
call into the noteSpend effect-descriptor emit / executor `apply_note_spend` so the deployed
noteSpend row REQUIRES a non-membership proof (today the executor enforces double-spend by the
in-memory `note_nullifiers` set, and the *light-client in-circuit* freshness force exists + is
mutation-confirmed as a standalone deployed gate but is not yet a required column of the noteSpend
descriptor — that wiring touches the IR hash-site arity the §8 trailer named). The Lean force is now
a theorem; the Rust force is a tested deployed verifier; the call-site wiring is the residual.

### D2 — heapWrite: the header overstates its own definition
`CircuitSoundnessAssembled.lean:99-100,265-271` asserts heapWrite GAP-2 closed, `Rfix 56 =
heapWriteV3` "the LIVE Class-A heap-root recompute descriptor." But the file that DEFINES the
refinement (`RotatedKernelRefinementExercise.lean`) says, present-tense: `HeapWriteSpec` takes
`newRoot` as a **FREE parameter** (`:199`), `heapWriteV3 := graduateV1 (rotateV3
heapWriteVmDescriptor)` is the BASE (`:344`), the recompute-FORCING is a *separate* FIX
(`heapWriteEncodes.recompute` / `heapWrite_newRoot_forced` `:250`), and the sorted-tree SPLICE
(`heapsSplice`, the `heaps := heapWriteHeapsMap` content update) is the explicit **PHASE-E
residual** carried as a hypothesis (`:218,231`). So: the new-root register *can* be forced (FIX
exists), but (a) whether the LIVE `heapWriteV3` row wires that FIX vs carries the free-param spec,
and (b) the heap-content splice, are the un-carried-home 20–40%. Adversarially: a prover could
satisfy the base `heapWriteV3` with a `heap_root` advance that does not match the actual heap
content, unless the splice+recompute are forced into THE LIVE descriptor's row. **Bound ≠ forced,
made literal.**

### D3 — epoch stamps: the textbook bound-vs-forced gap
`EffectRefinement.lean:797` states it without euphemism: "What is NOT yet WRITE-GATE-forced is
that the descriptor binds the epoch WRITE (revokeDelegation's v1 face FREEZES `cap_root`; the
genuine epoch/snapshot move rides OFF-ROW)." The commitment BINDS limbs 30 (epoch) + 24
(snapshot) — that is the 60–80% scaffolding. The deployed gate does not FORCE the write — that is
the 20–40%. Carried as `RevokeDelegationEpochResidual` (`:809`), a fail-closed data-bearing Prop
(NOT an open hole), conjoined onto `revokeCircuitStep`. Same for spawn/refresh. Closure = the
moving-face V3-base descriptor cutover, a VK change.

### D4 — handler `hinner` and metadata (handler lane, not circuit)
`handler_refines_execFullA_exercise` (`HandlerExecutor.lean:1199`) carries `hinner` — the
inner-fold-reaches-the-same-kernel — as an un-discharged hypothesis. And the ONE live
`HandlerOpenFronts` entry (`:53-72`): spawn/factory map to born-empty `createCellH`, so the
cap-handoff (`caps`/`delegate`/`delegations`) and factory-install (`factoryVkField`/
`initialFields`/`slotCaveats`) writes are UNVERIFIED *by the handler refinement*. NOTE the scope:
the *circuit* spawn cap-handoff IS forced (`Rfix 19 = spawnWriteCapOpenV3`); this is specifically
the handler-executor refinement lane. The facet-mask leg is genuinely closed (no shortcut).

### F3 — why WitnessDecodes is a floor, not a dangerous-assumed item
`WitnessDecodes` (`CircuitSoundness.lean:446`) = the prover committed to the kernels whose roots
its trace publishes (and to its own trace's column decode). It MUST NOT be discharged by assuming
the apex's conclusion (`:443`, explicit). It is the same KIND of object as `StarkSound` — a §8
prover/circuit obligation, realizable (`closedWitness_of_readouts` BUILDS the bundle from genuine
readouts, `ClosureFinal.lean:202`). So it is a floor, not an un-carried-home binding. The
per-effect `<effect>Encodes` (rotatedEncodes etc.) are the same class: the circuit's own decode
the LEDGER-root commitment cannot give. (Distinguish from D1's `NmRowEncodes`, which is NOT this
class: it is a *committed-root adjacency* binding the running circuit lacks and a built AIR
supplies — a missing FORCE, not a prover self-commitment.)

---

## Final ranking — the real soundness items, by danger

1. **D1 — noteSpend `NmRowEncodes` / adjacency opening.** Only item with a concrete forgery;
   forcing AIR already built+tested; residual is integration. **Do this first.**
2. **D2 — heapWrite splice/recompute into the LIVE descriptor** (and correct the overstated
   header). Bound-not-forced; a prover could publish a heap-root not matching heap content.
3. **D3 — the three epoch-stamp moving-face cutovers.** Bound-not-forced; fail-closed today, but
   the descriptor binds rather than forces; VK-affecting close.
4. **D4 — handler `hinner` + spawn/factory metadata refinement.** Handler-executor lane;
   circuit lane already forces the cap-handoff.
5. **D5 — #139 rest-hash wire conformance.** Rust circuit-emit conformance, not a Lean gap.

The floors (F1–F3) are the TCB; the stale/done items (S1–S4) survived adversarial re-check.
**The apex's GLOBAL unfoolability rests only on floors + a built-from-readouts witness; the
honest concern is that its PER-EFFECT faithfulness for heapWrite (D2) and the three epoch moves
(D3) is commitment-bound-but-not-gate-forced, and the noteSpend non-membership (D1) rests on an
assumed adjacency decode whose forcing object exists but is unwired.**

*Census verified against HEAD `34950c586`. READ-ONLY: no code edited, nothing committed. Every
"done/closed" claim was re-checked against the source it cites; D2's header claim was found to
overstate its own definition file.*
