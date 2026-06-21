# SAFELY-LIVE-CHECKLIST — the mechanically-auditable burn-down

The goal "safely live within dregg" is satisfied when **every box below is checked, each by
its stated green check** — not by prose. Law #6: a named gap is never a deliverable. A box is
checked ONLY when its verification command is green at HEAD.

Reconciled against HEAD `867f6a66a` (audit a6473605). The dominant open axis is **WIRE, not
Lean**: 18 of 30 effects are FORCED-IN-LEAN (the apex consumes `Satisfied2(deployed descriptor)`,
editing the descriptor reds the apex) but the deployed producer selects the *plain* descriptor /
the verifier rides the record-pin residual. The single structural unlock is the producer
re-point + the VK epoch that absorbs the record-digest + sorted roots into `compute_commitment`.

## STATE TODAY (verified)
- FORCED-ON-WIRE + light-client-verifiable: **8/30** — transfer, burn, mint, bridgeMint, setField,
  incrementNonce, emitEvent, pipelinedSend (the moved column is already in `compute_commitment`'s preimage).
- FORCED-IN-LEAN-NOT-WIRE: **18/30** — lifecycle/permsVK/birth/notes/cap-write families.
- MODELLED-FLOOR (not yet `_sat`): receiptArchive, attenuate(2-arm), revoke(tag-2), refreshDelegation.
- cap-AUTHORITY light-client forge: **CLOSED** (verify rejects plain cap descriptors, e26fe42df).

## (A) WIRE — producer-selection re-point (VK-FREE-driveable NOW, the highest leverage)
- [ ] `rotated_descriptor_name` selects the apex-consumed write-bearing descriptor for the cap-write
      family — GRANT_CAP/DELEGATE→delegateWriteCapOpen, INTRODUCE→introduceWriteCapOpen,
      REVOKE_DELEGATION→revokeDelegationWriteCapOpen, +delegateAtten arm.
      **green:** a producer-selection test asserting each `rotated_descriptor_name(sel::X) == "…WriteCapOpenVmDescriptor2R24"` + `scripts/check-descriptor-drift.sh` PASS.
- [ ] the cap-WRITE light-client axis — `verify_full_turn` rejects the authority-ONLY CapOpen
      (no write) for write-bearing cap effects (extend `is_forbidden_plain_cap_descriptor`).
      **green:** a forge test — RevokeDelegation under `revokeCapOpen` (authority, no write) REJECTED.

## (B) GREEN-BOARD (VK-FREE-driveable NOW)
- [ ] `resolvers_cover_exactly_the_rotated_registry` RED (37 vs 36) — heapWriteVmDescriptor2R24 is a
      registry member with no resolver arm + no live HeapWrite Effect variant. Reconcile (add the
      Effect+selector+resolver if heapWrite is live, OR exclude it as separately-routed) — NOT a blind bump.
      **green:** `cargo test -p dregg-circuit resolvers_cover_exactly_the_rotated_registry`.
- [ ] receiptArchive(40) spec-bridge — the dispatch arm reduces to the toy record-slot `ReceiptArchiveSpec`;
      reconcile the arm to `ReceiptArchiveLifecycleSpec` (what the deployed disc gate forces) + a `_sat` discharger.
      **green:** editing `receiptArchiveV3`'s disc gate reds the apex (a mutation test).
- [ ] attenuate(12) + revoke(tag-2) `_sat` — the apex calls the modelled `attenuate_closedLog`/`revoke_closedLog`
      (encode-consuming), not a deployed-descriptor force-lemma. Wire `_sat` dischargers.
      **green:** editing the attenuate/revoke descriptor reds the apex.
- [ ] SetProgram circuit witness — SetProgram reuses EFFECT_SET_VERIFICATION_KEY's tag (action.rs:2191), no own rung.
      **green:** a `setProgramV3` descriptor + `closedLogExtract_setProgram_closed` in the apex.

## (C) VK EPOCH (ember-gated — but VK-FREEDOM ERA, so driveable; the unlock for all 18 not-on-wire)
- [ ] `compute_commitment` (cell_state.rs:76) absorbs the record-digest + sorted cap/nullifier/commitment/deleg
      roots, so the running circuit IS `S_live`/`Rfix` — the 18 FORCED-IN-LEAN writes become on-wire-realized,
      and a light client binds lifecycle/perms/vk/deathCert/nullifier/commitment columns, not just balance/nonce/field/cap_root.
      **green:** a light-client test rejecting a post-state differing ONLY in (lifecycle | permissions | vk | nullifier-root) under the deployed VK.
- [ ] refreshDelegation(55) deleg-tree write column — new deleg-tree map-op + its runtime column (cap_root is the wrong primitive).
      **green:** a `refreshDelegation_descriptorRefines_sat` consuming a deleg-tree write descriptor.

## INVARIANTS (must stay green throughout)
- [ ] `lake build Dregg2` axiom-clean (⊆ {propext, Classical.choice, Quot.sound}).
- [ ] `scripts/check-descriptor-drift.sh` PASS.
- [ ] `cargo test -p dregg-sdk --features prover` + `cargo test -p dregg-circuit` green.

## (D) OWN-LANE (NOT in the 30/30 write-binding scope — tracked, not blocking this goal)
- apexLowers distributed-modernization · l4v marshal translation-validation · WitnessDecodes prover wiring
  (the cap path-witness from the c-list) · network-genesis ceremony · HORIZONLOG compaction.

## HEADLINE GREEN-TEST (the goal is met when this is true)
30/30 effects FORCED-ON-WIRE + light-client-verifiable: every cap/write effect's producer selects + verifier
checks the authority-AND-write-bearing descriptor; (A)+(B)+(C) boxes checked; the INVARIANTS green; the board red-free.
