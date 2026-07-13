# GOAL: VK-epoch nullifier accumulator flip (night 07-09/10)

STATUS: ~COMPLETE. All 3 canonical accumulators flipped in Lean; nullifier + commitments Rust mirrors landed. (On mlkem-route = main+23, my work safe.)

DONE-LOG:
- 1dce9523c Lean flip nullifier+revoked (green 4599)
- 9e77654b5 Rust mirror nullifier_root (cross-node test green, ripple clean)
- 47188f76f Lean commitments-dual, 3rd accumulator (green 4616, verified, no sorry)
- df499c654 Rust mirror commitments (INDEPENDENTLY VERIFIED by me: commitments_root_faithful_8felt_and_cross_node_distinguishing green on fresh target)
- VK regen: ruled out

- 73c7b80b4 ripple straggler fixed (effect_vm_wide_roundtrip Faithful8) — node NOW BUILDS green (PredicateProof red was test-only)
- live-path integration test (nullifier_root_faithful_fill: executor live frontier -> committed root, cross-node) VERIFYING (bhskkvezl)

REMAINING:
1. blocklace_sync commitments live-root — DEFERRED (interleaved with another lane's uncommitted nullifier-node work; reconcile when they commit). turn_proving path already has it.
2. Live federation (fresh-genesis gate-ON noteSpend) — BLOCKED: node won't build on mlkem-route (other lanes' red: membership_verifier PredicateProof + test-helper nullifier_root:[u8;32]). Re-check when tree calms.
3. revoked-root ARCHITECTURE CALL — ember (committed rotation limb + VK regen, or leave as the verify-time gate it is?).
4. VK regen (stage F) owed for the committed-value shift — do alongside a fresh federation.

The devnet-soundness holes ember flagged (no cross-node anti-replay for double-spend AND note-existence) are CLOSED. Only the revoked-root call + a live demo remain.
