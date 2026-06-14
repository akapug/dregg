// =============================================================================
// Section 13: The assurance case
// =============================================================================

#import "../defs.typ": lean
= The assurance case <sec-assurance>

The system's guarantees are an artifact, not a narrative. `Dregg2/
AssuranceCase.lean` states them *by guarantee*, assembles under each the keystone
DAG that discharges it, and `#assert_axioms`-pins every name: the Lean build
fails unless each theorem's full axiom set is exactly the kernel triple
${"propext", "Classical.choice", "Quot.sound"}$ --- in particular, no `sorryAx`.
`Dregg2/Claims.lean` is the corpus-wide per-keystone pin net behind it. The
machine-readable form is the generated assurance catalog
(`studio/assurance-catalog.generated.json`); the paper states the guarantees and
defers the roster of record to it. Where a guarantee's substantive apex carries
long module-local frame hypotheses, the file uses a heading anchor and pins the
load-bearing keystone beneath it; the citations below name the keystone that
carries the content, not the anchor.

== The five guarantees and the running entry

*A --- Authority.* _Every state change is justified by an unforgeable,
non-amplified, fresh token chain._ The apex
#lean("AssuranceCase.authority_guarantee"): an introduction's conferred
capability is a genuine non-amplifying subset of the held one
(#lean("EffectsAuthority.introduce_non_amplifying")) *and* the predicate
discriminates --- an amplifying grant is rejected
(#lean("EffectsAuthority.amplifying_grant_rejected")). Keystones include the
per-mode admission soundness (#lean("AuthModes.captp_sound"),
#lean("AuthModes.bearer_sound"), #lean("AuthModes.token_sound")) and the
dispatcher gate #lean("AuthModes.captp_granted_le_held"). Floor: ed25519, HMAC,
Poseidon2-CR.

*B --- Conservation.* _Per asset, the resource sum is exactly zero across a turn
and a run._ The apex #lean("AssuranceCase.conservation_guarantee") over the
genuine multi-asset ledger: the moved asset's total is invariant
(#lean("RecordKernel.recTransferBal_sum_conserve_moved")) and every other asset
is pointwise untouched (#lean("RecordKernel.recTransferBal_untouched")), lifted
to the executor (#lean("RecordKernel.recKExec_conserves")) and to the abstract
monoid (#lean("Spec.conservation_over_monoid")), with
#lean("Spec.committed_iff_cleartext") proving the committed and cleartext
judgments agree. Floor: integer arithmetic only (Pedersen/DLog only when values
are committed).

*C --- Integrity.* _A receipt binds the whole post-state; a tampered input is
rejected._ The load-bearing apex is the cross-bind
#lean("CommitmentCrossBind.runnable_binds_same_system_roots"), with the teeth
#lean("CommitmentCrossBind.chC_bad_not_bridge") (a field-dropping commitment is
not a faithful bridge) and the one-receipt welds
(#lean("Argus.Receipt.argus_commits_to_one_receipt"),
#lean("Argus.Receipt.argus_circuit_executor_receipts_agree")). Floor:
Poseidon2-permutation-CR --- a second preimage is exactly the only way to forge a
receipt for a different state.

*D --- Freshness.* _No replay or double-spend; revocation takes effect at
finality._ The apex #lean("AssuranceCase.freshness_guarantee"): a committed
spend's nullifier was fresh, is now present, and a repeat fails closed
(#lean("noteSpendStmt_no_double_spend"), #lean("noteSpendStmt_replay_rejected")),
with non-membership a witnessed opening
(#lean("NonMembership.nonmembership_sound") and
#lean("NonMembership.nonmembership_complete")), never a scan. Revocation is
consensus-bound (#lean("Liveness.revocation_needs_consensus")), with its
undecidable dual pinned alongside (#lean("Liveness.dead_undecidable")). Floor:
Poseidon2-CR; PostGSTProgress for the at-finality leg.

*E --- Unfoolability.* _A light client verifying a Q-chain learns A--D for the
whole history while re-witnessing nothing._ The load-bearing apex is
#lean("RecursiveAggregation.light_client_verifies_whole_history") (@sec-proofs)
with the anti-tamper teeth (#lean("RecursiveAggregation.tampered_aggregate_cannot_bind"),
#lean("RecursiveAggregation.leaf_pairing_defeats_swap")) and the strand
realization (#lean("Argus.Aggregate.argus_strand_light_client")). The whole
attested history conserves along the fold
(#lean("RecursiveAggregation.attested_history_conserves")). Floor: FRI/STARK
soundness (#lean("EngineSound.recursive_sound")), Poseidon2-CR, ed25519,
PostGSTProgress.

*R --- The running entry.* _A, B, and C hold over what the node actually
invokes._ The five guarantees above are stated over the kernel; guarantee R
closes the gap to the deployment in one statement,
#lean("FullForestAuth.running_entry_sound"), about
#lean("FullForestAuth.execFullForestG") --- the body behind the
`dregg_exec_full_forest_auth` FFI export (@sec-realization): a committed gated
forest conserves per asset, every delegation edge is non-amplifying
(#lean("FullForestAuth.execFullForestG_no_amplify")), and every node at every
depth attests its gate (credential, caveats, capability-authority, and the
per-asset obligation). The gate adds teeth without weakening the linear
guarantees (#lean("FullForestAuth.execFullForestG_unauthorized_fails")).

== The assumption floor

Everything above is unconditional in the Lean-kernel sense *modulo* eight
carriers --- entering as `Prop`-portals (typeclass fields or hypotheses), never
as axioms; nothing else is load-bearing anywhere in the case.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*carrier*], [*what it guards*]),
    [Poseidon2-permutation CR], [sponge / Merkle / state commitments reduce to
      permutation collision-resistance],
    [BLAKE3 CR], [the out-of-circuit content / transcript hash],
    [ed25519 EUF-CMA], [turn and strand-block signatures],
    [HMAC (PRF/MAC) unforgeability], [macaroon caveat-chain tags],
    [AEAD confidentiality + integrity], [sealed-value / disclosure payloads],
    [discrete-log hardness], [Pedersen value commitments],
    [FRI / STARK soundness], [a verifying proof attests its statement
      (#lean("EngineSound.recursive_sound"))],
    [PostGSTProgress], [eventual synchrony after GST --- the consensus liveness
      carrier (@sec-ordering)],
  ),
  caption: [The eight-carrier floor. The first seven are cryptographic; the last
    is liveness. Safety rests on the cryptographic seven; liveness additionally
    on the eighth.],
)

In particular: there is no trusted executor, no out-of-band "this was
authorized" premise, and no field of the post-state left uncommitted.
