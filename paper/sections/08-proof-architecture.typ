// =============================================================================
// Section 8: The proof architecture
// =============================================================================

#import "../defs.typ": lean
= The proof architecture: ARGUS and path preservation <sec-proof-arch>

@sec-proofs states what a proof says: a verifier holding one root learns the
whole history. This section is how that claim is kept *honest as the proof system
itself changes shape*. The arithmetization is not frozen --- the field, the
commitment layout, and the per-effect circuits evolve --- and a verified
substrate has to guarantee that evolution never opens a gap the @sec-intro
adversary, the server that ran the protocol wrong, can slip through. The
discipline that guarantees it has three parts: the circuit *witnesses correct
evolution* (ARGUS), the circuit shape *rotates* under proof, and every finalized
turn *stays proven across shapes*.

== ARGUS: the circuit witnesses correct evolution

The design principle of the proof layer is that the proof is not an external
certificate *about* a run but an internal witness *of the protocol's correct
evolution*. A light client that checks one aggregate root is fooled exactly when
it can be convinced of a transition the kernel would not have produced; the
circuit is built so that no such proof exists. This is the negation @sec-intro
names --- the *pale ghost*, a history that verifies but never happened --- and
the whole circuit architecture is derived from ruling it out, not from matching
whatever the executor's host implementation happened to compute.

Concretely, ARGUS is the two-readings discipline of @sec-proofs carried to every
effect. Each kernel statement is a descriptor; the executor reading (`interp`)
and the circuit reading (`compile`) are obtained from the *same* descriptor, and
the receipt-level weld #lean("Argus.Receipt.argus_circuit_executor_receipts_agree")
proves they cannot disagree. Because the circuit reading is generated, not
hand-authored, there is no second source of truth to drift: a coverage gap is
closed by emitting from a proved Lean module, and the worthwhile semantics the
proof attests is *derived from the unfoolability requirement*, never inherited
from a lossy host encoding. The per-effect statements live in
`Circuit/Argus/Effects/`; the aggregate realization is the Argus strand
(#lean("Argus.Aggregate.argus_strand_light_client"),
#lean("Argus.Aggregate.tampered_argus_strand_rejected")).

== The state commitment binds the whole post-state

The fidelity floor is the per-turn state commitment: the field from which the
proof's pre- and post-state are read. It is a chained Poseidon2 sponge over a
fixed limb layout --- the cells root, the application registers, the capability /
nullifier / heap map roots, and the lifecycle, epoch, and height fields --- so
that, under permutation collision-resistance, equal commitments imply equal
state in *every* limb, including the frame the step did not touch
(#lean("RotationLayout.rotatedCommit_binds")). The binding is non-vacuous limb by
limb: tampering with the heap root (#lean("RotationLayout.rotatedCommit_binds_heapRoot")),
a named register (#lean("RotationLayout.rotatedCommit_binds_named_field")), or the
receipt log --- by omission, reorder, extension, or truncation
(#lean("RotationLayout.rotatedCommit_binds_log"), composing
#lean("RotationLayout.mroot_injective")) --- produces a distinct commitment. The
chained absorption itself is the circuit-side construction `wireCommit`, proved
collision-resistant against the same floor
(#lean("EffectVmEmitRotation.wireCommit_binds")). This is the @sec-proofs
"receipt binds the whole post-state" made a property of the arithmetized field,
so a proof cannot certify a post-state that differs anywhere from the one the
executor produced.

== Rotation: the circuit shape evolves under proof

The commitment layout and the per-effect circuit cohort are not fixed constants;
they *rotate*. A rotation is a coordinated regeneration of the arithmetization
--- the limb layout, the per-effect descriptors, and the verifying key together
--- carried out under a single discipline: the rotated shape is proven to enforce
the same semantics as the shape it replaces *before* any verifying key changes.
The mechanism is one parametric transformation, #lean("EffectVmEmitRotationV3.rotateV3"),
that appends the rotated commitment block to any per-effect descriptor, and two
keystones that make the rotation safe to land:

- *equivalent enforcement* --- a rotated descriptor forces exactly the
  pre-rotation per-effect satisfaction semantics, so rotating adds no new
  per-effect proof obligation
  (#lean("EffectVmEmitRotationV3.rotateV3_satisfiedVm_v1"));
- *equal published state* --- a pre-rotation and a rotated witness of the same
  effect publish the same state (cells root, registers, map roots, nullifiers),
  so the rotation cannot change what a turn means
  (#lean("EffectVmEmitRotationV3.rotV3_binds_published")).

Rotation is a *staged-additive-then-cutover* operation: the rotated cohort is
generated and proven beside the live path, with the legacy path byte-identical
and its drift guards green, and the verifying-key change is a single deliberate
step that makes the rotated shape live. The economics are measured before that
step, not assumed: a real multi-operation heap turn proves at a measured size,
and the always-paid register limbs versus the metered heap limbs are priced from
that measurement. The cell-side and circuit-side state shapes are kept identical
by a differential that takes a real turn's post-state through both the cell's
commitment and the circuit's trace and asserts they agree, with anti-tamper teeth.

== Path preservation: every finalized turn stays proven

Rotation raises a sharper obligation than "the new shape is sound": *every turn
the system has ever finalized must remain provable on the live path, including
turns whose shape is heterogeneous.* A single turn may exercise several distinct
effect kinds, and an actor's cell may carry arbitrary fields and capabilities ---
shapes a single monolithic per-effect leg does not cover. Path preservation is
the composition that covers them without authoring a new circuit: a heterogeneous
turn is split into maximal *cohort-runs* --- contiguous spans whose effects all
resolve to one rotated descriptor --- each cohort-run proves through its
Lean-emitted descriptor, and the legs are *chained* by an adjacency check, each
run's post-commitment equal to the next run's pre-commitment. A homogeneous turn
is one run, byte-identical to the single-leg case; the chain only generalizes it.

The composition is verifier-side arithmetic over the existing Lean-emitted
descriptors --- it authors no new constraint (the @sec-proofs law). The per-leg
binding each cohort descriptor already proves
(#lean("EffectVmEmitRotationV3.rotV3_binds_published")) pins each leg's pre/post;
the verifier adds the adjacency check (a chain break is a typed rejection), pins
each leg's effect span by re-deriving the cohort split, and sums the per-leg net
deltas to the turn's declared total, so conservation rides the chain. The result
is the @sec-proofs light-client guarantee made *robust to the proof system's own
evolution*: the aggregate a light client checks
(#lean("RecursiveAggregation.light_client_verifies_whole_history")) folds the
rotated, chained legs, and no finalized turn falls back to an unverified path on
account of its shape.

#emph[Scope.] The rotated cohort covers the live-path effects; two effect kinds
whose circuits require constructions the current per-row arithmetization does not
express (a capability-revocation circuit under active reshaping, and a custom
recursive-binding effect) resolve fail-closed to the monolithic path rather than
to a rotated descriptor, and total rotated coverage of heterogeneous turns on the
live path is the in-progress edge --- the chaining mechanism and its per-leg
binding are proven, the live cutover of every heterogeneous shape is staged.
@sec-limitations states this as a checkable fact, not a roadmap.
