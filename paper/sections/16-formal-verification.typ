// =============================================================================
// Section 16: Formal Verification
// =============================================================================

= Formal Verification <sec-formal>

Dragon's Egg's assurance story has two layers. The Rust heritage runtime (`dreggrs`)
provides a typed composition checker and an adversarial test suite (described first). The
authoritative specification is a machine-checked Lean 4 development (`dregg2`), where the
turn executor, the verified-by-construction circuit emission, and the distributed-protocol
and CapTP guarantees are *proved* rather than tested. The Lean layer is the substance of this
section; the Rust-side checks remain the engineering safety net while the runtime is swapped
onto the verified executor. Throughout, proofs are treated as *additive attestation* over the
running system, and every place a guarantee rests on a named assumption is flagged.

== Typed Composition Checker

Dragon's Egg's proof system comprises 30+ circuit descriptors that must compose correctly. A _typed composition checker_ verifies at compile time that composed proofs maintain soundness---that public input/output types align, that witness bindings are consistent, and that trust assumptions compose without contradiction.

=== Circuit Descriptors

Each circuit in the system is described by a `CircuitDescriptor`:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Field*], [*Description*]),
    [`name: &str`], [Human-readable circuit identifier],
    [`public_inputs: Vec<TypedSlot>`], [Typed public input schema],
    [`public_outputs: Vec<TypedSlot>`], [Typed public output schema],
    [`witness_schema: Vec<TypedSlot>`], [Private witness structure],
    [`constraint_degree: usize`], [Maximum polynomial degree in AIR],
    [`trust_assumptions: Vec<Assumption>`], [Explicit trust model],
    [`soundness_bits: usize`], [Security parameter (typically 124)],
  ),
  caption: [CircuitDescriptor fields. The typed schema enables compile-time composition checking.],
)

=== Composition Rules

The four composition operators are type-checked:

*`compose_chain(A, B)`*: Sequential composition. Requires $A."public_outputs" supset.eq B."public_inputs"$ (type-compatible). The composed circuit proves "A then B" with $A$'s outputs fed as $B$'s inputs.

*`compose_and(A, B)`*: Parallel conjunction. Both proofs must be valid. Public inputs are the union of $A$ and $B$'s inputs. Trust assumptions are the union.

*`compose_or(A, B)`*: Parallel disjunction. At least one proof must be valid. Public inputs must have compatible types. Trust assumptions are the intersection (only assumptions common to both paths hold unconditionally).

*`compose_aggregate([A_1, ..., A_n])`*: Batch composition. All $n$ proofs are valid. Amortizes verification cost. Trust assumptions are the union of all components.

=== Type Errors Caught at Compile Time

The checker prevents:

- Feeding a nullifier (field element) where a state commitment (hash) is expected.
- Composing circuits with incompatible field sizes (BabyBear vs. BN254).
- Chaining circuits where the output of $A$ is a different Merkle root type than the input of $B$.
- Aggregating circuits with contradictory trust assumptions.

== The 30-Circuit Catalog

Dragon's Egg's proof system comprises the following verified circuit descriptors:

=== Core Cryptographic Circuits (8)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [Poseidon2 Permutation], [7], [Correct hash computation],
    [Merkle Membership (4-ary)], [7], [Leaf exists in committed tree],
    [Merkle Non-Membership], [7], [Leaf does NOT exist in committed tree],
    [Note Spending], [7], [Nullifier correctly derived, note exists],
    [Range Proof], [3], [Value in range $[0, 2^k)$ without revealing value],
    [Pedersen Commitment], [5], [Value correctly committed with blinding],
    [Ed25519 Signature], [5], [Signature valid for message and public key],
    [BLS12-381 Aggregation], [7], [Aggregate signature valid],
  ),
  caption: [Core cryptographic circuits. These are the building blocks for all higher-level proofs.],
)

=== Authorization Circuits (6)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [Fold (attenuation step)], [7], [Single capability restriction is valid],
    [Multi-Step Fold (IVC)], [7], [Chain of $k$ restrictions from root],
    [Derivation (Datalog)], [7], [Authorization rules yield "allow"],
    [Body Membership], [7], [Facts used in derivation exist in tree],
    [Blinded Issuer Ring], [7], [Issuer is in set without revealing which],
    [Presentation Randomization], [7], [Blinded tag correctly derived from root],
  ),
  caption: [Authorization circuits. Compose to prove "I am authorized" without revealing the chain.],
)

=== Effect VM Circuits (5)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [Effect VM (14 effects)], [7], [Arbitrary turn is valid (conservation + state + auth)],
    [Conservation], [3], [Total value in $=$ total value out],
    [State Continuity], [7], [Post-state correctly derived from pre-state + effects],
    [CapTP Send], [7], [Message correctly dispatched via protocol],
    [CapTP Handoff], [5], [Certificate correctly constructed],
  ),
  caption: [Effect VM circuits. The Effect VM composes all per-effect proofs into a single STARK per turn.],
)

=== Governance and Economics Circuits (6)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [DFA Classification], [3], [Message correctly classified by committed DFA],
    [Fee Sufficiency], [3], [Turn fee covers base fee + priority],
    [Stake Threshold], [3], [Staked value $>=$ minimum without revealing exact],
    [Budget Gate], [3], [Silo budget not exceeded (Stingray bounded counter)],
    [Conditional Turn], [7], [Turn executes only if condition proof verified],
    [Intent Satisfaction], [7], [Solution satisfies all intent constraints],
  ),
  caption: [Governance and economics circuits. Enable privacy-preserving economic participation.],
)

=== Bridge and Recursion Circuits (5)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [IVC Compression], [7], [Receipt chain valid from genesis (constant-size)],
    [STARK-in-Kimchi], [7], [BabyBear STARK verified inside Pasta circuit],
    [Plonky3 Recursive], [7], [Inner proof verified by outer proof],
    [SP1 Guest (STARK Verifier)], [N/A (RISC-V)], [STARK valid (for Groth16 extraction)],
    [Checkpoint Proof], [7], [Group state at height $H$ is commitment $C$],
  ),
  caption: [Bridge and recursion circuits. Enable cross-system proof translation.],
)

== Cryptographic Guarantees

The system provides 11 cryptographic guarantees, each derivable from the circuit catalog:

+ *Authorization soundness*: No cell can exercise a capability it was not delegated (Fold + Derivation + Body Membership).
+ *Attenuation monotonicity*: Delegation can only narrow scope (Fold constraint: $F_(i+1) subset.eq F_i$).
+ *Conservation*: No value created or destroyed in a turn (Conservation circuit).
+ *State continuity*: Post-state is deterministically derived from pre-state + effects (State Continuity).
+ *Nullifier uniqueness*: No note spent twice (Note Spending + federation nullifier set).
+ *Issuer anonymity*: Verifier cannot determine which group member issued a credential (Blinded Issuer Ring).
+ *Presentation unlinkability*: Multiple presentations of the same credential are uncorrelatable (Presentation Randomization).
+ *Routing integrity*: Messages are classified according to the committed DFA (DFA Classification).
+ *Fee validity*: Every turn pays at least the base fee (Fee Sufficiency).
+ *Stake privacy*: Validator stake amount is hidden; only threshold satisfaction is proven (Stake Threshold + Range Proof).
+ *IVC correctness*: Any receipt chain can be verified from genesis in constant time (IVC Compression).

== Trust Boundary

The system explicitly identifies 7 trust assumptions---points where cryptographic proofs are insufficient and operational trust is required:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Assumption*], [*Boundary*], [*Mitigation*]),
    [Federation honest majority], [$f < n\/3$ Byzantine], [Equivocation detection + slashing],
    [Executor state correctness], [Executor faithfully maintains state], [Challenge protocol + bonding],
    [Swiss table integrity], [Federation maintains swiss table], [Replication across nodes],
    [Relay availability], [Relays deliver messages (may delay)], [Multiple relays + TTL],
    [Clock synchrony], [Bounded clock drift for TTL], [NTP + generous bounds],
    [RNG quality], [Random number generators produce entropy], [Hardware RNG + mixing],
    [Cryptographic hardness], [Poseidon2, Ed25519, BLS12-381, FRI], [Conservative parameters + agility],
  ),
  caption: [Explicit trust assumptions. Each is documented, bounded, and mitigated.],
)

The key principle: every trust assumption is _explicit_ and _bounded_. No assumption says "the system is secure"---each says "IF this specific property holds (with this specific mitigation), THEN this specific guarantee follows."

== Verification Methodology

=== Compile-Time Checks

The typed composition checker runs at Rust compile time (via proc macros):

- All `compose_chain` calls are type-checked for input/output compatibility.
- All `compose_and` calls verify no conflicting assumptions.
- Circuit degree bounds are verified against FRI parameters.
- Public input schemas are checked against proof generation code.

=== Test-Time Verification

The test suite (4,046 tests) includes:

- *Soundness tests*: For each circuit, verify that invalid witnesses produce failing proofs (adversarial testing).
- *Composition tests*: For each composition operator, verify that composed proofs are valid iff both components are valid.
- *Property tests*: Proptest-generated random inputs verify conservation, monotonicity, and nullifier properties across 10,000+ random cases.
- *Regression tests*: Every security audit finding has a regression test that would catch reintroduction.

== The Lean 4 Kernel: `dregg2`

The compile-time and test-time disciplines above describe the Rust heritage codebase
(`dreggrs`). Since the May draft, the project's center of gravity has moved: the
authoritative specification of Dragon's Egg is now a machine-checked Lean 4 development,
`dregg2` (the `metatheory/Dregg2/` tree). `dregg2` is not a sketch of "future work" --- it
is the primary artifact, and the Rust runtime is increasingly routed through, or
differentially checked against, it. The relationship is deliberate:

- *`dregg2` (Lean) is the verified primary.* A purely functional Lean executor
  (`Dregg2/Exec/TurnExecutorFull.lean`, `FullActionA`) defines the turn semantics for the
  full effect vocabulary. The drift-guarded ontology catalog
  (`site/tools/gen-ontology-catalog.js`) is generated *from this Lean source* and reports
  *56 effects* (across value, authority, state, lifecycle, escrow, privacy, bridge, seal,
  queue, and swiss families) with a required-authorization facet and a wire codec for every
  one (`facet 56/56`, `wire 56/56`). The 29-variant predicate vocabulary is checked the same
  way. The catalog's `--check` mode is byte-stable against the source, so the paper's effect
  and constraint counts cannot silently drift from the verified model.
- *`dreggrs` (Rust) is the heritage runtime.* It carries the network stack, the production
  provers, the live node, the CLI, the extension, and the QUIC consensus. It is being
  *swapped* onto the verified executor on the commit path rather than trusted on its own
  say-so; a Rust$arrow.l.r$Lean differential harness drives concrete corpora through both and
  flags divergence.

The Lean development is axiom-disciplined. The load-bearing distributed-protocol and CapTP
modules are `#assert_axioms`-clean: they close against only Lean's standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) with *no* `sorry`, no `:= True` placeholder
specifications, and no `native_decide` shortcut. Where a property genuinely rests on a
cryptographic hardness assumption (collision-resistance of a state commitment, signature
unforgeability), the assumption is *named* as a typeclass hypothesis and the theorem is
proved relative to it --- it is not silently assumed away. We flag these named-assumption
seams explicitly below rather than presenting them as unconditional.

== Verified Execution and Circuit Emission

Two results connect the Lean kernel to what the runtime actually does.

*Verified executor.* The Lean executor runs the full effect set as a pure state transition
over a record-shaped kernel state. Per-effect soundness pins the *whole* post-state (not a
conservation projection): tampering with an untouched cell, a capability table, or a
nullifier makes the witnessed transition unsatisfiable (the anti-ghost discipline). Value
effects conserve; capability effects only attenuate (granted $subset.eq$ held); spending an
already-spent note is rejected by the nullifier set.

*Verified-by-construction circuit (ONE-circuit emission).* The May draft described several
hand-written AIRs (A/B/C) and a $tilde$151-column Effect VM trace. That architecture is being
*collapsed*: rather than maintaining hand-written constraints in parallel with the executor
(and trusting that they agree), the circuit is *emitted from the verified Lean executor* as a
single descriptor-driven AIR --- one circuit, derived from the same `FullActionA` semantics
the catalog is generated from. The migration is in flight (the `EffectVmEmit*` family of
emitters), and the live gate is a differential harness that proves the descriptor-driven
prover and the legacy hand-AIR accept exactly the same witnesses before any hand-AIR is
retired. We therefore do *not* restate a fixed column count here: the present-tense claim is
the emission discipline (circuit derived from the verified executor, not hand-maintained
beside it), not a specific trace width. Three production provers (a BabyBear/FRI STARK,
Plonky3's `p3-uni-stark`, and Kimchi/Pickles over the Pasta cycle) remain available as
proving backends for the emitted constraints.

== Verified Distributed Protocols

The single largest understatement of the May draft was to describe the distributed layer as
"consensus correctness tests under simulated network conditions." Those guarantees are now
*machine-checked theorems* in `dregg2`. Each module follows the same discipline: a faithful,
*executable* Lean model that mirrors the real Rust protocol line-for-line (cited to
`file:line`), a proved safety property the node relies on, a connection to the verified
executor where applicable, and a `#guard` golden-vector *differential* that the corresponding
Rust test reproduces.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Module*], [*Key theorems*], [*Guarantee*]),
    [`Distributed/BlocklaceFinality`],
      [`finalLeaderAt_unique`, `finalLeaders_one_per_wave`, `tauOrder_deterministic`, `tau_drives_verified_run`, `tau_execution_agreement`],
      [The node's real $tau$ finalization rule (blocklace `ordering.rs::tau`) yields a single anchor per wave and a deterministic total order, and that order drives the verified executor to a deterministic state.],
    [`Distributed/StrandIntegrity`],
      [`strand_single_tip`, `insert_preserves_forkFree`, `forkFree_of_honestChain`, `forked_strand_not_forkFree`],
      [Strand (= SSB feed) integrity: a fork-free strand has exactly one head, the fixed insert preserves fork-freedom, and every fork is a downstream-checkable incomparable pair.],
    [`Distributed/LaceMerge`],
      [`merge_comm`, `merge_assoc`, `merge_idem`, `merge_monotone`, `merge_least_upper_bound`, `merge_convergence_to_state`],
      [CRDT replica convergence: the blocklace merge is a join (commutative, associative, idempotent, monotone); replicas merging the same causally-closed blocks reach the same lace and --- via $tau$ determinism --- the same executed state.],
    [`Distributed/MembershipSafety`],
      [`apply_join_threshold`, `apply_leave_threshold`, `h_rule_passing_needs_both`, `passed_needs_quorum_in_past`, `membership_change_reparameterizes_finality`],
      [Governed membership: a Join/Leave applies only with a supermajority of *distinct current-member* approvals in causal past; the H-rule ($max(T,T')$) caps threshold manipulation, so no minority lowers the bar and no majority locks others out.],
    [`Distributed/EntangledJoint`],
      [`jointApplyAll_atomic`, `jointApplyAll_dichotomy`, `jointApplyAll_all_authorized`, `jointApplyAll_conserves`, `tryDebit_table_preserves_ok`, `jointBinding_one_identity`],
      [Multi-cell entanglement: an $N$-cell joint turn commits all legs or none (atomic), every leg is independently authorized, value is conserved across the joint, and a shared budget never overspends.],
    [`Distributed/CellMigration`],
      [`handoff_unique_home`, `accept_refuses_double`, `handoff_conserves_balance`, `handoff_conserves_caps`, `migrated_cannot_reprepare`],
      [Cross-federation cell handoff (Hosted$arrow.l.r$Sovereign): prepare$arrow$accept$arrow$commit leaves the cell live at exactly one home, conserves balance and capabilities byte-for-byte, and cannot be replayed.],
    [`Distributed/Consensus`],
      [`resilience_gap_real`, `safety_holds_below_tS`, `safety_can_break_above_tS`, `equivocation_excluded`, `honest_finalization_unforkable`, `no_conflicting_finalized_state_reconfig`, `blocklace_is_leaderless`],
      [A *resilience pair* (separate safety threshold $t_S$ and liveness threshold $t_L$, with $t_L < t_S$): safety holds below $t_S$ (and a negative theorem shows it *can* break above it), equivocators are repelled, and finalized state survives reconfiguration.],
    [`Distributed/Revocation`],
      [`eventual_bounded_revocation`, `immediate_revocation`, `single_machine_collapse`, `tightness_tooth`, `spec_nonvacuous`],
      [Topology-parametrized revocation: a credential is honored at most until $tau + "delay"$ and never after; the single-machine instance collapses this to immediate revocation (the dregg4 single-machine principle).],
    [`Distributed/FinalityGate`],
      [`gate_admits_iff_verified_finalizes`, `gate_deterministic`, `gate_admit_is_rule_output`],
      [The wire finalization gate admits exactly what the verified $tau$ rule finalizes, deterministically.],
  ),
  caption: [Machine-checked distributed-protocol theorems in `dregg2`. Each module is `#assert_axioms`-clean (only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`:= True`) and ships a Rust `#guard` differential.],
)

== Verified CapTP

The object-capability transport carries its own verified core. These modules pin the
properties on which cross-vat capability flow depends.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Module*], [*Key theorems*], [*Guarantee*]),
    [`Exec/CapTPHandoffSound`],
      [`handoff_installs_exactly`, `validateHandoff2_nonAmplifying`, `validateHandoff2_attenuates`, `handoff_unforgeable`, `adversary_cannot_forge_at_n_gt_1`, `forged_handoff_installs_nothing`],
      [Three-party handoff is non-amplifying (the installed authority $subset.eq$ the conferred authority) and *unforgeable*: a certificate not signed under the federation's keys installs nothing, even at $n > 1$ vats.],
    [`Exec/CapTPConcrete`],
      [`authNarrowerOrEqual_trans`, `grant_none_over_nonnone_amplifies`, `handoff_concrete_attenuation`, `handoff_non_amplifying_concrete`],
      [The concrete `AuthRequired` attenuation lattice the captp runtime enforces, pinned to Lean and mirrored by a Rust differential test (`handoff_lattice_differential.rs`) across the FFI gap.],
    [`Exec/CapTPGCConcrete`],
      [`drop_retains_when_refcount_gt_one`, `reclaim_only_at_last_ref`, `byzantine_cannot_drop_victim_ref`, `wrong_session_no_op`, `leased_reclaim_eventual`, `leased_no_premature`],
      [Distributed GC safety: a reference is reclaimed only at its last drop, a Byzantine peer cannot drop a victim's reference (wrong-session drops are no-ops), and leased references are eventually but never prematurely reclaimed.],
    [`Exec/CapTPConfinement`],
      [`enliven_unreachable_without_swiss`, `enliven_no_authority_without_swiss`, `enliven_confined_strong`, `unguessable_implies_unreachable`, `confinement_under_entropy`],
      [Swiss-number confinement: no authority is reachable without the (unguessable) swiss number; an adversary with bounded knowledge cannot enliven a reference.],
    [`Exec/CapTPSettlement`, `Exec/CapTPConsentLace`],
      [`settle_complete_is_drain`, `settle_atomic_aborts_on_unauthorized`, `settle_conserves`, `forged_approval_does_not_count`, `laceSettle_atomic_aborts_on_unauthorized`, `consent_equivocation_detectable`, `equivocating_party_blocks_settlement`],
      [Multi-party suspended settlement: a batch settles only when every party's *signed* consent is present in the lace, settlement is atomic (an unauthorized leg aborts the whole batch) and conserving, a forged approval does not count, and an equivocating party is detectable and blocks settlement.],
  ),
  caption: [Machine-checked CapTP theorems in `dregg2`. The swiss-table/GC/session surface is executor-trusted in the heritage runtime; these proofs pin the discipline the runtime must honor, and the Rust differentials gate drift across the FFI boundary.],
)

== Named-Assumption Seams (what is *not* unconditional)

Honesty requires naming where the proofs rest on assumptions rather than discharging them:

- *Cryptographic hardness.* Handoff unforgeability is proved relative to a `SignatureKernel`
  with a `unforgeable` law (instantiated by a reference kernel for the non-vacuity
  witnesses); state-commitment soundness rests on a collision-resistance assumption stated as
  a typeclass. These are standard reductions, but they are assumptions, not theorems about
  the concrete hash/signature primitives.
- *Circuit$arrow.l.r$executor gate is in flight.* The ONE-circuit emission is migrating; until
  every hand-AIR is retired behind the differential harness, the runtime's proving path is a
  mix of emitted and legacy constraints. We claim the emission *discipline*, not that the
  collapse is complete.
- *Liveness residual.* Consensus *safety* is proved below $t_S$; the post-GST *liveness*
  property is reduced to a named delivery model (`PostGSTProgress`), not proved from raw
  network assumptions --- this is flagged in the module itself.
- *The Lean$arrow.l.r$Rust swap is partial.* `dregg2` is the verified primary, but the live
  node still runs heritage Rust on several paths; the differential harness is how we shrink
  that gap, and the cutover ledger gates each deletion. The proofs are *additive attestation*
  over the running system, not a per-step gate that every production turn already passes
  through.

These modules are individually machine-checked (their compiled artifacts are present in the
Lean build and they are `#assert_axioms`-clean); two of them are under active edit by
concurrent verification work at the time of writing and are not yet folded into the single
default aggregate target. We name this rather than imply a frozen, fully-integrated whole.
