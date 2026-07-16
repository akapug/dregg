// =============================================================================
// Section 1: Introduction
// =============================================================================

#import "../defs.typ": lean
= Introduction <sec-intro>

A distributed object-capability substrate has one hard problem: a party absent
from a transition must still be able to verify that it happened correctly.
dregg makes the proof witness the protocol's *correct evolution*. Subject to
the assumption floor stated in @sec-assurance, a new node, auditor, or phone can
check one aggregate root and learn that the attested history was authorized,
conserved value, and was faithfully committed. It re-executes nothing and need
not trust the executor. The design follows from the adversarial form of this
requirement: a server that ran the protocol incorrectly must not be able to
convince a light client otherwise.

Each proof-carrying turn is designed along three axes. It is
*non-malleable*: every guarantee-relevant field is bound, so the proof cannot
be re-pointed at a different state or receipt. It is *precondition-complete*:
authority, availability, freshness, and non-amplification are circuit
conjuncts, not side checks a prover may omit. And it *refines the protocol*:
the attested relation is the kernel's semantics, not a lossy re-encoding.
Together these properties exclude the central failure mode --- a history that
verifies although the kernel could not have produced it --- conditional on the
proof-system carrier made explicit in @sec-proofs.

== The sentence

The whole system is one sentence, given algebra:

#align(center)[
  _A turn is the exercise of an attenuable, proof-carrying token over owned
  state, leaving a verifiable receipt._
]

State lives in *cells*. A *turn* exercises authority --- a *token* that may be
attenuated on every axis and that carries a proof of its own legitimacy ---
over *owned state*, and leaves *Q*, a receipt that commits to the result. The
section on the model fixes the nouns; the section on authorization gives the
authority logic; the section on proofs gives the receipt and its aggregation.

== The organizing asymmetry

dregg treats authority as *constructive knowledge*. To hold a capability is to
be able to exhibit a witness that authorizes an act, never merely to assert
it. This is the realizability reading of intuitionistic logic made
operational, and it rests on one asymmetry:

#align(center)[
  _proof-checking is cheap and trusted; proof-search is undecidable and untrusted._
]

Every trust decision in the system is a check. Whoever wants to act bears the
burden of producing a witness; whoever guards state only ever verifies. A
capability is not a key in a lock --- it is a proof obligation one can
discharge. The asymmetry places search at the untrusted edges (solvers, intent
matchers, provers) and checking at the trusted core (the executor, the
circuit, the light client). It is the same asymmetry that lets a STARK
verifier accept a statement it could not have found.

== What the kernel governs

The kernel governs four *substances*, each under a discipline of use --- a law
about how it may move through time. Value is *linear*: per asset, the resource
sum across a turn is exactly zero. Authority is *produced under
non-forgeability*: it grows only by authorized, receipt-disclosed construction
from connectivity already held, and narrows freely along one edge. Evidence is
*monotone*: once known, never unknown. State is *guarded-mutable*: it changes
only under a predicate, only by its owner. The kernel's signature is seven
constructors, with `shield` and `unshield` as the two directions of one evidence
operation. Each is assigned a structural role in a substance discipline; the
section on the model states the roster and the exact, signature-level
independence property proved about that assignment.

The authority discipline is the one most often gotten wrong. A model in which
every step only narrows --- a monotone descent down a lattice --- forbids the
patterns that give capabilities their power: a holder introducing a third
party, an unsealer combining with a sealed box to yield contents neither names
alone, a mint creating fresh resource on an authorized gesture. dregg's
authority law is generative *and* disciplined: authority grows, but every
generative act is itself authorized by held knowledge and lands on the chain
receipt-disclosed. The section on authorization states this as one law,
Miller's _only connectivity begets connectivity_.

Everything that constrains a turn --- a caveat on delegated power, a program
on owned state, a precondition on a turn, a demand on the world --- is one
algebra of decidable predicates over the proposed step. The predicate the
executor evaluates is compiled to the circuit obligation a proof discharges,
so an installable guard and a provable property are one mechanism. Two prices
are computed rather than assumed. A *coordination dial* classifies whether two
concurrent turns merge without coordination: a confluence-stable guard runs
coordination-free, one that is not provably so forces ordering, and the
classifier prices the difference rather than forbidding the expensive case. A
*disclosure dial* governs how much a guard reveals while checking ---
cleartext, committed, range-proved, jointly-garbled --- on the principle that
what the proof does not need, it does not ask to see.

== The proofs are about the thing that runs

The semantics are a Lean 4 development that is *also the deployed executor*.
The gated whole-forest step #lean("execFullForestG") is compiled, exported
through FFI as `dregg_exec_full_forest_auth`, and invoked by the node on its
production path. The running-entry guarantee
(#lean("AssuranceCase.running_entry_sound")) is stated over exactly this
function: conservation, non-amplification, and per-node attestation hold over
the entry the node calls, not over an abstract model beside it.

The proof system inherits the same discipline. Each kernel statement carries a
descriptor from which both the executor reading and the circuit obligation are
obtained, and an agreement theorem welds the two readings
(#lean("Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree")). No
constraint is authored in Rust, and this is an enforced invariant, not a
convention. The hand-written STARK engine is deleted; the descriptor prover
(`prove_vm_descriptor2` / `verify_vm_descriptor2` in
`circuit/src/descriptor_ir2.rs`), driven by Lean-emitted descriptors, is the
only production proving path. The last first-party circuit authored in Rust
--- the non-revocation freshness check --- is retired: its constraints are
emitted from `Dregg2/Circuit/Emit/NonRevocationAdjacencyEmit.lean`, and the
deployed prover loads the emitted descriptor by name
(`circuit/src/dsl/revocation.rs`). Two gates keep this true. A ratcheting test
scans every source file in the circuit crates across all three constraint
dialects --- symbolic builder calls, evaluation closures, and constraint-
expression literals --- and fails the build on any new or grown Rust-authored
constraint algebra (`circuit-prove/tests/law1_enforcement_gate.rs`). A
pull-request check detects re-authored mirrors --- a hand-typed copy standing
in for a loaded artifact --- and runs a canary against itself before each run,
refusing to report from a gate that cannot fail
(`scripts/check-mirror-gates.sh`).

== The assurance case is an artifact

The system's guarantees are a Lean file,
`metatheory/Dregg2/AssuranceCase.lean`. It states five guarantees ---
authority, conservation, integrity, freshness, unfoolability --- plus a
running entry that closes the first three over the deployed function. Under
each guarantee it assembles the keystone theorems that discharge it, and it
`#assert_axioms`-pins every name: the build fails unless each theorem's full
axiom set is exactly the kernel triple
${"propext", "Classical.choice", "Quot.sound"}$. Everything else enters as an
explicit floor of eight cryptographic and liveness carriers, stated as
hypotheses rather than axioms. On the verified entry there is no
trusted-executor premise, no out-of-band "this was authorized" premise, and no
guarantee-relevant field of the post-state omitted from the commitment.
@sec-limitations states where host execution and deployment state remain
outside that claim.

== Applications inherit theorems

Applications do not extend the kernel; they are cells. A *factory* publishes a
descriptor --- a slot layout plus predicate constraints --- and the `create`
verb mints cells from it. From that moment the executor enforces the program
on every turn touching the cell. Recurring coordination shapes --- escrow,
obligations, queues, mailboxes, bridges, sealer/unsealer boxes --- ship as
verified factories whose safety keystones are kernel theorems, so an
application's contract is inherited from the kernel rather than re-established
per app. The shape is uniform: value at stake lives in the minted cell's own
balance column, so funding and settling are ordinary moves and conservation is
the ordinary kernel law with no side tables. The section on realization
develops the catalog.
