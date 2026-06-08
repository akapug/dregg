// =============================================================================
// Section 1: Introduction
// =============================================================================

= Introduction

Cross-domain authorization for autonomous agents presents a challenge that existing systems address incompletely. Consider an AI agent dispatched by Organization A to invoke a service hosted by Organization B. The agent must prove it is authorized---but without revealing Organization A's internal delegation structure, the identities of intermediate signatories, or what other capabilities the agent holds. Further: the *transition* the agent's invocation produces on B's ledger must be algebraically tied back to the authority A delegated, so that a third party reviewing the joint record weeks later can re-derive the entire chain without trusting either A or B's executor to have been honest.

Existing approaches each fail along a different axis:

- *UCAN/ZCAP-LD* @ucan provide delegation chains but require revealing the full chain to the verifier. Privacy is absent.
- *Coconut credentials* @coconut offer selective disclosure of attributes but lack the delegation semantics needed for capability attenuation.
- *Cap'n Proto RPC* provides promise pipelining and E-style messaging but operates within a single trust domain with no privacy, no proof of authorization, and no offline verification.
- *Blockchain-based authorization* achieves transparency but requires chain liveness, incurs gas costs, and exposes all authorization state on-chain.
- *seL4* @sel4 provides a rigorous Capability Derivation Tree with synchronous kernel-enforced revocation, but requires a single address space and cannot distribute across trust boundaries.

== The thesis: proof-carrying capability mesh

Dragon's Egg frames the answer as a single shape---a *proof-carrying capability mesh*. The kernel of the system is:

+ *OCapN-lineage Capability Transport Protocol* between sovereign cells (vats), with sturdy references, distributed garbage collection, three-party handoff, promise pipelining, and store-and-forward.
+ *Effect VM execution* that batches per-turn effects into a single STARK over a real BabyBear AIR. The circuit is migrating from hand-written constraints to a single descriptor-driven AIR *emitted from the verified Lean executor* (see @sec-formal), so the trace is derived from --- not maintained beside --- the executor semantics.
+ *STARK-attested transitions* whose public inputs bind the canonical turn hash, the effects-hash chain, the actor nonce, and the previous-receipt hash, giving algebraic answers to forge-effects, reorder-effects, skip-effects, replay-nonce, stale-proof, and forge-effects-hash threats.
+ *Federated BFT consensus* over a blocklace DAG (Cordial Miners + Constitutional Consensus) attested by constant-size BLS threshold quorum certificates.
+ *Cross-cell algebraic binding* via canonical bilateral identifiers $"transfer_id"$, $"grant_id"$, $"intro_id"$ derivable by any third party from the bilateral effect's surface inputs plus `ACTOR_NONCE`.
+ *Programmable predicates*: a 29-variant `StateConstraint` vocabulary declared per-cell, unified with witness-attached predicates under a single `WitnessedPredicate` shape.
+ *Trustless intent matching* with real threshold-encrypted intent pool (Shamir over GF(256) + ChaCha20-Poly1305).
+ *Federation bypass via `peer_exchange`*: two sovereign cells can directly exchange signed (optionally STARK-attested) state transitions without ever touching consensus, then promote to federation order on reconnect.

The thesis under this shape: any security invariant maintained synchronously by a kernel can be maintained asynchronously by a proof system, trading latency for distribution. The "kernel" in Dragon's Egg is not a process or a service but a *constraint family*---the AIR plus the predicate registry plus the canonical-message signing discipline. That constraint family is the thing every party trusts; everything else is replaceable.

== Two codebases: `dregg2` (verified) and `dreggrs` (heritage)

Dragon's Egg exists as two coordinated artifacts. *`dregg2`* is a machine-checked Lean 4
development: the authoritative specification of the turn executor, the predicate vocabulary,
the verified-by-construction circuit emission, and the distributed-protocol and CapTP
guarantees. *`dreggrs`* is the Rust heritage runtime: the network stack, the production
provers, the live node, the CLI, the extension, the Discord bot, and QUIC consensus. The
direction of travel is *`dregg2` first*: the runtime is being swapped onto the verified
executor on the commit path, and a Rust$arrow.l.r$Lean differential harness checks the two for
agreement. The ontology this paper quotes (56 effects, 29 constraints) is generated from the
Lean source and drift-guarded, so the specification and the prose cannot silently diverge.
@sec-formal is the substance of the verification story.

== Two visions, one runtime

The codebase carries two coexisting visions, both honest. Since the May draft, the boundary
between them has moved: the distributed-semantics guarantees that "Silver" once delegated to
the executor's say-so are now *machine-checked theorems* in `dregg2` (@sec-formal) ---
blocklace $tau$ finality, strand integrity, CRDT-merge convergence, membership safety,
multi-cell entanglement, cell handoff, and the CapTP handoff/GC/settlement core. What remains
"Silver" is the integration-completeness of the heritage runtime; what is now stronger than
Silver is that the cross-cell laws are *proved*, not asserted.

The *Silver Vision* is the _integration-complete, pre-algebraic state_: every loop is closed, every primitive's caller actually calls it, but the single-cell algebra and the runtime's cross-cell glue are the executor's say-so where the Lean proofs do not yet reach. CapTP messages produce real Turns on the receiving cell's ledger; three-party handoff is constructible from the SDK; `FederationReceipt` is produced by the live node path, not just tests; `AttestedRoot` is bound to a blocklace `block_id` plus finality round; $"federation_id" = "BLAKE3"("committee_pubkeys" || "epoch")$ rather than a random 16-byte tag; the bridge `destination_federation` is enforced in AIR; apps run as pure userspace through `app-framework` with a real cclerk---no `[0u8; 64]` placeholder signatures, no `Authorization::Unchecked`, no app-specific `Effect` variants. Silver is what the runtime actually delivers today.

The *Golden Vision* is the _full distributed-semantics algebraic constraint_: a folded DAG of attestations where Bob's cap exercise depends causally on Alice's grant, which depended on Carol's introduction (different cells' chains), and the whole mesh up to "now" is provable as one statement. Today's per-cell receipt chain linearizes one cell's history; Stage 7-$gamma$.2 Phase 1 compresses one turn's bilateral view; the full Golden Vision is folded mesh. Phase 2 of $gamma$.2 introduces a joint aggregation AIR built atop a generalized `plonky3_recursion_impl` substrate (Lane Golden-Edge Block 1 lifts it past the `P3MerklePoseidon2Air` placeholder); Kimchi/Pickles is a credible production-grade outer recursive layer as an alternative path.

The handoff between the two visions is structural: Silver produces real `WitnessedReceipt` chains whose scope-1 mode ships proof + public inputs and scope-2 mode optionally ships an inline witness bundle for replay-everything verification; Golden folds those chains into one statement.

== Contributions

Dragon's Egg's contributions span six architectural layers:

*Authorization and Privacy:* (1) proving monotonic attenuation of a bearer token chain in zero knowledge; (2) a distributed CDT that replaces kernel enforcement with cryptographic proof; (3) multi-modal authorization (`Signature`, `Proof`, `Breadstuff`, `Bearer`, `CapTpDelivered`, and the new `Authorization::Custom { predicate: WitnessedPredicate }` for app-defined modes); (4) a 29-variant `StateConstraint` predicate vocabulary unified with witness-attached predicates under `WitnessedPredicate` with kind registry (`Dfa`, `Temporal`, `MerkleMembership`, `BlindedMembership`, `BridgePredicate`, `PedersenEquality`, `Custom { vk_hash }`); (5) a 14-boundary vocabulary (BOUNDARIES.md) for cleartext-inside / commitment-inside / acceptance-inside / out-of-band populations.

*Distributed Object Runtime:* (6) E-style messaging semantics (promise pipelining, three-party introduction, sealer/unsealer) integrated with proof-carrying state; (7) `Authorization::CapTpDelivered` makes CapTP-delivered messages produce algebraically-bound Turns on the receiving ledger; (8) sovereign cells on a sovereignty spectrum with $"federation_id" = "BLAKE3"("committee_pubkeys" || "epoch")$; (9) EROS-style factories with computable child verification keys; (10) federation-bypass `peer_exchange` for direct sovereign-cell-to-sovereign-cell signed (optionally STARK-attested) state transitions.

*Unified Fabric:* (11) one canonical `Federation` type subsumes the four prior disjoint concepts; (12) `AttestedRoot` v3 binds $"federation_id"$ plus blocklace `block_id` plus finality round; (13) `KnownFederations` registry persisted at `<data-dir>/known_federations/<federation_id>.json` with `register-federation` CLI; (14) DFA routing as a first-class userspace primitive with `RouteTarget::Userspace { kind, payload }` dispatch and governance-bound atomic table swaps; (15) interest-based dissemination with subscription-filtered block propagation.

*Proof System:* (16) a backend-agnostic constraint DSL compiling to 8 targets from a single source; (17) a verified-by-construction Effect VM AIR *emitted from the verified Lean executor* (the ONE-circuit migration, @sec-formal), gated by a descriptor-vs-hand-AIR differential harness; (18) Stage 7-$gamma$.0 shared-PI bundle joining per-cell proofs of one turn; (19) Stage 7-$gamma$.2 Phase 1 bilateral cross-cell binding with off-AIR `dregg-verifier bilateral-pair` subcommand; (20) generalized `plonky3_recursion_impl` substrate lifted past `P3MerklePoseidon2Air` as the recursive verifier AIR; (21) Kimchi/Pickles as a credible production-grade alternative outer recursive layer.

*Trustless Coordination:* (22) trustless intent engine wired into production (`node::state::trustless_intent_engine`) using real Shamir-over-GF(256) + ChaCha20-Poly1305 threshold decryption from `federation::threshold_decrypt`; (23) bond escrow with predicate-attested matching; (24) bridge with destination-federation algebraic binding in AIR (closes T6); (25) executor delegation spectrum from full sovereignty to delegated execution with challenge protocols.

*Userspace + Storage:* (26) AppCipherclerk---a narrow six-method handle---plus EmbeddedExecutor and StarbridgeAppContext let apps run as pure userspace; (27) storage primitives become cell-program patterns: CapInbox is a monotonic-sequence WriteOnce-slot composition with `SenderAuthorized`; ProgrammableQueue lifts the legacy `QueueConstraint` vocabulary directly into `StateConstraint`; PubSubTopic, BlindedQueue, and RelayOperator follow the same pattern; (28) `FactoryDescriptor` + slot caveats + DSL = constructor transparency for every primitive.

*Threat Model + Soundness Ledger:* (29) the executor-honesty audit (T1--T15) is a living artifact tracking which threats are closed at AIR level, which at canonical-message signing, which at verifier replay; T1/T3/T15 closed at single-cell + $gamma$.2 multi-cell; T5 closed at AIR via Stage 7-$gamma$.0; T6 closed by `federation_id` algebraic binding; T8 and T11 closed by verifier PI completeness; T9 (sovereign-witness teeth) Phase 1 designed (Lane Hardening).

== Lineage

The design draws from Mina Protocol's execution model (cells as zkApp accounts, turns as ZkappCommands, call forests), E's distributed object semantics (eventual sends, three-party handoff, sealer/unsealer pairs), seL4's capability derivation (recast as a proof structure for asynchronous distributed systems), EROS's factory pattern (constrained constructors with auditable verification keys), Stingray's bounded counters for BFT budget channels, the Blocklace's DAG-based ordering generalized via Cordial Miners and Constitutional Consensus, and the macaroon/biscuit lineage of caveat predicates (now widened into the `StateConstraint` vocabulary and unified with witness-attached predicates as `WitnessedPredicate`).
