# HANDOFF — fhEgg protocol + Lean-game swarm results (Codex, 2026-07-18—19)

This is an implementation handoff, not a feasibility estimate.  It records what the
swarm changed in the shared working tree, the narrow gates that actually ran, and the
remaining security boundaries.  Verify at HEAD before quoting it: other lanes are active
in this repository and generated artifacts can move underneath a long-lived note.

## 0. Claude re-entry: the current shape in one page

This file is cumulative.  Sections 1–16 record the first swarm wave; sections 17 onward are the
07-19 continuation and should be read before planning new work.

The system is no longer best understood as “FHE plus one private auction.”  Four reusable organs
now meet at the game engine:

1. **Confidential decision/optimization relations, authored in Lean.**  Dark Bazaar clearing,
   private preference aggregation, exact portfolio-QP certification, private raid assignment, and
   private shuffle/fairness are fixed relations with Lean-emitted descriptors and HidingFri runtime
   paths.  HidingFri is Tier 1: proof consumers do not learn the witness, but the trace-building
   process does.  No-single-viewer production remains the separate FHE/MPC/distributed-prover lane.
2. **Exact state/enactment.**  Cells, exact factory-installed `CellProgram`s and canonical-v2 VKs,
   capabilities, predicates, receipts, and the recursive history fold bind a verified result to a
   state transition.  Complex/private mechanics are custom-VK leaves; simple public local checks
   remain predicate teeth.
3. **Policy authoring and semantic audit.**  The registered `Crypto/Deriv` tower now decides and
   *runs* unbounded emptiness and language equivalence for the symbolic `PredRE` fragment over the
   infinite `Value` alphabet.  `SymbolicMintermsPlus` covers enum membership, policy lists, and
   scoped owner-match; `PredicateLibrary` is the usable surface.  A separate Fable lane is widening
   scalar atom covers.  Do not repeat the older docs' claims that equivalence/fixpoint are absent;
   supersession notices were added to those audits.
4. **Derivation/rewrite attestations.**  `Crypto.Chain.Cert R` is the generic locally-checkable
   reduction certificate.  DFA, VPA, CFG, pushdown replay, hypergraph replacement, and genuine
   match-driven graph rewriting all instantiate it.  `Crypto.GraphRewrite` already proves the
   match/delete/glue semantics in Lean.  The general hiding graph-rewrite circuit/runtime is the
   newly active devnet campaign; only the Dyck/CFG instance currently has a deployed end-to-end
   parse AIR.

The load-bearing runtime boundary at this handoff is the custom-leaf VK carrier: a direct IR2 leaf
can now validate the exact canonical-v2 recipe and expose all eight faithful VK limbs, but the
shared RotationV3 leg still publishes only the low four.  The direct chain therefore refuses
closed.  Widening the leg to VK8, regenerating its descriptors, and connecting all eight limbs is
required before new private/rewrite leaves honestly fold into turn histories.

Do not add conventional calendar or staffing estimates to this handoff.  The executable board is
in §21; narrow gates and exact refusal boundaries are the unit of progress.

## 1. Output crossing: balanced, reveal-minimal at the recorded-transcript boundary

`fhegg-fhe/src/mpc.rs` now computes the exact uniform-price rule as:

1. secret-shared `min(D[p], S[p])` for every bucket;
2. a balanced oblivious argmax tournament;
3. left/lower-index wins equality, including through odd carries;
4. only `(p*, V*)` is opened.

The modeled online depth is
`(max(b,2) + 1) * (1 + ceil(log2 K))`: 119 rounds for `(b=16,K=64)` and
153 for `K=256`.  The exact Beaver-AND count is
`K*4b + (K-1)*(4b+ceil(log2 K))` (8,506 / 34,744 for those shapes).
Tests cover power and non-power `K`, ties, odd carries, `K=1`, and the old
largest-crossing counterexample.

`Transcript::is_reveal_only(k,b)` now validates the complete recorded schema, not
only the width of `p*`: exact `p*` and `V*` widths, exactly two masked openings per
AND, and canonical bits throughout.  Appending an unmasked output, an extra masked
opening, or a non-bit turns the tooth red.  This is a simulator for the public
one-process transcript; it is not a corrupted-party/network UC theorem.

Narrow gate: `mpc::pure_tests` — 7/7 PASS.

## 2. Smudging: the scalar theorem is now an explicit transcript ledger

`metatheory/Bfv/Smudging.lean` now carries the deployed scalar epsilon, transcript
coordinate count, session count, a `TranscriptHybridLedger`, and the corresponding
union/hybrid bound.  Exact pins include:

- 4,096 coefficients × 16 ciphertexts × one session = `2^-32`;
- 256 sessions = `2^-24`;
- 65,536 sessions = `2^-16`;
- `2^32` sessions exhaust the bound at 1; beyond that it is no longer useful.

This does not invent the adaptive/RLWE bridge.  It makes the existing conditional
assumption and its composition budget explicit.

Gates: `lake env lean Bfv/Smudging.lean` and `lake build Bfv.Smudging`; 27 pinned
keystones kernel-clean.

## 3. BFV key custody: party-owned n-of-n, no conveniently assembled secret key

`fhegg-fhe/src/threshold.rs` now exposes a production-shaped honest-party API:

- public `KeygenSession` / CRP seed;
- opaque, non-`Clone`, non-`Debug` `ThresholdParty` custody;
- public-key contributions aggregated by `KeygenCoordinator` without collecting
  secret shares;
- strict public-key/decrypt-share framing;
- duplicate, session/CRP, parameter, malformed-residue, incomplete-quorum, and
  smudging-floor/ceiling refusals;
- byte-equality against fhe.rs's native mbfv public-key aggregation and a native
  decrypt oracle.

The old helper that assembles all key shares is test-only.  Channel integration
puts each party in its own thread, refuses `n-1`, and combines only the full framed
quorum.

Narrow gates: threshold unit 9/9; `threshold_party_isolation` 1/1;
`threshold_no_viewer` 2/2; private-derivative integration 1/1.

Honest residuals: this is `n-of-n`, not `t-of-n`; messages are not authenticated;
malicious-share validity, replay/crash recovery, and a zeroized persistent secret
store remain unbuilt.

## 4. Masked BFV → MPC boundary: the two halves now actually compose

`fhegg-fhe/src/boundary.rs` now has `MaskedDecryptSession`, party-retained
`MaskedBoundaryParty` masks, strict `EncryptedMaskContribution` framing,
`MaskedDecryptCoordinator`, and `ThresholdMaskedCiphertext::open_framed`.
The process-shaped path is:

`ct` → each party adds public `Enc(r_i)` → parties smudged-decrypt the exact masked
`ct'` → only `y = m + Σr_i mod t` opens → each party locally derives its mod-t row.

The coordinator never receives a plaintext mask or a threshold secret share.
`open_framed` is now bound to the exact masked ciphertext owned by the session.  This
was a real review finding: equality among submitted shares alone allowed a valid full
quorum for another ciphertext.  The gate now rejects both a mixed share and a
self-consistent wrong-target quorum before accepting the honest quorum.

Narrow gate: `threshold_masked_boundary_channels` — 1/1 PASS (5.7s test).

That arithmetic ingress is now implemented at party-thread scope in
`fhegg-fhe/src/mpc_party.rs`.  Each `PartyArithmeticInput` constructor sees only one
party's locally derived demand/supply rows, XOR-shares every bit directly to the peer
endpoints, and the parties perform a balanced source-adder tree followed by `n-1`
oblivious conditional reductions modulo `t`.  The coordinator has no peer-input
endpoint; the trusted triple dealer accepts public session shape only and cannot name
an input row or aggregate curve.  The unchanged balanced crossing then reconstructs
only `(p*,V*)`.

The exact transcript ledger includes the A2B/mod-`t` gates, actual scalar Beaver
opening rounds, and the smaller batched dependency depth
`ceil(log2 n)*(w-1) + (n-1)*(w+1) + crossing_rounds(K,b)`, where
`w = bit_length(n*(t-1))`.  Tests cover `K=1,3,5,7,8,9`, ties and odd carries,
strict transcript mutations, cross-session refusal, and `n-1` input withholding.
The real `MaskedBoundaryParty` integration now feeds its derived rows through this
runtime and returns `(Some(2),65535)`.

Narrow gates: party MPC 3/3 PASS (0.219s); composed masked boundary → party MPC
1/1 PASS (4.956s).

Remaining deployment seams are authenticated isolated-process transport,
roster/replay binding, malicious input/share validity, dealer-free or auditable
triple preprocessing, crash recovery, and `t<n` custody.  They are no longer a
clear-curve ingress seam.

`metatheory/Market/MpcClearingSecurity.lean` now models this same volume-argmax
object rather than an obsolete balance-threshold/sign-vector protocol. `MpcView`
contains only `(p*,V*)` plus public shape; the joined theorem proves conservation,
uniform-price optimality, volume maximality for every bucket, and exact reveal-only
simulation on that same clearing. RED teeth show the old balance crossing disagrees,
the old sign vector is not determined by actual leakage, and a private demand cell
cannot be simulated. The masked-boundary/A2B bridge is stated over `ZMod` with the
actual bounded-bit premises. Direct Lean gate: 17 keystones kernel-clean.

## 5. First retained resident-GPU consumer

`fhegg-fhe/src/additive.rs` now has the first real consumer of
`gpu_arena::FoldEngine`:

`KeygenCoordinator/CollectivePublicKey` → unary order-row SIMD encryption → the
required strict fhe.rs-wire parse → retained demand/supply `FoldEngine` → encrypted
`LeanCiphertext` curves → the masked threshold boundary above.

`CollectiveOrderFoldEngine` reports the actual backend, adapter capacity, resident
plan, and timings.  CPU-no-arena and GPU-unsupported-shape fallbacks are labelled;
wrap refusal stays fail-closed.  There is no joint secret key.

Focused integration: 1/1 PASS (4.15s).  On the M2 run it used the resident GPU for
both three-row sides: one upload and no reduction round per side; demand fold 8.74ms,
supply 3.71ms.  The unavoidable representation ingress was measured separately
(33.7ms total for six rows).  Exact CPU bytes and the plaintext recovered only
through the masked threshold boundary matched.

Honest transfer boundary: fhe.rs keeps coefficient rows private, so each submitted
ciphertext currently pays one serialize + strict parse; each side then pays one
host→GPU upload and one folded-ciphertext readback because the boundary consumes a
host `LeanCiphertext`.  No ct×ct or whole-solver residency claim is made.

## 6. Cert-F: field acceptance now implies integer admission for both registered wires

`metatheory/Market/CertFDescriptor.lean` first made the missing field→integer boundary
explicit (`IntegerCertF`, `IntegerWellFormed`, `IntegerAdmission`) and proved exact
incidence/objective/gap bridges plus concrete wrap countermodels.  The descriptor now
enforces the sufficient ranges rather than accepting them from callers:

- every dual potential has a fresh 28-bit range gadget;
- ring3 retains 28-bit flow/slack policy;
- market4 reuses its existing bit bands with tight 21-bit flow and 19-bit slack
  recomposition gates;
- `ring3Prog_integerAdmission` and `market4Prog_integerAdmission` are unconditional
  consequences of canonical descriptor satisfaction.

This intentionally changes the registered wire shapes: ring3 is width 465 / 482
constraints; market4 is width 581 / 602 constraints.  The Lean goldens and checked-in
descriptor JSON were regenerated.  Rust base-trace construction fills the new
potential band and tests pin the exact shape, the old common-π-shift attack, and both
market-specific tight guards.

The new artifact hashes are:

- ring3: `8f104012760b24ccda1065ed4b559a0c9c10188acd5523298bfb77a5095ab0cc`;
- market4: `15d421d24c725da84f2c67061a171a9b4f5c37323f94b662cec590974e2e1520`.

Old proofs/VKs for these descriptors are intentionally incompatible with the new bytes.

Gates: `lake env lean Market/CertFDescriptor.lean` green; 34 keystones and all 85
namespace theorems kernel-clean.  Runtime teeth 4/4 PASS:
`registered_descriptors_carry_integer_admission_policy`,
`air_rejects_unranged_potential_shift`,
`market4_tight_flow_and_slack_gates_bite`, and `air_accepts_valid_ring3`.
A redundant full-STARK rerun was deliberately not used as a per-edit tax.

The theorem is still for the registered circulation-LP certificate.  It does not
turn arbitrary complementarity/bundle auctions into integral programs, and it does
not discharge the FRI soundness floor.

The Cert-F proof path now has an actual hiding batch-STARK entry point rather than a
comment that overclaimed the plain PCS.  `prove_cert_f_zk` / `verify_cert_f_zk` run
the identical Lean-emitted IR-v2 descriptor through the repository's OS-seeded
`DreggZkStarkConfig` (`HidingFriPcs`); the compatibility `prove_cert_f` path is now
explicitly documented as non-hiding.  The focused ring3 tooth mints and verifies a
real hiding proof, asserts the random-polynomial commitment and per-instance random
openings are present, and refuses changing the public volume from 3 to 4.

Narrow gate: `hiding_stark_proves_and_binds_public_volume_ring3` — 1/1 PASS
(0.056s test body).  This builds the hiding PCS construction for registered Cert-F
programs.  A formal simulator theorem for the complete batch-STARK transcript remains
separate, as does Tier-0 distributed proving/source binding where no one prover sees
the clear orders.

The Dark Bazaar caller is now a real Cargo surface rather than an untracked file Cargo
never compiled. `dreggnet-market` exposes `certified_clearing` behind the opt-in
`certified-clearing` feature and declares the heavy prover/solver dependencies only on
that feature. Its `try_prove_stark` entry point uses the hiding Cert-F prover. An
independent minimal-crate gate compiled the exact module and drove a real three-bid
book through deterministic clearing, a valid tight certificate, and the named
unregistered-program refusal.

That refusal is the honest current boundary, not success disguised as wiring: the
auction certificate is a dynamic 2-node program whose public `w` coefficients are the
bid values, while the registered descriptors are ring3 and market4. Per-book public
descriptor specialization would reveal the bids. A fixed relation that binds private
order commitments/coefficients—or a distributed integrity proof over the party MPC—is
required before the Bazaar can mint a Tier-0 proof.

## 7. Private derivative path

`fhegg-fhe/tests/e2e_private_derivative.rs` is no longer an ignored placeholder.
It builds a real fhIR program, demonstrates the active `[-15,15]` prox refusal,
runs the certified identity sibling over `[-100,100]` for six encrypted affine
steps, encrypts under the collective key, refuses `n-1`, and decrypts only through
the full smudged quorum.  All 4,096 slots match the exact scaled result
`(1536,-1536)` at scale `3^6=729`.

This is an honest correctness/integration tooth, not a transcript-security theorem.

## 8. Lean-native game braid

The game work stayed Lean-first rather than extending the Rust AIR archaeology.

**Descent.** `Dregg2/Games/DungeonCompleteness.lean` generalizes key exhibition to
every deployed keyed way 2–4 and proves a key-mutation refusal.  More importantly,
the attempted universal completeness theorem found a real abstraction mismatch:
`Dungeon.Inv` permits a relic at another relic's home floor, while the authored
program's provenance tooth is per-relic.  `wrongHomeState` is model-invariant and
model-legal for `delve` but program-refused.  The exact repair is
`ModelProgramInv := Inv ∧ CustodyHomeWF`; it holds at genesis and is preserved by
step, replay, and reachability.  `modelProgram_delve_admitted` is the first positive
method theorem and includes exactly the depth/spent riders. The completed method suite
proves unlock (selected way 2/3/4 + spent), smite (spent), loot (spent), and flee
(fate + spent, with bank constraints exactly when its slot changes). Universal
`modelProgram_step_admitted` dispatches every legal `Move`, and
`reachable_step_admitted` lifts it to reachable states. Direct Lean check is green;
all seven capstones are individually axiom-clean and the exact forbidden-token scan
is empty.

**Automatafl Leg S.** Three new Lean-authored modules now define, refine, and join a
fixed 11×11 sealed-reveal leaf:

- `AutomataflRevealEmit`: 105 columns, 41 PIs, 115 constraints; coordinates are
  degree-2 range-constrained, flattened in-circuit, and served through Poseidon2;
- `AutomataflRevealRefine`: SAT implies both exact public openings and all nine
  old-board packed felts; a changed opening with the same commitment unconditionally
  extracts a concrete arity-4 collision;
- `AutomataflRevealJoin`: PI `[39,41)` is a constrained commit-pair slice matching
  the deployed `AppRootBinding` shape, and the join theorem binds it to the preceding
  commitment fields given the real weld/preservation carriers.

No descriptor or caller is registered.  The refusal boundary is proved and named:
the live game stores a truncated ~63-bit BLAKE3 seal while Leg S has one ~31-bit
BabyBear Poseidon lane; the current flat-field weld loses high host bits; one-felt
generic birthday scale is only about `2^15.5`; the live board is 5×5 rather than
11×11; and the nine-felt heap board pack does not fit the eight flat-field lanes.
An attempted one-felt live cutover was reverted rather than weakening the playable
game.  Emit, Refine, and Join each pass their direct Lean check and axiom gates.

`Dregg2/Games/AutomataflBraid.lean` now performs that all-Lean composition through
resolved board, automaton step, and winner. It proves functional staged outcome and
Leg-S-selected outcome, unconditional swap-to-collision extraction, no-spurious
winner, and proof-native commitment/old-pack joins; executable winning and non-winning
traces are green. The deployment mismatches remain theorems rather than prose: current
live `n=5` cannot be the `n=11` Leg-S relation, and the closed R/A `n=2` carrier cannot
be the `n=11` board. Direct Lean check, 14 axiom gates, and three executable guards are
green with no forbidden proof tokens.

## 9. Exact Dark Bazaar attestation contract

`metatheory/Market/DarkBazaarAttestation.lean` now states and proves the strongest
honest end-to-end join rather than letting four proof objects sit adjacent in prose:

`committed (OrderBook,K)` → exact volume-argmax output → fixed registered market4
Cert-F statement → exact settlement receipt.

The join carries an explicit injective source-to-Cert-F compiler, proves
`honest_end_to_end_join`, `no_spurious_settlement`, and `end_to_end_binding`, and uses
the actual market4 deployed emit-soundness bridge. The RED
`output_only_attestation_does_not_bind_source` exhibits two distinct books whose
actual outputs are both `(1,8)`, so a receipt containing only `(p*,V*)` cannot identify
which source book was cleared.

Tier 1 and Tier 0 are separated in the type-level contract. The Tier-1 world simulator
coexists with an explicit theorem that the solver receives the plaintext book. The
Tier-0 residual requires both public-view simulation and source extraction from every
accepting distributed proof; identical public views over different solver books are a
separation tooth. The compiler and Tier-0 carrier are specified, not fictionalized as
installed. Direct Lean gate: 12 keystones kernel-clean, forbidden-token scan empty.

`fhegg-fhe/src/attestation.rs` implements the matching canonical runtime envelope.
It domain-separates and length-prefixes SHA-256 bindings for protocol/session, exact
ordered roster and input ciphertext/commitment digests, BFV degree/moduli/plaintext
modulus/CRP/collective-key identity, public `(K,b,t)` rule shape, strict distributed
transcript, output-bit consistency, and `(p*,V*)`. Verification reconstructs those
objects independently and a stateful guard rejects replay.

The API refuses to equate that binding with malicious computation integrity.
`BindingOnly(OutputOnlySelfAssertion)` can pass structural binding but can never pass
`verify_full`; full verification requires a relying-party-supplied external verifier
over the exact claim digest. Mutation, roster/input reorder, wrong BFV identity,
transcript/output mismatch, binding-only promotion, bad evidence, and replay teeth are
green. Narrow gate: `attested_clearing_receipt` 3/3 PASS (0.015s).

The envelope now also has a concrete `AuthenticatedQuorumVerifier`: an exact ordered Ed25519 roster,
threshold, and verifier identity derived from roster+threshold; signatures are over the canonical claim,
signers must be strictly ordered and unique, and an unknown, duplicate, missing, reordered, or invalid signer
refuses. `dreggnet-market`'s opt-in `authenticated-clearing` feature canonicalizes the complete
`CertifiedClearing`, requires its digest exactly once inside the FHE claim, checks the output crossing, and
replays the full verification. This is a real authenticated co-endorsement weld. Its negative test also pins
the boundary: old evidence fails after a ciphertext digest changes, but a quorum can sign a newly fabricated
combined claim. Therefore it proves exact attribution and agreement, not ciphertext-opening/source relation
or malicious MPC correctness.

## 10. The feasibility brief is now an implementation brief

The earlier brief was wrong, so `HANDOFF-FHEGG-FEASIBILITY-CODEX.md` was corrected
in place. It no longer tells an agent not to build or asks for sequential rough-cost,
calendar, or conventional staffing estimates. It now asks an adversarial swarm to
implement independent technical lanes in parallel and report executable exit gates.
The current concrete boundary is:

- balanced reveal-minimal public MPC transcript: built;
- scalar-to-transcript smudging ledger: built, conditional bridge explicit;
- party-owned n-of-n BFV keygen/decrypt: built at process-shaped honest-party scope;
- party-owned masked boundary composition: built at process-shaped scope;
- retained resident GPU fold under the collective key: built and measured;
- integer-sound registered Cert-F wires: built and enforced;
- hiding Cert-F batch-STARK for registered programs: built and exercised;
- authenticated/malicious distributed protocol, `t<n`, exact committed-volume
  argmax/source attestation, a complete ZK simulator theorem, and full FRI decode:
  still distinct frontiers.

Do not collapse those last items into one "threshold/networking" checkbox; they are
different security statements and need different teeth.

## 11. First fixed private-input Dark Bazaar relation

`metatheory/Market/DarkBazaarPrivateDescriptor.lean` authors a fixed `N<=4,K=4,qty<16` relation in Lean.
Orders and eight canonical blind felts are private witness data. The public statement is exactly
`(session, rule, order_root[8], p*, V*)`; the root is the full eight-lane output of an arity-16 Poseidon2
permutation over domain/session/rule/injective packed book/blindings/four framing zeros. The arity-16 detail
is load-bearing: the first arity-12 attempt passed a width check but the deployed chip selector replaced
input lanes and made a blinding mutation root-insensitive. The wide mutation tests found it before handoff.

The emitted descriptor recomputes book packing, demand/supply/volume, minimums, unique selection, global
maximum, and lowest-price tie break. `circuit-prove::dark_bazaar_private` exposes separate non-hiding and
`HidingFriPcs` proof APIs plus fresh OS-sampled canonical blindings. Private-order/session/blind mutations
change the root; public root/price/volume tampering refuses; two proofs have different random commitments.

Lean proves semantic checker soundness, packing injectivity, collision reduction, and extraction of all
emitted modular gates/root-chip/PI pins from actual `Satisfied2` against arbitrary external public inputs.
The named residual `DarkBazaarDescriptorToAccepts` is the final bounded modular-to-integer decode/no-wrap
lift from those gates to the semantic `Accepts` relation. This is Tier-1 shielding from proof consumers: the
process constructing the trace sees plaintext orders. It is not the Tier-0 no-single-viewer producer.

Narrow gates: Lean file/module and byte-emission parity green; degraded-felt AST gate green; focused Rust
proof tests 3/3 PASS, with the hiding/tamper test taking 0.347s after build.

## 12. fhIR/optimizer admission moved onto exact teeth

`metatheory/Market/FhIRClearingPlan.lean` is the first Lean-authoritative fhIR product family: a typed
two-coordinate rebalance plan, exact compiler, resource/leakage/no-wrap/noise proofs, canonical emitted JSON,
and a strict Rust decoder that refuses malformed or drifted bytes before dispatching the real solver. This is
one concrete family, not a claim that the legacy Rust compiler for every product was replaced.

For portfolio QPs, fhIR acceptance no longer follows the f64 diagnostic certificate. `solver_bridge` lifts
the certificate into the exact fixed-point checker and accepts only the exact verdict. `compile` now
canonicalizes at `10^-9`, checks all data/dimensions/finite values and the `2^53` lift envelope, and admits the
exact rounded matrix only with a symmetric nonnegative diagonally-dominant certificate. The same rounded
matrix reaches the backend; unsupported PSD matrices refuse closed; f64 LDL remains diagnostic. Focused fhir
gate: 46/46 PASS (0.221s).

A separate fixed full-shape `n=6,mc=7` CertQp descriptor now closes the concrete emitted bridge at `S=10^3`.
`portfolio_satisfied2_implies_checker` takes only canonical BabyBear cells plus actual byte-pinned
`Satisfied2 portfolioDescriptor` and returns every exact integer checker clause: primal feasibility,
stationarity, and the low/mid/high normal-cone/clamp cases. `portfolio_noWrap_of_satisfied` derives the complete
residual window internally from the emitted 24-bit tables, x10/y12 upper gates, BabyBear-prime selector
Booleanity, and the fixed `P/q/A/l/u` arithmetic; there is no caller-supplied no-wrap premise or trusted clause
flag. `portfolio_public_return_exact` pins the sole public value to exact `-q^T x`; `(x,y)` remain private.

The verifier also exact-compares the supplied descriptor with the committed Lean artifact, so descriptor drift
refuses. Direct Lean/axiom gates and regeneration `--check` are green. An actual fhIR compile/solve/lift run
mints and verifies a HidingFri proof, and changing the public return refuses. The production runner's `S=10^9`
still needs an honest multi-limb carry/comparator AIR rather than a silent scale claim.

## 13. The Dark Bazaar now has a real Descent-asset settlement seam

`LootVault::into_assets` hands another engine organ the exact live Descent note world. A settled Bazaar
session exposes the winning `DreggIdentity` and `settle_winning_asset` crosses an existing `AssetId` for the
verified winning `$DREGG` price through `dreggnet-trade`'s sealed-escrow atomic swap. The end-to-end test starts
with a real fair-drawn Descent boss drop, never re-mints it, and verifies the lineage after
`mint -> escrow -> winner`. An unfunded winner is refused and the item returns to the seller.

Narrow remote gate: 2/2 PASS in 0.053s after build. Honest residual: auction resolution and the asset/value
cross are two committed operations, not one indivisible multi-cell turn; the dedicated live Descent frontend
does not yet feed its durable player world into the catalog Bazaar session.

## 14. Factory birth now installs the exact full program and canonical v2 VK

The sealed-auction factory previously advertised a method-dispatched `CellProgram::Cases` but factory birth
installed only a flattened `Predicate(state_constraints)`. That was a real semantic weakening: the born cell
did not necessarily execute the program whose identity the app claimed.

`ChildVkStrategy::FixedProgram` now carries the exact executable `CellProgram` together with the AIR,
verifier-implementation, and proving-system components of the canonical v2 verification-key recipe. Strategy
hashing and child validation bind all four components; executor birth installs that exact program and derives
the exact same v2 VK; node seed construction follows the same recipe. The enum variant was appended and its
postcard round-trip is pinned so existing discriminants do not move.

The sealed-auction factory now uses the full program, including constructor dispatch and the exact phase
`AllowedTransitions` floor. Integration checks program and VK identity after birth and throughout commit,
close, reveal, and resolve. Legacy-v1/wrong-VK birth, wrong verifier/proving-system components, phase rewinds,
phase skips, and overwrites refuse without leaving ghost cells.

Remote gates: `dregg-cell` 788/788 PASS (one skipped); sealed-auction factory integration 4/4 PASS;
sealed-auction library 29/29 PASS; `dregg-node --lib` compiles green.

## 15. Reusable private preference aggregation is a Lean-emitted proof organ

`Dregg2/Games/PrivatePreferenceDescriptor.lean` and `circuit-prove::private_preference` implement a fixed
`N=4,K=4` score ballot for party forks, guild votes, matchmaking selection, and quest choices. Every private
participant scores each option in `0..3`; the public statement is only
`(session, rule, ballot_root8, winner)`, with the lowest index winning a tie. Aggregate totals and winning score
remain private.

The sixteen scores are injectively packed into two 16-bit felts and committed with eight canonical blind felts
through one full-arity Poseidon2 permutation exposing all eight output lanes. Lean proves semantic checker
soundness, pack injectivity, distinct-opening collision reduction, actual `Satisfied2` gate/PI/root-chip
extraction, every binary-column decode, and exact two-bit score plus four-bit difference/slack recomposition.
`privatePreferenceN4K4_descriptor_to_accepts` now closes the whole functional bridge: actual `Satisfied2`,
canonical trace cells and canonical external PI representatives, plus the wide Poseidon chip-table theorem,
imply semantic `Accepts` for the decoded witness. Total/pack/select/max/root identification is no longer a
residual.

Rust provides strict validation, fresh CSPRNG blindings, explicit hiding/non-hiding proof APIs, and
`verify_decision_zk -> VerifiedDecision`, so a lightweight game crate can consume a verified winner without
depending on the proving stack. Tier 1 remains explicit: the trace-building process sees all ballots; a
threshold-FHE/MPC or distributed producer is required for a house-blind ballot service.

Gates: 19 Lean keystones kernel-clean; fresh emission byte-identical at SHA-256
`e7e2c7dbf4d34b104f2478b4c745a399936b5b127afa4f8b793e9ef177cc902d`; faithful-commitment scan green;
focused Rust 3/3 PASS (hiding test 0.204s after build).

## 16. Private N=8 shuffle/deal proves exact permutation and selective openings

`Dregg2/Games/PrivateShuffleDescriptor.lean` and `circuit-prove::private_shuffle` implement a fixed eight-seat
private deal. The public statement is only `(session, rule, deal_root8)`. Each seat's hidden card and eight
independent canonical blind felts enter a full-arity-16 Poseidon2 leaf; eight leaf digests fold through seven
full-width `node8` compressions. A recipient can receive only its card, leaf blind, and depth-three sibling path
and reconstruct all eight public root lanes without learning another card.

The descriptor carries an 8x8 one-hot matrix. Row-one and column-one gates plus card recomposition prove the
assignment is a bijection of canonical cards `0..7`: no duplicate and no omission. The Lean author has 258
columns, 10 PIs, 15 full-width chip lookups, and 89 exact-permutation gates; all seven named keystones are
kernel-clean. Rust exposes only the HidingFri proof API for this privacy-facing family. Opening membership and
the exact-permutation proof are deliberately separate checks and must verify against the same public statement.

The security boundary is formal, not prose: `coordinator_choice_bias_residual` exhibits two distinct valid
permutations. This organ proves shuffle correctness, not unbiased sampling. Joint entropy, a threshold MPC
shuffle, or a verifiable mix/re-encryption layer remains required before claiming that no coordinator chose the
deal.

The emitted artifact re-emits byte-exact at SHA-256
`6c1e390a0a86bf6778e62e7541a6053240207dddad6acafba457a282c9f0c539`. Five narrow tests pass: host shape and
permutation refusal, root binding, duplicate AIR rejection, selective-opening tamper refusal, and HidingFri
proof/public-statement tamper refusal.

## 17. Private preference now has a cell-bound direct-IR2 carrier, fail-closed at the exact VK boundary

`Dregg2/Games/PrivatePreferenceCellDescriptor.lean`,
`circuit-prove/src/private_preference_cell.rs`, and `turn/src/private_preference_custom.rs` extend the
standalone preference proof into a real cell-transition statement.  Its 27 public inputs are

`[old_root8, new_root8, session, rule, ballot_root8, winner]`.

The winner is the app-root field selected by the cell transition; the descriptor is width 134 and
the emitted artifact is 53,430 bytes with SHA-256
`c1009a7bc63e3669b3754c07e60748dcb9faf3ea748f45a71cad3483ae6e9b44`.  Lean proves the cell relation
projects to the base private-preference relation and therefore to semantic `Accepts`; six keystones
are kernel-clean.

The direct `CustomIr2WitnessBundle` now retains the exact canonical-v2 recipe, validates the program
bytes by parsing them as the exact descriptor, and exposes all eight faithful VK limbs from the
anchored leaf.  This found the remaining correlation boundary: RotationV3 currently publishes the
full eight proof-commitment limbs but only four VK limbs at PI 54–57.  The direct arm refuses closed
rather than claiming a low-four comparison is exact.  Tests pin both a same-descriptor/wrong-full-VK8
case and a wrong VK whose low four limbs still match.

Gates: direct Lean 6 clean; remote `dregg-circuit-prove --lib` and `dregg-turn --features prover
--lib` checks green; three recipe/layout tests, one direct-VK tooth, and the canonical registry
configuration test all pass.  Logs are `/tmp/private-preference-cell-lean-fixed.log`,
`/tmp/private-preference-ir2-cargo-check.log`, `/tmp/private-preference-turn-check.log`,
`/tmp/private-preference-cell-fast-pbuild.log`, `/tmp/direct-ir2-correlation-pbuild.log`, and
`/tmp/private-preference-registry-fast.log`.

The active VK8 flag-day lane must widen RotationV3 to expose all eight limbs, shift the exact wrapped
PI layout, regenerate only the affected descriptors, and connect leg VK8 to leaf VK8.  Until that
gate is green, preference and future graph-rewrite leaves may prove standalone but must not be
described as honestly folded direct custom turns.

## 18. Private raid/matchmaking assignment: runtime real, formal optimizer bridge one bounded lemma away

`Dregg2/Games/PrivateRaidAssignmentDescriptor.lean` and
`circuit-prove/src/private_raid_assignment.rs` define a fixed four-seat/four-role optimizer.  The
private witness contains sixteen scores in `0..3`, sixteen independent admissibility bits, and eight
blind felts.  The public statement is only `(session, rule, input_root8, roles4)`.  A valid result is
an exact role permutation, every selected seat/role pair is admissible, the total score is globally
maximal over all 24 assignments, and the lowest assignment row wins an equal-score tie.

The descriptor has 299 columns, 14 public inputs, one full-arity-16 Poseidon2 lookup, and 701
constraints.  Artifact SHA-256:
`141aec3bbed421fc984200c97d158591f0792266d7e5fb71ffe2d7480ea7a869`.

Lean is green with 16 kernel-clean keystones.  It already extracts exact integer
score/admissibility/select/total/difference bits from actual `Satisfied2`, proves every
recomposition, obtains a genuine decoded permutation, identifies the chosen total, and closes the
candidate-chosen/candidate-allowed products without a caller-supplied no-wrap premise.  The exact
remaining bridge is narrow but semantic: map an arbitrary feasible assignment to its `Fin 24` row;
use that row's allowed/dominance certificate to prove its score is at most the selected score; then
use row order plus the lex gate to rule out an equal-score earlier row.  That packages
`Satisfied2 -> OptimalLex -> Accepts`.

The isolated Rust surface already mints and verifies a real HidingFri proof and returns
`VerifiedAssignment`.  Six remote tests pass in 0.169s, including an admissible-but-suboptimal row,
an equal-score lex-later row, faithful root binding, score-zero distinct from inadmissible, and
public-statement tampering.  The descriptor remains intentionally unregistered until the final
`OptimalLex` bridge closes.  `docs/deos/PRIVATE-RAID-ASSIGNMENT-N4K4.md` is its focused ABI/security
record.

The intended engine weld keeps the optimizer ABI small.  A surrounding protocol envelope binds the
audited eligibility-policy artifact/certificate, the private admissibility proof, the optimizer's
`input_root8`, and its exact rule/VK.  A verified result then grants the existing `dreggnet-party`
role capabilities atomically; it should not lossy-fold a policy digest into one BabyBear `session`
felt.

## 19. Joint-entropy N=8 fair shuffle: exact unbiased accepted rank, temporal anti-abort still external

`Dregg2/Games/PrivateShuffleFairDescriptor.lean`, `EmitPrivateShuffleFair.lean`,
`circuit-prove/src/private_shuffle_fair.rs`, and `private_shuffle_fair_zk.rs` add the missing
sampling organ above §16's permutation checker.  Eight private 16-bit contributions add modulo
`2^16`; an attempt is accepted only when the entropy lies below 40,320.  Accepted entropy is used
directly as a permutation rank—never reduced with `% 40320`—so no modulo bias is introduced.

Lean proves exact equivalences
`AcceptedEntropy ≃ Fin 40320 ≃ Equiv.Perm (Fin 8)`, no duplicate/no omission, and that one honest
additive contribution is a bijection conditional on all fixed other contributions.  The public
statement is `(session, fair_rule, attempt, commitment_root8, accepted, deal_root8)`.  Seed
commitment leaves bind the participant, attempt, seed, and eight blindings; an accepted deal root is
byte-compatible with the existing private-shuffle framing, while a rejected attempt exposes a zero
deal root.

The descriptor has 823 columns, 20 public inputs, 1,026 constraints, and 30 full-width Poseidon2
lookups.  It enforces seed bits/recomposition, exact additive carry, accepted/rejected threshold
slacks, factorial/mixed-radix rank recurrence, the recursive `Perm.decomposeFin` selector, and final
row/column permutation gates.  Thirteen keystones are kernel-clean.  The artifact SHA-256 is
`43d010af24ffcd7cee9aa5af7e8d5e4919173411ba82c19c777606f7f66a3c52`; the faithful-commitment scan
passes.

Rust proves and verifies both accepted and rejected attempts through HidingFri.  Four remote tests
pass in 0.330s, including an exhaustive host enumeration of all 40,320 ranks, AIR rank/permutation
mutation, and seed/blind/attempt/root/acceptance tampering.

Two boundaries remain explicit.  First, the emitted `Satisfied2` facts still need their final
bounded modular-to-integer identification with the semantic seed/carry/threshold/factorial selectors
and both root trees.  Second, a static accepted/rejected relation does not prevent selective abort:
cell/receipt state must commit before reveals, increase `attempt` monotonically, record every
rejected or completed attempt, and give withholding/timeout a deterministic consequence.  Lean
already exhibits that an unrecorded restart can select a different accepted deal; do not market the
AIR alone as an anti-abort protocol.

## 20. Policy decisions and graph rewriting are complementary semantic-web attestation backends

The live `Crypto/Deriv` tower has moved materially beyond the older audit documents:

- `SymbolicEquivalence` assembles language equivalence from symmetric-difference emptiness;
- `SymbolicMinterms` generalizes the hard-coded delimiter witnesses to per-guard symbolic covers;
- `SymbolicFixpoint` consumes `simDecide` in an adaptive similarity-deduplicated worklist;
- `EquivalenceFixpoint` makes equivalence kernel-runnable on real examples;
- `SymbolicMintermsPlus` closes `symMemberOf`, semantics-preserving `allOf`/`anyOf` desugaring, and
  scoped correlated `digFieldEq` covers;
- `PredicateLibrary` exposes role/status/reference/owner and boolean policy combinators with actual
  satisfiable/contradictory/equivalent/not-equivalent examples.

This is the authoring/audit organ: “is my guild/quest/raid guard contradictory?” and “did this edit
change the accepted histories?”  It does not by itself hide the player's state.  For hidden state,
the exact audited policy identity and its VK bind a Hiding/FHE/MPC relation which reveals only the
authorized result.  Cells and receipts then make the result temporal and enforceable.

The rewrite side is more general than a word guard.  `Crypto.Chain` proves
`(exists c, Cert R start goal c) <-> ReflTransGen R start goal` for any relation.  DFA acceptance,
VPA acceptance, CFG production, pushdown replay, hyperedge replacement, and full graph rewriting
all reuse that substrate.  `Crypto.GraphRewrite` has genuine pattern homomorphisms/embeddings and a
match-driven DPO-style `RewriteStep`: select a licensed rule, instantiate its variables, preserve a
context, delete the matched LHS, and glue the RHS.  `graphRewrite_bridge` lifts chains of those steps
to semantic reduction.

Do not confuse the two hypergraph layers.  `Crypto.Hypergraph` is the rewrite-certificate carrier;
`Dregg2.Hyperedge` is the N-party atomic-turn apex.  The latter binds all legs to one turn id and one
aggregate conservation equation, and `Apps.SheafHyperedge` proves agreement gives distributed
knowledge while a fork has no shared apex.  Together they support the intended distributed
operation: privately prove a valid semantic rewrite, then enact its N-party resource/capability
effects atomically.

`Crypto.GraphRewriteHistory` now supplies the receipt/history bridge.  A certified step's public
ABI is `(session, rulesRoot, index, oldRoot, newRoot)` while its semantic graph openings and
`RewriteStep` proof remain witness-side.  Links require the same session/ruleset, an exact `+1`
index, and equal adjacent roots.  Under an explicit commitment-binding carrier,
`linked_reduces`/`linked_has_cert` recover a genuine semantic reduction and the common `Cert R`
form; without pretending hashes are injective, a same-root/different-graph splice extracts a
concrete commitment collision.  Wrong session, rules root, index, or public endpoint refuses.
The registered module has 11 kernel-clean keystones (`/tmp/graph-rewrite-history-lean.log`).

The exact deployment boundary is important.  The graph-rewrite semantics and generic certificate
bridge are formalized, but no general graph-rewrite descriptor/witness builder/Hiding prover is
registered.  The deployed parse circuit is the one-bracket Dyck/CFG instance.  The active devnet
lane is building a bounded generic one-step rewrite leaf with committed ruleset and graph roots,
private rule/match/substitution/context, faithful match/delete/glue constraints, Hiding proof, and
tamper teeth.  Adjacent old/new roots are the intended segment endpoints for arbitrary folded
rewrite histories.

## 21. Executable board after this handoff

These are active technical closures, not a sequential schedule:

1. **Graph-rewrite leaf:** land the bounded generic Lean relation/AIR, full
   `Satisfied2 -> semantic RewriteStep` bridge, exact emitted artifact, HidingFri witness/proof, and
   wrong-match/context/rule/root refusal teeth.  Keep it isolated until coherent.
2. **Faithful custom carrier:** widen RotationV3 from VK4 to VK8, regenerate the exact affected
   custom descriptors, and connect the leg's eight VK limbs to the anchored direct IR2 leaf.  An
   honest private-preference fold plus wrong-limb teeth is the first consumer gate; graph rewrite is
   the next.
3. **Private raid semantics:** close the `Fin 24` dominance/lex bridge, register the descriptor, then
   consume `VerifiedAssignment` in a party/raid enactment that grants exactly the proved role caps.
4. **Fair shuffle semantics and temporal protocol:** close the modular-to-semantic theorem, register
   the descriptor, then add the commit-before-reveal/monotone-attempt/timeout receipt cell.
5. **Rewrite history and N-party enactment:** the generic same-ruleset/contiguous-index/root-linked
   semantic history theorem is built.  Connect the new rewrite AIR's public endpoints to that
   receipt ABI, fold them to one history proof, and use the N-party `Hyperedge` apex for balanced
   cross-cell effects.
6. **Playable surfaces:** wrap the completed organs as Offerings.  The generic web/Telegram/Discord
   adapters can carry a correctly mounted offering, but the new private preference/raid/fair-shuffle
   and rewrite games are not mounted yet.  The local Dark Bazaar catalog/web/Telegram seams exist;
   the live `arcade.dregg.net` deployment has not been refreshed and must not be used as evidence
   that these new organs are publicly playable.

The reuse rule is: retain existing identity, eligibility, custody, asset, capability, cell, receipt,
history, and frontend shells; author a fresh Lean relation when the old mechanic leaks the wrong
information or proves the wrong semantics.  Rewriting the entire engine is not required, but
reusing a public-ballot or coordinator-chosen core merely because its shell exists is also not
acceptable.
