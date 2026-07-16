# Quantum-aware finality — the PQ story end to end

This document tells one story at current resolution: **what it takes to forge dregg finality, and
why a quantum adversary does not get a discount.** It walks the deployed Rust perimeter (every
consensus authority artifact is hybrid-signed), the Lean metatheory chain that stands under it
(floor → quantum adversary → primitive games → hybrid keystone → consensus safety → code
refinement), the adversarial tests that exercise exactly the attacks the design exists to stop, and
the named boundary — what "quantum-aware" means here, what the named FIPS hypothesis is, and which
seams remain open by name.

The primitive-by-primitive map (every scheme, every reduction, every floor caveat) is
[PQ-CRYPTO.md](PQ-CRYPTO.md); this document is the *finality-shaped* cut through it. The repo spine
is [OVERVIEW.md](OVERVIEW.md).

**"Quantum-aware" means three precise things — and not a fourth:**

1. **Hybrid, not PQ-only, at the perimeter.** Every signature that carries consensus authority is
   `ed25519 ∧ ML-DSA-65`, and a verifier accepts only when both halves verify. The halves are
   byte-bound to each other: finalization votes and strand blocks put both halves over one signing
   message, while the consensus finality block follows `Block::new`'s design — "the ed25519 half
   signs the compact `signing_content`; the post-quantum half signs the canonical `id()` (which
   already commits to the ed25519 signature)" (`blocklace/src/finality.rs:443`). Either way, an
   adversary must break discrete log AND module-lattice SIS/LWE simultaneously.
2. **The safety theorem survives a classical break.** Quantum-safe finality is proven under the
   *disjunctive* floor `SchnorrDLHard ∨ MSISHard`: a quantum adversary that breaks the discrete-log
   half (Shor) still faces Module-SIS, and no two conflicting blocks finalize.
3. **The adversary in the QROM step is a real quantum object.** Where the proofs touch the random
   oracle (the ML-KEM FO transform), the reprogramming bound is the One-Way-to-Hiding lemma, proved
   in Lean over a genuine model of a q-query quantum adversary — states in `EuclideanSpace ℂ B`,
   oracles as `LinearIsometryEquiv`s — not an opaque idealisation constant.

What it does **not** mean: "proven secure against quantum computers." The lattice floors are named
**assumptions** (believed quantum-hard; never discharged), the FIPS-primitive correctness is a named
**hypothesis** with partially-built discharge ladders, and the signature-side reductions are
classical game reductions whose *floors* are quantum-plausible — not QROM-internal forgery proofs.
All of this is spelled out in [the named boundary](#the-named-boundary) below.

---

## The perimeter — every consensus authority artifact is hybrid-signed

### Identity is a hybrid commitment

A consensus identity is not an ed25519 key. It is the 32-byte commitment
`H(ed25519_pk ‖ ml_dsa_pk)` — `dregg_types::hybrid_id_commitment` (`types/src/lib.rs:965`), a
BLAKE3 derive-key hash with length-prefixed, injective encoding. The enroll+pin check
`verify_committed_ml_dsa` (`types/src/lib.rs:984`) recomputes the commitment from the two presented
keys: an attacker who presents the honest ed25519 key with their *own* ML-DSA key produces a
different identity. **The id IS the enrollment** — the roster pin is cryptographic, not an
out-of-band binding.

The ML-DSA-65 key is **derived from the same 32-byte seed as the ed25519 identity**
(`MlDsaSigningKey::from_seed`, one shared leaf: `dregg-pq/`), so no participant manages a separate
PQ key and the enrolled PQ public key is a deterministic function of the classical identity. The
verifier never trusts a key carried inside a block — the PQ half is always pinned to the enrolled
roster key.

### Consensus blocks

The finality `Block` (`blocklace/src/finality.rs`) carries the full hybrid shape:

- `creator` (`finality.rs:140`) — the hybrid id. It is the identity label everything downstream
  keys on: roster, tips, equivocation bookkeeping, cohort counting, votes, gossip `NodeId`.
- `ed25519` (`finality.rs:147`) — the classical verify key, carried separately so it stays usable
  as a verify key while `creator` stays a commitment.
- `signature` + `pq_signature` (`finality.rs:156,173`) — the ed25519 half signs `signing_content`
  (domain tag ‖ creator ‖ seq ‖ payload hash ‖ predecessors; `Block::new`, `finality.rs:464`); the
  ML-DSA-65 half signs the canonical `id()`, the blake3 hash of that content *plus the ed25519
  signature* (`finality.rs:398`) — so the PQ half commits to the classical half rather than
  co-signing identical bytes. An empty PQ half is a fail-closed sentinel, never an "ed25519-only"
  block.

Verification is `Block::verify_hybrid` (`finality.rs:529`), and its order is the design:

1. **Commitment gate** — `creator` must recompute from the carried ed25519 key and the *enrolled*
   ML-DSA key (`verify_committed_ml_dsa`), before either signature is examined.
2. **Classical half** — real ed25519 verification against the carried key.
3. **PQ presence** — an absent ML-DSA half rejects (`BlockError::UnsignedPq`).
4. **PQ half, pinned** — ML-DSA-65 verification against the *enrolled* roster key, over the
   block's `id()` (which commits to the ed25519 signature, `finality.rs:554`), under the
   block-specific FIPS 204 context `BLOCK_PQ_CTX` (`blocklace/src/pq.rs:31` —
   distinct from the quorum context, so a block signature can never replay as a quorum signature).

The live wire ingests through `Blocklace::receive_block_pinned` (`finality.rs:836`): unenrolled
creator ⇒ `UnenrolledCreator`, fail-closed; enrolled ⇒ `verify_hybrid`. There is no classical-only
acceptance path on the wire. (`receive_block`, `finality.rs:810`, is ed25519-only **by design** —
local DAG reconstruction and equivocation bookkeeping, a named seam tested as such; see the
adversarial coverage below.)

The strand-integrity blocklace (`blocklace/src/lib.rs`) has the same law at its own perimeter:
hybrid `Block::sign`, enrolled-key pinning via `Blocklace::enroll_pq`, `BadPqSignature` on a
mismatched or foreign PQ half.

### Finalization votes

A `FinalizationVote` (`node/src/finalization_votes.rs:51`) carries an ed25519 signature and an
ML-DSA-65 `pq_signature` (`:75`) over the same signing message (which binds the attested
`merkle_root`, so a vote quorum is a restart-anchor for a specific finalized state).
`FinalizationVote::verify_hybrid` (`:151`) is `classical ∧ pq`; the `VoteCollector` (`:177`) counts
a vote toward quorum **only** when both halves verify, with the voter's ML-DSA key looked up from
its `pq_committee` roster — a quantum adversary that breaks ed25519 entirely still cannot forge
finality.

### The executor's participant projection

The verified finalizer identifies each wave's leader by matching the participant set against
`Block::creator` — so the participant set the executor projects consensus over is keyed by the
**same hybrid id**, mapped from admitted ed25519 members through the enrolled ML-DSA roster
(`node/src/blocklace_sync.rs:1013`). A member with no enrolled ML-DSA key is dropped from the
projection — fail-closed, consistent with the ingest pin, never an ed25519-only downgrade. This is
**surface-3** ("no live path keys identity by raw ed25519"), committed at this projection; the
verified finalization rule itself admits creators by hybrid id (`node/src/finality_gate.rs:198`),
so an attacker key that is not an enrolled hybrid participant is never interned at all.

---

## Adversarial coverage — testing the attack the hybrid id exists to stop

The redteam suites (`redteam/tests/blocklace_attacks.rs`, `blocklace_deep_attacks.rs`) drive the
adversary models against the hybrid identity, each asserting the *specific* rejection variant, not
just "it errs":

- **Self-fork** (equivocation) → `Equivocation { creator: hybrid_id, seq }`.
- **Cross-creator forgery** (inject a block as another creator) → `InvalidSignature`, asserted
  *after* the identity is well-formed — so the signature check, not an id/parse check, is what
  rejects.
- **Framer** (signature malleability to make an honest creator look like an equivocator) →
  `InvalidSignature`, with the honest strand asserted live and unflagged *before* the attempt.
- **Replay** → `Ok(())`, idempotent.
- **Attack 2b — the impersonation the hybrid id exists to stop**
  (`blocklace_attacks.rs:185`): claim the victim's hybrid id, carry your **own** ed25519 key and a
  signature that *genuinely verifies* under it. The classical half is satisfied — the test proves
  this non-vacuously — and only the commitment gate in `verify_hybrid` refuses the block
  (`BadPqSignature`). The test also discriminates the gate from later checks: a well-committed id
  with the same shape passes the gate and is refused one check later by the missing-PQ sentinel.

Attack 2b names its path: `receive_block` (ed25519-only, DAG reconstruction) *cannot*
refuse this forgery — that is documented at the call site (`node/src/finality_gate.rs:238`) — so
the test drives `verify_hybrid` directly, the check the live wire actually reaches via
`receive_block_pinned`. The finality gate's own tests close the loop at the verified rule: an
unenrolled attacker hybrid id is never admitted, and an identity built from an honest ed25519 half
with a substituted ML-DSA half is a *different* hybrid id that the verified rule does not admit
(`finality_gate.rs:389`). The suites carry their non-vacuity in-line: attack 2b asserts the
classical half verifies before the gate refuses, and the framer test asserts the honest strand is
live before the framing attempt — so a pass means "refused", never "never reached".

---

## The metatheory chain — floor to finality, in Lean

Everything below lives in `metatheory/Dregg2/Crypto/`, with in-file `#assert_axioms` /
`#assert_all_clean` guards (axioms ⊆ `{propext, Classical.choice, Quot.sound}`) that fail the build
if a keystone is not axiom-clean. The chain, bottom-up:

**The floor.** Named hardness assumptions, taken as hypotheses and never discharged:
`SchnorrDLHard` (discrete log), `Lattice.MSISHard` (Module-SIS), `Lattice.MLWESearchHard`
(Module-LWE), hash collision-resistance. Three of these are existence-form and **degenerate at
deployed parameters** — proven so by `CryptoFloorTeeth.lean`, which also carries the proper
adversary-indexed replacement: bounded-adversary advantage ensembles (`…HardQuantShape`) with the
deployed keystone re-grounded on them (`dregg_pq_game_forger_negl_under_comp_floor`). Real hardness
quantifies over efficient adversaries, not over the existence of solutions. Read the full caveat in
[PQ-CRYPTO.md](PQ-CRYPTO.md) ("the existence-form floor caveat") before trusting any floor row.

**The quantum adversary.** `QuantumOracle.lean` models the QROM from Mathlib primitives: states are
`EuclideanSpace ℂ B`, the random-oracle unitary `|x,y⟩ ↦ |x, y + H x⟩` is a proved
`LinearIsometryEquiv`. `OneWayToHiding.lean` proves the O2H lemma over it — `o2h_bound`
(`OneWayToHiding.lean:212`): a q-query quantum adversary's advantage at distinguishing a
reprogrammed oracle is `≤ 2·√(q·Pfind)` — by hybrid telescoping and the same Cauchy–Schwarz core as
the forking lemma. `FoQrom.lean` / `FoQromRegrounded.lean` ground the ML-KEM FO transform's
random-oracle leg on this proved bound (`foQromIndCca_negl`), replacing the opaque `1/2^λ`
idealisation with the genuine O2H term.

**Primitive games.** ML-DSA forgery → SelfTargetMSIS (the forking extraction is *proved*, not
hypothesized, in `ForkingDischarge.lean`); Schnorr/ed25519 EUF-CMA → discrete log
(`SchnorrEufCma.lean`, full forking extraction); ML-KEM IND-CCA → MLWE in the QROM
(`MlKemIndCca.lean`, its QROM leg discharged via O2H as above).

**The hybrid keystone.** `hybrid_secure_if_either_floor` (`HybridCombiner.lean:232`), discharged
form `hybrid_secure_if_either_floor_discharged` (`ForkingDischarge.lean:458`): the `ed25519 ∧
ML-DSA` combiner is EUF-CMA if **either** floor holds. Breaking the hybrid requires breaking both.

**Quantum-safe finality.** `consensus_safe_under_floor` (`ConsensusSafety.lean:200`): with a
committee of `n` members, `≤ f` Byzantine, `n > 3f`, quorum `n − f`, and finalization votes signed
by the hybrid scheme, **two conflicting blocks cannot both finalize at a height** under
`SchnorrDLHard ∨ MSISHard`. The proof is quorum-intersection counting (two quorums share an honest
member) plus unforgeability (that member's double-vote is a `Forgery` refuting its `EufCma`, which
the keystone discharges from the floor). The discharged sibling — per-member forking reductions
proved, not hypothesized — is `consensus_safe_under_floor_discharged`
(`ForkingDischargeConsumers.lean:233`). The quantitative shadow (`ProtocolSoundnessQuant.lean`)
bounds the consensus-break *advantage* by the hybrid forger advantage, negligible under the
adversary-indexed floors.

**Down to code.** `DreggPqRefinement.lean` connects the deployed `dregg-pq` API to the proved
`SigScheme` model: `dregg_pq_refines_sigscheme` (the model reads back exactly the API's public
behavior, with teeth — an unfaithful model fails to refine), `dregg_pq_correct` (`:109`) deriving
model-correctness from the named FIPS floor, and MSIS/IND-CCA inheritance for the deployed scheme.
The code's signature scheme bottoms out at the same lattice floor the model does.

---

## The named boundary

**The FIPS hypothesis.** The one labeled hypothesis per primitive that the code-correctness
conclusion is conditioned on:

- `Fips204Correct` (`DreggPqRefinement.lean:84`): the deployed API's sign→verify round-trip —
  `∀ seed ctx msg, verify (keygen seed) ctx msg (sign seed ctx msg) = true`. It is proven
  **load-bearing** (`badApi_not_correct`: without it, correctness is underivable), taken as a
  theorem hypothesis, never used as a carrier.
- `Fips203Correct` (`DreggPqRefinement.lean:206`): the ML-KEM encaps→decaps round-trip, same
  discipline, same falsifiability tooth (`badKem_not_fips203`).

**The verified-FIPS ladders, at current resolution.** The discharges of `Fips204Correct` and
`Fips203Correct` are each partially built, each rung real and each residual named. The
fips204 side:

- `Fips204Verify.lean` extracts an **executable, Lean-verified ML-DSA verify core** at deployed
  literals (`q = 8380417`, `γ₂`, `β = 196`, …), `@[export]`ed and compiled leanc-native;
  `extractedApi_fips204` (`:156`) proves `Fips204Correct` for the extracted core as a theorem — but
  at a scalar caricature of the module (`n = 1`, `A = id`), which its own header forbids reading as
  a full-dimension floor.
- `Fips204FullDim.lean` proves the **full-dimension mathematical floor**: `fullDimApi_fips204`
  (`:173`) — `Fips204Correct` over the real `R_q = ℤ_q[X]/(X²⁵⁶+1)`, `M = R_q^5`, `N = R_q^6`, for
  arbitrary linear `A`, arbitrary Fiat–Shamir hash, arbitrary `SampleInBall` sampler.
- The deployed verify **routes through the Lean object**: `dregg_pq::ml_dsa_verify`
  (`dregg-pq/src/mldsa.rs:509`) takes its accept/reject verdict from the Lean-verified real-byte
  verify core when an integration layer installs it (`install_lean_verify_core_real`, `:73`) — on
  that path the `fips204` crate has left the verify TCB. The gate test
  (`dregg-pq/tests/mldsa_lean_verify.rs`) proves the routing over genuine 1952/3309-byte
  keys/signatures: honest accepts, tampered rejects, and agreement with the crate as a behavioral
  witness. *The one deploy caveat of this document:* `dregg-pq` ships as a light leaf that never
  links the Lean archive — a node built without installing the cores falls back to the `fips204` /
  `ml-kem` crates for verify / encaps / decaps.
- **Named residuals** (frontier, tracked in `Fips204FullDim.lean` "NEXT LANE"): the `Poly ↔ R_q`
  coefficient bridge that ties the byte-level `signCore`/`verifyCore` to the full-dimension
  `Fips204Correct`; and the sign-side `commit_gap` (the one genuinely-resampled FIPS 204
  Algorithm 7 condition — the other three `HonestKey` gates are theorems from the secret's norm).

The fips203 side:

- `Fips203Kem.lean` extracts **executable, Lean-verified ML-KEM encaps/decaps cores** (the FO
  transform with re-encryption check and implicit reject) and proves `extractedKemApi_fips203` —
  "`Fips203Correct` DISCHARGED — no crate hypothesis" (`Fips203Kem.lean:36`) — as a theorem for the
  extracted cores, at the scalar CPAPKE its header scopes (`n = 1`, `A = 1`; the full-dimension
  ring + byte codec are its named engineering residual).
- `MlKemFips203FullDim.lean` discharges the **same `Fips203Correct`, definition unweakened, at real
  ML-KEM-768 parameters** — `k = 3`, `n = 256`, `q = 3329`, the byte-exact 1184/2400/1088-byte
  pipeline: `fullKemApi_fips203` (`:428`) is kernel-clean over the `goodKey` subtype (FIPS 203
  correctness *is* δ-correctness — an unconditioned `∀ dk` statement would be false — so the
  subtype conditions on exactly the event whose probability `MlKemDelta` bounds, and it is
  inhabited on the genuine `ml-kem` crate key). The quantitative
  `≤ 2⁻¹⁴⁸` failure bound (`roundtrip_fails_le_delta`) carries the file's one named residual:
  `hdom`, the noise envelope's stochastic domination of the true executable noise — a stated
  hypothesis, satisfiable (`roundtrip_fails_le_delta_nonvacuous`), open as the MGF-domination lane.
- The deployed KEM **routes through the Lean objects**: the node installs the extracted real-byte
  decaps core as the shared-secret authority behind `dregg_pq::HybridResponder::finish` and the
  encaps core behind `dregg_pq::hybrid_kem::initiate`
  (`install_mlkem_verified_decaps_core` / `…_encaps_core`) — "taking the `ml-kem` crate OUT of the
  node's KEM-decaps TCB" (`node/src/lib.rs:2526`; the light-leaf install seam is
  `dregg-pq/src/hybrid_kem.rs:137`). Encaps is proved byte-exact against the crate
  (`encaps_matches_crate`), and the running-binary gates `node/tests/mlkem_live_decaps.rs` /
  `mlkem_live_encaps.rs` drive the exact production installs.

**Surface-3** — "no live path keys identity through raw ed25519" — is committed: block identity,
roster, tips, votes, gossip `NodeId`, the verified rule, and the executor's participant projection
(`blocklace_sync.rs:1013`) all key on the hybrid commitment, and the projection fails closed for
members without an enrolled ML-DSA key.

**Modelling boundaries, named.** EUF-CMA / IND-CCA are predicate-level games; the KEM combiner
rests on the standard HKDF dual-PRF assumption; the quantum adversary model enters through the
QROM/O2H leg — the signature-side forking extractions are classical rewinding arguments whose
floors are quantum-plausible, not quantum-internal proofs. The turn-authorization perimeter (a
different surface from consensus finality) has its PQ half verified-when-present but not yet
required — that staging, and the `require_pq` flip, are [PQ-CRYPTO.md](PQ-CRYPTO.md) §4's story.

---

## Related

- [PQ-CRYPTO.md](PQ-CRYPTO.md) — the full hybrid crypto stack: every scheme, reduction table, floor
  caveats, the Hermine threshold-signature compact future.
- [OVERVIEW.md](OVERVIEW.md) — the repo spine.
- [deos/UMEM-POSTQUANTUM.md](deos/UMEM-POSTQUANTUM.md) — the hash-based memory argument's PQ
  posture (the proof side is hash-floored, hence PQ-plausible on different grounds than the
  signature perimeter).
- [reference/STARK-SOUNDNESS-CENSUS.md](reference/STARK-SOUNDNESS-CENSUS.md) — the proof-system
  soundness census the hash floor feeds.
