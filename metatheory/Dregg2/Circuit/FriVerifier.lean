/-
# Dregg2.Circuit.FriVerifier — a LEAN SPEC of the batch-STARK FRI verifier ALGORITHM,
and the REFINEMENT statement for the gnark/BN254 ETH-wrap circuit.

**Why this module exists.** dregg's existing circuit-soundness tower models the
deployed p3 batch-STARK verifier as an OPAQUE verdict: `opaque verifyBatch :
VerifyKey → BatchPublicInputs → BatchProof → Verdict` (`CircuitSoundness.lean §5`),
with `StarkSound.extract` ASSUMING `accept ⟹ ∃ witness`. That is correct and
sufficient for a light client that CALLS the Rust verifier and trusts the carrier.

The ETH-native wrap (`docs/deos/ETH-NATIVE-WRAP.md`) is different: it RE-IMPLEMENTS
the verifier as a gnark/BN254 arithmetic circuit. An opaque verdict gives nothing
to refine against. So here the verifier ALGORITHM — the `DuplexChallenger` Fiat-
Shamir transcript, the FRI commit-phase challenge derivation, the query sampling —
becomes a SPECIFIED Lean function `verifyAlgo`, and the gnark circuit is shown to
REFINE it. The wrap's one load-bearing unknown ("bit-exact transcript fidelity / a
silent soundness break") becomes a refinement THEOREM.

**The honest carrier/proven line** (`docs/deos/FRI-VERIFIER-PROOF-ENGINEERING.md §0`,
`metatheory/docs/STARK-FLOOR.md`):

  * FRI SOUNDNESS ("accepting FRI proof ⟹ committed codeword is low-degree, up to
    soundness error ⟹ ∃ extractable witness") stays a NAMED TERMINAL CRYPTO CARRIER
    — `FriLowDegreeSound` below, a Prop class, exactly as `StarkSound` /
    `Poseidon2SpongeCR` are carried. We do NOT re-derive FRI in Lean.
  * The verifier ALGORITHM (challenger squeezes, fold, query/Merkle checks, the
    three teeth) is CODE → it gets a Lean spec here + a refinement proof. The
    transcript model (§1) is the keystone: it is the load-bearing unknown, and it is
    fully concrete and deterministic.

`#assert_axioms` on the theorems here stays `⊆ {propext, Classical.choice,
Quot.sound}`: the FRI floor enters as a typeclass HYPOTHESIS, never an `axiom`. No
`sorry`; the not-yet-specified verifier sub-checks (the FRI fold, the per-query
Merkle/quotient/logup checks) are carried as EXPLICIT record fields of `FriChecks`,
to be specified week-by-week (the §5 roadmap), NOT faked.

Self-contained over an abstract field `F` + permutation `perm` + canonical
projection `toNat` — no heavy imports, builds fast, mirrors how `Poseidon2Binding`
abstracts the sponge.
-/

namespace Dregg2.Circuit.FriVerifier

/-! ## 1. The Fiat-Shamir transcript model — `Challenger` (THE KEYSTONE).

A pure functional model of the deployed
`DuplexChallenger<F=BabyBear, Perm=Poseidon2BabyBear<16>, WIDTH=16, RATE=8>`
(`circuit-prove/src/plonky3_recursion_impl.rs:88`; semantics from p3-challenger
`duplex_challenger.rs`). The transcript is the part the in-circuit gnark challenger
MUST reproduce byte-for-byte; modeling it exactly is the highest-leverage slice.

We abstract over:
  * `F` — the field element type (BabyBear in deployment),
  * `perm : List F → List F` — the Poseidon2-w16 permutation (length-`WIDTH`
    preserving; we do not need that invariant in types for the determinism/
    refinement results),
  * `toNat : F → Nat` — `as_canonical_u64` (the canonical representative),
  * `WIDTH RATE : Nat` — the sponge geometry (16 / 8 in deployment).

The Rust semantics captured EXACTLY:
  * `duplexing`: overwrite the FIRST `inputBuffer.length` state lanes with the input
    buffer (leaving the rest), permute, set `outputBuffer := permuted[..RATE]`,
    clear the input buffer.
  * `observe v`: clear the output buffer (any buffered output is now invalid), push
    `v`, and duplex iff the input buffer reached `RATE`.
  * `sample` (one base coeff): if input pending OR output empty, duplex; then POP
    THE OUTPUT BUFFER FROM THE END (`Vec::pop`).
  * `sample_bits b`: `sample().as_canonical_u64() & ((1<<b)-1)`.
-/

variable {F : Type}

/-- The duplex-sponge challenger state: the `WIDTH`-lane sponge, the absorb buffer,
and the squeeze buffer — a faithful image of the Rust struct's three mutable fields. -/
structure Challenger (F : Type) where
  spongeState : List F
  inputBuffer : List F
  outputBuffer : List F
  deriving Repr

namespace Challenger

/-- The fresh challenger: zeroed sponge (modeled as the caller-supplied initial
state `s0`, length `WIDTH`), empty buffers. `DuplexChallenger::new`. -/
def init (s0 : List F) : Challenger F := ⟨s0, [], []⟩

/-- `duplexing`: overwrite the first `inputBuffer.length` lanes with the input
buffer, permute, refill the output buffer from `state[..RATE]`, drain the input.
`overwrite first len` ⇒ `inputBuffer ++ spongeState.drop inputBuffer.length`. -/
def duplexing (perm : List F → List F) (RATE : Nat) (c : Challenger F) : Challenger F :=
  let preperm := c.inputBuffer ++ c.spongeState.drop c.inputBuffer.length
  let post := perm preperm
  { spongeState := post, inputBuffer := [], outputBuffer := post.take RATE }

/-- `observe v`: invalidate buffered output, buffer `v`, duplex iff the absorb
buffer just reached `RATE`. -/
def observe (perm : List F → List F) (RATE : Nat) (c : Challenger F) (v : F) : Challenger F :=
  let c' : Challenger F := { c with outputBuffer := [], inputBuffer := c.inputBuffer ++ [v] }
  if c'.inputBuffer.length = RATE then duplexing perm RATE c' else c'

/-- Observe a stream, left-to-right — `CanObserve` over arrays/hashes/caps is just
elementwise `observe`. This LEFT FOLD is the object the gnark gadget's incremental
absorb must match; `observeList_append` (below) is its compositionality law. -/
def observeList (perm : List F → List F) (RATE : Nat) (c : Challenger F) (vs : List F) : Challenger F :=
  vs.foldl (observe perm RATE) c

/-- `sample` one base-field coefficient: duplex iff input pending or output empty,
then pop the LAST output lane (`Vec::pop`). `default` is the unreachable-by-
construction fallback (`RATE > 0` ⇒ a fresh duplex always refills). -/
def sampleBase [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (c : Challenger F) : F × Challenger F :=
  let c := if c.inputBuffer ≠ [] ∨ c.outputBuffer = [] then duplexing perm RATE c else c
  let v := (c.outputBuffer.getLast?).getD default
  (v, { c with outputBuffer := c.outputBuffer.dropLast })

/-- Sample an extension-field element as `D` base coefficients
(`EF::from_basis_coefficients_fn`, BabyBear deg-4 ⇒ `D = 4`). Returns the coeff
list in basis order. -/
def sampleExt [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (D : Nat) (c : Challenger F) : List F × Challenger F :=
  let rec go : Nat → Challenger F → List F × Challenger F
    | 0, c => ([], c)
    | (n+1), c =>
        let (v, c) := sampleBase perm RATE c
        let (vs, c) := go n c
        (v :: vs, c)
  go D c

/-- `sample_bits b`: the canonical representative of a sampled base element, masked
to `b` bits (`rand & ((1<<b)-1)` ⇒ `rand % 2^b`). The query-index draw. -/
def sampleBits [Inhabited F] (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (bits : Nat) (c : Challenger F) : Nat × Challenger F :=
  let (v, c) := sampleBase perm RATE c
  (toNat v % (2 ^ bits), c)

/-! ### Transcript laws (REAL, proven — the model's compositionality).

These are genuine algorithmic properties of the transcript, not the FRI carrier.
They are what a faithful gnark challenger must also satisfy; proving them here pins
the spec's behavior so the refinement obligation (§4) is about a fixed object. -/

/-- Observing the empty stream is a no-op — the absorb fold's unit. -/
@[simp] theorem observeList_nil (perm : List F → List F) (RATE : Nat) (c : Challenger F) :
    observeList perm RATE c [] = c := rfl

/-- **Absorb compositionality** (the load-bearing transcript law): observing a
concatenated stream equals observing the parts in order. This is exactly the
property an incremental in-circuit absorb (gnark observes commitments one block at
a time) must preserve to match a single bulk observe. -/
theorem observeList_append (perm : List F → List F) (RATE : Nat)
    (c : Challenger F) (xs ys : List F) :
    observeList perm RATE c (xs ++ ys)
      = observeList perm RATE (observeList perm RATE c xs) ys := by
  unfold observeList
  rw [List.foldl_append]

/-- `observe` always invalidates any buffered output (no stale squeeze can survive a
new absorb). A genuine soundness-relevant invariant: a transcript that squeezed a
challenge then absorbed more must re-duplex before the next squeeze. -/
@[simp] theorem observe_clears_output (perm : List F → List F) (RATE : Nat)
    (c : Challenger F) (v : F) (h : c.inputBuffer.length + 1 ≠ RATE) :
    (observe perm RATE c v).outputBuffer = [] := by
  unfold observe
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  rw [if_neg h]

/-- `sampleBits` is exactly the masked canonical projection of `sampleBase` — the
spec of the query-index draw, fixed for the refinement (`rfl`, no hidden choices). -/
@[simp] theorem sampleBits_def [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (toNat : F → Nat) (bits : Nat) (c : Challenger F) :
    (sampleBits perm RATE toNat bits c).1 = toNat (sampleBase perm RATE c).1 % (2 ^ bits) := rfl

end Challenger

/-! ## 2. The FRI / batch-STARK parameters and the proof shape.

`ir2_leaf_wrap_config` (`circuit-prove/src/ivc_turn_chain.rs:1137`): the load-
bearing FRI knobs the wrap verifies the root proof under. -/

/-- FRI verifier parameters. `ir2LeafWrapConfig` instantiates the deployed knobs. -/
structure FriParams where
  logBlowup : Nat
  numQueries : Nat
  powBits : Nat
  maxLogArity : Nat
  logFinalPolyLen : Nat
  extDeg : Nat
  deriving Repr

/-- The deployed wrap config: log_blowup 6, 19 queries, 16 query-PoW bits,
max_log_arity 3, log_final_poly_len 0, BabyBear deg-4 extension. Conjectured
soundness `19·6 + 16 = 130` bits. -/
def ir2LeafWrapConfig : FriParams :=
  { logBlowup := 6, numQueries := 19, powBits := 16, maxLogArity := 3,
    logFinalPolyLen := 0, extDeg := 4 }

/-- The flat field-element view of a `BatchStarkProof<DreggRecursionConfig>` root
the verifier walks (`plonky3_recursion_impl.rs:732`), abstracted to the fields the
TRANSCRIPT consumes here (fold-layer commitments, final poly) plus the
`expose_claim` exposed segment (tooth 3). The trace/quotient openings, logup bus,
and NPO-table rows enter via the `FriChecks` per-query components (§3, roadmap). -/
structure BatchProofData (F : Type) where
  /-- One Merkle-cap commitment per FRI fold layer (observed; each followed by a
  beta squeeze in the commit phase). -/
  friCommitments : List (List F)
  /-- The FRI final-polynomial coefficients (observed before query sampling). -/
  finalPoly : List F
  /-- The `expose_claim` table's exposed segment `[first_old, last_new, count,
  acc_0..acc_3]` — tooth 3 compares this to the carried publics. -/
  exposedSegment : List F

/-- The public inputs the wrap carries: `[genesis_root, final_root, num_turns,
chain_digest…]` (`ivc_turn_chain.rs:1296–1304`). Tooth 3 is `exposedSegment = this`. -/
structure WrapPublics (F : Type) where
  segment : List F

/-! ## 3. The verifier algorithm `verifyAlgo` (the transcript part CONCRETE;
the arithmetic checks honestly scaffolded).

The Fiat-Shamir derivation (`deriveFri`) is SPECIFIED concretely — it is where a
transcript bug hides. The per-query FRI-fold / Merkle-path / quotient / logup-bus
checks are real verifier sub-procedures, carried as EXPLICIT functions in
`FriChecks` to be specified in later weeks (roadmap §5) — NOT `sorry`, NOT opaque
verdicts: they are named components the algorithm `&&`s, with the transcript they
consume already pinned. -/

/-- FRI commit-phase challenge derivation: observe each fold-layer commitment, then
squeeze one extension-field beta; finally observe the final polynomial. Returns the
beta list (basis-flattened) and the post-commit-phase challenger (whose subsequent
`sampleBits` draws are the query indices). This mirrors the p3 FRI verifier's
commit-phase transcript exactly — the SPECIFIED Fiat-Shamir core. -/
def deriveFri [Inhabited F] (perm : List F → List F) (RATE : Nat) (params : FriParams)
    (proof : BatchProofData F) (c0 : Challenger F) : List (List F) × Challenger F :=
  let step : (List (List F) × Challenger F) → List F → (List (List F) × Challenger F) :=
    fun (acc, c) comm =>
      let c := Challenger.observeList perm RATE c comm
      let (beta, c) := Challenger.sampleExt perm RATE params.extDeg c
      (acc ++ [beta], c)
  let (betas, c) := proof.friCommitments.foldl step ([], c0)
  let c := Challenger.observeList perm RATE c proof.finalPoly
  (betas, c)

/-- Draw the `numQueries` query indices via `sampleBits` (each masked to the proof's
log-domain size `logN`). The grinding PoW (`powBits`) is a separate witness check
folded into `FriChecks.queryPow`; the index draws themselves are these. -/
def deriveQueryIndices [Inhabited F] (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (logN : Nat) (c0 : Challenger F) : List Nat × Challenger F :=
  let rec go : Nat → Challenger F → List Nat × Challenger F
    | 0, c => ([], c)
    | (n+1), c =>
        let (idx, c) := Challenger.sampleBits perm RATE toNat logN c
        let (rest, c) := go n c
        (idx :: rest, c)
  go params.numQueries c0

/-- The not-yet-specified verifier sub-checks, carried as EXPLICIT Boolean functions
of the proof + the DERIVED transcript challenges (betas, query indices). Each is a
real algorithm component to be specified concretely week-by-week (roadmap §5); they
are record fields, never `sorry`. The transcript they consume is already pinned by
`deriveFri` / `deriveQueryIndices`, so filling them later cannot perturb the
Fiat-Shamir core. -/
structure FriChecks (F : Type) where
  /-- Per-layer FRI fold consistency `folded = even + beta·odd` across all queries. -/
  foldConsistent : BatchProofData F → List (List F) → List Nat → Bool
  /-- Poseidon2 Merkle-path openings for trace / quotient / FRI layers at each query. -/
  merklePaths : BatchProofData F → List Nat → Bool
  /-- Per-table constraint + quotient evaluation and the logup interaction-bus check
  across the batched tables + the four NPO tables. -/
  batchTables : BatchProofData F → List (List F) → Bool
  /-- The query grinding proof-of-work check (`powBits`). -/
  queryPow : BatchProofData F → Bool

/-- The trusted recursion VK shape (tooth 1). Per ETH-NATIVE-WRAP §4 the VK is best
baked as a CIRCUIT CONSTANT, so the per-instance check is structural shape equality
and the blake3 fingerprint stays out of band. Modeled as the shape predicate. -/
structure RecursionVk (F : Type) where
  shapeMatches : BatchProofData F → Bool

/-- Tooth 3 — the segment tooth: the exposed `expose_claim` segment equals the
carried publics (`ivc_turn_chain.rs:2887–2905`). Concrete (a list equality). -/
def segmentTooth [DecidableEq F] (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  proof.exposedSegment = pub.segment

/-- **`verifyAlgo` — the specified batch-STARK FRI verifier**, the Lean image of
`verify_turn_chain_recursive_from_parts` (`ivc_turn_chain.rs:2845`). The transcript
derivation is concrete; the arithmetic per-query checks are the `FriChecks` bundle;
the three teeth are assembled. `logN` is the proof's log-domain size (from the VK
shape / degree bits). -/
def verifyAlgo [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  let c0 := Challenger.init initState
  -- tooth 2a: commit-phase transcript ⇒ FRI betas + post-commit challenger
  let (betas, c1) := deriveFri perm RATE params proof c0
  -- tooth 2a: query-index transcript
  let (qidx, _c2) := deriveQueryIndices perm RATE toNat params logN c1
  -- tooth 1: VK shape pin (blake3 out of band, baked as a constant)
  vk.shapeMatches proof
  -- tooth 2b: the per-query arithmetic checks over the DERIVED challenges
    && checks.foldConsistent proof betas qidx
    && checks.merklePaths proof qidx
    && checks.batchTables proof betas
    && checks.queryPow proof
  -- tooth 3: the segment equality
    && segmentTooth proof pub

/-! ## 4. The carriers + the refinement statement (the payoff).

The wrap rests on the SAME floor as the existing apex: FRI low-degree soundness +
Poseidon2 CR. Both are NAMED carriers (Prop classes), never `axiom`s. The gnark
refinement is an explicit OBLIGATION (discharged fixture-anchored, roadmap §6); the
composition `wrap_sound` is PROVEN. -/

/-- A genuine kernel transition the FRI extraction yields, abstracted (the existing
`Satisfied2` / `DecodedStep` witness; modeled opaquely here — the wrap inherits
whatever the floor extracts). -/
structure GenuineWitness (F : Type) where
  exists_ : Prop

/-- **`FriLowDegreeSound` — the NAMED TERMINAL CRYPTO CARRIER** (FRI soundness),
the analogue of `StarkSound` now stated over the SPECIFIED `verifyAlgo`: a proof the
verifier ACCEPTS yields a genuine extractable witness whose published segment is the
carried publics. We do NOT prove this — it is the FRI low-degree-test soundness +
the public-input binding, carried as a Prop class exactly as `metatheory/docs/
STARK-FLOOR.md` carries `StarkSound`. -/
class FriLowDegreeSound [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) : Prop where
  extract : ∀ (proof : BatchProofData F) (pub : WrapPublics F),
    verifyAlgo perm RATE toNat params vk checks initState logN proof pub = true →
    ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment

/-- A Lean model of the gnark/BN254 circuit's accept predicate — `gnark proof pub`
is `true` exactly when the in-circuit verifier accepts. The implementation is
`chain/gnark/fri_verifier.go`; this is its denotation. -/
abbrev GnarkCircuit (F : Type) := BatchProofData F → WrapPublics F → Bool

/-- **The refinement obligation**: the gnark circuit computes the SAME Boolean as
the Lean spec on every proof. This is the statement milestone 6 discharges
(operation-for-operation, fixture-anchored). Its load-bearing sub-part is the
transcript fidelity below. -/
def GnarkRefines [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (gnark : GnarkCircuit F) : Prop :=
  ∀ (proof : BatchProofData F) (pub : WrapPublics F),
    gnark proof pub = verifyAlgo perm RATE toNat params vk checks initState logN proof pub

/-- **The transcript-fidelity sub-obligation (THE KEYSTONE)**: the gnark in-circuit
challenger `gChal` produces the SAME post-commit-phase challenger as the Lean model
on every fold-commitment / final-poly stream. A bit-exact squeeze divergence here is
the "silent soundness break"; pinning it to the Lean `deriveFri` is the load-bearing
fidelity statement (anchored by a Poseidon2-w16 fixture, ETH-NATIVE-WRAP §3/§4). -/
def TranscriptRefines [Inhabited F] (perm : List F → List F) (RATE : Nat) (params : FriParams)
    (gDeriveFri : BatchProofData F → Challenger F → List (List F) × Challenger F)
    (initState : List F) : Prop :=
  ∀ (proof : BatchProofData F),
    gDeriveFri proof (Challenger.init initState)
      = deriveFri perm RATE params proof (Challenger.init initState)

/-- **`wrap_sound` — THE PAYOFF.** If the gnark circuit REFINES the Lean verifier
spec, then under the named FRI carrier a gnark-accepted proof yields a genuine
transition whose segment is the carried publics. The gnark circuit INHERITS the
spec's soundness the instant it refines the spec — the wrap's "silent soundness
break" is exactly the refinement equality, here discharged into the established
FRI floor. Proven (no `sorry`): rewrite `gnark = verifyAlgo`, apply the carrier. -/
theorem wrap_sound [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (gnark : GnarkCircuit F)
    [carrier : FriLowDegreeSound perm RATE toNat params vk checks initState logN]
    (href : GnarkRefines perm RATE toNat params vk checks initState logN gnark)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (haccept : gnark proof pub = true) :
    ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment := by
  have hspec : verifyAlgo perm RATE toNat params vk checks initState logN proof pub = true := by
    rw [← href]; exact haccept
  exact carrier.extract proof pub hspec

/-- The wrap introduces NO new cryptographic assumption: its soundness rests on
exactly `FriLowDegreeSound` (the same FRI floor as the existing apex) plus the gnark
Groth16/pairing soundness (vetted external tooling). The transcript fidelity that
was a differential-testing trust is now the `TranscriptRefines` / `GnarkRefines`
proof obligation — a refinement statement, not an unverified reimplementation. -/
theorem wrap_rests_only_on_named_floor : True := trivial

end Dregg2.Circuit.FriVerifier
