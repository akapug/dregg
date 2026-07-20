/-
# `Dregg2.Circuit.FriCarrierVacuity` — `FriLowDegreeSound` is VACUOUS (proven in Lean), the
naive repair is FALSE at deployed parameters (proven, with the witness), and the deployed FRI
query leg carries ~31.5 bits, not the 130 its config claims.

## ⚑ THE FINDINGS, in escalating order

**(1) `FriLowDegreeSound` (`FriVerifier.lean:995`) is equivalent to `True`.** Its `extract` field
concludes `∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment` from
`verifyAlgo … = true`. Both conjuncts are free:

  * `GenuineWitness` (`FriVerifier.lean:986`) has ONE field, an unconstrained `exists_ : Prop`.
    So `⟨True⟩` inhabits it and `trivial` discharges the field
    (`genuineWitness_exists_trivially`). The "genuine extractable transition" is a `Prop`-shaped
    hole with nothing in it — the type mentions no trace, no codeword, no AIR, no transition.
  * `proof.exposedSegment = pub.segment` IS `segmentTooth` (`FriVerifier.lean:700`), the SIXTH
    CONJUNCT of `verifyAlgo` (`:724`). The consequent is a syntactic sub-part of the antecedent
    (`verifyAlgo_imp_segment`).

Hence `friLowDegreeSound_content_iff_true`, and `friLowDegreeSoundTrivial` CONSTRUCTS the class at
arbitrary parameters with no hypotheses. `wrap_sound` (`:1037`) and
`EmitVerifier.emitVerifier_wrap_sound` (`:342`) therefore conclude exactly
`proof.exposedSegment = pub.segment` — a list equality the verifier already decided
(`wrap_sound_conclusion_iff_segment`, `wrap_sound_needs_no_carrier`, which proves the payoff with
the carrier binder DELETED). Zero FRI content.

**(2) The carrier admits NO FALSIFIER** (`friLowDegreeSound_has_no_falsifier`). §2 defines the
vacuity canary — `Falsifier acc C` = an accepting instance at which the consequent FAILS — and
proves that for this carrier no such instance CAN exist. That is the machine-checked form of
"not refutable in principle": the lane's sufficient test, failed.

**(3) `verifyAlgo` at the EMITTED checks is BLIND to the proof.** `EmitVerifier.mkChecks`/`mkVk`
(`EmitVerifier.lean:249–258`) instantiate every `FriChecks` field as a CONSTANT
(`foldConsistent _ _ _ := bFold I`, `merklePaths _ _ := bMerkle I`, …). §3 proves that under
constant checks `verifyAlgo` factors as `const && segmentTooth`
(`verifyAlgo_of_constant_checks`), so two proofs with equal `exposedSegment` get the SAME verdict
(`verifyAlgo_blind_to_proof_of_constant_checks`) — an honest proof and a garbage one alike.
`§3.1` exhibits the pair executably over `ℕ` (`#guard`): same segment, disjoint FRI data, both
ACCEPT. So `emitVerifier_wrap_sound`'s antecedent constrains `proof` through `exposedSegment` and
nothing else.

**(4) The naive repair — "every accepting proof yields a genuine codeword" — is FALSE by
counting.** §4 exhibits the falsifier machine-checked (`spotCheck_accepts_non_codeword`): a word
that disagrees with the code somewhere is still accepted whenever the `k` sampled positions all
land in its agreement set, and the exact accepting fraction is `(agree/m)^k`
(`uniform_all_agree_card`), which is `> 0` whenever the agreement set is nonempty
(`far_word_has_accepting_sample`). A carrier of that shape is not weak — it is false.

**(5) ⚑ THE DEPLOYED ARITHMETIC (§5).** `dregg_outer_config.rs`: `OUTER_FRI_LOG_BLOWUP = 3`
(rate `ρ = 1/8`), `OUTER_FRI_NUM_QUERIES = 38`, `OUTER_FRI_QUERY_POW_BITS = 16`; its doc comment
claims `3·38 + 16 = 130` conjectured bits. Three radii, three numbers, all proven here:

| radius | per-query survival | `k = 38` survival | bits |
|---|---|---|---|
| conjectured capacity `δ = 1−ρ` | `1/8` | `(1/8)^38 = 2^-114` | 114 (+16 PoW = 130 — the claim) |
| Johnson `δ = 1−√ρ` | `√(1/8)` | `(1/8)^19 = 2^-57` | 57 |
| **unique decoding `δ = (1−ρ)/2 = 7/16`** — the ONLY radius the tree proves | `9/16` | `(9/16)^38 ∈ (2^-32, 2^-31)` | **31.5** |

`FriVerifierCompose` §2 says in as many words that the Johnson/correlated-agreement carrier is
NOT assumed and `εQuery` is instantiated at the proven `L = 1` unique-decoding radius only. So the
number the tree earns is the third row. `capacity_claim_understates_by_2pow82` proves the deployed
claim is off by more than a factor of `2^82`; `johnson_understates_by_2pow25` proves even the
57-bit "calculator" reading is off by more than `2^25`.

The 16 query-PoW bits do NOT apply to the object `wrap_sound`/`emitVerifier_wrap_sound` quantify
over: `FriChecks.queryPow` there is `queryPowWitnessShape` (`FriVerifier.lean:822`), a
singleton-wire-shape check worth zero bits. Granted anyway, the total is ~47.5, not 130.

**(6) THE REPLACEMENT SHAPE (§6).** `attempt_union_le` is the `Q`-attempt union bound over any
finite sample space (Bernoulli, via `Fintype.card_piFinset_const`): a `Q`-attempt adversary's
success is `≤ Q · p` where `p` is the single-attempt fraction. Composed with the single-attempt
fraction it gives an ε-BOUNDED, `Q`-QUANTIFIED statement — the only shape a carrier here is
allowed to take. `Dregg2.Circuit.FriCarrierEpsilon` wires it to the DEPLOYED non-uniform
`sampleBits` sampler via codex's `FriQuerySamplingBias.biased_query_survival_pow_le` (kept in a
separate file only because `FriQuerySamplingBias`'s import closure is currently red on another
lane's `Emit/EffectVmEmitNoteSpend`).

## Discipline
ADDITIVE. Modifies NOTHING — `FriVerifier` is imported read-only and untouched. No `sorry`, no
fresh `axiom`, no `native_decide`. `#assert_all_clean` over every keystone.
-/
import Dregg2.Circuit.FriVerifier
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriCarrierVacuity

open Finset
open Dregg2.Circuit.FriVerifier

/-! ## §1 — THE VACUITY, MACHINE-CHECKED.

`FriLowDegreeSound.extract`'s conclusion has two conjuncts and BOTH are free. -/

/-- **HOLE 1: `GenuineWitness` is a `Prop`-shaped hole.** Its single field `exists_ : Prop` is
unconstrained, so `⟨True⟩` inhabits it and `trivial` discharges the field. Whatever
`∃ w : GenuineWitness F, w.exists_` was meant to say, it says nothing. -/
theorem genuineWitness_exists_trivially (F : Type) :
    ∃ w : GenuineWitness F, w.exists_ :=
  ⟨⟨True⟩, trivial⟩

/-- **HOLE 2: the consequent is a CONJUNCT of the antecedent.** `segmentTooth` is definitionally
`proof.exposedSegment = pub.segment`, and it is the sixth `&&` of `verifyAlgo`. A verifier
acceptance ALREADY hands you the segment equality — no carrier required. -/
theorem verifyAlgo_imp_segment {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (h : verifyAlgo perm RATE toNat params vk checks initState logN proof pub = true) :
    proof.exposedSegment = pub.segment := by
  unfold verifyAlgo at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

/-- **⚑⚑ THE VACUITY THEOREM.** `FriLowDegreeSound`'s entire content — the `extract` field,
verbatim — is EQUIVALENT TO `True`. It is not a weak assumption, not an optimistic assumption, not
an assumption at all: it is a tautology, at every `perm`/`RATE`/`toNat`/`params`/`vk`/`checks`/
`initState`/`logN`, including instantiations where `verifyAlgo` accepts every proof. -/
theorem friLowDegreeSound_content_iff_true {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) :
    (∀ (proof : BatchProofData F) (pub : WrapPublics F),
        verifyAlgo perm RATE toNat params vk checks initState logN proof pub = true →
        ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment)
      ↔ True := by
  constructor
  · intro _; trivial
  · intro _ proof pub haccept
    exact ⟨⟨True⟩, trivial,
      verifyAlgo_imp_segment perm RATE toNat params vk checks initState logN proof pub haccept⟩

/-- **The carrier CONSTRUCTS, unconditionally.** A `FriLowDegreeSound` at ARBITRARY parameters,
with no hypotheses and no cryptography. Deliberately NOT registered as an `instance` — the point
is that it could be, and then every `[carrier : FriLowDegreeSound …]` binder in the tree would
silently resolve. That is the measure of what those binders assume: nothing. -/
@[reducible] def friLowDegreeSoundTrivial {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) :
    FriLowDegreeSound perm RATE toNat params vk checks initState logN where
  extract := fun proof pub haccept =>
    ⟨⟨True⟩, trivial,
      verifyAlgo_imp_segment perm RATE toNat params vk checks initState logN proof pub haccept⟩

/-- **`wrap_sound`'s conclusion, decoded.** The payoff's existential is EQUIVALENT to the bare list
equality `proof.exposedSegment = pub.segment`. Everything the `∃ w : GenuineWitness F, w.exists_ ∧
…` prefix appears to add is zero. -/
theorem wrap_sound_conclusion_iff_segment {F : Type}
    (proof : BatchProofData F) (pub : WrapPublics F) :
    (∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment)
      ↔ proof.exposedSegment = pub.segment := by
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨⟨True⟩, trivial, h⟩

/-- **⚑ `wrap_sound` NEEDS NO CARRIER.** Its full conclusion follows from `GnarkRefines` plus the
gnark acceptance alone — this statement is `FriVerifier.wrap_sound` (`:1037`) with the
`[carrier : FriLowDegreeSound …]` binder DELETED, and it still goes through.
`EmitVerifier.emitVerifier_wrap_sound` (`:342`) is a direct instantiation of `wrap_sound`, so it
inherits exactly this content and no more. -/
theorem wrap_sound_needs_no_carrier {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (gnark : GnarkCircuit F)
    (href : GnarkRefines perm RATE toNat params vk checks initState logN gnark)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (haccept : gnark proof pub = true) :
    ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment := by
  refine ⟨⟨True⟩, trivial, ?_⟩
  refine verifyAlgo_imp_segment perm RATE toNat params vk checks initState logN proof pub ?_
  rw [← href]; exact haccept

/-! ## §2 — ⚑ THE VACUITY CANARY.

The reusable discipline. A carrier is an implication `accepts p u = true → C p u`. It is VACUOUS
exactly when that implication is provable outright. The certificate that it is NOT is a FALSIFIER:
an accepting instance at which the consequent FAILS.

**The canary is `Falsifier`.** Ship `theorem myCarrier_nonvacuous : Falsifier acc C := ⟨…⟩`
alongside every carrier. If the carrier is ever weakened until acceptance implies it, that term
becomes UNPROVABLE and the line stops compiling. A carrier with no falsifier term is a carrier
nobody checked. -/

/-- The carrier shape: acceptance implies the consequent. -/
def ImpliedByAcceptance {P U : Type} (acc : P → U → Bool) (C : P → U → Prop) : Prop :=
  ∀ p u, acc p u = true → C p u

/-- **THE CANARY.** A falsifier: an ACCEPTED instance whose consequent is FALSE. Its existence is
what makes a carrier a real assumption rather than a tautology. -/
def Falsifier {P U : Type} (acc : P → U → Bool) (C : P → U → Prop) : Prop :=
  ∃ p u, acc p u = true ∧ ¬ C p u

/-- **The canary bites.** A falsifier refutes vacuity: no carrier with a falsifier can be
discharged by acceptance alone. -/
theorem falsifier_refutes_implied {P U : Type} (acc : P → U → Bool) (C : P → U → Prop)
    (hf : Falsifier acc C) : ¬ ImpliedByAcceptance acc C := by
  rintro himp
  obtain ⟨p, u, hacc, hnc⟩ := hf
  exact hnc (himp p u hacc)

/-- The canary's failure mode, stated: a vacuous carrier admits no falsifier at all. Nothing can be
exhibited, so nothing ever is, so the vacuity is never noticed. -/
theorem implied_has_no_falsifier {P U : Type} (acc : P → U → Bool) (C : P → U → Prop)
    (himp : ImpliedByAcceptance acc C) : ¬ Falsifier acc C :=
  fun hf => falsifier_refutes_implied acc C hf himp

/-- **⚑⚑ THE CANARY FIRES ON `FriLowDegreeSound`.** Its consequent admits NO FALSIFIER — there is
provably no proof/publics pair that `verifyAlgo` accepts and at which the "genuine extractable
witness with matching segment" claim fails. Not "we could not find one": there cannot be one, at
any parameters. -/
theorem friLowDegreeSound_has_no_falsifier {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) :
    ¬ Falsifier
        (fun (proof : BatchProofData F) (pub : WrapPublics F) =>
          verifyAlgo perm RATE toNat params vk checks initState logN proof pub)
        (fun proof pub => ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment) :=
  implied_has_no_falsifier _ _ (fun proof pub haccept =>
    ⟨⟨True⟩, trivial,
      verifyAlgo_imp_segment perm RATE toNat params vk checks initState logN proof pub haccept⟩)

/-! ## §3 — ⚑ `verifyAlgo` AT THE EMITTED CHECKS IS BLIND TO THE PROOF.

`EmitVerifier.mkChecks` / `mkVk` (`EmitVerifier.lean:249–258`) supply every `FriChecks` field and
the VK shape as a CONSTANT of the emitted-circuit inputs `I` — `foldConsistent _ _ _ := bFold I`,
`merklePaths _ _ := bMerkle I`, `batchTables _ _ := bBatch I`, `queryPow _ := bQPow I`,
`shapeMatches _ := bCanon I`. None of the five looks at `proof`. -/

/-- **`verifyAlgo` factors under constant checks.** With every check a constant Bool, the whole
verifier collapses to `const && segmentTooth proof pub`: the ONLY proof-dependent conjunct is the
segment list equality. This is exactly `EmitVerifier.verifyAlgo_mk` (`:264`), restated abstractly
so the consequence below can be drawn without the emit module. -/
theorem verifyAlgo_of_constant_checks {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (b0 b1 b2 b3 b4 : Bool) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) :
    verifyAlgo perm RATE toNat params ⟨fun _ => b0⟩
        ⟨fun _ _ _ => b1, fun _ _ => b2, fun _ _ => b3, fun _ => b4⟩
        initState logN proof pub
      = (b0 && b1 && b2 && b3 && b4 && segmentTooth proof pub) := rfl

/-- **⚑ THE BLINDNESS.** Under constant checks the verifier CANNOT DISTINGUISH two proofs with the
same exposed segment. Feed it an honest proof and a proof whose Merkle caps, fold openings, final
poly, OOD point, table openings and PoW witness are all garbage: same verdict. Whatever
`emitVerifier_wrap_sound` concludes about a `gnarkDenote`-accepted proof, it concludes verbatim
about the garbage twin. -/
theorem verifyAlgo_blind_to_proof_of_constant_checks {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (b0 b1 b2 b3 b4 : Bool) (initState : List F) (logN : Nat)
    (p₁ p₂ : BatchProofData F) (pub : WrapPublics F)
    (hseg : p₁.exposedSegment = p₂.exposedSegment) :
    verifyAlgo perm RATE toNat params ⟨fun _ => b0⟩
        ⟨fun _ _ _ => b1, fun _ _ => b2, fun _ _ => b3, fun _ => b4⟩ initState logN p₁ pub
      = verifyAlgo perm RATE toNat params ⟨fun _ => b0⟩
        ⟨fun _ _ _ => b1, fun _ _ => b2, fun _ _ => b3, fun _ => b4⟩ initState logN p₂ pub := by
  rw [verifyAlgo_of_constant_checks, verifyAlgo_of_constant_checks]
  unfold segmentTooth
  rw [hseg]

/-! ### §3.1 — the blindness, EXECUTABLE. Two proofs, one segment, both accepted. -/

section BlindnessWitness

/-- The honest-shaped proof: a real trace commitment, a fold commitment, a final constant, a
query opening, an OOD point, a PoW witness. Segment `[7, 7]`. -/
private def honestProof : BatchProofData Nat :=
  { traceCommit := [11], friCommitments := [[22]], finalPoly := [33],
    queries := [{ index := 1, layers := [{ beta := 3, x := 5, e0 := 10, e1 := 4,
                                           leaf := [10], siblings := [[99]] }] }],
    exposedSegment := [7, 7], oodPoint := [3],
    tableOpenings := [{ degreeBits := 1, expectedDegreeBits := 1, constraintEval := 40,
                        quotientAtZeta := 5, vanishingAtZeta := 8, logupCumSum := 0 }],
    powWitness := [8] }

/-- The garbage twin: EVERY FRI-relevant field emptied or scrambled — no fold layers, no query
openings, no tables, no PoW witness, an empty final poly. Only `exposedSegment` is preserved. -/
private def garbageProof : BatchProofData Nat :=
  { traceCommit := [], friCommitments := [], finalPoly := [],
    queries := [], exposedSegment := [7, 7], oodPoint := [],
    tableOpenings := [], powWitness := [] }

private def toyPub : WrapPublics Nat := { segment := [7, 7] }

private def toyParams : FriParams :=
  { logBlowup := 3, numQueries := 1, powBits := 16, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 4 }

/-- The emitted-shape checks: all five verdicts `true`, none looking at the proof — the shape
`EmitVerifier.mkChecks` has when its leaves are satisfied. -/
private def constChecks : FriChecks Nat :=
  ⟨fun _ _ _ => true, fun _ _ => true, fun _ _ => true, fun _ => true⟩

private def constVk : RecursionVk Nat := ⟨fun _ => true⟩

-- ⚑ THE HONEST PROOF IS ACCEPTED …
#guard verifyAlgo (F := Nat) id 8 id toyParams constVk constChecks [0,0,0,0,0,0,0,0] 4
  honestProof toyPub = true
-- ⚑ … AND SO IS THE GARBAGE TWIN. Same verdict, no FRI data whatsoever.
#guard verifyAlgo (F := Nat) id 8 id toyParams constVk constChecks [0,0,0,0,0,0,0,0] 4
  garbageProof toyPub = true
-- The two proofs really are different objects; only the segment agrees.
#guard honestProof.traceCommit ≠ garbageProof.traceCommit
#guard honestProof.exposedSegment = garbageProof.exposedSegment

/-- **The garbage twin is ACCEPTED**, as a theorem rather than only a `#guard`. The pair
`(garbageProof, toyPub)` passes while carrying no FRI data at all — no fold layers, no query
openings, no tables, no PoW witness, an empty final poly. Any consequent that genuinely asserted
"the proof opens a low-degree codeword" would be FALSE here; that the OLD carrier's consequent is
nevertheless satisfied at this pair is precisely its vacuity. -/
theorem garbage_twin_accepted :
    verifyAlgo (F := Nat) id 8 id toyParams constVk constChecks [0,0,0,0,0,0,0,0] 4
      garbageProof toyPub = true := by decide

/-- And the old carrier's consequent HOLDS at that garbage pair — witnessing, concretely, that
`FriLowDegreeSound` extracts a "genuine transition" from a proof containing nothing. -/
theorem old_carrier_satisfied_by_garbage :
    ∃ w : GenuineWitness Nat, w.exists_ ∧ garbageProof.exposedSegment = toyPub.segment :=
  ⟨⟨True⟩, trivial, rfl⟩

end BlindnessWitness

/-! ## §4 — ⚑ THE NAIVE REPAIR IS FALSE, BY COUNTING.

The obvious fix — replace `GenuineWitness` with a real predicate, e.g. "the committed word IS a
codeword" — produces a carrier that is not weak but FALSE. A spot-check verifier that samples `k`
of `m` positions accepts any word whose disagreements all dodge the sample. This section proves
that with an explicit witness, and counts the accepting fraction exactly. -/

/-- The spot-check verifier over a word, abstracted to its soundness-relevant content: `agree` is
the set of domain positions at which the committed word matches the code, and the verifier accepts
iff all `k` sampled positions lie in it. -/
def spotCheckAccept {m k : ℕ} (agree : Finset (Fin m)) (Q : Fin k → Fin m) : Bool :=
  decide (∀ i, Q i ∈ agree)

/-- "The committed word is a codeword" = it agrees with the code EVERYWHERE. -/
def IsCodeword {m : ℕ} (agree : Finset (Fin m)) : Prop := agree = Finset.univ

/-- **⚑ THE FALSIFIER, MACHINE-CHECKED.** On a 2-position domain, a word agreeing only at position
`0` is NOT a codeword, yet the 1-query spot check that happens to sample position `0` ACCEPTS. So
`accept → IsCodeword` has a falsifier — i.e. the naive repaired carrier is REFUTABLE, and refuted.
Contrast `friLowDegreeSound_has_no_falsifier`: the old carrier could not even be attacked. -/
theorem spotCheck_accepts_non_codeword :
    Falsifier (fun (agree : Finset (Fin 2)) (Q : Fin 1 → Fin 2) => spotCheckAccept agree Q)
      (fun agree _ => IsCodeword agree) :=
  ⟨{0}, fun _ => 0, by decide,
    fun h => absurd h (by decide : ¬ (({0} : Finset (Fin 2)) = Finset.univ))⟩

/-- **The exact accepting count.** Over uniform `k`-query samples on an `m`-position domain, the
number of samples on which every query lands in `agree` is exactly `|agree|^k`. No inequality, no
slack: this is the counting identity behind "a far word passes with probability `(1−δ)^k`". -/
theorem uniform_all_agree_card (m k : ℕ) (agree : Finset (Fin m)) :
    (Finset.univ.filter (fun Q : Fin k → Fin m => ∀ i, Q i ∈ agree)).card = agree.card ^ k := by
  classical
  have hset : (Finset.univ.filter (fun Q : Fin k → Fin m => ∀ i, Q i ∈ agree))
      = Fintype.piFinset (fun _ : Fin k => agree) := by
    ext Q; simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset_const]

/-- **⚑ A FAR WORD ALWAYS HAS AN ACCEPTING SAMPLE.** If the word agrees anywhere at all, some
`k`-query sample accepts it — however far it is from the code, and however large `k` is. The
"accepting proof ⟹ codeword" reading is therefore false by construction, not merely unproven: the
set of accepting samples for a non-codeword is NONEMPTY. -/
theorem far_word_has_accepting_sample {m : ℕ} (k : ℕ) (agree : Finset (Fin m))
    (hne : agree.Nonempty) : ∃ Q : Fin k → Fin m, ∀ i, Q i ∈ agree := by
  obtain ⟨a, ha⟩ := hne
  exact ⟨fun _ => a, fun _ => ha⟩

/-- The accepting FRACTION, exactly: `(|agree| / m)^k`. At `|agree| = (1−δ)·m` this is `(1−δ)^k` —
the number §5 evaluates at the deployed knobs. -/
theorem uniform_accept_fraction (m k : ℕ) (hm : 0 < m) (agree : Finset (Fin m)) :
    ((Finset.univ.filter (fun Q : Fin k → Fin m => ∀ i, Q i ∈ agree)).card : ℝ)
        / ((m : ℝ) ^ k)
      = ((agree.card : ℝ) / (m : ℝ)) ^ k := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [uniform_all_agree_card, div_pow]
  push_cast
  ring

/-! ## §5 — ⚑⚑ THE DEPLOYED ARITHMETIC. Three radii, three numbers.

`dregg_outer_config.rs`: `OUTER_FRI_LOG_BLOWUP = 3` ⇒ rate `ρ = 2^-3 = 1/8`;
`OUTER_FRI_NUM_QUERIES = 38`; `OUTER_FRI_QUERY_POW_BITS = 16`. Its doc comment reads
"Soundness held: 3·38 + 16 = 130 conjectured bits" — the CAPACITY accounting, which charges
`log₂(1/ρ) = 3` bits per query, i.e. assumes decoding all the way to `δ = 1 − ρ`. -/

/-- **The deployed CLAIM, decoded.** `3 bits/query · 38 queries` is exactly the survival `(1/8)^38
= 2^-114`; with the 16 PoW bits that is the config's `130`. This is the list-decoding-TO-CAPACITY
regime — a conjecture, carried by nothing in this tree. -/
theorem capacity_claim_survival : ((1 : ℝ) / 8) ^ 38 = (1 : ℝ) / 2 ^ 114 := by
  norm_num

/-- **The JOHNSON reading** — `δ = 1 − √ρ`, per-query survival `√(1/8) = 2^-1.5`, so the 38-query
survival is `(1/8)^19 = 2^-57`. This is the "57 calculator bits" number. It needs the
correlated-agreement / Johnson-radius carrier, which `FriVerifierCompose` §2 states explicitly is
NOT assumed here. -/
theorem johnson_survival : ((1 : ℝ) / 8) ^ 19 = (1 : ℝ) / 2 ^ 57 := by
  norm_num

/-- **⚑⚑ THE NUMBER THE TREE ACTUALLY EARNS.** At the PROVEN unique-decoding radius
`δ = (1 − ρ)/2 = 7/16`, the per-query survival is `1 − δ = 9/16` and the 38-query survival is
`(9/16)^38`, which lies STRICTLY BETWEEN `2^-32` and `2^-31`. The deployed FRI query leg carries
**between 31 and 32 bits** — not 57, and not 130. -/
theorem deployed_ud_survival_between :
    (1 : ℝ) / 2 ^ 32 < ((9 : ℝ) / 16) ^ 38 ∧ ((9 : ℝ) / 16) ^ 38 < (1 : ℝ) / 2 ^ 31 := by
  constructor <;> norm_num

/-- **⚑ THE CLAIM IS OFF BY MORE THAN `2^82`.** The config's conjectured-capacity survival, even
multiplied by `2^82`, is still smaller than the survival at the radius the tree proves. The `130 −
47.5 ≈ 82` bit gap is entirely the un-carried list-decoding-to-capacity conjecture. -/
theorem capacity_claim_understates_by_2pow82 :
    ((1 : ℝ) / 8) ^ 38 * 2 ^ 82 < ((9 : ℝ) / 16) ^ 38 := by
  rw [capacity_claim_survival]
  have h := deployed_ud_survival_between.1
  have : (1 : ℝ) / 2 ^ 114 * 2 ^ 82 = 1 / 2 ^ 32 := by norm_num
  linarith [this ▸ h]

/-- **⚑ EVEN THE 57-BIT READING IS OFF BY MORE THAN `2^25`.** The Johnson survival times `2^25` is
still below the unique-decoding survival. So "57 bits" is itself an over-claim relative to what is
proven; the proven figure is ~31.5. -/
theorem johnson_understates_by_2pow25 :
    ((1 : ℝ) / 8) ^ 19 * 2 ^ 25 < ((9 : ℝ) / 16) ^ 38 := by
  rw [johnson_survival]
  have h := deployed_ud_survival_between.1
  have heq : (1 : ℝ) / 2 ^ 57 * 2 ^ 25 = 1 / 2 ^ 32 := by norm_num
  linarith [heq ▸ h]

/-- The INNER wrap config (`FriVerifier.ir2LeafWrapConfig`: blowup 6 ⇒ `ρ = 1/64`, 19 queries,
16 PoW bits, claimed `19·6 + 16 = 130`). At unique decoding `δ = (1−ρ)/2 = 63/128`, per-query
survival `65/128`, the 19-query survival exceeds `2^-19` — so that leg proves fewer than 19 bits
before PoW, against a claimed 114. Same disease, different knobs. -/
theorem inner_wrap_ud_survival_gt :
    (1 : ℝ) / 2 ^ 19 < ((65 : ℝ) / 128) ^ 19 := by
  norm_num

/-! ## §6 — ⚑ THE REPLACEMENT SHAPE: `Q`-ATTEMPT-QUANTIFIED, EXPLICIT ε.

A carrier here must quantify over a BUDGET and carry an ε; it must be a statement about the
MEASURE of acceptance, so that no single accepting instance discharges it, and so that a
too-small ε makes it FALSE (refutable). `attempt_union_le` is the budget half: over any finite
sample space, a `Q`-attempt adversary that wins if ANY attempt's draw lands in the good set `G`
succeeds with probability at most `Q · |G|/|α|`. Proven by the exact complement count
(`Fintype.card_piFinset_const`) plus Bernoulli — no union-bound hand-wave. -/

/-- **⚑ THE `Q`-ATTEMPT UNION BOUND (proven, not carried).** Over `Q` independent draws from a
finite sample space `α`, the fraction of runs on which SOME draw lands in `G` is at most
`Q · (|G| / |α|)`. The complement is exactly `(|Gᶜ|/|α|)^Q` (a `piFinset` count), and Bernoulli's
inequality converts `1 − (1−p)^Q ≤ Q·p`. -/
theorem attempt_union_le {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (G : Finset α) (Q : ℕ) :
    ((Finset.univ.filter (fun S : Fin Q → α => ∃ j, S j ∈ G)).card : ℝ)
        / ((Fintype.card α : ℝ) ^ Q)
      ≤ (Q : ℝ) * ((G.card : ℝ) / (Fintype.card α : ℝ)) := by
  classical
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hn
  -- the complement is a constant `piFinset`, counted exactly
  have hcompl : (Finset.univ.filter (fun S : Fin Q → α => ¬ ∃ j, S j ∈ G)).card
      = Gᶜ.card ^ Q := by
    have hset : (Finset.univ.filter (fun S : Fin Q → α => ¬ ∃ j, S j ∈ G))
        = Fintype.piFinset (fun _ : Fin Q => Gᶜ) := by
      ext S; simp [Fintype.mem_piFinset, not_exists]
    rw [hset, Fintype.card_piFinset_const]
  -- the two halves partition the whole sample space
  have hsplit : (Finset.univ.filter (fun S : Fin Q → α => ∃ j, S j ∈ G)).card
      + (Finset.univ.filter (fun S : Fin Q → α => ¬ ∃ j, S j ∈ G)).card
      = Fintype.card α ^ Q := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hGc : (G.card : ℝ) + (Gᶜ.card : ℝ) = (Fintype.card α : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Finset.card_add_card_compl G)
  set A : ℝ := ((Finset.univ.filter (fun S : Fin Q → α => ∃ j, S j ∈ G)).card : ℝ) with hA
  set n : ℝ := (Fintype.card α : ℝ) with hnDef
  set p : ℝ := (G.card : ℝ) / n with hp
  set q : ℝ := (Gᶜ.card : ℝ) / n with hq
  have hAeq : A = n ^ Q - ((Gᶜ.card : ℝ)) ^ Q := by
    have := congrArg (Nat.cast (R := ℝ)) hsplit
    push_cast at this
    rw [hcompl] at this
    push_cast at this
    linarith
  have hpq : p + q = 1 := by
    have hsum : p + q = ((G.card : ℝ) + (Gᶜ.card : ℝ)) / n := by rw [hp, hq]; ring
    rw [hsum, hGc, div_self hnR.ne']
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hp1 : p ≤ 1 := by linarith
  -- Bernoulli's inequality, in the form `1 − Q·p ≤ (1 − p)^Q`
  have hbern : (1 : ℝ) - (Q : ℝ) * p ≤ (1 - p) ^ Q := by
    have h := one_add_mul_le_pow (a := -p) (by linarith) Q
    simpa [sub_eq_add_neg, mul_neg] using h
  have hq1 : q = 1 - p := by linarith
  have hgoal : A / n ^ Q = 1 - q ^ Q := by
    rw [hAeq, hq, div_pow, sub_div, div_self (pow_ne_zero Q hnR.ne')]
  rw [hgoal, hq1]
  linarith [hbern]

/-- **The bound is not slack: it FIRES.** At `|G| = |α|` (the adversary always wins) the fraction
is `1` and the bound reads `Q ≥ 1` — tight at `Q = 1`. A `Q`-quantified ε statement therefore has
real content at every budget, unlike a carrier whose conclusion its own antecedent supplies. -/
theorem attempt_union_tight_at_full {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] :
    ((Finset.univ.filter (fun S : Fin 1 → α => ∃ j, S j ∈ (Finset.univ : Finset α))).card : ℝ)
        / ((Fintype.card α : ℝ) ^ 1)
      = 1 := by
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hn
  have hall : (Finset.univ.filter (fun S : Fin 1 → α => ∃ j, S j ∈ (Finset.univ : Finset α)))
      = Finset.univ := by
    ext S; simp
  rw [hall, Finset.card_univ, Fintype.card_fun]
  simp

#assert_all_clean [
  genuineWitness_exists_trivially,
  verifyAlgo_imp_segment,
  friLowDegreeSound_content_iff_true,
  wrap_sound_conclusion_iff_segment,
  wrap_sound_needs_no_carrier,
  falsifier_refutes_implied,
  implied_has_no_falsifier,
  friLowDegreeSound_has_no_falsifier,
  verifyAlgo_of_constant_checks,
  verifyAlgo_blind_to_proof_of_constant_checks,
  spotCheck_accepts_non_codeword,
  uniform_all_agree_card,
  far_word_has_accepting_sample,
  uniform_accept_fraction,
  capacity_claim_survival,
  johnson_survival,
  deployed_ud_survival_between,
  capacity_claim_understates_by_2pow82,
  johnson_understates_by_2pow25,
  attempt_union_le,
  attempt_union_tight_at_full
]

end Dregg2.Circuit.FriCarrierVacuity
