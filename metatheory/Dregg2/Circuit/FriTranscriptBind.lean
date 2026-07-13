import Dregg2.Circuit.FriVerifier
import Dregg2.Tactics

/-!
# Transcript-binding the OOD challenge ζ (survey finding #4), faithful to the deployed p3 order

The modeled `verifyAlgo` derives ONLY the FRI betas and query indices from the Challenger; the OOD
point ζ is read straight from the prover-supplied `proof.oodPoint` (`batchTablesCheck`,
FriVerifier.lean:655) and NEVER checked against the transcript. So in the model a malicious prover
chooses ζ freely, and the proved Schwartz–Zippel ε-bound is decorative.

## The deployed transcript order (READ from the deployed verifier)

`circuit-prove` calls `p3_uni_stark::verify` (plonky3 @82cfad7, `uni-stark/src/verifier.rs`). Its
challenger sequence around ζ is, verbatim (ZK is OFF at deployment, so the random-commitment branch is
inert):

```
observe(degree_bits); observe(base_degree_bits); observe(preprocessed_width);   -- 361-363
observe(commitments.trace);                                                     -- 369
observe_slice(public_values);                                                   -- 373
let alpha = challenger.sample_algebra_element();   -- Λ, the constraint RLC challenge  -- 379
observe(commitments.quotient_chunks);                                           -- 380
let zeta  = challenger.sample_algebra_element();   -- ζ, the OOD point           -- 390
```

FINDING: BOTH ζ and α(=Λ) are transcript-derived in the DEPLOYED verifier. The survey's "Λ appears
nowhere in verifyAlgo" was true of the MODEL, not the deployment.

## What `deriveOod` faithfully models, and the named abstraction gap

`deriveOod` observes `traceCommit` THEN the public values (`pub.segment`), matching the deployed prefix
`observe(trace); observe_slice(public_values)`, then squeezes one extension element. The essential FS
property — ζ is a function of the committed trace AND the public inputs, so a prover cannot pick ζ
before committing — is thereby captured. The residual, named honestly as the KAT correspondence (the
FRI-batch model abstracts p3-uni-stark, so these are folded / validated by the KAT corpus, not modeled
term-for-term): (i) the `degree_bits`/`base_degree_bits`/`preprocessed_width` preamble (public
constants); (ii) the `sample α` + `observe(quotient_chunks)` steps between the public values and ζ — the
FRI-batch `BatchProofData` carries no separate quotient commitment (α is modeled separately as Λ). The
probabilistic half (the squeeze is a uniform draw ⇒ ζ non-exceptional except ε ≤ dN/|F|, matching the
verifier's own "Soundness Error: dN/|EF|" comment) is `OodRomBound`, over this transcript-bound ζ.
-/

namespace Dregg2.Circuit.FriTranscriptBind

open Dregg2.Circuit.FriVerifier

/-- **Derive the OOD point from the transcript prefix.** Observe the prefix (the challenger's absorbed
data up to ζ), then squeeze one extension element. Kept prefix-parametric so `observe(a); observe(b)`
and `observe(a ++ b)` coincide (`observeList` is a left fold — `List.foldl_append`); the deployed order
`observe(trace); observe_slice(public_values)` is exactly `deriveOod … (traceCommit ++ pub.segment)`. -/
def deriveOod {F : Type} [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (initState : List F) (transcriptPrefix : List F) : List F :=
  (Challenger.sampleExt perm RATE 1
    (Challenger.observeList perm RATE (Challenger.init initState) transcriptPrefix)).1

/-- **The transcript-binding check.** The prover's OOD point must EQUAL the one derived from the FAITHFUL
deployed prefix `traceCommit ++ pub.segment` (p3's `observe(commitments.trace)` then
`observe_slice(public_values)` — see the module header). -/
def oodTranscriptCheck {F : Type} [Inhabited F] [DecidableEq F] (perm : List F → List F) (RATE : Nat)
    (initState : List F) (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  decide (proof.oodPoint = deriveOod perm RATE initState (proof.traceCommit ++ pub.segment))

/-- **The transcript-bound verifier.** `verifyAlgo` AND the OOD point is transcript-derived — the
faithful model of the deployed verifier, closing the free-ζ gap. -/
def verifyAlgoTB {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  verifyAlgo perm RATE toNat params vk checks initState logN proof pub
    && oodTranscriptCheck perm RATE initState proof pub

/-- **`verifyAlgoTB` acceptance FORCES the OOD point transcript-bound.** ζ is no longer a free prover
choice: acceptance pins `proof.oodPoint` to `deriveOod` of the trace commitment and public values. -/
theorem verifyAlgoTB_forces_ood_transcript_bound {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoTB perm RATE toNat params vk checks initState logN proof pub = true) :
    proof.oodPoint = deriveOod perm RATE initState (proof.traceCommit ++ pub.segment) := by
  unfold verifyAlgoTB at hacc
  simp only [Bool.and_eq_true] at hacc
  exact of_decide_eq_true hacc.2

/-- **`verifyAlgoTB` is a strengthening.** Whatever it accepts, `verifyAlgo` accepts — so every
existing `verifyAlgo`-soundness theorem transports to `verifyAlgoTB` unchanged. -/
theorem verifyAlgoTB_imp_verifyAlgo {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoTB perm RATE toNat params vk checks initState logN proof pub = true) :
    verifyAlgo perm RATE toNat params vk checks initState logN proof pub = true := by
  unfold verifyAlgoTB at hacc
  simp only [Bool.and_eq_true] at hacc
  exact hacc.1

/-- **The check is LOAD-BEARING (anti-forgery tooth).** A prover-chosen OOD point that differs from the
transcript-derived one is REJECTED — exactly the free-ζ forgery the plain verifier admitted. -/
theorem oodTranscriptCheck_rejects_free_ood {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (initState : List F) (proof : BatchProofData F)
    (pub : WrapPublics F)
    (h : proof.oodPoint ≠ deriveOod perm RATE initState (proof.traceCommit ++ pub.segment)) :
    oodTranscriptCheck perm RATE initState proof pub = false := by
  unfold oodTranscriptCheck
  exact decide_eq_false h

/-- **Non-vacuity (positive): the honest transcript-derived OOD point PASSES.** -/
theorem oodTranscriptCheck_accepts_honest {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (initState : List F) (proof : BatchProofData F)
    (pub : WrapPublics F)
    (h : proof.oodPoint = deriveOod perm RATE initState (proof.traceCommit ++ pub.segment)) :
    oodTranscriptCheck perm RATE initState proof pub = true := by
  unfold oodTranscriptCheck
  exact decide_eq_true h

#assert_axioms deriveOod
#assert_axioms verifyAlgoTB_forces_ood_transcript_bound
#assert_axioms verifyAlgoTB_imp_verifyAlgo
#assert_axioms oodTranscriptCheck_rejects_free_ood
#assert_axioms oodTranscriptCheck_accepts_honest

end Dregg2.Circuit.FriTranscriptBind
