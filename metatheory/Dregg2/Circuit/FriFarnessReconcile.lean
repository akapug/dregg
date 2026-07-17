/-
# `Dregg2.Circuit.FriFarnessReconcile` — RECONCILING the two FRI-farness radii: the bridge's
0-farness (`· ∉ friSetupK8.C`) and `epsQuery`'s δ-far quantitative radius (`farN … (4*d)`).

This is blocker (a)'s LAST residual, named precisely in `WordProofBridgeDeployed`:

> "the `isFar := (· ∉ friSetupK8.C)` used here is 0-farness ("not a codeword"). At the deployed
>  arity-8 unique-decoding radius the embedding's `accept_folds` + `friProximityK8_discharge0`
>  make that event deterministically empty on accepting runs, so `εQuery` here is discharged by
>  the DETERMINISTIC embedding hypothesis, NOT paid probabilistically. Reconciling 0-farness with
>  `epsQuery`'s δ-far quantitative radius (`FriVerifierQuery`) is the residual the compose file's
>  `epsQuery` addend still rests on."

## The two radii, and why they are NOT interchangeable

`FriVerifierQuery.epsilon_query_layer` bounds `Pr[a FAR word passes the k spot-checks]` for a word
that is `farN S.C (4*d) f` — the QUANTITATIVE unique-decoding radius (`> 4*d` disagreements from
EVERY codeword). `WordProofBridgeDeployed.wordProofBridge_of_embedding` produces instead
`isFar := (· ∉ friSetupK8.C)` = `farN friSetupK8.C 0` — 0-farness, i.e. merely "not a codeword".

These differ, and the difference is REAL (§1, `zeroFar_not_imp_udrFar`): a word one symbol away from a
codeword is `∉ C` (0-far) yet `(4*d)`-CLOSE (not `(4*d)`-far) for `d ≥ 1`. So the bridge's 0-far
predicate is STRICTLY WEAKER than `epsQuery`'s `(4*d)`-far one; the implication runs ONLY the strong
⇒ weak way (`farN_imp_not_mem`: `(4*d)`-far ⟹ `∉ C`), never the reverse. A composition that fed the
bridge's 0-far output into `epsQuery`'s `(4*d)`-far precondition WITHOUT the embedding would be FALSE
— `zeroFar_not_imp_udrFar` is the counterexample.

## How they RECONCILE — the deterministic collapse (§2)

Under `DeployedFriEmbedding`, `accept_folds` + the PROVED arity-8 keystone
`friProximityK8_discharge0` force the committed oracle to be a genuine codeword on EVERY accepting
run (`embedding_oracle_mem`: `accept → oracle ∈ friSetupK8.C`). A codeword is `d`-close at every
radius, so `¬ farN friSetupK8.C d (oracle)` for ALL `d` (`embedding_not_far`). Hence BOTH the
bridge's 0-far event AND `epsQuery`'s `(4*d)`-far event are deterministically EMPTY on accepting
runs — so they COINCIDE (`bridge_isFar_iff_epsQuery_far`: `oracle ∉ C ↔ farN … (4*d) oracle`, both
false). That is the reconciliation the compose step consumes: on the deployed embedding the word the
bridge calls "far" (`∉ C`) and the word `epsQuery` calls "δ-far" (`farN (4*d)`) are the SAME
(empty) event, so `epsQuery`'s bound applies to the bridge's event with `Pr = 0`.

## What is PROVEN here vs what STAYS the residual (honest scope)

PROVEN (this file, additive, `#assert_axioms`-clean):
  * radius monotonicity of `closeN`/`farN` (`closeN_mono`, `farN_antitone`) and the strong⇒weak
    implication `farN C (4*d) f → f ∉ C` (`farN_imp_not_mem`);
  * that the converse FAILS — 0-far ↛ `(4*d)`-far — with an explicit witness (`zeroFar_not_imp_udrFar`),
    so the reconciliation is NON-VACUOUS: the embedding hypothesis is load-bearing, without it the two
    radii genuinely disagree;
  * under `DeployedFriEmbedding`, the far-passes event is empty at EVERY radius
    (`embedding_not_far`), so the bridge's 0-far event and `epsQuery`'s `(4*d)`-far event COINCIDE
    (`bridge_isFar_iff_epsQuery_far`, `embedding_far_events_agree`).

STAYS THE RESIDUAL (NAMED, not papered):
  * The reconciliation composes the two radii by DETERMINISTIC COLLAPSE — both far events empty under
    `accept → ∈ C` — NOT by paying `epsQuery`'s `(1−δ)^k` term at a POSITIVE radius. To make `epsQuery`
    pay PROBABILISTICALLY, the embedding's `decode_trace` must fire at the unique-decoding radius
    `d > 0` (i.e. "bundle fails ⟹ `farN friSetupK8.C (4*d) oracle` with `d > 0`"), which needs
    `friProximityK8_discharge` at `d > 0` (its `8²·d = 64·d`-closeness form) wired into a QUANTITATIVE
    `decode_trace` — currently `decode_trace` requires only `oracle ∈ friSetupK8.C` (the `d = 0`
    instance, discharged by `friProximityK8_discharge0`). That positive-radius quantitative decode is
    one residual; the further coupling of the deployed `BatchProof`-space event into the
    oracle-conditioned probability space `H : D → R` of `FriVerifierCompose.friLdtExtractV3_rom_of_legs`
    (blocker (b)'s bias term is closed by `FriQuerySamplingBias`) is the other, separate one.

So the deliverable is exactly: the farness-radius reconciliation the compose file's `epsQuery` addend
rests on — 0-farness and the `(4*d)`-far radius COINCIDE on the deployed embedding — stated at the
real `friSetupK8` code, with the strict-containment non-vacuity that shows why it is not trivial.

## Discipline
Sorry-free; no `axiom`; no `def …Sound`/`…Hard` carrier — the reconciliation is a theorem from the
explicit `DeployedFriEmbedding` hypothesis and the PROVED `friProximityK8_discharge0`. ADDITIVE new
file; all imports read-only; the shared apex modules are untouched.
`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.WordProofBridgeDeployed
import Dregg2.Tactics

namespace Dregg2.Circuit.FriFarnessReconcile

open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriVerifier (verifyAlgo FriParams RecursionVk FriChecks)
open Dregg2.Circuit.CircuitSoundness (Registry BatchPublicInputs BatchProof)
open Dregg2.Circuit.FriFoldArity (friSetupK8 f0 fHon8 f0_not_mem fHon8_mem)
open Dregg2.Circuit.FriBridgeDeployedArity (friProximityK8_discharge0)
open Dregg2.Circuit.DeployedTraceExtract (DeployedFriEmbedding)
open Dregg2.Circuit.FriSoundness
  (closeN farN disagree closeN_zero_iff_mem farN_zero_iff_not_mem)

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1 — the RADIUS relation: `closeN`/`farN` monotonicity, and the strict containment. -/

/-- **Closeness is MONOTONE in the radius.** A word `d`-close at radius `m` is `d`-close at any
larger radius `n ≥ m`: the same codeword witness serves. -/
theorem closeN_mono {C : Submodule F (ι → F)} {m n : ℕ} (hmn : m ≤ n) {f : ι → F}
    (h : closeN C m f) : closeN C n f := by
  obtain ⟨g, hg, hc⟩ := h
  exact ⟨g, hg, hc.trans hmn⟩

/-- **Farness is ANTITONE in the radius.** A word far at a LARGE radius `n` is far at any smaller
radius `m ≤ n` — being `> n` from every codeword is stronger than being `> m`. -/
theorem farN_antitone {C : Submodule F (ι → F)} {m n : ℕ} (hmn : m ≤ n) {f : ι → F}
    (h : farN C n f) : farN C m f := fun hc => h (closeN_mono hmn hc)

/-- **⚑ THE STRONG ⇒ WEAK IMPLICATION.** A word FAR at ANY radius `n` (in particular `epsQuery`'s
`(4*d)` unique-decoding radius) is NOT a codeword — the bridge's `isFar`. So the `(4*d)`-far event
`epsQuery` quantifies is CONTAINED in the bridge's 0-far event `(· ∉ C)`; the reconciliation's
implication runs ONLY this way. -/
theorem farN_imp_not_mem {C : Submodule F (ι → F)} {n : ℕ} {f : ι → F}
    (h : farN C n f) : f ∉ C :=
  farN_zero_iff_not_mem.mp (farN_antitone (Nat.zero_le n) h)

/-- **⚑ `epsQuery`'s δ-far radius ⟹ the bridge's `isFar`, at the deployed shape.** Specialization of
`farN_imp_not_mem` at the unique-decoding radius `4*d`: a word `epsQuery` treats as δ-far is one the
bridge treats as `∉ C`. This is the ONLY direction that holds pointwise. -/
theorem udrFar_imp_notMem {C : Submodule F (ι → F)} {d : ℕ} {f : ι → F}
    (h : farN C (4 * d) f) : f ∉ C :=
  farN_imp_not_mem h

/-! ### Non-vacuity: the CONVERSE FAILS — 0-far does NOT imply `(4*d)`-far. -/

/-- **⚑⚑ THE RECONCILIATION IS NON-VACUOUS — 0-far ↛ `(4*d)`-far.** Over the trivial code
`C = ⊥` on `Fin 2 → ZMod 5`, the weight-1 word `![1, 0]` is 0-FAR (`∉ ⊥`, since `≠ 0`) yet
`(4*1)`-CLOSE (its single disagreement with the codeword `0` is `≤ 4`). So the bridge's 0-far
predicate does NOT imply `epsQuery`'s `(4*d)`-far one: feeding the bridge's `∉ C` output into
`epsQuery`'s `farN (4*d)` precondition WITHOUT the embedding collapse (§2) would be FALSE. This is
exactly why the embedding hypothesis is LOAD-BEARING, and why the reconciliation is not a triviality
— the two radii genuinely differ off the accepting-run set. -/
theorem zeroFar_not_imp_udrFar :
    ∃ f : Fin 2 → ZMod 5,
      farN (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5)) 0 f
        ∧ ¬ farN (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5)) (4 * 1) f := by
  refine ⟨![1, 0], ?_, ?_⟩
  · -- 0-far: `![1,0] ∉ ⊥` because it is `≠ 0`.
    rw [farN_zero_iff_not_mem, Submodule.mem_bot]
    intro h
    have h0 := congrFun h 0
    rw [Matrix.cons_val_zero, Pi.zero_apply] at h0
    exact (by decide : (1 : ZMod 5) ≠ 0) h0
  · -- NOT `(4*1)`-far: it is `4`-close to the codeword `0` (at most `|Fin 2| = 2 ≤ 4` disagreements).
    have hclose : closeN (⊥ : Submodule (ZMod 5) (Fin 2 → ZMod 5)) (4 * 1) ![1, 0] := by
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have h := Finset.card_le_univ
        (disagree (![1, 0] : Fin 2 → ZMod 5) (0 : Fin 2 → ZMod 5))
      rw [Fintype.card_fin] at h
      omega
    exact fun hfar => hfar hclose

/-! ## §2 — the DEPLOYED reconciliation: both far events collapse to EMPTY under the embedding. -/

variable (hash : List Int → Int) (R : Registry)
variable (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
variable (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
variable (initState : List Int) (logN : Nat) (view : ProofView)

/-- **⚑ THE COMMITTED ORACLE IS A CODEWORD ON ACCEPT.** From `DeployedFriEmbedding`: an accepting
run's `accept_folds` (all `8` distinct challenges fold the oracle into `friSetupK8.C'`) plus the
PROVED arity-8 keystone `friProximityK8_discharge0` (0-closeness = membership at unique decoding)
force `oracle pi π ∈ friSetupK8.C`. This is the same load-bearing step
`DeployedTraceExtract.deployedTraceExtract_of_embedding` uses, isolated here as the collapse driver. -/
theorem embedding_oracle_mem
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true) :
    emb.oracle pi π ∈ friSetupK8.C :=
  closeN_zero_iff_mem.mp
    (friProximityK8_discharge0 (emb.chal_inj pi π) (emb.accept_folds pi π hacc))

/-- **⚑ THE FAR-PASSES EVENT IS EMPTY AT EVERY RADIUS.** On an accepting run the committed oracle is
a codeword (`embedding_oracle_mem`), and a codeword is `d`-close at EVERY radius `d` — so it is NEVER
`d`-far, for any `d`. In particular at the bridge's radius `0` AND `epsQuery`'s radius `4*d`: neither
"far" event ever occurs. -/
theorem embedding_not_far
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true)
    (d : ℕ) :
    ¬ farN friSetupK8.C d (emb.oracle pi π) := fun hfar =>
  farN_imp_not_mem hfar
    (embedding_oracle_mem hash R perm RATE toNat params vk checks initState logN view emb pi π hacc)

/-- **⚑⚑ THE RADII COINCIDE ON THE EMBEDDING.** For ANY two radii `d₁ d₂` — in particular the
bridge's `0` and `epsQuery`'s `4*d` — the two far events agree on every accepting run, because BOTH
are empty (`embedding_not_far`). This is the reconciliation: the word the bridge calls far and the
word `epsQuery` calls δ-far are the SAME (empty) event on the deployed embedding. -/
theorem embedding_far_events_agree
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true)
    (d₁ d₂ : ℕ) :
    farN friSetupK8.C d₁ (emb.oracle pi π) ↔ farN friSetupK8.C d₂ (emb.oracle pi π) :=
  ⟨fun h => absurd h
      (embedding_not_far hash R perm RATE toNat params vk checks initState logN view emb pi π hacc d₁),
   fun h => absurd h
      (embedding_not_far hash R perm RATE toNat params vk checks initState logN view emb pi π hacc d₂)⟩

/-- **⚑⚑⚑ THE RECONCILIATION, IN THE TWO FILES' OWN VOCABULARY.** On an accepting run under the
embedding, the bridge's `isFar` (`oracle ∉ friSetupK8.C`, `WordProofBridgeDeployed`) holds iff
`epsQuery`'s δ-far predicate (`farN friSetupK8.C (4*d) oracle`, `FriVerifierQuery.epsilon_query_layer`)
holds — both are FALSE. So the compose file's `epsQuery` addend, quantified at the `(4*d)` radius,
applies to the bridge-produced 0-far event: the two coincide (empty), and `epsQuery` bounds the
bridge event with `Pr = 0`. This is exactly the residual `WordProofBridgeDeployed` names, closed at
the farness-radius level for the deployed `friSetupK8` code. -/
theorem bridge_isFar_iff_epsQuery_far
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true)
    (d : ℕ) :
    emb.oracle pi π ∉ friSetupK8.C ↔ farN friSetupK8.C (4 * d) (emb.oracle pi π) := by
  rw [← farN_zero_iff_not_mem]
  exact embedding_far_events_agree hash R perm RATE toNat params vk checks initState logN view
    emb pi π hacc 0 (4 * d)

/-! ## §3 — TEETH: what would make the reconciliation FALSE, and the predicate is two-valued. -/

/-- **⚑ WHAT WOULD MAKE THE RECONCILIATION FALSE, AND WHY IT CANNOT.** The reconciliation fails at an
accepting run whose committed oracle is `(4*d)`-far (`epsQuery` would fire but the bridge's collapse
would not). Such a run directly refutes `friProximityK8_discharge0`: `farN … (4*d)` gives `oracle ∉ C`
(`farN_imp_not_mem`), yet `accept_folds` + the keystone force `oracle ∈ C`. So the reconciliation's
truth is precisely the PROVED arity-8 proximity — non-vacuous, pinned to a real obligation. -/
theorem embedding_far_oracle_refutes_proximity
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true)
    (d : ℕ)
    (hfar : farN friSetupK8.C (4 * d) (emb.oracle pi π)) :
    False :=
  farN_imp_not_mem hfar
    (embedding_oracle_mem hash R perm RATE toNat params vk checks initState logN view emb pi π hacc)

/-- **`isFar`/δ-far FIRES** — the frequency-8 far word `f0` is 0-far (`∉ friSetupK8.C`). So the
reconciled predicate genuinely takes the "far" value; the far side is inhabited. -/
theorem farN_zero_f0 : farN friSetupK8.C 0 f0 := farN_zero_iff_not_mem.mpr f0_not_mem

/-- **`isFar`/δ-far is REFUTABLE** — the honest degree-`< 8` codeword `fHon8` is NOT 0-far (it IS a
codeword). So the reconciled predicate is not constant-`True`: a real, two-valued statement about the
committed word, not a tautology. -/
theorem not_farN_zero_fHon8 : ¬ farN friSetupK8.C 0 fHon8 := fun h =>
  (farN_zero_iff_not_mem.mp h) fHon8_mem

/-- **A CODEWORD IS FAR AT NO RADIUS.** `fHon8 ∈ friSetupK8.C`, so `¬ farN friSetupK8.C d fHon8` for
every `d` — the honest word is never far, matching the embedding's collapse (`embedding_not_far`)
pointwise on a concrete codeword. -/
theorem not_farN_any_fHon8 (d : ℕ) : ¬ farN friSetupK8.C d fHon8 := fun h =>
  farN_imp_not_mem h fHon8_mem

#assert_axioms closeN_mono
#assert_axioms farN_antitone
#assert_axioms farN_imp_not_mem
#assert_axioms udrFar_imp_notMem
#assert_axioms zeroFar_not_imp_udrFar
#assert_axioms embedding_oracle_mem
#assert_axioms embedding_not_far
#assert_axioms embedding_far_events_agree
#assert_axioms bridge_isFar_iff_epsQuery_far
#assert_axioms embedding_far_oracle_refutes_proximity
#assert_axioms farN_zero_f0
#assert_axioms not_farN_zero_fHon8
#assert_axioms not_farN_any_fHon8

end Dregg2.Circuit.FriFarnessReconcile
