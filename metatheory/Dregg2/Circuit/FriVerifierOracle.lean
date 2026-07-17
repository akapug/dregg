/-
# `Dregg2.Circuit.FriVerifierOracle` — the ORACLE-IZED batch-STARK FRI verifier
(`verifyAlgoO`) and the **faithfulness bridge** to the deployed `verifyAlgo`.

This is **Stage 1** of the FRI-extraction-floor re-basing
(`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5). It is the smallest-first,
purely STRUCTURAL step: no probability, no adversary, no crypto assumption. It does
one thing and proves it: re-express the deployed verifier `verifyAlgo` as an
`OracleComp (List F) (List F) Bool` — a `RomOracle` decision tree that threads every
use of the Poseidon2 permutation `perm` through an oracle QUERY — and prove that
running this oracle version against the concrete permutation-oracle `fun q => perm q`
recovers the deployed `Bool` EXACTLY.

**Why this matters / what it unblocks.** `verifyAlgo` (`FriVerifier.lean:695`) is
parametric in `perm : List F → List F`; every Fiat–Shamir squeeze, every duplex, the
grinding PoW and the query draws flow through that ONE parameter. `verifyAlgoO`
re-interprets that parameter as an oracle rather than a value, so the deployed
verifier becomes the image of an ORACLE ADVERSARY'S acceptance predicate. Stages 2–5
(the FS non-exceptionality terms, Merkle binding, the query-phase composition) all
live downstream of this bridge: they reason about a `QueryBounded` oracle computation,
and this file is what certifies that computation is a CONSERVATIVE image of the real
verifier — the deployed `verifyAlgo` is untouched and recoverable by `eval`.

**The theorem (`verifyAlgoO_run_eq`) is NON-VACUOUS.** `verifyAlgoO` does NOT take
`perm` as a value; it cannot — an `OracleComp` never has the oracle in hand
(`RomOracle.lean:12`). It threads each of the finitely-many permutation applications
through `OracleComp.query`, and the bridge asserts these queries, answered by `perm`,
reassemble into the deployed Boolean. It would be FALSE if `verifyAlgoO` queried the
wrong sponge state at any duplex, threaded the challenger state incorrectly across a
squeeze, mis-ordered the transcript, or combined the answers into a different Boolean:
any such error makes `(verifyAlgoO …).eval perm ≠ verifyAlgo perm …` on some proof.
The per-layer `…O_eval` lemmas (each proven by structural induction / `eval_bind`)
are the audit trail for "the oracle version threads perm at EXACTLY the deployed
call-sites, in the deployed order."

## Axiom hygiene
`#assert_axioms` on the theorems here stays `⊆ {propext, Classical.choice,
Quot.sound}`. No `sorry`, no fresh `axiom`, no `native_decide`. The permutation is
threaded structurally; no cryptographic property of `perm` is used or assumed.
-/
import Dregg2.Circuit.FriVerifier
import Dregg2.Crypto.RomOracle

set_option autoImplicit false

/-! ## 0. `OracleComp` monadic sequencing — `bind` and its run/budget laws.

`RomOracle.OracleComp` is presented as a bare decision tree (`pure`/`query`); to
thread a stateful transcript through it we need sequential composition. `bind`
grafts the continuation onto every leaf of the tree; `eval_bind` says running the
graft equals running the parts in order; `QueryBounded.bind` says query budgets add.
These are the standard free-monad laws, added here (additively, in the RomOracle
namespace) because Stage 1 is their first consumer. -/

namespace Dregg2.Crypto.RomOracle

universe u

/-- Sequential composition of oracle computations: run `m`, then continue with `f` on
its result. Structurally, graft `f` onto every `pure` leaf of `m`. -/
def OracleComp.bind {D R A B : Type} :
    OracleComp D R A → (A → OracleComp D R B) → OracleComp D R B
  | .pure a,    f => f a
  | .query d k, f => .query d (fun r => (k r).bind f)

/-- Running a `bind` runs the parts in order: `eval (m >>= f) H = eval (f (eval m H)) H`.
This is the law the faithfulness bridge is assembled from. -/
theorem OracleComp.eval_bind {D R A B : Type}
    (m : OracleComp D R A) (f : A → OracleComp D R B) (H : D → R) :
    (m.bind f).eval H = (f (m.eval H)).eval H := by
  induction m with
  | pure a => rfl
  | query d k ih =>
      show ((k (H d)).bind f).eval H = (f ((k (H d)).eval H)).eval H
      exact ih (H d)

/-- Query budgets add across a `bind`: `Q`-query `m` then `Q'`-query continuation is a
`(Q + Q')`-query computation. -/
theorem QueryBounded.bind {D R A B : Type} {m : OracleComp D R A}
    {f : A → OracleComp D R B} {n n' : ℕ}
    (hm : QueryBounded n m) (hf : ∀ a, QueryBounded n' (f a)) :
    QueryBounded (n + n') (m.bind f) := by
  induction hm with
  | pure k a =>
      show QueryBounded (k + n') (f a)
      exact (hf a).mono (by omega)
  | query k d κ _ ih =>
      show QueryBounded (k + 1 + n') (OracleComp.query d (fun r => (κ r).bind f))
      have hk : k + 1 + n' = (k + n') + 1 := by omega
      rw [hk]
      exact QueryBounded.query (k + n') d (fun r => (κ r).bind f) (fun r => ih r)

end Dregg2.Crypto.RomOracle

namespace Dregg2.Circuit.FriVerifier

open Dregg2.Crypto.RomOracle

variable {F : Type}

/-- The permutation-oracle computation type: an oracle over sponge states
(`List F → List F`) returning `A`. The single oracle IS the Poseidon2 permutation. -/
abbrev PermComp (F : Type) (A : Type) := OracleComp (List F) (List F) A

/-! ## 1. Oracle-ized challenger primitives — one `query` per `perm` application. -/

/-- Oracle-ized `duplexing`: the single `perm` application becomes ONE oracle query at
the pre-permutation sponge state; the answer `post` is the new state. -/
def Challenger.duplexingO (RATE : Nat) (c : Challenger F) : PermComp F (Challenger F) :=
  .query (c.inputBuffer ++ c.spongeState.drop c.inputBuffer.length)
    (fun post => .pure
      { spongeState := post, inputBuffer := [], outputBuffer := post.take RATE })

/-- Running `duplexingO` against `perm` recovers `duplexing perm`. Definitional. -/
@[simp] theorem Challenger.duplexingO_eval (perm : List F → List F) (RATE : Nat)
    (c : Challenger F) :
    (Challenger.duplexingO RATE c).eval perm = Challenger.duplexing perm RATE c := rfl

/-- Oracle-ized `observe`: at most one query (the conditional duplex); the branch
condition is on the absorb buffer length, independent of any oracle answer. -/
def Challenger.observeO (RATE : Nat) (c : Challenger F) (v : F) : PermComp F (Challenger F) :=
  let c' : Challenger F := { c with outputBuffer := [], inputBuffer := c.inputBuffer ++ [v] }
  if c'.inputBuffer.length = RATE then Challenger.duplexingO RATE c' else .pure c'

/-- Running `observeO` against `perm` recovers `observe perm`. -/
@[simp] theorem Challenger.observeO_eval (perm : List F → List F) (RATE : Nat)
    (c : Challenger F) (v : F) :
    (Challenger.observeO RATE c v).eval perm = Challenger.observe perm RATE c v := by
  unfold Challenger.observeO Challenger.observe
  by_cases h : (({ c with outputBuffer := [], inputBuffer := c.inputBuffer ++ [v] } :
      Challenger F).inputBuffer).length = RATE
  · rw [if_pos h, if_pos h, Challenger.duplexingO_eval]
  · rw [if_neg h, if_neg h]
    rfl

/-- Oracle-ized `observeList`: fold `observeO` left-to-right, sequenced by `bind`. -/
def Challenger.observeListO (RATE : Nat) : Challenger F → List F → PermComp F (Challenger F)
  | c, []      => .pure c
  | c, v :: vs => (Challenger.observeO RATE c v).bind (fun c' => Challenger.observeListO RATE c' vs)

/-- Running `observeListO` against `perm` recovers `observeList perm`. -/
@[simp] theorem Challenger.observeListO_eval (perm : List F → List F) (RATE : Nat) :
    ∀ (c : Challenger F) (vs : List F),
      (Challenger.observeListO RATE c vs).eval perm = Challenger.observeList perm RATE c vs
  | c, [] => rfl
  | c, v :: vs => by
      unfold Challenger.observeListO
      rw [OracleComp.eval_bind, Challenger.observeO_eval,
        Challenger.observeListO_eval perm RATE (Challenger.observe perm RATE c v) vs]
      unfold Challenger.observeList
      rw [List.foldl_cons]

/-- Oracle-ized `sampleBase`: the conditional refill duplex, then read+pop the last
output lane. At most one query. -/
def Challenger.sampleBaseO [Inhabited F] (RATE : Nat) (c : Challenger F) :
    PermComp F (F × Challenger F) :=
  (if c.inputBuffer ≠ [] ∨ c.outputBuffer = [] then Challenger.duplexingO RATE c else .pure c).bind
    (fun c => .pure ((c.outputBuffer.getLast?).getD default,
      { c with outputBuffer := c.outputBuffer.dropLast }))

/-- Running `sampleBaseO` against `perm` recovers `sampleBase perm`. -/
@[simp] theorem Challenger.sampleBaseO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (c : Challenger F) :
    (Challenger.sampleBaseO RATE c).eval perm = Challenger.sampleBase perm RATE c := by
  unfold Challenger.sampleBaseO Challenger.sampleBase
  rw [OracleComp.eval_bind]
  by_cases h : c.inputBuffer ≠ [] ∨ c.outputBuffer = []
  · rw [if_pos h, if_pos h, Challenger.duplexingO_eval]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- Oracle-ized `sampleN`: sample `n` base coefficients in order, sequenced by `bind`. -/
def Challenger.sampleNO [Inhabited F] (RATE : Nat) :
    Nat → Challenger F → PermComp F (List F × Challenger F)
  | 0,     c => .pure ([], c)
  | n + 1, c => (Challenger.sampleBaseO RATE c).bind (fun vc =>
      (Challenger.sampleNO RATE n vc.2).bind (fun vsc =>
        .pure (vc.1 :: vsc.1, vsc.2)))

/-- Running `sampleNO` against `perm` recovers `sampleN perm`. -/
@[simp] theorem Challenger.sampleNO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat) :
    ∀ (n : Nat) (c : Challenger F),
      (Challenger.sampleNO RATE n c).eval perm = Challenger.sampleN perm RATE n c
  | 0, c => rfl
  | n + 1, c => by
      unfold Challenger.sampleNO Challenger.sampleN
      rw [OracleComp.eval_bind, Challenger.sampleBaseO_eval, OracleComp.eval_bind,
        Challenger.sampleNO_eval perm RATE n]
      rfl

/-- Oracle-ized `sampleExt`. -/
def Challenger.sampleExtO [Inhabited F] (RATE : Nat) (D : Nat) (c : Challenger F) :
    PermComp F (List F × Challenger F) :=
  Challenger.sampleNO RATE D c

/-- Running `sampleExtO` against `perm` recovers `sampleExt perm`. -/
@[simp] theorem Challenger.sampleExtO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (D : Nat) (c : Challenger F) :
    (Challenger.sampleExtO RATE D c).eval perm = Challenger.sampleExt perm RATE D c :=
  Challenger.sampleNO_eval perm RATE D c

/-- Oracle-ized `sampleBits`. -/
def Challenger.sampleBitsO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (bits : Nat)
    (c : Challenger F) : PermComp F (Nat × Challenger F) :=
  (Challenger.sampleBaseO RATE c).bind (fun vc => .pure (toNat vc.1 % (2 ^ bits), vc.2))

/-- Running `sampleBitsO` against `perm` recovers `sampleBits perm`. -/
@[simp] theorem Challenger.sampleBitsO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (toNat : F → Nat) (bits : Nat) (c : Challenger F) :
    (Challenger.sampleBitsO RATE toNat bits c).eval perm
      = Challenger.sampleBits perm RATE toNat bits c := by
  unfold Challenger.sampleBitsO Challenger.sampleBits
  rw [OracleComp.eval_bind, Challenger.sampleBaseO_eval]
  rfl

/-! ## 2. Oracle-ized transcript stages. -/

/-- Oracle-ized FRI commit-phase fold: observe each fold-layer commitment, squeeze one
beta, accumulate — the monadic mirror of `deriveFri`'s `foldl` step. -/
def deriveFriFoldO [Inhabited F] (RATE : Nat) (params : FriParams) :
    List (List F) → (List (List F) × Challenger F) → PermComp F (List (List F) × Challenger F)
  | [],          acc => .pure acc
  | comm :: rest, acc =>
      (Challenger.observeListO RATE acc.2 comm).bind (fun c =>
        (Challenger.sampleExtO RATE params.extDeg c).bind (fun bc =>
          deriveFriFoldO RATE params rest (acc.1 ++ [bc.1], bc.2)))

/-- The oracle fold agrees with `deriveFri`'s inner `foldl` on the concrete permutation. -/
theorem deriveFriFoldO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (params : FriParams) :
    ∀ (comms : List (List F)) (acc : List (List F) × Challenger F),
      (deriveFriFoldO RATE params comms acc).eval perm
        = comms.foldl
            (fun (ac : List (List F) × Challenger F) (comm : List F) =>
              let c := Challenger.observeList perm RATE ac.2 comm
              let bc := Challenger.sampleExt perm RATE params.extDeg c
              (ac.1 ++ [bc.1], bc.2)) acc
  | [], acc => rfl
  | comm :: rest, acc => by
      unfold deriveFriFoldO
      rw [OracleComp.eval_bind, Challenger.observeListO_eval, OracleComp.eval_bind,
        Challenger.sampleExtO_eval, deriveFriFoldO_eval perm RATE params rest]
      rfl

/-- Oracle-ized `deriveFri`. -/
def deriveFriO [Inhabited F] (RATE : Nat) (params : FriParams) (proof : BatchProofData F)
    (c0 : Challenger F) : PermComp F (List (List F) × Challenger F) :=
  (deriveFriFoldO RATE params proof.friCommitments ([], c0)).bind (fun bc =>
    (Challenger.observeListO RATE bc.2 proof.finalPoly).bind (fun c => .pure (bc.1, c)))

/-- Running `deriveFriO` against `perm` recovers `deriveFri perm`. -/
@[simp] theorem deriveFriO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (params : FriParams) (proof : BatchProofData F) (c0 : Challenger F) :
    (deriveFriO RATE params proof c0).eval perm = deriveFri perm RATE params proof c0 := by
  unfold deriveFriO deriveFri
  rw [OracleComp.eval_bind, deriveFriFoldO_eval, OracleComp.eval_bind,
    Challenger.observeListO_eval]
  rfl

/-- Oracle-ized `drawQueries`. -/
def drawQueriesO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (logN : Nat) :
    Nat → Challenger F → PermComp F (List Nat × Challenger F)
  | 0,     c => .pure ([], c)
  | n + 1, c => (Challenger.sampleBitsO RATE toNat logN c).bind (fun ic =>
      (drawQueriesO RATE toNat logN n ic.2).bind (fun rc =>
        .pure (ic.1 :: rc.1, rc.2)))

/-- Running `drawQueriesO` against `perm` recovers `drawQueries perm`. -/
@[simp] theorem drawQueriesO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (toNat : F → Nat) (logN : Nat) :
    ∀ (n : Nat) (c : Challenger F),
      (drawQueriesO RATE toNat logN n c).eval perm = drawQueries perm RATE toNat logN n c
  | 0, c => rfl
  | n + 1, c => by
      unfold drawQueriesO drawQueries
      rw [OracleComp.eval_bind, Challenger.sampleBitsO_eval, OracleComp.eval_bind,
        drawQueriesO_eval perm RATE toNat logN n]
      rfl

/-- Oracle-ized `deriveQueryIndices`. -/
def deriveQueryIndicesO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (logN : Nat) (c0 : Challenger F) : PermComp F (List Nat × Challenger F) :=
  drawQueriesO RATE toNat logN params.numQueries c0

/-- Running `deriveQueryIndicesO` against `perm` recovers `deriveQueryIndices perm`. -/
@[simp] theorem deriveQueryIndicesO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (toNat : F → Nat) (params : FriParams) (logN : Nat) (c0 : Challenger F) :
    (deriveQueryIndicesO RATE toNat params logN c0).eval perm
      = deriveQueryIndices perm RATE toNat params logN c0 :=
  drawQueriesO_eval perm RATE toNat logN params.numQueries c0

/-- Oracle-ized `deriveQueryPow`. -/
def deriveQueryPowO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (powBits : Nat)
    (witness : List F) (c : Challenger F) : PermComp F (Option Nat × Challenger F) :=
  match witness with
  | [w] =>
      if powBits = 0 then .pure (some 0, c)
      else (Challenger.observeO RATE c w).bind (fun c =>
        (Challenger.sampleBitsO RATE toNat powBits c).bind (fun mc =>
          .pure (some mc.1, mc.2)))
  | _ => .pure (none, c)

/-- Running `deriveQueryPowO` against `perm` recovers `deriveQueryPow perm`. -/
@[simp] theorem deriveQueryPowO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (toNat : F → Nat) (powBits : Nat) (witness : List F) (c : Challenger F) :
    (deriveQueryPowO RATE toNat powBits witness c).eval perm
      = deriveQueryPow perm RATE toNat powBits witness c := by
  rcases witness with _ | ⟨w, _ | ⟨w2, rest⟩⟩
  · rfl
  · simp only [deriveQueryPowO, deriveQueryPow]
    by_cases h : powBits = 0
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h, OracleComp.eval_bind, Challenger.observeO_eval,
        OracleComp.eval_bind, Challenger.sampleBitsO_eval]; rfl
  · rfl

/-! ## 3. The oracle-ized transcript and verifier. -/

/-- **Oracle-ized `deriveTranscript`.** Every `perm` application in the deployed
one-thread transcript is threaded through an oracle query, in the deployed order; the
`DerivedChallenges` record is assembled from the sequenced results. -/
def deriveTranscriptO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    PermComp F (DerivedChallenges F) :=
  (Challenger.observeListO RATE (Challenger.init initState) proof.degreeBitsPreamble).bind (fun c =>
  (Challenger.observeListO RATE c proof.baseDegreeBitsPreamble).bind (fun c =>
  (Challenger.observeListO RATE c proof.preprocessedWidthPreamble).bind (fun c =>
    let postPreamble := c
  (Challenger.observeListO RATE c proof.traceCommit).bind (fun c =>
  (Challenger.observeListO RATE c proof.preprocessedCommit).bind (fun c =>
  (Challenger.observeListO RATE c pub.segment).bind (fun c =>
  (Challenger.sampleExtO RATE params.extDeg c).bind (fun caC =>
    let constraintAlpha := caC.1
    let postConstraintAlpha := caC.2
  (Challenger.observeListO RATE caC.2 proof.quotientCommit).bind (fun c =>
  (Challenger.sampleExtO RATE params.extDeg c).bind (fun zC =>
    let zeta := zC.1
    let postZeta := zC.2
  (Challenger.observeListO RATE zC.2 proof.openedEvaluations).bind (fun c =>
  (Challenger.sampleExtO RATE params.extDeg c).bind (fun oaC =>
    let openingAlpha := oaC.1
    let postOpeningAlpha := oaC.2
  (deriveFriO RATE params proof oaC.2).bind (fun bC =>
    let betas := bC.1
  (Challenger.observeListO RATE bC.2 proof.friLogArities).bind (fun c =>
    let postFri := c
  (deriveQueryPowO RATE toNat params.powBits proof.powWitness c).bind (fun pC =>
    let powSample := pC.1
    let postPow := pC.2
  (deriveQueryIndicesO RATE toNat params logN pC.2).bind (fun qC =>
    .pure
      { constraintAlpha := constraintAlpha, ζ := zeta, openingAlpha := openingAlpha,
        betas := betas, powSample := powSample, qidx := qC.1,
        postPreamble := postPreamble, postConstraintAlpha := postConstraintAlpha,
        postZeta := postZeta, postOpeningAlpha := postOpeningAlpha,
        postFri := postFri, postPow := postPow })))))))))))))))

/-- Running `deriveTranscriptO` against `perm` recovers `deriveTranscript perm`. -/
@[simp] theorem deriveTranscriptO_eval [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (toNat : F → Nat) (params : FriParams) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) :
    (deriveTranscriptO RATE toNat params initState logN proof pub).eval perm
      = deriveTranscript perm RATE toNat params initState logN proof pub := by
  unfold deriveTranscriptO deriveTranscript
  simp only [OracleComp.eval_bind, Challenger.observeListO_eval, Challenger.sampleExtO_eval,
    deriveFriO_eval, deriveQueryPowO_eval, deriveQueryIndicesO_eval, OracleComp.eval_pure]

/-- **`verifyAlgoO` — the oracle-ized batch-STARK FRI verifier.** Identical structure
to `verifyAlgo` (`FriVerifier.lean:695`): derive the transcript (now oracle-threaded),
then combine the three teeth and the `FriChecks` bundle into the accept `Bool`. The
`perm` parameter is GONE — it lives only in the oracle answered by `eval`. -/
def verifyAlgoO [Inhabited F] [DecidableEq F]
    (RATE : Nat) (toNat : F → Nat) (params : FriParams) (vk : RecursionVk F)
    (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : PermComp F Bool :=
  (deriveTranscriptO RATE toNat params initState logN proof pub).bind (fun d =>
    .pure
      (vk.shapeMatches proof
        && checks.foldConsistent proof d.betas d.qidx
        && checks.merklePaths proof d.qidx
        && checks.batchTables proof d.betas
        && checks.queryPow proof
        && segmentTooth proof pub))

/-- **⚑ THE FAITHFULNESS BRIDGE (Stage 1).** Running the oracle-ized verifier against
the concrete permutation-oracle `perm` recovers the deployed `verifyAlgo` Boolean —
EXACTLY, on every supplied proof/public pair. The oracle re-basing is CONSERVATIVE:
the deployed verifier is untouched and is the `eval`-image of `verifyAlgoO`.

NON-VACUITY: `verifyAlgoO` does not receive `perm` as a value; it threads each of the
finitely-many permutation applications through `OracleComp.query`. The statement is
false if any query targets the wrong sponge state, the challenger state is threaded
incorrectly across any squeeze, the transcript order differs, or the answers are
recombined into a different Boolean — every such defect changes `.eval perm` on some
input. (Cf. the per-stage `…O_eval` lemmas, each a structural induction.) -/
theorem verifyAlgoO_run_eq [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) :
    (verifyAlgoO RATE toNat params vk checks initState logN proof pub).eval perm
      = verifyAlgo perm RATE toNat params vk checks initState logN proof pub := by
  unfold verifyAlgoO verifyAlgo
  rw [OracleComp.eval_bind, deriveTranscriptO_eval]
  rfl

/-! ## 4. `verifyAlgoO` is a genuine query-bounded oracle adversary.

The whole point of the re-basing is that `verifyAlgoO` is a `RomEff`-style member: a
computation that learns the permutation ONLY by querying it, a bounded number of times
along every path. We record here that it IS query-bounded — witnessing that the
faithful image is a legitimate oracle adversary, not a computation that reads the whole
oracle. (An explicit closed-form query count is Stage 1's optional refinement; the
existential already certifies membership in the bounded class.) -/

/-- Each oracle-ized challenger primitive is query-bounded (structural, over all
answers). `observeO`/`sampleBaseO` cost at most one query; `observeListO`/`sampleNO`
at most the length/count. -/
theorem Challenger.duplexingO_queryBounded (RATE : Nat) (c : Challenger F) :
    QueryBounded 1 (Challenger.duplexingO RATE c) := by
  unfold Challenger.duplexingO
  exact QueryBounded.query 0 _ _ (fun _ => QueryBounded.pure 0 _)

theorem Challenger.observeO_queryBounded (RATE : Nat) (c : Challenger F) (v : F) :
    QueryBounded 1 (Challenger.observeO RATE c v) := by
  unfold Challenger.observeO
  by_cases h : (({ c with outputBuffer := [], inputBuffer := c.inputBuffer ++ [v] } :
      Challenger F).inputBuffer).length = RATE
  · rw [if_pos h]; exact Challenger.duplexingO_queryBounded RATE _
  · rw [if_neg h]; exact (QueryBounded.pure 0 _).mono (by omega)

theorem Challenger.observeListO_queryBounded (RATE : Nat) :
    ∀ (c : Challenger F) (vs : List F),
      QueryBounded vs.length (Challenger.observeListO RATE c vs)
  | c, [] => QueryBounded.pure 0 c
  | c, v :: vs => by
      show QueryBounded (v :: vs).length
        ((Challenger.observeO RATE c v).bind (fun c' => Challenger.observeListO RATE c' vs))
      have hlen : (v :: vs).length = 1 + vs.length := by simp [Nat.add_comm]
      rw [hlen]
      exact QueryBounded.bind (Challenger.observeO_queryBounded RATE c v)
        (fun c' => Challenger.observeListO_queryBounded RATE c' vs)

theorem Challenger.sampleBaseO_queryBounded [Inhabited F] (RATE : Nat) (c : Challenger F) :
    QueryBounded 1 (Challenger.sampleBaseO RATE c) := by
  unfold Challenger.sampleBaseO
  have hif : QueryBounded 1
      (if c.inputBuffer ≠ [] ∨ c.outputBuffer = [] then Challenger.duplexingO RATE c
        else (OracleComp.pure c : PermComp F (Challenger F))) := by
    by_cases h : c.inputBuffer ≠ [] ∨ c.outputBuffer = []
    · rw [if_pos h]; exact Challenger.duplexingO_queryBounded RATE c
    · rw [if_neg h]; exact (QueryBounded.pure 0 c).mono (by omega)
  exact QueryBounded.bind hif (fun cc => QueryBounded.pure 0 _)

theorem Challenger.sampleNO_queryBounded [Inhabited F] (RATE : Nat) :
    ∀ (n : Nat) (c : Challenger F), QueryBounded n (Challenger.sampleNO RATE n c)
  | 0, c => QueryBounded.pure 0 ([], c)
  | n + 1, c => by
      show QueryBounded (n + 1)
        ((Challenger.sampleBaseO RATE c).bind (fun vc =>
          (Challenger.sampleNO RATE n vc.2).bind (fun vsc => OracleComp.pure (vc.1 :: vsc.1, vsc.2))))
      rw [show n + 1 = 1 + n from by omega]
      exact QueryBounded.bind (Challenger.sampleBaseO_queryBounded RATE c)
        (fun vc => QueryBounded.bind (Challenger.sampleNO_queryBounded RATE n vc.2)
          (fun vsc => QueryBounded.pure 0 _))

theorem Challenger.sampleExtO_queryBounded [Inhabited F] (RATE : Nat) (D : Nat) (c : Challenger F) :
    QueryBounded D (Challenger.sampleExtO RATE D c) :=
  Challenger.sampleNO_queryBounded RATE D c

theorem Challenger.sampleBitsO_queryBounded [Inhabited F] (RATE : Nat) (toNat : F → Nat)
    (bits : Nat) (c : Challenger F) :
    QueryBounded 1 (Challenger.sampleBitsO RATE toNat bits c) := by
  unfold Challenger.sampleBitsO
  exact QueryBounded.bind (Challenger.sampleBaseO_queryBounded RATE c)
    (fun vc => QueryBounded.pure 0 _)

/-- The oracle FRI fold's query budget: for each layer, `comm.length` absorbs plus
`extDeg` squeezes. -/
theorem deriveFriFoldO_queryBounded [Inhabited F] (RATE : Nat) (params : FriParams) :
    ∀ (comms : List (List F)) (acc : List (List F) × Challenger F),
      QueryBounded ((comms.map (fun comm => comm.length + params.extDeg)).sum)
        (deriveFriFoldO RATE params comms acc)
  | [], acc => QueryBounded.pure 0 acc
  | comm :: rest, acc => by
      show QueryBounded (((comm :: rest).map (fun comm => comm.length + params.extDeg)).sum)
        ((Challenger.observeListO RATE acc.2 comm).bind (fun c =>
          (Challenger.sampleExtO RATE params.extDeg c).bind (fun bc =>
            deriveFriFoldO RATE params rest (acc.1 ++ [bc.1], bc.2))))
      rw [List.map_cons, List.sum_cons, Nat.add_assoc]
      exact QueryBounded.bind (Challenger.observeListO_queryBounded RATE acc.2 comm)
        (fun c => QueryBounded.bind (Challenger.sampleExtO_queryBounded RATE params.extDeg c)
          (fun bc => deriveFriFoldO_queryBounded RATE params rest (acc.1 ++ [bc.1], bc.2)))

theorem deriveFriO_queryBounded [Inhabited F] (RATE : Nat) (params : FriParams)
    (proof : BatchProofData F) (c0 : Challenger F) :
    QueryBounded
      ((proof.friCommitments.map (fun comm => comm.length + params.extDeg)).sum
        + proof.finalPoly.length)
      (deriveFriO RATE params proof c0) := by
  unfold deriveFriO
  exact QueryBounded.bind (deriveFriFoldO_queryBounded RATE params proof.friCommitments ([], c0))
    (fun bc => QueryBounded.bind (Challenger.observeListO_queryBounded RATE bc.2 proof.finalPoly)
      (fun c => QueryBounded.pure 0 _))

theorem drawQueriesO_queryBounded [Inhabited F] (RATE : Nat) (toNat : F → Nat) (logN : Nat) :
    ∀ (n : Nat) (c : Challenger F), QueryBounded n (drawQueriesO RATE toNat logN n c)
  | 0, c => QueryBounded.pure 0 ([], c)
  | n + 1, c => by
      show QueryBounded (n + 1)
        ((Challenger.sampleBitsO RATE toNat logN c).bind (fun ic =>
          (drawQueriesO RATE toNat logN n ic.2).bind (fun rc => OracleComp.pure (ic.1 :: rc.1, rc.2))))
      rw [show n + 1 = 1 + n from by omega]
      exact QueryBounded.bind (Challenger.sampleBitsO_queryBounded RATE toNat logN c)
        (fun ic => QueryBounded.bind (drawQueriesO_queryBounded RATE toNat logN n ic.2)
          (fun rc => QueryBounded.pure 0 _))

theorem deriveQueryIndicesO_queryBounded [Inhabited F] (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (logN : Nat) (c0 : Challenger F) :
    QueryBounded params.numQueries (deriveQueryIndicesO RATE toNat params logN c0) :=
  drawQueriesO_queryBounded RATE toNat logN params.numQueries c0

theorem deriveQueryPowO_queryBounded [Inhabited F] (RATE : Nat) (toNat : F → Nat) (powBits : Nat)
    (witness : List F) (c : Challenger F) :
    QueryBounded 2 (deriveQueryPowO RATE toNat powBits witness c) := by
  rcases witness with _ | ⟨w, _ | ⟨w2, rest⟩⟩
  · exact (QueryBounded.pure 0 _).mono (by omega)
  · simp only [deriveQueryPowO]
    by_cases h : powBits = 0
    · rw [if_pos h]; exact (QueryBounded.pure 0 _).mono (by omega)
    · rw [if_neg h]
      exact QueryBounded.bind (Challenger.observeO_queryBounded RATE c w)
        (fun c => QueryBounded.bind (Challenger.sampleBitsO_queryBounded RATE toNat powBits c)
          (fun mc => QueryBounded.pure 0 _))
  · exact (QueryBounded.pure 0 _).mono (by omega)

/-- **`verifyAlgoO` is a genuine query-bounded oracle adversary.** An explicit finite
`Q` (a closed arithmetic function of the proof shape) bounds its permutation queries
along EVERY path — witnessing that the faithful image learns `perm` ONLY by querying
it a bounded number of times (a `RomEff`-style member), never by reading the whole
oracle. This is the non-vacuous sense in which `verifyAlgoO` is an oracle ADVERSARY. -/
theorem verifyAlgoO_queryBounded [Inhabited F] [DecidableEq F]
    (RATE : Nat) (toNat : F → Nat) (params : FriParams) (vk : RecursionVk F)
    (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) :
    ∃ Q, QueryBounded Q (verifyAlgoO RATE toNat params vk checks initState logN proof pub) :=
  ⟨_, by
  unfold verifyAlgoO deriveTranscriptO
  exact
    QueryBounded.bind
      (QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.sampleExtO_queryBounded RATE _ _) (fun caC =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.sampleExtO_queryBounded RATE _ _) (fun zC =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (Challenger.sampleExtO_queryBounded RATE _ _) (fun oaC =>
       QueryBounded.bind (deriveFriO_queryBounded RATE _ _ _) (fun bC =>
       QueryBounded.bind (Challenger.observeListO_queryBounded RATE _ _) (fun c =>
       QueryBounded.bind (deriveQueryPowO_queryBounded RATE _ _ _ _) (fun pC =>
       QueryBounded.bind (deriveQueryIndicesO_queryBounded RATE _ _ _ _) (fun qC =>
         QueryBounded.pure 0 _))))))))))))))))
      (fun d => QueryBounded.pure 0 _)⟩

#assert_axioms verifyAlgoO_run_eq
#assert_axioms verifyAlgoO_queryBounded
#assert_axioms deriveTranscriptO_eval

end Dregg2.Circuit.FriVerifier
