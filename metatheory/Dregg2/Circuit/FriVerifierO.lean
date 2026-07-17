import Dregg2.Circuit.FriVerifier
import Dregg2.Crypto.RomOracle
import Dregg2.Tactics
import Mathlib.Tactic

/-
# `Dregg2.Circuit.FriVerifierO` — the FAITHFULNESS BRIDGE (FRI-soundness re-basing, Stage 1).

`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5 Stage 1. The deployed `verifyAlgo`
(`FriVerifier.lean:695`) is a `Bool`-valued function of a *supplied* proof at a FIXED concrete
permutation `perm : List F → List F`; every use of `perm` flows through `deriveTranscript`
(the Fiat–Shamir observe/squeeze thread). §4.2's fortunate fact: because `verifyAlgo` is
PARAMETRIC in `perm`, the random-oracle re-basing is a RE-INTERPRETATION, not a rewrite.

This file gives the oracle image `verifyAlgoO` over `RomOracle.OracleComp (List F) (List F)`
(domain = range = the sponge state), and the three Stage-1 deliverables — all PURELY
STRUCTURAL (no probability, no crypto; those are Stages 2–4):

  1. `verifyAlgoO` — the same verifier with each `perm x` lifted to `OracleComp.query x (fun r ⇒ …)`.
  2. `verifyAlgoO_run_eq` — THE FAITHFULNESS THEOREM: running the oracle version against the
     deterministic `perm`-oracle recovers the deployed `Bool`
     (`(verifyAlgoO …).eval perm = verifyAlgo perm …`). This is the proof that the re-basing is
     CONSERVATIVE: the deployed verifier is untouched and recoverable.
  3. `permCallCount` (an explicit arithmetic UPPER bound on the permutation calls, read off the
     proof shape) + `verifyAlgoO_queryBounded : QueryBounded (verifyAlgoO …) (permCallCount …)`.

⚑ FAITHFULNESS NOTE. In `verifyAlgo`, `perm` appears ONLY inside `deriveTranscript`; the per-query
FRI/Merkle recomputes use `FriCore.compress` carried in the `checks : FriChecks F` bundle, a
SEPARATE parameter that is not `perm`. So `verifyAlgoO` keeps `checks` intact and lifts only the
transcript's permutation calls — the mirror had NOWHERE to differ from `verifyAlgo` beyond
`perm x ↦ query x`. `permCallCount` therefore counts only the transcript's observe/squeeze
permutations (each `observe`/`sampleBase` is at most one `perm` call — the bound is an
over-approximation, which is all `QueryBounded`, a per-path upper bound, requires).

⚑ ADDITIVE. This file modifies NO deployed spec or proof: `verifyAlgo`, `deriveTranscript`,
`fullChecks`, `FriLdtExtractV3`, the Poseidon2 model — all untouched. Stage 2 (the FS-terms
ε-bound) consumes `verifyAlgoO`, the query budget, and the faithfulness lemma from here.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace Dregg2.Circuit.FriVerifierO

open Dregg2.Crypto.RomOracle
open Dregg2.Circuit.FriVerifier

set_option autoImplicit false

universe u

variable {F : Type}

/-- The permutation-oracle computation: an `OracleComp` whose one oracle has domain = range = the
sponge state `List F`. The oracle is the Poseidon2 permutation, queried rather than applied. -/
abbrev PermOC (F : Type) (A : Type) : Type := OracleComp (List F) (List F) A

/-! ## Monadic glue on `OracleComp` (additive; `RomOracle` untouched).

`RomOracle.OracleComp` exposes only `pure`/`query`; `obind` is the sequencing that lets the mirror
thread the challenger state through the queries. Its `eval`/`QueryBounded` laws are the two facts
every downstream lemma uses. -/

/-- Monadic bind for `OracleComp`: run `m`, feed its result to `f`. -/
def obind {D R A B : Type} : OracleComp D R A → (A → OracleComp D R B) → OracleComp D R B
  | .pure a,    f => f a
  | .query d k, f => .query d (fun r => obind (k r) f)

/-- Running a bind: `eval` distributes through `obind` — the result of `m` under `H` is fed to `f`,
whose continuation is then run under the SAME `H`. -/
theorem obind_eval {D R A B : Type} (m : OracleComp D R A) (f : A → OracleComp D R B) (H : D → R) :
    (obind m f).eval H = (f (m.eval H)).eval H := by
  induction m with
  | pure a => rfl
  | query d k ih =>
      show (obind (k (H d)) f).eval H = (f ((k (H d)).eval H)).eval H
      exact ih (H d)

/-- The bind's query budget is the sum: `m`'s budget plus the continuation's (uniform over the
result). This is the compositional law `permCallCount` is assembled from. -/
theorem queryBounded_obind {D R A B : Type} {m : OracleComp D R A} {f : A → OracleComp D R B}
    {n k : ℕ} (hm : QueryBounded n m) (hf : ∀ a, QueryBounded k (f a)) :
    QueryBounded (n + k) (obind m f) := by
  induction hm with
  | pure n' a => exact (hf a).mono (by omega)
  | query n' d kk _ ih =>
      show QueryBounded (n' + 1 + k) (OracleComp.query d (fun r => obind (kk r) f))
      have hcast : n' + 1 + k = (n' + k) + 1 := by omega
      rw [hcast]
      exact QueryBounded.query _ d _ (fun r => ih r)

/-- Push `eval` through an `if` — the guard is oracle-independent, so it commutes with the run. -/
theorem ite_eval {D R A : Type} (P : Prop) [Decidable P] (a b : OracleComp D R A) (H : D → R) :
    (if P then a else b).eval H = if P then a.eval H else b.eval H := by
  by_cases h : P <;> simp [h]

/-! ## 1. The oracle-lifted challenger operations.

Each mirrors the deployed `Challenger` op verbatim, replacing the single `perm _` with a
`query _`. The `_eval` lemma for each proves running it against `perm` recovers the deployed op;
the `_qb` lemma bounds its permutation calls. -/

/-- `duplexing`, oracle-lifted: query the permutation at the overwritten sponge preimage. -/
def duplexingO (RATE : Nat) (c : Challenger F) : PermOC F (Challenger F) :=
  let preperm := c.inputBuffer ++ c.spongeState.drop c.inputBuffer.length
  .query preperm (fun post =>
    .pure { spongeState := post, inputBuffer := [], outputBuffer := post.take RATE })

theorem duplexingO_eval (RATE : Nat) (c : Challenger F) (perm : List F → List F) :
    (duplexingO RATE c).eval perm = Challenger.duplexing perm RATE c := rfl

theorem duplexingO_qb (RATE : Nat) (c : Challenger F) :
    QueryBounded 1 (duplexingO RATE c) :=
  QueryBounded.query 0 _ _ (fun _post => QueryBounded.pure 0 _)

/-- `observe`, oracle-lifted. -/
def observeO (RATE : Nat) (c : Challenger F) (v : F) : PermOC F (Challenger F) :=
  let c' : Challenger F := { c with outputBuffer := [], inputBuffer := c.inputBuffer ++ [v] }
  if c'.inputBuffer.length = RATE then duplexingO RATE c' else .pure c'

theorem observeO_eval (RATE : Nat) (c : Challenger F) (v : F) (perm : List F → List F) :
    (observeO RATE c v).eval perm = Challenger.observe perm RATE c v := by
  unfold observeO Challenger.observe
  rw [ite_eval, duplexingO_eval, OracleComp.eval_pure]

theorem observeO_qb (RATE : Nat) (c : Challenger F) (v : F) :
    QueryBounded 1 (observeO RATE c v) := by
  dsimp only [observeO]
  split_ifs with h
  · exact duplexingO_qb RATE _
  · exact QueryBounded.pure 1 _

/-- `observeList`, oracle-lifted: thread `observeO` left to right. -/
def observeListO (RATE : Nat) (c : Challenger F) (vs : List F) : PermOC F (Challenger F) :=
  match vs with
  | [] => .pure c
  | v :: rest => obind (observeO RATE c v) (fun c' => observeListO RATE c' rest)

theorem observeListO_eval (RATE : Nat) (perm : List F → List F) :
    ∀ (vs : List F) (c : Challenger F),
      (observeListO RATE c vs).eval perm = Challenger.observeList perm RATE c vs := by
  intro vs
  induction vs with
  | nil => intro c; rfl
  | cons v rest ih =>
      intro c
      show (obind (observeO RATE c v) (fun c' => observeListO RATE c' rest)).eval perm
        = Challenger.observeList perm RATE c (v :: rest)
      rw [obind_eval, observeO_eval, ih]
      simp only [Challenger.observeList, List.foldl_cons]

theorem observeListO_qb (RATE : Nat) :
    ∀ (c : Challenger F) (vs : List F), QueryBounded vs.length (observeListO RATE c vs) := by
  intro c vs
  induction vs generalizing c with
  | nil => exact QueryBounded.pure 0 _
  | cons v rest ih =>
      show QueryBounded (v :: rest).length
        (obind (observeO RATE c v) (fun c' => observeListO RATE c' rest))
      have h := queryBounded_obind (observeO_qb RATE c v) (fun c' => ih c')
      simpa [List.length_cons, Nat.add_comm] using h

/-- `sampleBase`, oracle-lifted: duplex if needed (one query), then pop the last output lane. -/
def sampleBaseO [Inhabited F] (RATE : Nat) (c0 : Challenger F) : PermOC F (F × Challenger F) :=
  obind (if c0.inputBuffer ≠ [] ∨ c0.outputBuffer = [] then duplexingO RATE c0 else .pure c0)
    (fun c => .pure ((c.outputBuffer.getLast?).getD default,
                     { c with outputBuffer := c.outputBuffer.dropLast }))

theorem sampleBaseO_eval [Inhabited F] (RATE : Nat) (c0 : Challenger F) (perm : List F → List F) :
    (sampleBaseO RATE c0).eval perm = Challenger.sampleBase perm RATE c0 := by
  unfold sampleBaseO Challenger.sampleBase
  simp only [obind_eval, ite_eval, duplexingO_eval, OracleComp.eval_pure]

theorem sampleBaseO_qb [Inhabited F] (RATE : Nat) (c0 : Challenger F) :
    QueryBounded 1 (sampleBaseO RATE c0) := by
  unfold sampleBaseO
  refine queryBounded_obind (n := 1) (k := 0) ?_ (fun _ => QueryBounded.pure 0 _)
  split_ifs
  · exact duplexingO_qb RATE _
  · exact QueryBounded.pure 1 _

/-- `sampleN`, oracle-lifted. -/
def sampleNO [Inhabited F] (RATE : Nat) : Nat → Challenger F → PermOC F (List F × Challenger F)
  | 0,     c => .pure ([], c)
  | (n+1), c =>
      obind (sampleBaseO RATE c) (fun p =>
        obind (sampleNO RATE n p.2) (fun q =>
          .pure (p.1 :: q.1, q.2)))

theorem sampleNO_eval [Inhabited F] (RATE : Nat) (perm : List F → List F) :
    ∀ (n : Nat) (c : Challenger F),
      (sampleNO RATE n c).eval perm = Challenger.sampleN perm RATE n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ k ih =>
      intro c
      show (obind (sampleBaseO RATE c) (fun p =>
              obind (sampleNO RATE k p.2) (fun q => .pure (p.1 :: q.1, q.2)))).eval perm
        = Challenger.sampleN perm RATE (k + 1) c
      simp only [obind_eval, sampleBaseO_eval, ih, OracleComp.eval_pure]
      rfl

theorem sampleNO_qb [Inhabited F] (RATE : Nat) :
    ∀ (n : Nat) (c : Challenger F), QueryBounded n (sampleNO RATE n c) := by
  intro n
  induction n with
  | zero => intro c; exact QueryBounded.pure 0 _
  | succ k ih =>
      intro c
      show QueryBounded (k + 1)
        (obind (sampleBaseO RATE c) (fun p =>
          obind (sampleNO RATE k p.2) (fun q => .pure (p.1 :: q.1, q.2))))
      refine (queryBounded_obind (sampleBaseO_qb RATE c) (fun p =>
        queryBounded_obind (ih p.2) (fun q => QueryBounded.pure 0 _))).mono ?_
      omega

/-- `sampleExt`, oracle-lifted. -/
def sampleExtO [Inhabited F] (RATE D : Nat) (c : Challenger F) : PermOC F (List F × Challenger F) :=
  sampleNO RATE D c

theorem sampleExtO_eval [Inhabited F] (RATE D : Nat) (c : Challenger F) (perm : List F → List F) :
    (sampleExtO RATE D c).eval perm = Challenger.sampleExt perm RATE D c :=
  sampleNO_eval RATE perm D c

theorem sampleExtO_qb [Inhabited F] (RATE D : Nat) (c : Challenger F) :
    QueryBounded D (sampleExtO RATE D c) :=
  sampleNO_qb RATE D c

/-- `sampleBits`, oracle-lifted. -/
def sampleBitsO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (bits : Nat) (c : Challenger F) :
    PermOC F (Nat × Challenger F) :=
  obind (sampleBaseO RATE c) (fun p => .pure (toNat p.1 % (2 ^ bits), p.2))

theorem sampleBitsO_eval [Inhabited F] (RATE : Nat) (toNat : F → Nat) (bits : Nat)
    (c : Challenger F) (perm : List F → List F) :
    (sampleBitsO RATE toNat bits c).eval perm = Challenger.sampleBits perm RATE toNat bits c := by
  unfold sampleBitsO Challenger.sampleBits
  rw [obind_eval, sampleBaseO_eval, OracleComp.eval_pure]

theorem sampleBitsO_qb [Inhabited F] (RATE : Nat) (toNat : F → Nat) (bits : Nat)
    (c : Challenger F) : QueryBounded 1 (sampleBitsO RATE toNat bits c) := by
  unfold sampleBitsO
  refine queryBounded_obind (n := 1) (k := 0) (sampleBaseO_qb RATE c) (fun _ => QueryBounded.pure 0 _)

/-! ## 2. The oracle-lifted transcript stages. -/

/-- `deriveFri`'s commit-phase fold, oracle-lifted (accumulator threaded explicitly). -/
def deriveFriGoO [Inhabited F] (RATE : Nat) (params : FriParams) :
    List (List F) → List (List F) → Challenger F → PermOC F (List (List F) × Challenger F)
  | [],           betas, c => .pure (betas, c)
  | comm :: rest, betas, c =>
      obind (observeListO RATE c comm) (fun c =>
        obind (sampleExtO RATE params.extDeg c) (fun p =>
          deriveFriGoO RATE params rest (betas ++ [p.1]) p.2))

theorem deriveFriGoO_eval [Inhabited F] (RATE : Nat) (params : FriParams) (perm : List F → List F) :
    ∀ (cs : List (List F)) (betas : List (List F)) (c : Challenger F),
      (deriveFriGoO RATE params cs betas c).eval perm
        = cs.foldl (fun (acc : List (List F) × Challenger F) comm =>
            let c := Challenger.observeList perm RATE acc.2 comm
            let p := Challenger.sampleExt perm RATE params.extDeg c
            (acc.1 ++ [p.1], p.2)) (betas, c) := by
  intro cs
  induction cs with
  | nil => intro betas c; rfl
  | cons comm rest ih =>
      intro betas c
      show (obind (observeListO RATE c comm) (fun c =>
              obind (sampleExtO RATE params.extDeg c) (fun p =>
                deriveFriGoO RATE params rest (betas ++ [p.1]) p.2))).eval perm = _
      rw [obind_eval, observeListO_eval, obind_eval, sampleExtO_eval, ih, List.foldl_cons]

theorem deriveFriGoO_qb [Inhabited F] (RATE : Nat) (params : FriParams) :
    ∀ (cs : List (List F)) (betas : List (List F)) (c : Challenger F),
      QueryBounded ((cs.map (fun comm => comm.length + params.extDeg)).sum)
        (deriveFriGoO RATE params cs betas c) := by
  intro cs
  induction cs with
  | nil => intro betas c; exact QueryBounded.pure 0 _
  | cons comm rest ih =>
      intro betas c
      show QueryBounded _
        (obind (observeListO RATE c comm) (fun c =>
          obind (sampleExtO RATE params.extDeg c) (fun p =>
            deriveFriGoO RATE params rest (betas ++ [p.1]) p.2)))
      refine (queryBounded_obind (observeListO_qb RATE c comm) (fun c' =>
        queryBounded_obind (sampleExtO_qb RATE params.extDeg c') (fun p =>
          ih (betas ++ [p.1]) p.2))).mono ?_
      simp only [List.map_cons, List.sum_cons]
      omega

/-- `deriveFri`, oracle-lifted. -/
def deriveFriO [Inhabited F] (RATE : Nat) (params : FriParams) (proof : BatchProofData F)
    (c0 : Challenger F) : PermOC F (List (List F) × Challenger F) :=
  obind (deriveFriGoO RATE params proof.friCommitments [] c0) (fun p =>
    obind (observeListO RATE p.2 proof.finalPoly) (fun c => .pure (p.1, c)))

theorem deriveFriO_eval [Inhabited F] (RATE : Nat) (params : FriParams) (proof : BatchProofData F)
    (c0 : Challenger F) (perm : List F → List F) :
    (deriveFriO RATE params proof c0).eval perm = deriveFri perm RATE params proof c0 := by
  unfold deriveFriO deriveFri
  rw [obind_eval, deriveFriGoO_eval, obind_eval, observeListO_eval, OracleComp.eval_pure]

theorem deriveFriO_qb [Inhabited F] (RATE : Nat) (params : FriParams) (proof : BatchProofData F)
    (c0 : Challenger F) :
    QueryBounded
      ((proof.friCommitments.map (fun comm => comm.length + params.extDeg)).sum
        + proof.finalPoly.length)
      (deriveFriO RATE params proof c0) := by
  unfold deriveFriO
  refine (queryBounded_obind (deriveFriGoO_qb RATE params proof.friCommitments [] c0) (fun p =>
    queryBounded_obind (observeListO_qb RATE p.2 proof.finalPoly)
      (fun _ => QueryBounded.pure 0 _))).mono ?_
  omega

/-- `drawQueries`, oracle-lifted. -/
def drawQueriesO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (logN : Nat) :
    Nat → Challenger F → PermOC F (List Nat × Challenger F)
  | 0,     c => .pure ([], c)
  | (n+1), c =>
      obind (sampleBitsO RATE toNat logN c) (fun p =>
        obind (drawQueriesO RATE toNat logN n p.2) (fun q =>
          .pure (p.1 :: q.1, q.2)))

theorem drawQueriesO_eval [Inhabited F] (RATE : Nat) (toNat : F → Nat) (logN : Nat)
    (perm : List F → List F) :
    ∀ (n : Nat) (c : Challenger F),
      (drawQueriesO RATE toNat logN n c).eval perm = drawQueries perm RATE toNat logN n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ k ih =>
      intro c
      show (obind (sampleBitsO RATE toNat logN c) (fun p =>
              obind (drawQueriesO RATE toNat logN k p.2) (fun q => .pure (p.1 :: q.1, q.2)))).eval perm
        = drawQueries perm RATE toNat logN (k + 1) c
      simp only [obind_eval, sampleBitsO_eval, ih, OracleComp.eval_pure]
      rfl

theorem drawQueriesO_qb [Inhabited F] (RATE : Nat) (toNat : F → Nat) (logN : Nat) :
    ∀ (n : Nat) (c : Challenger F), QueryBounded n (drawQueriesO RATE toNat logN n c) := by
  intro n
  induction n with
  | zero => intro c; exact QueryBounded.pure 0 _
  | succ k ih =>
      intro c
      show QueryBounded (k + 1)
        (obind (sampleBitsO RATE toNat logN c) (fun p =>
          obind (drawQueriesO RATE toNat logN k p.2) (fun q => .pure (p.1 :: q.1, q.2))))
      refine (queryBounded_obind (sampleBitsO_qb RATE toNat logN c) (fun p =>
        queryBounded_obind (ih p.2) (fun q => QueryBounded.pure 0 _))).mono ?_
      omega

/-- `deriveQueryIndices`, oracle-lifted. -/
def deriveQueryIndicesO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (logN : Nat) (c0 : Challenger F) : PermOC F (List Nat × Challenger F) :=
  drawQueriesO RATE toNat logN params.numQueries c0

theorem deriveQueryIndicesO_eval [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (logN : Nat) (c0 : Challenger F) (perm : List F → List F) :
    (deriveQueryIndicesO RATE toNat params logN c0).eval perm
      = deriveQueryIndices perm RATE toNat params logN c0 :=
  drawQueriesO_eval RATE toNat logN perm params.numQueries c0

theorem deriveQueryIndicesO_qb [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (logN : Nat) (c0 : Challenger F) :
    QueryBounded params.numQueries (deriveQueryIndicesO RATE toNat params logN c0) :=
  drawQueriesO_qb RATE toNat logN params.numQueries c0

/-- `deriveQueryPow`, oracle-lifted. -/
def deriveQueryPowO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (powBits : Nat)
    (witness : List F) (c : Challenger F) : PermOC F (Option Nat × Challenger F) :=
  match witness with
  | [w] =>
      if powBits = 0 then .pure (some 0, c)
      else
        obind (observeO RATE c w) (fun c =>
          obind (sampleBitsO RATE toNat powBits c) (fun p => .pure (some p.1, p.2)))
  | _ => .pure (none, c)

theorem deriveQueryPowO_eval [Inhabited F] (RATE : Nat) (toNat : F → Nat) (powBits : Nat)
    (witness : List F) (c : Challenger F) (perm : List F → List F) :
    (deriveQueryPowO RATE toNat powBits witness c).eval perm
      = deriveQueryPow perm RATE toNat powBits witness c := by
  cases witness with
  | nil => rfl
  | cons w tl =>
      cases tl with
      | nil =>
          show (if powBits = 0 then OracleComp.pure (some 0, c)
                else obind (observeO RATE c w) (fun c =>
                  obind (sampleBitsO RATE toNat powBits c)
                    (fun p => .pure (some p.1, p.2)))).eval perm
            = deriveQueryPow perm RATE toNat powBits [w] c
          unfold deriveQueryPow
          split_ifs with hp
          · rfl
          · rw [obind_eval, observeO_eval, obind_eval, sampleBitsO_eval, OracleComp.eval_pure]
      | cons w2 tl2 => rfl

theorem deriveQueryPowO_qb [Inhabited F] (RATE : Nat) (toNat : F → Nat) (powBits : Nat)
    (witness : List F) (c : Challenger F) :
    QueryBounded 2 (deriveQueryPowO RATE toNat powBits witness c) := by
  cases witness with
  | nil => exact QueryBounded.pure 2 _
  | cons w tl =>
      cases tl with
      | nil =>
          show QueryBounded 2
            (if powBits = 0 then OracleComp.pure (some 0, c)
             else obind (observeO RATE c w) (fun c =>
               obind (sampleBitsO RATE toNat powBits c) (fun p => .pure (some p.1, p.2))))
          split_ifs with hp
          · exact QueryBounded.pure 2 _
          · refine (queryBounded_obind (observeO_qb RATE c w) (fun c' =>
              queryBounded_obind (sampleBitsO_qb RATE toNat powBits c')
                (fun _ => QueryBounded.pure 0 _))).mono ?_
            omega
      | cons w2 tl2 => exact QueryBounded.pure 2 _

/-- **`deriveTranscript`, oracle-lifted** — the ONE place `perm` enters `verifyAlgo`, mirrored
verbatim with every `perm` call lifted to a `query`. -/
def deriveTranscriptO [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    PermOC F (DerivedChallenges F) :=
  obind (observeListO RATE (Challenger.init initState) proof.degreeBitsPreamble) (fun c1 =>
  obind (observeListO RATE c1 proof.baseDegreeBitsPreamble) (fun c2 =>
  obind (observeListO RATE c2 proof.preprocessedWidthPreamble) (fun c3 =>
  obind (observeListO RATE c3 proof.traceCommit) (fun c4 =>
  obind (observeListO RATE c4 proof.preprocessedCommit) (fun c5 =>
  obind (observeListO RATE c5 pub.segment) (fun c6 =>
  obind (sampleExtO RATE params.extDeg c6) (fun p7 =>
  obind (observeListO RATE p7.2 proof.quotientCommit) (fun c8 =>
  obind (sampleExtO RATE params.extDeg c8) (fun p9 =>
  obind (observeListO RATE p9.2 proof.openedEvaluations) (fun c10 =>
  obind (sampleExtO RATE params.extDeg c10) (fun p11 =>
  obind (deriveFriO RATE params proof p11.2) (fun p12 =>
  obind (observeListO RATE p12.2 proof.friLogArities) (fun c13 =>
  obind (deriveQueryPowO RATE toNat params.powBits proof.powWitness c13) (fun p14 =>
  obind (deriveQueryIndicesO RATE toNat params logN p14.2) (fun p15 =>
    OracleComp.pure
      { constraintAlpha := p7.1, ζ := p9.1, openingAlpha := p11.1, betas := p12.1,
        powSample := p14.1, qidx := p15.1,
        postPreamble := c3, postConstraintAlpha := p7.2, postZeta := p9.2,
        postOpeningAlpha := p11.2, postFri := c13, postPow := p14.2 })))))))))))))))

theorem deriveTranscriptO_eval [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (perm : List F → List F) :
    (deriveTranscriptO RATE toNat params initState logN proof pub).eval perm
      = deriveTranscript perm RATE toNat params initState logN proof pub := by
  unfold deriveTranscriptO deriveTranscript
  simp only [obind_eval, observeListO_eval, sampleExtO_eval, deriveFriO_eval,
    deriveQueryPowO_eval, deriveQueryIndicesO_eval, OracleComp.eval_pure]

/-- **`permCallCount`** — an explicit UPPER bound on the number of permutation calls
`deriveTranscriptO` (hence `verifyAlgoO`) makes, read off the proof shape: one per observed field
element (the observe-list lengths), `extDeg` per sponge squeeze, the commit-phase fold cost, `2`
for the query-PoW absorb+squeeze, and `numQueries` for the index draws. Over-approximate because
each `observe`/`sampleBase` performs AT MOST one permutation, which is all a per-path
`QueryBounded` needs. -/
def permCallCount {F : Type} (params : FriParams) (proof : BatchProofData F)
    (pub : WrapPublics F) : ℕ :=
  proof.degreeBitsPreamble.length
    + proof.baseDegreeBitsPreamble.length
    + proof.preprocessedWidthPreamble.length
    + proof.traceCommit.length
    + proof.preprocessedCommit.length
    + pub.segment.length
    + params.extDeg
    + proof.quotientCommit.length
    + params.extDeg
    + proof.openedEvaluations.length
    + params.extDeg
    + ((proof.friCommitments.map (fun comm => comm.length + params.extDeg)).sum
        + proof.finalPoly.length)
    + proof.friLogArities.length
    + 2
    + params.numQueries

theorem deriveTranscriptO_qb [Inhabited F] (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    QueryBounded (permCallCount params proof pub)
      (deriveTranscriptO RATE toNat params initState logN proof pub) := by
  unfold deriveTranscriptO
  refine (
    queryBounded_obind (observeListO_qb RATE (Challenger.init initState) proof.degreeBitsPreamble) fun c1 =>
    queryBounded_obind (observeListO_qb RATE c1 proof.baseDegreeBitsPreamble) fun c2 =>
    queryBounded_obind (observeListO_qb RATE c2 proof.preprocessedWidthPreamble) fun c3 =>
    queryBounded_obind (observeListO_qb RATE c3 proof.traceCommit) fun c4 =>
    queryBounded_obind (observeListO_qb RATE c4 proof.preprocessedCommit) fun c5 =>
    queryBounded_obind (observeListO_qb RATE c5 pub.segment) fun c6 =>
    queryBounded_obind (sampleExtO_qb RATE params.extDeg c6) fun p7 =>
    queryBounded_obind (observeListO_qb RATE p7.2 proof.quotientCommit) fun c8 =>
    queryBounded_obind (sampleExtO_qb RATE params.extDeg c8) fun p9 =>
    queryBounded_obind (observeListO_qb RATE p9.2 proof.openedEvaluations) fun c10 =>
    queryBounded_obind (sampleExtO_qb RATE params.extDeg c10) fun p11 =>
    queryBounded_obind (deriveFriO_qb RATE params proof p11.2) fun p12 =>
    queryBounded_obind (observeListO_qb RATE p12.2 proof.friLogArities) fun c13 =>
    queryBounded_obind (deriveQueryPowO_qb RATE toNat params.powBits proof.powWitness c13) fun p14 =>
    queryBounded_obind (deriveQueryIndicesO_qb RATE toNat params logN p14.2) fun p15 =>
    QueryBounded.pure 0
      ({ constraintAlpha := p7.1, ζ := p9.1, openingAlpha := p11.1, betas := p12.1,
         powSample := p14.1, qidx := p15.1,
         postPreamble := c3, postConstraintAlpha := p7.2, postZeta := p9.2,
         postOpeningAlpha := p11.2, postFri := c13,
         postPow := p14.2 } : DerivedChallenges F)
    ).mono ?_
  unfold permCallCount
  omega

/-! ## 3. The oracle verifier and the Stage-1 deliverables. -/

/-- **`verifyAlgoO`** — the oracle image of `verifyAlgo`: same signature WITHOUT `perm`, returning
an `OracleComp` over the sponge state. Only the transcript's permutation calls are lifted; the
`checks : FriChecks F` bundle (the per-query FRI/Merkle recomputes, over `FriCore.compress`, a
separate parameter) is threaded UNCHANGED. -/
def verifyAlgoO [Inhabited F] [DecidableEq F]
    (RATE : Nat) (toNat : F → Nat) (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    PermOC F Bool :=
  obind (deriveTranscriptO RATE toNat params initState logN proof pub) (fun d =>
    .pure
      (vk.shapeMatches proof
        && checks.foldConsistent proof d.betas d.qidx
        && checks.merklePaths proof d.qidx
        && checks.batchTables proof d.betas
        && checks.queryPow proof
        && segmentTooth proof pub))

/-- **THE FAITHFULNESS THEOREM (Stage-1 deliverable 2).** Running the oracle verifier against the
deterministic `perm`-oracle recovers the deployed `Bool`. The re-basing is CONSERVATIVE: `verifyAlgo`
is untouched and recoverable. -/
theorem verifyAlgoO_run_eq [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    (verifyAlgoO RATE toNat params vk checks initState logN proof pub).eval perm
      = verifyAlgo perm RATE toNat params vk checks initState logN proof pub := by
  unfold verifyAlgoO verifyAlgo
  rw [obind_eval, deriveTranscriptO_eval, OracleComp.eval_pure]

/-- The faithfulness theorem in the `OracleComp.eval (fun q => perm q) …` presentation of the design
doc (`§5 Stage 1`); `fun q => perm q` is `perm` by η, so this is `verifyAlgoO_run_eq`. -/
theorem verifyAlgoO_run_eq' [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    OracleComp.eval (verifyAlgoO RATE toNat params vk checks initState logN proof pub)
        (fun q => perm q)
      = verifyAlgo perm RATE toNat params vk checks initState logN proof pub :=
  verifyAlgoO_run_eq perm RATE toNat params vk checks initState logN proof pub

/-- **THE QUERY BUDGET (Stage-1 deliverable 3).** `verifyAlgoO` makes at most `permCallCount`
permutation queries along every path — the explicit proof-shape bound the Stage-2 ε(Q, params)
accounting quantifies over. -/
theorem verifyAlgoO_queryBounded [Inhabited F] [DecidableEq F]
    (RATE : Nat) (toNat : F → Nat) (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    QueryBounded (permCallCount params proof pub)
      (verifyAlgoO RATE toNat params vk checks initState logN proof pub) := by
  unfold verifyAlgoO
  exact queryBounded_obind (n := permCallCount params proof pub) (k := 0)
    (deriveTranscriptO_qb RATE toNat params initState logN proof pub)
    (fun _ => QueryBounded.pure 0 _)

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  obind_eval,
  queryBounded_obind,
  duplexingO_eval,
  observeO_eval,
  observeListO_eval,
  sampleBaseO_eval,
  sampleNO_eval,
  sampleExtO_eval,
  sampleBitsO_eval,
  deriveFriGoO_eval,
  deriveFriO_eval,
  drawQueriesO_eval,
  deriveQueryIndicesO_eval,
  deriveQueryPowO_eval,
  deriveTranscriptO_eval,
  deriveTranscriptO_qb,
  verifyAlgoO_run_eq,
  verifyAlgoO_run_eq',
  verifyAlgoO_queryBounded
]

end Dregg2.Circuit.FriVerifierO
