/-
# `Dregg2.Crypto.RomOracle` — the SYNTAX of a random-oracle adversary.

`FloorGames` §8 names the tree's residual: `Eff` is a parameter with no content, because an
`Adversary G` is an arbitrary Lean function and an arbitrary Lean function reads the WHOLE
instance. The same defect appears one level up whenever a floor is stated relative to a hash
oracle `H : D → R`: an adversary of type `(D → R) → A` receives the entire oracle as a value, so
`Classical.choice` can pick, from that value, an answer that no querying algorithm could find.

This file gives the type that cannot do that. `OracleComp D R A` is a decision tree over oracle
ANSWERS: `pure a` halts, `query d k` asks at `d` and continues with `k r` on answer `r`. The
oracle is not a parameter of the tree — it appears only in `eval`, which walks the tree against a
concrete `H`. So an `OracleComp` never has the oracle in hand; it has, at each node, exactly the
answers it asked for.

`QueryBounded Q M` is the resource bound this type makes statable: along every path, at most `Q`
queries. It is SYNTACTIC — it quantifies over all possible answers `r`, so it mentions no oracle
and no probability. This is the `Eff` shape for a random-oracle floor.

`OracleComp.eval_congr_of_agree_on_queried` is the file's load-bearing fact: two oracles agreeing
on the points `M` queries under `H` are indistinguishable to `M` — same path, same output. An
oracle adversary's output is a function of the answers it received and of nothing else. That is
the precise sense in which this class is smaller than `(D → R) → A`.

§Teeth: `ofList` exhibits real members (query a list of points, return a function of the answers),
`queryBounded_zero_pure` shows the class is inhabited, and `queryBounded_zero_const` shows the
budget is a genuine restriction — a 0-query computation's output is constant in the oracle, so
`QueryBounded` is not true of everything.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomOracle

set_option autoImplicit false

universe u

/-- An ORACLE COMPUTATION: a decision tree over oracle answers. `pure a` halts with `a`;
`query d k` asks the oracle at `d` and continues with `k r` on answer `r`. NOTE what this type
CANNOT do: look at the oracle. It only ever sees answers it asked for. -/
inductive OracleComp (D R A : Type) : Type where
  /-- Halt, returning `a`. -/
  | pure  : A → OracleComp D R A
  /-- Query the oracle at `d`; continue with `k r` on answer `r`. -/
  | query : D → (R → OracleComp D R A) → OracleComp D R A

/-- Run the computation against a concrete oracle `H`. The oracle enters here and only here: the
tree itself is oracle-free, and `eval` supplies the answers one node at a time. -/
def OracleComp.eval {D R A : Type} : OracleComp D R A → (D → R) → A
  | .pure a,    _ => a
  | .query d k, H => (k (H d)).eval H

/-- The list of points the computation actually queries when run against `H` (in order, with
repeats). It depends on `H`, because a later query point may be computed from an earlier answer. -/
def OracleComp.queried {D R A : Type} : OracleComp D R A → (D → R) → List D
  | .pure _,    _ => []
  | .query d k, H => d :: (k (H d)).queried H

/-- **QUERY BUDGET.** `QueryBounded Q M` — along EVERY path, `M` makes at most `Q` queries.
This is a SYNTACTIC bound: it quantifies over all possible answers `r`, so it does not depend on
any oracle. This predicate is the `Eff` this whole development is about. -/
inductive QueryBounded {D R A : Type} : ℕ → OracleComp D R A → Prop where
  /-- Halting costs nothing: `pure a` is within every budget. -/
  | pure  (n : ℕ) (a : A) : QueryBounded n (.pure a)
  /-- A query costs one, and every continuation must fit in the remaining budget. -/
  | query (n : ℕ) (d : D) (k : R → OracleComp D R A) :
      (∀ r, QueryBounded n (k r)) → QueryBounded (n + 1) (.query d k)

/-- The budget is monotone: a `Q`-query computation is a `Q'`-query computation for `Q ≤ Q'`. -/
theorem QueryBounded.mono {D R A : Type} {M : OracleComp D R A} {Q Q' : ℕ}
    (h : QueryBounded Q M) (hle : Q ≤ Q') : QueryBounded Q' M := by
  induction h generalizing Q' with
  | pure n a => exact QueryBounded.pure _ a
  | query n d k _ ih =>
      obtain ⟨m, rfl⟩ : ∃ m, Q' = m + 1 :=
        ⟨Q' - 1, by omega⟩
      exact QueryBounded.query _ d k (fun r => ih r (by omega))

/-- The queried list is no longer than the budget: a syntactic bound over all answers dominates the
run against any particular oracle. -/
theorem QueryBounded.queried_length_le {D R A : Type} {M : OracleComp D R A} {Q : ℕ}
    (h : QueryBounded Q M) (H : D → R) : (M.queried H).length ≤ Q := by
  induction h generalizing H with
  | pure n a => simp [OracleComp.queried]
  | query n d k _ ih =>
      have := ih (H d) H
      simpa [OracleComp.queried] using Nat.succ_le_succ this

/-- **⚑ THE DETERMINATION THEOREM — the whole point of the file.** If two oracles agree on every
point the computation queries under `H`, it cannot tell them apart: it takes the same path and
returns the same answer. An oracle adversary's output is a function of the answers it received —
and of NOTHING ELSE. This is what `Classical.choice`, which reads the whole oracle, does not obey. -/
theorem OracleComp.eval_congr_of_agree_on_queried {D R A : Type} (M : OracleComp D R A)
    (H H' : D → R) (hag : ∀ d ∈ M.queried H, H d = H' d) :
    M.eval H = M.eval H' ∧ M.queried H = M.queried H' := by
  induction M with
  | pure a => exact ⟨rfl, rfl⟩
  | query d k ih =>
      have hd : H d = H' d := hag d (by simp [OracleComp.queried])
      have htail : ∀ e ∈ (k (H d)).queried H, H e = H' e := fun e he =>
        hag e (by simp [OracleComp.queried, he])
      obtain ⟨hev, hq⟩ := ih (H d) htail
      refine ⟨?_, ?_⟩
      · show (k (H d)).eval H = (k (H' d)).eval H'
        rw [← hd]
        exact hev
      · show d :: (k (H d)).queried H = d :: (k (H' d)).queried H'
        rw [← hd, hq]

/-- Cleaner corollary: agreement on the queried set gives equal outputs. -/
theorem OracleComp.eval_congr {D R A : Type} (M : OracleComp D R A) (H H' : D → R)
    (hag : ∀ d ∈ M.queried H, H d = H' d) : M.eval H = M.eval H' :=
  (M.eval_congr_of_agree_on_queried H H' hag).1

/-- `eval` of a halted computation is its value. -/
theorem OracleComp.eval_pure {D R A : Type} (a : A) (H : D → R) :
    (OracleComp.pure a : OracleComp D R A).eval H = a := rfl

/-- `eval` of a query node runs the continuation on the oracle's answer. -/
theorem OracleComp.eval_query {D R A : Type} (d : D) (k : R → OracleComp D R A) (H : D → R) :
    (OracleComp.query d k).eval H = (k (H d)).eval H := rfl

/-- A halted computation queries nothing. -/
theorem OracleComp.queried_pure {D R A : Type} (a : A) (H : D → R) :
    (OracleComp.pure a : OracleComp D R A).queried H = [] := rfl

/-- A query node's query list is its point followed by the continuation's. -/
theorem OracleComp.queried_query {D R A : Type} (d : D) (k : R → OracleComp D R A) (H : D → R) :
    (OracleComp.query d k).queried H = d :: (k (H d)).queried H := rfl

/-! ## NON-VACUITY / EXPRESSIVENESS TEETH — this class contains REAL adversaries. -/

/-- A computation that queries a fixed list of points and returns a function of the answers.
`ofList ds f` queries `ds` in order and returns `f` applied to the answer list. -/
def OracleComp.ofList {D R A : Type} : List D → (List R → A) → OracleComp D R A
  | [],      f => .pure (f [])
  | d :: ds, f => .query d (fun r => OracleComp.ofList ds (fun rs => f (r :: rs)))

/-- `ofList` is bounded by the length of its query list. -/
theorem OracleComp.ofList_queryBounded {D R A : Type} (ds : List D) (f : List R → A) :
    QueryBounded ds.length (OracleComp.ofList ds f) := by
  induction ds generalizing f with
  | nil => exact QueryBounded.pure _ _
  | cons d ds ih =>
      exact QueryBounded.query _ d _ (fun r => ih (fun rs => f (r :: rs)))

/-- `ofList` really does query exactly `ds`. -/
theorem OracleComp.ofList_queried {D R A : Type} (ds : List D) (f : List R → A) (H : D → R) :
    (OracleComp.ofList ds f).queried H = ds := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
      show d :: (OracleComp.ofList ds (fun rs => f (H d :: rs))).queried H = d :: ds
      rw [ih]

/-- `ofList` returns `f` of the answers it got. -/
theorem OracleComp.ofList_eval {D R A : Type} (ds : List D) (f : List R → A) (H : D → R) :
    (OracleComp.ofList ds f).eval H = f (ds.map H) := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
      show (OracleComp.ofList ds (fun rs => f (H d :: rs))).eval H = f ((d :: ds).map H)
      rw [ih]
      rfl

/-- **(TOOTH — the class is not empty.)** A 0-query computation exists and is `QueryBounded 0`. -/
theorem queryBounded_zero_pure {D R A : Type} (a : A) :
    QueryBounded 0 (OracleComp.pure a : OracleComp D R A) :=
  QueryBounded.pure 0 a

/-- **(TOOTH — the budget is a GENUINE restriction: it is refutable.)** No `QueryBounded 0`
computation can depend on the oracle at all: its output is constant. So `QueryBounded` is not
trivially true of everything — it has real content. -/
theorem queryBounded_zero_const {D R A : Type} (M : OracleComp D R A) (h : QueryBounded 0 M) :
    ∃ a : A, ∀ H : D → R, M.eval H = a := by
  cases M with
  | pure a => exact ⟨a, fun _ => rfl⟩
  | query d k => cases h

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  QueryBounded.mono,
  QueryBounded.queried_length_le,
  OracleComp.eval_congr_of_agree_on_queried,
  OracleComp.eval_congr,
  OracleComp.eval_pure,
  OracleComp.eval_query,
  OracleComp.queried_pure,
  OracleComp.queried_query,
  OracleComp.ofList_queryBounded,
  OracleComp.ofList_queried,
  OracleComp.ofList_eval,
  queryBounded_zero_pure,
  queryBounded_zero_const
]

end Dregg2.Crypto.RomOracle
