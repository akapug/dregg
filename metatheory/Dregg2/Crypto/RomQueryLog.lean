/-
# `Dregg2.Crypto.RomQueryLog` — the QUERY LOG of an oracle computation.

`RomOracle` gives the SYNTAX of a query-bounded adversary (`OracleComp`), the run (`eval`), the
points it queries (`queried`), and the determination theorem
(`eval_congr_of_agree_on_queried`). This file adds the one interface a STRAIGHT-LINE EXTRACTOR
needs on top of that substrate: the adversary's own QUERY TRACE, and the evaluator that produces
both the result and the trace in one pass.

`OracleComp.log M H` is the list of `(d, H d)` pairs — every query the computation makes under
`H`, PAIRED with the answer it received, in order (with repeats). `OracleComp.evalLog M H` runs
`M` against `H` and returns `(result, log)`. The two agree with the un-instrumented substrate:
`(M.evalLog H).1 = M.eval H` (`evalLog_fst_eq_eval`) and `(M.evalLog H).2 = M.log H`
(`evalLog_snd_eq_log`), bundled as `evalLog_eq : M.evalLog H = (M.eval H, M.log H)`.

⚑ THE EXTRACTION SUBSTRATE — three facts a query-log extractor consumes:

  * `evalLog_snd_map_fst_eq_queried` — the log's domain projection IS `queried`: the log records
    the very points `RomOracle`'s determination theorem quantifies over, so a bound on the log's
    read set and a bound on `queried` are the same bound (`log_length_eq_queried_length`,
    `QueryBounded.log_length_le`).
  * `evalLog_fst_eq_eval` — the logging run does not change the output.
  * `mem_evalLog_answer` — the READ-BACK: `(d, r) ∈ (M.evalLog H).2 → H d = r`. The extractor
    recovers the oracle's answer at any logged point directly from the log. The log faithfully
    records `H` on the queried set — nothing more, nothing less.

§Teeth: `ofList_log` computes the log of the canonical member exactly (`ds.map (fun d => (d, H d))`
— the trace really is the queried points with their answers), so the log is not vacuously `[]`.

This is idea A2 of `docs/reference/ADOPT-ARKLIB-VCVIO-IDEAS.md`, imitating VCVio's `QueryLog`
(a list of dependent query+response pairs) and `withLogging` (its logging handler) in shape only —
mathlib-only, on our own `OracleComp` substrate, with no VCVio dependency. It is ADDITIVE: it
touches no existing soundness statement. B1 (re-basing `FriLdtExtractV3` over this model) is the
consumer, not this file.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomOracle
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomOracle

set_option autoImplicit false

/-- **THE QUERY LOG.** The list of `(d, H d)` pairs `M` produces when run against `H`: every
queried point PAIRED with the answer it received, in order (with repeats). It depends on `H`,
because a later query point may be computed from an earlier answer — the same dependency `queried`
has. This is the trace a straight-line extractor reads. -/
def OracleComp.log {D R A : Type} : OracleComp D R A → (D → R) → List (D × R)
  | .pure _,    _ => []
  | .query d k, H => (d, H d) :: (k (H d)).log H

/-- **THE LOGGING EVALUATOR.** Run `M` against `H`, returning BOTH the result and the query log in
one pass. Its projections are `eval` and `log` (`evalLog_fst_eq_eval`, `evalLog_snd_eq_log`). -/
def OracleComp.evalLog {D R A : Type} : OracleComp D R A → (D → R) → A × List (D × R)
  | .pure a,    _ => (a, [])
  | .query d k, H => (((k (H d)).evalLog H).1, (d, H d) :: ((k (H d)).evalLog H).2)

/-! ## Reduction lemmas — the equational shape of `log`/`evalLog`. -/

/-- A halted computation logs nothing. -/
theorem OracleComp.log_pure {D R A : Type} (a : A) (H : D → R) :
    (OracleComp.pure a : OracleComp D R A).log H = [] := rfl

/-- A query node's log is its `(point, answer)` pair followed by the continuation's. -/
theorem OracleComp.log_query {D R A : Type} (d : D) (k : R → OracleComp D R A) (H : D → R) :
    (OracleComp.query d k).log H = (d, H d) :: (k (H d)).log H := rfl

/-- `evalLog` of a halted computation is its value with the empty log. -/
theorem OracleComp.evalLog_pure {D R A : Type} (a : A) (H : D → R) :
    (OracleComp.pure a : OracleComp D R A).evalLog H = (a, []) := rfl

/-- `evalLog` of a query node runs the continuation on the answer and prepends the logged pair. -/
theorem OracleComp.evalLog_query {D R A : Type} (d : D) (k : R → OracleComp D R A) (H : D → R) :
    (OracleComp.query d k).evalLog H
      = (((k (H d)).evalLog H).1, (d, H d) :: ((k (H d)).evalLog H).2) := rfl

/-! ## §Agreement with the un-instrumented substrate. -/

/-- **(b) THE LOGGING RUN DOES NOT CHANGE THE OUTPUT.** `evalLog`'s result is `eval`. -/
theorem OracleComp.evalLog_fst_eq_eval {D R A : Type} (M : OracleComp D R A) (H : D → R) :
    (M.evalLog H).1 = M.eval H := by
  induction M with
  | pure a => rfl
  | query d k ih =>
      show ((k (H d)).evalLog H).1 = (k (H d)).eval H
      exact ih (H d)

/-- **`evalLog`'s log projection is `log`.** The one-pass evaluator produces exactly the trace. -/
theorem OracleComp.evalLog_snd_eq_log {D R A : Type} (M : OracleComp D R A) (H : D → R) :
    (M.evalLog H).2 = M.log H := by
  induction M with
  | pure a => rfl
  | query d k ih =>
      show (d, H d) :: ((k (H d)).evalLog H).2 = (d, H d) :: (k (H d)).log H
      rw [ih (H d)]

/-- **`evalLog` splits as `(eval, log)`.** The bundled form of the two projections. -/
theorem OracleComp.evalLog_eq {D R A : Type} (M : OracleComp D R A) (H : D → R) :
    M.evalLog H = (M.eval H, M.log H) :=
  Prod.ext (M.evalLog_fst_eq_eval H) (M.evalLog_snd_eq_log H)

/-- The log's domain projection is `log`'s queried points — it IS `queried`. -/
theorem OracleComp.log_map_fst_eq_queried {D R A : Type} (M : OracleComp D R A) (H : D → R) :
    (M.log H).map Prod.fst = M.queried H := by
  induction M with
  | pure a => rfl
  | query d k ih =>
      show ((d, H d) :: (k (H d)).log H).map Prod.fst = d :: (k (H d)).queried H
      rw [List.map_cons, ih (H d)]

/-- **(a) THE LOG'S DOMAIN PROJECTION EQUALS `queried`.** The extractor reads its committed data
from the very points `RomOracle`'s determination theorem
(`eval_congr_of_agree_on_queried`) quantifies over. -/
theorem OracleComp.evalLog_snd_map_fst_eq_queried {D R A : Type} (M : OracleComp D R A)
    (H : D → R) : ((M.evalLog H).2).map Prod.fst = M.queried H := by
  rw [M.evalLog_snd_eq_log, M.log_map_fst_eq_queried]

/-! ## §Read-back — the extractor recovers `H` from the log. -/

/-- The log faithfully records `H`: any logged pair `(d, r)` has `r = H d`. -/
theorem OracleComp.mem_log_answer {D R A : Type} (M : OracleComp D R A) (H : D → R)
    {d : D} {r : R} : (d, r) ∈ M.log H → H d = r := by
  induction M with
  | pure a => intro h; simp [OracleComp.log] at h
  | query e k ih =>
      intro h
      rw [OracleComp.log_query] at h
      rcases List.mem_cons.1 h with heq | htail
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rfl
      · exact ih (H e) htail

/-- **(c) THE READ-BACK LEMMA.** From a queried point in the log, the extractor recovers the
oracle's answer: `(d, r) ∈ (M.evalLog H).2 → H d = r`. The log records `H` on the queried set and
records nothing false. -/
theorem OracleComp.mem_evalLog_answer {D R A : Type} (M : OracleComp D R A) (H : D → R)
    {d : D} {r : R} (h : (d, r) ∈ (M.evalLog H).2) : H d = r := by
  rw [M.evalLog_snd_eq_log] at h
  exact M.mem_log_answer H h

/-! ## §The log respects the budget — it is the same read set `QueryBounded` bounds. -/

/-- The log's length is the number of queried points. -/
theorem OracleComp.log_length_eq_queried_length {D R A : Type} (M : OracleComp D R A) (H : D → R) :
    (M.log H).length = (M.queried H).length := by
  rw [← M.log_map_fst_eq_queried, List.length_map]

/-- **A `Q`-query computation logs at most `Q` pairs.** The syntactic budget bounds the extractor's
read set — the same bound `RomOracle.QueryBounded.queried_length_le` gives on `queried`. -/
theorem QueryBounded.log_length_le {D R A : Type} {M : OracleComp D R A} {Q : ℕ}
    (h : QueryBounded Q M) (H : D → R) : (M.log H).length ≤ Q := by
  rw [M.log_length_eq_queried_length]
  exact h.queried_length_le H

/-! ## NON-VACUITY TOOTH — the log is a REAL trace, not vacuously empty. -/

/-- **(TOOTH.)** The canonical member `ofList ds f` logs exactly its queried points paired with
their answers: `ds.map (fun d => (d, H d))`. So the log genuinely records the trace — its domain
projection is `ds` (`ofList_queried`) and each pair carries the right answer. -/
theorem OracleComp.ofList_log {D R A : Type} (ds : List D) (f : List R → A) (H : D → R) :
    (OracleComp.ofList ds f).log H = ds.map (fun d => (d, H d)) := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
      show (d, H d) :: (OracleComp.ofList ds (fun rs => f (H d :: rs))).log H
            = (d, H d) :: ds.map (fun d => (d, H d))
      rw [ih]

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  OracleComp.log_pure,
  OracleComp.log_query,
  OracleComp.evalLog_pure,
  OracleComp.evalLog_query,
  OracleComp.evalLog_fst_eq_eval,
  OracleComp.evalLog_snd_eq_log,
  OracleComp.evalLog_eq,
  OracleComp.log_map_fst_eq_queried,
  OracleComp.evalLog_snd_map_fst_eq_queried,
  OracleComp.mem_log_answer,
  OracleComp.mem_evalLog_answer,
  OracleComp.log_length_eq_queried_length,
  QueryBounded.log_length_le,
  OracleComp.ofList_log
]

end Dregg2.Crypto.RomOracle
