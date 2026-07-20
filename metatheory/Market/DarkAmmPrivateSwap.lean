/-
# Market.DarkAmmPrivateSwap — the semantic law for encrypted-amount AMM steps.

The executable carrier is `fhegg-fhe/src/dark_amm.rs`:

  Enc(x') = Enc(x) + Enc(dx)
  Enc(y') = Enc(y) - Enc(dy)
  Enc(x' * y') = ctMul(Enc(x'), Enc(y'))

Only the final product is threshold-opened.  An honest transition reveals the
already-public invariant `k`; the house never receives `dx`, `dy`, `x`, or `y`
as plaintext.  This file authors the state-transition meaning in Lean: an
admitted hidden-amount proposal cannot overdraw, its post-state preserves the
constant product, and a refused proposal is atomic (the old state survives).

Honest boundary: this is the pure integer semantic relation, not a theorem
about BFV, threshold decryption, ciphertext hiding, or ingest range proofs.
Those carriers must refine `Admissible`; the Rust API names its currently
caller-declared bounds explicitly.
-/

import Dregg2.Tactics

namespace Market.DarkAmmPrivateSwap

set_option autoImplicit false

/-- Hidden reserve state. Only `k` belongs in the verifier's public view. -/
structure Reserves where
  x : ℕ
  y : ℕ
  k : ℕ
  deriving DecidableEq, Repr

/-- Hidden trade amounts. The proof/verifier consumes commitments to these,
not this clear structure; it is the semantic witness. -/
structure Amounts where
  dx : ℕ
  dy : ℕ
  deriving DecidableEq, Repr

/-- Candidate reserve update. Nat subtraction is safe only under the explicit
`dy ≤ y` premise in `Admissible`. -/
def post (s : Reserves) (a : Amounts) : Reserves :=
  { x := s.x + a.dx, y := s.y - a.dy, k := s.k }

/-- The exact private-swap relation enforced before mutation. -/
def Admissible (s : Reserves) (a : Amounts) : Prop :=
  a.dy ≤ s.y ∧ (s.x + a.dx) * (s.y - a.dy) = s.k

instance (s : Reserves) (a : Amounts) : Decidable (Admissible s a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The one bit revealed by the masked-decrypt → MPC boundary.  Range and
no-overdraw validity is deliberately a separate ingest proof: equality alone
must not launder a wrapped amount into an admissible transition. -/
def invariantDecision (s : Reserves) (a : Amounts) : Bool :=
  decide ((s.x + a.dx) * (s.y - a.dy) = s.k)

/-- Exact semantic interface of the runtime composition: an authenticated
no-overdraw/range certificate plus the sole MPC result bit is precisely the
private-swap relation. -/
theorem range_and_decision_iff_admissible (s : Reserves) (a : Amounts) :
    (a.dy ≤ s.y ∧ invariantDecision s a = true) ↔ Admissible s a := by
  simp [invariantDecision, Admissible]

/-- Fail-closed commit: a bad proof/proposal returns the byte-identical old
semantic state. -/
def commit (s : Reserves) (a : Amounts) : Reserves :=
  if Admissible s a then post s a else s

/-- One admitted encrypted-amount step preserves the published invariant. -/
theorem admitted_post_preserves_product {s : Reserves} {a : Amounts}
    (h : Admissible s a) : (post s a).x * (post s a).y = s.k := by
  exact h.2

/-- The state-carried public invariant is unchanged independently of the
proposal polarity. -/
theorem post_preserves_public_k (s : Reserves) (a : Amounts) :
    (post s a).k = s.k := rfl

/-- Overdrawing the hidden output reserve is outside the relation. -/
theorem overdraw_refused {s : Reserves} {a : Amounts} (h : s.y < a.dy) :
    ¬ Admissible s a := by
  intro hadmit
  exact (Nat.not_lt_of_ge hadmit.1) h

/-- Refusal is atomic: no candidate reserve reaches the state. -/
theorem refused_holds_state {s : Reserves} {a : Amounts} (h : ¬ Admissible s a) :
    commit s a = s := by
  simp [commit, h]

/-- Acceptance commits exactly the relation-defined post-state. -/
theorem admitted_commits_post {s : Reserves} {a : Amounts} (h : Admissible s a) :
    commit s a = post s a := by
  simp [commit, h]

/-- A true decision with the independently checked range premise is sufficient
for the exact post-state; the clear product never needs to be a public output. -/
theorem accepted_decision_commits_post {s : Reserves} {a : Amounts}
    (hrange : a.dy ≤ s.y) (hdecision : invariantDecision s a = true) :
    commit s a = post s a := by
  exact admitted_commits_post ((range_and_decision_iff_admissible s a).mp ⟨hrange, hdecision⟩)

/-- A false equality decision is atomic regardless of the hidden amounts. -/
theorem false_decision_holds_state {s : Reserves} {a : Amounts}
    (hdecision : invariantDecision s a = false) : commit s a = s := by
  apply refused_holds_state
  intro hadmit
  have := (range_and_decision_iff_admissible s a).mpr hadmit
  simp [hdecision] at this

/-- Every commit, accepted or refused, leaves the public `k` unchanged. -/
theorem commit_preserves_public_k (s : Reserves) (a : Amounts) :
    (commit s a).k = s.k := by
  by_cases h : Admissible s a <;> simp [commit, h, post]

/-! Executable teeth mirror the Rust oracle vectors. -/

def pool : Reserves := { x := 100, y := 900, k := 90000 }
def exact : Amounts := { dx := 50, dy := 300 }
def wrong : Amounts := { dx := 50, dy := 301 }
def overdraw : Amounts := { dx := 50, dy := 901 }

#guard decide (Admissible pool exact) == true
#guard decide (Admissible pool wrong) == false
#guard decide (Admissible pool overdraw) == false
#guard commit pool exact == { x := 150, y := 600, k := 90000 }
#guard commit pool wrong == pool
#guard invariantDecision pool exact == true
#guard invariantDecision pool wrong == false

theorem wrong_quote_tooth : ¬ Admissible pool wrong := by decide
theorem overdraw_tooth : ¬ Admissible pool overdraw := by decide

#assert_all_clean [Market.DarkAmmPrivateSwap.admitted_post_preserves_product,
  Market.DarkAmmPrivateSwap.range_and_decision_iff_admissible,
  Market.DarkAmmPrivateSwap.post_preserves_public_k,
  Market.DarkAmmPrivateSwap.overdraw_refused,
  Market.DarkAmmPrivateSwap.refused_holds_state,
  Market.DarkAmmPrivateSwap.admitted_commits_post,
  Market.DarkAmmPrivateSwap.accepted_decision_commits_post,
  Market.DarkAmmPrivateSwap.false_decision_holds_state,
  Market.DarkAmmPrivateSwap.commit_preserves_public_k,
  Market.DarkAmmPrivateSwap.wrong_quote_tooth,
  Market.DarkAmmPrivateSwap.overdraw_tooth]

end Market.DarkAmmPrivateSwap
