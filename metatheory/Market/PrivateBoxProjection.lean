/-
# Market.PrivateBoxProjection — Lean-authored active box prox semantics.

This is the semantic contract for `fhegg-fhe/src/fhir/private_box.rs`, the first
fhIR runtime whose prox is allowed to bind.  The secret canonical input `x` is
projected onto the public natural-number interval `[lo, hi]`.  The executable
carrier reveals the selected public face (`lower | interior | upper`) but keeps
the input and projected output additively shared.

The refinement theorem below is about the exact mod-`t` sharing operation used
by Rust.  When the comparison bits faithfully determine `observedBranch`,
replacing the parties' shares by the party-zero sharing of a selected endpoint
(or retaining them in the interior) reconstructs exactly `project lo hi x`.

Honest boundary: this file proves integer semantics and the share transform,
not MPC transcript security, malicious input validity, or authenticated
transport.  Rust makes canonical comparison fail-closed by requiring
`t = 2^valueBits` and separately comparing the secret input to its public bound.
-/

import Dregg2.Tactics

namespace Market.PrivateBoxProjection

set_option autoImplicit false

/-- The intentionally public disclosure of the first active-prox product. -/
inductive Branch where
  | lower
  | interior
  | upper
  deriving DecidableEq, Repr

/-- Exact projection of `x` onto the public closed interval `[lo, hi]`. -/
def project (lo hi x : ℕ) : ℕ :=
  if x < lo then lo else if hi < x then hi else x

/-- Which public face the exact projection selected. Endpoints already in the
box count as `interior`; strict comparisons are the executable convention. -/
def observedBranch (lo hi x : ℕ) : Branch :=
  if x < lo then .lower else if hi < x then .upper else .interior

/-- Decode the two strict-comparison bits retained by the runtime. -/
def runtimeBranch (below above : Bool) : Branch :=
  match below, above with
  | true, _ => .lower
  | false, true => .upper
  | false, false => .interior

/-- Honest comparison bits refine the semantic branch exactly. -/
theorem runtimeBranch_refines (lo hi x : ℕ) (below above : Bool)
    (hbelow : below = decide (x < lo))
    (habove : above = decide (hi < x)) :
    runtimeBranch below above = observedBranch lo hi x := by
  subst below
  subst above
  by_cases hlo : x < lo <;> by_cases hhi : hi < x <;>
    simp [runtimeBranch, observedBranch, hlo, hhi]

/-- Party-zero sharing of a public endpoint, with the same roster length. -/
def publicShares : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, value => value :: List.replicate n 0

/-- Mod-`t` reconstruction of additive shares. -/
def reconstruct (t : ℕ) (shares : List ℕ) : ℕ := shares.sum % t

/-- Apply the observed public branch without opening the input shares. -/
def applyBranch (lo hi : ℕ) (branch : Branch) (shares : List ℕ) : List ℕ :=
  match branch with
  | .lower => publicShares shares.length lo
  | .interior => shares
  | .upper => publicShares shares.length hi

@[simp] theorem sum_publicShares (n value : ℕ) :
    (publicShares (n + 1) value).sum = value := by
  simp [publicShares]

theorem reconstruct_publicShares {t n value : ℕ} (hn : 0 < n) (hv : value < t) :
    reconstruct t (publicShares n value) = value := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [reconstruct, publicShares, Nat.mod_eq_of_lt hv]

/-- **Runtime refinement.** Given the actual input reconstruction and endpoint
range facts, the party-local share selection reconstructs the exact Lean box
projection. No projected value has to be a public output. -/
theorem apply_observed_refines {t lo hi x : ℕ} {shares : List ℕ}
    (hshares : shares ≠ []) (hx : reconstruct t shares = x)
    (hlo : lo < t) (hhi : hi < t) :
    reconstruct t (applyBranch lo hi (observedBranch lo hi x) shares) =
      project lo hi x := by
  cases shares with
  | nil => exact (hshares rfl).elim
  | cons head tail =>
    have hlen : 0 < (head :: tail).length := Nat.zero_lt_succ _
    by_cases hbelow : x < lo
    · simp only [observedBranch, hbelow, ↓reduceIte, applyBranch, project]
      exact reconstruct_publicShares hlen hlo
    · by_cases habove : hi < x
      · simp only [observedBranch, hbelow, ↓reduceIte, habove, applyBranch, project]
        exact reconstruct_publicShares hlen hhi
      · simp [observedBranch, project, hbelow, habove, applyBranch, hx]

/-- Projection always lands in the public box. -/
theorem project_mem {lo hi x : ℕ} (hbox : lo ≤ hi) :
    lo ≤ project lo hi x ∧ project lo hi x ≤ hi := by
  by_cases hbelow : x < lo
  · simp [project, hbelow, hbox]
  · by_cases habove : hi < x
    · simp [project, hbelow, habove, hbox]
    · simp [project, hbelow, habove]
      omega

/-- Points already in the box are fixed exactly. -/
theorem project_eq_self {lo hi x : ℕ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    project lo hi x = x := by
  simp [project, Nat.not_lt.mpr hlo, Nat.not_lt.mpr hhi]

/-- The box projection is idempotent. -/
theorem project_idempotent {lo hi x : ℕ} (hbox : lo ≤ hi) :
    project lo hi (project lo hi x) = project lo hi x := by
  have hmem := project_mem (x := x) hbox
  exact project_eq_self hmem.1 hmem.2

/-- Lower-face selection has the exact public endpoint meaning. -/
theorem lower_branch_projects {lo hi x : ℕ} (h : x < lo) :
    observedBranch lo hi x = .lower ∧ project lo hi x = lo := by
  simp [observedBranch, project, h]

/-- Upper-face selection has the exact public endpoint meaning. -/
theorem upper_branch_projects {lo hi x : ℕ} (hlohi : lo ≤ hi) (h : hi < x) :
    observedBranch lo hi x = .upper ∧ project lo hi x = hi := by
  have hnlo : ¬x < lo := by omega
  simp [observedBranch, project, hnlo, h]

/-! Executable teeth cover all three branches and endpoint convention. -/

#guard project 100 1000 42 == 100
#guard project 100 1000 100 == 100
#guard project 100 1000 500 == 500
#guard project 100 1000 1000 == 1000
#guard project 100 1000 1200 == 1000
#guard observedBranch 100 1000 42 == .lower
#guard observedBranch 100 1000 500 == .interior
#guard observedBranch 100 1000 1200 == .upper

#assert_all_clean [Market.PrivateBoxProjection.runtimeBranch_refines,
  Market.PrivateBoxProjection.reconstruct_publicShares,
  Market.PrivateBoxProjection.apply_observed_refines,
  Market.PrivateBoxProjection.project_mem,
  Market.PrivateBoxProjection.project_eq_self,
  Market.PrivateBoxProjection.project_idempotent,
  Market.PrivateBoxProjection.lower_branch_projects,
  Market.PrivateBoxProjection.upper_branch_projects]

end Market.PrivateBoxProjection
