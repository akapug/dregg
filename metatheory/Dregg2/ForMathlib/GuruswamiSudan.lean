import Mathlib

/-!
# Guruswami–Sudan list decoding for the affine-line / constant code — the upstreamable core.

Mathlib has no Guruswami–Sudan (GS) list-decoding. This file supplies the general, field-agnostic
skeleton of GS list decoding for the **line code** (messages of degree `< k`, agreement `t`,
block length `n = |ι|`), stated at the level the FRI correlated-agreement primitive needs
(`Dregg2/Circuit/FriCorrelatedAgreementSharp.lean`). It splits GS into its two honest halves:

* **The list-size half — PROVED here, fully general (`card_le_yDegree_of_dvd`).** An interpolation
  polynomial `Q ∈ F[X][Y]` (`Q ≠ 0`) divisible by `Y − p` for each of a finite set of *distinct*
  message polynomials `p` bounds that set by `deg_Y Q`. This is exactly "each agreeing codeword is a
  `Y`-root of `Q`", i.e. `Polynomial.card_roots'` for the coefficient domain `F[X]`. No hypothesis
  on agreement or multiplicity lives here.
* **The interpolation half — NAMED (`GSWitness`, `GuruswamiSudanLineList`).** The *existence* of such
  a `Q`, of controlled `Y`-degree, whose `Y`-roots include every message agreeing on `≥ t` positions.
  This is the multiplicity/Hasse-derivative vanishing + dimension count of GS; it is not proved here.

## The multiplicity obstruction (why the ideal `k·n` is out of reach for a *multiset* received word).

Classical GS assumes **distinct evaluation points** `xs : ι → F`. There the interpolation degree
window is nonempty above the GS radius `t² > (k−1)·n` and the list is `O(√(kn))`, well under `k·n`.
When `xs` **repeats** (the FRI constant-code fold: `xs = O f` can send many fibres to one value), a
good message can be supported on as few as `s` *distinct* evaluation points while still agreeing on
`≥ t` positions (a heavy point of multiplicity `t−1` plus one more). The divisibility half then needs
`s·m > D`, while the existence half needs `(D+1)(D+2) > n·m(m+1)` — and for `s = 2` these are
incompatible for **every** `m, D` (`gs_interp_window_empty`): the GS interpolation delivers *no*
bound at all. Equivalently the weighted (Koetter–Vardy) denominator `t² − m_max·n` goes negative
(`gs_weighted_denominator_negative` in the instantiating file). So `t² > k·n` (GS non-degeneracy for
*distinct* points) is necessary but **not sufficient** for a multiset word: the ideal `k·n` list is
not a theorem at multiplicities the fold actually produces. This file makes that precise rather than
papering over it.

`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `axiom`, no `sorry`.
-/

namespace Dregg2.ForMathlib.GuruswamiSudan

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-! ## The received word and message agreement. -/

/-- The positions where a message polynomial `p` agrees with the received word `(xs, ys)`:
`{i | p(xs i) = ys i}`. The evaluation points `xs` are **not** assumed distinct — that is the whole
point of the constant-code / multiset setting. -/
noncomputable def agreeSet (xs ys : ι → F) (p : Polynomial F) : Finset ι := by
  classical exact Finset.univ.filter (fun i => p.eval (xs i) = ys i)

/-! ## The list-size half of Guruswami–Sudan — PROVED, fully general. -/

/-- **The GS list-size core.** If `Q ∈ F[X][Y]` is nonzero and each `p` in a finite set `L` of
message polynomials satisfies `(Y − p) ∣ Q`, then `|L| ≤ deg_Y Q`. Every such `p` is a root of `Q`
viewed as a polynomial in `Y` over the domain `F[X]`, and a nonzero polynomial over a domain has at
most `natDegree`-many distinct roots. This is the half of GS that does **not** depend on agreement or
multiplicity; it is `Polynomial.card_roots'` transported to `F[X]`. -/
theorem card_le_yDegree_of_dvd (Q : (Polynomial F)[X]) (hQ : Q ≠ 0)
    (L : Finset (Polynomial F)) (hdvd : ∀ p ∈ L, (X - C p) ∣ Q) :
    L.card ≤ Q.natDegree := by
  classical
  have hsub : L ⊆ Q.roots.toFinset := by
    intro p hp
    rw [Multiset.mem_toFinset, mem_roots hQ]
    exact (dvd_iff_isRoot).mp (hdvd p hp)
  calc L.card ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q

/-! ## The interpolation half — NAMED (the upstream target, not proved). -/

/-- **NAMED TARGET — a Guruswami–Sudan interpolation witness.** For a received word `(xs, ys)` of
length `n = |ι|`, message-degree bound `k`, agreement `t`, and target `Y`-degree `D`: a nonzero
bivariate `Q ∈ F[X][Y]` of `Y`-degree `≤ D` such that **every** degree-`< k` message agreeing on
`≥ t` positions is a `Y`-root of `Q` (`(Y − p) ∣ Q`). Existence of `Q` is the multiplicity-`m`
interpolation + `t·m`-fold vanishing on each agreeing line of GS. Mathlib lacks bivariate
multiplicity interpolation; this is the precise sub-lemma to discharge upstream. -/
def GSWitness (xs ys : ι → F) (k t D : ℕ) : Prop :=
  ∃ Q : (Polynomial F)[X], Q ≠ 0 ∧ Q.natDegree ≤ D ∧
    ∀ p : Polynomial F, p.natDegree < k → t ≤ (agreeSet xs ys p).card →
      (X - C p) ∣ Q

/-- **Witness ⇒ list bound** — the two halves composed. A GS interpolation witness of `Y`-degree `≤ D`
caps any list of distinct degree-`< k`, agreement-`≥ t` messages at `D`. This is the deployed shape:
supply the witness (the open half) and the list bound follows from `card_le_yDegree_of_dvd`. -/
theorem card_goodMessages_le_of_witness (xs ys : ι → F) (k t D : ℕ)
    (h : GSWitness xs ys k t D) (L : Finset (Polynomial F))
    (hL : ∀ p ∈ L, p.natDegree < k ∧ t ≤ (agreeSet xs ys p).card) :
    L.card ≤ D := by
  obtain ⟨Q, hQ, hdeg, hdvd⟩ := h
  refine le_trans (card_le_yDegree_of_dvd Q hQ L ?_) hdeg
  intro p hp
  exact hdvd p (hL p hp).1 (hL p hp).2

/-- **NAMED UPSTREAM TARGET — the Guruswami–Sudan line list-size theorem.** Strictly above the GS
radius (`t² > k·n`), the number of distinct degree-`< k` messages agreeing with the received word on
`≥ t` positions is at most the ideal linear size `k·n`. It is PROVABLE from `GSWitness` (with
`D = k·n`) via `card_goodMessages_le_of_witness` **when the evaluation points are distinct** (or of
multiplicity below the GS threshold); for a genuine multiset word it is FALSE at these params — the
interpolation window is empty (`gs_interp_window_empty`). Stated as a `Prop` so the residual is a Lean
object, matching `FriCorrelatedAgreementSharp.GuruswamiSudanLineListBound` (`k = 2`, `k·n = 2·|κ|`). -/
def GuruswamiSudanLineList (xs ys : ι → F) (k : ℕ) : Prop :=
  ∀ (L : Finset (Polynomial F)) (t : ℕ), k * Fintype.card ι < t ^ 2 →
    (∀ p ∈ L, p.natDegree < k ∧ t ≤ (agreeSet xs ys p).card) →
    L.card ≤ k * Fintype.card ι

/-! ## The multiplicity obstruction — PROVED. -/

/-- **The GS interpolation degree window is EMPTY at a support-`2` good line.** For a received word
of length `n ≥ 32` (the FRI fold has `n = 64`), a good message supported on only `2` distinct
evaluation points forces the divisibility bound `D < 2·m`, while a nonzero multiplicity-`m`
interpolation polynomial needs `(D+1)(D+2) > n·m(m+1)` coefficients-over-constraints. No `D, m` meet
both: `(D+1)(D+2) ≤ 2m(2m+1) = 4m²+2m ≤ 32·m(m+1) ≤ n·m(m+1)`. So the polynomial method yields **no**
list bound (least of all the ideal `k·n`) when the fold sends `≥ t−1` fibres onto one plane point —
the exact multiplicity regime the constant-code fold produces. -/
theorem gs_interp_window_empty (n m D : ℕ) (hn : 32 ≤ n) (hm : 1 ≤ m) (hdiv : D < 2 * m) :
    ¬ ((D + 1) * (D + 2) > n * (m * (m + 1))) := by
  intro hex
  have hD1 : D + 1 ≤ 2 * m := by omega
  have hD2 : D + 2 ≤ 2 * m + 1 := by omega
  have hprod : (D + 1) * (D + 2) ≤ (2 * m) * (2 * m + 1) := Nat.mul_le_mul hD1 hD2
  have hlow : (32 : ℕ) * (m * (m + 1)) ≤ n * (m * (m + 1)) := Nat.mul_le_mul_right _ hn
  nlinarith [hprod, hlow, hex, hm]

end Dregg2.ForMathlib.GuruswamiSudan
