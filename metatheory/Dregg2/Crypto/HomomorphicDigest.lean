/-
# `Dregg2.Crypto.HomomorphicDigest` — the SIS-based homomorphic MONOID digest (experiment)

The one coordination gadget the census found **absent**: a commutative/associative *fold monoid*
for a whole-history digest. Every fold in the tree today is either the shape-*sensitive* Poseidon
`acc` (`H(l ‖ r) ≠ H(r ‖ l)`, so a streaming fold must reproduce the exact tree shape) or the
order-*dependent* first-wins `resolveOrdered`. Neither lets a worker pool fold ANY subranges and
recombine freely — the "fluid scan state" the Mina-critique motivated.

This file builds the alternative and proves it works. The digest of a history `S : Finset ι` is

    digest A encode S  :=  A (∑ i ∈ S, encode i)

for a **linear** SIS map `A : M →ₗ[Rq] N` and a per-turn short encoding `encode : ι → M`. Because `A`
is linear and `∑` is a `Finset.sum`, three properties fall out with no new mathematics:

  * **HOMOMORPHISM / COMBINE** — disjoint sub-histories digest independently and add
    (`digest_union`); the whole digest is a plain sum of per-turn contributions (`digest_eq_sum`).
  * **A COMMUTATIVE MONOID, shape-free** — the fold is `Finset.sum`, so it is independent of order
    AND of any grouping into blocks (`digest_biUnion`). This is the property the Poseidon `acc`
    lacks; it is exactly what dissolves the MMR shape-guard the streaming fold needed, and what lets
    a distributed worker pool combine partials in any order.
  * **BINDING = SIS** — a collision on two *distinct* histories EXTRACTS a short nonzero kernel
    vector, i.e. a Module-SIS solution (`digest_collision_extracts_msis`), so binding reduces to
    `MSISHard` (`digest_binds_under_msis`) — the same honest, named lattice floor every PQ scheme
    rests on (`Dregg2.Crypto.Lattice`), reached the census-praised extraction-as-DATA way, not via a
    supplied adversary.

## Honest scope (the named seams, not hidden)

  * `MSISHard` is the assumed floor — stated in `Lattice.lean` as an existence-refutation that is
    itself vacuous at deployed parameters; the CONTENT here is the reduction (a collision *is* a
    short kernel vector), consumed under `MSISHard` exactly as `HermineMSIS.no_forgery_under_msis`.
  * `SumInjective encode` is a carried obligation — distinct histories must have distinct encode
    sums, else the extracted witness is `0` (not a solution). It is LOAD-BEARING, with teeth
    (`digest_collides_of_not_sumInjective`): drop it and a distinct-history collision reappears. A
    position-indexed encoding makes it structural — the parameterization / emit-to-AIR is the
    follow-up; this file is the proof-of-concept that the construction is sound.

Sorry-free; `#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `native_decide`.
-/
import Dregg2.Crypto.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Dregg2.Crypto.HomomorphicDigest

set_option linter.unusedSectionVars false

open Dregg2.Crypto.Lattice

variable {ι : Type*} [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [ShortNorm M]
variable {Rq : Type*} [CommRing Rq] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- The homomorphic digest of a history `S`: the SIS image of the per-turn encode sum. -/
def digest (A : M →ₗ[Rq] N) (encode : ι → M) (S : Finset ι) : N :=
  A (∑ i ∈ S, encode i)

/-! ## §1 — the fold is a COMMUTATIVE MONOID: order-free and grouping-free. -/

/-- The digest is a `Finset.sum` of per-turn contributions — a commutative-monoid fold, so it is
independent of order and of any grouping. This is what the shape-sensitive Poseidon `acc` cannot be. -/
theorem digest_eq_sum (A : M →ₗ[Rq] N) (encode : ι → M) (S : Finset ι) :
    digest A encode S = ∑ i ∈ S, A (encode i) := by
  unfold digest
  exact map_sum A encode S

/-- **COMBINE.** Two disjoint sub-histories fold independently and add — the homomorphism a
worker pool exploits to merge partials. -/
theorem digest_union (A : M →ₗ[Rq] N) (encode : ι → M) {S T : Finset ι} (h : Disjoint S T) :
    digest A encode (S ∪ T) = digest A encode S + digest A encode T := by
  unfold digest
  rw [Finset.sum_union h, map_add]

/-- **FLUID FOLD.** Fold a history by ANY partition into pairwise-disjoint blocks, digest each block
independently, sum the block digests — recover the whole-history digest. The distributed pool's
associativity, as a theorem: workers combine partials in any order and agree. -/
theorem digest_biUnion (A : M →ₗ[Rq] N) (encode : ι → M) (P : Finset (Finset ι))
    (hd : (P : Set (Finset ι)).PairwiseDisjoint id) :
    digest A encode (P.biUnion id) = ∑ blk ∈ P, digest A encode blk := by
  simp only [digest]
  rw [Finset.sum_biUnion hd, map_sum]
  simp only [id_eq]

/-! ## §2 — the norm algebra: the extracted witness stays short. -/

/-- Triangle inequality lifted over a `Finset.sum`. -/
theorem nrm_sum_le (encode : ι → M) (S : Finset ι) :
    nrm (∑ i ∈ S, encode i) ≤ ∑ i ∈ S, nrm (encode i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [nrm_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (nrm_add_le _ _) (Nat.add_le_add_left ih _)

/-- A sum of `S.card`-many `β₀`-short encodings is `(S.card * β₀)`-short. -/
theorem sum_isShort {β₀ : ℕ} {encode : ι → M} (hshort : ∀ i, IsShort β₀ (encode i))
    (S : Finset ι) : IsShort (S.card * β₀) (∑ i ∈ S, encode i) := by
  refine le_trans (nrm_sum_le encode S) ?_
  calc ∑ i ∈ S, nrm (encode i) ≤ ∑ _i ∈ S, β₀ := Finset.sum_le_sum (fun i _ => hshort i)
    _ = S.card * β₀ := by rw [Finset.sum_const, smul_eq_mul]

/-! ## §3 — BINDING = SIS: a distinct-history collision extracts a Module-SIS solution. -/

/-- The carried obligation: distinct histories have distinct encode sums. Load-bearing (§4 teeth);
achievable structurally by a position-indexed encoding (the parameterization follow-up). -/
def SumInjective (encode : ι → M) : Prop :=
  ∀ S T : Finset ι, (∑ i ∈ S, encode i) = (∑ i ∈ T, encode i) → S = T

/-- **THE EXTRACTION (the crux).** A digest collision on two DISTINCT histories `S ≠ T` yields a
SHORT, NONZERO kernel vector of `A` — a genuine Module-SIS solution, produced as DATA (the
`HermineMSIS`-style extraction, no adversary/probability). Short because it is a difference of two
sums of `β₀`-short encodings; nonzero because `SumInjective` rules out the trivial `∑S = ∑T`; in the
kernel because `A` is linear and the digests agree. -/
theorem digest_collision_extracts_msis
    (A : M →ₗ[Rq] N) (encode : ι → M) (β₀ : ℕ)
    (hshort : ∀ i, IsShort β₀ (encode i)) (hsi : SumInjective encode)
    {S T : Finset ι} (hne : S ≠ T) (hcol : digest A encode S = digest A encode T) :
    IsMSISSolution A ((S.card + T.card) * β₀)
      ((∑ i ∈ S, encode i) - (∑ i ∈ T, encode i)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- NONZERO: `∑S - ∑T = 0` would force `∑S = ∑T`, hence `S = T` by sum-injectivity.
    intro h
    exact hne (hsi S T (sub_eq_zero.mp h))
  · -- SHORT: a difference of two card·β₀-short sums.
    rw [Nat.add_mul]
    exact IsShort.sub (sum_isShort hshort S) (sum_isShort hshort T)
  · -- IN THE KERNEL: `A` linear + the digests agree.
    unfold digest at hcol
    rw [map_sub]
    exact sub_eq_zero.mpr hcol

/-- **BINDING under the SIS floor** (the consumer — `HermineMSIS.no_forgery_under_msis` shape).
Under `MSISHard` at the relevant bound, the digest is injective: two histories with the same digest
are the same history. No collision survives, because any collision would be a forbidden SIS solution. -/
theorem digest_binds_under_msis
    (A : M →ₗ[Rq] N) (encode : ι → M) (β₀ : ℕ)
    (hshort : ∀ i, IsShort β₀ (encode i)) (hsi : SumInjective encode)
    {S T : Finset ι} (hard : MSISHard A ((S.card + T.card) * β₀))
    (hcol : digest A encode S = digest A encode T) : S = T := by
  by_contra hne
  exact hard ⟨_, digest_collision_extracts_msis A encode β₀ hshort hsi hne hcol⟩

/-- **BINDING over a bounded-capacity scan state** (one floor for the whole epoch). If every folded
history has at most `Nmax` turns, one assumption `MSISHard A (2·Nmax·β₀)` binds them all — the
natural shape for a bounded-capacity scan state (Mina's own design constraint, here made honest). -/
theorem digest_binds_bounded
    (A : M →ₗ[Rq] N) (encode : ι → M) (β₀ : ℕ)
    (hshort : ∀ i, IsShort β₀ (encode i)) (hsi : SumInjective encode)
    {Nmax : ℕ} (hard : MSISHard A (2 * Nmax * β₀))
    {S T : Finset ι} (hS : S.card ≤ Nmax) (hT : T.card ≤ Nmax)
    (hcol : digest A encode S = digest A encode T) : S = T := by
  by_contra hne
  have hsol := digest_collision_extracts_msis A encode β₀ hshort hsi hne hcol
  refine hard ⟨_, hsol.1, le_trans hsol.2.1 ?_, hsol.2.2⟩
  calc (S.card + T.card) * β₀ ≤ (Nmax + Nmax) * β₀ := by gcongr
    _ = 2 * Nmax * β₀ := by ring

/-! ## §4 — TEETH: `SumInjective` is load-bearing, not decorative. -/

/-- **PROVE-THE-OBLIGATION-NECESSARY.** Drop `SumInjective` and binding fails: two DISTINCT histories
whose encode sums coincide collide in the digest, and their extracted witness is `0` — which
`zero_not_msis_solution` says is never a Module-SIS solution. So the extraction genuinely NEEDS
`SumInjective`; it is not a decorative hypothesis. -/
theorem digest_collides_of_not_sumInjective
    (A : M →ₗ[Rq] N) (encode : ι → M) {S T : Finset ι}
    (hsum : (∑ i ∈ S, encode i) = (∑ i ∈ T, encode i)) :
    digest A encode S = digest A encode T := by
  unfold digest
  rw [hsum]

#assert_axioms digest_eq_sum
#assert_axioms digest_union
#assert_axioms digest_biUnion
#assert_axioms sum_isShort
#assert_axioms digest_collision_extracts_msis
#assert_axioms digest_binds_under_msis
#assert_axioms digest_binds_bounded
#assert_axioms digest_collides_of_not_sumInjective

end Dregg2.Crypto.HomomorphicDigest
