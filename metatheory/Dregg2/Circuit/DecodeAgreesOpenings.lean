/-
# DecodeAgreesOpenings — the bridge from the QUERY CHECK to the DECODED codeword.

THE SEAM THIS FILE CLOSES: `FriQuerySoundness.Accepts` is the verifier's opening check —
the received word `w` agrees with a claimed codeword at every queried position. The
RS-decoding bricks (`RsUniqueDecoding`, `LowDegreeUniqueness`, `LagrangeExistence`) speak
about the low-degree polynomial the extractor DECODES from `w`. This file states the
acceptance predicate in the RS `evalVec` vocabulary and proves that the two ends meet:

  (1) **`decode_agrees_on_queries`** — if the query check passes against the decoded
      polynomial's codeword (`Accepts w (evalVec pts p) Q`), then `p`'s evaluation vector
      AGREES with the received word at every queried position: the extracted polynomial is
      CONSISTENT with the openings the verifier checked (`accepts_iff_openings` is the
      vocabulary bridge, definitional and stated so the two module languages are literally
      the same predicate).
  (2) **`decoder_output_agrees_and_unique`** — the decoder-side composition: when `p` is
      in the unique-decoding ball of `w` (the `RsUniqueDecoding.decode_wellDefined`
      regime) AND the openings check passes against `p`, then `p` agrees with `w` on the
      queried set and is the UNIQUE in-ball low-degree polynomial
      (`unique_nearest_codeword` supplies uniqueness).
  (3) **`openings_pin_polynomial`** — the openings DETERMINE the extracted polynomial:
      two `natDegree < k` polynomials that BOTH pass the opening check against `w` on a
      query sample touching `≥ k` distinct points are EQUAL
      (`lowDegree_agree_forces_eq` on the queried point set `queriedPts`).
  (4) **`openings_realize_unique_interpolant`** — existence, not just uniqueness: for ANY
      received word and ANY nonempty query sample there is EXACTLY ONE polynomial of
      `natDegree < |queried points|` passing the opening check (Lagrange witness through
      `interpolant_exists`), so "the polynomial the openings pin" always exists.

Deployed instantiations: `openings_pin_polynomial_babyBear` (BabyBear = `ZMod 2013265921`,
the shipped prover field) and `openings_pin_polynomial_deployed38` at the shipped
`plonky3ProverParams.numQueries = 38` query count (`DeployedUdrRegime.prover_numQueries`).

Both polarities on concrete BabyBear data (`pts4 = ![0,1,2,3]`, `w4 = ![1,2,3,42]` — the
codeword of `X + 1` with coordinate 3 GENUINELY corrupted, `RsUniqueDecoding.w4_corrupted`):
  * FIRE — `fire_accepts`/`fire_accepts_q`: the 3-query sample `![0,1,2]` (which misses the
    corruption) PASSES against both spellings of the decoded polynomial; `fire_pins`: those
    openings FORCE `X + C 1 = C 1 + X` through theorem (3), every hypothesis discharged
    (`k = 2 ≤ 3` distinct queried points, kernel-counted by `fire_queried_card`);
    `fire_decoder_bridge`: theorem (2) discharged with the REAL ball data (distance 1,
    radius `2·1 + 2 ≤ 4`); `fire_openings_realize`: the `∃!` of (4) on the same sample.
  * BITE — `underdetermined_openings_bite`: with only ONE queried point, TWO distinct
    low-degree polynomials (`X + C 1` and `C 1`) both pass the opening check — the
    `k ≤ |queried points|` hypothesis of (3) is load-bearing, not decorative.

SCOPE (honest): this file is the CONSISTENCY/DETERMINATION bridge — accepted openings pin
the extracted polynomial. That FRI acceptance certifies `w` is within the unique-decoding
radius at all (so the ball in (2) is inhabited) is the separate proximity seam
(`FriQuerySoundness` bounds its failure probability at the deployed `38` queries,
`δ = 7/16`); it is used here only as the hypothesis it honestly is.
-/
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.RsUniqueDecoding
import Dregg2.Circuit.LagrangeExistence
import Dregg2.Circuit.DeployedUdrRegime
import Dregg2.Tactics

namespace Dregg2.Circuit.DecodeAgreesOpenings

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriQuerySoundness (Accepts)
open Dregg2.Circuit.LowDegreeUniqueness (lowDegree_agree_forces_eq)
open Dregg2.Circuit.LagrangeExistence (interpolant_exists)
open Dregg2.Circuit.RsUniqueDecoding

/-! ## §1 — The vocabulary bridge: `Accepts` against `evalVec` IS the opening check.

`FriQuerySoundness.Accepts w g Q` says `∀ i, w (Q i) = g (Q i)`; with `g := evalVec pts p`
(the RS codeword of the decoded polynomial, `RsUniqueDecoding.evalVec`) the queried values
of `w` are exactly `p`'s evaluations at the queried points. Definitionally equal — stated
so the two modules' languages are interchangeable downstream. -/

/-- The set of FIELD points a query sample `Q` touches: the image of the sample under the
evaluation-point family `pts`. This is the set the interpolation bricks count. -/
def queriedPts {F : Type*} [DecidableEq F] {n m : ℕ}
    (pts : Fin n → F) (Q : Fin m → Fin n) : Finset F :=
  Finset.image (fun i => pts (Q i)) Finset.univ

/-- Every queried point is in the queried set (the sample is what the set counts). -/
theorem mem_queriedPts {F : Type*} [DecidableEq F] {n m : ℕ}
    (pts : Fin n → F) (Q : Fin m → Fin n) (i : Fin m) :
    pts (Q i) ∈ queriedPts pts Q :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- **The vocabulary bridge (definitional).** The FRI opening check against the decoded
polynomial's RS codeword — `Accepts w (evalVec pts p) Q` — IS the statement that every
queried value of the received word is `p`'s evaluation at the queried point. -/
theorem accepts_iff_openings {F : Type*} [CommRing F] {n m : ℕ}
    (pts : Fin n → F) (w : Fin n → F) (p : Polynomial F) (Q : Fin m → Fin n) :
    Accepts w (evalVec pts p) Q ↔ ∀ i, w (Q i) = p.eval (pts (Q i)) :=
  Iff.rfl

/-- **`decode_agrees_on_queries`.** If the query check passes against the decoded
polynomial `p` (`Accepts w (evalVec p) Q`), then `p`'s evaluation vector agrees with the
received word at every queried position — the extracted polynomial is CONSISTENT with the
openings the verifier checked. (In `evalVec` vocabulary; `_eval` gives the pointwise
polynomial form.) -/
theorem decode_agrees_on_queries {F : Type*} [CommRing F] {n m : ℕ}
    (pts : Fin n → F) (w : Fin n → F) {p : Polynomial F} {Q : Fin m → Fin n}
    (hacc : Accepts w (evalVec pts p) Q) :
    ∀ i, w (Q i) = evalVec pts p (Q i) :=
  hacc

/-- Pointwise polynomial-evaluation form of `decode_agrees_on_queries`. -/
theorem decode_agrees_on_queries_eval {F : Type*} [CommRing F] {n m : ℕ}
    (pts : Fin n → F) (w : Fin n → F) {p : Polynomial F} {Q : Fin m → Fin n}
    (hacc : Accepts w (evalVec pts p) Q) :
    ∀ i, w (Q i) = p.eval (pts (Q i)) :=
  hacc

/-! ## §2 — The decoder-side composition: in-ball + accepted ⇒ consistent AND unique.

`RsUniqueDecoding.decode_wellDefined` says the unique-decoding ball holds at most one
low-degree polynomial; `Accepts` says the openings match. Together: the decoder's output
agrees with the received word on the queried set, and NO other in-ball low-degree
polynomial exists — the openings were checked against THE decoding, not a decoding. -/

/-- **The decoder output is consistent with the openings AND unique in the ball.** If `p`
is a `natDegree < k` polynomial within the unique-decoding radius of `w`
(`2·d(w, evalVec p) + k ≤ n`, the `RsUniqueDecoding` regime) and the opening check passes
against `p`'s codeword, then (a) `p` agrees with `w` at every queried position and (b) any
other in-ball `natDegree < k` polynomial equals `p` (`unique_nearest_codeword`). -/
theorem decoder_output_agrees_and_unique {F : Type*} [CommRing F] [IsDomain F]
    [DecidableEq F] {n k m : ℕ}
    (pts : Fin n → F) (hinj : Function.Injective pts) (w : Fin n → F) {p : Polynomial F}
    (hp : p.natDegree < k) (hball : 2 * hammingDist w (evalVec pts p) + k ≤ n)
    {Q : Fin m → Fin n} (hacc : Accepts w (evalVec pts p) Q) :
    (∀ i, w (Q i) = evalVec pts p (Q i)) ∧
      ∀ q : Polynomial F, q.natDegree < k →
        2 * hammingDist w (evalVec pts q) + k ≤ n → q = p :=
  ⟨hacc, fun _q hq hqball => unique_nearest_codeword pts hinj w hq hp hqball hball⟩

/-! ## §3 — The openings DETERMINE the extracted polynomial.

The uniqueness half without any ball hypothesis: two low-degree polynomials that BOTH pass
the opening check against the same received word, on a sample touching at least `k`
distinct points, are EQUAL — `lowDegree_agree_forces_eq` on `queriedPts`. So the verifier's
opening checks pin a UNIQUE extracted witness. -/

/-- **Openings pin the polynomial.** If `p, q` both have `natDegree < k` and both pass the
opening check against `w` on the sample `Q`, and `Q` touches `≥ k` distinct field points,
then `p = q`: the checked openings determine the extracted polynomial. -/
theorem openings_pin_polynomial {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n k m : ℕ} (pts : Fin n → F) (w : Fin n → F) {p q : Polynomial F} {Q : Fin m → Fin n}
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hcard : k ≤ (queriedPts pts Q).card)
    (haccp : Accepts w (evalVec pts p) Q) (haccq : Accepts w (evalVec pts q) Q) :
    p = q := by
  refine lowDegree_agree_forces_eq p q (queriedPts pts Q) hp hq hcard ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact (haccp i).symm.trans (haccq i)

/-- **Openings decode uniquely (`∃!` given `∃`).** If SOME `natDegree < k` polynomial
passes the opening check (the proximity seam's promise) and the sample touches `≥ k`
distinct points, then EXACTLY ONE does — the extracted witness is well-defined. -/
theorem openings_decode_existsUnique {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n k m : ℕ} (pts : Fin n → F) (w : Fin n → F) {Q : Fin m → Fin n}
    (hcard : k ≤ (queriedPts pts Q).card)
    (hex : ∃ p : Polynomial F, p.natDegree < k ∧ Accepts w (evalVec pts p) Q) :
    ∃! p : Polynomial F, p.natDegree < k ∧ Accepts w (evalVec pts p) Q :=
  let ⟨p, hp⟩ := hex
  ⟨p, hp, fun _q hq => openings_pin_polynomial pts w hq.1 hp.1 hcard hq.2 hp.2⟩

/-! ## §4 — Existence: the pinned polynomial always EXISTS at the queried-card degree.

Uniqueness alone could be vacuous; here the Lagrange brick supplies the witness. At degree
bound `k := |queried points|` (exactly the information the openings carry) there is always
exactly one polynomial passing the check — genuinely `∃!`, no hypothesis about `w`. -/

/-- **The openings realize a unique interpolant.** For ANY received word `w` and ANY
nonempty query sample `Q` (over injective evaluation points), there is EXACTLY ONE
polynomial of `natDegree < |queriedPts|` passing the opening check: existence by Lagrange
interpolation of the opened values (`interpolant_exists`), uniqueness by
`openings_pin_polynomial` at `k := |queriedPts|`. -/
theorem openings_realize_unique_interpolant {F : Type*} [Field F] [DecidableEq F]
    {n m : ℕ} (pts : Fin n → F) (hinj : Function.Injective pts) (w : Fin n → F)
    (Q : Fin m → Fin n) (hm : 0 < m) :
    ∃! p : Polynomial F,
      p.natDegree < (queriedPts pts Q).card ∧ Accepts w (evalVec pts p) Q := by
  classical
  -- The opened values as a function on field points (well-defined since `pts` is injective).
  set v : F → F := fun x => if h : ∃ i, pts (Q i) = x then w (Q h.choose) else 0 with hv
  have hSne : (queriedPts pts Q).Nonempty := ⟨pts (Q ⟨0, hm⟩), mem_queriedPts pts Q ⟨0, hm⟩⟩
  have hvq : ∀ i, v (pts (Q i)) = w (Q i) := by
    intro i
    have hex : ∃ j, pts (Q j) = pts (Q i) := ⟨i, rfl⟩
    have hQ : Q hex.choose = Q i := hinj hex.choose_spec
    simp only [hv]
    rw [dif_pos hex, hQ]
  obtain ⟨p, hpd, hpe⟩ := interpolant_exists (queriedPts pts Q) hSne v
  refine openings_decode_existsUnique pts w le_rfl ⟨p, hpd, ?_⟩
  intro i
  show w (Q i) = p.eval (pts (Q i))
  rw [hpe _ (mem_queriedPts pts Q i), hvq i]

/-! ## §5 — Deployed instantiations: BabyBear, and the shipped 38-query sample. -/

/-- `openings_pin_polynomial` over **BabyBear** (`ZMod 2013265921`) — the deployed
prover's field. Pure instantiation. -/
theorem openings_pin_polynomial_babyBear {n k m : ℕ}
    (pts : Fin n → BabyBear) (w : Fin n → BabyBear) {p q : Polynomial BabyBear}
    {Q : Fin m → Fin n} (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hcard : k ≤ (queriedPts pts Q).card)
    (haccp : Accepts w (evalVec pts p) Q) (haccq : Accepts w (evalVec pts q) Q) :
    p = q :=
  openings_pin_polynomial pts w hp hq hcard haccp haccq

/-- **At the SHIPPED query count.** The sample length is literally the deployed
`plonky3ProverParams.numQueries` (`= 38` by `DeployedUdrRegime.prover_numQueries`,
from `circuit/src/plonky3_prover.rs:99`): if the deployed 38-query opening check passes
for two `natDegree < k` candidates and the 38 queries touch `≥ k` distinct points, the
extracted polynomial is pinned. -/
theorem openings_pin_polynomial_deployed38 {n k : ℕ}
    (pts : Fin n → BabyBear) (w : Fin n → BabyBear) {p q : Polynomial BabyBear}
    {Q : Fin (Dregg2.Circuit.DeployedUdrRegime.plonky3ProverParams.numQueries) → Fin n}
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hcard : k ≤ (queriedPts pts Q).card)
    (haccp : Accepts w (evalVec pts p) Q) (haccq : Accepts w (evalVec pts q) Q) :
    p = q :=
  openings_pin_polynomial pts w hp hq hcard haccp haccq

/-! ## §6 — FIRE: concrete BabyBear data (the corrupted word of `RsUniqueDecoding`).

`pts4 = ![0,1,2,3]`, `w4 = ![1,2,3,42]` — the codeword of `X + 1` with coordinate 3
genuinely corrupted (`RsUniqueDecoding.w4_corrupted`). The verifier samples the 3 queries
`![0,1,2]` (missing the corruption): the opening check PASSES against the decoded
polynomial, and those openings PIN it. -/

/-- The concrete 3-query sample: positions `0, 1, 2` of the 4-point domain. -/
def Q3 : Fin 3 → Fin 4 := ![0, 1, 2]

/-- **FIRE (the opening check passes).** The received word `w4` agrees with the decoded
polynomial's codeword `evalVec pts4 (X + C 1) = ![1,2,3,4]` at all three queried
positions — the sample missed the corrupted coordinate 3. -/
theorem fire_accepts : Accepts w4 (evalVec pts4 (X + C 1 : Polynomial BabyBear)) Q3 := by
  intro i
  rw [evalVec_pts4_XaddOne]
  fin_cases i <;> decide

/-- The other spelling `C 1 + X` of the same codeword also passes the same openings. -/
theorem fire_accepts_q : Accepts w4 (evalVec pts4 (C 1 + X : Polynomial BabyBear)) Q3 := by
  intro i
  rw [evalVec_pts4_OneAddX]
  fin_cases i <;> decide

/-- **FIRE (consistency, via the bridge).** The extracted polynomial `X + C 1` is
consistent with every opening the verifier checked — `decode_agrees_on_queries` discharged
on the concrete data. -/
theorem fire_openings_agree :
    ∀ i, w4 (Q3 i) = (X + C 1 : Polynomial BabyBear).eval (pts4 (Q3 i)) :=
  decode_agrees_on_queries_eval pts4 w4 fire_accepts

/-- The 3-query sample touches exactly 3 distinct BabyBear points (kernel-counted). -/
theorem fire_queried_card : (queriedPts pts4 Q3).card = 3 := by decide

/-- **FIRE (the openings pin the witness).** Both in-vocabulary spellings of the decoded
polynomial pass the same 3 openings, and `3 ≥ k = 2` distinct points force them EQUAL —
`X + C 1 = C 1 + X` derived THROUGH `openings_pin_polynomial` (not by `ring`), every
hypothesis discharged on concrete deployed-field data. -/
theorem fire_pins : (X + C 1 : Polynomial BabyBear) = C 1 + X := by
  refine openings_pin_polynomial (k := 2) pts4 w4 ?_ ?_ ?_ fire_accepts fire_accepts_q
  · rw [natDegree_X_add_C]
    norm_num
  · have h : (C 1 + X : Polynomial BabyBear).natDegree ≤ 1 := by compute_degree
    omega
  · rw [fire_queried_card]
    norm_num

/-- **FIRE (the decoder-side composition, real ball data).** `X + C 1` is in the
unique-decoding ball of `w4` (distance 1, radius `2·1 + 2 ≤ 4`) and passes the openings,
so it agrees with `w4` at every queried position AND is the unique in-ball `natDegree < 2`
polynomial — `decoder_output_agrees_and_unique` fully discharged. -/
theorem fire_decoder_bridge :
    (∀ i, w4 (Q3 i) = evalVec pts4 (X + C 1 : Polynomial BabyBear) (Q3 i)) ∧
      ∀ q : Polynomial BabyBear, q.natDegree < 2 →
        2 * hammingDist w4 (evalVec pts4 q) + 2 ≤ 4 → q = X + C 1 := by
  refine decoder_output_agrees_and_unique (k := 2) pts4 pts4_injective w4 ?_ ?_ fire_accepts
  · rw [natDegree_X_add_C]
    norm_num
  · rw [evalVec_pts4_XaddOne, w4_dist]

/-- **FIRE (`∃!` realized).** On the same concrete sample there is EXACTLY ONE polynomial
of `natDegree < 3` passing the opening check — existence and uniqueness both discharged. -/
theorem fire_openings_realize :
    ∃! p : Polynomial BabyBear,
      p.natDegree < (queriedPts pts4 Q3).card ∧ Accepts w4 (evalVec pts4 p) Q3 :=
  openings_realize_unique_interpolant pts4 pts4_injective w4 Q3 (by norm_num)

/-! ## §7 — BITE: too few distinct openings do NOT pin the polynomial.

The `k ≤ |queriedPts|` hypothesis of §3 is load-bearing: with a single queried point, two
DISTINCT `natDegree < 2` polynomials both pass the opening check against `w4`. -/

/-- The undersized sample: a single query at position `0`. -/
def Q1 : Fin 1 → Fin 4 := ![0]

/-- Codeword of the constant `C 1` on `pts4` is `![1,1,1,1]`. -/
theorem evalVec_pts4_C1 : evalVec pts4 (C 1 : Polynomial BabyBear) = ![1, 1, 1, 1] := by
  funext i
  fin_cases i <;> simp [evalVec, pts4]

/-- **BITE.** On the single-point sample `Q1`, BOTH `X + C 1` and the constant `C 1` pass
the opening check against `w4` (`w4 0 = 1` matches both), yet they are DISTINCT
polynomials — with fewer than `k` distinct queried points the openings genuinely fail to
pin the witness, so the cardinality hypothesis of `openings_pin_polynomial` is necessary. -/
theorem underdetermined_openings_bite :
    Accepts w4 (evalVec pts4 (X + C 1 : Polynomial BabyBear)) Q1 ∧
      Accepts w4 (evalVec pts4 (C 1 : Polynomial BabyBear)) Q1 ∧
      (X + C 1 : Polynomial BabyBear) ≠ C 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [evalVec_pts4_XaddOne]
    fin_cases i
    decide
  · intro i
    rw [evalVec_pts4_C1]
    fin_cases i
    decide
  · intro h
    have hx : (X : Polynomial BabyBear) = 0 := by
      have h' := h
      rwa [add_comm, ← sub_eq_zero, add_sub_cancel_left] at h'
    exact X_ne_zero hx

/-! ## §8 — Axiom hygiene: every theorem kernel-clean. -/

#assert_axioms mem_queriedPts
#assert_axioms accepts_iff_openings
#assert_axioms decode_agrees_on_queries
#assert_axioms decode_agrees_on_queries_eval
#assert_axioms decoder_output_agrees_and_unique
#assert_axioms openings_pin_polynomial
#assert_axioms openings_decode_existsUnique
#assert_axioms openings_realize_unique_interpolant
#assert_axioms openings_pin_polynomial_babyBear
#assert_axioms openings_pin_polynomial_deployed38
#assert_axioms fire_accepts
#assert_axioms fire_accepts_q
#assert_axioms fire_openings_agree
#assert_axioms fire_queried_card
#assert_axioms fire_pins
#assert_axioms fire_decoder_bridge
#assert_axioms fire_openings_realize
#assert_axioms evalVec_pts4_C1
#assert_axioms underdetermined_openings_bite

end Dregg2.Circuit.DecodeAgreesOpenings
