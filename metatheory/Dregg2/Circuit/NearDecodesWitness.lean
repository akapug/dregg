/-
# NEAR-WORD DECODES TO A UNIQUE WITNESS — the deterministic core of FriExtract,
GIVEN proximity.

THE BRICK: composing the committed pieces —

  * `RsUniqueDecoding.unique_nearest_codeword_radius` (uniqueness inside the radius),
  * `LagrangeExistence.natDegree_interpolate_lt` / `Lagrange.interpolate` (the
    constructed decoder output),
  * `DeployedUdrRegime.deployed_udr_unique_decoding` (uniqueness at the deployed
    rate `1/8`, radius `δ = 7/16`, over BabyBear) —

into the statement the FriExtract decoder RETURNS once link-A proximity is supplied:

  (1) **`near_word_decodes_existsUnique`** — a word `w` on `n` injective points that is
      within the unique-decoding radius `d < (n−k+1)/2` (ℕ-clean: `2·d < n−k+1`) of SOME
      `natDegree < k` polynomial is within that radius of EXACTLY ONE. Existence is the
      hypothesis; uniqueness is `unique_nearest_codeword_radius`. The "within radius"
      hypothesis is EXPLICIT — it is precisely what link A (FRI proximity) must supply,
      and nothing else is carried.
  (2) **`decoded_eq_interpolant`** — the unique witness is COMPUTED, not just abstract:
      any near polynomial equals the Lagrange interpolant of `w` on (the image of) any
      agreement set of ≥ k coordinates — the polynomial the concrete decoder builds.
  (3) **`near_decodes_of_interpolant_lowDegree`** — the decoder-side existence route:
      if the interpolant of `w` on an erasure-free set `S` (with `2·(n−|S|) < n−k+1`)
      already has `natDegree < k` — a CHECKABLE condition — then the `∃!` follows with
      the interpolant itself as the witness (Lagrange on the agreement set).
  (4) **`deployed_near_decodes_existsUnique`** — the same `∃!` at the DEPLOYED regime:
      rate `1/8` (`N = 8k`, `logBlowup = 3`), radius `δ = 7/16`, field
      `BabyBear = ZMod 2013265921`, uniqueness discharged by
      `deployed_udr_unique_decoding`. Plus the evaluation-vector form
      `deployed_near_decodes_existsUnique_evalVec` (`16·d ≤ 7·n`, which
      `deployed_radius_nat_iff` proves IS the `δ = 7/16` radius, exactly).

FIRE (hypotheses genuinely discharged on concrete corrupted BabyBear words):
  * `near_decodes_fires` / `near_decodes_fires_pins` — the corrupted word
    `w4 = ![1,2,3,42]` (codeword of `X + 1` with coordinate 3 GENUINELY corrupted,
    `RsUniqueDecoding.w4_corrupted`) decodes to exactly one polynomial, and any
    in-radius polynomial is FORCED to be `X + C 1`.
  * `interpolant_fire` — the decoder's actual output on `w4`'s agreement set `{0,1,2}`
    IS `X + C 1`: the Lagrange interpolant is pinned through `decoded_eq_interpolant`.
  * `near_decodes_interpolant_fires` — the `∃!` re-derived through the CHECKABLE
    interpolant route (3), all hypotheses concrete.
  * `deployed_near_decodes_fires` — the deployed-rate `∃!` on `DeployedUdrRegime`'s
    corrupted 16-point instance (`fireWord`, 1 error vs budget `⌊δ·16⌋ = 7`), through
    `deployed_udr_unique_decoding`.
  * `deployed_near_decodes_evalVec_fires` — the `16·d ≤ 7·n` form fired at `n = 8·1`
    on a fresh corrupted word `w8` (corruption REAL: `w8_corrupted`).

SCOPE (honest): the hypothesis "w is within the radius of SOME low-degree polynomial"
is link A (FRI proximity soundness, the BBHR18-style analysis; numeric error teeth in
`FriQuerySoundness`) and is taken as an explicit hypothesis of each theorem — NOT proved
here, NOT an axiom, and the only assumption carried. GIVEN it, everything is closed.
-/
import Dregg2.Circuit.RsUniqueDecoding
import Dregg2.Circuit.LagrangeExistence
import Dregg2.Circuit.DeployedUdrRegime
import Dregg2.Tactics

namespace Dregg2.Circuit.NearDecodesWitness

open Polynomial
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.LowDegreeUniqueness
open Dregg2.Circuit.RsUniqueDecoding
open Dregg2.Circuit.LagrangeExistence
open Dregg2.Circuit.DeployedUdrRegime

/-! ## §1 — The deterministic core: near word ⇒ exactly one low-degree witness. -/

section General

variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] {n k : ℕ}

/-- **Near word decodes to a unique witness.** If SOME `natDegree < k` polynomial has
evaluation vector within the unique-decoding radius of `w` — `2·d < n − k + 1`, the
ℕ-clean form of `d < (n−k+1)/2`; this is EXACTLY the proximity fact link A supplies —
then EXACTLY ONE does. Existence is the hypothesis; uniqueness is
`unique_nearest_codeword_radius`. This `∃!` is the polynomial the FriExtract decoder
returns. -/
theorem near_word_decodes_existsUnique (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F) (hk : k ≤ n)
    (hex : ∃ p : Polynomial F,
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) < n - k + 1) :
    ∃! p : Polynomial F,
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) < n - k + 1 :=
  let ⟨p, hp⟩ := hex
  ⟨p, hp, fun _q hq => unique_nearest_codeword_radius pts hinj w hk hq.1 hp.1 hq.2 hp.2⟩

end General

/-! ## §2 — The witness is COMPUTED: it is the Lagrange interpolant on any agreement set. -/

section Interpolant

variable {F : Type*} [Field F] [DecidableEq F] {n k : ℕ}

/-- The received word `w : Fin n → F`, transported along the (injective) point map to a
value function `F → F` — the shape `Lagrange.interpolate` consumes. Off the image of
`pts` it reads `0` (never consulted: interpolation only evaluates at nodes). -/
noncomputable def extendWord (pts : Fin n → F) (w : Fin n → F) : F → F :=
  Function.extend pts w fun _ => 0

omit [DecidableEq F] in
/-- At a genuine point, the transported word reads the original word. -/
theorem extendWord_apply (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F) (i : Fin n) : extendWord pts w (pts i) = w i :=
  hinj.extend_apply w _ i

/-- **The decoded witness IS the interpolant.** Any `natDegree < k` polynomial agreeing
with `w` on an agreement set `S` of ≥ k coordinates equals the Lagrange interpolant of
`w` on (the image of) `S` — the polynomial the concrete FriExtract decoder BUILDS from
queried values. Composes `natDegree_interpolate_lt` (LagrangeExistence) with
`lowDegree_agree_forces_eq` (LowDegreeUniqueness) at degree bound `|S|`. -/
theorem decoded_eq_interpolant (pts : Fin n → F) (hinj : Function.Injective pts)
    (w : Fin n → F) {p : Polynomial F} (hp : p.natDegree < k)
    (S : Finset (Fin n)) (hkS : k ≤ S.card)
    (hagree : ∀ i ∈ S, p.eval (pts i) = w i) :
    p = Lagrange.interpolate (S.image pts) id (extendWord pts w) := by
  have hScard : (S.image pts).card = S.card := Finset.card_image_of_injective S hinj
  have hSne : (S.image pts).Nonempty := by
    rw [← Finset.card_pos, hScard]
    omega
  have hqd := natDegree_interpolate_lt (S.image pts) hSne (extendWord pts w)
  refine lowDegree_agree_forces_eq p _ (S.image pts) ?_ hqd le_rfl ?_
  · omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hEv : (Lagrange.interpolate (S.image pts) id (extendWord pts w)).eval (pts i)
        = extendWord pts w (pts i) :=
      Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hx
    rw [hEv, extendWord_apply pts hinj w i]
    exact hagree i hi

/-- **Existence through the decoder (Lagrange on the agreement set).** If the interpolant
of `w` on an erasure-free coordinate set `S` — with fewer than `(n−k+1)/2` coordinates
missing, `2·(n − |S|) < n − k + 1` — already has `natDegree < k` (a condition the decoder
CHECKS on its computed output), then the `∃!` of §1 holds, with the interpolant itself as
the existence witness: it agrees with `w` on all of `S`, so its distance to `w` is at
most `n − |S|`, inside the radius. -/
theorem near_decodes_of_interpolant_lowDegree (pts : Fin n → F)
    (hinj : Function.Injective pts) (w : Fin n → F) (hk : k ≤ n)
    (S : Finset (Fin n)) (hgap : 2 * (n - S.card) < n - k + 1)
    (hdeg : (Lagrange.interpolate (S.image pts) id (extendWord pts w)).natDegree < k) :
    ∃! p : Polynomial F,
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) < n - k + 1 := by
  refine near_word_decodes_existsUnique pts hinj w hk ⟨_, hdeg, ?_⟩
  -- the interpolant disagrees with w only OUTSIDE S
  have hsub : (Finset.univ.filter fun i : Fin n =>
      ¬ w i = evalVec pts (Lagrange.interpolate (S.image pts) id (extendWord pts w)) i)
      ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_compl]
    intro hiS
    apply hi.2
    have hx : pts i ∈ S.image pts := Finset.mem_image_of_mem pts hiS
    have hEv : (Lagrange.interpolate (S.image pts) id (extendWord pts w)).eval (pts i)
        = extendWord pts w (pts i) :=
      Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hx
    show w i = (Lagrange.interpolate (S.image pts) id (extendWord pts w)).eval (pts i)
    rw [hEv, extendWord_apply pts hinj w i]
  have hdd : hammingDist w
      (evalVec pts (Lagrange.interpolate (S.image pts) id (extendWord pts w)))
      = (Finset.univ.filter fun i : Fin n =>
          ¬ w i = evalVec pts (Lagrange.interpolate (S.image pts) id (extendWord pts w)) i
        ).card := rfl
  have hdist : hammingDist w
      (evalVec pts (Lagrange.interpolate (S.image pts) id (extendWord pts w)))
      ≤ n - S.card := by
    rw [hdd]
    calc (Finset.univ.filter fun i : Fin n =>
          ¬ w i = evalVec pts (Lagrange.interpolate (S.image pts) id (extendWord pts w)) i
        ).card
        ≤ (Sᶜ : Finset (Fin n)).card := Finset.card_le_card hsub
      _ = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
  omega

end Interpolant

/-! ## §3 — The DEPLOYED regime: rate `1/8`, radius `δ = 7/16`, field BabyBear. -/

/-- **Deployed near-decode `∃!`** — at the shipped parameters (`logBlowup = 3` ⇒ rate
`1/8`, `N = 8k`; proximity parameter `δ = deployedDelta = 7/16`; field
`BabyBear = ZMod 2013265921`): if SOME `natDegree < k` polynomial disagrees with the
committed word `f` on at most `δ·N` of the `N` points — the link-A proximity fact —
then EXACTLY ONE does. Uniqueness is `deployed_udr_unique_decoding`
(DeployedUdrRegime §4); existence is the hypothesis. -/
theorem deployed_near_decodes_existsUnique {N k : ℕ} (hNk : N = 8 * k)
    (pts : Finset BabyBear) (hcard : pts.card = N)
    (f : BabyBear → BabyBear)
    (hex : ∃ p : Polynomial BabyBear, p.natDegree < k ∧
      (((pts.filter (fun x => p.eval x ≠ f x)).card : ℚ)) ≤ deployedDelta * N) :
    ∃! p : Polynomial BabyBear, p.natDegree < k ∧
      (((pts.filter (fun x => p.eval x ≠ f x)).card : ℚ)) ≤ deployedDelta * N :=
  let ⟨p, hp⟩ := hex
  ⟨p, hp, fun _q hq =>
    deployed_udr_unique_decoding hNk pts hcard f _ p hq.1 hp.1 hq.2 hp.2⟩

/-- The ℕ-clean deployed radius: `16·d ≤ 7·N` says EXACTLY `d ≤ δ·N` at
`δ = deployedDelta = 7/16` — no rounding slack in either direction. -/
theorem deployed_radius_nat_iff (d N : ℕ) :
    ((d : ℚ) ≤ deployedDelta * N) ↔ 16 * d ≤ 7 * N := by
  have hδ : deployedDelta = 7 / 16 := rfl
  constructor <;> intro hle
  · have h16 : (16 : ℚ) * d ≤ 7 * N := by
      rw [hδ] at hle
      linarith
    exact_mod_cast h16
  · have h16 : ((16 * d : ℕ) : ℚ) ≤ ((7 * N : ℕ) : ℚ) := Nat.cast_le.mpr hle
    push_cast at h16
    rw [hδ]
    linarith

/-- **Deployed near-decode `∃!`, evaluation-vector form** — the §1 geometry at the
deployed rate: `n = 8k` points, radius stated as `16·d ≤ 7·n` (which
`deployed_radius_nat_iff` proves is exactly `d ≤ (7/16)·n`). Inside the UDR because
`2·d ≤ (7/8)·n = 7k < 7k + 1 = n − k + 1` — the MDS `+1` strictness reserve
(`deployed_two_delta_lt_minDist`) is what the `< n − k + 1` uses. -/
theorem deployed_near_decodes_existsUnique_evalVec {k : ℕ}
    (pts : Fin (8 * k) → BabyBear) (hinj : Function.Injective pts)
    (w : Fin (8 * k) → BabyBear)
    (hex : ∃ p : Polynomial BabyBear, p.natDegree < k ∧
      16 * hammingDist w (evalVec pts p) ≤ 7 * (8 * k)) :
    ∃! p : Polynomial BabyBear, p.natDegree < k ∧
      16 * hammingDist w (evalVec pts p) ≤ 7 * (8 * k) := by
  obtain ⟨p, hp, hd⟩ := hex
  refine ⟨p, ⟨hp, hd⟩, ?_⟩
  rintro q ⟨hq, hdq⟩
  exact unique_nearest_codeword_radius pts hinj w (by omega) hq hp (by omega) (by omega)

/-! ## §4 — FIRE: every hypothesis discharged on concrete corrupted BabyBear words.

Fixtures reused from the committed base: `RsUniqueDecoding.pts4/w4` (the word
`![1,2,3,42]`, the codeword of `X + 1` with coordinate 3 corrupted — `w4_corrupted`
proves the error is REAL) and `DeployedUdrRegime.firePts/fireWord` (the 16-point
deployed-rate instance with 1 error against budget 7). -/

/-- **FIRE (§1).** The corrupted word `w4` decodes to EXACTLY ONE `natDegree < 2`
polynomial within the radius — existence witnessed by `X + C 1` at distance 1
(`2·1 < 3`), uniqueness through the theorem. -/
theorem near_decodes_fires :
    ∃! p : Polynomial BabyBear,
      p.natDegree < 2 ∧ 2 * hammingDist w4 (evalVec pts4 p) < 4 - 2 + 1 :=
  near_word_decodes_existsUnique pts4 pts4_injective w4 (by norm_num)
    ⟨X + C 1, by rw [natDegree_X_add_C]; norm_num,
      by rw [evalVec_pts4_XaddOne, w4_dist]; norm_num⟩

/-- **FIRE (the witness is pinned).** ANY `natDegree < 2` polynomial within the radius
of the corrupted `w4` IS `X + C 1` — the decoder's answer is forced, not chosen. -/
theorem near_decodes_fires_pins (p : Polynomial BabyBear) (hp : p.natDegree < 2)
    (hd : 2 * hammingDist w4 (evalVec pts4 p) < 4 - 2 + 1) :
    p = X + C 1 :=
  unique_nearest_codeword_radius pts4 pts4_injective w4 (by norm_num) hp
    (by rw [natDegree_X_add_C]; norm_num) hd
    (by rw [evalVec_pts4_XaddOne, w4_dist]; norm_num)

/-- **FIRE (§2, the computed output).** On `w4`'s agreement set `{0,1,2}` (the three
uncorrupted coordinates), the Lagrange interpolant the decoder builds IS `X + C 1` —
pinned through `decoded_eq_interpolant`, every hypothesis concrete. -/
theorem interpolant_fire :
    (X + C 1 : Polynomial BabyBear)
      = Lagrange.interpolate (({0, 1, 2} : Finset (Fin 4)).image pts4) id
          (extendWord pts4 w4) := by
  refine decoded_eq_interpolant (k := 2) pts4 pts4_injective w4 ?_ _ ?_ ?_
  · rw [natDegree_X_add_C]
    norm_num
  · decide
  · intro i hi
    fin_cases hi <;> simp [pts4, w4] <;> norm_num

/-- **FIRE (§2, existence through the decoder).** The `∃!` on `w4` re-derived through the
CHECKABLE route: the agreement set `{0,1,2}` misses 1 coordinate (`2·1 < 3`), its
interpolant has `natDegree = 1 < 2` (it is `X + C 1`, by `interpolant_fire`) — so
`near_decodes_of_interpolant_lowDegree` produces the same unique decoding. -/
theorem near_decodes_interpolant_fires :
    ∃! p : Polynomial BabyBear,
      p.natDegree < 2 ∧ 2 * hammingDist w4 (evalVec pts4 p) < 4 - 2 + 1 := by
  refine near_decodes_of_interpolant_lowDegree pts4 pts4_injective w4 (by norm_num)
    ({0, 1, 2} : Finset (Fin 4)) ?_ ?_
  · decide
  · rw [← interpolant_fire, natDegree_X_add_C]
    norm_num

/-- **FIRE (§3, deployed rate, through `deployed_udr_unique_decoding`).** On the
committed 16-point deployed-rate instance (`N = 16 = 8·2`, word `fireWord` = `x + 3`
corrupted at `0`, error budget `δ·16 = 7`): exactly one `natDegree < 2` polynomial is
within the deployed radius — existence witnessed by `X + C 3` via the committed
`fire_p_close`, uniqueness via the deployed-rate theorem. -/
theorem deployed_near_decodes_fires :
    ∃! p : Polynomial BabyBear, p.natDegree < 2 ∧
      (((firePts.filter (fun x => p.eval x ≠ fireWord x)).card : ℚ))
        ≤ deployedDelta * ((16 : ℕ) : ℚ) :=
  deployed_near_decodes_existsUnique (N := 16) (k := 2) rfl firePts firePts_card fireWord
    ⟨X + C 3, by rw [natDegree_X_add_C]; norm_num, fire_p_close⟩

/-- Eight distinct BabyBear points `{0,…,7}` — the smallest deployed-rate (`n = 8·1`)
evaluation domain for the evalVec form. -/
noncomputable def pts8 : Fin 8 → BabyBear := ![0, 1, 2, 3, 4, 5, 6, 7]

/-- The eight points are genuinely distinct in BabyBear (kernel-checked). -/
theorem pts8_injective : Function.Injective pts8 := by decide

/-- The received word: the constant codeword `5` with coordinate 5 corrupted to `42` —
1 error against the deployed budget `⌊(7/16)·8⌋ = 3`. -/
noncomputable def w8 : Fin 8 → BabyBear := ![5, 5, 5, 5, 5, 42, 5, 5]

/-- Codeword of `C 5` on `pts8` is the constant vector. -/
theorem evalVec_pts8_C5 :
    evalVec pts8 (C 5 : Polynomial BabyBear) = ![5, 5, 5, 5, 5, 5, 5, 5] := by
  funext i
  fin_cases i <;> simp [evalVec, pts8]

/-- The corruption is REAL: `w8` is NOT the codeword of `C 5` (coordinate 5 differs). -/
theorem w8_corrupted : w8 ≠ evalVec pts8 (C 5 : Polynomial BabyBear) := by
  rw [evalVec_pts8_C5]
  decide

/-- `w8` is at Hamming distance exactly 1 from the constant codeword. -/
theorem w8_dist : hammingDist w8 (![5, 5, 5, 5, 5, 5, 5, 5] : Fin 8 → BabyBear) = 1 := by
  decide

/-- **FIRE (§3, evalVec form).** At `n = 8·1`, the corrupted word `w8` is within the
deployed radius of `C 5` (`16·1 ≤ 7·8`) — so exactly one `natDegree < 1` polynomial
decodes it. Every hypothesis discharged on concrete data. -/
theorem deployed_near_decodes_evalVec_fires :
    ∃! p : Polynomial BabyBear, p.natDegree < 1 ∧
      16 * hammingDist w8 (evalVec pts8 p) ≤ 7 * (8 * 1) :=
  deployed_near_decodes_existsUnique_evalVec (k := 1) pts8 pts8_injective w8
    ⟨C 5, by rw [natDegree_C]; norm_num,
      by rw [evalVec_pts8_C5, w8_dist]; norm_num⟩

/-- The `16·d ≤ 7·N` radius used above is EXACTLY the deployed `δ = 7/16` radius,
instantiated at the fire's numbers: distance 1 on 8 points. -/
theorem deployed_radius_nat_fires :
    (((1 : ℕ) : ℚ) ≤ deployedDelta * ((8 : ℕ) : ℚ)) ↔ 16 * 1 ≤ 7 * 8 :=
  deployed_radius_nat_iff 1 8

/-! ## §5 — Axiom hygiene: every theorem kernel-clean. -/

#assert_axioms near_word_decodes_existsUnique
#assert_axioms extendWord_apply
#assert_axioms decoded_eq_interpolant
#assert_axioms near_decodes_of_interpolant_lowDegree
#assert_axioms deployed_near_decodes_existsUnique
#assert_axioms deployed_radius_nat_iff
#assert_axioms deployed_near_decodes_existsUnique_evalVec
#assert_axioms near_decodes_fires
#assert_axioms near_decodes_fires_pins
#assert_axioms interpolant_fire
#assert_axioms near_decodes_interpolant_fires
#assert_axioms deployed_near_decodes_fires
#assert_axioms pts8_injective
#assert_axioms evalVec_pts8_C5
#assert_axioms w8_corrupted
#assert_axioms w8_dist
#assert_axioms deployed_near_decodes_evalVec_fires
#assert_axioms deployed_radius_nat_fires

end Dregg2.Circuit.NearDecodesWitness
