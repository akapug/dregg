/-
# `Dregg2.Crypto.FoBookkeeping` — the QUANTITATIVE Fujisaki–Okamoto advantage bound.

`MlKemIndCca.lean` captured the classical-ROM FO transform STRUCTURALLY: `decaps_oracle_simulable`
proves the CCA decapsulation oracle EQUALS a secret-free simulator on honest ciphertexts,
`ind_cpa_reduces_to_mlwe` proves an IND-CPA distinguisher IS a decisional-MLWE distinguisher, and
`QROMInjective` names the random-oracle idealisation. What it did NOT do is BOOKKEEP the advantage: the
structural composition is not the theorem, the advantage bound is (ember asked for this explicitly). This
file closes that half in the tree's finite-ℚ probability style — the SAME machinery that let us prove
`HermineTSUF.forking_probability_bound` (a `Fin n → ℚ` / `ℕ → ℚ` weight world + Mathlib inequalities, NO
measure theory).

## The bound

The classical Fujisaki–Okamoto (Hofheinz–Hövelmanns–Kiltz "modular FO") IND-CCA bound has the shape

  `Adv^IND-CCA(A) ≤ f(Adv^IND-CPA(B)) + (decaps-simulation failure) + (correctness-error / γ-spreadness)`,

obtained by a GAME-HOPPING chain: G₀ (real IND-CCA) → G₁ (decaps oracle replaced by the secret-free
simulator) → G₂ (the T-transform derandomisation idealised) → G₃ (the U-transform / IND-CPA game, where
the challenge key is a guess, win-probability `1/2`). Each hop is bounded by ONE term:

* **G₀ → G₁ — the decaps-simulation failure (`simFail`).** Identical-until-bad: the two games differ only
  when the secret-free simulator disagrees with the real decapsulation oracle, an event
  `MlKemIndCca.decaps_oracle_simulable` proves NEVER fires on an honest ciphertext
  (`sim_no_divergence_on_honest` below), so `simFail` is carried entirely by malformed / unqueried
  ciphertexts and bounded by the spreadness term (a union bound over the `q_D` decapsulation queries).
* **G₁ → G₂ — the correctness-error / γ-spreadness (`corrSpread`).** The T-transform replaces the
  derandomised coins `r = G(m)`; it fails on a correctness-error coin (probability `δ`) or a non-γ-spread
  colliding ciphertext (probability `2^(−γ)`), union-bounded over the `q_G` random-oracle queries to
  `q_G·(δ + 2^(−γ))` (`t_transform_hop_bound`).
* **G₂ → G₃ — the IND-CPA advantage (`f(Adv^IND-CPA(B))`).** The idealised game IS the IND-CPA game on the
  underlying Kyber CPAPKE; its advantage is `f` of the IND-CPA advantage of the reduction `B`, whose
  structural content is decisional-MLWE (`cpa_hop_grounded_in_mlwe`, re-exporting
  `MlKemIndCca.ind_cpa_reduces_to_mlwe`) — bottoming out at `Lattice.MLWESearchHard`, NO fresh carrier.

The composition is the game-hopping telescope `|g 0 − g m| ≤ ∑_{k<m} |g k − g(k+1)|` (the ℚ analog of
`HermineHiding.statDist_telescope`, proved by induction from the triangle inequality), specialised to the
three FO hops. The union-bound accumulation `∑ᵢ pᵢ ≤ q·pmax` is `Finset.sum_le_card_nsmul` (the ℚ analog
of `HermineTSUF.oracle_view_within_tv`'s `Q·ε`).

## No named-carrier laundering

The only assumed objects are the ALREADY-established floors: `Lattice.MLWESearchHard` (through
`MlKemIndCca`'s IND-CPA→MLWE reduction, re-exported here as `cpa_hop_grounded_in_mlwe`) and the
random-oracle idealisation `MlKemIndCca.QROMInjective` (stated in the open, cited to HHK'17 /
Don–Fehr–Majenz–Schaffner). `δ` (correctness error) and `2^(−γ)` (γ-spreadness) are honestly-named PKE
parameters, not hardness carriers. No `def …Hard` is introduced or used as a hypothesis. The game-hop
terms are REAL ℚ quantities the reduction supplies; the theorem is the pure-ℚ inequality composing them,
proved with no `sorry` and `#assert_axioms`-clean.

Cite: Hofheinz–Hövelmanns–Kiltz "A Modular Analysis of the Fujisaki–Okamoto Transformation" (TCC 2017);
Fujisaki–Okamoto; FIPS 203 (ML-KEM); Bellare–Rogaway game-playing / identical-until-bad.
-/
import Dregg2.Crypto.MlKemIndCca

namespace Dregg2.Crypto.FoBookkeeping

open Dregg2.Crypto.MlKemIndCca
open Dregg2.Crypto.Lattice

/-! ## PART 0 — the game-hopping composition engine (finite-ℚ, no measure theory).

Two reusable cores: the advantage telescope (triangle inequality summed over a game chain) and the
union bound (independent bad events accumulate). These are the exact ℚ analogs of
`HermineHiding.statDist_telescope` and `HermineTSUF.oracle_view_within_tv` — standard probability
lemmas, no hardness content. -/

section Engine

/-- **Distinguishing advantage** against a `1/2` guess: `|win − 1/2|`. The IND-CCA / IND-CPA advantage in
the finite model is this deviation of the adversary's win-probability from a coin flip. -/
def Adv (win : ℚ) : ℚ := |win - 1/2|

/-- **The game-hopping telescope.** For any chain of win-probabilities `g 0, g 1, …, g m`,
`|g 0 − g m| ≤ ∑_{k<m} |g k − g(k+1)|` — the total advantage swing is at most the sum of the per-hop
swings. Proved by induction from the triangle inequality (`abs_sub_le`); the exact ℚ analog of
`HermineHiding.statDist_telescope`, and the composition engine every game-hopping proof telescopes
through. -/
theorem abs_telescope (g : ℕ → ℚ) (m : ℕ) :
    |g 0 - g m| ≤ ∑ k ∈ Finset.range m, |g k - g (k + 1)| := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have htri : |g 0 - g (m + 1)| ≤ |g 0 - g m| + |g m - g (m + 1)| := abs_sub_le _ _ _
    linarith [ih]

/-- **The telescope, per-hop bounded.** If each game hop swings by at most `ε k`, the total advantage
swing is at most `∑ ε`. This is the shape a game-hopping proof uses: bound each adjacent transition, sum
the bounds. -/
theorem abs_telescope_bound (g ε : ℕ → ℚ) (m : ℕ)
    (h : ∀ k, k < m → |g k - g (k + 1)| ≤ ε k) :
    |g 0 - g m| ≤ ∑ k ∈ Finset.range m, ε k :=
  calc |g 0 - g m| ≤ ∑ k ∈ Finset.range m, |g k - g (k + 1)| := abs_telescope g m
    _ ≤ ∑ k ∈ Finset.range m, ε k :=
        Finset.sum_le_sum (fun k hk => h k (Finset.mem_range.mp hk))

/-- **The union bound.** Over a finite query set, if each query is "bad" with probability at most `pmax`,
the total bad mass is at most `|queries| • pmax`. Directly `Finset.sum_le_card_nsmul`; the ℚ analog of
`HermineTSUF.oracle_view_within_tv`'s `Q·ε`. This accumulates the per-query correctness / spreadness /
simulation-failure contributions. -/
theorem union_bound {ι : Type*} (queries : Finset ι) (p : ι → ℚ) (pmax : ℚ)
    (h : ∀ i ∈ queries, p i ≤ pmax) :
    ∑ i ∈ queries, p i ≤ queries.card • pmax :=
  Finset.sum_le_card_nsmul queries p pmax h

end Engine

/-! ## PART 1 — the FO game chain and the IND-CCA advantage bound (THE THEOREM).

The four-game FO chain, and the bound composing the three hops. `fo_ind_cca_bound` is the requested
theorem — the advantage bookkeeping, derived through the game-hopping telescope. -/

section FoBound

/-- **The FO game chain.** `g 0` = real IND-CCA win-probability; `g 1` = win with the decapsulation oracle
replaced by the secret-free simulator; `g 2` = win with the T-transform derandomisation idealised;
`g 3` (and beyond) = `1/2`, the guessing probability of the final IND-CPA game. -/
def foChain (cca hyb ideal : ℚ) (k : ℕ) : ℚ :=
  if k = 0 then cca else if k = 1 then hyb else if k = 2 then ideal else 1 / 2

/-- **The FO per-hop bounds.** `step 0` = the decaps-simulation failure; `step 1` = the correctness /
γ-spreadness term; `step k≥2` = the IND-CPA advantage term. -/
def foSteps (simFail corrSpread cpaTerm : ℚ) (k : ℕ) : ℚ :=
  if k = 0 then simFail else if k = 1 then corrSpread else cpaTerm

/-- **`fo_ind_cca_bound` — THE FUJISAKI–OKAMOTO IND-CCA ADVANTAGE BOUND.** Given the three game-hop bounds:
* `hSim`: G₀→G₁ swings by at most the decaps-simulation failure `simFail` (identical-until-bad);
* `hT`:  G₁→G₂ swings by at most the correctness / γ-spreadness term `corrSpread`;
* `hCpa`: G₂→G₃ swings by at most the IND-CPA advantage term `cpaTerm` (the `1/2`-guessing final game),

the IND-CCA advantage of `A` is bounded by their sum:
`Adv^IND-CCA(A) ≤ cpaTerm + simFail + corrSpread`. This is the classical-ROM FO bookkeeping — proved by
telescoping the three hops over the four-game chain (`abs_telescope_bound`), NOT re-asserted. The terms
are grounded in PART 2: `cpaTerm` in `MLWESearchHard`, `simFail` in `decaps_oracle_simulable`,
`corrSpread` in the honestly-named `δ`/`2^(−γ)` PKE parameters. -/
theorem fo_ind_cca_bound (cca hyb ideal simFail cpaTerm corrSpread : ℚ)
    (hSim : |cca - hyb| ≤ simFail)
    (hT : |hyb - ideal| ≤ corrSpread)
    (hCpa : |ideal - 1 / 2| ≤ cpaTerm) :
    Adv cca ≤ cpaTerm + simFail + corrSpread := by
  -- chain / step evaluations
  have c0 : foChain cca hyb ideal 0 = cca := by simp [foChain]
  have c1 : foChain cca hyb ideal 1 = hyb := by simp [foChain]
  have c2 : foChain cca hyb ideal 2 = ideal := by simp [foChain]
  have c3 : foChain cca hyb ideal 3 = 1 / 2 := by simp [foChain]
  have s0 : foSteps simFail corrSpread cpaTerm 0 = simFail := by simp [foSteps]
  have s1 : foSteps simFail corrSpread cpaTerm 1 = corrSpread := by simp [foSteps]
  have s2 : foSteps simFail corrSpread cpaTerm 2 = cpaTerm := by simp [foSteps]
  -- each hop is bounded by its step term
  have hsteps : ∀ k, k < 3 →
      |foChain cca hyb ideal k - foChain cca hyb ideal (k + 1)|
        ≤ foSteps simFail corrSpread cpaTerm k := by
    intro k hk
    -- the chain / step evaluations hold by definitional `if`-reduction (`0+1 ≡ 1`, etc.)
    interval_cases k
    · exact hSim
    · exact hT
    · exact hCpa
  -- telescope the chain from G₀ to G₃, then read off the sum
  have ht := abs_telescope_bound (foChain cca hyb ideal) (foSteps simFail corrSpread cpaTerm) 3 hsteps
  rw [c0, c3] at ht
  have hsum : ∑ k ∈ Finset.range 3, foSteps simFail corrSpread cpaTerm k
      = simFail + corrSpread + cpaTerm := by
    simp [Finset.sum_range_succ, s0, s1, s2]
  rw [hsum] at ht
  unfold Adv
  linarith [ht]

/-- **The `f(Adv^IND-CPA(B))` form.** The IND-CPA hop is bounded by `f` of the reduction `B`'s IND-CPA
advantage (`f` a scheme-supplied bound; the classical modular FO takes `f` linear). Feeding
`|ideal − 1/2| ≤ f cpaAdv` into `fo_ind_cca_bound` yields exactly the requested shape
`Adv^IND-CCA(A) ≤ f(Adv^IND-CPA(B)) + simFail + corrSpread`. -/
theorem fo_ind_cca_bound_of_cpa (cca hyb ideal simFail corrSpread cpaAdv : ℚ) (f : ℚ → ℚ)
    (hSim : |cca - hyb| ≤ simFail)
    (hT : |hyb - ideal| ≤ corrSpread)
    (hCpa : |ideal - 1 / 2| ≤ f cpaAdv) :
    Adv cca ≤ f cpaAdv + simFail + corrSpread :=
  fo_ind_cca_bound cca hyb ideal simFail (f cpaAdv) corrSpread hSim hT hCpa

/-- **The T-transform hop, union-bounded.** The correctness / γ-spreadness term is the `q_G` random-oracle
queries, each bad with probability at most `δ + spreadPer` (a correctness-error coin `δ` OR a non-spread
collision `spreadPer = 2^(−γ)`), accumulated by the union bound to `q_G • (δ + spreadPer)`. This is the
`corrSpread` term of `fo_ind_cca_bound`, grounded as a concrete accumulation, not a bare ℚ. -/
theorem t_transform_hop_bound {ι : Type*} (queries : Finset ι) (badProb : ι → ℚ) (δ spreadPer : ℚ)
    (h : ∀ i ∈ queries, badProb i ≤ δ + spreadPer) :
    ∑ i ∈ queries, badProb i ≤ queries.card • (δ + spreadPer) :=
  union_bound queries badProb (δ + spreadPer) h

/-- **γ-spreadness as a probability.** `spreadPer γ = 2^(−γ)` — the per-query bound that a fresh ciphertext
collides / is producible without querying `G`. Named honestly; `2^(−γ) → 0` as the scheme's spreadness `γ`
grows. -/
def spreadPer (γ : ℕ) : ℚ := 1 / 2 ^ γ

end FoBound

/-! ## PART 2 — grounding the three terms (no named-carrier laundering).

Each term routes to an ALREADY-established object: `cpaTerm` to `MLWESearchHard` (via the re-exported
IND-CPA→MLWE reduction), `simFail` to `decaps_oracle_simulable` (honest queries never diverge), and
`corrSpread` to the honestly-named `δ`/`2^(−γ)` PKE parameters (PART 1, `t_transform_hop_bound`). No fresh
hardness carrier appears. -/

section CpaGrounding

variable {Rq : Type*} [CommRing Rq]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **The IND-CPA hop is grounded in decisional-MLWE.** Re-exports `MlKemIndCca.ind_cpa_reduces_to_mlwe`:
the reduction `B` whose IND-CPA advantage is the `cpaTerm` of `fo_ind_cca_bound` is, structurally, a
decisional-MLWE distinguisher on the Kyber masking sample (`z ↦ D (z + m0)` separates the MLWE mask `y`
from its shift). So `cpaTerm` bottoms out at `Lattice.MLWESearchHard` (via the standard Regev
search-decision reduction, as in `MlKemIndCca`) — NOT a re-asserted "ML-KEM is IND-CPA" carrier. -/
theorem cpa_hop_grounded_in_mlwe (D : N → Prop) (y m0 m1 : N)
    (h : IndCpaDistinguishes D y m0 m1) :
    MlweShiftDistinguishes (fun z => D (z + m0)) y (m1 - m0) :=
  ind_cpa_reduces_to_mlwe D y m0 m1 h

end CpaGrounding

section SimGrounding

variable {PK SK Msg CT Coins SS : Type*}

/-- **The decapsulation-simulation discrepancy** on ciphertext `c` at candidate message `m`: the real
(secret-key) `foDecaps` disagrees with the secret-free simulator `foDecapsSim`. This is the "bad" event of
the G₀→G₁ hop; its probability is the `simFail` term. -/
def SimDiverges [DecidableEq CT] (P : PKE PK SK Msg CT Coins) (G : Msg → Coins) (H : Msg → SS)
    (reject : SS) (sk : SK) (pk : PK) (m : Msg) (c : CT) : Prop :=
  foDecaps P G H reject sk c ≠ foDecapsSim P G H reject pk m c

/-- **The decaps simulator NEVER diverges on an honest ciphertext** — the structural ground of `simFail`.
On `c = Enc(pk, m; G(m))` the real oracle and the secret-free simulator agree
(`MlKemIndCca.decaps_oracle_simulable`), so the G₀→G₁ "bad" event cannot fire for honest queries: `simFail`
is carried ENTIRELY by malformed / mis-extracted ciphertexts (bounded by the spreadness union bound), not
by the honest game. This is why the simulation failure is a small additive term, not the whole advantage. -/
theorem sim_no_divergence_on_honest [DecidableEq CT] (P : PKE PK SK Msg CT Coins) (hc : P.Correct)
    (G : Msg → Coins) (H : Msg → SS) (reject : SS) (sk : SK) (m : Msg) :
    ¬ SimDiverges P G H reject sk (P.pkOf sk) m (P.enc (P.pkOf sk) m (G m)) :=
  fun hdiv => hdiv (decaps_oracle_simulable P hc G H reject sk m)

end SimGrounding

#assert_axioms Adv
#assert_axioms abs_telescope
#assert_axioms abs_telescope_bound
#assert_axioms union_bound
#assert_axioms fo_ind_cca_bound
#assert_axioms fo_ind_cca_bound_of_cpa
#assert_axioms t_transform_hop_bound
#assert_axioms cpa_hop_grounded_in_mlwe
#assert_axioms sim_no_divergence_on_honest

/-! ## Teeth — the bound FIRES on concrete data; every term is load-bearing (non-vacuity).

(a) The game-hopping telescope is TIGHT on a monotone chain (the composition is exact, not slack).
(b) `fo_ind_cca_bound` is TIGHT on concrete advantages — `Adv = cpaTerm + simFail + corrSpread` exactly —
    so NO term is droppable (dropping `corrSpread` breaks the bound: `corrSpread_load_bearing`).
(c) The union bound fires: `q_G = 4` queries at `δ + 2^(−10)` accumulate to `4·(δ + 2^(−10))`.
(d) On the concrete `MlKemIndCca.exPKE`, the honest query provably does NOT diverge while a
    MIS-EXTRACTED candidate DOES — the simulation-failure event is real and its honest-freeness is a
    theorem (`decaps_oracle_simulable` is load-bearing). -/

section Teeth

/-! ### (a) the telescope is tight on a monotone chain. -/

/-- A concrete monotone win-probability chain `1, 3/4, 5/8, 1/2` (three game hops). -/
def gTest : ℕ → ℚ := fun k => if k = 0 then 1 else if k = 1 then 3 / 4 else if k = 2 then 5 / 8 else 1 / 2

/-- **The telescope FIRES.** The end-to-end swing `|g 0 − g 3|` is bounded by the summed per-hop swings. -/
theorem ex_abs_telescope_fires :
    |gTest 0 - gTest 3| ≤ ∑ k ∈ Finset.range 3, |gTest k - gTest (k + 1)| :=
  abs_telescope gTest 3

/-- **…and is TIGHT** on the monotone chain: `|g 0 − g 3| = ∑ per-hop swings = 1/2`. The triangle
inequality is saturated (all hops descend), so the game-hopping composition is exact, not slack — the
engine moves a real object. -/
theorem ex_abs_telescope_tight :
    |gTest 0 - gTest 3| = ∑ k ∈ Finset.range 3, |gTest k - gTest (k + 1)| := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [gTest]
  norm_num

-- The chain descends 1 → 3/4 → 5/8 → 1/2; the total drop is 1/2, split as 1/4 + 1/8 + 1/8.
#guard decide (gTest 0 - gTest 3 = 1 / 2)
#guard decide (|gTest 0 - gTest 1| + |gTest 1 - gTest 2| + |gTest 2 - gTest 3| = (1 : ℚ) / 2)

/-! ### (b) the FO bound is tight; every term is load-bearing. -/

/-- **`fo_ind_cca_bound` FIRES, and is TIGHT.** With `cpaTerm = 1/10`, `simFail = corrSpread = 1/20` and
the monotone chain `cca = 7/10, hyb = 13/20, ideal = 3/5`, the bound gives
`Adv^IND-CCA ≤ 1/10 + 1/20 + 1/20 = 1/5`, and `Adv(7/10) = |7/10 − 1/2| = 1/5` EXACTLY — the three FO
terms saturate the bound, so the reduction is non-vacuous and no term is slack. -/
theorem ex_fo_bound_fires : Adv (7 / 10 : ℚ) ≤ 1 / 10 + 1 / 20 + 1 / 20 :=
  fo_ind_cca_bound (7 / 10) (13 / 20) (3 / 5) (1 / 20) (1 / 10) (1 / 20)
    (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num)

/-- The bound is SATURATED: `Adv(7/10) = 1/5 = cpaTerm + simFail + corrSpread`. -/
theorem ex_fo_bound_tight : Adv (7 / 10 : ℚ) = 1 / 10 + 1 / 20 + 1 / 20 := by
  unfold Adv; rw [show (7 / 10 - 1 / 2 : ℚ) = 1 / 5 by norm_num, abs_of_pos (by norm_num)]; norm_num

/-- **THE LOAD-BEARING TOOTH.** Drop the `corrSpread` term and the bound FAILS: `Adv(7/10) = 1/5` exceeds
`cpaTerm + simFail = 1/10 + 1/20 = 3/20`. So the correctness / γ-spreadness term is not vacuous — the FO
bound genuinely needs it (and symmetrically each other term). -/
theorem ex_fo_corrSpread_load_bearing : ¬ (Adv (7 / 10 : ℚ) ≤ 1 / 10 + 1 / 20) := by
  rw [ex_fo_bound_tight]; norm_num

/-- Symmetrically the IND-CPA term is load-bearing: dropping `cpaTerm` breaks the bound
(`1/5 > simFail + corrSpread = 1/10`). -/
theorem ex_fo_cpaTerm_load_bearing : ¬ (Adv (7 / 10 : ℚ) ≤ 1 / 20 + 1 / 20) := by
  rw [ex_fo_bound_tight]; norm_num

/-! ### (c) the union bound fires (correctness / spreadness accumulation). -/

/-- **The T-transform union bound FIRES.** Four `G`-queries each bad with probability at most
`δ + 2^(−10) = 1/100 + 1/1024` accumulate to `4 • (1/100 + 1/1024)` — the `corrSpread` term as a concrete
`q_G·(δ + 2^(−γ))`. -/
theorem ex_t_transform_hop :
    ∑ _i ∈ ({0, 1, 2, 3} : Finset ℕ), (1 / 100 + spreadPer 10 : ℚ)
      ≤ ({0, 1, 2, 3} : Finset ℕ).card • (1 / 100 + spreadPer 10 : ℚ) :=
  t_transform_hop_bound ({0, 1, 2, 3} : Finset ℕ) (fun _ => 1 / 100 + spreadPer 10) (1 / 100)
    (spreadPer 10) (fun _ _ => le_refl _)

-- γ-spreadness shrinks with γ: 2^(−10) = 1/1024, and the four-query bound is a real positive number.
#guard decide (spreadPer 10 = (1 : ℚ) / 1024)
#guard decide ((0 : ℚ) < ({0, 1, 2, 3} : Finset ℕ).card • (1 / 100 + spreadPer 10 : ℚ))

/-! ### (d) the decaps-simulation failure is real and honest-free (grounded in `decaps_oracle_simulable`).

Reuse the concrete `MlKemIndCca.exPKE` (`enc m = 2m`, `dec c = c/2`), `exG`, `exH` (`H m = 2m + 1`),
reject `0`. On the honest ciphertext `enc 2 = 4` the real decaps and the simulator AGREE (both `H 2 = 5`);
with a MIS-EXTRACTED candidate `m = 3` the simulator DIVERGES (`0 ≠ 5`) — the failure event is genuine, and
`sim_no_divergence_on_honest` proves the honest query is free of it. -/

/-- **The honest query does NOT diverge** — instantiating `sim_no_divergence_on_honest` on `exPKE`,
candidate `m = 2`, honest ciphertext `enc 2 = 4`: real decaps = simulator = `H 2`. The G₀→G₁ "bad" event
is provably impossible on the honest game. -/
theorem ex_sim_no_divergence_honest :
    ¬ SimDiverges exPKE exG exH 0 () (exPKE.pkOf ()) 2 (exPKE.enc (exPKE.pkOf ()) 2 (exG 2)) :=
  sim_no_divergence_on_honest exPKE exPKE_correct exG exH 0 () 2

-- Honest candidate (m = 2) on c = 4: real decaps = simulator = H 2 = 5 (no divergence)…
#guard decide (foDecaps exPKE exG exH 0 () 4 = foDecapsSim exPKE exG exH 0 (exPKE.pkOf ()) 2 4)
-- …but a MIS-EXTRACTED candidate (m = 3) on the SAME c = 4 DIVERGES: real = 5, simulator = 0.
-- (this is exactly `SimDiverges exPKE exG exH 0 () (exPKE.pkOf ()) 3 4` with the `def` unfolded.)
#guard decide (foDecaps exPKE exG exH 0 () 4 ≠ foDecapsSim exPKE exG exH 0 (exPKE.pkOf ()) 3 4)
#guard decide (foDecaps exPKE exG exH 0 () 4 = 5)
#guard decide (foDecapsSim exPKE exG exH 0 (exPKE.pkOf ()) 3 4 = 0)

end Teeth

#assert_axioms ex_abs_telescope_fires
#assert_axioms ex_abs_telescope_tight
#assert_axioms ex_fo_bound_fires
#assert_axioms ex_fo_bound_tight
#assert_axioms ex_fo_corrSpread_load_bearing
#assert_axioms ex_fo_cpaTerm_load_bearing
#assert_axioms ex_t_transform_hop
#assert_axioms ex_sim_no_divergence_honest

end Dregg2.Crypto.FoBookkeeping
