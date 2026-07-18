/-
# Bfv.Noise — silent-failure class (A): the noise budget, as a proved rounding theorem.

**The failure this module kills:** BFV decryption is a ROUNDING. A ciphertext's phase is
`Δ·m + e`; decrypt recovers `m` by rounding `t·phase/q` to the nearest integer. While `|e|` is
inside the rounding radius, decryption is EXACT; the instant it crosses, decryption returns a
different message — silently. There is no error, no exception: an over-noised ciphertext decrypts
*cleanly* to a wrong number. The observable that turns this cliff into a METER is a noise-margin
bound proved here and emitted for the Rust side to enforce (refuse to decrypt when the accumulated
bound crosses the margin).

## The model (stated honestly, so the correspondence gap is NAMED, not hidden)

A ciphertext is modeled by its exact integer **phase** `p : ℤ` (one polynomial coefficient's
worth). This is the scalar-coefficient model:

  * Real BFV phases are polynomial: `n = 4096` coefficients, each carrying this scalar structure;
    homomorphic addition is coefficient-wise, so every statement here lifts pointwise. The lift is
    NOT formalized (no polynomial ring here) — that correspondence is a NAMED model gap.
  * Real phases live mod `q`. This model works in ℤ. Two mitigations, both in-file:
    `decryptPhase_add_q` proves a `+q` phase shift moves the readout by exactly `+t` — i.e. the
    mod-`q` wrap corresponds to a mod-`t` readout shift (the classical fact), so within the fold's
    envelope (`Bfv.Fold.fold_phase_lt_q`: the honest fold's phase never leaves `[0, q)`) the ℤ
    model and the mod-`q` machine agree on the nose.
  * The FRESH-ciphertext noise bound (`|e| ≤ B_fresh` for a public-key encryption, `B_fresh ≈ 2^20`
    for the deployed set) is an ASSUMPTION fed to these theorems, not derived: deriving it needs
    the ring-product expansion (`|u·e|_∞ ≤ n·|u|_∞·|e|_∞`), which is Phase-2 work. The theorems
    are conditional on it, and say so.

## What is proved

  1. **`decrypt_exact` (THE KEYSTONE)** — if `m < t` and `2t·|e| + 2(t−1)·r < q`, then
     `decryptPhase (Δ·m + e) = m`: decryption is EXACT, not approximate, inside the margin. The
     bound is the true integer-arithmetic condition (including the `(t−1)·r` cross-term that the
     folklore `|e| < Δ/2` slogan drops — with the deployed numbers that term is ~2^40, six orders
     of magnitude above the fresh noise, so dropping it is not pedantry).
  2. **`decrypt_misses` (the cliff is REAL — a witness, not a scare)** — with the deployed
     parameters, the phase `q/(2t)+1` (an over-budget noise on `m = 0`) decrypts to `1`, not `0`.
     A theorem that could not fail would prove nothing; this is the failing side, proved.
  3. **`noiseAt_add`** — homomorphic addition adds phases, so noise (relative to the summed
     message) adds EXACTLY: `noise(c₁+c₂ | m₁+m₂) = noise(c₁|m₁) + noise(c₂|m₂)`.
  4. **`abs_noise_add_le`** — hence the worst-case ℓ∞ bound is MONOTONE and additive:
     `|noise| ≤ |noise₁| + |noise₂|`. K-fold version in `Bfv.Fold` (K adds of `≤ B` fresh noise
     ⇒ `≤ K·B`). **Honesty note:** the memo's "add roughly doubles noise *variance*" is the
     average-case heuristic; what is PROVED is the sound worst-case linear bound. The variance
     model is NOT formalized and nothing here depends on it.
  5. **`decryptPhase_add_q`** — the mod-`q`/mod-`t` correspondence named above.

Pure. No axioms beyond the kernel triple.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Bfv.Params

namespace Bfv

/-! ## 1. The phase model. -/

/-- A model BFV ciphertext: its exact integer phase (one coefficient; see the module doc for the
scalar-model correspondence gap, which is NAMED, not hidden). -/
structure Ct (P : Params) where
  /-- The exact integer phase (`Δ·m + e` for an honest encryption of `m` with noise `e`). -/
  phase : ℤ

variable {P : Params}

/-- Model encryption of message `m` with noise `e`: phase `Δ·m + e`. (The fhe.rs
`Ciphertext::zero` is `encrypt 0 0` — exactly the zero phase.) -/
def encrypt (P : Params) (m : ℕ) (e : ℤ) : Ct P := ⟨(P.Δ : ℤ) * m + e⟩

/-- Homomorphic addition: phases add. This IS the entire fold-path API surface. -/
def Ct.add (c₁ c₂ : Ct P) : Ct P := ⟨c₁.phase + c₂.phase⟩

/-- The noise of a ciphertext *relative to an intended message* `m`: `phase − Δ·m`. -/
def Ct.noiseAt (c : Ct P) (m : ℕ) : ℤ := c.phase - (P.Δ : ℤ) * m

/-- BFV decryption of a phase: round `t·p/q` to the nearest integer, computed exactly in integer
arithmetic as `⌊(2t·p + q) / (2q)⌋` (round-half-up; for in-margin phases the tie never occurs). -/
def decryptPhase (P : Params) (p : ℤ) : ℤ :=
  (2 * (P.t : ℤ) * p + P.q) / (2 * (P.q : ℤ))

/-- Decrypt a ciphertext. Real BFV additionally reduces mod `t`; inside the proved envelope the
result is already in `[0, t)` so the reduction is the identity (`Bfv.Fold` composes with
`Bfv.NoWrap.fold_sum_no_wrap` to keep it there). -/
def Ct.decrypt (c : Ct P) : ℤ := decryptPhase P c.phase

/-- The margin condition of the keystone, as a named predicate: noise magnitude `≤ B` is SAFE for
parameter set `P` when `2t·B + 2(t−1)·r < q`. -/
def SafeNoise (P : Params) (B : ℤ) : Prop :=
  2 * (P.t : ℤ) * B + 2 * ((P.t : ℤ) - 1) * (P.r : ℤ) < (P.q : ℤ)

/-! ## 2. The keystone: exact decryption inside the margin. -/

/-- **THE KEYSTONE (class A):** for any message `m < t` and any noise `e` with
`2t·|e| + 2(t−1)·r < q`, decryption of the phase `Δ·m + e` returns EXACTLY `m`. This is the
theorem a Lean-emitted noise margin makes operational: while the accumulated noise bound satisfies
`SafeNoise`, a decrypt cannot be silently wrong. -/
theorem decrypt_exact (P : Params) (m : ℕ) (e : ℤ)
    (hm : m < P.t) (hbound : SafeNoise P |e|) :
    decryptPhase P ((P.Δ : ℤ) * m + e) = m := by
  unfold SafeNoise at hbound
  set T : ℤ := (P.t : ℤ) with hT_def
  set Q : ℤ := (P.q : ℤ) with hQ_def
  set D : ℤ := (P.Δ : ℤ) with hD_def
  set R : ℤ := (P.r : ℤ) with hR_def
  set M : ℤ := (m : ℤ) with hM_def
  -- the ground facts, cast to ℤ
  have hQeq : Q = D * T + R := by
    rw [hQ_def, hD_def, hT_def, hR_def]; exact_mod_cast P.q_eq
  have hT0 : (0 : ℤ) < T := by rw [hT_def]; exact_mod_cast P.t_pos
  have hQ0 : (0 : ℤ) < Q := by rw [hQ_def]; exact_mod_cast P.q_pos
  have hR0 : (0 : ℤ) ≤ R := by rw [hR_def]; exact_mod_cast Nat.zero_le _
  have hM0 : (0 : ℤ) ≤ M := by rw [hM_def]; exact_mod_cast Nat.zero_le _
  have hMT : M < T := by rw [hM_def, hT_def]; exact_mod_cast hm
  -- the product facts (each nonlinear step named, so `linarith` runs on atoms)
  have hmr_le : M * R ≤ (T - 1) * R :=
    mul_le_mul_of_nonneg_right (by omega) hR0
  have hmr0 : (0 : ℤ) ≤ M * R := mul_nonneg hM0 hR0
  have htr0 : (0 : ℤ) ≤ (T - 1) * R := mul_nonneg (by omega) hR0
  have hte_le : T * e ≤ T * |e| := mul_le_mul_of_nonneg_left (le_abs_self e) hT0.le
  have hte_ge : -(T * |e|) ≤ T * e := by
    have h := mul_le_mul_of_nonneg_left (neg_abs_le e) hT0.le
    linarith [h]
  -- lower bound: M·(2Q) ≤ 2T(DM+e) + Q
  have expand_lo : 2 * T * (D * M + e) + Q - M * (2 * Q) = 2 * (T * e) + Q - 2 * (M * R) := by
    rw [hQeq]; ring
  have hlow : M * (2 * Q) ≤ 2 * T * (D * M + e) + Q := by linarith
  -- upper bound: 2T(DM+e) + Q < (M+1)·(2Q)
  have expand_hi : (M + 1) * (2 * Q) - (2 * T * (D * M + e) + Q) = Q + 2 * (M * R) - 2 * (T * e) := by
    rw [hQeq]; ring
  have hup : 2 * T * (D * M + e) + Q < (M + 1) * (2 * Q) := by linarith
  -- floor characterization
  have h2Q : (0 : ℤ) < 2 * Q := by linarith
  have h1 : M ≤ (2 * T * (D * M + e) + Q) / (2 * Q) :=
    (Int.le_ediv_iff_mul_le h2Q).mpr hlow
  have h2 : (2 * T * (D * M + e) + Q) / (2 * Q) < M + 1 :=
    (Int.ediv_lt_iff_lt_mul h2Q).mpr hup
  show (2 * T * (D * M + e) + Q) / (2 * Q) = M
  exact le_antisymm (Int.lt_add_one_iff.mp h2) h1

/-! ## 3. The cliff is real: the failing side, proved on the deployed numbers. -/

/-- **Over-budget noise decrypts CLEANLY to the WRONG message.** On the deployed parameters, the
phase `q/(2t) + 1` — i.e. `m = 0` carrying noise just past the rounding radius — decrypts to `1`.
No error is possible at any layer: the wrong answer is a perfectly well-formed plaintext. (This is
the witness that `decrypt_exact`'s hypothesis is load-bearing, and the reason production decrypt
must REFUSE when the emitted margin is exhausted rather than "just decrypt".) -/
theorem decrypt_misses :
    decryptPhase fheRs4096 ((q4096 : ℤ) / (2 * (t4096 : ℤ)) + 1) = 1 := by
  decide

/-! ## 4. Noise algebra under homomorphic addition. -/

/-- Encryption has exactly its stated noise: `noiseAt (encrypt m e) m = e`. -/
@[simp] theorem encrypt_noiseAt (P : Params) (m : ℕ) (e : ℤ) :
    (encrypt P m e).noiseAt m = e := by
  simp [encrypt, Ct.noiseAt]

/-- **Noise adds EXACTLY under homomorphic addition** (relative to the summed message):
`noise(c₁ + c₂ | m₁ + m₂) = noise(c₁ | m₁) + noise(c₂ | m₂)`. -/
theorem noiseAt_add (c₁ c₂ : Ct P) (m₁ m₂ : ℕ) :
    (c₁.add c₂).noiseAt (m₁ + m₂) = c₁.noiseAt m₁ + c₂.noiseAt m₂ := by
  simp [Ct.add, Ct.noiseAt]
  ring

/-- The sound worst-case ℓ∞ growth: noise magnitude is subadditive across a homomorphic add. (The
"variance doubles" story is the average-case heuristic — NOT what is proved; this linear bound is
the one that is actually sound, and the one `Bfv.Fold` iterates to `K·B`.) -/
theorem abs_noise_add_le (c₁ c₂ : Ct P) (m₁ m₂ : ℕ) :
    |(c₁.add c₂).noiseAt (m₁ + m₂)| ≤ |c₁.noiseAt m₁| + |c₂.noiseAt m₂| := by
  rw [noiseAt_add]
  exact abs_add_le _ _

/-! ## 5. The mod-q correspondence, named and half-discharged. -/

/-- **A `+q` phase wrap shifts the readout by exactly `+t`** — so a mod-`q` phase reduction moves
the decrypt by a multiple of `t`, which the final mod-`t` readout erases. This is the classical
fact that lets the ℤ-phase model stand in for the mod-`q` machine; combined with
`Bfv.Fold.fold_phase_lt_q` (the honest fold's phase never reaches `q`), the two agree exactly on
the fold path. -/
theorem decryptPhase_add_q (P : Params) (p : ℤ) :
    decryptPhase P (p + P.q) = decryptPhase P p + P.t := by
  unfold decryptPhase
  have h2q : (2 : ℤ) * (P.q : ℤ) ≠ 0 := by
    have := P.q_pos
    omega
  have : 2 * (P.t : ℤ) * (p + P.q) + P.q = (2 * (P.t : ℤ) * p + P.q) + (P.t : ℤ) * (2 * P.q) := by
    ring
  rw [this, Int.add_mul_ediv_right _ _ h2q]

#assert_all_clean [Bfv.decrypt_exact, Bfv.decrypt_misses, Bfv.encrypt_noiseAt,
  Bfv.noiseAt_add, Bfv.abs_noise_add_le, Bfv.decryptPhase_add_q]

/-! ## 6. T-composition (contract 2b): the iterated public-linear step, its compounding noise,
and the PROVEN T ceiling.

**The engine shape this covers** (`fhegg-fhe/src/convex_step.rs` → `convex_engine.rs`): one
first-order iteration `x ← x − τ·A·x` is homomorphically `w_i = tauDen·x_i − tauNum·Σ_j A_ij·x_j`
— public-scalar-muls plus adds, i.e. one ℤ-linear map on phases with step matrix
`S = tauDen·I − tauNum·A`. A public-scalar-mul by `c` multiplies phase (hence noise) by exactly
`c`; a row of adds compounds them. So T fully-homomorphic iterations multiply the worst-case
noise bound by `G^T`, where `G` bounds every row's absolute sum of `S`
(`G = tauDen + tauNum·‖A‖∞`, exported as `iterGrowth`). This section proves:

  * **`iter_noise_le`** — the ACTUAL iterated linear map (phase model, `matVecCt`) has
    per-component noise `≤ G^T·B` from fresh noise `≤ B`. Not a slogan: the phase algebra.
  * **`noise_after_T` (SAFE SIDE)** — for `T ≤ iterCeiling P G B`, the accumulated bound
    `G^T·B` satisfies `SafeNoise` — decryption after T iterations is provably exact
    (`iter_decrypts_exact` composes this with `decrypt_exact`).
  * **`T_gt_ceiling_fails` (FAILING SIDE, required)** — for `T > iterCeiling P G B`, the
    accumulated bound PROVABLY EXCEEDS the margin: `¬ SafeNoise`. The ceiling is EXACT
    (`safeNoise_iff_le_ceiling`), not conservative slack. Deployed pins: at `G = 3 =
    iterGrowth 1 1 2` (τ = 1, `‖A‖∞ ≤ 2`), `B = 2^20`, the ceiling is **42**; the T = 43 check
    is kernel-`decide`d FALSE, and the T = 43 noise budget already ADMITS the
    `decrypt_misses` cliff phase (a wrong message decrypting cleanly).

**THE EXPORTED CEILING FORMULA** (what `convex_engine.rs::max_iterations_for_params` computes):

    G        = tau_den + tau_num · maxᵢ Σⱼ |A_ij|          (`iterGrowth`)
    headroom = (q − 2·(t−1)·r − 1) / (2·t·B)               (`depthHeadroom`, integer division)
    T_max    = floor(log_G headroom) = Nat.log G headroom  (`iterCeiling`)

equivalently: the largest `T` with `iterMarginHolds P G B T = true` (`iterMargin_iff` proves the
check and the log formula agree exactly). `B` is the fresh-noise bound (the `B_fresh ≈ 2^20`
assumption, same status as everywhere in this file).

**Honesty notes (the model, stated so the gaps are NAMED):**

  * This bounds the **fully-homomorphic composition** (`tau_den = 1` integer-step path): T linear
    steps between one encrypt and one decrypt, prox applied at the decrypt boundary. The
    boundary-assisted path (decrypt–prox–re-encrypt each iteration) RESETS noise to fresh `B`
    per segment; each segment then re-obeys this same ceiling with T = segment depth — strictly
    inside this bound. Either way the ceiling governs homomorphic depth between boundaries.
  * **Where the prox bound enters:** the prox clamp bounds the MESSAGE, not the noise — it
    guarantees the decoded value stays inside the plaintext window (class C), which is the
    `mi < P.t` hypothesis of `iter_decrypts_exact`. The noise margin (class A) is `G`/`B`/`T`'s
    job; the two gates are separate and both appear in the end-to-end statement.
  * **Mod-q correspondence for the iterated path:** the step is ℤ-linear in phases with public
    integer coefficients, and mod-q reduction commutes with such maps; a hypothetical `±q` wrap
    shifts the readout by a multiple of `t` (`decryptPhase_add_q`), erased by the final mod-t
    readout. Same NAMED model gap as the fold path, no worse.
  * Intermediate messages are SIGNED (`ℤ`, the centered encoding); the final readout hypothesis
    takes the intended message as `mi : ℕ` — the centered encode/decode bijection
    (`encode_signed`/`center`, Rust side) is a named correspondence gap, as in `Bfv.Mul`. -/

/-- Noise relative to a SIGNED intended message — the iterated step's intermediate messages are
signed (centered encoding). Agrees with `Ct.noiseAt` on ℕ messages definitionally. -/
def Ct.noiseAtInt (c : Ct P) (m : ℤ) : ℤ := c.phase - (P.Δ : ℤ) * m

@[simp] theorem noiseAtInt_natCast (c : Ct P) (m : ℕ) :
    c.noiseAtInt (m : ℤ) = c.noiseAt m := rfl

/-- Triangle for a difference: `|a − b| ≤ |a| + |b|` (local helper). -/
theorem abs_sub_le_abs_add_abs (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-- One homomorphic public-linear step on a ciphertext vector: component `i` of `S·x`, computed
exactly as the Rust loop does — public-scalar-muls (`S i j` times a phase) plus adds. -/
def matVecCt {n : ℕ} (S : Fin n → Fin n → ℤ) (x : Fin n → Ct P) : Fin n → Ct P :=
  fun i => ⟨∑ j, S i j * (x j).phase⟩

/-- The same linear step on the intended (clear) messages. -/
def matVecMsg {n : ℕ} (S : Fin n → Fin n → ℤ) (m : Fin n → ℤ) : Fin n → ℤ :=
  fun i => ∑ j, S i j * m j

/-- `G` bounds every row's absolute sum — the operator ℓ∞ bound the ceiling is stated over. -/
def RowBound {n : ℕ} (S : Fin n → Fin n → ℤ) (G : ℤ) : Prop :=
  ∀ i, (∑ j, |S i j|) ≤ G

/-- The step's noise is the SAME linear map applied to the input noises — exact phase algebra,
the T-composition analog of `noiseAt_add`. -/
theorem matVec_noiseAtInt {n : ℕ} (S : Fin n → Fin n → ℤ) (x : Fin n → Ct P)
    (m : Fin n → ℤ) (i : Fin n) :
    (matVecCt S x i).noiseAtInt (matVecMsg S m i)
      = ∑ j, S i j * (x j).noiseAtInt (m j) := by
  simp only [Ct.noiseAtInt, matVecCt, matVecMsg, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **One step multiplies the noise bound by ≤ G**: from noises `≤ N` to noises `≤ G·N`. -/
theorem step_noise_le {n : ℕ} {S : Fin n → Fin n → ℤ} {G : ℤ} (hS : RowBound S G)
    {x : Fin n → Ct P} {m : Fin n → ℤ} (N : ℤ) (hN : 0 ≤ N)
    (h : ∀ j, |(x j).noiseAtInt (m j)| ≤ N) (i : Fin n) :
    |(matVecCt S x i).noiseAtInt (matVecMsg S m i)| ≤ G * N := by
  rw [matVec_noiseAtInt]
  calc |∑ j, S i j * (x j).noiseAtInt (m j)|
      ≤ ∑ j, |S i j * (x j).noiseAtInt (m j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |S i j| * |(x j).noiseAtInt (m j)| := by simp only [abs_mul]
    _ ≤ ∑ j, |S i j| * N :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)
    _ = (∑ j, |S i j|) * N := (Finset.sum_mul _ _ _).symm
    _ ≤ G * N := mul_le_mul_of_nonneg_right (hS i) hN

/-- T iterations of the homomorphic linear step (the `convex_solve` loop body, phase model). -/
def iterCt {n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (x : Fin n → Ct P) : Fin n → Ct P :=
  (matVecCt S)^[T] x

/-- T iterations on the clear messages. -/
def iterMsg {n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (m : Fin n → ℤ) : Fin n → ℤ :=
  (matVecMsg S)^[T] m

theorem iterCt_succ {n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (x : Fin n → Ct P) :
    iterCt S (T + 1) x = matVecCt S (iterCt S T x) :=
  Function.iterate_succ_apply' _ _ _

theorem iterMsg_succ {n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (m : Fin n → ℤ) :
    iterMsg S (T + 1) m = matVecMsg S (iterMsg S T m) :=
  Function.iterate_succ_apply' _ _ _

/-- **The compounding law, proved on the model:** T iterations from fresh noise `≤ B` leave every
component's noise `≤ G^T·B`. This is the theorem `noise_after_T`'s bound is ABOUT — the actual
iterated phase map, not a free-floating formula. -/
theorem iter_noise_le {n : ℕ} {S : Fin n → Fin n → ℤ} {G N : ℤ} (hS : RowBound S G)
    (hG : 0 ≤ G) (hN : 0 ≤ N) {x : Fin n → Ct P} {m : Fin n → ℤ}
    (h : ∀ j, |(x j).noiseAtInt (m j)| ≤ N) (T : ℕ) :
    ∀ i, |(iterCt S T x i).noiseAtInt (iterMsg S T m i)| ≤ G ^ T * N := by
  induction T with
  | zero => simpa [iterCt, iterMsg] using h
  | succ T ih =>
    intro i
    rw [iterCt_succ, iterMsg_succ]
    have hstep := step_noise_le hS (G ^ T * N) (mul_nonneg (pow_nonneg hG T) hN) ih i
    calc |(matVecCt S (iterCt S T x) i).noiseAtInt (matVecMsg S (iterMsg S T m) i)|
        ≤ G * (G ^ T * N) := hstep
      _ = G ^ (T + 1) * N := by ring

/-! ### The growth factor, derived from τ and ‖A‖∞ (the exported `G`). -/

/-- **The exported growth factor** `G = tauDen + tauNum·normA`: the per-iteration noise
multiplier of the scaled step `w = tauDen·x − tauNum·A·x`. -/
def iterGrowth (tauDen tauNum normA : ℕ) : ℕ := tauDen + tauNum * normA

/-- The scaled step matrix `S = tauDen·I − tauNum·A` — exactly what `convex_linear_step`
applies (`acc = tauDen·x_i`, then `c = −tauNum·A_ij` scalar-muls). -/
def stepMatrix {n : ℕ} (tauDen tauNum : ℕ) (A : Fin n → Fin n → ℤ) :
    Fin n → Fin n → ℤ :=
  fun i j => (if i = j then (tauDen : ℤ) else 0) - (tauNum : ℤ) * A i j

/-- The step matrix's rows are bounded by `iterGrowth`: `‖A‖∞ ≤ normA` gives
`Σ_j |S i j| ≤ tauDen + tauNum·normA`. This derives the ceiling's `G` from τ and the norm of A. -/
theorem stepMatrix_rowBound {n : ℕ} (tauDen tauNum normA : ℕ) (A : Fin n → Fin n → ℤ)
    (hA : ∀ i, (∑ j, |A i j|) ≤ (normA : ℤ)) :
    RowBound (stepMatrix tauDen tauNum A) ((iterGrowth tauDen tauNum normA : ℕ) : ℤ) := by
  intro i
  have hstep : ∀ j, |stepMatrix tauDen tauNum A i j|
      ≤ (if i = j then (tauDen : ℤ) else 0) + (tauNum : ℤ) * |A i j| := by
    intro j
    refine (abs_sub_le_abs_add_abs _ _).trans ?_
    have h1 : |if i = j then (tauDen : ℤ) else 0| = if i = j then (tauDen : ℤ) else 0 := by
      split <;> simp
    have h2 : |(tauNum : ℤ) * A i j| = (tauNum : ℤ) * |A i j| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (tauNum : ℤ))]
    rw [h1, h2]
  calc (∑ j, |stepMatrix tauDen tauNum A i j|)
      ≤ ∑ j, ((if i = j then (tauDen : ℤ) else 0) + (tauNum : ℤ) * |A i j|) :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = (tauDen : ℤ) + (tauNum : ℤ) * ∑ j, |A i j| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        simp
    _ ≤ (tauDen : ℤ) + (tauNum : ℤ) * (normA : ℤ) := by
        have := mul_le_mul_of_nonneg_left (hA i) (by positivity : (0 : ℤ) ≤ (tauNum : ℤ))
        linarith
    _ = ((iterGrowth tauDen tauNum normA : ℕ) : ℤ) := by
        unfold iterGrowth
        push_cast
        ring

/-! ### The ceiling: headroom, log formula, computable check — and their exact agreement. -/

/-- The noise headroom: how many multiples of `B` fit inside the decrypt margin.
`(q − 2(t−1)r − 1) / (2tB)`, integer division. -/
def depthHeadroom (P : Params) (B : ℕ) : ℕ :=
  (P.q - 2 * (P.t - 1) * P.r - 1) / (2 * P.t * B)

/-- **THE PROVEN T CEILING (the export `max_iterations_for_params` computes):**
`T_max = floor(log_G headroom)`. Safe at every `T ≤` this (`noise_after_T`); the margin check
FAILS at every `T >` this (`T_gt_ceiling_fails`). -/
def iterCeiling (P : Params) (G B : ℕ) : ℕ :=
  Nat.log G (depthHeadroom P B)

/-- The computable per-T margin check (the `marginHolds` analog with `K·B` replaced by the
compounded `G^T·B`) — what a Rust gate evaluates before agreeing to iterate depth T. -/
def iterMarginHolds (P : Params) (G B T : ℕ) : Bool :=
  decide (2 * P.t * (G ^ T * B) + 2 * (P.t - 1) * P.r < P.q)

/-- `SafeNoise` at a ℕ bound is exactly the ℕ-side margin inequality (the cast bridge). -/
theorem safeNoise_natCast_iff (P : Params) (N : ℕ) :
    SafeNoise P (N : ℤ) ↔ 2 * P.t * N + 2 * (P.t - 1) * P.r < P.q := by
  have h1 : 1 ≤ P.t := P.t_pos
  unfold SafeNoise
  constructor
  · intro h
    zify [h1]
    linarith
  · intro h
    zify [h1] at h
    linarith

/-- **The check and the log formula agree EXACTLY:** the margin holds at depth T iff
`G^T ≤ depthHeadroom`. This is the equivalence that makes `iterCeiling` the true maximum, and
lets the Rust side compute either form. -/
theorem iterMargin_iff (P : Params) (G B T : ℕ) (hG : 0 < G) (hB : 0 < B) :
    (2 * P.t * (G ^ T * B) + 2 * (P.t - 1) * P.r < P.q)
      ↔ G ^ T ≤ depthHeadroom P B := by
  have hd : 0 < 2 * P.t * B := by
    have := P.t_pos
    positivity
  rw [depthHeadroom, Nat.le_div_iff_mul_le hd]
  have hkey : 2 * P.t * (G ^ T * B) = G ^ T * (2 * P.t * B) := by ring
  rw [hkey]
  have hx : 0 < G ^ T * (2 * P.t * B) := Nat.mul_pos (Nat.pow_pos hG) hd
  omega

/-- Soundness of the computable check: `iterMarginHolds = true` implies the keystone hypothesis
`SafeNoise` at the compounded bound. A gate on this check enforces a theorem's hypothesis. -/
theorem iterMarginHolds_safe (P : Params) (G B T : ℕ)
    (h : iterMarginHolds P G B T = true) :
    SafeNoise P ((G : ℤ) ^ T * (B : ℤ)) := by
  have hnat := of_decide_eq_true h
  have hcast : ((G : ℤ) ^ T * (B : ℤ)) = ((G ^ T * B : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, safeNoise_natCast_iff]
  exact hnat

/-! ### The two contract theorems: safe up to the ceiling, FAILS one past it. -/

/-- **`noise_after_T` (contract 2b, SAFE SIDE):** for any `T ≤ iterCeiling P G B`, the
accumulated worst-case noise bound `G^T·B` after T iterations satisfies the decrypt margin.
Hypothesis `h0` is depth-0 sanity (fresh noise `B` is itself inside the margin — if even that
fails, no ceiling exists). Combined with `iter_noise_le` (the model's noise really is `≤ G^T·B`)
and `decrypt_exact`, this closes the T-composition: see `iter_decrypts_exact`. -/
theorem noise_after_T (P : Params) (G B T : ℕ) (hG : 2 ≤ G) (hB : 0 < B)
    (h0 : 2 * P.t * B + 2 * (P.t - 1) * P.r < P.q)
    (hT : T ≤ iterCeiling P G B) :
    SafeNoise P ((G : ℤ) ^ T * (B : ℤ)) := by
  have hG1 : 0 < G := by omega
  have h00 : 2 * P.t * (G ^ 0 * B) + 2 * (P.t - 1) * P.r < P.q := by simpa using h0
  have hH : 1 ≤ depthHeadroom P B := by
    simpa using (iterMargin_iff P G B 0 hG1 hB).mp h00
  have hlog : G ^ iterCeiling P G B ≤ depthHeadroom P B :=
    Nat.pow_log_le_self G (by omega)
  have hpow : G ^ T ≤ depthHeadroom P B :=
    le_trans (Nat.pow_le_pow_right (by omega) hT) hlog
  have hnat : 2 * P.t * (G ^ T * B) + 2 * (P.t - 1) * P.r < P.q :=
    (iterMargin_iff P G B T hG1 hB).mpr hpow
  have hcast : ((G : ℤ) ^ T * (B : ℤ)) = ((G ^ T * B : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, safeNoise_natCast_iff]
  exact hnat

/-- **`T_gt_ceiling_fails` (contract 2b, FAILING SIDE — required):** ONE PAST THE CEILING (any
`T > iterCeiling P G B`), the accumulated bound `G^T·B` PROVABLY EXCEEDS the decrypt margin:
`SafeNoise` is FALSE. A ceiling theorem without this direction would be vacuously loose (any
under-estimate of `T_max` would satisfy it); with it, the ceiling is exact. -/
theorem T_gt_ceiling_fails (P : Params) (G B T : ℕ) (hG : 2 ≤ G) (hB : 0 < B)
    (hT : iterCeiling P G B < T) :
    ¬ SafeNoise P ((G : ℤ) ^ T * (B : ℤ)) := by
  have hcast : ((G : ℤ) ^ T * (B : ℤ)) = ((G ^ T * B : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, safeNoise_natCast_iff, iterMargin_iff P G B T (by omega) hB]
  intro hle
  have h1 : depthHeadroom P B < G ^ (iterCeiling P G B + 1) :=
    Nat.lt_pow_succ_log_self (by omega) _
  have h2 : G ^ (iterCeiling P G B + 1) ≤ G ^ T :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The two sides as one exact characterization: the compounded bound is safe IFF
`T ≤ iterCeiling`. -/
theorem safeNoise_iff_le_ceiling (P : Params) (G B T : ℕ) (hG : 2 ≤ G) (hB : 0 < B)
    (h0 : 2 * P.t * B + 2 * (P.t - 1) * P.r < P.q) :
    SafeNoise P ((G : ℤ) ^ T * (B : ℤ)) ↔ T ≤ iterCeiling P G B := by
  constructor
  · intro h
    by_contra hlt
    exact T_gt_ceiling_fails P G B T hG hB (by omega) h
  · exact noise_after_T P G B T hG hB h0

/-! ### The end-to-end T-composition keystone. -/

/-- **T iterations, then decrypt: EXACT.** Run `T ≤ iterCeiling` homomorphic public-linear steps
(row bound `G`) from fresh state (noises `≤ B`); any component whose intended clear-iterated
message lands at `mi ∈ [0, t)` (the prox clamp's job — the class-C gate) decrypts to EXACTLY
`mi`. Both silent-failure classes closed for the T-deep convex engine, conditional on the same
named assumptions as the fold path. -/
theorem iter_decrypts_exact {n : ℕ} (P : Params) (S : Fin n → Fin n → ℤ)
    (G B T : ℕ) (x : Fin n → Ct P) (m : Fin n → ℤ)
    (hS : RowBound S ((G : ℕ) : ℤ)) (hG : 2 ≤ G) (hB : 0 < B)
    (hfresh : ∀ j, |(x j).noiseAtInt (m j)| ≤ (B : ℤ))
    (h0 : 2 * P.t * B + 2 * (P.t - 1) * P.r < P.q)
    (hT : T ≤ iterCeiling P G B)
    (i : Fin n) (mi : ℕ) (hmi : (mi : ℤ) = iterMsg S T m i) (hlt : mi < P.t) :
    (iterCt S T x i).decrypt = mi := by
  have hnoise : |(iterCt S T x i).noiseAtInt (iterMsg S T m i)| ≤ (G : ℤ) ^ T * (B : ℤ) :=
    iter_noise_le hS (by positivity) (by positivity) hfresh T i
  have hsafeN : SafeNoise P ((G : ℤ) ^ T * (B : ℤ)) := noise_after_T P G B T hG hB h0 hT
  set e := (iterCt S T x i).noiseAtInt (iterMsg S T m i) with he
  have hsafe_e : SafeNoise P |e| := by
    unfold SafeNoise at hsafeN ⊢
    have ht2 : (0 : ℤ) ≤ 2 * (P.t : ℤ) := by positivity
    linarith [mul_le_mul_of_nonneg_left hnoise ht2]
  have hphase : (iterCt S T x i).phase = (P.Δ : ℤ) * mi + e := by
    rw [he]
    unfold Ct.noiseAtInt
    rw [hmi]
    ring
  show decryptPhase P (iterCt S T x i).phase = mi
  rw [hphase]
  exact decrypt_exact P mi e hlt hsafe_e

/-! ### Deployed pins: the real ceiling on the real numbers, and the cliff past it. -/

/-- The example growth factor of the deployed pins: τ = 1 (`tauDen = tauNum = 1`), `‖A‖∞ ≤ 2`
gives `G = 3`. -/
theorem iterGrowth_example : iterGrowth 1 1 2 = 3 := rfl

/-- **The deployed T ceiling is 42**: on the fhe.rs degree-4096 parameters with `G = 3`,
`B = 2^20`, `iterCeiling = 42` — kernel-checked via the log characterization
(`3^42 ≤ headroom < 3^43` on the real 109-bit `q`). -/
theorem deployed_iterCeiling : iterCeiling fheRs4096 3 (2 ^ 20) = 42 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)

/-- The margin check HOLDS at the ceiling (T = 42), kernel-evaluated on the deployed numbers. -/
theorem deployed_iterMargin_at_ceiling :
    iterMarginHolds fheRs4096 3 (2 ^ 20) 42 = true := by decide

/-- **The margin check FAILS one past the ceiling (T = 43)**, kernel-evaluated — the concrete
one-past-the-ceiling failing side, on the real parameters. -/
theorem deployed_iterMargin_past_ceiling :
    iterMarginHolds fheRs4096 3 (2 ^ 20) 43 = false := by decide

/-- **One past the ceiling, the cliff is REACHABLE:** the T = 43 noise budget `3^43·2^20`
already ADMITS the `decrypt_misses` witness phase — an in-budget-at-43 noise that decrypts
`m = 0` cleanly to `1`. The ceiling is not bookkeeping: one step past it, a silently wrong
decrypt is inside the accumulated envelope. -/
theorem deployed_past_ceiling_admits_misdecrypt :
    ((q4096 : ℤ) / (2 * (t4096 : ℤ)) + 1 ≤ 3 ^ 43 * 2 ^ 20)
      ∧ decryptPhase fheRs4096 ((q4096 : ℤ) / (2 * (t4096 : ℤ)) + 1) = 1 :=
  ⟨by decide, decrypt_misses⟩

#assert_all_clean [Bfv.matVec_noiseAtInt, Bfv.step_noise_le, Bfv.iter_noise_le,
  Bfv.stepMatrix_rowBound, Bfv.safeNoise_natCast_iff, Bfv.iterMargin_iff,
  Bfv.iterMarginHolds_safe, Bfv.noise_after_T, Bfv.T_gt_ceiling_fails,
  Bfv.safeNoise_iff_le_ceiling, Bfv.iter_decrypts_exact, Bfv.deployed_iterCeiling,
  Bfv.deployed_iterMargin_at_ceiling, Bfv.deployed_iterMargin_past_ceiling,
  Bfv.deployed_past_ceiling_admits_misdecrypt]

end Bfv
