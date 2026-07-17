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

end Bfv
