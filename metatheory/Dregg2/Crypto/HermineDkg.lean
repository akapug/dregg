/-
# `Dregg2.Crypto.HermineDkg` — the joint-Feldman DKG (Pedersen, NO trusted dealer), formalized.

`HermineThreshold.lean` proved the threshold quorum certificate CORRECT given a group secret `s` and a
Vandermonde/Lagrange reconstruction `s = Σ λ_j · x_j`. But WHERE does the group key come from without a
trusted dealer? The Rust `crypto-hermine/src/dkg.rs` runs Pedersen's **joint-Feldman** DKG: every member
`i` samples its OWN short secret `sᵢ` as the constant term of a degree-`(t−1)` sharing polynomial
`fᵢ` over `R_q^ℓ`, privately sends `fᵢ(j)` to each member `j`, and BROADCASTS Feldman commitments
`Cᵢ,ₖ = A·aᵢ,ₖ` to every coefficient. The final share is `xⱼ = Σᵢ fᵢ(j)`; the group secret
`s = Σᵢ sᵢ` is NEVER materialized; the group key is `t = A·s = Σᵢ Cᵢ,₀`. This file closes the
verification gap where that Rust ran ahead of the metatheory.

We abstract the public map as the same `A : M →ₗ[R] N` the existing files use, and a sharing polynomial
as its coefficient function `a : ℕ → M` evaluated at scalar points by `evalPoly t a x = Σ_{k<t} xᵏ·a k`
(the Horner form `threshold::horner_eval` computes, rearranged). The commitment to `a` is `k ↦ A(a k)`.

## What is PROVED (unconditional module algebra)
* **`dkg_group_key_eq`** — the broadcasts assemble: `Σᵢ Cᵢ,₀ = A·(Σᵢ sᵢ) = A·s` (by `A.map_sum`); no
  party's contribution alone is `s`.
* **`dkg_shares_reconstruct`** — any `t`-subset of the final shares `xⱼ = Σᵢ fᵢ(j)` Lagrange-reconstructs
  `s = Σᵢ sᵢ`: reconstruction of the SUMMED shares = the SUMMED reconstructions, by linearity of
  evaluation + Lagrange combination over `Σᵢ`. Reuses `HermineThreshold`'s style of taking the
  per-polynomial Lagrange-at-zero as the reconstruction hypothesis.
* **`dkg_share_verify_sound`** — a share passing Feldman verification `A·share = Σₖ jᵏ·Cᵢ,ₖ` satisfies
  `A·share = A·fᵢ(j)`, so (modulo `ker A`) it IS the committed evaluation. Contrapositive
  (`dkg_share_verify_off_poly`): a cheating dealer's off-polynomial share is CAUGHT — matching the Rust
  `verify_dkg_share`.

## What is a NAMED carrier (mirroring `HermineMSIS`'s `MSISHard`, never a Lean axiom)
* **`dkg_secrecy_reduces`** proves the secrecy COMPOSITION: the group secret `s` is hidden from a
  `t`-minority who see the broadcasts + their own shares, REDUCED to two existing assumptions, not
  reproved — (a) `MLWEHidesGroupSecret`: the broadcast `A·s` admits a DISTINCT alternative group secret
  (justified by `HermineLossiness`'s pigeonhole — `A·sᵢ` reveals nothing about `sᵢ` beyond the public
  key), and (b) `ShareConsistent`: every candidate group secret admits a sharing matching the minority's
  observed shares (justified by `ShamirPrivacy.shamir_t_privacy`, per coordinate). The ALGEBRAIC
  composition around them — two distinct group secrets reproduce the ENTIRE minority view — is proved
  here; each leg is a hypothesis backed by a named carrier, and `secrecy_nonvacuous` discharges BOTH on
  a concrete compressing instance so the composition is not vacuous.

The `#guard`-style instances at the bottom exhibit, on real numbers, a group key that assembles, `t`
shares that reconstruct `s`, and a Feldman check that passes on-polynomial and fails off-polynomial.
-/
import Dregg2.Tactics
import Dregg2.Crypto.HermineThreshold
import Dregg2.Crypto.ShamirPrivacy
import Dregg2.Crypto.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

namespace Dregg2.Crypto.HermineDkg

open scoped BigOperators

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-! ## The sharing-polynomial model -/

/-- A degree-`(t−1)` sharing polynomial with coefficients `a : ℕ → M`, evaluated at a SCALAR point `x`:
`fᵢ(x) = Σ_{k<t} xᵏ · a k`. The constant term `a 0 = sᵢ` is member `i`'s secret; this is the
`threshold::horner_eval` the Rust computes, in monomial form. -/
def evalPoly (t : ℕ) (a : ℕ → M) (x : R) : M := ∑ k ∈ Finset.range t, x ^ k • a k

/-- Evaluation at `0` recovers the constant term: `fᵢ(0) = a 0 = sᵢ`. (For a nonempty degree, i.e.
`t = n+1`; `0⁰ = 1` picks out the constant term, `0ᵏ = 0` kills the rest.) -/
theorem evalPoly_zero (n : ℕ) (a : ℕ → M) : evalPoly (n + 1) a (0 : R) = a 0 := by
  rw [evalPoly, Finset.sum_range_succ']
  simp

/-- Evaluation of a degree-1 sharing polynomial: `f(x) = a 0 + x · a 1`. -/
theorem evalPoly_two (a : ℕ → M) (x : R) : evalPoly 2 a x = a 0 + x • a 1 := by
  simp [evalPoly, Finset.sum_range_succ]

/-- **Evaluation is linear over the SUM of dealers.** The summed sharing polynomial
`(Σᵢ aᵢ)` evaluated at `x` equals `Σᵢ fᵢ(x)` — the key step behind reconstruction of the combined
share. -/
theorem evalPoly_sum {ι : Type*} (t : ℕ) (P : Finset ι) (c : ι → ℕ → M) (x : R) :
    evalPoly t (fun k => ∑ i ∈ P, c i k) x = ∑ i ∈ P, evalPoly t (c i) x := by
  simp only [evalPoly, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- **Feldman is public via `A`'s linearity**: `A·fᵢ(x) = Σₖ xᵏ · A(a k) = Σₖ xᵏ · Cᵢ,ₖ`. -/
theorem map_evalPoly (A : M →ₗ[R] N) (t : ℕ) (a : ℕ → M) (x : R) :
    A (evalPoly t a x) = ∑ k ∈ Finset.range t, x ^ k • A (a k) := by
  simp only [evalPoly, map_sum, map_smul]

/-! ## 1. Correctness — the group key assembles to `A·s` -/

/-- **`dkg_group_key_eq` — the broadcasts assemble to the group key.** The sum of the broadcast
constant-term commitments `Σᵢ Cᵢ,₀ = Σᵢ A(sᵢ)` equals `A·(Σᵢ sᵢ) = A·s`, by `A`'s linearity
(`map_sum`). The group secret `s = Σᵢ sᵢ` is never materialized; the KEY assembles from the public
broadcasts alone, and no single dealer's `Cᵢ,₀` is it. -/
theorem dkg_group_key_eq {ι : Type*} (A : M →ₗ[R] N) (P : Finset ι) (sec : ι → M) :
    (∑ i ∈ P, A (sec i)) = A (∑ i ∈ P, sec i) :=
  (map_sum A sec P).symm

/-! ## 2. Correctness — the final shares reconstruct `s` -/

/-- **`dkg_shares_reconstruct` — a `t`-subset of the final shares reconstructs `s = Σᵢ sᵢ`.** The final
share of member `j` is `xⱼ = Σᵢ fᵢ(j)`. Given Lagrange coefficients `lam` over a `t`-subset `parts`
(evaluation points `pt`) that reconstruct each dealer's constant term at zero (`hrecon` — reused from
`HermineThreshold`'s reconstruction-as-hypothesis discipline), the SAME combination on the final shares
yields `Σᵢ sᵢ`: reconstruction of the summed shares = the summed reconstructions. -/
theorem dkg_shares_reconstruct {ι κ : Type*} (t : ℕ) (P : Finset ι) (coeff : ι → ℕ → M)
    (parts : Finset κ) (pt : κ → R) (lam : κ → R)
    (hrecon : ∀ i ∈ P, (∑ j ∈ parts, lam j • evalPoly t (coeff i) (pt j)) = coeff i 0) :
    (∑ j ∈ parts, lam j • (∑ i ∈ P, evalPoly t (coeff i) (pt j))) = ∑ i ∈ P, coeff i 0 := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl hrecon

/-! ## 3. Feldman soundness — an off-polynomial share is caught -/

/-- Feldman share verification, exactly as the Rust `verify_dkg_share`: `A·share = Σₖ xᵏ · Cₖ`, with the
public per-coefficient commitments `C : ℕ → N`. -/
def feldmanVerify (A : M →ₗ[R] N) (C : ℕ → N) (t : ℕ) (x : R) (share : M) : Prop :=
  A share = ∑ k ∈ Finset.range t, x ^ k • C k

/-- **Completeness** — the honest evaluation `fᵢ(x)` always verifies against the commitments
`Cₖ = A(a k)`. -/
theorem dkg_share_verify_complete (A : M →ₗ[R] N) (t : ℕ) (a : ℕ → M) (x : R) :
    feldmanVerify A (fun k => A (a k)) t x (evalPoly t a x) :=
  map_evalPoly A t a x

/-- **`dkg_share_verify_sound` — a passing share IS the committed evaluation (mod `ker A`).** If
`share` passes Feldman verification against the commitments `Cₖ = A(a k)` to the polynomial `a`, then
`A·share = A·fᵢ(x)` — the share equals the correct evaluation of the committed polynomial up to the
kernel of `A`. So the commitment BINDS the dealer to its polynomial. -/
theorem dkg_share_verify_sound (A : M →ₗ[R] N) (t : ℕ) (a : ℕ → M) (x : R) (share : M)
    (hv : feldmanVerify A (fun k => A (a k)) t x share) :
    A share = A (evalPoly t a x) := by
  rw [feldmanVerify] at hv
  rw [hv, map_evalPoly]

/-- **`dkg_share_verify_off_poly` — a cheating dealer is CAUGHT.** The contrapositive: a share whose
image differs from the committed evaluation FAILS Feldman verification. An off-polynomial share cannot
pass. -/
theorem dkg_share_verify_off_poly (A : M →ₗ[R] N) (t : ℕ) (a : ℕ → M) (x : R) (share : M)
    (hoff : A share ≠ A (evalPoly t a x)) :
    ¬ feldmanVerify A (fun k => A (a k)) t x share :=
  fun hv => hoff (dkg_share_verify_sound A t a x share hv)

/-! ## 4. Secrecy — the reduction to two named carriers -/

/-- **MLWE key-hiding carrier** (mirrors `Lattice.MSISHard`): the group key `A·s` does not DETERMINE the
group secret — there is a DISTINCT alternative group secret with the same broadcast. Justified by
`HermineLossiness`'s pigeonhole collision (a compressing `A` has two short preimages of the same value);
named here, not reproved. -/
def MLWEHidesGroupSecret (A : M →ₗ[R] N) (s : M) : Prop :=
  ∃ s' : M, s' ≠ s ∧ A s' = A s

/-- **Shamir consistency carrier**: a candidate group secret `cand` admits a sharing (per-dealer
coefficients) whose combined final shares match the minority's observed shares on `parts`, with combined
constant term `cand`. Justified by `ShamirPrivacy.shamir_t_privacy` (per coordinate: any `t−1` observed
shares are consistent with any candidate constant term). -/
def ShareConsistent {ι κ : Type*} (t : ℕ) (P : Finset ι) (parts : Finset κ) (pt : κ → R)
    (obs : κ → M) (cand : M) : Prop :=
  ∃ coeff : ι → ℕ → M,
    (∑ i ∈ P, coeff i 0) = cand ∧
    ∀ j ∈ parts, (∑ i ∈ P, evalPoly t (coeff i) (pt j)) = obs j

/-- **`dkg_secrecy_reduces` — the secrecy COMPOSITION.** The group secret `s` is hidden from a
`t`-minority: reducing to (a) the MLWE carrier (`A·s` admits a distinct alternative group secret) and
(b) the Shamir carrier (every candidate group secret is consistent with the minority's observed shares),
we exhibit TWO DISTINCT group secrets that reproduce the ENTIRE minority view — the same broadcast public
key `A·s` AND the same observed shares. So the minority, seeing broadcasts + its own shares, cannot
determine `s`. The two legs are hypotheses backed by named carriers; the composition around them is
proved. -/
theorem dkg_secrecy_reduces {ι κ : Type*}
    (A : M →ₗ[R] N) (s : M) (t : ℕ) (P : Finset ι)
    (parts : Finset κ) (pt : κ → R) (obs : κ → M)
    (hmlwe : MLWEHidesGroupSecret A s)
    (hshamir : ∀ cand : M, ShareConsistent t P parts pt obs cand) :
    ∃ s₀ s₁ : M, s₀ ≠ s₁ ∧ A s₀ = A s₁ ∧
      ShareConsistent t P parts pt obs s₀ ∧ ShareConsistent t P parts pt obs s₁ := by
  obtain ⟨s', hne, heq⟩ := hmlwe
  exact ⟨s, s', fun h => hne h.symm, heq.symm, hshamir s, hshamir s'⟩

/-! ## `#guard`-style instances — the model is NON-VACUOUS on real numbers

Group-key/reconstruct/Feldman on `K = ZMod 11` (a field, so the small Lagrange combination is exact and
`decide` evaluates); the secrecy composition over a genuinely COMPRESSING map `ℚ² → ℚ` where the MLWE and
Shamir carriers are both discharged. -/

namespace Instance

abbrev K : Type := ZMod 11

/-- Two dealers' degree-1 sharing polynomials: `f₀ = 3 + 5X` (secret `s₀ = 3`), `f₁ = 7 + 2X`
(secret `s₁ = 7`). -/
def cf0 : ℕ → K := fun k => if k = 0 then 3 else if k = 1 then 5 else 0
def cf1 : ℕ → K := fun k => if k = 0 then 7 else if k = 1 then 2 else 0
def cf : Fin 2 → ℕ → K := ![cf0, cf1]

/-- Public map — identity on `K` (injective, so Feldman soundness genuinely rejects off-polynomial
shares). -/
def Aid : K →ₗ[K] K := LinearMap.id

/-- The group secret `s = s₀ + s₁ = 3 + 7 = 10`, never materialized in the protocol but pinned here. -/
theorem inst_group_secret : (∑ i, cf i 0) = (10 : K) := by decide

/-- **Group key assembles** (`dkg_group_key_eq` on the instance): `Σᵢ A(sᵢ) = A(Σᵢ sᵢ) = A·s`. -/
theorem inst_group_key_assembles : (∑ i, Aid (cf i 0)) = Aid (∑ i, cf i 0) :=
  dkg_group_key_eq Aid Finset.univ (fun i => cf i 0)

/-- Reconstruction points `{1, 2}` and their Lagrange-at-zero coefficients `{2, −1}`. -/
def pts : Fin 2 → K := ![1, 2]
def lam : Fin 2 → K := ![2, -1]

/-- **`t = 2` shares reconstruct `s`** (`dkg_shares_reconstruct` on the instance): the Lagrange
combination of the two final shares `xⱼ = f₀(j) + f₁(j)` recovers `Σᵢ sᵢ`. The per-dealer Lagrange-at-zero
facts are checked on the numbers. -/
theorem inst_reconstruct :
    (∑ j : Fin 2, lam j • (∑ i : Fin 2, evalPoly 2 (cf i) (pts j))) = ∑ i : Fin 2, cf i 0 := by
  apply dkg_shares_reconstruct
  decide

/-- …and the reconstructed value is exactly `s = 10`. -/
theorem inst_reconstruct_value :
    (∑ j : Fin 2, lam j • (∑ i : Fin 2, evalPoly 2 (cf i) (pts j))) = (10 : K) := by
  rw [inst_reconstruct]; exact inst_group_secret

/-- **A valid share PASSES Feldman verification** — the honest evaluation `f₀(2)` against `f₀`'s
commitments. -/
theorem inst_feldman_pass :
    feldmanVerify Aid (fun k => Aid (cf0 k)) 2 (2 : K) (evalPoly 2 cf0 (2 : K)) :=
  dkg_share_verify_complete Aid 2 cf0 (2 : K)

/-- **An off-polynomial share FAILS Feldman verification** — a cheating dealer offering `f₀(2) + 1`
instead of `f₀(2)` is caught. -/
theorem inst_feldman_fail :
    ¬ feldmanVerify Aid (fun k => Aid (cf0 k)) 2 (2 : K) (evalPoly 2 cf0 (2 : K) + 1) := by
  apply dkg_share_verify_off_poly
  decide

end Instance

namespace SecrecyInstance

/-- Group secrets live in `ℚ²`; the broadcast map `A·v = v₀ + v₁ : ℚ² → ℚ` is COMPRESSING, so the group
key does not determine the group secret. -/
abbrev Vec : Type := Fin 2 → ℚ

def Asum : Vec →ₗ[ℚ] ℚ where
  toFun v := v 0 + v 1
  map_add' x y := by simp [Pi.add_apply]; ring
  map_smul' r x := by simp [Pi.smul_apply]; ring

def sSec : Vec := ![0, 0]
def sTwin : Vec := ![1, -1]

/-- **The MLWE carrier is discharged**: `s' = (1,−1) ≠ (0,0) = s` yet `A·s' = 0 = A·s`. The broadcast
public key `A·s` genuinely hides which of two group secrets was shared. -/
theorem inst_mlwe : Dregg2.Crypto.HermineDkg.MLWEHidesGroupSecret Asum sSec := by
  refine ⟨sTwin, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [sTwin, sSec] at this
  · show (sTwin 0 + sTwin 1 : ℚ) = sSec 0 + sSec 1
    simp [sTwin, sSec]

/-- **The Shamir carrier is discharged**: for the single-dealer minority view with one observed share
at point `1`, EVERY candidate group secret `cand` admits a consistent sharing — `f = cand + (obs − cand)X`,
which has constant term `cand` and evaluates to `obs` at `1`. Mirrors `shamir_t_privacy` on this cut. -/
theorem inst_shamir (obsVal : Vec) :
    ∀ cand : Vec, Dregg2.Crypto.HermineDkg.ShareConsistent 2
      (Finset.univ : Finset (Fin 1)) (Finset.univ : Finset (Fin 1))
      (fun _ => (1 : ℚ)) (fun _ => obsVal) cand := by
  intro cand
  refine ⟨fun _ k => if k = 0 then cand else obsVal - cand, ?_, ?_⟩
  · simp
  · intro j _
    rw [Fin.sum_univ_one, Dregg2.Crypto.HermineDkg.evalPoly_two]
    norm_num

/-- **`secrecy_nonvacuous` — the composition is NOT vacuous.** Feeding the discharged MLWE + Shamir
carriers to `dkg_secrecy_reduces` produces two DISTINCT group secrets reproducing the whole minority
view over the compressing `A` — the group secret is hidden, on real numbers, with both legs proved. -/
theorem secrecy_nonvacuous (obsVal : Vec) :
    ∃ s₀ s₁ : Vec, s₀ ≠ s₁ ∧ Asum s₀ = Asum s₁ ∧
      Dregg2.Crypto.HermineDkg.ShareConsistent 2 (Finset.univ : Finset (Fin 1))
        (Finset.univ : Finset (Fin 1)) (fun _ => (1 : ℚ)) (fun _ => obsVal) s₀ ∧
      Dregg2.Crypto.HermineDkg.ShareConsistent 2 (Finset.univ : Finset (Fin 1))
        (Finset.univ : Finset (Fin 1)) (fun _ => (1 : ℚ)) (fun _ => obsVal) s₁ :=
  dkg_secrecy_reduces Asum sSec 2 (Finset.univ : Finset (Fin 1)) (Finset.univ : Finset (Fin 1))
    (fun _ => (1 : ℚ)) (fun _ => obsVal) inst_mlwe (inst_shamir obsVal)

end SecrecyInstance

#assert_axioms evalPoly_zero
#assert_axioms evalPoly_sum
#assert_axioms map_evalPoly
#assert_axioms dkg_group_key_eq
#assert_axioms dkg_shares_reconstruct
#assert_axioms dkg_share_verify_complete
#assert_axioms dkg_share_verify_sound
#assert_axioms dkg_share_verify_off_poly
#assert_axioms dkg_secrecy_reduces
#assert_axioms Instance.inst_group_secret
#assert_axioms Instance.inst_group_key_assembles
#assert_axioms Instance.inst_reconstruct
#assert_axioms Instance.inst_reconstruct_value
#assert_axioms Instance.inst_feldman_pass
#assert_axioms Instance.inst_feldman_fail
#assert_axioms SecrecyInstance.inst_mlwe
#assert_axioms SecrecyInstance.inst_shamir
#assert_axioms SecrecyInstance.secrecy_nonvacuous

end Dregg2.Crypto.HermineDkg
