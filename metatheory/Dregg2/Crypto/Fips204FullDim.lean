/-
# `Dregg2.Crypto.Fips204FullDim` — `Fips204Correct` at FULL ML-DSA-65 DIMENSION: the deployed
`dregg_pq_correct` is fed a full-dimension proof, not the `n = 1` caricature.

`DreggPqRefinement.dregg_pq_correct` takes `hfips : Fips204Correct api` as the trusted primitive floor.
It WAS discharged — but only for `Fips204Verify.extractedApi` / `signExtractedApi`, which live at
`realParams`: `n = 1`, `A = LinearMap.id`, the CONSTANT challenge `c = 1`, and a single FIXED secret
`(s₁,s₂,t₀) = (5,1,3)` with the fixed mask `y = 40`. Those are real DEPLOYED parameters (`q`, `γ₂`, `α`,
`β`, `γ₁−β`) but a SCALAR caricature of the ML-DSA-65 module — the correctness floor of the deployed
refinement was fed a toy.

THIS FILE closes that. It assembles the api at the REAL dimension and proves `Fips204Correct` there,
UNIVERSALLY:

  * **THE RING AND MODULES ARE REAL.** `Rq = ℤ_q[X]/(X²⁵⁶+1)` (`q = 8380417`, `root²⁵⁶ = −1`, power-basis
    dimension EXACTLY 256), `M = R_q^5`, `N = R_q^6` — ML-DSA-65's `(k, ℓ) = (6, 5)`. Reused verbatim from
    `Fips204CorrectReal` (BRICK: the componentwise `realRoundingK` whose two `RoundingScheme` lemma-fields
    are PROVED over all `6 × 256` coefficients, `ℤ_q`-wrap included).

  * **`A` IS ARBITRARY.** `fullParams` takes ANY `R_q`-linear `A : M →ₗ[Rq] N` — the ExpandA matrix is a
    variable, not `id`. Correctness needs only linearity, so this is the strongest form.

  * **THE CHALLENGE SAMPLER AND THE HASH ARE ARBITRARY.** `fullParams` takes ANY `hash : Msg → Coeffs →
    Cbar` and ANY `chal : Cbar → Rq`. There is NO `c = 1`, no `hash = 0`: the round-trip is proven for
    EVERY SampleInBall and EVERY Fiat–Shamir hash (correctness is hash-agnostic — only the post-rejection
    NORM gates on `c·s₁`, `c·s₂`, `c·t₀` matter, and those are hypotheses of the honest key).
    `Fips204CorrectReal.realParamsK` fixed both (`hash _ _ := 0`, `challenge _ := 1`); this does not.

  * **THE SECRET IS ARBITRARY.** The seed type is `HonestKey A hash chal` — ANY `(s₁, s₂, t₀, thi)` with
    Power2Round consistency and ANY per-message accepted mask. No fixed `(5,1,3)`, no fixed `y = 40`.

`fullDimApi_fips204 : Fips204Correct (fullDimApi A hash chal)` is then a ∀-theorem over all of that, and
`fullDimApi_correct : Correct (dreggPqSigScheme (fullDimApi A hash chal))` feeds it straight into the
deployed `dregg_pq_correct`. KERNEL-CLEAN: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} —
no `sorryAx`, and NO `native_decide` (no `Lean.ofReduceBool` / `Lean.trustCompiler`). The symbolic route
was taken precisely so the full-dimension floor does not trade the toy residual for a compiler residual:
`MlDsaVerifyReal.verify_accepts_real` (which DOES ride `native_decide`) is a byte-level KAT and is NOT
used here.

## THE ONE NAMED RESIDUAL — the accepted-iteration certificate (`HonestKey`)

The seed of the real API is 32 bytes; the seed here is an `HonestKey`, which BUNDLES the four
post-rejection gates as fields:

  * `power2round` — `A·s₁ + s₂ = thi + t₀` (a definitional property of keygen, not a residual);
  * `hint_small`  — `‖c·t₀‖ ≤ γ₂`, `cs2_small` — `‖c·s₂‖ ≤ β`, `resp_bound` — `‖y + c·s₁‖ < γ₁−β`;
  * `commit_gap`  — `LowBits(A·y)` in the gap `[β, α−β)`.

These are EXACTLY the four gates FIPS 204 Algorithm 7's rejection loop evaluates before it returns a
signature; a key carries, per message, the mask the loop ACCEPTED. So the residual is precisely the
Dilithium **rejection-termination** fact ("the loop finds an accepting mask") that `Fips204Spec`'s honest
boundary already NAMES — a probabilistic statement (expected ≈ 4.25 iterations), NOT a mathematical
theorem, and NOT a hardness carrier. What is retired is the toy-ness: dimension, `A`, the sampler, the
hash and the secret are now universally quantified.

`fips204Correct_of_fullDim` exports the bridge for ANY byte-level api (e.g. the `MlDsaSignReal` /
`MlDsaVerifyReal` cores): produce an `HonestKey` per seed whose observable verify agrees, and
`Fips204Correct` follows at full dimension. Wiring the byte codec through it is the next lane (it needs
the `Poly ↔ Rq` coefficient bridge, i.e. `NttFaithful`'s ring-faithfulness lifted to `AdjoinRoot`'s power
basis — see the NEXT LANE note at the bottom).

## NON-VACUITY (both directions, at full dimension)

  * `honestKey` — a NON-DEGENERATE inhabitant: `s₁ ≠ 0`, `s₂ ≠ 0`, `t₀ ≠ 0` (`s1Rt_ne_zero`,
    `t0Rt_ne_zero`), over `R_q^k`, with a gapped commitment and gate values at the DEPLOYED magnitudes
    (`‖c·s₂‖∞ = η = 4 ≤ β = 196`, `‖c·t₀‖∞ = 2^{d−1} = 4096 ≤ γ₂`). Its challenge is `c = root` — a
    genuine NON-SCALAR element of `R_q` (`rt_not_scalar`: `root ≠ a·1` for every `a ∈ ℤ_q`), a UNIT by
    `root²⁵⁶ = −1` (`rt_mul_rtInv`) — so the witness does NOT smuggle back the `c = 1` caricature. Holds
    for ANY hash. (It is the `τ = 1` monomial, not the `τ = 49` SampleInBall ball — that needs the
    negacyclic shift lemma, NEXT LANE below.)
  * `fullDim_honest_verifies` — the honest full-dimension signature VERIFIES.
  * `fullDim_rejects_out_of_norm` — for EVERY `A`, hash, sampler, key and message, a signature whose `z`
    has an out-of-range coefficient is REJECTED. The verify gate is real at full dimension, not `fun _ =>
    true`.
-/
import Dregg2.Crypto.Fips204CorrectReal

namespace Dregg2.Crypto.Fips204FullDim

open Dregg2.Crypto.Fips204Spec
open Dregg2.Crypto.DreggPqRefinement
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Fips204CorrectReal
open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-! ## PART 1 — the FULL-DIMENSION ML-DSA-65 params: real ring, ARBITRARY `A` / hash / sampler.

`Fips204CorrectReal` supplies the real objects: `Rq = ℤ_q[X]/(X²⁵⁶+1)`, `M = R_q^5`, `N = R_q^6`,
`Coeffs = Fin 6 → Fin 256 → ℤ`, and `realRoundingK` — the FIPS 204 round-to-nearest decomposition
(`γ₂ = 261888`, `α = 523776`, `β = 196`) applied to each of the `6 × 256` coefficients, with both
`RoundingScheme` lemma-fields PROVED. Here we quantify over everything the caricature had fixed. -/

/-- The DEPLOYED response gate `‖z‖∞ < γ₁ − β = 524092` over `M = R_q^ℓ`, coefficientwise on the
canonical `ℤ_q` representatives (a coefficient is in range iff its rep is `< 524092` — the positive
side — or `> q − 524092` — the negative side). Decidable, so it is a genuine `Bool` gate. -/
noncomputable def zGate (z : M) : Bool :=
  decide (∀ i j, rv (z i) j < 524092 ∨ 8380417 - 524092 < rv (z i) j)

/-- **THE FULL-DIMENSION ML-DSA-65 INSTANCE.** The real ring/modules, the real componentwise rounding at
the deployed literals, and — unlike `Fips204Verify.realParams` (`A = id`, `c = 1`) and
`Fips204CorrectReal.realParamsK` (`hash = 0`, `challenge = 1`) — an ARBITRARY linear `A` (the ExpandA
matrix), an ARBITRARY Fiat–Shamir `hash`, and an ARBITRARY `SampleInBall` sampler `chal`. -/
noncomputable def fullParams {Msg Cbar : Type*} (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) :
    MlDsaParams Rq M N Coeffs Coeffs Cbar Msg where
  A := A
  round := realRoundingK
  hash := hash
  challenge := chal
  zBoundB := zGate

/-- The honest challenge at message `μ` on mask `y`: `c = SampleInBall(H(μ, HighBits(A·y)))` — the
Fiat–Shamir fixed point the verifier re-derives. -/
noncomputable def challengeAt {Msg Cbar : Type*} (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) (μ : Msg) (y : M) : Rq :=
  chal (hash μ (realRoundingK.highBits (A y)))

/-! ## PART 2 — the honest key = the ACCEPTED-ITERATION CERTIFICATE (the one named residual).

An honest ML-DSA-65 signer is a secret `(s₁, s₂, t₀)` with public high part `thi` (Power2Round), plus —
per message — the mask its rejection loop ACCEPTED. `HonestKey` is exactly that: the four fields
`hint_small`/`cs2_small`/`commit_gap`/`resp_bound` are the four gates FIPS 204 Algorithm 7 evaluates
before returning. Nothing about dimension, `A`, the sampler, the hash or the secret is fixed. -/

/-- **THE HONEST ML-DSA-65 KEY (accepted-iteration certificate).** Arbitrary secret `(s₁, s₂, t₀)` over the
REAL `R_q^ℓ`/`R_q^k`, arbitrary public high part `thi` subject to Power2Round consistency, and a mask per
message carrying the four post-rejection gates of FIPS 204 Algorithm 7. -/
structure HonestKey {Msg Cbar : Type*} (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) where
  /-- The secret `s₁ ∈ R_q^ℓ`. -/
  s1 : M
  /-- The secret `s₂ ∈ R_q^k`. -/
  s2 : N
  /-- The secret low part `t₀ ∈ R_q^k` (Power2Round). -/
  t0 : N
  /-- The public high part `thi = t₁·2^d ∈ R_q^k`. -/
  thi : N
  /-- The mask the rejection loop ACCEPTED for this message (FIPS 204 Alg. 7's `y` at the accepting `κ`). -/
  mask : Msg → M
  /-- Power2Round consistency: `t = A·s₁ + s₂ = thi + t₀`. -/
  power2round : A s1 + s2 = thi + t0
  /-- Gate `‖c·t₀‖∞ ≤ γ₂` — the `MakeHint` precondition. -/
  hint_small : ∀ μ : Msg, realRoundingK.nearGamma2 (-(challengeAt A hash chal μ (mask μ) • t0))
  /-- Gate `‖c·s₂‖∞ ≤ β` — the high-bits perturbation bound. -/
  cs2_small : ∀ μ : Msg, realRoundingK.betaSmall (-(challengeAt A hash chal μ (mask μ) • s2))
  /-- Gate `LowBits(A·y) ∈ [β, α−β)` — the commitment low-gap (the resampled condition). -/
  commit_gap : ∀ μ : Msg, realRoundingK.lowGap (A (mask μ))
  /-- Gate `‖z‖∞ = ‖y + c·s₁‖∞ < γ₁ − β` — the response norm bound. -/
  resp_bound : ∀ μ : Msg, zGate (mask μ + challengeAt A hash chal μ (mask μ) • s1) = true

/-! ## PART 3 — the FULL-DIMENSION `DreggPqApi`, and `Fips204Correct` PROVEN there. -/

/-- **THE FULL-DIMENSION `dregg-pq` ML-DSA API.** Seeds are honest ML-DSA-65 keys (accepted-iteration
certificates), public keys are the real `thi ∈ R_q^k`, signatures are the real `(c̃, z, h) ∈ Cbar × R_q^ℓ ×
Coeffs`. `sign`/`verify` are the FIPS 204 equations of `fullParams` at the REAL ring — no `n = 1`, no
`A = id`, no constant challenge, no fixed secret. -/
noncomputable def fullDimApi {Msg Cbar Ctx : Type*} [DecidableEq Cbar] (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) :
    DreggPqApi (HonestKey A hash chal) N Ctx Msg (Cbar × M × Coeffs) where
  keygen K := K.thi
  sign K _ μ := (fullParams A hash chal).sign K.s1 K.s2 K.t0 μ (K.mask μ)
  verify thi _ μ σ := (fullParams A hash chal).verifyB thi μ σ

/-- **`Fips204Correct` AT FULL ML-DSA-65 DIMENSION.** For EVERY `R_q`-linear `A`, EVERY Fiat–Shamir hash,
EVERY `SampleInBall` sampler, EVERY honest key (arbitrary secret + accepted mask) and EVERY message, the
full-dimension verify ACCEPTS the full-dimension signature. This is the trusted floor of
`DreggPqRefinement`, now discharged over `R_q^k` (`R_q = ℤ_q[X]/(X²⁵⁶+1)`, `(k,ℓ) = (6,5)`) instead of the
`n = 1`, `A = id`, `c = 1`, fixed-secret caricature. Derived from the generic `Fips204Spec.fips204_correct`
via the componentwise `realRoundingK` — KERNEL-CLEAN, no `native_decide`. -/
theorem fullDimApi_fips204 {Msg Cbar Ctx : Type*} [DecidableEq Cbar] (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) :
    Fips204Correct (Ctx := Ctx) (fullDimApi A hash chal) := by
  intro K _ μ
  exact fips204_correct (fullParams A hash chal) K.s1 K.s2 K.t0 K.thi μ (K.mask μ)
    (challengeAt A hash chal μ (K.mask μ)) rfl K.power2round (K.hint_small μ) (K.cs2_small μ)
    (K.commit_gap μ) (K.resp_bound μ)

/-- **THE DEPLOYED REFINEMENT, FED A FULL-DIMENSION FLOOR.** `dreggPqSigScheme (fullDimApi …)` satisfies
`Correct` — every honestly-produced signature verifies — with `dregg_pq_correct`'s `hfips` hypothesis
supplied by the FULL-DIMENSION `fullDimApi_fips204`, not by the `n = 1` `extractedApi_fips204`. This is
the payoff: the deployed correctness conclusion now rides the real ML-DSA-65 module. -/
theorem fullDimApi_correct {Msg Cbar Ctx : Type*} [DecidableEq Cbar] (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) :
    Correct (dreggPqSigScheme (Ctx := Ctx) (fullDimApi A hash chal)) :=
  dregg_pq_correct (fullDimApi A hash chal) (fullDimApi_fips204 A hash chal)

/-- **THE EXPORT BRIDGE — any api that agrees with the full-dimension equations inherits the floor.**
For an arbitrary `DreggPqApi` (in particular the byte-level `MlDsaSignReal`/`MlDsaVerifyReal` cores), it
suffices to exhibit, per seed, an `HonestKey` at full dimension whose modeled verify agrees with the api's
observable verify. Then `Fips204Correct` holds for THAT api — at real dimension. The remaining obligation
is the codec/NTT bridge (`Poly ↔ R_q` coefficients), NOT the ML-DSA algebra. -/
theorem fips204Correct_of_fullDim {Msg Cbar Ctx Seed PK : Type*} [DecidableEq Cbar]
    (A : M →ₗ[Rq] N) (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq)
    (api : DreggPqApi Seed PK Ctx Msg (Cbar × M × Coeffs))
    (key : Seed → HonestKey A hash chal)
    (agree : ∀ (seed : Seed) (ctx : Ctx) (msg : Msg),
      api.verify (api.keygen seed) ctx msg (api.sign seed ctx msg)
        = (fullParams A hash chal).verifyB (key seed).thi msg
            ((fullParams A hash chal).sign (key seed).s1 (key seed).s2 (key seed).t0 msg
              ((key seed).mask msg))) :
    Fips204Correct api := by
  intro seed ctx msg
  rw [agree seed ctx msg]
  exact fullDimApi_fips204 (Ctx := Ctx) A hash chal (key seed) ctx msg

/-! ## PART 4 — NON-VACUITY (accept side): a NON-DEGENERATE honest key, with a NON-SCALAR challenge.

The witness must not quietly re-introduce the caricature it retires. So:

  * the secret is NONZERO at the DEPLOYED magnitudes — the gate-side `−(c·s₂)` is `η = 4` in every one of
    the `6 × 256` coefficients, the gate-side `−(c·t₀)` is `2^{d−1} = 4096` in every one — and `thi` is the
    induced Power2Round high part;
  * the challenge is `c = root` — a genuine NON-SCALAR element of `R_q` (`rt_not_scalar`: it is not
    `a · 1` for ANY `a ∈ ℤ_q`), NOT the `c = 1` of the caricature. It is a UNIT (`rt_mul_rtInv`, from
    `root²⁵⁶ = −1`), which is what lets the secret be defined as `c⁻¹ · (gate value)`: the gates then hold
    by RING ALGEBRA in `R_q`, with no coefficient-of-a-product computation;
  * the commitment `A·y` is the gapped `wVec` (all coefficients `300000`, low part `38112 ∈ [β, α−β)`), so
    `commit_gap` holds, and the response `y + c·s₁` has coefficients `≤ 5 ≪ γ₁−β`;
  * it holds for ANY Fiat–Shamir hash.

(`c = root` is the `τ = 1` monomial, not the `τ = 49` SampleInBall ball — that needs the negacyclic shift
lemma, NEXT LANE below. What it establishes is that neither the theorem NOR the witness rests on a scalar
challenge.) -/

/-- The ring generator `root ∈ R_q` (the class of `X`). -/
noncomputable def rt : Rq := AdjoinRoot.root (X ^ 256 + 1 : (ZMod q)[X])

/-- The inverse of `root`: `−root²⁵⁵`. -/
noncomputable def rtInv : Rq := -(rt ^ 255)

/-- **`root` IS A UNIT of `R_q`** — `root · (−root²⁵⁵) = −root²⁵⁶ = 1`, straight from the negacyclic law
`root²⁵⁶ = −1` (`Fips204CorrectReal.root_pow_256`). This is what makes a NON-SCALAR challenge witness
constructible without computing any product's coefficients. -/
theorem rt_mul_rtInv : rt * rtInv = 1 := by
  have h : rt ^ 256 = -1 := root_pow_256
  unfold rtInv
  have hexp : rt * -(rt ^ 255) = -(rt ^ 256) := by ring
  rw [hexp, h, neg_neg]

theorem one_lt_dim : 1 < pb.dim := by rw [realDim]; norm_num

/-- The power-basis index `1` (legal because the dimension is `256`). -/
noncomputable def j1 : Fin pb.dim := ⟨1, one_lt_dim⟩
/-- The power-basis index `0`. -/
noncomputable def j0 : Fin pb.dim := ⟨0, dim_pos⟩

theorem basis_j1 : pb.basis j1 = rt := by
  rw [pb.basis_eq_pow]
  show pb.gen ^ (1 : ℕ) = rt
  rw [pow_one]
  unfold pb rt
  rw [AdjoinRoot.powerBasis'_gen]

theorem basis_j0 : pb.basis j0 = (1 : Rq) := by
  rw [pb.basis_eq_pow]; simp [j0]

/-- **THE WITNESS CHALLENGE IS NOT A SCALAR.** `root ≠ a · 1` for EVERY `a ∈ ℤ_q` — its power-basis
coordinate at index `1` is `1`, while every scalar's is `0`. So the non-vacuity witness does NOT smuggle
back the `challenge _ := 1` caricature: it uses a genuine degree-`1` element of the `256`-dimensional
ring. -/
theorem rt_not_scalar (a : ZMod q) : rt ≠ a • (1 : Rq) := by
  intro h
  have hrt : pb.basis.repr rt j1 = 1 := by
    rw [← basis_j1, pb.basis.repr_self_apply, if_pos rfl]
  have hsc : pb.basis.repr (a • (1 : Rq)) j1 = 0 := by
    rw [map_smul, Finsupp.smul_apply, ← basis_j0, pb.basis.repr_self_apply,
      if_neg (by simp [j0, j1, Fin.ext_iff]), smul_zero]
  rw [h, hsc] at hrt
  exact one_ne_zero hrt.symm

/-- The WITNESS sampler: the constant NON-SCALAR challenge `c = root` (the theorem quantifies over ALL
samplers; the witness must merely exhibit one that is not a caricature). -/
noncomputable def rtChal {Cbar : Type*} : Cbar → Rq := fun _ => rt

theorem challengeAt_rt {Msg Cbar : Type*} (hash : Msg → Coeffs → Cbar) (μ : Msg) (y : M) :
    challengeAt honestA hash (rtChal (Cbar := Cbar)) μ y = rt := rfl

/-! ### The gate values, at the deployed magnitudes. -/

/-- `η = 4` in every coefficient — the gate value of `−(c·s₂)` (so `‖c·s₂‖∞ = 4 ≤ β = 196`). -/
noncomputable def etaElt : Rq := mkElt (fun _ => (4 : ZMod q))
/-- `2^{d−1} = 4096` in every coefficient — the gate value of `−(c·t₀)` (so `‖c·t₀‖∞ = 4096 ≤ γ₂`). -/
noncomputable def t0Elt : Rq := mkElt (fun _ => (4096 : ZMod q))

theorem etaElt_rv (j : Fin pb.dim) : rv etaElt j = 4 := by
  unfold rv etaElt
  rw [mkElt_coeff]
  have hv : (4 : ZMod q).val = 4 := ZMod.val_ofNat_of_lt (by rw [q_val]; norm_num)
  rw [hv]; norm_num

theorem t0Elt_rv (j : Fin pb.dim) : rv t0Elt j = 4096 := by
  unfold rv t0Elt
  rw [mkElt_coeff]
  have hv : (4096 : ZMod q).val = 4096 := ZMod.val_ofNat_of_lt (by rw [q_val]; norm_num)
  rw [hv]; norm_num

/-- The secret `s₁ ∈ R_q^ℓ` — `c⁻¹ · η`, so `c·s₁` is the small `η` gate value. NONZERO. -/
noncomputable def s1Rt : M := fun _ => rtInv * etaElt
/-- The secret `s₂ ∈ R_q^k` — `−c⁻¹ · η`, so `−(c·s₂)` is the small `η` gate value. NONZERO. -/
noncomputable def s2Rt : N := fun _ => -(rtInv * etaElt)
/-- The secret low part `t₀ ∈ R_q^k` — `−c⁻¹ · 2^{d−1}`, so `−(c·t₀)` is the `2^{d−1}` gate value. NONZERO. -/
noncomputable def t0Rt : N := fun _ => -(rtInv * t0Elt)
/-- The induced public high part `thi = A·s₁ + s₂ − t₀` (Power2Round consistency by construction). -/
noncomputable def thiRt : N := honestA s1Rt + s2Rt - t0Rt

/-- `c · s₁ = η` — the challenge cancels the `c⁻¹`, by ring algebra in `R_q`. -/
theorem rt_smul_s1Rt (i : Fin ell) : (rt • s1Rt) i = etaElt := by
  show rt • (rtInv * etaElt) = etaElt
  rw [smul_eq_mul, ← mul_assoc, rt_mul_rtInv, one_mul]

/-- `−(c · s₂) = η` — the gate value, at the deployed `η = 4`. -/
theorem neg_rt_smul_s2Rt (i : Fin kk) : (-(rt • s2Rt)) i = etaElt := by
  show -(rt • -(rtInv * etaElt)) = etaElt
  rw [smul_eq_mul, mul_neg, neg_neg, ← mul_assoc, rt_mul_rtInv, one_mul]

/-- `−(c · t₀) = 2^{d−1}` — the gate value, at the deployed `2^{d−1} = 4096`. -/
theorem neg_rt_smul_t0Rt (i : Fin kk) : (-(rt • t0Rt)) i = t0Elt := by
  show -(rt • -(rtInv * t0Elt)) = t0Elt
  rw [smul_eq_mul, mul_neg, neg_neg, ← mul_assoc, rt_mul_rtInv, one_mul]

/-- The honest response `z = y + c·s₁ = y + η` on the unit mask: every coefficient is `≤ 5`, so the
DEPLOYED `‖z‖∞ < γ₁ − β = 524092` gate PASSES on genuine `R_q^ℓ` data. -/
theorem zGate_unitMask_s1 : zGate (unitMask + rt • s1Rt) = true := by
  unfold zGate
  rw [decide_eq_true_eq]
  intro i j
  left
  have hcoe : (unitMask + rt • s1Rt) i = unitMask i + etaElt := by
    show unitMask i + (rt • s1Rt) i = unitMask i + etaElt
    rw [rt_smul_s1Rt]
  rw [hcoe, rv_add, etaElt_rv]
  have hu : rv (unitMask i) j ≤ 1 := by
    unfold unitMask
    rcases eq_or_ne i 0 with hi | hi
    · subst hi; rw [Function.update_self]; exact rv_one_le j
    · rw [Function.update_of_ne hi]; simp only [Pi.zero_apply]; rw [rv_zero]; norm_num
  have hu0 : 0 ≤ rv (unitMask i) j := by
    unfold unitMask
    rcases eq_or_ne i 0 with hi | hi
    · subst hi; rw [Function.update_self]; exact rv_nonneg _ _
    · rw [Function.update_of_ne hi]; simp only [Pi.zero_apply]; rw [rv_zero]
  omega

/-- **A NON-DEGENERATE FULL-DIMENSION HONEST KEY.** Nonzero `s₁`, `s₂`, `t₀` over the real `R_q^ℓ`/`R_q^k`,
a NON-SCALAR challenge `c = root`, gate values at the DEPLOYED magnitudes (`‖c·s₂‖∞ = η = 4 ≤ β`,
`‖c·t₀‖∞ = 2^{d−1} = 4096 ≤ γ₂`), a gapped commitment `A·y = wVec`, and all four FIPS 204 Algorithm 7 gates
DISCHARGED — for ANY Fiat–Shamir hash. So `HonestKey` is inhabited at the real dimension with a real-shaped
secret and a real ring challenge: `fullDimApi_fips204` is NOT vacuous. -/
noncomputable def honestKey {Msg Cbar : Type*} (hash : Msg → Coeffs → Cbar) :
    HonestKey honestA hash (rtChal (Cbar := Cbar)) where
  s1 := s1Rt
  s2 := s2Rt
  t0 := t0Rt
  thi := thiRt
  mask := fun _ => unitMask
  power2round := by unfold thiRt; abel
  hint_small := by
    intro μ i j
    left
    rw [challengeAt_rt, neg_rt_smul_t0Rt, t0Elt_rv]
    norm_num
  cs2_small := by
    intro μ i j
    left
    rw [challengeAt_rt, neg_rt_smul_s2Rt, etaElt_rv]
    norm_num
  commit_gap := by
    intro μ
    show realRoundingK.lowGap (honestA unitMask)
    rw [honestA_unitMask]
    exact wVec_lowGap
  resp_bound := by
    intro μ
    rw [challengeAt_rt]
    exact zGate_unitMask_s1

/-- **THE FULL-DIMENSION HONEST ROUND-TRIP FIRES.** The real ML-DSA-65 verify ACCEPTS the real
ML-DSA-65 signature of the non-degenerate honest key, for EVERY message and EVERY context — over
`R_q^k`, with a nonzero secret and a non-scalar ring challenge. -/
theorem fullDim_honest_verifies {Msg Cbar Ctx : Type*} [DecidableEq Cbar]
    (hash : Msg → Coeffs → Cbar) (ctx : Ctx) (μ : Msg) :
    (fullDimApi (Ctx := Ctx) honestA hash (rtChal (Cbar := Cbar))).verify
      ((fullDimApi (Ctx := Ctx) honestA hash rtChal).keygen (honestKey hash)) ctx μ
      ((fullDimApi (Ctx := Ctx) honestA hash rtChal).sign (honestKey hash) ctx μ) = true :=
  fullDimApi_fips204 honestA hash rtChal (honestKey hash) ctx μ

/-! ## PART 5 — NON-VACUITY (reject side): the full-dimension verify is a REAL GATE.

`Fips204Correct` would be worthless if `verify` were `fun _ => true`. At full dimension the DEPLOYED
`‖z‖∞ < γ₁−β` gate REJECTS a response with an out-of-range coefficient — for EVERY `A`, hash, sampler,
public key, message, `c̃` and hint. So the accept side above is a real accept. -/

/-- An out-of-range ring element: every coefficient is `600000 ∈ [γ₁−β, q−(γ₁−β)]` — outside the DEPLOYED
response window on BOTH sides. -/
noncomputable def bigElt : Rq := mkElt (fun _ => (600000 : ZMod q))

theorem bigElt_rv (j : Fin pb.dim) : rv bigElt j = 600000 := by
  unfold rv bigElt
  rw [mkElt_coeff]
  have hv : (600000 : ZMod q).val = 600000 := ZMod.val_ofNat_of_lt (by rw [q_val]; norm_num)
  rw [hv]; norm_num

/-- The out-of-norm response `z ∈ R_q^ℓ`. -/
noncomputable def bigZ : M := fun _ => bigElt

/-- The DEPLOYED response gate REJECTS it — the `‖z‖∞` check is real, over all `6 × 256` coefficients. -/
theorem zGate_bigZ : zGate bigZ = false := by
  unfold zGate
  rw [decide_eq_false_iff_not]
  intro h
  have := h 0 ⟨0, dim_pos⟩
  rw [show bigZ 0 = bigElt from rfl, bigElt_rv] at this
  omega

/-- **THE FULL-DIMENSION VERIFY IS A REAL GATE (anti-vacuity).** For EVERY linear `A`, EVERY hash, EVERY
sampler, EVERY public key `thi`, EVERY message, EVERY `c̃` and EVERY hint, a signature whose response `z`
has an out-of-range coefficient is REJECTED. So the full-dimension `Fips204Correct` is a statement about a
verifier that genuinely discriminates. -/
theorem fullDim_rejects_out_of_norm {Msg Cbar : Type*} [DecidableEq Cbar] (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq) (thi : N) (μ : Msg) (cbar : Cbar) (h : Coeffs) :
    (fullParams A hash chal).verifyB thi μ (cbar, bigZ, h) = false := by
  show ((fullParams A hash chal).zBoundB bigZ &&
    decide ((fullParams A hash chal).hash μ
      ((fullParams A hash chal).round.useHint h
        ((fullParams A hash chal).A bigZ - chal cbar • thi)) = cbar)) = false
  rw [show (fullParams A hash chal).zBoundB bigZ = zGate bigZ from rfl, zGate_bigZ]
  simp

/-- **THE SECRET IS GENUINELY NONZERO** — `s₁ ≠ 0` over `R_q^ℓ`: if it were `0` then `c·s₁` would be `0`,
but `c·s₁ = η` has every coefficient `4`. So the honest key is NOT the degenerate `s = 0` witness for which
every norm gate is free. -/
theorem s1Rt_ne_zero : s1Rt ≠ 0 := by
  intro h
  have h0 : (rt • s1Rt) 0 = (0 : Rq) := by rw [h, smul_zero]; rfl
  have h4 : rv ((rt • s1Rt) 0) ⟨0, dim_pos⟩ = 4 := by rw [rt_smul_s1Rt]; exact etaElt_rv _
  rw [h0, rv_zero] at h4
  norm_num at h4

/-- **THE REJECTION GATE IS A REAL FILTER (`HonestKey` is not free).** The zero commitment is NOT
low-gapped (`rv 0 = 0 < β = 196`), so `commit_gap` genuinely REJECTS masks: the FIPS 204 rejection loop is
not a no-op, and `HonestKey` is not a constraint every tuple satisfies. This is the tooth that keeps the
accepted-iteration certificate honest — it carries real information. -/
theorem lowGap_zero_false : ¬ realRoundingK.lowGap (0 : N) := by
  intro h
  have h1 := (h 0 ⟨0, dim_pos⟩).1
  rw [show (0 : N) 0 = (0 : Rq) from rfl, rv_zero] at h1
  omega

/-- `t₀ ≠ 0` likewise — the secret low part is genuinely present (`c·t₀` has every coefficient `4096`). -/
theorem t0Rt_ne_zero : t0Rt ≠ 0 := by
  intro h
  have h0 : (-(rt • t0Rt)) 0 = (0 : Rq) := by rw [h, smul_zero, neg_zero]; rfl
  have h4 : rv ((-(rt • t0Rt)) 0) ⟨0, dim_pos⟩ = 4096 := by rw [neg_rt_smul_t0Rt]; exact t0Elt_rv _
  rw [h0, rv_zero] at h4
  norm_num at h4

/-! ## PART 6 — THE NEGACYCLIC SHIFT LEMMA and the τ·‖s‖∞ NORM BOUND: three `HonestKey` gates as THEOREMS.

This closes the FIRST of the two "NEXT LANE" items named below. `repr (root · x)` is the ±-shifted
coordinates of `repr x` (the coefficient-level form of the already-proved `root²⁵⁶ = −1`). From it,
multiplication by `root` is a signed coordinate permutation (`rt_preserves_absB`), a `τ`-sparse ±1
`SampleInBall` challenge gives the norm bound `‖c·s‖∞ ≤ τ·‖s‖∞` (`absB_challenge_mul`), and THREE of the four
`HonestKey` gates — `cs2_small`, `hint_small`, `resp_bound` — become THEOREMS from the secret's coefficient
norm (`honestKeyOfNorm`), collapsing the residual to `commit_gap` ALONE. All kernel-clean, no `native_decide`. -/

theorem pb_gen : pb.gen = rt := by
  unfold pb rt; rw [AdjoinRoot.powerBasis'_gen]

/-- `rt * basis i = basis (i+1)` when `i < 255`, else (`i = 255`) `= −1`. -/
theorem rt_mul_basis (i : Fin pb.dim) :
    rt * pb.basis i =
      if h : (i : ℕ) < 255 then pb.basis ⟨(i : ℕ) + 1, by have := realDim; omega⟩
      else -(1 : Rq) := by
  rw [pb.basis_eq_pow, ← pb_gen]
  by_cases h : (i : ℕ) < 255
  · rw [dif_pos h, pb.basis_eq_pow]
    show pb.gen * pb.gen ^ (i : ℕ) = pb.gen ^ ((i : ℕ) + 1)
    rw [← pow_succ']
  · rw [dif_neg h]
    have hi : (i : ℕ) = 255 := by have := i.isLt; have := realDim; omega
    show pb.gen * pb.gen ^ (i : ℕ) = -(1 : Rq)
    rw [← pow_succ', hi, pb_gen]; exact root_pow_256

/-- Expand `repr (rt * x) j` as the basis-linear sum. -/
theorem repr_rt_mul_apply (x : Rq) (j : Fin pb.dim) :
    pb.basis.repr (rt * x) j
      = ∑ i, pb.basis.repr x i * pb.basis.repr (rt * pb.basis i) j := by
  conv_lhs => rw [← pb.basis.sum_repr x]
  rw [Finset.mul_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- The closed form of `repr (rt * basis i) j`. -/
theorem repr_rt_basis (i j : Fin pb.dim) :
    pb.basis.repr (rt * pb.basis i) j =
      if (i : ℕ) < 255 then (if (i : ℕ) + 1 = (j : ℕ) then 1 else 0)
      else (if (j : ℕ) = 0 then -1 else 0) := by
  by_cases h : (i : ℕ) < 255
  · rw [if_pos h, rt_mul_basis i, dif_pos h, pb.basis.repr_self_apply]
    by_cases hij : (i : ℕ) + 1 = (j : ℕ)
    · rw [if_pos hij, if_pos (Fin.ext hij)]
    · rw [if_neg hij, if_neg (fun heq => hij (congrArg Fin.val heq))]
  · rw [if_neg h, rt_mul_basis i, dif_neg h, map_neg, Finsupp.neg_apply]
    have h1 : (1 : Rq) = pb.basis ⟨0, dim_pos⟩ := by rw [pb.basis_eq_pow]; simp
    rw [h1, pb.basis.repr_self_apply]
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj, if_pos (Fin.ext hj.symm)]
    · rw [if_neg hj, if_neg (fun heq => hj (congrArg Fin.val heq).symm)]; simp

/-- **THE NEGACYCLIC SHIFT LEMMA.** `repr (root · x) j = −repr x 255` at `j = 0`, else `repr x (j−1)` —
the coefficient-level form of `root²⁵⁶ = −1` (`Fips204CorrectReal.root_pow_256`). This is the named lever
of the first NEXT-LANE item. -/
theorem repr_rt_mul (x : Rq) (j : Fin pb.dim) :
    pb.basis.repr (rt * x) j =
      if (j : ℕ) = 0 then - pb.basis.repr x ⟨255, by have := realDim; omega⟩
      else pb.basis.repr x ⟨(j : ℕ) - 1, by have := j.isLt; have := realDim; omega⟩ := by
  rw [repr_rt_mul_apply]
  simp only [repr_rt_basis]
  by_cases hj : (j : ℕ) = 0
  · conv_rhs => rw [if_pos hj]
    rw [Finset.sum_eq_single (⟨255, by have := realDim; omega⟩ : Fin pb.dim)]
    · rw [if_neg (by show ¬ (255 : ℕ) < 255; omega), if_pos hj]; ring
    · intro i _ hi
      by_cases h : (i : ℕ) < 255
      · rw [if_pos h, if_neg (by omega)]; ring
      · exfalso; exact hi (Fin.ext (by show (i : ℕ) = 255; have := i.isLt; have := realDim; omega))
    · intro h; exact absurd (Finset.mem_univ _) h
  · conv_rhs => rw [if_neg hj]
    rw [Finset.sum_eq_single (⟨(j : ℕ) - 1, by have := j.isLt; have := realDim; omega⟩ : Fin pb.dim)]
    · have hlt : (j : ℕ) - 1 < 255 := by have := j.isLt; have := realDim; omega
      rw [if_pos hlt, if_pos (by show (j : ℕ) - 1 + 1 = (j : ℕ); omega)]; ring
    · intro i _ hi
      by_cases h : (i : ℕ) < 255
      · rw [if_pos h]
        by_cases he : (i : ℕ) + 1 = (j : ℕ)
        · exfalso; exact hi (Fin.ext (by show (i : ℕ) = (j : ℕ) - 1; omega))
        · rw [if_neg he]; ring
      · rw [if_neg h, if_neg hj]; ring
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The coefficient sup-norm and its behaviour under `root`-multiplication, negation, addition, sums. -/

/-- Coefficientwise sup-norm bound: every `ℤ_q` coordinate is within `±B` (centered). -/
def absB (x : Rq) (B : ℤ) : Prop := ∀ j, rv x j ≤ B ∨ 8380417 - B ≤ rv x j

theorem absB_mono {x : Rq} {A A' : ℤ} (hA : A ≤ A') (h : absB x A) : absB x A' := by
  intro j; rcases h j with hl | hr
  · left; omega
  · right; omega

theorem rv_neg (x : Rq) (j : Fin pb.dim) :
    rv (-x) j = if pb.basis.repr x j = 0 then 0 else 8380417 - rv x j := by
  have hq : q = 8380417 := rfl
  unfold rv
  rw [map_neg, Finsupp.neg_apply, ZMod.neg_val]
  by_cases h : pb.basis.repr x j = 0
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]
    have hlt : (pb.basis.repr x j).val < 8380417 := ZMod.val_lt _
    omega

theorem neg_preserves_absB {x : Rq} {B : ℤ} (h : absB x B) : absB (-x) B := by
  intro j
  rw [rv_neg]
  have hb0 := rv_nonneg x j; have hbq := rv_lt x j
  have hj := h j
  by_cases hz : pb.basis.repr x j = 0
  · rw [if_pos hz]
    have hrv0 : rv x j = 0 := by unfold rv; rw [hz]; simp
    rw [hrv0] at hj; omega
  · rw [if_neg hz]; omega

/-- `rv (rt * x) j` in closed form (from the shift lemma). -/
theorem rv_rt_mul (x : Rq) (j : Fin pb.dim) :
    rv (rt * x) j =
      if hj : (j : ℕ) = 0 then
        (if pb.basis.repr x ⟨255, by have := realDim; omega⟩ = 0 then 0
         else 8380417 - rv x ⟨255, by have := realDim; omega⟩)
      else rv x ⟨(j : ℕ) - 1, by have := j.isLt; have := realDim; omega⟩ := by
  have hq : q = 8380417 := rfl
  unfold rv
  rw [repr_rt_mul]
  by_cases hj : (j : ℕ) = 0
  · rw [if_pos hj, dif_pos hj, ZMod.neg_val]
    by_cases hz : pb.basis.repr x ⟨255, by have := realDim; omega⟩ = 0
    · rw [if_pos hz, if_pos hz]; simp
    · rw [if_neg hz, if_neg hz]
      have hlt : (pb.basis.repr x ⟨255, by have := realDim; omega⟩).val < 8380417 := ZMod.val_lt _
      omega
  · rw [if_neg hj, dif_neg hj]

/-- **Multiplication by `root` preserves the coefficient sup-norm** — the direct payoff of the shift lemma
(`root` acts as a signed coordinate permutation). -/
theorem rt_preserves_absB {x : Rq} {B : ℤ} (hB : 0 ≤ B) (h : absB x B) : absB (rt * x) B := by
  intro j
  rw [rv_rt_mul]
  by_cases hj : (j : ℕ) = 0
  · rw [dif_pos hj]
    have h255 := h ⟨255, by have := realDim; omega⟩
    have hb0 := rv_nonneg x ⟨255, by have := realDim; omega⟩
    by_cases hz : pb.basis.repr x ⟨255, by have := realDim; omega⟩ = 0
    · rw [if_pos hz]; left; omega
    · rw [if_neg hz]; omega
  · rw [dif_neg hj]; exact h ⟨(j : ℕ) - 1, by have := j.isLt; have := realDim; omega⟩

theorem rt_pow_preserves_absB (p : ℕ) {x : Rq} {B : ℤ} (hB : 0 ≤ B) (h : absB x B) :
    absB (rt ^ p * x) B := by
  induction p with
  | zero => simpa using h
  | succ k ih =>
    have hstep : rt ^ (k + 1) * x = rt * (rt ^ k * x) := by ring
    rw [hstep]; exact rt_preserves_absB hB ih

theorem absB_add {x y : Rq} {A C : ℤ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hAC : A + C ≤ 4190208)
    (hx : absB x A) (hy : absB y C) : absB (x + y) (A + C) := by
  intro j
  have hxj := hx j; have hyj := hy j
  have hbx0 := rv_nonneg x j; have hbxq := rv_lt x j
  have hby0 := rv_nonneg y j; have hbyq := rv_lt y j
  rw [rv_add]; omega

theorem absB_zero : absB (0 : Rq) 0 := by
  intro j; left; rw [rv_zero]

/-- Sum bound: `‖∑ f p‖∞ ≤ |T|·B` when each `‖f p‖∞ ≤ B` (provided `|T|·B < q/2`). -/
theorem absB_sum {α : Type*} [DecidableEq α] (T : Finset α) (f : α → Rq) (B : ℤ) (hB : 0 ≤ B) :
    (T.card : ℤ) * B ≤ 4190208 → (∀ p ∈ T, absB (f p) B) →
    absB (∑ p ∈ T, f p) ((T.card : ℤ) * B) := by
  refine Finset.induction_on T ?_ ?_
  · intro _ _; simpa using absB_zero
  · intro a S ha ih hbound hf
    rw [Finset.card_insert_of_notMem ha] at hbound
    have hbound' : B + (S.card : ℤ) * B ≤ 4190208 := by push_cast at hbound; nlinarith [hbound]
    have hcardS : (S.card : ℤ) * B ≤ 4190208 := by nlinarith [hB, Int.natCast_nonneg S.card]
    have hIH : absB (∑ p ∈ S, f p) ((S.card : ℤ) * B) :=
      ih hcardS (fun p hp => hf p (Finset.mem_insert_of_mem hp))
    have hfa : absB (f a) B := hf a (Finset.mem_insert_self a S)
    have hres : absB (f a + ∑ p ∈ S, f p) (B + (S.card : ℤ) * B) :=
      absB_add hB (by positivity) hbound' hfa hIH
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hgoal : ((S.card + 1 : ℕ) : ℤ) * B = B + (S.card : ℤ) * B := by push_cast; ring
    rw [hgoal]; exact hres

/-! ### Sparse-sign (`SampleInBall`) challenges and the `τ·‖s‖∞` bound. -/

/-- A `SampleInBall` challenge: `τ` nonzero coefficients, each `±1` (a signed sum of `τ` monomials). -/
def IsSparseSign (c : Rq) (τ : ℕ) : Prop :=
  ∃ (T : Finset (Fin pb.dim)) (ε : Fin pb.dim → Rq),
    T.card = τ ∧ (∀ p ∈ T, ε p = 1 ∨ ε p = -1) ∧ c = ∑ p ∈ T, ε p * rt ^ (p : ℕ)

/-- **THE CHALLENGE NORM BOUND** `‖c·s‖∞ ≤ τ·‖s‖∞` for a `τ`-sparse ±1 challenge `c` (`SampleInBall`).
Each of the `τ` signed monomials `ε·root^p` permutes-with-sign the coordinates of `s` (`rt_pow_preserves_absB`
+ `neg_preserves_absB`); the triangle inequality over the `τ` terms is `absB_sum`. -/
theorem absB_challenge_mul {c : Rq} {τ : ℕ} {s : Rq} {B : ℤ} (hB : 0 ≤ B)
    (hbound : (τ : ℤ) * B ≤ 4190208) (hc : IsSparseSign c τ) (hs : absB s B) :
    absB (c * s) ((τ : ℤ) * B) := by
  obtain ⟨T, ε, hcard, hε, hceq⟩ := hc
  subst hceq
  rw [Finset.sum_mul]
  have hterm : ∀ p ∈ T, absB (ε p * rt ^ (p : ℕ) * s) B := by
    intro p hp
    have hpre : absB (rt ^ (p : ℕ) * s) B := rt_pow_preserves_absB _ hB hs
    rcases hε p hp with h1 | h1
    · rw [h1, one_mul]; exact hpre
    · rw [h1]
      have hneg : (-1 : Rq) * rt ^ (p : ℕ) * s = -(rt ^ (p : ℕ) * s) := by ring
      rw [hneg]; exact neg_preserves_absB hpre
  have hsum := absB_sum T (fun p => ε p * rt ^ (p : ℕ) * s) B hB (by rw [hcard]; exact hbound) hterm
  rw [hcard] at hsum
  exact hsum

/-! ### The three `HonestKey` gates as THEOREMS from the secret's coefficient norm. -/

/-- Gate `cs2_small` (`‖c·s₂‖∞ ≤ β = 196`) as a THEOREM, from `‖s₂‖∞ ≤ η = 4` and a `τ = 49`-sparse ±1
challenge (`49·4 = 196 = β`). -/
theorem betaSmall_of_norm {c : Rq} {s2 : N}
    (hc : IsSparseSign c 49) (hs : ∀ i, absB (s2 i) 4) :
    realRoundingK.betaSmall (-(c • s2)) := by
  intro i j
  have h1 : absB (c * s2 i) 196 := by
    have h := absB_challenge_mul (τ := 49) (by norm_num) (by norm_num) hc (hs i)
    have hval : ((49 : ℕ) : ℤ) * 4 = 196 := by norm_num
    rwa [hval] at h
  have hkey := (neg_preserves_absB h1) j
  simpa only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using hkey

/-- Gate `hint_small` (`‖c·t₀‖∞ ≤ γ₂`) as a THEOREM, from `‖t₀‖∞ ≤ 2^{d−1} = 4096` and a `τ = 49`-sparse ±1
challenge (`49·4096 = 200704 ≤ γ₂ = 261888`). -/
theorem nearGamma2_of_norm {c : Rq} {t0 : N}
    (hc : IsSparseSign c 49) (hs : ∀ i, absB (t0 i) 4096) :
    realRoundingK.nearGamma2 (-(c • t0)) := by
  intro i j
  have h1 : absB (c * t0 i) 200704 := by
    have h := absB_challenge_mul (τ := 49) (by norm_num) (by norm_num) hc (hs i)
    have hval : ((49 : ℕ) : ℤ) * 4096 = 200704 := by norm_num
    rwa [hval] at h
  have h2 : absB (c * t0 i) 261888 := absB_mono (by norm_num) h1
  have hkey := (neg_preserves_absB h2) j
  simpa only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using hkey

/-- Gate `resp_bound` (`zGate (y + c·s₁)`, i.e. `‖z‖∞ < γ₁ − β = 524092`) as a THEOREM, from a mask with
`‖y‖∞ ≤ 523895`, `‖s₁‖∞ ≤ η = 4` and a `τ = 49`-sparse ±1 challenge: `‖z‖∞ ≤ 523895 + 49·4 = 524091 < 524092`. -/
theorem respGate_of_norm {y : M} {c : Rq} {s1 : M}
    (hy : ∀ i, absB (y i) 523895) (hc : IsSparseSign c 49) (hs1 : ∀ i, absB (s1 i) 4) :
    zGate (y + c • s1) = true := by
  unfold zGate
  rw [decide_eq_true_eq]
  intro i j
  have hcs1 : absB (c * s1 i) 196 := by
    have h := absB_challenge_mul (τ := 49) (by norm_num) (by norm_num) hc (hs1 i)
    have hval : ((49 : ℕ) : ℤ) * 4 = 196 := by norm_num
    rwa [hval] at h
  have hsum : absB (y i + c * s1 i) (523895 + 196) :=
    absB_add (by norm_num) (by norm_num) (by norm_num) (hy i) hcs1
  have hkey := hsum j
  have hcomp : (y + c • s1) i = y i + c * s1 i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcomp]; omega

/-! ### `honestKeyOfNorm` — build a `HonestKey` from norm hypotheses: three gates DISCHARGED, `commit_gap`
the sole remaining input. -/

/-- **THE NORM-BASED HONEST KEY.** Given a secret `(s₁, s₂, t₀)` with `‖s₁‖∞, ‖s₂‖∞ ≤ η = 4`,
`‖t₀‖∞ ≤ 2^{d−1} = 4096`, a per-message mask with `‖y‖∞ ≤ 523895`, a `SampleInBall` sampler (every output
`τ = 49`-sparse ±1), and Power2Round consistency, the gates `hint_small`, `cs2_small`, `resp_bound` are
THEOREMS (`nearGamma2_of_norm` / `betaSmall_of_norm` / `respGate_of_norm`). The ONLY residual field is
`commit_gap` — the single genuinely-resampled FIPS 204 Algorithm 7 condition. -/
noncomputable def honestKeyOfNorm {Msg Cbar : Type*} (A : M →ₗ[Rq] N)
    (hash : Msg → Coeffs → Cbar) (chal : Cbar → Rq)
    (hchal : ∀ cb : Cbar, IsSparseSign (chal cb) 49)
    (s1 : M) (s2 t0 thi : N) (mask : Msg → M)
    (hp2 : A s1 + s2 = thi + t0)
    (hs1 : ∀ i, absB (s1 i) 4) (hs2 : ∀ i, absB (s2 i) 4) (ht0 : ∀ i, absB (t0 i) 4096)
    (hy : ∀ (μ : Msg) i, absB (mask μ i) 523895)
    (hgap : ∀ μ : Msg, realRoundingK.lowGap (A (mask μ))) :
    HonestKey A hash chal where
  s1 := s1
  s2 := s2
  t0 := t0
  thi := thi
  mask := mask
  power2round := hp2
  hint_small := fun _ => nearGamma2_of_norm (hchal _) ht0
  cs2_small := fun _ => betaSmall_of_norm (hchal _) hs2
  commit_gap := hgap
  resp_bound := fun μ => respGate_of_norm (hy μ) (hchal _) hs1

/-! ### Non-vacuity of the sparse-challenge path (the gate lemmas are not vacuous). -/

/-- The inclusion `Fin 49 ↪ Fin 256` (the first 49 power-basis indices). -/
def emb49 : Fin 49 ↪ Fin pb.dim :=
  ⟨fun i => ⟨i.val, by have := i.isLt; have := realDim; omega⟩,
   fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- A concrete `τ = 49` support: the first 49 power-basis indices. -/
def T49 : Finset (Fin pb.dim) := Finset.univ.map emb49

theorem T49_card : T49.card = 49 := by
  rw [T49, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- **THE `τ = 49`-SPARSE CHALLENGE PREDICATE IS INHABITED** — `∑_{p<49} root^p` is a genuine `SampleInBall`
shape (49 nonzero ±1 coefficients). So `betaSmall_of_norm` / `nearGamma2_of_norm` / `respGate_of_norm` are NOT
vacuous: a challenge satisfying their `IsSparseSign … 49` hypothesis exists. -/
theorem sparseSign_inhabited : ∃ c : Rq, IsSparseSign c 49 :=
  ⟨∑ p ∈ T49, (1 : Rq) * rt ^ (p : ℕ), T49, fun _ => 1, T49_card, fun _ _ => Or.inl rfl, rfl⟩

#assert_axioms fullParams
#assert_axioms fullDimApi
#assert_axioms fullDimApi_fips204
#assert_axioms fullDimApi_correct
#assert_axioms fips204Correct_of_fullDim
#assert_axioms rt_mul_rtInv
#assert_axioms rt_not_scalar
#assert_axioms honestKey
#assert_axioms fullDim_honest_verifies
#assert_axioms zGate_bigZ
#assert_axioms fullDim_rejects_out_of_norm
#assert_axioms lowGap_zero_false
#assert_axioms s1Rt_ne_zero
#assert_axioms t0Rt_ne_zero
#assert_axioms repr_rt_mul
#assert_axioms rt_preserves_absB
#assert_axioms absB_challenge_mul
#assert_axioms betaSmall_of_norm
#assert_axioms nearGamma2_of_norm
#assert_axioms respGate_of_norm
#assert_axioms honestKeyOfNorm
#assert_axioms sparseSign_inhabited

/-! ## NEXT LANE (named precisely, not hand-waved)

1. **The negacyclic SHIFT lemma — DONE (PART 6).** `repr_rt_mul` proves `repr (root · x) j = if j = 0 then
   −repr x 255 else repr x (j−1)` over `pb` (the coefficient-level form of `root²⁵⁶ = −1`), kernel-clean.
   From it: `rt_preserves_absB` (root-multiplication is a signed coordinate permutation), the τ-sparse
   `SampleInBall` norm bound `absB_challenge_mul` (`‖c·s‖∞ ≤ τ·‖s‖∞`), and THREE of the four `HonestKey`
   gates as THEOREMS from the secret's coefficient norm — `betaSmall_of_norm` (`‖c·s₂‖∞ ≤ β = 196`,
   τ = 49, η = 4), `nearGamma2_of_norm` (`‖c·t₀‖∞ ≤ 200704 ≤ γ₂`), `respGate_of_norm` (`‖z‖∞ ≤ 524091 <
   γ₁−β`). `honestKeyOfNorm` bundles them: given a norm-bounded secret + a `SampleInBall` sampler + a
   per-message mask + Power2Round, the ONLY remaining `HonestKey` field is `commit_gap` — the single
   genuinely-resampled FIPS 204 Algorithm 7 condition. `sparseSign_inhabited` witnesses the τ = 49 predicate,
   so the gate lemmas are non-vacuous. (The τ = 1 monomial `honestKey` inhabitant in PART 4 remains for the
   `∀`-sampler non-vacuity of `fullDimApi_fips204`.)

2. **The `Poly ↔ R_q` coefficient bridge** — `MlDsaRing.Poly` (an `Array Nat`, what `NttFaithful`'s
   now-∀ `ntt_computes_negacyclic_mul` / `ntt_intt_id` talk about) vs `pb.basis.repr` (what `rv`, and hence
   `realRoundingK`, reads). With that bridge, `fips204Correct_of_fullDim` takes the byte-level
   `MlDsaSignReal.signCore` / `MlDsaVerifyReal.verifyCore` to a full-dimension `Fips204Correct` — and the
   `native_decide` KAT (`verify_accepts_real`) reverts to what it should be: a cross-check against the
   crate, not a load-bearing step. -/

end Dregg2.Crypto.Fips204FullDim
