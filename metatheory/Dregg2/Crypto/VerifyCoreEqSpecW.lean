/-
# `Dregg2.Crypto.VerifyCoreEqSpecW` — `WOneRecoversSpec`, the `toRq`-INVERSE coordinate bridge.

`VerifyCoreEqSpec` closed the FORWARD algebra of the ML-DSA-65 verify: `toRq_intt_matmul_row` proves that
verifyCore's per-row NTT value `w_i = intt(Σ_j Â_ij⊙ẑ_j − ĉ⊙ŝ_i)` maps under `toRq` to the FIPS 204 spec's
`R_q`-matrix–vector value `(A·z − c·s)_i`. What that leaves is the OTHER direction — reading a `R_q` element
back to its `Fin 256 → ℤ_q` coordinates, so that verifyCore's per-COEFFICIENT `useHint(h_i, w_i[jj])` loop
(over the coefficient array `w_i`) is identified with the abstract `round.useHint` applied to the coordinates
of the `R_q` value. THIS module closes that coordinate inverse:

* **`pbW`** — the `ℤ_q`-power basis of `Rq = ℤ_q[X]/(X²⁵⁶+1)`, built here over `MlDsaRing.q` (the same `q` as
  `toRq`/`r`), so its coordinate reader `pbW.basis.repr` lines up syntactically with `toRq`'s coefficient sum.
  `pbW.dim = 256` (`pbW_dim`), a genuine degree-256 extension.
* **`toRq_coeff` — THE COORDINATE INVERSE.** `pbW.basis.repr (toRq a) j = a_j` (the `ℤ_q` reduction of the
  `j`-th executable coefficient) for every power-basis index `j`. This is the `PowerBasis.repr` of the
  canonical coefficient-sum `toRq a = ∑ᵢ aᵢ·rootⁱ`: `repr` and `toRq` are mutually inverse on coordinates.
  Proved from `PowerBasis.basis_eq_pow` + `Basis.repr_self` — the crux of the coordinate bridge.
* **`wOne_coord` / `wOne_recovers` — `WOneRecoversSpec`, coordinate form.** Composing `toRq_coeff` (backwards)
  with `toRq_intt_matmul_row` (the forward ring value), verifyCore's per-row coefficient array `w_i`, read at
  coordinate `jj`, IS the `jj`-th power-basis coordinate of the abstract `R_q` matvec `(A·z − c·s)_i` — and
  its canonical `ℤ_q` rep `w_i[jj]` is exactly the `Nat` that the executable `useHint(h_i[jj], ·)` consumes.
  So verifyCore's per-coefficient `UseHint` loop applies the FIPS rounding to precisely the coordinates of the
  abstract `R_q` recovery argument `A·z − c·t1·2^d` — the `WOneRecoversSpec` bridge, at the executable types.

## HONEST FRONTIER (named, not laundered)

`wOne_*` are stated over `wRow terms c s := intt(subPoly (Σ_j pointwiseMul (ntt A_ij) (ntt z_j))
(pointwiseMul (ntt c) (ntt s)))`, i.e. verifyCore's per-row value with the matrix entry `Â_ij` written as
`ntt A_ij` for a ring preimage `A_ij`. The executable stores `Â := expandA ρ` DIRECTLY in the NTT domain, so
`A_ij = intt Â_ij` and `ntt A_ij = Â_ij` needs the NTT right-inverse `ntt ∘ intt = id` (`ExpandAIsMatrix`) —
a real NTT-correctness fact, CLOSED for-all (`MlDsaRing.nttRightInverse_proven`; the left inverse is the
∀-gate `ntt_intt_id` in `NttFaithful` — axiom-clean, no `native_decide`), NOT a hardness carrier. The final `challengeMatches =
verifyB.hash` identification additionally wraps `w1Encode(w1')` under SHAKE-256 — a legitimate INSTANTIATION
of `verifyB`'s generic `hash` field (its collision-resistance lives on the `HashSig`/`FoQrom` floor), not a
soundness gap. Both are named precisely; the coordinate math — the `WOneRecoversSpec` core — is CLOSED here.
-/
import Dregg2.Crypto.VerifyCoreEqSpec

namespace Dregg2.Crypto.VerifyCoreEqSpec

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly subPoly
  subPoly_size subPoly_lt intt_lt)
open Polynomial Finset

set_option maxRecDepth 8000

local notation "F" => (X ^ 256 + 1 : (ZMod q)[X])

/-! ## PART 1 — the `ℤ_q`-power basis of `Rq`, over `MlDsaRing.q`. -/

/-- `F = X²⁵⁶+1` is monic over `ℤ_q`. -/
theorem F_monic : Monic F := by
  apply Monic.add_of_left (monic_X_pow 256)
  rw [degree_X_pow, degree_one]; norm_num

/-- `F` has degree exactly `256` (the quotient degree). -/
theorem F_natDeg : natDegree F = 256 := by compute_degree!

/-- The `ℤ_q`-power basis of `Rq = ℤ_q[X]/(X²⁵⁶+1)` (`1, root, …, root²⁵⁵`), over `MlDsaRing.q` — the SAME `q`
as `toRq`/`r`, so its coordinate reader lines up with `toRq`'s coefficient sum. -/
noncomputable def pbW : PowerBasis (ZMod q) Rq := AdjoinRoot.powerBasis' F_monic

/-- **NON-VACUITY (dimension):** `pbW.dim = 256` — a genuine degree-256 extension, not a scalar. -/
theorem pbW_dim : pbW.dim = 256 := by
  unfold pbW; rw [AdjoinRoot.powerBasis'_dim]; exact F_natDeg

/-- The power-basis generator IS `r = AdjoinRoot.root F`. -/
theorem pbW_gen : pbW.gen = r := by unfold pbW; rw [AdjoinRoot.powerBasis'_gen]

/-- The `i`-th basis vector is `rootⁱ`. -/
theorem pbW_basis_eq (i : Fin pbW.dim) : pbW.basis i = r ^ (i : ℕ) := by
  rw [pbW.basis_eq_pow, pbW_gen]

/-! ## PART 2 — `toRq_coeff`, THE COORDINATE INVERSE. -/

/-- `of F c · x = c • x` (the algebra-map scalar action). -/
theorem of_mul_eq_smul (c : ZMod q) (x : Rq) : (AdjoinRoot.of F c : Rq) * x = c • x := by
  rw [Algebra.smul_def]; rfl

/-- Each `toRq` summand `of F aᵢ · rootⁱ`, read at coordinate `j`, is `aᵢ · [i = j]` (a Kronecker delta):
`of F aᵢ · rootⁱ = aᵢ • basisᵢ`, and `repr (basisᵢ) = single i 1`. -/
theorem toRq_repr_term (a : Poly) (i : ℕ) (hi : i < pbW.dim) (j : Fin pbW.dim) :
    pbW.basis.repr ((AdjoinRoot.of F (cf (a[i]!)) : Rq) * r ^ i) j
      = cf (a[i]!) * (if (⟨i, hi⟩ : Fin pbW.dim) = j then 1 else 0) := by
  rw [of_mul_eq_smul, show r ^ i = pbW.basis ⟨i, hi⟩ from (pbW_basis_eq ⟨i, hi⟩).symm,
      map_smul, Finsupp.smul_apply, pbW.basis.repr_self_apply, smul_eq_mul]

/-- **THE COORDINATE INVERSE.** `pbW.basis.repr (toRq a) j = a_j` (the `ℤ_q` reduction of the `j`-th
executable coefficient) for every power-basis index `j`. `toRq` and `PowerBasis.repr` are mutually inverse on
coordinates: `repr (∑ᵢ aᵢ·rootⁱ) j = a_j`. This is the `toRq`-inverse the `WOneRecoversSpec` coordinate bridge
rests on — turning a `R_q` ring value back into its `Fin 256 → ℤ_q` coefficients. -/
theorem toRq_coeff (a : Poly) (j : Fin pbW.dim) :
    pbW.basis.repr (toRq a) j = cf (a[(j : ℕ)]!) := by
  have hj256 : (j : ℕ) < 256 := by have h := j.isLt; have := pbW_dim; omega
  unfold toRq
  rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single (j : ℕ)]
  · rw [toRq_repr_term a (j : ℕ) (by have := pbW_dim; omega) j, if_pos (Fin.eta j _), mul_one]
  · intro i hi hij
    rw [toRq_repr_term a i (by have := pbW_dim; have := Finset.mem_range.mp hi; omega) j,
        if_neg (fun h => hij (by rw [← h])), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hj256) h

#assert_axioms toRq_coeff

/-! ## PART 3 — `WOneRecoversSpec`: verifyCore's per-coefficient `w_i` IS the coordinate reading of `A·z−c·s`. -/

/-- The abstract `R_q` matrix–vector value `(A·z − c·s)_i` (the `verifyB` hash argument, pre-rounding). -/
noncomputable def rqMatvec (terms : List (Poly × Poly)) (c s : Poly) : Rq :=
  (terms.map (fun t => toRq t.1 * toRq t.2)).sum - toRq c * toRq s

/-- verifyCore's per-row value `w_i = intt(Σ_j Â_ij⊙ẑ_j − ĉ⊙ŝ_i)`, with `Â_ij` written as `ntt A_ij` (the
ExpandA-as-matrix identification — see the honest frontier). -/
noncomputable def wRow (terms : List (Poly × Poly)) (c s : Poly) : Poly :=
  intt (subPoly
    (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms)
    (pointwiseMul (ntt c) (ntt s)))

/-- `toRq (wRow …) = rqMatvec …` — verifyCore's per-row NTT value IS the abstract `R_q` matvec (this is
`toRq_intt_matmul_row`, unfolded through `wRow`/`rqMatvec`). -/
theorem wRow_toRq (terms : List (Poly × Poly)) (c s : Poly)
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256) :
    toRq (wRow terms c s) = rqMatvec terms c s :=
  toRq_intt_matmul_row terms c s hterm hc hs

/-- The per-row value stays reduced (`< q`), so its coefficients are canonical `ℤ_q` reps. -/
theorem wRow_lt (terms : List (Poly × Poly)) (c s : Poly) (p : Nat) : (wRow terms c s)[p]! < q :=
  intt_lt _ (subPoly_size _ _) (subPoly_lt _ _) p

/-- **`WOneRecoversSpec` (coordinate identity).** verifyCore's per-row coefficient array `w_i`, read at
coordinate `jj`, equals the `jj`-th power-basis coordinate of the abstract `R_q` matvec `(A·z − c·s)_i`.
`toRq_coeff` (backwards) turns the coefficient into a coordinate; `toRq_intt_matmul_row` supplies the ring
value. This is the exact bridge from verifyCore's per-coefficient `w1` array to the spec's `R_q` recovery
argument. -/
theorem wOne_coord (terms : List (Poly × Poly)) (c s : Poly)
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256)
    (jj : Fin pbW.dim) :
    cf ((wRow terms c s)[(jj : ℕ)]!) = pbW.basis.repr (rqMatvec terms c s) jj := by
  rw [← wRow_toRq terms c s hterm hc hs]; exact (toRq_coeff _ jj).symm

/-- **`WOneRecoversSpec` (executable-argument form).** The canonical `ℤ_q` rep `w_i[jj]` that verifyCore's
per-coefficient `useHint(h_i[jj], ·)` loop consumes IS the canonical rep of the `jj`-th coordinate of the
abstract `R_q` matvec `(A·z − c·s)_i`. So the executable per-coefficient `UseHint` applies the FIPS rounding
to EXACTLY the coordinates of the spec's `R_q` recovery argument `A·z − c·t1·2^d`. -/
theorem wOne_recovers (terms : List (Poly × Poly)) (c s : Poly)
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256)
    (jj : Fin pbW.dim) :
    (wRow terms c s)[(jj : ℕ)]! = (pbW.basis.repr (rqMatvec terms c s) jj).val := by
  have hcoord : cf ((wRow terms c s)[(jj : ℕ)]!) = pbW.basis.repr (rqMatvec terms c s) jj :=
    wOne_coord terms c s hterm hc hs jj
  have hval := congrArg ZMod.val hcoord
  rwa [show cf ((wRow terms c s)[(jj : ℕ)]!) = (((wRow terms c s)[(jj : ℕ)]! : ℕ) : ZMod q) from rfl,
      ZMod.val_natCast_of_lt (wRow_lt terms c s _)] at hval

#assert_axioms rqMatvec
#assert_axioms wOne_coord
#assert_axioms wOne_recovers

/-! ## PART 3b — `ExpandAIsMatrix` DISCHARGED: the executable's stored NTT-domain `Â` IS `ntt A`.

The `wRow`/`wOne_*` theorems above write the per-row matrix entry as `ntt A_ij` for a ring preimage `A_ij`.
The executable stores `Â := expandA ρ` DIRECTLY in the NTT domain. Its normal-domain preimage is `A_ij :=
intt Â_ij`, and recovering the stored entry is `ntt A_ij = ntt (intt Â_ij) = Â_ij` — the NTT RIGHT-inverse,
now CLOSED for-all at the operational guards (`MlDsaRing.nttRightInverse_proven`, size-256 + reduced, no
`native_decide` in the `∀`). Every `expandA` entry meets those guards: `expandA_shape` (each poly is exactly
256 coeffs) and `rejNTTPoly_coeffs_in_range` (every coeff `< q`). So the identification is exact, not a gap.
Below, `wRowHat` is verifyCore's ACTUAL per-row value — it multiplies the STORED `Â_ij` in directly — and
`wOne_recovers_hat` transfers `wOne_recovers` to it unconditionally, closing the last Seam-1 verify non-gap. -/

/-- **`ExpandAIsMatrix`.** For a stored NTT-domain matrix entry `aHat` meeting the operational guards
(canonical size-256, coeffs `< q` — exactly what `expandA`/`rejNTTPoly` produce), its normal-domain preimage
`intt aHat` transforms back to it: `ntt (intt aHat) = aHat`. Direct instance of the NTT right-inverse. -/
theorem expandA_is_matrix (aHat : Poly) (hsz : aHat.size = 256) (hlt : ∀ (p : Nat), aHat[p]! < q) :
    ntt (intt aHat) = aHat :=
  MlDsaRing.nttRightInverse_proven aHat hsz hlt

/-- Fold-congruence over the row terms: replacing each stored entry `t.1 = Â_ij` by `ntt (intt t.1)` leaves the
per-row accumulator unchanged, since `ntt (intt Â_ij) = Â_ij` on the canonical guards. The bridge between the
executable's stored-`Â` fold (`wRowHat`) and `wRow`'s `ntt (preimage)` fold. -/
theorem foldl_pointwise_expandA :
    ∀ (terms : List (Poly × Poly)) (z : Poly),
      (∀ t ∈ terms, t.1.size = 256 ∧ (∀ (p : Nat), t.1[p]! < q)) →
      List.foldl (fun az t => addPoly az (pointwiseMul t.1 (ntt t.2))) z terms
        = List.foldl (fun az t => addPoly az (pointwiseMul (ntt (intt t.1)) (ntt t.2))) z terms := by
  intro terms
  induction terms with
  | nil => intro z _; rfl
  | cons hd tl ih =>
    intro z hmem
    simp only [List.foldl_cons]
    rw [expandA_is_matrix hd.1 (hmem hd (by simp)).1 (hmem hd (by simp)).2]
    exact ih _ (fun t ht => hmem t (by simp [ht]))

/-- verifyCore's ACTUAL per-row value: the STORED NTT-domain matrix entries `Â_ij = t.1` are multiplied in
directly (no `ntt` applied), against `ẑ_j = ntt t.2` and `ĉ⊙ŝ`. This is the deployed executable's `w_i`. -/
noncomputable def wRowHat (terms : List (Poly × Poly)) (c s : Poly) : Poly :=
  intt (subPoly
    (List.foldl (fun az t => addPoly az (pointwiseMul t.1 (ntt t.2))) zeroPoly terms)
    (pointwiseMul (ntt c) (ntt s)))

/-- The executable's stored-`Â` per-row value IS `wRow` with the normal-domain preimages `A_ij := intt Â_ij` —
by `ExpandAIsMatrix` (`ntt (intt Â_ij) = Â_ij`) under the fold. -/
theorem wRowHat_eq_wRow (terms : List (Poly × Poly)) (c s : Poly)
    (hAhat : ∀ t ∈ terms, t.1.size = 256 ∧ (∀ (p : Nat), t.1[p]! < q)) :
    wRowHat terms c s = wRow (terms.map (fun t => (intt t.1, t.2))) c s := by
  unfold wRowHat wRow
  rw [List.foldl_map]
  congr 2
  exact foldl_pointwise_expandA terms zeroPoly hAhat

/-- `terms.map (fun t => (intt t.1, t.2))` inherits the size-256 hypotheses (`intt` preserves size; the
second component is unchanged) — the honest-key `hterm` shared by the two theorems below. -/
theorem hatTerms_hterm (terms : List (Poly × Poly))
    (hAhat : ∀ t ∈ terms, t.1.size = 256 ∧ (∀ (p : Nat), t.1[p]! < q))
    (hz : ∀ t ∈ terms, t.2.size = 256) :
    ∀ t ∈ terms.map (fun t => (intt t.1, t.2)), t.1.size = 256 ∧ t.2.size = 256 := by
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨t0, ht0, rfl⟩ := ht
  exact ⟨MlDsaRing.intt_size t0.1 (hAhat t0 ht0).1 (hAhat t0 ht0).2, hz t0 ht0⟩

/-- The stored-`Â` per-row value stays reduced (`< q`) — the same `intt`-range fact as `wRow_lt`. -/
theorem wRowHat_lt (terms : List (Poly × Poly)) (c s : Poly) (p : Nat) : (wRowHat terms c s)[p]! < q :=
  intt_lt _ (subPoly_size _ _) (subPoly_lt _ _) p

/-- **`WOneRecoversSpec` for the HONEST KEY — unconditional.** verifyCore's per-row coefficient array `w_i`
built from the STORED NTT-domain matrix `Â` (`wRowHat`), read at coordinate `jj`, IS the canonical `ℤ_q` rep
of the `jj`-th power-basis coordinate of the abstract `R_q` matvec `(A·z − c·s)_i` with `A_ij := intt Â_ij`.
No `ntt A_ij = Â_ij` residual remains — it is discharged by `ExpandAIsMatrix`. The last Seam-1 verify non-gap
is closed: the executable applies the FIPS rounding to exactly the coordinates of the spec's recovery argument.

Proof = `wOne_recovers` applied to the ExpandA preimage list `A_ij := intt Â_ij`, after `wRowHat_eq_wRow`
(`ExpandAIsMatrix`) identifies `wRowHat` with `wRow` on those preimages. The `generalize` is load-bearing:
`wOne_recovers`/`wRow_toRq`/etc. elaborate fine over a bare list VARIABLE, but instantiating them at the
concrete `terms.map (fun t => (intt t.1, t.2))` makes the elaborator whnf `toRq`/`AdjoinRoot` reductions over
that closed expression and hit the heartbeat wall. Abstracting it to a fresh `M` first keeps it opaque. -/
theorem wOne_recovers_hat (terms : List (Poly × Poly)) (c s : Poly)
    (hAhat : ∀ t ∈ terms, t.1.size = 256 ∧ (∀ (p : Nat), t.1[p]! < q))
    (hz : ∀ t ∈ terms, t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256)
    (jj : Fin pbW.dim) :
    (wRowHat terms c s)[(jj : ℕ)]!
      = (pbW.basis.repr (rqMatvec (terms.map (fun t => (intt t.1, t.2))) c s) jj).val := by
  have hterm := hatTerms_hterm terms hAhat hz
  have hEq := wRowHat_eq_wRow terms c s hAhat
  generalize hM : terms.map (fun t => (intt t.1, t.2)) = M at hterm hEq ⊢
  rw [hEq]
  exact wOne_recovers M c s hterm hc hs jj

#assert_axioms expandA_is_matrix
#assert_axioms wRowHat_eq_wRow
#assert_axioms wOne_recovers_hat

/-! ## PART 4 — NON-VACUITY: the coordinate reader is a GENUINE degree-256 iso, not a scalar collapse.

`toRq_coeff`/`wOne_*` are statements over the coordinate space `Fin pbW.dim → ℤ_q` with `pbW.dim = 256`; if
the ring were a scalar (`dim = 1`) the bridge would be vacuous. It is NOT — `pbW.dim = 256` (`pbW_dim`), and
the reader separates coordinates: two coefficient arrays that differ at index `j` have different `toRq`. -/

/-- The coordinate reader separates coefficients: if `toRq a = toRq b` then every coordinate agrees
(`a_j = b_j` in `ℤ_q`) — `toRq` is injective on coordinates, so the bridge lands in a genuine `256`-dim space,
not a collapse. -/
theorem toRq_coeff_separates (a b : Poly) (h : toRq a = toRq b) (j : Fin pbW.dim) :
    cf (a[(j : ℕ)]!) = cf (b[(j : ℕ)]!) := by
  rw [← toRq_coeff a j, ← toRq_coeff b j, h]

/-- **NON-VACUITY (dimension):** the coordinate bridge maps into a genuine degree-`256` ring. -/
theorem pbW_dim_256 : pbW.dim = 256 := pbW_dim

#assert_axioms toRq_coeff_separates

end Dregg2.Crypto.VerifyCoreEqSpec
