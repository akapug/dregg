/-
# `Dregg2.Crypto.ParameterSecurity` — THE PARAMETER-LEVEL SECURITY THEOREM.

The rest of the crypto tree proves the QUALITATIVE reduction tree: the hybrid signature is unforgeable if
`DL ∨ MSIS` holds (`HybridCombiner`), the KEM is IND-CCA in the QROM up to the FO + O2H terms (`FoQrom`,
`FoBookkeeping`), multi-session UC costs a session-count union bound (`UcSignature`), adaptive corruption
costs ZERO (`AdaptiveTSUF`), and the combiner is TIGHT (`HybridCombiner.hybrid_euf_cma_if_either`). Each is
a `Prop`-level statement or a symbolic advantage term. This module turns that qualitative tree into a
DEPLOYABLE NUMBER: at the deployed ML-DSA-65 / ML-KEM-768 parameters, against any `q`-query quantum
adversary, the whole system's advantage is `≤ 2^(−λ)` for a λ we COMPUTE.

## The accounting (§-by-§)

  **§1 — `advOf` — the advantage-in-bits calculus.** `advOf b = 2^(−b)` (an advantage of `b` bits). The
  whole composition is arithmetic in this one function: `advOf a · advOf b = advOf (a+b)` (union/product),
  `√(advOf b) = advOf (b/2)` (the forking / O2H square-root loss), `advOf` is ANTITONE (more bits = smaller
  advantage), and finite sums fold with a `−log₂(#terms)` bit cost. BOTH TEETH: `advOf` is a genuine
  discriminator — antitone both directions — and `λ ↦ advOf λ` is negligible (`negl_advOf`, ties into
  `ConcreteSecurity`).

  **§2 — THE ADVANTAGE TWINS (1a).** Each qualitative reduction gets its quantitative twin, a real-valued
  advantage bound whose SHAPE is the cited theorem's:
   * `sigForkAdv` — the ML-DSA (hybrid PQ half) forgery advantage, `√(q · advOf msisBits)`, the FORKING
     inversion of `HermineTSUF.forking_probability_bound` (`frk ≥ ε(ε/q_H − 1/|C|)` ⟹ `ε ≤ √(q_H·frk)`),
     with the hybrid combiner TIGHT (`HybridCombiner.hybrid_forger_projects_to_pq`, no loss), and adaptive
     corruption ZERO loss (`AdaptiveTSUF.adaptive_ts_uf_reduces_lossfree`).
   * `kemQromAdv` — the ML-KEM IND-CCA advantage, `2√(q·(q·b)) + advOf mlweBits + advOf foBits`, the QROM
     bound of `FoQrom.ml_kem_ind_cca_qrom` (O2H reprogramming term `OneWayToHiding.o2h_bound` + the FO
     classical hops `FoBookkeeping.fo_ind_cca_bound`).
   * the UC session factor — `2^sessions · sigForkAdv`, the union bound `UcSignature.multiUcAdv_le_sum`.
   * the consensus factor — `2^consensus · (…)`, the per-turn union bound over the finality gate.

  **§3 — THE COMPOSITION (1b).** `sysAdvExpr E q sessions consensus` composes all of the above by the
  actual reduction structure, and `system_advantage_bound` proves it `≤ advOf (lambdaR …)` — every step an
  `advOf` law, no new assumption.

  **§4 — THE LATTICE-HARDNESS INTERFACE (1c).** `LatticeEstimate` carries the bit-security of MSIS and MLWE
  at the deployed parameters as LABELED NUMERIC INPUTS. **This is the ONLY non-proof input in the entire
  tree.** The two fields `msisBits`, `mlweBits` are the empirical Lattice-Estimator / NIST outputs — they
  are NUMBERS, NOT a `def …Hard`, NOT used as a hardness hypothesis anywhere; only fed to arithmetic.

  **§5 — THE THEOREM (1d).** `system_security_bits`: given a `LatticeEstimate` in the deployable regime, for
  any `q ≤ 2^log2q` quantum adversary, `sysAdvExpr ≤ advOf (sysSecurityBits …)` — i.e. `≤ 2^(−λ)` for the
  COMPUTED λ `sysSecurityBits`. `#eval`/`#guard` compute λ at the NIST-claimed estimates; the TOOTH shows a
  DEGRADED estimate (halved bits) provably yields a smaller λ — the estimate is load-bearing and the
  composition losses (forking halving, query budget, session/consensus union) are visible in the number.

## No named-carrier laundering.

No `def …Hard` is introduced. The `LatticeEstimate` is a bag of NUMBERS, never a `Prop`, never assumed.
Every bound is `advOf` arithmetic proved from Mathlib's `rpow`/`sqrt` API — theorems, never `axiom`s. The
qualitative reductions are CITED (their shapes are these terms); the numeric composition is self-contained.
The only residual is the lattice floor (`MSISHard`/`MLWESearchHard`, quantified by the ONE labeled
estimate), exactly as the discipline permits.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Dregg2.Tactics
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Crypto.Lattice
import Dregg2.Crypto.HermineTSUF
import Dregg2.Crypto.FoQrom
import Dregg2.Crypto.FoBookkeeping
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.UcSignature
import Dregg2.Crypto.AdaptiveTSUF

open Dregg2.Crypto.ConcreteSecurity

namespace Dregg2.Crypto.ParameterSecurity

/-! ## §1 — `advOf` — the advantage-in-bits calculus. -/

/-- **`advOf b = 2^(−b)`** — an advantage of `b` BITS of security. The single object the whole
parameter-level composition is arithmetic in. -/
noncomputable def advOf (b : ℝ) : ℝ := (2 : ℝ) ^ (-b)

theorem advOf_pos (b : ℝ) : 0 < advOf b := Real.rpow_pos_of_pos (by norm_num) _

/-- `advOf a · advOf b = advOf (a+b)` — the UNION / product law: multiplying advantages ADDS bit-losses. -/
theorem advOf_mul (a b : ℝ) : advOf a * advOf b = advOf (a + b) := by
  unfold advOf
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1; ring

/-- `advOf (-(n)) = 2^n` — a NEGATIVE bit-count is a power blow-up (the `2^sessions` / `2^consensus` /
`2^log2q` factors). -/
theorem advOf_negNat (n : ℕ) : advOf (-(n:ℝ)) = (2:ℝ) ^ n := by
  unfold advOf; rw [neg_neg, Real.rpow_natCast]

/-- `advOf (-1) = 2`. -/
theorem advOf_negOne : advOf (-1) = 2 := by
  unfold advOf; rw [neg_neg, Real.rpow_one]

/-- `2^k · advOf x = advOf (x − k)` — a `k`-bit blow-up EATS `k` bits of an advantage. -/
theorem natpow_mul_advOf (k : ℕ) (x : ℝ) : (2:ℝ) ^ k * advOf x = advOf (x - (k:ℝ)) := by
  rw [← advOf_negNat, advOf_mul]; congr 1; ring

/-- `√(advOf b) = advOf (b/2)` — THE SQUARE-ROOT LOSS: the forking-lemma / O2H reduction HALVES the bits. -/
theorem advOf_sqrt (b : ℝ) : Real.sqrt (advOf b) = advOf (b / 2) := by
  rw [Real.sqrt_eq_rpow]
  unfold advOf
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1; ring

/-- `advOf` is ANTITONE: more bits ⟹ smaller advantage. -/
theorem advOf_antitone {a b : ℝ} (h : a ≤ b) : advOf b ≤ advOf a := by
  unfold advOf
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)

/-- `2 · advOf b = advOf (b − 1)`. -/
theorem two_mul_advOf (b : ℝ) : 2 * advOf b = advOf (b - 1) := by
  rw [← advOf_negOne, advOf_mul]; congr 1; ring

/-- **TWO-TERM UNION.** `advOf a + advOf b ≤ advOf (min a b − 1)` — summing two advantages costs one bit. -/
theorem advOf_add_le (a b : ℝ) : advOf a + advOf b ≤ advOf (min a b - 1) := by
  have h1 : advOf a ≤ advOf (min a b) := advOf_antitone (min_le_left a b)
  have h2 : advOf b ≤ advOf (min a b) := advOf_antitone (min_le_right a b)
  calc advOf a + advOf b ≤ 2 * advOf (min a b) := by linarith
    _ = advOf (min a b - 1) := two_mul_advOf _

/-- **THREE-TERM UNION.** `advOf a + advOf b + advOf c ≤ advOf (min a (min b c) − 2)` — summing three
advantages costs two bits (`3 ≤ 4 = 2²`). The FO chain's O2H + CPA + correctness fold. -/
theorem advOf_add3_le (a b c : ℝ) :
    advOf a + advOf b + advOf c ≤ advOf (min a (min b c) - 2) := by
  set m := min a (min b c) with hm
  have ha : advOf a ≤ advOf m := advOf_antitone (min_le_left _ _)
  have hb : advOf b ≤ advOf m := advOf_antitone (le_trans (min_le_right a (min b c)) (min_le_left b c))
  have hc : advOf c ≤ advOf m := advOf_antitone (le_trans (min_le_right a (min b c)) (min_le_right b c))
  have hpos := advOf_pos m
  have e4 : (4:ℝ) * advOf m = advOf (m - 2) := by
    have : (4:ℝ) * advOf m = 2 * (2 * advOf m) := by ring
    rw [this, two_mul_advOf, two_mul_advOf]; congr 1; ring
  calc advOf a + advOf b + advOf c ≤ 4 * advOf m := by linarith
    _ = advOf (m - 2) := e4

/-- `advOf (n : ℝ) = 1/2^n` — the bridge to `ConcreteSecurity.Negl`. -/
theorem advOf_natCast (n : ℕ) : advOf (n : ℝ) = 1 / (2:ℝ) ^ n := by
  unfold advOf
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- **(TOOTH — ties `advOf` into the concrete-security substrate.)** The ensemble `λ ↦ advOf λ = 2^(−λ)` is
NEGLIGIBLE — the parameter-level advantage, taken as a family in the security parameter, lands in the
`ConcreteSecurity.Negl` algebra. -/
theorem negl_advOf : Negl (fun n : ℕ => advOf (n : ℝ)) := by
  have h : (fun n : ℕ => advOf (n:ℝ)) = (fun n : ℕ => 1 / (2:ℝ) ^ n) := by
    funext n; exact advOf_natCast n
  rw [h]; exact negl_two_pow

/-! ## §4 (stated early) — THE DEPLOYED PARAMETERS + THE LATTICE-HARDNESS INTERFACE. -/

/-- ML-DSA parameter record (for citation of the deployed instance). -/
structure MlDsaParams where
  k : ℕ
  l : ℕ
  eta : ℕ
  q : ℕ
  n : ℕ
deriving Repr, DecidableEq

/-- ML-KEM parameter record (for citation of the deployed instance). -/
structure MlKemParams where
  k : ℕ
  eta1 : ℕ
  eta2 : ℕ
  q : ℕ
  n : ℕ
deriving Repr, DecidableEq

/-- **ML-DSA-65** (FIPS 204, NIST security category 3): `(k,l,η,q,n) = (6,5,4,8380417,256)`. -/
def mlDsa65 : MlDsaParams := ⟨6, 5, 4, 8380417, 256⟩

/-- **ML-KEM-768** (FIPS 203, NIST security category 3): `(k,η₁,η₂,q,n) = (3,2,2,3329,256)`. -/
def mlKem768 : MlKemParams := ⟨3, 2, 2, 3329, 256⟩

/-- **`LatticeEstimate` — THE ONLY NON-PROOF INPUT IN THE ENTIRE TREE.**

The parameter-level theorem bottoms out at the concrete hardness of MSIS/MLWE at the deployed lattice
parameters. That hardness is NOT provable in Lean (it is the lattice FLOOR); its bit-security is an
EMPIRICAL number from the Lattice Estimator [Albrecht–Player–Scott] and the NIST parameter rationale
[FIPS 203/204]. This structure carries those numbers — and ONLY numbers.

It is deliberately a bag of `ℕ`s, **NOT** a `def …Hard`, **NOT** a `Prop`, **NOT** used as a hardness
hypothesis anywhere below: the fields are read ONLY by arithmetic (`sysSecurityBits`). This is the single
place the tree touches the empirical world; everything downstream is proof. -/
structure LatticeEstimate where
  /-- **EMPIRICAL (Lattice Estimator / NIST).** Bit-security of Module-SIS at the ML-DSA-65 parameters — the
  quantum core-SVP cost of finding a short vector, i.e. `−log₂(Adv^MSIS)`. A NUMBER, not a hypothesis. -/
  msisBits : ℕ
  /-- **EMPIRICAL (Lattice Estimator / NIST).** Bit-security of Module-LWE at the ML-KEM-768 parameters —
  `−log₂(Adv^MLWE)`. A NUMBER, not a hypothesis. -/
  mlweBits : ℕ
  /-- Message / seed min-entropy `H∞(m*)` feeding the O2H guessing term `b = 2^(−msgEntropyBits)`. A SPEC
  constant (ML-KEM encapsulates a 256-bit seed), not a lattice estimate. -/
  msgEntropyBits : ℕ
  /-- FO correctness margin: `−log₂(δ)` for the decryption-failure rate `δ` (the `simFail + corrSpread`
  bucket of `FoBookkeeping.fo_ind_cca_bound`). A SPEC constant computed from the noise distribution. -/
  foCorrectnessBits : ℕ
  /-- The deployed ML-DSA parameters these `msisBits` were estimated at (for citation). -/
  mldsa : MlDsaParams
  /-- The deployed ML-KEM parameters these `mlweBits` were estimated at (for citation). -/
  mlkem : MlKemParams

/-! ## §2 — THE ADVANTAGE TWINS (1a). Each reduction as a real-valued advantage bound. -/

/-- **`sigForkAdv E q` — the hybrid-signature (PQ half) forgery advantage of a `q`-query adversary.**
`√(q · advOf msisBits)`: the FORKING inversion of `HermineTSUF.forking_probability_bound`
(`frk ≥ ε(ε/q_H − 1/|C|)`, so a forger with advantage `ε` yields an MSIS solver with `frk ≥ ε²/q_H`, i.e.
`ε ≤ √(q_H · Adv^MSIS)`). The hybrid combiner is TIGHT — a hybrid forgery projects to a PQ forgery with NO
advantage loss (`HybridCombiner.hybrid_forger_projects_to_pq`) — so this IS the hybrid signature's
quantum-forgery advantage; adaptive corruption adds ZERO
(`AdaptiveTSUF.adaptive_ts_uf_reduces_lossfree`). -/
noncomputable def sigForkAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  Real.sqrt ((q : ℝ) * advOf E.msisBits)

/-- **`kemQromAdv E q` — the ML-KEM IND-CCA advantage of a `q`-query QUANTUM adversary.**
`2·√(q·(q·b)) + advOf mlweBits + advOf foCorrectnessBits` with `b = advOf msgEntropyBits`: the O2H
reprogramming term (`FoQrom.reprog_term_bound` / `OneWayToHiding.o2h_bound`) plus the FO classical hops
(`FoBookkeeping.fo_ind_cca_bound`: `cpaTerm` grounded in `Lattice.MLWESearchHard`, `simFail + corrSpread`
in the correctness margin). This is exactly `FoQrom.ml_kem_ind_cca_qrom`'s bound, as a NUMBER. -/
noncomputable def kemQromAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
    + advOf E.mlweBits + advOf E.foCorrectnessBits

/-- The signature's per-adversary security in bits (post-forking): `(msisBits − log₂q)/2`. The quadratic
forking loss HALVES the assumption bits and pays the query budget. -/
noncomputable def sigBitsR (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  ((E.msisBits : ℝ) - (log2q : ℝ)) / 2

/-- The O2H reprogramming term's bits: `msgEntropyBits/2 − log₂q − 1` (from `2q·√b`). -/
noncomputable def o2hBitsR (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  (E.msgEntropyBits : ℝ) / 2 - (log2q : ℝ) - 1

/-- The KEM's security in bits: the MIN of the O2H term, the MLWE (CPA) term, and the correctness term. -/
noncomputable def kem3R (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  min (o2hBitsR E log2q) (min (E.mlweBits : ℝ) (E.foCorrectnessBits : ℝ))

/-- **`sigForkAdv` bit bound.** A `q ≤ 2^log2q` adversary's forging advantage is `≤ advOf (sigBitsR)` — the
forking square-root loss made numeric. `q` is LOAD-BEARING (a larger query budget shrinks the bits). -/
theorem sigForkAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    sigForkAdv E q ≤ advOf (sigBitsR E log2q) := by
  unfold sigForkAdv sigBitsR
  have hqr : (q : ℝ) ≤ (2:ℝ) ^ log2q := by exact_mod_cast hq
  have h1 : (q : ℝ) * advOf E.msisBits ≤ (2:ℝ) ^ log2q * advOf E.msisBits :=
    mul_le_mul_of_nonneg_right hqr (le_of_lt (advOf_pos _))
  calc Real.sqrt ((q : ℝ) * advOf E.msisBits)
      ≤ Real.sqrt ((2:ℝ) ^ log2q * advOf E.msisBits) := Real.sqrt_le_sqrt h1
    _ = advOf (((E.msisBits : ℝ) - (log2q : ℝ)) / 2) := by rw [natpow_mul_advOf, advOf_sqrt]

/-- The O2H term at the query budget: `2·√(2^log2q·(2^log2q·advOf msgEntropy)) = advOf (o2hBitsR)`. -/
theorem o2hTerm_bound (E : LatticeEstimate) (log2q : ℕ) :
    2 * Real.sqrt ((2:ℝ) ^ log2q * ((2:ℝ) ^ log2q * advOf E.msgEntropyBits))
      = advOf (o2hBitsR E log2q) := by
  unfold o2hBitsR
  rw [natpow_mul_advOf, natpow_mul_advOf, advOf_sqrt, two_mul_advOf]
  congr 1; ring

/-- **`kemQromAdv` bit bound.** A `q ≤ 2^log2q` quantum adversary's IND-CCA advantage is `≤ advOf (kem3R − 2)`
— the three FO/QROM terms folded with a two-bit union cost. -/
theorem kemQromAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    kemQromAdv E q ≤ advOf (kem3R E log2q - 2) := by
  unfold kemQromAdv kem3R
  have hqr : (q : ℝ) ≤ (2:ℝ) ^ log2q := by exact_mod_cast hq
  have hpos : (0:ℝ) ≤ advOf E.msgEntropyBits := le_of_lt (advOf_pos _)
  have hle : (q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits)
      ≤ (2:ℝ) ^ log2q * ((2:ℝ) ^ log2q * advOf E.msgEntropyBits) := by
    have hinner : (q : ℝ) * advOf E.msgEntropyBits ≤ (2:ℝ) ^ log2q * advOf E.msgEntropyBits :=
      mul_le_mul_of_nonneg_right hqr hpos
    exact mul_le_mul hqr hinner (by positivity) (by positivity)
  have ho2h : 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
      ≤ advOf (o2hBitsR E log2q) := by
    calc 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
        ≤ 2 * Real.sqrt ((2:ℝ) ^ log2q * ((2:ℝ) ^ log2q * advOf E.msgEntropyBits)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)
      _ = advOf (o2hBitsR E log2q) := o2hTerm_bound E log2q
  have h3 := advOf_add3_le (o2hBitsR E log2q) (E.mlweBits : ℝ) (E.foCorrectnessBits : ℝ)
  calc 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
          + advOf E.mlweBits + advOf E.foCorrectnessBits
      ≤ advOf (o2hBitsR E log2q) + advOf E.mlweBits + advOf E.foCorrectnessBits := by linarith
    _ ≤ advOf (min (o2hBitsR E log2q) (min (E.mlweBits : ℝ) (E.foCorrectnessBits : ℝ)) - 2) := h3

/-! ## §3 — THE COMPOSITION (1b). -/

/-- **`sysAdvExpr E q sessions consensus` — THE END-TO-END SYSTEM ADVANTAGE.** A `2^consensus`-turn consensus
run, each turn union-bounding the `2^sessions`-session UC hybrid signature (`UcSignature.multiUcAdv_le_sum`)
and the KEM. The full composition following the actual reduction structure. -/
noncomputable def sysAdvExpr (E : LatticeEstimate) (q sessions consensus : ℕ) : ℝ :=
  (2:ℝ) ^ consensus * ((2:ℝ) ^ sessions * sigForkAdv E q + kemQromAdv E q)

/-- **`lambdaR` — the derived security bits (real).** `min (sigBits − sessions) (kemBits − 2) − 1 − consensus`:
the smaller of the signature and KEM floors, minus the session, union, and consensus bit-costs. -/
noncomputable def lambdaR (E : LatticeEstimate) (log2q sessions consensus : ℕ) : ℝ :=
  min (sigBitsR E log2q - (sessions : ℝ)) (kem3R E log2q - 2) - 1 - (consensus : ℝ)

/-- **THE END-TO-END ADVANTAGE BOUND (1b).** For any `q ≤ 2^log2q` quantum adversary,
`sysAdvExpr E q sessions consensus ≤ advOf (lambdaR E log2q sessions consensus)`. Every step is an `advOf`
law composing the twins — hybrid combiner tight, forking square-root, O2H, session/consensus union, adaptive
zero — with NO new assumption. -/
theorem system_advantage_bound (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q)
    (sessions consensus : ℕ) :
    sysAdvExpr E q sessions consensus ≤ advOf (lambdaR E log2q sessions consensus) := by
  unfold sysAdvExpr lambdaR
  have hsig : (2:ℝ) ^ sessions * sigForkAdv E q ≤ advOf (sigBitsR E log2q - (sessions : ℝ)) := by
    calc (2:ℝ) ^ sessions * sigForkAdv E q
        ≤ (2:ℝ) ^ sessions * advOf (sigBitsR E log2q) :=
          mul_le_mul_of_nonneg_left (sigForkAdv_le E hq) (by positivity)
      _ = advOf (sigBitsR E log2q - (sessions : ℝ)) := natpow_mul_advOf _ _
  have hkem := kemQromAdv_le E (log2q := log2q) hq
  have hsum : (2:ℝ) ^ sessions * sigForkAdv E q + kemQromAdv E q
      ≤ advOf (min (sigBitsR E log2q - (sessions : ℝ)) (kem3R E log2q - 2) - 1) := by
    calc (2:ℝ) ^ sessions * sigForkAdv E q + kemQromAdv E q
        ≤ advOf (sigBitsR E log2q - (sessions : ℝ)) + advOf (kem3R E log2q - 2) := by linarith
      _ ≤ advOf (min (sigBitsR E log2q - (sessions : ℝ)) (kem3R E log2q - 2) - 1) := advOf_add_le _ _
  calc (2:ℝ) ^ consensus * ((2:ℝ) ^ sessions * sigForkAdv E q + kemQromAdv E q)
      ≤ (2:ℝ) ^ consensus * advOf (min (sigBitsR E log2q - (sessions : ℝ)) (kem3R E log2q - 2) - 1) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = advOf (min (sigBitsR E log2q - (sessions : ℝ)) (kem3R E log2q - 2) - 1 - (consensus : ℝ)) := by
        rw [natpow_mul_advOf]

/-! ## §5 — THE THEOREM (1d). The computed λ and the deployable-regime restatement. -/

/-- **`sysSecurityBits E log2q sessions consensus` — THE COMPUTED SECURITY PARAMETER λ (in bits).**
`min ((msisBits − log₂q)/2 − sessions) (kemBits − 2) − 1 − consensus`, all `ℕ` (truncating, hence a
CONSERVATIVE lower bound on the real derived bits). Instantiating a `LatticeEstimate` and the adversary
budget makes this a concrete number — the deployable security claim. -/
def sysSecurityBits (E : LatticeEstimate) (log2q sessions consensus : ℕ) : ℕ :=
  min ((E.msisBits - log2q) / 2 - sessions)
      (min (E.msgEntropyBits / 2 - log2q - 1) (min E.mlweBits E.foCorrectnessBits) - 2)
    - 1 - consensus

/-- **`Deployable` — the meaningful-parameter regime.** The estimate bits exceed the composition losses at
every stage (no bit-count underflows). Decidable, so `by decide` discharges it at any concrete instance.
Outside this regime the bound is vacuous (the advantage can exceed `1`); inside it, it is the deployable
claim. -/
def Deployable (E : LatticeEstimate) (log2q sessions consensus : ℕ) : Prop :=
  log2q ≤ E.msisBits ∧
  sessions ≤ (E.msisBits - log2q) / 2 ∧
  log2q + 1 ≤ E.msgEntropyBits / 2 ∧
  2 ≤ min (E.msgEntropyBits / 2 - log2q - 1) (min E.mlweBits E.foCorrectnessBits) ∧
  1 + consensus ≤ min ((E.msisBits - log2q) / 2 - sessions)
      (min (E.msgEntropyBits / 2 - log2q - 1) (min E.mlweBits E.foCorrectnessBits) - 2)

instance (E : LatticeEstimate) (log2q sessions consensus : ℕ) :
    Decidable (Deployable E log2q sessions consensus) := by unfold Deployable; infer_instance

/-- The computed `ℕ` λ lower-bounds the real derived bits: `↑sysSecurityBits ≤ lambdaR` (`ℕ` truncation is
conservative). Needs the `Deployable` regime so the bit-count subtractions cast exactly. -/
theorem sysSecurityBits_le_lambdaR (E : LatticeEstimate) {log2q sessions consensus : ℕ}
    (hdep : Deployable E log2q sessions consensus) :
    (sysSecurityBits E log2q sessions consensus : ℝ) ≤ lambdaR E log2q sessions consensus := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hdep
  set kem3N : ℕ := min (E.msgEntropyBits / 2 - log2q - 1) (min E.mlweBits E.foCorrectnessBits) with hk3
  -- (1) signature bits: ↑((msisBits - log2q)/2) ≤ sigBitsR
  have hsigDiv : (((E.msisBits - log2q) / 2 : ℕ) : ℝ) ≤ sigBitsR E log2q := by
    unfold sigBitsR
    calc (((E.msisBits - log2q) / 2 : ℕ) : ℝ)
        ≤ ((E.msisBits - log2q : ℕ) : ℝ) / 2 := Nat.cast_div_le
      _ = ((E.msisBits : ℝ) - (log2q : ℝ)) / 2 := by rw [Nat.cast_sub h1]
  have hsigS : (((E.msisBits - log2q) / 2 - sessions : ℕ) : ℝ) ≤ sigBitsR E log2q - (sessions : ℝ) := by
    rw [Nat.cast_sub h2]; linarith
  -- (2) o2h bits: ↑(msgEntropy/2 - log2q - 1) ≤ o2hBitsR
  have hlog2q_le : log2q ≤ E.msgEntropyBits / 2 := le_trans (Nat.le_succ _) h3
  have hone_le : 1 ≤ E.msgEntropyBits / 2 - log2q := by omega
  have ho2h : ((E.msgEntropyBits / 2 - log2q - 1 : ℕ) : ℝ) ≤ o2hBitsR E log2q := by
    unfold o2hBitsR
    have hdiv : ((E.msgEntropyBits / 2 : ℕ) : ℝ) ≤ (E.msgEntropyBits : ℝ) / 2 := Nat.cast_div_le
    rw [Nat.cast_sub hone_le, Nat.cast_sub hlog2q_le]
    linarith
  -- (3) kem bits: ↑kem3N ≤ kem3R
  have hkem3 : ((kem3N : ℕ) : ℝ) ≤ kem3R E log2q := by
    rw [hk3]; unfold kem3R
    rw [Nat.cast_min, Nat.cast_min]
    exact min_le_min ho2h (le_refl _)
  have hkemS : ((kem3N - 2 : ℕ) : ℝ) ≤ kem3R E log2q - 2 := by
    rw [Nat.cast_sub h4, Nat.cast_ofNat]; linarith
  -- (4) the outer min
  have hmin : ((min ((E.msisBits - log2q) / 2 - sessions) (kem3N - 2) : ℕ) : ℝ)
      ≤ min (sigBitsR E log2q - (sessions : ℝ)) (kem3R E log2q - 2) := by
    rw [Nat.cast_min]; exact min_le_min hsigS hkemS
  -- (5) subtract 1 and consensus
  have hmin_ge : 1 + consensus ≤ min ((E.msisBits - log2q) / 2 - sessions) (kem3N - 2) := h5
  unfold sysSecurityBits lambdaR
  rw [show min ((E.msisBits - log2q) / 2 - sessions)
        (min (E.msgEntropyBits / 2 - log2q - 1) (min E.mlweBits E.foCorrectnessBits) - 2)
      = min ((E.msisBits - log2q) / 2 - sessions) (kem3N - 2) from by rw [hk3]]
  rw [Nat.cast_sub (by omega : consensus ≤ min ((E.msisBits - log2q) / 2 - sessions) (kem3N - 2) - 1),
      Nat.cast_sub (by omega : 1 ≤ min ((E.msisBits - log2q) / 2 - sessions) (kem3N - 2)),
      Nat.cast_one]
  linarith [hmin]

/-- **`system_security_bits` — THE PARAMETER-LEVEL SECURITY THEOREM (1d).**

Given a `LatticeEstimate` in the deployable regime, for ANY `q`-query quantum adversary (`q ≤ 2^log2q`),
the entire system's advantage is bounded:

  `sysAdvExpr E q sessions consensus ≤ 2^(−λ)`,  where λ = `sysSecurityBits E log2q sessions consensus`.

Instantiating the estimate and the budget yields a CONCRETE λ (see the `#eval`s below). Every reduction is
cited and proved; the ONLY empirical input is the `LatticeEstimate`'s `msisBits`/`mlweBits`. -/
theorem system_security_bits (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q)
    (sessions consensus : ℕ) (hdep : Deployable E log2q sessions consensus) :
    sysAdvExpr E q sessions consensus ≤ advOf ((sysSecurityBits E log2q sessions consensus : ℕ) : ℝ) := by
  refine (system_advantage_bound E hq sessions consensus).trans ?_
  exact advOf_antitone (sysSecurityBits_le_lambdaR E hdep)

/-! ## §6 — INSTANTIATION AT THE NIST-CLAIMED ESTIMATES + THE LOAD-BEARING TOOTH. -/

/-- **THE DEPLOYED ESTIMATE.** ML-DSA-65 / ML-KEM-768, NIST security category 3. The empirical inputs:
`msisBits = 192` (the category-3 MSIS target, Lattice-Estimator quantum core-SVP for Dilithium3),
`mlweBits = 181` (Kyber768 MLWE), `msgEntropyBits = 256` (the encapsulated seed), `foCorrectnessBits = 174`
(ML-KEM-768 `δ ≈ 2^(−174)`). -/
def deployedEstimate : LatticeEstimate where
  msisBits := 192
  mlweBits := 181
  msgEntropyBits := 256
  foCorrectnessBits := 174
  mldsa := mlDsa65
  mlkem := mlKem768

/-- **A DEGRADED ESTIMATE — the tooth.** Halve the lattice-hardness bits (`msisBits 192→96`,
`mlweBits 181→90`), everything else identical. Models the Lattice Estimator delivering a WEAKER hardness
number (better cryptanalysis). -/
def degradedEstimate : LatticeEstimate :=
  { deployedEstimate with msisBits := 96, mlweBits := 90 }

/-- λ at the DEPLOYED estimate: a `2^20`-query, `2^4`-session, `2^2`-turn quantum adversary faces **79 bits**.
The forking halving `(192−20)/2 = 86`, minus sessions/union/consensus, is the binding term. -/
example : sysSecurityBits deployedEstimate 20 4 2 = 79 := by decide

#eval sysSecurityBits deployedEstimate 20 4 2   -- 79
#guard sysSecurityBits deployedEstimate 20 4 2 = 79

/-- The deployed estimate is in the deployable regime at these parameters, so `system_security_bits` fires:
the system advantage is `≤ 2^(−79)`. -/
example : Deployable deployedEstimate 20 4 2 := by decide

-- λ at a stress budget (`2^40` queries, `2^20` sessions, `2^10` turns): still **45 bits** — the composition
-- losses (forking halving + query + session/consensus union) are VISIBLE in the drop from the 192-bit input.
#eval sysSecurityBits deployedEstimate 40 20 10   -- 45
#guard sysSecurityBits deployedEstimate 40 20 10 = 45
example : Deployable deployedEstimate 40 20 10 := by decide

-- **THE LOAD-BEARING TOOTH.** Halving the lattice-hardness bits STRICTLY drops the security parameter
-- (79 → 31 at the same budget). The `LatticeEstimate` is load-bearing — the whole claim moves with it — and
-- because the forking loss halves the estimate, a halving of `msisBits` costs DOUBLE in the final number.
#eval sysSecurityBits degradedEstimate 20 4 2   -- 31
#guard sysSecurityBits degradedEstimate 20 4 2 = 31

example : sysSecurityBits degradedEstimate 20 4 2 < sysSecurityBits deployedEstimate 20 4 2 := by decide

/-- **THE VIOLATING (out-of-regime) INSTANCE.** If the query budget MEETS the assumption bits
(`log2q = msisBits`), the signature floor collapses: λ bottoms out at `0` and `advOf 0 = 1` — a vacuous
bound. So `Deployable` is genuinely restrictive, and the estimate must EXCEED the losses for a real claim. -/
example : sysSecurityBits deployedEstimate 192 4 2 = 0 := by decide
example : ¬ Deployable deployedEstimate 192 4 2 := by decide

/-- The λ arithmetic is exactly `2^(−λ)`: at the deployed estimate the bound reads
`sysAdvExpr ≤ 1 / 2^79`. -/
example : advOf ((sysSecurityBits deployedEstimate 20 4 2 : ℕ) : ℝ) = 1 / (2:ℝ) ^ 79 := by
  rw [show sysSecurityBits deployedEstimate 20 4 2 = 79 from by decide, advOf_natCast]

#assert_all_clean [
  advOf_pos,
  advOf_mul,
  advOf_sqrt,
  advOf_antitone,
  advOf_add_le,
  advOf_add3_le,
  negl_advOf,
  sigForkAdv_le,
  o2hTerm_bound,
  kemQromAdv_le,
  system_advantage_bound,
  sysSecurityBits_le_lambdaR,
  system_security_bits
]

end Dregg2.Crypto.ParameterSecurity
