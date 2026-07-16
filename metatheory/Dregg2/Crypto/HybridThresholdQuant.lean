/-
# `Dregg2.Crypto.HybridThresholdQuant` — the HYBRID / THRESHOLD / UC-disjunctive reductions, THREADED
  through the quantitative (`ProbCrypto`) substrate.

Track B step 3. Steps 1–2 built the concrete-security substrate — `winProb` games, the `ForkingFamily`
with its PROVED forking bound `ε·(ε − 1/|C|) ≤ solverAdv`, the quantitative floors
`MSISHardQuantShape`/`DLHardQuantShape`, and the reduction `forking_reduces_against_floor` — and closed the two UC
gaps (`UcSignatureQuant`). This module re-threads the remaining three Boolean reductions AS GENUINE
ADVANTAGE-INEQUALITIES, never relabelling a Boolean fact as quantitative.

## What is threaded (§-by-§)

  **§0 — two monotonicity lemmas.** `winProb_le_of_imp` — if a game's win predicate implies another's, its
  winning probability is `≤`. `negl_of_le` — a nonnegative ensemble dominated by a negligible one is
  negligible. The two combinators every lift below uses.

  **§1 — HYBRID COMBINER, quantitative ("secure-if-either" over real advantages).** The Boolean keystone
  `HybridCombiner.hybrid_euf_cma_if_either` says a hybrid forgery PROJECTS to a forgery on BOTH components
  (`hybrid_forger_projects_to_{classical,pq}`). Re-threaded: a `HybridForkingFamily` carries the two
  components' accept events over a SHARED outcome space; `hybridForgerAdv` is the `winProb` of their
  CONJUNCTION (the hybrid accepts iff both do). The combiner property is now the POINTWISE implication
  `accC ω c ∧ accP ω c ⟹ accC ω c` (resp. `accP`), which lifts to `hybridForgerAdv ≤ classicalForgerAdv`
  AND `≤ pqForgerAdv` (`winProb_le_of_imp` + the §1 bridge). Hence `hybrid_forger_negl_under_floors`:
  `Negl hybridForgerAdv` under `DLHardQuantShape ∨ MSISHardQuantShape` — a non-negligible hybrid advantage would force
  a non-negligible advantage in WHICHEVER component's floor holds, contradicting it (each leg discharged by
  `ucForger_negl_of_dl`/`_of_msis`). Teeth: ONE secure component ⇒ `hybridForgerAdv ≡ 0` (Negl); BOTH broken
  ⇒ `hybridForgerAdv ≡ 2/5` (NOT Negl) — the "either" is load-bearing on real advantages.

  **§2 — THRESHOLD (concurrent/adaptive), quantitative.** The `ForkingFamily`'s `forgerAdv` IS the concurrent
  TS-UF-0 forger's advantage in `HermineTSUF`'s finite counting-probability model (`§ProbForking`). So
  `threshold_forger_negl_of_msis` packages `Negl thresholdForgerAdv` under `MSISHardQuantShape`, reusing
  `forking_reduces_against_floor` — the concurrent threshold forger's forking→MSIS reduction, over real
  advantages. `adaptive_threshold_negl_of_msis` carries the adaptive/erasure statistical term as an ADDITIVE
  `Negl` summand (`negl_add`): an adaptive advantage `≤ forgerAdv + erasureTerm` with both negligible is
  negligible. Teeth: fires (base ≡ 0, negligible erasure); the const-`2/5` threshold forger breaks the floor.

  **§3 — UC DISJUNCTIVE BUNDLING (finishing UC's "grounded in one floor" residual).** `UcSignatureQuant`'s
  `computational_uc_realizes` grounded `advₑ` in a SINGLE floor (`MSISHardQuantShape`). `uc_realizes_disjunctive`
  carries TWO forking families `Fc` (DL leg) + `Fp` (MSIS leg) with `advₑ ≤` each, concluding `Negl advₑ`
  under `DLHardQuantShape ∨ MSISHardQuantShape` — case-split the disjunction, each leg discharged by
  `ucForger_negl_of_{dl,msis}` and dominated. Teeth: fires (advₑ ≡ 0 under either floor); the const-`2/5`
  advantage is NOT negligible (the disjunction is load-bearing — no floor ⇒ no realization).

## No relabelling, no named-carrier laundering.

Every advantage here is a genuine real (`winProb`) that CAN be non-negligible — the teeth exhibit `2/5`
advantages that BREAK the floor and `0` advantages that realize. The reductions are honest
advantage-inequalities (`hybridForgerAdv ≤ classicalForgerAdv`, `advₑ ≤ Fc.forgerAdv`), never a Boolean flag
renamed. Nothing here introduces an `axiom` or a `def …Hard` used as a hypothesis. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Crypto.ProbCrypto
import Dregg2.Crypto.UcSignatureQuant
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.HybridThresholdQuant

open Filter
open scoped BigOperators
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.UcSignatureQuant
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.Lattice (ShortNorm)

/-! ## §0 — Two monotonicity combinators. -/

/-! The two monotonicity combinators every lift below uses — `winProb_le_of_imp` (a `winProb` is monotone
in its win predicate) and `negl_of_le` (a nonnegative ensemble dominated by a negligible one is
negligible) — live next to `winProb` itself in `ProbCrypto` and arrive through the `open` above. They were
stated here first; `FloorGames` needs them too, so they moved to the layer that owns `winProb` rather than
being duplicated. -/

/-! ## §1 — The HYBRID combiner, quantitative: "secure-if-either" over real advantages. -/

/-- **A hybrid forging family** — the concrete-security lift of `HybridCombiner`'s ∧-combiner. Over a SHARED
outcome geometry (prefix world `World l`, challenge set `Chal l`) it carries TWO component accept events:
`accC` (the classical/ed25519 leg) and `accP` (the pq/ML-DSA leg). The hybrid accepts iff BOTH do — the whole
content of "hybrid", exactly `HybridCombiner.hybridVerify` at the event level. Every geometry field mirrors
`ForkingFamily`; the two projections `classical`/`pq` are genuine `ForkingFamily`s. -/
structure HybridForkingFamily where
  /-- The challenge set at parameter `l`. -/
  Chal : ℕ → Type
  /-- The prefix world at parameter `l`. -/
  World : ℕ → Type
  /-- The challenge set is a commutative ring. -/
  chalRing : ∀ l, CommRing (Chal l)
  /-- The shortness seminorm on the challenge set (carried; norm-irrelevant to the counting bound). -/
  chalNorm : ∀ l, letI := chalRing l; ShortNorm (Chal l)
  /-- Finiteness of the challenge set. -/
  chalFin : ∀ l, Fintype (Chal l)
  /-- Decidable equality on the challenge set. -/
  chalDec : ∀ l, DecidableEq (Chal l)
  /-- Finiteness of the prefix world. -/
  worldFin : ∀ l, Fintype (World l)
  /-- The CLASSICAL component's accept event. -/
  accC : ∀ l, World l → Chal l → Bool
  /-- The PQ component's accept event. -/
  accP : ∀ l, World l → Chal l → Bool
  /-- The prefix world is inhabited. -/
  worldPos : ∀ l, 0 < @Fintype.card (World l) (worldFin l)
  /-- The challenge set is inhabited. -/
  chalPos : ∀ l, 0 < @Fintype.card (Chal l) (chalFin l)

namespace HybridForkingFamily

/-- The CLASSICAL component as a genuine `ForkingFamily` — same geometry, `acc := accC`. -/
def classical (H : HybridForkingFamily) : ForkingFamily where
  Chal := H.Chal
  World := H.World
  chalRing := H.chalRing
  chalNorm := H.chalNorm
  chalFin := H.chalFin
  chalDec := H.chalDec
  worldFin := H.worldFin
  acc := H.accC
  worldPos := H.worldPos
  chalPos := H.chalPos

/-- The PQ component as a genuine `ForkingFamily` — same geometry, `acc := accP`. -/
def pq (H : HybridForkingFamily) : ForkingFamily where
  Chal := H.Chal
  World := H.World
  chalRing := H.chalRing
  chalNorm := H.chalNorm
  chalFin := H.chalFin
  chalDec := H.chalDec
  worldFin := H.worldFin
  acc := H.accP
  worldPos := H.worldPos
  chalPos := H.chalPos

/-- **The HYBRID forger advantage** — the `winProb` of the CONJUNCTION event `accC ∧ accP` over
`World l × Chal l`. A genuine real in `[0,1]`: the fraction of outcomes on which BOTH components' forgeries
verify (the hybrid accepts iff both do). -/
noncomputable def hybridForgerAdv (H : HybridForkingFamily) : ℕ → ℝ := fun l =>
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2 && H.accP l p.1 p.2)

theorem hybridForgerAdv_nonneg (H : HybridForkingFamily) (l : ℕ) : 0 ≤ H.hybridForgerAdv l := by
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  exact winProb_nonneg _

/-- **THE COMBINER PROPERTY, lifted — hybrid advantage `≤` CLASSICAL advantage.** The hybrid conjunction
event implies the classical event (`accC ω c ∧ accP ω c ⟹ accC ω c`), so `winProb (conjunction) ≤ winProb
(classical)`, which by the §1 bridge `winProb_prod_eq_advantage` IS `(H.classical).forgerAdv l`. The
probability-level `hybrid_forger_projects_to_classical`. -/
theorem hybridForgerAdv_le_classical (H : HybridForkingFamily) (l : ℕ) :
    H.hybridForgerAdv l ≤ (H.classical).forgerAdv l := by
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  have hbridge : (H.classical).forgerAdv l
      = winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2) :=
    (winProb_prod_eq_advantage (H.accC l)).symm
  rw [hbridge]
  show winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2 && H.accP l p.1 p.2)
      ≤ winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2)
  refine winProb_le_of_imp (fun p hp => ?_)
  rw [Bool.and_eq_true] at hp; exact hp.1

/-- **THE COMBINER PROPERTY, lifted — hybrid advantage `≤` PQ advantage.** Symmetrically, the hybrid
conjunction implies the pq event, so `hybridForgerAdv l ≤ (H.pq).forgerAdv l`. The probability-level
`hybrid_forger_projects_to_pq`. -/
theorem hybridForgerAdv_le_pq (H : HybridForkingFamily) (l : ℕ) :
    H.hybridForgerAdv l ≤ (H.pq).forgerAdv l := by
  letI := H.chalRing l; letI := H.chalNorm l; letI := H.chalFin l
  letI := H.chalDec l; letI := H.worldFin l
  have hbridge : (H.pq).forgerAdv l
      = winProb (fun p : H.World l × H.Chal l => H.accP l p.1 p.2) :=
    (winProb_prod_eq_advantage (H.accP l)).symm
  rw [hbridge]
  show winProb (fun p : H.World l × H.Chal l => H.accC l p.1 p.2 && H.accP l p.1 p.2)
      ≤ winProb (fun p : H.World l × H.Chal l => H.accP l p.1 p.2)
  refine winProb_le_of_imp (fun p hp => ?_)
  rw [Bool.and_eq_true] at hp; exact hp.2

end HybridForkingFamily

/-- **THE HYBRID COMBINER, QUANTITATIVE — `Negl hybridForgerAdv` under `DLHardQuantShape ∨ MSISHardQuantShape`.** If
EITHER the classical DL floor OR the pq MSIS floor holds (quantitatively), the hybrid forger's advantage is
negligible. Case-split the disjunction: whichever floor holds discharges its component's forger advantage
(`ucForger_negl_of_dl`/`_of_msis`), and the hybrid advantage — bounded ABOVE by that component's advantage
(`hybridForgerAdv_le_classical`/`_pq`) — is dominated, hence negligible (`negl_of_le`). A non-negligible
hybrid forger would force a non-negligible forger against the floor that holds — the concrete-security
"hybrid, not PQ-only". -/
theorem hybrid_forger_negl_under_floors (H : HybridForkingFamily)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = (H.classical).solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = (H.pq).solverAdv)
    (hCnegC : Negl (H.classical).invChal) (hCnegP : Negl (H.pq).invChal)
    (hfloor : DLHardQuantShape dlSolverOf ∨ MSISHardQuantShape msisSolverOf) :
    Negl H.hybridForgerAdv := by
  rcases hfloor with hdl | hmsis
  · have hc : Negl (H.classical).forgerAdv :=
      ucForger_negl_of_dl (H.classical) dlSolverOf sc hsc hdl hCnegC
    exact negl_of_le H.hybridForgerAdv_nonneg H.hybridForgerAdv_le_classical hc
  · have hp : Negl (H.pq).forgerAdv :=
      ucForger_negl_of_msis (H.pq) msisSolverOf sp hsp hmsis hCnegP
    exact negl_of_le H.hybridForgerAdv_nonneg H.hybridForgerAdv_le_pq hp

/-! ### Non-vacuity — the "either" is load-bearing on REAL advantages. -/

/-- **ONE SECURE COMPONENT** hybrid: classical accepts NOTHING (`accC ≡ false`), pq is the broken `exampleAcc`
(`2/5` advantage). The conjunction is `false && _ = false`, so the hybrid advantage is `0`. -/
def secureLeftHybrid : HybridForkingFamily where
  Chal := fun _ => ZMod 5
  World := fun _ => Unit
  chalRing := fun _ => inferInstance
  chalNorm := fun _ => trivNorm (ZMod 5)
  chalFin := fun _ => inferInstance
  chalDec := fun _ => inferInstance
  worldFin := fun _ => inferInstance
  accC := fun _ _ _ => false
  accP := fun _ => exampleAcc
  worldPos := fun _ => by decide
  chalPos := fun _ => by decide

/-- **(TOOTH — one secure component blocks the hybrid.)** `secureLeftHybrid`'s advantage is the constant `0`
— the secure classical half `false` collapses the conjunction, even though the pq half is fully broken.
The real-advantage mirror of `HybridCombiner.hybrid_secure_via_left`. -/
theorem secureLeftHybrid_forgerAdv_zero : secureLeftHybrid.hybridForgerAdv = fun _ => (0 : ℝ) := by
  funext l
  show winProb (fun p : Unit × ZMod 5 => (false && exampleAcc p.1 p.2)) = 0
  simp only [Bool.false_and]
  exact winProb_bot

/-- **THE SECURE HYBRID REALIZES** — `Negl` advantage from the single secure component. -/
theorem secureLeftHybrid_negl : Negl secureLeftHybrid.hybridForgerAdv := by
  rw [secureLeftHybrid_forgerAdv_zero]; exact negl_zero

/-- **BOTH COMPONENTS BROKEN** hybrid: `accC = accP = exampleAcc`, each with `2/5` advantage. The conjunction
`exampleAcc && exampleAcc = exampleAcc` keeps the `2/5` advantage — a broken hybrid. -/
def bothBrokenHybrid : HybridForkingFamily where
  Chal := fun _ => ZMod 5
  World := fun _ => Unit
  chalRing := fun _ => inferInstance
  chalNorm := fun _ => trivNorm (ZMod 5)
  chalFin := fun _ => inferInstance
  chalDec := fun _ => inferInstance
  worldFin := fun _ => inferInstance
  accC := fun _ => exampleAcc
  accP := fun _ => exampleAcc
  worldPos := fun _ => by decide
  chalPos := fun _ => by decide

/-- The both-broken hybrid's advantage is the constant `2/5`. -/
theorem bothBrokenHybrid_forgerAdv : bothBrokenHybrid.hybridForgerAdv = fun _ => (2 / 5 : ℝ) := by
  funext l
  letI : ShortNorm (ZMod 5) := trivNorm (ZMod 5)
  show winProb (fun p : Unit × ZMod 5 => (exampleAcc p.1 p.2 && exampleAcc p.1 p.2)) = 2 / 5
  simp only [Bool.and_self]
  rw [winProb_prod_eq_advantage exampleAcc, advantage_example_eq]
  norm_num

/-- **THE LOAD-BEARING TOOTH — both broken ⇒ NON-negligible hybrid advantage.** With BOTH components broken
(`2/5` each), the hybrid advantage is the constant `2/5`, NOT negligible. So the `DLHardQuantShape ∨ MSISHardQuantShape`
hypothesis of `hybrid_forger_negl_under_floors` is load-bearing: with neither floor holding the hybrid genuinely
fails. The real-advantage mirror of `HybridCombiner.hybrid_broken_not_euf`. -/
theorem bothBrokenHybrid_not_negl : ¬ Negl bothBrokenHybrid.hybridForgerAdv := by
  rw [bothBrokenHybrid_forgerAdv]
  exact not_negl_const_pos (by norm_num)

/-! ## §2 — THRESHOLD (concurrent / adaptive TS-UF-0), quantitative. -/

/-- **The THRESHOLD forger advantage** — the concurrent TS-UF-0 forger's advantage ensemble. In
`HermineTSUF`'s `§ProbForking` finite counting-probability model, the TS-UF-0 forger (static `≤ thr−1`
corruption + concurrent signing oracle + fresh forgery) IS a `ForkingFamily`, its advantage `forgerAdv` and
its derived MSIS-solver advantage `solverAdv` the objects the forking bound governs. This names that
advantage as the threshold forger's. -/
noncomputable def thresholdForgerAdv (F : ForkingFamily) : ℕ → ℝ := F.forgerAdv

/-- **THE THRESHOLD REDUCTION, QUANTITATIVE — `Negl thresholdForgerAdv` under `MSISHardQuantShape`.** The
concurrent TS-UF-0 forger's advantage is negligible whenever its derived forking solver is quantitatively
MSIS-hard and the challenge space grows — packaging `ProbCrypto.forking_reduces_against_floor` at the threshold
forger. This is `HermineTSUF.concurrent_ts_uf_0_reduces` (forking→MSIS) lifted from a Boolean implication to a
genuine advantage-inequality against the quantitative floor. -/
theorem threshold_forger_negl_of_msis {Sv : Type*} (F : ForkingFamily)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuantShape solverAdvOf) (hCneg : Negl F.invChal) :
    Negl (thresholdForgerAdv F) :=
  forking_reduces_against_floor F solverAdvOf s hs hfloor hCneg

/-- **THE ADAPTIVE THRESHOLD REDUCTION — the erasure/adaptive-corruption term carried ADDITIVELY.** An
adaptive TS-UF-0 forger (adaptive corruption with secure erasure) has advantage bounded by the static-forking
advantage PLUS a statistical `erasureTerm` (the adaptive-corruption simulation cost / erasure gap). If the base
forger advantage is negligible (via the MSIS floor) and the erasure term is negligible, their sum is negligible
(`negl_add`), and the adaptive advantage — dominated by it — is negligible (`negl_of_le`). The extra adaptive
layer is carried through the `Negl` algebra, not swept under the rug. -/
theorem adaptive_threshold_negl_of_msis {Sv : Type*} (F : ForkingFamily)
    (erasureTerm adaptiveAdv : Ensemble)
    (hnn : ∀ n, 0 ≤ adaptiveAdv n)
    (hbound : ∀ n, adaptiveAdv n ≤ F.forgerAdv n + erasureTerm n)
    (herasure : Negl erasureTerm)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuantShape solverAdvOf) (hCneg : Negl F.invChal) :
    Negl adaptiveAdv := by
  have hbase : Negl F.forgerAdv := forking_reduces_against_floor F solverAdvOf s hs hfloor hCneg
  have hsum : Negl (fun n => F.forgerAdv n + erasureTerm n) := negl_add hbase herasure
  exact negl_of_le hnn hbound hsum

/-! ### Non-vacuity — the threshold reduction fires, and the floor is load-bearing. -/

/-- **(FIRES — the threshold reduction runs end-to-end.)** The never-accepting super-polynomial-challenge
`zeroFamily` is a TS-UF-0 forger with `forgerAdv ≡ 0`, negligible: the reduction concludes `Negl
thresholdForgerAdv` from the (trivial) MSIS floor and the growing challenge set. -/
theorem zeroFamily_threshold_negl : Negl (thresholdForgerAdv zeroFamily) :=
  threshold_forger_negl_of_msis zeroFamily (fun _ : Unit => (fun _ => (0 : ℝ))) ()
    zeroFamily_solverAdv_zero.symm (fun _ => negl_zero) zeroFamily_invChal_negl

/-- **(FIRES — the ADAPTIVE reduction runs, erasure term carried additively.)** Base forger `zeroFamily`
(`forgerAdv ≡ 0`), erasure term `2⁻ⁿ` (negligible), adaptive advantage `2⁻ⁿ⁻¹ ≤ 0 + 2⁻ⁿ`: the adaptive
threshold advantage is negligible, the erasure term threaded through `negl_add`. -/
theorem adaptive_threshold_fires :
    Negl (fun n : ℕ => 1 / (2 : ℝ) ^ (n + 1)) := by
  refine adaptive_threshold_negl_of_msis zeroFamily (fun n => 1 / (2 : ℝ) ^ n)
    (fun n => 1 / (2 : ℝ) ^ (n + 1)) (fun n => by positivity) (fun n => ?_) negl_two_pow
    (fun _ : Unit => (fun _ => (0 : ℝ))) () zeroFamily_solverAdv_zero.symm
    (fun _ => negl_zero) zeroFamily_invChal_negl
  have h0 : (0 : ℝ) ≤ zeroFamily.forgerAdv n := zeroFamily.forgerAdv_nonneg n
  have hle : (1 : ℝ) / 2 ^ (n + 1) ≤ 1 / 2 ^ n := by
    apply one_div_le_one_div_of_le (by positivity)
    rw [pow_succ]; nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) n]
  linarith [h0, hle]

/-- **THE FLOOR IS LOAD-BEARING** — the const-`2/5` threshold forger's derived MSIS solver advantage is
`≥ 2/25`, NON-negligible (`const25_forger_breaks_floor`). So no `MSISHardQuantShape` floor can hold for it, and
`threshold_forger_negl_of_msis` genuinely could not fire — the quantitative floor is exactly what buys the
threshold reduction. -/
theorem const25_threshold_breaks_floor : ¬ Negl const25Family.solverAdv := const25_forger_breaks_floor

/-! ## §3 — UC DISJUNCTIVE BUNDLING: `Negl advₑ` under `DLHardQuantShape ∨ MSISHardQuantShape`. -/

/-- **UC REALIZATION UNDER EITHER FLOOR — the "grounded in one floor" residual, closed.** The environment's
distinguishing advantage `advₑ` is negligible whenever it is bounded ABOVE by BOTH a DL-leg forger family
`Fc` and an MSIS-leg forger family `Fp`, and EITHER floor holds (`DLHardQuantShape dlSolverOf ∨ MSISHardQuantShape
msisSolverOf`). Case-split the disjunction: each leg discharges its family's forger advantage
(`ucForger_negl_of_dl`/`_of_msis`), and `advₑ` — dominated by it — is negligible. This extends
`UcSignatureQuant.computational_uc_realizes` (single MSIS floor) to the hybrid disjunction: the UC realization
is now grounded in EITHER the classical or the pq floor, matching the hybrid combiner. -/
theorem uc_realizes_disjunctive (advE : Ensemble) (Fc Fp : ForkingFamily)
    (hnn : ∀ n, 0 ≤ advE n)
    (hleC : ∀ n, advE n ≤ Fc.forgerAdv n) (hleP : ∀ n, advE n ≤ Fp.forgerAdv n)
    {Sc Sp : Type*}
    (dlSolverOf : Sc → Ensemble) (sc : Sc) (hsc : dlSolverOf sc = Fc.solverAdv)
    (msisSolverOf : Sp → Ensemble) (sp : Sp) (hsp : msisSolverOf sp = Fp.solverAdv)
    (hCnegC : Negl Fc.invChal) (hCnegP : Negl Fp.invChal)
    (hfloor : DLHardQuantShape dlSolverOf ∨ MSISHardQuantShape msisSolverOf) :
    Negl advE := by
  rcases hfloor with hdl | hmsis
  · have hc : Negl Fc.forgerAdv := ucForger_negl_of_dl Fc dlSolverOf sc hsc hdl hCnegC
    exact negl_of_le hnn hleC hc
  · have hp : Negl Fp.forgerAdv := ucForger_negl_of_msis Fp msisSolverOf sp hsp hmsis hCnegP
    exact negl_of_le hnn hleP hp

/-! ### Non-vacuity — realized under either floor, and the disjunction is load-bearing. -/

/-- **(FIRES — UC realizes under either floor.)** With `advₑ ≡ 0` (bounded by every family's advantage) and
BOTH legs the never-accepting `zeroFamily`, the disjunctive realization gives `Negl advₑ` — here through the
DL leg (`Or.inl`), a trivial DL floor. The positive pole of the bundled realization. -/
theorem uc_disjunctive_fires : Negl (fun _ : ℕ => (0 : ℝ)) :=
  uc_realizes_disjunctive (fun _ => 0) zeroFamily zeroFamily
    (fun _ => le_refl 0) (fun n => zeroFamily.forgerAdv_nonneg n)
    (fun n => zeroFamily.forgerAdv_nonneg n)
    (fun _ : Unit => (fun _ => (0 : ℝ))) () zeroFamily_solverAdv_zero.symm
    (fun _ : Unit => (fun _ => (0 : ℝ))) () zeroFamily_solverAdv_zero.symm
    zeroFamily_invChal_negl zeroFamily_invChal_negl
    (Or.inl (fun _ => negl_zero))

/-- **THE DISJUNCTION IS LOAD-BEARING** — the const-`2/5` distinguishing advantage is NOT negligible, and its
derived solver breaks EITHER floor (`const25_forger_breaks_floor`). So with NEITHER floor holding the UC
realization genuinely fails — `uc_realizes_disjunctive` needs at least one of the two floors, exactly the
hybrid guarantee. -/
theorem uc_disjunctive_bites : ¬ Negl const25Family.forgerAdv := by
  rw [const25_forgerAdv]
  exact not_negl_const_pos (by norm_num)

#assert_all_clean [
  winProb_le_of_imp,
  negl_of_le,
  HybridForkingFamily.hybridForgerAdv_nonneg,
  HybridForkingFamily.hybridForgerAdv_le_classical,
  HybridForkingFamily.hybridForgerAdv_le_pq,
  hybrid_forger_negl_under_floors,
  secureLeftHybrid_forgerAdv_zero,
  secureLeftHybrid_negl,
  bothBrokenHybrid_forgerAdv,
  bothBrokenHybrid_not_negl,
  threshold_forger_negl_of_msis,
  adaptive_threshold_negl_of_msis,
  zeroFamily_threshold_negl,
  adaptive_threshold_fires,
  const25_threshold_breaks_floor,
  uc_realizes_disjunctive,
  uc_disjunctive_fires,
  uc_disjunctive_bites
]

end Dregg2.Crypto.HybridThresholdQuant
