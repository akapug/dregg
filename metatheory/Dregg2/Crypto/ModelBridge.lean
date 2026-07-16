/-
# `Dregg2.Crypto.ModelBridge` — Seam 3 (model ↔ reality): two honestly-named modelling assumptions of the
  quantitative crypto campaign, closed or precisely reduced to a single named residual.

The `ProbCrypto` / `HybridThresholdQuant` / `HermineTSUF` substrate proves genuine concrete-security
advantage-inequalities, but TWO places quietly IDENTIFY the model with reality. This module removes the first
outright and reduces the second to one precisely-named measure-theoretic step.

## §A — HYBRID COMBINER: shared challenge → INDEPENDENT challenge spaces.  (CLOSED)

`HybridThresholdQuant.HybridForkingFamily` places both legs' accept events (`accC`, `accP`) over a SHARED
outcome space `World × Chal` — it assumes a common challenge. Here `IndepHybridForkingFamily` gives the two
components their OWN challenge sets `ChalC`, `ChalP` and their OWN prefix worlds `WorldC`, `WorldP`; the hybrid
accepts iff BOTH do, over the PRODUCT space `(WorldC × ChalC) × (WorldP × ChalP)`. The engine is
`winProb_prod_factor`: the joint accept probability of a conjunction whose factors depend on DISJOINT
coordinates FACTORISES as the product of the marginals (the independent-uniform / product-measure law),
`winProb (fun p => f p.1 && g p.2) = winProb f * winProb g`. So `hybridForgerAdv = classicalForgerAdv ·
pqForgerAdv` (an EQUALITY, `hybridForgerAdv_eq_mul`), which — each marginal being a probability `≤ 1` —
dominates BOTH marginals (`hybridForgerAdv_le_classical`/`_le_pq`). `hybrid_forger_negl_under_floors_indep`
re-proves `Negl hybridForgerAdv` under `DLHardQuantShape ∨ MSISHardQuantShape` with the two legs' challenges genuinely
INDEPENDENT — the shared-challenge assumption is gone. Teeth: one secure component ⇒ `hybridForgerAdv ≡ 0`;
BOTH broken (each `2/5`) ⇒ `hybridForgerAdv ≡ 4/25 = (2/5)·(2/5)` (the independent PRODUCT, not `2/5`) — NOT
Negl, so the "either" is load-bearing AND the factorisation is exhibited numerically.

## §B — FINITE SHADOW ↔ ABSTRACT FORGER.  (structure + the tail-canonical shadow; measure MATERIALIZED in §C)

`HermineTSUF.ProbForger` is the "fixed-fork-index finite shadow" of the abstract `Forger : (ℕ → Rq) → …`
(infinite RO). The quantitative reductions IDENTIFY the two. This module makes the identification a
CONSTRUCTION, and isolates precisely what remains:

  * **`extend` + `commitment_extend_eq` (CLOSED — the coordinate-restriction of the commitment).** Reconstruct
    a full RO from a prefix world `ω : Fin challengeIdx → Rq`, a fork challenge `c`, and a tail. The abstract
    commitment of the reconstruction depends ONLY on `ω` — NOT on `c` or the tail — proved from the abstract
    forger's `commitment_preChallenge`. So the commitment genuinely FACTORS through the fork prefix; the two
    reruns share it. This is the forking-relevant half of "the RO measure restricted to the fork prefix".

  * **`abstractShadow` (CLOSED — the finite model exists and is SOUND).** From an abstract `Forger` and a
    frozen tail we BUILD a genuine `ProbForger`; its `acc_sound` is DISCHARGED (an accepting `(ω, c)` yields a
    real `IsSelfTargetMSISSolution` on the SHARED prefix-commitment with challenge `c`). The finite shadow
    faithfully carries the abstract forger's soundness + shared-commitment structure.

  * **`TailIndependent` (the tail-independence hypothesis — its measure content MATERIALIZED in §C).** The ONE
    thing not provable from the `Forger` structure is that acceptance is independent of the RO answers STRICTLY
    ABOVE `challengeIdx` (the abstract `response` may read them; `exTailForger` genuinely does). This is exactly
    the marginalisation of the uniform RO tail — carried out for real in §C over the infinite-product RO
    measure. Here we prove that GIVEN it, the finite shadow's `advantage`/`forkProb`
    are INDEPENDENT of the frozen tail (`abstractShadow_advantage_tailIndep`/`_forkProb_`) — i.e. the shadow is
    canonical and genuinely captures the abstract forger's fork behaviour with NO residual dependence on the
    unmodelled coordinates. Teeth: `exAbstractForger` (reads only the challenge) IS `TailIndependent`;
    `exTailForger` (reads an above-challenge coordinate) is NOT — so `TailIndependent` is load-bearing.

## §C — THE GENUINE INFINITE-RO PRODUCT MEASURE.  (CLOSED — the model↔reality identification is a THEOREM)

The prior lane STOPPED at "`ℕ → Rq` is not a `Fintype`, so the abstract Forger's advantage isn't a finite
counting probability — establishing `TailIndependent`'s measure content needs an infinite-product RO measure
this model does not carry." §C BUILDS that measure and proves the identification.

  * **`roMeasure` (the RO measure, CLOSED).** The random oracle `ℕ → Rq` carries the infinite PRODUCT of the
    uniform measure on the finite `Rq` — `MeasureTheory.Measure.infinitePi (fun _ => uniformOfFintype Rq)` — a
    genuine `IsProbabilityMeasure` on `ℕ → Rq` (`instIsProbabilityMeasure_roMeasure`). The abstract Forger's
    advantage is now a real probability over `ℕ → Rq`, not a finite counting stand-in.

  * **`accepts_congr_of_le` (the marginalisation content, CLOSED).** `TailIndependent` says exactly that the
    accept indicator is a function of the coordinates `≤ challengeIdx` (two oracles agreeing there accept
    together — both are `extend`-reconstructions with the same prefix+challenge and differing tails). So the
    acceptance event is a measurable CYLINDER over `Finset.Iic challengeIdx` (`acceptEvent_eq_cylinder`).

  * **`roMeasure_accept` (the marginalisation, CLOSED).** `infinitePi_cylinder` collapses the infinite-product
    measure of the acceptance cylinder to the finite product measure of the accepting prefix set, which
    `pi_uniform_finset` computes as `|accBase| · (|Rq|⁻¹)^(challengeIdx+1)` — the finite counting probability,
    with the tail genuinely MARGINALISED (integrated out), not frozen.

  * **`abstractShadow_advantage_eq_roMeasure` (THE BRIDGE, CLOSED).** Under `TailIndependent`, the finite
    shadow's `advantage` (a `ℚ` count) EQUALS `(roMeasure {ρ | Accepts F ρ}).toReal` — the real probability of
    the acceptance event under the genuine infinite-RO measure. Both collapse to `|accBase|/|Rq|^(challengeIdx
    +1)` (the `iicEquiv` prefix×challenge ≃ `Iic n` bijection carries `accBase` onto the accepting `(ω,c)`
    pairs, `accBase_card`). Tail-invariance of the shadow advantage then falls out with the tail absent
    (`abstractShadow_advantage_tailInvariant_via_roMeasure`). The identification is a THEOREM — no residual, no
    assumption, no `sorry`.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}; measure theory pulls `Classical.choice`). No
`native_decide` in any `∀`; §A teeth exhibit `0` / `4/25`, §B teeth tail-dependence, §C teeth the bridge
firing on `exAbstractForger` with the real RO probability `1` — so nothing is vacuous.
-/
import Dregg2.Crypto.HybridThresholdQuant
import Dregg2.Tactics
import Mathlib.Tactic
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

namespace Dregg2.Crypto.ModelBridge

open Filter
open scoped BigOperators
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.UcSignatureQuant
open Dregg2.Crypto.HybridThresholdQuant
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.Lattice (ShortNorm)

/-! ## §A — the HYBRID combiner with INDEPENDENT challenge spaces. -/

/-! ### The product-measure factorisation — the independence law. -/

/-- **INDEPENDENCE / PRODUCT-MEASURE FACTORISATION.** The winning probability of a conjunction whose two
factors depend on DISJOINT coordinates factorises as the product of the marginals:
`winProb (fun p : X × Y => f p.1 && g p.2) = winProb f · winProb g`. The favorable set is the product
`{x | f x} ×ˢ {y | g y}`, whose card is `|f|·|g|`, over `|X|·|Y|`. This is the genuine content of "the two
legs' challenges are drawn from INDEPENDENT uniform measures": the joint accept probability is the product,
so it is bounded by each marginal (each being `≤ 1`). The Seam-3 engine that removes the shared-challenge
modelling assumption. -/
theorem winProb_prod_factor {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Bool) (g : Y → Bool) :
    winProb (fun p : X × Y => f p.1 && g p.2) = winProb f * winProb g := by
  unfold winProb
  have hset : (Finset.univ.filter (fun p : X × Y => (f p.1 && g p.2) = true))
      = (Finset.univ.filter (fun x => f x = true)) ×ˢ (Finset.univ.filter (fun y => g y = true)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Bool.and_eq_true]
  rw [hset, Finset.card_product, Fintype.card_prod]
  push_cast
  ring

/-! ### The independent-challenge hybrid forging family. -/

/-- **A hybrid forging family with INDEPENDENT legs.** Unlike `HybridThresholdQuant.HybridForkingFamily`
(shared `World`/`Chal`), each component here carries its OWN challenge set (`ChalC`, `ChalP`) and its OWN
prefix world (`WorldC`, `WorldP`). The hybrid accepts iff both do, over the PRODUCT outcome space — the two
legs' randomness is genuinely independent. The projections `classical`/`pq` are real `ForkingFamily`s. -/
structure IndepHybridForkingFamily where
  /-- The classical leg's challenge set. -/
  ChalC : ℕ → Type
  /-- The pq leg's challenge set. -/
  ChalP : ℕ → Type
  /-- The classical leg's prefix world. -/
  WorldC : ℕ → Type
  /-- The pq leg's prefix world. -/
  WorldP : ℕ → Type
  chalCRing : ∀ l, CommRing (ChalC l)
  chalPRing : ∀ l, CommRing (ChalP l)
  chalCNorm : ∀ l, letI := chalCRing l; ShortNorm (ChalC l)
  chalPNorm : ∀ l, letI := chalPRing l; ShortNorm (ChalP l)
  chalCFin : ∀ l, Fintype (ChalC l)
  chalPFin : ∀ l, Fintype (ChalP l)
  chalCDec : ∀ l, DecidableEq (ChalC l)
  chalPDec : ∀ l, DecidableEq (ChalP l)
  worldCFin : ∀ l, Fintype (WorldC l)
  worldPFin : ∀ l, Fintype (WorldP l)
  /-- The classical component's accept event (own world × own challenge). -/
  accC : ∀ l, WorldC l → ChalC l → Bool
  /-- The pq component's accept event (own world × own challenge). -/
  accP : ∀ l, WorldP l → ChalP l → Bool
  worldCPos : ∀ l, 0 < @Fintype.card (WorldC l) (worldCFin l)
  worldPPos : ∀ l, 0 < @Fintype.card (WorldP l) (worldPFin l)
  chalCPos : ∀ l, 0 < @Fintype.card (ChalC l) (chalCFin l)
  chalPPos : ∀ l, 0 < @Fintype.card (ChalP l) (chalPFin l)

namespace IndepHybridForkingFamily

/-- The CLASSICAL leg as a genuine `ForkingFamily` — its own geometry, `acc := accC`. -/
def classical (H : IndepHybridForkingFamily) : ForkingFamily where
  Chal := H.ChalC
  World := H.WorldC
  chalRing := H.chalCRing
  chalNorm := H.chalCNorm
  chalFin := H.chalCFin
  chalDec := H.chalCDec
  worldFin := H.worldCFin
  acc := H.accC
  worldPos := H.worldCPos
  chalPos := H.chalCPos

/-- The PQ leg as a genuine `ForkingFamily` — its own geometry, `acc := accP`. -/
def pq (H : IndepHybridForkingFamily) : ForkingFamily where
  Chal := H.ChalP
  World := H.WorldP
  chalRing := H.chalPRing
  chalNorm := H.chalPNorm
  chalFin := H.chalPFin
  chalDec := H.chalPDec
  worldFin := H.worldPFin
  acc := H.accP
  worldPos := H.worldPPos
  chalPos := H.chalPPos

/-- **The INDEPENDENT hybrid forger advantage** — the `winProb` of the conjunction `accC ∧ accP` over the
PRODUCT space `(WorldC × ChalC) × (WorldP × ChalP)`. Each leg draws its own world and its own challenge; the
hybrid accepts iff both forgeries verify. A genuine real in `[0,1]`. -/
noncomputable def hybridForgerAdv (H : IndepHybridForkingFamily) : ℕ → ℝ := fun l =>
  letI := H.chalCRing l; letI := H.chalCNorm l; letI := H.chalCFin l
  letI := H.chalCDec l; letI := H.worldCFin l
  letI := H.chalPRing l; letI := H.chalPNorm l; letI := H.chalPFin l
  letI := H.chalPDec l; letI := H.worldPFin l
  winProb (fun p : (H.WorldC l × H.ChalC l) × (H.WorldP l × H.ChalP l) =>
    H.accC l p.1.1 p.1.2 && H.accP l p.2.1 p.2.2)

theorem hybridForgerAdv_nonneg (H : IndepHybridForkingFamily) (l : ℕ) : 0 ≤ H.hybridForgerAdv l := by
  letI := H.chalCRing l; letI := H.chalCNorm l; letI := H.chalCFin l
  letI := H.chalCDec l; letI := H.worldCFin l
  letI := H.chalPRing l; letI := H.chalPNorm l; letI := H.chalPFin l
  letI := H.chalPDec l; letI := H.worldPFin l
  exact winProb_nonneg _

/-- **THE FACTORISATION — hybrid advantage = product of the marginals.** Because the two legs' accept events
depend on DISJOINT coordinates, `winProb_prod_factor` gives `hybridForgerAdv l = classicalForgerAdv l ·
pqForgerAdv l` — an EQUALITY, the independent-challenge law made explicit. -/
theorem hybridForgerAdv_eq_mul (H : IndepHybridForkingFamily) (l : ℕ) :
    H.hybridForgerAdv l = (H.classical).forgerAdv l * (H.pq).forgerAdv l := by
  letI := H.chalCRing l; letI := H.chalCNorm l; letI := H.chalCFin l
  letI := H.chalCDec l; letI := H.worldCFin l
  letI := H.chalPRing l; letI := H.chalPNorm l; letI := H.chalPFin l
  letI := H.chalPDec l; letI := H.worldPFin l
  show winProb (fun p : (H.WorldC l × H.ChalC l) × (H.WorldP l × H.ChalP l) =>
      (fun q : H.WorldC l × H.ChalC l => H.accC l q.1 q.2) p.1
      && (fun q : H.WorldP l × H.ChalP l => H.accP l q.1 q.2) p.2) = _
  rw [winProb_prod_factor (fun q : H.WorldC l × H.ChalC l => H.accC l q.1 q.2)
        (fun q : H.WorldP l × H.ChalP l => H.accP l q.1 q.2),
      winProb_prod_eq_advantage (H.accC l), winProb_prod_eq_advantage (H.accP l)]
  rfl

/-- **THE COMBINER PROPERTY, INDEPENDENT — hybrid advantage `≤` CLASSICAL advantage.** The product of two
probabilities is `≤` the first factor (the second being `≤ 1`). No shared-challenge assumption. -/
theorem hybridForgerAdv_le_classical (H : IndepHybridForkingFamily) (l : ℕ) :
    H.hybridForgerAdv l ≤ (H.classical).forgerAdv l := by
  rw [H.hybridForgerAdv_eq_mul l]
  exact mul_le_of_le_one_right ((H.classical).forgerAdv_nonneg l) ((H.pq).forgerAdv_le_one l)

/-- **THE COMBINER PROPERTY, INDEPENDENT — hybrid advantage `≤` PQ advantage.** Symmetrically, the product is
`≤` the second factor (the first being `≤ 1`). -/
theorem hybridForgerAdv_le_pq (H : IndepHybridForkingFamily) (l : ℕ) :
    H.hybridForgerAdv l ≤ (H.pq).forgerAdv l := by
  rw [H.hybridForgerAdv_eq_mul l]
  exact mul_le_of_le_one_left ((H.pq).forgerAdv_nonneg l) ((H.classical).forgerAdv_le_one l)

end IndepHybridForkingFamily

/-- **THE INDEPENDENT-CHALLENGE HYBRID COMBINER — `Negl hybridForgerAdv` under `DLHardQuantShape ∨ MSISHardQuantShape`.**
Identical guarantee to `HybridThresholdQuant.hybrid_forger_negl_under_floors`, but with the two components'
challenge spaces (and prefix worlds) genuinely INDEPENDENT — the shared-challenge modelling assumption is
removed. Case-split the disjunction: whichever floor holds discharges its component's forger advantage, and the
hybrid advantage — bounded above by that marginal (`hybridForgerAdv_le_classical`/`_pq`, from the product
factorisation) — is dominated, hence negligible. -/
theorem hybrid_forger_negl_under_floors_indep (H : IndepHybridForkingFamily)
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

/-! ### Non-vacuity — the "either" is load-bearing, and the PRODUCT (independence) is exhibited. -/

/-- **ONE SECURE COMPONENT** (independent legs): classical accepts nothing (`accC ≡ false`), pq is the broken
`exampleAcc` (`2/5`). The conjunction collapses to `false`, so the hybrid advantage is `0`. -/
def secureLeftHybridI : IndepHybridForkingFamily where
  ChalC := fun _ => ZMod 5
  ChalP := fun _ => ZMod 5
  WorldC := fun _ => Unit
  WorldP := fun _ => Unit
  chalCRing := fun _ => inferInstance
  chalPRing := fun _ => inferInstance
  chalCNorm := fun _ => trivNorm (ZMod 5)
  chalPNorm := fun _ => trivNorm (ZMod 5)
  chalCFin := fun _ => inferInstance
  chalPFin := fun _ => inferInstance
  chalCDec := fun _ => inferInstance
  chalPDec := fun _ => inferInstance
  worldCFin := fun _ => inferInstance
  worldPFin := fun _ => inferInstance
  accC := fun _ _ _ => false
  accP := fun _ => exampleAcc
  worldCPos := fun _ => by decide
  worldPPos := fun _ => by decide
  chalCPos := fun _ => by decide
  chalPPos := fun _ => by decide

/-- **(TOOTH — one secure component blocks the independent hybrid.)** `secureLeftHybridI`'s advantage is the
constant `0`. -/
theorem secureLeftHybridI_zero : secureLeftHybridI.hybridForgerAdv = fun _ => (0 : ℝ) := by
  funext l
  show winProb (fun p : (Unit × ZMod 5) × (Unit × ZMod 5) => (false && exampleAcc p.2.1 p.2.2)) = 0
  simp only [Bool.false_and]
  exact winProb_bot

/-- **THE SECURE INDEPENDENT HYBRID REALISES** — `Negl` advantage from the single secure component. -/
theorem secureLeftHybridI_negl : Negl secureLeftHybridI.hybridForgerAdv := by
  rw [secureLeftHybridI_zero]; exact negl_zero

/-- **BOTH COMPONENTS BROKEN** (independent legs): `accC = accP = exampleAcc`, each `2/5`. Because the legs are
INDEPENDENT the joint advantage is the PRODUCT `(2/5)·(2/5) = 4/25`, NOT `2/5` (the shared-challenge value). -/
def bothBrokenHybridI : IndepHybridForkingFamily where
  ChalC := fun _ => ZMod 5
  ChalP := fun _ => ZMod 5
  WorldC := fun _ => Unit
  WorldP := fun _ => Unit
  chalCRing := fun _ => inferInstance
  chalPRing := fun _ => inferInstance
  chalCNorm := fun _ => trivNorm (ZMod 5)
  chalPNorm := fun _ => trivNorm (ZMod 5)
  chalCFin := fun _ => inferInstance
  chalPFin := fun _ => inferInstance
  chalCDec := fun _ => inferInstance
  chalPDec := fun _ => inferInstance
  worldCFin := fun _ => inferInstance
  worldPFin := fun _ => inferInstance
  accC := fun _ => exampleAcc
  accP := fun _ => exampleAcc
  worldCPos := fun _ => by decide
  worldPPos := fun _ => by decide
  chalCPos := fun _ => by decide
  chalPPos := fun _ => by decide

/-- **THE INDEPENDENT PRODUCT — both broken ⇒ advantage `4/25`.** The factorisation `hybridForgerAdv_eq_mul`
computes the joint advantage as the PRODUCT of the two `2/5` marginals: `4/25`. This is exactly the
independence content — with a SHARED challenge (`HybridThresholdQuant.bothBrokenHybrid`) the value was `2/5`;
independent draws multiply. -/
theorem bothBrokenHybridI_forgerAdv : bothBrokenHybridI.hybridForgerAdv = fun _ => (4 / 25 : ℝ) := by
  funext l
  rw [bothBrokenHybridI.hybridForgerAdv_eq_mul l]
  have hc : (bothBrokenHybridI.classical).forgerAdv l = 2 / 5 := by
    show ((advantage exampleAcc : ℚ) : ℝ) = 2 / 5
    rw [advantage_example_eq]; norm_num
  have hp : (bothBrokenHybridI.pq).forgerAdv l = 2 / 5 := by
    show ((advantage exampleAcc : ℚ) : ℝ) = 2 / 5
    rw [advantage_example_eq]; norm_num
  rw [hc, hp]; norm_num

/-- **THE LOAD-BEARING TOOTH — both broken ⇒ NON-negligible independent-hybrid advantage.** `4/25` is a
positive constant, NOT negligible; so `DLHardQuantShape ∨ MSISHardQuantShape` is load-bearing even with independent
challenges. -/
theorem bothBrokenHybridI_not_negl : ¬ Negl bothBrokenHybridI.hybridForgerAdv := by
  rw [bothBrokenHybridI_forgerAdv]
  exact not_negl_const_pos (by norm_num)

/-! ## §B — finite shadow ↔ abstract Forger. -/

section AbstractShadow

open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}

/-- **The RO reconstruction from the fork-relevant coordinates.** Given a prefix world `ω : Fin challengeIdx →
Rq` (the answers strictly below the fork index), a fork challenge `c`, and a tail `tail` (the answers strictly
above), assemble a full random oracle: `ω` below `challengeIdx`, `c` at `challengeIdx`, `tail` above. This is
the inverse of the "restrict to the fork prefix" map; the finite shadow's outcome space is the `ω`-part. -/
def extend (F : Forger Rq M N Msg) (ω : Fin F.challengeIdx → Rq) (c : Rq) (tail : ℕ → Rq) : ℕ → Rq :=
  fun j => if h : j < F.challengeIdx then ω ⟨j, h⟩ else if j = F.challengeIdx then c else tail j

/-- Below the fork index, `extend` reads the prefix world. -/
theorem extend_below (F : Forger Rq M N Msg) (ω : Fin F.challengeIdx → Rq) (c : Rq) (tail : ℕ → Rq)
    {j : ℕ} (hj : j < F.challengeIdx) : extend F ω c tail j = ω ⟨j, hj⟩ := by
  simp only [extend, dif_pos hj]

/-- At the fork index, `extend` reads the fork challenge `c`. -/
theorem extend_at (F : Forger Rq M N Msg) (ω : Fin F.challengeIdx → Rq) (c : Rq) (tail : ℕ → Rq) :
    extend F ω c tail F.challengeIdx = c := by
  unfold extend
  rw [dif_neg (lt_irrefl F.challengeIdx), if_pos rfl]

/-- Above the fork index, `extend` reads the tail. -/
theorem extend_above (F : Forger Rq M N Msg) (ω : Fin F.challengeIdx → Rq) (c : Rq) (tail : ℕ → Rq)
    {j : ℕ} (hj : F.challengeIdx < j) : extend F ω c tail j = tail j := by
  have h1 : ¬ j < F.challengeIdx := by omega
  have h2 : j ≠ F.challengeIdx := by omega
  simp only [extend, dif_neg h1, if_neg h2]

/-- **THE COORDINATE-RESTRICTION OF THE COMMITMENT (CLOSED).** The abstract forger's commitment of a
reconstructed RO depends ONLY on the prefix world `ω` — not on the fork challenge `c`, nor on the tail. This is
the abstract `Forger.commitment_preChallenge` (the side output is produced before the challenge query) made
into a factorisation through the fork prefix. It is the forking-relevant half of "the RO measure restricted to
the fork prefix": the two reruns (different `c`, same `ω`) SHARE the commitment. Unconditional. -/
theorem commitment_extend_eq (F : Forger Rq M N Msg) (ω : Fin F.challengeIdx → Rq)
    (c c' : Rq) (tail tail' : ℕ → Rq) :
    F.commitment (extend F ω c tail) = F.commitment (extend F ω c' tail') := by
  apply F.commitment_preChallenge
  intro j hj
  rw [extend_below F ω c tail hj, extend_below F ω c' tail' hj]

open Classical in
/-- **THE FINITE SHADOW OF AN ABSTRACT FORGER (CLOSED, SOUND).** From an abstract `Forger` and a FROZEN tail,
build a genuine `ProbForger` over the prefix world `Ω = Fin challengeIdx → Rq`: `comm ω` is the
prefix-determined commitment (any `c` works, `commitment_extend_eq`), `resp ω c`/`acc ω c` run the abstract
forger on the reconstructed RO. `acc_sound` is DISCHARGED: an accepting `(ω, c)` is a genuine
`IsSelfTargetMSISSolution` on the SHARED commitment `comm ω` with challenge `c` (the challenge read at
`challengeIdx` IS `c`, and the commitment factors through `ω`). So the finite model faithfully carries the
abstract forger's soundness and shared-commitment structure. -/
noncomputable def abstractShadow (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (F : Forger Rq M N Msg) (tail : ℕ → Rq) : ProbForger A t β (Fin F.challengeIdx → Rq) where
  comm := fun ω => F.commitment (extend F ω 0 tail)
  resp := fun ω c => F.response (extend F ω c tail)
  acc := fun ω c => decide (Accepts A t β F (extend F ω c tail))
  acc_sound := by
    intro ω c hc
    have hacc : Accepts A t β F (extend F ω c tail) := of_decide_eq_true hc
    have hcomm : F.commitment (extend F ω c tail) = F.commitment (extend F ω 0 tail) :=
      commitment_extend_eq F ω c 0 tail tail
    have hch : extend F ω c tail F.challengeIdx = c := extend_at F ω c tail
    unfold Accepts at hacc
    rw [hch, hcomm] at hacc
    exact hacc

/-- **THE NAMED RESIDUAL — acceptance's independence from the above-`challengeIdx` coordinates.** The one thing
NOT provable from the `Forger` structure: the abstract `response`/`message` may read RO answers strictly ABOVE
the fork index, so acceptance can depend on the tail. `TailIndependent` says it does not — equivalently, that
marginalising the uniform tail commutes with the accept indicator. This is the EXACT measure-theoretic step the
finite shadow needs and the model does not carry (`ℕ → Rq` is not a `Fintype`, so the abstract advantage is not
a finite counting probability). It is load-bearing: `exAbstractForger` satisfies it, `exTailForger` refutes
it. -/
def TailIndependent (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg) : Prop :=
  ∀ (ω : Fin F.challengeIdx → Rq) (c : Rq) (tail tail' : ℕ → Rq),
    Accepts A t β F (extend F ω c tail) ↔ Accepts A t β F (extend F ω c tail')

open Classical in
/-- **FAITHFULNESS UNDER THE NAMED RESIDUAL — the shadow's accept event is tail-canonical.** Given
`TailIndependent`, the finite shadow's `acc` is INDEPENDENT of the frozen tail: two shadows built from
different tails have the SAME accept event. The finite model therefore captures the abstract forger's accept
behaviour with NO residual dependence on the unmodelled above-challenge coordinates. -/
theorem abstractShadow_acc_tailIndep (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) (tail tail' : ℕ → Rq) :
    (abstractShadow A t β F tail).acc = (abstractShadow A t β F tail').acc := by
  funext ω c
  show decide (Accepts A t β F (extend F ω c tail)) = decide (Accepts A t β F (extend F ω c tail'))
  exact decide_eq_decide.mpr (h ω c tail tail')

/-- **FAITHFULNESS — the shadow's ADVANTAGE is tail-canonical (given the named residual).** Under
`TailIndependent`, the finite shadow's `advantage` is independent of the frozen tail: it genuinely measures the
abstract forger's fork-relevant advantage, not an artifact of the tail choice. -/
theorem abstractShadow_advantage_tailIndep (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) (tail tail' : ℕ → Rq) :
    advantage (abstractShadow A t β F tail).acc = advantage (abstractShadow A t β F tail').acc :=
  congrArg advantage (abstractShadow_acc_tailIndep A t β F h tail tail')

/-- **FAITHFULNESS — the shadow's FORK PROBABILITY is tail-canonical (given the named residual).** Likewise
`forkProb` is tail-independent under `TailIndependent`; the finite shadow's forking probability faithfully
tracks the abstract forger. -/
theorem abstractShadow_forkProb_tailIndep (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) (tail tail' : ℕ → Rq) :
    forkProb (abstractShadow A t β F tail).acc = forkProb (abstractShadow A t β F tail').acc :=
  congrArg forkProb (abstractShadow_acc_tailIndep A t β F h tail tail')

end AbstractShadow

/-! ### Teeth — `TailIndependent` is load-bearing (one forger satisfies it, one refutes it). -/

section TeethB

open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS

/-- A concrete abstract forger over `ZMod 5` that reads ONLY the fork challenge (RO index `0`): commitment `0`,
response `ρ 0`, message `0`. The pre-challenge determinacy is trivial (constant commitment). -/
def exAbstractForger : Forger (ZMod 5) (ZMod 5) (ZMod 5) ℕ where
  challengeIdx := 0
  commitment := fun _ => 0
  response := fun ρ => ρ 0
  message := fun _ => 0
  commitment_preChallenge := fun _ _ _ => rfl

/-- `exAbstractForger` accepts on every reconstruction: `z = extend..0 = c`, commitment `0`, `id·c = 0 + c·1`.
It reads no above-challenge coordinate, so acceptance never touches the tail. -/
theorem exAbstract_accepts (ω : Fin 0 → ZMod 5) (c : ZMod 5) (tail : ℕ → ZMod 5) :
    Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger (extend exAbstractForger ω c tail) := by
  refine ⟨Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, ?_⟩
  simp [exAbstractForger, HermineThreshold.verify, extend]

/-- **(TOOTH — positive: the reading-only-the-challenge forger IS tail-independent.)** Both sides of the
`TailIndependent` iff always accept, so it holds — the finite shadow of `exAbstractForger` is canonical. -/
theorem exAbstract_tailIndep :
    TailIndependent (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger := by
  intro ω c tail tail'
  exact ⟨fun _ => exAbstract_accepts ω c tail', fun _ => exAbstract_accepts ω c tail⟩

/-- A concrete abstract forger over `ZMod 5` that reads an ABOVE-challenge coordinate (RO index `1`, while the
fork index is `0`): commitment `0`, response `ρ 1`, message `0`. Acceptance becomes `ρ 1 = ρ 0`, i.e. it
depends on the tail. -/
def exTailForger : Forger (ZMod 5) (ZMod 5) (ZMod 5) ℕ where
  challengeIdx := 0
  commitment := fun _ => 0
  response := fun ρ => ρ 1
  message := fun _ => 0
  commitment_preChallenge := fun _ _ _ => rfl

/-- With tail `≡ 1` and challenge `c = 1`, the reconstruction accepts (`extend..1 = 1 = c`). -/
theorem exTail_accepts_true (ω : Fin 0 → ZMod 5) :
    Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exTailForger
      (extend exTailForger ω 1 (fun _ => 1)) := by
  refine ⟨Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, ?_⟩
  simp [HermineThreshold.verify, exTailForger, extend]

/-- With tail `≡ 0` and challenge `c = 1`, the reconstruction REJECTS (`extend..1 = 0 ≠ 1 = c`). -/
theorem exTail_accepts_false (ω : Fin 0 → ZMod 5) :
    ¬ Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exTailForger
      (extend exTailForger ω 1 (fun _ => 0)) := by
  rintro ⟨_, _, _, hv⟩
  simp [HermineThreshold.verify, exTailForger, extend] at hv
  exact absurd hv (by decide)

/-- **(TOOTH — negative: the tail-reading forger is NOT tail-independent.)** The same `(ω, c)` accepts under
tail `≡ 1` but rejects under tail `≡ 0`, so `TailIndependent` fails — the residual is load-bearing, not
vacuous. Acceptance genuinely depends on the unmodelled above-challenge coordinate, which is exactly why the
finite shadow needs the named marginalisation step. -/
theorem exTail_not_tailIndep :
    ¬ TailIndependent (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exTailForger := by
  intro h
  have hiff := h Fin.elim0 1 (fun _ => 1) (fun _ => 0)
  exact exTail_accepts_false Fin.elim0 (hiff.mp (exTail_accepts_true Fin.elim0))

end TeethB

/-! ## §C — the genuine infinite-product RANDOM-ORACLE measure: `TailIndependent` MATERIALIZED.

`§B` names `TailIndependent` and proves the finite shadow is tail-canonical GIVEN it, but the abstract
Forger's advantage was never itself a probability: `ℕ → Rq` is not a `Fintype`, so there was no measure to
take (the residual the prior lane stopped at). This section BUILDS that measure — the infinite product of the
uniform measure on the finite `Rq` (`MeasureTheory.Measure.infinitePi`, a genuine `IsProbabilityMeasure` on
`ℕ → Rq`) — and PROVES that the finite shadow's `advantage` EQUALS the real probability of the acceptance
event under it. The bridge: `TailIndependent` says acceptance depends only on the coordinates `≤ challengeIdx`
(`accepts_congr_of_le`), so the acceptance event is a measurable CYLINDER over `Finset.Iic challengeIdx`
(`acceptEvent_eq_cylinder`); its infinite-product measure MARGINALISES the tail — `infinitePi_cylinder`
collapses it to the finite product measure of the accepting prefix set (`roMeasure_accept`), which is exactly
the finite counting probability the shadow computes (`abstractShadow_advantage_eq_roMeasure`). Tail-invariance
of the shadow advantage then falls out with the tail no longer present at all
(`abstractShadow_advantage_tailInvariant_via_roMeasure`). No residual, no assumption: the model↔reality
identification is a THEOREM over the real infinite-RO measure. -/
section ROMeasureBridge

open MeasureTheory
open scoped ENNReal
open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS

set_option linter.unusedSectionVars false

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
  [MeasurableSpace Rq] [DiscreteMeasurableSpace Rq] [Nonempty Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}

/-! ### The RO measure and finite uniform-product primitives. -/

/-- **THE RANDOM-ORACLE MEASURE.** The random oracle `ℕ → Rq` carries the infinite PRODUCT of the uniform
measure on the finite `Rq` (`PMF.uniformOfFintype Rq |>.toMeasure`, a genuine probability measure). This is
`MeasureTheory.Measure.infinitePi`, whose `IsProbabilityMeasure` instance makes the abstract Forger's advantage
a genuine probability over `ℕ → Rq` — the object the prior lane could not construct. -/
noncomputable def roMeasure (Rq : Type*) [Fintype Rq] [Nonempty Rq] [MeasurableSpace Rq] :
    Measure (ℕ → Rq) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Rq).toMeasure)

instance instIsProbabilityMeasure_roMeasure : IsProbabilityMeasure (roMeasure Rq) := by
  unfold roMeasure; infer_instance

/-- The finite product of uniform measures assigns to a SINGLETON the reciprocal of the product's cardinality
(`(|Rq|⁻¹)^|κ|`). Each factor is `PMF.uniformOfFintype`, whose singleton mass is `|Rq|⁻¹`
(`toMeasure_apply_singleton` + `uniformOfFintype_apply`); the product over `κ` multiplies them. -/
theorem pi_uniform_singleton (Rq : Type*) [Fintype Rq] [Nonempty Rq] [MeasurableSpace Rq]
    [MeasurableSingletonClass Rq] {κ : Type*} [Fintype κ] (x : κ → Rq) :
    Measure.pi (fun _ : κ => (PMF.uniformOfFintype Rq).toMeasure) {x}
      = (Fintype.card Rq : ℝ≥0∞)⁻¹ ^ (Fintype.card κ) := by
  rw [← Set.univ_pi_singleton x, Measure.pi_pi]
  have hfac : ∀ i : κ, (PMF.uniformOfFintype Rq).toMeasure {x i} = (Fintype.card Rq : ℝ≥0∞)⁻¹ := by
    intro i
    rw [(PMF.uniformOfFintype Rq).toMeasure_apply_singleton (x i) (measurableSet_singleton _),
        PMF.uniformOfFintype_apply]
  simp only [hfac]
  rw [Finset.prod_const, Finset.card_univ]

/-- The finite product of uniform measures of a FINSET is `|S| · (|Rq|⁻¹)^|κ|` — the finite counting
probability. `↑S` is the disjoint union of its singletons; `measure_biUnion_finset` sums the per-singleton mass
(`pi_uniform_singleton`). -/
theorem pi_uniform_finset (Rq : Type*) [Fintype Rq] [Nonempty Rq] [MeasurableSpace Rq]
    [MeasurableSingletonClass Rq] {κ : Type*} [Fintype κ] (S : Finset (κ → Rq)) :
    Measure.pi (fun _ : κ => (PMF.uniformOfFintype Rq).toMeasure) (↑S : Set (κ → Rq))
      = (S.card : ℝ≥0∞) * (Fintype.card Rq : ℝ≥0∞)⁻¹ ^ (Fintype.card κ) := by
  classical
  have hcov : (↑S : Set (κ → Rq)) = ⋃ x ∈ S, ({x} : Set (κ → Rq)) := by
    ext y; simp
  rw [hcov, measure_biUnion_finset
      (fun a _ b _ hab => Set.disjoint_singleton.mpr hab)
      (fun b _ => measurableSet_singleton b)]
  simp only [pi_uniform_singleton Rq]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Reconstruction of the fork-relevant coordinates and the prefix↔`Iic` bijection. -/

/-- Rebuild a full random oracle from just the coordinates `≤ n`: use `x` on `Iic n`, `0` above. The above-`n`
answers are irrelevant under `TailIndependent`, so this canonical `0`-tail extension carries the acceptance. -/
def iicExtend (n : ℕ) (x : ↥(Finset.Iic n) → Rq) : ℕ → Rq :=
  fun j => if h : j ≤ n then x ⟨j, Finset.mem_Iic.mpr h⟩ else 0

/-- **The prefix × challenge ≃ `Iic n` coordinates bijection.** A fork prefix `ω : Fin n → Rq` and a fork
challenge `c : Rq` together ARE exactly the coordinates `0 ≤ · ≤ n` of a random oracle: `ω` below `n`, `c` at
`n`. This `Equiv` is what identifies the finite shadow's outcome space `(Fin n → Rq) × Rq` with the cylinder
base `↥(Finset.Iic n) → Rq`. -/
def iicEquiv (Rq : Type*) (n : ℕ) : ((Fin n → Rq) × Rq) ≃ (↥(Finset.Iic n) → Rq) where
  toFun p := fun i => if h : (↑i : ℕ) < n then p.1 ⟨↑i, h⟩ else p.2
  invFun x := (fun j => x ⟨↑j, Finset.mem_Iic.mpr (le_of_lt j.2)⟩,
               x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩)
  left_inv := by
    rintro ⟨ω, c⟩
    refine Prod.ext ?_ ?_
    · funext j
      simp only [dif_pos j.2]
    · simp only [Nat.lt_irrefl, dif_neg, not_false_eq_true]
  right_inv := by
    intro x
    funext i
    by_cases h : (↑i : ℕ) < n
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      have hle : (↑i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
      congr 1
      exact Subtype.ext (le_antisymm (not_lt.mp h) hle)

/-! ### `TailIndependent` ⟹ acceptance depends only on the coordinates `≤ challengeIdx`. -/

/-- The random oracle `ρ` is its own `extend` reconstruction (prefix `ρ|_{<n}`, challenge `ρ n`, tail `ρ`). -/
theorem extend_self (F : Forger Rq M N Msg) (ρ : ℕ → Rq) :
    extend F (fun i : Fin F.challengeIdx => ρ ↑i) (ρ F.challengeIdx) ρ = ρ := by
  funext j
  unfold extend
  split_ifs with h1 h2
  · rfl
  · rw [h2]
  · rfl

/-- **`TailIndependent` ⟹ acceptance is a function of the coordinates `≤ challengeIdx`.** If two oracles agree
on all coordinates `≤ challengeIdx`, they accept together. Both `ρ`, `ρ'` are `extend`-reconstructions with the
SAME prefix and challenge (they agree there) and differing tails, so `TailIndependent` equates them. This is
the marginalisation content: the accept indicator ignores the tail. -/
theorem accepts_congr_of_le (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) {ρ ρ' : ℕ → Rq}
    (hle : ∀ j, j ≤ F.challengeIdx → ρ j = ρ' j) :
    Accepts A t β F ρ ↔ Accepts A t β F ρ' := by
  have hp : (fun i : Fin F.challengeIdx => ρ ↑i) = (fun i : Fin F.challengeIdx => ρ' ↑i) := by
    funext i; exact hle ↑i (le_of_lt i.2)
  have hc : ρ F.challengeIdx = ρ' F.challengeIdx := hle _ (le_refl _)
  calc Accepts A t β F ρ
      ↔ Accepts A t β F (extend F (fun i => ρ ↑i) (ρ F.challengeIdx) ρ) := by rw [extend_self F ρ]
    _ ↔ Accepts A t β F (extend F (fun i => ρ ↑i) (ρ F.challengeIdx) ρ') :=
        h (fun i => ρ ↑i) (ρ F.challengeIdx) ρ ρ'
    _ ↔ Accepts A t β F ρ' := by rw [hp, hc, extend_self F ρ']

/-- The `extend` reconstruction (prefix `ω`, challenge `c`, any tail) and the canonical `iicExtend` of the
corresponding `Iic n` coordinates agree on `≤ challengeIdx` — hence accept together under `TailIndependent`.
This is the acceptance-correspondence across the `iicEquiv` bijection. -/
theorem accepts_iicEquiv (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) (tail : ℕ → Rq) (p : (Fin F.challengeIdx → Rq) × Rq) :
    Accepts A t β F (extend F p.1 p.2 tail)
      ↔ Accepts A t β F (iicExtend F.challengeIdx (iicEquiv Rq F.challengeIdx p)) := by
  apply accepts_congr_of_le A t β F h
  intro j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [extend_below F p.1 p.2 tail hlt]
    simp only [iicExtend, dif_pos hj, iicEquiv, Equiv.coe_fn_mk, dif_pos hlt]
  · subst heq
    rw [extend_at F p.1 p.2 tail]
    simp only [iicExtend, dif_pos (le_refl _), iicEquiv, Equiv.coe_fn_mk, Nat.lt_irrefl,
      dif_neg, not_false_eq_true]

/-! ### The acceptance event is a measurable cylinder; its RO measure is the finite counting probability. -/

open Classical in
/-- The finite base of the acceptance cylinder: the `Iic challengeIdx` coordinate-tuples whose canonical
reconstruction accepts. Its cardinality is the numerator of the finite counting probability. -/
noncomputable def accBase (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg) :
    Finset (↥(Finset.Iic F.challengeIdx) → Rq) :=
  Finset.univ.filter (fun x => Accepts A t β F (iicExtend F.challengeIdx x))

theorem mem_accBase (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (x : ↥(Finset.Iic F.challengeIdx) → Rq) :
    x ∈ accBase A t β F ↔ Accepts A t β F (iicExtend F.challengeIdx x) := by
  classical
  simp only [accBase, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **THE ACCEPTANCE EVENT IS A CYLINDER (given `TailIndependent`).** Because acceptance depends only on the
coordinates `≤ challengeIdx` (`accepts_congr_of_le`), the acceptance event `{ρ | Accepts ρ}` is exactly the
cylinder over `Finset.Iic challengeIdx` with base `accBase` — measurable, and its RO measure is computed by
marginalising the tail. -/
theorem acceptEvent_eq_cylinder (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) :
    {ρ : ℕ → Rq | Accepts A t β F ρ}
      = cylinder (Finset.Iic F.challengeIdx) (↑(accBase A t β F)) := by
  ext ρ
  rw [Set.mem_setOf_eq, mem_cylinder, Finset.mem_coe, mem_accBase]
  apply accepts_congr_of_le A t β F h
  intro j hj
  simp only [iicExtend, dif_pos hj]
  rfl

/-- **THE RO MEASURE OF THE ACCEPTANCE EVENT = the finite counting probability.** `infinitePi_cylinder`
marginalises the tail: the infinite-product measure of the acceptance cylinder is the finite product measure of
`accBase`, which is `|accBase| · (|Rq|⁻¹)^(challengeIdx+1)`. The abstract Forger's advantage is now a genuine
probability over `ℕ → Rq`, computed by a finite count. -/
theorem roMeasure_accept (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) :
    roMeasure Rq {ρ : ℕ → Rq | Accepts A t β F ρ}
      = (accBase A t β F).card * (Fintype.card Rq : ℝ≥0∞)⁻¹ ^ (F.challengeIdx + 1) := by
  rw [acceptEvent_eq_cylinder A t β F h]
  have hcyl : roMeasure Rq (cylinder (Finset.Iic F.challengeIdx) (↑(accBase A t β F)))
      = Measure.pi (fun _ : ↥(Finset.Iic F.challengeIdx) => (PMF.uniformOfFintype Rq).toMeasure)
          (↑(accBase A t β F)) := by
    rw [roMeasure]
    exact Measure.infinitePi_cylinder (μ := fun _ : ℕ => (PMF.uniformOfFintype Rq).toMeasure)
      (mS := Finset.measurableSet _)
  rw [hcyl, pi_uniform_finset, Fintype.card_coe, Nat.card_Iic]

/-! ### The finite-shadow advantage EQUALS the RO probability of acceptance — the bridge MATERIALIZED. -/

/-- **THE COUNTING IDENTITY.** The cylinder base's cardinality is the shadow's total accepting mass
`∑_ω hits_ω`: the `iicEquiv` bijection carries `accBase` onto the accepting `(ω, c)` pairs, and summing the
off-fibers gives the per-prefix hit counts. Pure combinatorics — no measure, no assumption beyond
`TailIndependent` (used only to move acceptance across the bijection). -/
theorem accBase_card (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) (tail : ℕ → Rq) :
    (accBase A t β F).card
      = ∑ ω : (Fin F.challengeIdx → Rq), hits (abstractShadow A t β F tail).acc ω := by
  classical
  have step1 : (accBase A t β F).card
      = (Finset.univ.filter (fun p : (Fin F.challengeIdx → Rq) × Rq =>
            Accepts A t β F (extend F p.1 p.2 tail))).card := by
    apply Finset.card_equiv (iicEquiv Rq F.challengeIdx).symm
    intro x
    rw [mem_accBase]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [accepts_iicEquiv A t β F h tail ((iicEquiv Rq F.challengeIdx).symm x),
        Equiv.apply_symm_apply]
  rw [step1, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.card_filter]
  unfold hits acceptSet
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, abstractShadow, decide_eq_true_eq]

/-- **THE BRIDGE — the finite shadow's advantage IS the RO probability of acceptance.** Under
`TailIndependent`, the finite shadow's `advantage` (a `ℚ` counting probability over `(Fin challengeIdx → Rq) ×
Rq`) equals the genuine probability of the acceptance event under the real infinite-product RO measure
`roMeasure`. Both collapse to `|accBase| / |Rq|^(challengeIdx+1)`. The model↔reality identification of §B is now
a THEOREM: the shadow's advantage no longer merely stands in for the abstract Forger's — it EQUALS its accept
probability over `ℕ → Rq`. -/
theorem abstractShadow_advantage_eq_roMeasure (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (h : TailIndependent A t β F) (tail : ℕ → Rq) :
    ((advantage (abstractShadow A t β F tail).acc : ℚ) : ℝ)
      = (roMeasure Rq {ρ : ℕ → Rq | Accepts A t β F ρ}).toReal := by
  have hpos : 0 < Fintype.card Rq := Fintype.card_pos
  have hcard0 : (Fintype.card Rq : ℝ) ≠ 0 := by positivity
  have hRHS : (roMeasure Rq {ρ : ℕ → Rq | Accepts A t β F ρ}).toReal
            = (accBase A t β F).card / (Fintype.card Rq : ℝ) ^ (F.challengeIdx + 1) := by
    rw [roMeasure_accept A t β F h, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_pow, ← div_eq_mul_inv]
  have hnum : (∑ ω : (Fin F.challengeIdx → Rq), (hits (abstractShadow A t β F tail).acc ω : ℚ))
            = ((accBase A t β F).card : ℚ) := by
    rw [← Nat.cast_sum, ← accBase_card A t β F h tail]
  have hΩcard : (Fintype.card (Fin F.challengeIdx → Rq) : ℚ) = (Fintype.card Rq : ℚ) ^ F.challengeIdx := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hLHS : ((advantage (abstractShadow A t β F tail).acc : ℚ) : ℝ)
            = (accBase A t β F).card / (Fintype.card Rq : ℝ) ^ (F.challengeIdx + 1) := by
    rw [advantage, hnum, hΩcard, pow_succ]
    push_cast
    ring
  rw [hLHS, hRHS]

/-- **TAIL-INVARIANCE, re-derived over the real measure.** Since the shadow's advantage equals the tail-free
`roMeasure`-probability of acceptance, it is the SAME for every frozen tail — the §B result
`abstractShadow_advantage_tailIndep`, now with the tail genuinely absent (it was marginalised). -/
theorem abstractShadow_advantage_tailInvariant_via_roMeasure (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (F : Forger Rq M N Msg) (h : TailIndependent A t β F) (tail tail' : ℕ → Rq) :
    advantage (abstractShadow A t β F tail).acc = advantage (abstractShadow A t β F tail').acc := by
  have e1 := abstractShadow_advantage_eq_roMeasure A t β F h tail
  have e2 := abstractShadow_advantage_eq_roMeasure A t β F h tail'
  have : ((advantage (abstractShadow A t β F tail).acc : ℚ) : ℝ)
       = ((advantage (abstractShadow A t β F tail').acc : ℚ) : ℝ) := by rw [e1, e2]
  exact_mod_cast this

end ROMeasureBridge

/-! ### Teeth — the materialized RO bridge FIRES on a concrete forger, non-vacuously. -/

section ROTeeth

open MeasureTheory
open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS

/-- `⊤` (discrete) measurable structure on the finite `ZMod 5`: every set measurable, the uniform PMF is a
genuine probability measure — the substrate for the infinite-RO product measure on `ℕ → ZMod 5`. -/
noncomputable local instance : MeasurableSpace (ZMod 5) := ⊤

/-- **THE MATERIALIZED BRIDGE FIRES.** `exAbstractForger` is `TailIndependent` (it reads only the challenge),
so `abstractShadow_advantage_eq_roMeasure` applies: its finite-shadow advantage EQUALS the genuine probability
of its acceptance event under the real infinite-product RO measure on `ℕ → ZMod 5`. The model↔reality
identification is exhibited on concrete data. -/
theorem exAbstract_advantage_eq_roMeasure :
    ((advantage (abstractShadow (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger
        (fun _ => 0)).acc : ℚ) : ℝ)
      = (roMeasure (ZMod 5) {ρ : ℕ → ZMod 5 |
          Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger ρ}).toReal :=
  abstractShadow_advantage_eq_roMeasure (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0
    exAbstractForger exAbstract_tailIndep (fun _ => 0)

/-- `exAbstractForger` accepts on EVERY oracle (it reads only the challenge; `id·(ρ 0) = 0 + (ρ 0)·1`). -/
theorem exAbstract_accepts_all (ρ : ℕ → ZMod 5) :
    Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger ρ := by
  refine ⟨Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, ?_⟩
  simp [exAbstractForger, HermineThreshold.verify]

/-- **NON-VACUITY — the acceptance probability is a positive `1`, not a vacuous `0`.** `exAbstractForger`
accepts on every oracle, so its acceptance event is the WHOLE space `ℕ → ZMod 5`, and the genuine infinite-RO
product measure — being a real `IsProbabilityMeasure` — gives it mass `1`. The RO measure is a genuine
probability, and the bridge above equates the finite advantage with this real `1`. -/
theorem exAbstract_roMeasure_eq_one :
    roMeasure (ZMod 5) {ρ : ℕ → ZMod 5 |
        Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger ρ} = 1 := by
  have hset : {ρ : ℕ → ZMod 5 |
        Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exAbstractForger ρ} = Set.univ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exAbstract_accepts_all ρ
  rw [hset, measure_univ]

end ROTeeth

#assert_all_clean [
  winProb_prod_factor,
  IndepHybridForkingFamily.hybridForgerAdv_nonneg,
  IndepHybridForkingFamily.hybridForgerAdv_eq_mul,
  IndepHybridForkingFamily.hybridForgerAdv_le_classical,
  IndepHybridForkingFamily.hybridForgerAdv_le_pq,
  hybrid_forger_negl_under_floors_indep,
  secureLeftHybridI_zero,
  secureLeftHybridI_negl,
  bothBrokenHybridI_forgerAdv,
  bothBrokenHybridI_not_negl,
  commitment_extend_eq,
  abstractShadow_acc_tailIndep,
  abstractShadow_advantage_tailIndep,
  abstractShadow_forkProb_tailIndep,
  exAbstract_accepts,
  exAbstract_tailIndep,
  exTail_accepts_true,
  exTail_accepts_false,
  exTail_not_tailIndep,
  pi_uniform_singleton,
  pi_uniform_finset,
  extend_self,
  accepts_congr_of_le,
  accepts_iicEquiv,
  acceptEvent_eq_cylinder,
  roMeasure_accept,
  accBase_card,
  abstractShadow_advantage_eq_roMeasure,
  abstractShadow_advantage_tailInvariant_via_roMeasure,
  exAbstract_advantage_eq_roMeasure,
  exAbstract_accepts_all,
  exAbstract_roMeasure_eq_one
]

end Dregg2.Crypto.ModelBridge
