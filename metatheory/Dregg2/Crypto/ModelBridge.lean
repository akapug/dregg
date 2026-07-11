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
re-proves `Negl hybridForgerAdv` under `DLHardQuant ∨ MSISHardQuant` with the two legs' challenges genuinely
INDEPENDENT — the shared-challenge assumption is gone. Teeth: one secure component ⇒ `hybridForgerAdv ≡ 0`;
BOTH broken (each `2/5`) ⇒ `hybridForgerAdv ≡ 4/25 = (2/5)·(2/5)` (the independent PRODUCT, not `2/5`) — NOT
Negl, so the "either" is load-bearing AND the factorisation is exhibited numerically.

## §B — FINITE SHADOW ↔ ABSTRACT FORGER.  (partial — the commitment leg CLOSED, one measure step NAMED)

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

  * **`TailIndependent` (the NAMED residual) + faithfulness under it (CLOSED given the name).** The ONE thing
    not provable from the `Forger` structure is that acceptance is independent of the RO answers STRICTLY ABOVE
    `challengeIdx` (the abstract `response` may read them). This is exactly the marginalisation of the uniform
    RO tail. We name it `TailIndependent` and prove that GIVEN it, the finite shadow's `advantage`/`forkProb`
    are INDEPENDENT of the frozen tail (`abstractShadow_advantage_tailIndep`/`_forkProb_`) — i.e. the shadow is
    canonical and genuinely captures the abstract forger's fork behaviour with NO residual dependence on the
    unmodelled coordinates. Teeth: `exAbstractForger` (reads only the challenge) IS `TailIndependent`;
    `exTailForger` (reads an above-challenge coordinate) is NOT — so `TailIndependent` is load-bearing.

  EXACT REMAINING STEP: the coordinate-restriction of the RO measure to the fork prefix is established (the
  commitment factors through the prefix, unconditionally). The remaining measure-theoretic lemma is the
  independence of the ACCEPTANCE event from the answers above `challengeIdx` (`TailIndependent`) — equivalently
  that marginalising the uniform tail commutes with the accept indicator. Given it, the finite shadow's
  advantage/forkProb are tail-canonical (proved here); establishing it in general needs an infinite-product RO
  measure this finite counting-probability model does not carry (`ℕ → Rq` is not a `Fintype`). Named, not
  `sorry`-ed, not silently assumed.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}). No `native_decide` in any `∀`; teeth exhibit
`0` / `4/25` / tail-dependence so nothing is vacuous.
-/
import Dregg2.Crypto.HybridThresholdQuant
import Dregg2.Tactics
import Mathlib.Tactic

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

/-- **THE INDEPENDENT-CHALLENGE HYBRID COMBINER — `Negl hybridForgerAdv` under `DLHardQuant ∨ MSISHardQuant`.**
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
    (hfloor : DLHardQuant dlSolverOf ∨ MSISHardQuant msisSolverOf) :
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
positive constant, NOT negligible; so `DLHardQuant ∨ MSISHardQuant` is load-bearing even with independent
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
  exTail_not_tailIndep
]

end Dregg2.Crypto.ModelBridge
