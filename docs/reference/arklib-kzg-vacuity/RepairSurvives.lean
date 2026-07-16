/-
Demonstration that the extraction-shaped repair of KZG evaluation binding
(`KZG.CommitmentScheme.binding_reduces_to_tSdh`) SURVIVES THE EXACT ATTACK that made the
original assumption-form vacuous.

NOT part of ArkLib. Scratch file supporting the repair proposal.

The refutation section (`dlogOf … not_tSdhAssumption`) is copied verbatim from the
disclosure artifact and re-proved here against the *repaired* Binding.lean, so the two
coexist in one axiom closure. The final theorem `repair_survives_attack` states, for the
same groups/pairing in which the attack succeeds:

  (1) the exact trapdoor-extracting adversary STILL refutes `tSdhAssumption` below error 1
      (`not_tSdhAssumption`), AND
  (2) the repaired reduction bound `binding_reduces_to_tSdh` holds UNCONDITIONALLY and
      relates two concrete probabilities — it never mentions `tSdhAssumption`, so there is
      nothing for the choice-adversary to inhabit.

`sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`.
-/
import ArkLib.Commitments.Functional.KZG.Binding

open OracleSpec OracleComp
open scoped NNReal ENNReal

namespace ArkLibRepairCheck

section Dlog

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The choice-definable discrete logarithm base a nontrivial `g` in a prime-order group:
`Exists.choose` applied to ArkLib's own `Groups.exists_zmod_power_of_generator`. -/
noncomputable def dlogOf {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1)
    (x : G) : ZMod p :=
  (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg
    (Groups.orderOf_eq_prime_of_ne_one g hg) x).choose

lemma dlogOf_pow {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1) (a : ZMod p) :
    dlogOf (p := p) hg (g ^ a.val) = a := by
  have hord : orderOf g = p := Groups.orderOf_eq_prime_of_ne_one g hg
  have hspec : g ^ a.val = g ^ (dlogOf (p := p) hg (g ^ a.val)).val :=
    (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg hord
      (g ^ a.val)).choose_spec
  have hdiv : g ^ (dlogOf (p := p) hg (g ^ a.val) - a).val = 1 := by
    rw [← Groups.gpow_div_eq hord _ a, ← hspec, div_self']
  exact sub_eq_zero.mp (Groups.zmod_eq_zero_of_gpow_eq_one hord hdiv)

lemma sampleNonzeroZMod_ne_zero {τ : ZMod p}
    (hτ : τ ∈ support (Groups.sampleNonzeroZMod (p := p))) : τ ≠ 0 := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  haveI : NeZero (p - 1) := ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hp)⟩
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hp)⟩
  rw [Groups.sampleNonzeroZMod, support_map] at hτ
  obtain ⟨i, -, rfl⟩ := hτ
  have hi := i.isLt
  have hlt : (i : ℕ) + 1 < p := by omega
  intro hzero
  simp only at hzero
  have hdvd : (((i : ℕ) + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact hzero
  rw [ZMod.natCast_eq_zero_iff] at hdvd
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) hdvd) (not_le.mpr hlt)

lemma probFailure_sampleNonzeroZMod : Pr[⊥ | Groups.sampleNonzeroZMod (p := p)] = 0 := by
  rw [Groups.sampleNonzeroZMod]; simp

end Dlog

section Refutation

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  [∀ i, SampleableType (unifSpec.Range i)]

/-- The winning t-SDH adversary: reads `g₂ ^ τ` from the verifier SRS leg, recovers `τ` by
`Classical.choice`, returns the solution at offset `c = 0`. Zero oracle queries. -/
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf (p := p) hg₂ srs.2[1]).val))

lemma game_run_eq (hg₂ : g₂ ≠ 1) (D : ℕ) :
    (Groups.tSdhGame (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D)).run
      = (fun τ : ZMod p => some (τ, (0 : ZMod p), g₁ ^ (1 / τ).val))
          <$> Groups.sampleNonzeroZMod := by
  simp [Groups.tSdhGame, tauExtractingAdversary, Groups.PowerSrs.generate,
    Groups.PowerSrs.tower, dlogOf_pow hg₂]

theorem tSdhExperiment_tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D) = 1 := by
  classical
  rw [Groups.tSdhExperiment, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, game_run_eq (g₁ := g₁) hg₂ D, probFailure_map,
      probFailure_sampleNonzeroZMod]
    simp
  · intro x hx
    rw [OptionT.support_def, game_run_eq (g₁ := g₁) hg₂ D, support_map] at hx
    obtain ⟨τ, hτ, hxτ⟩ := hx
    simp only [Option.some.injEq] at hxτ
    subst hxτ
    have hτ0 : τ ≠ 0 := sampleNonzeroZMod_ne_zero hτ
    exact ⟨by simpa using hτ0, by simp⟩

/-- **The exact attack.** ArkLib's `tSdhAssumption` is FALSE for every error bound `< 1`. -/
theorem not_tSdhAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro h
  have hle := h (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D)
  rw [tSdhExperiment_tauExtractingAdversary (g₁ := g₁) hg₂ D] at hle
  exact absurd (lt_of_le_of_lt hle herr) (lt_irrefl 1)

end Refutation

section RepairSurvives

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]

variable {n : ℕ}

open CompPoly CompPoly.CPolynomial in
/-- Mirror of ArkLib's `local instance bindingOracleInterface` (Binding.lean:51). Because
that instance is `local`, it is not in scope here, and the KZG binding types would otherwise
resolve `OracleInterface (Fin (n+1) → ZMod p)` to the generic `instFunction`, mismatching the
instance the library was compiled against. Declaring the identical local instance makes the
types line up. -/
local instance bindingOracleInterface : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

/-- `binding`'s pairing hypothesis forces `g₂ ≠ 1` (bilinear pairing kills the identity). -/
lemma g₂_ne_one_of_pairing_ne_zero
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0) : g₂ ≠ 1 := by
  intro h
  apply hpair
  rw [show (Additive.ofMul g₂) = 0 from congrArg Additive.ofMul h]
  exact map_zero _

/-- **The repair survives the exact attack.** For any prime-order group pair and any
nondegenerate pairing — precisely the setting in which the trapdoor-extracting adversary
refutes `tSdhAssumption` — BOTH of the following hold simultaneously:

* `(1)` the exact attack still refutes the assumption below error `1`
  (`not_tSdhAssumption`); and
* `(2)` the repaired, extraction-shaped reduction bound
  `KZG.CommitmentScheme.binding_reduces_to_tSdh` holds *unconditionally*, upper-bounding
  every binding adversary's advantage by the success probability of its explicit t-SDH
  reduction.

The old assumption-form `binding` was vacuous because `(1)` made its premise false. The new
form is not: `(2)` never takes `tSdhAssumption` as a hypothesis, so `(1)` cannot empty it.
The two live together in one `sorry`-free axiom closure. -/
theorem repair_survives_attack
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hg₁ : g₁ ≠ 1)
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0)
    [SampleableType G₁]
    (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1)
    (AuxState : Type)
    (adversary : KZG.CommitmentScheme.KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    (¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n tSdhError)
    ∧ (Commitment.bindingExperiment (init := pure ∅) (impl := randomOracle)
          (KZG.CommitmentScheme.kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))
          AuxState adversary
        ≤ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
          (KZG.CommitmentScheme.bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
            AuxState adversary)) := by
  refine ⟨?_, ?_⟩
  · exact not_tSdhAssumption (g₁ := g₁)
      (g₂_ne_one_of_pairing_ne_zero pairing hpair) n tSdhError herr
  · exact KZG.CommitmentScheme.binding_reduces_to_tSdh (pairing := pairing) hg₁ hpair
      AuxState adversary

end RepairSurvives

end ArkLibRepairCheck

#print axioms ArkLibRepairCheck.not_tSdhAssumption
#print axioms ArkLibRepairCheck.repair_survives_attack
#print axioms KZG.CommitmentScheme.binding_reduces_to_tSdh
#print axioms KZG.CommitmentScheme.binding
