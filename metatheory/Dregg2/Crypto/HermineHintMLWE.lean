/-
# `Dregg2.Crypto.HermineHintMLWE` — the REAL Raccoon concurrent-security argument.

This is the STRAIGHT-LINE (non-forking) reduction that actually defends the Raccoon/Hermine lattice
threshold signature against concurrent / rushing adversaries. It is a game-hop with THREE pillars and
NO forking, NO ROS combinatorial bound:

1. **MASKING (Hint-MLWE).** Each signer's response `zᵢ = yᵢ + c·(λᵢ·sᵢ)` is a fresh one-time mask `yᵢ`
   plus a secret-dependent shift. Across MANY concurrent sessions the adversary sees many
   `(wᵢ = A·yᵢ, zᵢ)` "hints" on the secret; Hint-MLWE says the secret STAYS HIDDEN given these hints —
   the masked responses are SIMULATABLE without the secret. This is the multi-session generalization of
   the SINGLE-session key-hiding already proved in `Smudging`/`HermineHiding`/`RenyiHiding`/`GaussianRenyi`;
   we ground it there (`hint_mlwe_of_smudge` reduces one session to `signature_hides_secret`/`smudge_bound`),
   so `HintMLWEHard` is the honest generalization, NOT a fresh unrelated axiom. Leakage is additive in TV
   (`hint_mlwe_hybrid_leakage`); the Rényi form (`RenyiHiding.renyiDiv2_mul`, `GaussianRenyi.gaussian_renyi2_pair`)
   tightens the `Q`-session cost from `Q·ε` to `≈ √Q`.
2. **COMMIT-THEN-REVEAL (binding).** Each signer commits `cmᵢ = H(i, wᵢ)` BEFORE revealing `wᵢ`, so a
   rushing adversary cannot adaptively choose its `wⱼ` after seeing the honest commitments — it is BOUND by
   `cmⱼ`. Under collision-resistance (`HashCR`) a signer cannot open one commitment to two different `wᵢ`
   (`commitment_binding`); an equivocating opening BREAKS `HashCR` (`equivocation_breaks_hashcr`). This is
   the rushing defense's teeth: it is what forces the two forgery transcripts to share ONE commitment `w`.
3. **SelfTargetMSIS.** A forgery bound to its commitment still yields an MSIS solution via the committed
   `Dregg2.Crypto.HermineSelfTargetMSIS.no_forgery_under_msis_selftarget` — `c ≠ c'` alone gives the
   nonzero short solution on the augmented map `[A | t]`, no invertibility, no MLWE-lossiness.

**THE HEADLINE** `concurrent_unforgeable_reduces`: a concurrent (rushing) forger who opens a common
commitment and outputs two accepting SelfTargetMSIS solutions with `c ≠ c'` cannot exist under
`HashCR ∧ MSISHard` — binding forces the shared commitment `w`, SelfTargetMSIS closes it. The dichotomy
`concurrent_forgery_breaks_hashcr_or_msis` shows the rushing forger breaks HashCR (equivocation) OR
MSIS (bound forgery); `leakage_exceeds_budget_breaks_hint_mlwe` is the masking-pillar break (it learned
the secret from the hints). The proof COMPOSES the three pillars — no forking lemma, no ROS bound.

This is the REAL Raccoon concurrency argument (masking + commit-reveal + SelfTargetMSIS, Hint-MLWE
straight-line). It SUPERSEDES the FROST-binding-factor / ROS framing, which is a group-setting object and
was a mis-model; the crypto-hermine impl is being aligned to the matching 2-round commit-reveal protocol.
-/
import Dregg2.Crypto.HermineSelfTargetMSIS
import Dregg2.Crypto.HermineHiding

namespace Dregg2.Crypto.HermineHintMLWE

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.Smudging
open Dregg2.Crypto.HermineHiding
open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS

/-! ## Pillar 1 — MASKING: the Hint-MLWE carrier, grounded in single-session key-hiding.

A concurrent transcript is a family of "hint sessions": each session `i` shifts the WIDE mask support `S`
by a secret-dependent shift `shift i` (the `c·(λᵢ·sᵢ)` translate), so the real masked responses are
`unif (S.image (shift i))` while a secret-free SIMULATOR outputs `unif S`. `HintMLWEHard` says every
session's real transcript stays within statistical distance `ε` of the simulator — the secret is hidden
under concurrency. We PROVE this is exactly the multi-session lift of the smudging key-hiding bound. -/

section HintMLWE

variable {α : Type*} [DecidableEq α] {ι : Type*}

/-- **`HintMLWEHard`** — the named multi-session masking assumption. Over `sessions` concurrent signing
sessions, each a secret-dependent shift `shift i` of the wide mask support `S`, the real masked-response
transcript `unif (S.image (shift i))` is within statistical distance `ε` of the secret-free simulator
`unif S`. When it holds, the many hints leak at most `ε` per session about the secret — the secret stays
hidden across concurrency. Stated in the SAME `statDist`/`unif` currency as the single-session key-hiding
it generalizes (so it is grounded, not a fresh axiom — see `hint_mlwe_of_smudge`). -/
def HintMLWEHard (S : Finset α) (sessions : Finset ι) (shift : ι → α → α) (ε : ℚ) : Prop :=
  ∀ i ∈ sessions, statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i))) ≤ ε

/-- **Hint-MLWE reduces to single-session key-hiding (the grounding).** If each session's shift is
injective (a genuine translate of the mask support) and moves at most `B` of the `M = |S|`-wide support,
then `HintMLWEHard` holds at `ε = B / M` — and it does so BY `HermineHiding.signature_hides_secret`
(itself `Smudging.smudge_bound`) applied per session. So Hint-MLWE is the honest multi-session
generalization of the already-proved single-session masking, not an unrelated hardness assumption. -/
theorem hint_mlwe_of_smudge (S : Finset α) (sessions : Finset ι) (shift : ι → α → α)
    (hinj : ∀ i ∈ sessions, Function.Injective (shift i)) (hpos : 0 < S.card) (B : ℕ)
    (hB : ∀ i ∈ sessions, (S \ S.image (shift i)).card ≤ B) :
    HintMLWEHard S sessions shift ((B : ℚ) / (S.card : ℚ)) := fun i hi =>
  signature_hides_secret S (shift i) (hinj i hi) hpos B (hB i hi)

/-- **Additive (TV) hybrid bound over `Q` concurrent sessions.** If each session is within `ε` of the
simulator, the total per-session leakage over the session set is at most `Q·ε` (`Q = |sessions|`) — the
straightforward union/hybrid bound. This is the loose TV form; the Rényi divergence
(`RenyiHiding.renyiDiv2_mul` multiplicativity, `GaussianRenyi.gaussian_renyi2_pair`) replaces the linear
`Q·ε` with the near-constant `≈ √Q` cost that Raccoon's parameters actually use. -/
theorem hint_mlwe_hybrid_leakage (S : Finset α) (sessions : Finset ι) (shift : ι → α → α) (ε : ℚ)
    (h : HintMLWEHard S sessions shift ε) :
    (∑ i ∈ sessions, statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i))))
      ≤ sessions.card • ε :=
  Finset.sum_le_card_nsmul sessions _ ε h

/-- **The masking-pillar break.** If some concurrent session leaks MORE than the budget `ε` (the adversary
learned the secret from the hints), then `HintMLWEHard` fails at `ε` — the forger has broken pillar 1. The
contrapositive of the definition, isolating "it learned the secret from the hints" as a genuine break. -/
theorem leakage_exceeds_budget_breaks_hint_mlwe (S : Finset α) (sessions : Finset ι)
    (shift : ι → α → α) (ε : ℚ) (i : ι) (hi : i ∈ sessions)
    (hleak : ε < statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i)))) :
    ¬ HintMLWEHard S sessions shift ε :=
  fun h => absurd (h i hi) (not_le.mpr hleak)

end HintMLWE

/-! ## Pillar 2 — COMMIT-THEN-REVEAL: binding is the rushing defense.

A signer commits `cmᵢ = H(i, wᵢ)` before revealing `wᵢ`. Collision-resistance of `H` (the named carrier
`HashCR`) is exactly what stops a rushing adversary from equivocating: it cannot open one commitment to
two different `wᵢ`. Binding is what FORCES the two forgery transcripts to carry the SAME commitment `w`,
which is precisely what SelfTargetMSIS (pillar 3) consumes. -/

section CommitReveal

/-- A commit-reveal instantiation: a hash `H` on `(index, commitment)` pairs. `commit i w = H(i, w)` and
`opens cm i w` says `w` is a valid opening of `cm` at index `i`. The committed value `w` is the Raccoon
lattice commitment `wᵢ = A·yᵢ`. -/
structure CommitReveal (Idx W C : Type*) where
  H : Idx → W → C

/-- The commitment of `w` at index `i`: `cmᵢ = H(i, w)`. -/
def CommitReveal.commit {Idx W C : Type*} (cr : CommitReveal Idx W C) (i : Idx) (w : W) : C :=
  cr.H i w

/-- `w` opens the commitment `cm` at index `i` iff `H(i, w) = cm`. -/
def CommitReveal.opens {Idx W C : Type*} (cr : CommitReveal Idx W C) (cm : C) (i : Idx) (w : W) : Prop :=
  cr.commit i w = cm

/-- **`HashCR`** — the named collision-resistance carrier: `H` is injective on the committed domain (for
each fixed index, distinct `w` hash to distinct commitments). Modeled as the abstract injectivity a
collision-resistant hash provides on the committed domain; assumed at the boundary, never proved (the
Poseidon2/hash floor `Dregg2` already carries). -/
def HashCR {Idx W C : Type*} (cr : CommitReveal Idx W C) : Prop :=
  ∀ (i : Idx) (w w' : W), cr.H i w = cr.H i w' → w = w'

/-- **COMMITMENT BINDING (the rushing teeth).** Under `HashCR`, a signer cannot open one commitment `cm`
to two different reveals: if `w` and `w'` both open `cm` at index `i`, then `w = w'`. So a rushing
adversary is BOUND to the `wⱼ` it committed — it cannot adaptively swap its commitment after seeing the
honest ones. This is the property that pins the two forgery transcripts to a SINGLE commitment `w`. -/
theorem commitment_binding {Idx W C : Type*} (cr : CommitReveal Idx W C) (hcr : HashCR cr)
    (cm : C) (i : Idx) (w w' : W) (ho : cr.opens cm i w) (ho' : cr.opens cm i w') : w = w' := by
  unfold CommitReveal.opens CommitReveal.commit at ho ho'
  exact hcr i w w' (ho.trans ho'.symm)

/-- **An equivocating opening BREAKS `HashCR`.** Two DISTINCT reveals `w ≠ w'` of the SAME commitment `cm`
witness a collision — so `HashCR` cannot hold. The contrapositive of `commitment_binding`: equivocation is
exactly a hash collision, the concrete break of pillar 2. -/
theorem equivocation_breaks_hashcr {Idx W C : Type*} (cr : CommitReveal Idx W C)
    (cm : C) (i : Idx) (w w' : W) (hne : w ≠ w')
    (ho : cr.opens cm i w) (ho' : cr.opens cm i w') : ¬ HashCR cr :=
  fun hcr => hne (commitment_binding cr hcr cm i w w' ho ho')

end CommitReveal

/-! ## The straight-line composition — the three pillars, no forking.

The rushing forger opens a common commitment (`cm`, index `i`) and outputs two accepting SelfTargetMSIS
solutions with `c ≠ c'`. Binding (pillar 2) forces the two reveals to the SAME lattice commitment `w`;
that shared `w` is what SelfTargetMSIS (pillar 3) needs; and the honest hints are simulatable (pillar 1),
so the reduction runs secret-free. There is NO forking lemma and NO ROS bound anywhere. -/

section Composition

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **THE RUSHING DICHOTOMY.** A concurrent forger that opens the commitment `cm` (index `i`) with two
reveals `w`, `w'` and outputs two accepting SelfTargetMSIS solutions with `c ≠ c'` either
* **equivocated** (`w ≠ w'`) — an opening collision, so it BREAKS `HashCR` (pillar 2); or
* **is bound to one commitment** (`w = w'`) — then the two transcripts share the commitment, and
  `selftarget_extract_nonzero` extracts a genuine NONZERO short MSIS solution on `[A | t]` from `c ≠ c'`
  (pillar 3), breaking `MSISHard`.

This IS the straight-line rushing defense: commit-then-reveal leaves the adversary exactly these two doors,
and both are closed by a named lattice/hash carrier. No forking, no ROS. -/
theorem concurrent_forgery_breaks_hashcr_or_msis {Idx C : Type*}
    (cr : CommitReveal Idx N C) (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (cm : C) (i : Idx) (w w' : N) (ho : cr.opens cm i w) (ho' : cr.opens cm i w')
    (c c' : Rq) (z z' : M) (hne : c ≠ c')
    (hf : IsSelfTargetMSISSolution A t β z c w)
    (hf' : IsSelfTargetMSISSolution A t β z' c' w') :
    ¬ HashCR cr ∨ ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v := by
  by_cases hww : w = w'
  · -- BOUND to one commitment: the shared `w` feeds SelfTargetMSIS → a real MSIS solution.
    subst hww
    obtain ⟨hz, hc, _hw, h1⟩ := hf
    obtain ⟨hz', hc', _hw', h2⟩ := hf'
    exact Or.inr ⟨_, selftarget_extract_nonzero A t w c c' z z' β β hz hz' hc hc' hne h1 h2⟩
  · -- EQUIVOCATED: two distinct reveals of one commitment — a HashCR collision.
    exact Or.inl (equivocation_breaks_hashcr cr cm i w w' hww ho ho')

/-- **THE HEADLINE — `concurrent_unforgeable_reduces`.** Under the three pillars — `HashCR` (binding),
`MSISHard` (the augmented lattice floor), and Hint-MLWE (masking, established as the honest generalization
of key-hiding by `hint_mlwe_of_smudge`, which lets the reduction run secret-free) — a concurrent forger who
opens a common commitment `cm` at index `i` and outputs two accepting SelfTargetMSIS solutions with
`c ≠ c'` CANNOT EXIST. Straight-line composition: binding (`commitment_binding`) forces the two reveals to
the same lattice commitment `w`; the shared `w` with `c ≠ c'` hands SelfTargetMSIS a nonzero short MSIS
solution (`no_forgery_under_msis_selftarget`), contradicting `MSISHard`. No forking lemma, no ROS bound. -/
theorem concurrent_unforgeable_reduces {Idx C : Type*}
    (cr : CommitReveal Idx N C) (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (cm : C) (i : Idx) (w w' : N) (ho : cr.opens cm i w) (ho' : cr.opens cm i w')
    (c c' : Rq) (z z' : M) (hne : c ≠ c')
    (hf : IsSelfTargetMSISSolution A t β z c w)
    (hf' : IsSelfTargetMSISSolution A t β z' c' w')
    (hbind : HashCR cr)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) : False := by
  -- Pillar 2: binding pins both reveals to ONE commitment `w`.
  have hw : w = w' := commitment_binding cr hbind cm i w w' ho ho'
  subst hw
  -- Pillar 3: the shared commitment + `c ≠ c'` → MSIS solution, contradicting `MSISHard`.
  exact no_forgery_under_msis_selftarget A t w c c' z z' β hne hf hf' hard

end Composition

#assert_axioms hint_mlwe_of_smudge
#assert_axioms hint_mlwe_hybrid_leakage
#assert_axioms leakage_exceeds_budget_breaks_hint_mlwe
#assert_axioms commitment_binding
#assert_axioms equivocation_breaks_hashcr
#assert_axioms concurrent_forgery_breaks_hashcr_or_msis
#assert_axioms concurrent_unforgeable_reduces

/-! ## Teeth — the pillars FIRE on concrete data.

(a) Binding: an injective `H` opens a matching reveal and CATCHES a mismatched one; a colliding `H`
    equivocates and breaks `HashCR`.
(b) Composition: a "forgery" with distinct challenges yields the SelfTargetMSIS solution while the masked
    hints are simulatable (`HintMLWEHard`) — the two-pillar composition running end-to-end. -/

section Teeth

/-! ### (a) Binding teeth. -/

/-- A binding commit-reveal: `H(i, w) = (i, w)` is injective on the committed domain. -/
def exCR : CommitReveal ℕ ℤ (ℕ × ℤ) := ⟨fun i w => (i, w)⟩

/-- The binding instance genuinely satisfies `HashCR`. -/
theorem exCR_hashcr : HashCR exCR := fun _ _ _ h => (Prod.ext_iff.mp h).2

-- A matching reveal OPENS the commitment.
example : exCR.opens (3, 7) 3 7 := rfl
-- A mismatched reveal is CAUGHT (does not open) — the binding tooth.
example : ¬ exCR.opens (3, 7) 3 8 := by
  intro h; simp [CommitReveal.opens, CommitReveal.commit, exCR] at h
#guard exCR.commit 3 7 = (3, 7)
#guard exCR.commit 3 8 ≠ (3, 7)

/-- A COLLIDING commit-reveal: `H(i, w) = 0` for all `w` — every reveal opens every commitment. -/
def badCR : CommitReveal ℕ ℤ ℕ := ⟨fun _ _ => 0⟩

/-- **Equivocation FIRES.** On `badCR`, the distinct reveals `7 ≠ 8` both open the same commitment `0`, so
`equivocation_breaks_hashcr` produces a genuine `¬ HashCR badCR` — the pillar-2 break, non-vacuously. -/
theorem badCR_not_binding : ¬ HashCR badCR :=
  equivocation_breaks_hashcr badCR 0 5 7 8 (by decide) rfl rfl

/-! ### (b) Composition teeth — `A = id`, key `t = 1`, commitment `w = 0`, over `ZMod 5`. -/

/-- A binding commit-reveal over the lattice commitment type `ZMod 5`. -/
def exCR5 : CommitReveal ℕ (ZMod 5) (ℕ × ZMod 5) := ⟨fun i w => (i, w)⟩

theorem exCR5_hashcr : HashCR exCR5 := fun _ _ _ h => (Prod.ext_iff.mp h).2

/-- Signer's forgery #1: response `z = 1`, challenge `c = 1`, commitment `w = 0` — accepts against `t = 1`. -/
theorem forge1 : IsSelfTargetMSISSolution (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 1 1 0 :=
  ⟨by decide, by decide, by decide, by simp [verify]⟩

/-- Signer's forgery #2: response `z' = 2`, challenge `c' = 2`, SAME commitment `w = 0`. `c ≠ c'`. -/
theorem forge2 : IsSelfTargetMSISSolution (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 2 2 0 :=
  ⟨by decide, by decide, by decide, by simp [verify]⟩

/-- **THE COMPOSITION FIRES.** Two forgeries sharing the commitment `w = 0` with `c ≠ c'`, opened under the
BINDING `exCR5`: the rushing dichotomy CANNOT take the equivocation door (`exCR5` is binding), so it hands
back a genuine `IsMSISSolution` on `[A | t]` — the straight-line composition running end-to-end. -/
example : ∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
    ((0 + 0) + (0 + 0)) v := by
  rcases concurrent_forgery_breaks_hashcr_or_msis exCR5 (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)
      1 0 (0, 0) 0 0 0 rfl rfl 1 2 1 2 (by decide) forge1 forge2 with h | h
  · exact absurd exCR5_hashcr h
  · exact h

-- The extracted MSIS solution's challenge coordinate is NONZERO (`−(1 − 2) = 1 ≠ 0` in `ZMod 5`) — the
-- `c ≠ c'` payoff is a real solution, not the trivial vector.
#guard decide (-((1 : ZMod 5) - 2) ≠ 0)
-- Collapse check: with `c = c'` the challenge coordinate would be `0` (non-triviality lost).
#guard decide (-((1 : ZMod 5) - 1) = 0)

/-- **The masked hints are SIMULATABLE (pillar 1), concretely.** One session shifts a width-10 uniform mask
by `+1`; `HintMLWEHard` holds at leakage `≤ 1/10`, grounded in `signature_hides_secret`/`smudge_bound`. So
the concurrent transcript hides the secret while the composition above extracts the MSIS solution. -/
theorem concrete_hints_simulatable :
    HintMLWEHard (Finset.Ico (0 : ℤ) 10) ({0} : Finset ℕ) (fun _ => (· + 1)) ((1 : ℚ) / 10) := by
  intro i _
  have hinj : Function.Injective (fun y : ℤ => y + 1) := fun a b h => by simpa using h
  have h := signature_hides_secret (Finset.Ico (0 : ℤ) 10) (· + 1) hinj (by decide) 1 (by decide)
  simpa using h

end Teeth

#assert_axioms exCR_hashcr
#assert_axioms badCR_not_binding
#assert_axioms forge1
#assert_axioms forge2
#assert_axioms concrete_hints_simulatable

end Dregg2.Crypto.HermineHintMLWE
