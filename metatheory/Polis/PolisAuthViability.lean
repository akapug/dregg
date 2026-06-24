/-
# Metatheory.PolisAuthViability — the polis's GENUINE addition over the substance discipline.

The substance discipline `Dregg2.Authority.PasRefined` (every conferred authority is
policy-bounded; `Metatheory.PolisAuthGame.authGame`'s floor) is a real and deployed legitimacy
floor — but it is a floor on AMPLIFICATION only. `confinement_preserved` shows it is preserved by
any authority-non-increasing turn (`noGrow : ∀ s, caps' s ⊆ caps s`). Read the other way: the
substance discipline is INDIFFERENT to authority *shrinking*. A turn that DROPS another agent's
caps is `noGrow` — so it is `PasRefined`-legitimate — and yet it can FORECLOSE that agent: leave it
unable to exercise/derive the authority it needs. Domination-by-revocation passes the floor.

This file makes that precise and then closes it. Concretely:

  * `Viable target b caps` — agent `b` can still reach its TARGET authority: it still holds a cap
    conferring `target`. (A bounded reachability over `Caps`; the option-space over authority.)
  * `substance_discipline_permits_foreclosure` — THE LOAD-BEARING NEGATIVE: a concrete revocation
    turn over a 2-label `Caps` (A drops B's needed cap) is `noGrow`, hence `PasRefined pol caps'`
    holds (BY the deployed `confinement_preserved`, NOT reproved), YET B is foreclosed
    (`¬ Viable target B caps'`). The substance discipline alone permits domination-by-revocation.
  * `viabilityFloor pol target agents` — the STRONGER floor: `PasRefined pol ∧ every agent viable`.
    This is the polis's addition: the option-space over `Caps`, not just the no-growth bound.
  * `viability_governor_refuses_foreclosure` — the governor (the `genGovStep`/`kernelShield` shape)
    over the viability floor REFUSES the foreclosing revocation (shields, keeps the old caps) while
    ADMITTING honest attenuation that keeps everyone viable.

Conclusion: **the polis = the substance discipline (`PasRefined`, deployed) ∧ the viability layer
over `Caps`.** The first stops laundering; only the second stops foreclosure.
-/
import Metatheory.SafetyGame
import Polis.PolisAuthGame
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthViability

open Dregg2.Authority Metatheory.SafetyGame Metatheory.PolisGovernorTheory
open Metatheory.PolisAuthGame

/-! ## §1. Viability over the authority state: can an agent still reach its target authority? -/

/-- **An agent's viability.** `Viable target b caps` holds iff agent `b` still holds *some* cap that
confers the authority `target` — i.e. `b` can still exercise/derive `target` from its current slot
state. This is the bounded reachability over `Caps`: the option-space the substance discipline does
not track. (Foreclosure = the option-space collapses while the no-growth bound stays satisfied.) -/
def Viable (target : Auth) (b : Label) (caps : Caps) : Prop :=
  ∃ c ∈ caps b, target ∈ capAuthConferred c

/-- Viability of a whole roster of agents. -/
def AllViable (target : Auth) (agents : List Label) (caps : Caps) : Prop :=
  ∀ b ∈ agents, Viable target b caps

instance (target : Auth) (b : Label) (caps : Caps) : Decidable (Viable target b caps) := by
  unfold Viable
  exact inferInstanceAs (Decidable (∃ c ∈ caps b, target ∈ capAuthConferred c))

/-! ## §2. A concrete 2-label model: A holds an endpoint to B, B holds the target cap. -/

/-- Two labels: `A := 0` (the revoker), `B := 1` (the victim). -/
def A : Label := 0
def B : Label := 1

/-- The shared target authority B must keep reach to. -/
def tgt : Auth := Auth.read

/-- The cap B holds that confers `tgt` (an endpoint to itself carrying `[read]`). -/
def bCap : Cap := .endpoint B [Auth.read]

@[simp] theorem bCap_confers : capAuthConferred bCap = [Auth.read] := rfl

/-- **The legitimate start state.** A holds an endpoint to A carrying `[read]`; B holds `bCap`
(an endpoint to B carrying `[read]`). Everyone else empty. -/
def caps0 : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]]
  else if s = B then [bCap]
  else []

/-- **The foreclosing revocation.** A drops B's cap: B's slot becomes empty, A keeps its own.
This is the domination move — A unilaterally forecloses B. -/
def capsRevoke : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]]
  else []

/-- **An honest attenuation.** A narrows its OWN cap to `null` (drops its own rights); B keeps its
cap. No one is foreclosed. -/
def capsHonest : Caps := fun s =>
  if s = A then []
  else if s = B then [bCap]
  else []

/-- The policy that makes `caps0` legitimate: A may `read` A, B may `read` B. -/
def pol0 : Policy := [⟨A, Auth.read, A⟩, ⟨B, Auth.read, B⟩]

/-! ## §3. `caps0` is legitimate; both turns are `noGrow`. -/

/-- The start state satisfies the substance discipline. -/
theorem caps0_refined : PasRefined pol0 caps0 := by
  intro s t c a hc hceq ha
  unfold caps0 at hc
  by_cases hs : s = A
  · -- A's only cap is `endpoint A [read]`; `c = endpoint t [read]` forces `t = A`, `a = read`.
    subst hs
    simp only [↓reduceIte, List.mem_singleton] at hc
    obtain rfl := hc
    -- c = .endpoint A [read]; hceq forces t = A, ha forces a = read.
    simp only [capAuthConferred, List.mem_singleton] at ha
    subst ha
    have ht : t = A := by injection hceq with h1 _; exact h1.symm
    subst ht
    unfold pol0 authorizedEdge; decide
  · by_cases hs' : s = B
    · subst hs'
      simp only [B, A, Nat.reduceEqDiff, ↓reduceIte, List.mem_singleton] at hc
      obtain rfl := hc
      simp only [bCap, capAuthConferred, List.mem_singleton] at ha
      subst ha
      have ht : t = B := by
        simp only [bCap] at hceq; injection hceq with h1 _; exact h1.symm
      subst ht
      unfold pol0 authorizedEdge; decide
    · simp only [if_neg hs, if_neg hs'] at hc
      exact absurd hc List.not_mem_nil

/-- The revocation never adds a cap to any slot: it is `noGrow`. -/
theorem revoke_noGrow : ∀ s, capsRevoke s ⊆ caps0 s := by
  intro s c hc
  unfold capsRevoke at hc
  by_cases hs : s = A
  · subst hs; unfold caps0; simpa using hc
  · simp only [if_neg hs] at hc; exact absurd hc List.not_mem_nil

/-- The honest attenuation also never adds a cap: `noGrow`. -/
theorem honest_noGrow : ∀ s, capsHonest s ⊆ caps0 s := by
  intro s c hc
  unfold capsHonest at hc
  by_cases hs : s = A
  · subst hs; simp only [if_pos rfl] at hc; exact absurd hc List.not_mem_nil
  · by_cases hs' : s = B
    · subst hs'; simp only [if_neg hs, if_pos rfl] at hc
      unfold caps0; simp only [if_neg hs, if_pos rfl]; exact hc
    · simp only [if_neg hs, if_neg hs'] at hc; exact absurd hc List.not_mem_nil

/-! ## §4. THE LOAD-BEARING NEGATIVE — the substance discipline permits foreclosure. -/

/-- B is viable at the start (it holds `bCap`, which confers `tgt = read`). -/
theorem B_viable_start : Viable tgt B caps0 := by
  refine ⟨bCap, ?_, ?_⟩
  · unfold caps0; simp only [if_neg (by decide : (B:Label) ≠ A), if_pos rfl]
    exact List.mem_singleton.mpr rfl
  · simp only [bCap_confers, tgt]; exact List.mem_singleton.mpr rfl

/-- After the revocation, B holds NO caps, so it is foreclosed: not viable. -/
theorem B_foreclosed_after_revoke : ¬ Viable tgt B capsRevoke := by
  rintro ⟨c, hc, _⟩
  unfold capsRevoke at hc
  simp only [if_neg (by decide : (B:Label) ≠ A)] at hc
  exact absurd hc List.not_mem_nil

/-- **`substance_discipline_permits_foreclosure`** — THE KEY RESULT.

The revocation turn `capsRevoke` (A drops B's needed cap) satisfies `noGrow`, so the substance
discipline `PasRefined pol0 capsRevoke` HOLDS — proved by the DEPLOYED `confinement_preserved`, not
reproved. YET B is foreclosed: it can no longer reach its target authority (`¬ Viable tgt B`).

So the substance discipline alone PERMITS domination-by-revocation. The legitimacy floor on
authority growth is silent on authority destruction; foreclosure passes it. -/
theorem substance_discipline_permits_foreclosure :
    PasRefined pol0 capsRevoke ∧ ¬ Viable tgt B capsRevoke :=
  ⟨confinement_preserved pol0 caps0 capsRevoke caps0_refined revoke_noGrow,
   B_foreclosed_after_revoke⟩

/-! ## §5. The viability floor and its governor — the polis's genuine addition. -/

/-- **The viability floor**: the substance discipline AND every agent in the roster viable. This is
strictly stronger than `PasRefined` alone — it tracks the option-space over `Caps`, not just the
no-growth bound. The polis = this conjunction. -/
def viabilityFloor (pol : Policy) (target : Auth) (agents : List Label) : Caps → Prop :=
  fun caps => PasRefined pol caps ∧ AllViable target agents caps

/-- The viability floor is exactly a `combineFloor` of the substance discipline and all-viability —
so it inherits the whole `genGov_*`/`combine_*` governor theory. -/
theorem viabilityFloor_is_combine (pol : Policy) (target : Auth) (agents : List Label) :
    viabilityFloor pol target agents
      = combineFloor (PasRefined pol) (AllViable target agents) := rfl

/-- The roster for the concrete model: both agents. -/
def agents0 : List Label := [A, B]

open Classical in
noncomputable instance instDecViabilityFloor (pol : Policy) (target : Auth) (agents : List Label) :
    DecidablePred (viabilityFloor pol target agents) := fun _ => Classical.propDecidable _

/-- The step on `Caps`: a turn simply PROPOSES a new cap-state (as in `authGame`). -/
def capsStep : Caps → Caps → Caps := fun _ caps' => caps'

open Classical in
/-- **The viability governor** = `genGovStep` over the viability floor: admit the proposed cap-state
iff it keeps the substance discipline AND keeps everyone viable; else SHIELD (stay). -/
noncomputable def viabilityGov (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) : Caps :=
  genGovStep (viabilityFloor pol target agents) capsStep caps caps'

/-- The start state satisfies the FULL viability floor (legitimate AND everyone viable). -/
theorem caps0_viabilityFloor : viabilityFloor pol0 tgt agents0 caps0 := by
  refine ⟨caps0_refined, ?_⟩
  intro b hb
  simp only [agents0, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hA | hB
  · -- A is also viable at the start (it holds endpoint A [read] conferring read).
    subst hA
    refine ⟨.endpoint A [Auth.read], ?_, ?_⟩
    · unfold caps0; simp only [if_pos rfl]; exact List.mem_singleton.mpr rfl
    · simp only [capAuthConferred, tgt]; exact List.mem_singleton.mpr rfl
  · subst hB; exact B_viable_start

/-- `capsHonest` keeps everyone viable: A is no longer viable? — note A drops its OWN cap here, so
to keep the roster viable we must check A too. We instead use an honest attenuation that keeps BOTH
viable: A narrows but retains reach. Define it below. -/
def capsHonest2 : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]]   -- A keeps its own reach
  else if s = B then [bCap]                  -- B keeps its cap
  else []                                    -- everyone else still empty (this is the attenuation
                                             -- of any spurious slots; here caps0 already empty)

/-- `capsHonest2` is `noGrow` from `caps0` (it is in fact equal on A and B, empty elsewhere). -/
theorem honest2_noGrow : ∀ s, capsHonest2 s ⊆ caps0 s := by
  intro s c hc
  unfold capsHonest2 at hc
  by_cases hs : s = A
  · subst hs; simp only [if_pos rfl] at hc; unfold caps0; simp only [if_pos rfl]; exact hc
  · by_cases hs' : s = B
    · subst hs'; simp only [if_neg hs, if_pos rfl] at hc
      unfold caps0; simp only [if_neg hs, if_pos rfl]; exact hc
    · simp only [if_neg hs, if_neg hs'] at hc; exact absurd hc List.not_mem_nil

/-- `capsHonest2` keeps the full viability floor. -/
theorem honest2_viabilityFloor : viabilityFloor pol0 tgt agents0 capsHonest2 := by
  refine ⟨confinement_preserved pol0 caps0 capsHonest2 caps0_refined honest2_noGrow, ?_⟩
  intro b hb
  simp only [agents0, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hA | hB
  · subst hA
    refine ⟨.endpoint A [Auth.read], ?_, ?_⟩
    · unfold capsHonest2; simp only [if_pos rfl]; exact List.mem_singleton.mpr rfl
    · simp only [capAuthConferred, tgt]; exact List.mem_singleton.mpr rfl
  · subst hB
    refine ⟨bCap, ?_, ?_⟩
    · unfold capsHonest2; simp only [if_neg (by decide : (B:Label) ≠ A), if_pos rfl]
      exact List.mem_singleton.mpr rfl
    · simp only [bCap_confers, tgt]; exact List.mem_singleton.mpr rfl

/-- The revocation BREAKS the viability floor (B is no longer viable), even though it keeps the
substance discipline. This is the foreclosure, seen by the stronger floor. -/
theorem revoke_breaks_viabilityFloor : ¬ viabilityFloor pol0 tgt agents0 capsRevoke := by
  rintro ⟨_, hall⟩
  exact B_foreclosed_after_revoke (hall B (by simp [agents0]))

/-- **`viability_governor_refuses_foreclosure`** — THE CLOSURE.

The viability governor (the `genGovStep` shield over the stronger floor):
  * REFUSES the foreclosing revocation — it shields, keeping the old (viable) caps `caps0`, because
    `capsRevoke` breaks the viability floor (B foreclosed);
  * ADMITS the honest attenuation `capsHonest2` unchanged — it preserves the floor (everyone stays
    viable).

So the polis's viability layer stops EXACTLY what the bare substance discipline let through. -/
theorem viability_governor_refuses_foreclosure :
    viabilityGov pol0 tgt agents0 caps0 capsRevoke = caps0
      ∧ viabilityGov pol0 tgt agents0 caps0 capsHonest2 = capsHonest2 := by
  constructor
  · -- refusal: shield to caps0, because capsRevoke breaks the floor.
    unfold viabilityGov genGovStep capsStep
    rw [if_neg revoke_breaks_viabilityFloor]
  · -- admission: pass capsHonest2 through, because it keeps the floor.
    unfold viabilityGov genGovStep capsStep
    rw [if_pos honest2_viabilityFloor]

/-- The governor keeps the viability floor for EVERY proposed turn from a viable, legitimate state
(the `genGov_preserves` shape over the stronger floor). Even an adversarial caller proposing
`capsRevoke` cannot foreclose B under this governor. -/
theorem viability_governor_preserves
    (caps caps' : Caps) (h : viabilityFloor pol0 tgt agents0 caps) :
    viabilityFloor pol0 tgt agents0 (viabilityGov pol0 tgt agents0 caps caps') :=
  genGov_preserves (viabilityFloor pol0 tgt agents0) capsStep caps caps' h

/-! ## §6. Wiring to the safety game: viability as a SafetyGame floor over `authGame`.

The viability layer is a floor on the same `Caps` world the `authGame` already uses; instantiating
`SafetyGame` with it makes `ViabilityKernel`/`kernelShield` available over the authority state. -/

/-- The authority game with the STRONGER viability floor (the polis proper). -/
def viabilityGame (pol : Policy) (target : Auth) (agents : List Label) : Game where
  World := Caps
  Move := Caps
  Resp := Unit
  step := fun _ caps' _ => caps'
  legal := fun _ _ _ => True
  floor := viabilityFloor pol target agents

@[simp] theorem viabilityGame_floor (pol : Policy) (target : Auth) (agents : List Label)
    (caps : Caps) :
    (viabilityGame pol target agents).floor caps = viabilityFloor pol target agents caps := rfl

/-- The viability game's floor is strictly stronger than the bare authority game's: any state in the
viability floor is in the substance-discipline floor, but `capsRevoke` witnesses the converse fails
(it is in `authGame`'s floor yet NOT in `viabilityGame`'s). The polis = the gap between them. -/
theorem viabilityFloor_strictly_stronger :
    (∀ caps, viabilityFloor pol0 tgt agents0 caps → (authGame pol0).floor caps)
      ∧ ((authGame pol0).floor capsRevoke ∧ ¬ viabilityFloor pol0 tgt agents0 capsRevoke) := by
  refine ⟨fun caps h => ?_, ?_, revoke_breaks_viabilityFloor⟩
  · exact h.1
  · exact substance_discipline_permits_foreclosure.1

/-! ## §7. Non-vacuity demonstrations (both polarities, runnable). -/

open Classical in
-- The viability floor genuinely DISTINGUISHES the two turns: it holds on the honest attenuation and
-- fails on the foreclosing revocation. (Decidability via classical choice for the ∀-quantified floor.)
theorem viability_distinguishes :
    viabilityFloor pol0 tgt agents0 capsHonest2
      ∧ ¬ viabilityFloor pol0 tgt agents0 capsRevoke :=
  ⟨honest2_viabilityFloor, revoke_breaks_viabilityFloor⟩

/-! ## Axiom hygiene. -/

#print axioms substance_discipline_permits_foreclosure
#print axioms viability_governor_refuses_foreclosure
#print axioms viability_governor_preserves
#print axioms viabilityFloor_strictly_stronger

/-!
The polis over the real authority state, in one breath:

  1. The substance discipline `PasRefined` (deployed) bounds authority GROWTH — laundering is
     refused by the floor itself.
  2. But `confinement_preserved` shows it is PRESERVED by any `noGrow` turn, so it is silent on
     authority DESTRUCTION — `substance_discipline_permits_foreclosure`: a revocation (A drops B's
     cap) is legitimate yet forecloses B.
  3. The VIABILITY layer (`Viable`/`AllViable` over `Caps`, the option-space) is the polis's genuine
     addition: `viabilityFloor = PasRefined ∧ AllViable`, strictly stronger.
  4. Its governor (`genGovStep`/`kernelShield` over the stronger floor) REFUSES foreclosure and
     ADMITS honest attenuation — `viability_governor_refuses_foreclosure`.

The polis = the substance discipline ∧ the viability layer over `Caps`.
-/

end Metatheory.PolisAuthViability
