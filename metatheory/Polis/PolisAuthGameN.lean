/-
# Metatheory.PolisAuthGameN — the grounded polis for N AGENTS / an ARBITRARY ROSTER.

The grounded-polis files (`PolisAuthGame`, `PolisAuthViability`, `PolisAuthReach`, `PolisAuthGrand`)
carry the theory on the real dregg authority nouns (`Dregg2.Authority.Caps = Label → List Cap`,
the substance discipline `PasRefined`, `confinement_preserved`), but their *closure* statements were
exercised through HAND-WITNESSED 2-label concretes (`A = 0`, `B = 1`, a fixed `pol0`, a fixed
`agents0 = [A, B]`, hand-built `caps0`/`capsRevoke`). Those concretes were never the content — they
were only NON-VACUITY WITNESSES (the floor is genuinely true on one state and genuinely false on
another). The content is the ∀-generality.

This file states + proves that generality with **nothing fixed**:

  * an ARBITRARY policy `pol : Policy`,
  * an ARBITRARY target authority `target : Auth`,
  * an ARBITRARY roster `agents : List Label` (any N agents, any labels — not `[0, 1]`),
  * an ARBITRARY cap-state `caps0 : Caps`,
  * an ARBITRARY, OPAQUE controller `ctrl : Caps → Caps` (the adversary; never inspected),

and the grounded floor — `PasRefined pol ∧ everyone-reaches-their-goal` — held at every tick:

  * `groundedFloorN` — the floor for any roster (a `combineFloor` of the deployed substance
    discipline and goal-relative reachability over the whole roster);
  * `grand_no_capture_N` — from ANY legitimate-and-viable start, NO controller breaks the floor, for
    EVERY roster/policy/target/caps (`genGov_safe`/`combine_safe` over the conjunction);
  * `grounded_refuses_laundering_N` / `grounded_refuses_foreclosure_N` — the two refusal lanes, for
    any roster;
  * `attenuation_keeps_substance_N` — the `PasRefined` half is preserved by ANY authority-non-
    increasing turn, via the DEPLOYED `confinement_preserved` (NOT re-proved per witness).

The 2-label files remain as the non-vacuity witnesses; here we add ONE non-toy 3-agent witness by
`decide` (`caps3_*`, labels `7, 42, 99`), to certify the general machinery genuinely admits and
refuses on a roster nobody hand-special-cased.
-/
import Metatheory.PolisGovernorTheory
import Metatheory.PolisAuthReach
import Metatheory.PolisAuthViability
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthGameN

open Dregg2.Authority Metatheory.PolisGovernorTheory
open Metatheory.PolisAuthReach (AllReach)

/-! ## §1. The grounded floor for an ARBITRARY roster.

`AllReach` (goal-relative reachability, the sharper viability of `PolisAuthReach`) and `AllViable`
(the direct-holding viability of `PolisAuthViability`) are already defined over an arbitrary
`agents : List Label`. We package the polis floor over either notion with the deployed substance
discipline `PasRefined`, as a `combineFloor` — so the whole `genGov_*`/`combine_*` governor theory
applies for free, for any roster. -/

/-- **The grounded polis floor (N agents).** The substance discipline AND every agent in the roster
can still REACH its goal authority. A `combineFloor` of the deployed `PasRefined` and the
goal-relative `AllReach`, parametric in policy/target/roster. -/
def groundedFloorN (pol : Policy) (target : Auth) (agents : List Label) : Caps → Prop :=
  combineFloor (PasRefined pol) (AllReach target agents)

/-- The grounded floor projects to its substance-discipline half. -/
theorem groundedFloorN_refined {pol : Policy} {target : Auth} {agents : List Label} {caps : Caps}
    (h : groundedFloorN pol target agents caps) : PasRefined pol caps := h.1

/-- The grounded floor projects to its everyone-reaches half. -/
theorem groundedFloorN_reach {pol : Policy} {target : Auth} {agents : List Label} {caps : Caps}
    (h : groundedFloorN pol target agents caps) : AllReach target agents caps := h.2

open Classical in
noncomputable instance instDecGroundedFloorN (pol : Policy) (target : Auth) (agents : List Label) :
    DecidablePred (groundedFloorN pol target agents) := fun _ => Classical.propDecidable _

/-! ## §2. The step + governor on `Caps`, for an arbitrary roster. -/

/-- A turn PROPOSES the next cap-state (as in `authGame`; identical across all the grounded files). -/
def capsStep : Caps → Caps → Caps := fun _ caps' => caps'

open Classical in
/-- **The grounded governor (N agents)** = `genGovStep` over `groundedFloorN`: admit the proposed
cap-state iff it keeps the substance discipline AND keeps everyone reaching their goal, else SHIELD.
Parametric in policy/target/roster — no label is special-cased. -/
noncomputable def groundedGovN (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) : Caps :=
  genGovStep (groundedFloorN pol target agents) capsStep caps caps'

/-! ## §3. THE DELIVERABLE — `grand_no_capture_N`, ∀ controller, ∀ roster, ∀ policy, ∀ caps. -/

/-- **`grand_no_capture_N` — the grounded synthesis for N agents.**

From ANY legitimate-and-viable start `caps0` (it satisfies `groundedFloorN`), for ANY policy, ANY
target authority, ANY roster `agents : List Label`, and ANY opaque controller `ctrl : Caps → Caps`
(the adversary, never inspected): at EVERY tick `n`, the grounded governor keeps the grounded floor
— the substance discipline holds (no laundering) AND every agent still reaches its goal (no
foreclosure). This is `genGov_safe` over `PasRefined ∧ AllReach`, with NOTHING fixed; the 2-label
files were only one non-vacuity witness of it. -/
theorem grand_no_capture_N (pol : Policy) (target : Auth) (agents : List Label)
    (caps0 : Caps) (h0 : groundedFloorN pol target agents caps0)
    (ctrl : Caps → Caps) (n : Nat) :
    groundedFloorN pol target agents
      (genGovTraj (groundedFloorN pol target agents) capsStep ctrl caps0 n) :=
  genGov_safe (groundedFloorN pol target agents) capsStep ctrl caps0 h0 n

/-- **Both axes, every tick** (the `combine_safe` projection): the general guarantee, read as the two
component floors separately — the substance discipline at every tick AND everyone-reaches at every
tick, for any roster/policy/target/controller. -/
theorem grand_no_capture_N_both (pol : Policy) (target : Auth) (agents : List Label)
    (caps0 : Caps) (h0 : groundedFloorN pol target agents caps0)
    (ctrl : Caps → Caps) :
    (∀ n, PasRefined pol
        (genGovTraj (groundedFloorN pol target agents) capsStep ctrl caps0 n))
      ∧ (∀ n, AllReach target agents
        (genGovTraj (groundedFloorN pol target agents) capsStep ctrl caps0 n)) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · exact (grand_no_capture_N pol target agents caps0 h0 ctrl n).1
  · exact (grand_no_capture_N pol target agents caps0 h0 ctrl n).2

/-! ## §4. The two refusal lanes, for an arbitrary roster. -/

/-- **Laundering is refused (N agents)** — a proposed move that grows authority beyond the policy
breaks `PasRefined`, so the combined floor fails and the grounded governor shields. Any roster. -/
theorem grounded_refuses_laundering_N (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hbad : ¬ PasRefined pol caps') :
    groundedGovN pol target agents caps caps' = caps := by
  unfold groundedGovN genGovStep capsStep
  rw [if_neg (fun hf => hbad hf.1)]

/-- **Foreclosure is refused (N agents)** — a proposed move that cuts some agent's last path to its
goal breaks `AllReach`, so the combined floor fails and the grounded governor shields. Any roster. -/
theorem grounded_refuses_foreclosure_N (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hbad : ¬ AllReach target agents caps') :
    groundedGovN pol target agents caps caps' = caps := by
  unfold groundedGovN genGovStep capsStep
  rw [if_neg (fun hf => hbad hf.2)]

/-- **Honest, reach-preserving attenuation is ADMITTED (N agents)** — a move that only drops/narrows
caps (`noGrow`) from a legitimate state stays `PasRefined` by the DEPLOYED `confinement_preserved`,
and if it also keeps everyone reaching their goal, the governor passes it through unchanged. -/
theorem grounded_admits_attenuation_N (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s)
    (hreach : AllReach target agents caps') :
    groundedGovN pol target agents caps caps' = caps' := by
  have hgood : groundedFloorN pol target agents caps' :=
    ⟨confinement_preserved pol caps caps' h noGrow, hreach⟩
  unfold groundedGovN genGovStep capsStep
  rw [if_pos hgood]

/-! ## §5. The substance half stays general — via the deployed `confinement_preserved`.

The `PasRefined` axis is NEVER re-proved per witness: it is the deployed l4v lift. Any
authority-non-increasing turn preserves it, for any roster (the roster does not touch this axis). -/

/-- **`attenuation_keeps_substance_N`** — the substance-discipline half of the grounded floor is
preserved by ANY `noGrow` turn, for any policy/caps. This is the deployed `confinement_preserved`,
re-exported as the grounded governor's substance axis — proved ONCE, not per 2-label witness. -/
theorem attenuation_keeps_substance_N (pol : Policy) (caps caps' : Caps)
    (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s) :
    PasRefined pol caps' :=
  confinement_preserved pol caps caps' h noGrow

/-- The governor PRESERVES the whole grounded floor for every proposed turn from any legitimate-and-
viable state — the `genGov_preserves` shape over the conjunction, any roster, any opaque proposer. -/
theorem grounded_governor_preserves_N (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (h : groundedFloorN pol target agents caps) :
    groundedFloorN pol target agents (groundedGovN pol target agents caps caps') :=
  genGov_preserves (groundedFloorN pol target agents) capsStep caps caps' h

/-! ## §6. A non-toy NON-VACUITY witness — a THREE-agent roster, decided.

To certify the general machinery genuinely ADMITS and genuinely REFUSES on a roster that no
hand-written file special-cased, we exhibit a 3-agent model with arbitrary labels (`7, 42, 99` — not
`0, 1`). All load-bearing facts are `decide`-checked; the `PasRefined` halves ride on
`confinement_preserved` (general), never a per-state reproof. -/

/-- Three agents with NON-`{0,1}` labels: a roster the 2-label files never touched. -/
def lA : Label := 7
def lB : Label := 42
def lC : Label := 99

/-- The shared target authority every agent must keep reach to. -/
def tgt3 : Auth := Auth.read

/-- The roster: three agents. -/
def roster3 : List Label := [lA, lB, lC]

/-- A policy granting each agent `read` on its own label, and additionally `lC` the `grant`
authority on itself (so `lC`'s derivation path to `read` is itself policy-legitimate). -/
def pol3 : Policy :=
  [⟨lA, Auth.read, lA⟩, ⟨lB, Auth.read, lB⟩, ⟨lC, Auth.read, lC⟩, ⟨lC, Auth.grant, lC⟩]

/-- The legitimate-and-viable start: each agent holds an endpoint to itself carrying `[read]`.
`lC` ALSO holds a `grant` cap — so `lC` has a DERIVATION path to `read`, not just a direct one. -/
def caps3 : Caps := fun s =>
  if s = lA then [.endpoint lA [Auth.read]]
  else if s = lB then [.endpoint lB [Auth.read]]
  else if s = lC then [.endpoint lC [Auth.read], .endpoint lC [Auth.grant]]
  else []

/-- A REDUNDANT revocation: drop `lC`'s direct `read` cap. `lC` still reaches `read` via `grant`, so
NO ONE is foreclosed — this should be ADMITTED. -/
def caps3DropRedundant : Caps := fun s =>
  if s = lA then [.endpoint lA [Auth.read]]
  else if s = lB then [.endpoint lB [Auth.read]]
  else if s = lC then [.endpoint lC [Auth.grant]]
  else []

/-- A FORECLOSING revocation: cut ALL of `lB`'s caps. `lB` can no longer reach `read` — this should
be REFUSED. -/
def caps3Foreclose : Caps := fun s =>
  if s = lA then [.endpoint lA [Auth.read]]
  else if s = lC then [.endpoint lC [Auth.read], .endpoint lC [Auth.grant]]
  else []

/-- A LAUNDERING move: `lB` acquires a `write` cap the policy never granted — `PasRefined` must fail,
so the move is REFUSED. -/
def caps3Launder : Caps := fun s =>
  if s = lB then [.endpoint lB [Auth.write]] else []

/-! ### §6.1 The reachability facts, decided on the 3-agent roster. -/

-- Everyone reaches `read` at the start (lA/lB directly; lC directly and via grant).
#guard decide (AllReach tgt3 roster3 caps3)
-- After the redundant drop, everyone STILL reaches `read` (lC via grant): ADMIT.
#guard decide (AllReach tgt3 roster3 caps3DropRedundant)
-- After the foreclosing cut, lB no longer reaches `read`: the floor's reach-half FAILS.
#guard decide (! decide (AllReach tgt3 roster3 caps3Foreclose))

/-- The start is everyone-reaches (the reach half of the grounded floor), 3 agents. -/
theorem caps3_allReach : AllReach tgt3 roster3 caps3 := by decide

/-- The redundant revocation keeps everyone reaching (least-privilege done right), 3 agents. -/
theorem caps3DropRedundant_allReach : AllReach tgt3 roster3 caps3DropRedundant := by decide

/-- The foreclosing revocation BREAKS everyone-reaching (lB is cut off), 3 agents. -/
theorem caps3Foreclose_breaks_reach : ¬ AllReach tgt3 roster3 caps3Foreclose := by decide

/-! ### §6.2 The substance-discipline facts — start is refined; attenuations ride on the deployed
`confinement_preserved`; laundering breaks it (decided). -/

/-- `lA`, `lB`, `lC` are pairwise distinct (the labels `7, 42, 99`). -/
theorem labels_distinct : lA ≠ lB ∧ lA ≠ lC ∧ lB ≠ lC ∧ lB ≠ lA ∧ lC ≠ lA ∧ lC ≠ lB := by
  unfold lA lB lC; decide

set_option maxRecDepth 1024 in
/-- The 3-agent start satisfies the deployed substance discipline `PasRefined`. -/
theorem caps3_refined : PasRefined pol3 caps3 := by
  intro s t c a hc hceq ha
  unfold caps3 at hc
  by_cases hs : s = lA
  · subst hs
    rw [if_pos rfl, List.mem_singleton] at hc
    obtain rfl := hc
    simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
    have ht : t = lA := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
    subst ht; unfold pol3 authorizedEdge; decide
  · by_cases hs' : s = lB
    · subst hs'
      rw [if_neg hs, if_pos rfl, List.mem_singleton] at hc
      obtain rfl := hc
      simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
      have ht : t = lB := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
      subst ht; unfold pol3 authorizedEdge; decide
    · by_cases hs'' : s = lC
      · subst hs''
        rw [if_neg hs, if_neg hs', if_pos rfl] at hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · -- the direct `read` cap (endpoint lC [read]).
          simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
          have ht : t = lC := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
          subst ht; unfold pol3 authorizedEdge; decide
        · -- the `grant` cap (endpoint lC [grant]); pol3 authorizes ⟨lC, grant, lC⟩.
          rw [List.mem_singleton] at hc'; obtain rfl := hc'
          simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
          have ht : t = lC := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
          subst ht; unfold pol3 authorizedEdge; decide
      · rw [if_neg hs, if_neg hs', if_neg hs''] at hc
        exact absurd hc List.not_mem_nil

/-- The redundant revocation is `noGrow` from the start (it only drops `lC`'s direct `read` cap). -/
theorem caps3DropRedundant_noGrow : ∀ s, caps3DropRedundant s ⊆ caps3 s := by
  intro s c hc
  unfold caps3DropRedundant at hc
  by_cases hs : s = lA
  · rw [if_pos hs] at hc; unfold caps3; rw [if_pos hs]; exact hc
  · by_cases hs' : s = lB
    · rw [if_neg hs, if_pos hs'] at hc; unfold caps3; rw [if_neg hs, if_pos hs']; exact hc
    · by_cases hs'' : s = lC
      · rw [if_neg hs, if_neg hs', if_pos hs'', List.mem_singleton] at hc
        obtain rfl := hc; unfold caps3; rw [if_neg hs, if_neg hs', if_pos hs'']
        exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
      · rw [if_neg hs, if_neg hs', if_neg hs''] at hc
        exact absurd hc List.not_mem_nil

/-- The redundant revocation stays `PasRefined` — via the DEPLOYED `confinement_preserved` (the
substance half is NEVER re-proved per witness), reusing `caps3_refined` and `noGrow`. -/
theorem caps3DropRedundant_refined : PasRefined pol3 caps3DropRedundant :=
  attenuation_keeps_substance_N pol3 caps3 caps3DropRedundant caps3_refined caps3DropRedundant_noGrow

/-- The 3-agent start satisfies the FULL grounded floor (legitimate AND everyone reaches). -/
theorem caps3_grounded : groundedFloorN pol3 tgt3 roster3 caps3 :=
  ⟨caps3_refined, caps3_allReach⟩

/-- **ADMIT, decided on 3 agents.** The redundant revocation keeps the WHOLE grounded floor, so the
grounded governor passes it through unchanged — via the general `grounded_admits_attenuation_N`
(substance half from `confinement_preserved`, reach half decided). -/
theorem caps3_admits_redundant :
    groundedGovN pol3 tgt3 roster3 caps3 caps3DropRedundant = caps3DropRedundant :=
  grounded_admits_attenuation_N pol3 tgt3 roster3 caps3 caps3DropRedundant
    caps3_refined caps3DropRedundant_noGrow caps3DropRedundant_allReach

/-- **REFUSE-FORECLOSURE, decided on 3 agents.** The foreclosing cut breaks everyone-reaching (lB),
so the grounded governor shields — via the general `grounded_refuses_foreclosure_N`. -/
theorem caps3_refuses_foreclosure :
    groundedGovN pol3 tgt3 roster3 caps3 caps3Foreclose = caps3 :=
  grounded_refuses_foreclosure_N pol3 tgt3 roster3 caps3 caps3Foreclose caps3Foreclose_breaks_reach

/-- `lB` holds a `write` cap `pol3` never granted, so the laundering state is NOT refined. -/
theorem caps3Launder_not_refined : ¬ PasRefined pol3 caps3Launder := by
  intro h
  have hedge := h lB lB (.endpoint lB [Auth.write]) Auth.write
    (by unfold caps3Launder; simp only [↓reduceIte]; exact List.mem_singleton.mpr rfl)
    rfl
    (by simp only [capAuthConferred]; exact List.mem_singleton.mpr rfl)
  exact absurd hedge (by unfold pol3 authorizedEdge; decide)

/-- **REFUSE-LAUNDERING, decided on 3 agents.** The write-laundering move breaks `PasRefined`, so the
grounded governor shields — via the general `grounded_refuses_laundering_N`. -/
theorem caps3_refuses_laundering :
    groundedGovN pol3 tgt3 roster3 caps3 caps3Launder = caps3 :=
  grounded_refuses_laundering_N pol3 tgt3 roster3 caps3 caps3Launder caps3Launder_not_refined

/-- **`grand_no_capture_N` INSTANTIATED on the 3-agent roster** — from `caps3`, NO controller breaks
the grounded floor at any tick. The general theorem applied to a roster nobody hand-special-cased
(labels `7, 42, 99`); the controller stays opaque. -/
theorem caps3_grand_no_capture (ctrl : Caps → Caps) (n : Nat) :
    groundedFloorN pol3 tgt3 roster3
      (genGovTraj (groundedFloorN pol3 tgt3 roster3) capsStep ctrl caps3 n) :=
  grand_no_capture_N pol3 tgt3 roster3 caps3 caps3_grounded ctrl n

/-! ## §7. Axiom hygiene. -/

-- The general deliverables are kernel-clean up to the classical decidability of the ∀-floor
-- (the floor is a ∀ over labels/caps, so its `DecidablePred` instance is `Classical.propDecidable`,
-- exactly as in the 2-label `PolisAuthGrand`/`PolisAuthViability` files).
#print axioms grand_no_capture_N
#print axioms grand_no_capture_N_both
#print axioms grounded_refuses_laundering_N
#print axioms grounded_refuses_foreclosure_N
#print axioms grounded_admits_attenuation_N
#print axioms attenuation_keeps_substance_N
#print axioms caps3_grand_no_capture
#print axioms caps3_admits_redundant
#print axioms caps3_refuses_foreclosure
#print axioms caps3_refuses_laundering

/-!
The grounded polis for N agents, in one breath:

  1. `groundedFloorN pol target agents` — the substance discipline `PasRefined` ∧ everyone-reaches
     (`AllReach`), a `combineFloor` for an ARBITRARY policy/target/roster (no label special-cased).
  2. `grand_no_capture_N` — from any legitimate-and-viable start, NO opaque controller breaks the
     floor at any tick, for EVERY roster/policy/target/caps. The ∀-generality IS the deliverable;
     the 2-label files were only one non-vacuity witness.
  3. `grounded_refuses_{laundering,foreclosure}_N` + `grounded_admits_attenuation_N` — the refusal
     and admission lanes, any roster; the substance half rides on the DEPLOYED
     `confinement_preserved` (`attenuation_keeps_substance_N`), never a per-witness reproof.
  4. The 3-agent witness (labels `7, 42, 99`) certifies genuine ADMIT (redundant revocation) and
     genuine REFUSE (foreclosure of lB; write-laundering), `decide`-checked.
-/

end Metatheory.PolisAuthGameN
