/-
# Metatheory.PolisAuthLive — inter-agent delegation rules DERIVED FROM THE LIVE CELLS.

`PolisAuthDelegate` proved the SHAPE of inter-agent delegation (`atomOf Y target ← [atomOf X grant]`,
`delegation_unlocks_other`, `inter_agent_foreclosure`) — but those rules were HAND-AUTHORED:
`delegRules`/`chainRules3` were literal `List Rule` constants, not read off any cap-state. A polis
that reasons over an author's idea of the delegation graph is still a toy; the genuine object reasons
over the delegation graph the LIVE CELLS actually present.

This file closes that rung. `delegRulesOf` is a TOTAL function of the live cap-state: it folds over the
cells, and for every cell `s` that holds a cap conferring authority over ANOTHER label `t`
(`.endpoint t rights` with `Auth.grant ∈ rights`, or a `.node t` control cap), it EMITS the inter-agent
delegation rules `atomOf t a ← [atomOf s Auth.grant]` for the authorities `a` that cap delegates. So the
rule-base is read off the real cells — revoke the grant cap and the rule simply is not emitted.

  * `delegRulesOf cells caps : List Rule` — the live inter-agent delegation rules (a fold over cells).
  * `ReachesLive target b cells caps := Derivable (delegRulesOf cells caps) (factsOf caps b)
    (atomOf b target) K` — viability over rules DERIVED FROM THE LIVE CELLS, multi-step.
  * `AllReachLive` + `groundedFloorLive := combineFloor (PasRefined pol) (AllReachLive …)` +
    `grand_no_capture_Live` — the grand no-capture synthesis over GENUINE multi-agent reachability read
    off the real cells (`genGov_safe` over the conjunction, any roster/policy/target/controller).
  * `live_inter_agent_foreclosure` — a concrete 3-cell `Caps` where agent `t` reaches `target` ONLY
    because cell `s` holds the grant cap; revoke `s`'s grant and `delegRulesOf` no longer emits the
    rule, so `t` can no longer derive `target` — foreclosed (`decide`-checked on a real `Caps`).
  * `live_delegation_admitted` — with the grant cap present, the derived rule fires and `t` reaches
    `target` (`decide`-checked).

The remaining toy edges are the scan domain `cells` (an explicit
roster, since `Caps := Label → List Cap` has no enumerable domain) and the fixed delegated-authority
set — both named, neither load-bearing for the foreclosure/admission content.
-/
import Metatheory.PolisDatalog
import Metatheory.PolisAuthReachDatalog
import Metatheory.PolisGovernorTheory
import Metatheory.PolisAuthViability
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthLive

open Dregg2.Authority Metatheory.PolisDatalog Metatheory.PolisGovernorTheory
open Metatheory.PolisAuthReachDatalog (atomOf atomOf_injective factsOf K)

/-! ## §1. The live delegation rules — read off the real cap-state.

For ONE cell `s` and ONE cap it holds, `capDelegRules s c` emits the inter-agent delegation rules the
cap licenses. The genuinely-new object: the body atom names `s` (the grantor's grant-fact) and the head
atom names the cap's TARGET `t` (the grantee), so the rule crosses an agent boundary, and it exists in
the rule-base ONLY because `s` actually holds the cap. -/

/-- The authorities a delegation cap over `t` lets `t` derive from `s`'s grant. A grant-endpoint at `s`
delegates to `t` whatever rights it carries (besides `grant` itself); a `.node t` control cap is total
authority, so it delegates `control` (whence `t` derives anything via its own `grantRules`). We use the
cap's `capAuthConferred` minus `grant` for endpoints, and `[control]` for node caps — read off the cap. -/
def delegatedAuths : Cap → List Auth
  | .endpoint _ rights => rights.filter (fun a => a ≠ Auth.grant)
  | .node _            => [Auth.control]
  | .null              => []

/-- Does this cap, held at `s`, license an inter-agent delegation to ANOTHER label `t`? A grant-bearing
endpoint to `t ≠ s`, or a node (control) cap to `t ≠ s`. (Self-caps `t = s` are intra-agent — handled by
`grantRules`, not here.) Returns the target label option. -/
def delegTarget (s : Label) : Cap → Option Label
  | .endpoint t rights => if t ≠ s ∧ Auth.grant ∈ rights then some t else none
  | .node t            => if t ≠ s then some t else none
  | .null              => none

/-- **The delegation rules a single held cap emits.** If cap `c` at cell `s` delegates to `t`, emit one
rule `atomOf t a ← [atomOf s Auth.grant]` per delegated authority `a` — `t` derives `a` from `s`'s
grant-fact. The body atom is `s`'s grant; so the rule fires only when `s` actually holds (and thus has a
base-fact for) `grant`. If the cap is not a delegation cap, no rule. -/
def capDelegRules (s : Label) (c : Cap) : List Rule :=
  match delegTarget s c with
  | some t => (delegatedAuths c).map (fun a => ⟨atomOf t a, [atomOf s Auth.grant]⟩)
  | none   => []

/-- **The live inter-agent delegation rules.** Fold over the cells `cells`; for each cell `s`, scan the
caps it HOLDS in the live state (`caps s`) and emit each cap's delegation rules. A total function of the
cap-state — the rule-base is exactly what the live cells present. Revoke a grant cap and its rule is no
longer emitted. -/
def delegRulesOf (cells : List Label) (caps : Caps) : List Rule :=
  cells.flatMap (fun s => (caps s).flatMap (capDelegRules s))

/-! ## §2. Viability over the LIVE-derived rules. -/

/-- **The pooled base facts of the live society.** A polis pools its participants' held reach-facts into
one shared derivation base: the reach-atoms for every authority every scanned cell holds DIRECTLY. The
inter-agent delegation rules (whose body atoms name the grantor) fire against THIS pool — `g`'s grant
fact and `t`'s own facts coexist, exactly as the cross-vat discharge gate pools facts. -/
def pooledFactsOf (cells : List Label) (caps : Caps) : List Atom :=
  cells.flatMap (factsOf caps)

/-- **`ReachesLive`** — agent `b` reaches `target` iff `atomOf b target` is in the bounded consequence
closure of the rules DERIVED FROM THE LIVE CELLS (`delegRulesOf cells caps`) from the POOLED facts of the
live society. Multi-step (budget `K`), and the rule-base is read off the real cap-state — not
hand-authored. The pool means a grantor's grant-fact is available to fire the delegation rule it emits. -/
def ReachesLive (target : Auth) (b : Label) (cells : List Label) (caps : Caps) : Prop :=
  Derivable (delegRulesOf cells caps) (pooledFactsOf cells caps) (atomOf b target) K

instance (target : Auth) (b : Label) (cells : List Label) (caps : Caps) :
    Decidable (ReachesLive target b cells caps) :=
  inferInstanceAs (Decidable (Derivable _ _ _ _))

/-- **`AllReachLive`** — every agent in the roster reaches its goal over the live-derived rules. -/
def AllReachLive (target : Auth) (agents cells : List Label) (caps : Caps) : Prop :=
  ∀ b ∈ agents, ReachesLive target b cells caps

instance instDecAllReachLive (target : Auth) (agents cells : List Label) (caps : Caps) :
    Decidable (AllReachLive target agents cells caps) :=
  inferInstanceAs (Decidable (∀ b ∈ agents, ReachesLive target b cells caps))

/-! ## §3. The grounded floor on live multi-agent reachability, and the grand synthesis. -/

/-- **The grounded polis floor over LIVE-derived viability.** The deployed substance discipline
`PasRefined pol` AND every agent in the roster can still DERIVE its goal authority through the rules read
off the live cells. A `combineFloor` — so the whole `genGov_*`/`combine_*` governor theory applies. -/
def groundedFloorLive (pol : Policy) (target : Auth) (agents cells : List Label) : Caps → Prop :=
  combineFloor (PasRefined pol) (AllReachLive target agents cells)

/-- The grounded floor projects to its substance-discipline half. -/
theorem groundedFloorLive_refined {pol : Policy} {target : Auth} {agents cells : List Label}
    {caps : Caps} (h : groundedFloorLive pol target agents cells caps) : PasRefined pol caps := h.1

/-- The grounded floor projects to its everyone-derives-from-live-cells half. -/
theorem groundedFloorLive_reach {pol : Policy} {target : Auth} {agents cells : List Label}
    {caps : Caps} (h : groundedFloorLive pol target agents cells caps) :
    AllReachLive target agents cells caps := h.2

open Classical in
noncomputable instance instDecGroundedFloorLive
    (pol : Policy) (target : Auth) (agents cells : List Label) :
    DecidablePred (groundedFloorLive pol target agents cells) := fun _ => Classical.propDecidable _

/-- A turn PROPOSES the next cap-state (identical to the other grounded files). -/
def capsStep : Caps → Caps → Caps := fun _ caps' => caps'

open Classical in
/-- **The grounded governor over LIVE-derived viability** = `genGovStep` over `groundedFloorLive`:
admit the proposed cap-state iff it keeps the substance discipline AND keeps everyone deriving its goal
through the rules read off the live cells, else SHIELD. Parametric in policy/target/roster/scan-domain. -/
noncomputable def groundedGovLive (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps caps' : Caps) : Caps :=
  genGovStep (groundedFloorLive pol target agents cells) capsStep caps caps'

/-- **`grand_no_capture_Live` — the grounded synthesis over GENUINE multi-agent reachability from the
live cells.** From ANY legitimate-and-viable start `caps0`, for ANY policy / target / roster /
scan-domain, and ANY opaque controller `ctrl` (the adversary, never inspected): at EVERY tick the
grounded governor keeps the grounded floor — the substance discipline holds (no laundering) AND every
agent still DERIVES its goal through the rules DERIVED FROM THE LIVE CELLS (no foreclosure). This is
`genGov_safe` over `PasRefined ∧ AllReachLive`. -/
theorem grand_no_capture_Live (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps0 : Caps) (h0 : groundedFloorLive pol target agents cells caps0)
    (ctrl : Caps → Caps) (n : Nat) :
    groundedFloorLive pol target agents cells
      (genGovTraj (groundedFloorLive pol target agents cells) capsStep ctrl caps0 n) :=
  genGov_safe (groundedFloorLive pol target agents cells) capsStep ctrl caps0 h0 n

/-- **Both axes, every tick** (the `combine_safe` projection): the substance discipline at every tick
AND everyone-derives-from-the-live-cells at every tick, for any roster/policy/target/controller. -/
theorem grand_no_capture_Live_both (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps0 : Caps) (h0 : groundedFloorLive pol target agents cells caps0) (ctrl : Caps → Caps) :
    (∀ n, PasRefined pol
        (genGovTraj (groundedFloorLive pol target agents cells) capsStep ctrl caps0 n))
      ∧ (∀ n, AllReachLive target agents cells
        (genGovTraj (groundedFloorLive pol target agents cells) capsStep ctrl caps0 n)) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · exact (grand_no_capture_Live pol target agents cells caps0 h0 ctrl n).1
  · exact (grand_no_capture_Live pol target agents cells caps0 h0 ctrl n).2

/-! ## §4. The two refusal lanes + admission, on the live-derived viability. -/

/-- **Laundering is refused** — a proposed move that grows authority beyond the policy breaks
`PasRefined`, so the combined floor fails and the grounded governor shields. -/
theorem grounded_refuses_laundering_Live (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps caps' : Caps) (hbad : ¬ PasRefined pol caps') :
    groundedGovLive pol target agents cells caps caps' = caps := by
  unfold groundedGovLive genGovStep capsStep
  rw [if_neg (fun hf => hbad hf.1)]

/-- **Foreclosure is refused** — a proposed move under which some agent's goal is no longer derivable
from the live-derived rules breaks `AllReachLive`, so the grounded governor shields. -/
theorem grounded_refuses_foreclosure_Live (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps caps' : Caps) (hbad : ¬ AllReachLive target agents cells caps') :
    groundedGovLive pol target agents cells caps caps' = caps := by
  unfold groundedGovLive genGovStep capsStep
  rw [if_neg (fun hf => hbad hf.2)]

/-- **Honest, derivation-preserving attenuation is ADMITTED** — a `noGrow` move from a legitimate state
stays `PasRefined` via the DEPLOYED `confinement_preserved`, and if it ALSO keeps everyone deriving its
goal from the live cells, the governor passes it through unchanged. -/
theorem grounded_admits_attenuation_Live (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps caps' : Caps) (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s)
    (hreach : AllReachLive target agents cells caps') :
    groundedGovLive pol target agents cells caps caps' = caps' := by
  have hgood : groundedFloorLive pol target agents cells caps' :=
    ⟨confinement_preserved pol caps caps' h noGrow, hreach⟩
  unfold groundedGovLive genGovStep capsStep
  rw [if_pos hgood]

/-- The governor PRESERVES the whole grounded floor for every proposed turn from any legitimate-and-
viable state — `genGov_preserves` over the conjunction. -/
theorem grounded_governor_preserves_Live (pol : Policy) (target : Auth) (agents cells : List Label)
    (caps caps' : Caps) (h : groundedFloorLive pol target agents cells caps) :
    groundedFloorLive pol target agents cells (groundedGovLive pol target agents cells caps caps') :=
  genGov_preserves (groundedFloorLive pol target agents cells) capsStep caps caps' h

/-! ## §5. The concrete LIVE model — a 3-cell society where one cell's grant cap unlocks another.

Cells: `g := 10` (the grantor), `t := 20` (the grantee), `o := 30` (a bystander). `g` holds a self
`grant` cap (so the society's pooled facts contain `atomOf g grant`) AND a delegation endpoint to `t`
carrying `[read, grant]`. The delegation cap makes `delegRulesOf` emit the live rule
`atomOf t read ← [atomOf g grant]` — read directly off `g`'s held cap. The grantee `t` holds NOTHING of
its own, so its ONLY route to `target := read` is that emitted rule firing on `g`'s pooled grant-fact:

  `g` holds the delegation cap ⟹ `delegRulesOf` emits `atomOf t read ← [atomOf g grant]`
    ⟹ that rule fires on the pooled fact `atomOf g grant` ⟹ `t` derives `read`.

Revoke `g`'s delegation endpoint and the rule is no longer emitted — `t` is foreclosed. -/

/-- The grantor cell. -/
def g : Label := 10
/-- The grantee cell. -/
def t : Label := 20
/-- A bystander cell. -/
def o : Label := 30
/-- The authority delegated around. -/
def target : Auth := Auth.read
/-- The scan domain (the live cells). -/
def cells : List Label := [g, t, o]

/-- **The live cap-state WITH the grant delegation.** `g` holds a self `grant` cap (so the pooled facts
contain `atomOf g grant`) AND a delegation endpoint to `t` carrying `[read, grant]` (so `delegRulesOf`
emits `atomOf t read ← [atomOf g grant]`). `o` holds a self `read` endpoint (an unrelated bystander
fact). `t` holds NOTHING of its own — its only route to `read` is `g`'s delegation cap. -/
def capsLive : Caps := fun s =>
  if s = g then [.endpoint g [Auth.grant], .endpoint t [Auth.read, Auth.grant]]
  else if s = o then [.endpoint o [Auth.read]]
  else []   -- `t` holds nothing on its own: its only route to `read` is `g`'s delegation cap.

/-- **The live cap-state with `g`'s grant delegation REVOKED.** `g` keeps its self `grant` cap but the
delegation endpoint to `t` is gone, so `delegRulesOf` no longer emits `atomOf t read ← [atomOf g grant]`.
`t` still holds nothing — now there is NO rule and NO fact deriving `t`'s `read`. -/
def capsRevoked : Caps := fun s =>
  if s = g then [.endpoint g [Auth.grant]]   -- the delegation endpoint to `t` is revoked.
  else if s = o then [.endpoint o [Auth.read]]
  else []

/-! ### §5.1 The live foreclosure + admission, decided on the real cap-state. -/

-- WITH the grant delegation, `t` reaches `read` (the live-emitted rule fires on `g`'s grant fact).
#guard decide (ReachesLive target t cells capsLive)
-- WITHOUT it (delegation revoked), `t` no longer reaches `read` — the rule is not emitted.
#guard decide (! decide (ReachesLive target t cells capsRevoked))

/-- **`live_delegation_admitted`.** With `g`'s grant delegation cap PRESENT, the rule
`atomOf t read ← [atomOf g grant]` is emitted by `delegRulesOf` (read off the live cell `g`), and it
fires on `g`'s `grant` base fact — so grantee `t` reaches `target`. Genuine cross-agent unlock, the rule
derived from the LIVE cells. -/
theorem live_delegation_admitted : ReachesLive target t cells capsLive := by decide

/-- **`live_inter_agent_foreclosure`.** Revoke `g`'s grant delegation cap (`capsRevoked`): `delegRulesOf`
no longer emits `atomOf t read ← [atomOf g grant]`, and `t` holds nothing of its own, so `t` can NO
LONGER derive `target`. Cell `g`'s revocation forecloses `t` — and it does so by CHANGING THE RULE-BASE
the polis reasons over, because the rule-base is read off the live cells. -/
theorem live_inter_agent_foreclosure : ¬ ReachesLive target t cells capsRevoked := by decide

/-- `g` dominates `t`: `t` reaches `target` exactly when `g` holds the delegation cap, and not when it is
revoked. Same roster, same goal — only `g`'s held cap toggles `t`'s reachability, via the live-derived
rule-base. -/
theorem live_g_dominates_t :
    ReachesLive target t cells capsLive ∧ ¬ ReachesLive target t cells capsRevoked :=
  ⟨live_delegation_admitted, live_inter_agent_foreclosure⟩

/-- The unlock is genuinely cross-agent and genuinely live: the delegation rule that fires is present in
`delegRulesOf cells capsLive` and ABSENT from `delegRulesOf cells capsRevoked`. The rule-base literally
changed when the cap was revoked. -/
theorem live_rule_emitted_iff_cap_held :
    (⟨atomOf t target, [atomOf g Auth.grant]⟩ : Rule) ∈ delegRulesOf cells capsLive
      ∧ (⟨atomOf t target, [atomOf g Auth.grant]⟩ : Rule) ∉ delegRulesOf cells capsRevoked := by
  decide

/-! ### §5.2 The substance-discipline half — start refined; the foreclosing revocation rides
`confinement_preserved`. -/

/-- A policy authorizing `g`'s self `grant`, `g`'s delegation edge to `t` (both `read` and `grant`), and
`o`'s self `read`. So `capsLive` is policy-legitimate. -/
def polLive : Policy :=
  [⟨g, Auth.grant, g⟩, ⟨g, Auth.read, t⟩, ⟨g, Auth.grant, t⟩, ⟨o, Auth.read, o⟩]

set_option maxRecDepth 1024 in
/-- `capsLive` satisfies the deployed substance discipline `PasRefined` — every conferred authority is a
policy edge. -/
theorem capsLive_refined : PasRefined polLive capsLive := by
  intro s x c a hc hceq ha
  by_cases hs : s = g
  · subst hs
    simp only [capsLive, ↓reduceIte] at hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · -- g's self grant cap (endpoint g [grant]).
      simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
      have hx : x = g := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
      subst hx; unfold polLive authorizedEdge g; decide
    · -- g's delegation endpoint to t (endpoint t [read, grant]).
      rw [List.mem_singleton] at hc'; obtain rfl := hc'
      have hx : x = t := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
      subst hx
      simp only [capAuthConferred] at ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · unfold polLive authorizedEdge g t; decide
      · rw [List.mem_singleton] at ha'; subst ha'
        unfold polLive authorizedEdge g t; decide
  · by_cases ho : s = o
    · subst ho
      simp only [capsLive, if_neg hs, ↓reduceIte] at hc
      rw [List.mem_singleton] at hc; obtain rfl := hc
      simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
      have hx : x = o := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
      subst hx; unfold polLive authorizedEdge o; decide
    · simp only [capsLive, if_neg hs, if_neg ho] at hc
      exact absurd hc List.not_mem_nil

/-- The revocation is `noGrow` from `capsLive` (it only drops `g`'s delegation endpoint to `t`). -/
theorem capsRevoked_noGrow : ∀ s, capsRevoked s ⊆ capsLive s := by
  intro s c hc
  by_cases hs : s = g
  · subst hs
    simp only [capsRevoked, ↓reduceIte, List.mem_singleton] at hc
    obtain rfl := hc
    simp only [capsLive, ↓reduceIte]
    exact List.mem_cons_self
  · by_cases ho : s = o
    · subst ho
      simp only [capsRevoked, if_neg hs, ↓reduceIte] at hc
      simp only [capsLive, if_neg hs, ↓reduceIte]; exact hc
    · simp only [capsRevoked, if_neg hs, if_neg ho] at hc
      exact absurd hc List.not_mem_nil

/-- The revocation stays `PasRefined` — via the DEPLOYED `confinement_preserved`, never re-proved. -/
theorem capsRevoked_refined : PasRefined polLive capsRevoked :=
  confinement_preserved polLive capsLive capsRevoked capsLive_refined capsRevoked_noGrow

/-! ### §5.3 The grand synthesis, instantiated on the live society. -/

/-- The roster whose viability the polis floor tracks: the grantee `t` (and we could add others; here
the load-bearing agent is `t`, whose reachability is live-derived from `g`'s cap). -/
def rosterLive : List Label := [t]

/-- The start `capsLive` is everyone-derives over the live rules (here: `t` reaches `read`). -/
theorem capsLive_allReachLive : AllReachLive target rosterLive cells capsLive := by decide

/-- After revoking `g`'s delegation, the roster's viability BREAKS — `t` no longer derives `read`. -/
theorem capsRevoked_breaks_allReachLive : ¬ AllReachLive target rosterLive cells capsRevoked := by
  decide

/-- `capsLive` satisfies the FULL grounded floor over live-derived viability. -/
theorem capsLive_grounded : groundedFloorLive polLive target rosterLive cells capsLive :=
  ⟨capsLive_refined, capsLive_allReachLive⟩

/-- **REFUSE-FORECLOSURE on the live society.** Revoking `g`'s delegation cap breaks the live-derived
reach of `t`, so the grounded governor shields — the rule the polis reasoned over is gone, foreclosing
`t`. The sharper, live refusal: a move is shielded when it removes the very CAP whose delegation rule
kept the grantee viable. -/
theorem capsLive_refuses_foreclosure :
    groundedGovLive polLive target rosterLive cells capsLive capsRevoked = capsLive :=
  grounded_refuses_foreclosure_Live polLive target rosterLive cells capsLive capsRevoked
    capsRevoked_breaks_allReachLive

/-- **`grand_no_capture_Live` INSTANTIATED on the live society** — from `capsLive`, NO controller breaks
the grounded floor at any tick, with viability = derivation over rules read off the LIVE CELLS. -/
theorem capsLive_grand_no_capture (ctrl : Caps → Caps) (n : Nat) :
    groundedFloorLive polLive target rosterLive cells
      (genGovTraj (groundedFloorLive polLive target rosterLive cells) capsStep ctrl capsLive n) :=
  grand_no_capture_Live polLive target rosterLive cells capsLive capsLive_grounded ctrl n

/-! ## §6. Faithfulness of the cross-agent claim. -/

/-- The grantor `g` and grantee `t` are DISTINCT agents (labels `10 ≠ 20`), so the delegation crosses a
real boundary — it is not `t` deriving from itself under an alias (`atomOf_injective` makes their atoms
distinct). -/
theorem grantor_grantee_distinct : atomOf g Auth.grant ≠ atomOf t Auth.read := by
  intro h
  exact absurd (atomOf_injective h).1 (by unfold g t; decide)

/-! ## §7. Runnable — watch the live-derived delegation decide on the real engine. -/

-- The rules emitted from the LIVE cells (one per delegated authority of g's endpoint to t):
#eval delegRulesOf cells capsLive
-- After revocation, the t-delegation rules are gone:
#eval delegRulesOf cells capsRevoked
-- t reaches read WITH the grant cap (the live rule fires): true.
#eval decide (ReachesLive target t cells capsLive)
-- t does NOT reach read with it revoked (the rule is not emitted): false.
#eval decide (ReachesLive target t cells capsRevoked)

/-! ## §8. Axiom hygiene. -/

#print axioms live_delegation_admitted
#print axioms live_inter_agent_foreclosure
#print axioms live_rule_emitted_iff_cap_held
#print axioms grand_no_capture_Live
#print axioms capsLive_refuses_foreclosure
#print axioms capsLive_grand_no_capture
#print axioms capsLive_refined
#print axioms grantor_grantee_distinct

/-!
The live-grounded polis, in one breath:

  1. `delegRulesOf cells caps` — the inter-agent delegation rules DERIVED FROM THE LIVE CELLS: a fold
     over the cells emitting `atomOf t a ← [atomOf s grant]` for every grant/control cap a cell `s`
     holds over another label `t`. Revoke the cap and the rule is not emitted.
  2. `ReachesLive`/`AllReachLive` — multi-step viability over the live-derived rules.
  3. `groundedFloorLive := combineFloor (PasRefined pol) (AllReachLive …)` + `grand_no_capture_Live` —
     the grand no-capture synthesis over genuine multi-agent reachability read off the real cells.
  4. `live_delegation_admitted` (grant cap present ⟹ `t` reaches `target`) + `live_inter_agent_
     foreclosure` (cap revoked ⟹ rule not emitted ⟹ `t` foreclosed) + `live_rule_emitted_iff_cap_held`
     (the rule-base literally changes with the cap) — all `decide`-checked on a real 3-cell `Caps`.
-/

end Metatheory.PolisAuthLive
