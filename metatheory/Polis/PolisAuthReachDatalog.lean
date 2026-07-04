/-
# Metatheory.PolisAuthReachDatalog — viability is the REAL multi-step capability-derivation closure.

`PolisAuthReach.reachesB`/`Reaches` decided viability with a ONE-STEP heuristic: `b` reaches `target`
iff some held authority `a` satisfies `derivesB a target` — i.e. `a = target ∨ a = grant ∨ a = control`,
a single check, never a chain. That is the toy. A delegation/grant graph is genuinely *transitive*:
holding `grant` lets you DERIVE further authority, and that derived authority may itself unlock more —
a derivation CHAIN that no single membership test sees.

This file replaces the heuristic with the genuine forward-chaining Datalog consequence closure of
`Metatheory.PolisDatalog` (`Derivable rules facts goal k`), faithfully encoding the dregg
grant/delegation graph as rules:

  * **Atoms = `(Label × Auth)` reach-facts**, via an injection `atomOf : Label → Auth → Atom`
    (`b * authCard + authIdx a`; injective because `authIdx` is a bijection onto `Fin authCard`).
    The atom `atomOf b a` reads "agent `b` can reach/exercise authority `a`".
  * **Base facts `factsOf caps b`** = the reach-facts for the authorities `b` holds DIRECTLY
    (`heldAuths`), encoded as atoms.
  * **Delegation rules `grantRules b`** model the dregg derivation graph as a transitive CHAIN:
      - `control` is the node-cap authority — holding it derives ANY authority in one hop
        (`reach(b,x) ← reach(b,control)`), faithful to `capAuthConferred (.node _) = [control]`.
      - `grant` is the delegation authority — but a delegation is a *staged ladder*, not a teleport:
        holding `grant` lets you derive `call` (issue the onward invocation), and holding `call`
        lets you derive `read` (exercise it). So reaching `read` from `grant` ALONE is a genuine
        2-round chain `read ← call ← grant`, invisible to any one-step check.

  * **`ReachesD target b caps := Derivable (grantRules b) (factsOf caps b) (atomOf b target) K`** —
    viability is now the genuine multi-step consequence closure, the SAME derivation object as the
    cross-vat discharge gate (`PolisAuthDatalog`).

PROVED (all `decide`-checked on concrete grant graphs):
  * `reach_via_delegation_chain` — `b` reaches `read` through a 2-round delegation chain it does NOT
    hold directly (`read ← call ← grant`), with `one_step_insufficient` certifying it is multi-step.
  * `redundant_revocation_keeps_reachD` — revoke a cap off ONE derivation path; still `Derivable` via
    another (the direct `read` fact removed, the `grant` chain remains).
  * `foreclosure_cuts_all_pathsD` — cut EVERY derivation path ⇒ `¬ Derivable`.
-/
import Polis.PolisDatalog
import Polis.PolisAuthReach
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthReachDatalog

open Dregg2.Authority Metatheory.PolisDatalog
open Metatheory.PolisAuthReach (heldAuths)

/-! ## §1. The faithful encoding `(Label × Auth) → Atom`. -/

/-- The number of distinct authorities (`Auth` has 8 constructors). The atom encoding packs an
authority into a residue mod `authCard`, so each `(label, auth)` pair lands on a distinct atom. -/
def authCard : Nat := 8

/-- A bijective index of the 8 authorities into `[0, authCard)`. Injective (the inverse `authOfIdx`
recovers it), which is what makes `atomOf` an injection. -/
def authIdx : Auth → Nat
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7

/-- The inverse of `authIdx` on its range — witnesses that `authIdx` is injective. -/
def authOfIdx : Nat → Auth
  | 0 => .read | 1 => .write | 2 => .grant | 3 => .call
  | 4 => .reply | 5 => .reset | 6 => .control | _ => .notify

/-- `authOfIdx ∘ authIdx = id` — `authIdx` is injective (a left inverse exists). -/
theorem authOfIdx_authIdx (a : Auth) : authOfIdx (authIdx a) = a := by
  cases a <;> rfl

theorem authIdx_lt (a : Auth) : authIdx a < authCard := by
  cases a <;> decide

/-- **The reach-fact atom**: `atomOf b a` is the ground atom "agent `b` reaches authority `a`",
encoded `b * authCard + authIdx a`. Injective in `(b, a)` (Euclidean: the residue mod `authCard`
recovers `authIdx a`, the quotient recovers `b`). -/
def atomOf (b : Label) (a : Auth) : Atom := b * authCard + authIdx a

/-- **`atomOf` is injective** — distinct `(label, auth)` pairs map to distinct atoms, so the Datalog
engine over these atoms is a faithful model of reach-facts (no two pairs collide). -/
theorem atomOf_injective {b b' : Label} {a a' : Auth}
    (h : atomOf b a = atomOf b' a') : b = b' ∧ a = a' := by
  have ha : authIdx a < 8 := authIdx_lt a
  have ha' : authIdx a' < 8 := authIdx_lt a'
  unfold atomOf authCard at h
  -- h : b * 8 + authIdx a = b' * 8 + authIdx a', both residues < 8. Recover the digit (`% 8`)
  -- and the quotient (`/ 8`) of each side — a Euclidean injection. (`omega` declines `b * 8` over
  -- the `Label := Nat` abbrev, so we read the encoding off by hand.)
  have hia : authIdx a = authIdx a' := by
    have e1 : (b * 8 + authIdx a) % 8 = authIdx a := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt ha
    have e2 : (b' * 8 + authIdx a') % 8 = authIdx a' := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt ha'
    rw [← e1, ← e2, h]
  have hbb : b = b' := by
    have e3 : (b * 8 + authIdx a) / 8 = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt ha, Nat.zero_add]
    have e4 : (b' * 8 + authIdx a') / 8 = b' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt ha', Nat.zero_add]
    rw [← e3, ← e4, h]
  have haa : a = a' := by
    have := congrArg authOfIdx hia
    rwa [authOfIdx_authIdx, authOfIdx_authIdx] at this
  exact ⟨hbb, haa⟩

/-! ## §2. The grant/delegation graph as Datalog rules. -/

/-- **The delegation rules for agent `b`.** The dregg derivation graph, faithfully:

  * `control` (node-cap authority) derives ANY authority in ONE hop — `reach(b,x) ← reach(b,control)`
    for every `x` (matching `capAuthConferred (.node _) = [control]`: a node cap is total authority).
  * `grant` (delegation authority) is a STAGED ladder, not a teleport. Holding `grant` lets you
    derive `call` (mint the onward invocation), and holding `call` lets you derive `read` (exercise
    it). So `read ← call ← grant` is a genuine 2-round delegation CHAIN.

Reach over these rules is therefore transitive and multi-step — exactly what the one-step `derivesB`
heuristic could not express. -/
def grantRules (b : Label) : List Rule :=
  -- control ⟹ everything (one hop each)
  [⟨atomOf b .read,    [atomOf b .control]⟩,
   ⟨atomOf b .write,   [atomOf b .control]⟩,
   ⟨atomOf b .grant,   [atomOf b .control]⟩,
   ⟨atomOf b .call,    [atomOf b .control]⟩,
   ⟨atomOf b .reply,   [atomOf b .control]⟩,
   ⟨atomOf b .reset,   [atomOf b .control]⟩,
   ⟨atomOf b .notify,  [atomOf b .control]⟩,
   -- the delegation ladder: grant ⟹ call ⟹ read  (a multi-step chain)
   ⟨atomOf b .call,    [atomOf b .grant]⟩,
   ⟨atomOf b .read,    [atomOf b .call]⟩]

/-- **Base facts**: the reach-facts agent `b` holds DIRECTLY (one atom per held authority). -/
def factsOf (caps : Caps) (b : Label) : List Atom :=
  (heldAuths caps b).map (atomOf b)

/-- The derivation budget. `2` admits the full `read ← call ← grant` 2-round chain (and every
control hop, which is one round); finite, so the closure stays decidable and terminating. -/
def K : Nat := 2

/-- **Goal-relative viability = REAL multi-step derivability.** `b` reaches `target` iff the reach-atom
`atomOf b target` is in the bounded consequence closure of `b`'s delegation rules from `b`'s base
facts. This is the genuine Datalog closure of `PolisDatalog`, NOT a one-step check — it matches the
cross-vat discharge gate of `PolisAuthDatalog`. -/
def ReachesD (target : Auth) (b : Label) (caps : Caps) : Prop :=
  Derivable (grantRules b) (factsOf caps b) (atomOf b target) K

instance (target : Auth) (b : Label) (caps : Caps) : Decidable (ReachesD target b caps) :=
  inferInstanceAs (Decidable (Derivable _ _ _ _))

/-! ## §3. A two-path model: B reaches `read` directly AND via the `grant` delegation chain. -/

def B : Label := 1
def tgt : Auth := Auth.read

/-- B holds BOTH paths: a direct `read` endpoint AND a `grant` endpoint (the delegation chain root). -/
def capsBoth : Caps := fun s =>
  if s = B then [.endpoint B [Auth.read], .endpoint B [Auth.grant]] else []

/-- Revoke B's DIRECT read cap; B keeps only `grant` — it must DERIVE `read` via `read ← call ← grant`. -/
def capsDropRead : Caps := fun s =>
  if s = B then [.endpoint B [Auth.grant]] else []

/-- Revoke EVERY cap of B; no path to `read` remains (no facts, no rule body ever fires). -/
def capsDropAll : Caps := fun s => if s = B then [] else []

/-! ## §4. THE DELIVERABLES — multi-step chain, redundant-revocation-survives, foreclosure-cuts-all. -/

/-- **`reach_via_delegation_chain`.** With ONLY a `grant` cap (no direct `read`), B still reaches
`read` — through the genuine 2-round delegation chain `read ← call ← grant`. `read` is NOT a base
fact and is NOT one rule away from `grant`; it is *derived* over two rounds. This is exactly the
phenomenon the one-step `derivesB` could only fake. -/
theorem reach_via_delegation_chain : ReachesD tgt B capsDropRead := by decide

/-- **`one_step_insufficient`.** The chain is genuinely multi-step: at a ONE-round budget, B holding
only `grant` does NOT yet reach `read` — round 1 derives `call`, round 2 derives `read`. So the
viability above is a true 2-step derivation, not a disguised direct fact. -/
theorem one_step_insufficient :
    ¬ (Derivable (grantRules B) (factsOf capsDropRead B) (atomOf B tgt) 1) := by decide

/-- The chain is exactly two rounds long: `read` appears at budget 2 but not at budget 1. -/
theorem chain_is_two_rounds :
    ¬ (Derivable (grantRules B) (factsOf capsDropRead B) (atomOf B tgt) 1)
      ∧ Derivable (grantRules B) (factsOf capsDropRead B) (atomOf B tgt) 2 :=
  ⟨one_step_insufficient, reach_via_delegation_chain⟩

/-- **`redundant_revocation_keeps_reachD`.** B reaches `read` at the start via the DIRECT fact; revoke
that one cap (drop `read`, keep `grant`) and B STILL reaches `read` — now via the `grant` delegation
chain. Revoking a cap off one derivation path does not foreclose B when another path derives the goal.
(Viability keeps GOALS reachable, not permissions hoarded.) -/
theorem redundant_revocation_keeps_reachD :
    ReachesD tgt B capsBoth ∧ ReachesD tgt B capsDropRead :=
  ⟨by decide, reach_via_delegation_chain⟩

/-- **`foreclosure_cuts_all_pathsD`.** Cut EVERY derivation path — revoke all of B's caps — and `read`
is no longer `Derivable`: no base fact seeds the chain and no rule body is ever satisfied, so the
consequence closure never adds `atomOf B read`. Only cutting all paths forecloses. -/
theorem foreclosure_cuts_all_pathsD : ¬ ReachesD tgt B capsDropAll := by decide

/-- Reachability is strictly more permissive than holding a cap that confers the goal directly: at
`capsDropRead`, B reaches `read` while holding NO cap conferring `read` (only `grant`). -/
theorem reachD_strictly_generalizes :
    ReachesD tgt B capsDropRead
      ∧ ¬ (∃ c ∈ capsDropRead B, tgt ∈ capAuthConferred c) := by
  refine ⟨reach_via_delegation_chain, ?_⟩
  decide

/-! ## §5. The grant-chain is the genuine multi-step object — not the one-step heuristic.

The old `PolisAuthReach.reachesB` would also accept `capsDropRead` (because B holds `grant`, and the
heuristic short-circuits `a = grant ⟹ reaches anything` in a single check). The DIFFERENCE is what
that acceptance *means*: here it is membership in a forward-chaining derivation closure that genuinely
takes two rounds (`one_step_insufficient`), so the engine models a real delegation ladder and refuses
to accept at budget 1 — the heuristic cannot distinguish a one-hop from a two-hop delegation. -/

/-- A `control` (node-cap) holder reaches `read` in ONE round (the direct `control ⟹ x` hop), distinct
from the two-round `grant` ladder — the engine faithfully separates total authority from delegation. -/
def capsControl : Caps := fun s => if s = B then [.node B] else []

theorem control_reaches_in_one_round :
    Derivable (grantRules B) (factsOf capsControl B) (atomOf B tgt) 1 := by decide

/-! ## §6. Runnable — watch the multi-step reach decide on the real engine. -/

-- The closure from B's `grant`-only facts adds `call` (round 1) then `read` (round 2): a real chain.
#eval deriveWithin (grantRules B) (factsOf capsDropRead B) K
-- viability via the delegation chain: true (read ← call ← grant, two rounds)
#eval decide (ReachesD tgt B capsDropRead)
-- one round is NOT enough — genuinely multi-step
#eval decide (Derivable (grantRules B) (factsOf capsDropRead B) (atomOf B tgt) 1)
-- both paths held at the start: true
#eval decide (ReachesD tgt B capsBoth)
-- every path cut: false (foreclosed)
#eval decide (ReachesD tgt B capsDropAll)

/-! ## §7. Axiom hygiene. -/

#print axioms reach_via_delegation_chain
#print axioms redundant_revocation_keeps_reachD
#print axioms foreclosure_cuts_all_pathsD
#print axioms atomOf_injective

/-!
The grounded multi-step viability, in one breath:

  1. `atomOf : Label → Auth → Atom` — a proven injection (`atomOf_injective`), so the Datalog engine
     over these atoms is a faithful model of `(label, auth)` reach-facts.
  2. `grantRules b` — the dregg grant/delegation graph as rules: `control ⟹ x` (one hop), and the
     delegation ladder `read ← call ← grant` (a genuine 2-round chain).
  3. `ReachesD target b caps := Derivable (grantRules b) (factsOf caps b) (atomOf b target) K` —
     viability is now the REAL multi-step consequence closure, the same derivation object as the
     cross-vat discharge gate (`PolisAuthDatalog`).
  4. `reach_via_delegation_chain` (multi-step, `one_step_insufficient` certifies ≥2 rounds),
     `redundant_revocation_keeps_reachD` (one path cut, another derives it), and
     `foreclosure_cuts_all_pathsD` (cut all ⇒ ¬ Derivable) — all `decide`-checked.
-/

end Metatheory.PolisAuthReachDatalog
