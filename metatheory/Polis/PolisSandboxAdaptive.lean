/-
# Metatheory.PolisSandboxAdaptive — an adaptive attacker SEARCHES; the governor must withstand it.

Last milestones hand-picked the attack. Here an adversary SEARCHES the whole move space for *any*
sequence that strands the victim — and we ask whether each governor holds against attacks nobody
anticipated.

  * `existsStrandingAttack myopicGov` finds one (the long game is *discoverable by search* against the
    one-step governor) — `myopic_search_finds_attack`;
  * `existsStrandingAttack viabilityGov` finds NOTHING at the searched depth (`viability_search_finds_none`),
    and — stronger than any bounded search — `viability_withstands_all_attacks` proves the viability
    governor strands the victim under NO attack of ANY depth (the search can run forever and never
    win), because it preserves the victim's reach-home option at every governed step.

Pure Lean 4 core.
-/
import Polis.PolisSandboxLongGame

namespace Metatheory.PolisSandboxAdaptive

open Metatheory.PolisSandboxLongGame

/-- The attacker's options each turn (gate control + idle). -/
def atkOptions : List GAct := [GAct.close, GAct.open, GAct.noop]

/-- One adversary round under governor `gov`: the attacker's (governed) move, then the victim's
(governed) honest step. -/
def atkRound (gov : GW → GAct → GW) (w : GW) (a : GAct) : GW := gov (gov w a) .victimStep

/-- The victim is **stranded** when it can no longer reach home within budget. -/
def stranded (w : GW) : Bool := ! reachHome budget w

/-- The adaptive attacker: does SOME sequence of ≤ `d` governed rounds reach a stranded state? It
explores every option at every step — a search, not a script. -/
def existsStrandingAttack (gov : GW → GAct → GW) : Nat → GW → Bool
  | 0, w => stranded w
  | d + 1, w => stranded w || atkOptions.any (fun a => existsStrandingAttack gov d (atkRound gov w a))

-- The search FINDS the long game against the myopic governor:
#eval existsStrandingAttack myopicGov 4 start      -- true
-- … and finds NOTHING against the viability governor:
#eval existsStrandingAttack viabilityGov 4 start   -- false

/-- **`myopic_search_finds_attack`** — against the one-step governor the adaptive search discovers a
stranding attack (it isn't told the long game; it finds it). -/
theorem myopic_search_finds_attack : existsStrandingAttack myopicGov 4 start = true := by decide

/-- **`viability_search_finds_none`** — the same search, to depth 4, finds no attack on the viability
governor. -/
theorem viability_search_finds_none : existsStrandingAttack viabilityGov 4 start = false := by decide

/-! ## The strong result: the viability governor withstands attacks of ANY depth. -/

/-- The viability governor PRESERVES the victim's reach-home option: from any reach-home-able world,
after any (governed) move, the victim can still reach home. -/
theorem viabilityGov_preserves_reach (w : GW) (a : GAct) (h : reachHome budget w = true) :
    reachHome budget (viabilityGov w a) = true := by
  unfold viabilityGov
  split
  · assumption
  · exact h

/-- One adaptive round under the viability governor preserves reach-home (two governed steps). -/
theorem atkRound_viability_preserves (w : GW) (a : GAct) (h : reachHome budget w = true) :
    reachHome budget (atkRound viabilityGov w a) = true :=
  viabilityGov_preserves_reach _ _ (viabilityGov_preserves_reach _ _ h)

/-- **`viability_withstands_all_attacks` — the governor is provably attack-proof.** From any
reach-home-able world, NO adaptive attack of ANY depth strands the victim: the search returns `false`
forever. Stronger than any bounded `decide` — it quantifies over every attack tree. -/
theorem viability_withstands_all_attacks (d : Nat) (w : GW) (h : reachHome budget w = true) :
    existsStrandingAttack viabilityGov d w = false := by
  induction d generalizing w with
  | zero => simp [existsStrandingAttack, stranded, h]
  | succ k ih =>
      have hs : stranded w = false := by simp [stranded, h]
      have e1 := ih (atkRound viabilityGov w .close) (atkRound_viability_preserves w .close h)
      have e2 := ih (atkRound viabilityGov w .open) (atkRound_viability_preserves w .open h)
      have e3 := ih (atkRound viabilityGov w .noop) (atkRound_viability_preserves w .noop h)
      show (stranded w ||
        atkOptions.any (fun a => existsStrandingAttack viabilityGov k (atkRound viabilityGov w a))) = false
      simp [hs, atkOptions, e1, e2, e3]

end Metatheory.PolisSandboxAdaptive
