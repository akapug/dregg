/-
# Dregg2.Circuit.Spec.swissenliven — INDEPENDENT full-state spec + executor⟺spec for `enlivenRefA`.
-/
import Dregg2.Circuit.Spec.swissframe

namespace Dregg2.Circuit.Spec.SwissEnliven

open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Auth)

def enlivenReceipt (actor exporter : CellId) : Turn :=
  { actor := actor, src := exporter, dst := exporter, amt := 0 }

def enlivenRecord (e : SwissRecord) : SwissRecord :=
  { e with refcount := e.refcount + 1 }

def enlivenSwissPost (ss : List SwissRecord) (sw : Nat) (e : SwissRecord) : List SwissRecord :=
  replaceSwiss ss sw (enlivenRecord e)

def enlivenSwissUpdate (ss : List SwissRecord) (sw : Nat) (claimed : List Auth) : Option (List SwissRecord) :=
  match findSwiss ss sw with
  | none   => none
  | some e =>
      if rightsNarrowerOrEqual claimed e.rights then
        some (enlivenSwissPost ss sw e)
      else none

def EnlivenGuard (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth) : Prop :=
  stateAuthB s.kernel.caps actor exporter = true
  ∧ ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
      ∧ rightsNarrowerOrEqual claimed e.rights

theorem enlivenRecord_correct (e : SwissRecord) :
    (enlivenRecord e).swiss = e.swiss
    ∧ (enlivenRecord e).exporter = e.exporter
    ∧ (enlivenRecord e).target = e.target
    ∧ (enlivenRecord e).rights = e.rights
    ∧ (enlivenRecord e).refcount = e.refcount + 1
    ∧ (enlivenRecord e).cert = e.cert := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem enlivenRecord_lookup (ss : List SwissRecord) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) :
    findSwiss (enlivenSwissPost ss sw e) sw = some (enlivenRecord e) := by
  have hsw : (enlivenRecord e).swiss = sw := by
    rw [(enlivenRecord_correct e).1, findSwiss_swiss_eq hf]
  exact findSwiss_replaceSwiss_self ss sw e (enlivenRecord e) hf hsw

theorem enlivenSwissUpdate_some (ss : List SwissRecord) (sw : Nat) (claimed : List Auth) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) (hr : rightsNarrowerOrEqual claimed e.rights) :
    enlivenSwissUpdate ss sw claimed = some (enlivenSwissPost ss sw e) := by
  simp only [enlivenSwissUpdate, hf, if_pos hr]

/-- Existential post-state: guard + kernel witness + log head (queue-atomic style). -/
def EnlivenSpec (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth)
    (s' : RecChainedState) : Prop :=
  EnlivenGuard s sw actor exporter claimed
  ∧ ∃ k', swissEnlivenK s.kernel sw claimed = some k'
    ∧ s' = { kernel := k', log := enlivenReceipt actor exporter :: s.log }

theorem enlivenChain_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) :
    swissEnlivenChainA s sw actor exporter claimed = some s'
      ↔ EnlivenSpec s sw actor exporter claimed s' := by
  unfold EnlivenSpec swissEnlivenChainA
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth]
    cases hk : swissEnlivenK s.kernel sw claimed with
    | none =>
      simp only [hk]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨⟨_, ⟨_, ⟨e, ⟨hf, _⟩⟩⟩, ⟨_, hf'⟩⟩
        exact absurd hf' (by simp [hk])
    | some k' =>
      simp only [hk]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨⟨hauth, ?_⟩, k', rfl, rfl⟩
        unfold swissEnlivenK at hk
        cases hf : findSwiss s.kernel.swiss sw with
        | none => simp [hf] at hk
        | some e =>
          simp only [hf] at hk
          by_cases hr : rightsNarrowerOrEqual claimed e.rights
          · simp only [if_pos hr] at hk; exact ⟨e, hf, hr⟩
          · simp only [if_neg hr] at hk; exact absurd hk (by simp)
      · rintro ⟨_, k'', hk', hs'⟩
        simp only [Option.some.injEq] at hk'; subst hk'
        cases s'; simpa using hs'
  · rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth', _, _⟩, _⟩; exact absurd hauth' hauth

theorem execFullA_enliven_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = some s'
      ↔ EnlivenSpec s sw actor exporter claimed s' := by
  simp only [execFullA]
  exact enlivenChain_iff_spec s sw actor exporter claimed s'

theorem enliven_spec_bumps_refcount (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) (e : SwissRecord)
    (hf : findSwiss s.kernel.swiss sw = some e)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    findSwiss s'.kernel.swiss sw = some (enlivenRecord e) := by
  rcases (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h with ⟨hg, k', hk, hs'⟩
  obtain ⟨_, ⟨e', hf', hr⟩⟩ := hg.2
  have heq : e' = e := Option.some.inj (hf.symm.trans hf')
  subst heq
  unfold swissEnlivenK at hk
  simp only [hf, if_pos hr] at hk
  rcases hs' with ⟨hker, _⟩
  rw [← hker, hk]
  exact enlivenRecord_lookup s.kernel.swiss sw e hf

theorem enliven_spec_non_amplifying (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
      ∧ rightsNarrowerOrEqual claimed e.rights :=
  (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h |>.1.2

theorem enliven_spec_balance_neutral (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  rcases (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h with ⟨_, k', _, hs'⟩
  rcases hs' with ⟨hker, _⟩
  rcases withSwiss_preserves_rest s.kernel k'.swiss with ⟨_, _, _, _, _, _, _, hBal, hAcc, _, _, _, _, _, _, _⟩
  rw [← hker]; exact ⟨hBal, hAcc⟩

theorem enliven_spec_authorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    stateAuthB s.kernel.caps actor exporter = true :=
  (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h |>.1.1

theorem enliven_rejects_unauthorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (hbad : stateAuthB s.kernel.caps actor exporter ≠ true) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  simp only [execFullA, enlivenChain_iff_spec, if_neg hbad]

theorem enliven_rejects_absent (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (hf : findSwiss s.kernel.swiss sw = none) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  simp only [execFullA, enlivenChain_iff_spec, swissEnlivenK, hf]

theorem enliven_rejects_amplifying (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (e : SwissRecord) (hf : findSwiss s.kernel.swiss sw = some e)
    (hbad : rightsNarrowerOrEqual claimed e.rights = false) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  simp only [execFullA, enlivenChain_iff_spec, swissEnlivenK, hf, if_neg hbad]

#assert_axioms enlivenRecord_correct
#assert_axioms enlivenRecord_lookup
#assert_axioms enlivenSwissUpdate_some
#assert_axioms enlivenChain_iff_spec
#assert_axioms execFullA_enliven_iff_spec
#assert_axioms enliven_spec_bumps_refcount
#assert_axioms enliven_spec_non_amplifying
#assert_axioms enliven_spec_balance_neutral
#assert_axioms enliven_spec_authorized
#assert_axioms enliven_rejects_unauthorized
#assert_axioms enliven_rejects_absent
#assert_axioms enliven_rejects_amplifying

end Dregg2.Circuit.Spec.SwissEnliven