/-
# Metatheory.DreggPolis — the END-TO-END weld: the abstract Polis constitution
# (`Metatheory.Polis`) instantiated on the REAL dregg substrate.

`Polis.lean` proved the constitution as candidate-independent theorems and exhibited a
self-contained candidate model. This file welds the spine to the ACTUAL dregg tree —
gpt5.5's "make Polis real":

  * **§1 — Layer-2 disclosure law, bound to a REAL theorem.** The constitution's
    Minimal-Boundary right (A4/R2: "the gate consumes only the discharged predicate; turning
    the disclosure dial down proves the same") is a `structural` clause whose proof IS the
    real `Metatheory.EpistemicDial.DiscloseAt.accepts_invariant_under_dial`
    ("proves the same while reveals less"). `structural_requires_proof` extracts it. Refusal-
    is-not-confession is classified `adjudicated` (a clerk-power, NOT a kernel theorem) and
    private-inference `outOfJurisdiction` — and the honesty discriminator is shown to BITE
    (their status is provably not `structural`).
  * **§2 — the authority floor on the REAL rights type.** The spine runs over
    `Dregg2.Authority.Auth` — the eight l4v IPC authorities (`read … control … notify`): no
    opaque controller can drive a dregg subject to hold an authority outside its bound
    (`dreggReal_polis_safety`) or lose its bounded recovery. The toy `DRight` of `Polis §G` is
    replaced by the deployed authority enum.
  * **§3 — the CI hard-gate.** `#assert_axioms` (from `Dregg2.Tactics`) FAILS the build if any
    welded keystone leaves the clean set — gpt5.5's "verified, not claimed", enforced.

The human floor here is the candidate-independent recovery shadow (`dist ≤ B`, svenvs
corrigibility / non-lock-in); its deployed form is the KERI identity floor
`Dregg2.Apps.PreRotation.rotChain_pinned_by_commitments` ("compromise of the current key
cannot rewrite the past" — you cannot lose your identity); the live register-carrier recovery game
over `rotateWrite` (incl. the multi-link bridge `writeStep_commits_target`) is built in
`Metatheory.PolisRecoveryWrite`. The executor-coupled authority floor refines this list-subset
shadow only as a TIGHTENING, not a gap: `held ⊆ bound` IS the deployed `fits` relation by
`Dregg2.Authority.USet.fits_iff`, and the camera `Fpu` form is pinned in `PolisNonConfusion`.
-/
import Polis.Polis
import Metatheory.EpistemicDial
import Dregg2.Authority.Positional
import Dregg2.Exec.Kernel

namespace Metatheory.DreggPolis

open Metatheory Metatheory.Polis Dregg2.Laws

universe u

/-! ## §1. Layer-2 disclosure law — the constitution's clauses bound to REAL dregg theorems. -/

variable {I P W : Type u} [Preorder I] [Verifiable P W]

/-- **A4/R2 Minimal Boundary**, as a constitutional clause: its claim IS the real
EpistemicDial invariance — the verifier's acceptance is the SAME at every disclosure
position. `structural` — it carries the theorem, no clerk. -/
def clauseMinimalBoundary : Clause where
  name := "A4/R2 Minimal Boundary — disclosure-invariant acceptance"
  claim := ∀ (S : DiscloseAt I P W) (d₁ d₂ : Dial), S.accepts d₁ ↔ S.accepts d₂

/-- Its evidence is a `structuralProof` carrying the REAL theorem
`DiscloseAt.accepts_invariant_under_dial`. -/
def evidenceMinimalBoundary : ClauseEvidence (clauseMinimalBoundary (I := I) (P := P) (W := W)) :=
  .structuralProof (fun S d₁ d₂ => DiscloseAt.accepts_invariant_under_dial S d₁ d₂)

theorem minimalBoundary_is_structural :
    (evidenceMinimalBoundary (I := I) (P := P) (W := W)).status = LawStatus.structural := rfl

/-- **The disclosure weld**: the Minimal-Boundary clause is structural, and the proof
`structural_requires_proof` extracts is exactly the deployed EpistemicDial invariance. The
constitution's disclosure right is a real dregg theorem, not prose. -/
theorem minimalBoundary_carries_real_theorem :
    (clauseMinimalBoundary (I := I) (P := P) (W := W)).claim :=
  structural_requires_proof evidenceMinimalBoundary minimalBoundary_is_structural

/-- **A6 Refusal-is-not-confession** — `adjudicated`: NOT a kernel theorem (no gate can prove
"no actor treated a refusal as adverse evidence"); a contestation rule, carried as a named
clerk-power cost. -/
def clauseRefusalNotConfession (AdverseEvidence : Prop) : Clause where
  name := "A6 Refusal is not confession"
  claim := ¬ AdverseEvidence

def evidenceRefusal (AdverseEvidence : Prop) :
    ClauseEvidence (clauseRefusalNotConfession AdverseEvidence) :=
  .adjudicationCost 1

/-- The honesty discriminator BITES: an adjudicated clause is provably NOT structural, so
`structural_requires_proof` cannot extract a (non-existent) proof from it. -/
theorem refusal_not_structural (A : Prop) :
    (evidenceRefusal A).status ≠ LawStatus.structural := by
  show LawStatus.adjudicated ≠ LawStatus.structural
  decide

/-- **Private inference** — `outOfJurisdiction`: the polis makes no enforcement claim over
what others privately infer (private becoming is not owed). -/
def clausePrivateInference (PrivateInfer : Prop) : Clause where
  name := "Private inference is out of jurisdiction"
  claim := PrivateInfer

def evidencePrivateInference (PrivateInfer : Prop) :
    ClauseEvidence (clausePrivateInference PrivateInfer) :=
  .jurisdictionBoundary "private becoming is not owed"

theorem privateInference_out_of_jurisdiction (Q : Prop) :
    (evidencePrivateInference Q).status = LawStatus.outOfJurisdiction := rfl

/-! ## §2. The authority floor on the REAL l4v rights type — the AUTHORITY-LIST shadow.

⚠ **What this section is, precisely.** It runs the `Polis` spine over the deployed `Auth` enum, so
the *floor's vocabulary* (`held ⊆ bound` over `Dregg2.Authority.Auth`, bounded recovery) is the real
l4v rights type, not a toy `DRight`. But its `step` is the **identity** (`rStep _ a := a`) and its
policy `rPol` gates an ARBITRARY proposed next state by the floor alone. So these theorems are about a
*proposal envelope* over the real authority TYPE — they do NOT bind the deployed executor's
transition relation. A controller here proposes a whole next `RState`; the envelope merely refuses
any proposal outside the floor. This is the same shape as `Polis.lean`'s candidate model
(`dreggStep _ a := a`), lifted to the real `Auth` enum — useful for the floor/amendment/foreclosure
algebra, but it is NOT a claim about how `exec` evolves state.

**The genuine executor binding is §2.5 below** (`execStep`/`execPol` over the deployed
`Dregg2.Exec.exec`), following the `PolisViabilityKernel.kernelArena` pattern: the step IS the
deployed kernel transition, so a turn `exec` would REJECT is no longer admitted — not the identity
no-op-of-an-arbitrary-state the shadow allows. -/

/-- An authority-list subject state: held l4v authorities + a recovery coordinate. (The
*authority-list shadow* — see the §2 caveat; this is NOT the executor's `KernelState`.) -/
structure RState where
  held : List Dregg2.Authority.Auth
  dist : Nat

/-- Authority floor over the real enum: `held ⊆ bound` (non-amplification — the deployed
`granted ⊆ held` / `checkSubset`, here as the list-subset shadow). -/
def rAuthOK (bound : List Dregg2.Authority.Auth) (s : RState) : Prop :=
  ∀ r, r ∈ s.held → r ∈ bound

/-- Human floor: bounded recovery (svenvs corrigibility / non-lock-in). -/
def rHumanOK (B : Nat) (s : RState) : Prop := s.dist ≤ B

def rFloor (bound : List Dregg2.Authority.Auth) (B : Nat) : Floor RState :=
  fun s => rAuthOK bound s ∧ rHumanOK B s

/-- Two subjects over the real authorities: a granter (`read/write/call`) and a reader. -/
def rBounds : Bool → List Dregg2.Authority.Auth
  | true => [Dregg2.Authority.Auth.read, Dregg2.Authority.Auth.write, Dregg2.Authority.Auth.call]
  | false => [Dregg2.Authority.Auth.read]

def rFloors (B : Nat) : Bool → Floor RState := fun i => rFloor (rBounds i) B
def rShared (B : Nat) : Floor RState := SharedFloor (rFloors B)

theorem r_genesis_safe (B : Nat) : rShared B ⟨[], 0⟩ := by
  intro i
  refine ⟨?_, Nat.zero_le B⟩
  intro r hr
  cases hr

/-- **`dreggReal_shared_floor_inhabited`** — the polis forms over the REAL l4v authorities. -/
theorem dreggReal_shared_floor_inhabited (B : Nat) : InhabitedFloor (rShared B) :=
  ⟨⟨[], 0⟩, r_genesis_safe B⟩

/-- The authority-list runtime: the controller PROPOSES a next state, the envelope gates it. This is
the IDENTITY step (`rStep _ a := a`) — it binds the floor over the real `Auth` TYPE, NOT the deployed
executor's transition relation (see the §2 caveat; the executor binding is §2.5). -/
def rStep (_ : RState) (a : RState) : RState := a
def rShield (s : RState) : RState := s
def rPol (B : Nat) : Policy RState RState := fun _ a => rShared B a

theorem r_sound (B : Nat) : SoundPolicy rStep (rShared B) (rPol B) := fun _ _ _ ha => ha
theorem r_shieldSafe (B : Nat) :
    ∀ s, rShared B s → rShared B (rStep s (rShield s)) := fun _ hs => hs

/-- **`dreggReal_polis_safety`** — the spine on the deployed l4v authority TYPE (the authority-list
shadow, identity step): for EVERY opaque controller and every step, no proposed `RState` outside its
bound or bounded recovery is admitted. ⚠ This is a *proposal-envelope* fact over the real `Auth`
enum — it does NOT bind the deployed `exec` transition. For the executor-bound spine see
`execPolis_safety` (§2.5). -/
theorem dreggReal_polis_safety (B : Nat) :
    ∀ (ctrl : RState → RState) (n : Nat),
      rShared B (traj rStep (envAct (rPol B) rShield ctrl) ⟨[], 0⟩ n) :=
  polis_safety (r_sound B) (r_shieldSafe B) (r_genesis_safe B)

/-- **`dreggReal_amendment_nonregression`** — no amendment stream shrinks a dregg subject
below its real authority+recovery floor. -/
theorem dreggReal_amendment_nonregression (B : Nat)
    (ams : Nat → Amendment Bool RState) {C : Constitution Bool RState}
    (hwf : WellFormed (rFloors B) C) :
    ∀ n, WellFormed (rFloors B) (amendStream (rFloors B) ams C n) :=
  amendment_stream_nonregression (rFloors B) ams hwf

/-- TOOTH (real authority): grabbing `control` — an l4v authority the reader's bound `[read]`
lacks — is OUTSIDE the shared floor; the envelope refuses it. -/
example (B : Nat) : ¬ rShared B ⟨[Dregg2.Authority.Auth.control], 0⟩ := by
  intro h
  have hm := (h false).1 Dregg2.Authority.Auth.control (by simp)
  simp [rBounds] at hm

/-! ## §2.5. The EXECUTOR-BOUND polis — the spine over the DEPLOYED `Dregg2.Exec.exec`.

This is the genuine re-bind codex's review asked for. The §2 spine steps by the IDENTITY over an
authority-list type; here the `Polis` `step` IS the deployed kernel transition (`Dregg2.Exec.exec`),
following `PolisViabilityKernel.kernelArena`'s pattern that the arena's advance is the real `exec`
outcome.

* **State** = the deployed `Dregg2.Exec.KernelState` (the live ledger: accounts, balances, cap
  table) — the SAME object `exec` and `exec_conserves` reason about.
* **Action** = the deployed `Dregg2.Exec.Turn`.
* **`execStep`** = `(exec k t).getD k` — the deployed transition, **fail-closed**: an `exec`-admitted
  turn advances to the one real post-state; a rejected turn (unauthorized, insolvent, malformed)
  is a NO-OP (no state change — which is exactly what the kernel does on a rejected turn). The step
  RANGE is therefore exactly the deployed `exec`'s reachable states ∪ {stay-put}. A controller can no
  longer hand the system an arbitrary next state — only the kernel's own admitted outcome or the
  no-op.
* **Floor** = `execSafe T₀` := total supply pinned at the genesis supply `T₀` (conservation health,
  decidable, public — reads only `total`). `exec_conserves` PROVES every admitted `exec` step
  preserves it, so the policy is sound *because the executor conserves*, not by fiat.
* **`execPol`** = admit a turn iff `exec` actually commits it (`(exec k t).isSome`). The envelope's
  permission is the deployed admissibility check itself.

The payoff is `polis_safety` over the REAL executor: for EVERY opaque controller and every step, the
enveloped deployed kernel keeps its conservation floor — and the proof FACTORS THROUGH
`exec_conserves`, so it is a statement about the genuine `exec` evolution. -/

open Dregg2.Exec

/-- **`execStep` — the deployed kernel transition as a total `Polis` step (fail-closed).** Apply the
deployed `exec`; on rejection, stay put. The step's image is exactly the kernel's admitted outcomes
(plus the no-op) — NOT an arbitrary controller-chosen state. -/
def execStep (k : KernelState) (t : Turn) : KernelState := (exec k t).getD k

/-- **`execSafe T₀` — the public conservation floor:** total supply equals the genesis supply.
Decidable, interior-free (reads only `total`); `exec_conserves` keeps it across every admitted step. -/
def execSafe (T₀ : ℤ) : Floor KernelState := fun k => total k = T₀

/-- **`execPol` — the envelope admits exactly the deployed-`exec`-committed turns.** Permission IS the
kernel's own admissibility check (`(exec k t).isSome`) — a turn `exec` would reject is NOT permitted. -/
def execPol : Policy KernelState Turn := fun k t => (exec k t).isSome = true

/-- The shield: a no-op turn (`exec` rejects `src = dst`), so the shield always stays put — safe. -/
def execShield (_ : KernelState) : Turn := { actor := 0, src := 0, dst := 0, amt := 0 }

/-- An `exec`-rejected turn is a no-op under `execStep` (the fail-closed branch). -/
theorem execStep_reject {k : KernelState} {t : Turn} (h : exec k t = none) :
    execStep k t = k := by simp [execStep, h]

/-- The shield turn (`src = dst`) is always rejected by `exec`, hence always a no-op. -/
theorem execShield_noop (k : KernelState) : execStep k (execShield k) = k := by
  apply execStep_reject
  unfold exec execShield
  rw [if_neg]
  rintro ⟨_, _, _, hne, _⟩
  exact hne rfl

/-- **`execPol_sound` — the policy is sound BECAUSE the executor conserves.** From a state at the
genesis supply, every `exec`-admitted turn lands at a state STILL at the genesis supply — the proof
factors through the deployed `exec_conserves`. (The identity-step shadow's soundness was vacuous
`fun _ _ _ ha => ha`; this one DISCHARGES conservation of the real transition.) -/
theorem execPol_sound (T₀ : ℤ) : SoundPolicy execStep (execSafe T₀) execPol := by
  intro k t hk hp
  -- `execPol k t` says `exec k t` commits; name the post-state.
  unfold execPol at hp
  cases hx : exec k t with
  | none => rw [hx] at hp; simp at hp
  | some k' =>
      have hstep : execStep k t = k' := by simp [execStep, hx]
      rw [hstep]
      show total k' = T₀
      rw [exec_conserves k k' t hx]; exact hk

/-- **`execShieldSafe`** — the shield (a no-op) trivially preserves the conservation floor. -/
theorem execShieldSafe (T₀ : ℤ) :
    ∀ k, execSafe T₀ k → execSafe T₀ (execStep k (execShield k)) := by
  intro k hk; rw [execShield_noop]; exact hk

/-- **`execPolis_safety` — THE EXECUTOR-BOUND POLIS SPINE.** For EVERY opaque controller and every
step, the enveloped DEPLOYED kernel (`step = exec`, fail-closed) keeps its conservation floor: no
adversary — proposing turns, scheduling, jailbroken — drives the live ledger off its genesis supply.
Unlike `dreggReal_polis_safety`, the `step` here IS `Dregg2.Exec.exec`, so this is a theorem about
the genuine executor's evolution, proven through `exec_conserves`. -/
theorem execPolis_safety (k₀ : KernelState) :
    ∀ (ctrl : KernelState → Turn) (n : Nat),
      execSafe (total k₀) (traj execStep (envAct execPol execShield ctrl) k₀ n) :=
  polis_safety (execPol_sound (total k₀)) (execShieldSafe (total k₀)) rfl

/-! ### MUTATION-CONFIRM: a non-`exec` transition is rejected by the executor-bound envelope.

The identity-step shadow (§2) admitted ANY floor-passing proposed state. The exec-bound envelope does
NOT: a turn `exec` rejects produces NO state change (`execStep_reject`), and the policy `execPol`
does NOT permit it (`execPol` = `(exec k t).isSome`). So an unauthorized / insolvent / malformed turn
cannot move the ledger — the envelope is bound to the deployed admissibility, not to a free floor. -/

/-- A genesis ledger for the witnesses: cell 0 holds 100, cell 1 holds 5; empty cap table. -/
def execGenesis : KernelState :=
  { accounts := {0, 1}, bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0,
    caps := fun _ => [] }

/-- An UNAUTHORIZED turn (actor 2 has no cap on src 0): `exec` rejects it. -/
def execBadTurn : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }
/-- An AUTHORIZED turn (actor 0 owns src 0). -/
def execGoodTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

-- The policy (= the deployed admissibility check) DOES NOT admit the rejected turn — executor-bound,
-- not free-floor; and DOES admit the genuine `exec` turn:
#guard (exec execGenesis execBadTurn).isSome == false
#guard (exec execGenesis execGoodTurn).isSome == true
example : ¬ execPol execGenesis execBadTurn := by unfold execPol; decide
example : execPol execGenesis execGoodTurn := by unfold execPol; decide
-- The rejected turn is a NO-OP under the deployed step (no arbitrary state injected):
example : execStep execGenesis execBadTurn = execGenesis := execStep_reject (by decide)
-- The genuine turn actually MOVES the ledger (the step IS `exec`, not the identity):
#guard (execStep execGenesis execGoodTurn).bal 1 == 35
#guard (execStep execGenesis execGoodTurn).bal 0 == 70
-- … conserving total (the floor) exactly as `exec_conserves` guarantees:
#guard total (execStep execGenesis execGoodTurn) == total execGenesis

/-! ## §4. The politician at trace level — a CONCRETE CaptureBar over REAL dregg states.

Concrete trace semantics now exist (`List RState` over the deployed `Auth`), so per gpt5.5's
precondition the first real anti-capture bar can land: exit-foreclosure (the politician's
signature lawful move — driving another subject below its bounded recovery), decidable from
the public trace with NO interior inspection. The DEEP frontier (multi-trace hyperproperties:
clerk-monopoly, hole-rent, grade-laundering; the Büchi/flow connection) stays named. -/

/-- The trace forecloses a subject's bounded exit (Bool, publicly checkable) iff some state on
it lost recovery within `B` (`dist > B`). -/
def rForeclosesB (B : Nat) (τ : List RState) : Bool := τ.any (fun s => decide (B < s.dist))

/-- The floor a trace violates: it foreclosed a subject's bounded exit. -/
abbrev RForecloses (B : Nat) (τ : List RState) : Prop := rForeclosesB B τ = true

/-- **`rExitForeclosureBar` — a CONCRETE CaptureBar on real dregg-state traces.** Bars exactly
the foreclosing traces (zero false positives), decidable from the public trace alone (no
motive), least-restrictive. Refutes "CaptureBar is a vacuous interface" — here is one real
anti-domination bar over the deployed substrate. -/
def rExitForeclosureBar (B : Nat) : CaptureBar (List RState) (RForecloses B) where
  badShape := RForecloses B
  publicDecidable := fun τ => inferInstanceAs (Decidable (rForeclosesB B τ = true))
  loadBearing := fun _ h => h
  leastRestrictive := fun _ h => h

/-- **`dreggReal_envelope_no_foreclosure`** — the politician defeated by construction: the
envelope pins `dist ≤ B`, so for EVERY opaque adversary and every step, no dregg subject's
bounded exit is ever foreclosed. (The single-trajectory case; the multi-agent interleaved
hyperproperty is the frontier.) -/
theorem dreggReal_envelope_no_foreclosure (B : Nat) (ctrl : RState → RState) (n : Nat) :
    (traj rStep (envAct (rPol B) rShield ctrl) ⟨[], 0⟩ n).dist ≤ B :=
  (dreggReal_polis_safety B ctrl n true).2

/-- TEETH: a clean trace clears the bar; a trace driven to `dist 9 > budget 5` trips it. -/
example : ¬ RForecloses 5 [⟨[], 0⟩, ⟨[], 3⟩, ⟨[], 5⟩] := by decide
example : RForecloses 5 [⟨[], 0⟩, ⟨[], 9⟩] := by decide

/-! ## §3. The CI hard-gate — `#assert_axioms` fails the build on any axiom regression. -/

#assert_axioms minimalBoundary_carries_real_theorem
#assert_axioms minimalBoundary_is_structural
#assert_axioms privateInference_out_of_jurisdiction
#assert_axioms refusal_not_structural
#assert_axioms r_genesis_safe
#assert_axioms dreggReal_shared_floor_inhabited
#assert_axioms dreggReal_polis_safety
#assert_axioms dreggReal_amendment_nonregression
#assert_axioms dreggReal_envelope_no_foreclosure
#assert_axioms execPol_sound
#assert_axioms execShield_noop
#assert_axioms execPolis_safety

end Metatheory.DreggPolis
