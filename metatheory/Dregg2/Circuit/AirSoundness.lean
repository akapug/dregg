/-
# `Dregg2.Circuit.AirSoundness` — AIR SOUNDNESS: a trace satisfying the constraint system IS the
effect-VM execution. This is UNIT 2a, the first half of discharging `CircuitSound`.

`Circuit.lean` proves the SINGLE-step bridge `satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'`
(the four conjuncts as arithmetic gates) and, in `section DigestBinding`, that the Rust prover's CR-hash
digest BINDS the chain trace (`chain_digest_binds` / `chain_digest_binds_chainOk`, reduced to `HashCR`).
`Crypto/TurnSoundness.lean` carries the honest boundary hypothesis `CircuitSound applyEff checks`:
`∀ π old eff new, checks π old eff new → new = applyEff eff old`.

This file discharges the *execution* content of that hypothesis at the AIR level. The deployed AIR
(`circuit/src/descriptor_ir2.rs`, `EffectVmDescriptor2`) is a set of ALGEBRAIC constraints over an
execution TRACE:

  * **row-local step gate** — each row's `post` is the effect-VM's application to its `pre`
    (`local.post = applyEff local.eff local.pre`); this is the per-row polynomial gate;
  * **two-row window / carry (copy) constraint** — the state column carries between rows
    (`next.pre = local.post`), the Rust `when_transition()` arm of a `WindowGateSpec`;
  * **boundary constraints** — the first row's `pre` is the claimed `old` and the last row's `post` is
    the claimed `new` (the `boundary` / `pi_binding` forms of the v1 grammar embedded in v2).

`air_sound` proves: a trace satisfying ALL of these IS a valid VM execution — the claimed `new` is exactly
the VM run `old ↦ applyEff …` threaded through every effect (`vmResult`). Its corollary on a single-effect
turn, `air_sound_correct_transition`, gives precisely `new = applyEff eff old` — the `CircuitSound`
conclusion — and `circuit_sound_via_fri` assembles the full `CircuitSound applyEff checks` for the
AIR-realized checker, MODULO the one interface unit 2b must supply.

## The 2b seam, stated precisely (NOT assumed silently)

`air_sound` reasons about the trace the constraints were *checked on*. A STARK verifier never sees that
trace: it sees a Merkle commitment `com` and FRI/DEEP query answers. The guarantee that the committed
polynomial IS a low-degree codeword — hence corresponds to a genuine trace on the evaluation domain, on
which the spot-checked algebraic constraints actually hold — is FRI / low-degree proximity. That is unit
2b. Here it is the NAMED hypothesis

    FriProximity applyEff verifyLD openTr :
      ∀ π com, verifyLD π com → satisfiesTransition applyEff (openTr com).1 (openTr com).2

i.e. *acceptance of the low-degree/query verifier `verifyLD` on `(π, com)` implies the trace `openTr com`
that the commitment opens to satisfies the transition constraints.* Unit 2b PROVES this from the FRI
soundness bound; this file never assumes it as closed — it is carried as an explicit hypothesis exactly
like `CircuitSound` is in `TurnSoundness`, and named so 2b has a precise target. The Merkle *binding* leg
(the opened trace is UNIQUE for a commitment/digest) is already `Circuit.chain_digest_binds` (→ `HashCR`),
re-exposed here as `committed_trace_pinned`.

## Residual

`HashCR` (Merkle/digest binding — the hash floor, via `Circuit.chain_digest_binds`) + the named
`FriProximity` interface (low-degree proximity — to be PROVED by unit 2b, never assumed forever). No
`…Hard` carrier, no `:= True`, no laundered assumption.

## Teeth (all load-bearing, both instances exhibited)

* an HONEST trace satisfies the constraints AND is a VM execution (`honest_satisfies`, `honest_isVm`);
* a trace with a WRONG step VIOLATES the step gate — exhibited (`wrong_step_violates`);
* the BOUNDARY constraint is load-bearing: drop `last.post = new` and a wrong `old/new` pair satisfies
  every remaining constraint (`boundary_load_bearing`).
-/
import Dregg2.Circuit
import Dregg2.Crypto.TurnSoundness

namespace Dregg2.Circuit.AirSoundness

open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.TurnSoundness (CircuitSound)

variable {State Effect Proof Commitment : Type*}

/-! ## §1 — The execution trace as AIR rows. -/

/-- **`Step State Effect`** — one AIR trace row: the state the row acts on (`pre`), the effect the row
applies (`eff`), and the state the row claims to produce (`post`). A trace is a nonempty run `s :: rest`
of these rows. This mirrors the deployed `EffectVmDescriptor2` main trace: one row per effect, the state
threaded down the state columns. -/
structure Step (State Effect : Type*) where
  /-- The pre-state this row acts on (the state columns of the current row). -/
  pre : State
  /-- The effect this row applies. -/
  eff : Effect
  /-- The post-state this row claims (the state columns fed to the next row). -/
  post : State

/-! ## §2 — The three algebraic constraint families (row-local, two-row window, boundary). -/

/-- **Row-local step gate** — `post = applyEff eff pre`: the per-row polynomial gate that IS the
effect-VM's transition relation on this row. -/
def stepGate (applyEff : Effect → State → State) (s : Step State Effect) : Prop :=
  s.post = applyEff s.eff s.pre

/-- **The step gate on every row** — the row-local gate holds at each row of the nonempty trace
`s :: rest`. -/
def allStep (applyEff : Effect → State → State) :
    Step State Effect → List (Step State Effect) → Prop
  | s, []            => stepGate applyEff s
  | s, s' :: rest    => stepGate applyEff s ∧ allStep applyEff s' rest

/-- **The two-row window / carry (copy) constraint** — the state column carries from a row's `post` into
the next row's `pre` (`next.pre = local.post`). This is the Rust `WindowGateSpec` with `on_transition`,
the `builder.when_transition()` arm. -/
def carryChain : Step State Effect → List (Step State Effect) → Prop
  | _, []            => True
  | s, s' :: rest    => s'.pre = s.post ∧ carryChain s' rest

/-- The `post` of the LAST row of the nonempty trace `s :: rest` (the wire the final boundary constraint
pins to the claimed `new`). -/
def lastPost : Step State Effect → List (Step State Effect) → State
  | s, []            => s.post
  | _, s' :: rest    => lastPost s' rest

/-- The effect sequence a trace `s :: rest` applies, in order. -/
def effsOf : Step State Effect → List (Step State Effect) → List Effect
  | s, []            => [s.eff]
  | s, s' :: rest    => s.eff :: effsOf s' rest

/-- **The effect-VM run** — fold the effect sequence through `applyEff`, threading state from `old`.
`vmResult applyEff old s rest` is the state the VM genuinely reaches; the boundary constraint claims it
equals `new`, and `air_sound` proves the constraints FORCE that. -/
def vmResult (applyEff : Effect → State → State) (old : State)
    (s : Step State Effect) (rest : List (Step State Effect)) : State :=
  (effsOf s rest).foldl (fun st e => applyEff e st) old

/-- **The transition constraints** — the step gate on every row AND the carry constraint between rows.
These are the constraints unit 2b's `FriProximity` delivers from a committed trace (the algebraic
part FRI spot-checks); the boundary is checked publicly against the public inputs. -/
def satisfiesTransition (applyEff : Effect → State → State)
    (s : Step State Effect) (rest : List (Step State Effect)) : Prop :=
  allStep applyEff s rest ∧ carryChain s rest

/-- **The full AIR constraint system on a trace** — transition constraints AND both boundary constraints
(`first.pre = old`, `last.post = new`). Satisfying this is the prover's claim. -/
def satisfiesConstraints (applyEff : Effect → State → State) (old new : State)
    (s : Step State Effect) (rest : List (Step State Effect)) : Prop :=
  satisfiesTransition applyEff s rest ∧ s.pre = old ∧ lastPost s rest = new

/-- **`isVmExecution`** — the trace IS a genuine effect-VM execution: it chains, each row is a real VM
step, it starts at `old`, and the claimed `new` is EXACTLY the VM run result `vmResult`. This is the
semantic target `air_sound` lands on. -/
def isVmExecution (applyEff : Effect → State → State) (old new : State)
    (s : Step State Effect) (rest : List (Step State Effect)) : Prop :=
  satisfiesTransition applyEff s rest ∧ s.pre = old ∧ new = vmResult applyEff old s rest

/-! ## §3 — THE CORE LEMMA: the transition + start constraints FORCE the last state to be the VM run. -/

/-- **The trace runs to the VM result.** Under the step gate on every row, the carry constraint, and the
start boundary `s.pre = old`, the last row's `post` is EXACTLY the effect-VM run `vmResult applyEff old`.
Proved by induction threading the carry: `s.post = applyEff s.eff old` (step gate + start) becomes the
next row's `pre`, so the tail runs from `applyEff s.eff old`. -/
theorem lastPost_eq_vmResult (applyEff : Effect → State → State) :
    ∀ (s : Step State Effect) (rest : List (Step State Effect)) (old : State),
      allStep applyEff s rest → carryChain s rest → s.pre = old →
      lastPost s rest = vmResult applyEff old s rest := by
  intro s rest
  induction rest generalizing s with
  | nil =>
      intro old hstep _ hpre
      -- lastPost s [] = s.post ; vmResult old s [] = applyEff s.eff old
      have hg : s.post = applyEff s.eff s.pre := hstep
      subst hpre
      simp only [lastPost, vmResult, effsOf, List.foldl_cons, List.foldl_nil]
      exact hg
  | cons s' rest ih =>
      intro old hstep hcarry hpre
      obtain ⟨hg, hrest⟩ := hstep
      obtain ⟨hc, hcrest⟩ := hcarry
      -- carry threads: next.pre = s.post = applyEff s.eff old
      have hpre' : s'.pre = applyEff s.eff old := by
        rw [hc, hg, hpre]
      have htail := ih s' (applyEff s.eff old) hrest hcrest hpre'
      -- lastPost s (s'::rest) = lastPost s' rest = vmResult (applyEff s.eff old) s' rest
      -- and vmResult old s (s'::rest) = vmResult (applyEff s.eff old) s' rest
      calc lastPost s (s' :: rest)
          = lastPost s' rest := rfl
        _ = vmResult applyEff (applyEff s.eff old) s' rest := htail
        _ = vmResult applyEff old s (s' :: rest) := by
              simp only [vmResult, effsOf, List.foldl_cons]

/-! ## §4 — AIR SOUNDNESS (the deliverable). -/

/-- **THEOREM `air_sound` — a trace satisfying ALL the AIR constraints IS the effect-VM execution.**
Given the transition constraints (step gate on every row + carry) and BOTH boundary constraints
(`first.pre = old`, `last.post = new`), the trace is a genuine VM execution: it chains, each row is a real
VM step, it starts at `old`, and `new` is EXACTLY the VM run `vmResult`. The boundary `last.post = new`
combines with `lastPost_eq_vmResult` (which forces `last.post = vmResult`) to pin `new = vmResult`. -/
theorem air_sound (applyEff : Effect → State → State) (old new : State)
    (s : Step State Effect) (rest : List (Step State Effect))
    (h : satisfiesConstraints applyEff old new s rest) :
    isVmExecution applyEff old new s rest := by
  obtain ⟨⟨hstep, hcarry⟩, hstart, hend⟩ := h
  refine ⟨⟨hstep, hcarry⟩, hstart, ?_⟩
  -- new = last.post = vmResult
  rw [← hend]
  exact lastPost_eq_vmResult applyEff s rest old hstep hcarry hstart

/-- **Corollary — the claimed new state equals the VM run.** The direct denotational conclusion:
constraint-satisfaction forces `new = vmResult applyEff old …`. -/
theorem air_sound_new_eq_run (applyEff : Effect → State → State) (old new : State)
    (s : Step State Effect) (rest : List (Step State Effect))
    (h : satisfiesConstraints applyEff old new s rest) :
    new = vmResult applyEff old s rest :=
  (air_sound applyEff old new s rest h).2.2

/-- **`air_sound_single` — the single-effect turn discharge of `CircuitSound`'s conclusion.** A one-row
trace `⟨old, eff, new⟩` satisfying the AIR constraints has `new = applyEff eff old`. -/
theorem air_sound_single (applyEff : Effect → State → State) (old : State) (eff : Effect) (new : State)
    (h : satisfiesConstraints applyEff old new ⟨old, eff, new⟩ []) :
    new = applyEff eff old := by
  have := air_sound_new_eq_run applyEff old new ⟨old, eff, new⟩ [] h
  simpa [vmResult, effsOf] using this

/-! ## §5 — THE 2b SEAM: FRI / low-degree proximity, stated as a named interface. -/

/-- **`FriProximity` — the interface unit 2b must PROVE (never assumed closed here).** A STARK verifier
sees a Merkle commitment `com` and FRI/DEEP query answers, not the trace. `verifyLD π com` is the
low-degree / query verifier accepting; `openTr com` is the trace the commitment opens to. This Prop says:
*acceptance of `verifyLD` implies the committed trace satisfies the TRANSITION constraints* — i.e. the
constraints the verifier spot-checks really do hold on the committed low-degree codeword. Unit 2b
discharges this from the FRI soundness bound (proximity gap ⇒ a passing prover is δ-close to a genuine
codeword). It is carried as an explicit hypothesis, exactly like `CircuitSound` in `TurnSoundness`. -/
def FriProximity (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect)) : Prop :=
  ∀ (π : Proof) (com : Commitment),
    verifyLD π com → satisfiesTransition applyEff (openTr com).1 (openTr com).2

/-- **The AIR-realized checker.** `airChecks` accepts a proof `π` for a claimed turn `(old, eff, new)`
iff there is a commitment `com` the low-degree verifier accepts, whose opened trace is the single row
`⟨old, eff, new⟩` (the public-input boundary binding the verifier checks in the clear). This is the
`checks : Proof → State → Effect → State → Prop` the deployed AIR realizes. -/
def airChecks (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (π : Proof) (old : State) (eff : Effect) (new : State) : Prop :=
  ∃ com : Commitment, verifyLD π com ∧ openTr com = (⟨old, eff, new⟩, [])

/-- **THEOREM `circuit_sound_via_fri` — the full `CircuitSound`, MODULO `FriProximity`.** Under the 2b
interface `FriProximity`, the AIR-realized checker `airChecks` satisfies `CircuitSound applyEff` — every
accepted proof forces `new = applyEff eff old`. Chain: `airChecks` acceptance ⇒ (FriProximity) the opened
single-row trace satisfies the transition constraints ⇒ (its boundary is the public `old`/`new`) it
satisfies ALL constraints ⇒ (`air_sound_single`) `new = applyEff eff old`. This is unit 2a's contribution
to discharging the `CircuitSound` hypothesis of `Crypto.TurnSoundness.turn_sound`; the only residual is
the named `FriProximity` (unit 2b) and, for Merkle binding, `HashCR` (`committed_trace_pinned`). -/
theorem circuit_sound_via_fri (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (hfri : FriProximity applyEff verifyLD openTr) :
    CircuitSound applyEff (airChecks verifyLD openTr) := by
  intro π old eff new h
  obtain ⟨com, hv, hopen⟩ := h
  have htrans : satisfiesTransition applyEff (openTr com).1 (openTr com).2 := hfri π com hv
  rw [hopen] at htrans
  -- htrans : satisfiesTransition applyEff ⟨old,eff,new⟩ []
  -- assemble full constraints: boundary is (⟨old,eff,new⟩).pre = old and lastPost = new — both rfl
  have hfull : satisfiesConstraints applyEff old new ⟨old, eff, new⟩ [] :=
    ⟨htrans, rfl, rfl⟩
  exact air_sound_single applyEff old eff new hfull

/-! ## §6 — Merkle binding leg: the digest pins the committed trace (reuse `Circuit.chain_digest_binds`).

`FriProximity` gives "the committed trace satisfies the constraints". The companion guarantee — the
committed trace is UNIQUE for its digest (the prover can't open one commitment to two traces) — is exactly
`Circuit.chain_digest_binds`, already reduced to `HashCR` in `Circuit.lean`'s `section DigestBinding`. We
re-expose it here on the AIR trace type so the two legs sit together: FRI proximity (2b) + Merkle binding
(`HashCR`) ⇒ the digest the verifier checks pins the exact trace `air_sound` reasons about. -/

/-- **`committed_trace_pinned` — the digest binds the AIR trace UNIQUELY (→ `HashCR`).** Instantiates
`Circuit.chain_digest_binds` at the AIR trace type: under `HashCR` and an injective framing, two traces
that both recompute the claimed digest are equal. So a prover cannot serve one digest for two different
committed traces — the trace `air_sound` consumes is the one the verifier's digest check pins. -/
theorem committed_trace_pinned {Pre Dig : Type*}
    (cr : CommitReveal Unit Pre Dig)
    (frame : (Step State Effect × List (Step State Effect)) → Pre)
    (hinj : Function.Injective frame) (hcr : HashCR cr) (dig : Dig)
    (tr tr' : Step State Effect × List (Step State Effect))
    (h : Dregg2.Circuit.verifyDigest cr frame dig tr)
    (h' : Dregg2.Circuit.verifyDigest cr frame dig tr') : tr = tr' :=
  Dregg2.Circuit.chain_digest_binds cr frame hinj hcr dig tr tr' h h'

#assert_axioms lastPost_eq_vmResult
#assert_axioms air_sound
#assert_axioms air_sound_new_eq_run
#assert_axioms air_sound_single
#assert_axioms circuit_sound_via_fri
#assert_axioms committed_trace_pinned

/-! ## §7 — TEETH (all load-bearing, both instances exhibited).

The toy VM: `State = Effect = ℕ`, `applyEff e s = s + e` (an additive counter). -/

section Teeth

/-- The toy effect-VM: an additive counter. -/
def toyApply : ℕ → ℕ → ℕ := fun e s => s + e

/-- An HONEST two-row trace: `0 --(+1)--> 1 --(+2)--> 3`. Rows chain, each is a real step, boundary
`old = 0`, `new = 3`. -/
def honestHead : Step ℕ ℕ := ⟨0, 1, 1⟩
def honestRest : List (Step ℕ ℕ) := [⟨1, 2, 3⟩]

/-- **RESPECTING INSTANCE (a).** The honest trace satisfies ALL the AIR constraints. -/
theorem honest_satisfies : satisfiesConstraints toyApply 0 3 honestHead honestRest := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- step gate on every row: 1 = 0 + 1, 3 = 1 + 2
    exact ⟨rfl, rfl⟩
  · -- carry: next.pre (=1) = head.post (=1)
    exact ⟨rfl, trivial⟩
  · rfl
  · rfl

/-- **RESPECTING INSTANCE (b).** …and `air_sound` certifies it IS a VM execution: `new = vmResult`. -/
theorem honest_isVm : isVmExecution toyApply 0 3 honestHead honestRest :=
  air_sound toyApply 0 3 honestHead honestRest honest_satisfies

-- The honest trace's VM run really lands on 3 (foldl [1,2] 0 = 3).
example : vmResult toyApply 0 honestHead honestRest = 3 := rfl

/-- A trace with a WRONG step: `⟨0, 1, 5⟩` claims `0 --(+1)--> 5`, but `5 ≠ 0 + 1`. -/
def wrongStepHead : Step ℕ ℕ := ⟨0, 1, 5⟩

/-- **WRONG-STEP TOOTH (load-bearing).** The wrong-step trace VIOLATES the step gate — `allStep` fails, so
it does NOT satisfy the transition constraints (hence not the full system). A prover cannot commit a trace
whose row lies about the transition and still pass the AIR. -/
theorem wrong_step_violates : ¬ satisfiesTransition toyApply wrongStepHead [] := by
  rintro ⟨hstep, _⟩
  -- allStep toyApply ⟨0,1,5⟩ [] = stepGate = (5 = 0 + 1) = (5 = 1)
  have : (5 : ℕ) = toyApply 1 0 := hstep
  simp [toyApply] at this

/-- …and consequently no boundary can rescue it: it fails the full constraint system too. -/
theorem wrong_step_no_constraints (new : ℕ) :
    ¬ satisfiesConstraints toyApply 0 new wrongStepHead [] := by
  rintro ⟨htrans, _, _⟩
  exact wrong_step_violates htrans

/-- **BOUNDARY-LOAD-BEARING TOOTH.** Drop the `last.post = new` boundary constraint and a WRONG `old/new`
pair sails through everything else. The one-row trace `⟨0, 1, 1⟩` satisfies the transition constraints AND
the START boundary `pre = 0`, yet the claimed `new = 999` is FALSE (`999 ≠ vmResult = 1`). So the final
boundary constraint is exactly what rejects a lying `new`: without it `air_sound`'s conclusion fails. -/
theorem boundary_load_bearing :
    satisfiesTransition toyApply (⟨0, 1, 1⟩ : Step ℕ ℕ) []
      ∧ (⟨0, 1, 1⟩ : Step ℕ ℕ).pre = 0
      ∧ (999 : ℕ) ≠ vmResult toyApply 0 (⟨0, 1, 1⟩ : Step ℕ ℕ) [] := by
  refine ⟨⟨?_, trivial⟩, rfl, ?_⟩
  · -- step gate: 1 = 0 + 1
    exact rfl
  · -- 999 ≠ foldl [1] 0 = 1
    decide

-- The wrong step really is wrong under the VM; the honest one really lands on the boundary.
example : ¬ stepGate toyApply wrongStepHead := by simp [stepGate, toyApply, wrongStepHead]
example : stepGate toyApply honestHead := rfl
#guard decide (vmResult toyApply 0 honestHead honestRest = 3)
#guard decide (lastPost honestHead honestRest = 3)

end Teeth

#assert_axioms honest_satisfies
#assert_axioms honest_isVm
#assert_axioms wrong_step_violates
#assert_axioms wrong_step_no_constraints
#assert_axioms boundary_load_bearing

end Dregg2.Circuit.AirSoundness
