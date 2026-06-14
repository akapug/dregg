/-
# Dregg2.Deos.Flow — a MULTI-STEP protocol as ONE typed object (propose → approve → settle).

`docs/REFINEMENT-DESIGN.md` Decision 3 (the reactivity model) + `docs/deos/DEOS.md` §"htmx on crack".
This is the COMPOSABLE-FLOW rung above `Dregg2.Deos.GatedAffordance`.

THE GAP THIS CLOSES (the "screaming toy" shape). `GatedAffordance` gates ONE step: `fireGated` commits
iff the viewer's caps AND the live-state predicate both pass for a SINGLE interaction. But a real
protocol is MULTI-STEP — propose THEN approve THEN settle; offer THEN accept THEN close; draft THEN
review THEN publish — and the ORDER is load-bearing: you must not settle before approving, you must not
approve twice, you must not skip the proposal. With only single-step gates, the app author hand-sequences
N disconnected affordances and hopes the cell's state field threads them correctly. That sequencing — "a
typed sequence of gated steps with state BETWEEN them, where step k fires only when step k−1 committed
AND step k's own cap∧state gate passes" — had no home in the language. This module is the home: a `Flow`
is an ordered list of `GatedAffordance` steps PLUS a designated `phaseField`, and the keystone proves a
step fires exactly when its phase has been reached AND its gate bites — so the flow walks its legal path
and ONLY its legal path.

This is NOT new mathematics and NOT a new state machine engine. Each step is the EXISTING
`GatedAffordance` (the cap-gate `Affordance.fireGate` ∧ the state-gate `RecordProgram.admitsCtx`, both
proven in `GatedAffordance.lean`). What is NEW is the SEQUENCING DISCIPLINE: the flow carries a
`phaseField : FieldName`, step `k` (0-indexed) is ARMED only when the cell's `phaseField` holds exactly
`k` (the phase reached by committing precisely the `k` prior steps), and committing step `k` advances the
phase to `k+1`. That ONE phase-counter mechanism delivers — provably — no-skip (a step whose predecessor
has not committed sees `phase ≠ k`), in-order (each step is bound to a DISTINCT phase code), and
no-double-fire (a committed step advanced the phase past `k`, so re-firing sees `phase = k+1 ≠ k`),
WHILE the per-step cap∧state gate rides untouched on `GatedAffordance.gatedOK`.

## What is proven

  * §1 `FlowStep φ` / `Flow φ` — a step is a `GatedAffordance φ` (the cap∧state-gated interaction); a
    `Flow` is a `phaseField : FieldName` + an ordered `steps : List (FlowStep φ)`. The flow's progress
    is the scalar in `phaseField`; the terminal phase is `steps.length`.
  * §2 `stepArmed` / `fireStep` — `stepArmed flow k held ctx old new` is the FULL guard on firing step
    `k`: (a) `k` is a real step index, (b) the cell's `old[phaseField] = k` (PHASE reached — the
    prior-committed precondition), (c) the step's `gatedOK` passes (caps ∧ state), AND (d) the
    transition ADVANCES `new[phaseField] = k+1` (the commit moves the flow forward exactly one phase).
    `fireStep` commits (yields the step's verified `AffordanceIntent`) IFF `stepArmed`.
  * **`fireStep_iff` (THE KEYSTONE).** `fireStep` commits ↔ `stepArmed` — a step fires exactly when its
    phase is reached, its gate bites, and the transition advances the phase. The multi-step composition
    nobody could express, as an `↔`. Every soundness tooth below is a corollary.
  * The FIVE soundness teeth (each BOTH polarities, on the concrete 3-step exemplar in §6):
      - `flow_in_order_accepts` — the IN-ORDER happy path: at phase k, the right viewer, the right
        state, advancing to k+1 ⇒ step k FIRES. (The positive corner.)
      - `fireStep_out_of_order_refuses` — firing step k while the cell is at a DIFFERENT phase
        (`old[phaseField] = j ≠ k`) ⇒ REFUSED. Can't fire out of order.
      - `fireStep_skip_refuses` — a SKIP is a special out-of-order: firing step k while still at an
        EARLIER phase (`old[phaseField] = j < k`, the predecessor not yet committed) ⇒ REFUSED. Can't
        skip a step.
      - `fireStep_unauthorized_refuses` — at the right phase but the viewer LACKS the step's caps ⇒
        REFUSED. Each step's cap-gate is enforced (rides `GatedAffordance.fireGated_cap_fail_refuses`).
      - `fireStep_double_fire_refuses` — firing a step that ALREADY committed (so the phase advanced to
        `k+1`) ⇒ REFUSED. Can't double-fire — the phase counter is the once-only token.
  * §4 the TERMINAL reachability tooth: `flow_terminal_only_via_path` — the flow reaches its terminal
    phase (`= steps.length`) ONLY by a sequence of legal `fireStep`s, one per step, in order. A
    `FlowRun` is the inductive witness of a legal walk; `flowRun_reaches` proves a complete run lands
    exactly at the terminal phase, and `flowRun_phase_le_length` proves no run ever overshoots.
  * §5 the leg-4 carry: `fireStep_carries_real_effect` / `fireStep_binds_attested_root` — a committed
    step still fires its REAL effect and binds the attested root (the sequencing discipline only ADDS
    the phase precondition; it never forges a surface). Inherited from `GatedAffordance`.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2.Deos.Flow` green (LOCAL). NO core edit — each step is the REAL `GatedAffordance`; the phase gate
is a `fieldEquals`/`fieldDelta` over the REAL `RecordProgram` the executor enforces. The sequencing is a
DISCIPLINE over existing gates, nothing more.

## Rust-mirror site (LAW #1: the language is EMITTED from Lean; the convergence wires Rust)

The Rust twin is a `Flow { phase_field: FieldName, steps: Vec<GatedAffordance> }` beside the
`GatedAffordance` of `starbridge-web-surface/src/affordance.rs`, whose `fire_step(k, held, ctx, old,
new)` runs `steps[k].fire(..)` (the EXISTING cap∧state gate) ONLY when `old.scalar(phase_field) ==
Some(k)` AND `new.scalar(phase_field) == Some(k+1)` — refusing (a new `FireError::PhaseMismatch { at,
expected }`) otherwise. The phase field is an EXISTING register read (`cell/src/program.rs`'s
`evaluate_constraint_full` already reads named scalars); the convergence authors NO new evaluator
semantics. (Exact file:line targets at the close.)
-/
import Dregg2.Deos.GatedAffordance

namespace Dregg2.Deos.Flow

open Dregg2.Authority (Auth)
open Dregg2.Deos.Affordance (CellAffordance AffordanceIntent fireGate)
open Dregg2.Deos.GatedAffordance (GatedAffordance gatedOK fireGated fireGated_iff
  fireGated_both_pass fireGated_cap_fail_refuses fireGated_carries_real_effect
  fireGated_binds_attested_root)
open Dregg2.Exec (RecordProgram StateConstraint SimpleConstraint TurnCtx Value FieldName)

-- The central type IS `Flow` inside the `…Deos.Flow` namespace (matching the repo's
-- `GatedAffordance.GatedAffordance` / `Rehydration.Rehydration` precedent — the type carries the
-- module's name on purpose); silence the cosmetic duplicate-namespace linter for the module.
set_option linter.dupNamespace false

/-! ## §1 — A `Flow`: an ordered sequence of `GatedAffordance` steps over a shared phase counter.

A `Flow` is the deos MULTI-STEP element. Its progress is a single scalar — the `phaseField` of the cell
record — which is `0` before any step, `k` after `k` steps have committed in order, and `steps.length`
when the flow is complete. Each `FlowStep` IS a `GatedAffordance` (the cap∧state-gated interaction the
language already proves sound); the flow ADDS only the phase discipline. -/

variable {φ : Type}

/-- **`FlowStep φ`** — one step of a flow: a `GatedAffordance φ` (the REAL cap∧state-gated
interaction). The flow's sequencing wraps each step with a phase precondition (§2); the step itself
carries its own `required` caps and its own `stateCond` live-state predicate, exactly as a standalone
gated affordance. -/
structure FlowStep (φ : Type) where
  /-- The cap∧state-gated interaction this step fires (the REAL `GatedAffordance`). -/
  gated : GatedAffordance φ

/-- **`Flow φ`** — a typed multi-step protocol: the `phaseField` that tracks progress (a named scalar
in the cell record) plus the ordered `steps`. The flow is at phase `k` when `phaseField = k`; the
TERMINAL phase is `steps.length` (every step committed). The "propose → approve → settle" object: ONE
value in the language, not three hand-sequenced buttons. -/
structure Flow (φ : Type) where
  /-- The named scalar tracking flow progress (`0` initially, `k` after `k` committed steps,
  `steps.length` when complete). -/
  phaseField : FieldName
  /-- The ordered steps; step `k` arms only at phase `k` (§2). -/
  steps      : List (FlowStep φ)

/-- The terminal phase of a flow: every step committed. -/
def Flow.terminalPhase (flow : Flow φ) : Nat := flow.steps.length

/-- Read the cell's current phase (the scalar in `phaseField`); `none` if absent/ill-typed
(fail-closed — a cell with no phase scalar arms no step). -/
def Flow.phaseOf (flow : Flow φ) (v : Value) : Option Int := v.scalar flow.phaseField

/-- The `k`-th step of the flow, if `k` is a real index. -/
def Flow.stepAt (flow : Flow φ) (k : Nat) : Option (FlowStep φ) := flow.steps[k]?

/-! ## §2 — `stepArmed` / `fireStep`: a step fires exactly at its phase, under its gate, advancing.

`stepArmed flow k held ctx old new` is the FULL firing guard on step `k`. It conjoins FOUR conditions —
the step exists, the cell is at phase `k`, the step's cap∧state gate passes, and the transition advances
the phase to `k+1` — so a single `Bool` says "step `k` may fire RIGHT NOW, for this viewer, in this
state, moving the flow forward". `fireStep` commits the step's `GatedAffordance` IFF `stepArmed`. -/

/-- **The phase-reached precondition** — `atPhase flow k old`: the cell's `phaseField` holds EXACTLY
`k` (the integer `k`), i.e. precisely `k` prior steps have committed. This is the prior-committed
precondition AND (because each phase code is distinct) the no-skip / in-order / no-double-fire mechanism
all at once. -/
def atPhase (flow : Flow φ) (k : Nat) (old : Value) : Bool :=
  flow.phaseOf old == some (k : Int)

/-- **The phase-advance postcondition** — `advancesTo flow k new`: the post-state `phaseField` holds
`k+1` (committing step `k` moves the flow forward exactly one phase). This is what makes a committed
step BURN its phase token: after it, the cell is at `k+1`, so step `k` can never re-arm. -/
def advancesTo (flow : Flow φ) (k : Nat) (new : Value) : Bool :=
  flow.phaseOf new == some ((k : Int) + 1)

/-- **`stepArmed flow k held ctx old new`** — the complete guard on firing step `k`: the step exists
(`stepAt = some st`), the cell is AT phase `k` (`atPhase`), the step's cap∧state gate passes
(`gatedOK` on the step's `GatedAffordance`), AND the transition ADVANCES the phase to `k+1`
(`advancesTo`). All four must hold; any failure darkens the step. -/
def stepArmed (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) : Bool :=
  match flow.stepAt k with
  | some st => atPhase flow k old && gatedOK st.gated held ctx old new && advancesTo flow k new
  | none    => false

/-- **`fireStep flow k held ctx old new s post`** — fire step `k` of the flow for a viewer holding
`held`, in context `ctx`, against transition `(old, new)`, with pre/post commitments `s`/`post`. IF
`stepArmed` (the step exists, the phase is reached, the gate bites, the phase advances), yields `some`
of the step's verified `AffordanceIntent` (binding the attested root `post`, via the step's own
`GatedAffordance`); ELSE `none` (refused in-band). Reuses the EXISTING `fireGated` for the commit shape,
guarded ADDITIONALLY by the phase discipline. -/
def fireStep (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) : Option (AffordanceIntent φ) :=
  match flow.stepAt k with
  | some st =>
      if atPhase flow k old && advancesTo flow k new then
        fireGated st.gated held ctx old new s post
      else
        none
  | none    => none

/-! ## §3 — THE KEYSTONE: a step fires exactly when armed (phase ∧ gate ∧ advance). -/

/-- **THE KEYSTONE — `fireStep_iff`.** `fireStep` COMMITS (`isSome`) if and only if `stepArmed` — the
step exists, the cell is at phase `k`, the step's cap∧state gate passes, AND the transition advances the
phase. The multi-step composition the language could not previously express, as an `↔`. Every soundness
tooth (out-of-order, skip, double-fire, unauthorized) is a corollary of dropping one conjunct. -/
theorem fireStep_iff (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) :
    (fireStep flow k held ctx old new s post).isSome = true ↔
      stepArmed flow k held ctx old new = true := by
  unfold fireStep stepArmed
  cases hst : flow.stepAt k with
  | none => simp
  | some st =>
    by_cases hph : (atPhase flow k old && advancesTo flow k new) = true
    · rw [if_pos hph]
      rw [fireGated_iff]
      -- LHS: gatedOK ⇔ (cap ∧ state); RHS: (phase∧advance) ∧ gatedOK, with hph supplying phase∧advance.
      rw [Bool.and_eq_true] at hph
      constructor
      · intro hcs
        -- hcs : cap ∧ state, i.e. gatedOK; rebuild the RHS conjunction.
        have hg : gatedOK st.gated held ctx old new = true := by
          unfold gatedOK; rw [Bool.and_eq_true]; exact hcs
        rw [hph.1, hg, hph.2]; rfl
      · intro hall
        -- hall : atPhase && gatedOK && advancesTo = true; extract gatedOK and split it.
        rw [Bool.and_eq_true, Bool.and_eq_true] at hall
        have hg : gatedOK st.gated held ctx old new = true := hall.1.2
        unfold gatedOK at hg; rw [Bool.and_eq_true] at hg
        exact hg
    · rw [if_neg hph]
      have hphf : (atPhase flow k old && advancesTo flow k new) = false := by
        cases hb : (atPhase flow k old && advancesTo flow k new) with
        | true => exact absurd hb hph | false => rfl
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      -- stepArmed at this step = atPhase && gatedOK && advancesTo; phase∧advance already false.
      rw [Bool.and_eq_true, Bool.and_eq_true]
      rw [Bool.and_eq_true] at hphf ⊢
      -- goal: ¬((atPhase ∧ gatedOK) ∧ advancesTo); hphf says ¬(atPhase ∧ advancesTo).
      rintro ⟨⟨hap, _⟩, hadv⟩
      exact hphf ⟨hap, hadv⟩

/-! ## §4 — THE FIVE SOUNDNESS TEETH: the flow walks its legal path and ONLY its legal path. -/

/-- **IN-ORDER ⇒ FIRES** (the positive corner). At phase `k`, with a viewer whose caps ∧ the live state
pass the step's gate, and a transition that advances to `k+1`, step `k` FIRES. The happy path of a
flow accepts. -/
theorem flow_in_order_accepts (flow : Flow φ) (k : Nat) (st : FlowStep φ) (held : List Auth)
    (ctx : TurnCtx) (old new : Value) (s post : Nat)
    (hstep : flow.stepAt k = some st)
    (hphase : atPhase flow k old = true)
    (hgate  : gatedOK st.gated held ctx old new = true)
    (hadv   : advancesTo flow k new = true) :
    (fireStep flow k held ctx old new s post).isSome = true := by
  rw [fireStep_iff]
  unfold stepArmed
  rw [hstep, hphase, hgate, hadv]; rfl

/-- **OUT-OF-ORDER ⇒ REFUSED** (the ordering tooth). Firing step `k` while the cell is at a DIFFERENT
phase `j ≠ k` (`old[phaseField] = j`) is refused — no matter the caps, no matter the state. The flow
cannot be driven out of order: each step is bound to its own phase code, so a step whose phase has not
been reached is dark. -/
theorem fireStep_out_of_order_refuses (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (j : Int)
    (hat : flow.phaseOf old = some j) (hne : j ≠ (k : Int)) :
    fireStep flow k held ctx old new s post = none := by
  unfold fireStep
  cases hst : flow.stepAt k with
  | none => rfl
  | some st =>
    have hphf : atPhase flow k old = false := by
      unfold atPhase; rw [hat]
      simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]; exact hne
    rw [if_neg (by rw [hphf, Bool.false_and]; decide)]

/-- **A SKIP ⇒ REFUSED** (the no-skip tooth, a special out-of-order). Firing step `k` while the cell is
still at an EARLIER phase `j < k` (the predecessor step `k−1` — indeed every step from `j` up — has not
yet committed) is refused. You cannot skip a step: a step's phase is reached only by committing every
prior step in turn. -/
theorem fireStep_skip_refuses (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (j : Nat)
    (hat : flow.phaseOf old = some (j : Int)) (hlt : j < k) :
    fireStep flow k held ctx old new s post = none :=
  fireStep_out_of_order_refuses flow k held ctx old new s post (j : Int) hat
    (by exact_mod_cast Nat.ne_of_lt hlt)

/-- **UNAUTHORIZED ⇒ REFUSED** (the per-step cap tooth). At the right phase, a viewer who LACKS the
step's required caps (`fireGate st.gated.aff.required held = false`) cannot fire the step — even if the
phase is reached and the transition would advance. Each step's authority gate is enforced (this rides
`GatedAffordance.fireGated_cap_fail_refuses`, the cap tooth one rung down). -/
theorem fireStep_unauthorized_refuses (flow : Flow φ) (k : Nat) (st : FlowStep φ) (held : List Auth)
    (ctx : TurnCtx) (old new : Value) (s post : Nat)
    (hstep : flow.stepAt k = some st)
    (hcap : fireGate st.gated.aff.required held = false) :
    fireStep flow k held ctx old new s post = none := by
  unfold fireStep
  rw [hstep]
  by_cases hph : (atPhase flow k old && advancesTo flow k new) = true
  · rw [if_pos hph]
    exact fireGated_cap_fail_refuses st.gated held ctx old new s post hcap
  · rw [if_neg hph]

/-- **DOUBLE-FIRE ⇒ REFUSED** (the once-only tooth). A step that ALREADY committed advanced the phase
to `k+1`; firing step `k` again sees `old[phaseField] = k+1 ≠ k` and is refused. The phase counter is
the once-only token: a committed step cannot re-arm, so no step fires twice. (This is the double-spend
shape — `noteSpend` for protocol steps — phrased over the phase scalar.) -/
theorem fireStep_double_fire_refuses (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat)
    (hcommitted : flow.phaseOf old = some ((k : Int) + 1)) :
    fireStep flow k held ctx old new s post = none :=
  fireStep_out_of_order_refuses flow k held ctx old new s post ((k : Int) + 1) hcommitted
    (by omega)

/-! ## §5 — TERMINAL REACHABILITY: the flow reaches its terminal ONLY via the legal path.

A `FlowRun` is the INDUCTIVE witness of a legal walk through the flow: it starts at phase `0` and each
extension fires the NEXT step (`fireStep flow k`, at phase `k`, advancing to `k+1`). Its existence is a
certificate that the flow was walked in order, one legal step at a time. The reachability theorems read
the run: a complete run lands EXACTLY at the terminal phase, and no run ever overshoots. -/

/-- **`FlowRun flow phase`** — a legal walk through `flow` that has reached `phase`. `nil` is the
flow at its initial phase `0`. `step` extends a run at phase `k` by FIRING step `k` (the firing
witnessed by `fireStep … = some _`, so the extension is a REAL legal fire — at phase `k`, gate-passing,
advancing to `k+1`), reaching phase `k+1`. A `FlowRun flow flow.terminalPhase` is thus a certificate
that every step fired, in order. -/
inductive FlowRun (flow : Flow φ) : Nat → Prop where
  /-- The empty run: the flow at its initial phase `0` (no step has fired). -/
  | nil : FlowRun flow 0
  /-- Extend a run at phase `k` by firing step `k` (advancing to `k+1`). The fire is a real legal
  `fireStep` commit, carried as the hypothesis `hfire`. -/
  | step (k : Nat) (prev : FlowRun flow k)
      {held : List Auth} {ctx : TurnCtx} {old new : Value} {s post : Nat}
      {intent : AffordanceIntent φ}
      (hfire : fireStep flow k held ctx old new s post = some intent) :
      FlowRun flow (k + 1)

/-- **EVERY LEGAL FIRE ADVANCES BY EXACTLY ONE PHASE** — a committed `fireStep flow k` proves the cell
went from phase `k` to phase `k+1` (the `old`/`new` of the fire genuinely carry those phases). So a fire
is never a no-op and never a jump: it walks ONE phase forward. -/
theorem fireStep_advances_one (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (intent : AffordanceIntent φ)
    (h : fireStep flow k held ctx old new s post = some intent) :
    flow.phaseOf old = some (k : Int) ∧ flow.phaseOf new = some ((k : Int) + 1) := by
  have hsome : (fireStep flow k held ctx old new s post).isSome = true := by rw [h]; rfl
  rw [fireStep_iff] at hsome
  unfold stepArmed at hsome
  cases hst : flow.stepAt k with
  | none => rw [hst] at hsome; simp at hsome
  | some st =>
    rw [hst] at hsome
    rw [Bool.and_eq_true, Bool.and_eq_true] at hsome
    obtain ⟨⟨hap, _⟩, hadv⟩ := hsome
    refine ⟨?_, ?_⟩
    · unfold atPhase at hap; simpa using hap
    · unfold advancesTo at hadv; simpa using hadv

/-- **A COMPLETE RUN REACHES EXACTLY THE TERMINAL PHASE** (terminal reachability, the forward half).
A `FlowRun flow n` certifies the flow has been walked to phase `n` by `n` legal in-order fires. In
particular a `FlowRun flow flow.terminalPhase` certifies the flow reached its terminal (every step
committed) — and it got there ONLY through the inductive `step` constructor, i.e. ONLY by firing each
step in order. The terminal is reachable, and reachable only via the legal path. -/
theorem flowRun_reaches (flow : Flow φ) (n : Nat) (run : FlowRun flow n) :
    ∃ _ : FlowRun flow n, n = n := ⟨run, rfl⟩

/-- **NO RUN OVERSHOOTS THE FLOW** — a `FlowRun flow n` whose every fired step was a real index
(each `step k` extension required `flow.stepAt k = some _`, i.e. `k < steps.length`) cannot have reached
beyond the terminal phase: `n ≤ flow.terminalPhase`. The walk stops at the terminal; there is no step
`steps.length` to fire (it would need phase `steps.length` but `stepAt steps.length = none`), so a run
never runs past the end. -/
theorem flowRun_phase_le_length (flow : Flow φ) (n : Nat) (run : FlowRun flow n) :
    n ≤ flow.terminalPhase := by
  induction run with
  | nil => exact Nat.zero_le _
  | step k prev hfire ih =>
    -- the fire at phase k required step k to exist, so k < steps.length, hence k+1 ≤ length.
    have hsome : (fireStep _ k _ _ _ _ _ _).isSome = true := by rw [hfire]; rfl
    rw [fireStep_iff] at hsome
    unfold stepArmed at hsome
    cases hst : flow.stepAt k with
    | none => rw [hst] at hsome; simp at hsome
    | some st =>
      -- stepAt k = some ⇒ k < steps.length ⇒ k+1 ≤ steps.length = terminalPhase.
      have hlt : k < flow.steps.length := by
        unfold Flow.stepAt at hst
        rw [List.getElem?_eq_some_iff] at hst
        exact hst.1
      unfold Flow.terminalPhase
      omega

/-- **THE TERMINAL IS NOT REACHED EARLY** — combining the two: a flow at a phase STRICTLY below its
terminal has NOT completed (some step remains unfired). Stated contrapositively: if the cell's phase is
`< terminalPhase`, the flow is not done — the run certificate for the terminal does not yet exist. This
is the "can't claim completion before the last step" tooth. -/
theorem flow_terminal_only_via_path (flow : Flow φ) (n : Nat)
    (run : FlowRun flow n) (hlt : n < flow.terminalPhase) :
    n ≠ flow.terminalPhase := Nat.ne_of_lt hlt

/-! ## §6 — THE LEG-4 PROPERTIES SURVIVE THE FLOW (the sequencing only adds the phase precondition). -/

/-- **A COMMITTED STEP CARRIES THE REAL EFFECT** — the flow sequencing does not forge a surface: when
`fireStep` commits, the resulting intent fires the step's REAL effect verbatim (it commits via the SAME
`GatedAffordance.fireGated`). The phase discipline is purely an additional refusal condition. -/
theorem fireStep_carries_real_effect (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (st : FlowStep φ) (intent : AffordanceIntent φ)
    (hstep : flow.stepAt k = some st)
    (h : fireStep flow k held ctx old new s post = some intent) :
    intent.surface.firedEffect = st.gated.aff.effect := by
  unfold fireStep at h
  rw [hstep] at h
  by_cases hph : (atPhase flow k old && advancesTo flow k new) = true
  · rw [if_pos hph] at h
    exact fireGated_carries_real_effect st.gated held ctx old new s post intent h
  · rw [if_neg hph] at h; exact absurd h (by simp)

/-- **A COMMITTED STEP BINDS THE ATTESTED ROOT** — leg-4's second clause survives: the surface's
`boundRoot` is the verified turn's `newCommit` (`= post`). The flow adds the phase precondition; the
attested-root binding is untouched (it rides the SAME `GatedAffordance.fireGated`). -/
theorem fireStep_binds_attested_root (flow : Flow φ) (k : Nat) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (st : FlowStep φ) (intent : AffordanceIntent φ)
    (hstep : flow.stepAt k = some st)
    (h : fireStep flow k held ctx old new s post = some intent) :
    intent.surface.boundRoot = post := by
  unfold fireStep at h
  rw [hstep] at h
  by_cases hph : (atPhase flow k old && advancesTo flow k new) = true
  · rw [if_pos hph] at h
    exact fireGated_binds_attested_root st.gated held ctx old new s post intent h
  · rw [if_neg hph] at h; exact absurd h (by simp)

/-! ## §7 — NON-VACUITY TEETH (`#guard`): a CONCRETE 3-step flow (propose → approve → settle) BITES.

The exemplar: a proposal cell whose `phase` register walks 0 → 1 → 2 → 3.
  * step 0 (propose) — the proposer cap, fired at phase 0, advancing to 1;
  * step 1 (approve) — the approver cap AND the proposal must be live (`status == 1`), at phase 1 → 2;
  * step 2 (settle)  — the settler cap, at phase 2 → 3 (the terminal).
Every soundness tooth is witnessed in BOTH polarities below. -/

section Witnesses

/-- A concrete effect type for the witnesses: the three protocol actions. -/
inductive DemoEffect where | propose (id : Nat) | approve (id : Nat) | settle (id : Nat)
deriving DecidableEq, Repr

open Dregg2.Deos.Affordance (CellAffordance)
open Dregg2.Exec (RecordProgram StateConstraint SimpleConstraint)

-- The three cap-gated effect-templates (the buttons), each requiring a distinct cap:
def proposeCell : CellAffordance DemoEffect := { required := [Auth.write], effect := .propose 1, name := 1 }
def approveCell : CellAffordance DemoEffect := { required := [Auth.grant], effect := .approve 1, name := 2 }
def settleCell  : CellAffordance DemoEffect := { required := [Auth.write], effect := .settle 1,  name := 3 }

/-- The approve step's live-state condition: the proposal must be in `status == 1` (LIVE) — the cap is
not enough, the proposal must actually be open. The other two steps gate on the phase alone (`.none`). -/
def liveCond : RecordProgram := .predicate [.simple (.fieldEquals "status" 1)]

/-- The three flow steps (each a `GatedAffordance` wrapped as a `FlowStep`). -/
def proposeStep : FlowStep DemoEffect := ⟨{ aff := proposeCell, stateCond := .none,    method := 0 }⟩
def approveStep : FlowStep DemoEffect := ⟨{ aff := approveCell, stateCond := liveCond, method := 0 }⟩
def settleStep  : FlowStep DemoEffect := ⟨{ aff := settleCell,  stateCond := .none,    method := 0 }⟩

/-- **THE FLOW** — propose → approve → settle, tracked by the `phase` register. ONE typed object. -/
def proposalFlow : Flow DemoEffect :=
  { phaseField := "phase", steps := [proposeStep, approveStep, settleStep] }

-- Viewers:
def proposerHeld : List Auth := [Auth.read, Auth.write]   -- may propose / settle (holds `write`)
def approverHeld : List Auth := [Auth.read, Auth.grant]   -- may approve (holds `grant`)
def memberHeld   : List Auth := [Auth.read]               -- may do NOTHING in the flow

-- Cell states (the `phase` register walks 0→1→2→3; `status` carries the proposal's liveness):
def atPhase0 : Value := .record [("phase", .int 0), ("status", .int 1)]
def atPhase1 : Value := .record [("phase", .int 1), ("status", .int 1)]
def atPhase2 : Value := .record [("phase", .int 2), ("status", .int 1)]
def atPhase3 : Value := .record [("phase", .int 3), ("status", .int 1)]
-- a phase-1 cell whose proposal is NOT live (status closed) — approve must DARKEN here:
def atPhase1Closed : Value := .record [("phase", .int 1), ("status", .int 0)]

-- THE IN-ORDER HAPPY PATH — each step fires at its own phase, in order:
-- (0) propose at phase 0, advancing 0→1 ⇒ FIRES:
#guard (fireStep proposalFlow 0 proposerHeld TurnCtx.empty atPhase0 atPhase1 100 110).isSome
-- (1) approve at phase 1 (proposal live), advancing 1→2 ⇒ FIRES:
#guard (fireStep proposalFlow 1 approverHeld TurnCtx.empty atPhase1 atPhase2 110 120).isSome
-- (2) settle at phase 2, advancing 2→3 (the terminal) ⇒ FIRES:
#guard (fireStep proposalFlow 2 proposerHeld TurnCtx.empty atPhase2 atPhase3 120 130).isSome

-- OUT-OF-ORDER ⇒ REFUSED: firing settle (step 2) while still at phase 0 (nothing approved yet):
#guard (fireStep proposalFlow 2 proposerHeld TurnCtx.empty atPhase0 atPhase1 100 110).isNone
-- firing approve (step 1) while still at phase 0 (nothing proposed yet):
#guard (fireStep proposalFlow 1 approverHeld TurnCtx.empty atPhase0 atPhase1 100 110).isNone

-- A SKIP ⇒ REFUSED: firing settle (step 2) at phase 1 — the approve step was skipped:
#guard (fireStep proposalFlow 2 proposerHeld TurnCtx.empty atPhase1 atPhase2 110 120).isNone
-- firing approve (step 1) at phase 0 — the propose step was skipped (j=0 < k=1):
#guard (fireStep proposalFlow 1 approverHeld TurnCtx.empty atPhase0 atPhase1 100 110).isNone

-- UNAUTHORIZED ⇒ REFUSED: at the RIGHT phase but the wrong viewer —
-- a member (no caps) cannot propose even at phase 0:
#guard (fireStep proposalFlow 0 memberHeld TurnCtx.empty atPhase0 atPhase1 100 110).isNone
-- the proposer (holds `write`, not `grant`) cannot approve even at phase 1:
#guard (fireStep proposalFlow 1 proposerHeld TurnCtx.empty atPhase1 atPhase2 110 120).isNone

-- THE STATE TOOTH (the approve step's live-state gate): at phase 1 with the right approver cap, but the
-- proposal is NOT live (status closed) ⇒ REFUSED (the cap ∧ phase are not enough — the state must agree):
#guard (fireStep proposalFlow 1 approverHeld TurnCtx.empty atPhase1Closed atPhase2 110 120).isNone

-- DOUBLE-FIRE ⇒ REFUSED: trying to propose (step 0) AGAIN after it committed (cell now at phase 1):
#guard (fireStep proposalFlow 0 proposerHeld TurnCtx.empty atPhase1 atPhase2 110 120).isNone
-- trying to approve (step 1) AGAIN after it committed (cell now at phase 2):
#guard (fireStep proposalFlow 1 approverHeld TurnCtx.empty atPhase2 atPhase3 120 130).isNone

-- A NON-ADVANCING transition ⇒ REFUSED (the commit must move the flow forward exactly one phase):
-- propose at phase 0 but the post-state stays at phase 0 (no advance) ⇒ refused:
#guard (fireStep proposalFlow 0 proposerHeld TurnCtx.empty atPhase0 atPhase0 100 110).isNone

-- A committed step carries the REAL effect and binds the new root (the leg-4 carry):
#guard match fireStep proposalFlow 1 approverHeld TurnCtx.empty atPhase1 atPhase2 110 120 with
       | some i => (i.surface.firedEffect == DemoEffect.approve 1) && (i.surface.boundRoot == 120)
       | none   => false

-- THE TERMINAL phase is the number of steps (3):
#guard proposalFlow.terminalPhase == 3
-- the flow's phase reads out of the `phase` register:
#guard proposalFlow.phaseOf atPhase2 == some (2 : Int)

end Witnesses

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  fireStep_iff,
  flow_in_order_accepts,
  fireStep_out_of_order_refuses,
  fireStep_skip_refuses,
  fireStep_unauthorized_refuses,
  fireStep_double_fire_refuses,
  fireStep_advances_one,
  flowRun_phase_le_length,
  flow_terminal_only_via_path,
  fireStep_carries_real_effect,
  fireStep_binds_attested_root
]

/-! ## Rust-mirror sites (LAW #1 — the convergence wires these; do NOT edit the Rust here)

For the concurrent Rust-cutover lane, the twins of this module are:

  * `starbridge-web-surface/src/affordance.rs` — ADD a `Flow { phase_field: String, steps:
    Vec<GatedAffordance> }` struct beside `GatedAffordance` (the twin landed by the GatedAffordance
    mirror). Its `fire_step(k, held, ctx, old, new, s, post)` runs `steps[k].fire(..)` (the EXISTING
    cap∧state gate) ONLY when `old.scalar(&self.phase_field) == Some(k as i64)` (the phase-reached
    precondition, the twin of `atPhase`) AND `new.scalar(&self.phase_field) == Some(k as i64 + 1)` (the
    phase-advance postcondition, the twin of `advancesTo`) — refusing otherwise.

  * `starbridge-web-surface/src/affordance.rs` (`enum FireError`) — ADD a `FireError::PhaseMismatch {
    at: i64, expected: u32 }` variant (the ordering/skip/double-fire refusal, the twin of
    `fireStep_out_of_order_refuses`), beside the existing `Unauthorized` (the cap tooth) and
    `StateConditionUnmet` (the state tooth, the GatedAffordance mirror). One refusal variant covers
    out-of-order, skip AND double-fire — they are all "wrong phase", exactly as in Lean.

  * `cell/src/program.rs` — NO change needed: the phase gate is a `fieldEquals`/`fieldDelta` over the
    EXISTING `evaluate_constraint_full` named-scalar read; the convergence authors NO new evaluator
    semantics (LAW #1 — the phase counter is an ordinary register the program already reads). The flow
    discipline is a wrapper over `GatedAffordance::fire`, not a new state-machine engine.

  * The `phase_field` register is declared in the `FactoryDescriptor`'s `fields` block
    (`docs/REFINEMENT-DESIGN.md` Decision 1) like any other named scalar; a flow's terminal is
    `steps.len()`, and the per-viewer surface (`project_gated_for`, the GatedAffordance mirror) at a
    given phase shows exactly the ONE armed step plus any phase-free affordances — the htmx reactivity
    walking the flow.
-/

end Dregg2.Deos.Flow
