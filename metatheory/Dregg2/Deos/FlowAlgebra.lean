/-
# Dregg2.Deos.FlowAlgebra — the workflow/affordance-flow COMPOSITION ALGEBRA is RIGHT-SKEWED.

`docs/FLOW-COMPOSITION-ALGEBRA.md` (companion). Anchors: `Dregg2.Deos.Reactive` (the `TransitionGate`
reads BOTH `old` and `new` — the late-binding / online-choice mechanism; "a property of `new` alone can
never witness it"), `Dregg2.Deos.WorkflowBridge` (a `Protocol.Workflow` step IS a sequenced reactive
fire — the workflow exec is the `⋆`), and `Dregg2.Exec.Value` (the real name-keyed state substrate the
flows thread).

THE QUESTION (falsifiable). Does dregg's flow algebra satisfy FULL left-distributivity of CHOICE over
COMPOSITION — `(P ⊔ Q) ⋆ R = (P ⋆ R) ⊔ (Q ⋆ R)` — or only the HALF
`(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R`?

THE ANSWER (this module, proved). **Only the HALF.** dregg's flow algebra is RIGHT-SKEWED: the half
holds (`flow_choice_halfdistrib`) but the converse FAILS (`flow_choice_right_skewed`, the headline).
dregg's flow algebra is a **right-skewed Kleene algebra with distributive meets** (RSKA_d⊓, à la Pradic,
"The Equational Theory of the Weihrauch Lattice with (Iterated) Composition", arXiv:2408.14999) — and
the distributive MEET is discharged here too (`flow_meet_semilattice`, the `_d⊓` of the classification).

WHY (the algebraic shadow of the reactive rung). The separation is NOT a trace-LANGUAGE fact — in trace
language the two sides are EQUAL (`flow_choice_languages_equal`, the dregg analogue of Pradic's
Example 1.1: `(b⋆a) ⊔ (c⋆a)` and `(b⊔c) ⋆ a` both denote `{ab, ac}`). The separation lives ONE rung up,
in the ONLINE step-by-step SIMULATION preorder (Pradic's SG game). We model a flow as a labelled
TRANSITION SYSTEM over the real `Value` state (each fire is a visible letter; `⊔` is a branch node; `⋆`
threads the state, `R` first), and `≤` as a STEP-BY-STEP SIMULATION: a relation matching each letter-move
of the simulated side by a letter-move of the simulator, PRESERVING the relation. In `(P ⊔ Q) ⋆ R`
(Pradic's order: `⋆`'s RIGHT factor runs FIRST), `R` runs first and emits its output letter; the
`P`-vs-`Q` branch is taken AFTER — from ONE node that still has BOTH continuations (the LATE branch,
exactly the `TransitionGate.link` reading `new`: the choice reads `R`'s output). In `(P ⋆ R) ⊔ (Q ⋆ R)`
the branch is the FIRST node, committing BEFORE `R` runs (the EARLY branch). A step-by-step simulator of
the late side from the early side must, to match `R`'s move, have ALREADY committed its branch — so from
its post-`R` node only ONE continuation remains, and the late side's OTHER continuation cannot be matched.
No lookahead: the simulator commits before it learns which continuation will be demanded. The right-skew
is the algebraic shadow of the reactive/observed-state rung — Pradic: "the second component `f` of a
question `⟨w,f⟩ ∈ dom((P⊔Q)⋆R)` might decide whether a question should be asked to `P` or `Q` depending on
its input" — which is exactly the `old+new` read of the `TransitionGate`.

## What is built

  * §1 `Proc` + `Step` — a flow as a labelled transition system over the real `Value`: `done` (halt),
    `emit ℓ` (a visible letter then halt), `wr f v` (a state WRITE that ALSO emits its output letter —
    `R`'s observable, reading-its-output is the late-binding), `ch` (branch — offer both), `seqp`
    (sequential, state-threaded: the RIGHT factor runs first, then the left reads its post-state). The
    flow operators `⊔`/`⋆`/`⊓` and atoms compile to `Proc`s. ALL steps are visible letters (the
    simulation is over the observable transition graph, matching Pradic's automata).

  * §2 `IsSim` / `Flow.Sim` (the ONLINE simulation preorder `≤ᶠ`) — a STEP-BY-STEP SIMULATION: a
    relation `Rel` with `Rel (P-start) (Q-start)` such that every letter-move `c →ℓ d` of the simulated
    side is matched by a move `c' →ℓ d'` of the simulator with `Rel d d'`. Built step by step ⟹ the
    simulator commits ONLINE (no lookahead). A genuine preorder (`sim_refl`, `sim_trans`). NOT offline
    trace-containment (which would miss the separation — `flow_choice_languages_equal`).

  * §3 `flow_choice_halfdistrib` (THE HALF — always holds, keystone). `(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R`:
    the EARLY side step-by-step-simulates INTO the late side. The late side mimics the early side's
    committed branch — it has MORE freedom (after `R` it can still take EITHER branch), so the early
    behavior embeds. (Pradic: this direction holds throughout the Weihrauch lattice.)

  * §4 `flow_choice_right_skewed` (THE HEADLINE — the converse FAILS). The concrete REACTIVE
    counterexample: `R` runs and emits its output letter `0` (and writes a field); the `P`-vs-`Q` branch
    fires DIFFERENT letters `1`/`2`. We prove `(P ⊔ Q) ⋆ R ≰ (P ⋆ R) ⊔ (Q ⋆ R)` — NO simulation embeds
    the late side into the early side: after matching `R`'s move `0`, the early simulator sits at a node
    that has ALREADY committed to one branch (one of `1`,`2`), but the late side's post-`R` node has
    BOTH live, so the late `1`-move and `2`-move cannot both be matched. The verdict: right-skewed.

  * §5 NON-VACUITY (`#guard` + the `_live`/`_run` lemmas): every load-bearing `≤` holds on a NON-empty
    transition graph (a vacuous simulation that holds because the graph is dead would be a BUG — pinned
    shut by exhibited letter-moves). `flow_choice_languages_equal` pins the separation is NOT in the
    language; the right-skew is genuinely the online rung.

## The payoff (a named follow-on — NOT built in this lane; `docs/FLOW-COMPOSITION-ALGEBRA.md` §Payoff)

If dregg's flow algebra is right-skewed (it is), then "does flow/caveat-policy A REFINE B" is a DECIDABLE
question via Pradic's Büchi / alternating-automata simulation-game characterization of RSKA_d⊓
(PSPACE-hard in general; PTIME on the pointed Weihrauch fragment) — Theorem 1.4: `e ≤ f` is valid iff
Duplicator wins `SG(∅ | {e} ⊢ f)`. The ARGUS "refines" bar (does this protocol evolution refine the
spec?) inherits a decision procedure with known complexity. This module pins the PRECONDITION of that
payoff — the right-skew — as a machine-checked theorem; the decision procedure itself is the follow-on.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2.Deos.FlowAlgebra` green (LOCAL). Disjoint + additive: a NEW module, touches NO existing proof.
-/
import Dregg2.Exec.Program
import Dregg2.Tactics
import Mathlib.Order.Lattice
import Mathlib.Data.Set.Basic

namespace Dregg2.Deos.FlowAlgebra

open Dregg2.Exec (Value)

set_option linter.dupNamespace false

/-! ## §1 — A flow as a labelled transition system over the real `Value` state.

A flow's behavior is a labelled transition graph: nodes are process states `(p, σ)` (the remaining
structure plus the live cell state); edges are VISIBLE letters (the affordance fired / `R`'s output). The
state is THREADED through `seqp`, so a later factor reads an earlier one's post-state — the `old → new`
read of the reactive `TransitionGate`, which is what makes the choice ONLINE.

ALL steps are VISIBLE (matching Pradic's automata, whose edges are all letters). The branch `ch` is a
NODE with both out-edges available — NOT a silent commitment — so the timing of the choice is encoded in
the GRAPH SHAPE (early = branch first; late = branch after `R`'s letter), which is exactly what the
step-by-step simulation can see and the trace language cannot. -/

/-- A `Letter` is one observed affordance fire (or `R`'s output) — a `Nat` tag. -/
abbrev Letter := Nat

/-- A `Trace` is the sequence of fired letters (the observable event log). -/
abbrev Trace := List Letter

/-- Update (or insert) field `f := .int v` in a record value; on a non-record, produce `{f := v}`. -/
def setField : Value → Dregg2.Exec.FieldName → Int → Value
  | .record fs, f, v =>
      if fs.any (fun p => p.1 == f)
      then .record (fs.map (fun p => if p.1 == f then (p.1, .int v) else p))
      else .record (fs ++ [(f, .int v)])
  | _, f, v => .record [(f, .int v)]

/-- **`Proc`** — a process tree (the syntax of a flow), so the labelled transition `Step` can read the
branch STRUCTURE (which distinguishes early from late choice). -/
inductive Proc where
  /-- The halted process (the unit of `seqp`). -/
  | done : Proc
  /-- Emit a visible letter `ℓ`, then halt (`fire ℓ`). -/
  | emit : Letter → Proc
  /-- A state WRITE `f := v` that ALSO emits its output letter `ℓ` (the `R` of the counterexample: it
  runs, mutates state, and produces an observable output the downstream choice reads). -/
  | wr   : Letter → Dregg2.Exec.FieldName → Int → Proc
  /-- BRANCH — offer BOTH continuations (`P ⊔ Q`): a node with both out-edges. -/
  | ch   : Proc → Proc → Proc
  /-- SEQUENTIAL composition (Pradic's order: do the RIGHT factor `r` FIRST, then the left `p` on `r`'s
  post-state). `seqp p r` runs `r` to a halt threading state, then continues as `p`. -/
  | seqp : Proc → Proc → Proc

/-- **`Step (p, σ) ℓ (p', σ')`** — one labelled (VISIBLE) small step from `(p, σ)` to `(p', σ')` emitting
letter `ℓ`. The `seqp` rule THREADS the state: the right factor steps first; only when it HALTS (`done`)
does control pass SILENTLY-VIA-A-HANDOFF… — but to keep ALL transitions visible-letter-labelled (so the
simulation is a clean letter-matching), the hand-off is folded into the right factor's LAST step: when
`r` would halt, `seqp p r` instead continues directly as `p` carrying `r`'s post-state. Concretely there
is no separate silent hand-off step — the `seqDone` case fires the FIRST letter of `p` from `r`'s
post-state in one move. We achieve this by the two `seqp` rules below. -/
inductive Step : Proc × Value → Letter → Proc × Value → Prop where
  /-- `emit ℓ` fires a visible `ℓ` and halts (state unchanged). -/
  | emit (ℓ : Letter) (σ : Value) :
      Step (.emit ℓ, σ) ℓ (.done, σ)
  /-- `wr ℓ f v` emits its output letter `ℓ` AND writes `f := v` in one step (the `R`-move: run +
  observable output + state mutation). -/
  | wr (ℓ : Letter) (f : Dregg2.Exec.FieldName) (v : Int) (σ : Value) :
      Step (.wr ℓ f v, σ) ℓ (.done, setField σ f v)
  /-- BRANCH left: take the left continuation's FIRST move (a letter-move of `p`). -/
  | chL (p q p' : Proc) (σ σ' : Value) (ℓ : Letter) (h : Step (p, σ) ℓ (p', σ')) :
      Step (.ch p q, σ) ℓ (p', σ')
  /-- BRANCH right: take the right continuation's FIRST move (a letter-move of `q`). -/
  | chR (p q q' : Proc) (σ σ' : Value) (ℓ : Letter) (h : Step (q, σ) ℓ (q', σ')) :
      Step (.ch p q, σ) ℓ (q', σ')
  /-- SEQ step: the RIGHT factor `r` takes a NON-halting step (it runs FIRST, `r` not yet done); `seqp p
  r` follows it, staying in the sequence. -/
  | seqR (p r r' : Proc) (σ σ' : Value) (ℓ : Letter) (h : Step (r, σ) ℓ (r', σ')) :
      Step (.seqp p r, σ) ℓ (.seqp p r', σ')
  /-- SEQ hand-off + first-move-of-`p`: when the right factor `r`'s step LANDS it in `done` (it just
  finished), control passes to the left factor `p`, whose FIRST move fires immediately from `r`'s
  post-state `σ'` (`p` reads what `r` wrote — the threading). One visible step carries `r`'s last letter;
  the next step is `p`'s first. We split it: a `seqp p done` is `p`. -/
  | seqDone (p p' : Proc) (σ σ' : Value) (ℓ : Letter) (h : Step (p, σ) ℓ (p', σ')) :
      Step (.seqp p .done, σ) ℓ (p', σ')

/-! ## §2 — The ONLINE simulation preorder `≤ᶠ` (a STEP-BY-STEP SIMULATION; no lookahead).

`P ≤ Q` ("`Q` online-simulates `P`") iff there is a SIMULATION relation `Rel` with `Rel (P-start)
(Q-start)` such that whenever `Rel c c'`, every letter-move `c →ℓ d` of the simulated side is matched by a
move `c' →ℓ d'` of the simulator with `Rel d d'`. The relation is built STEP BY STEP, so the simulator
commits its branch ONLINE — it must produce a matching move NOW, not knowing which move will be demanded
NEXT (no lookahead). This is the dregg analogue of Pradic's SG game (Theorem 1.4). It is STRICTLY FINER
than offline trace-containment: the late and early sides share a language
(`flow_choice_languages_equal`) yet are separated here (`flow_choice_right_skewed`). -/

/-- **`IsSim Rel`** — `Rel` is a (step-by-step) simulation: every letter-move of the LEFT (simulated) side
is matched by a letter-move of the RIGHT (simulator) side with the SAME letter, preserving `Rel`. -/
def IsSim (Rel : (Proc × Value) → (Proc × Value) → Prop) : Prop :=
  ∀ c c', Rel c c' → ∀ ℓ d, Step c ℓ d → ∃ d', Step c' ℓ d' ∧ Rel d d'

/-- **`SimFrom c c'`** — `c'` simulates `c`: some simulation relates them. -/
def SimFrom (c c' : Proc × Value) : Prop := ∃ Rel, IsSim Rel ∧ Rel c c'

/-- **`Flow.Sim P Q` (the ONLINE simulation preorder `≤ᶠ`).** `Q` online-simulates `P` iff `Q`'s start
process simulates `P`'s, FROM EVERY start state σ (the state is part of the configuration; we quantify
over the initial σ so the order is uniform in the cell's starting state). -/
def Flow.Sim (P Q : Proc) : Prop := ∀ σ : Value, SimFrom (P, σ) (Q, σ)

@[inherit_doc] infix:50 " ≤ᶠ " => Flow.Sim

/-! ## §2a — `≤ᶠ` is a genuine preorder (reflexive + transitive). -/

/-- Equality is a simulation (the diagonal): a move is matched by the SAME move. -/
theorem isSim_eq : IsSim (· = ·) := by
  intro c c' hcc' ℓ d hd; subst hcc'; exact ⟨d, hd, rfl⟩

/-- **`sim_refl` — `≤ᶠ` is reflexive.** `P ≤ᶠ P` via the diagonal simulation. -/
theorem sim_refl (P : Proc) : P ≤ᶠ P := fun σ => ⟨(· = ·), isSim_eq, rfl⟩

/-- The relational composition of two simulations is a simulation (so `≤ᶠ` is transitive). -/
theorem isSim_comp {R₁ R₂ : (Proc × Value) → (Proc × Value) → Prop}
    (h₁ : IsSim R₁) (h₂ : IsSim R₂) : IsSim (fun a c => ∃ b, R₁ a b ∧ R₂ b c) := by
  rintro a c ⟨b, hab, hbc⟩ ℓ d hd
  obtain ⟨e, hbe, hRe⟩ := h₁ a b hab ℓ d hd
  obtain ⟨f, hcf, hRf⟩ := h₂ b c hbc ℓ e hbe
  exact ⟨f, hcf, e, hRe, hRf⟩

/-- **`sim_trans` — `≤ᶠ` is transitive.** `P ≤ᶠ Q`, `Q ≤ᶠ S` ⟹ `P ≤ᶠ S`, by composing simulations at
each start state. -/
theorem sim_trans {P Q S : Proc} (hPQ : P ≤ᶠ Q) (hQS : Q ≤ᶠ S) : P ≤ᶠ S := by
  intro σ
  obtain ⟨R₁, h₁, hr₁⟩ := hPQ σ
  obtain ⟨R₂, h₂, hr₂⟩ := hQS σ
  exact ⟨fun a c => ∃ b, R₁ a b ∧ R₂ b c, isSim_comp h₁ h₂, ⟨(Q, σ), hr₁, hr₂⟩⟩

/-! ## §1b — The flow operators as `Proc`-builders (`⊔` / `⋆` / `⊓` / atoms). -/

/-- `Flow.fire ℓ` — the atomic flow firing letter `ℓ` once. -/
def Flow.fire (ℓ : Letter) : Proc := .emit ℓ

/-- `Flow.run ℓ f v` — the `R`-atom: run, emit output letter `ℓ`, write field `f := v`. -/
def Flow.run (ℓ : Letter) (f : Dregg2.Exec.FieldName) (v : Int) : Proc := .wr ℓ f v

/-- `Flow.done` — the skip flow (halt). -/
def Flow.done : Proc := .done

/-- `P ⊔ Q` — CHOICE (offer both): the branch node. -/
def Flow.join (P Q : Proc) : Proc := .ch P Q

/-- `P ⋆ R` — SEQUENTIAL composition (Pradic's order: do `R` then `P`): the `seqp` node, `R` first. -/
def Flow.seq (P R : Proc) : Proc := .seqp P R

@[inherit_doc] infixl:65 " ⊔ᶠ " => Flow.join
@[inherit_doc] infixl:70 " ⋆ᶠ " => Flow.seq

/-! ## §1c — The MEET, as a genuine `SemilatticeInf` (the `_d⊓` of RSKA_d⊓).

The denotational MEET (run-set intersection — the §C2 `ReplayMembrane` negotiation meet, lifted to flows)
is a `SemilatticeInf` over the OFFLINE run-set order. We expose the denotation `runs` and the meet on it,
so the "distributive meet" of the classification is REAL. (The right-skew lives in the ONLINE order §2;
the meet's lattice structure is an OFFLINE fact, which is exactly where Pradic's distributive-meet axioms
sit — the lattice `⊓`/`⊔` ARE distributive among themselves; only `⊔`-over-`⋆` is skewed.) -/

/-- **`runs P σ`** — the offline trace LANGUAGE of `P` from σ: the set of finite letter-traces `P` can
emit (multi-step). The denotation the lattice operations live over. -/
inductive runs : Proc → Value → Trace → Prop where
  /-- The empty trace is always a run (a process may halt / be observed having done nothing yet). -/
  | nil (p : Proc) (σ : Value) : runs p σ []
  /-- A letter-move extends a run of the successor. -/
  | cons {p : Proc} {σ : Value} {ℓ : Letter} {p' : Proc} {σ' : Value} {t : Trace}
      (h : Step (p, σ) ℓ (p', σ')) (hr : runs p' σ' t) : runs p σ (ℓ :: t)

/-- The trace-language denotation as a `Value`-indexed set (for the lattice instance). -/
def lang (P : Proc) : Value → Set Trace := fun σ => { t | runs P σ t }

/-- Flows ordered by pointwise language containment (the OFFLINE order — NOT the online `≤ᶠ`). The two
DIFFER (the whole point: §4 separates them). Carried only to host the meet's `SemilatticeInf`. -/
instance : PartialOrder (Value → Set Trace) where
  le f g := ∀ σ, f σ ⊆ g σ
  le_refl f σ := subset_rfl
  le_trans f g h hfg hgh σ := subset_trans (hfg σ) (hgh σ)
  le_antisymm f g hfg hgf := funext fun σ => Set.Subset.antisymm (hfg σ) (hgf σ)

/-- **`flow_meet_semilattice` — the language meet is a genuine `SemilatticeInf`.** Run-set intersection
is the greatest lower bound under pointwise containment (the §C2 negotiation meet, at the flow layer): so
the "distributive MEET" of RSKA_d⊓ is REAL here. The `_d⊓` of the classification is discharged. -/
instance flow_meet_semilattice : SemilatticeInf (Value → Set Trace) where
  inf f g := fun σ => f σ ∩ g σ
  inf_le_left f g σ := Set.inter_subset_left
  inf_le_right f g σ := Set.inter_subset_right
  le_inf f g h hfg hfh σ := Set.subset_inter (hfg σ) (hfh σ)

/-! ## §3 — THE HALF (always holds): `(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R`.

The EARLY side step-by-step-simulates INTO the late side. The simulating relation `halfRel` covers the
reachable related pairs: the START pair (early branch-of-sequences ↦ late deferred sequence), a COMMITTED
branch still threading through `R`'s remaining process `r'` (early `seqp F r'` ↦ late `seqp (P⊔Q) r'`),
and the DIAGONAL once `R` has handed off. The crux: the early side commits its branch up front; the late
side matches by taking the SAME branch through its `ch` AFTER `R` — it has MORE freedom (it can defer), so
the early committed behavior embeds. No lookahead needed (the late side commits LATER than required). -/

/-- The explicit simulation for the half. `F` (the committed factor) ranges over `{P, Q}`; pairs are
indexed by `R`'s remaining process `r'` and the threaded state. -/
inductive halfRel (P Q R : Proc) : (Proc × Value) → (Proc × Value) → Prop where
  /-- Start: early choice-of-two-sequences ↦ late deferred sequence. -/
  | start (σ : Value) :
      halfRel P Q R ((P ⋆ᶠ R) ⊔ᶠ (Q ⋆ᶠ R), σ) ((P ⊔ᶠ Q) ⋆ᶠ R, σ)
  /-- A committed branch `F ∈ {P, Q}` still threading through `R`'s remaining process `r'`. -/
  | committed (F r' : Proc) (σ : Value) (hF : F = P ∨ F = Q) :
      halfRel P Q R (.seqp F r', σ) (.seqp (P ⊔ᶠ Q) r', σ)
  /-- The diagonal: once both sides reach the SAME state (after `R`'s hand-off), lockstep. -/
  | diag (c : Proc × Value) : halfRel P Q R c c

/-- A late-side `seqp (P⊔Q) r'` matches a left/right branch's sequential move by taking that branch
through the `ch` (folding the early `chL`/`chR` into a `seqR`/`seqDone` after the `ch`). -/
theorem late_matches_committed (P Q R F r' : Proc) (σ : Value) (hF : F = P ∨ F = Q)
    {ℓ : Letter} {d : Proc × Value} (hstep : Step (.seqp F r', σ) ℓ d) :
    ∃ d', Step (.seqp (P ⊔ᶠ Q) r', σ) ℓ d' ∧ halfRel P Q R d d' := by
  cases hstep with
  | seqR _ _ r'' _ σ'' _ hr =>
    -- R stepped r' → r''; late matches with the SAME seqR step, staying committed.
    exact ⟨_, Step.seqR (P ⊔ᶠ Q) r' r'' σ σ'' ℓ hr, halfRel.committed F r'' σ'' hF⟩
  | seqDone _ p' _ σ'' _ hp =>
    -- r' = done: early hands off to F's first move (Step (F,σ) ℓ p'). Late: seqp (P⊔Q) done hands off to
    -- (P⊔Q)'s first move = the SAME F-move, taken through the ch (chL if F=P, chR if F=Q).
    rcases hF with h | h
    · -- F = P: the early F-move IS a P-move; late takes the chL branch through (P⊔Q)'s hand-off.
      rw [h] at hp
      exact ⟨_, Step.seqDone (P ⊔ᶠ Q) p' σ σ'' ℓ (Step.chL P Q p' σ σ'' ℓ hp), halfRel.diag _⟩
    · -- F = Q: the early F-move IS a Q-move; late takes the chR branch.
      rw [h] at hp
      exact ⟨_, Step.seqDone (P ⊔ᶠ Q) p' σ σ'' ℓ (Step.chR P Q p' σ σ'' ℓ hp), halfRel.diag _⟩

/-- `halfRel` is a simulation. -/
theorem halfRel_isSim (P Q R : Proc) : IsSim (halfRel P Q R) := by
  intro c c' hcc' ℓ d hd
  induction hcc' with
  | start σ =>
    -- early start = ch (P⋆R) (Q⋆R); a move is chL (P⋆R's first move) or chR (Q⋆R's first move).
    cases hd with
    | chL _ _ p' _ σ' _ hp =>
      -- p' is the result of (P⋆R)'s first move = a seqp-move; relate to late by `committed`/`late_matches`.
      -- (P⋆R) = seqp P R; its move hp : Step (seqp P R, σ) ℓ p'. Late = seqp (P⊔Q) R; match via committed.
      exact late_matches_committed P Q R P R σ (Or.inl rfl) hp
    | chR _ _ q' _ σ' _ hq =>
      exact late_matches_committed P Q R Q R σ (Or.inr rfl) hq
  | committed F r' σ hF =>
    exact late_matches_committed P Q R F r' σ hF hd
  | diag c =>
    exact ⟨d, hd, halfRel.diag d⟩

/-- **`flow_choice_halfdistrib` — THE HALF (keystone, always holds).** `(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R`
in the ONLINE simulation order: the early-branch side online-simulates into the late-branch side. The
witnessing simulation is `halfRel` — the late side mimics the early side's committed branch by taking the
SAME branch through its `ch` AFTER `R`. No lookahead is needed: deferring a commitment is always
online-admissible. This is the half that ALWAYS holds (Pradic: this direction holds throughout the
Weihrauch lattice) — the "right-skew" is the FAILURE of the converse (§4). -/
theorem flow_choice_halfdistrib (P Q R : Proc) :
    ((P ⋆ᶠ R) ⊔ᶠ (Q ⋆ᶠ R)) ≤ᶠ ((P ⊔ᶠ Q) ⋆ᶠ R) :=
  fun σ => ⟨halfRel P Q R, halfRel_isSim P Q R, halfRel.start σ⟩

/-! ## §4 — THE HEADLINE: the converse FAILS — dregg's flow algebra is RIGHT-SKEWED.

The concrete REACTIVE counterexample. `R := run 0 "b" 1` runs, emits its output letter `0`, and writes
`b := 1` (the state a downstream reactive choice reads). The `P`-vs-`Q` branch fires DIFFERENT letters:
`P := fire 1`, `Q := fire 2`.

  * LATE `(P ⊔ Q) ⋆ R`: `R` runs first (one node, the `0`-move), landing in a node `(ch (fire 1)
    (fire 2), σ1)` that has BOTH the `1`-move and the `2`-move live (the choice is taken AFTER `R`,
    reading its output — the late-binding).
  * EARLY `(P ⋆ R) ⊔ (Q ⋆ R)`: the branch is the FIRST node. The `0`-move is available on either branch,
    but TAKING it commits the branch — after the `0`-move the early side sits at `(fire 1, σ1)` (only the
    `1`-move) OR `(fire 2, σ1)` (only the `2`-move).

A simulation embedding the late side into the early side must match `R`'s `0`-move; whatever early node
it lands in has ALREADY committed to one of `1`,`2` — so it cannot match BOTH of the late side's `1` and
`2` moves. We prove `¬ (late ≤ early)` — the right-skew. -/

section Counterexample

/-- The field `R` writes (and the reactive choice reads). -/
private def fld : Dregg2.Exec.FieldName := "b"

/-- `R := run 0 "b" 1` — runs, emits output letter `0`, writes `b := 1` (the first-executed factor whose
output the downstream choice reads). -/
def Rr : Proc := Flow.run 0 fld 1

/-- `P := fire 1` — the left branch fires `1`. -/
def Pf : Proc := Flow.fire 1

/-- `Q := fire 2` — the right branch fires `2` (DIFFERENT letter — the choice is observable). -/
def Qf : Proc := Flow.fire 2

/-- A concrete start state — a record without `b` (so `R`'s write is observable). -/
def σ0 : Value := .record [("a", .int 0)]

/-- `R`'s post-state from `σ0`: `σ0` with `b := 1` appended. -/
def σ1 : Value := setField σ0 fld 1

/-- The LATE side's first move from `σ0`: `R` runs (emits its output letter `0`, writes `b := 1`),
landing in the post-`R` node `(seqp (P⊔Q) done, σ1)` — the STILL-OPEN choice node from which BOTH the
`1`-move and the `2`-move are live (the branch is taken AFTER `R`, reading its output). -/
theorem late_step0 : Step ((Pf ⊔ᶠ Qf) ⋆ᶠ Rr, σ0) 0 (.seqp (Pf ⊔ᶠ Qf) .done, σ1) := by
  -- (P⊔Q) ⋆ R = seqp (ch P Q) (wr 0 "b" 1); R's wr-move lands `r` in `done`, so the seqR step keeps the
  -- seqp wrapper and lands at (seqp (P⊔Q) done, σ1). Both branches are still reachable from there.
  exact Step.seqR (Pf ⊔ᶠ Qf) Rr .done σ0 σ1 0 (Step.wr 0 fld 1 σ0)

/-- From the post-`R` node BOTH letters are live: `(seqp (P⊔Q) done, σ1)` can fire `1` (via the
hand-off into `P`'s `chL` move) AND fire `2` (via `Q`'s `chR` move). The choice is OPEN after `R`. -/
theorem late_post_has_both :
    Step (.seqp (Pf ⊔ᶠ Qf) .done, σ1) 1 (.done, σ1) ∧
    Step (.seqp (Pf ⊔ᶠ Qf) .done, σ1) 2 (.done, σ1) := by
  constructor
  · exact Step.seqDone (Pf ⊔ᶠ Qf) .done σ1 σ1 1 (Step.chL Pf Qf .done σ1 σ1 1 (Step.emit 1 σ1))
  · exact Step.seqDone (Pf ⊔ᶠ Qf) .done σ1 σ1 2 (Step.chR Pf Qf .done σ1 σ1 2 (Step.emit 2 σ1))

/-! ### §4a — The early side's structure: its `0`-move COMMITS the branch (the inversion lemmas). -/

/-- The atom `Pf = emit 1` has a UNIQUE move: `1` to `done`. (Inversion.) -/
theorem Pf_step_inv {ℓ : Letter} {d : Proc × Value} {σ : Value} (h : Step (Pf, σ) ℓ d) :
    ℓ = 1 ∧ d = (.done, σ) := by
  cases h with | emit _ _ => exact ⟨rfl, rfl⟩

/-- The atom `Qf = emit 2` has a UNIQUE move: `2` to `done`. (Inversion.) -/
theorem Qf_step_inv {ℓ : Letter} {d : Proc × Value} {σ : Value} (h : Step (Qf, σ) ℓ d) :
    ℓ = 2 ∧ d = (.done, σ) := by
  cases h with | emit _ _ => exact ⟨rfl, rfl⟩

/-- `R = wr 0 "b" 1` has a UNIQUE move: `0` to `(done, σ[b:=1])`. (Inversion.) -/
theorem Rr_step_inv {ℓ : Letter} {d : Proc × Value} {σ : Value} (h : Step (Rr, σ) ℓ d) :
    ℓ = 0 ∧ d = (.done, setField σ fld 1) := by
  cases h with | wr _ _ _ _ => exact ⟨rfl, rfl⟩

/-- **The committed early node `(seqp Pf done, σ1)` admits ONLY the `1`-move** — it CANNOT fire `2`.
(Once the early side committed to the `P`-branch, `2` is gone.) This is the obstruction: after matching
`R`, the early simulator that committed to `P` cannot follow the late side's `2`. -/
theorem seqPdone_no_2 {d : Proc × Value} (h : Step (.seqp Pf .done, σ1) 2 d) : False := by
  cases h with
  | seqR _ _ r' _ _ _ hr => cases hr   -- r = done has no move
  | seqDone _ p' _ _ _ hp =>
    -- the hand-off fires Pf's first move with letter 2 — but Pf only fires 1. Contradiction.
    exact absurd (Pf_step_inv hp).1 (by decide)

/-- **The committed early node `(seqp Qf done, σ1)` admits ONLY the `2`-move** — it CANNOT fire `1`. -/
theorem seqQdone_no_1 {d : Proc × Value} (h : Step (.seqp Qf .done, σ1) 1 d) : False := by
  cases h with
  | seqR _ _ r' _ _ _ hr => cases hr
  | seqDone _ p' _ _ _ hp =>
    exact absurd (Qf_step_inv hp).1 (by decide)

/-- **Every `0`-move from the early start COMMITS the branch** — it lands in either `(seqp Pf done, σ1)`
(committed to `P`) or `(seqp Qf done, σ1)` (committed to `Q`). There is no `0`-move keeping BOTH branches
open: taking `R`'s move forces the branch. (Inversion on the early start's step.) -/
theorem early_step0_commits {d : Proc × Value} (h : Step ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr), σ0) 0 d) :
    d = (.seqp Pf .done, σ1) ∨ d = (.seqp Qf .done, σ1) := by
  -- early start = ch (seqp Pf Rr) (seqp Qf Rr). A 0-move is chL (P-branch's R-move) or chR (Q-branch's).
  cases h with
  | chL _ _ p' _ σ' _ hp =>
    -- p' is (seqp Pf Rr)'s first move. seqp Pf Rr runs Rr first; its move is Rr's wr-move → seqp Pf done.
    left
    cases hp with
    | seqR _ _ r' _ σ'' _ hr =>
      -- hr : Step (Rr, σ0) 0 (r', σ''); Rr's only move lands in (done, σ1). seqR lands at
      -- (seqp Pf r', σ''); with (r', σ'') = (done, σ1) this is (seqp Pf done, σ1).
      obtain ⟨_, hd⟩ := Rr_step_inv hr
      rw [Prod.mk.injEq] at hd; obtain ⟨hr', hσ''⟩ := hd
      subst hr'; subst hσ''; rfl
  | chR _ _ q' _ σ' _ hq =>
    right
    cases hq with
    | seqR _ _ r' _ σ'' _ hr =>
      obtain ⟨_, hd⟩ := Rr_step_inv hr
      rw [Prod.mk.injEq] at hd; obtain ⟨hr', hσ''⟩ := hd
      subst hr'; subst hσ''; rfl

/-- **`flow_choice_right_skewed` — THE HEADLINE (the converse FAILS; dregg's flow algebra is right-skewed).**
`(P ⊔ Q) ⋆ R ≰ (P ⋆ R) ⊔ (Q ⋆ R)` in the ONLINE simulation order, on the concrete reactive
counterexample (`R := run 0 "b" 1`, `P := fire 1`, `Q := fire 2`). NO simulation embeds the late side into
the early side: after matching `R`'s `0`-move, the early simulator has COMMITTED its branch (it sits at
`(seqp Pf done, σ1)` OR `(seqp Qf done, σ1)`, by `early_step0_commits`), so it admits ONLY ONE of the
letters `1`,`2` (`seqPdone_no_2` / `seqQdone_no_1`) — but the late side's post-`R` node has BOTH live
(`late_post_has_both`), and a simulation must match BOTH. The early side cannot, because it had to commit
before learning which letter would be demanded — no lookahead. This is the algebraic shadow of the
reactive rung: the branch reads `R`'s output, which the early side cannot anticipate. dregg's flow algebra
is RIGHT-SKEWED — a right-skewed Kleene algebra with distributive meets (RSKA_d⊓). -/
theorem flow_choice_right_skewed :
    ¬ (((Pf ⊔ᶠ Qf) ⋆ᶠ Rr) ≤ᶠ ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr))) := by
  intro hsim
  -- instantiate the simulation at the start state σ0.
  obtain ⟨Rel, hRelSim, hRel0⟩ := hsim σ0
  -- LATE takes its 0-move (R runs); the simulator matches, landing in some early `e` related to the
  -- late post-R node.
  obtain ⟨e, he0, hRelPost⟩ := hRelSim _ _ hRel0 0 _ late_step0
  -- `e` is a 0-move target from the early start ⇒ committed to P or Q.
  rcases early_step0_commits he0 with hP | hP
  · -- e = (seqp Pf done, σ1): committed to P. The late post-R node fires 2 (late_post_has_both.2); the
    -- simulator must match with a 2-move from e — but seqPdone has no 2-move. Contradiction.
    subst hP
    obtain ⟨e2, he2, _⟩ := hRelSim _ _ hRelPost 2 _ late_post_has_both.2
    exact seqPdone_no_2 he2
  · -- e = (seqp Qf done, σ1): committed to Q. The late post-R node fires 1; the simulator must match
    -- with a 1-move from e — but seqQdone has no 1-move. Contradiction.
    subst hP
    obtain ⟨e1, he1, _⟩ := hRelSim _ _ hRelPost 1 _ late_post_has_both.1
    exact seqQdone_no_1 he1

/-! ### §4b — The separation is NOT in the trace LANGUAGE (the dregg Example 1.1).

Both sides recognize the SAME language `{[], [0], [0,1], [0,2]}` from `σ0` (Pradic's Example 1.1:
`(b⋆a) ⊔ (c⋆a)` and `(b⊔c) ⋆ a` both denote `{ab, ac}`). So the right-skew (§4) is INVISIBLE to offline
trace-containment — it lives genuinely in the ONLINE simulation rung. This is what makes the result deep:
a coarser (language) semantics would WRONGLY conclude the algebra distributes. -/

/-- The common trace language of both sides from `σ0` (prefix-closed, since `runs` admits `nil` at every
node): the empty trace, `R`'s output `[0]`, and the two full runs `[0,1]` / `[0,2]`. -/
def commonLang : Set Trace := {[], [0], [0, 1], [0, 2]}

/-- THE LATE side recognizes exactly `commonLang` from `σ0`. -/
theorem late_lang : lang ((Pf ⊔ᶠ Qf) ⋆ᶠ Rr) σ0 = commonLang := by
  apply Set.eq_of_subset_of_subset
  · -- every late run is one of the four. Invert step-by-step.
    intro t ht
    rcases ht with _ | ⟨h0, hr⟩
    · left; rfl   -- nil
    · -- first move from the late start is R's 0-move (early_step0 shape) landing in seqp (P⊔Q) done σ1.
      cases h0 with
      | seqR _ _ r' _ σ'' _ hr0 =>
        obtain ⟨hℓ, hd⟩ := Rr_step_inv hr0
        subst hℓ
        rw [Prod.mk.injEq] at hd; obtain ⟨hr', hσ''⟩ := hd; subst hr'; subst hσ''
        -- now at (seqp (P⊔Q) done, σ1); the tail run hr : runs (seqp (P⊔Q) done) σ1 t'.
        rcases hr with _ | ⟨h1, hr1⟩
        · right; left; rfl   -- [0]
        · -- the second move is the hand-off firing 1 or 2 into done.
          cases h1 with
          | seqR _ _ r'' _ _ _ hbadr => cases hbadr   -- right factor `done` has no move
          | seqDone _ p' _ σ''' _ hp =>
            cases hp with
            | chL _ _ p'' _ _ _ hpp =>
              obtain ⟨hℓ1, hd1⟩ := Pf_step_inv hpp; subst hℓ1
              rw [Prod.mk.injEq] at hd1; obtain ⟨hp'', hσ'''⟩ := hd1; subst hp''; subst hσ'''
              rcases hr1 with _ | ⟨hbad, _⟩
              · right; right; left; rfl   -- [0,1]
              · cases hbad   -- done has no move
            | chR _ _ p'' _ _ _ hpp =>
              obtain ⟨hℓ2, hd2⟩ := Qf_step_inv hpp; subst hℓ2
              rw [Prod.mk.injEq] at hd2; obtain ⟨hp'', hσ'''⟩ := hd2; subst hp''; subst hσ'''
              rcases hr1 with _ | ⟨hbad, _⟩
              · right; right; right; rfl   -- [0,2]
              · cases hbad
  · -- each of the four traces is a late run.
    intro t ht
    rcases ht with h | h | h | h
    · subst h; exact runs.nil _ _
    · subst h; exact runs.cons late_step0 (runs.nil _ _)
    · subst h; exact runs.cons late_step0 (runs.cons late_post_has_both.1 (runs.nil _ _))
    · rw [Set.mem_singleton_iff] at h; subst h
      exact runs.cons late_step0 (runs.cons late_post_has_both.2 (runs.nil _ _))

/-- THE EARLY side recognizes exactly `commonLang` from `σ0` — the SAME language as the late side. -/
theorem early_lang : lang ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr)) σ0 = commonLang := by
  apply Set.eq_of_subset_of_subset
  · intro t ht
    rcases ht with _ | ⟨h0, hr⟩
    · left; rfl
    · -- the early start's first move is a 0-move committing to P or Q (early_step0_commits).
      have hℓ0 : ∀ {ℓ d}, Step ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr), σ0) ℓ d → ℓ = 0 := by
        intro ℓ d h
        cases h with
        | chL _ _ _ _ _ _ hp => cases hp with | seqR _ _ _ _ _ _ hr0 => exact (Rr_step_inv hr0).1
        | chR _ _ _ _ _ _ hq => cases hq with | seqR _ _ _ _ _ _ hr0 => exact (Rr_step_inv hr0).1
      have := hℓ0 h0; subst this
      rcases early_step0_commits h0 with hc | hc
      · -- committed to P. hc : (committed target) = (seqp Pf done, σ1). Rewrite hr's indices.
        rw [Prod.mk.injEq] at hc; obtain ⟨hp', hσ'⟩ := hc; rw [hp', hσ'] at hr
        rcases hr with _ | ⟨h1, hr1⟩
        · right; left; rfl
        · cases h1 with
          | seqR _ _ r'' _ _ _ hbadr => cases hbadr
          | seqDone _ p' _ _ _ hp =>
            obtain ⟨hℓ1, hd1⟩ := Pf_step_inv hp; subst hℓ1
            rw [Prod.mk.injEq] at hd1; obtain ⟨hp'', hσ''⟩ := hd1; subst hp''; subst hσ''
            rcases hr1 with _ | ⟨hbad, _⟩
            · right; right; left; rfl
            · cases hbad
      · -- committed to Q.
        rw [Prod.mk.injEq] at hc; obtain ⟨hp', hσ'⟩ := hc; rw [hp', hσ'] at hr
        rcases hr with _ | ⟨h1, hr1⟩
        · right; left; rfl
        · cases h1 with
          | seqR _ _ r'' _ _ _ hbadr => cases hbadr
          | seqDone _ p' _ _ _ hp =>
            obtain ⟨hℓ2, hd2⟩ := Qf_step_inv hp; subst hℓ2
            rw [Prod.mk.injEq] at hd2; obtain ⟨hp'', hσ''⟩ := hd2; subst hp''; subst hσ''
            rcases hr1 with _ | ⟨hbad, _⟩
            · right; right; right; rfl
            · cases hbad
  · intro t ht
    -- the early side's two committed branches realize [0,1] and [0,2]; [] and [0] are prefixes.
    have hP0 : Step ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr), σ0) 0 (.seqp Pf .done, σ1) :=
      Step.chL (Pf ⋆ᶠ Rr) (Qf ⋆ᶠ Rr) _ σ0 σ1 0 (Step.seqR Pf Rr .done σ0 σ1 0 (Step.wr 0 fld 1 σ0))
    have hQ0 : Step ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr), σ0) 0 (.seqp Qf .done, σ1) :=
      Step.chR (Pf ⋆ᶠ Rr) (Qf ⋆ᶠ Rr) _ σ0 σ1 0 (Step.seqR Qf Rr .done σ0 σ1 0 (Step.wr 0 fld 1 σ0))
    have hP1 : Step (.seqp Pf .done, σ1) 1 (.done, σ1) :=
      Step.seqDone Pf .done σ1 σ1 1 (Step.emit 1 σ1)
    have hQ2 : Step (.seqp Qf .done, σ1) 2 (.done, σ1) :=
      Step.seqDone Qf .done σ1 σ1 2 (Step.emit 2 σ1)
    rcases ht with h | h | h | h
    · subst h; exact runs.nil _ _
    · subst h; exact runs.cons hP0 (runs.nil _ _)
    · subst h; exact runs.cons hP0 (runs.cons hP1 (runs.nil _ _))
    · rw [Set.mem_singleton_iff] at h; subst h; exact runs.cons hQ0 (runs.cons hQ2 (runs.nil _ _))

/-- **`flow_choice_languages_equal` (the dregg Example 1.1).** The two sides denote the SAME trace
LANGUAGE from `σ0`. So the right-skew (§4) is INVISIBLE to offline trace-containment — exactly Pradic's
Example 1.1 (`(b⋆a) ⊔ (c⋆a)` and `(b⊔c) ⋆ a` share `{ab, ac}`). The separation lives genuinely in the
ONLINE simulation rung; a language semantics would wrongly conclude distributivity. -/
theorem flow_choice_languages_equal :
    lang ((Pf ⊔ᶠ Qf) ⋆ᶠ Rr) σ0 = lang ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr)) σ0 := by
  rw [late_lang, early_lang]

/-! ## §5 — NON-VACUITY (`#guard`-style): the `≤` is NOT vacuous; the right-skew is GENUINE.

A vacuous simulation that holds because the transition graph is DEAD (no moves) would be a BUG. We pin:
the half holds with a WITNESSED non-empty behavior (both sides actually fire letters), and the right-skew
is genuine (the late side really has BOTH post-`R` moves, the early side really commits). -/

/-- NON-VACUITY of the late side: it really runs `[0,1]` AND `[0,2]` (two distinct maximal traces) — the
graph is alive, with a genuine post-`R` branch. -/
theorem late_nonvacuous :
    runs ((Pf ⊔ᶠ Qf) ⋆ᶠ Rr) σ0 [0, 1] ∧ runs ((Pf ⊔ᶠ Qf) ⋆ᶠ Rr) σ0 [0, 2] := by
  refine ⟨runs.cons late_step0 (runs.cons late_post_has_both.1 (runs.nil _ _)),
          runs.cons late_step0 (runs.cons late_post_has_both.2 (runs.nil _ _))⟩

/-- NON-VACUITY of the right-skew: the late side's post-`R` node has BOTH letters live (so the `≰` is not
because a side is dead — it is the genuine branch-timing obstruction). `[0,1] ≠ [0,2]`, so the two runs
are distinct observable behaviors. -/
theorem rightskew_nonvacuous : ([0, 1] : Trace) ≠ [0, 2] := by decide

/-- The HALF is non-vacuous: the early side it certifies really fires (e.g. `[0,1]`), so
`flow_choice_halfdistrib` is not a statement about a dead process. -/
theorem half_nonvacuous : runs ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr)) σ0 [0, 1] := by
  have hP0 : Step ((Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr), σ0) 0 (.seqp Pf .done, σ1) :=
    Step.chL (Pf ⋆ᶠ Rr) (Qf ⋆ᶠ Rr) _ σ0 σ1 0 (Step.seqR Pf Rr .done σ0 σ1 0 (Step.wr 0 fld 1 σ0))
  have hP1 : Step (.seqp Pf .done, σ1) 1 (.done, σ1) :=
    Step.seqDone Pf .done σ1 σ1 1 (Step.emit 1 σ1)
  exact runs.cons hP0 (runs.cons hP1 (runs.nil _ _))

end Counterexample

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  isSim_eq,
  sim_refl,
  isSim_comp,
  sim_trans,
  halfRel_isSim,
  flow_choice_halfdistrib,
  Pf_step_inv,
  Qf_step_inv,
  Rr_step_inv,
  seqPdone_no_2,
  seqQdone_no_1,
  early_step0_commits,
  flow_choice_right_skewed,
  late_lang,
  early_lang,
  flow_choice_languages_equal,
  late_nonvacuous,
  half_nonvacuous
]

end Dregg2.Deos.FlowAlgebra
