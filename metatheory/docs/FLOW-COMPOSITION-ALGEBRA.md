# The flow-composition algebra is right-skewed

A dregg **flow** is a workflow / affordance-flow: a state-threaded, nondeterministic computation built
from atomic affordance fires by three operators — **choice** `⊔` (offer both branches), **sequential
composition** `⋆` (do one flow, then the next on its post-state), and **meet** `⊓` (admit what both
admit). This document records one algebraic fact about that algebra, proved in Lean
(`metatheory/Dregg2/Deos/FlowAlgebra.lean`):

> **Choice does not fully left-distribute over composition.** The half
> `(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R` holds; the converse
> `(P ⊔ Q) ⋆ R ≤ (P ⋆ R) ⊔ (Q ⋆ R)` **fails**.

So dregg's flow algebra is a **right-skewed Kleene algebra with distributive meets** — RSKA_d⊓, the
structure Pradic identifies for the Weihrauch lattice ("The Equational Theory of the Weihrauch Lattice
with (Iterated) Composition", arXiv:2408.14999). The verdict is a named keystone,
`flow_choice_right_skewed`; the half is `flow_choice_halfdistrib`; both are `#assert_all_clean`.

## The order is online simulation, not trace language

The order `≤` on flows is **online step-by-step simulation** (`Flow.Sim`, written `≤ᶠ`), the dregg
analogue of Pradic's simulation game / a Weihrauch reduction. A flow is read as a labelled transition
system over the real cell state (`Dregg2.Exec.Value`): nodes are `(remaining-flow, state)`, edges are
visible letters (the affordance fired, or a stage's observable output). `P ≤ᶠ Q` holds when a relation
matches every letter-move of `P` by a letter-move of `Q`, **step by step, preserving the relation** — so
the simulator commits its choices online, with no lookahead onto which move will be demanded next. It is
a genuine preorder (`sim_refl`, `sim_trans`).

This order is **strictly finer than offline trace language**, and that is what makes the right-skew a
real theorem rather than an arithmetic slip. On the very counterexample that separates the two sides in
simulation, **the trace languages are equal**:

> `flow_choice_languages_equal` — `(P ⊔ Q) ⋆ R` and `(P ⋆ R) ⊔ (Q ⋆ R)` denote the **same** set of
> traces from the witness state.

This is the dregg form of Pradic's Example 1.1: `(b ⋆ a) ⊔ (c ⋆ a)` and `(b ⊔ c) ⋆ a` both recognize the
language `{ab, ac}`, yet the late-branch automaton `(b ⊔ c) ⋆ a` can step-by-step simulate the
early-branch one and **not** conversely. A coarser, language-only semantics would *wrongly* conclude that
the algebra distributes. The skew lives one rung up.

## Why: the right-skew is the algebraic shadow of the reactive rung

Read `⋆` in Pradic's order — `P ⋆ R` runs the **right** factor `R` first, then `P` on `R`'s post-state.
The two sides differ in *when the `P`-vs-`Q` choice is made relative to `R`*:

- In **`(P ⊔ Q) ⋆ R`**, `R` runs first and produces its output; the choice between `P` and `Q` is taken
  **after**, from a single node that still has both continuations live. The choice **reads `R`'s
  output** — this is the **late** branch.
- In **`(P ⋆ R) ⊔ (Q ⋆ R)`**, the choice is the **first** node; it commits **before** `R` runs — the
  **early** branch.

A simulator embedding the late side into the early side must, to match `R`'s move, have **already
committed** its branch — so from its post-`R` node only one continuation survives, and the late side's
other continuation cannot be matched. The obstruction is precisely no-lookahead: the early side must
choose before it learns which continuation `R`'s output will demand.

This is the **algebraic shadow of dregg's reactive rung**. The reactive affordance gate
(`Dregg2.Deos.Reactive`) is a `TransitionGate` whose `link` reads **both** the old and the new state — "a
property of `new` alone can never witness it." That `old + new` read is exactly the late-binding the
counterexample exploits: in `(P ⊔ Q) ⋆ R`, the branch is a reactive gate reading the field `R` wrote.
Pradic states the same obstruction abstractly — *"the second component `f` of a question
`⟨w, f⟩ ∈ dom((P ⊔ Q) ⋆ R)` might decide whether a question should be asked to `P` or `Q` depending on its
input"* — and in dregg that input is the observed post-state. Because the workflow executor **is** a
sequenced reactive fire (`Dregg2.Deos.WorkflowBridge`: a `Protocol.Workflow` step is a `⋆` of gated /
reactive affordances), the skew is a property of the real workflow-flow algebra, not of a toy.

The half-distributivity, by contrast, needs no lookahead: an *early* commitment is a special case of a
*late* one (the late side can always defer to mimic an early choice), so the early behavior embeds. This
is the direction that holds throughout the Weihrauch lattice.

## The meet is distributive (the `_d⊓`)

The denotational meet `⊓` (run-set intersection — the same negotiation meet proved path-independent in
`Dregg2.Deos.ReplayMembrane` §C2) is a genuine `SemilatticeInf` over the offline run-set order
(`flow_meet_semilattice`). The lattice operations `⊔` / `⊓` are well-behaved among themselves; only
`⊔`-over-`⋆` is skewed. This is exactly the `_d⊓` of RSKA_d⊓: distributive meets, right-skewed
composition.

## Placement in Pradic's classification

| structure | `⊔ ⊓` lattice | `⋆` composition | `⊔` over `⋆` |
|---|---|---|---|
| Kleene algebra (KA) | join only | monoid | full left-distributivity |
| **RSKA_d⊓ (dregg flows)** | distributive lattice with `0`, `⊤` | ordered monoid | **right-half only** (`(P⋆R)⊔(Q⋆R) ≤ (P⊔Q)⋆R`) |

dregg's flow algebra lands in the **RSKA_d⊓** row: it is a right-handed Kleene algebra (the right-half
distributivities `a ⋆ (b ⊔ c) ≤ (a⋆b) ⊔ (a⋆c)`, `(a⋆b) ⊓ (a⋆c) ≤ a ⋆ (b⊓c)`, `(a⋆b) ⊓ c ≤ (a⊓c) ⋆ b`
hold, as in Pradic Figure 2) **plus** distributive meets, **minus** the left-distributivity of `⊔` over
`⋆`. The single fact this lane pins is the load-bearing one: that the left-distributivity genuinely
fails, in the online order, on a denotation that is non-vacuous (both sides really fire —
`late_nonvacuous`, `half_nonvacuous`).

## The payoff (a named follow-on, not built here)

The right-skew is the **precondition** of a decision procedure. Pradic's Theorem 1.4 characterizes
`e ≤ f` in RSKA_d⊓ as *"Duplicator wins the simulation game `SG(∅ | {e} ⊢ f)`"* — a Büchi game on a
finite graph, hence **decidable**, with known complexity (PSPACE-hard in general; PTIME on the pointed
Weihrauch fragment; EXPTIME with iterated composition `(−)°` and meets — Figure 1).

For dregg this means: **"does flow / caveat-policy A refine B" is a decidable question.** The ARGUS bar —
*does this protocol evolution refine the spec?* — is a refinement question over exactly this algebra
(flows of gated reactive fires). Once the algebra is known to be RSKA_d⊓, that bar inherits a decision
procedure with a known complexity class, via the Büchi-game characterization. This lane does **not** build
the decision procedure; it establishes, machine-checked, that the algebra is the right-skewed one the
procedure applies to — and pins *why* (the reactive `old + new` read), so the follow-on rests on a proof,
not a hope.

## Where it lives

- `metatheory/Dregg2/Deos/FlowAlgebra.lean` — the module. `Proc` + `Step` (the labelled transition
  semantics over `Value`), `Flow.Sim` / `≤ᶠ` (the online simulation preorder), `flow_choice_halfdistrib`
  (the half), `flow_choice_right_skewed` (the headline), `flow_choice_languages_equal` (the
  language-equality depth), `flow_meet_semilattice` (the distributive meet), and the non-vacuity teeth.
  Wired into `Dregg2/Deos.lean`.
- Anchors it builds on: `Dregg2/Deos/Reactive.lean` (the `TransitionGate` old+new read — the
  late-binding), `Dregg2/Deos/WorkflowBridge.lean` (a workflow step **is** a sequenced reactive `⋆`),
  `Dregg2/Deos/ReplayMembrane.lean` §C2 (the path-independent negotiation meet), `Dregg2/Exec/Value.lean`
  (the threaded record state).
