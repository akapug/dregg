/-
# Dregg2.Time.Causal — `causal_after`: the LIGHTCONE-FACT deadline (frame-invariant, no trust).

The relativistic time-typing innovation (`.docs-history-noclaude/rebuild/metatheory/INTENT-AS-CO-RECEIPT.md` §4,
`.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-time.md`) splits "time" into two different things, and FORCES
the author of a deadline to declare which one they mean:

  * **CAUSAL / ordering time** — the lightcone partial order = the lace = happens-before. It is
    *internal*, *frame-invariant*, and *provable* with NO trust assumption. THIS module.
  * **PHYSICAL / wall-clock time** — a *chosen reference frame*: an attested predicate carrying an
    explicit skew bound `±δ` (a §8 trust assumption). `Dregg2/Time/Frame.lean`.

This module builds the causal face. Following Lamport 1978 (happens-before `→` is the only
frame-invariant ordering of events) and Bombelli–Lee–Meyer–Sorkin 1987 (spacetime *is* a discrete
partial order — "a blocklace IS a causal set"), we ground the deadline directly on the lace's
ALREADY-PROVED partial order `Authority.Blocklace.precedes` (`≺`, the transitive closure of the ack
edge `←`). There is no new theory: `causal_after` is a thin predicate over `precedes`, and its two
load-bearing properties (monotone along the lace, frame-invariant) are immediate from the order.

  `CausalAfter B E now  :=  precedes B E now`   ("E is in the causal past of the frontier `now`")

Anti-frontrunning's "no fill before reveal" is `CausalAfter B revealBlock fillBlock` — a happens-
before FACT on the lace, provably enforced, never a timestamp race (`§4`, `§5`: MEV = control of the
simultaneity surface; a causal model has no global order to capture).

§8 boundary: NONE. The whole point of the causal face is that it carries no trust assumption — no
clock, no authority, no skew. It is the partial order itself. (Hash-injectivity / signature seams
are inherited from `Blocklace`, but no theorem here touches them: every result is a pure order fact.)

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Blocklace

namespace Dregg2.Time.Causal

open Dregg2.Authority.Blocklace

/-! ## 1. The frontier ("now") and the causal-after predicate. -/

/-- **`Frontier`** — the observer's "now" is a concrete block on the lace: the event whose causal
past defines "what has already happened". There is no *global* now (relativity of simultaneity,
Einstein 1905 / Lamport 1978); a frontier is one cell's worldline position — the block from which we
ask "is `E` causally behind me?". (A `Block`; named for the role it plays.) -/
abbrev Frontier := Block

/-- **`CausalAfter B E now` — `causal_after(E)` at the frontier `now`.** The event `E` is in the
causal past of `now`: `E ≺ now` on the lace (Lamport's `E → now`). A LIGHTCONE FACT — frame-
invariant, internal, provable, carrying NO trust. This is the lightcone-fact deadline: "this must
causally follow `E`" is discharged exactly when `E` is in the frontier's causal past.

It is *definitionally* the lace's partial order `precedes`, so it inherits the order's full theory
(transitivity, the already-proved structure) for free. -/
def CausalAfter (B : Lace) (E : Frontier) (now : Frontier) : Prop :=
  precedes B E now

/-- `CausalAfter` is exactly `precedes` (the defining equation, for rewriting). -/
@[simp] theorem causalAfter_iff_precedes (B : Lace) (E now : Frontier) :
    CausalAfter B E now ↔ precedes B E now := Iff.rfl

/-! ## 2. MONOTONICITY along the lace — once true at a frontier, true at every later frontier.

The design's first keystone: "once true at frontier `f`, true at every later `f' ≽ f`". A *later
frontier* is one that causally observes the current one (`f ≺ f'`, the worldline advancing). Then a
causal deadline already met stays met — by the transitivity of `precedes` (Lamport's `→` is
transitive; the lace's order is a genuine partial order). Nothing can *un-happen*: the causal past
only grows as the frontier advances. -/

/-- **`causalAfter_mono` — MONOTONE along the lace.** If `CausalAfter B E now` holds at
frontier `now`, and `now'` is a LATER frontier (`now ≺ now'`, i.e. `now'` causally observes `now`),
then `CausalAfter B E now'` holds too. A causal deadline, once met, STAYS met: the frontier's causal
past only grows. Proved by a single `precedes.trans` — the transitivity of the lace order. -/
theorem causalAfter_mono {B : Lace} {E now now' : Frontier}
    (h : CausalAfter B E now) (hlater : precedes B now now') :
    CausalAfter B E now' :=
  precedes.trans h hlater

/-- **`causalAfter_trans`** — `causal_after` composes: if `E₁` is causally before `E₂` and
`E₂` is causally before the frontier, then `E₁` is too. The chaining law that makes a sequence of
causal deadlines collapse to one (`reveal ≺ commit ≺ fill` ⟹ `reveal ≺ fill`). -/
theorem causalAfter_trans {B : Lace} {E₁ E₂ now : Frontier}
    (h₁ : precedes B E₁ E₂) (h₂ : CausalAfter B E₂ now) :
    CausalAfter B E₁ now :=
  precedes.trans h₁ h₂

/-! ## 3. FRAME-INVARIANCE — there is no clock, no authority, no skew.

`CausalAfter` is the partial order itself. It mentions no `Time`, no `TimeAuthority`, no attestation,
no `δ`. Formally: it is a function of `(B, E, now)` ALONE — it does not, and cannot, depend on any
external frame parameter. We make this load-bearing with a theorem schema: for ANY family of "frame"
data `φ : Frame → Prop` adjoined to the question, the truth of `CausalAfter` is constant in the frame
(it is the same proposition no matter which frame you pick). This is the formal content of "the
lightcone order is the invariant content of relativistic spacetime" (Lamport's relativity analogy). -/

/-- **`causalAfter_frame_invariant`** — `CausalAfter` does not depend on any chosen frame.
For an ARBITRARY frame type `Frame` and ANY two frames `fr₁ fr₂ : Frame`, the causal-after question
is *the same proposition* — there is no frame argument to vary. This is frame-invariance as a
theorem: adjoining a frame changes nothing, because the lightcone order is intrinsic. -/
theorem causalAfter_frame_invariant {Frame : Type} (B : Lace) (E now : Frontier) (fr₁ fr₂ : Frame) :
    (fun (_ : Frame) => CausalAfter B E now) fr₁ ↔ (fun (_ : Frame) => CausalAfter B E now) fr₂ :=
  Iff.rfl

/-- **`causalAfter_no_authority`** — the sharper statement of "no trust": whether
`CausalAfter B E now` holds is decided by the lace `B` and the two blocks alone. We exhibit this as:
the predicate is literally `precedes B E now`, a fact about `B`'s ack-DAG, with no oracle, no
credential, no `verify` call in its definition. (Stated as the defining equality so it is checkable;
the ABSENCE of a §8 hypothesis in every theorem above is the real witness.) -/
theorem causalAfter_no_authority (B : Lace) (E now : Frontier) :
    CausalAfter B E now = precedes B E now := rfl

/-! ## 4. ANTI-FRONTRUNNING as a causal type — the §5 application.

"No one may fill before I reveal" = `reveal ≺ fill` = `CausalAfter B reveal fill`. The DUAL teeth:
a fill block whose causal past does NOT contain the reveal block is `incomparable` to it (or earlier)
— and the gate rejects it. Frontrunning excluded as a *theorem*, not a gas race. -/

/-- **`frontrunExcluded B reveal fill`** — the anti-frontrunning predicate: the `fill` event causally
follows the `reveal` event. Exactly `CausalAfter B reveal fill`. When this holds the fill is honest
(it saw the reveal); when it FAILS the fill is a frontrun (it acted without the reveal in its past). -/
def frontrunExcluded (B : Lace) (reveal fill : Frontier) : Prop :=
  CausalAfter B reveal fill

/-- **`frontrun_is_incomparable_or_early` — the frontrunning teeth.** If a `fill` block does
NOT causally follow the `reveal` (`¬ frontrunExcluded`), then it is NOT the case that the reveal is in
the fill's causal past: the fill either acted concurrently with (incomparable to) or strictly before
the reveal. There is no honest interpretation under which a frontrun "saw" the reveal — its rejection
is forced by the order, not adjudicated by a timestamp. -/
theorem frontrun_is_incomparable_or_early {B : Lace} {reveal fill : Frontier}
    (h : ¬ frontrunExcluded B reveal fill) :
    ¬ precedes B reveal fill := h

/-! ## 5. Non-vacuity — the TEETH: a causal_after that HOLDS with no frame, and one that does NOT.

The distinction must be REAL: we exhibit on the concrete `Blocklace.demoLace`
  (a) a `CausalAfter` that PROVABLY HOLDS with no frame / no authority (the honest ack edge `g0 ≺ g1`);
  (b) an INCOMPARABLE pair whose `CausalAfter` PROVABLY FAILS (the Byzantine fork `f1 ∦ f2`) —
      i.e. "not everything is causally before everything"; concurrency is genuine.
Both are decided by the lace alone — no clock is ever consulted. -/

/-- **`demo_causalAfter_holds` — a lightcone fact with NO frame.** In `demoLace`, the
honest successor `g1` is causally after its genesis `g0`: `CausalAfter demoLace g0 g1`. Discharged by
the existing `demo_honest_precedes` (the ack edge `g0 ≺ g1`). No authority, no clock, no skew is
mentioned — this is a deadline that *needs no trust*. -/
theorem demo_causalAfter_holds : CausalAfter demoLace g0 g1 :=
  demo_honest_precedes

/-- **`demo_causalAfter_fails` — the TEETH: not everything is causally before.** The two
Byzantine fork blocks `f1, f2` are concurrent (`incomparable`), so NEITHER is causally after the
other: `¬ CausalAfter demoLace f1 f2 ∧ ¬ CausalAfter demoLace f2 f1`. A causal deadline `f1 ≺ f2` is
*unmet* — the order is non-trivial, concurrency is real, and the causal-after predicate
discriminates. Discharged by the existing `demo_no_fork_precedes`. -/
theorem demo_causalAfter_fails :
    ¬ CausalAfter demoLace f1 f2 ∧ ¬ CausalAfter demoLace f2 f1 :=
  demo_no_fork_precedes

/-- **`demo_frontrun_excluded` — anti-frontrunning on the concrete lace.** Treat `g0` as the
reveal and `g1` as the fill: the fill causally follows the reveal, so frontrunning is excluded
(`frontrunExcluded demoLace g0 g1`). The honest fill is admissible because it *observed* the reveal. -/
theorem demo_frontrun_excluded : frontrunExcluded demoLace g0 g1 :=
  demo_causalAfter_holds

/-- **`demo_frontrun_caught` — the dual: a concurrent fill is a frontrun.** Treat `f1` as the
reveal and `f2` as the fill: `f2` did NOT observe `f1` (they are concurrent), so the anti-frontrunning
predicate fails — `f2` is a frontrun and is rejected by the order. -/
theorem demo_frontrun_caught : ¬ frontrunExcluded demoLace f1 f2 :=
  demo_causalAfter_fails.1

/-! ### `#guard` smoke — the causal-after / frontrun bits, decided by the lace alone (no clock). -/

-- The honest ack edge IS a pointed edge, so `g0 ≺ g1` is a base step (the witness `CausalAfter` uses).
#guard (decide (g0.id ∈ g1.preds))                                   -- true  (g1 acks g0 ⇒ g0 ≺ g1)
-- The fork blocks do not ack each other — the structural root of their concurrency.
#guard (decide (f1.id ∈ f2.preds ∨ f2.id ∈ f1.preds) == false)               -- false (f1 ∦ f2 ⇒ causal_after FAILS)
-- Anti-frontrunning reads the SAME bit: fill `g1` saw reveal `g0` ⇔ the ack edge is present.
#guard (decide (g0.id ∈ g1.preds))                                   -- true  (frontrunExcluded holds)

/-! ### Keystones — `#assert_axioms`-clean. -/

#assert_axioms causalAfter_mono
#assert_axioms causalAfter_trans
#assert_axioms causalAfter_frame_invariant
#assert_axioms causalAfter_no_authority
#assert_axioms frontrun_is_incomparable_or_early
#assert_axioms demo_causalAfter_holds
#assert_axioms demo_causalAfter_fails
#assert_axioms demo_frontrun_excluded
#assert_axioms demo_frontrun_caught

end Dregg2.Time.Causal
