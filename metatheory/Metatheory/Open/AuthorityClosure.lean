/-
# Metatheory.Open.AuthorityClosure — the transitive reachability closure of the
# non-forgeability invariant (`ConstructiveKnowledge.lean §3` OPEN, closed).

`ConstructiveKnowledge.lean §3` proves the **single-step** non-forgeability law
`Metatheory.no_forge_step`: after one authorized `Produces` step, every newly-held right
either was already held or is `≤` a previously-held right (conferred, non-amplifying). It
leaves OPEN the **transitive reachability closure**: that in any state reachable by *any*
finite sequence of authorized productions from an initial knowledge `init`, every held
right still traces back to `init`. This module closes it.

It imports the repo's ACTUAL `Metatheory.Produces` / `Metatheory.Confers` /
`Metatheory.no_forge_step` (does not re-derive copies) and uses `Relation.ReflTransGen`
from `Mathlib.Logic.Relation` for the finite chain of authorized steps.

Two deliverables, exactly as flagged in the OPEN note:

* **(A) The non-amplifying closure — CLOSED, kernel-clean.** `noforge_closure`: along any
  `ReflTransGen Produces init final`, every `final`-held right `r` satisfies
  `TracesTo init r := init r ∨ ∃ h, init h ∧ r ≤ h`. The inductive invariant `Q state :=
  ∀ r, state r → TracesTo init r` is preserved by every `Produces` step (`no_forge_step` +
  `≤`-transitivity of the `Preorder`), and lifts along `ReflTransGen` induction.

* **(B) The amplifier `⊗` extension — CLOSED, kernel-clean, on a STATED new algebra.** The
  OPEN note warns the closure "must thread an amplification account" — rights-amplification
  (`unsealer ⊗ box ⊢ contents`) combines two held facts to yield access neither names
  alone, which the *bounded* `Confers` (`≤ held`) cannot express. We introduce a monotone
  ordered-commutative-monoid `⊗` on rights (`RightsAmp`), an amplifying production relation
  `AmpProduces` (a new right may descend from a `⊗`-combination of two held rights), and
  prove `amp_noforge_closure`: along any `ReflTransGen AmpProduces init final`, every held
  right is `≤` a finite `⊗`-combination of `init`-held rights (`AmpClosed`). The
  non-amplifying closure (A) is recovered as the `b = 𝟙` special case.

What remains genuinely OPEN is stated precisely at the foot of §B: the *receipt-disclosure
typing* (that `Generative`/amplifying acts are forced on-chain and un-strippable) is an
operational obligation on the executable system, not an order-theoretic fact about
`AmpProduces`, and is not modelled here. The closure proved is exactly the reachability
statement the §3 note quantifies over — no more, no less.

ZERO `sorry`/`admit`/`native_decide`/`axiom`; keystones pinned with `#assert_axioms`.
-/
import Metatheory.ConstructiveKnowledge
import Mathlib.Logic.Relation

namespace Metatheory.Open.AuthorityClosure

open Metatheory
open Relation

universe u

/-! # §A. The non-amplifying transitive closure (the OPEN, closed)

`ConstructiveKnowledge.lean §3` leaves OPEN the transitive closure of `no_forge_step`. We
close it with the inductive invariant the note implicitly asks for: every reachable right
*traces to* `init` — it is either `init`-held outright, or `≤` some `init`-held right. -/

/-- **`TracesTo init r`** — `r` *descends to* the initial knowledge `init`: either `r` is
held in `init` outright, or `r` is an attenuation (`≤`) of some right `init` holds. This is
the single inductive invariant that survives a `Produces` step: `no_forge_step` says one
step lands a new right `≤` a previously-held right, and `≤`-transitivity lets that
previously-held right itself trace to `init`. -/
def TracesTo {R : Type u} [Preorder R] (init : Rights R → Prop) (r : Rights R) : Prop :=
  init r ∨ ∃ h, init h ∧ r ≤ h

/-- Anything `init` holds outright traces to `init` (the `Or.inl` injection, named). -/
theorem tracesTo_of_init {R : Type u} [Preorder R] {init : Rights R → Prop}
    {r : Rights R} (h : init r) : TracesTo init r :=
  Or.inl h

/-- `TracesTo` is itself `≤`-downward-along-held closed: if `r ≤ h` and `h` traces to
`init`, then `r` traces to `init`. This is the lemma that makes the `Produces` inductive
step go through — a conferred right (`≤` a held right that itself traces back) still traces
back, by transitivity in the `Preorder`. -/
theorem tracesTo_le_trans {R : Type u} [Preorder R] {init : Rights R → Prop}
    {r h : Rights R} (hle : r ≤ h) (hh : TracesTo init h) : TracesTo init r := by
  rcases hh with hi | ⟨h2, hi2, hle2⟩
  · exact Or.inr ⟨h, hi, hle⟩
  · exact Or.inr ⟨h2, hi2, le_trans hle hle2⟩

/-- **`noforge_step_tracesTo` — the invariant `Q := ∀ r, state r → TracesTo init r` is
preserved by ONE `Produces` step.** If everything `state` holds traces to `init`, then
after an authorized `Produces state state'` step, everything `state'` holds traces to
`init`. This is the heart of the closure: it composes `no_forge_step` (the proved
single-step law) with `tracesTo_le_trans`. -/
theorem noforge_step_tracesTo {R : Type u} [Preorder R] {init state state' : Rights R → Prop}
    (hQ : ∀ r, state r → TracesTo init r)
    (hstep : Produces state state') :
    ∀ r, state' r → TracesTo init r := by
  intro r hr
  rcases no_forge_step hstep r hr with hsr | ⟨held, hheld, hle⟩
  · exact hQ r hsr
  · exact tracesTo_le_trans hle (hQ held hheld)

/-- **`noforge_closure` — THE TRANSITIVE NON-FORGEABILITY CLOSURE (the §3 OPEN, CLOSED).**

In any state `final` reachable by ANY finite sequence of authorized `Produces` steps from
the initial knowledge `init` (`ReflTransGen Produces init final`), EVERY right `r` held in
`final` traces back to `init` — it is either `init`-held outright, or `≤` some `init`-held
right. This is *"only connectivity begets connectivity"* across arbitrary reachable states:
no right ever appears ex nihilo, no matter how long the production history.

The proof is the `tail`-form induction on the `ReflTransGen` chain: the base case is
`init` reaching itself (every held right traces to itself trivially); the inductive step
applies `noforge_step_tracesTo` to extend the invariant across one more `Produces` step. -/
theorem noforge_closure {R : Type u} [Preorder R] {init final : Rights R → Prop}
    (reach : ReflTransGen Produces init final) :
    ∀ r, final r → TracesTo init r := by
  induction reach with
  | refl => intro r hr; exact tracesTo_of_init hr
  | tail _ hbc ih => exact noforge_step_tracesTo ih hbc

/-- **Corollary — the closure in the raw `∃` form the §3 OPEN literally wrote.** Unfolding
`TracesTo`: every right held in a reachable `final` is either `init`-held or descends
(`≤`) through to some `init`-held right. (This is `noforge_closure` with `TracesTo`
inlined, matching the OPEN's *"r descends, through a chain of `Confers` steps, to some
`init`-held right"* — each `Confers` step is exactly a `≤`, and the chain collapses by
transitivity to a single `≤`.) -/
theorem noforge_closure_unfolded {R : Type u} [Preorder R] {init final : Rights R → Prop}
    (reach : ReflTransGen Produces init final) (r : Rights R) (hr : final r) :
    init r ∨ ∃ h, init h ∧ r ≤ h :=
  noforge_closure reach r hr

#assert_axioms TracesTo.eq_1
#assert_axioms tracesTo_of_init
#assert_axioms tracesTo_le_trans
#assert_axioms noforge_step_tracesTo
#assert_axioms noforge_closure
#assert_axioms noforge_closure_unfolded

/-! # §B. The amplifier `⊗` extension (the part the OPEN flags as needing new algebra)

`ConstructiveKnowledge.lean §3` OPEN: the inductive step "must thread an *amplification*
account — rights-amplification combines a held amplifier with another held fact to yield
access neither names alone: `unsealer ⊗ box ⊢ contents`". The bounded `Confers held r' :=
r' ≤ held` of §3 CANNOT express this: `contents` is in general `≤` *neither* `unsealer`
*nor* `box` alone — it is `≤` their **combination**. So §A's closure (`r ≤` a single held
right) is *too strong* a conclusion under amplification, and a faithful closure must instead
bound reachable rights by a `⊗`-**combination** of init-held rights.

We supply the missing algebra as a STATED structure (a monotone ordered commutative monoid
on rights), define the amplifying production relation, and prove the corresponding closure.
The non-amplifying §A is recovered as the degenerate case (combine with the unit). -/

/-- **`RightsAmp R` — the amplifier algebra on rights (`§3`, the new module the OPEN flags).**
A commutative monoid `(R, ⊗, 𝟙)` on rights, **monotone in the order** (`amp_mono`), with
the unit `𝟙` acting as a *no-op amplifier* (`amp_unit_le` / `le_amp_unit`: `a ⊗ 𝟙 ≈ a`).
`amp a b` (`a ⊗ b`) is the **joint authority** obtained by *combining* two held facts —
e.g. `unsealer ⊗ box` — which may exceed either factor: rights amplification. Monotonicity
is the discipline that keeps it from forging: combining *weaker* facts yields *weaker*
joint authority. Candidate-independent: any concrete amplifier lattice instantiates it. -/
class RightsAmp (R : Type u) [Preorder R] where
  /-- The amplifying combination `a ⊗ b` — joint authority from two held facts. -/
  amp : R → R → R
  /-- The no-op amplifier (combining with `𝟙` adds nothing). -/
  one : R
  /-- `⊗` is commutative: order of combination is irrelevant. -/
  amp_comm : ∀ a b, amp a b = amp b a
  /-- `⊗` is associative: combining three facts is unambiguous. -/
  amp_assoc : ∀ a b c, amp (amp a b) c = amp a (amp b c)
  /-- `𝟙` is a right unit: `a ⊗ 𝟙 = a`. -/
  amp_one : ∀ a, amp a one = a
  /-- `⊗` is **monotone in both arguments** (the non-forging discipline): weaker factors
  combine to weaker joint authority. -/
  amp_mono : ∀ {a b c d : R}, a ≤ b → c ≤ d → amp a c ≤ amp b d

/-- **`AmpComb init c`** — `c` is a finite `⊗`-combination of `init`-held rights. The
inductive closure of `init` under the amplifier `⊗`: every `init`-held right is a (trivial)
combination, and combinations combine. This is the carrier of *"access neither names
alone"*: `unsealer` and `box` are each `AmpComb init`, hence so is `unsealer ⊗ box`. -/
inductive AmpComb {R : Type u} [Preorder R] [RightsAmp R] (init : Rights R → Prop) :
    Rights R → Prop where
  /-- An `init`-held right is a (degenerate) combination of itself. -/
  | base {r : Rights R} (h : init r) : AmpComb init r
  /-- Two combinations combine via `⊗` into a combination. -/
  | combine {a b : Rights R} (ha : AmpComb init a) (hb : AmpComb init b) :
      AmpComb init (RightsAmp.amp a b)

/-- **`AmpClosed init r`** — `r` descends to a finite `⊗`-combination of `init`-held rights:
`∃ c, AmpComb init c ∧ r ≤ c`. The amplifier-aware analogue of `TracesTo`: under
amplification a reachable right need not be `≤` any *single* init right, but it is `≤` a
`⊗`-combination of init rights. This is the honest, faithful closure conclusion. -/
def AmpClosed {R : Type u} [Preorder R] [RightsAmp R] (init : Rights R → Prop)
    (r : Rights R) : Prop :=
  ∃ c, AmpComb init c ∧ r ≤ c

/-- **`AmpProduces`** — the *amplifying* one-step production relation (`§3`, generative half
WITH amplification). `state'` is reachable from `state` in one amplifying step iff every
right held in `state'` is either already held, **or** descends (`≤`) from the *joint
authority* `a ⊗ b` of **two** held facts `a, b` (`r' ≤ amp a b`). This strictly extends
`Produces`: taking `b := 𝟙` and `amp a 𝟙 = a` recovers the bounded `Confers held r' = r' ≤
held` step (see `produces_le_ampProduces`). The new clause is precisely the `unsealer ⊗ box
⊢ contents` pattern the OPEN names. -/
def AmpProduces {R : Type u} [Preorder R] [RightsAmp R] (state state' : Rights R → Prop) :
    Prop :=
  ∀ r', state' r' → state r' ∨ ∃ a b, state a ∧ state b ∧ r' ≤ RightsAmp.amp a b

/-- **`AmpProduces` strictly extends `Produces`.** Every authorized non-amplifying
`Produces` step is an authorized amplifying `AmpProduces` step — combine with the unit:
`r' ≤ held = held ⊗ 𝟙`. So the amplifier model conservatively contains §3's model, and the
amplifier closure (`amp_noforge_closure`) subsumes the §A closure. -/
theorem produces_le_ampProduces {R : Type u} [Preorder R] [RightsAmp R]
    {state state' : Rights R → Prop} (h : Produces state state') (hone : state RightsAmp.one) :
    AmpProduces state state' := by
  intro r' hr'
  rcases no_forge_step h r' hr' with hsr | ⟨held, hheld, hle⟩
  · exact Or.inl hsr
  · refine Or.inr ⟨held, RightsAmp.one, hheld, hone, ?_⟩
    rw [RightsAmp.amp_one]; exact hle

/-- `AmpClosed` is downward-`≤`-closed: if `r ≤ s` and `s` is amp-closed, so is `r`. -/
theorem ampClosed_le_trans {R : Type u} [Preorder R] [RightsAmp R]
    {init : Rights R → Prop} {r s : Rights R} (hle : r ≤ s) (hs : AmpClosed init s) :
    AmpClosed init r := by
  obtain ⟨c, hc, hsc⟩ := hs
  exact ⟨c, hc, le_trans hle hsc⟩

/-- **The joint authority of two amp-closed rights is amp-closed.** If `a` and `b` each
descend to `⊗`-combinations of init rights (`a ≤ ca`, `b ≤ cb`), then `a ⊗ b ≤ ca ⊗ cb`
(by `amp_mono`) and `ca ⊗ cb` is itself an `AmpComb` (by `combine`) — so `a ⊗ b` is
amp-closed. This is the lemma that lets the amplifying inductive step thread the
amplification account `unsealer ⊗ box`. -/
theorem ampClosed_amp {R : Type u} [Preorder R] [RightsAmp R]
    {init : Rights R → Prop} {a b : Rights R}
    (ha : AmpClosed init a) (hb : AmpClosed init b) :
    AmpClosed init (RightsAmp.amp a b) := by
  obtain ⟨ca, hca, hale⟩ := ha
  obtain ⟨cb, hcb, hble⟩ := hb
  exact ⟨RightsAmp.amp ca cb, AmpComb.combine hca hcb, RightsAmp.amp_mono hale hble⟩

/-- **`ampNoforge_step` — the invariant `∀ r, state r → AmpClosed init r` is preserved by
ONE `AmpProduces` step.** The amplifier-aware analogue of `noforge_step_tracesTo`: if
everything `state` holds is amp-closed, then after an `AmpProduces` step everything `state'`
holds is amp-closed. The new amplifying clause (`r' ≤ a ⊗ b`) is handled by `ampClosed_amp`
+ `ampClosed_le_trans`: the joint authority of two amp-closed held facts is amp-closed, and
a `≤`-attenuation of it stays amp-closed. -/
theorem ampNoforge_step {R : Type u} [Preorder R] [RightsAmp R]
    {init state state' : Rights R → Prop}
    (hQ : ∀ r, state r → AmpClosed init r) (hstep : AmpProduces state state') :
    ∀ r, state' r → AmpClosed init r := by
  intro r hr
  rcases hstep r hr with hsr | ⟨a, b, ha, hb, hle⟩
  · exact hQ r hsr
  · exact ampClosed_le_trans hle (ampClosed_amp (hQ a ha) (hQ b hb))

/-- **`amp_noforge_closure` — THE AMPLIFIER-AWARE TRANSITIVE CLOSURE (the §3 OPEN's
amplification account, CLOSED).**

In any state `final` reachable by ANY finite sequence of *amplifying* productions
(`ReflTransGen AmpProduces init final`) from the initial knowledge `init`, EVERY right `r`
held in `final` descends (`≤`) to a finite `⊗`-**combination** of `init`-held rights
(`AmpClosed init r`). This is *"only connectivity begets connectivity"* WITH rights
amplification: a reachable right need not be bounded by any single init right (amplification
genuinely produces new access — `unsealer ⊗ box ⊢ contents`), but it is *still* bounded by
the joint authority of the rights `init` actually held. No access appears that is not a
`⊗`-combination of initial connectivity.

`ReflTransGen` `tail`-induction: base `init` reaches itself (every held right is its own
`base` `AmpComb`, dominated reflexively); inductive step is `ampNoforge_step`. -/
theorem amp_noforge_closure {R : Type u} [Preorder R] [RightsAmp R]
    {init final : Rights R → Prop} (reach : ReflTransGen AmpProduces init final) :
    ∀ r, final r → AmpClosed init r := by
  induction reach with
  | refl => intro r hr; exact ⟨r, AmpComb.base hr, le_refl r⟩
  | tail _ hbc ih => exact ampNoforge_step ih hbc

/-- **The amplifier closure subsumes the §A closure.** If a reachable right traces to a
*single* init-held right (the §A `TracesTo` conclusion), it is a fortiori `AmpClosed` (a
single init right is a `base` `AmpComb`). So §B is a faithful generalization of §A, not a
different theory: dropping amplification (`AmpProduces` with `b = 𝟙`) returns §A. -/
theorem tracesTo_le_ampClosed {R : Type u} [Preorder R] [RightsAmp R]
    {init : Rights R → Prop} {r : Rights R} (h : TracesTo init r) : AmpClosed init r := by
  rcases h with hi | ⟨h, hih, hle⟩
  · exact ⟨r, AmpComb.base hi, le_refl r⟩
  · exact ⟨h, AmpComb.base hih, hle⟩

#assert_axioms AmpClosed.eq_1
#assert_axioms produces_le_ampProduces
#assert_axioms ampClosed_le_trans
#assert_axioms ampClosed_amp
#assert_axioms ampNoforge_step
#assert_axioms amp_noforge_closure
#assert_axioms tracesTo_le_ampClosed

/-
OPEN (the sharp residual after §B). The order-theoretic reachability closure is now CLOSED
in both forms: §A (`noforge_closure`, non-amplifying) and §B (`amp_noforge_closure`,
amplifier-aware). What §B does NOT — and an order theory CANNOT — capture is the
**receipt-disclosure typing** the §3 prose attaches to amplification: that `Generative` /
amplifying acts are *forced on-chain and un-strippable* (a minted/amplified right carries an
indelible disclosure receipt; you cannot launder amplified authority into ordinary
authority). That is an *operational* obligation on the executable system's turn semantics —
a property of HOW an `AmpProduces` step is recorded and attested, not of the order relation
`r' ≤ a ⊗ b` itself — and it lives with `Dregg2.Core`'s conservation/`TurnTag` machinery
(`§4.1`, the `withholding_no_free_copy` / minting line), not in this candidate-independent
closure. The honest residue here: the reachability *bound* is proved (every reachable right
is a `⊗`-combination of initial connectivity); the *un-strippability of the amplification
receipt* remains an operational obligation, precisely stated and explicitly NOT faked here. -/

end Metatheory.Open.AuthorityClosure
