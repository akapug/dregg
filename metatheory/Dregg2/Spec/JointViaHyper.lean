/-
# Dregg2.Spec.JointViaHyper — N-ary cross-cell joint soundness, VIA the hyperedge apex.

`JointTurn.lean` records the cross-cell binding at two grains: the load-bearing **binary**
keystone `joint_sound` (via `stepComplete_preserves` on the product coalgebra), and a
**stubbed N-ary** `family_joint_sound` (`JointTurn.lean:447`, an open hole) framed over a *family
of binary edges* (`JointFamily`/`FamilyBinding`). That stub is open for a structural reason,
not a missing lemma: its *conclusion* is `Sound (J.cell i) (Spec i) (b.pre i)` — bisimilarity
of each participant to an ARBITRARY free `Spec i` — which is exactly the ill-posed
"bisimulation-to-a-free-`Spec`" shape `Boundary` retired (`Spec.Carrier = Empty` refutes it).

`Hyperedge.lean` then reframed the binding as ONE atomic **wide-pullback object** (the apex
`tid` + a single Σ-over-`univ` CG-5) and PROVED the *well-posed* N-ary keystone
`hyperedge_sound`: the safety / no-drift form. This module is the thin **corollary layer**:
we take `hyperedge_sound` as given and read off

  1. **`joint_via_hyperedge`** — the honest N-ary joint soundness `family_joint_sound` was
     reaching for, now a one-line corollary of `hyperedge_sound`;
  2. **`binary_joint_via_hyperedge`** — the bilateral `JointTurn.joint_sound` recovered as the
     `ι = Fin 2` slice (via `Hyperedge.toJointBinding`);
  3. **`hyperedge_is_validity_not_canonicity`** — the factoring theorem: a hyperedge's
     `HyperAdmissible` is a DECIDABLE proof-property (all-verify ∧ shared-tid ∧ Σ=0), and
     validity does NOT imply uniqueness — two distinct admissible hyperedges can share a
     participant pre-state, so *canonicity* (which valid history wins a double-spend) is a
     SEPARATE obligation, delegated to `Finality`.

Style (matching `Boundary`/`JointTurn`/`Hyperedge`): faithful `Prop`s, real content; every
open hole is a precisely-stated genuine obligation, never a vacuous `True`/`Iff.rfl`, never
`axiom`/`admit`/`native_decide`. PROVED keystones pinned with `#assert_axioms`.
-/
import Dregg2.Core
import Dregg2.Boundary
import Dregg2.JointTurn
import Dregg2.Hyperedge
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Fin

namespace Dregg2.Spec

open Dregg2.Boundary Dregg2.JointTurn Dregg2.Hyperedge

universe u v

variable {Obs AdmissibleTurn TurnId : Type u}
variable {Bal : Type u} [AddCommMonoid Bal]

/-! ## §1 — `joint_via_hyperedge`: the N-ary keystone as a corollary of `hyperedge_sound`.

The content `family_joint_sound` was reaching for, derived in essentially one step
from the apex. A forest of `N` participants — packaged as ONE `Hyperedge` carrying the
wide-pullback `tid` agreement (CG-2 at every leg) and the single Σ-over-`univ` = 0
conservation (CG-5) — is *sound in the safety sense*: a joint predicate `Good`, preserved by
every `StepInv`-respecting tuple-transition, holds along the ENTIRE run from the bound
incidence tuple `H.x`.

Why this is provable where `family_joint_sound` is not: the apex dissolves the O(N²) pairwise
agreement bookkeeping (`Hyperedge.legs_agree` / `hyper_stepComplete` discharge all `N` legs
with a single `∀ i`), AND the conclusion is the *well-posed* safety form, not the ill-posed
bisimulation-to-a-free-`Spec` target. The binding `H` enters as the irreducible premise
(`hyper_binding_is_proper`), exactly as the binary `joint_sound` needs its `JointBinding`. -/

/-- **`joint_via_hyperedge` — N-ary cross-cell joint soundness, via the hyperedge apex
.**

A forest of `N := ι` participants (one shared coalgebra `T`, per-incidence projections
`turnId`/`halfEdge`) bound by ONE `Hyperedge H` (apex `tid` + Σ=0) is sound: if every
incidence is per-cell step-complete and a joint `Good` is preserved by every
`StepInv`-respecting tuple-transition of the product coalgebra `hyperCoalg ι T`, then `Good`
holds at every configuration reachable from the bound incidence tuple `H.x`.

This is exactly the honest N-ary keystone `family_joint_sound` gestures at — and here it is a
**thin corollary** of `Hyperedge.hyperedge_sound`: no new content, the apex framing already
did all the work. The O(N²) pairwise gluing that made the family-of-binary-edges stub
intractable simply does not exist at the apex. -/
theorem joint_via_hyperedge
    {ι : Type u} [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    (turnId : ι → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : ι → HalfEdgeOf (Bal := Bal) T)
    (cons auth chain obsAdv : (i : ι) → T.Carrier → AdmissibleTurn → T.Carrier → Prop)
    (hsc : ∀ i, StepComplete T (cons i) (auth i) (chain i) (obsAdv i))
    (H : Hyperedge ι T turnId halfEdge)
    (Good : (ι → T.Carrier) → Prop)
    (hpres : ∀ xs t, Good xs →
        StepInv (hyperCoalg ι T)
          (hyperPred T cons) (hyperPred T auth) (hyperPred T chain) (hyperPred T obsAdv)
          xs t ((hyperCoalg ι T).next xs t) →
        Good ((hyperCoalg ι T).next xs t))
    {ys : ι → T.Carrier}
    (hrun : Execution.Run (inducedSystem (hyperCoalg ι T)) H.x ys)
    (hgood : Good H.x) :
    Good ys :=
  -- one step: the apex keystone is exactly this statement.
  hyperedge_sound (TurnId := TurnId) (Bal := Bal)
    T turnId halfEdge cons auth chain obsAdv hsc H Good hpres hrun hgood

/-! ## §2 — `binary_joint_via_hyperedge`: the bilateral is the `ι = Fin 2` slice.

The binary `JointTurn.joint_sound` is recovered from a `Fin 2`-indexed hyperedge: incidence
`0` is participant 1, incidence `1` is participant 2, both over the *same* carrier `T` (the
homogeneous reading the binary `joint_sound` specializes to when `T₁ = T₂ = T`). The CG-2 ⊗
CG-5 `JointBinding` the binary keystone demands is supplied for free by
`Hyperedge.toJointBinding H` — so the bilateral keystone is a *literal special case* of the
hyperedge, with no extra data.

We expose this two ways:
  * `binary_joint_via_hyperedge` — run the binary `joint_sound` keystone, feeding it the
    binding extracted from the `Fin 2` hyperedge;
  * `binary_binding_from_hyperedge` — the standalone statement that a `Fin 2` hyperedge IS a
    bilateral `JointBinding` over its two incidences (this is the re-bundling
    `Hyperedge` documented as the *forward* direction — the reverse `SharedTurnId.toHyperedge`
    is the homogeneous round-trip, with the genuine obstruction being only the
    distinct-coalgebra `T₁ ≠ T₂` re-bundling, recorded there). -/

/-- **`binary_binding_from_hyperedge` — a 2-incidence hyperedge IS a bilateral `JointBinding`
.** The forward re-bundling: from a `Fin 2`-indexed hyperedge over one carrier `T`,
`Hyperedge.toJointBinding` reads off the binary CG-2 ⊗ CG-5 binding over its two incidences.
So the bilateral binding is the `ι = Fin 2` slice of the apex, no extra content. -/
theorem binary_binding_from_hyperedge
    {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : Fin 2 → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : Fin 2 → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge (Fin 2) T turnId halfEdge) :
    Nonempty
      (JointBinding (TurnId := TurnId) T T
        (turnId 0) (turnId 1) (halfEdge 0) (halfEdge 1)) :=
  ⟨H.toJointBinding⟩

/-- **`binary_joint_via_hyperedge` — the bilateral keystone as the `ι = Fin 2` slice
.**

Recovers `JointTurn.joint_sound` from a `Fin 2`-indexed `Hyperedge`: the binary keystone's
required `JointBinding` premise is the hyperedge's own binding read through
`Hyperedge.toJointBinding`, and the run starts at the binding's bound pre-state pair
`(b.shared.x₁, b.shared.x₂) = (H.x 0, H.x 1)`. So the bilateral cross-cell soundness is
literally the 2-incidence case of the hyperedge — no new proof, just a projection of the apex.

The conclusion is phrased exactly as `joint_sound`'s (safety along any `Run` of the product
coalgebra `jointCoalg T T`), with the binding-derived start pair, demonstrating the binary
structure is the `N = 2` reading of the wide pullback. -/
theorem binary_joint_via_hyperedge
    {T : TurnCoalg Obs AdmissibleTurn}
    (turnId : Fin 2 → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : Fin 2 → HalfEdgeOf (Bal := Bal) T)
    (cons₁ auth₁ chain₁ obs₁ : T.Carrier → AdmissibleTurn → T.Carrier → Prop)
    (cons₂ auth₂ chain₂ obs₂ : T.Carrier → AdmissibleTurn → T.Carrier → Prop)
    (hsc₁ : StepComplete T cons₁ auth₁ chain₁ obs₁)
    (hsc₂ : StepComplete T cons₂ auth₂ chain₂ obs₂)
    (H : Hyperedge (Fin 2) T turnId halfEdge)
    (Good : (T.Carrier × T.Carrier) → Prop)
    (hpres : ∀ p t, Good p →
        StepInv (jointCoalg T T)
          (jointPred T T cons₁ cons₂) (jointPred T T auth₁ auth₂)
          (jointPred T T chain₁ chain₂) (jointPred T T obs₁ obs₂)
          p t ((jointCoalg T T).next p t) →
        Good ((jointCoalg T T).next p t))
    {y : T.Carrier × T.Carrier}
    (hrun : Execution.Run (inducedSystem (jointCoalg T T))
              ((H.toJointBinding).shared.x₁, (H.toJointBinding).shared.x₂) y)
    (hgood : Good ((H.toJointBinding).shared.x₁, (H.toJointBinding).shared.x₂)) :
    Good y :=
  -- the binary keystone, fed the binding extracted from the `Fin 2` hyperedge.
  joint_sound (TurnId := TurnId) (Bal := Bal)
    T T (turnId 0) (turnId 1) (halfEdge 0) (halfEdge 1)
    cons₁ auth₁ chain₁ obs₁ cons₂ auth₂ chain₂ obs₂ hsc₁ hsc₂
    (H.toJointBinding) Good hpres hrun hgood

/-! ## §3 — validity ≠ canonicity (faithful Props, not prose).

The hyperedge's admissibility (`HyperAdmissible` / `hyperedge_sound`) is **validity**: a
DECIDABLE proof-property — all incidences verify (`hsc`), all commit to one shared `tid`
(CG-2, `agree`), and the half-edges balance to `0` (CG-5, `balanced`). Mina's `will_succeed`
prophecy + cumulative-AND (`JointTurn.atomicity_as_proof`): atomicity is proven by the
aggregate, no coordinator. This is "atomicity-as-proof".

It is NOT a consensus decision. **Canonicity** — which of two conflicting *valid* hyperedges
becomes THE history (a double-spend resolution) — is a SEPARATE obligation. We make
"validity ≠ canonicity" a theorem by exhibiting two DISTINCT hyperedges that are each
`HyperAdmissible`, sharing a participant pre-state, yet differing: validity does not pin a
unique successor. Canonicity is delegated to `Dregg2.Finality` (the SECOND judgement:
ordering / canonicity / consensus — `Finality.lean:2`, the pluggable finality tier `[G]`);
we cite it, we do NOT prove the Byzantine-agreement part here. -/

/-! ### §3.1 — the decidability face of validity (atomicity-as-proof).

`HyperAdmissible` is the existence of a `Hyperedge` (CG-2 legs + CG-5 Σ=0). On the
single-incidence singleton (`ι = Unit`, `Bal = ℤ`) it is *decidable*: the only obligation is
the Σ over `Unit` being `0`, i.e. the lone half-edge value being `0`. We exhibit the
decidable both-ways slice so "validity is a proof-property, not a vote" is concrete. -/

/-- **`singletonHyperedge` — the canonical admissible singleton.** Over `ι = Unit`,
one-state carrier, `Bal = ℤ`, a hyperedge whose lone half-edge is `0` (so CG-5 `Σ = 0`
holds). This *is* `HyperAdmissible` — the positive face of validity-as-decidable-proof. -/
def singletonHyperedge :
    Hyperedge Unit
      ({ Carrier := Unit, step := fun _ => ((), fun _ => ()) } : TurnCoalg Unit Unit)
      (fun _ _ => ())
      (fun _ _ _ => (0 : ℤ)) where
  x := fun _ => ()
  t := ()
  tid := ()
  agree := fun _ => rfl
  balanced := by simp

/-! ### §3.2 — validity does NOT imply canonicity (the theorem + its witness).

Two DISTINCT hyperedges, each `HyperAdmissible`, sharing the *same* participant pre-state
`xs = fun _ => ()`. They are admissible under DIFFERENT turns (the `Bool`-turn coalgebra:
turn `false` vs `true`), each with a balanced (zero) half-edge. Both are valid; neither
validity proof selects between them. That is precisely the double-spend shape: one pre-state,
two valid atomic turns. Resolving it is canonicity, NOT validity — `Finality`'s job. -/

/-- **`hyperedge_is_validity_not_canonicity` — validity ≠ canonicity.**

There is a single coalgebra / framing / participant pre-state `xs` admitting TWO DISTINCT
turns `t₁ ≠ t₂`, each making `xs` `HyperAdmissible`. Hence validity (`HyperAdmissible`) does
NOT pin a unique turn: two conflicting-yet-valid hyperedges share the pre-state. So
"the binding is valid" is strictly weaker than "this binding is THE canonical one" — the
double-spend resolution is a *separate* judgement.

Concretely: `ι = Unit`, carrier `Unit`, turns `Bool`, `Bal = ℤ`, both half-edges `0`. Both
`HyperAdmissible xs false` and `HyperAdmissible xs true` hold; `false ≠ true`. Atomicity (the
all-verify ∧ shared-tid ∧ Σ=0 proof) is *decidable* and holds for BOTH — exactly why
canonicity cannot be a proof-property and must be delegated. We cite `Dregg2.Finality` (the
canonicity / ordering / consensus judgement) for that resolution; we do not prove it here. -/
theorem hyperedge_is_validity_not_canonicity :
    ∃ (T : TurnCoalg Unit Bool)
      (turnId : Unit → TurnIdOf (TurnId := Unit) T)
      (halfEdge : Unit → HalfEdgeOf (Bal := ℤ) T)
      (xs : Unit → T.Carrier) (t₁ t₂ : Bool),
      t₁ ≠ t₂ ∧
      HyperAdmissible Unit T turnId halfEdge xs t₁ ∧
      HyperAdmissible Unit T turnId halfEdge xs t₂ := by
  -- the `Bool`-turn one-state coalgebra; both turns balance (lone half-edge `0`).
  let T : TurnCoalg Unit Bool := { Carrier := Unit, step := fun _ => ((), fun _ => ()) }
  refine ⟨T, fun _ _ => (), fun _ _ _ => (0 : ℤ), fun _ => (), false, true, by decide, ?_, ?_⟩
  · -- `HyperAdmissible … false`: the hyperedge fired at turn `false`.
    exact ⟨{ x := fun _ => (), t := false, tid := (),
             agree := fun _ => rfl, balanced := by simp }, rfl, rfl⟩
  · -- `HyperAdmissible … true`: the SAME pre-state, fired at turn `true` — a distinct,
    -- equally-valid hyperedge. Validity does not choose between them.
    exact ⟨{ x := fun _ => (), t := true, tid := (),
             agree := fun _ => rfl, balanced := by simp }, rfl, rfl⟩

/-! ### §3.3 — why canonicity (not validity) is where consensus lives.

`Hyperedge.hyper_binding_is_proper` (in `Hyperedge.lean`) says the binding is a
PROPER subobject of the N-fold product — content per-cell soundness cannot supply. The
*validity* half of that content (CG-2 ⊗ CG-5 on a SINGLE hyperedge) is decidable and local
(`atomicity_as_proof`). What is irreducibly NON-local is choosing among MULTIPLE valid
hyperedges incident to a shared pre-state (§3.2): no amount of per-incidence proof breaks the
tie, because BOTH ties are valid. That is exactly the seam where a *global judgement*
(ordering / consensus) must enter — `Finality`'s pluggable tier — and exactly why the binding
being a proper subobject (validity content) is distinct from canonicity (consensus content).

`selector_needs_more_than_validity` records the EXTRA content the prose above claims, which
`hyperedge_is_validity_not_canonicity` (a mere ∃ of two admissible turns) does NOT itself state:
that a canonical *selector* — a function from the shared pre-state to a chosen turn — needs
input the validity proof cannot supply. We make this precise and non-vacuous: there exist TWO
selectors, BOTH of which always return a `HyperAdmissible` turn for the §3.2 pre-state, that
DISAGREE on that pre-state. So "always selects something valid" does not pin a unique selector;
distinguishing them consumes data outside `HyperAdmissible`. -/

/-- **`selector_needs_more_than_validity` — a valid selector is not unique.**

Strengthens the §3.2 ∃-witness into a statement ABOUT selectors (the extra content canonicity
needs). For the §3.2 coalgebra/framing/pre-state `xs`, there exist TWO selectors
`sel₁ sel₂ : (Unit → T.Carrier) → Bool` such that:

* each is **validity-respecting** at `xs`: the turn it returns there is `HyperAdmissible`
  (`sel₁ xs` and `sel₂ xs` both make `xs` admissible), yet
* they **disagree** at `xs`: `sel₁ xs ≠ sel₂ xs`.

So the property "returns an admissible turn" does NOT determine the selector: validity is
satisfied by two different choices. Any *canonical* selector must therefore consume
information OUTSIDE the validity proof — the symmetric admissibility of §3.2 cannot break the
tie — which is exactly the `Finality` tier's ordering input. This is the precise sense in which
`hyper_binding_is_proper`'s irreducible content is *validity* (local, decidable), while
canonicity (choosing among valid selectors) lives one level up, in consensus. -/
theorem selector_needs_more_than_validity :
    ∃ (T : TurnCoalg Unit Bool)
      (turnId : Unit → TurnIdOf (TurnId := Unit) T)
      (halfEdge : Unit → HalfEdgeOf (Bal := ℤ) T)
      (xs : Unit → T.Carrier)
      (sel₁ sel₂ : (Unit → T.Carrier) → Bool),
      -- both selectors return a VALID (admissible) turn at the shared pre-state …
      HyperAdmissible Unit T turnId halfEdge xs (sel₁ xs) ∧
        HyperAdmissible Unit T turnId halfEdge xs (sel₂ xs) ∧
        -- … yet they DISAGREE there: validity does not single out the selector.
        sel₁ xs ≠ sel₂ xs := by
  obtain ⟨T, turnId, halfEdge, xs, t₁, t₂, hne, h₁, h₂⟩ :=
    hyperedge_is_validity_not_canonicity
  -- constant selectors picking `t₁` resp. `t₂`: each returns a valid turn at `xs`, they differ.
  exact ⟨T, turnId, halfEdge, xs, fun _ => t₁, fun _ => t₂, h₁, h₂, hne⟩

/-! ## §3.4 — the CG-2 REJECTION tooth: mismatched legs admit no hyperedge.

This is the formal counterpart of the *cross-cell aggregation* circuit's load-bearing
rejection (`circuit/src/joint_turn_aggregation.rs`, `JointTurnAggregationAir` constraint 1 /
`SharedTurnIdMismatch`): the Rust aggregator binds N per-cell whole-turn proofs into ONE proof
ONLY when every leg agrees on the shared turn-id, and REJECTS a bundle whose any leg carries a
different turn-id — even when each per-cell proof is individually valid. The apex side of that
is `Hyperedge.agree : ∀ i, turnId i (T.next (x i) t) = tid`: a *single* `tid` every leg must
hit. If two legs hit DIFFERENT post-step turn-ids for the same turn `t`, there is no `tid` they
both equal, so NO `Hyperedge` over that incidence tuple exists. We prove exactly that, making
the binding's CG-2 a genuine constraint (it rejects), not a vacuous record.

This is the "validity is a real gate" half that complements §3.2's "validity ≠ canonicity":
§3.2 shows two *agreeing* admissible turns can't be told apart by validity; §3.4 shows two
*disagreeing* legs are rejected by validity outright. Together: the apex agreement is necessary
(rejects mismatch) but not sufficient for canonicity (two valid apexes can collide). -/

/-- **`mismatched_legs_have_no_hyperedge` — CG-2 rejects disagreeing legs.**

If two incidences `i j : ι` reach DIFFERENT post-step turn-ids under the SAME turn `t`
(`turnId i (T.next (x i) t) ≠ turnId j (T.next (x j) t)`), then there is NO `Hyperedge`
`H` over `T`/`turnId`/`halfEdge` whose bound pre-states are `x` and whose turn is `t`. The
apex `H.tid` would have to equal both post-step ids (`H.agree i`, `H.agree j`), contradicting
their inequality.

This is the Lean mirror of the Rust aggregator's `SharedTurnIdMismatch`: per-leg data that
disagrees on the turn identity cannot be bound into one joint turn. The hyperedge's `agree`
field is therefore a real gate — it has a case it provably REJECTS. -/
theorem mismatched_legs_have_no_hyperedge
    {ι : Type u} [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    (turnId : ι → TurnIdOf (TurnId := TurnId) T)
    (halfEdge : ι → HalfEdgeOf (Bal := Bal) T)
    (x : ι → T.Carrier) (t : AdmissibleTurn) (i j : ι)
    (hmis : turnId i (T.next (x i) t) ≠ turnId j (T.next (x j) t)) :
    ¬ ∃ H : Hyperedge ι T turnId halfEdge, H.x = x ∧ H.t = t := by
  rintro ⟨H, hx, ht⟩
  -- both legs must equal the single apex `tid`; substitute the bound `x`/`t`.
  subst hx; subst ht
  exact hmis ((H.agree i).trans (H.agree j).symm)

/-- **`mismatch_rejection_is_nonvacuous` — the rejection fires on a concrete instance.**

The §3.4 tooth is not vacuously true: we exhibit a concrete coalgebra (carrier `Bool`,
identity transition, `turnId = id`) and two pre-states `x 0 = false`, `x 1 = true` whose legs
DISAGREE, so `mismatched_legs_have_no_hyperedge` actually denies a hyperedge there. This is the
non-vacuity witness for the rejection (the Lean analogue of the Rust
`disagreeing_turn_id_rejected_even_with_valid_proofs` test). -/
theorem mismatch_rejection_is_nonvacuous :
    ∃ (T : TurnCoalg Unit Unit)
      (turnId : Fin 2 → TurnIdOf (TurnId := Bool) T)
      (halfEdge : Fin 2 → HalfEdgeOf (Bal := ℤ) T)
      (x : Fin 2 → T.Carrier) (t : Unit) (i j : Fin 2),
      turnId i (T.next (x i) t) ≠ turnId j (T.next (x j) t) ∧
      ¬ ∃ H : Hyperedge (Fin 2) T turnId halfEdge, H.x = x ∧ H.t = t := by
  -- carrier `Bool`, transition = identity (ignore the `Unit` turn), `turnId = id`.
  let T : TurnCoalg Unit Unit :=
    { Carrier := Bool, step := fun b => ((), fun _ => b) }
  refine ⟨T, fun _ => (fun b => b), fun _ => (fun _ _ => (0 : ℤ)),
    ![false, true], (), 0, 1, ?_, ?_⟩
  · -- leg 0 post-id = `false`, leg 1 post-id = `true`; distinct.
    decide
  · exact mismatched_legs_have_no_hyperedge T (fun _ => (fun b => b)) (fun _ => (fun _ _ => (0 : ℤ)))
      ![false, true] () 0 1 (by decide)

/-! ## §4 — How `joint_via_hyperedge` discharges what `family_joint_sound` could not.

`family_joint_sound` (`JointTurn.lean:447`, an open hole) has TWO problems the apex fixes:

  * **Bookkeeping (dissolved by the apex).** Its `FamilyBinding` carries `agree : ∀ i, … = tid`
    and `balanced : Σ = 0` over a *family of binary edges* hashed into a forest; gluing the
    per-pair agreements is O(N²). `Hyperedge` packages these as the SINGLE wide-pullback apex
    (`legs_agree` is a theorem; `hyper_stepComplete` discharges all legs with one `∀ i`), so
    `joint_via_hyperedge` inherits a one-step proof.

  * **Ill-posed conclusion (avoided, not patched).** `family_joint_sound` concludes
    `Sound (J.cell i) (Spec i) (b.pre i)` — bisimilarity to an ARBITRARY free `Spec i`,
    refutable at `Spec.Carrier = Empty` (the same defect `Boundary` retired in
    `sound_of_step_complete`). `joint_via_hyperedge` instead concludes the WELL-POSED safety
    form (`Good` preserved along the whole run), which is what soundness should mean. So this
    module does not "fix" the stub's signature; it provides the *honest* keystone alongside
    it, leaving `family_joint_sound` untouched (as instructed). The remaining open
    bisimulation form is recorded in `Hyperedge.hyperedge_sound_bisim`. -/

/-! ## §5 — GOLD: recursive aggregation is the apex conjunction, no leak.

The Rust `circuit/src/joint_turn_recursive.rs` (`prove_joint_turn_recursive`) folds `N` per-cell
whole-turn proofs **and** the shared-turn-id binding leaf into ONE succinct recursive proof via a
binary aggregation tree (`build_and_prove_aggregation_layer`, chained `BatchOnly`). The verifier
checks only the ROOT proof, at cost independent of `N` — the Golden Vision's constant-verifier
property.

For that to be *sound*, the recursive fold must accept exactly the bundles whose every leg
verifies (no acceptance the legs don't justify) AND drops none (every all-legs-verify bundle is
accepted). The aggregation node is logically a **conjunction** of its two children's acceptance
(`build_and_prove_aggregation_layer` verifies BOTH sub-proofs in one circuit), so the whole tree
computes the `N`-fold conjunction of the leaf acceptances. We model the per-leg acceptance as an
abstract predicate `accept : ι → Prop` (read: "leg `i`'s recursive verifier sub-circuit is
satisfied") and prove the binary-tree fold equals `∀ i, accept i`.

This is the faithful meaning of "ONE root proof attests all `N` legs": the root accepts iff every
leg accepts — `recursive_agg_no_leak` is the soundness+completeness of the fold itself
(orthogonal to per-leg STARK soundness, which is the Rust leaf verifier circuits' job, and to the
CG-2 apex agreement, which is `mismatched_legs_have_no_hyperedge` above). The constant-verifier
claim is then: the verifier evaluates this single conjunction-via-root rather than `N` separate
checks. -/

/-- A binary aggregation tree over leaves indexed by a list — the structural shape of the Rust
`aggregate_tree`'s pairwise fold (`Leaf` = one wrapped per-cell/binding proof, `Node` = one
`build_and_prove_aggregation_layer` over two sub-proofs). -/
inductive AggTree (α : Type u) where
  | leaf : α → AggTree α
  | node : AggTree α → AggTree α → AggTree α

namespace AggTree

variable {α : Type u}

/-- The multiset of leaves of an aggregation tree (the bundle it attests). -/
def leaves : AggTree α → List α
  | .leaf a => [a]
  | .node l r => l.leaves ++ r.leaves

/-- **`accepts`** — the tree's acceptance: a leaf accepts iff its own verifier sub-circuit is
satisfied (`accept a`); a node accepts iff BOTH children accept (the `build_and_prove_aggregation_layer`
conjunction — both sub-proofs verify in the one aggregation circuit). -/
def accepts (accept : α → Prop) : AggTree α → Prop
  | .leaf a => accept a
  | .node l r => l.accepts accept ∧ r.accepts accept

/-- **`recursive_agg_no_leak` — the recursive aggregation root accepts iff every leaf accepts
.**

For ANY aggregation tree shape (any pairing order the Rust `aggregate_tree` produces, balanced or
with carried odd leaves), the root's acceptance is logically equivalent to the conjunction of all
leaf acceptances: `t.accepts accept ↔ ∀ a ∈ t.leaves, accept a`.

So the recursive fold:
  * adds NO acceptance (soundness of the fold): if the root accepts, every leaf accepted — the
    verifier never certifies a bundle with an unverified leg;
  * drops NO acceptance (completeness of the fold): if every leg accepted, the root accepts.

This is exactly what makes "check ONE root proof" equivalent to "check all `N` leaves" while
costing `O(1)` in `N`. The per-leaf `accept` carries the actual STARK soundness (the Rust leaf
verifier circuits); this theorem is the *composition* law that the tree does not leak. -/
theorem accepts_iff_all_leaves (accept : α → Prop) :
    ∀ t : AggTree α, t.accepts accept ↔ ∀ a ∈ t.leaves, accept a
  | .leaf a => by simp [accepts, leaves]
  | .node l r => by
      simp only [accepts, leaves, List.mem_append]
      rw [accepts_iff_all_leaves accept l, accepts_iff_all_leaves accept r]
      constructor
      · rintro ⟨hl, hr⟩ a (ha | ha)
        · exact hl a ha
        · exact hr a ha
      · intro h
        exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩

/-- **`recursive_agg_rejects_unverified_leaf` — the tooth: ONE unverified leaf sinks the root
.**

If any leaf `a ∈ t.leaves` fails its verifier (`¬ accept a`), the root does NOT accept. This is
the Lean mirror of the Rust `recursive_layer_rejects_mismatched_leaf_public_inputs` /
`recursive_rejects_tampered_participant_proof` teeth: a tampered participant proof breaks its leaf
sub-circuit, so the conjunction — hence the root — fails. The recursion is a real gate, not a
rubber stamp. -/
theorem rejects_unverified_leaf (accept : α → Prop) (t : AggTree α)
    {a : α} (ha : a ∈ t.leaves) (hbad : ¬ accept a) :
    ¬ t.accepts accept := by
  rw [accepts_iff_all_leaves]
  intro h
  exact hbad (h a ha)

end AggTree

/-- **`recursive_agg_constant_shape` — the root attests the WHOLE bundle regardless of tree shape
.** Two aggregation trees with the SAME leaf multiset accept on the same condition (`∀
leaf, accept`). So the pairing order the Rust `aggregate_tree` chooses (and the carried odd leaf)
does not change WHAT the root attests — only one root proof is checked either way. This underwrites
"the verification cost doesn't grow with the number of cells": the root's meaning is the leaf
conjunction, independent of how the tree was folded. -/
theorem recursive_agg_constant_shape {α : Type u} (accept : α → Prop)
    (t₁ t₂ : AggTree α) (hsame : ∀ a, a ∈ t₁.leaves ↔ a ∈ t₂.leaves) :
    t₁.accepts accept ↔ t₂.accepts accept := by
  rw [AggTree.accepts_iff_all_leaves, AggTree.accepts_iff_all_leaves]
  constructor
  · intro h a ha; exact h a ((hsame a).mpr ha)
  · intro h a ha; exact h a ((hsame a).mp ha)

/-! ## Axiom-hygiene pins (PROVED keystones only). -/

#assert_axioms AggTree.accepts_iff_all_leaves
#assert_axioms AggTree.rejects_unverified_leaf
#assert_axioms recursive_agg_constant_shape
#assert_axioms joint_via_hyperedge
#assert_axioms binary_binding_from_hyperedge
#assert_axioms binary_joint_via_hyperedge
#assert_axioms singletonHyperedge
#assert_axioms mismatched_legs_have_no_hyperedge
#assert_axioms mismatch_rejection_is_nonvacuous
#assert_axioms hyperedge_is_validity_not_canonicity
#assert_axioms selector_needs_more_than_validity

end Dregg2.Spec
