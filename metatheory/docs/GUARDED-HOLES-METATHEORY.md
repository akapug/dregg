# Guarded Holes — a categorical / metalogical analysis

**Status: design study, not a build.** This document studies ember's "guarded hole" idea for its
bearing on dregg's existing metatheory. Every structural claim is grounded in a named file; where a
claim is a conjecture it is **labelled SPECULATION**. No code is changed by this document, and it does
not assert that any guarded-hole construct is currently proven — only what it *would* instantiate or
require.

## 0. The idea, restated against the code

A **partial turn with holes** already exists, two ways:

- `Dregg2.Exec.ConditionalTurn.ConditionalBatch { nodes, edges }`
  (`Dregg2/Exec/ConditionalTurn.lean:82`) — a DAG of turns plus `edges : List (Nat × Nat)` where
  `(consumer, producer)` is an `EventualRef`: a **hole** the producer fills and the consumer reads.
  The hole's fill-state is the slot environment `Slots : Nat → Bool`
  (`ConditionalTurn.lean:101`), with `Slots.fill` the producer-commit forward step and `Slots.fill_mono`
  the monotonicity of forwarding (`:113`).
- `Dregg2.Spec.Await` (`Dregg2/Spec/Await.lean`) factors the same family into
  `Conditional ⊕ Promise`: the `Promise`/`EventualRef` is the dataflow hole (`Spec/Await.lean:253`),
  the `Conditional` is a third-party guard deferred over a `Height` (`:95`), and `PromiseGraph`
  (`:266`) is the DAG of holes.

The hole-filling is `Await.Op.await` resumed exactly once by the rollback handler
(`Dregg2/Await.lean`): `commit_resumes_once` (`Await.lean:260`) and
`rollback_discards_continuation` (`Await.lean:246`), over the **one-shot / linear** continuation
`OneShot` (`Await.lean:85`). This linearity is load-bearing below.

ember's specific extension: a participant attaches a **predicate to a hole** that a future filler must
**discharge before they may fill that hole a certain way**; multiple parties may accumulate/refine the
guards over the structure's lifetime. The predicate vocabulary already exists:
`Exec.PredAlgebra.Pred` (`Dregg2/Exec/PredAlgebra.lean:127`) — a genuine Boolean algebra over the
transition `(old, new)` with decidable, fail-closed `Pred.eval` (`:190`) — and the
attenuation/caveat layer `Authority.Caveat` (`Dregg2/Authority/Caveat.lean`) with
`attenuate_narrows` (`Caveat.lean:84`).

So a **guarded hole** is the pair

> `(hole : EventualRef/slot)  +  (guard : Pred)`  such that a fill is admissible only when the guard
> is discharged on the fill.

The rest of this document asks: what is that, categorically, and what does it touch?

---

## 1. What IS a guarded hole, categorically?

I evaluate the five candidates the brief names against the actual `Slots`/`EventualRef`/`Pred` code.

### 1a. A refinement / subobject of the slot type — **best fit for the static face.**

`Pred.eval g : Value → Value → Bool` (`PredAlgebra.lean:190`) is a decidable predicate on the
transition `(old, new)`. Its extension `{ (o,n) | g.eval o n = true }` is a **subobject** of the slot's
transition type `Value × Value`. A guard *carves out the admissible fills*: filling the hole "a certain
way" = landing the `new` value inside this subobject. The executor already realizes exactly this as a
**domain restrictor that never mutates**: `predStateStepGuarded` (`PredAlgebra.lean:580`) commits
*exactly* `stateStep`'s post-state when `predCaveatsAdmit` holds and `none` otherwise
(`predStateStepGuarded_eq`, `:591`; `predStateStepGuarded_violation_fails`, `:615`). That "only
restricts the domain, never changes the post-state" property is *precisely* the categorical signature
of a **monomorphism / subobject inclusion** on the fill type, not a general morphism.

Verdict: a guarded hole's **guard** is a subobject of the slot's transition object; the **fill** is a
section that must factor through that subobject (§1b). This is the cleanest and most defensible
identification, and it is already code (`predStateStepGuarded`).

### 1b. A section of a bundle over the predicate's extension — **best fit for the dynamic face.**

The hole itself (an `EventualRef p`) is a request for a value produced later. Filling it is providing
the value; `Slots.fill i` records the production (`ConditionalTurn.lean:107`). Combine with §1a: a
*guarded* fill is a **partial section** of the slot bundle that is *defined only over the guard's
extension* — i.e. a section of the restricted bundle `slot ↾ {guard holds}`. The dependency-soundness
theorems make this faithful: `condTurn_dependency_sound` (`ConditionalTurn.lean:407`) +
`runOrder_fills` (`:333`) prove a consumer never reads an unfilled slot, so the "section" is genuinely
total over the *resolved* sub-DAG and undefined elsewhere. The producer-commit ↔ handler-commit bridge
`forward_is_handler_commit` (`ConditionalTurn.lean:602`) ties the fill to `OneShot.resume` — the
section is *installed once*.

### 1c. A metavariable-with-a-constraint (contextual modal type theory) — **best fit for the metalogic.**

This is the right reading of the *propagation* the brief emphasizes ("a predicate a future participant
must discharge"). A hole is a metavariable; its guard is a constraint that travels with the metavariable
into every future fill-context. In contextual modal type theory (Nanevski–Pfenning–Pientka, *Contextual
Modal Type Theory*, TOCL 2008) a metavariable `u :: (Ψ ⊢ A)` carries its context `Ψ`; the boxed
`□(Ψ ⊢ A)` reading is "`A` derivable in *every* extension of `Ψ`". The guard `g` on a hole is exactly a
`Ψ`-resident obligation: a filler in a future context `Ψ' ⊇ Ψ` may instantiate the metavariable only by
*also* supplying a derivation of `g`. The "discharge before you may fill" is the metavariable
substitution side-condition. See §5 for why this is the load-bearing metalogical identity, and where
the `□` modality is genuine vs. cosmetic.

### 1d. A representable functor restricted by a sieve — **partial fit, the temporal face.**

A sieve on the deadline poset models "fills allowed up to height `d`". The `Conditional`'s deadline gate
(`Spec/Await.lean:136`, `resolve` returns `Resolved` iff the gateway discharged AND `height ≤ deadline`)
is literally a sieve-style cutoff on the `Height` linear order. But this only captures the *temporal*
half of the guard, not the predicate-on-the-fill half. It is a faithful description of `Conditional`,
not of the `Pred`-guard. Use it for the deadline coordinate only.

### 1e. A comma / Kan object — **not a fit; over-reach.** Nothing in `Slots`/`Pred` supplies the
universal-property data a comma or Kan object needs (no functor pair being compared, no left/right
extension). Cataloguing it as such would be manufactured elegance. Reject.

> **Identity (the honest composite).** A guarded hole is a **constrained metavariable** (§1c, the
> metalogic) whose constraint is a **subobject of the slot's transition type** (§1a, already
> `predStateStepGuarded`) and whose fill is a **once-installed partial section** of the slot bundle over
> that subobject (§1b, already `Slots.fill` + `forward_is_handler_commit`), optionally cut by a
> **deadline sieve** (§1d, already `Conditional.resolve`). Three of the four pieces are *already code*;
> only the metavariable-propagation framing (§1c) is new vocabulary over existing objects.

---

## 2. The hyperdoctrine bearing

dregg's `Pred` algebra plausibly *are* fibres of a hyperdoctrine over contexts, and the repo already
builds the hyperdoctrine: `Dregg2.Metatheory.Lawvere` proves the full posetal triple
`∃_f ⊣ f* ⊣ ∀_f` (`Lawvere.lean:112`, `lawvere_triple`), Frobenius (`:134`), Beck–Chevalley (`:175`),
and the Byzantine relational form `∃_R ⊣ ∀_R` (`Lawvere.lean:323`). The base/`Predicate ⊣ Witness`
reading is `Metatheory.Disputation` and `Authority.Predicate` (the registry's `Verify` seam,
`Predicate.lean:99` `registry_sound`).

### 2a. Filling = the `∃ ⊣ Witness` unit at a hole. **Expressible — this one fits cleanly.**

Filling a guarded hole is "providing a witness that the guard holds". The repo's witness-discharge
seam is exactly this: `Discharged ctx w` = `registryVerify … = true` (`Predicate.lean:88`), and
`registry_sound` (`:99`) says an accepted witness *discharges* the predicate. Read through the
hyperdoctrine: the guard `g` is a fibre element (a `Pred` over the fill-context); the fill provides a
point of its extension; that point is the **counit/unit of `∃ ⊣ f*`** localized at the slot — "there
exists a fill in the guard's extension" is `∃` applied to the slot, and supplying the actual fill is
the adjunction witness. The `intent.Fires` definition is literally this existential:
`∃ w, Discharged i.want w` (`Await.lean:325`). So **"discharge before fill" = the existential side of
`Predicate ⊣ Witness` localized at a hole** — and it is already a theorem-bearing seam, not new.

### 2b. Multiparty accumulation of guards = MEET in the fibre. **Expressible — and it is the existing `⋀`.**

When several parties each attach a guard to the same hole, the hole becomes admissible only when *all*
guards hold. That is the **meet** in the predicate fibre. The repo has it two ways that *agree*:
`Token.admits = caveats.all (…)` is the conjunction `⋀` (`Caveat.lean:71`), and
`Pred.allOf` / `Pred.and` is the Boolean meet (`PredAlgebra.lean:197`, `:271`). `attenuate_narrows`
(`Caveat.lean:84`) proves appending a guard can only *shrink* the admissible set — i.e. guard
accumulation is **monotone decreasing in the fibre order**, which is exactly meet behaviour. So
multiparty guard accumulation = `⋀` of fibre elements, and `attenuate_subset` (`Caveat.lean:92`) is the
proof that more guards ⊆ fewer guards.

Is this the "agreement = limit" of the adjunction thesis? **Partially, and the distinction matters.**
The adjunction-thesis verdict (`project-adjunction-thesis-verdict.md`) established: agreement = the
meet/limit `DistKnows = ⋂ ∼_a`, and that meet is a *limit in the fibre*. Guard accumulation is a meet
**in the same fibre poset**, so it is the *same kind of object* as "agreement = limit." But it is **not
the epistemic agreement meet** — guard accumulation is parties *adding constraints to one shared
object*, whereas the epistemic meet is *intersecting agents' knowledge*. They coincide as "meet in a
Heyting/Boolean fibre"; they differ in *what is being met* (constraints-on-a-hole vs.
knowledge-of-agents). Honest statement: guard accumulation **instantiates the fibre-meet structure the
hyperdoctrine already names**, and is the *constraint-side* analogue of the *knowledge-side* "agreement
= limit." Calling them literally the same theorem would be overclaiming.

### 2c. Does it touch the graded `∃ ⊣ q* ⊣ ∀` or the adjudication reflector?

- The **graded `∀_a`** (`Lawvere.lean` Part B, `relForall`) is the box/Knows modality. A guard that says
  "*P* must hold in *all* future fill-contexts" (the `□P` of §1c/§5) is a `∀`-quantification along the
  future-context relation — i.e. it lands in the `∀_R` fibre, the right adjoint. This is the one place a
  guarded hole reaches past the existing *posetal* Set-doctrine into the **relational** Part B box.
  Crucially, Part B already proves the box is well-behaved only up to the relation's structure:
  `relForall_idem_of_preorder` (`Lawvere.lean:411`) gives S4 idempotence for a preorder, and
  `box_box_ne_box` (`:486`) shows it FAILS for a Byzantine (reflexive-non-transitive) relation. **So a
  "holds in all future contexts" guard inherits exactly Part B's caveat:** if the future-fill-context
  relation is a genuine preorder (single-machine, total-order accumulation — see §6) the `□`-guard is
  idempotent and clean; under Byzantine context-confusion it is *not* idempotent, and `□□g ≠ □g` is a
  real failure, not a cosmetic one.
- The **adjudication reflector `R`** (`Disputation.upheld`, `Disputation.lean`) is a *separately built*
  graded reflector, and the verdict warns it does **not** come free from the meet. Guard accumulation is
  meet-side (§2b); adjudicating a *dispute over a guarded fill* (two parties disagree whether a fill
  discharges a guard) would be reflector-side. The honest reading: **guard accumulation does not touch
  the reflector; resolving a contested fill does.** A guarded-hole construct that needs to *decide* a
  contested discharge inherits the reflector's per-regime existence condition — total on the
  witness/certifiable regime (`R_witness`, `Disputation.upheld`), refutable=Arrow on the ballot regime.

### 2d. Expressible vs. needs-extension — the precise line.

**Expressible in the existing posetal hyperdoctrine:** the guard as a fibre `Pred`; filling as the
existential witness (`∃ ⊣ Witness`, §2a); multiparty accumulation as the fibre meet `⋀` (§2b);
attenuation-narrowing as the Heyting residual (`attenuate_narrows`). All of these are *already proven
objects*.

**Requires extension** in two specific places:

1. **Dependent/linear fibres.** The plain Lawvere doctrine has **cartesian (duplicable)** Heyting
   fibres. But a hole-fill consumes a *one-shot* continuation (`OneShot`, `Await.lean:85`;
   `commit_resumes_once`, `:260`) — the fill is a **linear resource**, used exactly once. A guard that
   gates a *resource-bearing* fill therefore lives in a **linear/monoidal fibre**, not a cartesian one.
   The repo *already built the floor for this*: `Dregg2.Metatheory.IndexedMonoidal` welds the Lawvere
   base to **monoidal (linear) fibres** following Shulman's *Framed bicategories and monoidal
   fibrations* and Ponto–Shulman — "the SAME fibration with MONOIDAL fibres" (`IndexedMonoidal.lean`
   header), proving `∃_f ⊣ f* ⊣ ∀_f` on the base *and* each fibre monoidal. **So the extension a
   resource-guarded hole needs is named and partly built — it is the indexed *monoidal* category, the
   linear hyperdoctrine — not a fresh invention.** What is *not* yet built there: the interaction making
   the *guard* (a base/Set-fibre predicate) gate a *fill* (a monoidal-fibre resource) — only the lax
   Frobenius `⊆` half is proved (`IndexedMonoidal.lean` §4), the equality fails non-functionally, mirror
   of `Lawvere.frobenius_le` (`Lawvere.lean:656`).
2. **The future-context box.** "`P` holds in all future fill-contexts" needs the *relational* `∀_R`
   (Part B), with the S4 caveat of §2c. This is *expressible* in Part B but is genuinely the
   relational fibre, not the clean posetal triple.

> A **Dialectica** setting is *not* required by anything in the code. The brief lists it as a candidate;
> I find no obligation that forces it. Guard accumulation is a meet, not a two-player
> witness/counter-witness game, so the Dialectica double-fibration is more machinery than the structure
> pays for. **SPECULATION:** Dialectica *might* become relevant only if one models *contested* fills as
> a verifier/refuter game (the dispute reflector of §2c), where the witness/counter pairing is natural —
> but that is the reflector, already a separate object, and I would not reach for Dialectica before the
> reflector's own per-regime analysis.

---

## 3. The flow-algebra bearing

The partial turn with holes is the **reactive / online** fragment, and the repo proves that fragment is
**right-skewed**: `Dregg2.Deos.FlowAlgebra` shows choice `⊔` does *not* left-distribute over compose `⋆`
in the online simulation order — `flow_choice_halfdistrib` holds (`FlowAlgebra.lean:339`) but
`flow_choice_right_skewed` (`:467`) refutes the converse, with `flow_choice_languages_equal` (`:599`)
showing the separation is invisible to trace language and lives in the online rung (Pradic,
arXiv:2408.14999, RSKA_d⊓).

### 3a. A guarded fill IS a `⋆`-composition gated by a `⊔`-choice on the predicate.

This is the precise structural match. In `FlowAlgebra`, the `R`-atom `Flow.run ℓ f v`
(`FlowAlgebra.lean:223`) *writes a field and emits its output letter*, and the downstream branch reads
that output — "the choice reads `R`'s output" (`FlowAlgebra.lean:29-36`). A **guarded fill is exactly
this shape**: the producer fills the hole (`R` runs, emits its output = the fill value), and *whether
the fill is admissible* is a branch (`⊔`) on the guard `Pred` evaluated against that just-produced value.
The `TransitionGate` reading both `old` and `new` (`FlowAlgebra.lean` anchors) is precisely
`Pred.eval old new` (`PredAlgebra.lean:190`). So:

> guarded-fill `=` `(admit-fill ⊔ reject-fill) ⋆ produce-value`, where the `⊔`-branch reads the value
> `⋆ produce` emitted.

### 3b. Does adding guards respect or break the right-skew? **It SITS on the right-skew, and a guard's
*late binding* is exactly the right-skew's witness.**

The right-skew obstruction is: an *early* commitment (branch before `R` runs) cannot simulate a *late*
commitment (branch after `R`'s output is observed), because the early simulator must commit before it
learns which continuation is demanded — *no lookahead* (`FlowAlgebra.lean:457-466`). A guard on a hole
is **inherently late-binding**: the guard reads the *produced fill value* (`new`), which does not exist
until the producer commits. So a guarded fill is a **late** branch by construction — it lives on the
late side of the right-skew, the `(P ⊔ Q) ⋆ R` side that the early side cannot simulate.

**Consequence (honest, important):** a guarded hole **cannot be soundly compiled to an early branch.**
If an implementation tried to decide hole-admissibility *before* the producer runs (early), it would be
attempting the simulation the right-skew theorem proves *impossible* on reactive data
(`flow_choice_right_skewed`). The guard *must* be evaluated after the fill is produced. This is not a
tension with the right-skew — it is the right-skew *telling the implementation where the guard check
must go*. Guard accumulation (§2b) does not interact with left-distributivity at all: accumulating
guards is meet on the *predicate* (an offline lattice fact — `flow_meet_semilattice`,
`FlowAlgebra.lean:268`, is a genuine `SemilatticeInf`), while the right-skew is about `⊔`-over-`⋆`
*timing*. The two are orthogonal: **meet-accumulation is the `_d⊓` (distributive meet) axis; the
guarded-fill late-branch is the right-skewed `⊔`/`⋆` axis.**

### 3c. Payoff inheritance.

If the guarded-fill flow is RSKA_d⊓ (it is, by 3a/3b sitting inside the proven algebra), then "does this
guarded-flow refine that one?" inherits Pradic's decidable Büchi/SG-game characterization
(`FlowAlgebra.lean:70-77` "the payoff"). This is the ARGUS "refines" bar. **SPECULATION (degree:
plausible, unbuilt):** guard *refinement* — "guard `g'` is at least as strong as `g`" — is just fibre
order (`g' ≤ g`, i.e. `g'.eval ⟹ g.eval`), which is decidable directly (`Pred.eval` is decidable); the
*flow*-level refinement of guarded fills is the part that would route through the Büchi game. The
decidability claim for *guards alone* is immediate; for *guarded flows* it is the named follow-on, not
proved.

---

## 4. The comodel / lens bearing

The dregg4 frame (`project-dregg4-vision.md`) reads the turn as a **guarded comodel of an effect
theory**, the three faces effects/caveats/attestation as the **get/put/guard of a lens**, with
`capExercise = lens composition`. The memory is explicit that this lens/comodel framing is currently
**aspirational/decorative in Lean** (grep-confirmed not built; `project-dregg4-vision.md` "DECORATION"
and "ASPIRATIONAL" paragraphs). I treat it accordingly.

### 4a. A guarded hole = a lens position whose `put` has a precondition. **Fits the frame; not yet code.**

If turn = lens with `(get, put, guard)`, then a **guarded hole is a `put` whose domain is restricted by
its `guard`**. This is *exactly* `predStateStepGuarded` again (`PredAlgebra.lean:580`): the write (`put`
= `stateStep`) is gated by the guard (`predCaveatsAdmit`), committing the same post-state when admitted
(`predStateStepGuarded_eq`, `:591`). So the *executable shadow* of "a lens `put` with a precondition"
already exists — `predStateStepGuarded` IS a guarded `put`. What is not built is the *lens laws*
(get-put / put-put) over it; the dregg4 memory flags `lens/get-put-put` as decoration not yet in Lean.

### 4b. A partial turn = a PARTIAL lens (profunctor / Tambara module). **SPECULATION — structurally
suggestive, unproven.**

A lens with holes is a partial map; the standard categorical home for "lens-with-structure" is a
**profunctor / Tambara module** (Pickering–Gibbons–Wu; Boisseau–Gibbons; Riley, *Categories of Optics*).
A partial turn — a `ConditionalBatch` with unfilled `EventualRef`s — is a profunctor `P(s, a)` that is
only *defined* where the dependency DAG is resolved. The `Slots`/`EventualRef` machinery
(`ConditionalTurn.lean`) is the bookkeeping of *which positions are defined*, and `runOrder_fills`
(`:333`) proves the partial lens becomes total over the resolved sub-DAG. **This is a plausible and
attractive reading**, and the optic/profunctor literature is the right place to look — but **nothing in
the repo builds a profunctor or Tambara structure**, and I will not claim the identification is
established. Label: SPECULATION, well-motivated, would need a `Profunctor`/`Tambara` instance over
`ConditionalBatch` to become real.

### 4c. Multiparty accumulation = lens composition with strengthening preconditions. **Partial fit.**

Lens composition is `capExercise` in the dregg4 frame. If party A's guarded put composes with party B's
guarded put, the *preconditions conjoin* — and conjunction of guards is the meet `⋀` of §2b. So
"composition with strengthening preconditions" = lens-compose where the guard coordinate accumulates by
meet. The meet-accumulation IS code (`Token.admits`/`Pred.allOf`); the *lens composition* carrying it is
the aspirational `capExercise = lens composition`. Honest split: the **guard-meet half is built**; the
**lens-composition half is the dregg4 aspiration**, and the brief's framing is correct *as a target*,
not as a current theorem.

---

## 5. The metalogical core — the logic of guard accumulation

Guarded holes are **proof obligations that propagate to future fillers**. What logic governs the
accumulation?

### 5a. The base logic is the caveat **Heyting/Boolean algebra** — intuitionistic, fail-closed.

`Pred` is a genuine Boolean algebra (`PredAlgebra.lean`: `eval_not_not` `:266`, `deMorgan_and` `:279`,
`deMorgan_or` `:284`), and the caveat layer is the Heyting residual: `attenuate_narrows`
(`Caveat.lean:84`) is the `⇨`-narrowing the header calls "the Heyting residual" (`Caveat.lean:15, 83`).
Guard accumulation is **conjunction** in this algebra (`Pred.allOf`, `Token.admits = ⋀`). Evaluation is
**fail-closed/decidable** (`PredAlgebra.lean:190` and the typed atoms' fail-closed-on-type theorem
`:503`) — an absent or mistyped fill *rejects*. So the logic of "does this fill satisfy the accumulated
guards" is **decidable intuitionistic (in fact Boolean) propositional logic over the transition
atoms**, with the meet for accumulation and the residual for attenuation. This is fully built.

### 5b. The propagation is **contextual-modal `□`** — and the modality is *genuine* iff the future-context
relation is a preorder.

"A guard a *future* participant must discharge" is the necessitation `□g` = "`g` holds in every future
fill-context" (contextual modal type theory, §1c). The repo's box is `relForall` (`Lawvere.lean:315`),
and §2c established the load-bearing fact: `□` is **idempotent / S4-clean** exactly when the
future-context relation is a preorder (`relForall_idem_of_preorder`, `Lawvere.lean:411`) and **breaks**
(`□□g ≠ □g`) on a Byzantine reflexive-non-transitive relation (`box_box_ne_box`, `:486`). Therefore:

> **The logic of guard *propagation* is a modal `□` over the future-fill-context relation, and its
> cleanliness is conditional on that relation's structure** — S4 (a real necessity modality) under
> single-machine/total-order accumulation, sub-S4 (necessitation that does not chain) under Byzantine
> multiparty accumulation. This is not a defect to paper over; it is the same `□`-idempotence boundary
> the hyperdoctrine already proves with teeth.

### 5c. The accumulation also carries a **graded/linear modality** because of one-shot fills.

The fill is a *linear resource* (`OneShot`, used exactly once: `commit_resumes_once` `Await.lean:260` /
`rollback_discards_continuation` `:246`; `one_shot_is_static` `:111`). A guard that gates a
resource-bearing fill therefore lives in a setting where the *fill* is affine even though the *guard*
(a `Pred`) is freely duplicable/Boolean. This is the **linear hyperdoctrine** split the repo's
`IndexedMonoidal` builds: a Boolean predicate base with linear/monoidal fibres
(`IndexedMonoidal.lean` header, Shulman). So the full metalogic is **two-sorted**: a *cartesian Boolean*
guard logic (duplicable constraints, `⋀`-accumulation) gating a *linear/affine* fill logic
(use-once resources). The `Await` one-shot discipline forbids the obvious unsound move (resume-twice =
double-spend, `runtime_guard_is_double_spend` `Await.lean:178`), which is the linear side's teeth.

### 5d. Is it a sheaf/gluing condition? **Yes for the *merge* reading — and it is the I-confluence wall.**

"Partial turns glue iff their guards are compatible" is a sheaf-gluing condition. The repo's gluing /
merge axis is the I-confluent fragment (`project-rhizomatic-dregg-slotting.md`,
`Dregg2/Confluence.lean`: `IConfluent I := ∀ x y, I x → I y → I(x⊔y)`). The crucial, already-proven
caveat: **not every guard glues.** Rhizomatic's monotone (grow-only) predicates I-confluently merge;
dregg's *non-monotone* guards (a balance bound, `Σδ=0`) provably do **not** — "two withdrawals merge to
overdraft" is the keystone counterexample, forcing `nonpairwise_escalation` to consensus
(`project-rhizomatic-dregg-slotting.md`). Therefore:

> **A multiparty guard accumulation glues coordination-free (sheaf-style, merge-by-union) iff every
> accumulated guard is I-confluent (monotone).** A non-monotone guard (capacity, conservation) breaks
> the gluing and forces an ordered/consensus accumulation — which is *exactly* why the receipt chain is
> a `List` (totally ordered) and rhizomatic's delta is a `Set` (order-blind):
> `project-rhizomatic-dregg-slotting.md`'s "I-confluence wall cashed out at the data-structure level."

And this is the connection to the **reflector-failure ≅ Byzantine-non-gluing** novelty
(`project-adjunction-thesis-verdict.md`, residue (2)): a guard-accumulation that *cannot* glue (a bad
coequalizer collapsing admissible≡inadmissible) is the categorical dual of the `H¹≠0` sheaf obstruction.
So the metalogic of guard accumulation **touches the one genuinely novel theorem the adjunction-thesis
work isolated** — not as decoration, but because guard-gluing is exactly a sheaf condition and its
failure is exactly that obstruction.

---

## 6. The honest implications verdict

Mapping each piece to the brief's (a) fits-cleanly / (b) needs-named-extension / (c) reveals-tension.

### (a) Fits cleanly into existing metatheory — instantiates an existing object.

| Guarded-hole piece | Existing object it instantiates | Citation |
|---|---|---|
| Guard as subobject of the fill type | `predStateStepGuarded` (domain restrictor, never mutates) | `PredAlgebra.lean:580, 591, 615` |
| Filling = existential witness | `Predicate ⊣ Witness` seam, `intent.Fires` | `Predicate.lean:99`, `Await.lean:325` |
| Multiparty accumulation = fibre meet `⋀` | `Token.admits`, `Pred.allOf`, `attenuate_narrows` | `Caveat.lean:71,84`, `PredAlgebra.lean:197` |
| Guard logic = Boolean/Heyting, fail-closed | `Pred` Boolean-algebra laws, typed fail-closed | `PredAlgebra.lean:266,279,503` |
| Guarded `put` with precondition (lens get-put-**guard**) | `predStateStepGuarded` (the executable shadow) | `PredAlgebra.lean:580` |
| Hole dependency-soundness (no use-before-fill) | `condTurn_dependency_sound`, `runOrder_fills` | `ConditionalTurn.lean:407,333` |
| Once-installed fill (linearity) | `OneShot`, `commit_resumes_once` | `Await.lean:85,260` |

### (b) Requires a NAMED extension — and the extension is mostly already named/started.

1. **Linear/monoidal fibres for resource-bearing fills** — the *linear hyperdoctrine* / *indexed
   monoidal category* (Shulman; Ponto–Shulman). **Partly built:** `IndexedMonoidal.lean` welds Lawvere
   base + monoidal fibres and proves `∃⊣f*⊣∀` on the base with monoidal fibres. **Not built:** the
   *guard-gates-resource* interaction (only the lax Frobenius `⊆` half exists,
   `IndexedMonoidal.lean` §4 / `Lawvere.frobenius_le` `:656`); making the *guard predicate* (Set fibre)
   gate the *fill resource* (monoidal fibre) as a verified construct is genuinely new work.
2. **The future-context box `□`** — contextual modal type theory (Nanevski–Pfenning–Pientka) realized
   via the relational `∀_R` (`Lawvere.lean:315`). **Expressible in Part B already**, but it is the
   relational fibre with the S4-idempotence boundary, not the clean posetal triple. A "holds in all
   future fills" guard is a real `□`, with the proven caveat that it is S4 only under preorder
   context-accumulation.
3. **The partial-turn-as-profunctor/optic** (§4b) — SPECULATION; no `Profunctor`/`Tambara` instance
   exists. This is the dregg4 aspiration (`capExercise = lens composition`), explicitly flagged
   not-in-Lean.

### (c) Reveals a TENSION with an existing result — two, both *informative* not *blocking*.

1. **The right-skew forbids early guard-checking.** A guard reads the produced fill (`new`), so it is
   *late-binding* by construction (§3b); `flow_choice_right_skewed` (`FlowAlgebra.lean:467`) proves a
   late branch *cannot* be simulated by an early one on reactive data. **Tension:** any implementation
   that tries to decide hole-admissibility before the producer commits is attempting a provably
   impossible simulation. **Resolution:** this is the right-skew *prescribing* where the guard check
   lives (after the fill), not a contradiction — but it is a hard constraint a naive implementation
   would violate.
2. **Non-monotone guards break coordination-free gluing.** Multiparty guard accumulation glues
   sheaf-style only for I-confluent (monotone) guards; a conservation/capacity guard is non-monotone and
   forces ordered/consensus accumulation (§5d, `project-rhizomatic-dregg-slotting.md`,
   `Confluence.lean`). **Tension:** "multiple parties freely accumulate/refine guards over the
   structure's lifetime" is only *coordination-free* on the monotone fragment; the moment a guard is a
   bounded-counter/conservation predicate, accumulation must serialize (the `List`-not-`Set` receipt).
   **Resolution:** the `ConfluenceClassifier` is the existing gate that decides which guard-merges are
   coordination-free vs. must escalate — so the tension is *already diagnosed and routed* by dregg's
   monotonicity split; a guarded-hole construct must run guards through it.

### What would have to be PROVEN to make guarded holes a first-class verified construct.

1. **`guardedFill_sound`** — a guarded fill commits iff (the producer committed) ∧ (the accumulated
   guard `⋀ gᵢ` evaluates true on the produced value). This is `predStateStepGuarded`
   (`PredAlgebra.lean:580`) lifted over `EventualRef`/`Slots`: gate `runOrder`'s slot-fill
   (`ConditionalTurn.lean:171`) by the guard. **Reuses:** `predStateStepGuarded_eq` (`:591`),
   `condTurn_dependency_sound` (`:407`), `forward_is_handler_commit` (`:602`). Mostly assembly of
   existing keystones.
2. **`guardAccumulation_is_meet` + `guardAccumulation_narrows`** — accumulating guards is the fibre
   meet and can only shrink admissibility. **Reuses:** `attenuate_narrows` (`Caveat.lean:84`) and the
   `Pred.allOf` laws verbatim; this is nearly free.
3. **`guardedFill_late_binding` / right-skew placement** — the guard check must read the produced value,
   formalized as: the guarded fill is the late side `(admit ⊔ reject) ⋆ produce`, which by
   `flow_choice_right_skewed` cannot be lowered to an early branch. **Reuses:** `FlowAlgebra` verbatim;
   new content is the embedding of guarded-fill into `Proc`.
4. **`guardGluing_iff_iconfluent`** — multiparty guard accumulation glues coordination-free iff each
   guard is I-confluent; non-monotone guards force escalation. **Reuses:** `Confluence.IConfluent`,
   `nonpairwise_escalation`, `ConfluenceClassifier`. This is the *new theorem with teeth* and the one
   that touches the reflector-failure≅dual-H¹ novelty.
5. **(harder, named extension)** **`resourceGuardedFill` in the indexed-monoidal fibre** — a guard
   (Boolean base fibre) gating a linear fill (monoidal fibre), with the lax interaction law. **Reuses:**
   `IndexedMonoidal.lean`'s welded structure; new content is the guard×resource interaction beyond the
   lax `⊆` half.

---

## 7. Keystones it builds on, and the genuinely-new things it needs

**Existing keystones reused (3–5):**

1. **`predStateStepGuarded` + `_eq` + `_violation_fails`** (`PredAlgebra.lean:580,591,615`) — the
   guard as a domain-restricting `put`; this IS the guarded-fill executor, already proven to lift every
   `stateStep` keystone.
2. **`attenuate_narrows` / `Token.admits = ⋀`** (`Caveat.lean:84,71`) — guard accumulation = fibre meet
   = Heyting narrowing; the multiparty-refinement law is already a theorem.
3. **`condTurn_dependency_sound` + `runOrder_fills` + `forward_is_handler_commit`**
   (`ConditionalTurn.lean:407,333,602`) — holes never read-before-fill; fills install once via the
   one-shot handler. The partial-turn substrate is sound and computable.
4. **The Lawvere hyperdoctrine `∃⊣f*⊣∀` + the relational `∀_R` box with its S4 boundary**
   (`Lawvere.lean:112,323,411,486`) — fill = existential witness; "holds in all future contexts" = the
   `□` modality, with the proven idempotence-iff-preorder caveat.
5. **The right-skew `flow_choice_right_skewed`** (`FlowAlgebra.lean:467`) — places the guard check on
   the late (post-fill) side and inherits the decidable-refinement payoff.

**Genuinely new things needed (1–3):**

1. **`guardGluing_iff_iconfluent`** — the *one new theorem with teeth*: multiparty guard accumulation
   glues coordination-free exactly on the monotone/I-confluent fragment; non-monotone guards
   (conservation, capacity) force serialized/consensus accumulation. This is where guarded holes touch
   the novel **reflector-failure ≅ dual-H¹ Byzantine-non-gluing** result (`adjunction-thesis-verdict`
   residue 2) and the `ConfluenceClassifier` routing. Not a reassembly — genuinely new content.
2. **The resource-guarded fill in the linear/monoidal fibre** — a Boolean guard gating a one-shot
   (linear) fill, the guard×resource interaction in `IndexedMonoidal`. The *floor* is built (Shulman
   indexed-monoidal weld); the *interaction* is new, and only the lax `⊆` half is currently within
   reach.
3. **(SPECULATION, optional) the partial-turn-as-profunctor/optic** — if one wants the dregg4
   `capExercise = lens composition` to be a *theorem* rather than a slogan, a `Profunctor`/`Tambara`
   instance over `ConditionalBatch` would make "partial turn = partial lens" precise. Well-motivated by
   the optics literature; nothing in the repo builds it yet.

**One-line verdict.** A guarded hole is a *constrained metavariable* — a subobject-of-the-fill guard
(already `predStateStepGuarded`) attached to an `EventualRef`, accumulated by fibre-meet (already
`attenuate_narrows`), filled by the existential-witness seam (already `Predicate ⊣ Witness`), checked
*late* by the right-skew's mandate, and propagated by a contextual `□` that is S4-clean only under
preorder accumulation. It **fits the existing metatheory at four of five seams using objects already
proven**, **needs one named extension that is already started** (the linear/monoidal fibre,
`IndexedMonoidal`), and **reveals exactly one genuinely-new theorem worth proving**:
guard-gluing is coordination-free iff the guards are I-confluent — which is where the construct earns
its keep, touching both the conservation boundary and the reflector-failure≅dual-H¹ novelty.
