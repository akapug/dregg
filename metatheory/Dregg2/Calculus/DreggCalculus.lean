/-
# Dregg2.Calculus.DreggCalculus — what KIND of runtime dregg is, named as a small calculus.

This module gives the system a FORMAL CALCULUS. It is NOT new heavy proof — it is a thin
PRESENTATION over types and theorems that ALREADY EXIST, naming precisely the shape of the
runtime so the whole thing is "easier to reason about" (the goal of the verb-compression and
coordination-classifier work). Every law here is a POINTER to a landed theorem, or a `def`/`example`
that typechecks; nothing below is an axiom, a `sorry`, or a `:= True`.

## THE CLAIM, in one line

**dregg is a CAPABILITY CALCULUS with ATTESTABLE REDUCTION and COORDINATION-TYPED GUARD MODALITIES.**

Unpacked, against the cited modules:

  1. **A capability calculus.** The term language is cells (≈ processes), capabilities (≈ names /
     channels), and exactly THREE verb shapes — `create · guarded-write · move`
     (`Substrate.VerbCompression.compressed_kernel_three`; the survivor roster
     `Substrate.VerbRegistry.survivors`). The guard algebra is the typing / precondition layer:
     a write commits only past its guard (`Exec.EffectsState.stateStepGuarded`).

  2. **Attestable reduction.** The calculus's reduction relation `→` IS the gated step
     `stateStepGuarded` (`Reduces`, definitionally equal — `reduces_iff_step`). Every reduction
     leaves a RECEIPT: the receipt chain grows by exactly one row per committed step
     (`Exec.EffectsState.state_obsadvance`), so reduction is attestable — `reduces_is_attested`.

  3. **Coordination-typed guard modalities.** Each guard modality (actor / heap / temporal /
     epistemic / order) carries a COORDINATION PRICE — the I-confluence classification of the
     invariant it installs (`Authority.ConfluenceClassifier.guardKeepsConfluence`). The TYPE of a
     guard tells you what consensus it costs: a monotone (grow-only) modality runs coordination-free
     (`modality_price_monotone`, via `monotone_keeps`), a bounded (ceiling) modality forces ordering
     with a CONSTRUCTIVE clashing witness (`modality_price_bounded`, via `bounded_breaks` /
     `nonpairwise_escalation`). This is the novel structural observation, made a theorem.

## What is a PROOF vs. a documented-structural POINTER (honesty ledger)

  * PROVED here (assembled from cited pieces, axiom-clean):
      - `reduces_iff_step`        — reduction IS the gated step (definitional);
      - `reduces_is_attested`     — every reduction emits one receipt row (via `state_obsadvance`);
      - `modality_price_monotone` / `modality_price_bounded` — the modality→price laws (via the
        ConfluenceClassifier), WITH the constructive clashing witness in the bounded case;
      - `dregg_calculus` — THE HEADLINE, the conjunction of the three, over a concrete witness.
  * POINTERS (the correspondence is a theorem ELSEWHERE; cited, re-pinned by `#assert_axioms`):
      - attenuation ≈ scope-restriction-with-non-amplification
        (`Exec.EffectsAuthority.introduce_non_amplifying` + `amplifying_grant_rejected`);
      - the three-verb kernel (`Substrate.VerbCompression.compressed_kernel_three`);
      - the verb roster + minimality (`Substrate.VerbRegistry.minimality`).
  * STRUCTURAL `def`/`example` (typechecks; the correspondence is a naming, not a separate theorem):
      - `Cell` / `Capability` / the verb-shape constructors `CTerm`;
      - the π-calculus correspondence table (`exercise ≈ communication`, `factory ≈ replication`,
        `program ≈ input-guard`) — `Correspondence`, an enumerated `def` with prose.

## Provenance & scope

NEW file. Imports the landed modules it presents over — it INTRODUCES no new lattice, no new step
relation, no new guard atom. The `Reduces` relation is `stateStepGuarded` under a name; the modality
prices are `ConfluenceClassifier.guardKeepsConfluence` under a name. Every theorem
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no `sorry`, no `:= True`,
no `native_decide`.
-/
import Dregg2.Exec.EffectsState
import Dregg2.Exec.EffectsAuthority
import Dregg2.Substrate.VerbRegistry
import Dregg2.Substrate.VerbCompression
import Dregg2.Authority.ConfluenceClassifier
import Dregg2.Tactics

namespace Dregg2.Calculus

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Substrate          -- exposes the `VerbRegistry` and `VerbCompression` namespace prefixes
open Dregg2.Authority.ConfluenceClassifier
open Dregg2.Confluence

/-! ## §1 — THE SYNTAX: cells, capabilities, the three verb shapes, the guard layer.

The term language is a THIN presentation over the existing types. A cell is a process; a capability
is a name/channel (`Exec.EffectsAuthority.ECap`, the real `List Auth` attenuation lattice); the
verbs are the three compressed shapes (`VerbCompression.CVerb` — `create · gwrite · move`,
`compressed_kernel_three`). Nothing here is reinvented: the constructors carry the live types. -/

/-- **A cell ≈ a process.** Identified by its `CellId` (the existing kernel address). The calculus
treats a cell as a located bundle of the four substances (value/authority/evidence/state). -/
abbrev Cell := CellId

/-- **A capability ≈ a name / channel.** The REAL attenuation lattice (`ECap` over `List Auth`):
holding it authorizes exercising it; attenuating it restricts its scope (§3). -/
abbrev Capability := EffectsAuthority.ECap

/-- **The three verb shapes — the calculus's term constructors.** Exactly the compressed kernel
(`VerbCompression.CVerb`): everything else among the live effects dissolves into `gwrite` at a named
guard class (`VerbCompression.cfate`) or is turn-structure (`VerbRegistry.TurnStructure`). A `CTerm`
is one located kernel action; a turn is a list of them (the existing executor's `FullActionA` list). -/
inductive CTerm where
  /-- **create** — mint a new four-substance cell (atomic bundle birth; separated by arity,
  `VerbCompression.create_birth_not_single_write`). -/
  | create (born : Cell)
  /-- **gwrite** — THE guarded write: write field `f` of `target` to `n`, by `actor`, past the
  guard. Five of the seven survivor verbs dissolve into this (`VerbCompression.compressed_kernel_three`).
  Reduction is `Exec.EffectsState.stateStepGuarded`. -/
  | gwrite (actor target : Cell) (f : FieldName) (n : Int)
  /-- **move** — the paired Σδ = 0 exchange (separated from `gwrite` by conservation:
  `VerbCompression.gwrite_conservation_trivializes` + `move_not_single_write`). -/
  | move (src dst : Cell) (amt : Int)
  deriving Repr

/-- The calculus's verb-shape of a term — its image in the compressed kernel `CVerb`. The three
constructors are in bijection with the three compressed verbs (`VerbCompression.compressed_kernel_three`). -/
def CTerm.verb : CTerm → VerbCompression.CVerb
  | .create _       => .create
  | .gwrite _ _ _ _ => .gwrite
  | .move _ _ _     => .move

/-- The calculus's verb set is EXACTLY the three compressed verbs (re-pin of
`VerbCompression.compressed_kernel_three`: the survivor roster collapses to three under the universal
map). The syntax is complete and minimal by that theorem. -/
theorem verbs_are_three :
    ((VerbRegistry.survivors.map
        (fun v => (VerbCompression.cfate v).compressedVerb)).eraseDups).length = 3 :=
  VerbCompression.compressed_kernel_three

/-! ### The guard layer — the typing / precondition.

A `gwrite` commits ONLY past its guard. The guard algebra is stratified (the PROVED tower of
`VerbCompression` §8): the deployed atom families are the typing layer. We name the families as a
MODALITY index (the guard's "type"), each a pointer to its live atom module. The precondition of a
`gwrite` reduction is exactly `Exec.EffectsState.caveatsAdmit` (the slot-caveat gate). -/

/-- **The guard modalities — the "type" of a guard.** Each names a LANDED atom family (the cited
module is the home of its `eval`). The novel §5 claim is that each modality carries a coordination
PRICE; this index is what that price is computed against. -/
inductive GuardModality where
  /-- ACTOR / context atoms — `Exec.Program.SimpleConstraint` (`senderIs`/`balanceGe`/…): the WHO
  and the local-resource guard. -/
  | actor
  /-- HEAP membership atoms — `Substrate.HeapKernel.HeapAtom` (`heapContains`/`heapGetEq`) + the
  absence extension (`VerbCompression.LitAtom.absent`, freshness): the WHERE. -/
  | heap
  /-- TEMPORAL modal atoms — `Authority.TemporalAlgebra.TemporalAtom`
  (`afterHeight`/`withinWindow`/`cooledSince`/…) + the UNTIL/SINCE pair (`TemporalAlgebra2`): the WHEN. -/
  | temporal
  /-- EPISTEMIC atoms — `Authority.Epistemic` (`Knows` K / `EveryoneKnows` E / `DistributedKnows` D /
  `CommonAt` C): the WHO-KNOWS. -/
  | epistemic
  /-- ORDER-RELATIONAL atoms — the rights-order guard `new ⊆ get(k)`
  (`VerbCompression.grantGuard`, non-amplification): the authority production gate. -/
  | order
  deriving DecidableEq, Repr

/-- The landed atom-family module each modality is the calculus-level name of (a `String`, a
cross-reference — the proofs live in the named module). -/
def GuardModality.atomModule : GuardModality → String
  | .actor     => "Dregg2.Exec.Program (SimpleConstraint: senderIs/balanceGe/…)"
  | .heap      => "Dregg2.Substrate.HeapKernel (HeapAtom) + VerbCompression.LitAtom.absent"
  | .temporal  => "Dregg2.Authority.TemporalAlgebra(2) (TemporalAtom / EventAtom)"
  | .epistemic => "Dregg2.Authority.Epistemic (Knows / EveryoneKnows / DistributedKnows / CommonAt)"
  | .order     => "Dregg2.Substrate.VerbCompression.grantGuard (new ⊆ get k)"

theorem guard_modality_modules_nonempty : ∀ m : GuardModality, m.atomModule ≠ "" := by
  intro m; cases m <;> decide

/-! ## §2 — THE REDUCTION RELATION: `→` IS the gated step `stateStepGuarded`.

The calculus's reduction is NOT a new relation. It is `Exec.EffectsState.stateStepGuarded` (the
authority gate ∘ the slot-caveat gate, fail-closed). `Reduces s t s'` says: term `t`'s `gwrite`
shape reduces the chained state `s` to `s'`. We give the relation as a thin wrapper and prove it is
definitionally the existing step (`reduces_iff_step`). -/

/-- **`Reduces s t s'` — the calculus's small-step reduction `s -[t]→ s'`.** For the `gwrite` verb
shape it is EXACTLY `stateStepGuarded` (the gated field write). (The `create` and `move` shapes have
their own existing executor steps — `recKCreateCell`, `moveStep` — pointed to in §3; this relation
presents the workhorse `gwrite`, the shape five survivor verbs share.) -/
def Reduces (s : RecChainedState) (t : CTerm) (s' : RecChainedState) : Prop :=
  match t with
  | .gwrite actor target f n => stateStepGuarded s f actor target n = some s'
  | _ => False

/-- **`reduces_iff_step` — reduction IS the gated step (definitional).** The calculus's `→` on a
`gwrite` term is, by definition, a committed `stateStepGuarded`. No new operational semantics is
introduced — the calculus reads off the executor. -/
theorem reduces_iff_step (s s' : RecChainedState) (actor target : Cell) (f : FieldName) (n : Int) :
    Reduces s (.gwrite actor target f n) s' ↔ stateStepGuarded s f actor target n = some s' :=
  Iff.rfl

/-- **`reduces_admits_guard` — a reduction certifies its guard held.** Every reduction means the
slot-caveat gate ADMITTED the transition at the pre-state (`stateStepGuarded_admits`): the
precondition layer is enforced, by the executor, on every step. -/
theorem reduces_admits_guard {s s' : RecChainedState} {actor target : Cell} {f : FieldName} {n : Int}
    (h : Reduces s (.gwrite actor target f n) s') :
    caveatsAdmit s.kernel f actor target n = true :=
  stateStepGuarded_admits ((reduces_iff_step s s' actor target f n).mp h)

/-- **`reduces_is_attested` — EVERY REDUCTION LEAVES A RECEIPT.** A committed reduction grows the
receipt chain by exactly one row (the monotone, replay-detectable metadata clock —
`Exec.EffectsState.state_obsadvance`, lifted through `stateStepGuarded_eq`). Reduction is
ATTESTABLE: the log is a faithful, append-only witness of the reduction sequence. -/
theorem reduces_is_attested {s s' : RecChainedState} {actor target : Cell} {f : FieldName} {n : Int}
    (h : Reduces s (.gwrite actor target f n) s') :
    s'.log.length = s.log.length + 1 :=
  state_obsadvance (stateStepGuarded_eq ((reduces_iff_step s s' actor target f n).mp h))

/-- **`reduces_writes` — read-after-reduce.** After a reduction writing `n` to slot `f` of
`target`, the slot reads back exactly `n` (`state_field_written`). The reduction's effect is
exactly the guarded field move; the post-state is pinned. -/
theorem reduces_writes {s s' : RecChainedState} {actor target : Cell} {f : FieldName} {n : Int}
    (h : Reduces s (.gwrite actor target f n) s') :
    fieldOf f (s'.kernel.cell target) = n :=
  state_field_written (stateStepGuarded_eq ((reduces_iff_step s s' actor target f n).mp h))

/-- **`reduces_fail_closed` — no reduction past a refused guard.** If any caveat bound to the slot
rejects the transition, there is NO reduction (`stateStepGuarded_caveat_violation_fails`). The
precondition layer is FAIL-CLOSED — the calculus has no escape hatch. -/
theorem reduces_fail_closed (s : RecChainedState) (actor target : Cell) (f : FieldName) (n : Int)
    (h : caveatsAdmit s.kernel f actor target n = false) :
    ∀ s', ¬ Reduces s (.gwrite actor target f n) s' := by
  intro s' hr
  rw [reduces_iff_step] at hr
  rw [stateStepGuarded_caveat_violation_fails s f actor target n h] at hr
  exact absurd hr (by simp)

/-! ## §3 — THE STRUCTURAL CORRESPONDENCES (process-calculus dictionary).

dregg, named against the standard capability / process-calculus vocabulary. Where the correspondence
is ALREADY a theorem, we cite + re-pin it; where it is a structural naming, we state it as a `def` /
`example` that typechecks. We do NOT invent a proof for a naming. -/

/-- **ATTENUATION ≈ scope restriction with NON-AMPLIFICATION** (the enforced scope-extrusion
discipline). This is a THEOREM, not a naming: a conferred capability is a genuine SUBSET of the held
one (`introduce_non_amplifying`), and the discipline has TEETH — a grant conferring authority the
holder lacks is REJECTED (`amplifying_grant_rejected`). Scope can only NARROW as a capability flows;
it never amplifies. (Re-pin of `Calculus.AssuranceCase.authority_guarantee`'s underlying keystones.) -/
theorem attenuation_is_scope_restriction
    (held granted : Capability) (keep : List Authority.Auth) (a : Authority.Auth)
    (hgranted : a ∈ Authority.capAuthConferred granted)
    (hheld : a ∉ Authority.capAuthConferred held) :
    EffectsAuthority.IsNonAmplifying held (attenuate keep held)
      ∧ ¬ EffectsAuthority.IsNonAmplifying held granted :=
  ⟨EffectsAuthority.introduce_non_amplifying held keep,
   EffectsAuthority.amplifying_grant_rejected held granted a hgranted hheld⟩

/-- The π-calculus / process-calculus reading of each non-kernel structural role. A STRUCTURAL
naming (`def`, typechecks) — the correspondence is the vocabulary, the behavior is the cited module.
The arms:
  * `exercise ≈ COMMUNICATION` — exercising a cap from the c-list is the categorical eval map, a
    send/receive along the capability-as-channel (`VerbRegistry.classify .ExerciseViaCapability =
    .turnStructure .exercise`; non-amplification in `EffectsAuthority.exercise_non_amplifying`);
  * `pipelining ≈ ASYNC COMMUNICATION / promise` — eventual/pipelined send is Turn composition;
  * `prologue ≈ replay guard` — the nonce prologue (`IncrementNonce`);
  * `refusal ≈ NEGATIVE OUTCOME` — proof-of-non-action, not a state verb;
  * `receiptLog ≈ OBSERVATION` — emitted into Q, the attestation channel (§2's receipt). -/
def Correspondence : VerbRegistry.TurnStructure → String
  | .exercise   => "communication (send/receive along the capability-as-channel)"
  | .pipelining => "asynchronous communication (promise pipelining; three-party introduction)"
  | .prologue   => "replay-nonce prologue (input freshness)"
  | .refusal    => "refusal outcome (proof of non-action)"
  | .receiptLog => "receipt/observation emission (the attestation channel Q)"

/-- **factories ≈ REPLICATION** (`!P`): a factory re-provides a doomed verb family as a verified,
factory-born cell PROGRAM that can be instantiated repeatedly (`VerbRegistry.FactoryPattern`, each a
landed module). A STRUCTURAL naming — the live enum carries no factory tag
(`VerbRegistry.no_live_factory_tags`); the pattern is the replication operator of the calculus. -/
def factory_is_replication : VerbRegistry.FactoryPattern → String :=
  fun p => "replication: instantiate the verified cell-program " ++ p.module

/-- **programs ≈ INPUT GUARDS** (guarded choice). A cell program is a `Pred` precondition on each
write — the input-guard `g(x).P` of the calculus, enforced by `stateStepGuarded`'s caveat gate. This
is exactly the §1 guard layer; the correspondence is the naming, the enforcement is `caveatsAdmit`.
We witness it as a typechecking `example`: a guarded write under a refusing guard does not reduce. -/
example (s : RecChainedState) (actor target : Cell) (f : FieldName) (n : Int)
    (h : caveatsAdmit s.kernel f actor target n = false) :
    ∀ s', ¬ Reduces s (.gwrite actor target f n) s' :=
  reduces_fail_closed s actor target f n h

/-! ## §4 — THE NOVEL PART: COORDINATION-TYPED GUARD MODALITIES.

THE THESIS: each guard modality carries a COORDINATION PRICE — the I-confluence classification
(`Authority.ConfluenceClassifier`) of the invariant it installs. dregg is "a runtime where the TYPE
of an operation tells you what consensus it COSTS": classify the guard, and you have proved its
finality tier. The classifier + the conflict relation already exist; here we connect a MODALITY to
its price as theorems.

The price of a guard `g` is `guardKeepsConfluence g` (`Confluence.IConfluent (guardInv g)`):
  * TRUE  ⇒ coordination-FREE (tier-1, partition-tolerant, no consensus) — `CoordinationFree g`;
  * FALSE ⇒ forces ORDERING (consensus), WITH a constructive clashing-pair witness — `ForcesOrdering g`.
The dichotomy is `keeps_iff_coordinationFree`. We state ONE law per pole, each a re-pin of the
classifier's own theorem, named at the calculus level. -/

/-- **`modality_price` — the coordination price of a guard.** The calculus-level name for
`ConfluenceClassifier.guardKeepsConfluence`: a guard `g` is CHEAP (runs coordination-free) iff its
installed invariant is I-confluent under the concurrent merge. This is the "type-tells-you-the-cost"
function — the price IS the I-confluence verdict. -/
def modality_price {S : Type _} [MergeState S] (g : Guard S) : Prop :=
  guardKeepsConfluence g

/-- **`modality_price_is_tier` — the price IS the finality tier (the dichotomy).** A guard's price
being "free" is DEFINITIONALLY its cell being tier-1 eligible
(`ConfluenceClassifier.keeps_iff_coordinationFree`). Classifying a modality IS deciding its consensus
cost — the central claim, as an iff. -/
theorem modality_price_is_tier {S : Type _} [MergeState S] (g : Guard S) :
    modality_price g ↔ CoordinationFree g :=
  keeps_iff_coordinationFree g

/-- **`modality_price_monotone` — a MONOTONE (grow-only) modality runs COORDINATION-FREE.** Any
guard whose installed invariant is a grow-only floor over a merge-monotone projection
(`Guard.monotone`, the high-water-mark / sequence-number / evidence-↑ shape — the EVIDENCE and
monotone-TEMPORAL atoms) is I-confluent, hence tier-1: no consensus, partition-tolerant. The price of
the monotone modality is FREE. (Via `ConfluenceClassifier.monotone_keeps_runs_free`.) -/
theorem modality_price_monotone {S : Type _} [MergeState S] (proj : S → ℕ) (c : ℕ)
    (hmono : ∀ x y : S, x ≤ y → proj x ≤ proj y) :
    CoordinationFree (Guard.monotone proj c) :=
  monotone_keeps_runs_free proj c hmono

/-- **`modality_price_bounded` — a BOUNDED (ceiling) modality FORCES ORDERING, with a witness.**
A guard whose invariant is a resource ceiling that two concurrent branches can each respect but
TOGETHER overshoot (`Guard.bounded`, the `balance ≥ 0` / budget / cardinality-bound shape — the
bounded-resource ACTOR atoms) is NOT I-confluent: the cell must serialize (consensus). The price is
reported with a CONSTRUCTIVE clashing pair (`nonpairwise_escalation` via `bounded_forces_ordering`),
never a bare declaration — the system tells the app author WHY their guard is not cheap. -/
theorem modality_price_bounded {S : Type _} [MergeState S] (proj : S → ℕ) (c : ℕ)
    {x y : S} (hx : proj x ≤ c) (hy : proj y ≤ c) (hbad : ¬ proj (x ⊔ y) ≤ c) :
    ForcesOrdering (Guard.bounded proj c) ∧
      ∃ a b : S, guardInv (Guard.bounded proj c) a ∧ guardInv (Guard.bounded proj c) b ∧
        ¬ guardInv (Guard.bounded proj c) (a ⊔ b) :=
  bounded_forces_ordering proj c hx hy hbad

/-- **`modality_price_relational` — a RELATIONAL modality's price is DECIDED BY THE MERGE.** A
cross-slot relational guard (the record-level `Exec.RelationalCaveat` shape) is cheap IFF its relation
survives the pointwise join — there is no syntactic shortcut (`relational_decided_by_merge`). The
verdict is the merge, nothing else. -/
theorem modality_price_relational {S : Type _} [MergeState S] (P : Invariant S) :
    (∀ x y : S, P x → P y → P (x ⊔ y)) ↔ modality_price (Guard.relational P) :=
  relational_decided_by_merge P

/-! ## §5 — THE HEADLINE.

The three faces, assembled over a concrete witness — NOT a new axiom. The statement is the
conjunction:

  (1) the syntax has exactly the three compressed verbs (`verbs_are_three`);
  (2) reduction is the gated step AND is attested by a receipt (`reduces_iff_step` +
      `reduces_is_attested`, over a concrete reduction `hr`);
  (3) a guard modality's price is its finality tier, with both poles inhabited
      (`Witness.markGuard_runs_free` free, `Witness.budgetGuard_forces_ordering` ordered).

So: **dregg is a capability calculus (3 verbs) with attestable reduction (every step a receipt) and
coordination-typed guard modalities (the type is the consensus cost).** -/

/-- **`dregg_calculus` — THE HEADLINE.** For ANY committed `gwrite` reduction `hr : Reduces s t s'`:
the calculus has exactly three verbs, the reduction is the gated step and emits exactly one receipt
row, and the two coordination-price poles are both inhabited (a monotone modality runs free; a
bounded modality forces ordering with a witness). One statement, assembled from the cited theorems —
the precise name of what KIND of runtime dregg is. -/
theorem dregg_calculus
    {s s' : RecChainedState} {actor target : Cell} {f : FieldName} {n : Int}
    (hr : Reduces s (.gwrite actor target f n) s') :
    -- (1) capability calculus: exactly three verb shapes.
    ((VerbRegistry.survivors.map
        (fun v => (VerbCompression.cfate v).compressedVerb)).eraseDups).length = 3
    -- (2) attestable reduction: the reduction IS the gated step, and emits one receipt row.
    ∧ stateStepGuarded s f actor target n = some s'
    ∧ s'.log.length = s.log.length + 1
    -- (3) coordination-typed modalities: the free pole AND the ordering pole are both inhabited.
    ∧ CoordinationFree Witness.markGuard
    ∧ (ForcesOrdering Witness.budgetGuard ∧
        ∃ a b : Confluence.CRDT.Budget,
          guardInv Witness.budgetGuard a ∧ guardInv Witness.budgetGuard b ∧
          ¬ guardInv Witness.budgetGuard (a ⊔ b)) :=
  ⟨verbs_are_three,
   (reduces_iff_step s s' actor target f n).mp hr,
   reduces_is_attested hr,
   Witness.markGuard_runs_free,
   Witness.budgetGuard_forces_ordering⟩

/-! ## §6 — Non-vacuity spot-checks. The calculus's pieces are MEANINGFUL, not degenerate. -/

-- the three verb shapes map onto the three compressed verbs:
#guard (CTerm.create 1).verb == VerbCompression.CVerb.create
#guard (CTerm.gwrite 0 1 "balance" 5).verb == VerbCompression.CVerb.gwrite
#guard (CTerm.move 1 2 30).verb == VerbCompression.CVerb.move
-- the verb set has exactly three members:
#guard ((VerbRegistry.survivors.map
          (fun v => (VerbCompression.cfate v).compressedVerb)).eraseDups).length == 3
-- the five guard modalities, each naming a non-empty atom module:
#guard GuardModality.actor.atomModule ≠ ""
#guard GuardModality.epistemic.atomModule ≠ ""
-- the correspondence dictionary is populated:
#guard Correspondence .exercise ≠ ""
#guard factory_is_replication .escrow ≠ ""

/-! ## §7 — Axiom hygiene. Every PROVED keystone pinned to the three kernel axioms;
every POINTER re-pinned to confirm the cited theorem is itself axiom-clean. -/

-- §1 syntax
#assert_axioms verbs_are_three
#assert_axioms guard_modality_modules_nonempty
-- §2 reduction
#assert_axioms reduces_iff_step
#assert_axioms reduces_admits_guard
#assert_axioms reduces_is_attested
#assert_axioms reduces_writes
#assert_axioms reduces_fail_closed
-- §3 correspondences (the attenuation one is a real theorem)
#assert_axioms attenuation_is_scope_restriction
-- §4 the modality-pricing laws
#assert_axioms modality_price_is_tier
#assert_axioms modality_price_monotone
#assert_axioms modality_price_bounded
#assert_axioms modality_price_relational
-- §5 the headline
#assert_axioms dregg_calculus
-- the cited POINTERS, re-pinned axiom-clean:
#assert_axioms Dregg2.Exec.EffectsAuthority.introduce_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.amplifying_grant_rejected
#assert_axioms Dregg2.Substrate.VerbCompression.compressed_kernel_three
#assert_axioms Dregg2.Substrate.VerbRegistry.minimality
#assert_axioms Dregg2.Authority.ConfluenceClassifier.keeps_iff_coordinationFree

end Dregg2.Calculus
