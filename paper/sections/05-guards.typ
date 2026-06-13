// =============================================================================
// Section 5: The guard algebra
// =============================================================================

#import "../defs.typ": lean
= The guard algebra <sec-guards>

Everything that constrains a turn is one algebra of decidable predicates over
the proposed step. The same `Pred` the executor evaluates is compiled to the
circuit obligation a proof discharges: an installable guard and a provable
property are one mechanism. This section gives the algebra, its closures, and
the two prices it computes.

== One `Pred`, four polarities

A predicate is one object:

```
Pred = curated atoms ⊕ all/any/not ⊕ witnessed(vk) ⊕ thirdParty(discharge)
```

It is either *first-party* --- decidable now against the old and new state ---
or *witnessed*: `witnessed(vk)` defers to a registered verifier, which is how a
third-party discharge, a range proof, or an arbitrary proof-carrying claim
enters the same grammar. The novelty is not the grammar but its reach: the one
algebra appears at four *polarities* that are four separate mechanisms in most
systems.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*polarity*], [*the predicate is imposed on*]),
    [*caveat*], [_delegated_ power --- a restriction travelling with a capability],
    [*program constraint*], [_owned_ state --- the cell's self-imposed law],
    [*precondition*], [a _turn_ --- what an action requires to be admissible],
    [*intent demand*], [the _world_ --- the typed hole `hole(Pred)` a counterparty's fulfillment discharges (@sec-model)],
  ),
  caption: [The four polarities of one predicate algebra. A caveat on a
    macaroon, a smart-contract invariant, a transaction guard, and an
    open-order condition are one mechanism here.],
)

Because the four are one object, a caveat is checkable by the proof system, not
only by the issuing service; an intent demand is the same kind of fact as a cell
program; and a precondition compiles to a circuit obligation exactly as an
invariant does. An intent is the demand polarity made first-class: a fulfillment
supplies the witness that closes the hole, and the counit of @sec-authority's
demand $tack.l$ supply adjunction is what discharges it.

== The grammar and its closures

The curated atoms are small decidable shapes over a cell's slots --- equality,
bounds, write-once, immutability, monotone and strictly-monotone updates,
deltas, sums, allowed-transition automata, membership, prefix. The roster of
record is enumerable and lives in the generated predicate catalog
(`studio/predicate-catalog.generated.json`); the paper cites it rather than
fixing it here. Two closures keep the grammar from ossifying into axis-aligned
special cases.

*Relational closure* (`Authority/RelationalClosure.lean`). Any affine relation
over the post-state --- $"head" lt.eq "tail" + "capacity"$, $Sigma "slots" =
"const"$ --- is the same `Pred` object (#lean("RelationalClosure.RelPred")), with
#lean("RelationalClosure.ofFieldLteOther_eq") recovering the single-slot atoms as
instances. There is no new atom per shape: the guard language is the internal
predicate logic of the state object, bounded only by decidability and
circuit-expressibility.

*Quantified closure* (`Authority/QuantifiedPredicate.lean`). Bounded $forall$ and
$exists$ over slot ranges compile to the relational closure with a proven
constraint budget: #lean("QuantifiedPredicate.compile_sound") welds the compiled
form to the quantified meaning, and #lean("QuantifiedPredicate.andFold_budget") /
#lean("QuantifiedPredicate.orFold_budget") bound the cost. Quantifiers cost what
they cost, and the cost is a theorem.

== The coordination dial

Guards carry a coordination price, and the system computes it
(`Authority/ConfluenceClassifier.lean`) rather than assuming it. Two concurrent
turns merge without coordination exactly when their guards are
*confluence-stable* --- the invariant survives merging independently-taken steps.
The classifier is the independence logic of @sec-authority landing in the guard
language:

- #lean("ConfluenceClassifier.keeps_iff_coordinationFree") --- a guard preserves
  confluence if and only if it runs coordination-free;
- #lean("ConfluenceClassifier.monotone_keeps") --- monotone thresholds are free;
- #lean("ConfluenceClassifier.bounded_breaks") /
  #lean("ConfluenceClassifier.bounded_forces_ordering") --- an upper bound forces
  ordering (consensus).

The classifier does not forbid the expensive case; it *prices* it. A
confluence-stable guard runs coordination-free; a guard that is not provably so
forces ordering, and the difference is reported, not legislated.

== The disclosure dial

The second computed price is disclosure: how much a guard reveals while being
checked. The principle is that *what the proof does not need, it does not ask to
see*. The ladder, most to least disclosed:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*rung*], [*what the guard sees*]),
    [*cleartext*], [the predicate reads values directly],
    [*committed*], [values behind Pedersen commitments; conservation checks
      homomorphically without opening],
    [*range-proved*], [only the bound is disclosed],
    [*jointly garbled*], [two parties evaluate a shared gate over private inputs
      and learn the verdict and nothing else],
  ),
  caption: [The disclosure dial. Each rung is an evaluation mode of the *same*
    predicate; the law is rung-invariant.],
)

The ladder is mechanized so that privacy never changes the law it checks.
Committed evaluation checks conservation homomorphically
(#lean("PrivatePredicate.private_conservation_checks_homomorphically")), and the
committed and cleartext judgments provably agree
(#lean("Spec.committed_iff_cleartext")) --- moving down the dial hides inputs, not
verdicts. A range proof discloses only the bound
(#lean("RangeProof.disclosure_only_the_bound"),
#lean("RangeProof.committed_inequality_via_range")). The garbled rung lets two
parties evaluate one gate over private inputs
(#lean("GarbledJoint.garbled_input_private"),
#lean("GarbledJoint.joint_turn_private_gate")), and its disclosure floor is
acceptance-only --- the verdict and nothing else
(#lean("GarbledJoint.garbledDialFloor_is_bot")). The Poseidon2 garbling
construction that makes this rung STARK-provable is @app-garbled.

Selective disclosure of a receipt --- hide, reveal, predicate,
committed-threshold --- is the same dial applied to *Q* (@sec-proofs): a
projection of the receipt, not a second copy of it. Disclosure and proof are one
object viewed at a chosen resolution.
