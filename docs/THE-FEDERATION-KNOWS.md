# The Federation Knows a Secret No Member Knows

*On distributed knowledge, manufactured common knowledge, and the rare case where emergence
is a theorem instead of a vibe.*

Take three validators. Give each one byte of a Shamir sharing: member *i* holds the point
`(i, 0x42 ⊕ 0xAB·i)` in GF(256). Ask each of them: what is the secret?

None of them knows. This is not a manner of speaking — it is proven twice over, once
structurally and once information-theoretically. Structurally: a share sits at `x ≠ 0` and
the secret lives at `x = 0`, so no share can ever verify the secret statement
(`share_alone_never_verifies`). Information-theoretically: any sub-threshold collection of
shares is consistent with *every possible secret* — for any two candidate secrets there
exist sharings agreeing on everything observed whose secrets differ by exactly that gap
(`subthreshold_pool_blind`, riding Mathlib's Lagrange interpolation).

Now let any two of them cooperate. The Lagrange reconstruction of their two shares at
`x = 0` — the *real* reconstruction, the executable `reconstructByte` pinned byte-for-byte
to the deployed Rust — produces `0x42`, and the proof executes it (`two_shares_reconstruct`
runs the GF(256) arithmetic inside the kernel by `decide`). So:

> **The group knows. No member knows.** `distributed_without_individual`
> (`Dregg2/Authority/Epistemic.lean:565`): `DistributedKnows … ∧ ∀ i, ¬ Knows i` — one
> theorem, both halves, over the federation's actual threshold-decryption algebra.

Epistemic logicians call this D-without-K: distributed knowledge strictly above every
individual's. It is usually presented as a curiosity about possible-world models. dregg's
version is different in two ways that matter. First, it is *constructive*: "knows" never
means anything mentalistic — it means *can exhibit a verifying witness*. Second, it is
proven against the running mechanism, not a toy: the pooling operation is the federation's
threshold decryption, the shares are its shares, and the statement the coalition knows is
the one its quorum gate actually discharges.

This article is about what that theorem — and the tower it sits in — says about *entities*.
Because "the group knows something no member knows" is the definition people reach for when
they want to say a collective is *real*, over and above its members. Usually that claim is
atmosphere. Here it has a proof, a birth condition, a substance, and a uniqueness law.

---

## 1. Knowledge is what you can exhibit

Everything runs on one definition (`Epistemic.lean:102`):

```
Knows pocket a φ  :=  ∃ w, pocket a w ∧ Discharged φ w
```

An agent's epistemic state is its **pocket** — the witnesses it can produce on demand: held
credentials, received discharges, locally computed openings. To know `φ` is to be able to
pull out a witness that the verifier accepts. Not a relation between the agent and a
proposition; a relation between the agent and what it can *do* under interrogation. (This is
the BHK/realizability reading, and it is the same shape as dregg's authority doctrine — you
hold a capability iff you can produce its witness. Knowledge and authority are one
discipline: production under verification.)

Three things follow immediately, all proven, all strange from the classical angle:

**Possession is not knowledge.** The designated-verifier machinery (§7 of the file) hands
`v0`'s zero-knowledge transcript to *every* agent — total forwarding, everyone holds the
bytes. `v0` knows; the others, holding the identical witness, provably do not
(`dv_forwarding_no_E`): the discharge relation is verifier-indexed, and for anyone else the
transcript could have been a simulation. Knowledge lives in the *relation between a witness
and a verifier*, not in the bytes. Only at the public, transferable endpoint of the dial
does forwarding a proof transfer the knowledge (`transferable_forwarding_lifts`).

**Knowledge is production, not descent.** The modal structure is pinned categorically: over
the witness fibration, `Knows` *is* the left-adjoint composite `∃_a ∘ q_a*`
(`mem_knowsSet_iff`), and the classical box reading — "everything the agent holds verifies
φ" — coincides with it exactly when each agent holds one credential
(`knowsSet_eq_boxSet_of_functional`), and provably diverges at a mixed pocket
(`MixedPocket.knows_ne_box`). Knowing is an existential act, ◇ not □; the ∀-reading of
knowledge is a special case, not the definition.

**Ignorance is not a type.** On the biorthogonal side of the tree
(`Calculus/BiorthRelational.lean`), knowledge classes are behaviours — closed under the
double-orthogonal of a challenge relation — and behaviours are evidence-monotone. The
complement, "does not know," is *not* a behaviour (`ignorance_not_behaviour`): the closure
floods non-knowledge upward. In a witness semantics you can prove that someone knows; you
can never carve out, by any family of tests, the set of those who don't. Plausible
deniability is not a policy in this logic. It is a structural fact about what testing can
see.

## 2. The tower, and where it breaks

Four operators, one pocket semantics (`Epistemic.lean` §2):

- **K** — `Knows`: one agent can exhibit a witness.
- **E** — `EveryoneKnows`: every member of a group can exhibit a witness — *each possibly
  its own, private, mutually invisible witness*.
- **D** — `DistributedKnows`: the group's *pooled* witnesses — the closure of members'
  pockets under an explicit combining operation (`Pooled`: Lagrange interpolation,
  signature aggregation, concatenation) — contain a verifying witness.
- **C** — `CommonAt`: a verifying witness is *finalized*, hence visible to every agent by
  the floor law.

The inclusions that hold are proven (`C → E → K → D`), and the ones that fail are witnessed
rather than waved at, which is where the philosophy lives:

**D ⇏ K** is the threshold separation above: the coalition's knowledge is not any member's
and not their union's — it exists only through the combining computation. The `Pooled`
closure is the exact formal content of "the whole is more than the parts": not a mystical
surplus, an *inductive datatype* — seeds (what members hold) plus mixes (what combining
derives). And `pooled_invariant` is the no-conjuring law: pooling cannot produce witnesses
outside the closure. The surplus is real and bounded.

**E ⇏ C** is subtler and, we think, the deepest single fact in the file
(`no_common_for_private_pockets`): two agents each privately know `φ` — genuinely,
verifiably — and *no possible finality floor consistent with their pockets* can ever make
`φ` common knowledge. Everyone knowing is compatible with the group never knowing that it
knows. The gap between E and C is not iteration bookkeeping; it is a missing *object* — the
one shared witness — and no amount of private knowing manufactures it.

## 3. The entity that exists only above threshold

Put the two separations together and something with contours appears.

Below the threshold, the coalition-as-knower does not exist — not "knows less," but *is
consistent with every secret* (`subthreshold_pool_blind`). At the threshold, it snaps into
existence: `threshold_knows_secret` exhibits the quorum — distinct members, each producing
its share, one combine, verification passes. The birth of the collective epistemic subject
is a step function, and both sides of the step are theorems.

What is the entity *made of*? Here the biorthogonal analysis gives an answer that should
sound familiar to readers of the companion essay on cells. The distributed-knowledge class
is **not rectangular** — provably, no family of per-member tests can carve it
(`distributed_not_behaviour_rectangular`); it becomes a behaviour only when the *pooled
reconstruction challenge* is fielded as a test, and it then equals exactly the closure of
matched-randomness tensors (`dclass_eq_closure_of_matched_tensors`). Compare conservation:
not carvable per-turn, exactly the closure of matched-delta tensors. The pattern theorem
(`correlation_classifies_the_family`) says these are the same phenomenon: a law that lives
in the *correlation* between components, invisible to every componentwise view.

So the emergent knower is made of correlation the way a conserved quantity is made of
matched deltas. The federation's knowledge is not stored anywhere. It is not distributed
*over* the members like files over disks. It is the correlation between their pockets,
plus a combining computation — and it is exactly as real as conservation is, which in this
codebase is very real indeed: both are behaviours, both are carved by tests, and both
provably do not reduce to their components.

## 4. Common knowledge is manufactured, and the machine is the ledger

E ⇏ C says private knowledge never spontaneously becomes common. The classical folklore
(the coordinated-attack problem) says messages can't close the gap either: no finite
exchange of "I know that you know that I know…" reaches the fixed point. So where does
common knowledge ever come from?

dregg's answer: you *manufacture the shared witness*. `finality_is_common`
(`Epistemic.lean:660`): a valid finality certificate — validity being the node's real
super-ratification rule over its real tau ordering — makes its finalized root common
knowledge at its wave. The mechanism is almost embarrassingly concrete once stated. The
infinite E^k tower collapses because there is *one* witness, the cert, and its
verification is agent-independent (`cert_visibility_uniform` — the check takes no agent,
definitionally); so every agent can exhibit the very witness that establishes every other
agent's knowledge, at every depth, uniformly (`common_gives_mutual_witness`). Common
knowledge is not an infinite conjunction achieved; it is a single transferable artifact,
engineered. A ledger, on this reading, is a **common-knowledge prosthesis** — a machine
whose product is the shared witness that private pockets and message-passing provably
cannot produce.

And the manufactured subject has laws:

- **It cannot bifurcate.** `no_conflicting_common_per_wave`: two valid certificates over
  the same view anchor the same leader — common knowledge at a wave is unique. There is at
  most one "what we all know" per wave; the collective subject has an identity criterion.
- **It cannot be forked by a partition.** The killer example, stated as theorems: a bridge
  that settles on locally-visible approval double-settles under partition
  (`unguarded_double_settles` — four validators split two and two, both sides mint). Guard
  the settlement on the common-knowledge constructor — a super-majority of ratifiers — and
  *no partition of any committee size* can settle on both sides
  (`commonAt_guard_partition_safe`), because two disjoint super-majorities cannot fit in
  one committee (`superMajority_gt_half`). Safety is unconditional; the price is waiting
  for the partition to heal.

That price is itself typed. The epistemic guard atoms carry their coordination cost as
part of their design (`EpistemicAtom.cost`): K and DV-K are **free** (a local witness
check); D costs **one quorum round**; C costs **finality latency**. To be an individual
knower is cheap. To be a coalition costs a round-trip. To be a *public* — a subject whose
knowledge is common — costs finality, and the partition-safety theorem is what that
latency buys. The ontology has a price list.

## 5. What kind of thing is a federation, then?

The companion essay argued that a cell is not a datastructure — it is pinned between two
fixpoints, its identity the unique unfold into a final coalgebra, its interface a
biorthogonally closed set. The epistemic tower extends the same maneuver upward, to
collectives:

A federation, as an epistemic subject, is **a pocket plus a combining operation plus a
floor** — and each ingredient is individually load-bearing. The pocket says what members
can exhibit. The combining operation (`PoolOps`) says what the coalition can derive; change
it and you change what the group knows, with the members untouched. The finality floor says
what the group knows *in common*, and it is exactly the assumption a partition suspends —
which the file states plainly rather than hiding: C_G holds *relative to the floor law*,
finalized-implies-visible, and at n = 1 the whole tower collapses onto K
(`knows_to_common_single` — on a single machine, private knowledge already is common).

None of these ingredients is a member. None is a sum of members. The subject they compose
is nevertheless fully real by the only standard this codebase accepts: it is
*interrogable* — there are tests it passes that nothing smaller passes, and theorems, with
`#assert_axioms` pins, about exactly when it exists, what it is made of, and why there is
only one of it per wave.

Emergence talk usually asks you to squint. This is the other thing: a collective entity
with a proven birth condition (the threshold), a proven substance (correlation, in the
precise biorthogonal sense), a proven identity law (uniqueness per wave), a proven
non-reducibility (D-without-K, both halves), and a posted price (free / quorum / finality).
The federation knows a secret no member knows — and we can say *exactly* what the "it"
in that sentence is.

---

### Resolution ledger

Stated at current resolution. The mechanism instances are proven against the real
machinery — the council's actor-bound approval slots (`council_certification_is_E`, with
the tooth that no member can exhibit another's approval), the deployed Shamir/GF(256)
threshold algebra with its Rust-pinned `reconstructByte`, and the node's real
super-ratification rule — while the §1 TRUE/FALSE demos are labeled toys. The four
epistemic guard atoms (`knownBy / distributedAmong / commonAt / privateTo`) are **design
only** at this writing: signatures, denotations into the tower operators, and cost
classification exist; installation into the executor's guard surface is owned by a
separate lane and has not happened. C_G is explicitly relative to the finality floor's
delivery law (finalized ⇒ visible to every light client) — that law is what a partition
suspends, which is precisely why the `commonAt` guard is the partition-safe one. The
cryptographic floors enter only through the consumed modules and are named there. The
epistemic tower itself — operators, inclusions, separations, mechanism welds, adjoint
triple, partition theorems — is sorry-free and `#assert_axioms`-clean against
`{propext, Classical.choice, Quot.sound}`.
