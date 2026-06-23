# Private offline cells: witnessless participation in a multi-cell turn

> ember's question (2026-06-13): *how flexible is the system toward participating in a
> consensus operation in a turn with a cell that someone else maintains OFFLINE and only
> wants to publish witnessless ZK proofs about?*

Short answer: **the architecture already supports commitment-only cells and proof-as-attestation;
what is missing is a first-class "private participant" turn ROLE — a per-leg disclosure choice
inside the N-cell atomic turn.** This doc states the design precisely, maps it onto the existing
primitives, and points at the Lean model that proves the composition law sound.

The Lean model: `Dregg2/Distributed/PrivateLeg.lean` (keystone
`joint_turn_sound_with_private_legs`). This is **design + model**, not yet production wiring.

---

## 1. The scenario

A party `P` maintains a cell entirely offline: its `RecordKernelState` (balances, caps, nullifiers)
is held by `P` and **never published in cleartext** — not to the other turn participants, not to the
chain. `P` nonetheless wants to take part in a multi-cell coordinated turn (a `JointTurn` / the
coordinator's `AtomicForest` 2-phase commit) by contributing **only**:

  * a **state commitment** to its private pre-state and post-state (the Poseidon2 state root,
    `recStateCommit`), and
  * a **ZK proof** that *its side of the turn is a valid, guarded, conserving, authorized executor
    step* — with no witness (no pre/post state, no amounts, no caps) revealed to anyone.

The other legs of the turn may be **public** (run on the shared machine, state visible) or themselves
private. The turn must commit **all-or-none** and the whole-turn guarantees (per-asset conservation,
no capability amplification, one CG-2 shared identity) must hold across the **public + private**
composition.

---

## 2. What the current architecture ALREADY supports

The pieces are all present; they have simply never been **composed into one turn with a per-leg
disclosure choice**.

| Capability | Where it lives | Status |
|---|---|---|
| **Commitment-only state** — a cell published as a `ℤ` root, not cleartext | `Circuit/StateCommit.lean` `recStateCommit` (Poseidon2 state root, `recStateCommit_binds` injective under the CR floor) | EXISTS |
| **Proof = attestation** — the executor's correctness witnessed by a STARK, not re-execution | `Circuit/*` (the whole verified-emission column); `Crypto/PortalFloor.lean` `VerifierKernel` (the §8 STARK floor) | EXISTS |
| **The N-cell atomic turn** — many cells contribute legs to one forest, all-or-none 2PC | `Distributed/EntangledJoint.lean` (`jointApplyAll`, `joint_sound_of_binding`) | EXISTS (all legs **public**) |
| **CG-2 shared identity** — every leg consents to ONE `jid` (Mina's `account_updates_hash`) | `EntangledJoint.JointBinding` | EXISTS |
| **The disclosure dial** — per-cell field visibility, `private`/`selective`/`trusted` | `Circuit/Argus/Disclose.lean` `Tier`, `disclose_hides_private` | EXISTS |
| **Selective-disclosure joint state caveats** — a cross-cell predicate gating the joint turn | `Exec/CrossCaveat.lean` | EXISTS |
| **Threshold turn-privacy** — t-of-n decryption so no single party sees the payload | `Distributed/ThresholdDecrypt.lean` | EXISTS |
| **Per-leg conservation + authority** — every `recKExecAsset` step conserves per-asset and is authorized | `Exec/RecordKernel.lean` (`recKExecAsset_conserves_per_asset`, `recKExecAsset_authorized`) | EXISTS |

So: a cell **can** be represented to the rest of the system by a commitment + a proof
(`recStateCommit` + a `VerifierKernel` acceptance), and the N-cell atomic turn **does** compose
per-leg conservation/authority into a whole-turn guarantee. The substrate is there.

---

## 3. What is MISSING

1. **A "private participant" turn role.** `EntangledJoint.Leg` is *public by construction*: it carries
   a `Turn` and is run by `recKExecAsset` on the **shared** `RecordKernelState`. There is no leg shape
   that is "commitment + proof, never touch the shared machine." The coordinator
   (`coord/src/atomic.rs`) likewise assumes every participant's action is applied to the shared ledger.

2. **Selective-disclosure joint turns where one leg is proof-only.** The disclosure dial
   (`Disclose.Tier`) is currently a *read projection over already-public state* — it hides fields when
   you OBSERVE a cell. It does not yet describe a leg that was **never on the machine**, whose only
   public footprint is `(commitPre, commitPost, acceptance-bit)`. Mixing a `.trusted` (public) leg and
   a `.private` (proof-only) leg in **one atomic turn** is unmodeled.

3. **The composition soundness law** for that mix: that public-machine conservation + private-proof
   conservation compose to a sound whole turn **without the composite ever holding a private witness**.
   This is the keystone the Lean model now supplies (§5).

---

## 4. The design — the mixed joint turn

A **private leg** publishes only its public face `PrivLeg = (asset, commitPre, commitPost, jid)` — the
hidden `RecordKernelState` is *not a field*. The ZK proof certifies the relation

```
PrivLegHolds scommit pl  :=
  ∃ kPre kPost turn,
      recKExecAsset kPre turn pl.asset = some kPost     -- a real guarded executor step happened offline
    ∧ scommit kPre  = pl.commitPre                       -- ...committing to the published pre root
    ∧ scommit kPost = pl.commitPost                      -- ...and the published post root
```

The hidden `kPre`/`kPost` live **under the `∃`** — the *statement itself* never exposes them. An
accepting `VerifierKernel` proof discharges `PrivLegHolds` via `verify_sound` (the STARK
extractability carrier). Because `recKExecAsset` is the *verified per-cell executor*, certifying that
relation certifies — for free, via `recKExecAsset_conserves_per_asset` and `recKExecAsset_authorized`
— that the offline step **conserved every asset** and was **authorized**, even though no one but `P`
ever saw the state or the authority check.

A **mixed joint turn** is then:

```
MixedJoint = (jid, publicLegs : List Leg, privateLegs : List (PrivLeg × Proof))
```

admissible iff: the public legs commit all-or-none on the shared machine (`jointApplyAll = some k'`),
**and** every private leg's proof verifies under the §8 carrier, **and** every private leg consents to
the shared `jid` (CG-2). On the disclosure cube:

  * a **public leg** sits at Disclosure = `.trusted` (full state on the shared machine),
  * a **private leg** sits at Disclosure = `.private` (only `commitPre`/`commitPost` + the acceptance
    bit leave the offline cell — the `acceptanceOnly` ZK floor of `Crypto/PredicateKernel.lean`),
  * **Agreement** is the same CG-2 `jid` binding for both,
  * **Transferability** is whatever the leg's caps allow (orthogonal; the proof certifies authority).

That per-leg disclosure choice is the "flexibility" answer: **the architecture admits each
participant choosing public vs. proof-only, in one atomic turn, without weakening whole-turn
conservation or authority.**

---

## 5. The keystone (proved, axiom-clean)

`joint_turn_sound_with_private_legs` (in `Dregg2/Distributed/PrivateLeg.lean`): given admissibility +
the named ZK floor, the mixed turn is sound as a whole —

  1. the public side **conserves every asset** on the shared machine (`jointApplyAll_conserves`),
  2. the public side **amplifies no capability** (`jointApplyAll_caps_frame`),
  3. **every private leg certifiably ran a real conserving offline step, witness HIDDEN** (the
     existential keeps `kPre`/`kPost` off the wire),
  4. every public leg AND every private leg **consents to the one shared `jid`** (CG-2).

Companion: `mixed_turn_composite_conserves` (public ⊕ private composite conserves, the private
contributions accounted only by their certified deltas). Teeth both polarities:
`privLeg_real_verifies` (an honest carrier accepts a real leg; the statement is genuinely inhabited)
and `privLeg_forged_rejected` / `exists_forged_leg` (a "conjure value from nothing" leg is genuinely
FALSE under an injective commitment — only the extractability carrier could ever have rescued it, and
the forging verifier that lacks it is unsound). `private_reveals_strictly_less` pins the disclosure
position.

All `#assert_axioms`-clean (⊆ {`propext`, `Classical.choice`, `Quot.sound`}).

---

## 6. The named crypto floor

The single irreducible assumption is **STARK extractability of each private leg's ZK proof**
(`PortalFloor.VerifierKernel.extractable`) — that an accepting proof certifies a real guarded
executor step existed offline whose commitments match. This is the **same** floor every other circuit
verification in the tree already rests on; the private-participant feature adds **no new cryptographic
assumption** beyond it (plus the existing `recStateCommit` collision-resistance/binding floor for the
state-root commitments). Nothing about "offline + witnessless" weakens the floor — it is exactly the
soundness STARKs already give.

---

## 7. What production wiring would require (follow-ups)

This doc + model establish *feasibility and the soundness law*. To ship it:

  * **Rust: a private-participant leg type** in `coord/src/atomic.rs` — an `AtomicForest`
    participant whose contribution is `(commitPre, commitPost, proof)` rather than an applied action,
    plus a verify-gate in the commit path (the `MixedAdmissible` check). *(HORIZONLOG follow-up.)*
  * **An AIR encoding `PrivLegHolds`** — the circuit that the `CarrierEncodesPrivLeg` hypothesis
    names: `recKExecAsset` + the `recStateCommit` state-root opening, so the proof is producible
    offline by `P`.
  * **State-root continuity across turns** for a long-lived offline cell (the `commitPost` of one
    turn = the `commitPre` of `P`'s next), mirroring `HistoryAggregation.ChainBound`.
  * **Liveness / availability** is explicitly *out of scope of soundness*: a private participant that
    goes dark aborts the all-or-none turn (a safety-preserving failure), exactly as a public
    participant voting No does. Data-availability of `P`'s own state is `P`'s problem by construction —
    that is the point of holding it offline.
