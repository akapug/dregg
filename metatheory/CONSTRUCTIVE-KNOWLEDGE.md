# dregg, as a metatheory of constructive knowledge

> This file names the thing the directory has been *mis-calling* "Metatheory." There is an
> **actual metatheory** here — a distributed, intuitionistic logic of *constructive knowledge and
> authority* — and there is the **verification of dregg2** (the Lean proofs that the system realizes
> that logic). They interact, but they are not the same. This document is the former: the conceptual
> spine, with the authority model stated as the law the verification discharges.

---

## 0. The thesis: authority is constructive knowledge

**A principal's authority over a resource is exactly its ability to constructively exhibit a witness
the kernel accepts.** You *hold* a capability iff you can *produce* the witness for it — never merely
assert it, never merely be named in a table. Authority is **production under non-forgeability**.

This is the corrected, current thesis, and the correction is load-bearing enough to state its negation
first:

> **Authority is *not* affine descent.** It is tempting to read a capability as a linear/affine resource
> that is *consumed* as it flows — held, then spent, monotonically narrowing down a meet-semilattice.
> That frame is **wrong**: it forbids exactly the generative patterns (introduction, sealer/unsealer
> amplification, mint/factory) that give object-capabilities their power, and it locates authority in a
> *quantity that drains* rather than in a *witness you can re-exhibit*. Authority does not deplete by
> being used; it is constituted by what you can prove, every time, at the point of use.

So the unit of authority is a **proof obligation you can discharge**, and four facets make that sound:

1. **non-forgeability** — the crypto floor makes the ability to produce a witness *un-counterfeitable*;
2. **monotone attenuation** (`granted ⊆ held`) — production is monotone-*decreasing* along delegation:
   a delegate can only produce what its delegator could, or less;
3. **kernel enforcement** — the gate that accepts the witness is the kernel's, run on every step;
4. **zk-checkability** — the production is witnessed by a proof a light client (holding no secrets)
   can check.

Everything else — cells, turns, effects, the constraint catalog, finality, privacy — is a *projection*
of "authority = constructive knowledge = production-under-non-forgeability." This is the
[BHK / realizability](https://en.wikipedia.org/wiki/Realizability) reading of intuitionistic logic,
made operational and distributed: the whole edifice is organized around the asymmetry **proof-checking
is cheap and trusted; proof-*search* is undecidable and untrusted.**

---

## 1. The knowledge graph

The capability graph **is** a distributed knowledge graph:

- **nodes** are *cells* — the knowers / agents / objects, each with private state and a program;
- **edges** are *capabilities* — directed facts of the form "this cell can constructively produce a
  witness the kernel accepts for authority over that one," carrying *attenuated rights* (a facet:
  which acts the edge licenses);
- the graph is **partial and local**: no node sees the whole graph. You learn of an edge only when
  someone *produces a witness* for it. There is **no global registry of who-can-do-what** — the
  capability-derivation tree is at most a *retrospective* log (the de-jure record), never a live oracle
  you consult. Authority is established by *exhibiting a discharging witness at the point of use*, and
  checking it.

To *hold* a capability is therefore not to possess a key in a lock — it is to be able to **discharge a
proof obligation**. Possession and production are the same act.

---

## 2. A turn is an authorized inference step

A **turn** is one step of distributed inference: a forest of *actions*, each of which proposes to move
the knowledge graph from one state to a successor, **executed as a transaction** (all-or-nothing;
journalled, rolled back on any failure). An action carries:

- a **demand ⊣ supply** pair (the cell *demands* `AuthRequired`; the action *supplies* a witnessed
  `Authorization`) — this is exactly the **`Predicate ⊣ Witness` adjunction**: admissibility is "does
  the supplied witness realize the demanded predicate?", i.e. `Verify P w`. Read as a Lawvere
  hyperdoctrine, `Predicate ⊣ Witness` is the *base* adjunction; production (this section) is its left
  leg made operational — you supply the witness, the kernel checks the predicate. (Agreement across
  knowers is the *limit* in this hyperdoctrine; the witness escapes Arrow-style impossibility precisely
  by restricting to *certifiable* claims — but that is the agreement story, downstream of production,
  and not relied on here.)
- **guards** (preconditions / program-constraints / caveats) — *more* predicates over the proposed
  step, each again first-party (decidable now) or witnessed (a registry verifier discharges it);
- **effects** — the proposed graph mutation;
- a signed **binding** to a canonical message (federation, nonce, action, effects) — so an inference
  cannot be replayed into a context it was not proved for.

Soundness is not a property of one step but of the **unbounded life of the cell**: the cell is *codata*
(`νC. µI. StepProof I × (Turn ⇒ C)`), and "the cell stays correct forever" is a **▶-guarded
bisimulation** to a golden-oracle reference — "the knowledge never drifts from the truth it claims."
Step-completeness (each step really attests its full invariant) is what makes the coinduction
productive rather than a *drifting future* that type-checks while leaking.

---

## 3. The production law

To *produce* authority is to **exhibit the witness the kernel's gate accepts** — and the gate is one
fail-closed conjunction, run on every action. In the Lean executor it is `gateOK`
(`Dregg2/Exec/FullForestAuth.lean:490`):

```
gateOK na s = credentialValidG na      -- WHO  : the credential's witness verifies (non-forgeability)
           && capAuthorityG na          -- WHAT : kernel cap narrowing,  granted ⊆ held
           && caveatsDischarged na s     -- HOW  : caveat chain + tiered caveats discharge
           && revocationGate na s        --        the edge is not revoked/expired
```

The four facets of §0, mapped to the real proofs:

**(1) non-forgeability — the credential's witness verifies.** `credentialValidG`
(`FullForestAuth.lean:433`) reduces through **`portalVerify`** (`FullForestAuth.lean:138`): the crypto
arms (signature / proof / bearer / capTpDelivered / custom / stealth / token) route through the
`CryptoKernel.verify` portal — a named crypto floor — and the structural arms are pure reads. The
ten-variant `Authorization` dispatcher is `authModeAdmits` (`Dregg2/Exec/AuthModes.lean:182`), which
proves per-mode that admission implies the abstract authority object holds. `portalVerify`'s
non-vacuity is pinned in-file: a genuine signature is accepted, a *forged* one fail-closes, and
`Unchecked` is rejected at the §8 anchor (`FullForestAuth.lean:192-198`). Forgery is what production
must be safe against; the portal is where that safety is named.

**(2) monotone attenuation — `granted ⊆ held`.** Production is monotone-decreasing along delegation.
This is *not* a `() ≤ ()` collapse: the rights lattice is `ExecAuth := Finset Auth`, ordered by genuine
`⊆`, with `{read}` and `{write}` **incomparable** (`Dregg2/Exec/Caps.lean:57`). Attenuation narrows in
that real lattice: `attenuate_confRights_le` (`Caps.lean:130`). The delegation verb
`recKDelegateAtten` (`Dregg2/Exec/AuthTurn.lean:97`) carries
`recKDelegateAtten_non_amplifying` (`:439`): when a delegation commits, the granted cap's conferred
rights are `⊆` the held cap's — *granted-vs-held, not self-vs-self*. The generative twin,
`introduce_non_amplifying` (`Dregg2/Exec/EffectsAuthority.lean:207`), proves a Granovetter introduction
confers no more than the introducer holds, and `handoff_non_amplifying` (`Dregg2/Exec/CapTP.lean:286`)
reuses it for the two-signature CapTP handoff.

**(3) kernel enforcement — the gate is the kernel's, every step.** `gateOK` is *the* admission gate;
there is no ungated escape hatch on the gated forest. Whole-turn non-amplification survives the gate:
`execFullForestG_no_amplify` (`FullForestAuth.lean:1014`) — **every delegation edge produced by a gated
turn confers `≤` what the actor holds** — is a one-line corollary of the ungated
`execFullForestA_no_amplify` via the erasure discipline (`eraseG`). The gate adds restrictions and
removes none, so the headline survives it for free.

**(4) zk-checkability — the production is witnessed in-circuit.** The same `granted ⊆ held` is decided
in the circuit IR by **`checkSubset`** (`Dregg2/Circuit/Argus/Stmt.lean:83`), which commits iff
`a k ≤ b k` over the genuine partial order — fail-closed on a strict superset *and* on an incomparable
pair (`interp_checkSubset`, `Stmt.lean:338`). The deployed turn proof carries it: `AttenuateCapability`
and `GrantCapability` are witnessed in-circuit against the **authenticated openable `capability_root`**
(`circuit/tests/effect_vm_attenuate_non_amp.rs`, `effect_vm_grant_non_amp.rs`,
`circuit/src/cap_root.rs`), seeded from the cell's canonical root rather than zero
(`circuit/tests/cap_root_cell_circuit_differential.rs`), and the consumed capability's full leaf is
proven a member of the holder's pre-state root (`CapMembershipWitness`, `sdk/src/full_turn_proof.rs:212`).

These four are AND-ed and **fail-closed on any leg**. Production is the act that makes all four true at
once: exhibit a witness that verifies (1), confers no more than you hold (2), passes the kernel gate
(3), and leaves a proof a stranger can check (4).

---

## 4. What the production law grounds

**Non-amplification is the monotonicity of constructive knowledge under delegation.** `granted ⊆ held`
is not a side-condition bolted onto delegation — it *is* the statement that you cannot produce a
witness for authority you could not already produce. The whole-turn theorem
`execFullForestG_no_amplify` lifts this from one edge to the entire forest of a turn. Authority can
still *grow* — introduction, sealer/unsealer rights amplification, mint/factory, parenthood/endowment
are all generative — but every generative act is *itself authorized by held knowledge* and
*receipt-disclosed*. Miller's law, *"only connectivity begets connectivity,"* is exactly: **you can
only produce witnesses you (transitively) hold the material to produce.** This is an epistemic
non-forgeability invariant, not a lattice descent.

**Light-client unfoolability is the proof witnessing the production.** A light client holds no secrets
and cannot re-run a cell; it can only *check a proof*. Because production is witnessed in-circuit
(`checkSubset` against the authenticated `capability_root`), a verifying turn proof *is* the evidence
that authority was produced honestly — the kernel narrowed correctly, no amplification, against the
real pre-state. The pale ghost (a forged history that type-checks) cannot be produced, because the
witness it would need does not exist under non-forgeability.

**The cipherclerk is a sovereign executor because a principal *is* what it can produce.** A sovereign
cell keeps only a commitment to its state and *proves* its own transitions (a STARK in the public
inputs); a far federation admits it knowing only how to *check a proof*, never how to *re-run* it. This
is identity-as-production: the cell's authority over its own resources is precisely its ability to
exhibit accepted witnesses for its transitions. Inside a trust root authority is positional
("caps-as-caps": holding the edge *is* the proof); across a boundary it becomes epistemic
("keys-as-keys": you must *present* a verifiable witness, because the far side shares no mediator) — and
the crossing is a named-lossy functor Φ under which *permission survives, authority does not* (which is
why a forwarded capability becomes revocable by construction).

---

## 5. The honest open frontier: the macaroon ↔ cap convergence

The production law is fully proven and in-circuit for **one** of the four credential aspects — the
kernel capability (`granted ⊆ held` via `recKDelegateAtten` / `capAuthorityG` / `checkSubset`,
witnessed against the authenticated `capability_root`). The credential is meant to be *one authority
seen four ways* — **biscuit** (Datalog policy: what is permitted) · **macaroon** (caveat-chain
transport: how it narrows hop by hop) · **cap** (kernel c-list: what the kernel enforces) · **zk**
(proof of honest narrowing) — all refining the single relation `granted ⊆ held`
(see `docs/AUTHORIZATION-MODEL.md`).

Today these are joined by **conjunction, not by a proven arrow**. `gateOK` reads *independent*
`NodeAuth` fields: `capAuthorityG` (`FullForestAuth.lean:443`) and `chainGateG` (`:452`, the macaroon
HMAC face) are AND-ed over disjoint state, and **there is no theorem `chainGateG na → capAuthorityG na`**
anywhere in `Dregg2/` — the kernel files do not even import the caveat-chain model. So at the delegation
verb, where the macaroon caveat chain and the kernel cap both narrow authority, non-amplification is
told *twice*, in two separately-modeled lattices welded by `&&`. It is a genuine fail-closed conjunction
(a macaroon can never widen *past* the kernel cap, so this is defense-in-depth, not a hole) — but it is
not *one* proven production-arrow.

**The live research edge is the `chainGateG → capAuthorityG` arrow:** prove that the macaroon caveat
chain's narrowing *is* (or refines) the kernel's `granted ⊆ held` narrowing on the verb where they
overlap, so the four aspects bind into a single proven production rather than four agreeing stories.
The smallest first step is a single Lean lemma over a shared `NodeAuth.narrowed : ExecAuth` field plus
the SDK projection of the caveat chain onto that lattice (`docs/AUTHORIZATION-MODEL.md` §4). Until that
arrow exists, the production law is *proven for the cap aspect and conjoined with the others*, not yet
*proven as one production* across all four. This is the place the four facets do not yet bind into one
proven production-arrow, and it is named, not papered over.

---

## 6. Metatheory vs. verification (why the rename)

- **The metatheory** (this document, and the small Lean core that genuinely encodes it) is the *logic*:
  what a capability/proof/turn *is*; the demand⊣supply adjunction; **authority as
  production-under-non-forgeability** and its four facets; the generative/restrictive dynamics and the
  non-forgeability invariant; coinductive soundness. It is, deliberately, *candidate-independent* — it
  would be the metatheory of any system built this way.
- **The verification of dregg2** is the (much larger) body of Lean that proves *the dregg2 system*
  realizes that logic — the executable cells, the constraint catalog, the kernels, the protocols, the
  circuit bridges, the FFI cascade.

They interact (verification *discharges* the metatheory's obligations against a real system) but are
**not the same thing**, and conflating them under one name "Metatheory" hid the actual metatheory.

> The egg metaphor still holds: we are learning what is inside without cracking it. What is inside is a
> living, distributed, capability-secure organism that *knows things by being able to prove them* — and
> whose authority is, all the way down, the disciplined production of authorized, non-forgeable
> witnesses over unbounded time. 🐉🥚
