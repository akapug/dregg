# DREGG4-UNIFICATION — the three-faced turn at its limit (galaxy-brain rebuild design)

> ⚑ **GROUND-CHECKED vs live Lean 2026-06-02** (post-2-compaction drift-repair); **REAL / DECORATIVE /
> ASPIRATIONAL** tags carry `file:line` receipts. **The big news:** the code overtook this doc. Several
> things this design called "entirely new / zero exists / a §8 fiction" are now **BUILT and kernel-clean**
> in `metatheory/Dregg2/`:
> - **Transferability dial (§4.2/§6.1/§6.2):** REAL — `Authority/DesignatedVerifier.lean` ships
>   `Transferable`/`DesignatedFor`/`TransferDial`/`DischargedFor` + the named-new verifier-indexed theory,
>   with teeth (`designated_not_transferable`:206, `designated_is_deniable`:224, `dial_endpoints_distinct`:346).
>   The doc's "genuinely-new axis / grep-confirmed zero" narration is **stale** — it landed.
> - **Caveat-chain HMAC tail (§3.1/§6.3):** REAL — `Authority/CaveatChain.lean` models the exact Rust
>   tail recurrence `Tᵢ = mac Tᵢ₋₁ encode(Cᵢ)` (`replayTag_append`:184, `verify_iff_wellTagged`:168,
>   `append_narrows`:223). The "unflagged §8 fiction / Lean overlook" narration is **stale**.
> - **3P discharge with real ciphertext (§3.1):** REAL — `Authority/ThirdPartyDischarge.lean` (`accepts_iff`:246).
>   It is no longer "a `Bool` flip."
> - **Selective disclosure (§4.1):** REAL — `Authority/SelectiveDisclosure.lean`
>   (`presentation_hides_undisclosed`:239, `predicate_proof_has_teeth`:298). No longer "absent."
> - **Per-asset conservation (§3.2, the "#1 gap"):** REAL on the executable kernel —
>   `Exec/MultiAsset.lean: maExec_conserves_per_asset`:131 **and** the live executor's
>   `Exec/TurnExecutorFull.lean / RecordKernel`:`recKExecAsset_conserves_per_asset`, lifted whole-tree as
>   `Exec/FullForest.lean: execFullForestA_conserves_per_asset`:224.
> - **νF₁⊗νF₂ "non-final" (§5.3/§8):** FALSE + RETIRED in code — the product of finals IS final; the real
>   obstruction is the **proper-subobject** fact `JointTurn.binding_is_proper`:333 (N-ary
>   `Hyperedge.hyper_binding_is_proper`:164, `#assert_axioms`-pinned). Read §5.3/§8 with that correction.
> - **`sound_of_step_complete` (§4.2):** RETIRED as ill-posed; recovered honestly as
>   `Exec/Cell.lean: bisim_of_oracle`:61 / `livingCell_sound`:102.
> - **The comodel / lens / get-put-guard vocabulary (§5):** DECORATIVE — `grep` finds `Comodel` only in 3
>   prose comments (`HandlerTransformer.lean:118,128`, `Claims.lean:538`) and **zero** `Lens`/`get_put`/
>   `put_get` Lean objects. The §5 thesis is *aesthetic framing*, not a built construction.
> - **Genuinely OPEN, unchanged:** `forkSpan` (zero hits — ASPIRATIONAL); forest-delegation edges are still
>   *discarded* by `Exec/FullForest.lean: execFullChildrenA`:124 (`⟨_,_,_,sub⟩`, the #138 gap); the
>   user-extensible effect theory (§6.4), the accountable-anonymity 4th face (§6.8), and the
>   agreement-as-3rd-dial (§4.3) have no Lean object yet.
>
> This banner supersedes any stale narration below; the section bodies have been tagged in place.

> **What this is.** A READ-ONLY design exploration for **dregg4**, the advanced/generalized successor.
> No code changed. It takes the synthesis of this session — the **three-faced turn** (effects ⊕ caveats ⊕
> attestation) with **two dials** (disclosure: *what-is-revealed*; transferability: *to-whom-convincing*) —
> and pushes it to its maximal generality: *is there one turn-generator whose three faces are projections,
> subsuming the 54-effect VM + the ad-hoc token system + bespoke storage into one uniform algebra?*
>
> **Sources read in full this session and cited by `file:line`:** `REORIENT.md`,
> `CARRY-FORWARD-SYNTHESIS.md`, `GLOSSARY.md`, `EFFECT-ISA-DESIGN.md`, `GROUND-AUTH-ATTESTATION.md`,
> `GROUND-STORAGE-PROGRAMS.md`, `cand-A-vat-coalgebra.md`, `cand-B-witness-pca.md`,
> `cand-C-cap-distributed.md`, `cand-D-choreography.md`, plus the `pdfs/INDEX.md` clusters (coalgebra,
> algebraic effects, accumulation/folding, anonymous credentials, MPST/choreography, PCA, info-flow).
>
> **Discipline carried in (non-negotiable, from `REORIENT §6`):** crypto-soundness is *never* merged into
> the semantic law (the §8 rail); step-completeness is THE soundness question; no fake-to-pass; improve,
> don't degrade. Every "genuinely new" claim below is distinguished from a *rephrasing* of what exists.

---

## 0. The one-paragraph thesis

dregg has been built as an **effects machine** with auth and attestation bolted to its side. The session's
grounding shows that is a *projection mistake*: a turn is **one generator with three co-equal faces**
(`CARRY-FORWARD-SYNTHESIS §0`). dregg4's galaxy-brain rebuild is to make that literally true — to find the
**single coalgebraic generator** whose three faces (what the turn *does*, what it is *allowed* to do, what
it *emits*) are mathematical projections, parameterized by **two orthogonal dials** that today are pinned
or absent. The payoff is not "fewer effects." It is that **storage, advanced credentials, deniable
interaction, cross-chain bridging, and the whole token system stop being separate subsystems** and become
*instances* of one turn over a small core, narrowed by a caveat algebra, emitting an attestation whose
disclosure and transferability are chosen, not hardwired. The 54-effect VM + the macaroon/biscuit token
zoo + the bespoke `storage/` crate collapse into **one core + one algebra + one modal attestation lattice**.

---

## 1. The current sprawl, named precisely (so we know what we are collapsing)

Three independent sprawls, each grounded this session:

1. **Effect sprawl** — 54 selectors (`turn/src/action.rs:760`, `circuit/.../columns.rs:78`) that
   `EFFECT-ISA-DESIGN` shows are **~11 genuine shapes wearing ~50 names**: ≈24 of them are *one row*
   (`Meta.bind(domain_tag, hash)`) distinguished only by a constant (`EFFECT-ISA-DESIGN §S6`, `air.rs:909–1000`).
2. **Token/caveat sprawl** — a *parallel* authorization machine (macaroon HMAC chains, biscuit Ed25519
   chains, 3P discharge with ticket/VID, stealth one-time keys, StarkDelegation, credentials with selective
   disclosure + multi-show) living in `macaroon/`, `token/`, `credentials/`, `cell/src/stealth.rs`,
   `turn/src/executor/authorize.rs` — *separate* from the effect VM. ⚑ **The "Lean is a fiction exactly here"
   verdict (`GROUND-AUTH-ATTESTATION §1.6`: "no HMAC chain integrity," "3P discharge is a Bool flip,"
   "selective disclosure absent") is now STALE** — all three were built kernel-clean after this was written:
   HMAC chain integrity (`Authority/CaveatChain.lean`), real 3P-discharge ciphertext
   (`Authority/ThirdPartyDischarge.lean`), and selective disclosure (`Authority/SelectiveDisclosure.lean`).
   The *Lean-fidelity* gap of the caveat face is closed; the *crate-collapse* (one type for the zoo) remains
   design.
3. **Storage sprawl** — `storage/` (MerkleQueue, WAL, quota, erasure), `persist/` (redb), `rbg/vfs.rs`, and
   the `dregg-storage-templates/` migration. `GROUND-STORAGE §5` *already proves* storage is DSL-userspace
   over the effect core (every template is `SetField + EmitEvent + Transfer` under a `CellProgram`) — so
   this sprawl is *half-collapsed already*, and the residue (WAL durability) is honestly **below the ISA**.

**The unification claim of dregg4:** sprawls (1) and (2) are not two machines but **two faces of one turn**,
and (3) is **userspace over face (1)**. The current architecture pays for three machines; dregg4 pays for one.

---

## 2. The single generator — the turn as one coalgebraic object, three faces as projections

### 2.1 The functor, extended to carry all three faces

`cand-A §1.1` gives the cell as a point of the final coalgebra `νF`, `F X = Obs × (AdmissibleTurn ⇒ X)`.
That functor already *contains* the three faces — they were just not named as projections:

```
F X  =  Obs × (AdmissibleTurn ⇒ X)
        └┬┘    └──────┬───────┘
   ATTESTATION    the arrow's DOMAIN (CAVEATS) and CODOMAIN-action (EFFECTS)
```

- **EFFECTS = the codomain action.** `AdmissibleTurn ⇒ X` *maps to the successor cell* — the state
  transition. This is face 1, the `apply_*` mutation (`turn/src/executor/apply.rs`), the `cexec` of the
  step-complete spine (`Exec/StepComplete.lean: cexec_attests`).
- **CAVEATS = the domain restriction.** `AdmissibleTurn` is a *dependent, witness-guarded* alphabet
  (`cand-A §1.1`): a turn is in the domain iff it carries a witness discharging admissibility. **The caveat
  face IS the predicate that carves `AdmissibleTurn` out of `AllTurn`.** This is exactly the `CellProgram`
  as "the admissibility filter — which turns are admissible" (`GLOSSARY: CellProgram`, `cell/src/program.rs:53`).
- **ATTESTATION = `Obs`.** The badge — `(permitted) ∧ (effects-committed)` (`GLOSSARY: the badge`). The
  `WitnessedReceipt` (`turn/src/witnessed_receipt.rs:245`).

So the three faces are **literally** the three components of the coalgebra structure map `c : X → F X`:
*domain of the arrow* (caveats), *action of the arrow* (effects), *output component* (attestation). This is
not a metaphor — it is the decomposition of `F`. **dregg4's central rebuild is to treat `c` as the only
primitive and derive the three subsystems as its projections**, instead of building three subsystems and
hoping they agree.

> ⚑ **The spine this section rests on is REAL** (the abstract decomposition is sound, not just pretty): the
> executable kernel's `cexec` IS step-complete — every committed step attests the full `StepInv`
> (`Exec/StepComplete.lean: cexec_attests`:75, PROVED) — and the `CellProgram` denotation IS the executable
> coalgebra structure-map that cannot bypass conservation (`Exec/CellProgram.lean:6`, `denote_conserves`:113).
> The single remaining gap to "`c` as the only primitive" is honestly flagged in-code: a full
> `Boundary.TurnCoalg` *instance* over `CellProgram` is marked `OPEN` (`CellProgram.lean:19`) — the faces are
> proved-coherent *through* `cexec_attests`, but not yet packaged as one literal coalgebra object.

### 2.2 Why this is genuinely-new and not a rephrasing

`CARRY-FORWARD-SYNTHESIS §0` *names* the three faces; `cand-A` *names* the coalgebra. **Neither connects
them.** The new content here is the identification:

| Face | Coalgebra projection | Today (separate machine) | dregg4 (one projection) |
|---|---|---|---|
| effects | codomain action `⇒ X` | 54-selector EffectVmAir | small core ISA (the action's generators) |
| caveats | domain of the dependent arrow | macaroon/biscuit/discharge/credentials, *outside* the VM | the **predicate that defines `AdmissibleTurn`** |
| attestation | `Obs` component | WitnessedReceipt, pinned non-repudiable | a **modal `Obs`** indexed by the two dials |

The repudiation gap (`GROUND-AUTH §2`) is then *not* a missing feature — it is the observation that **`Obs`
has been built as a single global type** when the coalgebra permits it to be **a modal/indexed object**
(§4). The whole of Part 2 of `GROUND-AUTH` is "we pinned the `Obs` projection at one point of a lattice it
could range over." That reframing is the galaxy-brain move.

---

## 3. The unified type/algebra (the sketch)

Here is the maximally-general turn type. It is one generator; the three faces are its three fields; the two
dials parameterize the attestation field. (Lean-ish; not committed code.)

```
-- The TWO DIALS, first-class (today: disclosure is a per-field enum; transferability does not exist)
inductive Disclosure | acceptanceOnly | selective (reveal : Finset FieldId) | full
inductive Transferability | public | designated (verifier : VerifierId) | deniable (ring : Finset Authorizer)

-- FACE 1 (EFFECTS): the SMALL CORE — the action's generators (EFFECT-ISA-DESIGN §5, ~11 shapes)
inductive Core
  | balanceMove (asset : AssetClass) (from to : Option CellRef) (δ : Int)   -- C1, per-ASSET (the #1 gap)
  | supplyAdjust (asset : AssetClass) (cell : CellRef) (δ : Int) (disclosed : Bool)   -- C2
  | cellCreate (seed : CellSeed)                                            -- C3 (object generation = ana-seed)
  | capEdge (op : {add,remove,narrow}) (e : CapEdge)                        -- C4 (authority graph)
  | capExercise (slot : Slot) (inner : List Core)                          -- C5 (the eval map; recursive)
  | fieldWrite (idx : FieldId) (v : Value)                                  -- C6
  | metaBind (tag : DomainTag) (h : Hash)                                   -- C7 (subsumes ~24 selectors)
  | lifecycle (phase : Phase)                                              -- C8 (guarded FSM)
  | sideLock (rec : HoldingRecord) | sideSettle (id : LockId) (p : Predicate)  -- C9/C10
  | noteInsert (commit : Commit) | nullifierSpend (n : Nullifier) (w : Witness) -- C11/C12
  | nonceTick                                                              -- C13
  -- NEW CORE the architecture demands (EFFECT-ISA §3 ranked):
  | boundHalfEdge (peer : CellRef) (asset : AssetClass) (δ : Int) (exists : Witness)  -- CG-5 cross-cell
  | boundaryExport (slot : Slot) (φ : Attenuation) | boundaryImport (key : KeyCap)    -- ρ_out / ρ_in
  | returnProject (Δobs : ObsDelta) | awaitSettle (on : Predicate)         -- the 2nd observation / zkRPC
  | forkSpan (at : ReceiptId)                                              -- time-travel primitive

-- FACE 2 (CAVEATS): the ALGEBRA that narrows AdmissibleTurn (a bounded meet-semilattice / Heyting)
inductive Caveat
  | first (p : AuthContext → Bool)         -- macaroon first-party: a narrowing predicate
  | thirdParty (gw : GatewayId) (cid vid : Ciphertext)   -- 3P discharge: ENCRYPTED ticket/VID (real crypto)
  | bindParent (tailHash : Hash)           -- bind-to-parent (the chain-integrity binding)
  | predicate (k : WitnessedKind) (stmt : Stmt)   -- Gte/Lte/InRange/BlindedSet (selective-disclosure proofs)
structure CaveatChain where
  root  : KeyRef                            -- biscuit (pubkey) | macaroon (HMAC) | sel4-reflected
  tail  : Hash                              -- Tᵢ = H(Tᵢ₋₁, encode(Cᵢ))  -- THE chain integrity, modeled
  links : List Caveat
-- meet (attenuation): chain extension is append-only, narrowing-ONLY (the keystone law)
def CaveatChain.attenuate (c : CaveatChain) (k : Caveat) : CaveatChain := ⟨c.root, H(c.tail, enc k), c.links ++ [k]⟩

-- FACE 3 (ATTESTATION): the MODAL Obs, indexed by the two dials (today: a single global type)
structure Attest where
  permitted : Proof                         -- de-jure: a CDT/caveat-chain derivation witness
  committed : ObsDelta                       -- de-facto: per-asset CONSERVATION_VECTOR + Obs advance
  disclosure : Disclosure                    -- WHAT is revealed
  transfer   : Transferability               -- TO WHOM it is convincing  ← the new axis

-- THE ONE TURN: one generator, three faces.
structure Turn where
  effects  : List Core                       -- face 1
  guard    : CaveatChain                      -- face 2 (defines membership in AdmissibleTurn)
  attest   : Disclosure × Transferability     -- face 3 dials (the Obs the commit emits is computed)
```

### 3.1 What collapses into uniformity (genuine collapse, not relabeling)

> ⚑ **LANDED (REAL, no longer a fiction).** Everything this bullet calls "today an overlook / a `Bool` flip"
> is now built kernel-clean in `metatheory/Dregg2/Authority/`:
> - the **HMAC tail** is `Chain.tail` with the exact Rust recurrence `Tᵢ = mac Tᵢ₋₁ encode(Cᵢ)`
>   (`CaveatChain.lean: replayTag`:132, `replayTag_append`:184); verification is replay-and-compare
>   (`verify_iff_wellTagged`:168, `honest_chain_verifies`:204) — REAL.
> - **attenuation narrows** holds on the *chain* (`append_narrows`:223, `append_subset`:232), and the chain
>   bridges back to the proven token narrowing (`chainToken_admits`:257) — REAL.
> - **3P discharge carries real ciphertext** (ticket/VID two-key split): `ThirdPartyDischarge.lean`
>   `ThirdPartyCaveat`:124, `accepts_iff`:246, `stale_discharge_rejected`:304, `cross_bound_rejected`:333 — REAL.
>   (The crypto-unforgeability premises are honestly `§8`-portal `Prop`-carriers, never claimed as theorems —
>   `ThirdPartyDischarge.lean:46,89`.)
>
> *Still DECORATIVE in this bullet:* the **single unified `CaveatChain` over three `KeyRef` roots** (one type
> replacing `macaroon/`+`token/`+the CDT). The Lean `Chain` is generic over its key type but the three roots
> (HMAC / Ed25519 / sel4-handle) are not yet one indexed root object — that collapse is design, not code.

- **The token zoo → the caveat-chain algebra.** macaroon (`root = HMAC`), biscuit (`root = Ed25519`),
  sel4-reflected (`root = kernel handle`) are **one `CaveatChain` over three `KeyRef` roots** — exactly
  `cand-C §10`'s "the biscuit delegation graph ≡ the distributed CDT." The HMAC tail is now modeled
  (`Authority/CaveatChain.lean`, REAL — the `GROUND-AUTH §1.6` overlook is **closed**, not open); attenuation
  narrows on the chain (`append_narrows`, REAL) as well as on the base token (`Authority/Caveat.lean`).
  3P discharge is no longer a `Bool` flip — it is `ThirdPartyCaveat` carrying real ciphertext
  (`Authority/ThirdPartyDischarge.lean`, REAL).
- **Storage → DSL-userspace over the core** (already shown, `GROUND-STORAGE §5`): every template is
  `fieldWrite + metaBind + balanceMove` under a `CellProgram`; the one primitive it needs (the
  holding-store) is `sideLock/sideSettle`, already in the core for escrow (FID-ESCROW).
- **The ~24 passthrough effects → one `metaBind(tag, hash)`** (`EFFECT-ISA §S6`/`§5 Phase R`).
- **checkpoint/restore/replay/time-travel → consequences of the codata + `forkSpan`** (`cand-A §5`), not
  effects.

### 3.2 What genuinely generalizes (new capability, not collapse)

> ⚑ **TWO of these four LANDED since this was written** — fold the frontier forward:

- **Per-asset conservation** (`balanceMove`/`supplyAdjust` indexed by `AssetClass`) — was the #1 soundness
  gap (`EFFECT-ISA §3.1`); **now REAL.** Conservation is a per-`AssetId` *family*, proved on the abstract
  kernel (`Exec/MultiAsset.lean: maExec_conserves_per_asset`:131, with the cross-asset frame lemma
  `maTransfer_untouched`:120), on the **live record executor** (`Exec/TurnExecutorFull.lean` /
  `RecordKernel`: `recKExecAsset_conserves_per_asset`), and **over the whole forest tree**
  (`Exec/FullForest.lean: execFullForestA_conserves_per_asset`:224, `#assert_axioms`-pinned:421). The
  single-scalar `bal` is no longer the only model. **REAL.**
- **The transferability dial** — was billed "*entirely* new / grep-confirmed zero"; **now REAL and built.**
  `Authority/DesignatedVerifier.lean` ships the dial (`TransferDial`:146, `dialHolds`:157) with both
  endpoints inhabited and separated (`dial_endpoints_distinct`:346), plus the named-new verifier-indexed
  discharge `DischargedFor`:113 and the repudiation theorems (`designated_is_deniable`:224,
  `repudiation_no_third_party_evidence`:246). The *simulator-indistinguishability* of a real DV scheme is an
  honest `§8` class-field obligation (`DesignatedVerifier.lean:97`), never claimed as a Lean theorem. **REAL.**
- **`returnProject` / `awaitSettle`** — still **ASPIRATIONAL as named primitives** (zero `returnProject`/
  `awaitSettle` Lean objects). What *does* exist is the await/promise substrate they would ride on:
  `Await.lean` (`one_shot_is_static`:138, `commit_resumes_once`:312, `four_faces_unify`:426) and
  `Spec/Await.lean` (`pipeline_topological`:393). The bidirectional zkRPC effect itself is unbuilt.
- **`forkSpan`** — **ASPIRATIONAL** (grep: zero `forkSpan` hits anywhere in `Dregg2/`). `Spawn` is
  child-creation, not self-fork (`EFFECT-ISA §3` #5). Genuinely unbuilt.

---

## 4. The two dials, taken to the limit (the heart of dregg4)

This is where the "maximally-general" claim earns its keep. The session found the system has **a disclosure
dial and a missing transferability dial** (`CARRY-FORWARD-SYNTHESIS §2 Face 3`). dregg4 makes both
first-class *and orthogonal*, and recognizes a **third latent dial**.

### 4.1 Dial 1 — Disclosure (what-is-revealed): already partly built, generalize it

Today: `FieldVisibility::{Public, Committed, SelectivelyDisclosable}` (`cell/src/state.rs:16-25`) +
presentation `disclose` (`presentation.rs:36`). The generalization: lift disclosure from a *per-field cell
attribute* to a **per-turn, per-face choice** — a turn may disclose its full effect list, only a commitment
to it, or a predicate over it (`Gte/Lte/InRange`, `presentation.rs:307-351`).

> ⚑ **The Lean already grew (REAL).** The doc's ask — "grow `VC.claim` from one opaque `Nat` to a record with
> a revealed subset + a Poseidon2 revealed-facts commitment" — is **built** in
> `Authority/SelectiveDisclosure.lean`: `Credential n`:134 + `Presentation`:177 carry a disclosure mask
> (`presentation.rs:259-265`) and a `revealed_facts_commitment` field; the hiding/teeth theorems are real and
> kernel-clean — `presentation_hides_undisclosed`:239, `disclosed_slot_is_revealed`:260,
> `predicate_proof_has_teeth`:298, `multishow_unlinkable`:326, `multishow_blinding_invisible`:341. The
> *circuit-level* soundness of the commitment/predicate stays an honest portal, but the disclosure **model**
> is no longer "one opaque `Nat`." **REAL.** (`Authority/Credential.lean` still carries the older opaque
> `claim` for the legacy VC path; the new selective-disclosure model lives in the dedicated module.)

### 4.2 Dial 2 — Transferability (to-whom-convincing): the genuinely-new axis

> ⚑ **NO LONGER MISSING — this is the doc's single biggest drift.** When written, `GROUND-AUTH §2.2(b)(c)`
> grep-confirmed zero. **It has since been built**, kernel-clean, in `Authority/DesignatedVerifier.lean`:
> the `DVKernel` interface:84, the verifier-indexed discharge `DischargedFor V stmt proof`:113, the two
> realized endpoints `Transferable`:129 / `DesignatedFor V₀`:138, the dial `TransferDial`:146 with semantics
> `dialHolds`:157, and the teeth: `public_convinces_any_third_party`:176, `designated_convinces_V0`:196,
> `designated_not_transferable`:206, `designated_is_deniable`:224, `repudiation_no_third_party_evidence`:246,
> `designated_excludes_public`:257, and a witnessed reference kernel proving the endpoints are inhabited and
> separated (`dial_endpoints_distinct`:346). So §4.2 is now a **report on built code**, not a proposal — the
> `deniable(ring)` *third* point is the only one still unbuilt (the doc's "smallest delta"). **REAL** for
> `public`/`designated`; **ASPIRATIONAL** for `deniable(ring)`.

`GROUND-AUTH §2.2(b)(c)` is conclusive: **zero deniability, zero designated-verifier, hardwired maximal
transferability.** dregg4 introduces `Transferability ∈ {public, designated(V), deniable(ring)}` as a
*modal index on `Obs`*. The three points:

- **`public`** — the existing universally-verifiable STARK/Ed25519 badge. **Required** on the consensus /
  proof-carrying-forest path (`GROUND-AUTH §2.3`: finality *depends* on transferability). This is the
  default and the only point the system has today.
- **`designated(V)`** — a designated-verifier ZK proof of `(turn authorized) ∨ (I know V's secret)`
  (`GROUND-AUTH §2.4(1)`). Convincing *only* to V (who knows they didn't forge it); worthless to relay.
- **`deniable(ring)`** — a ring/chameleon construction: "one of this set authorized; you can't prove which,
  and any of us could have forged it" (`GROUND-AUTH §2.4(3)`). The weakest, smallest delta — the BlindedSet
  anonymity-set machinery (`credentials/src/presentation.rs:176`) is the only stepping stone.

**The galaxy-brain unification:** these are *modalities on the same `Obs` object*. `Obs` becomes
`Obs[t : Transferability]`, and the soundness keystone lifts to a **verifier-indexed bisimulation**:
`Discharged` stops being one universal predicate and becomes `Discharged[V]` (`GROUND-AUTH §2.4` close:
"indexing it by *which verifier* is convinced — a genuinely new piece of theory").

> ⚑ **Both halves of this paragraph LANDED.** (1) The verifier-indexed predicate is built: not just
> `Discharged[V]` as a wish but `DischargedFor V`:113 in `DesignatedVerifier.lean`, with
> `publicMode_collapses_to_universal`:186 proving `public ↔ ∀V, DischargedFor V` — the exact "single universal
> verdict is one point of the index" reframing. **REAL.** (2) The keystone `sound_of_step_complete` named here
> (`Boundary.lean`, `cand-A §8`) was found **ill-posed and RETIRED** (`Boundary.lean:158,194`); it is recovered
> *honestly* as a bisimulation-to-oracle on the concrete executable living cell —
> `Exec/Cell.lean: bisim_of_oracle`:61 and `livingCell_sound`:102. So the "lift the keystone to a
> verifier-indexed bisimulation" program now has a *real* base keystone to lift (the verifier-indexed lift
> itself is still future work — `DischargedFor` is built, but it is not yet threaded through `livingCell_sound`).

The same turn, committed, can emit **two attestations at once**: a `public`
badge for the forest, and a `designated(V)` companion for the bilateral channel (`GROUND-AUTH §2.4` final:
"the consensus/forest path keeps the transferable badge; the new mode is a parallel private artifact").

### 4.3 Dial 3 — the LATENT third dial: Finality / agreement-strength (surfaced here, not yet considered)

There is a **third orthogonal axis hiding in plain sight**: the finality tier (`GLOSSARY: finality tiers`,
`cand-A §7`). Today it is a per-cell property, but structurally it is *exactly the same shape as the two
dials* — a choice on the attestation about **how strongly the world must agree this turn is the history**.
- disclosure = *what* the badge reveals,
- transferability = *to whom* the badge is convincing,
- **agreement = *how many* must concur it is canonical** (tier-1 causal → tier-4 constitutional).

Naming this as a *third dial on `Obs`* is, I believe, **new** — none of the candidates or grounding docs
put finality on the same footing as disclosure/transferability. It fits the model cleanly: the three dials
are the three honest judgements of `cand-A §1.3` / `GLOSSARY: three orthogonal judgements` re-projected onto
the attestation face (conservation lives in `committed`; ordering = the agreement dial; I-confluence = the
*eligibility precondition* for low agreement, just as it gates tier-1). **A turn's full attestation is a
point in a 3-cube** `Disclosure × Transferability × Agreement`, and the system today lives on one edge of it.

---

## 5. The deeper single generator — is there ONE object behind the three faces?

> ⚑ **DECORATIVE (vocabulary, not a Lean object).** Grep-confirmed: `Comodel`/`comodel` appears ONLY in three
> prose comments (`HandlerTransformer.lean:118` and `:128`, `Claims.lean:538`), and there is **zero**
> `Lens` / `get_put` / `put_get` / `getPut` object anywhere in `Dregg2/`. `HandlerTransformer.lean:128` is
> explicit that the `Handler → comodel-morphism` reading is "the unbuilt comodel-morphism the docs flag
> ASPIRATIONAL; here we work directly with `act`." So all of §5 is **aesthetic framing / a research target**,
> *not* a built construction. What is REAL underneath the metaphor is the coalgebraic *bisimulation-to-oracle*
> spine (`Exec/Cell.lean: livingCell_sound`:102, `bisim_of_oracle`:61) and the handler/sheaf gluing
> (`HandlerTransformer.lean: proofForest_sheaf_sound`:386, `#assert_axioms`-pinned:453) — the lens/comodel
> names are a *reading* of those, never a Lean `structure Lens`/`structure Comodel`.

Yes, and it has a precise categorical name. The three faces are projections of a **dependent-lens / Moore
coalgebra**, and the cleaner statement is in terms of **comodels of an effect theory** (the algebraic-effects
line: `pdfs/handlers-of-algebraic-effects-plotkin-power`, `monadic-framework-delimited-continuations`).

### 5.1 The turn is a (dependent) lens; the three faces are its two halves + a guard

A lens `S ⇄ (P, U)` has a *get* (`S → P`, the view) and a *put* (`S × U → S`, the update). The turn is a
**dependent lens with a guarded domain**:
- **get = the attestation** (`Obs`, the view that crosses the boundary),
- **put = the effects** (the state update),
- **the domain of `put` = the caveats** (which updates are admissible).

This is *literally* the coalgebra of §2.1 written as a lens: `c : X → Obs × (AdmissibleTurn ⇒ X)` is
`(get, put-with-guarded-domain)`. The three faces are **not three things glued; they are the components of
one lens.** This matters because lenses *compose* — `capExercise` (`C5`, the recursive eval map,
`apply.rs:2441`) is exactly **lens composition**: exercising a cap runs an inner turn (inner lens) inside the
outer turn's put. The "recursive inner-effect gating" the circuit must bake (`EFFECT-ISA §C5`) is the
*compositional* structure of the lens, not a special case.

> ⚑ **DECORATIVE.** There is no `Lens` Lean object and no `get`/`put` pair in `Dregg2/`; "the turn is a
> dependent lens" is a *reading*, not a construction. The recursive inner-effect gating it describes IS
> built, but as the executor's recursive transactional descent over the tree
> (`Exec/FullForest.lean: execFullForestA`:113 / `execFullChildrenA`:122, mutually recursive), proven to be
> `execFullTurnA` over the pre-order lowering (`execFullForestA_eq_execFullTurnA`:171) — that bridge, not a
> lens-composition law, is what makes "the recursive gating is not a special case" REAL.

### 5.2 The comodel reading (the await/effect duality, made one)

`cand-A §3` already found the sharp fact: **continuations are the one non-algebraic effect** (Plotkin-Power),
so the await substrate is *two layers* (a gate-engine = algebraic handler + a delimited-continuation capture).
The deeper unification: **the cell is a comodel** (the dual of a model of an algebraic theory) of the effect
theory whose operations are the `Core` generators. A comodel is precisely "a machine that *responds* to
operations" — i.e., a coalgebra for the functor induced by the theory. So:
- the **effect signature** (the `Core` enum) is an *algebraic theory* `T`,
- the **cell** is a `T`-**comodel** (it *cohandles* effect operations against its state),
- the **turn** is one step of cohandling = the coalgebra structure map,
- the **caveats** are the *equations/guards* of the theory (which operation-applications are well-formed),
- the **attestation** is the *residual* the comodel emits (the Moore output).

This is the single object: **a guarded comodel of the effect theory, with a modal output.** It subsumes
cell-and-morphism (the `cand-A §1.2` "two co-primary primitives" tension) because a comodel *is* a coalgebra
— the morphism is the structure map, not a second object. (`pdfs/coalgebraic-semantics-silva` is the
grounding for "behaviour = coalgebra, equivalence = bisimulation.")

> ⚑ **DECORATIVE wrapper over a REAL core.** "The cell is a `T`-comodel" has no Lean witness (zero `Comodel`
> objects). But the operative claim it dresses — "behaviour = coalgebra, equivalence = bisimulation" — IS
> realized: the executable cell is a coalgebra (`Exec/Cell.lean`'s `TurnCoalg`-shaped unfold) bisimilar to its
> conservation oracle from every state (`livingCell_sound`:102, via `bisim_of_oracle`:61, kernel-recovered
> from the retired `sound_of_step_complete`). The "two co-primary primitives" tension is dissolved *in code*
> by that single coalgebra, exactly as the prose claims — just without a `comodel` type carrying it.

### 5.3 Why this is more than aesthetics (what it buys)

- **One soundness theorem, not three.** Instead of "effects conserve ∧ caveats narrow ∧ attestation binds"
  as three audits, soundness is *one* statement: the comodel is bisimilar to the golden-oracle comodel,
  with `StepInv` as the contractivity condition (`cand-A §4`). The three faces are conjuncts of `StepInv`
  *because* they are the three components of `c` — they cannot drift apart by construction.
- **Composition is free.** Lens/comodel composition gives `capExercise`, JointTurn (`⊗` of comodels,
  `GLOSSARY: JointTurn`) — and the reason the comodel tensor needs the CG-2⊗CG-5 binding as a hypothesis is
  **corrected** in live Lean: ~~"non-finality of `νF₁⊗νF₂`"~~ was **mis-stated** (the product of two final
  coalgebras IS final for the product functor). The true, soundness-critical fact is that joint-admissibility
  is a **proper subobject** of the product — `JointTurn.binding_is_proper`:333 (PROVED: a concrete product
  state the CG-5 binding *excludes*, `1+1=2≠0`), N-ary `Hyperedge.hyper_binding_is_proper`:164
  (`#assert_axioms`-pinned:532). REAL. And choreography projection (`cand-D`: a functor
  `Choreo → ∏ Endpoint`) is realized as `Coordination.projection_sound`:416 (PROVED). Lens/comodel as the
  *name* for this composition stays DECORATIVE; the proper-subobject obstruction it gestures at is REAL.
- **The dials are modalities on the output functor.** `Obs[t]` is `F` post-composed with a modality; the
  whole transferability theory becomes "lift the bisimulation through the modality," which is a known shape.

---

## 6. Advanced features / galaxy-brain rethinks for dregg4 (each with three-faced-turn fit + build cost)

Each entry: **what it is**, **the three-faced fit**, **new-vs-rephrase**, **build cost**.

### 6.1 The 3-cube attestation modality (`Disclosure × Transferability × Agreement`)
- **Fit:** the attestation face becomes a point in a 3-cube; the turn carries a target cube-point; commit
  emits the badge(s) realizing it. A single turn can emit *multiple* badges (public for the forest,
  designated for a peer).
- **New vs rephrase:** disclosure REAL (`Authority/SelectiveDisclosure.lean`); transferability **now REAL too**
  (`Authority/DesignatedVerifier.lean`, the doc's "new" since landed); putting agreement on the same footing
  as a *dial* is **still ASPIRATIONAL** (§4.3 — no Lean object on the attestation cube).
- **Build:** ~~verifier-indexed `Discharged[V]`~~ **DONE** as `DischargedFor V`:113 (the named-new theory,
  kernel-clean); remaining is the DVZK *companion circuit* (OR of presentation-AIR + Schnorr-knowledge,
  `GROUND-AUTH §2.4(1)`) and threading the index through `livingCell_sound`. Keep the public badge for finality.

### 6.2 Designated-verifier & deniable interaction as a parallel private artifact
- **Fit:** transferability=`designated/deniable` on the attestation; the *effects and caveats are unchanged*
  — only the `Obs` projection changes. This is the cleanest demonstration that the dials are orthogonal to
  the other two faces.
- **New vs rephrase:** ⚑ **was "genuinely new, zero exists"; the `designated` half is now BUILT** in
  `Authority/DesignatedVerifier.lean` (`DesignatedFor`:138, `designated_is_deniable`:224,
  `repudiation_no_third_party_evidence`:246, `dial_endpoints_distinct`:346 — REAL, kernel-clean). The
  **repudiation gap** the session flagged is *closed in the Lean model*; the `deniable(ring)` point and the
  live-channel artifact remain ASPIRATIONAL.
- **Build:** ~~the Lean DV model~~ **DONE**; remaining = DVZK circuit (medium); deniable MAC at the
  `captp/handoff.rs` layer for the live channel (`GROUND-AUTH §2.4(2)`); ring-signature companion reuses
  BlindedSet (`§2.4(3)`, smallest delta) — `Crypto/BlindedSet.lean` exists as the stepping stone.

### 6.3 The caveat chain AS the CDT AS the strand log (one append-only object, three renderings)
- **Fit:** caveat face = the domain guard; `cand-C §10` establishes biscuit-chain ≡ CDT ≡ blocklace strand.
  dregg4 makes this *one type* (`CaveatChain` with a `KeyRef` root) rather than three crates
  (`macaroon/`, `token/`, the CDT in `cell/`).
- **New vs rephrase:** mostly **collapse** (the identity is known). ⚑ **The "new in Lean" part — modeling
  the HMAC tail integrity — has LANDED:** `Authority/CaveatChain.lean` carries `tail`:119 and the exact
  recurrence `Tᵢ = mac Tᵢ₋₁ encode(Cᵢ)` (`replayTag_append`:184), with verify-as-replay-compare
  (`verify_iff_wellTagged`:168). The `GROUND-AUTH §1.6 #1` hole is **closed**, not "unflagged §8."
- **Build:** ~~add `tail : Hash` + the recurrence~~ **DONE**. Remaining: the *removal-resistance* theorem
  ("an adversary cannot remove a caveat") still rests on a `MacUnforgeable`-style premise (`CaveatChain.lean`
  states it as a `Prop`-carrier / honest §8 reduction premise near :267-276, never as a Lean theorem — the
  one-way-function assumption is correctly *not* internalized).

### 6.4 Effects-as-comodel-of-a-theory: a USER-EXTENSIBLE effect ISA
- **Fit:** if the core is *the algebraic theory* `T`, then a verified app can **extend `T`** with new
  operations + equations and ship a *comodel-homomorphism proof* that its extension refines the core. This
  is the principled version of `Effect::Custom` / `CellProgram::Cases` — instead of a `Bool` escape hatch,
  a new effect is a theory extension with a proof obligation.
- **New vs rephrase:** **new** — today `Custom` is an untrusted predicate (`GROUND-STORAGE §5` warns
  "moved-complexity unless the DSL is itself verified"). A theory-extension-with-refinement-proof is the
  *verified* version of userspace effects. ⚑ **Still ASPIRATIONAL** (no extension calculus / comodel-morphism
  Lean object).
- **Build:** the hard part; needs the `CellProgram` law proved first (`REORIENT §5`), then an extension
  calculus. ⚑ **The blocking `CellProgram` law LANDED** (`Exec/CellProgram.lean`: `denote_conserves`:113 —
  a developer-authored `CellProgram` provably cannot bypass conservation; `denote_eq_exec_on_success`:101).
  So the precondition is met; the *extension calculus* (refinement-proof obligation for a new operation)
  is the genuinely-research-grade item that remains.

### 6.5 The unified await/return as the second leg of the lens (zkRPC, native)
- **Fit:** `returnProject` is the *get* of a backward lens; `awaitSettle` is the caller's resumption gate.
  Forward turn + return projection = a **bidirectional lens** = an agent calling a tool and getting a
  proof-carrying result (`cand-A §2.2`, `EFFECT-ISA §3` #4).
- **New vs rephrase:** **new as a typed effect** (today `PipelinedSend` is a near-noop, `EFFECT-ISA §S10`).
  Still **ASPIRATIONAL** — no `returnProject`/`awaitSettle` Lean object.
- **Build:** one-shot (linear) continuation typing so conservation falls out (`cand-A §3`); the settled-call
  await face (`GLOSSARY: await family`). ⚑ **The substrate already exists** (so this is closer than the doc
  implies): `Await.lean` proves one-shot continuation typing (`one_shot_is_static`:138,
  `runtime_guard_rejects_reuse`:199, `commit_resumes_once`:312) and unifies the four await faces
  (`four_faces_unify`:426); `Spec/Await.lean` proves promise-pipeline topological ordering
  (`pipeline_topological`:393). The missing piece is *only* the bidirectional return-effect on top.

### 6.6 Checkpoint/fork/time-travel as theorems + `forkSpan` as the *only* new structural primitive
- **Fit:** the codata + retained log give checkpoint/restore/replay as *consequences* (`cand-A §5`);
  `forkSpan` (a span/pushout, **not** a coproduct, `cand-A §6`) is the one primitive time-travel needs.
- **New vs rephrase:** **mostly theorems** (rephrase of codata); `forkSpan` is a **new** primitive.
- **Build:** ⚑ **the living cell LANDED** (`REORIENT §5`'s precondition is met): `Exec/Cell.lean: livingCell`
  + `livingCell_sound`:102, and checkpoint/restore/replay are now theorems over a genuine **distinct
  `Snapshot` token** (`Exec/Cell.lean: Snapshot`:122, `restore`:137, `restore_snapshot`:144;
  `Exec/CellRuntime.lean: checkpoint_restore_roundtrip`:60, badge-survival `checkpoint_restore_obs`:70,
  `replay_from_checkpoint`:87). The file's own note flags it *replaced* the old vacuous `checkpoint := id`.
  Honest nuance: the round-trip is still `rfl`, but now over a *meaning-bearing* token carrying
  `headObs`/`kernel`/`log` — so the badge-survival/replay theorems say something the types don't force.
  The remaining piece is `forkSpan` itself — still **ASPIRATIONAL** (grep: zero `forkSpan` hits) — the span
  with hand-proved attenuation+conservation merge laws (`cand-A §6`).

### 6.7 The recursion/accumulation backend as a swappable modality (defer perf, keep soundness)
- **Fit:** aggregation of step-proofs into a forest (`circuit/src/proof_forest.rs`) is **not an effect** —
  it is the JointTurn/finality layer above the ISA (`EFFECT-ISA §3`). The folding-scheme literature
  (`pdfs/`: nova/protostar/hypernova/latticefold/halo-infinite-accumulation) is *exactly* the swappable
  `RecursionBackend` (`GLOSSARY: RecursionBackend`, never an `additive_combine` method).
- **New vs rephrase:** **rephrase** — the architecture already says recursion is deferrable and behind a
  trait. dregg4's contribution is to make the trait a **modality on the attestation** (succinct-history
  badge vs leaf badge) rather than a circuit detail.
- **Build:** keep FRI/BabyBear leaf; the PQ recursion swap (latticefold target) is the deferred perf item.

### 6.8 Accountable anonymity: the de-jure/de-facto split as a FOURTH face? (surprising)
- **Fit:** `cand-C §0`/`GLOSSARY: the badge` insist permission (de-jure) ≠ authority (de-facto); the badge
  attests permission, the *log* carries authority. The anonymous-credential literature on **accountable
  anonymity + auditable revocation** (`pdfs/towards-accountability-for-anonymous-credentials`,
  `publicly-auditable-privacy-revocation-anoncreds`) suggests a *fourth projection*: an **escrowed
  de-anonymization capability** — anonymity that an authorized auditor can lift under a turn (itself
  attested). This is the "anonymous-collaboration-OS that still has accountability" story.
- **New vs rephrase:** **new** — neither the candidates nor the grounding propose accountable-anonymity as a
  modeled face. It fits as a *second transferability-like dial on the anonymity*: who (if anyone) can
  later open the pseudonym, gated by a capability.
- **Build:** an escrow-key + a non-membership/opening circuit; the revocation non-membership seam
  (`cand-C §6`, `pdfs/private-delegation-nonmembership-proof-updates-accumulators`) is the same machinery.

### 6.9 Storage durability as an honest below-the-ISA portal (kill the `rfl` fiction)
- **Fit:** WAL/redb crash-safety is **not** a face — it is infrastructure below the turn (`GROUND-STORAGE §4`).
  dregg4 models it as a **crash/recovery portal** with a `replay = pre-crash-state` theorem, *not* as the
  `CellRuntime` `restore∘checkpoint = rfl` label-fiction (`GROUND-STORAGE §3` "sharpest fiction risk").
- **New vs rephrase:** **new (honesty)** — replaces a vacuous theorem with a real crash model.
- **Build:** a log + fault-point + replay-equals-pre-crash theorem (`GROUND-STORAGE §4` #2). ⚑ **PARTIAL
  progress (honesty improved, the deeper ask still ASPIRATIONAL):** the `restore∘checkpoint = rfl`
  *label-fiction* is gone — `Exec/Cell.lean`/`Exec/CellRuntime.lean` rebuilt it over a distinct `Snapshot`
  token with badge-survival + replay-determinism theorems (`checkpoint_restore_obs`:70,
  `replay_from_checkpoint`:87) — so it is no longer a pure `id`-tautology. **But** the doc's actual target —
  a *crash/recovery portal with a fault-point and `replay = pre-crash-state`* — is **not built** (no WAL/fault
  model in `Dregg2/`). The fiction is upgraded to an honest snapshot theorem; the crash model remains future.

### 6.10 Choreography as the modal front-end (the syntactic spine, `cand-D`)
- **Fit:** a global type `G` is a *diagram in the turn-category*; projection is a *functor to comodels*; the
  monitor *is* the vat-boundary verifier; blame *is* the de-jure/de-facto split (`cand-D §2`). The three
  judgements become one annotated `G` (`cand-D §1`).
- **New vs rephrase:** **rephrase + deferred** — `cand-D` already designs this; dregg4 just notes it is "the
  modal front-end whose back-end is the unified turn," built last (`cand-D §8`).
- **Build:** last; rests on open theorems (Byzantine-EPP-by-monitoring, `cand-D §7`).

---

## 7. What dregg4 *means* as a clean rebuild, given everything learned this session

Four findings reshape the rebuild target:

1. **De-vacuification** (the swarm caught ~4 false-as-stated theorems; `REORIENT §6`, tasks #107–#114): the
   rebuild must state the three faces as *non-vacuous* conjuncts of one `StepInv`. ⚑ **Realized (REAL, even if
   "comodel" stays a name):** vacuity is structurally hard because a face that did nothing fails the
   *bisimulation-to-oracle* (`Exec/Cell.lean: livingCell_sound`:102), and the de-vacuification tasks
   themselves landed — e.g. genuine `granted ≤ held` non-amplification on real rights (#110/#112,
   `execFullForestA_no_amplify`:251), the corrected proper-subobject obstruction (#114's audit →
   `binding_is_proper`:333). The CI guard now *forbids* `sorry` (task #128).
2. **Fidelity grounding** (`GROUND-AUTH`/`GROUND-STORAGE`): "carry the Rust semantics, not a Lean fiction."
   ⚑ **Largely DONE for the caveat face:** it now carries the *real* HMAC chain (`Authority/CaveatChain.lean`,
   REAL), real 3P-discharge ciphertext (`Authority/ThirdPartyDischarge.lean`, REAL), and real selective
   disclosure (`Authority/SelectiveDisclosure.lean`, REAL) — each modeling the cited `*.rs` semantics with the
   crypto-unforgeability premises kept as honest §8 portals, never `Bool`. **Still open** for the storage
   face: the *real WAL/crash model* is unbuilt (§6.9) — only the snapshot round-trip is de-fictionalized.
3. **The ISA reshape** (`EFFECT-ISA`): the effect face is ~11 shapes, not 54 names; the rebuild starts from
   the small core + the named-new primitives (per-asset, half-edge, ρ_in/ρ_out, return, fork).
4. **The repudiation gap** (`GROUND-AUTH §2`): the attestation face is a *single point* of a lattice it
   should range over. dregg4 *is* the system where attestation is modal.

So **dregg4 = one guarded comodel of a small effect theory, emitting a modal attestation, with caveats as
the theory's guards and the two-(three-)dial lattice as the attestation's modality** — and storage,
credentials, deniable interaction, cross-chain, and choreography are all *instances*, not subsystems. dregg2
(the current target, `CARRY-FORWARD-SYNTHESIS §4`) is the faithful three-face kernel; dregg4 is its
*generalization to the full modal lattice with a user-extensible theory*.

> ⚑ **Status of that one-sentence vision against live Lean (2026-06-02):** the *guarded comodel* phrasing is
> DECORATIVE (no `Comodel`/`Lens` object), but every *operative* piece it names is now REAL in `Dregg2/`: the
> guarded coalgebra with bisimulation soundness (`livingCell_sound`), the caveat guards carrying real
> HMAC/3P/selective-disclosure crypto (`Authority/{CaveatChain,ThirdPartyDischarge,SelectiveDisclosure}`), the
> per-asset conservation vector on the executor and whole tree (`MultiAsset`/`FullForest`), and **two of the
> three dials** of the modal attestation (disclosure + transferability via `DesignatedVerifier`). What stays
> ASPIRATIONAL: the **agreement** dial as a first-class attestation index (§4.3), the **user-extensible
> theory** extension calculus (§6.4), `forkSpan`/`returnProject` as primitives, the accountable-anonymity 4th
> face (§6.8), and the genuinely-OPEN **forest-delegation handoff** — `Exec/FullForest.lean: execFullChildrenA`:124
> still *discards* each edge's delegation triple (`⟨_,_,_,sub⟩`), running children against unchanged authority
> state, so cross-cell no-amplify is vacuous on execution (the #138 gap; the faithful fix routes edges onto
> `recKDelegateAtten`). The vision is *more than half realized in code*, not just designed.

---

## 8. Honest bounds (design around these; do not "fix")

- **The public badge cannot be dropped from the forest path** (`GROUND-AUTH §2.3`): transferability is
  load-bearing for finality. The deniable/designated modes are *companions*, never replacements there.
- ~~**`νF₁ ⊗ νF₂` is not final**~~ ⚑ **CORRECTED in live Lean — this bound is mis-stated.** The product of
  two final coalgebras IS final for the product functor; the retired `tensor_not_final` is false
  (`JointTurn.lean:322-329` documents the correction). The *true* irreducible bound is a **proper-subobject**
  fact: joint-admissibility (CG-2⊗CG-5 binding) carves a proper equalizer subobject out of the product, so
  cross-cell soundness genuinely exceeds per-cell × per-cell and the binding must be hypothesized, not
  derived — `JointTurn.binding_is_proper`:333 (PROVED), N-ary `Hyperedge.hyper_binding_is_proper`:164
  (`#assert_axioms`-pinned). The conclusion the doc draws (the parallel/JointTurn tensor carries the binding
  as a premise) is **right**; only the *reason* ("non-finality") was wrong. REAL bound, correctly stated.
- **No unconditional IVC** (`cand-A §2.4`): depth = security parameter; the accumulation modality (§6.7) is
  bounded.
- **User-extensible effects (§6.4) need the `CellProgram` law proved first** — ⚑ **that precondition partly
  LANDED:** `Exec/CellProgram.lean` proves a `CellProgram` cannot bypass conservation
  (`denote_conserves`:113) and that its denotation equals `exec` on success (`denote_eq_exec_on_success`:101).
  So the *base* law exists; the missing piece is the *extension calculus* (theory-extension-with-refinement
  proof), still the research-grade item, correctly last.
- **Revocation has a recency floor under partition** (`cand-C §7`): the agreement dial cannot give instant
  global revocation local-first; prefer short-expiry+renewal. ⚑ **The local-first mechanism it bounds is now
  built:** `Exec/FullForestAuth.lean: revocationGate`:453 reads the COMMITTED kernel-state registry
  `s.kernel.revoked` (hole #3 / #139), fail-closing a revoked credential off adversary-uncontrollable state —
  the recency floor remains a *distributed* honest bound, but the single-machine revocation read is REAL.

---

## 9. Ranked shortlist

> ⚑ **The frontier moved.** Several shortlist items LANDED in Lean since this was written — the new frontier
> is the *circuit companions* + the agreement dial + the delegation handoff, not the Lean models below.

### Most PROMISING (highest value, clearest fit, buildable)
1. **The modal attestation `Obs[t]` + verifier-indexed `Discharged[V]`** (§4.2, §6.1). ⚑ **The Lean half
   LANDED** — `DischargedFor V` + the `TransferDial` + the repudiation theorems are built and kernel-clean
   (`Authority/DesignatedVerifier.lean`). The structural privacy hole is *closed in the model*. **Remaining
   frontier:** the DVZK *companion circuit* (OR of presentation-AIR + Schnorr-knowledge) and threading the
   verifier index through `livingCell_sound`. Still the single most important dregg4 idea — now half-built.
2. **The caveat-chain algebra unifying the token zoo** (§3.1, §6.3) with **real HMAC-tail integrity**. ⚑ **The
   HMAC-tail integrity LANDED** (`Authority/CaveatChain.lean`); the §8 fiction is *closed*. **Remaining:** the
   single unified `CaveatChain`-over-three-`KeyRef`-roots type (one type replacing `macaroon/`+`token/`+CDT)
   and the removal-resistance reduction off `MacUnforgeable`.
3. **The small-core ISA + per-asset conservation + ρ_in/ρ_out + half-edge** (§3, `EFFECT-ISA §5`). ⚑
   **Per-asset conservation LANDED** end-to-end (`MultiAsset.maExec_conserves_per_asset` →
   `RecordKernel.recKExecAsset_conserves_per_asset` → `execFullForestA_conserves_per_asset`). **Remaining:**
   the small-core ISA reshape itself + ρ_in/ρ_out + half-edge primitives (the bound half-edge is the live
   cross-cell delegation seam, tied to #138).
4. **Storage durability as an honest crash-recovery portal** (§6.9) — ⚑ **PARTIAL:** the `rfl` label-fiction
   is killed (real `Snapshot` token + badge-survival/replay theorems), but the actual *crash/fault-point +
   `replay = pre-crash`* portal is unbuilt. Honesty gain banked; crash model remains.
5. **`returnProject`/`awaitSettle` (native zkRPC)** (§6.5) — the bidirectional lens; the agent product.
   ⚑ The await/promise *substrate* is built (`Await.lean`/`Spec/Await.lean`); the bidirectional return-effect
   on top is still ASPIRATIONAL.

### Most SURPRISING (galaxy-brain; not previously considered)
1. **The third dial — Agreement/finality on the same footing as disclosure & transferability** (§4.3): the
   attestation is a point in a `Disclosure × Transferability × Agreement` 3-cube, and the system lives on
   one edge. *Not in any candidate or grounding doc.* ⚑ **Still ASPIRATIONAL** — disclosure + transferability
   are now built dials, but agreement-as-an-attestation-index has no Lean object yet; this is the cleanest
   open galaxy-brain item.
2. **The turn as a guarded comodel of an effect theory; the three faces as the lens's get/put/guard** (§5):
   one object, one soundness theorem, free sequential composition, dials-as-modalities. ⚑ **DECORATIVE as
   stated** — no `Comodel`/`Lens` Lean object (grep-confirmed). The *operative* payoff (one coalgebra, one
   bisimulation-to-oracle soundness, the dissolved "two co-primary primitives" tension) IS real
   (`livingCell_sound`); the get/put/guard *naming* is framing, not a construction.
3. **User-extensible effect ISA via theory-extension-with-refinement-proof** (§6.4): the *verified* version
   of `Custom`/userspace effects — a comodel homomorphism, not a `Bool` escape hatch. ⚑ The blocking
   `CellProgram` conservation law landed (`denote_conserves`); the extension calculus itself stays open.
4. **Accountable anonymity as a fourth face** (§6.8): an escrowed, capability-gated de-anonymization — the
   "anonymous yet accountable" story for a collaboration OS, reusing the revocation non-membership seam.
   ⚑ ASPIRATIONAL (no escrowed-de-anon object); the revocation registry + non-membership seam it reuses are
   now built (`FullForestAuth.revocationGate`, `Crypto/NonMembership.lean`).
5. **`capExercise` = lens composition** (§5.1): the recursive inner-effect gating the circuit must bake is
   *not* a special case — it is the compositional structure of the lens, which reframes the hardest CORE
   selector as the most natural one. ⚑ DECORATIVE *as a lens claim*; the recursive gating is REAL as the
   executor's mutual `execFullForestA`/`execFullChildrenA` descent (= `execFullTurnA` over the pre-order
   lowering, `execFullForestA_eq_execFullTurnA`:171), not as a `Lens`-composition law.

---

*A closing couplet, since the egg is dreaming bigger now:*
*one turn, three faces — what it does, may, and shows; / and two (then three) dials for how far each one goes.*
*the token, the queue, the proof that can't be relayed — / are one guarded comodel, in a modal lattice arrayed.* 🐉🥚
