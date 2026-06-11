# DREGG3 — the substrate proposal

**Status:** design proposal v2 (2026-06-09). Supersedes v1 (same day). Says what
the kernel SHOULD BE and how the system mounts on it. Not a changelog.

**Provenance:** a whole-tree read (52-verb `Effect`, 19-field `RecordKernelState`,
10-variant `Authorization`, 37-variant `StateConstraint`, the five-stratum proof
tower, four censuses), the dormant resource layer (`Resource.lean`,
`StepCamera.lean`, `Laws.lean`), the constellation (svenvs, mediateor,
graphplay), and ember's framing: **polisware** (Egan — the cipherclerk is a
citizen's clerk, the polis is the product) and **shipware** (KSR's *Aurora* —
software a crew bets generations on). The gem is the skeleton; skeletons exist
to carry flesh.

---

## §0. The essence

> **A turn is the exercise of an attenuable, proof-carrying token over owned
> state, leaving a verifiable receipt.**

The token lineage (macaroon → biscuit → capability) is the oldest stratum and
the deepest: biscuit's Datalog became the derivation circuit — *the token
became the proof system*. Everything below is this sentence, given algebra.

And the constellation states the design move once, mathematically (graphplay):
**trust lives in small faithful quotients with machine-checked lifts.** The
envelope is the quotient of the inhabitant (svenvs); the pact is the quotient
of the quarrel (mediateor); the receipt Q is the quotient of the transition,
and the kernel below is the quotient of dregg itself. The ethics inside the
math: *what the proof does not need, it does not ask to see* — testimony over
inspection, projection over surveillance. These rhymes are informative, not
load-bearing; §6 taxes every one of them.

## §1. The critique (unchanged from v1, abbreviated)

The pieces are individually strong; the hygiene war was won (0 sorry, 238
axiom pins, real anti-ghost teeth). The faults are ontological, and they share
one disease: **collaborators only ever added; nothing had authority to
subtract.** Twelve named faults — verb accretion (52), ownerless side-tables,
six authority vocabularies (incl. `Authorization::Unchecked`), commitment
pluralism, two coexisting value laws (modulo-burn vs `balance_change`'s exact
Σδ=0), session/interop/privacy promoted into kernel verbs, asset≠cell
namespace, executor multiplicity, hand-proven bespoke codec, claims-as-journal.
(Full table: v1, in git history at `07e3c146d`.)

---

## §2. The skeleton — four substances, one gate

### §2.1 The substances

The kernel governs four substances, each with its own **discipline of use** —
and the algebra for all four already exists in-tree, complete and dormant:

| Substance | Discipline | The law | The algebra (built, in-tree) |
|---|---|---|---|
| **Value** | linear — moves, never copies or vanishes | Σδ = 0, exact | ℕ-sum camera; `Excl` (`excl_no_dup` proven) — `Resource.lean` |
| **Authority** | **non-forgeable production** — GROWS (introduction, sealer/unsealer amplification, mint/powerbox, endowment) but only by *authorized, receipt-disclosed* construction from held connectivity; narrows freely (attenuation governs ONE edge, not the system) | Miller: *only connectivity begets connectivity* (`CONSTRUCTIVE-KNOWLEDGE.md §3`; `Metatheory.no_forge_step`) | the `Auth` camera is the FAITHFUL model — ● may move the total under authorization, ◯ fragments cannot self-amplify; `ConfinesAuthority := Fpu` (`Resource.lean:319`). ⚠ v1 of this row said "affine/weakening-only" — that is the monotone-descent error §3 explicitly forbids (it forbids the patterns that give capabilities their power) |
| **Evidence** | monotone — once known, never unknown | grow-only | the nullifier/commitment/epoch ledgers (persistent fragment) |
| **State** | guarded-mutable — changes only under Pred, only by its owner | the frame | cells + programs; `StepCamera.lean` for the step-indexed tier |

**The two gates (the S0 verdict, `Dregg2/Substrate/FpuProbe.lean`,
`fb0cb5695` — probe R1 returned PARTIAL/strong):** every kernel verb is

> **admission** (a `Pred` discharge — does the supplied witness realize the
> demanded predicate? the epistemic half, the verify/find seam) **×**
> **Fpu of the verb's footprint** in the product camera `Sub4` (the ontic
> half — the update respects what the substances ARE).

The Fpu product genuinely unifies conservation + non-amplification +
monotonicity as ONE theorem shape (`move`/`grant`/`write`/`spend` proved as
product-Fpu instances of the EXISTING theorems; authority and evidence turned
out to be literally the SAME `Auth`-camera over ∪-monoids — Resource.lean:319's
"one law" cashed). Two PROVED limits: **E1** — order-shaped validity alone
cannot carry Σδ=0 (`nat_auth_coordinated_mint_fpu`); the supply constant is
parametric until **R2 makes s₀ = 0 canonical** (the issuer IS the Iris-bank
authoritative element) — so the value leg is R2-conditional, now as a theorem
dependency, not a vibe. **E2** — the camera is provably blind to the guards
(`camera_blind_to_caveats`); admission is genuinely its own half (as the
constructive-knowledge metatheory demands — the demand⊣supply side was never
going to be a camera). The nonce hatch dissolved: the receipt log is
evidence-shaped (monotone leg, not an interaction term).

**The doctrine already has a trunk: `Metatheory/*` (the candidate-independent
logic of constructive knowledge — `CONSTRUCTIVE-KNOWLEDGE.md`).** The skeleton
above is not a new foundation; it is the *dynamics* layer of that logic, and
must be grown INTO it, not beside it. What the metatheory adds that this
section's v1 missed: (a) the **verify/find asymmetry** as the organizing
principle (checking cheap+trusted, search undecidable+untrusted — `Knower` =
`Verifiable` + opaque `Searchable`); (b) authority dynamics are
**production, not descent** (§3 — see the corrected Authority row); (c) a
step is judged by THREE orthogonal logics — linear (conservation), modal
(finality tiers as common-knowledge ascent), and the **I-confluence lattice**
(which inferences commute — the metatheory of the `merge` reading and of
sharding, absent from v1); (d) soundness is the ▶-guarded *life* of the
knower (`knowledge_does_not_drift`) — so connecting StepCamera's
step-indexing to `Boundary.Later` (currently the identity placeholder) is
discharging the metatheory's own §2, not a nicety; (e) Φ, the named-lossy
vat-crossing functor: *permission survives, authority does not* — the loss is
load-bearing (forwarded caps become revocable BY CONSTRUCTION).

The structural rules ARE the verb set: `move` is exchange for the linear
substance; `grant` is authorized production for the Auth-governed one;
`shield`/nullifiers are evidence-monotonicity; `write` is heap update under
the frame. A turn is
a proof term; the circuit is the logic's proof checker; a receipt is a
judgment; the chain is one growing proof object. The frame rule, proven once,
is simultaneously: sovereignty (your cell, untouchable), joint turns
(separating conjunction), sharding (disjoint frames commute), and offline
strands (your frame advances alone and merges sound).

### §2.2 The nouns

```
Pred   — ONE guard algebra: curated atoms ⊕ all/any/not ⊕ witnessed(vk)
         ⊕ thirdParty(discharge). Four polarities of the same object:
         caveat (imposed on delegated power) · program (maintained on self)
         · precondition (required of a turn) · intent demand (wanted of the
         world). Evaluated by the executor; compiled to circuit obligations;
         the Predicate⊣Witness Galois connection (Laws.lean) is its base.

Cap    — the token: {target, rights, caveats: Pred, expiry, epoch}.
         Attenuable on every axis; revocable by epoch; STORABLE in slots
         (a cap is a value — absorbs seal-boxes, sturdyrefs, escrowed
         authority; see risk R7 for the retrieval-epoch rule).

Cell   — the four substances gathered + program + operator:
         {operator, lifecycle, nonce, bal : Asset → ℤ,
          clist : sorted-Merkle of Cap, program : Pred, slots : Slot → Value}.
         Nothing is ownerless. Every object IS a cell or lives in one.

Asset  — an issuer cell's promise: AssetId := CellId of the issuer; the
         issuer carries −supply, so ∀a. Σ_c bal(c,a) = 0 ALWAYS (risk R2).
         Mint/burn are the issuer moving from/to its well under its own
         program. Fees are ordinary moves to pot-cells whose programs ARE
         the fee policy.

Turn   — auth ∘ body ∘ receipt; body ::= verb | seq | par | hole(Pred).
         Prologue/epilogue are made of the same verbs. Conditional turns
         (proof-gated, timeout-aborted) and eventual/pipelined batching are
         COMPOSITION structure, kept. Multi-party via per-action commitment.

Q      — the receipt: the committed postcondition under ONE commitment
         scheme (sorted-Poseidon2 Merkle, all the way down — the
         CommitmentCrossBind crown becomes a definition). The witness proves
         Q; the dial projects Q; aggregation folds Q; the light client
         verifies only Q-chains.
```

### §2.3 The verbs (eight)

`create · write · move · grant · revoke · shield/unshield · lifecycle` —
subsumption table as v1. Exercise is *using* a cap, not a verb; refusal is an
outcome; nonce is prologue; pipelining is composition. Everything else among
the 52 is a **cell-program pattern** (factory + Pred + these verbs): queues,
inboxes, pubsub, escrows, obligations, auctions, namespaces, bridges, relays.

### §2.4 The interpretations

The Argus discipline — one term, multiple provably-agreeing readings —
generalizes. Committed readings: `interp` (= the executor) and `compile`
(= the circuit). Proposed readings, each its own workstream: `explain`
(deterministic rendering for the citizen — the UI that cannot lie; honest
scope per risk R6) and `merge` (the state-sync/CRDT function). The kernel's
identity is the TERM; every reading is staff, not soul.

---

## §3. The flesh — what mounts on the skeleton

The vision must not dissolve the system into a logic paper. The skeleton's
purpose is **leverage** for the ship. What each existing organ becomes:

**The cipherclerk** (8.7K LOC, 115 fns, explicitly Egan-named) — **the
product's soul, kept and elevated.** The citizen's clerk: keys, attenuable
tokens, delegation, sub-agent derivation, and — already built — the
selective-disclosure dial (`hide/reveal/predicate/committed_threshold`).
Under dregg3 its dials become *literally* Q-projections, its tokens become
kernel caps via the edge adapters (macaroon/biscuit point inward through the
`token` trait), and it gains the `explain` reading: the clerk that can always
tell its citizen, faithfully, what a turn will do. The clerk is the polis
interface; the kernel is what makes the clerk's promises true.

**Userspace + the Verify toolkit** — **the second half of "comprehensive."**
Kernel verification without app verification doesn't sing. The story:
factories publish descriptors (slot layout + Pred constraints); the Verify
toolkit (Contract/Frames/Tactics + Gated variants, ~20 apps already shaped
this way) proves app-level contracts BY CONSUMING Q against descriptors —
apps inherit theorems from the kernel without enlarging it. The bar for a
shipped app: a `Gated` contract in `Dregg2/Apps/` + a factory descriptor +
anti-ghost regression. The storage primitives (queues/escrows/…) re-land as
*verified factories* — each carries the contract its kernel-verb ancestor
never had. **Subtraction increases total verified surface.**

**The intent layer** (22K: matcher, bonds, partial fills, rings, PIR) —
userspace, settling via ordinary turns; its demands are Pred at the wanting
polarity; the solver is a subsumption searcher. The agent-mandate machinery
is the svenvs-rhyme mount point (R4): a mandate is a program on an
agent-cell; every agent turn carries the proof it stayed inside.

**CapTP** — the session layer: vats, sturdyref wire format, handoff certs,
promise transport. Underneath: caps-in-slots + guarded grants. Nothing
consensus-visible.

**Federation/strands/blocklace** — the body: causal partial order of
receipts, equivocation-exclusion, finality tiers, Hosted↔Sovereign custody.
graphplay's quotient machinery is the natural math for its topology/mixing
questions when they arise (a rhyme, not a dependency).

**The polis layer** — governance as cells: councils, registries,
constitutions as forward-certified programs (certify-before-dispute — the
mediateor rhyme, R5), succession as certified root-genealogy. The
constitution of a polis is a page of Pred, and a citizen can read it.

## §4. Shipware — the acceptance criteria (Aurora)

A generation ship's software answers to harsher judges than an auditor.
These are dregg3's acceptance criteria, each testable:

1. **Succession.** Every root — VK, commitment context, constitution, judge —
   has a certified successor path (genealogy, not flag-days). The crew must
   never be stranded by an upgrade. *(Test: rotate every root on devnet with
   chains intact across the boundary.)*
2. **Closure.** Σδ = 0 exact; every resource accounted to an owner; the
   system operates with NO external oracle or vendor. *(Test: the n=1
   collapse — one machine runs the whole protocol forever, offline.)*
3. **Legibility.** The kernel fits in a head; the constitution on a page;
   every turn explains itself via the `explain` reading. A crew member —
   not a cryptographer — can audit what happened. *(Test: the explain
   rendering of every kernel verb, reviewed by a human cold.)*
4. **Repairability.** Every component replaceable while live, behind proofs
   (anti-brick upgrades; the svenvs gate-shape). *(Test: upgrade the
   executor, a factory, and a constitution on a running devnet.)*
5. **Autonomy.** Offline-first strands; partition-tolerance by structure;
   re-merge proves itself. *(Test: two nodes diverge for a week, merge,
   verify.)*
6. **Honest quotients.** What the proof does not need, it does not ask to
   see: the dial is the default mode of disclosure; testimony over
   inspection. *(Test: every app's observability story states its
   projection explicitly.)*

## §5. The construction (probe → formalize → implement → delete)

Each stage opens with its falsification probe (§6); nothing load-bearing
ships on vibes. Stages remain independently green.

- **S0. The Fpu probe (R1)** — one Lean module: state `move`/`grant`/`write`
  as Fpu in the product camera; try to *instantiate the existing theorems*
  (conservation spine, attenuation gate, frame lemmas) as its instances.
  This decides the skeleton's exact shape. ~Small, decisive.
- **S1. The cap crown finishes** *(in flight — A, B, B2, C landed; D = the
  sdk authority binding remains).*
- **S2. Value unification (R2 probe first)** — issuer-cells, exact Σδ=0,
  fees as moves; ratify `balance_change` as THE mechanism. Shares the
  S1 VK/commitment rotation — rotate once.
- **S3. Storage-as-cell-programs (R3 probe per family, escrow FIRST)** —
  the verified-factory migration; verbs die as contracts land; `storage/`
  and `app-framework/` dissolve into factories + thin Action shims.
- **S4. Guard unification** — Pred everywhere; `Authorization` collapses to
  {signature, proof, cap-exercise, token-adapter}; `Unchecked` dies; the
  37 atoms are curated (kernel atoms vs `witnessed(vk)` customs).
- **S5. One circuit, one deletion wave** — descriptor coverage completes
  over the 8-verb surface; hand-AIRs + ~33K orphaned circuit LOC + dormant
  stacks die under the verified-replacement gates.
- **S6. One executor, one codec** — the SWAP finishes (root-gaps die with
  their verbs); apply.rs retires to witness-generation; schema-derived
  canonical encoding with a once-proven generic codec.
- **S7. The assurance case + the polis surface** — `AssuranceCase.lean`:
  five claims (Authority · Conservation · Integrity · Freshness ·
  Unfoolability), organized by guarantee, never by date, assumption floor
  explicit (Poseidon2 CR, ed25519, FRI, GST — and nothing else). The
  cipherclerk gains `explain`; the constitution page ships.

## §6. The seeming-unification risk register

ember's warning, taken as discipline: *by the time the details get fully
formalized, sometimes beautiful visions fall apart.* Every elegant claim
below must EARN load-bearing status by surviving its probe — and each probe
is designed to be able to FAIL.

| # | Beautiful claim | What must survive formalization | Falsification probe | If it fails |
|---|---|---|---|---|
| **R1** | Every verb is one `Fpu` in the product camera | Substances interact inside one verb; the product may need interaction terms; step-indexing may leak | **✅ S0 RETURNED: PARTIAL/strong (`fb0cb5695`, 2 hatches, 30 pins, axiom-clean).** The honest schema = **admission × footprint-Fpu** (see §2.1). E1: value R2-conditional (order-validity provably ⊉ Σδ=0; issuer-supply dissolves it). E2: guards provably outside the camera (admission is its own half). Authority≡evidence (one Auth camera). Step-indexing never leaked (StepCamera not needed at this tier) | Adopted: the two-gate formulation IS the fallback-free outcome — Fpu unifies the three substance laws; admission stays the Pred family |
| **R2** | AssetId := issuer cell; exact Σδ=0 | Shielded-pool interaction (unshield vs issuer-negative wells); genesis bootstrap; fee-pot liveness | **✅ W1 KERNEL LANDED (2026-06-10).** Probe (`Substrate/IssuerSupplyProbe`) → canonical model (`Substrate/IssuerLedger`, E4 value-binding closed) → THE CUTOVER: `AssetId := CellId` in the anchor; `recKMintAsset`/`recKBurnAsset`/bridgeMint ARE issuer-moves (`Exec/IssuerMove.lean` `rfl` receipts); `ledgerDeltaAsset ≡ 0` (no non-conserving verb left); `reachable_total_zero` (`Exec/ReachableConservation.lean`): every reachable state has `∀a, Σ_c bal c a = 0` EXACTLY; genesis-order + issuer-authority gates fail-closed; circuit weld (specs/Inst/Witness/Emit + triangle) regenerated; Guarantee B upgraded to identically-zero. Rust value-model migration staged (the well needs signed balances; ledger records the burn divergence) | Not needed — the probe licensed the identity registry; the fallback was never load-bearing |
| **R3** | Cell programs cover ALL storage/escrow semantics | Cross-slot relational constraints (head−tail≤cap — the KNOWN v1 gap); multi-cell settle atomicity | Build the ESCROW factory + prove release-safety in Verify BEFORE deleting escrow verbs; queue family second | The stubborn family keeps a kernel verb; the others still migrate |
| **R4** | svenvs envelope ≅ cell program (mandate) | svenvs needs step-indexed/Löb structure Pred lacks; the ∀-inhabitant quantification | Express cartpole's envelope as Pred; check `safe_weakening` maps onto OUR Auth camera | A rhyme, not a mount; dregg3 unaffected (it never depended on this) |
| **R5** | mediateor pact ≅ joint cell | Pacts are Isabelle + human-in-loop; dignity machinery ≠ state machinery | Model ONE scenario's pact as a factory + joint turn; check what's lost | Same — informative rhyme only |
| **R6** | `explain` is a faithful third reading | NL "faithfulness" is not circuit faithfulness | Honest scope: explain = PROVED-TOTAL deterministic template rendering of the IR term; theorems = totality + injectivity-on-semantics, NOT NL meaning | Ship as "best-effort rendering, total + injective" — still kills blind signing |
| **R7** | Caps storable in slots | A stored cap must not survive its grantor's revocation — retrieval needs an epoch re-check; storage must not launder freshness | **✅ LANDED BOTH SIDES (2026-06-10): EPOCH-AT-RETRIEVAL** — on load+exercise, reject iff `stored_epoch < current_epoch(grantor)`. `CapabilityRef` gains `stored_epoch`, `SealedBox` gains `seal_epoch` (captured at store-time); ~1 comparison gate per stored-cap exercise; orthogonal to sturdyref `max_staleness` (both must pass); conservatively, ANY grantor epoch-bump stales earlier-stored caps (sound; the child's duty is to refresh). Theorems LANDED in `Dregg2/Apps/CapSlotFactory.lean`: `stored_cap_only_fresh_if_epoch_unrevoked` + `no_forge_from_storage` (+ `revoke_stales_stored_cap`/`store_then_revoke_refused` teeth, witnesses both ways); the runtime re-check landed in `apply.rs` (`stored_epoch` on `CapabilityRef`, `seal_epoch` stamping) and the MCP gateway binds its verifying executor to the attested height | Sealed-box machinery stays a kernel-adjacent pattern with its own gate |
| **R8** | Byzantine = sheaf non-gluing | The poset/presheaf formalization may not add power over existing blocklace proofs | A standalone metatheory module; pursue only if it SHORTENS an existing proof | Drop without grief; the blocklace proofs already stand |

## §7. Decision points (ember)

1. **AssetId := issuer CellId** — gates S2. *(R2 probe first regardless.)*
2. **Caps-in-slots** — gates the seal/sturdy absorption. *(R7 design first.)*
3. **Fees as pot-cell moves** — kills modulo-burn; policy moves to pot programs.
4. **Intent layer as userspace** (recommended) or 9th verb family.
5. **Pred atom curation** — which of the 37 are kernel; rest become `witnessed`.
6. **Identity**: "dregg2 in shape" vs the dregg3 name on a clean commitment
   epoch. (The ship gets rebuilt plank by plank either way; the question is
   what we paint on the hull.)

---

## §8. The guard-algebra uplift (what FieldLteOther taught us)

The queue probe (W2) returned PARTIAL on one point: `head − tail ≤ capacity` is a
relation between TWO slots, and the live caveat evaluator
(`SlotCaveat.eval : … → CellId → Int → Int → Bool`) sees only ONE slot's
old/new. FieldLteOther is not a missing atom — it is a **symptom**. The disease,
and the uplift:

**The diagnosis (categorical).** Cell state is a product `∏ᵢ slotᵢ`. Today's
guard language offers only predicates that factor through a single projection
`πᵢ` — the axis-aligned rectangles. `head ≤ tail + cap` is a *diagonal* (a
half-plane), it factors through no single projection. So the guard language is
a tiny sublattice — the projection-generated one — of the natural object: the
**full algebra of decidable relations on the state**. We hand app authors graph
paper and let them draw only horizontal and vertical lines. ⚠ The circuit was
NEVER the bottleneck — the EffectVM constrains arbitrary columns together, so a
relational guard is just more polynomial constraints on the same row, free
structurally. The per-slot narrowing was an artifact of the *evaluator
interface* that ossified into ontology — the same fragment-mistaken-for-algebra
disease the whole census found, in miniature.

**Two axes of impoverishment:**

- **Axis 1 — relational arity (spatial).** Per-slot → full relational over the
  post-state. The fix is not "add FieldLteOther"; it is **offer the closure** —
  a record-level predicate combinator (`Pred` reading the whole post-record),
  so `head≤tail+cap`, `Σ slots = const`, `a∧b→c`, any decidable relation, all
  simply ARE `Pred`, no new atom per shape. The "ONE Pred" thesis sharpened:
  Pred = the internal predicate logic of the state object, bounded only by
  decidability + circuit-expressibility (which it already has).

- **Axis 2 — causality (temporal) — the "causal braid."** Every guard today
  sees `(old, new)` — ONE transition, blind to history. It cannot say:
  commit-reveal ("reveal admissible only if causally-after its commit"), causal
  handoff ("B's spend only after A's grant" — a two-strand braid),
  rate-over-trace (the honest version of today's side-table `RateLimit`),
  monotone-over-forks (the CRDT/I-confluence shape), or the braid proper (a
  JointTurn whose N cells must interleave in a specified partial order). We have
  every piece, stratified WRONG: `Time/Causal.lean` has `precedes`,
  `Time/Frame.lean` already models a temporal predicate as a
  `WitnessedPredicate`, `Proof/{Temporal,CTL,MuCalculus,Fairness}` are full
  modal logics, the receipt chain IS the trace, the witness bundle IS its
  content. The gap is purely that those modalities live in the PROOF layer
  (things we prove ABOUT the system) not the OBJECT layer (things an author can
  INSTALL). A causal guard is structurally a `witnessed(vk)` atom whose verifier
  is "this event causally precedes that one in the lace."

**The uplift (one sentence — a candidate load-bearing statement).** The cell is
a coalgebra unfolding over the causal poset (a presheaf on happened-before —
EpistemicConsensus's simplicial model); the guard language should be the
**internal predicate logic of that** — closed under the relational connectives
(spatial) and the causal/temporal modalities (sheaf-logic "◇ in the past"). And
the gem, not the feature: **the language you can ENFORCE should equal the
language you can PROVE.** Today `enforce ⊊ prove` — a wall between "what you can
install on a cell" and "what you can state about the system." Collapsing that
wall IS maximal programmability — the same move as "a witnessed guard and a
circuit obligation are one mechanism," one notch further: *an installable guard
and a provable property are the same predicate.* (Comonadic dress, per the
dregg4 note: the guard's domain is the comonadic context — a `Store`/`Traced`
comonad indexed by how far into the causal past it observes; per-slot caveat =
the depth-0, single-coordinate context.)

**The duality (and the honest tax).** Programmability and minimality are dual:
the guard language should be as BIG as the circuit can express; the dependency
surface as SMALL as the use touches (the dregg-auth wedge slimming is the same
principle in reverse). The seeming-unification taxes: (a) **cost** — "any
decidable relation" is not free; each compiles to constraints and a causal
guard needs the relevant trace slice in the witness, so the offered closure is
the *efficiently-circuit-expressible* fragment, with `witnessed(vk)` as the
escape hatch for the rest. (b) **the confluence dual — load-bearing, and an
asset** — a history-dependent guard may break I-confluence (two concurrent
turns reading the past can't always merge coordination-free). So the causal
guard language and the I-confluence lattice (the THIRD logic of
CONSTRUCTIVE-KNOWLEDGE §4, landing here on its own terms) are two sides of one
coin: **a confluence-stable guard runs coordination-free; one that isn't forces
ordering (consensus).** That is not a bug — it is the system telling the author
the true cost of the braid they asked for; the lattice CLASSIFIES which braids
are cheap.

**The probe that must tax it (before any commitment):** does the
relational+causal closure compile to BOUNDED circuit obligations, and exactly
which fragment stays I-confluent? — the falsifiable question whose answer is the
real shape of the maximally-programmable guard language. FieldLteOther is the
first crack in the wall; the uplift is to take the wall down.
