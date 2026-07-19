# Predicate-Usefulness Targets — where a decision procedure earns its keep

**Purpose.** The "usefulness push" adds a *decision procedure* over dregg's
predicate language — not just `evalConstraint` (which decides one `(old,new)`
pair) but the semantic questions **satisfiability** ("can this guard ever
fire?" / "is this policy contradictory?"), **equivalence** ("did my refactor
change the policy?"), and **subsumption / entailment** ("does policy A imply
policy B?"). This doc MAPS where dregg actually expresses predicates, RANKS the
places a decision procedure would matter to a real builder, and — adversarially
— marks the sites whose predicates fall **outside** the decidable fragment, so
the fragment-closing work knows what frontier it must reach to serve those
users.

The deliverable is *targeting*: what to build next so this matters to someone.

---

## 0. What exists today, and the gap

The predicate vocabulary is authored in Lean and mirrored in Rust:

- **Lean (authoritative):** `metatheory/Dregg2/Exec/Program.lean`
  - `SimpleConstraint` (`:78`+): `equals / gte / lte / strictMono / monotonic /
    immutable / writeOnce / memberOf / prefixOf / inRangeTwoSided / deltaBounded
    / not` + context atoms (`senderIs / senderMemberOf / balanceGe / balanceLe /
    …`).
  - `StateConstraint` (`:295`+): `affineLe / affineEq / affineDeltaLe` (linear
    integer arithmetic over named scalar fields), `clearanceGe / reachable`
    (finite-lattice / DAG reachability via `dominatesD`), `anyOf / allOf`
    (Boolean).
  - `evalSimple` (`:465`), `evalConstraint` (`:531`), `admits` (`:655`) — decide
    a **given** transition.
- **Rust (executor mirror):** `cell/src/program/types.rs`
  — `SimpleStateConstraint` (`:535`), `StateConstraint` (`:970`); evaluated by
  `CellProgram::evaluate` (`cell/src/program/eval.rs:20`).

**The only decision procedure that exists is `DecidableEq`**
(`Program.lean:419–421`) — **syntactic** equality on the constraint catalog.
That is: today you can ask "are these two constraint ASTs literally the same
term?" You CANNOT ask "are these two policies *semantically* equivalent",
"is this policy *satisfiable*", or "does A *entail* B". Grep confirms no
`satisfiable` / `subsumes` / `equiv` / `isVacuous` procedure exists over the
predicate language anywhere in `metatheory/`. That absence is the whole gap.

### The decidable fragment (what the procedure can target)

The core algebra is squarely inside a **decidable** logic:

> **QF-LIA over finitely many named integer scalar fields, plus finite-domain
> atoms (membership, interval band, path-prefix, finite-lattice reachability),
> closed under Boolean AnyOf / AllOf / Not.**

- `affineLe / affineEq / affineDeltaLe` → quantifier-free linear integer
  arithmetic (satisfiability NP-complete, but small: a cell has 8–16 slots).
- `equals / gte / lte / inRangeTwoSided / deltaBounded / monotonic /
  strictMono / immutable / writeOnce / fieldLteField / fieldLteOther` → all
  reduce to LIA atoms over `new[i]` and `old[i]`.
- `memberOf / prefixOf` → finite disjunctions of equalities.
- `clearanceGe / reachable` → decision over a *finite* labelled DAG (already
  decidable via the proved-sound `dominatesD`).
- `anyOf / allOf / not` → Boolean structure.

Satisfiability of this fragment is decidable; **equivalence and subsumption
reduce to unsatisfiability of the negation** (`A ⊄ B ⟺ SAT(A ∧ ¬B)`), so one
SAT oracle buys all three questions.

**One load-bearing soundness caveat for the whole procedure (see §7.3):** the
Rust executor evaluates over `FieldElement` (mod-p, with big-endian-`u64`
projections and documented wraparound mint-holes throughout `eval.rs`), while
the Lean atoms evaluate over `Int`. A decision procedure that reasons over `Int`
can call a policy "unsatisfiable" that is in fact satisfiable *in the field* by
wraparound (and vice versa). The procedure must model the **deployed field/u64
semantics**, not idealized `ℤ`, or its "unsatisfiable"/"equivalent" verdicts are
unsound at exactly the boundary the executor cares about.

---

## 1. Ranked targets

Ranked by (value to a real builder) × (how squarely the site sits inside the
decidable fragment). Each row: the predicate expressed, the site, WHO authors
it, and WHAT a decision procedure buys them.

### ⭐ T1 — Cell-program / policy authorship: SAT + equivalence + subsumption over `CellProgram::Predicate`

- **Site:** `cell/src/program/types.rs:970` (`StateConstraint`), evaluated by
  `CellProgram::evaluate` (`cell/src/program/eval.rs:20`); the canonical worked
  example is `cell/examples/predicate_language.rs`. Lean twin
  `Program.lean:531`.
- **Predicate expressed:** an `AllOf` list of state constraints declared on a
  cell — the executor rejects any turn whose post-state violates one.
- **Who writes it:** a **policy admin / cell author** — the person defining what
  a cell will accept (audience routing, conservation, solvency floors, actor
  bindings).
- **Decision-procedure payoff:**
  - *Satisfiability* — "is this cell **ever** admittable, or did I write a
    contradictory `AllOf` (`FieldGte{hp,20} ∧ FieldLte{hp,10}`) that bricks the
    cell?" A brick-check is the single highest-value question: an unsatisfiable
    program is a deployed cell that can never take a turn.
  - *Equivalence* — "I refactored the constraint list (merged two atoms, flipped
    an `AnyOf` to `SenderMemberOf`); did the set of accepted turns change?" The
    executor's content-address is byte-sensitive and `DecidableEq` is syntactic,
    so today a semantics-preserving refactor is indistinguishable from a
    semantics-changing one.
  - *Subsumption* — "policy A ⊑ policy B" — is this new stricter program a
    refinement of the old one? The basis for a safe-migration / attenuation
    check.
- **Fragment fit:** the *core* atoms are fully inside. Witness-attached and
  reactive members of the same enum are not (§2); the honest procedure treats
  those as uninterpreted booleans (sound over-approximation for SAT — see §7.1).

### ⭐ T2 — Game designer / `.dungeon` compiler: contradictory-stakes + dead-gate linter

- **Site:** `dungeon-on-dregg/src/bloodgate.rs` (stakes as
  `StateConstraint::FieldGte/FieldLte/FieldLteField/WriteOnce`, e.g. `:246`
  `FieldLteField{dc, check_total}`, `:583/:594` gte/lte teeth) and
  `dungeon-on-dregg/src/dialogue.rs:196–199` (disposition floors `>= 4`, `>= 5`
  as executor-enforced `FieldGte`).
- **Predicate expressed:** game-mechanic teeth — a dialogue gate fires only at
  `disposition >= 5`; a bloodgate stake enforces `dc <= check_total`, HP bands,
  write-once downed flags.
- **Who writes it:** a **game designer** — emphatically *not* a
  formal-methods person. This is the highest **UX-leverage** target: the payoff
  lands as a linter/IDE diagnostic in the authoring tool, not a proof.
- **Decision-procedure payoff:**
  - *Emptiness* — "can this dialogue gate **ever** fire, given the disposition
    is capped at N?" A gate that requires `disposition >= 5` where the schema
    caps disposition at 4 is **dead content** — a quest step no player can reach.
  - *Contradiction (SAT)* — "the bloodgate bundle `FieldGte{hp,20} ∧
    FieldLte{hp,10}` is unsatisfiable — no turn ever passes this room." A
    designer typo that makes an encounter unwinnable.
  - *Equivalence* — "I rebalanced the DC from 12 to 14; did the set of passing
    check-totals actually change, or did I no-op?" Regression-diff for a balance
    patch.
- **Fragment fit:** **excellent** — dungeon teeth are pure LIA
  (`FieldGte/Lte/LteField/BoundedBy/WriteOnce/Equals`). This site is *entirely*
  inside the decidable fragment and is the best first customer.

### ⭐ T3 — Market designer: price-band / clearing feasibility over affine constraints

- **Site:** Lean `bandProgram` (`Program.lean:972`,
  `affineLe [(2,"bid"),(-1,"ask")] 100`), `consvProgram` (`:979`,
  `affineEq [(1,"inp"),(-1,"o0"),(-1,"o1")] 0`); market crates
  `param-compose/`, `dreggnet-market/`.
- **Predicate expressed:** price-band inequalities and conservation equalities
  over bid/ask/inventory scalar fields — the arithmetic heart of a clearing
  rule.
- **Who writes it:** a **market / AMM designer** setting fee schedules, price
  bands, basket weights.
- **Decision-procedure payoff:**
  - *Satisfiability* — "is my price band jointly satisfiable with the
    conservation equation and the fee floor, or have I written a market that can
    never clear?"
  - *Equivalence* — "I refactored the basket weights `2·Δprice − Δindex ≤ k`;
    does the clearing region match the old schedule?" A pricing-refactor
    regression check.
- **Fragment fit:** **excellent** — `affineLe/affineEq/affineDeltaLe` are
  textbook QF-LIA. (The *proof* that clearing is fair is a separate ZK circuit;
  the decision here is over the *plaintext* constraint algebra, which is
  decidable.)

### T4 — Credential relying party: predicate-request subsumption (minimal disclosure)

- **Site:** `credentials/src/schema.rs:146` (`PredicateRequest`), `:150`
  (`Predicate`, e.g. `Predicate::Gte(18)`); consumed by
  `credentials/src/presentation.rs` (`options.predicates`, one
  `BridgePredicateProof` per request).
- **Predicate expressed:** range/comparison predicates over credential
  attributes — "age ≥ 18", "score in [600,850]".
- **Who writes it:** a **relying party / verifier** stating what a presentation
  must prove.
- **Decision-procedure payoff:**
  - *Subsumption* — "a holder already has a proof for policy A (`age ≥ 21`);
    does that also satisfy policy B (`age ≥ 18`)? Then don't demand a fresh
    proof — accept the stronger one." Directly serves **minimal disclosure**:
    reuse the least-revealing proof that entails the requirement.
  - *Satisfiability against the schema domain* — "is `age ≥ 18 ∧ age ≤ 12` an
    impossible request I should reject at config time rather than send a holder
    on an unprovable errand?"
- **Fragment fit / honest scope:** the *predicate request algebra* is decidable
  (comparisons over a scalar attribute). The **proof** the holder produces is a
  ZK range proof (`dregg_bridge::present`) — the decision procedure operates on
  the *request*, never the witness. Multi-attribute requests with cross-attribute
  arithmetic reach into T1's LIA fragment; single-attribute comparisons are
  trivially decidable. Text/opaque attributes (`NonPredicateAttribute`,
  `schema.rs:142`) are outside — flag as not-a-predicate at the boundary.

### T5 — Token / macaroon attenuation: redundant- or contradictory-caveat check

- **Site:** `token/src/dregg_caveats.rs` (`DreggGrant` `:137`,
  `attenuation_to_wire_caveats` `:299`), `macaroon/src/caveat.rs`.
- **Predicate expressed:** a caveat set narrowing a token's authority —
  validity window `[not_before, not_after]`, feature globs (path prefixes),
  budget ceilings, confine-to-user equality.
- **Who writes it:** **anyone delegating** a token (a service, a user handing
  off attenuated authority).
- **Decision-procedure payoff:**
  - *Subsumption* — "the caveat I'm adding is already implied by one on the
    token — my attenuation is a **no-op** (a false sense of restriction)." The
    canonical macaroon footgun.
  - *Contradiction (SAT)* — "two validity windows / two budget ceilings make
    this caveat set unsatisfiable — the token is **dead** and no request will
    ever pass." A support-ticket-avoider.
- **Fragment fit / honest scope:** **partial.** The decidable slice is real —
  validity-window interval intersection, budget-ceiling comparison, and
  feature-glob **path-prefix** containment (the Lean `prefixOf` atom,
  `Program.lean:82`, exists precisely to model the datalog `feature_glob`
  prefix, `token/src/datalog_verify.rs`). Opaque service/app-ID equality caveats
  are finite-domain equality (decidable but uninteresting). This site rewards a
  *specialized* interval+prefix+equality decision, not full LIA.

### T6 — Polis governance: role-policy subsumption + workflow reachability

- **Site:** `metatheory/Dregg2/Apps/*` polis programs — the actor-binding idiom
  `AnyOf[Immutable{slot}, SenderMemberOf{board}]`, `clearanceGe` / `reachable`
  over a workflow DAG (`Program.lean:1034` `workflowDag`, `:1036`
  `workflowProgram`).
- **Predicate expressed:** who may flip which slot (multi-admin actor binding),
  and workflow-prerequisite reachability ("this step is admissible only if a
  prerequisite marker is reached").
- **Who writes it:** a **DAO / governance policy admin**.
- **Decision-procedure payoff:**
  - *Subsumption* — "does governance role-policy A grant a strict subset of what
    B grants?" — the audit question when reshaping a council.
  - *Reachability / emptiness* — "can this workflow step ever be reached, or did
    the DAG edit orphan it?" `clearanceGe`/`reachable` are already decidable over
    the finite DAG.
- **Fragment fit:** the lattice/actor-binding slice is inside (finite DAG +
  Boolean + equality). But **council quorum via `CountGe` / witness sets is
  outside** (§2) — a governance policy that leans on `CountGe` gets only a
  partial answer.

### T7 — Discord access gates (noted, LOW decision-procedure value)

- **Site:** `discord-bot/src/roles_caps.rs` (`RoleCapMap::gate` `:227`,
  `holds` `:220`).
- **Predicate expressed:** "member holds cap C" via a finite `role → cap` map.
- **Who writes it:** a **community/server admin**.
- **Honest verdict:** this is a finite lookup, **already fully decidable by
  evaluation** — there is no interesting satisfiability/equivalence question a
  decision procedure adds (you can enumerate the whole map). Listed for
  completeness so the push does *not* over-invest here. The one adjacent win is
  detecting an unreachable cap (a cap no role grants) — a trivial set-difference,
  not a fragment problem.

---

## 2. Frontier — sites the fragment-closing must reach (adversarial / honest)

These usage sites express predicates **outside** the current decidable
fragment. Naming them is the point: they bound what "usefulness" can honestly
claim until the fragment grows.

### 2.1 Witness-attached predicates — opaque hash/proof atoms

- **Sites:** `StateConstraint::PreimageGate`, `CountGe` (`types.rs`,
  `SimpleStateConstraint:~730`), `SenderAuthorized{BlindedSet}`,
  `WitnessedPredicate` / `Custom{vk_hash}` (`cell/src/predicate.rs`),
  `TemporalPredicate`.
- **Why outside:** acceptance is "a hash opens" / "a ZK proof verifies" / "a
  committed set has ≥ M distinct elements" — there is no static, input-free
  satisfiability. `Custom{vk_hash}` is deliberately an *opaque bytes*
  commitment (`predicate.rs:canonical_predicate_vk`); the platform does not know
  the language.
- **What the procedure CAN honestly do:** treat each witnessed atom as a **fresh
  uninterpreted boolean variable**. This is a *sound over-approximation for
  SAT/contradiction*: it still catches contradictions among the *decidable*
  atoms sharing the program (e.g. `FieldGte{20} ∧ FieldLte{10}` next to a
  `Custom` is still a brick), and never *falsely* reports unsatisfiable. It
  **cannot** decide the witnessed atom itself, so it cannot prove *equivalence*
  of two programs that differ only inside a `Custom`. State this bound explicitly
  wherever the procedure is surfaced to T1/T6 users.

### 2.2 Reactive / temporal / cross-turn predicates — need trace semantics

- **Sites:** `RateLimit` / `RateLimitBySum` / `RateBound` (`types.rs`),
  `UntilEvent` / `SinceEvent` / `CooledSince` / the challenge-window fraud gate.
- **Why outside:** these quantify over a cell's **turn history**, not a single
  `(old,new)`. "At most k admissions per window" is a property of a *trace*; a
  one-shot QF-LIA SAT over one transition cannot express it. (The atoms *read*
  an OLD counter register, so single-transition reasoning about *whether the
  atom fires this turn* is decidable — but the *rate invariant* it encodes is
  not.)
- **What closing it needs:** a **temporal / trace-level** decision procedure
  (bounded model-checking over the cell's serialized turn sequence), a different
  tool from the per-transition SAT. Worth a separate design; do not fold it into
  the LIA procedure and call temporal policies "checked".

### 2.3 Field vs Int semantics — the soundness frontier of the procedure ITSELF

- **Sites:** all of §1 — because the Rust executor evaluates over `FieldElement`
  (mod p) with big-endian-`u64` slot projections, and `eval.rs` documents
  wraparound *mint-holes* repeatedly (e.g. `:496`, `:1199–1224`, `:1847`).
- **Why it matters:** a decision procedure reasoning over `Int` can call a policy
  "unsatisfiable" that the *deployed* executor accepts via wraparound, or
  "equivalent" two programs the field distinguishes. This is not a peripheral
  atom being unsupported — it is a correctness condition on the procedure's
  verdict for **every** target above. The fragment-closing work must model the
  actual field/`u64` arithmetic (bit-vector / mod-p reasoning), not idealized
  `ℤ`, before any "unsatisfiable" / "equivalent" claim is sound at deployment
  resolution.

---

## 3. What to build first (the aim)

1. **A per-transition SAT oracle over the QF-LIA + finite-domain + Boolean
   fragment**, modelling **field/`u64` semantics** (§2.3), with witnessed/
   reactive atoms as sound uninterpreted booleans (§2.1). This single oracle
   yields SAT, equivalence, and subsumption (§0).
2. **First customer = T2** (dungeon designer linter): entirely inside the
   fragment, highest UX leverage, a diagnostic a non-expert reads. Then **T1**
   (the brick-check on `CellProgram::Predicate`) and **T3** (market feasibility).
3. **Surface the bound honestly:** wherever the procedure meets a witnessed or
   reactive atom, its answer is a sound *over-approximation*, not a decision —
   say so in the diagnostic, per the project's resolution discipline.
