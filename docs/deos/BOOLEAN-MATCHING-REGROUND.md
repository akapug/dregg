# Re-Grounding dregg's Matching Layer on a Boolean-Closed Derivative Algebra

> **STATUS (landed, one named residual):** both halves of this doc's program are built.
> The Rust half (Stage 3): the derivative FilterTree compiler (`dfa/src/derivative.rs`,
> Brzozowski/Antimirov front-end, lazy intersection, native complement) + `Pattern::Not`
> (`dfa/src/compiler.rs`) make the cap-secure **deny filter EXPRESSIBLE**, out-of-circuit
> and AIR-neutral (same flat `Dfa`). The Lean half is dregg's **OWN formalization** —
> `metatheory/Dregg2/Crypto/Deriv/` (15 modules: `Core`, `Correctness`, `Finiteness`,
> `TableDfa`, `Powerset`, `Thompson`, `Determinize`, …) builds the symbolic-derivative
> tower directly over dregg's `Pred` algebra with `σ := Value`, reading the
> `extended-regexes`/ITP'25 repos PURELY as proof blueprints — never a code dependency —
> so the license question this doc raised is MOOT. The faithfulness contract is closed
> table-opaquely (`TableDfa.tableDfa_faithful`; `Powerset` discharges it for the deployed
> lazy-derivative determinizer; `Thompson` for the legacy subset path). The one surviving
> Lean residual, named precisely in `Deriv/Determinize.lean` (`:26` and the closing note):
> the LITERAL table-equality `derivativeCompile_eq_tableDfa` against `compiler.rs`'s
> powerset `determinize` — unblocked by `der_finite`, not closed. The `(old,new)`/`Ctx`
> trace-lifts (Stage 5) stay open research. Landing doc:
> [DERIVATIVE-MATCHING-DESIGN.md](DERIVATIVE-MATCHING-DESIGN.md). Read the body as the
> design rationale; treat the §1.3-"inexpressible" and license-gate framing as settled.

dregg has **at least four** independent "boolean matching" surfaces, each
re-deriving the same operators (intersection, complement, union) over a
different carrier, with different closure proofs and different in-circuit
stories. This document asks one question: **can RE#/ERE≤'s boolean-closed
symbolic-derivative algebra — closed under `&`/`~`/lookaround, input-linear,
and Lean-formalized — serve as the *one* foundation those surfaces share?**

This is the design rationale behind what is now built. It lays out the case,
the reusable Lean artifact, the in-circuit split (which the prior eval
`REGEX-AUTOMATON-EVAL.md` already settled for the DFA face), the staged
re-grounding design, and an honest account of what is uncertain. The **Rust**
derivative front-end (Stage 3) is landed (`dfa/src/derivative.rs` +
`Pattern::Not`); the **Lean** derivative tower is landed as dregg's own
formalization (`Dregg2/Crypto/Deriv/`, status banner above); the Stage-5
trace-lifts remain the open research questions flagged *unverified* below.

---

## 1. The case — dregg's scattered matching surfaces

The owner's framing is correct: three (really four) subsystems are all boolean
matching, and they do not share an algebra.

### 1.1 The predicate / caveat algebra (slot policy + token authority)

This is the surface with the **strongest** existing boolean closure — it is
already a proven Boolean algebra, in both Lean and Rust.

- **`Pred`** (`metatheory/Dregg2/Exec/PredAlgebra.lean:127`): the uniform
  Boolean predicate algebra — atoms (`StateConstraint`) plus
  `tt`/`ff`/`and`/`or`/`not`/`allOf`/`anyOf`, with `not` at **every** level
  (the module header `:1-27` states the intent: replace the forked 2-level
  grammars with "the Heyting algebra done properly"). Old corpora embed as a
  no-op (`Pred.ofConstraint_eval`, `:245`), so existing proofs lift. Boolean
  laws are proven `#assert_axioms`-clean (`:680-706`): double-negation
  collapse `eval_not_not` (`:266` — Boolean, not merely intuitionistic),
  De Morgan (`:279`,`:284`). The evaluator `Pred.eval : Pred → Value → Value →
  Bool` (`:190`) denotes over a **single `(old, new)` transition** of a slot
  write.
- **Two fully-closed sibling algebras** with explicit complement laws proven:
  `ArithmeticClosure.lean` (`or_not_self` excluded middle `:251`,
  `and_not_self` non-contradiction `:259`) and `RelationalClosure.lean`
  (`:236`,`:244`) — over `Value`, single-frame.
- **`CaveatPred`** (the macaroon/biscuit token layer,
  `metatheory/Dregg2/Authority/Caveat.lean:66`): the reified caveat AST, the
  **same connective shape** `and`/`or`/`not`/`tt`/`ff` (`:83-89`), but denoting
  over a **request context `Ctx`** (time/height/sender), not the `(old,new)`
  transition. `Token.admits` = meet ⋀ of all caveats (`:149`);
  `attenuate_narrows` (`:162`) proves appending a caveat only narrows the
  admissible set (the Heyting residual). The header `:46-60` is explicit that
  this **deliberately is NOT aliased to `Pred`** ("a literal alias would be
  unsound" — different denotation domains, transition-vs-context).
- **The Rust executor twin**: `cell/src/program/types.rs:535`
  `SimpleStateConstraint` carries `Not(Box<...>)` (`:615`), the rustdoc
  (`:511`) explicitly lifting the predicate algebra from distributive
  lattice to Heyting algebra; `Implies(P,Q) == AnyOf([Not(P),Q])` is derived,
  not a variant.

**Boolean operators this surface needs:** intersection (`and`/`allOf`; token
meet ⋀), complement (`not` — the no-self-transfer tooth `not(digFieldEq from
to)` at `PredAlgebra.lean:427`, the reactive `Changed`/`Unchanged` complements
`:169-182`), union (`or`/`anyOf`). All present, all proven.

### 1.2 The cap-authority lattice (a *different* algebra)

Separate from the predicate algebra: `cell/src/permissions.rs:5`
`AuthRequired {None,Signature,Proof,Either,Impossible,Custom}` with a lattice
order `is_narrower_or_equal` (`:52`) — Impossible=⊥, None=⊤, distinct `Custom`
vk_hashes **incomparable**. `is_attenuation(held,granted)` (`capability.rs:1012`)
= `granted.is_narrower_or_equal(held)`. Action attenuation = set intersection:
`ActionSet::intersect` (`token/src/action_set.rs:166`).

**Boolean operators it needs:** intersection (meet / `ActionSet::intersect`).
It has **no complement** — there is no negation of a capability, and `Custom`
vk_hashes are incomparable, so it is **not even a complemented lattice**. This
is a real divergence from §1.1, not an oversight; a capability is monotone-only
by design.

### 1.3 The FilterTree / intent-matcher (the DFA face)

The capability-secure revocation and routing/gossip surface:
`dfa/src/filter.rs:97` `FilterTree` composes filters by **intersection along
every root→leaf path**; `revoke` (`:156`) flips a node to accept-all
(intersection identity) and `compile_combined` (`:163`) rebuilds the active
intersection. A k-deep tree is a k-fold DFA product,
`O(∏|S_i|)` — the actual state-explosion site. The legacy compiler path
(`dfa/src/compiler.rs`) is eager Thompson-NFA → subset-construction → flat
`Dfa` table; intersection is `dfa_intersection` (a Cartesian product).
**Complement is native** (this doc's Stage 3): `Pattern::Not`
(`compiler.rs`) compiles through the lazy Brzozowski/Antimirov derivative
front-end (`dfa/src/derivative.rs`) rather than the NFA-product path (Thompson
NFAs have no complement constructor), so the capability-secure *deny* filter
(match everything except a revoked namespace) is **expressible** and emits the
same flat `Dfa` the AIR consumes.

**Boolean operators it needs:** intersection (present — eager product, or the
lazy derivative `inter`), complement (present via `Pattern::Not` /
`derivative.rs`), union.

### 1.4 The shape of the problem

Three carriers — `(old,new)` transitions, request contexts, and byte/symbol
sequences — each want `&`/`~`/`|`, each prove (or fail to prove) closure
separately, and only one of them (FilterTree) is sequence-shaped. The Datalog
token-verification path (`token/src/datalog_verify.rs`) is a *fifth* engine
entirely: positive-only authorization rules + a fixpoint + injected deny-facts,
where negation is stratified deny-rules, not algebraic complement.

**The unifying observation:** every §1.1/§1.3 algebra is a reified, decidable,
eval-folded inductive AST closed under `and`/`or`/`not` — i.e. each is already
presented as a **Boolean algebra of characteristic functions** (`Value → Value
→ Bool`, `Ctx → Bool`, `[Symbol] → Bool`). That is *exactly* the carrier a
Brzozowski/Antimirov derivative construction lives over. The gap is that
§1.1's algebras are boolean over a **single frame**, while a derivative algebra
is boolean over a **sequence** — and FilterTree is the only surface that is
already sequence-shaped (and it had the explosion and the missing complement —
both now supplied by the landed derivative front-end, §1.3).

---

## 2. RE#/ERE≤ as the unifying foundation

Source: RE#, Varatalu/Veanes/Ernits, POPL'25 / Proc. ACM PL 9 Art.1 — on disk
at `/Users/ember/Desktop/3704837.pdf`.

### 2.1 What the algebra is

RE# is a symbolic Antimirov/Brzozowski-**derivative** matcher for the class
RE# ⊆ ERE≤, defined modulo a character theory `𝒜 = (Σ, Ψ, ⟦·⟧, ⊥, ⊤, ∨, ∧, ¬)`
— an **Effective Boolean Algebra (EBA)** (§3). Three properties make it a
candidate foundation:

- **Native boolean closure.** Intersection and complement are *constructors in
  the derivative*, not a separate product/determinize pass:
  `δ_x(R & S) = δ_x(R) & δ_x(S)`, `δ_x(~R) = ~δ_x(R)`, `δ_x(R | S) = δ_x(R) |
  δ_x(S)`. The "state" is the derivative-regex itself; the matcher is a lazy
  DFA that materializes only reached states. This is precisely the operator set
  §1.3 realizes today as eager product (`&`) and *not at all* (`~`).
- **Input-linearity** (Thm 4): `LLMatch` is linear in `|s|` for a single match.
  *Caveat carried forward from the eval:* the regex-size state space can still
  grow super-exponentially in the worst case (RE# §5); laziness defers the
  powerset wall, it does not repeal it.
- **Lookaround Normal Form** (Thm 1): `LNF(R) ≡ (?<=B)·E·(?=A)` — lookbehinds
  before, lookaheads after, the single-pass restriction that keeps it linear.
  dregg has no lookaround need today (REGEX-AUTOMATON-EVAL.md §7), but the
  *shape* is suggestive: a positive/negative lookbehind = "this turn is valid
  only if prior history matched B," a lookahead = "...only if a continuation
  exists" — which is the partial-turn/promise context-condition shape
  (memory: a promise-hole is a nullifier). The negative-lookaround-elimination
  theorem (`nla_elim`) reduces negatives to positive-context + complement,
  matching dregg's inexpressibility-as-safety preference. This axis is the
  least-relevant and most-speculative; flagged as such.

### 2.2 The Lean formalization — what it actually proves, and is it reusable

The ERE≤ derivative theory is formalized in Lean 4 by Zhuchko, Veanes, Ebner,
"Lean Formalization of Extended Regular Expression Matching with Lookarounds,"
CPP'24 (DOI 10.1145/3636501.3636959), open-source at
**github.com/ezhuchko/extended-regexes** (Lean 4, package `regex`). RE# cites
it as the *foundational theory of ERE≤* whose theorems it reuses.

What the repo contains (read at HEAD via the survey):

- **`EBA.lean`**: `class EffectiveBooleanAlgebra α σ extends Denotation, Bot,
  Top, Min, Max, HasCompl` with the denotation laws (`denote_bot/top/compl/
  inf/sup`) + a freely-generated `inductive BA` instance. **This is the same
  abstraction as dregg's `Pred`** — a denotation plus `⊥⊤⊓⊔ᶜ` with laws.
- **`Definitions.lean:14`**: `inductive RE` with 11 ctors — `ε`, `Pred`,
  `Alternation ⋓`, **`Intersection ⋒`**, `Concatenation ⬝`, `Star`,
  **`Negation ~`**, and the four lookarounds.
- **`Models.lean:17`** `RE.models : Span → RE → Prop` (`⊫`, declarative span
  semantics) vs **`Derives.lean`** where `null`/`existsMatch`/`der`/`derives`
  (`⊢`) are all `def … : Bool` (computable; `der` returns a height-bounded
  subtype for well-foundedness).
- **The keystone, `Correctness.lean:375`**:
  `theorem correctness : sp ⊢ R ↔ sp ⊫ R` — the *computable derivative
  matcher equals the declarative semantics*, with per-constructor lemmas
  including `derives_Inter`, `derives_Negation`, the four lookaround lemmas,
  and `derives_reversal` (`:427`).
- **POSIX correctness** (`MatchingAlgorithm.lean`: `maxMatchEnd_matches/_max/
  _no_match`) and **negative-lookaround elimination**
  (`EliminationNegLookarounds.lean`: `nla_elim`).
- Toolchain `leanprover/lean4:v4.24.0-rc1`; **depends on full mathlib4**.
- Follow-ups by the same group: ITP'25 "Finiteness of Symbolic Derivatives in
  Lean" (`ezhuchko/finiteness-derivatives` — the derivative state-set is
  finite, i.e. the DFA terminates) and PLDI'26 "EREQ"
  (`ezhuchko/ereq-derivatives`, quantifiers).

**Why this matters for dregg specifically:** the `correctness : ⊢ ↔ ⊫` theorem
is the *exact* shape dregg keeps reaching for — a computable function proven
equal to a declarative semantics — the "two gates provably agree" /
denotational-differential pattern (memory: byte-identity-is-not-faithfulness;
the executor⟺spec⟺circuit triangle). dregg has the EBA *carrier* (`Pred`), and
`Dregg2/Crypto/Deriv/` realizes the derivative *tower* and its correctness proof
natively over it — the repo served as the blueprint for exactly that shape.

---

## 3. The in-circuit split (settled by the prior eval)

This was already evaluated in `docs/deos/REGEX-AUTOMATON-EVAL.md` (POPL-paper-
grounded, `regex-automata`-grounded, AIR-grounded). The conclusion this doc
adopts wholesale and does not re-litigate:

- **The derivative algebra belongs in the *compiler*, not the AIR.** A STARK
  AIR wants a fixed, low-degree, data-independent per-row constraint set. The
  deployed `dregg-dfa-routing-v1` AIR (`circuit/src/dsl/dfa_routing.rs`) gives
  exactly that: one `TableFunction` lookup per row, binding the run to a rolling
  Poseidon2 commitment over the committed table. A derivative *rewrite step*
  `q' = δ_a(q)` is an AST manipulation of unbounded/variable shape — strictly
  worse in-circuit. So: derivatives compile the table out-of-circuit; the flat
  DFA-AIR proves the verdict in-circuit (REGEX-AUTOMATON-EVAL.md §2.3, §4, §5).
- **The Lean trust boundary starts at the flat table.** The Lean model
  `metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean` models only a `TableDfa`:
  `air_run_is_table_run`/`air_final_state_is_classification` (`:254-268`) and
  the crypto pivot `route_commitment_binds_trace` (`:418-436`, two satisfying
  traces with equal table+route commitment ⇒ identical hash chains under
  collision-freedom). All `#assert_axioms`-clean (`:568-577`). The proof is
  **table-opaque** — it does not care *how* the table was built — so a
  derivative compiler that emits the same flat `Dfa` (`compiler.rs:32-41`)
  inherits the entire proof untouched. This is the seam that makes re-grounding
  a *swap behind a stable boundary*, not a circuit rewrite.
- **The one in-circuit win is the symbolic alphabet.** RE#'s `K`-bit EBA
  predicates → fewer symbol *classes* → smaller AIR degree
  (`table_degree=(|states|-1)+(|symbols|-1)`, `dfa_routing.rs:198`). This is
  the *only* piece that touches the circuit + the Lean model, changes
  `vk_hash`, and must be name-gated as a new descriptor and re-grounded in Lean
  (REGEX-AUTOMATON-EVAL.md §6.1, §7) — real circuit+proof work, not plumbing.

**The gap the eval named — now closed at the language level, one literal
residual.** `Dregg2/Crypto/Deriv/` supplies the equivalence theorems: `Correctness`
proves the computable derivative matcher equals the denotational semantics over
`PredRE`; `TableDfa.tableDfa_faithful` is the table-opaque keystone (ANY flat
table whose `accepts` agrees with `derives` recognizes exactly `Matches`);
`Powerset` discharges the agreement hypothesis for the table the deployed
lazy-derivative determinizer (`derivative.rs::Re::compile`) actually emits, and
`Thompson` closes the legacy `pattern_to_nfa().determinize()` subset path (both
halves: Thompson-construction + subset-construction correctness). So "does this
compiled table really equal `R & S`?" is a theorem, not an untrusted Rust gap.
The surviving residual, named precisely in `Deriv/Determinize.lean` (`:26`,
closing note): the LITERAL table-equality `derivativeCompile_eq_tableDfa` against
the powerset table, up to a reachable-state bijection — its finiteness
prerequisite is discharged (`Finiteness.der_finite`), and language/bisim
equivalence (already proven) suffices for the table-opaque AIR.

---

## 4. A concrete re-grounding design + staged path

### 4.1 What unifies, and what stays separate (an honest scoping)

| Surface | Carrier | Re-ground? | Why |
|---|---|---|---|
| **FilterTree / intent / routing** (§1.3) | byte/symbol sequences | **Yes — primary; BOTH halves DONE.** Derivative compiler for `&`/`~`/`\|` (`derivative.rs` + `Pattern::Not`), emitting the same flat `Dfa`; the Lean tower (`Dregg2/Crypto/Deriv/`) proves its faithfulness. | Already sequence-shaped; had the explosion *and* the missing complement — the derivative front-end supplies both. The natural home for ERE≤. |
| **Predicate `Pred`** (§1.1) | single `(old,new)` frame | **Single-frame lift DONE** (`PredRE`'s `sym` leaf IS a `Pred`, σ := `Value`); the turn-*trace* `(old,new)` lift is NOT built (Stage 5). | Already a boolean algebra; the per-symbol acceptance test with `der` stepping one turn. *The trace lift's soundness is unverified.* |
| **`CaveatPred`** (§1.1) | request `Ctx` | **Maybe — same EBA, different σ.** | Shares connective shape but a deliberately distinct denotation domain; unifying needs reconciling `Ctx` vs `(old,new)` under one σ. The temporal floors/ceilings *are* a 1-frame degenerate of a trace lookbehind. |
| **Cap-authority lattice** (§1.2) | capability tokens | **No.** | No complement, incomparable Custom vk_hashes — not a complemented lattice; monotone-by-design. Welding it in would be wrong. |
| **Datalog verify** (§1.4) | fact sets + fixpoint | **No (bridge, don't subsume).** | Stratified deny-rules ≠ algebraic complement; a separate engine with its own STARK path. |
| **The DFA-AIR + `TableDfa` Lean** (§3) | flat table | **Unchanged.** | The trust boundary; derivatives feed it, they do not replace it. |

The key discipline (memory: house-capacities drift): a derivative re-grounding
lives at dregg's **read/query/policy face** (like the rhizomatic slotting), NOT
the kernel. ERE≤ has zero notion of δ-balance, capabilities, or nullifiers.
Over-claiming a "derivative kernel" would repeat the Rust-periphery-mistaken-
for-protocol scar.

### 4.2 The Lean strategy — blueprint, not dependency

The move taken: **build the derivative tower natively over dregg's own `Pred`
algebra** (`Dregg2/Crypto/Deriv/Core.lean`: `PredRE` is ERE≤'s `RE α` minus the
four lookarounds, with `Pred` as the `sym` leaf), reading `extended-regexes` and
the ITP'25 finiteness repo purely as proof blueprints — never a code dependency —
which dissolves the license gate entirely. The three candidate σ instantiations,
in increasing order of risk:

1. **σ := `Value` (single frame) — BUILT.** The `sym φ` leaf reads one `Value`
   per step, decided by `Pred.eval φ (.record []) a`. This carries both the
   FilterTree payoff (the faithfulness theorems of §3) and the `Pattern::Not`
   combinator.
2. **σ := `(old, new) : Value` transition** (`Pred` over a turn-trace) — NOT
   built (`Core.lean` names it explicitly as out of scope). Lift
   `Pred : Value→Value→Bool` to the `RE.Pred` ctor's per-location predicate;
   `der` then steps one *turn* at a time, and `correctness` proves the streaming
   matcher equals the declarative trace-predicate. The reactive
   `Monotonic`/`Unchanged`/`Changed` atoms (`PredAlgebra.lean:169-182`) are
   exactly the "remember the previous frame" residual state a derivative
   automaton threads — a hint this lift is natural. **Unverified**: their `Pred`
   ctor carries a single predicate per location, so a 2-state caveat needs σ to
   *be* the `(old,new)` pair, and lookbehind's `reversal` then reverses
   turn-order (meaningful, but needs checking).
3. **σ := `Ctx`** (CaveatPred). Same EBA, request-context denotation. Reconciles
   §1.1's two algebras under one carrier if and only if a common σ embeds both —
   the hardest and least-certain unification.

The pull is that **`attenuate_narrows` / `CaveatPred.refines`
(`Caveat.lean:162`,`:271`) is already a decidable refinement (language-
inclusion) order** — the very thing a derivative-based equivalence/inclusion
check computes structurally. Re-grounding would replace the per-context
`refines` proof with derivative-based decision (and connects to the proven
right-skew/Büchi-game *decidable flow/policy refinement* result — memory
flow-algebra-right-skew).

### 4.3 The staged path (additive-then-cutover, circuit never changes shape)

This sequences the always-good, low-risk pieces first; the speculative
unifications last and only on demand. Stages 1–3 are lifted from
REGEX-AUTOMATON-EVAL.md §6; stages 0 and 4–5 are this doc's additions.

- **Stage 0 — the Lean derivative core. ✅ DONE (natively — no license needed).**
  Instead of vendoring `extended-regexes`, `Dregg2/Crypto/Deriv/Core.lean` builds
  `PredRE` + `der`/`derives`/`Matches` directly over dregg's `Pred`, in dregg's
  own tree, with the upstream repos as read-only blueprints. `#guard`s pin
  non-vacuity in both polarities.
- **Stage 1 — symbol-class AIR (in-circuit, name-gated).** Map bytes → small
  category ids before the DFA (RE#'s EBA idea at coarse granularity); shrinks
  `|symbols|` and the AIR degree. New descriptor, new `vk_hash`, re-grounded in
  `DfaAcceptanceAir`. *The only circuit+proof work.*
- **Stage 2 — lazy determinization for the LEGACY path (out-of-circuit).** The
  derivative front-end already determinizes lazily (a worklist over canonicalized
  residuals, `derivative.rs::Re::compile`); the remaining piece is the
  complement-free legacy `pattern_to_nfa().determinize()` (cache budget +
  give-up, `regex-automata`-hybrid-modeled); same `Dfa` output, same AIR.
  `Dfa::table_size_bytes` becomes the enforced budget.
- **Stage 3 — derivative `&`/`~` compiler + `Pattern::Not` (out-of-circuit,
  the payoff). ✅ DONE (Rust).** `dfa/src/derivative.rs` is the RE#-style
  Brzozowski/Antimirov front-end (lazy intersection, native complement); `Pattern::Not`
  (`compiler.rs`) makes deny-filters expressible, routed through the derivative path.
  Retires the `FilterTree` product explosion. Still emits a flat `Dfa` (AIR-neutral).
  Independent of the Lean tower — the derivative front-end lives entirely in the
  compiler. See [DERIVATIVE-MATCHING-DESIGN.md](DERIVATIVE-MATCHING-DESIGN.md).
- **Stage 4 — the faithfulness close. ✅ CLOSED at the language level** (with
  `Finiteness.der_finite` as the Stage-3 Lean capstone): `Correctness` (matcher ≡
  denotation), `TableDfa.tableDfa_faithful` (table-opaque keystone), `Powerset`
  (the deployed lazy-derivative table agrees with `derives` by construction),
  `Thompson` (the legacy subset path, both halves). **Named residual:** the
  literal `derivativeCompile_eq_tableDfa` table equality against the powerset
  table (`Deriv/Determinize.lean:26` + closing note) — unblocked, not closed.
- **Stage 5 — predicate/caveat lift (speculative, last).** Only if §4.2(2)/(3)
  prove sound: lift `Pred`/`CaveatPred` to span-indexed recognizers over
  turn-traces, unifying §1.1's frame-algebras with the sequence algebra.

### 4.4 Risks and open questions (honest)

- **License — MOOT.** `github.com/ezhuchko/extended-regexes` has no LICENSE
  file, which blocked any vendor/port. The native `Dregg2/Crypto/Deriv/` tower
  dissolves this: the upstream repos are read purely as proof blueprints, never
  a code dependency, so no license is needed.
- **Semantics mismatch: strings vs turn-traces.** ERE≤ matches `List σ` with
  one predicate per location; dregg's real object is a regex over a *sequence of
  transitions*. Instantiating σ := `(old,new)` is *plausible but unverified*
  (§4.2(2)); the reversal/lookbehind interaction with turn-order is the first
  thing to check.
- **The equivalence theorems exist; one literal residual.** The faithfulness
  contract is closed table-opaquely and discharged for both deployed compilers
  (§3); the literal powerset table-equality `derivativeCompile_eq_tableDfa`
  remains named in `Deriv/Determinize.lean`.
- **Executable-but-nonlinear.** The Lean repo gives *correctness*, not
  *performance*. RE#'s input-linearity comes from LNF + .NET engineering
  (mintermization, lazy DFA, prefilters) that the Lean artifact does NOT
  contain. dregg would inherit a verified-but-slow matcher and own the perf
  engineering itself.
- **Finiteness — proven natively.** `Deriv/Finiteness.lean` proves `der_finite`
  (Brzozowski finiteness over `PredRE`, up to similarity `≅`), ported as a
  blueprint-read from the ITP'25 repo with the lookaround arms dropped —
  kernel-clean, `sorry`-free. No cross-repo version alignment.
- **Complement does not escape determinization.** RE# makes `~R` a native
  derivative, but settling it into a *committed* DFA still needs a total
  deterministic automaton; a complement of a Unicode-heavy / deeply-intersected
  pattern can still blow up `num_states`. The resource bound + give-up policy is
  the safety net, not a proof of small size (REGEX-AUTOMATON-EVAL.md §7).
- **Right-skew non-distributivity.** The trace/online-sim semantics is *proven*
  right-skewed — choice ⊔ does NOT left-distribute over compose ⋆ (memory
  flow-algebra-right-skew). A naive Kleene-algebra/derivative re-grounding that
  assumes full distributivity would be **unsound for the reactive rung**. Any
  Stage 5 lift must respect this, not assume a free Kleene algebra.
- **Reifying ≠ forcing in-circuit (the genuinely hard frontier).** `Caveat.lean`
  is explicit (`:57-60`): reifying a caveat is an *expressiveness* gain, not a
  *soundness* gain — "the circuit still binds an aggregate `caveatBit` and
  trusts the executor's decision." A boolean/derivative caveat algebra inherits
  this: making policy structurally inspectable ≠ forcing it in the light-client
  circuit. In-circuit forcing is orthogonal to the boolean closure and stays
  hard.
- **The opaque escape arm.** `Caveat.opaque (Ctx→Bool)` (`Caveat.lean:113`,
  `:127`) and the witnessed/ZK predicates (`cell/src/predicate.rs`
  `Custom{vk_hash}`) are NOT introspectable — a derivative algebra cannot see
  inside them. Re-grounding shrinks the opaque surface, it does not eliminate
  it.
- **Don't over-rotate.** The deployed router is 4 states / 4 symbols
  (`dfa_routing.rs:537`). The explosion is a *latent* `FilterTree`-deep-
  intersection risk, not a live fire. The staging deliberately lands the cheap
  always-good pieces (symbol classes, lazy compile) first and the derivative
  rewrite only when an intersection-heavy filter tree actually demands it.

---

## 5. Bottom line

dregg has the Boolean-algebra carrier (`Pred`/`CaveatPred`/the closure modules —
proven `#assert_axioms`-clean), the stable in-circuit trust boundary (the
table-opaque `TableDfa` proof), **(b) `~` for the FilterTree** — the derivative
front-end + `Pattern::Not` (Stage 3, Rust) — and **(a)+(c) the Lean
sequence/derivative layer with its faithfulness theorems** — the native
`Dregg2/Crypto/Deriv/` tower over `Pred` with `σ := Value`, closing "the compiled
boolean semantics is trusted" table-opaquely for both deployed compilers. RE#'s
derivative algebra is the *compiler*, never the in-circuit transition (the eval's
settled split holds).

The move was a **weld, not a build** — and the license never had to clear,
because the tower is dregg's own formalization with the upstream repos as
blueprints only. What remains: Stages 1–2 (symbol-class AIR; lazy determinization
for the legacy path — good independent of the unification), the literal
`derivativeCompile_eq_tableDfa` table equality (named, unblocked), and the
predicate/caveat trace-lift (Stage 5) as a genuine open research question, not a
foregone conclusion — the turn-trace σ instantiation and the right-skew
non-distributivity are real, unverified frontiers.

### Cited sources

- RE# paper: `/Users/ember/Desktop/3704837.pdf` (POPL'25, Proc. ACM PL 9 Art.1).
- ERE≤ Lean: `github.com/ezhuchko/extended-regexes` (CPP'24, DOI
  10.1145/3636501.3636959); follow-ups `ezhuchko/finiteness-derivatives`
  (ITP'25), `ezhuchko/ereq-derivatives` (PLDI'26).
- Predicate algebra: `metatheory/Dregg2/Exec/PredAlgebra.lean`,
  `Dregg2/Authority/{ArithmeticClosure,RelationalClosure,Caveat}.lean`,
  `cell/src/program/types.rs`, `cell/src/{permissions,capability}.rs`,
  `token/src/{action_set,datalog_verify}.rs`.
- DFA face: `dfa/src/{filter,compiler,derivative}.rs`, `circuit/src/dsl/dfa_routing.rs`,
  `metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean`,
  `metatheory/Dregg2/Crypto/Deriv/` (the native derivative tower),
  `cell/src/predicate.rs`, `turn/src/executor/membership_verifier.rs`.
- The settled in-circuit split: `docs/deos/REGEX-AUTOMATON-EVAL.md`.
