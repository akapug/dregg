# DESIGN — The Guarded-Grammar Circuit

**Status:** design + feasibility. Marks **BUILT** (deployed/proven, cited `file:line`) vs
**PROPOSED** (this design). Companion to `docs/DESIGN-parse-as-derivation.md` (the Dyck rung,
now fully landed through the general soundness theorem) and
`docs/DESIGN-composed-attestation-architecture.md` (the regex ⊗ CFG substrate). This doc is the
next rung: **take the parse-as-derivation circuit OFF the fixed Dyck grammar and point it at the
templater's per-hole-guarded grammars** — the composition that turns the parse circuit into the
attestable-schema templater's proof engine.

## Thesis

A guarded template (`HandlebarsGuarded.GuardedTemplate`) is *not* one monolithic grammar — it is
a **skeleton** (the segment sequence) whose leaves are **regular guards** over an infinite
alphabet. The right circuit is therefore not "generalize the Dyck rule table until it swallows
the templater" but the composed-architecture split, now made precise:

- each **hole span** is attested by the cheap, *already-parametric* DFA circuit
  (`dfa_routing_descriptor(name, transitions)` — table-generic since day one,
  `circuit/src/dsl/dfa_routing.rs:126`), one leaf proof per hole, ~7 columns;
- the **skeleton** rides the Dyck-stack machinery (`circuit/src/dsl/dyck_stack.rs`), whose rule
  table generalizes per-template by **emit**, and whose stack earns its keep exactly when
  templates **nest** (`HandlebarsGuardedCompose.guardedCompose`);
- the **fold** stitches spans by offset continuity into one word commitment.

The semantic statement that makes this split sound AND complete is now **PROVEN**:
`GuardedSpans.mem_language_iff_spans` (`metatheory/Dregg2/Crypto/GuardedSpans.lean`, landed with
this design, sorry-free, `lake env lean` green) — membership in the induced guarded language ⇔
a per-segment span decomposition where literal spans are pinned and hole spans are
guard-attested by the verified matcher. That is *exactly* the conjunction of obligations the
circuit stack discharges, so proving span-wise loses nothing and admits nothing extra.

---

## 0. The substrate (BUILT — verified at HEAD)

### The Dyck parse circuit — the machinery to generalize
- `circuit/src/dsl/dyck_stack.rs:540` `dyck_parse_descriptor` — 23 columns
  (`DYCK_WIDTH = STACK_D + 18`, `:192`), `D = 5` stack cells, `max_degree = 8` **exactly**
  (`:758` — the budget is *fully spent*; see §3.3).
- The grammar is hard-coded at **four distinct sites** (§1 inventories them): the rule-membership
  vanishing `(RULE_ID − 1)(RULE_ID − 2)` (`:600–620`), the per-rule selectors
  `SEL_BRACKET`/`SEL_EMPTY` + their pins (`:598–599`, `sel_pins_rule :243`), the RHS constant
  lanes `LANE_OP/CL/S/ZERO` (`:169–176`, `lane_fixes :502`) feeding
  `push_with_remainder_shift(SEL_BRACKET, [LANE_OP, LANE_S, LANE_CL])` (`:744`), and the rule-table
  commitment `dyck_rule_table_commitment` (`:856`) seeding the running hash via
  `pi[TABLE_COMMITMENT]` (`:700–708`).
- The stack discipline is grammar-*generic* already: `push_with_remainder_shift` (`:458`) takes an
  arbitrary RHS lane list, `pop_shift` (`:484`), `hold_stack` (`:495`), the depth grid
  (`vanishing_on_grid :278`, `:647`), the depth↔occupancy tooth (`occupancy_tooth :394`).

### The Lean side — the general soundness theorem EXISTS
- `Dregg2/Circuit/Emit/DyckStackReplay.lean` — **`parse_sat_imp_replay` is proven for an
  ARBITRARY satisfying trace** (its §4.5; header §"SCOPE": "The general theorem is now PROVEN"),
  via `decode` + `mrun_imp_replay` with the stack as the induction invariant, resting on the
  deployed occupancy tooth (`DyckStackRefine.occupied_of_sat`). The design-doc's multi-month-risk
  item is *behind us* — what remains is re-instantiating it per grammar (§4).
- `Dregg2/Circuit/Emit/DyckStackRefine.lean` — per-row bridge `dyck_sat_imp_row_valid` (`:914`),
  concrete SAT witness (`witTrace_satisfies :989`) + tamper rejections
  (`witTraceBad_not_satisfies :1075`, `witTraceWrapped_not_satisfies :1112`).

### The guarded templater — the target semantics
- `Dregg2/Crypto/HandlebarsGuarded.lean` — `GuardedTemplate` (`:66`): segments = literals + holes,
  each hole carrying a **`PredRE` guard over `Value`** decided by the verified derivative matcher
  (`Deriv/Correctness.lean:267` `correctness : derives w R = true ↔ Matches w R`).
  `guarded_render_mem_language` (`:145`) = generation soundness, guard-parametric.
  **Crucial structural fact** (its header, `:26–29`): the `Value` alphabet is *infinite*, so the
  induced object is NOT a finite `ContextFreeGrammar` — each hole is a **regular leaf**, and
  `guardedToGrammar` (`:117`) composes leaves, not productions.
- `Dregg2/Crypto/HandlebarsGuardedCompose.lean` — `guardedCompose` (`:136`) nests a template
  inside another's hole with guard refinement; `guardedCompose_render_mem_language` (`:218`).
  **Nesting is where the stack comes from** (§2.3).
- `Dregg2/Crypto/GuardedSpans.lean` — **NEW with this design**: `SpanOk`, `spans_compose`,
  `gLang_spans`, `mem_language_iff_spans`, Demo decomposition + tamper rejection
  (`demoSpans_bad_rejected`). Sorry-free, axiom set ⊆ {propext, Classical.choice, Quot.sound}.

### The DFA leaf — already parametric
- `circuit/src/dsl/dfa_routing.rs:126` `dfa_routing_descriptor(name, transitions: &[(u32,u32,u32)])`
  — the transition table is an **input**, interpolated by `TableFunction` (`:164`), committed by
  `compute_table_commitment` (`:336`), route committed at `route_commitment`. 7 columns. This is
  the deployed proof that *per-instance descriptor emission is the pattern*, and it is the leaf
  circuit the holes ride.

---

## 1. Generalizing the rule table (prompt item 1)

### 1.1 The four hard-coded sites, and what each becomes

| Dyck site (BUILT) | general form (PROPOSED) |
|---|---|
| membership `(RULE_ID−1)(RULE_ID−2) == 0` gated on `IS_RULE` (`dyck_stack.rs:600`) | `vanishing_on_grid(RULE_ID, {1..R})` — same idiom, R-point grid, degree R (see §3.3 for the budget) — **or** subsumed by the selector partition (1.2), which already pins `RULE_ID` |
| per-rule selectors `SEL_BRACKET`/`SEL_EMPTY`, partition `IS_RULE`, pinned by `sel_pins_rule` (`:243,:598`) | **R selector columns**, partition `IS_RULE`, each pinned to its rule id — emitted per grammar |
| RHS constant lanes + `push_with_remainder_shift(sel_r, lanes_r)` (`:169,:744`) | one lane per **distinct symbol** appearing in any RHS; per rule `r`, `push_with_remainder_shift(sel_r, lanes_of(rhs_r))` — the builder already takes arbitrary lanes |
| `dyck_rule_table_commitment` = `hash_2_to_1(enc rB, enc rE)` (`:856`) | ordered hash-fold over `enc(rule_i) = hash_4_to_1(id, lhs, …rhs…)` (rules with RHS > 2 symbols chain another `hash_4_to_1`), still seeding `pi[TABLE_COMMITMENT]` |

### 1.2 TableFunction vs per-template emit — the honest resolution

The prompt asks: "a `TableFunction` rule table like dfa_routing uses, **or** a per-template
emit?" The answer is **both, with a sharp boundary**, and the boundary is forced by one fact:

**The stack-shift wiring cannot be table-driven.** `push_with_remainder_shift` (`dyck_stack.rs:458`)
emits, for RHS length `L`, the family `next.STACK[j] = rhs[j]` (j < L), the remainder shift
`next.STACK[j] = local.STACK[j−(L−1)]` (L ≤ j < D), and the overflow guard. The *shift amount*
`L−1` is baked into **which column pairs the `Transition` constraints connect**. A `TableFunction`
can look up `RULE_ID → (lhs, rhs₀…, L)` as *values*, but a value cannot re-wire a `Transition`'s
column indices — a data-dependent shift would need a full barrel-shifter network (D×W selector
products, degree + width blowup) which is *exactly* the per-rule-selector design re-derived, only
worse. So:

- **Per-rule selectors + per-grammar emit** carry the stack threading (each rule's pop∘push is a
  statically-wired constraint group gated on its selector) — this is the Dyck design, kept, made
  R-ary. The emit is a Rust function `guarded_parse_descriptor(name, grammar: &GrammarSpec)`
  mirroring `dfa_routing_descriptor(name, transitions)` — **the deployed precedent for
  per-instance descriptors** (and the Lean mirror follows the per-DFA verified-emitter pattern
  the composed doc names at its "Verified-emitter parametricity" gap).
- **`TableFunction` is still the right tool for rule CONTENT binding** when R grows: one lookup
  `RULE_ID → lhs` replaces R gated `STACK0 == lhs_r` equalities, and (optionally)
  `RULE_ID → enc(rhs)` binds the fired rule's RHS *identity* into `ENTRY_HASH` so the running
  commitment names the rule content, not just its id. Membership comes free from the selector
  partition (∑ sel_r = IS_RULE, sel_r pins RULE_ID = r ⇒ RULE_ID ∈ {1..R} on rule rows).
- **The grammar's identity is pinned cryptographically, not structurally**: `pi[TABLE_COMMITMENT]`
  seeds the running hash (deployed, `:700`), so a proof under grammar G verifies only against
  G's commitment. Per-template emit + per-template VK + table commitment = three nested pins;
  the fold's multi-VK admission (§2.4) consumes the VK one.

**Cost of R-ary generalization:** columns += R (selectors) + |distinct RHS symbols| (lanes) −
the Dyck 2+4; constraints += R selector pins + Σ_r (D + overflow_r) threading gates. For a
template skeleton (§2.2) R is small (≈ 1 + #segment-kinds), so this stays in the tens of columns.

---

## 2. The per-hole guard as a cheap regular leaf (prompt item 2)

### 2.1 Why the guard must NOT enter the stack circuit

A guard is a `PredRE` over `Value` — an **infinite alphabet** (`HandlebarsGuarded.lean:26`). The
stack circuit's cells are range-pinned to a small symbol grid (`symbol_grid`, `dyck_stack.rs:311`;
the occupancy tooth *depends* on the grid being small, §3.3). Hole *content* therefore never
touches the stack: the skeleton consumes **one pseudo-token per hole** (a `SYM_HOLE` marker), and
the content is attested elsewhere. This is not a compromise — it is the composed architecture's
efficiency dial (`DESIGN-composed-attestation-architecture.md` §2): flat recognition goes to the
7-column DFA circuit, ~50× narrower than carrying it through a wide row.

### 2.2 The flat-template skeleton is REGULAR — and that is a feature

A flat `GuardedTemplate` is a *straight-line* composition `lit₀ · hole₀ · lit₁ · …` — its
skeleton language over the marker alphabet is a single word. **No stack is needed for the flat
class**: the skeleton itself can be a `dfa_routing` chain (7 columns) whose "route" is the
segment sequence, with literal steps binding literal-text hashes and hole steps binding the
hole's leaf proof (2.3). The Dyck-stack machinery enters exactly when
`guardedCompose` (`HandlebarsGuardedCompose.lean:136`) nests templates: hole-nesting depth =
stack depth, and the skeleton grammar becomes genuinely context-free
(`S_outer → lit₀ S_inner lit₁ …`). **Depth `D` per descriptor = the composition tree's max
nesting**, which the emitter knows statically — the honest expressiveness bound, same shape as
Dyck's `D = 5` (`dyck_stack.rs:43–49` states the discipline: exceeding D REJECTS, never
mis-proves).

### 2.3 Binding a hole span to its leaf proof

The deployed binding idiom is *committed hash citation* (composed doc §2: "a sub-proof cited by
hash, not a lookup"). Concretely, on a skeleton `hole` row:

- new column `HOLE_COMMIT` carries the hole's DFA `route_commitment` (a full field element —
  which is *why* it gets its own column instead of riding `INPUT_TOKEN`: the tape token must stay
  on the small symbol grid for the range/occupancy teeth);
- `ENTRY_HASH = hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, HOLE_COMMIT)` — the deployed
  `Hash4to1` gate (`dyck_stack.rs:696`) with its fourth lane (today `LANE_ZERO`) re-pointed;
  non-hole rows pin `HOLE_COMMIT = 0` (gated equality). The hole's leaf proof is thereby folded
  into the skeleton's `route_commitment`;
- the **leaf proof** is a `dfa_routing` STARK for the guard's DFA over the hole's span, exposing
  (a) that same `route_commitment` and (b) the guard-table commitment
  (`compute_table_commitment`, `dfa_routing.rs:336`) — pinning *which* guard admitted the span;
- the **fold** (§2.4) checks the citation: the skeleton proof's `HOLE_COMMIT` sequence equals the
  leaf proofs' route commitments, spans abut by offset continuity.

`GuardedSpans.mem_language_iff_spans` is the theorem that this conjunction of obligations —
literal pins + per-hole guard attestations + span continuity — is exactly language membership.

### 2.4 The guard → DFA table pipeline (the real new work)

The guard is a `PredRE` over `Value`; `dfa_routing` wants a finite `(state, symbol) → state`
table over small integer grids. The pipeline is: derivative-automaton construction
(`Deriv/Determinize.lean` exists) + **the `Value ↪ Nat` weld** — the encoding lemma the composed
doc already names as a localized gap (its §"Localized gaps": it closes both the
powerset-table-equality gap at `Deriv/Determinize.lean:171` and the compiler-table↔AIR-table
gap). Two honest sub-problems:

1. **Alphabet finitization.** The derivative construction quotients the infinite alphabet into
   finitely many predicate classes (the leaves' boolean algebra); the circuit-side tape symbol is
   the class id, and the *encoding* of hole bytes → class ids must be part of what the leaf proof
   commits (else the DFA ran on a word nobody pinned). This is the load-bearing weld; it is
   proof + plumbing work, not research.
2. **Fold heterogeneity** (composed doc §2 delta, unchanged): token-span segment endpoints,
   leaf-kind tag, multi-VK root admission in `verify_turn_chain_recursive`
   (`ivc_turn_chain.rs:3696`). Engineering on the existing circuit-agnostic combine.

---

## 3. Per-template descriptor parameterization (prompt item 3)

### 3.1 The emitter

```
GrammarSpec { symbols: Vec<SymbolDef>,            // small-grid ids; EMPTY = 0
              rules:   Vec<RuleDef { id, lhs, rhs: Vec<SymId> } >,
              d_max:   usize }                    // nesting depth bound
guarded_parse_descriptor(name, &GrammarSpec) -> CircuitDescriptor
```

Emits: R selectors + pins; per-rule `push_with_remainder_shift`/`pop_shift` groups (the builders
are already generic, `dyck_stack.rs:458,:484`); lanes for the distinct RHS symbols; depth grid
`{0..D}`; symbol-grid ranges; the occupancy tooth (as revised in 3.3); boundaries verbatim from
Dyck (`:760–804`); PI layout unchanged (`pi::TABLE_COMMITMENT` now the *grammar's* commitment).
A template compiles: flat → a `dfa_routing` skeleton descriptor; nested → a `GrammarSpec` from
the composition tree (one rule per template-expansion, terminals = literal-chunk ids + `SYM_HOLE`
markers) → the stack descriptor. Precedent for per-instance emission + Lean-mirrored constants:
`dfa_routing_descriptor` and the `DyckStackEmit.lean` column map (`:116–197`) — the Lean twin is
emitted per grammar exactly as verified emitters are per-DFA today.

### 3.2 What the commitment pins

`pi[TABLE_COMMITMENT] = H(fold over enc(rule_i))` — the skeleton's grammar. Each hole's leaf
proof pins its own guard-table commitment. The template-level object the SDK exposes is the pair
(grammar commitment, ordered guard commitments) — one hash = "this template, these guards", the
attestable-schema identity the templater signs against.

### 3.3 The degree budget — the one real redesign

Dyck's `max_degree = 8` is *exactly spent*: the occupancy tooth's non-empty-below family is
degree `|non-empty symbols| + i + 1 = 3 + D` at `i = D−1` (`dyck_stack.rs:754–758`), and the
depth-grid vanishing is `D + 1`. Generalizing naively, the tooth costs
**`|alphabet| + D` degree** — a 10-symbol grammar at `D = 5` is degree 15, over budget. The fix
is standard and strictly local: per-cell **binary is-empty indicator columns**
`E[i]` with `E[i] · STACK[i] == 0` (empty ⇒ cell 0) and
`(1 − E[i]) · ∏_{s ∈ nonempty…}` replaced by a second indicator against the cell's range check —
concretely, `E[i]` binary, `E[i]·STACK[i] == 0`, `(1−E[i])·nonzero-witness` via an inverse
column `STACK[i]·INV[i] == 1 − E[i]` (the classic is-zero gadget, degree 2). The occupancy
families become degree ≤ `D + 2` (from the depth products only) independent of alphabet size,
at a cost of `2D` extra columns. Depth-grid vanishing degree `D + 1` remains the binding term —
so `max_degree` caps `D ≤ 7` at the deployed `MAX_CONSTRAINT_DEGREE = 8`, or the depth range
also moves to a bit-decomposition/lookup for deeper nesting. **Stated bound: alphabet size is
now free; nesting depth D remains the capped resource.**

---

## 4. The Lean story per template

- **Semantics: parametric, DONE.** `guarded_render_mem_language`, `guardedCompose_*`, and now
  `GuardedSpans.mem_language_iff_spans` are template-parametric theorems — no per-template Lean
  needed at the semantic layer.
- **Refinement: per-descriptor, emitted.** `DyckStackRefine`/`DyckStackReplay` are stated
  against the concrete `dyckDesc`. The general `parse_sat_imp_replay` proof *structure* (decode,
  `MRun`, stack invariant, occupancy readout) is grammar-generic in all but the per-rule case
  analyses (`bracketPush`/`emptyPop` become one case per rule). Route: emit the per-grammar
  refinement file alongside the descriptor (the per-DFA verified-emitter pattern), or invest in
  the rule-indexed parametric proof once — the former is weeks and mechanical, the latter is the
  long-pole quality item. **First slice takes the former.**
- **The span weld closes the loop:** skeleton `parse_sat_imp_replay` gives the segment
  decomposition; leaf soundness (`route_commitment_binds_trace` + `correctness`) gives per-hole
  `derives = true`; `spans_compose` lands the render in `(guardedToGrammar T).language`.

---

## 5. FEASIBILITY VERDICT

**Weeks for the flat-template path end-to-end; the nested path is weeks of engineering on the
proven Dyck machinery plus one contained proof-effort item; the genuinely new work — the
guard→DFA-table weld — is the named risk, itself a known, localized gap (not research).**

Grounds:
- Every circuit primitive ships and is exercised: the generic stack builders
  (`push_with_remainder_shift`/`pop_shift`, already RHS-parametric), `vanishing_on_grid`,
  `Hash4to1`/`SeedHash2to1`/`ChainedHash2to1`, the parametric `dfa_routing_descriptor`, the
  fold. **No new prover, field, or FRI.**
- The design-doc's feared multi-month item — the multi-row inductive refinement — **is already
  proven** (`DyckStackReplay.parse_sat_imp_replay`, general form). Generalizing it is case-count
  growth, not new proof architecture.
- The semantic factorization justifying the split **landed with this design and builds**
  (`GuardedSpans.lean`).

Hard parts (honest, ranked):
1. **The `Value ↪ Nat` weld + alphabet finitization** (§2.4) — the pipeline from a `PredRE`
   guard to a committed finite AIR table with a proven encoding. The composed doc's named gap;
   the one item with month-scale risk if `Determinize.lean`'s residual is deeper than it looks.
2. **Fold heterogeneity** — span endpoints, leaf-kind tags, multi-VK admission. Deployed combine
   is circuit-agnostic; this is engineering, ~1–2 weeks.
3. **The degree-budget redesign of the occupancy tooth** (§3.3) — mechanical (is-zero gadget),
   but it touches the proven refinement's occupancy lemmas (`occupied_of_sat`), which must be
   re-proven against the indicator form. Days-to-a-week each side.
4. **Per-grammar Lean emission** — mechanical per-template refinement files until the
   rule-indexed parametric proof is written. Accepted debt, tracked.
5. **Uniqueness/ambiguity is out of scope for soundness** — two abutting permissive holes are
   ambiguous *as language members*; `HandlebarsGuardedUniqueness`'s delimiter-guarded class is
   where the inverse lives (its residual, unchanged by this design). `SpanOk` deliberately
   attests per-occurrence spans, not per-id equality of repeated holes — the id-equality pin
   belongs to the witness layer (`HandlebarsGuardedWitness`), not the language.

**Smallest first slice** (the concrete next PR, ~days):
- **Template:** the fixed 2-literal-1-hole flat skeleton `lit₀ ⟨hole g⟩ lit₁` — as a *stack*
  descriptor (not the dfa_routing shortcut), to exercise the generalization: `GrammarSpec` with
  rules `{rTemplate : S → t₀ H t₁}` (R = 1), symbols `{S, t₀, t₁, H}`, `D = 3`.
- **Circuit:** new module (do NOT edit `dyck_stack.rs`) reusing its public builders; R-ary
  selector partition degenerate at R = 1; `HOLE_COMMIT` column + re-pointed `Hash4to1` fourth
  lane; grammar commitment as the running-hash seed. Witness: the honest 5-row run
  (`rule · term t₀ · hole · term t₁ · done`).
- **Tamper canary** (the tooth that makes it real, per `dyck_parse_tamper.rs` precedent): (a)
  wrong literal token, (b) `HOLE_COMMIT ≠ 0` on a non-hole row, (c) mutated `HOLE_COMMIT` on the
  hole row vs the cited leaf commitment at the fold seam, (d) wrapped depth — each REJECTS.
- **Leaf:** instantiate `dfa_routing_descriptor` with the `noDoubleBraceRE` guard's 2-state DFA
  table (hand-derived for the slice; the pipeline of §2.4 replaces the hand step later), pin its
  `route_commitment` into the skeleton witness's `HOLE_COMMIT`.
- **Lean:** the slice's semantic target is already proven (`mem_language_iff_spans` +
  `noDoubleBraceRE_iff`); the per-descriptor refinement file follows the `DyckStackRefine`
  template in a later slice.

---

## Appendix — status ledger

| element | status |
|---|---|
| Dyck stack circuit, generic builders, occupancy tooth, depth range | **BUILT** `dyck_stack.rs:458,484,394,647` |
| general SAT⇒Replay soundness (arbitrary trace) | **BUILT (proven)** `DyckStackReplay.lean` §4.5 |
| guarded templater semantics + compose + guards-by-verified-matcher | **BUILT (proven)** `HandlebarsGuarded.lean:145`, `HandlebarsGuardedCompose.lean:218` |
| parametric DFA leaf descriptor + table commitment | **BUILT** `dfa_routing.rs:126,336` |
| **span factorization (membership ⇔ attested spans)** | **BUILT with this design** `GuardedSpans.lean` (`mem_language_iff_spans`) |
| R-ary rule table via per-rule selectors + emit; TableFunction for content binding | **PROPOSED** (§1) |
| hole leaf citation (`HOLE_COMMIT` + Hash4to1 fourth lane) | **PROPOSED** (§2.3) |
| guard → finite DFA table (Value↪Nat weld) | **PROPOSED, the named risk** (§2.4) |
| occupancy tooth degree redesign (is-zero gadget) | **PROPOSED** (§3.3) |
| fold heterogeneity (spans, leaf tags, multi-VK) | **PROPOSED** (§2.4, composed doc delta) |
| 2-lit-1-hole skeleton + leaf + tamper canary | **PROPOSED first slice** (§5) |
