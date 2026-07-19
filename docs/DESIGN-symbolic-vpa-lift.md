# Does the finite-alphabet VPL decidability lift to the templater's real guards? — symbolic VPA over `Pred`, adjudicated

> **Superseded implementation-status note (2026-07-19).** The conditional feasibility argument in
> this document has since been realized for the *regular* `PredRE` rung: registered modules now
> provide general symbolic minterm covers, unbounded emptiness and language-equivalence decisions,
> and runnable adaptive fixpoints over the infinite `Value` alphabet.  The useful leaf fragment has
> also widened through `symMemberOf`, `allOf`/`anyOf`, and scoped `digFieldEq` covers.  Thus the
> passages below saying that `PredSat`, `PredRE` emptiness, or infinite-alphabet equivalence are
> absent describe the earlier audit state, not HEAD.  The genuinely remaining campaign described
> here is the *symbolic VPA* lift for visibly nested protocols (plus each explicitly fail-closed
> predicate-cover frontier), not the already-landed flat symbolic-DFA decision.

A feasibility assessment, not advocacy. `Crypto/VpaDecidable.lean` just proved **unconditional,
computable, decidable template equivalence** on the finite `Sym = {op, cl, dat}` fragment
(`decidable_template_equivalence`, `VpaDecidable.lean:1624-1637`, kernel-`#guard`ed both answers).
The templater's real guards are `PredRE` over the **infinite** `Value` alphabet
(`HandlebarsGuarded.lean:19-21` states this outright). Two positions on whether the decidability
lifts:

- **Position A** (`docs/DESIGN-visibly-pushdown-reframe.md` §4.1 and its Recommendation,
  `:272-275`): the infinite alphabet needs symbolic **or register/nominal** automata; the lift
  "forfeits the free determinizability, complement, and decidable-equivalence results"; the marquee
  wins "transfer cleanly only to the **finite** fragment."
- **Position B** (the thesis under test): **symbolic** automata over an **effective boolean
  algebra** (EBA) of labels preserve all of it — determinization, complement, decidable
  equivalence — and dregg's guard algebra plausibly *is* an EBA, so Position A conflated
  "symbolic" with "register."

Adjudicated against HEAD below. Short answer: **Position B is structurally right and Position A's
operative conclusion is refuted — but Position B misidentifies the algebra and misstates the
evidence, and the one EBA ingredient that actually decides the question is absent at HEAD.** The
decidability lifts **conditionally**: for every guard fragment whose leaf `Pred`s have a decidable
satisfiability — which includes **every guard the templater writes at HEAD** (discharged by a
slice landed with this doc) and, in principle, essentially the whole ctx-less atom catalog, at the
price of a verified decision procedure that is the real cost of the whole program.

---

## 0. The theory both positions appeal to, stated checkably

**Symbolic finite automata** (Veanes et al.; D'Antoni–Veanes) and **symbolic visibly pushdown
automata** (Alur–D'Antoni, CAV 2014) replace the finite alphabet by transition labels drawn from a
boolean algebra of predicates over an arbitrary (possibly infinite) domain. The closure and
decidability results — product, complement, **determinization**, **decidable
equivalence/emptiness** — all go through *provided the label algebra is an EBA*:

1. predicates closed under `∧`/`∨`/`¬` with the boolean operations **semantically correct**;
2. **decidable satisfiability** — given a predicate, decide whether *some* domain element
   satisfies it;
3. computable predicate operations (so products/minterms can be formed).

The constructions never enumerate the alphabet; they enumerate **minterms** — the ≤ 2^k
satisfiable conjunctions of the finitely many predicates appearing on the machines' edges — and
consult the satisfiability oracle to know which minterms are inhabited. **Register/nominal
automata are a different device** (state carries data values; equality with *stored* registers),
and those genuinely do lose determinizability and complement. The two are not the same, and which
one dregg needs is exactly what decides this question.

One caveat carried from the s-VPA paper: full s-VPAs allow **binary** return predicates (the
return symbol constrained against the *popped call symbol* — how `<a>…</a>` tag-matching works).
Determinization still holds but the oracle must decide satisfiability of two-variable predicates.
The unary fragment (labels constrain only the current symbol) needs only the one-variable oracle.
Everything below is stated for the unary tier first; §5 prices the binary tier.

---

## 1. Is the guard algebra an EBA? — the crux, atom by atom

First, a correction to Position B's framing: **the EBA carrier for a symbolic VPA is `Pred`, not
`PredRE`.** An s-VPA transition reads *one frame*; its label is a one-frame predicate — dregg's
`Pred` (`Exec/PredAlgebra.lean:127-183`), read through the matcher's leaf decision
`PredRE.leaf φ a = Pred.eval φ ∅ a` (`Deriv/Core.lean:73`). `PredRE` (`Core.lean:39-54`) is the
*word-level* guard language; it enters the picture as the thing that **compiles into**
predicate-labeled automata via the derivative tower (§2). Position B's phrase "symbolic VPA over
PredRE" is a category slip — harmless for the verdict, but the obligations land on `Pred`.

Now the three EBA ingredients against HEAD:

**(1) Boolean closure, semantically correct — HAVE, proved.** `Pred` carries `and`/`or`/`not` at
every level (`PredAlgebra.lean:135-139`) and the semantics are the boolean operations by `rfl`:
`eval_not` (`:263`), `eval_and` (`:271`), `eval_or` (`:275`), De Morgan (`:279-286`). This half of
the EBA is unconditionally in hand.

**(2) Computable predicate operations — HAVE, trivially.** The operations are constructors;
minterm formation is syntactic.

**(3) Decidable satisfiability — ABSENT AT HEAD, and it is the entire question.** Nothing in the
tree decides `∃ a : Value, Pred.eval φ ∅ a = true` for any class of `φ` (grep: no
satisfiability/emptiness decision exists anywhere under `Deriv/` or `Exec/`). Position B's cited
evidence — "`PredRE` … with a DECIDABLE membership (`derives`) and decidable emptiness" — is
**wrong on both counts as support**: `derives` (`Core.lean:110`) is decidable *membership* (given
a word, evaluate), which is not satisfiability; and `PredRE` **emptiness is not decidable at
HEAD** — no such decision exists, and it cannot exist without the `Pred`-sat oracle (§2 shows
emptiness *reduces to* that oracle; it does not precede it). `Pred.eval` being `Bool`-valued makes
every *ground instance* decidable; the EBA needs the *existential over the infinite `Value`*.

So: **is `Pred` satisfiability decidable in principle?** This decomposes over the atom catalog
(`Exec/Program.lean:56-267` `SimpleConstraint`, `:269-420` `StateConstraint`, plus the typed
`sym`/`dig` leaves of `PredAlgebra.lean:151-183`), in the single-frame leaf reading the matcher
uses (`old := .record []`, `Core.lean:64-73`):

| Atom class | Leaf-reading behavior | Sat decidable? |
|---|---|---|
| `tt` / `ff` | constants | trivially (landed, §4) |
| `symEq`, `digEq`, `symMemberOf`, `memberOf`, `fieldEquals` | typed field read = / ∈ finite set | yes — witness by construction (single atom landed, §4) |
| `fieldGe/Le`, `inRangeTwoSided`, `sumEquals`, `affineLe`, `affineEq`, `fieldLeField`, `prefixOf` | QF linear integer arithmetic over scalar field reads | yes in principle (Presburger/ILP feasibility) — **verified decision is the expensive tier** |
| `digFieldEq`, `fieldEqField` (+ negations) | equality/disequality constraints over one free record | yes — equality logic over an infinite domain; small-model argument |
| `immutable`, `writeOnce`, `monotonic`, `strictMono`, `fieldDelta`, `deltaBounded`, `affineDeltaLe*`, `symUnchanged/Changed`, `digUnchanged/Changed` | read absent `old` → constant (`true` for first-write-permissive, `false` for fail-closed; `Core.lean:68-70`) | trivially |
| `clearanceGe`, `reachable` | fixed finite `ClearanceGraph` baked into the atom; reduces to a computable admissible-label set membership | yes |
| `senderIs`, `senderInField`, `balanceGe/Le`, `preimageGate`, `delegationEpochEquals`, `countGe`, `observedFieldEquals`, `boundDelta` | ctx-less evaluation is fail-closed constant (e.g. `boundDelta` rejects every single-cell transition, `Program.lean:884-886`) | trivially |

**No atom has undecidable satisfiability in the leaf reading.** The whole ctx-less catalog is
quantifier-free LIA + typed equalities + finite memberships over one free record — a decidable
theory (a QF-LIA/EUF-style combination). So the mathematical content of Position B's thesis holds:
`Pred` **is plausibly an EBA**, and Position A's clause 3 escape hatch ("if Pred leaves have
undecidable satisfiability, Position A wins") does **not** fire — for the ctx-less carrier.

Two honest boundaries on that "yes in principle":

- **In principle ≠ in Lean.** A `Decidable (PredSat φ)` for arbitrary `φ` is a verified
  mini-SMT: the SAT side is cheap (exhibit a witness, `Pred.eval` checks it), but the **UNSAT side
  of the LIA tier needs a verified integer-feasibility decision** — `omega` is a tactic, not a
  `Decidable` instance over an existential on `Value`, and Mathlib ships no Presburger decision
  procedure. That build is the dominant cost of the entire lift (§5).
- **The stateful carrier flips one leaf class.** `Core.lean:16-18` notes the stateful `(old,new)`
  carrier is not built. If it is, `preimageGate` stops being a fail-closed constant and its
  satisfiability becomes *hash inversion* — a leaf class that is decidable only in the useless
  classical sense. On that future carrier, Position A's caution genuinely bites for the
  crypto-portal atoms, and the lift must exclude them (they'd sit outside the EBA fragment). This
  is the one place a "which leaves are decidable" split has real teeth.

---

## 2. What already exists on the `PredRE` side — more than either position credits

The derivative tower under `Crypto/Deriv/` has already built, kernel-clean and `sorry`-free, most
of the *regex-to-symbolic-automaton* leg that Position B's pipeline needs:

- **`correctness`** (`Deriv/Correctness.lean:267`) — `derives ↔ Matches`, the verified matcher.
- **Symbolic derivative** — `derivative : PredRE → TTerm Pred PredRE`
  (`SymbolicDerivative.lean:35-43`): the transition structure *already branches on `Pred`
  labels*; `step`/`steps` (`:50`, `:74`) enumerate the symbolic state space.
- **Brzozowski finiteness** — `der_finite` (`Finiteness.lean:298`): finitely many derivatives up
  to language-sound ACI similarity (`Similarity.lean`). The symbolic automaton of any `PredRE`
  guard has a **finite state space**.
- **`derivativeTable_finite` / `tableDfa_faithful`** (`TableDfa.lean:166`, `:133`) — a finite
  table DFA recognizing the guard's language exists and table-language-agreement is a theorem.

So "compile a `PredRE` guard to a finite symbolic DFA" is not speculative — its hard combinatorial
core is **done**. What is missing is exactly one thing, visible in the definition of `step`:
`step r = leaves (𝜕 r)` (`SymbolicDerivative.lean:50`) collects **all** `TTerm` leaves,
**ignoring the branch conditions**. The reachable-state exploration is a sat-free
*over-approximation*: a leaf is listed even when the boolean valuation of `Pred` conditions
leading to it is satisfied by **no actual `Value`**. Consequences, stated precisely:

- For *finiteness* (what Stage 3 needed), the over-approximation is harmless — a superset of the
  reachable set being finite is exactly right.
- For **emptiness/equivalence decisions** it is fatal: deciding `∃ w, derives w R` as "some
  `null`-state is `step`-reachable" would be **unsound** (it can report words that no `Value`
  sequence realizes). The fix is sat-filtering: explore per **minterm** of the leaf `Pred`s of
  `R`, keeping a branch iff the minterm is satisfiable. That consult is the EBA oracle, and it is
  the *only* missing ingredient between the landed tower and decidable `PredRE`
  emptiness/equivalence.

This sharpens the adjudication: Position A's "transfers cleanly only to the finite fragment"
undercounts what HEAD already has (a finite symbolic state space over the infinite alphabet,
proved); Position B's "decidable emptiness" overcounts it (the decision does not exist until the
oracle does).

---

## 3. Does `VpaDecidable`'s proof structure survive the symbolic substitution?

Checked construction by construction. The striking structural fact: **`VpaDecidable.lean` never
enumerates the alphabet.** `Sym` has exactly one symbol per class (`VpaAsCert.lean:65-77`), no
`Fintype Sym` instance exists or is used, and every `Fintype`/`DecidableEq` hypothesis in the file
is over **states and stack symbols** (`:832-835`, `:1026-1039`) — which remain finite in the
symbolic setting (guard-automaton states are derivative classes, finite by `der_finite`; stack
alphabets are the machines' own, not data). The file is, in effect, already a symbolic VPA whose
per-class label happens to be `⊤`. The substitution map:

| Finite-fragment object (HEAD) | Symbolic replacement | New obligation |
|---|---|---|
| `Vpa` transitions `State → Sym → State → Gamma → Prop` (`VpaAsCert.lean:112-118`) | finitely many `Pred`-labeled call/ret/int edges; input `List (SymClass × Value)` (tagged nested-word presentation) | none (representation) |
| `prodVpa` + `prodVpa_lang` (`VpaDecidable.lean:106`, `:337-395`) | labels conjoin via `Pred.and`; zip/proj arguments are class-driven and alphabet-agnostic | only `eval_and` semantics — already proved. **Survives near-verbatim.** |
| `WM` summary rules (`:641-647`) | edge traversable ⇔ its label **satisfiable**; the wrap rule's call and return sat-checks are independent in the unary tier | `Decidable (PredSat φ)` — the oracle, entering exactly here |
| `satStep`/`sat` saturation + pigeonhole (`:840-849`, `:856`) | filter predicate consults `PredSat` per edge instead of `Decidable (M.int q Sym.dat q')`; `Finset (S × S)` grid unchanged | same oracle; pigeonhole untouched |
| `detVpa` (`:1371-1376`) — transitions ignore the symbol entirely (one symbol per class) | determinized transitions branch per **minterm** of the machine's label set: `relInt` (`:1338`) becomes one `relInt_m` per minterm m | minterm exhaustiveness/disjointness — an *eval-level* fact per frame (no oracle needed); the oracle only prunes empty minterms in the computable decision |
| `det_invariant` (`:1415`) snoc induction | per-word, per-frame; each read frame falls in exactly one minterm; the induction restructures per-minterm but the invariant (`DChain`) is unchanged | proof effort, no new mathematics |
| `decidable_template_equivalence` (`:1624`) | hypotheses become: finite edge lists + `Decidable (PredSat ·)` on the closure of both machines' labels under `∧`/`¬` | the EBA interface, literally |

**Answer: yes, the structure survives.** The load-bearing VPL fact — stack height determined by
the input (`stack_height_input_determined`, exploited in the zip direction of `prodVpa_lang` and
in `detVpa`'s lockstep) — is class-driven and cardinality-blind. No step of the existing proof
uses finiteness of the alphabet; the finite-`Sym` specificity is confined to (i) the trivial
one-symbol-per-class transition shapes and (ii) the `Decidable` instances on transition relations,
both of which are exactly where the EBA operations slot in. Determinization is the only
construction that *grows* (minterm branching, the known 2^k factor on top of the
Alur–Madhusudan exponential — matching the s-VPA paper's complexity).

One question the lift does **not** answer, flagged so it is not smuggled: **who assigns the
call/return/internal classes to raw `Value`s.** The reframe doc's §2 argument stands untouched —
the faithfulness of the visible partition *is* `Excludes`/`Separated`, and `abutting_ambiguous`
remains outside any partition. Two clean routes: carry the class **structurally** in the wire
format (tagged nested words — free in a receipts world), or assign classes by three predicates
whose pairwise-disjointness check is itself an UNSAT query to the same oracle. Either way the
alphabet-cardinality question (this doc) and the partition-faithfulness question (reframe doc §2)
are orthogonal, and Position B's win on the former moves nothing on the latter.

Also worth saying because it is cheaper than the headline: **the flat templater needs no VPA at
all.** A flat guarded template's language is a concatenation of regular leaves
(`HandlebarsGuarded.lean:97-111`) — *symbolic DFA* equivalence (derivative tower + oracle +
minterm product/complement) already decides flat template equivalence. The symbolic **VPA** rung
is needed only for the composed/nested case (`HandlebarsCompose`).

---

## 4. What was landed with this doc — the oracle's first slice

`metatheory/Dregg2/Crypto/Deriv/SatOracle.lean` (**unregistered** — no import chain touched;
builds standalone: `lake env lean Dregg2/Crypto/Deriv/SatOracle.lean`, `#assert_all_clean`
7 keystones, no `sorry`):

- **`PredSat φ := ∃ a : Value, PredRE.leaf φ a = true`** — the EBA obligation, stated over the
  real alphabet.
- `Decidable` instances, witness-backed, for: `tt` (sat), `ff` (**unsat** — the one negative
  answer, so the oracle is not vacuously `isTrue`), `symEq f s` and `not (symEq f s)` for
  **every** field/symbol.
- **`deployed_guard_minterms_decided`** — both minterms (`braceP`, `¬braceP`) of the leaf algebra
  generated by the guards the templater actually writes at HEAD
  (`HandlebarsGuarded.lean:162` — every deployed guard's leaf set is `{braceP}` ∪ `{tt, ff}`)
  are decided, reusing the deployed `leaf_braceP_brace`/`leaf_braceP_data` (`:170-172`).

Honest scope of the slice: it is the *witness* side for a specific fragment. It does not decide
`PredSat` of an arbitrary `Pred` — but it is sufficient oracle for every minterm a symbolic
determinization of the **currently deployed** guards would generate. The lift is therefore not
blocked on the expensive tier for the guards that exist; the expensive tier prices *future*
guards.

---

## 5. Cost, tiered

| Tier | Work | Cost | Unlocks |
|---|---|---|---|
| 0 | `PredSat` + deployed-minterm decisions | **landed** (SatOracle.lean) | oracle for every guard at HEAD |
| 1 | sat for the boolean closure over `symEq`-family atoms (small-model lemma: truth depends only on mentioned fields; candidates = none / mentioned constants / fresh) | days | oracle for any guard over typed identity/enum leaves |
| 2 | sat-filtered derivative exploration ⇒ `Decidable (∃ w, derives w R)` (reuses `der_finite` + minterms) | days–week | **`PredRE` guard emptiness/inclusion — the first user-visible decision** |
| 3 | symbolic DFA product/complement over minterms ⇒ decidable **flat** template equivalence | ~week | flat templater equivalence, no VPA needed |
| 4 | symbolic VPA port of `VpaDecidable` (unary labels, tagged classes; §3 substitution map) | 1.5–2× the 1679-line original — a focused campaign | **composed/nested template equivalence over real guards** |
| 5 | LIA-atom sat (verified integer feasibility, UNSAT certificates) | weeks; the genuinely expensive item | guards using affine atoms (none exist at HEAD) |
| 6 | binary return predicates (return constrained against call data) | s-VPA-paper machinery; two-variable oracle | data-matching delimiters — **not needed** for the current fixed-delimiter discipline; defer |

Tiers 0–4 never touch tier 5: the deployed guard language sits entirely in the cheap fragment.

---

## 6. Verdict

**1. Is `Pred`(RE's leaf algebra) an EBA?** Two of three ingredients are proved at HEAD (boolean
closure with correct semantics; computable operations). The third — decidable satisfiability —
exists for no fragment at HEAD *before this doc's slice*, holds **in principle for the entire
ctx-less atom catalog** (no leaf class fires Position A's undecidability escape; the only genuine
future exception is the crypto-portal atoms under the not-yet-built stateful carrier), and is now
**discharged by witness for the deployed guard fragment**. So: *yes, in the mathematical sense;
partially and growably, in the machine-checked sense.*

**2. Does the decidability lift?** **Yes — for the decidable-sat fragment, which is currently
every guard that exists**, via symbolic VPA (unary tier), with `decidable_template_equivalence`'s
proof architecture surviving the substitution (§3): the alphabet was never enumerated, the oracle
slots in exactly where the transition-`Decidable` instances sit, and determinization pays the
standard minterm factor. Not "fully" in the unconditional sense — the lift is forever conditioned
on the leaf fragment's oracle, which is the EBA discipline, not a defect.

**3. Position A vs Position B.** Position A's §4.1 *first sentence* was already correct and
already contained Position B (symbolic preserves the results iff the leaf theory qualifies — "that
is itself a slice to prove"). What is **refuted** is Position A's operative conclusion
(`reframe.md:272-275`): "forfeits the … determinizability, complement, and decidable-equivalence
results" and "transfer cleanly only to the finite fragment" — the results are **conditioned, not
forfeited**, the condition is dischargeable (tier 0 landed; nothing at HEAD needs the expensive
tier), and register/nominal automata — which do forfeit them — are the wrong device for this
problem: dregg's guards never store data values for later comparison; they constrain each frame by
a predicate. That is the definition of the symbolic, not the register, setting. Position A
conflated them in its conclusion. Position B is right on the structure and wrong on the details:
the EBA is `Pred` not `PredRE`, and "decidable membership + decidable emptiness" was one true
claim and one false one — membership (`derives`) is not satisfiability, and emptiness is
downstream of the oracle, not evidence for it.

**4. The "one `Value`→`Nat` weld unlocks both frontiers" claim: WRONG — on both sides.** An
injection `Value ↪ Nat` leaves the alphabet infinite; finite-alphabet VPL theory gains nothing
from it (no subset construction enumerates `Nat`), so the weld is **not sufficient**. And the
symbolic route needs no recoding at all — the finite object is the minterm algebra of the
predicates on the machines, not any coding of the domain — so it is **not necessary**. The correct
unlock is the sat oracle + minterms: the *predicate-generated* finite quotient of the alphabet,
which is what the weld intuition was reaching for, built per-machine instead of globally.

**5. Smallest next slice** (tier 2, the first decision a user can feel):
`Decidable (∃ w, derives w R)` for `R` over the deployed leaf fragment — sat-filtered reachability
on the derivative automaton, reusing `der_finite` (`Finiteness.lean:298`) for termination and
`SatOracle.PredSat` for branch pruning, with soundness against `Matches` via `correctness`
(`Correctness.lean:267`). Its statement is one line; everything it needs except the minterm
filtering is already in the tree.

---

*Register note: this doc lands one unregistered Lean file (`SatOracle.lean`, builds clean) and
changes nothing else. The classification it makes: the infinite-alphabet wall of the reframe doc
is not the register-automata wall; it is the EBA-oracle toll booth, the deployed guards have
already paid, and the partition-faithfulness wall (`Excludes`) is a different wall that symbolic
VPA does not touch.*
