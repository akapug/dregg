# RESEARCH — the predicate / caveat / datalog language uplift (read-only scoping pass)

Source-verified 2026-06-23 against HEAD. The governing design doc is
`.docs-history-noclaude/rebuild/metatheory/_POLICY-LANGUAGES-REFRESH.md` (the D0–D9 worklist). **This research pass corrects that
doc against the actual source: most of D0–D5 is BUILT, not pending.** Every claim below cites
`file:line`; trust the code, not the harvest.

---

## 1. WHAT EXISTS IN SOURCE NOW

### The predicate atom set is LARGE and the new atoms are already built (D0–D2 DONE)

`StateConstraint` (`Dregg2/Exec/Program.lean:269-…`) and its `SimpleConstraint` sub-layer
(`Program.lean:56-96`) carry, in source today:

- **`SimpleConstraint`** (`:56-96`): `fieldEquals` `:58`, `fieldGe` `:60`, `fieldLe`, `immutable`
  `:64`, `writeOnce`, `monotonic`, `strictMono`, `fieldDelta`, `not`, **`memberOf`** `:81`,
  **`prefixOf`** `:88`, **`inRangeTwoSided`** `:92`, **`deltaBounded`** `:96`. Evaluator `evalSimple`.
- **`StateConstraint`** (`:269-…`): `simple` `:271`, `fieldLeField`, `sumEquals`, `sumEqualsAcross`,
  `fieldDeltaInRange`, `allowedTransitions`, `anyOf`, `boundDelta` `:289`, **`clearanceGe`** `:298`,
  **`affineLe`** `:303`, **`affineEq`** `:306`, **`reachable`** `:313`, **`affineDeltaLe`** `:328`,
  **`affineDeltaLeField`** `:343`, **`observedFieldEquals`** `:344`. Evaluator `evalConstraint`.

So the four atoms the prompt names as "to add" — `memberOf`, `prefixOf`, two-sided arithmetic
(`inRangeTwoSided` + `affineLe`/`affineEq`/`affineDeltaLe`), nested Boolean — **already exist** with
admit-characterizations and non-vacuity `#guard`/`by decide` pairs (e.g. `prefixOf` admit-char
`Program.lean:730`, demo `:932-941`; `clearanceGe` admit-char + soundness `:697,711`).

### `clearanceGe` is NOT orphaned — it is fully wired (D0 DONE)

The harvest's "orphaned `clearanceGe`" is stale. In source `clearanceGe`:
- is a `StateConstraint` constructor with an arm in `evalConstraint` (`Program.lean:546`);
- has `evalConstraint_clearanceGe_iff` (admit-char, `:697`) and `evalConstraint_clearanceGe_sound`
  (semantic-dominance soundness, `:711`), both `#assert_axioms`-pinned (`:1034-1035`);
- is **wired into the executor-enforced surface**: `RecordKernel.SlotCaveat.clearanceGe`
  (`RecordKernel.lean:127`), evaluated in `SlotCaveat.eval` (`:156`), with a live demo in
  `EffectsState.lean:1025`. It reuses the proved-sound `ClearanceGraph.dominatesD`.

### The uniform Boolean algebra `Pred` is BUILT (D3 DONE)

`Dregg2/Exec/PredAlgebra.lean` is the clean Heyting/Boolean algebra the doc §B.1(ii) asked for:
`Pred` (`:127`) = `atom (c : StateConstraint) | tt | ff | and | or | not | allOf | anyOf` PLUS a typed
identity/ownership/enum leaf family (`symEq`/`symMemberOf`/`digEq`/`digFieldEq`/`fieldEqField`/
`symUnchanged`/`symChanged`/`digUnchanged`/`digChanged`, `:153-182`). It has:
- the no-op embeddings (`ofSimple_eval`/`ofConstraint_eval`/`ofProgram_eval`, `:239-257`) — every
  legacy program lifts to a `Pred` with the SAME truth value;
- the Boolean laws (De Morgan `:279,284`, double-negation `:266`, the meet/join cons laws);
- per-atom admit-chars + non-vacuity teeth (owner-may-act, no-self-transfer, status-∈-enum,
  `typed_atoms_discriminate` `:489`, `typed_atoms_fail_closed_on_type` `:503`);
- **the live-leg executor adapter** `PredCaveat` + `predStateStepGuarded` (`:556-619`) with
  `predStateStepGuarded_eq` (`:591`, the safety net: the gate only restricts the domain, never mutates
  the post-state), so every `stateStep` keystone lifts verbatim. `#assert_axioms`-clean throughout.

### The `boundDelta` enforcement-gap is FIXED — now fails CLOSED (D4 DONE)

The doc flagged `evalConstraint … boundDelta => true` as a fail-OPEN hole. In source it is
`| .boundDelta _ _ _ _, _, _ => false` (`Program.lean:538`), with the theorem
`evalConstraint_boundDelta_fails` (`:691`) and non-vacuity demos (`boundDeltaProgram`, `:885-889`)
proving a `boundDelta`-only program now REJECTS every single-cell transition.
`#assert_axioms evalConstraint_boundDelta_fails` (`:1033`).

### `dischargeCoordinated` is PROVED **and welded** into the forest gate (D7 DONE)

The harvest's "standalone, not welded" is stale. In source:
- `Dregg2/Exec/CoordinatedCaveat.lean:95` defines `dischargeCoordinated` over the proved
  atomic-snapshot equalizer `jointApplyCaveated`, with `coordinated_discharge_sound` (`:111`),
  `coordinated_no_toctou` (`:123`), `coordinated_refines_failclosed` (`:145`), and the
  bridge `coordinated_tier_discharges_via_equalizer` (`:168`) — all `#assert_axioms`-pinned.
- **The weld exists**: `FullForestAuth.GatedCaveat` now carries a `cross : Option (RecChainedState →
  Bool)` field (`:244`) and `GatedCaveat.holds` (`:254`) routes `.coordinated` THROUGH it
  (`some φ => φ s`, `none => false`, `:256-259`) — the equalizer welded inline on the SAME atomic
  snapshot the node commits against. `Dregg2/Exec/CoordinatedForestGate.lean` and
  `CoordinatedForestGLift.lean` carry the bilateral/`RecChainedState` lift with refinement proofs
  (`coordinated_forest_refines_bilateral` `:191`, `coordinated_intra_gate_failclosed` `:187`).

### `Caveat.local` is STILL OPAQUE — the one genuinely-open item (D6 NOT done)

`Dregg2/Authority/Caveat.lean:38-40`:
```lean
inductive Caveat (Ctx Gateway : Type) where
  | local      (check : Ctx → Bool)      -- ← opaque function, NOT an AST
  | thirdParty (gateway : Gateway)
```
`Caveat.ok` folds it as `check ctx` (`:47`). There is **no** `CaveatPred`/`Caveat.pred` AST anywhere
(grep `CaveatPred|Caveat.pred|appAction|featureGlob|DreggGrant` over `Dregg2/` → zero hits). The
executor-side `GatedCaveat.check` (`FullForestAuth.lean:238`) is likewise an opaque
`RecChainedState → Bool`. This is the real reification gap.

### The FORKED-ALGEBRA situation (the doc's standing warning, now THREE algebras)

There are now **three** parallel record-predicate algebras, not one:
1. `Pred` over `StateConstraint` (`PredAlgebra.lean`) — the developer/`SlotCaveat`-adjacent surface.
2. `RelPred` over `RelCaveat` (`Dregg2/Authority/RelationalClosure.lean:13`) — a general affine
   half-space atom `Σcᵢ·record[fᵢ] ≤ k` closed under Boolean connectives, with a bounded-circuit
   budget proof (`constraintBudget ≤ sizeBound`). A *different* clean algebra over a *different* atom.
3. `Spec.Guard` (`Dregg2/Spec/Guard.lean:90`) — the abstract `firstParty|witnessed|all|any|gnot`
   verify-seam guard (the `admits_sumEquals`/`senderAuthorized`/`nonMembership`/`oneOf` named atoms
   are DERIVED smart-ctors here, `:259-285`).

These three were each built to "offer the algebra not the atom," but they did so **independently**.
Convergence onto one vocabulary is now the live ergonomics tax (precisely the fork the doc §B set out
to delete; the builds closed the expressiveness gap but re-forked the surface).

### Datalog (D9): no Lean model

Confirmed: no Lean datalog evaluator. `RelationalClosure`/`ArithmeticClosure`/`QuantifiedPredicate`/
`PrivatePredicate` exist as *predicate* closures, but the Rust authorization-datalog
(`token/src/datalog_verify.rs`, `factset.rs`) has no Lean counterpart.

### GuardedTransformer (D8): not built

No `GuardedTransformer` (predicate + deterministic-derive pair) exists. The *related* `GuardedHole`
(`Dregg2/Exec/GuardedHole.lean:37`) exists — a `Pred`-guarded late-filled slot over
`predStateStepGuarded` — but that is the partial-turn/promise object, not the derive-with-guard lens.

---

## 2. THE EXPRESSIVENESS GAP (what we genuinely CANNOT say today)

The predicate-language gaps the harvest named are **closed**. The remaining real gaps are:

1. **A caveat cannot be inspected, serialized, refined, or circuit-emitted.** `Caveat.local` is a
   raw `Ctx → Bool`. You cannot decide whether one local caveat narrows another (the
   `attenuate_narrows` proof `Caveat.lean:84` works structurally on the *list*, never on caveat
   *content*); you cannot put a caveat on the wire or into the STARK as a term. Same gap on
   `GatedCaveat.check`.
2. **No shared caveat vocabulary with the Rust datalog factset.** The Rust `DreggGrant`
   (App/Service/Feature/ConfineUser/ValidityWindow/OAuthScope/Budget/FeatureGlob) is a *reified*
   caveat vocabulary that lives Rust-side; the Lean `Caveat` is the opaque function. The two forks
   cannot be proven equivalent.
3. **Three predicate algebras instead of one** (§1). An author choosing a surface gets a different
   atom set and a different evaluator. There is no single `Pred` that subsumes `RelPred`'s affine
   half-space and the `StateConstraint` shapes.
4. **No verified datalog semantics** (the "ground-truth verification is unverified" gap, unchanged).
5. **No predicate→function "derive-with-guard" facet** (D8) — authors must supply `new` and have it
   checked; they cannot have the cell DERIVE `new` under the same admission predicate.

---

## 3. THE DESIGN

Given the corrected state, the campaign is **mostly a CONVERGENCE + REIFICATION job, not an
atom-building job.** Three concrete moves:

### (A) Reify `Caveat.local` → `Caveat.pred` (the one genuinely-additive new AST — D6)

Replace the opaque `local (Ctx → Bool)` with a reified arm while **keeping** an opaque escape hatch:
```lean
inductive Caveat (Ctx Gateway : Type) where
  | pred       (p : CaveatPred)          -- NEW: introspectable AST (folds to a Ctx → Bool)
  | opaque     (check : Ctx → Bool)      -- RENAMED from `local`: handwritten escape hatch (nothing regresses)
  | thirdParty (gateway : Gateway)
```
`CaveatPred` mirrors the Rust `DreggGrant` vocabulary (appAction/service/confineUser/oauthScope/
feature/validAfter/validUntil/budget/featureGlob) closed under `and`/`or`/`not`. **Reuse the
existing `Pred`/`RelPred` Boolean-layer pattern** rather than inventing a fourth — ideally make
`CaveatPred` a thin wrapper or alias so the request-context atoms and the record atoms share one
connective layer.

- **Soundness obligation per atom**: a decidable `Bool` fold + an admit-characterization + a
  non-vacuity ADMIT/REJECT pair (`by decide`), exactly the `PredAlgebra.lean` discipline.
- **The payoff theorem this UNLOCKS**: a structural *refinement* check — one `CaveatPred` provably
  narrows another — sharpening the list-level `attenuate_narrows` to content-level. This is the new
  metatheory the reification buys.

### (B) Converge the three algebras onto one (the standing fork-debt)

The cheapest correct move is NOT a fourth algebra but a **subsumption bridge**: prove `RelPred`'s
affine atom is a `StateConstraint.affineLe`/`affineEq` instance (it is — same shape), and make
`CaveatPred`'s connectives the same `Pred` connectives. Land `ofRelCaveat`-style faithful-embedding
theorems (the `RelationalClosure.lean:358` pattern) BETWEEN the algebras, not just within each.
End state: one atom catalog (`StateConstraint`), one Boolean layer (`Pred`), `RelPred` and
`CaveatPred` as *views* with proven-equal denotation.

### (C) The forest-gate weld is DONE — verify, don't rebuild

`dischargeCoordinated` is already the live admission path for `.coordinated` via
`GatedCaveat.cross` (§1). The only remaining task here is to confirm `caveatsDischarged`/`gateOK`
(`FullForestAuth.lean:442,461`) actually *populate* `cross` on the standard `execFullForestG` path
for bilateral nodes (the doc §B.2 wiring) — i.e. that an author writing a coordinated caveat gets it
discharged without hand-routing to the joint-turn API. This is a wiring audit, not new math.

---

## 4. PHASED PLAN (D0–D9 corrected to source)

| ID | Doc item | **ACTUAL source state** | Action now |
|---|---|---|---|
| D0 | `clearanceGe`/`reachable` atoms | **DONE** (`Program.lean:298,313`, sound+wired) | none |
| D1 | `memberOf`/`inRangeTwoSided`/`deltaBounded` | **DONE** (`SimpleConstraint:81,92,96`) | none |
| D2 | `affineLe`/`affineEq` | **DONE** (`:303,306`; +`affineDeltaLe`/`…Field`) | none |
| D3 | uniform `Pred` Boolean layer | **DONE** (`PredAlgebra.lean`, lifts proved) | none |
| D4 | `boundDelta` silent-true → fail-closed | **DONE** (`Program.lean:538`, theorem `:691`) | none |
| D5 | unify `SlotCaveat` ⟶ `Pred` adapter | **PARTIAL** — `PredCaveat`/`predStateStepGuarded` exist (`PredAlgebra.lean:556`), but `SlotCaveat` (`RecordKernel.lean`) is still the 8-arm hand-catalog wired into `stateStepGuarded`; the live `setFieldA` leg's `caveatsAdmit` is `SlotCaveat`, NOT `Pred` | **migrate** `caveatsAdmit` to evaluate a `Pred` per slot; `stateStepGuarded_eq` is the safety net |
| D6 | reify `Caveat.local` → `Caveat.pred` | **NOT DONE** — still opaque `Ctx → Bool` (`Caveat.lean:39`) | **§3(A)** — the headline new work |
| D7 | weld coordinated discharge into forest gate | **DONE** (`GatedCaveat.cross`, `holds:256`) | wiring audit only (§3C) |
| D8 | `GuardedTransformer` (predicate→derive) | **NOT DONE** (`GuardedHole` is the adjacent, different object) | optional; build after D6 over the extended `Pred` |
| D9 | Lean datalog evaluator + soundness | **NOT DONE** (research-grade) | independent parallel workstream |

### THE PRECISE FIRST CONCRETE STEP

**D6 beachhead — reify ONE caveat atom end-to-end.** In `Dregg2/Authority/Caveat.lean`:
1. add `CaveatPred` with a SINGLE atom (`validAfter (t : Int)` — the simplest `DreggGrant` dimension,
   over a `Height`-shaped ctx) plus `and`/`or`/`not`/`tt`/`ff`, reusing the `PredAlgebra` connective
   shape;
2. add `Caveat.pred (p : CaveatPred)`, rename `local`→`opaque` (keep it — nothing regresses);
3. fold `CaveatPred` in `Caveat.ok` (`:47`);
4. prove `attenuate_narrows`/`attenuate_subset`/`token_discharges` STILL hold (they fold over the
   list, AST-agnostic — they lift by structural coverage);
5. add the new content the reification buys: `caveatPred_refines` (a structural narrows-check on
   `CaveatPred` content) + a non-vacuity ADMIT/REJECT `by decide` pair;
6. `#assert_axioms` every keystone kernel-clean.

This is a single-file, additive, ~few-hour change that proves the reification path before fanning the
full `DreggGrant` vocabulary out. THEN: fan the vocabulary (the temporal/budget/scope/glob atoms),
THEN D5 (SlotCaveat→Pred migration), THEN the convergence bridges §3(B), with D9 running in parallel
from the start.

---

## 5. RISKS

### Circuit / VK impact — the headline finding: **NEW ATOMS ARE NOT VK-AFFECTING**

The circuit binds the **aggregate decision bit**, not the atom structure. `setFieldA`'s circuit
(`Dregg2/Circuit/SetFieldCommit.lean`) carries `caveatBit : Var := 0` (`:102`) — a single {0,1}
witness column equal to `caveatsAdmit s.kernel f actor cell v` (`encSF_caveat:220`, `sfcaveat_iff:351`).
The descriptor (`EffectVmEmitSetField.lean`) pins the post-block (the moved field + frame), and the
guard is supplied as one indicator (`SetFieldCommit.lean:99`). **The circuit never enumerates atoms** —
it binds "the executor said admit." So adding atoms to `StateConstraint`/`SlotCaveat`/`Pred`/
`CaveatPred` changes only the executor's *off-circuit decidable `Bool`* `caveatsAdmit`, leaving the
column layout, descriptor, and VK **byte-identical**. Reifying `Caveat.local` is likewise off-circuit
(the token/caveat layer is not in the `setFieldA` descriptor). **Verdict: the language uplift is
NOT VK-affecting under the current binding model.**

The corollary caveat (connects to the circuit-soundness-apex campaign): because the circuit binds the
*outcome bit* and not the *policy term*, the circuit proves "the executor decided admit," NOT "the
policy was genuinely satisfied." Making the circuit bind the predicate *term* (so a light client can't
be fooled about WHICH policy gated a write) WOULD be VK-affecting — but that is the apex campaign's
descriptor-fix work, explicitly out of scope for the language uplift, and listed in
`.docs-history-noclaude/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`. The uplift does not regress it; it also does not close it.

### Per-atom soundness

Every existing new atom already ships its admit-char + non-vacuity teeth and is fail-closed on
absent/ill-typed fields (the typed `symField`/`digField` readers, `PredAlgebra.lean:51-63`). The
discipline is established; the only soundness risk is in NEW reified `CaveatPred` atoms — each must
ship the ADMIT/REJECT `by decide` pair (the mandatory anti-vacuity rule) and a fail-closed reading of
its request-context field. No `:= true` arms.

### Blast radius of the `Caveat` AST change (D6)

`Caveat.ok` (`Caveat.lean:47`), `Token.admits` (`:71`), the `CaveatChain` HMAC fold
(`CaveatChain.lean`), and `GatedCaveat.check`. The narrowing/unforgeability proofs (`attenuate_narrows`
`:84`, `chain_unforgeable`) are **structural over the list, AST-agnostic** — they lift by coverage.
The blast radius is the `.local`→`.opaque` rename (mechanical) + adding the `.pred` fold arm. Keeping
`.opaque` means zero behavioral regression for existing handwritten caveats. Low-to-mid.

### Blast radius of D5 (SlotCaveat → Pred)

Touches the EXECUTOR-enforced surface: `caveatsAdmit` (`EffectsState.lean`), `SlotCaveat.eval`/`.field`/
`.bornFresh` (`RecordKernel.lean:141-175`), `FactoryEntry.conforms`, and the circuit's `caveatBit`
binding (which stays correct — it binds whatever `caveatsAdmit` returns). The safety net is
`predStateStepGuarded_eq`/`stateStepGuarded_eq` (post-state unchanged). Mid-high — but the `PredCaveat`
adapter is already proved, so this is a *swap of the evaluator behind `caveatsAdmit`*, not new theory.

---

## 6. VERDICT

**Tractable, and much smaller than the harvest implies.** The harvest's D0–D9 worklist is ~60%
already in source: D0, D1, D2, D3, D4, D7 are DONE (atoms built + sound + wired; boundDelta fixed;
coordinated discharge welded). The campaign's *actual* remaining surface is three items:

- **D6 (reify `Caveat.local` → `Caveat.pred`)** — the genuine headline new work; a single additive,
  non-VK-affecting file change with a clear beachhead (one atom end-to-end) and a real new theorem
  (content-level caveat refinement). **Small, days.**
- **D5 (SlotCaveat → Pred migration)** + **the three-algebra convergence (§3B)** — mid-size cleanup;
  the proved `PredCaveat` adapter + the `ofRelCaveat`-style embedding pattern de-risk it. **Mid.**
- **D9 (Lean datalog)** + **D8 (GuardedTransformer)** — independent, optional, research-grade.

**Size: medium overall, front-loaded small.** **VK-affecting: NO** — the circuit binds the aggregate
`caveatsAdmit` decision bit, not the atom structure, so every atom/AST change is off-circuit and
VK-neutral. The honest caveat is that this same indirection means the circuit proves "executor decided
admit," not "policy genuinely held" — closing THAT is the apex campaign's descriptor work, not this
language uplift. The single most load-bearing correction to the harvest: **`clearanceGe` is not
orphaned and `dischargeCoordinated` is not standalone — both are already live in source.**
