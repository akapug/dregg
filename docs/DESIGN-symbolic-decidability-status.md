# Symbolic decidability at HEAD — does the Deriv/VPA tower COMPOSE? (full-closure audit)

Status audit of the symbolic-VPA / derivative decidability ladder, produced by reading the whole
theory closure: `Dregg2/Crypto/Deriv/{Core,Correctness,SymbolicDerivative,Finiteness,Similarity,
AciNormal,AciComplete,SatOracle,SymbolicEmptiness,StepBridge,SymbolicEmptinessUnbounded}.lean`,
`Dregg2/Crypto/{Chain,Hypergraph,DfaAsCert,VpaAsCert,VpaDecidable,ReplayAsCert}.lean`, and
`docs/DESIGN-symbolic-vpa-lift.md`. Every claim below carries decl + file:line at HEAD.

**Verdict in one paragraph.** The tower COMPOSES for unbounded language **nonemptiness** over the
infinite `Value` alphabet: there is a single assembled, computable
`predRENonemptyDecidable : IsDeployed R → Decidable (∃ w, derives w R = true)`
(`SymbolicEmptinessUnbounded.lean:233`), kernel-clean, with its hypothesis discharged for the real
deployed guard (`noDoubleBraceRE`, `SymbolicEmptinessUnbounded.lean:318`). It does NOT compose for
**equivalence** over the infinite alphabet — no `Decidable (∀ w, derives w R = derives w S)` exists
anywhere, even though every ingredient for the deployed-fragment case is banked and the assembly is
a ~20-line corollary nobody has written (§2). The three decision procedures that DO exist live on
three DIFFERENT fragments that no theorem connects (§3), and the Aci decidable-`≅` branch is
consumed by nothing (deliberately: the pigeonhole rung proved it unnecessary for decidability,
`SymbolicEmptinessUnbounded.lean:25-38`). Several module headers assert states the tree has since
moved past (§5).

---

## 1. The composition trace — unbounded emptiness IS assembled

The headline chain, as it actually links at HEAD (all `#assert_all_clean`, no `sorry`, no
`Classical.dec` laundering — the decision is `decidable_of_iff` off a computable Boolean):

```
tier 0   PredSat (SatOracle.lean:43) — the EBA obligation; witnesses braceVal/dataVal
             │  (realized constructively; see the caveat below)
tier 2   candidates = [braceVal, dataVal]        SymbolicEmptiness.lean:95
         satStep r = candidates.map (der · r)    SymbolicEmptiness.lean:101
         nonemptyWithin_iff_bounded              SymbolicEmptiness.lean:435   (sound ∧ complete, |w| ≤ n,
             │                                    hypothesis IsDeployed R, :240)
(b)      der_mem_step                            StepBridge.lean:86           (der a r ∈ step r, EXACT)
         satStep_reachable_finite                StepBridge.lean:177          (reachable set finite up to ≅,
             │                                    in der_finite's shape — Finiteness.lean:347)
(c)      derList_excise / exists_sim_prefix_pair SymbolicEmptinessUnbounded.lean:74/:113
         pumpDown                                SymbolicEmptinessUnbounded.lean:156
         emptinessBound R = |⊕(pieces R)|        SymbolicEmptinessUnbounded.lean:198  (a plain def — computable)
         nonempty_iff_nonemptyWithin_bound       SymbolicEmptinessUnbounded.lean:208  (the n-FREE reduction)
         predRENonemptyDecidable                 SymbolicEmptinessUnbounded.lean:233  ← THE ASSEMBLED DECISION
```

Semantic grounding: `derives ↔ Matches` (`correctness`, `Correctness.lean:267`) transports the
verdict to the denotational language; `≅`'s use inside the pigeonhole is licensed by `sim_null` /
`sim_der` / `sim_derList` (`Similarity.lean:97/:217/:266`), whose semantics-freedom is CI-pinned
(`#assert_not_depends_on`, `Similarity.lean:384-387`).

Three honest seams inside this otherwise-composed chain:

1. **The tier-0 `Decidable (PredSat φ)` instances are not consumed by the decision.** The oracle is
   realized as the two hard-coded witness frames `braceVal`/`dataVal`
   (`HandlebarsGuarded.lean:158/:160`) plus `leaf_braceP_brace`/`leaf_braceP_data`
   (`HandlebarsGuarded.lean:170-173`). `SatOracle.lean`'s instances (`:66-71,:90-91`) are parallel
   artifacts stating the same facts in `PredSat` form; in particular the general
   `predSat_symEq f s` for EVERY field/symbol (`SatOracle.lean:56`) does NOT flow into the search —
   `candidates` is welded to the `braceP` algebra. Tier 0's generality is banked but unplumbed.
2. **The decision is a termination argument, not an algorithm.** `emptinessBound` is exponential in
   `|pieces R|` and `reachableWithin` is exponential in depth with no dedup; the composite
   kernel-evaluates only for `ε` (budget 4, `SymbolicEmptinessUnbounded.lean:280-286`). The
   smallest EMPTY machine (`bot`, budget 15, ≈ 3^15 residuals) does not run; its `false` evaluation
   is carried as a hypothesis in an `example` (`:305`) while the theorem
   `nonemptyWithin_bound_complete` (`:240`) is fully proven. Tractability, not decidability, is the
   open axis — and that is exactly what a decidable `≅` (§3) would buy as an adaptive fixpoint.
3. **The `IsDeployed R` hypothesis is real but met.** It is discharged for `contradictionRE`,
   `bot`, `ε`, and the actual templater guard `noDoubleBraceRE`
   (`SymbolicEmptiness.lean:460-468`, `SymbolicEmptinessUnbounded.lean:278/:301/:318`). No
   assembled decision in the tower carries an un-met hypothesis.

## 2. Equivalence — the pieces are proven, the headline statement was never instantiated

**No `Decidable` of language equivalence over `List Value` exists at HEAD.** What exists instead:

- `simDecide_correct` (`AciComplete.lean:814`): `simDecide R S = reEq (nrm R) (nrm S)` decides
  `Sim R S` on `RigidFull` (`AciComplete.lean:479`). `Sim` (`Similarity.lean:57`) is the ACI
  congruence — strictly finer than language equivalence (no unit/annihilator/star laws;
  `AciComplete.lean:1080-1085` says so itself). Deciding `≅` is NOT deciding template equivalence.
- `decidable_template_equivalence` (`VpaDecidable.lean:1624`): genuine, unconditional, computable,
  kernel-`#guard`ed both polarities (`:1649-1655`) — but over the FINITE alphabet
  `Sym = {op, cl, dat}` (`VpaAsCert.lean:65`). It shares no types with `PredRE` (words are
  `List VpaAsCert.Sym`, not `List Value`) and neither file imports the other. It is the finite
  blueprint for tier 4, not a rung of the infinite-alphabet ladder.
- `LangEquiv R S := ∀ w, derives w R = derives w S` is DEFINED (`Powerset.lean:67`) with
  congruence lemmas, but no decision instance anywhere.

**The unwritten corollary — flat deployed-fragment equivalence is ~20 lines from done.** For
`IsDeployed R` and `IsDeployed S`:
`D := (R ⋒ ¬S) ⋓ (S ⋒ ¬R)` is `IsDeployed` (the fragment is closed under every constructor,
`SymbolicEmptiness.lean:240-247`), and `derives w D = true ↔ derives w R ≠ derives w S` by
`derives_alt`/`derives_inter`/`derives_neg` (`Correctness.lean:88/:95/:103` — `PredRE` has NATIVE
intersection and complement, `Core.lean:46-53`, which is why no product/determinization
construction is needed on the flat rung). So
`Decidable (∀ w, derives w R = derives w S) := not-instance of predRENonemptyDecidable at D`
follows from banked lemmas only. This is design-doc tier 3 (`DESIGN-symbolic-vpa-lift.md:239`),
estimated "~week" there; the actual remaining work is one corollary file. It is the sharpest
uncomposed seam in the tower: every piece proven, the headline claim never stated as one decl.

## 3. Fragment reconciliation — three fragments, no connecting theorem, no consumed mismatch

The three deciders run on three DIFFERENT fragments:

| Fragment | Definition | Nature | Consumed by |
|---|---|---|---|
| `IsDeployed` | `SymbolicEmptiness.lean:240` (leaves `LeafDeployed`, `:234` — read a frame only through `leaf braceP`) | SEMANTIC (braceP-generated boolean algebra) | the whole emptiness chain (§1) |
| `RigidFull` / `Frag` | `AciComplete.lean:479` / `:327` (every leaf in `predBEq`'s decidable set `tt/ff/symEq/digEq`, `AciNormal.lean:72`) | SYNTACTIC (leaf shape, any field/symbol) | `simDecide` only |
| finite `Sym` grid | `VpaAsCert.lean:65` | a different alphabet entirely | `decidable_template_equivalence` |

`IsDeployed` and `RigidFull` are INCOMPARABLE, and no lemma at HEAD relates them:

- `sym (.symEq "k" 7)` — `AciComplete`'s own test leaf `g7` (`:893`) — is `RigidFull` but NOT
  `IsDeployed`: `braceP = .symEq "t" 0` (`HandlebarsGuarded.lean:162`) cannot distinguish
  `record [("k", sym 7)]` from `record []` (both `braceP`-false), yet `symEq "k" 7` separates
  them, so `LeafDeployed` fails.
- A ctx-lessly CONSTANT atom leaf (the fail-closed classes tabulated in
  `DESIGN-symbolic-vpa-lift.md:98-100`) is `LeafDeployed` (constants distinguish nothing) but not
  rigid (`predBEq` answers `false` on every `atom`, `AciNormal.lean:77`).

**Is the mismatch a gap?** Not today, because nothing composes across it: ingredient (a) — the
decidable `≅` that `AciNormal`/`AciComplete` build — is imported by NOTHING in the emptiness chain
(verified: no reference to `simDecide`/`nrm`/`normalize` in `SymbolicEmptiness*`/`StepBridge`), and
`SymbolicEmptinessUnbounded.lean:25-38` proves the demotion is principled: `≅` occurs only inside
proofs, never in what runs, so `predRENonemptyDecidable` carries no `DecidableRel Sim`. The
mismatch BITES the moment someone builds the named next uses:

- the **adaptive fixpoint** (dedup the `reachableWithin` frontier by `simDecide` to make the
  decision run past `ε`) needs `RigidFull` on states of an `IsDeployed` search — the intersection
  is inhabited (`braceP` is a `symEq`, so every pure-`braceP` guard is in both) but nowhere
  characterized;
- **tier-1 widening** (guards over arbitrary `symEq` algebras): the pigeonhole machinery is
  parameterized in shape (`pumpDown` takes any `≅`-bounding list, `exists_sim_prefix_pair` any
  candidate word), but `candidates`, `LeafDeployed`, `der_factors` (`SymbolicEmptiness.lean:270`)
  and `canonicalWitness` (`:307`) all hard-code minterm-width 2 over the single atom `braceP`.
  Generalizing means: per-`R` leaf-set extraction → minterm enumeration → a witness per satisfiable
  minterm (which is exactly where the currently-unplumbed `predSat_symEq` generality plugs in).

One more fragment-adjacent finding: `Exec/Program.lean:419-421` now DERIVES
`DecidableEq SimpleConstraint/BoundBranch/StateConstraint` — the exact enabling instance
`AciComplete`'s residual (`:1064-1078`) named as the only remaining axis. But the comment above it
(`Program.lean:417`: "This TOTALIZES `predBEq`/`reEq` … the `atom` leaf … now decides")
OVERSTATES HEAD: `predBEq` (`AciNormal.lean:72-77`) still has no `atom` arm and `rigidRE` still
rejects atom leaves (`#guard rigidRE (.alt gAtom gAtom) = false`, `AciComplete.lean:972`). The
instance landed; the widening it enables did not. Every `AciComplete` theorem transports unchanged
once `predBEq` gains the arm (`AciComplete.lean:1074-1078`) — this is now mechanical, no longer
blocked.

## 4. Cross-cutting: duplication and subsumption

- **`derList` / `derives_eq_null_derList` — DEDUPED.** Defined once (`Similarity.lean:253/:258`);
  the byte-identical copies `SymbolicEmptiness` once carried were removed (its §2 note, `:112-115`
  records this). `derList_append` exists once (`SymbolicEmptiness.lean:117`). Clean.
- **`dedupFirst` vs `ddf` — intentional double implementation, proven equal.** `AciNormal`'s
  well-founded recursion (`:185`) and `AciComplete`'s structural `ddf` (`:123`), bridged by
  `dedupFirst_eq_ddf'` (`AciComplete.lean:311`). Fine.
- **`normalize` vs `nrm` — the subsumption is real and the keep-both justification is unfounded.**
  `nrm` (`AciComplete.lean:528`) strictly subsumes `normalize` (`AciNormal.lean:194`) in power
  (`rigidFull_of_frag`, `:498`), and `AciComplete.lean:77` keeps `normalize` because "other modules
  depend on its shape" — MEASURED FALSE: no file outside `AciNormal`/`AciComplete` references
  `normalize` (grep over `Dregg2/`). The pure-`alt` results (`sim_normalize_eq`, `not_sim_alt_comm`)
  could be restated as corollaries of `sim_nrm_eq` through `rigidFull_of_frag`. Low-risk cleanup,
  not a correctness issue.
- **`vchained` duplicates `Hypergraph.chain` structurally** with a proven `Iff`
  (`vchained_iff_chain`, `VpaAsCert.lean:169`), whereas `Dfa.chained` was REDEFINED as
  `Hypergraph.chain` (`DfaAsCert.lean:57-64`, `Iff.rfl`). Asymmetric treatment of the same dedup;
  the definitional route is available for `vchained` too.
- **Name collision, reader hazard only:** `Deriv.satStep` (sat-filtered derivative step,
  `SymbolicEmptiness.lean:101`) vs `VpaDecidable.satStep` (summary-saturation round on
  `Finset (S × S)`, `VpaDecidable.lean:840`) — same name, unrelated meanings, different namespaces.
- **The generic-subsumes-bespoke moves are already taken** on the certificate substrate:
  `Chain.lean`'s `bridge`/`Cert`/`Cert.foldSound` (`:84/:42/:125`) carry the DFA
  (`dfaAccepts_as_cert`, `DfaAsCert.lean:76`), VPA (`vpaAccepts_as_cert`, `VpaAsCert.lean:183`),
  CFG (`cfg_parse_via_reduction`, `Hypergraph.lean:69`), and pushdown-replay rungs
  (`ReplayAsCert` re-derives `mrun_imp_replay` through `Cert.foldSound`). No further duplicated
  multi-row induction was found in the Deriv tower; the pigeonhole (`exists_sim_prefix_pair`)
  correctly rides mathlib's `Fintype.exists_ne_map_eq_of_card_lt`.

## 5. Stale statements in the tree (headers asserting superseded states)

These matter because the module headers are how the next lane orients:

- `SatOracle.lean:4` — "UNREGISTERED (not in any import chain)". FALSE at HEAD: registered
  (`Dregg2.lean:192`) and imported by `SymbolicEmptiness.lean:72`.
- `SymbolicEmptiness.lean:54-70` and `:389` — "the UNBOUNDED decision … NOT PROVED", "the UNBOUNDED
  `C1` remains open", needing three ingredients including "(a) a DECIDABLE `≅`". Superseded:
  `SymbolicEmptinessUnbounded` proves the unbounded decision WITHOUT (a).
- `Dregg2.lean:195` (StepBridge import note) — "(a) decidable ≅ is a PREREQUISITE for (c) counting,
  not an independent axis". Superseded by the same finding (the Unbounded pigeonhole indexes into
  the bounding list, so ≅-duplicates only inflate the bound); `Dregg2.lean:194` states the
  corrected picture one line above.
- `AciNormal.lean:32-35` and residual `:382-390` — "there is no `starCong`", completeness "blocked
  on a PRIOR change". Superseded: `Similarity.lean:78-81` carries `catCongR`/`starCong` and
  `AciComplete` takes the widening. (`AciNormal`'s ⚑ note `:26-33` was updated; its residual §2
  text was not.)
- `Dregg2.lean:196` (AciNormal note) — "LRB non-commutativity is ARGUED (prose model), not yet a
  Lean theorem". Superseded: `not_sim_alt_comm` (`AciComplete.lean:868`).
- `Exec/Program.lean:417` — "TOTALIZES `predBEq` … now decides". Overstated: enabling instance
  only; `predBEq` unwidened (§3).

## 6. The sharpest true statement, and the distance to the full claim

**Decidable NOW, machine-checked, over the infinite `Value` alphabet:**

1. **Unbounded nonemptiness** `∃ w : List Value, derives w R = true` — decidable
   (`predRENonemptyDecidable`, `SymbolicEmptinessUnbounded.lean:233`) for every `R` with
   `IsDeployed R`: guards whose leaves read a frame only through `braceP` — the boolean algebra of
   every guard the templater writes at HEAD, including `noDoubleBraceRE`. Sound and complete
   against the denotational `Matches` via `correctness`. Computable in principle; kernel-feasible
   today only for trivial `R` (the bound is doubly exponential in practice).
2. **Bounded nonemptiness** (`|w| ≤ n`) — decidable at every `n` for the same fragment
   (`boundedNonemptyDecidable`, `SymbolicEmptiness.lean:449`).
3. **ACI similarity `≅`** (NOT language equivalence) — decidable on `RigidFull`
   (`simDecide_correct`, `AciComplete.lean:814`).
4. **Full template equivalence** — decidable ONLY on the finite `{op, cl, dat}` alphabet
   (`decidable_template_equivalence`, `VpaDecidable.lean:1624`), disconnected from `PredRE`.

Everything above lives in the single-frame leaf reading (`leaf φ a = Pred.eval φ (.record []) a`,
`Core.lean:73`); the stateful `(old,new)` carrier is out of scope by design (`Core.lean:19-21`).

**The remaining distance to "decide template equivalence over the infinite alphabet", ordered:**

1. **(days; zero new mathematics)** The symmetric-difference corollary of §2:
   `Decidable (∀ w, derives w R = derives w S)` for `IsDeployed R, S` — flat deployed-fragment
   template equivalence over the infinite alphabet. All pieces banked; nobody has assembled it.
   This is the single next rung and it completes the flat headline for the guards that exist.
2. **(the genuine widening)** Generalize `candidates` from the hard-coded 2-minterm `braceP`
   algebra to per-`R` minterm witness lists over arbitrary rigid leaf sets (tier 1's small-model
   argument; plumbs `predSat_symEq`'s already-proven generality into the search; `der_factors` /
   `pumpDown` are shape-ready). This also forces the §3 fragment reconciliation
   (`IsDeployed` ↔ `RigidFull`).
3. **(tractability, not decidability)** The adaptive fixpoint: `simDecide`-dedup of the reachable
   frontier, turning the astronomical `emptinessBound` into the actual `≅`-class count — the ONLY
   remaining role of ingredient (a), and prerequisite for any of this running on real guards.
4. **(the nested case; a campaign)** The symbolic VPA port — tier 4 of
   `DESIGN-symbolic-vpa-lift.md:240`, substitution map in its §3. `VpaDecidable` is the finite
   blueprint (never enumerates the alphabet; the oracle slots where the transition-`Decidable`
   instances sit); nothing of it is built symbolically. Needed only for composed/nested templates
   (`HandlebarsCompose`); the flat templater needs rungs 1–3 only.
