# The Dregg Calculus

*What kind of runtime is dregg? This document names it precisely.*

> **dregg is a capability calculus with attestable reduction and coordination-typed
> guard modalities.**

The formal statement lives in `Dregg2/Calculus/DreggCalculus.lean` as a small Lean spec.
It is **not new heavy proof** — it is a thin *presentation* over types and theorems that
already exist in the tree. Every law is a pointer to a landed theorem, or a `def`/`example`
that typechecks. The module is `#assert_axioms`-clean.

The headline is the theorem `Dregg2.Calculus.dregg_calculus`: for any committed reduction it
delivers the three faces below at once.

---

## 1. The syntax — a capability calculus

The term language is a thin naming over the live kernel types:

| calculus notion          | dregg type                                   | home |
|--------------------------|----------------------------------------------|------|
| cell ≈ process           | `Cell := CellId`                             | `Exec.Kernel` |
| capability ≈ name/channel| `Capability := EffectsAuthority.ECap` (real `List Auth` lattice) | `Exec.EffectsAuthority` |
| verb shapes (constructors)| `CTerm` = `create · gwrite · move`          | this module |
| guard algebra ≈ typing/precondition | `caveatsAdmit` (the slot-caveat gate) | `Exec.EffectsState` |

There are exactly **three** verb shapes. This is not a stipulation — it is the verb-compression
verdict `Substrate.VerbCompression.compressed_kernel_three`, re-pinned here as `verbs_are_three`:
under the universal map the survivor roster (`Substrate.VerbRegistry.survivors`) collapses to
`create · guarded-write · move`. Five of the seven survivor verbs (write/grant/revoke/
shieldUnshield/lifecycle) dissolve into `gwrite` at a named guard class
(`VerbCompression.cfate`); `move` and `create` separate by *arity* (conservation and bundle birth
are not guards — `gwrite_conservation_trivializes`, `move_not_single_write`,
`create_birth_not_single_write`).

The guard algebra is the **typing / precondition layer**. The deployed atom families are named as a
modality index `GuardModality`, each a cross-reference to its live home:

| modality   | atom family                                                  | home |
|------------|--------------------------------------------------------------|------|
| `actor`    | `SimpleConstraint` (`senderIs` / `balanceGe` / …)            | `Exec.Program` |
| `heap`     | `HeapAtom` (`heapContains`/`heapGetEq`) + the absence atom   | `Substrate.HeapKernel`, `VerbCompression.LitAtom.absent` |
| `temporal` | `TemporalAtom` (`afterHeight`/`withinWindow`/`cooledSince`/…) + UNTIL/SINCE | `Authority.TemporalAlgebra(2)` |
| `epistemic`| `Knows` (K) / `EveryoneKnows` (E) / `DistributedKnows` (D) / `CommonAt` (C) | `Authority.Epistemic` |
| `order`    | the rights-order guard `new ⊆ get(k)` (non-amplification)    | `VerbCompression.grantGuard` |

---

## 2. The reduction relation — `→` *is* the gated step

Reduction is **not a new relation**. The calculus's `→` is the existing gated step:

```
Reduces s (gwrite actor target f n) s'  ↔  stateStepGuarded s f actor target n = some s'
```

— definitionally (`reduces_iff_step`, an `Iff.rfl`). The calculus reads its operational semantics
straight off the executor. The `create` and `move` shapes have their own existing steps
(`recKCreateCell`, `VerbCompression.moveStep`); the `gwrite` shape — shared by five survivor verbs —
is the presented workhorse.

Three properties make this reduction **attestable and enforced**:

- **`reduces_admits_guard`** — every reduction certifies its guard held at the pre-state
  (`stateStepGuarded_admits`). The precondition layer is enforced by the executor on each step.
- **`reduces_is_attested`** — **every reduction leaves a receipt.** The receipt chain grows by
  exactly one row per committed step (`Exec.EffectsState.state_obsadvance`, lifted through
  `stateStepGuarded_eq`). The log is a faithful, append-only witness of the reduction sequence —
  this is what makes the runtime *attestable*.
- **`reduces_fail_closed`** — no reduction past a refused guard
  (`stateStepGuarded_caveat_violation_fails`). There is no escape hatch.

---

## 3. The structural correspondences (process-calculus dictionary)

dregg named against the standard capability / process-calculus vocabulary. Where the correspondence
is already a theorem, it is cited and re-pinned; where it is a structural naming, it is a `def` or
`example` that typechecks. No naming is dressed up as a fake proof.

| correspondence                        | status | reference |
|---------------------------------------|--------|-----------|
| attenuation ≈ scope restriction with **non-amplification** | **THEOREM** | `attenuation_is_scope_restriction` (via `introduce_non_amplifying` + `amplifying_grant_rejected`) |
| exercise ≈ communication (send/receive along the cap-as-channel) | structural `def` | `Correspondence .exercise`; behavior in `EffectsAuthority.exercise_non_amplifying` |
| pipelining ≈ asynchronous communication / promise | structural `def` | `Correspondence .pipelining` |
| factories ≈ replication (`!P`)        | structural `def` | `factory_is_replication` (each `FactoryPattern` a landed module) |
| programs ≈ input guards (`g(x).P`)    | typechecking `example` | the §1 guard layer, enforced by `caveatsAdmit` |

The attenuation correspondence is the load-bearing one and it is a real theorem: a conferred
capability is a genuine **subset** of the held one (scope can only narrow as a capability flows),
and the discipline has **teeth** — a grant conferring authority the holder lacks is *rejected*. This
is the enforced scope-extrusion discipline of the calculus.

---

## 4. The novel part — coordination-typed guard modalities

The thesis: **each guard modality carries a coordination price.** dregg is a runtime where the
*type* of an operation tells you what consensus it costs. The price of a guard is the I-confluence
classification of the invariant it installs
(`Authority.ConfluenceClassifier.guardKeepsConfluence`).

- `modality_price g := guardKeepsConfluence g` — the calculus-level name for the price.
- **`modality_price_is_tier`** — the price *is* the finality tier (the dichotomy
  `keeps_iff_coordinationFree`): classifying a modality *is* deciding its consensus cost.
- **`modality_price_monotone`** — a **monotone (grow-only) modality runs coordination-free**
  (tier-1, partition-tolerant, no consensus). The evidence-↑ and monotone-temporal atoms land here
  (via `monotone_keeps_runs_free`).
- **`modality_price_bounded`** — a **bounded (ceiling) modality forces ordering** (consensus),
  reported with a **constructive clashing-pair witness** (`nonpairwise_escalation` via
  `bounded_forces_ordering`) — the system tells the app author *why* their guard is not cheap, never
  a bare declaration. The `balance ≥ 0` / budget / cardinality-bound actor atoms land here.
- **`modality_price_relational`** — a cross-slot relational modality's price is *decided by the
  merge*: cheap iff its relation survives the pointwise join (`relational_decided_by_merge`). No
  syntactic shortcut.

This connects the guard algebra to the consensus-flex conflict relation
(`Consensus.OnDemandFeasibility`): a coordination-free modality's concurrent turns commute (the
positive pole), a forcing modality's do not (the negative witness).

---

## 5. The headline

`Dregg2.Calculus.dregg_calculus` assembles the three faces over a concrete reduction
`hr : Reduces s (gwrite …) s'`:

1. the syntax has exactly the three compressed verbs (`verbs_are_three`);
2. the reduction **is** the gated step and **emits exactly one receipt row** (`reduces_iff_step` +
   `reduces_is_attested`);
3. a guard modality's price is its finality tier, with **both poles inhabited** — a monotone
   modality runs free (`Witness.markGuard_runs_free`); a bounded modality forces ordering with a
   constructive witness (`Witness.budgetGuard_forces_ordering`).

So: **dregg is a capability calculus (three verbs) with attestable reduction (every step a receipt)
and coordination-typed guard modalities (the type is the consensus cost).** Assembled from cited
theorems — not a new axiom.

---

## Honesty ledger — proved vs. documented-structural

- **Proved here** (assembled from cited pieces, axiom-clean): `reduces_iff_step`,
  `reduces_admits_guard`, `reduces_is_attested`, `reduces_writes`, `reduces_fail_closed`,
  `attenuation_is_scope_restriction`, `modality_price_is_tier`, `modality_price_monotone`,
  `modality_price_bounded`, `modality_price_relational`, `verbs_are_three`, `dregg_calculus`.
- **Pointers** (theorem proved elsewhere, cited and re-pinned by `#assert_axioms`):
  `compressed_kernel_three`, `VerbRegistry.minimality`, `introduce_non_amplifying`,
  `amplifying_grant_rejected`, `ConfluenceClassifier.keeps_iff_coordinationFree`.
- **Structural `def`/`example`** (typechecks; the correspondence is a naming, not a separate
  theorem): `Cell`, `Capability`, `CTerm`, `GuardModality`, `Correspondence`,
  `factory_is_replication`, the program-as-input-guard `example`.
