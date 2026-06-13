# Axiom hygiene — the terse discipline

The dregg2 corpus advertises keystones as *kernel-clean*: a theorem is clean iff its full
transitive axiom set is a subset of the three standard Lean kernel axioms

```
{ propext, Classical.choice, Quot.sound }
```

— in particular it does **not** depend on `sorryAx`. A `sorryAx` in the axiom set means a
`sorry` (or `admit`, or a transitively-inherited one) leaked into a "PROVED" keystone. The
axiom-hygiene checkers reject that at build time. They are pure rejectors: a checker can only
*error*, never close or weaken a goal, so adding one can never make a false theorem look true.

This is the living assurance mechanism (the #93-successor discipline). It must stay. This doc
is about making it **terse** without weakening it.

## The commands (all in `Dregg2/Tactics.lean`)

One source of truth — `Dregg2.cleanAxioms : List Name` — names the allowed triple. Every
command below consults it via the shared one-name checker `Dregg2.assertNameClean`, so the
terse and batch forms are *exactly* as strict as the verbose one, by construction.

| command | use | strength |
|---|---|---|
| `#assert_axioms foo` | pin ONE keystone (the original verbose form) | per-theorem |
| `#assert_clean foo` | terse synonym of `#assert_axioms foo` | per-theorem (identical) |
| `#assert_all_clean [a, b, c]` | pin a LIST in one command | per-name, same check |
| `#assert_namespace_axioms NS (except …)?` | pin EVERY theorem under namespace `NS` | strongest |

All four fail loudly on the first non-clean name, naming the offending axiom. A typo'd name is
an `unknownConstant` build error, so a pin list can never silently drop a keystone.

### `#assert_namespace_axioms` is the strongest and the tersest

It walks the environment, finds every theorem whose name is under the `NS` prefix (descending
into nested namespaces — `Cav.*`, `ListGuard.*`, etc.), skips compiler-internal names, and
runs `collectAxioms` on each. It then logs how many it pinned. Because it audits *every*
theorem rather than a human-curated list, it cannot miss one someone forgot to add — it is
**strictly stronger** than a per-theorem block, while being a single line.

Empirically, converting the two demo modules showed this directly:

| module | per-theorem `#assert_axioms` lines (before) | batch lines (after) | theorems the batch pinned |
|---|---|---|---|
| `Dregg2/Apps/Trustline.lean` | 75 | 1 | **108** |
| `Dregg2/Calculus/Biorthogonality.lean` | 32 | 1 | **75** |

The batch pins *more* theorems than were individually listed (the 33 / 43 extra were proved
but never hand-added to the block) — the verbosity was hiding incomplete coverage.

### The `except` clause (honesty caveat)

`#assert_namespace_axioms NS except a b` skips the named keystones (and reports the count).
Use it ONLY for a keystone that legitimately rests on a §8 oracle or a Law-1 `sorry`'d
primitive — justify each skip with a comment. A keystone in `except` is *not* pinned; do not
reach for it to make a theorem pass. An `except` name that matches nothing in the namespace
is surfaced as a warning (a retired/renamed keystone left in the allow-out list is itself a
drift to catch).

The triple must stay `{propext, Classical.choice, Quot.sound}`. A crypto carrier enters as a
typeclass parameter / hypothesis (a `Prop`), **not** an `axiom`-keyword declaration, so it
does not appear in `collectAxioms` and does not trip these guards — by design. If a genuine
`axiom`-keyword oracle were ever added, it would surface here and would need an explicit,
commented allow-list entry. Never widen `Dregg2.cleanAxioms` to silence a failure.

## The discipline, terse

- A module that pins a single namespace ends with **one** line after its closing `end`:

  ```lean
  #assert_namespace_axioms Dregg2.Apps.Trustline
  ```

  rather than an N-line per-keystone block. Prefer this whenever a module's keystones all
  live under one prefix.

- For a scattered handful of keystones (e.g. the corpus net in `Dregg2/Claims.lean` that
  re-pins individual theorems across modules it imports but does not own), use
  `#assert_all_clean [a, b, c]` to collapse a run of pins into one command, or
  `#assert_namespace_axioms` per namespace.

- Use `#assert_clean foo` over `#assert_axioms foo` when pinning a one-off; it is the same
  check with less noise.

## What did NOT change

- The guarantee. Same triple, same `collectAxioms` dependency-DAG walk, same loud failure.
  The batch checker catches everything the per-theorem form did and more.
- The two-layer zero-sorry guard in `Dregg2/Claims.lean` (textual CI grep + this ledger).
- The corpus net itself: `Claims.lean` still re-pins the ~190 in-module keystones it can see.

## Non-vacuity of the checker

The checkers were validated against a planted bad axiom: a temporary module declared
`axiom bad : True` and a theorem `rests_on_bad : True := bad`. `#assert_clean`,
`#assert_all_clean`, and `#assert_namespace_axioms` each failed the build with

```
axiom-hygiene FAIL: …rests_on_bad depends on non-kernel axioms [AxiomHygieneTest.bad]
```

while the clean theorem in the same module passed all three. The checker rejects what it
should and accepts what it should — it is not vacuous.
