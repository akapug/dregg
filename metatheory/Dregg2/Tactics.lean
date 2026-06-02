/-
# Dregg2.Tactics — shared proof automation for the dregg2 metatheory.

Small, honest helpers shared across the modules and the executable protocols. The rule:
these CLOSE genuinely-routine goals (reflexivity, definitional simp, injection cleanup,
linear arithmetic). They are NOT a way to make a real obligation *look* discharged — if a
helper does not close a goal, the goal is real: prove it properly or leave an explicit
`sorry` with a one-line reason. (Never `admit`, never a fresh `axiom`, never
`native_decide` on a non-decidable prop.)

Grows as recurring patterns emerge from the proof-discharge swarm.
-/
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Lean

/-! ## Axiom-hygiene tripwire — the `sorryAx` regression guard.

A theorem can *look* clean ("PROVED, no sorry") while transitively depending on a
`sorryAx` pulled in through a renamed/aliased lemma or a spec-first `sorry`'d primitive.
This bit us once (a strengthened theorem silently inherited `sorryAx`). `#assert_axioms`
turns the prose promise "depends only on the standard kernel axioms" into a *build-checked*
one: it ELABORATES to an error if the named declaration's axiom set escapes
`{propext, Classical.choice, Quot.sound}` (notably: any `sorryAx`). It can only reject,
never close a goal — the safest possible addition. Pin it under each "PROVED" keystone.

Defined at TOP LEVEL (outside the namespace) so the `#assert_axioms` command token parses
in every importing module without needing `open`.

(Honest note on §8 oracles: `CryptoKernel`/`World`/`Verifiable` obligations enter as
*typeclass parameters/hypotheses*, NOT `axiom`-keyword declarations, so they do not appear
in `collectAxioms` and correctly do not trip this guard. A genuine `axiom`-keyword oracle,
were one ever added, would have to be allow-listed by name with a comment — by design.) -/

open Lean Elab Command in
/-- `#assert_axioms foo` errors unless every axiom `foo` depends on is one of the three
standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). In particular it
FAILS on `sorryAx`, catching a silent `sorry`-inheritance at build time. -/
elab "#assert_axioms" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "axiom-hygiene FAIL: {name} depends on non-kernel axioms {bad.toList} \
      (a `sorryAx` here means a silent `sorry` leaked into a 'PROVED' keystone)"

/-! ## `#assert_namespace_axioms` — module-wide axiom-hygiene pinning (the ledger-collapser).

`Claims.lean` hand-lists ~110 fully-qualified `#assert_axioms` names. `#assert_namespace_axioms`
does the same job over a whole NAMESPACE in one line: it walks `getEnv`, finds every
THEOREM whose name lies under the given prefix, runs `collectAxioms`, and THROWS if any
depends on an axiom outside `{propext, Classical.choice, Quot.sound}` (notably `sorryAx`).
It is a pure REJECTOR — it can only error, never close a goal — so it is the safest
possible automation.

**The honesty caveat (the `except` list).** Module-wide pinning could silently hide a
keystone that *legitimately* rests on a §8 oracle / Law-1 `sorry`'d primitive — exactly the
ones `Claims.lean` deliberately does NOT pin (its §12/§16 PARKED pins). So a name passed in
the `except` clause is SKIPPED (and reported), preserving the discipline "a keystone resting
on a primitive is NOT pinned". Each skip must be justified by a comment, exactly as the
PARKED pins are. This collapses the clean majority of the ledger while keeping the
fail-loud guard for the rest.

(Like `#assert_axioms`, this only sees `axiom`-keyword declarations; §8 oracles that enter
as typeclass parameters / hypotheses — `Verifiable` / `CryptoKernel` / `World` — do not
appear in `collectAxioms` and so do not trip it. By design.) -/

/-- `#assert_namespace_axioms NS (except a b …)?` — pin EVERY theorem under namespace `NS` to the
three standard kernel axioms, erroring on the first one that escapes (a `sorryAx` ⇒ a silent
`sorry` leaked). Names listed in `except` are skipped (they legitimately rest on a §8/Law-1
primitive — justify each with a comment). Logs the count pinned. Pure rejector. -/
syntax (name := assertNamespaceAxioms)
  "#assert_namespace_axioms" ident (" except " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(command| #assert_namespace_axioms $ns:ident $[ except $excIds:ident*]?) => do
  let env ← getEnv
  let prefixName := ns.getId
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- Resolve the `except` names to fully-qualified constants (a typo is an `unknownConstant`
  -- error here, so the allow-out list cannot silently drift — same discipline as a bad pin).
  let exceptIdents : Array Ident := match excIds with
    | some arr => arr
    | none => #[]
  let exceptNames ← exceptIdents.toList.mapM fun id =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id.raw
  let mut checked : Nat := 0
  let mut skipped : Nat := 0
  let mut seenExcept : List Name := []
  -- Walk the whole environment; `env.constants` is an `SMap Name ConstantInfo`.
  for (name, info) in env.constants.toList do
    -- direct or nested members of the namespace (`Dregg2.Spec.Guard.admits_all` etc.)
    unless prefixName.isPrefixOf name && prefixName != name do continue
    -- theorems only — skip defs, inductives, constructors, recursors, axioms themselves
    unless info.isThm do continue
    -- skip compiler-internal names (`_proof_`, `.match_`, equation lemmas, …)
    if name.isInternalDetail then continue
    if exceptNames.contains name then
      skipped := skipped + 1
      seenExcept := name :: seenExcept
      continue
    let axs ← collectAxioms name
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "axiom-hygiene FAIL: {name} depends on non-kernel axioms {bad.toList} \
        (a `sorryAx` here means a silent `sorry` leaked into a 'PROVED' keystone). \
        If this keystone legitimately rests on a §8/Law-1 primitive, add it to the \
        `except` clause with a justifying comment — do NOT weaken the theorem to pass."
    checked := checked + 1
  -- An `except` name that matched nothing in the namespace is dead allow-listing — surface it
  -- (a renamed/retired keystone left in the allow-out list is itself a drift to catch).
  for e in exceptNames do
    unless seenExcept.contains e do
      logWarning m!"#assert_namespace_axioms {prefixName}: `except` name {e} matched no \
        pinned theorem in this namespace (retired/renamed? remove it from the allow-out list)"
  logInfo m!"#assert_namespace_axioms {prefixName}: {checked} theorems pinned kernel-clean\
    {if skipped > 0 then m!", {skipped} skipped via `except`" else m!""}"

namespace Dregg2.Tactics

/-- `dregg_auto` — best-effort closer for *routine* obligations only: reflexivity,
`trivial`, definitional/hypothesis `simp`, linear arithmetic, propositional tautology.
Use it as the last step of a proof; if it fails, the goal carries real content. -/
macro "dregg_auto" : tactic =>
  `(tactic| first
    | rfl
    | trivial
    | (intros; first | rfl | trivial | simp_all | omega | tauto)
    | simp_all
    | omega
    | tauto)

/-- `option_inj at h` — collapse `some x = some y` (and any nested `(·,·) = (·,·)`) in `h`
to its component equalities; the standard first move when reading back a protocol step
that returned `some (newState…)`. -/
macro "option_inj" "at" h:ident : tactic =>
  `(tactic| simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident)

/-! ## §3 — Effect-arm combinators (the per-effect dispatch-proof de-boilerplaters).

The big `cases fa with` dispatch proofs (`execFullA_ledger_per_asset`, `_chainlink`,
`_attests_per_asset`, … over the ~46-arm `FullActionA`) repeat a tiny vocabulary of moves per
arm: reject the `none` (fail-closed) branch against the commit hypothesis, substitute the
committed state on the `some` branch, peel an inner `if gate then … else none`, and discharge a
balance-NEUTRAL (caps/log-only) edit. Each combinator below is a `macro` that expands to EXACTLY
those visible tactic steps — it can only do what the spelled-out block does (NO oracle, no
`native_decide`), so a wrong arm still fails loudly. They make adding the next effect a few
lines instead of a 9-site copy-paste (and shrink the laundering surface: less copy-paste, fewer
places a subtly-wrong arm can hide). -/

/-- `reject_none h hk` — the FAIL-CLOSED `none` branch. `hk : f = none` rewrites the commit
hypothesis `h : f = some _` to `none = some _`, closed by `absurd`. -/
macro "reject_none" h:ident hk:ident : tactic =>
  `(tactic| (rw [$hk:ident] at $h:ident; exact absurd $h:ident (by simp)))

/-- `commit_subst h hk` — the `some` branch. `hk : f = some k'` rewrites `h`, peels the
`some`-injection, and substitutes the committed state into the goal. -/
macro "commit_subst" h:ident hk:ident : tactic =>
  `(tactic| (rw [$hk:ident] at $h:ident; simp only [Option.some.injEq] at $h:ident; subst $h:ident))

/-- `gate_peel hk with finisher` — peel an `if guard then some _ else none` inside a chained step
`hk : (if … then some _ else none) = some _`. Uses `split` (so the guard need NOT be named): the
`then` branch substitutes the committed kernel and runs `finisher`; the `else` branch is
FAIL-CLOSED against `hk`. -/
macro "gate_peel" hk:ident " with " fin:tactic : tactic =>
  `(tactic|
    (split at $hk:ident
     · simp only [Option.some.injEq] at $hk:ident
       subst $hk:ident
       $fin
     · exact absurd $hk:ident (by simp)))

-- NOTE: the balance-NEUTRAL finisher `bal_neutral` (the fourth combinator) lives in
-- `Dregg2/Exec/RecordKernel.lean`, next to the per-asset measure (`recTotalAssetWithEscrow`)
-- it unfolds — a tactic-macro must reference user globals from a site where they are in
-- scope (macro hygiene resolves the simp-lemma names at the DEFINITION site, not the use
-- site), so a domain-specific finisher belongs with its domain, not in this generic file.

end Dregg2.Tactics
